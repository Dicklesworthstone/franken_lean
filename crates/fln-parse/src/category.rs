//! Parser categories and the indexed lookup with `LeadingIdentBehavior` (plan §9; bead fln-ffam).
//!
//! ## What the behaviour field is for
//!
//! Controlled punning between identifiers and keywords. Upstream's own words
//! (`Basic.lean:1638`): "This feature is used to avoid creating a reserved symbol for each
//! built-in tactic (e.g., `apply` or `assumption`). As a result, tactic names can be used as
//! identifiers."
//!
//! So a category chooses, per position, whether an identifier that *names* a production should
//! run that production, run the identifier production, or both.
//!
//! ## The three variants, and why each needs a NEGATIVE case
//!
//! Punning means a keyword-like identifier is legal in some positions and not others. A rule that
//! is **too permissive passes every positive test**, because permissiveness shows up only as a
//! missing rejection — nothing you can write down will fail. So each variant below is pinned by a
//! pair: what it must accept, and what it must refuse.
//!
//! Observed against the pinned `lean` binary by declaring three categories and giving the
//! ident-indexed and name-indexed productions *different* shapes, so which one matched is visible
//! in whether the file parses. `run pun` with the ident production requiring a trailing `!`:
//!
//! ```text
//! behaviour   production indexed under `pun`   identKind fallback
//! default     REFUSED                          available
//! symbol      available                        REFUSED
//! both        available                        available
//! ```
//!
//! Each `REFUSED` cell is a negative case, and each was produced by an actual refusal from the
//! pin — `unexpected end of input; expected '!'` — not by reasoning about what should happen.
//!
//! ## What is transcribed rather than observed
//!
//! `both`'s **dedup guard** — upstream's `if val == identKind then (s, as) -- avoid running the
//! same parsers twice` — is transcribed from `Basic.lean:1717`, **not** observed. I tried: two
//! identical `ident` productions in one category parse with no ambiguity error at all, because a
//! `choice` node is invisible until something elaborates it, and the probe categories have no
//! elaborator. So the guard's *consequence* is asserted here from the pin's source and from what
//! slice A establishes about ties, and it is graded accordingly on the bead.
//!
//! That consequence is worth stating because it is not obvious: without the guard the identKind
//! productions appear **twice** in the candidate list, tie by construction — same position, same
//! success, same priority — and [`crate::state::longest_match`] therefore builds a `choice` node.
//! The parser would manufacture an ambiguity out of nothing, and the elaborator would report a
//! genuine-looking ambiguity error for a file with no ambiguity in it.

use crate::pratt::Lookup;
use crate::state::Production;
use fln_core::name::Name;
use std::collections::BTreeMap;

/// `Lean.identKind` — the auxiliary token identifiers are indexed under.
pub fn ident_kind() -> Name {
    Name::str(Name::anonymous(), "ident")
}

/// `LeadingIdentBehavior` (`Basic.lean:1643`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LeadingIdentBehavior {
    /// "If the leading token is an identifier, then the parser just executes the parsers
    /// associated with the auxiliary token 'ident'."
    ///
    /// So a production indexed under the identifier's own name is **not** reached. `term`,
    /// `command` and `level` all register this (the latter two by omitting the argument).
    #[default]
    Default,
    /// "If the leading token is an identifier `<foo>`, and there are parsers `P` associated with
    /// the token `<foo>`, then the parser executes `P`. Otherwise, it executes only the parsers
    /// associated with the auxiliary token 'ident'."
    ///
    /// Registered by the `attr` category (`Parser/Attr.lean:20`).
    Symbol,
    /// "If the leading token is an identifier `<foo>`, then it executes the parsers associated
    /// with token `<foo>` **and** parsers associated with the auxiliary token 'ident'."
    ///
    /// Registered by the `tactic` category (`Parser/Term/Basic.lean:33`), which is what lets
    /// `apply` be both a tactic and a usable identifier.
    Both,
}

/// The leading token at a position, as `indexed` sees it after `peekToken`.
///
/// Only the shapes `indexed` branches on (`Basic.lean:1702-1723`). A token that is none of these
/// yields no productions at all — upstream's `| .ok _ => (s, [])`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeadingToken {
    /// An atom: indexed under the symbol's own name.
    Atom(String),
    /// An identifier, carrying the `Name` it spells. The behaviour field applies here and only
    /// here.
    Ident(Name),
    /// A node, indexed under its kind — a literal, for instance.
    Node(Name),
    /// Something else: no productions.
    Other,
    /// The token could not be lexed.
    Unlexable,
}

/// A map from token to the productions indexed under it — upstream `TokenMap`.
///
/// `BTreeMap` rather than a hash map so iteration is ordered: the candidate list's order reaches
/// [`crate::state::longest_match`], and while the resolution rule is order-independent for a
/// *winner*, the order decides which of two equal candidates is reported first. Determinism is a
/// contract (FL-INV-01), so the container is chosen to have one rather than to be fast.
#[derive(Debug, Default)]
pub struct TokenMap {
    entries: BTreeMap<String, Vec<Production>>,
}

impl TokenMap {
    pub fn new() -> TokenMap {
        TokenMap::default()
    }

    /// Index `production` under `token`.
    pub fn insert(&mut self, token: impl Into<String>, production: Production) {
        self.entries
            .entry(token.into())
            .or_default()
            .push(production);
    }

    /// The productions under `token`, or `None` if the token has no entry.
    ///
    /// `None` and `Some(empty)` are deliberately distinguishable because upstream's `map.get?`
    /// is what `symbol` branches on: an *absent* entry falls back to identKind, and that fallback
    /// is the difference between `symbol` and `default`.
    pub fn get(&self, token: &str) -> Option<&[Production]> {
        self.entries.get(token).map(Vec::as_slice)
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// A parser category: its tables, its behaviour, and the productions that are not indexed.
///
/// The unindexed lists exist because some productions have no first token — upstream's example
/// (`Basic.lean:1958`) is `syntax term:51 "≤" ident "<" term "|" term : index`, whose set of
/// first tokens "is any token that can start a term, but this set is always changing". Those are
/// always tried, whatever the leading token is.
#[derive(Debug, Default)]
pub struct Category {
    pub name: Name,
    pub behavior: LeadingIdentBehavior,
    pub leading: TokenMap,
    pub leading_unindexed: Vec<Production>,
    pub trailing: TokenMap,
    pub trailing_unindexed: Vec<Production>,
}

impl Category {
    pub fn new(name: Name, behavior: LeadingIdentBehavior) -> Category {
        Category {
            name,
            behavior,
            ..Category::default()
        }
    }

    /// `indexed` (`Basic.lean:1697`) for the leading table, plus the unindexed productions.
    pub fn leading_at(&self, token: &LeadingToken) -> Lookup<'_> {
        self.lookup(&self.leading, &self.leading_unindexed, token, self.behavior)
    }

    /// `indexed` for the trailing table.
    ///
    /// **Always `Default`**, whatever the category's behaviour is: upstream passes
    /// `LeadingIdentBehavior.default` explicitly at the trailing site (`Basic.lean:1932`). The
    /// field is called *Leading*IdentBehavior and it means it — punning applies to the position
    /// that opens a construct, not to positions inside one. A category that applied its behaviour
    /// to trailing lookups would let a keyword-like identifier act as an operator.
    pub fn trailing_at(&self, token: &LeadingToken) -> Lookup<'_> {
        self.lookup(
            &self.trailing,
            &self.trailing_unindexed,
            token,
            LeadingIdentBehavior::Default,
        )
    }

    fn lookup<'a>(
        &'a self,
        map: &'a TokenMap,
        unindexed: &'a [Production],
        token: &LeadingToken,
        behavior: LeadingIdentBehavior,
    ) -> Lookup<'a> {
        let indexed: Vec<&Production> = match token {
            LeadingToken::Unlexable => {
                return Lookup::TokenError(crate::state::ParseError::new(
                    "could not lex a token",
                    fln_syntax::source::BytePos(0),
                ));
            }
            LeadingToken::Atom(symbol) => refs(map.get(symbol)),
            LeadingToken::Node(kind) => refs(map.get(&kind.to_display_string())),
            LeadingToken::Other => Vec::new(),
            LeadingToken::Ident(value) => Self::for_ident(map, value, behavior),
        };
        // Upstream appends the unindexed parsers to the indexed ones
        // (`tables.leadingParsers ++ ps`, `Basic.lean:1912`).
        let mut productions: Vec<&Production> = unindexed.iter().collect();
        productions.extend(indexed);
        Lookup::Productions(productions)
    }

    /// The behaviour field's whole content (`Basic.lean:1705-1723`).
    fn for_ident<'a>(
        map: &'a TokenMap,
        value: &Name,
        behavior: LeadingIdentBehavior,
    ) -> Vec<&'a Production> {
        let ident = ident_kind().to_display_string();
        let spelled = value.to_display_string();
        match behavior {
            // The identifier's own name is not consulted at all.
            LeadingIdentBehavior::Default => refs(map.get(&ident)),
            // The identifier's own name wins outright when it has productions; identKind is
            // reached ONLY as a fallback when it does not.
            LeadingIdentBehavior::Symbol => match map.get(&spelled) {
                Some(productions) => productions.iter().collect(),
                None => refs(map.get(&ident)),
            },
            LeadingIdentBehavior::Both => match map.get(&spelled) {
                Some(productions) => {
                    // THE DEDUP GUARD. An identifier literally named `ident` looks up the same
                    // entry twice; appending both copies would make the identKind productions tie
                    // with themselves — same position, same success, same priority — and
                    // `longest_match` would build a `choice` node, manufacturing an ambiguity out
                    // of a file that has none. Transcribed from the pin, not observed: a spurious
                    // choice node is invisible without an elaborator to complain about it.
                    if spelled == ident {
                        productions.iter().collect()
                    } else {
                        let mut both: Vec<&Production> = productions.iter().collect();
                        both.extend(refs(map.get(&ident)));
                        both
                    }
                }
                None => refs(map.get(&ident)),
            },
        }
    }
}

fn refs(productions: Option<&[Production]>) -> Vec<&Production> {
    productions
        .map(|ps| ps.iter().collect())
        .unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::{ParserState, Prec};

    fn name(text: &str) -> Name {
        Name::str(Name::anonymous(), text)
    }

    fn production(label: &str) -> Production {
        Production::new(name(label), 0, |_state| {})
    }

    /// The labels of whatever a lookup returned, in order.
    fn labels(lookup: Lookup<'_>) -> Vec<String> {
        match lookup {
            Lookup::Productions(productions) => productions
                .iter()
                .map(|p| p.kind.to_display_string())
                .collect(),
            Lookup::TokenError(_) => vec!["<token error>".to_string()],
        }
    }

    /// A category with a production indexed under the identifier name `pun` and another under
    /// `ident` — the exact shape of the pin probes.
    fn category(behavior: LeadingIdentBehavior) -> Category {
        let mut category = Category::new(name("c"), behavior);
        category.leading.insert("pun", production("punProduction"));
        category
            .leading
            .insert("ident", production("identProduction"));
        category
    }

    /// **`default`: positive and negative.**
    ///
    /// Positive: the identKind production is available. Negative: the production indexed under the
    /// identifier's own name is **not** reached — which is the whole content of the variant, and
    /// the half that a too-permissive implementation would get wrong invisibly.
    ///
    /// Observed against the pin: with the ident production requiring a trailing `!`, `run pun` in
    /// a `default` category is REFUSED with `unexpected end of input; expected '!'` — so identKind
    /// ran and the `pun`-indexed production did not.
    #[test]
    fn default_reaches_identkind_and_never_the_identifiers_own_name() {
        let category = category(LeadingIdentBehavior::Default);
        let found = labels(category.leading_at(&LeadingToken::Ident(name("pun"))));
        assert_eq!(
            found,
            vec!["identProduction"],
            "default must reach identKind only"
        );
        assert!(
            !found.contains(&"punProduction".to_string()),
            "NEGATIVE: a production indexed under the identifier's own name must not run"
        );
    }

    /// **`symbol`: positive and negative.**
    ///
    /// Positive: the name-indexed production runs. Negative: identKind is **suppressed** — so the
    /// identifier is *not* usable as a plain identifier in that position. That refusal is the
    /// variant's entire distinguishing content, and it is the case a permissive implementation
    /// silently loses.
    ///
    /// Observed against the pin: with the `pun` production requiring a trailing `!`, `run pun` in
    /// a `symbol` category is REFUSED — identKind was not available to accept the bare identifier.
    #[test]
    fn symbol_runs_the_named_production_and_suppresses_identkind() {
        let category = category(LeadingIdentBehavior::Symbol);
        let found = labels(category.leading_at(&LeadingToken::Ident(name("pun"))));
        assert_eq!(
            found,
            vec!["punProduction"],
            "symbol must run the name-indexed production"
        );
        assert!(
            !found.contains(&"identProduction".to_string()),
            "NEGATIVE: identKind must be suppressed when the name has its own productions, so \
             the identifier is NOT usable as a plain identifier here"
        );
    }

    /// `symbol` falls back to identKind only when the name has **no** productions. The fallback is
    /// what distinguishes `symbol` from a rule that simply ignores identKind.
    #[test]
    fn symbol_falls_back_to_identkind_for_an_unknown_name() {
        let category = category(LeadingIdentBehavior::Symbol);
        assert_eq!(
            labels(category.leading_at(&LeadingToken::Ident(name("unknown")))),
            vec!["identProduction"],
            "an identifier with no productions of its own reaches identKind"
        );
    }

    /// **`both`: positive.** Both sets run, name-indexed first.
    ///
    /// Observed against the pin in both directions: `run pun` parses whether the `pun` production
    /// or the ident production is the one that can accept it, which is only possible if both are
    /// in the candidate list.
    #[test]
    fn both_runs_the_named_production_and_identkind_together() {
        let category = category(LeadingIdentBehavior::Both);
        assert_eq!(
            labels(category.leading_at(&LeadingToken::Ident(name("pun")))),
            vec!["punProduction", "identProduction"],
            "both must offer the name-indexed production AND identKind, in that order"
        );
    }

    /// **`both`: the negative — the dedup guard.**
    ///
    /// An identifier literally named `ident` resolves to the same table entry twice. Appending
    /// both copies would make the identKind productions tie with *themselves* — same position,
    /// same success, same priority — and `longest_match` would build a `choice` node,
    /// manufacturing an ambiguity in a file that has none.
    ///
    /// TRANSCRIBED, not observed: `Basic.lean:1717`, "avoid running the same parsers twice". I
    /// probed for it and could not observe it — two identical `ident` productions parse with no
    /// ambiguity error, because a choice node is invisible until something elaborates it. So this
    /// asserts the pin's rule and the consequence slice A establishes about ties, and is graded as
    /// transcribed on the bead.
    #[test]
    fn both_does_not_offer_the_same_productions_twice() {
        let category = category(LeadingIdentBehavior::Both);
        let found = labels(category.leading_at(&LeadingToken::Ident(ident_kind())));
        assert_eq!(
            found,
            vec!["identProduction"],
            "an identifier named `ident` must not duplicate the identKind productions"
        );
        assert_eq!(
            found.len(),
            1,
            "a duplicate would tie with itself and manufacture a choice node"
        );
    }

    /// The behaviour applies to identifiers **only**. An atom is indexed under its own symbol
    /// whatever the behaviour is, so the three variants agree on non-identifier tokens.
    #[test]
    fn the_behaviour_only_affects_identifiers() {
        for behavior in [
            LeadingIdentBehavior::Default,
            LeadingIdentBehavior::Symbol,
            LeadingIdentBehavior::Both,
        ] {
            let mut category = Category::new(name("c"), behavior);
            category.leading.insert("+", production("plus"));
            category
                .leading
                .insert("ident", production("identProduction"));
            assert_eq!(
                labels(category.leading_at(&LeadingToken::Atom("+".to_string()))),
                vec!["plus"],
                "{behavior:?}: an atom is indexed under its symbol, never under identKind"
            );
        }
    }

    /// **The trailing lookup is always `Default`**, whatever the category's behaviour is
    /// (`Basic.lean:1932` passes it explicitly).
    ///
    /// The field is called *Leading*IdentBehavior and it means it: punning applies to the position
    /// that opens a construct, not to positions inside one. A category that applied its behaviour
    /// to trailing lookups would let a keyword-like identifier act as an operator — so this is a
    /// negative case for the *category*, not for a variant.
    #[test]
    fn the_trailing_lookup_ignores_the_categorys_behaviour() {
        for behavior in [
            LeadingIdentBehavior::Default,
            LeadingIdentBehavior::Symbol,
            LeadingIdentBehavior::Both,
        ] {
            let mut category = Category::new(name("c"), behavior);
            category.trailing.insert("pun", production("punTrailing"));
            category
                .trailing
                .insert("ident", production("identTrailing"));
            assert_eq!(
                labels(category.trailing_at(&LeadingToken::Ident(name("pun")))),
                vec!["identTrailing"],
                "{behavior:?}: the trailing lookup must behave as Default, so a keyword-like \
                 identifier cannot act as an operator"
            );
        }
    }

    /// Unindexed productions are always offered, and come first — upstream's
    /// `tables.leadingParsers ++ ps`. They exist for productions with no fixed first token.
    #[test]
    fn unindexed_productions_are_always_offered_first() {
        let mut category = category(LeadingIdentBehavior::Default);
        category.leading_unindexed.push(production("unindexed"));
        assert_eq!(
            labels(category.leading_at(&LeadingToken::Ident(name("pun")))),
            vec!["unindexed", "identProduction"],
            "unindexed productions precede the indexed ones"
        );
        // And they are offered even for a token with no entry at all, which is the case that
        // makes them "unindexed" rather than "extra".
        assert_eq!(
            labels(category.leading_at(&LeadingToken::Atom("!!".to_string()))),
            vec!["unindexed"],
            "an unknown token still reaches the unindexed productions"
        );
    }

    /// An unlexable token is a token error, not an empty list. The trailing loop's rule 1 depends
    /// on telling those apart, so collapsing them here would erase that rule before it applied.
    #[test]
    fn an_unlexable_token_is_a_token_error_not_an_empty_lookup() {
        let category = category(LeadingIdentBehavior::Default);
        assert!(
            matches!(
                category.leading_at(&LeadingToken::Unlexable),
                Lookup::TokenError(_)
            ),
            "an unlexable token must be distinguishable from 'no applicable production'"
        );
        assert!(matches!(
            category.leading_at(&LeadingToken::Other),
            Lookup::Productions(_)
        ));
    }

    /// A node token is indexed under its kind — a literal, for instance.
    #[test]
    fn a_node_token_is_indexed_under_its_kind() {
        let mut category = Category::new(name("c"), LeadingIdentBehavior::Default);
        category.leading.insert("numLit", production("numeral"));
        assert_eq!(
            labels(category.leading_at(&LeadingToken::Node(name("numLit")))),
            vec!["numeral"]
        );
    }

    /// `None` and an empty entry are different things, because `symbol`'s fallback branches on
    /// exactly that distinction.
    #[test]
    fn an_absent_entry_and_an_empty_one_are_distinguishable() {
        let mut category = Category::new(name("c"), LeadingIdentBehavior::Symbol);
        category
            .leading
            .insert("ident", production("identProduction"));
        // `pun` is absent, so symbol falls back to identKind.
        assert_eq!(
            labels(category.leading_at(&LeadingToken::Ident(name("pun")))),
            vec!["identProduction"]
        );
        assert!(category.leading.get("pun").is_none(), "absent, not empty");
    }

    /// The category name is what the Pratt loop puts in "expected ..." — checked here so the two
    /// slices agree about where it comes from.
    #[test]
    fn a_category_carries_its_name_for_diagnostics() {
        let category = Category::new(name("term"), LeadingIdentBehavior::Default);
        assert_eq!(category.name.to_display_string(), "term");
        // And the state carries the precedence a category parser would have set.
        let state = ParserState::new(65 as Prec);
        assert_eq!(state.prec(), 65);
    }
}
