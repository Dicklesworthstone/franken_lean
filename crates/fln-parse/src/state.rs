//! Parser state, precedence, and the longest-match resolution law (plan §9; bead fln-ffam).
//!
//! ## What this module is
//!
//! The engine's substrate: the syntax stack a production builds into, the two precedence
//! registers, and [`longest_match`] — the rule that decides between applicable productions.
//! No grammar lives here. The Pratt loop that drives it is a separate slice.
//!
//! ## Three places upstream is not a textbook Pratt parser
//!
//! Each is a place a from-scratch implementation diverges *plausibly*, which is why each is
//! transcribed with a citation rather than reinvented.
//!
//! **1. Precedence is a property of parsers, not tokens.** Upstream says so in as many words
//! (`Lean/Parser/Basic.lean:1953-1965`): "In Pratt's algorithms tokens have a right and left
//! binding power. In our implementation, parsers have precedence instead." So there is no
//! binding-power table keyed by token, and building one would be a different algorithm that
//! happens to agree on simple arithmetic.
//!
//! **2. Leading parsers check precedence too.** Upstream, same comment: "in the original
//! Pratt's algorithm, precedences are only checked before calling trailing parsers. In our
//! implementation, leading *and* trailing parsers check the precedence." A textbook
//! implementation checks on the trailing side only, and the difference shows up exactly where
//! a leading production is precedence-restricted.
//!
//! **3. An ambiguity is preserved, not resolved.** [`longest_match`] scores candidates
//! lexicographically by `(end position, success beats error, priority)`
//! (`Basic.lean:1418-1436`) — and when two candidates *tie*, both are kept under a `choice`
//! node rather than one being picked. A parser that took the first winner would silently
//! discard an ambiguity the elaborator is supposed to resolve, and the parse would still look
//! perfectly well formed. This is the single most consequential rule in the module.
//!
//! On a tie the resulting node's `lhsPrec` is the **minimum** of the tied candidates', because
//! — again upstream's own words — "it is not clear what the precedence of a choice node should
//! be, so we conservatively take the minimum".
//!
//! ## What the differentials here do NOT establish
//!
//! Stated in the module because it decides how much the tests are worth: a differential proves
//! agreement, never correctness. Comparing this resolver against a second run of itself, at a
//! different thread count or with recovery toggled, passes whenever both sides are wrong the
//! same way. So the assertions below are against **the pin's rules as transcribed with
//! citations**, and the score tuple is asserted component by component — including the cases
//! where two components disagree about the winner, since that is where a rule invented from
//! intuition differs from the one upstream wrote.

use fln_core::name::Name;
use fln_syntax::source::BytePos;
use fln_syntax::tree::Syntax;
use std::sync::Arc;

/// A precedence level. `Nat` upstream, so unsigned and unbounded there; `u32` here is far above
/// any level the language uses and keeps the arithmetic total.
pub type Prec = u32;

/// `Lean.Parser.maxPrec` — the level a leading parser starts at.
pub const MAX_PREC: Prec = 1024;

/// `Lean.Parser.argPrec`, the precedence of a function argument.
pub const ARG_PREC: Prec = MAX_PREC - 1;

/// `Lean.Parser.leadPrec`, the precedence of a leading term.
pub const LEAD_PREC: Prec = MAX_PREC - 2;

/// Why a production did not apply.
///
/// Separate from a *diagnostic*: this is the engine's control-flow answer, and the trailing
/// loop deliberately discards some of these rather than reporting them
/// (`Basic.lean:1936-1948`). A refusal that reached the user unfiltered would report an error
/// for every fallback production that declined to apply.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    /// The unexpected side of the diagnostic, already phrased for rendering. Empty when a
    /// parser contributes only an expected alternative.
    unexpected: String,
    /// Expected alternatives in parser-composition order. Rendering sorts and deduplicates
    /// them exactly as the pin does; retaining the raw list keeps merging lossless.
    expected: Vec<String>,
    pub at: BytePos,
    /// Whether the production consumed input before failing. The trailing loop treats a
    /// *non-consuming* failure as "this production does not apply here" and a consuming one as
    /// a real error, which is why the distinction is recorded rather than inferred.
    pub consumed: bool,
}

impl ParseError {
    pub fn new(message: impl Into<String>, at: BytePos) -> ParseError {
        ParseError {
            unexpected: message.into(),
            expected: Vec::new(),
            at,
            consumed: false,
        }
    }

    pub fn consuming(message: impl Into<String>, at: BytePos) -> ParseError {
        ParseError {
            unexpected: message.into(),
            expected: Vec::new(),
            at,
            consumed: true,
        }
    }

    /// A parser contribution that names only what was expected.
    pub fn expecting(expected: impl Into<String>, at: BytePos) -> ParseError {
        ParseError {
            unexpected: String::new(),
            expected: vec![expected.into()],
            at,
            consumed: false,
        }
    }

    /// A consuming parser contribution that names only what was expected.
    pub fn consuming_expecting(expected: impl Into<String>, at: BytePos) -> ParseError {
        ParseError {
            unexpected: String::new(),
            expected: vec![expected.into()],
            at,
            consumed: true,
        }
    }

    /// Construct the complete Reference error shape: one optional unexpected description and
    /// zero or more expected alternatives.
    pub fn with_expected<I, S>(
        unexpected: impl Into<String>,
        expected: I,
        at: BytePos,
        consumed: bool,
    ) -> ParseError
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        ParseError {
            unexpected: unexpected.into(),
            expected: expected.into_iter().map(Into::into).collect(),
            at,
            consumed,
        }
    }

    pub fn unexpected(&self) -> &str {
        &self.unexpected
    }

    pub fn expected_items(&self) -> &[String] {
        &self.expected
    }

    /// Render `Lean.Parser.Error.toString`: expected alternatives are sorted, deduplicated, and
    /// joined with the pin's zero/one/two/many grammar.
    pub fn message(&self) -> String {
        let mut expected = self.expected.clone();
        expected.sort();
        expected.dedup();

        let expected = if expected.is_empty() {
            String::new()
        } else {
            format!("expected {}", expected_to_string(&expected))
        };
        match (self.unexpected.is_empty(), expected.is_empty()) {
            (false, false) => format!("{}; {expected}", self.unexpected),
            (false, true) => self.unexpected.clone(),
            (true, false) => expected,
            (true, true) => String::new(),
        }
    }

    /// `Lean.Parser.Error.merge`: the newer nonempty unexpected description wins, expected
    /// alternatives concatenate without losing information, and the newer token position is
    /// retained. Rendering performs the pin's sort and duplicate erasure.
    fn merge(&self, newer: &ParseError) -> ParseError {
        let unexpected = if newer.unexpected.is_empty() {
            self.unexpected.clone()
        } else {
            newer.unexpected.clone()
        };
        let mut expected = self.expected.clone();
        expected.extend(newer.expected.iter().cloned());
        ParseError {
            unexpected,
            expected,
            at: newer.at,
            consumed: self.consumed || newer.consumed,
        }
    }
}

fn expected_to_string(expected: &[String]) -> String {
    let mut rendered = String::new();
    for (index, item) in expected.iter().enumerate() {
        if index > 0 {
            if index + 1 == expected.len() {
                rendered.push_str(" or ");
            } else {
                rendered.push_str(", ");
            }
        }
        rendered.push_str(item);
    }
    rendered
}

/// The engine's state: a syntax stack, a position, the two precedence registers, and at most
/// one error.
///
/// A stack rather than a return value because that is what upstream productions build into,
/// and because `longest_match` has to be able to rewind it to a mark and re-run a candidate
/// from the same starting point. A production that returned a value could not be re-run without
/// re-deriving what it had already consumed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParserState {
    stack: Vec<Syntax>,
    pos: BytePos,
    /// `ParserContext.prec` — the level the *context* demands. A production applies only if its
    /// own precedence is at least this.
    prec: Prec,
    /// `ParserState.lhsPrec` — the precedence of what was just parsed. Read by
    /// [`Self::check_lhs_prec`] to decide whether a trailing production may consume it.
    lhs_prec: Prec,
    error: Option<ParseError>,
}

impl ParserState {
    pub fn new(prec: Prec) -> ParserState {
        ParserState {
            stack: Vec::new(),
            pos: BytePos(0),
            prec,
            lhs_prec: 0,
            error: None,
        }
    }

    pub fn at(mut self, pos: BytePos) -> ParserState {
        self.pos = pos;
        self
    }

    pub fn pos(&self) -> BytePos {
        self.pos
    }

    pub fn set_pos(&mut self, pos: BytePos) {
        self.pos = pos;
    }

    pub fn prec(&self) -> Prec {
        self.prec
    }

    pub fn set_prec(&mut self, prec: Prec) {
        self.prec = prec;
    }

    pub fn lhs_prec(&self) -> Prec {
        self.lhs_prec
    }

    pub fn set_lhs_prec(&mut self, prec: Prec) {
        self.lhs_prec = prec;
    }

    pub fn stack_size(&self) -> usize {
        self.stack.len()
    }

    pub fn push(&mut self, node: Syntax) {
        self.stack.push(node);
    }

    pub fn pop(&mut self) -> Option<Syntax> {
        self.stack.pop()
    }

    pub fn back(&self) -> Option<&Syntax> {
        self.stack.last()
    }

    pub fn stack(&self) -> &[Syntax] {
        &self.stack
    }

    pub fn error(&self) -> Option<&ParseError> {
        self.error.as_ref()
    }

    pub fn has_error(&self) -> bool {
        self.error.is_some()
    }

    pub fn set_error(&mut self, error: ParseError) {
        self.error = Some(error);
    }

    pub fn clear_error(&mut self) {
        self.error = None;
    }

    /// `checkPrecFn` (`Basic.lean:160`): succeeds if the context's demand is at most `prec`.
    ///
    /// The direction is the thing to get right, and it reads backwards at first glance: the
    /// *context* precedence is the floor, and a production whose own precedence is below it does
    /// not apply. Inverting this comparison is a defect that still parses most expressions,
    /// because it only shows up where a production is precedence-restricted.
    pub fn check_prec(&mut self, prec: Prec) -> bool {
        if self.prec <= prec {
            true
        } else {
            self.set_error(ParseError::new(PREC_MESSAGE, self.pos));
            false
        }
    }

    /// `checkLhsPrecFn` (`Basic.lean:169`): succeeds if what was just parsed binds at least as
    /// tightly as `prec`.
    pub fn check_lhs_prec(&mut self, prec: Prec) -> bool {
        if self.lhs_prec >= prec {
            true
        } else {
            self.set_error(ParseError::new(PREC_MESSAGE, self.pos));
            false
        }
    }

    /// Truncate the stack to `size` and move back to `pos` — `ParserState.restore`.
    pub fn restore(&mut self, size: usize, pos: BytePos) {
        self.stack.truncate(size);
        self.pos = pos;
        self.error = None;
    }

    fn shrink(&mut self, size: usize) {
        self.stack.truncate(size);
    }
}

/// The message both precedence checks produce, verbatim from the pin so ours cannot drift.
pub const PREC_MESSAGE: &str =
    "unexpected token at this precedence level; consider parenthesizing the term";

/// A production: a function over the state, plus the precedence and priority it was declared
/// with.
///
/// A shared closure rather than a trait object with associated types because the engine needs a
/// *homogeneous list* it can score against each other, which is what `longestMatchFn` consumes.
///
/// Sharing is semantic, not just an allocation optimization: a [`crate::registry::Registry`]
/// must be able to materialize the executable grammar at an older epoch. Replacing a callback
/// with a metadata-only stand-in would make the historical category look right while parsing
/// differently. `Arc` lets a view retain the exact immutable callback and captured state.
#[derive(Clone)]
pub struct Production {
    /// The node kind this production builds, for diagnostics and for the category inventory.
    pub kind: Name,
    /// Declaration priority — the third and weakest component of the score.
    pub priority: u32,
    pub run: Arc<dyn Fn(&mut ParserState) + Send + Sync>,
}

impl Production {
    pub fn new(
        kind: Name,
        priority: u32,
        run: impl Fn(&mut ParserState) + Send + Sync + 'static,
    ) -> Production {
        Production {
            kind,
            priority,
            run: Arc::new(run),
        }
    }
}

impl std::fmt::Debug for Production {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Production")
            .field("kind", &self.kind.to_display_string())
            .field("priority", &self.priority)
            .finish_non_exhaustive()
    }
}

/// A candidate's score — `(end position, success beats error, priority)`, compared
/// lexicographically (`Basic.lean:1418`).
///
/// A named type rather than a bare tuple so the ordering is stated once and the components
/// cannot be silently reordered. The order *is* the rule: a longer parse beats a shorter one
/// even when the shorter one succeeded and the longer one failed, which is the component pair
/// most likely to be got backwards.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Score {
    pub end: usize,
    /// 1 for success, 0 for error — so that success sorts above error at equal position.
    pub succeeded: u8,
    pub priority: u32,
}

impl Score {
    pub fn of(state: &ParserState, priority: u32) -> Score {
        Score {
            end: state.pos().0,
            succeeded: u8::from(!state.has_error()),
            priority,
        }
    }
}

/// `Lean.choiceKind` — the node an unresolved ambiguity becomes.
pub fn choice_kind() -> Name {
    Name::str(Name::anonymous(), "choice")
}

/// `Lean.nullKind` — the node a production that pushed the wrong number of results becomes.
pub fn null_kind() -> Name {
    Name::str(Name::anonymous(), "null")
}

/// Run every applicable production and resolve between them — `longestMatchFn`
/// (`Basic.lean:1451`).
///
/// Each candidate runs from the same starting mark. The winner is the highest [`Score`]; **ties
/// are kept**, wrapped in a `choice` node, with the node's `lhs_prec` set to the minimum of the
/// tied candidates'.
///
/// `left` is the already-parsed left operand for a trailing production, pushed before each
/// candidate runs so every candidate sees the same input. Leading productions pass `None`.
pub fn longest_match(
    state: &mut ParserState,
    left: Option<Syntax>,
    productions: &[&Production],
) -> Resolution {
    if productions.is_empty() {
        state.set_error(ParseError::new("longestMatch: empty list", state.pos()));
        return Resolution::None;
    }

    let start_size = state.stack_size();
    let start_pos = state.pos();
    let start_lhs_prec = state.lhs_prec();

    // `runLongestMatchParser` initialises `lhsPrec` to `maxPrec` in the leading case, because a
    // leading production has no left-hand side to inherit from and nothing will read the field
    // before it is set.
    let entry_lhs_prec = if left.is_some() {
        start_lhs_prec
    } else {
        MAX_PREC
    };

    let mut best: Option<(Score, Vec<Syntax>, Prec, Option<ParseError>)> = None;
    let mut tied: Vec<Syntax> = Vec::new();
    let mut tied_lhs_prec = MAX_PREC;

    for production in productions.iter().copied() {
        state.restore(start_size, start_pos);
        state.set_lhs_prec(entry_lhs_prec);
        if let Some(left) = &left {
            state.push(left.clone());
        }
        (production.run)(state);

        let score = Score::of(state, production.priority);
        let produced: Vec<Syntax> = state.stack()[start_size.min(state.stack_size())..].to_vec();
        let error = state.error().cloned();
        let lhs_prec = state.lhs_prec();

        let Some(best_entry) = &mut best else {
            best = Some((score, produced, lhs_prec, error));
            tied.clear();
            tied_lhs_prec = lhs_prec;
            continue;
        };
        match score.cmp(&best_entry.0) {
            std::cmp::Ordering::Greater => {
                *best_entry = (score, produced, lhs_prec, error);
                tied.clear();
                tied_lhs_prec = lhs_prec;
            }
            std::cmp::Ordering::Equal => {
                // A successful tie preserves every alternative under a choice node. A failing
                // tie remains one failure but merges the expected alternatives, exactly as
                // `ParserState.mergeErrors` does at the pin.
                match (&best_entry.3, &error) {
                    (None, None) => {
                        if tied.is_empty() {
                            tied.extend(best_entry.1.iter().cloned());
                        }
                        tied.extend(produced.iter().cloned());
                        tied_lhs_prec = tied_lhs_prec.min(lhs_prec);
                    }
                    (Some(old_error), Some(new_error)) => {
                        let merged = old_error.merge(new_error);
                        best_entry.3 = Some(merged);
                    }
                    // `Score::succeeded` is derived from `has_error`, so these cases cannot
                    // arise from the current state representation. Keep the resolver total if
                    // those representations are ever decoupled: retain an established error,
                    // or adopt the only error available.
                    (Some(_), None) => {}
                    (None, Some(new_error)) => best_entry.3 = Some(new_error.clone()),
                }
            }
            std::cmp::Ordering::Less => {}
        }
    }

    let Some((score, produced, lhs_prec, error)) = best else {
        return Resolution::None;
    };

    state.restore(start_size, start_pos);
    if tied.len() > 1 {
        // The choice node sits at the WINNER's end, not at the start. Found by parser_fuzz:
        // `restore` puts the position back, and the ambiguous path never moved it forward, so an
        // ambiguity left the cursor where the candidates began. The Pratt loop's no-progress guard
        // would then stop the trailing chain and the rest of the expression would vanish — a
        // silently truncated parse, on exactly the inputs where the language needs the elaborator
        // to choose. Upstream keeps the winning state throughout `longestMatchStep`, so its
        // position was never lost there in the first place.
        state.set_pos(BytePos(score.end));
        state.set_lhs_prec(tied_lhs_prec);
        let kinds = tied.len();
        state.push(Syntax::node(choice_kind(), tied));
        return Resolution::Ambiguous {
            alternatives: kinds,
        };
    }

    state.set_pos(BytePos(score.end));
    state.set_lhs_prec(lhs_prec);
    for node in produced {
        state.push(node);
    }
    match error {
        Some(error) => {
            state.set_error(error);
            Resolution::Failed
        }
        None => Resolution::Unique,
    }
}

/// What [`longest_match`] decided.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Resolution {
    /// One production won outright.
    Unique,
    /// Several tied and were preserved under a `choice` node.
    Ambiguous { alternatives: usize },
    /// The best candidate failed; its error is on the state.
    Failed,
    /// There were no productions to try.
    None,
}

/// `mkResult` (`Basic.lean:1903`): a production must leave exactly one node above the mark. If
/// it left a different number, the results are wrapped in a `null` node.
///
/// Not an error, deliberately — upstream's own comment there reads "throw error instead?", so
/// this is a place the Reference is unsure and we match its behaviour rather than its doubt.
pub fn make_result(state: &mut ParserState, mark: usize) {
    if state.stack_size() == mark + 1 {
        return;
    }
    let nodes: Vec<Syntax> = state.stack()[mark.min(state.stack_size())..].to_vec();
    state.shrink(mark);
    state.push(Syntax::node(null_kind(), nodes));
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_syntax::source::{ByteSpan, SourceInfo};

    fn name(text: &str) -> Name {
        Name::str(Name::anonymous(), text)
    }

    /// An atom carrying a span, so tests can tell nodes apart and check what was consumed.
    fn atom(text: &str, from: usize, to: usize) -> Syntax {
        Syntax::atom(
            SourceInfo::Original {
                leading: ByteSpan::empty_at(BytePos(from)),
                pos: BytePos(from),
                trailing: ByteSpan::empty_at(BytePos(to)),
                end_pos: BytePos(to),
            },
            text,
        )
    }

    /// A one-line description of a node, so a wrong shape shows up as a value diff rather than
    /// a panic inside a match arm — the same reason the lexer suites classify instead of assert.
    fn describe(node: Option<&Syntax>) -> String {
        match node {
            Some(Syntax::Atom { val, .. }) => format!("atom {val}"),
            Some(Syntax::Node { kind, args, .. }) => {
                format!("node {}[{}]", kind.to_display_string(), args.len())
            }
            Some(Syntax::Ident { .. }) => "ident".to_string(),
            Some(Syntax::Missing) => "missing".to_string(),
            None => "nothing".to_string(),
        }
    }

    /// A production that consumes to `end`, pushes one atom, and succeeds.
    fn consuming(kind: &str, priority: u32, end: usize) -> Production {
        let label = kind.to_string();
        Production::new(name(kind), priority, move |state| {
            let from = state.pos().0;
            state.set_pos(BytePos(end));
            state.push(atom(&label, from, end));
        })
    }

    /// A production that consumes to `end` and then fails.
    fn failing(kind: &str, priority: u32, end: usize) -> Production {
        Production::new(name(kind), priority, move |state| {
            state.set_pos(BytePos(end));
            state.set_error(ParseError::consuming("no", BytePos(end)));
        })
    }

    /// A production that contributes one expected alternative before failing.
    fn expecting_failure(kind: &str, expected: &str, priority: u32, end: usize) -> Production {
        let expected = expected.to_string();
        Production::new(name(kind), priority, move |state| {
            state.set_pos(BytePos(end));
            state.set_error(ParseError::consuming_expecting(
                expected.clone(),
                BytePos(end),
            ));
        })
    }

    fn run(productions: &[Production]) -> (Resolution, ParserState) {
        let borrowed: Vec<&Production> = productions.iter().collect();
        let mut state = ParserState::new(0);
        let resolution = longest_match(&mut state, None, &borrowed);
        (resolution, state)
    }

    /// **The score is lexicographic, and position dominates.** A longer parse beats a shorter
    /// one, and it does so even when the shorter one *succeeded* and the longer one failed —
    /// the component pair most likely to be got backwards, because "prefer the one that worked"
    /// is the intuitive rule and not the pin's.
    #[test]
    fn a_longer_parse_beats_a_shorter_one_even_if_the_longer_one_failed() {
        let (resolution, state) = run(&[consuming("short", 0, 3), failing("long", 0, 9)]);
        assert_eq!(
            resolution,
            Resolution::Failed,
            "the longer, failing candidate must win"
        );
        assert_eq!(state.pos(), BytePos(9));

        // And with the order reversed, so the answer is not an artefact of iteration order.
        let (resolution, state) = run(&[failing("long", 0, 9), consuming("short", 0, 3)]);
        assert_eq!(resolution, Resolution::Failed);
        assert_eq!(state.pos(), BytePos(9));
    }

    /// At equal position, success beats error. This is the second component, and it only ever
    /// decides anything when the first is tied — which is why it is asserted at equal length.
    #[test]
    fn at_equal_length_success_beats_error() {
        for productions in [
            vec![consuming("ok", 0, 5), failing("bad", 0, 5)],
            vec![failing("bad", 0, 5), consuming("ok", 0, 5)],
        ] {
            let (resolution, state) = run(&productions);
            assert_eq!(
                resolution,
                Resolution::Unique,
                "success must win at equal end"
            );
            assert_eq!(state.pos(), BytePos(5));
            assert!(!state.has_error());
        }
    }

    /// Priority is the third and weakest component: it decides only when position and success
    /// are both tied. A parser that consulted priority first would pick the wrong production
    /// whenever a lower-priority one matched further.
    #[test]
    fn priority_decides_only_after_position_and_success() {
        // Position beats priority: the low-priority production matches further and wins.
        let (_, state) = run(&[consuming("high", 100, 2), consuming("low", 1, 8)]);
        assert_eq!(
            state.pos(),
            BytePos(8),
            "a longer match must beat a higher priority"
        );

        // Success beats priority.
        let (resolution, _) = run(&[failing("high", 100, 5), consuming("low", 1, 5)]);
        assert_eq!(
            resolution,
            Resolution::Unique,
            "a successful match must beat a higher-priority failure"
        );

        // With both tied, priority decides — and the winner is unique, not a choice node.
        let (resolution, state) = run(&[consuming("high", 100, 5), consuming("low", 1, 5)]);
        assert_eq!(resolution, Resolution::Unique);
        assert_eq!(state.stack_size(), 1);
        assert_eq!(
            describe(state.back()),
            "atom high",
            "with position and success tied, the higher priority wins"
        );
    }

    /// **THE MOST CONSEQUENTIAL RULE.** A genuine tie is *preserved* under a `choice` node, not
    /// resolved by picking one.
    ///
    /// A parser that took the first winner would produce a perfectly well-formed tree with an
    /// ambiguity silently discarded — and the elaborator, which is what resolves ambiguity in
    /// this language, would never learn there was a decision to make. Nothing downstream can
    /// detect the loss, which is why it is asserted here at the only place it is visible.
    #[test]
    fn a_genuine_tie_is_preserved_as_a_choice_node() {
        let (resolution, state) = run(&[consuming("a", 7, 5), consuming("b", 7, 5)]);
        assert_eq!(
            resolution,
            Resolution::Ambiguous { alternatives: 2 },
            "equal position, both successful, equal priority: this is an ambiguity"
        );
        assert_eq!(state.stack_size(), 1, "the choice node is one node");
        assert_eq!(
            state.pos(),
            BytePos(5),
            "the choice node sits at the winner's end. With the position left at the start, the \
             Pratt loop's no-progress guard stops the chain and truncates the parse — found by \
             parser_fuzz rather than here, which is why the assertion exists now."
        );
        assert_eq!(
            describe(state.back()),
            "node choice[2]",
            "both alternatives are kept under a choice node"
        );
    }

    /// A tie's `lhs_prec` is the **minimum** of the tied candidates'. Upstream takes the minimum
    /// conservatively because the right answer is unclear; taking the maximum would let a
    /// trailing production consume a choice node it must not.
    #[test]
    fn a_choice_nodes_precedence_is_the_minimum_of_its_alternatives() {
        let tight = Production::new(name("tight"), 5, |state| {
            state.set_pos(BytePos(4));
            state.set_lhs_prec(MAX_PREC);
            state.push(atom("tight", 0, 4));
        });
        let loose = Production::new(name("loose"), 5, |state| {
            state.set_pos(BytePos(4));
            state.set_lhs_prec(17);
            state.push(atom("loose", 0, 4));
        });

        let mut state = ParserState::new(0);
        let resolution = longest_match(&mut state, None, &[&tight, &loose]);
        assert_eq!(resolution, Resolution::Ambiguous { alternatives: 2 });
        assert_eq!(
            state.lhs_prec(),
            17,
            "the minimum, not the maximum and not the last one seen"
        );
    }

    /// Every candidate runs from the same mark, so an earlier candidate cannot leave residue on
    /// the stack for a later one to inherit.
    #[test]
    fn each_candidate_starts_from_the_same_mark() {
        let messy = Production::new(name("messy"), 0, |state| {
            state.push(atom("junk", 0, 1));
            state.push(atom("more junk", 1, 2));
            state.set_pos(BytePos(2));
            state.set_error(ParseError::consuming("no", BytePos(2)));
        });
        let clean = consuming("clean", 0, 6);

        let mut state = ParserState::new(0);
        state.push(atom("pre-existing", 0, 0));
        let before = state.stack_size();
        let resolution = longest_match(&mut state, None, &[&messy, &clean]);

        assert_eq!(resolution, Resolution::Unique);
        assert_eq!(
            state.stack_size(),
            before + 1,
            "the winner leaves exactly one node above the mark, and the loser's junk is gone"
        );
        assert_eq!(
            describe(state.back()),
            "atom clean",
            "the winner is on the stack and the loser's junk is gone"
        );
    }

    /// A trailing production sees the left operand, and every candidate sees the *same* one.
    #[test]
    fn a_trailing_candidate_receives_the_left_operand() {
        let left = atom("left", 0, 4);
        let count_left = Production::new(name("count"), 0, |state| {
            // The left operand is on the stack when the production runs.
            assert_eq!(state.stack_size(), 1, "left operand must be present");
            state.set_pos(BytePos(8));
            let popped = state.pop().expect("left operand");
            state.push(Syntax::node(name("applied"), vec![popped]));
        });
        let other = Production::new(name("other"), 0, |state| {
            assert_eq!(
                state.stack_size(),
                1,
                "left operand must be present here too"
            );
            state.set_pos(BytePos(6));
        });

        let mut state = ParserState::new(0);
        let resolution = longest_match(&mut state, Some(left.clone()), &[&count_left, &other]);
        assert_eq!(resolution, Resolution::Unique);
        assert_eq!(state.pos(), BytePos(8));
    }

    /// A leading candidate enters with `lhs_prec = MAX_PREC`; a trailing one inherits the
    /// state's. Upstream sets this in `runLongestMatchParser` and explains why: a leading parser
    /// has no left-hand side to inherit from.
    #[test]
    fn a_leading_candidate_enters_at_max_prec_and_a_trailing_one_inherits() {
        let observed = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));

        let seen = std::sync::Arc::clone(&observed);
        let probe = Production::new(name("probe"), 0, move |state| {
            seen.lock().expect("lock").push(state.lhs_prec());
            state.set_pos(BytePos(1));
            state.push(atom("p", 0, 1));
        });
        let mut state = ParserState::new(0);
        state.set_lhs_prec(42);
        longest_match(&mut state, None, &[&probe]);
        assert_eq!(
            observed.lock().expect("lock").as_slice(),
            &[MAX_PREC],
            "a leading candidate enters at maxPrec regardless of the state's lhs_prec"
        );

        observed.lock().expect("lock").clear();
        let mut state = ParserState::new(0);
        state.set_lhs_prec(42);
        longest_match(&mut state, Some(atom("left", 0, 0)), &[&probe]);
        assert_eq!(
            observed.lock().expect("lock").as_slice(),
            &[42],
            "a trailing candidate inherits the state's lhs_prec"
        );
    }

    /// The precedence checks, in the direction the pin has them — and the message verbatim.
    #[test]
    fn the_precedence_checks_run_in_the_pins_direction() {
        // checkPrec succeeds when the CONTEXT's demand is at most the production's level.
        let mut state = ParserState::new(65);
        assert!(state.check_prec(65), "equal is allowed");
        assert!(!state.has_error());
        assert!(
            state.check_prec(70),
            "a higher-precedence production applies"
        );
        let mut state = ParserState::new(65);
        assert!(
            !state.check_prec(64),
            "a production below the context's demand does not apply"
        );
        assert_eq!(state.error().expect("an error").message(), PREC_MESSAGE);

        // checkLhsPrec succeeds when what was just parsed binds at least as tightly.
        let mut state = ParserState::new(0);
        state.set_lhs_prec(50);
        assert!(state.check_lhs_prec(50));
        assert!(state.check_lhs_prec(49));
        assert!(!state.check_lhs_prec(51));
        assert_eq!(state.error().expect("an error").message(), PREC_MESSAGE);
    }

    #[test]
    fn parse_error_rendering_matches_the_pins_expected_list_grammar() {
        let none = ParseError::with_expected("", std::iter::empty::<&str>(), BytePos(0), false);
        assert_eq!(none.message(), "");

        let one = ParseError::expecting("term", BytePos(0));
        assert_eq!(one.message(), "expected term");

        let two = ParseError::with_expected("", ["term", "identifier"], BytePos(0), false);
        assert_eq!(two.message(), "expected identifier or term");

        let many = ParseError::with_expected(
            "unexpected token '?'",
            ["term", "numeral", "identifier", "term"],
            BytePos(0),
            true,
        );
        assert_eq!(
            many.message(),
            "unexpected token '?'; expected identifier, numeral or term"
        );
    }

    #[test]
    fn merging_errors_keeps_the_newest_nonempty_unexpected_description() {
        let older = ParseError::with_expected("unexpected old token", ["term"], BytePos(1), false);
        let newer_without_unexpected =
            ParseError::with_expected("", ["identifier"], BytePos(2), true);
        let merged = older.merge(&newer_without_unexpected);
        assert_eq!(merged.unexpected(), "unexpected old token");
        assert_eq!(
            merged.message(),
            "unexpected old token; expected identifier or term"
        );
        assert_eq!(merged.at, BytePos(2));
        assert!(merged.consumed);

        let newest =
            ParseError::with_expected("unexpected new token", ["numeral"], BytePos(3), false);
        let merged = merged.merge(&newest);
        assert_eq!(merged.unexpected(), "unexpected new token");
        assert_eq!(
            merged.message(),
            "unexpected new token; expected identifier, numeral or term"
        );
        assert_eq!(merged.at, BytePos(3));
    }

    #[test]
    fn tied_failures_preserve_every_expected_alternative_in_any_order() {
        let cases: &[(&[&str], &str)] = &[
            (&["term", "identifier"], "expected identifier or term"),
            (&["identifier", "term"], "expected identifier or term"),
            (
                &["term", "identifier", "numeral"],
                "expected identifier, numeral or term",
            ),
            (
                &["numeral", "term", "identifier"],
                "expected identifier, numeral or term",
            ),
        ];
        for (expected, rendered) in cases {
            let productions: Vec<Production> = expected
                .iter()
                .map(|item| expecting_failure(item, item, 7, 5))
                .collect();
            let (resolution, state) = run(&productions);
            assert_eq!(resolution, Resolution::Failed);
            assert_eq!(state.error().expect("merged error").message(), *rendered);
        }
    }

    #[test]
    fn unequal_failure_scores_select_one_error_instead_of_merging() {
        for productions in [
            vec![
                expecting_failure("short", "shorter", 99, 4),
                expecting_failure("long", "longer", 1, 8),
            ],
            vec![
                expecting_failure("long", "longer", 1, 8),
                expecting_failure("short", "shorter", 99, 4),
            ],
        ] {
            let (resolution, state) = run(&productions);
            assert_eq!(resolution, Resolution::Failed);
            assert_eq!(
                state.error().expect("winning error").message(),
                "expected longer"
            );
        }
    }

    /// Two candidates that both fail at the same position are one error, not an ambiguity.
    ///
    /// Asserted next to the choice-node test because the two cases look alike from the score's
    /// point of view and differ entirely in what they should produce. A parser that built a
    /// choice node out of two failures would hand the elaborator a node full of nothing.
    #[test]
    fn two_failures_at_the_same_position_are_not_an_ambiguity() {
        let (resolution, state) = run(&[failing("a", 7, 5), failing("b", 7, 5)]);
        assert_eq!(
            resolution,
            Resolution::Failed,
            "two failures are a failure, not a choice"
        );
        assert!(state.has_error());
        assert_ne!(
            describe(state.back()),
            "node choice[2]",
            "no choice node may be built from failures"
        );
    }

    /// An empty production list is a typed refusal, not a panic and not a silent success.
    #[test]
    fn no_productions_is_a_refusal() {
        let (resolution, state) = run(&[]);
        assert_eq!(resolution, Resolution::None);
        assert!(state.has_error());
        assert_eq!(state.stack_size(), 0);
    }

    /// `mkResult`: exactly one node above the mark passes through; anything else is wrapped in a
    /// `null` node rather than being an error.
    #[test]
    fn a_production_leaving_the_wrong_count_is_wrapped_in_a_null_node() {
        // Exactly one: untouched.
        let mut state = ParserState::new(0);
        state.push(atom("a", 0, 1));
        make_result(&mut state, 0);
        assert_eq!(state.stack_size(), 1);
        assert_eq!(describe(state.back()), "atom a", "one node passes through");

        // Two: wrapped.
        let mut state = ParserState::new(0);
        state.push(atom("a", 0, 1));
        state.push(atom("b", 1, 2));
        make_result(&mut state, 0);
        assert_eq!(state.stack_size(), 1);
        assert_eq!(
            describe(state.back()),
            "node null[2]",
            "two nodes are wrapped"
        );

        // Zero: also wrapped, holding nothing.
        let mut state = ParserState::new(0);
        make_result(&mut state, 0);
        assert_eq!(state.stack_size(), 1);
        assert_eq!(
            describe(state.back()),
            "node null[0]",
            "zero nodes are wrapped too"
        );
    }
}
