//! Exact `Syntax` construction from lexer tokens (plan §9; bead fln-ffam).
//!
//! ## The rule: carry the extents, never rebuild the spans
//!
//! A leaf's [`SourceInfo`] is **taken from the attachment**, which took it from the lexer. It is
//! never recomputed from where a production happened to start and stop consuming.
//!
//! The reason this needs saying is that the wrong version *looks right*. A production that
//! recorded "I began at 4 and ended at 11" produces spans that are internally consistent, tile
//! the file with no gaps, and therefore **round-trip perfectly**. Reconstruction cannot tell the
//! difference. They are wrong only where reconstruction and reality diverge:
//!
//! * A token's `pos` is what a diagnostic underlines. Rebuild it from the consumption cursor and
//!   it drifts onto the leading trivia — the caret lands on the whitespace or the comment before
//!   the token, and every byte still reconstructs.
//! * Trivia *ownership* is a rule of its own (`chooseNiceTrailStop`, implemented and
//!   plant-proved in `fln_syntax::attach` under bead franken_lean-tkr2). A production that
//!   re-derives it has a second implementation of that rule, and the two drift.
//!
//! So the round-trip property in this module is necessary and **not sufficient**, and it says so
//! where it is asserted. The assertions that actually pin exactness compare each leaf's `pos` and
//! `end_pos` against the **lexer's** token extents.
//!
//! ## Lossless means recoverable through the crlfToLf map
//!
//! Held literally, per franken_lean-tkr2. The lexer runs on the *normalized* view
//! (`String.crlfToLf`), so every position a leaf holds is a **view** position, and a tree's
//! reconstruction reproduces the **view**, not the file. Recovering the file is
//! [`SourceView::reconstruct_original`]'s job.
//!
//! A round-trip test written against raw bytes therefore has exactly two futures: it fails on
//! every CRLF file, or it gets quietly relaxed until it passes. This module asserts the correct
//! chain — and, in the same test, asserts that the *raw* comparison **fails** for a CRLF file, so
//! the map is demonstrably load-bearing rather than incidentally satisfied.

use fln_core::name::Name;
use fln_syntax::attach::{Attached, Attachment, TokenExtent, attach};
use fln_syntax::source::{ByteSpan, SourceText};
use fln_syntax::token::{LexedToken, TokenKind};
use fln_syntax::tree::Syntax;

/// Why construction refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuildError {
    /// The token extents could not be attached — ascending/overlap/boundary rules.
    Attach(fln_syntax::attach::AttachError),
    /// A leaf was requested for a token index the run does not have.
    NoSuchToken { index: usize },
}

/// The leaves of a parse, with exact source info, indexed as the lexer produced them.
///
/// Built once from the attachment and then handed out. A production asks for leaf `i`; it does
/// not get to describe one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Leaves {
    leaves: Vec<Syntax>,
    /// The lexer's own extents, kept so exactness can be *checked* rather than trusted.
    extents: Vec<ByteSpan>,
    attachment: Attachment,
}

impl Leaves {
    /// Build every leaf from the lexer's tokens and the trivia attachment.
    ///
    /// `tokens` are the lexer's, in order. The `SourceInfo` of each leaf comes from
    /// [`attach`] — the same function whose trivia-ownership rule was plant-proved in
    /// franken_lean-tkr2 — so there is exactly one implementation of that rule in the program.
    pub fn build(text: &SourceText, tokens: &[LexedToken]) -> Result<Leaves, BuildError> {
        let extents: Vec<ByteSpan> = tokens.iter().map(|token| token.extent).collect();
        let requested: Vec<TokenExtent> =
            extents.iter().copied().map(TokenExtent::Present).collect();
        let attachment = attach(text, &requested).map_err(BuildError::Attach)?;

        let leaves = attachment
            .entries()
            .iter()
            .zip(tokens.iter())
            .map(|(entry, token)| leaf_for(text, *entry, token))
            .collect();

        Ok(Leaves {
            leaves,
            extents,
            attachment,
        })
    }

    /// The leaf for token `index`.
    pub fn leaf(&self, index: usize) -> Result<Syntax, BuildError> {
        self.leaves
            .get(index)
            .cloned()
            .ok_or(BuildError::NoSuchToken { index })
    }

    pub fn len(&self) -> usize {
        self.leaves.len()
    }

    pub fn is_empty(&self) -> bool {
        self.leaves.is_empty()
    }

    /// The lexer's extent for token `index` — the thing a leaf's position must equal.
    pub fn extent(&self, index: usize) -> Option<ByteSpan> {
        self.extents.get(index).copied()
    }

    pub fn attachment(&self) -> &Attachment {
        &self.attachment
    }

    /// Every leaf, in lexer order.
    pub fn all(&self) -> &[Syntax] {
        &self.leaves
    }
}

/// One leaf, with its `SourceInfo` taken from the attachment entry.
///
/// The only arithmetic here is reading fields out of the entry. That is the point: there is
/// nowhere for a coordinate-space mistake to happen, because no coordinate is computed.
fn leaf_for(text: &SourceText, entry: Attached, token: &LexedToken) -> Syntax {
    let info = match entry {
        Attached::Token(info) => info,
        // A missing token has no extent to carry; upstream's `Syntax.missing` holds no info.
        Attached::Missing { .. } => return Syntax::Missing,
    };
    match &token.kind {
        // `raw_val` is a ByteSpan, and it is the lexer's extent verbatim. Upstream holds the
        // substring; ours holds the span for the reason ByteSpan itself documents — carrying a
        // copy of the text would let a span and its text disagree about which text they are.
        // Either way it is CARRIED, not rebuilt.
        TokenKind::Ident(name) => Syntax::Ident {
            info,
            raw_val: token.extent,
            val: name.clone(),
            preresolved: Vec::new(),
        },
        TokenKind::Symbol(symbol) => Syntax::atom(info, symbol.clone()),
        // A literal's atom value is its source text: upstream's `mkNodeToken` uses
        // `c.extract startPos stopPos`, the raw slice, not a normalized rendering of the value.
        TokenKind::Literal(_) => Syntax::atom(info, slice_of(text, token.extent)),
    }
}

/// The source slice a span covers — used only for atom values, which upstream stores as text.
fn slice_of(text: &SourceText, span: ByteSpan) -> String {
    text.as_str()
        .get(span.start().0..span.end().0)
        .unwrap_or_default()
        .to_string()
}

/// A node built over leaves, with **no source info of its own**.
///
/// Upstream's `Syntax.node` carries no position: a node's span is derived from its arguments
/// (asserted in `fln_syntax::tree`'s "an interior node's own info contributes nothing"). Storing
/// one here would be a second place for a span to live and therefore a second place for it to be
/// wrong.
pub fn node(kind: Name, args: Vec<Syntax>) -> Syntax {
    Syntax::node(kind, args)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_syntax::run::{Event, lex_run};
    use fln_syntax::source::{BytePos, SourceInfo};
    use fln_syntax::token::TokenTable;
    use fln_syntax::view::SourceView;

    /// Report a non-Original leaf as a value comparison rather than a panic, for the same reason
    /// the lexer suites classify instead of matching with a failing arm.
    fn unreachable_info(context: &str, index: usize, info: SourceInfo) {
        assert_eq!(
            format!("{info:?}"),
            "Original",
            "{context}: leaf {index} must carry Original source info"
        );
    }

    fn describe(node: &Syntax) -> String {
        match node {
            Syntax::Atom { .. } => "atom".to_string(),
            Syntax::Ident { .. } => "ident".to_string(),
            Syntax::Node { kind, .. } => format!("node {}", kind.to_display_string()),
            Syntax::Missing => "missing".to_string(),
        }
    }

    fn atom_value(node: &Syntax) -> Option<String> {
        match node {
            Syntax::Atom { val, .. } => Some(val.clone()),
            _ => None,
        }
    }

    fn table() -> TokenTable {
        TokenTable::from_tokens(["def", ":=", "+", "(", ")", "theorem", "fun", "=>"])
    }

    /// Lex `raw` through the view and return the view text plus the tokens, which is the only
    /// entry point a parser should ever have: the lexer consumes the NORMALIZED view.
    fn lex_view(raw: &str) -> (SourceView, Vec<LexedToken>) {
        let original = SourceText::from_utf8(raw.as_bytes()).expect("valid UTF-8");
        let view = SourceView::of(&original);
        let run = lex_run(view.normalized(), &table());
        let tokens = run
            .events
            .iter()
            .filter_map(|event| match event {
                Event::Token(token) => Some(token.clone()),
                _ => None,
            })
            .collect();
        (view, tokens)
    }

    fn leaves_of(raw: &str) -> (SourceView, Vec<LexedToken>, Leaves) {
        let (view, tokens) = lex_view(raw);
        let leaves =
            Leaves::build(view.normalized(), &tokens).expect("the lexer's extents must attach");
        (view, tokens, leaves)
    }

    /// **THE EXACTNESS ASSERTION, and the one reconstruction cannot make.**
    ///
    /// Every leaf's `pos` and `end_pos` equal the **lexer's** token extent — not the region a
    /// production consumed, and not the region including leading trivia.
    ///
    /// This is the test that catches rebuilt spans. Rebuilt spans are internally consistent and
    /// round-trip perfectly, so no reconstruction test can see them; they differ only in *where
    /// the token is*, which is what a diagnostic underlines.
    #[test]
    fn every_leaf_carries_the_lexers_extent_not_a_rebuilt_one() {
        for raw in [
            "def f := 1 + 2\n",
            "  def   f  :=  1\n",
            "-- a comment\ndef f := 1\n",
            "def f := 1 /- inline -/ + 2\n",
            "def f := \"str\" + 1\n",
        ] {
            let (_, tokens, leaves) = leaves_of(raw);
            assert_eq!(leaves.len(), tokens.len(), "{raw:?}: a leaf per token");

            for (index, token) in tokens.iter().enumerate() {
                let leaf = leaves.leaf(index).expect("leaf");
                let info = leaf.info();
                let SourceInfo::Original { pos, end_pos, .. } = info else {
                    unreachable_info(raw, index, info);
                    continue;
                };
                assert_eq!(
                    (pos, end_pos),
                    (token.extent.start(), token.extent.end()),
                    "{raw:?}: leaf {index} must carry the LEXER's extent. A span rebuilt from a \
                     consumption cursor would still reconstruct correctly and would put the \
                     caret on the trivia before the token."
                );
            }
        }
    }

    /// The leading trivia is a *separate* field from the token's position, and where a token has
    /// leading trivia the two genuinely differ. If `pos` were rebuilt from where consumption
    /// began, they would be equal — the defect, and one no reconstruction test can see.
    ///
    /// The fixture spans a newline on purpose, and my first attempt at it was WRONG in a way worth
    /// recording: I used `def    f` and expected `f` to have four spaces of leading trivia. It has
    /// none. `chooseNiceTrailStop` (franken_lean-tkr2) attaches same-line whitespace BACKWARD, as
    /// the previous token's *trailing* trivia, so leading trivia only exists after a newline. The
    /// attachment layer corrected the test rather than the test being relaxed to fit.
    #[test]
    fn a_tokens_position_is_not_the_start_of_its_leading_trivia() {
        let raw = "def\n    f := 1\n";
        let (_, tokens, leaves) = leaves_of(raw);

        // Find a token that actually has leading trivia, rather than assuming which one does.
        let with_leading: Vec<usize> = (0..leaves.len())
            .filter(|index| {
                matches!(
                    leaves.leaf(*index).expect("leaf").info(),
                    SourceInfo::Original { leading, .. } if leading.len_bytes() > 0
                )
            })
            .collect();
        assert!(
            !with_leading.is_empty(),
            "the fixture must contain a token with leading trivia, or this proves nothing. \
             Same-line whitespace attaches BACKWARD as the previous token's trailing, so the \
             fixture has to span a newline."
        );

        for index in with_leading {
            let info = leaves.leaf(index).expect("leaf").info();
            let SourceInfo::Original { leading, pos, .. } = info else {
                unreachable_info("leading-trivia fixture", index, info);
                continue;
            };
            assert_ne!(
                leading.start(),
                pos,
                "leaf {index}: the token's position must not be the start of its leading trivia"
            );
            assert_eq!(
                pos,
                tokens[index].extent.start(),
                "leaf {index}: and it must be exactly the lexer's extent start"
            );
            assert_eq!(
                leading.end(),
                pos,
                "leaf {index}: the leading trivia must abut the token, with no gap"
            );
        }
    }

    /// **THE ROUND TRIP, held literally: through the crlfToLf map.**
    ///
    /// The chain is: raw bytes -> view -> lex -> attach -> tree -> reconstruct the VIEW ->
    /// `reconstruct_original` -> raw bytes.
    ///
    /// And in the same test, the raw comparison is asserted to **fail** for a CRLF file. Without
    /// that half, a test written against raw bytes has two futures — it fails on every CRLF file,
    /// or it gets relaxed until it passes — and neither tells anyone that the map is load-bearing.
    #[test]
    fn a_tree_reconstructs_the_view_and_the_view_reconstructs_the_file() {
        for raw in [
            "def f := 1 + 2\n",
            "def f := 1\r\ndef g := 2\r\n",
            "-- c\r\ndef f := 1\r\n",
            "def f := 1\rdef g := 2\n",
            "def f := 1",
            "\r\n\r\ndef f := 1\r\n",
        ] {
            let original = SourceText::from_utf8(raw.as_bytes()).expect("valid UTF-8");
            let view = SourceView::of(&original);
            let (_, tokens) = lex_view(raw);
            let leaves = Leaves::build(view.normalized(), &tokens).expect("attaches");

            // A flat tree over every leaf: construction, not parsing, is what is under test.
            let tree = node(Name::str(Name::anonymous(), "file"), leaves.all().to_vec());

            let view_bytes = tree
                .reconstruct(view.normalized(), leaves.attachment().epilogue())
                .expect("the tree must reconstruct the view it was built from");
            assert_eq!(
                view_bytes,
                view.normalized().as_bytes(),
                "{raw:?}: the tree reconstructs the VIEW byte for byte"
            );

            // And the view reconstructs the file.
            assert_eq!(
                view.reconstruct_original(),
                raw.as_bytes(),
                "{raw:?}: the view reconstructs the original bytes"
            );

            // THE OTHER HALF. For a file that was normalized, the tree's own reconstruction is
            // NOT the file — so a round-trip written against raw bytes would be wrong here.
            if view.normalized_anything() {
                assert_ne!(
                    view_bytes,
                    raw.as_bytes(),
                    "{raw:?}: this file WAS normalized, so the tree's reconstruction must differ \
                     from the raw bytes. If these were equal the crlfToLf map would be doing \
                     nothing and the test would prove nothing."
                );
            }
        }
    }

    /// A leaf's position maps back through the view onto the byte a user would see. This is the
    /// case where "reconstruction and reality diverge": in a CRLF file the view offset and the
    /// file offset are different numbers, and a diagnostic must use the second.
    #[test]
    fn a_leaf_position_maps_back_to_the_original_byte() {
        let raw = "def f := 1\r\ndef g := 2\r\n";
        let original = SourceText::from_utf8(raw.as_bytes()).expect("valid");
        let view = SourceView::of(&original);
        let (_, tokens) = lex_view(raw);
        let leaves = Leaves::build(view.normalized(), &tokens).expect("attaches");

        // The `g` on the second line: its view offset is one less than its file offset, because
        // the first line's CRLF became one byte.
        let index = tokens
            .iter()
            .position(|token| matches!(&token.kind, TokenKind::Ident(name) if name.to_display_string() == "g"))
            .expect("the fixture has `g`");
        let leaf = leaves.leaf(index).expect("leaf");
        let info = leaf.info();
        let SourceInfo::Original { pos, .. } = info else {
            unreachable_info("crlf fixture", index, info);
            return;
        };

        let in_file = view.to_original(pos);
        assert_ne!(
            in_file.0, pos.0,
            "the fixture must put `g` after a CRLF, or the mapping is untested"
        );
        assert_eq!(
            &raw[in_file.0..in_file.0 + 1],
            "g",
            "the mapped position must land on `g` in the RAW bytes"
        );
        // And the unmapped view position does not, which is why the map is not optional.
        assert_ne!(
            &raw[pos.0..pos.0 + 1],
            "g",
            "the unmapped view position lands elsewhere in the raw bytes — this is the divergence \
             the map exists to bridge"
        );
    }

    /// A literal's atom value is its **source slice**, as `mkNodeToken` uses `c.extract`. A
    /// normalized rendering would lose the spelling — `0x1F` and `31` are the same value and
    /// different source.
    #[test]
    fn a_literal_leaf_holds_its_source_spelling() {
        let raw = "def f := 0x1F\n";
        let (_, tokens, leaves) = leaves_of(raw);
        let index = tokens
            .iter()
            .position(|token| matches!(token.kind, TokenKind::Literal(_)))
            .expect("the fixture has a literal");
        let leaf = leaves.leaf(index).expect("leaf");
        assert_eq!(
            atom_value(&leaf).as_deref(),
            Some("0x1F"),
            "a literal keeps its spelling, not a canonical rendering of its value"
        );
    }

    /// An identifier leaf carries both its raw spelling and the structural `Name` the lexer
    /// spelled — and the `Name` is the lexer's, not re-parsed from the text.
    #[test]
    fn an_identifier_leaf_carries_the_lexers_name() {
        let raw = "def Nat.succ := 1\n";
        let (_, tokens, leaves) = leaves_of(raw);
        let index = tokens
            .iter()
            .position(|token| matches!(&token.kind, TokenKind::Ident(name) if name.to_display_string() == "Nat.succ"))
            .expect("the fixture has a dotted identifier");
        let leaf = leaves.leaf(index).expect("leaf");
        let Syntax::Ident { raw_val, val, .. } = &leaf else {
            assert_eq!(describe(&leaf), "ident", "wanted an identifier leaf");
            return;
        };
        assert_eq!(
            *raw_val, tokens[index].extent,
            "raw_val is the LEXER's extent, carried verbatim"
        );
        assert_eq!(
            &raw[raw_val.start().0..raw_val.end().0],
            "Nat.succ",
            "and it slices the source spelling"
        );
        assert_eq!(val.to_display_string(), "Nat.succ", "the structural Name");
    }

    /// A node carries no source info of its own; its span comes from its arguments. A stored span
    /// would be a second place for a position to live and so a second place to be wrong.
    #[test]
    fn an_interior_node_stores_no_position() {
        let raw = "def f := 1\n";
        let (_, _, leaves) = leaves_of(raw);
        let inner = node(Name::str(Name::anonymous(), "inner"), leaves.all().to_vec());
        let outer = node(Name::str(Name::anonymous(), "outer"), vec![inner]);
        assert_eq!(
            outer.info(),
            SourceInfo::None,
            "an interior node must not store a position of its own"
        );
    }

    /// Construction refuses extents it cannot attach rather than repairing them. A repaired
    /// attachment is the failure mode that reconstructs cleanly and misplaces everything.
    #[test]
    fn extents_that_cannot_attach_are_refused() {
        let text = SourceText::from_utf8(b"abcdef").expect("valid");
        let descending = vec![
            LexedToken {
                kind: TokenKind::Symbol("b".to_string()),
                extent: ByteSpan::new(BytePos(3), BytePos(4)).expect("span"),
            },
            LexedToken {
                kind: TokenKind::Symbol("a".to_string()),
                extent: ByteSpan::new(BytePos(0), BytePos(1)).expect("span"),
            },
        ];
        assert!(
            matches!(
                Leaves::build(&text, &descending),
                Err(BuildError::Attach(_))
            ),
            "descending extents must be refused, not silently sorted"
        );
    }

    /// Asking for a leaf that does not exist is a typed refusal.
    #[test]
    fn a_missing_leaf_index_is_a_typed_refusal() {
        let (_, _, leaves) = leaves_of("def f := 1\n");
        assert_eq!(
            leaves.leaf(leaves.len()),
            Err(BuildError::NoSuchToken {
                index: leaves.len()
            })
        );
    }

    /// The empty file builds an empty leaf set and still round-trips.
    #[test]
    fn an_empty_file_builds_and_round_trips() {
        let original = SourceText::from_utf8(b"").expect("valid");
        let view = SourceView::of(&original);
        let leaves = Leaves::build(view.normalized(), &[]).expect("attaches");
        assert!(leaves.is_empty());
        let tree = node(Name::str(Name::anonymous(), "file"), Vec::new());
        assert_eq!(
            tree.reconstruct(view.normalized(), leaves.attachment().epilogue()),
            Some(Vec::new()),
            "an empty tree reconstructs an empty view"
        );
    }

    /// A file that is nothing but trivia has no leaves, and the bytes live in the attachment's
    /// epilogue. Asserted because it is the case where "the tree reconstructs the file" is true
    /// only if the epilogue is honoured.
    #[test]
    fn a_file_of_only_trivia_reconstructs_from_the_epilogue() {
        let raw = "-- just a comment\n";
        let original = SourceText::from_utf8(raw.as_bytes()).expect("valid");
        let view = SourceView::of(&original);
        let (_, tokens) = lex_view(raw);
        assert!(tokens.is_empty(), "the fixture must have no tokens");

        let leaves = Leaves::build(view.normalized(), &tokens).expect("attaches");
        let tree = node(Name::str(Name::anonymous(), "file"), leaves.all().to_vec());
        assert_eq!(
            tree.reconstruct(view.normalized(), leaves.attachment().epilogue()),
            Some(view.normalized().as_bytes().to_vec()),
            "the whole file is epilogue and must still reconstruct"
        );
    }
}
