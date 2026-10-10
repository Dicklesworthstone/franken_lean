//! Declaration modifiers after the attributes: the pin's `declModifiers` slots 2..6
//! (bead `franken_lean-z8j.1.10`, stage 2).
//!
//! `Lean/Parser/Command.lean:114` at the pin:
//!
//! ```text
//! def declModifiers (inline : Bool) := leading_parser
//!   optional docComment >>
//!   optional (Term.«attributes» >> ...) >>
//!   optional visibility >>               -- «private» <|> «public»
//!   optional «protected» >>
//!   optional («meta» <|> «noncomputable») >>
//!   optional «unsafe» >>
//!   optional («partial» <|> «nonrec»)
//! ```
//!
//! Each keyword is its own `leading_parser` node holding one atom (`Command.protected
//! "protected"`), and each slot is a null node holding that node or nothing. The order is fixed:
//! a modifier out of order is not consumed, so the declaration keyword is expected there and the
//! parse refuses at it, as the pin does.
//!
//! This module only parses. Every elaborator path still refuses a non-empty slot other than the
//! attributes, so a modifier is never silently dropped: `private` mangling, `protected` name
//! resolution, `noncomputable`, `unsafe`, `partial` and `nonrec` each need their own semantics
//! before they can be admitted.
use super::*;

/// The five modifier slots after the attributes, in the pin's order. Each slot accepts
/// exactly these keywords, and the node kind is `Lean.Parser.Command.<keyword>`.
const SLOTS: [&[&str]; 5] = [
    &["private", "public"],
    &["protected"],
    &["meta", "noncomputable"],
    &["unsafe"],
    &["partial", "nonrec"],
];

/// Every keyword that may start a modifier slot.
pub(crate) fn is_modifier(word: &str) -> bool {
    SLOTS.iter().any(|slot| slot.contains(&word))
}

/// The keyword text of `token`, when it is one of the modifier keywords. Every modifier is a
/// keyword at the pin, so it is always a symbol; an escaped `«partial»` is an identifier and
/// never a modifier.
fn keyword(token: &LexedToken) -> Option<&str> {
    match &token.kind {
        TokenKind::Symbol(symbol) if is_modifier(symbol) => Some(symbol.as_str()),
        _ => None,
    }
}

/// The modifier tokens found after the attributes: for each slot, the token index of its
/// keyword, if present.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Modifiers {
    slots: [Option<usize>; 5],
    end: usize,
}

impl Modifiers {
    /// The token index just after the last modifier: where the declaration keyword must be.
    pub(crate) fn end(&self) -> usize {
        self.end
    }

    /// Write the five slot nodes (`declModifiers` children 2..=6) into `parts`, from the
    /// original leaves. Out of line and writing in place: the declaration parser runs on small
    /// host stacks (its deep-nesting tests use 96 KiB threads), so these nodes never live in its
    /// frame.
    #[inline(never)]
    pub(crate) fn fill(
        &self,
        view: &SourceView,
        leaves: &Leaves,
        tokens: &[LexedToken],
        parts: &mut [Syntax],
    ) -> Result<(), DefinitionParseError> {
        for (part, slot) in parts.iter_mut().zip(self.slots) {
            let Some(at) = slot else {
                continue;
            };
            let word = tokens.get(at).and_then(keyword).ok_or(
                NatDefinitionParseError::OutsideSeedGrammar {
                    at: original_position(view, tokens, at),
                    expected: NatDefinitionExpectation::DefinitionKeyword,
                },
            )?;
            *part = null_node(vec![Syntax::node(
                parser_kind(&["Command", word]),
                vec![leaves.leaf(at)?],
            )]);
        }
        Ok(())
    }
}

/// Whether `token` is a modifier keyword, so the command it starts is a declaration.
pub(crate) fn leads(token: &LexedToken) -> bool {
    keyword(token).is_some()
}

/// Scan the modifier keywords starting at token `start` (just after any attributes). Slots
/// are taken in order and each at most once; scanning stops at the first token that does not
/// fill the next possible slot.
pub(crate) fn scan(tokens: &[LexedToken], start: usize) -> Modifiers {
    let mut slots = [None; 5];
    let mut at = start;
    let mut next_slot = 0;
    while let Some(word) = tokens.get(at).and_then(keyword) {
        let Some(offset) = SLOTS[next_slot..]
            .iter()
            .position(|slot| slot.contains(&word))
        else {
            break;
        };
        slots[next_slot + offset] = Some(at);
        next_slot += offset + 1;
        at += 1;
        if next_slot == SLOTS.len() {
            break;
        }
    }
    Modifiers { slots, end: at }
}

/// Visibility at an unfinished declaration or material control's head. This is a query hint only:
/// no signature, body, modifier effect, or declaration has been validated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeclarationPrefix {
    pub public: Option<bool>,
    pub is_example: bool,
}

/// Read only the declaration prefix, reusing the ordinary parser's attribute
/// grammar and fixed modifier slots. Variable/attribute controls inherit the
/// section's visibility too. The body may end at an incomplete name or binder.
/// Query/lexical scope commands and unrecognized heads return `None`; a keyword
/// in a body, string, comment, or escaped identifier never supplies visibility.
pub fn prefix(source: &[u8]) -> Result<Option<DeclarationPrefix>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let tokens = super::tokens(&view)?;
    let (_, attributes_end, declaration_start) =
        crate::declaration_prefix(&view, &tokens, DefinitionGrammar::Scalar)?;
    let Some(TokenKind::Symbol(kind)) = tokens.get(declaration_start).map(|token| &token.kind)
    else {
        return Ok(None);
    };
    if !matches!(
        kind.as_str(),
        "def"
            | "theorem"
            | "abbrev"
            | "opaque"
            | "example"
            | "instance"
            | "structure"
            | "class"
            | "inductive"
            | "axiom"
            | "variable"
            | "attribute"
    ) {
        return Ok(None);
    }
    let modifiers = scan(&tokens, attributes_end);
    Ok(Some(DeclarationPrefix {
        public: modifiers.slots[0].map(|at| keyword(&tokens[at]) == Some("public")),
        is_example: kind == "example",
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn completion_visibility_reads_modifiers_without_requiring_a_finished_body() {
        for (source, public) in [
            (
                "@[expose] public def use (A : Type) (x : A) : A :=",
                Some(true),
            ),
            (
                "/-- API -/\nprivate def use (A : Type) (x : A) : A :=",
                Some(false),
            ),
            ("def use (A : Type) (x : A) : A :=", None),
            ("@[expose] public def use (", Some(true)),
            ("variable (x :", None),
            ("attribute [instance]", None),
        ] {
            assert_eq!(
                prefix(source.as_bytes()).unwrap(),
                Some(DeclarationPrefix {
                    public,
                    is_example: false
                }),
                "{source}"
            );
        }
        assert_eq!(
            prefix(b"example (P : Prop) : P :=").unwrap(),
            Some(DeclarationPrefix {
                public: None,
                is_example: true
            })
        );
        for source in [
            "#check",
            "#eval",
            "@[expose] public section",
            "«public» def use :=",
            "-- public def hidden :=\n#check",
        ] {
            assert_eq!(prefix(source.as_bytes()).unwrap(), None, "{source}");
        }
    }
}
