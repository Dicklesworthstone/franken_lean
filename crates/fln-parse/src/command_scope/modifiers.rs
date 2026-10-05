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

/// The keyword text of `token`, when it is one of the modifier keywords. `partial` is lexed
/// as an identifier in declaration bodies (`reference_tokens::SEED_IDENTIFIER_ALLOWANCE`), so
/// an identifier spelling exactly a keyword counts here too; an escaped `«partial»` does not,
/// because its source span is not the bare word.
fn keyword<'t>(view: &SourceView, token: &'t LexedToken) -> Option<&'t str> {
    let text = match &token.kind {
        TokenKind::Symbol(symbol) => symbol.as_str(),
        TokenKind::Ident(name) => {
            let spelled = view.normalized().span_str(token.extent)?;
            let display = name.to_display_string();
            if spelled != display {
                return None;
            }
            // Borrow the keyword from the static table so the result outlives `name`.
            return SLOTS
                .iter()
                .flat_map(|slot| slot.iter())
                .find(|word| **word == spelled)
                .copied();
        }
        TokenKind::Literal(_) => return None,
    };
    is_modifier(text).then_some(text)
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
            let word = tokens
                .get(at)
                .and_then(|token| keyword(view, token))
                .ok_or(NatDefinitionParseError::OutsideSeedGrammar {
                    at: original_position(view, tokens, at),
                    expected: NatDefinitionExpectation::DefinitionKeyword,
                })?;
            let atom = match leaves.leaf(at)? {
                // `partial` arrives as an identifier leaf; the pin's node holds an atom.
                Syntax::Ident { info, .. } => Syntax::Atom {
                    info,
                    val: word.into(),
                },
                atom => atom,
            };
            *part = null_node(vec![Syntax::node(
                parser_kind(&["Command", word]),
                vec![atom],
            )]);
        }
        Ok(())
    }
}

/// Whether `token` is a modifier keyword, so the command it starts is a declaration.
pub(crate) fn leads(view: &SourceView, token: &LexedToken) -> bool {
    keyword(view, token).is_some()
}

/// Scan the modifier keywords starting at token `start` (just after any attributes). Slots
/// are taken in order and each at most once; scanning stops at the first token that does not
/// fill the next possible slot.
pub(crate) fn scan(view: &SourceView, tokens: &[LexedToken], start: usize) -> Modifiers {
    let mut slots = [None; 5];
    let mut at = start;
    let mut next_slot = 0;
    while let Some(word) = tokens.get(at).and_then(|token| keyword(view, token)) {
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
