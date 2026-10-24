//! A source file's own notations printed back, as the pin's delaborator prints them through the
//! app unexpanders `notation` and the mixfix commands declare (`mkUnexpander`, read by
//! [`fln_parse::extensions::FileGrammar::notations`]).
//!
//! The pin tries a constant's unexpanders on a prefix of an application's explicit arguments,
//! longest first, newest first among equals (`tryAppUnexpanders`, vendored
//! `PrettyPrinter/Delaborator/Builtins.lean:449-480`); the arguments after the prefix stay
//! applied to the printed notation. An application written with `@` runs none.
//!
//! The notation's tokens are laid out as the pin's formatter lays out a token (`pushToken`,
//! vendored `PrettyPrinter/Formatter.lean:366-417`): an atom's leading spaces print as written,
//! its trailing space is a line, and two tokens written together are separated by a line where
//! they would lex as one, read against the active tokens. Where that cannot be told, the term
//! is refused.
use super::*;
use fln_parse::extensions::{Notations, Unexpander, UnexpanderItem};
use fln_syntax::token::is_id_rest;

/// One printed piece of a notation: its layout, its text on one line, whether it is an atom,
/// and the spaces its atom was declared with: the leading ones print as written.
struct Piece {
    doc: Format,
    text: String,
    atom: bool,
    leading_space: String,
    trailing_space: bool,
}

impl<'a> Printer<'a> {
    /// Print applications of the constants these notations print.
    pub fn with_notations(mut self, notations: &'a Notations) -> Self {
        self.notations = Some(notations);
        self
    }

    /// `name` applied to `args` through a notation of this file, `None` when none applies.
    pub(super) fn notation(&mut self, name: &Name, args: &[Expr], outer: u32) -> Option<Doc> {
        let notations = self.notations?;
        if !notations
            .unexpanders
            .iter()
            .any(|notation| notation.head == *name)
        {
            return None;
        }
        let infos = self.binder_infos(name);
        // `useAppExplicit`: with an implicit parameter next, the application prints with `@`,
        // and no unexpander runs on it.
        if infos
            .get(args.len())
            .is_some_and(|info| *info != BinderInfo::Default)
        {
            return None;
        }
        let explicit: Vec<&Expr> = args
            .iter()
            .enumerate()
            .filter(|(index, _)| {
                infos
                    .get(*index)
                    .is_none_or(|info| *info == BinderInfo::Default)
            })
            .map(|(_, arg)| arg)
            .collect();
        let candidates = || {
            notations
                .unexpanders
                .iter()
                .filter(|notation| notation.head == *name && notation.arity <= explicit.len())
        };
        if candidates().any(|notation| notation.items.is_none()) {
            return Some(Err(Unsupported(
                "an application a notation of this file may print",
            )));
        }
        let arity = candidates().map(|notation| notation.arity).max()?;
        let notation: &Unexpander = candidates().find(|notation| notation.arity == arity)?;
        let items = notation.items.as_deref()?;
        let (operands, rest) = explicit.split_at(arity);
        Some(self.unexpanded(
            &notations.tokens,
            notation.precedence,
            items,
            operands,
            rest,
            outer,
        ))
    }

    fn unexpanded(
        &mut self,
        tokens: &[String],
        precedence: u32,
        items: &[UnexpanderItem],
        operands: &[&Expr],
        rest: &[&Expr],
        outer: u32,
    ) -> Doc {
        // Applied to further arguments, the notation is an application's function.
        let level = if rest.is_empty() { outer } else { MAX_PREC };
        let mut pieces = Vec::new();
        for (index, item) in items.iter().enumerate() {
            pieces.push(match item {
                UnexpanderItem::Atom(text) => {
                    let token = text.trim();
                    Piece {
                        doc: Format::text(token),
                        text: token.to_owned(),
                        atom: true,
                        leading_space: text[..text.len() - text.trim_start().len()].to_owned(),
                        trailing_space: text.ends_with(char::is_whitespace),
                    }
                }
                UnexpanderItem::Argument {
                    position,
                    precedence: argument,
                } => {
                    let operand = operands
                        .get(*position)
                        .ok_or(Unsupported("a notation argument out of range"))?;
                    // A token follows every argument but the last.
                    let trailing =
                        index + 1 < items.len() || (self.trailing && precedence >= level);
                    let doc =
                        self.with_trailing(trailing, |printer| printer.doc(operand, *argument))?;
                    Piece {
                        text: flat(&doc),
                        doc,
                        atom: false,
                        leading_space: String::new(),
                        trailing_space: false,
                    }
                }
            });
        }
        let mut shown = Format::Nil;
        for (index, piece) in pieces.iter().enumerate() {
            if !piece.leading_space.is_empty() {
                shown = shown.then(Format::text(piece.leading_space.as_str()));
            } else if let Some(previous) = index.checked_sub(1).map(|at| &pieces[at])
                && (previous.trailing_space
                    || joined(tokens, previous, &piece.text)
                        .ok_or(Unsupported("a notation whose tokens may run together"))?)
            {
                shown = shown.then(Format::Line);
            }
            shown = shown.then(piece.doc.clone());
        }
        let printed = paren_doc(node(shown), precedence, level);
        if rest.is_empty() {
            return Ok(printed);
        }
        let mut applied = printed;
        for arg in rest {
            applied = applied.then(Format::Line).then(self.doc(arg, MAX_PREC)?);
        }
        Ok(paren_doc(node(applied), MAX_PREC - 1, outer))
    }
}

/// Whether the last token of `previous` and the text `next` begins with, written together,
/// would lex as more than that token (`pushToken`'s `parseToken (tk ++ leadWord)`); `None` where
/// that is not told here.
fn joined(tokens: &[String], previous: &Piece, next: &str) -> Option<bool> {
    let word: String = next.chars().take_while(|c| !c.is_whitespace()).collect();
    let (Some(left), Some(right)) = (previous.text.chars().last(), word.chars().next()) else {
        return Some(false);
    };
    if is_id_rest(left) {
        return if is_id_rest(right) {
            // A name or keyword reads on through identifier characters; but `1` then `x` is a
            // numeral then a name, while `0` then `x1` is `0x1`.
            (!left.is_ascii_digit()).then_some(true)
        } else if matches!(right, '.' | '«') {
            // `x.y` and `x«y»` continue a name.
            None
        } else {
            Some(false)
        };
    }
    // A symbol token: the longest active token at its start decides.
    let token = if previous.atom {
        previous.text.as_str()
    } else {
        let start = previous
            .text
            .char_indices()
            .rev()
            .take_while(|(_, c)| !c.is_whitespace() && !is_id_rest(*c))
            .last()
            .map_or(previous.text.len(), |(at, _)| at);
        &previous.text[start..]
    };
    let written = format!("{token}{word}");
    Some(
        tokens.iter().any(|candidate| {
            candidate.len() > token.len() && written.starts_with(candidate.as_str())
        }),
    )
}
