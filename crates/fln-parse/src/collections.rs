//! List literals and anonymous constructors share the ordinary term parser's
//! explicit frame stack.
//!
//! The pin's `term[_]` (`[a, b]`) and `Term.anonymousCtor` (`⟨a, b⟩`) trees retain
//! brackets, commas (including an optional trailing comma: `sepBy … (allowTrailingSep
//! := true)` in both), comments and source positions. Constructor expansion belongs
//! to elaboration, not to this source-preserving parser.
use super::*;

mod patterns;
pub(super) use patterns::pattern;

#[derive(Default)]
pub(super) struct Lists {
    active: Vec<List>,
}

struct List {
    open: usize,
    bracket: Bracket,
    elements_and_separators: Vec<Syntax>,
}

/// Which comma-separated bracket a [`List`] is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Bracket {
    /// `[a, b]`: `term[_]` (`Init/Data/List/Notation.lean`).
    List,
    /// `⟨a, b⟩`: `Lean.Parser.Term.anonymousCtor` (`Lean/Parser/Term.lean`).
    AnonymousCtor,
}

impl Bracket {
    fn close(self) -> &'static str {
        match self {
            Bracket::List => "]",
            Bracket::AnonymousCtor => "⟩",
        }
    }
    fn kind(self) -> Name {
        match self {
            Bracket::List => list_kind(),
            Bracket::AnonymousCtor => parser_kind(&["Term", "anonymousCtor"]),
        }
    }
}

fn frame(open: usize) -> BoundedTermFrame {
    BoundedTermFrame {
        record: None,
        ascription: None,
        open: Some(open),
        prefix: None,
        negation: None,
        application: Vec::new(),
        operands: Vec::new(),
        operators: Vec::new(),
    }
}

pub(super) fn list_kind() -> Name {
    Name::from_components(["term[_]"])
}

impl Lists {
    pub(super) fn open(&mut self, frames: &mut Vec<BoundedTermFrame>, at: usize, bracket: Bracket) {
        self.active.push(List {
            open: at,
            bracket,
            elements_and_separators: Vec::new(),
        });
        frames.push(frame(at));
    }

    /// Whether `symbol` is a delimiter of the innermost open bracket: `,` or its own close.
    pub(super) fn delimits(&self, symbol: &str) -> bool {
        self.active
            .last()
            .is_some_and(|list| symbol == "," || symbol == list.bracket.close())
    }

    /// A list does not own commas or closing delimiters inside a record,
    /// parenthesis, or binder header nested in its current element.
    pub(super) fn current(&self, frames: &[BoundedTermFrame]) -> bool {
        self.active.last().is_some_and(|list| {
            frames.last().is_some_and(|frame| {
                frame.open == Some(list.open)
                    && frame.record.is_none()
                    && frame.prefix.is_none()
                    && frame.negation.is_none()
            })
        })
    }

    pub(super) fn delimiter(
        &mut self,
        leaves: &Leaves,
        view: &SourceView,
        tokens: &[LexedToken],
        frames: &mut Vec<BoundedTermFrame>,
        at: usize,
    ) -> Result<(), NatDefinitionParseError> {
        let refusal = || NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(view, tokens, at),
            expected: NatDefinitionExpectation::ScalarValue,
        };
        if !self.current(frames) || frames.len() < 2 {
            return Err(refusal());
        }
        let Some(TokenKind::Symbol(symbol)) = tokens.get(at).map(|token| &token.kind) else {
            return Err(refusal());
        };
        let close = self
            .active
            .last()
            .expect("validated active list")
            .bracket
            .close();
        if symbol != "," && symbol != close {
            return Err(refusal());
        }
        let current = frames.pop().expect("validated list element frame");
        if current.ascription.is_some() {
            return Err(refusal());
        }
        let empty = current.application.is_empty()
            && current.operands.is_empty()
            && current.operators.is_empty();
        let list = self.active.last_mut().expect("validated active list");
        if empty {
            // [] and [a,] are valid; [,], [a,,b] and [a,,] are not (and so for ⟨⟩).
            // Every noninitial empty frame follows exactly one consumed comma.
            if symbol != close {
                return Err(refusal());
            }
        } else {
            let element =
                finish_bounded_frame(view, tokens, current, DefinitionGrammar::Scalar, at)?;
            list.elements_and_separators.push(element);
        }
        if symbol == "," {
            list.elements_and_separators.push(leaves.leaf(at)?);
            frames.push(frame(list.open));
        } else {
            let list = self.active.pop().expect("completed list");
            let syntax = Syntax::node(
                list.bracket.kind(),
                vec![
                    leaves.leaf(list.open)?,
                    null_node(list.elements_and_separators),
                    leaves.leaf(at)?,
                ],
            );
            frames
                .last_mut()
                .expect("list has an enclosing term frame")
                .application
                .push((syntax, list.open));
        }
        Ok(())
    }
}
