//! Priority attribute helper (`namedPrio`, `Lean/Parser/Syntax.lean`).
//!
//! Full syntax/notation/macro commands are parsed directly by the unified
//! generated registry engine (`BuiltinInterpreter`). This module retains only
//! the `(priority := prio)` reader shared by legacy modifier/instance helpers.
use super::*;

struct Reader<'a> {
    view: &'a SourceView,
    tokens: &'a [LexedToken],
    leaves: &'a Leaves,
    at: usize,
    end: usize,
}

fn kind(name: &str) -> Name {
    Name::str(Name::anonymous(), name)
}

impl Reader<'_> {
    fn symbol(&self, at: usize, text: &str) -> bool {
        at < self.end
            && matches!(&self.tokens[at].kind, TokenKind::Symbol(symbol) if symbol == text)
    }

    /// The symbol `text`, or an unescaped identifier spelling it (`priority`, `default`, `low`,
    /// `mid`, `high`).
    fn word(&self, at: usize, text: &str) -> bool {
        at < self.end
            && match &self.tokens[at].kind {
                TokenKind::Symbol(symbol) => symbol == text,
                TokenKind::Ident(_) => {
                    self.view.normalized().span_str(self.tokens[at].extent) == Some(text)
                }
                _ => false,
            }
    }

    fn literal(&self, at: usize, kind: LiteralKind) -> bool {
        at < self.end
            && matches!(&self.tokens[at].kind, TokenKind::Literal(found) if *found == kind)
    }

    fn bad(&self) -> NatDefinitionParseError {
        NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(self.view, self.tokens, self.at),
            expected: NatDefinitionExpectation::DefinitionKeyword,
        }
    }

    fn take(&mut self) -> Result<Syntax, NatDefinitionParseError> {
        self.at += 1;
        Ok(self.leaves.leaf(self.at - 1)?)
    }

    /// The symbol `text` at the cursor (or the identifier spelling it), as an atom.
    fn atom(&mut self, text: &str) -> Result<Syntax, NatDefinitionParseError> {
        if !self.word(self.at, text) {
            return Err(self.bad());
        }
        let leaf = self.take()?;
        Ok(Syntax::Atom {
            info: leaf.info(),
            val: text.to_owned(),
        })
    }

    fn expect(&mut self, text: &str) -> Result<Syntax, NatDefinitionParseError> {
        if !self.symbol(self.at, text) {
            return Err(self.bad());
        }
        self.take()
    }

    fn number(&mut self) -> Result<Syntax, NatDefinitionParseError> {
        if !self.literal(self.at, LiteralKind::Nat) {
            return Err(self.bad());
        }
        Ok(Syntax::node(kind("num"), vec![self.take()?]))
    }

    /// A `prio`: a numeral, `default`, `low`, `mid`, `high` (`Init/Prelude.lean`), then
    /// `+ prio` and `- prio` (`Syntax.addPrio`, `Syntax.subPrio`).
    fn prio(&mut self) -> Result<Syntax, NatDefinitionParseError> {
        let leading = |reader: &mut Self| -> Result<Syntax, NatDefinitionParseError> {
            if reader.literal(reader.at, LiteralKind::Nat) {
                return reader.number();
            }
            for (word, name) in [
                ("default", "prioDefault"),
                ("low", "prioLow"),
                ("mid", "prioMid"),
                ("high", "prioHigh"),
            ] {
                if reader.word(reader.at, word) {
                    return Ok(Syntax::node(kind(name), vec![reader.atom(word)?]));
                }
            }
            Err(reader.bad())
        };
        let mut value = leading(self)?;
        while let Some((symbol, name)) = [("+", "addPrio"), ("-", "subPrio")]
            .into_iter()
            .find(|(symbol, _)| self.symbol(self.at, symbol))
        {
            let operator = self.atom(symbol)?;
            let right = leading(self)?;
            value = Syntax::node(parser_kind(&["Syntax", name]), vec![value, operator, right]);
        }
        Ok(value)
    }

    /// `" (" "priority" " := " prio ")"`, if one is at the cursor.
    fn named_priority(&mut self) -> Result<Option<Syntax>, NatDefinitionParseError> {
        if !(self.symbol(self.at, "(")
            && self.word(self.at + 1, "priority")
            && self.symbol(self.at + 2, ":="))
        {
            return Ok(None);
        }
        let open = self.take()?;
        let word_atom = self.atom("priority")?;
        let assign = self.take()?;
        let value = self.prio()?;
        let close = self.expect(")")?;
        Ok(Some(Syntax::node(
            parser_kind(&["Command", "namedPrio"]),
            vec![open, word_atom, assign, value, close],
        )))
    }
}

/// `namedPrio` (`" (" "priority" " := " prio ")"`) at `start`, as the pin builds it, and the
/// token after its `)`; `None` when no `(priority :=` starts there.
pub(crate) fn named_priority(
    view: &SourceView,
    tokens: &[LexedToken],
    leaves: &Leaves,
    start: usize,
) -> Result<Option<(Syntax, usize)>, DefinitionParseError> {
    let mut reader = Reader {
        view,
        tokens,
        leaves,
        at: start,
        end: tokens.len(),
    };
    Ok(reader.named_priority()?.map(|node| (node, reader.at)))
}
