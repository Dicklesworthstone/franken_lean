//! Bounded, standalone native simp-attribute commands. All syntax is lexed;
//! unsupported attributes and modifiers are errors rather than ignored effects.
use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimpAttribute {
    pub declarations: Vec<Name>,
    /// `None` removes a rule; `Some` records (priority, reverse).
    pub rule: Option<(u32, bool)>,
}

pub fn parse(source: &[u8]) -> Result<Option<SimpAttribute>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let tokens = tokens(&view)?;
    let is = |at: usize, text: &str| {
        matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text)
    };
    if !is(0, "attribute") {
        return Ok(None);
    }
    let bad = |at: usize| NatDefinitionParseError::OutsideSeedGrammar {
        at: tokens.get(at).map_or(BytePos(source.len()), |t| {
            view.to_original(t.extent.start())
        }),
        expected: NatDefinitionExpectation::EndOfCommand,
    };
    if !is(1, "[") {
        return Err(bad(1));
    }
    let mut at = 2;
    let erase = is(at, "-");
    at += usize::from(erase);
    if !matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Ident(n)) if *n == Name::from_components(["simp"]))
    {
        return Err(bad(at));
    }
    at += 1;
    let reverse = is(at, "←") || is(at, "<-");
    if reverse && erase {
        return Err(bad(at));
    }
    at += usize::from(reverse);
    let mut priority = 1000;
    if matches!(
        tokens.get(at).map(|t| &t.kind),
        Some(TokenKind::Literal(LiteralKind::Nat))
    ) {
        if erase {
            return Err(bad(at));
        }
        let text = view
            .normalized()
            .span_str(tokens[at].extent)
            .ok_or_else(|| bad(at))?;
        if !text.bytes().all(|b| b.is_ascii_digit()) {
            return Err(bad(at));
        }
        priority = text.parse::<u32>().map_err(|_| bad(at))?;
        at += 1;
    }
    if !is(at, "]") {
        return Err(bad(at));
    }
    at += 1;
    let mut declarations = Vec::new();
    while at < tokens.len() {
        let TokenKind::Ident(name) = &tokens[at].kind else {
            return Err(bad(at));
        };
        declarations.push(name.clone());
        at += 1;
    }
    if declarations.is_empty() {
        return Err(bad(at));
    }
    Ok(Some(SimpAttribute {
        declarations,
        rule: (!erase).then_some((priority, reverse)),
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn parses_priorities_erasure_and_structural_names() {
        let parsed = parse("/- note -/ attribute [simp ← 7] A.«b.c» d".as_bytes())
            .unwrap()
            .unwrap();
        assert_eq!(parsed.rule, Some((7, true)));
        assert_eq!(
            parsed.declarations[0],
            Name::from_components(["A", "b.c"])
        );
        assert_eq!(parse(b"attribute [-simp] x").unwrap().unwrap().rule, None);
        assert_eq!(
            parse(b"attribute [simp] x").unwrap().unwrap().rule,
            Some((1000, false))
        );
    }
    #[test]
    fn malformed_or_unsupported_commands_fail_closed() {
        for source in [
            "attribute",
            "attribute [simp]",
            "attribute [simp, foo] x",
            "attribute [unknown] x",
            "attribute [-simp 10] x",
            "attribute [simp 4294967296] x",
            "attribute [simp high] x",
            "attribute [simp] x in",
            "attribute [simp <- <-] x",
        ] {
            assert!(parse(source.as_bytes()).is_err(), "{source}");
        }
    }
    #[test]
    fn partition_keeps_commands_and_original_offsets() {
        let source = b"namespace A\r\ndef x := 3\r\nattribute [simp] x\r\ntheorem t : x = 3 := by simp\r\nattribute [-simp] x\r\nend A\r\n";
        let rows = partition(source).unwrap();
        assert_eq!(rows.len(), 6);
        let mut bytes = Vec::new();
        for (offset, row) in rows {
            assert_eq!(offset, BytePos(bytes.len()));
            bytes.extend_from_slice(row);
        }
        assert_eq!(bytes, source);
    }
}
