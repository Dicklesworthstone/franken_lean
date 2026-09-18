//! Bounded, standalone native simp-attribute commands. All syntax is lexed;
//! unsupported attributes and modifiers are errors rather than ignored effects.
use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimpAttribute {
    pub declarations: Vec<Name>,
    /// `None` removes a rule; `Some` records (priority, reverse).
    pub rule: Option<(u32, bool)>,
}

/// Recognize one inline attribute without discarding or re-lexing source bytes.
/// Other attribute families and modifiers remain outside this source profile.
pub(crate) fn inline_end(
    view: &SourceView,
    tokens: &[LexedToken],
) -> Result<usize, DefinitionParseError> {
    let is = |at: usize, text: &str| matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text);
    let bad = |at| NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::DefinitionKeyword,
    };
    if !is(0, "@[") {
        return Ok(0);
    }
    if !matches!(tokens.get(1).map(|t| &t.kind), Some(TokenKind::Ident(n)) if *n == Name::from_components(["simp"]))
        || view.normalized().span_str(tokens[1].extent) != Some("simp")
    {
        return Err(bad(1));
    }
    let mut at = 2;
    at += usize::from(is(at, "←") || is(at, "<-"));
    if matches!(
        tokens.get(at).map(|t| &t.kind),
        Some(TokenKind::Literal(LiteralKind::Nat))
    ) {
        let text = view
            .normalized()
            .span_str(tokens[at].extent)
            .ok_or_else(|| bad(at))?;
        if !text.bytes().all(|b| b.is_ascii_digit()) || text.parse::<u32>().is_err() {
            return Err(bad(at));
        }
        at += 1;
    }
    if !is(at, "]") {
        return Err(bad(at));
    }
    Ok(at + 1)
}

/// The Reference declaration modifier/attribute production, with original
/// lexer leaves (including CRLF mapping, comments and Unicode extents).
pub(crate) fn inline_syntax(
    leaves: &Leaves,
    tokens: &[LexedToken],
    end: usize,
) -> Result<Syntax, DefinitionParseError> {
    let mut at = 2;
    let reverse = if matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == "←" || s == "<-")
    {
        at += 1;
        null_node(vec![leaves.leaf(at - 1)?])
    } else {
        null_node(Vec::new())
    };
    let priority = if at + 1 < end {
        null_node(vec![Syntax::node(
            parser_kind(&["Priority", "numPrio"]),
            vec![Syntax::node(
                Name::from_components(["num"]),
                vec![leaves.leaf(at)?],
            )],
        )])
    } else {
        null_node(Vec::new())
    };
    let simp = Syntax::node(
        parser_kind(&["Attr", "simp"]),
        vec![
            Syntax::Atom {
                info: leaves.leaf(1)?.info(),
                val: "simp".into(),
            },
            null_node(Vec::new()),
            reverse,
            priority,
        ],
    );
    Ok(null_node(vec![Syntax::node(
        parser_kind(&["Term", "attributes"]),
        vec![
            leaves.leaf(0)?,
            null_node(vec![Syntax::node(
                parser_kind(&["Term", "attrInstance"]),
                vec![
                    Syntax::node(
                        parser_kind(&["Term", "attrKind"]),
                        vec![null_node(Vec::new())],
                    ),
                    simp,
                ],
            )]),
            leaves.leaf(end - 1)?,
        ],
    )]))
}

pub fn parse(source: &[u8]) -> Result<Option<SimpAttribute>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let tokens = tokens(&view)?;
    let is = |at: usize, text: &str| matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text);
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
    fn inline_attributes_preserve_every_source_leaf_and_declaration_boundary() {
        let source = "/- 😀 -/ namespace N\r\n@[simp <- 700]\r\ntheorem flip (n : Nat) : n = n := by rfl\r\n@[simp] def wrap (n : Nat) := n\r\nend N\r\n";
        let commands = partition(source.as_bytes()).unwrap();
        assert_eq!(commands.len(), 4);
        let mut joined = Vec::new();
        for (offset, bytes) in &commands {
            assert_eq!(offset.0, joined.len());
            joined.extend_from_slice(bytes);
        }
        assert_eq!(joined, source.as_bytes());
        for (_, bytes) in &commands[1..3] {
            let parsed = parse_definition(bytes).unwrap();
            assert_eq!(parsed.reconstruct_original(), *bytes);
            let normalized = String::from_utf8_lossy(bytes).replace("\r\n", "\n");
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                normalized.as_bytes()
            );
        }
        for source in [
            "@[simp] theorem self.{u} {A : Sort u} (x : A) : x = x := by rfl",
            "@[simp /- phase -/ ← /- prio -/ 0] theorem self (x : Nat) : x = x := by rfl",
            "@[simp 4294967295] def «a.b» := 7",
        ] {
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
            assert!(parse_nat_definition(source.as_bytes()).is_err());
        }
    }

    #[test]
    fn unsupported_inline_attributes_never_disappear_from_the_command() {
        for source in [
            "@[other] def x := 0",
            "@[«simp»] def x := 0",
            "@[simp, other] def x := 0",
            "@[simp][other] def x := 0",
            "@[simp] @[simp] def x := 0",
            "@[simp ← ←] def x := 0",
            "@[simp 4294967296] def x := 0",
            "@[simp 0xff] def x := 0",
            "@[simp high] def x := 0",
            "@[local simp] def x := 0",
            "@[simp ↓] def x := 0",
            "@[simp] unsafe def x := 0",
            "@[simp] instance value : Inhabited Nat := Inhabited.mk 0",
            "@[simp] inductive T where | mk",
            "@[simp]",
        ] {
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
        let source = b"def x := 0\n@[other]\ndef y := 1\n";
        let commands = partition(source).unwrap();
        assert_eq!(commands.len(), 2);
        assert!(parse_definition(commands[1].1).is_err());
    }

    #[test]
    fn parses_priorities_erasure_and_structural_names() {
        let parsed = parse("/- note -/ attribute [simp ← 7] A.«b.c» d".as_bytes())
            .unwrap()
            .unwrap();
        assert_eq!(parsed.rule, Some((7, true)));
        assert_eq!(parsed.declarations[0], Name::from_components(["A", "b.c"]));
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
