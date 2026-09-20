//! Standalone global instance registration and decimal-priority attributes.
//! Erasure and local/scoped modifiers are deliberately not approximated as
//! persistent registrations; the ordinary attribute parser refuses them.
use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstanceAttribute {
    pub declarations: Vec<Name>,
    pub priority: u32,
}

/// Inspect the existing scope-command token stream, preserving original source
/// positions. `None` leaves other attribute families to their own parser.
pub(super) fn parse(
    view: &SourceView,
    tokens: &[LexedToken],
) -> Result<Option<InstanceAttribute>, DefinitionParseError> {
    let is = |at: usize, text: &str| {
        matches!(tokens.get(at).map(|token| &token.kind),
            Some(TokenKind::Symbol(symbol)) if symbol == text)
    };
    if !is(0, "attribute") || !is(1, "[") || !is(2, "instance") {
        return Ok(None);
    }
    let bad = |at: usize| NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::EndOfCommand,
    };
    let mut at = 3;
    let mut priority = 1000;
    if matches!(
        tokens.get(at).map(|token| &token.kind),
        Some(TokenKind::Literal(LiteralKind::Nat))
    ) {
        let text = view.normalized().span_str(tokens[at].extent)
            .ok_or_else(|| bad(at))?;
        if text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit()) {
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
    Ok(Some(InstanceAttribute { declarations, priority }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::command_scope::{parse as parse_command, partition};

    fn attribute(source: &str) -> InstanceAttribute {
        let Some(ScopeCommand::Instance(attribute)) =
            parse_command(source.as_bytes()).unwrap()
        else {
            panic!("instance attribute expected");
        };
        attribute
    }

    #[test]
    fn priorities_and_structural_names_use_the_real_lexer() {
        let parsed = attribute(
            "/- 😀 -/ attribute /- comment -/ [instance /- priority -/ 7] A.«b.c» d",
        );
        assert_eq!(parsed.priority, 7);
        assert_eq!(parsed.declarations,
            vec![Name::from_components(["A", "b.c"]), Name::from_components(["d"])]);
        assert_eq!(attribute("attribute [instance] d").priority, 1000);
        assert_eq!(attribute("attribute [instance 0] d").priority, 0);
        assert_eq!(attribute("attribute [instance 4294967295] d").priority, u32::MAX);
        assert!(matches!(parse_command(b"attribute [simp] d").unwrap(),
            Some(ScopeCommand::Simp(_))));
    }

    #[test]
    fn malformed_and_unsupported_effects_never_disappear() {
        for source in [
            "attribute [instance]",
            "attribute [instance 4294967296] d",
            "attribute [instance -1] d",
            "attribute [instance 0xff] d",
            "attribute [instance 1_000] d",
            "attribute [instance high] d",
            "attribute [instance 7 8] d",
            "attribute [instance, simp] d",
            "attribute [instance] d, e",
            "attribute [instance] d in",
            "attribute [instance] d := 0",
            "attribute [instance] d [simp]",
            "attribute [local instance] d",
            "attribute [scoped instance] d",
            "attribute [-instance] d",
            "attribute [«instance»] d",
        ] {
            assert!(parse_command(source.as_bytes()).is_err(), "{source}");
        }
    }

    #[test]
    fn original_offsets_and_command_boundaries_survive_attributes() {
        let source = "/- 😀 -/ namespace A\r\n\
            def «instance» : Inhabited Nat := Inhabited.mk 7\r\n\
            attribute [instance 2000] «instance»\r\n\
            theorem selected : default = 7 := by rfl\r\n\
            end A\r\n";
        let commands = partition(source.as_bytes()).unwrap();
        assert_eq!(commands.len(), 5);
        let mut reconstructed = Vec::new();
        for (offset, bytes) in &commands {
            assert_eq!(offset.0, reconstructed.len());
            reconstructed.extend_from_slice(bytes);
        }
        assert_eq!(reconstructed, source.as_bytes());
        assert!(matches!(parse_command(commands[2].1).unwrap(),
            Some(ScopeCommand::Instance(_))));
        let bad = "/- 😀 -/\r\nattribute [instance 4294967296] d";
        let error = parse_command(bad.as_bytes()).unwrap_err();
        assert_eq!(error.primary_offset(), Some(BytePos(bad.find("4294967296").unwrap())));
    }
}
