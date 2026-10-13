//! The state-only `attribute [-instance]` command. Erasure has no priority or
//! attribute-kind parameter and is distinct from persistent registration.
use super::*;

pub(super) fn parse(
    view: &SourceView,
    tokens: &[LexedToken],
) -> Result<Option<InstanceAttribute>, DefinitionParseError> {
    let is = |at: usize, text: &str| {
        tokens.get(at).is_some_and(|token| {
            matches!(&token.kind, TokenKind::Symbol(_) | TokenKind::Ident(_))
                && view.normalized().span_str(token.extent) == Some(text)
        })
    };
    if !(is(0, "attribute") && is(1, "[") && is(2, "-") && is(3, "instance")) {
        return Ok(None);
    }
    let bad = |at: usize| NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::EndOfCommand,
    };
    if !is(4, "]") {
        return Err(bad(4));
    }
    let mut declarations = Vec::new();
    for (at, token) in tokens.iter().enumerate().skip(5) {
        let TokenKind::Ident(name) = &token.kind else {
            return Err(bad(at));
        };
        declarations.push(name.clone());
    }
    if declarations.is_empty() {
        return Err(bad(5));
    }
    Ok(Some(InstanceAttribute {
        declarations,
        priority: 1000,
        scoped: false,
        is_default: false,
        local: false,
        erase: true,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::command_scope::{ScopeCommand, parse as parse_command, partition};

    #[test]
    fn erasure_keeps_structural_names_and_is_not_registration() {
        let source = "/- 😀 -/\r\nattribute /- a -/ [- /- b -/ instance] A.«b.c» d";
        let Some(ScopeCommand::Instance(attribute)) = parse_command(source.as_bytes()).unwrap()
        else {
            panic!("instance erasure expected");
        };
        assert!(attribute.erase);
        assert!(!attribute.local && !attribute.scoped && !attribute.is_default);
        assert_eq!(
            attribute.declarations,
            [
                Name::from_components(["A", "b.c"]),
                Name::from_components(["d"]),
            ]
        );
        for source in [
            "attribute [instance] d",
            "attribute [local instance] d",
            "attribute [scoped instance] d",
            "attribute [default_instance] d",
        ] {
            let Some(ScopeCommand::Instance(attribute)) = parse_command(source.as_bytes()).unwrap()
            else {
                panic!("instance attribute expected");
            };
            assert!(!attribute.erase, "{source}");
        }
    }

    #[test]
    fn erasure_refuses_parameters_modifiers_empty_lists_and_unconsumed_tokens() {
        for source in [
            "attribute [-instance]",
            "attribute [-instance 7] d",
            "attribute [-instance, simp] d",
            "attribute [-instance] d, e",
            "attribute [-instance] d := 0",
            "attribute [-instance] d [simp]",
            "attribute [local -instance] d",
            "attribute [scoped -instance] d",
            "attribute [-«instance»] d",
            "attribute [-default_instance] d",
        ] {
            assert!(parse_command(source.as_bytes()).is_err(), "{source}");
        }
    }

    #[test]
    fn erasure_errors_report_original_crlf_and_unicode_offsets() {
        let source = "/- 😀 -/\r\nattribute [-instance 7] d";
        assert_eq!(
            parse_command(source.as_bytes())
                .unwrap_err()
                .primary_offset(),
            Some(BytePos(source.find('7').unwrap()))
        );
        let source = "/- 😀 -/\r\nattribute [-instance] d, e";
        assert_eq!(
            parse_command(source.as_bytes())
                .unwrap_err()
                .primary_offset(),
            Some(BytePos(source.find(',').unwrap()))
        );
    }

    #[test]
    fn erasure_in_is_one_command_with_a_scoped_head_and_exact_original_bytes() {
        let source =
            "attribute [-instance] A.d in\r\ndef selected : Nat := 7\r\ndef after : Nat := 8\r\n";
        let commands = partition(source.as_bytes()).unwrap();
        assert_eq!(commands.len(), 2);
        assert_eq!(
            commands
                .iter()
                .flat_map(|(_, bytes)| bytes.iter().copied())
                .collect::<Vec<_>>(),
            source.as_bytes()
        );
        let Some(ScopeCommand::In { head, body }) = parse_command(commands[0].1).unwrap() else {
            panic!("scoped command wrapper expected");
        };
        assert!(body > head);
        let Some(ScopeCommand::Instance(attribute)) =
            parse_command(&commands[0].1[..head]).unwrap()
        else {
            panic!("erasure head expected");
        };
        assert!(attribute.erase);
        assert_eq!(attribute.declarations, [Name::from_components(["A", "d"])]);
        assert!(commands[0].1[body..].starts_with(b"def selected"));
    }
}
