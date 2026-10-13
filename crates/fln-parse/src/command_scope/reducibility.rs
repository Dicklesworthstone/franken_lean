//! Standalone reducibility attributes. Scope modifiers remain explicit so the
//! command checker can refuse unsupported lifetimes rather than persist them.
use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReducibilityStatus {
    Reducible,
    Semireducible,
    Irreducible,
    ImplicitReducible,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AttributeScope {
    Global,
    Local,
    Scoped,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReducibilityAttribute {
    pub declarations: Vec<Name>,
    pub status: ReducibilityStatus,
    pub scope: AttributeScope,
}

pub(super) fn parse(
    view: &SourceView,
    tokens: &[LexedToken],
) -> Result<Option<ReducibilityAttribute>, DefinitionParseError> {
    let is = |at: usize, text: &str| {
        matches!(tokens.get(at).map(|token| &token.kind),
            Some(TokenKind::Symbol(symbol)) if symbol == text)
    };
    if !is(0, "attribute") || !is(1, "[") {
        return Ok(None);
    }
    let (scope, keyword) = if is(2, "local") {
        (AttributeScope::Local, 3)
    } else if is(2, "scoped") {
        (AttributeScope::Scoped, 3)
    } else {
        (AttributeScope::Global, 2)
    };
    let Some(TokenKind::Ident(name)) = tokens.get(keyword).map(|token| &token.kind) else {
        return Ok(None);
    };
    let status = if name == &Name::from_components(["reducible"]) {
        ReducibilityStatus::Reducible
    } else if name == &Name::from_components(["irreducible"]) {
        ReducibilityStatus::Irreducible
    } else if name == &Name::from_components(["semireducible"]) {
        ReducibilityStatus::Semireducible
    } else if name == &Name::from_components(["implicit_reducible"])
        || name == &Name::from_components(["instance_reducible"])
    {
        ReducibilityStatus::ImplicitReducible
    } else {
        return Ok(None);
    };
    let bad = |at: usize| NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::EndOfCommand,
    };
    let mut at = keyword + 1;
    // The pin's Attribute.Builtin.ensureNoArgs rejects attribute arguments.
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
    Ok(Some(ReducibilityAttribute {
        declarations,
        status,
        scope,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reducibility_names_scopes_and_original_offsets_are_preserved() {
        for (text, status) in [
            ("reducible", ReducibilityStatus::Reducible),
            ("irreducible", ReducibilityStatus::Irreducible),
            ("semireducible", ReducibilityStatus::Semireducible),
            ("implicit_reducible", ReducibilityStatus::ImplicitReducible),
            ("instance_reducible", ReducibilityStatus::ImplicitReducible),
        ] {
            for (modifier, scope) in [
                ("", AttributeScope::Global),
                ("local ", AttributeScope::Local),
                ("scoped ", AttributeScope::Scoped),
            ] {
                let source = format!("/- 😀 -/ attribute [{modifier}{text}] A.«part.name» other");
                let Some(ScopeCommand::Reducibility(attribute)) =
                    super::super::parse(source.as_bytes()).unwrap()
                else {
                    panic!("a reducibility command: {source}");
                };
                assert_eq!(attribute.status, status);
                assert_eq!(attribute.scope, scope);
                assert_eq!(
                    attribute.declarations,
                    [
                        Name::from_components(["A", "part.name"]),
                        Name::from_components(["other"])
                    ],
                );
            }
        }
        let source = "/- 😀 -/\r\nattribute [irreducible 7] value";
        assert_eq!(
            super::super::parse(source.as_bytes())
                .unwrap_err()
                .primary_offset(),
            Some(BytePos(source.find('7').unwrap())),
        );
    }

    #[test]
    fn unsupported_arguments_erasure_and_combined_attributes_are_not_dropped() {
        for source in [
            "attribute [irreducible]",
            "attribute [reducible 7] value",
            "attribute [semireducible, simp] value",
            "attribute [-irreducible] value",
            "attribute [local scoped irreducible] value",
            "attribute [irreducible] value in",
            "attribute [irreducible] value, other",
            "attribute [irreducible] value := 0",
        ] {
            assert!(super::super::parse(source.as_bytes()).is_err(), "{source}");
        }
    }
}
