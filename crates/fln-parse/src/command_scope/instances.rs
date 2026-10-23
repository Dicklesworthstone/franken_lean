//! Global, namespace-scoped and local instance attributes, and global default candidates. A local
//! instance is never a persistent registration: it holds until the enclosing scope ends.
//! Erasure is a separate state-only operation and never exports a registration change.
use super::*;

mod erasure;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstanceAttribute {
    pub declarations: Vec<Name>,
    pub priority: u32,
    pub scoped: bool,
    pub is_default: bool,
    /// `attribute [local instance] x`: selected until the enclosing `section`/`namespace` ends.
    pub local: bool,
    /// `attribute [-instance] x`: remove a currently active instance in this lexical scope.
    /// Priority and registration-kind fields do not describe this operation.
    pub erase: bool,
    /// The `instance` (or `default_instance`) keyword's offset in the command, where the pin
    /// positions a message about the attribute.
    pub at: BytePos,
}

/// Inspect the existing scope-command token stream, preserving original source
/// positions. `None` leaves other attribute families to their own parser.
pub(super) fn parse(
    view: &SourceView,
    tokens: &[LexedToken],
) -> Result<Option<InstanceAttribute>, DefinitionParseError> {
    if let Some(attribute) = erasure::parse(view, tokens)? {
        return Ok(Some(attribute));
    }
    let is = |at: usize, text: &str| {
        tokens.get(at).is_some_and(|token| {
            matches!(&token.kind, TokenKind::Symbol(_) | TokenKind::Ident(_))
                && view.normalized().span_str(token.extent) == Some(text)
        })
    };
    let scoped = is(2, "scoped");
    let local = is(2, "local");
    let keyword = if scoped || local { 3 } else { 2 };
    let is_default = is(keyword, "default_instance");
    if !is(0, "attribute") || !is(1, "[") || !(is(keyword, "instance") || is_default) {
        return Ok(None);
    }
    let bad = |at: usize| NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::EndOfCommand,
    };
    // A local or scoped default instance is not read; a local instance is.
    if is_default && (local || scoped) {
        return Err(bad(2));
    }
    let mut at = keyword + 1;
    let mut priority = 1000;
    let mut depth = 0;
    while is(at, "(") {
        if depth >= 16 {
            return Err(bad(at));
        }
        depth += 1;
        at += 1;
    }
    if matches!(
        tokens.get(at).map(|token| &token.kind),
        Some(TokenKind::Literal(LiteralKind::Nat))
    ) {
        let text = view
            .normalized()
            .span_str(tokens[at].extent)
            .ok_or_else(|| bad(at))?;
        if text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err(bad(at));
        }
        priority = text.parse::<u32>().map_err(|_| bad(at))?;
        at += 1;
    } else if !is(at, "]") {
        priority = if is(at, "default") {
            1000
        } else if is(at, "low") {
            100
        } else if is(at, "mid") {
            500
        } else if is(at, "high") {
            10000
        } else {
            return Err(bad(at));
        };
        at += 1;
    }
    for _ in 0..depth {
        if !is(at, ")") {
            return Err(bad(at));
        }
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
    Ok(Some(InstanceAttribute {
        declarations,
        priority,
        scoped,
        is_default,
        local,
        erase: false,
        at: original_position(view, tokens, keyword),
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::command_scope::{parse as parse_command, partition};

    fn attribute(source: &str) -> InstanceAttribute {
        let Some(ScopeCommand::Instance(attribute)) = parse_command(source.as_bytes()).unwrap()
        else {
            panic!("instance attribute expected");
        };
        attribute
    }

    #[test]
    fn scoped_attributes_keep_visibility_priority_and_original_refusal_offsets() {
        let source = "/- 😀 -/ attribute [scoped instance 23] A.«b.c» d";
        let parsed = attribute(source);
        assert!(parsed.scoped);
        assert_eq!(parsed.priority, 23);
        assert_eq!(parsed.at, BytePos(source.find("instance").unwrap()));
        assert_eq!(
            parsed.declarations,
            [
                Name::from_components(["A", "b.c"]),
                Name::from_components(["d"])
            ]
        );
        assert!(!attribute("attribute [instance] d").scoped);
        assert!(attribute("attribute [scoped instance] d").scoped);
        let bad = "/- 😀 -/\r\nattribute [scoped instance 4294967296] d";
        assert_eq!(
            parse_command(bad.as_bytes()).unwrap_err().primary_offset(),
            Some(BytePos(bad.find("4294967296").unwrap()))
        );
    }

    #[test]
    fn priorities_and_structural_names_use_the_real_lexer() {
        let parsed =
            attribute("/- 😀 -/ attribute /- comment -/ [instance /- priority -/ 7] A.«b.c» d");
        assert_eq!(parsed.priority, 7);
        assert_eq!(
            parsed.declarations,
            vec![
                Name::from_components(["A", "b.c"]),
                Name::from_components(["d"])
            ]
        );
        assert_eq!(attribute("attribute [instance] d").priority, 1000);
        assert_eq!(attribute("attribute [instance 0] d").priority, 0);
        assert_eq!(attribute("attribute [instance high] d").priority, 10000);
        assert_eq!(attribute("attribute [instance (low)] d").priority, 100);
        assert_eq!(attribute("attribute [instance ((mid))] d").priority, 500);
        assert_eq!(
            attribute("attribute [instance 4294967295] d").priority,
            u32::MAX
        );
        assert!(matches!(
            parse_command(b"attribute [simp] d").unwrap(),
            Some(ScopeCommand::Simp(_))
        ));
    }

    #[test]
    fn default_candidates_preserve_priority_and_refuse_unsupported_scopes() {
        for (source, priority) in [
            ("attribute [default_instance] d", 1000),
            ("attribute [default_instance 0] d", 0),
            ("attribute [default_instance 4294967295] d", u32::MAX),
            ("attribute [default_instance default] d", 1000),
            ("attribute [default_instance (low)] d", 100),
            ("attribute [default_instance ((mid))] d", 500),
            ("attribute [default_instance high] d", 10000),
        ] {
            let parsed = attribute(source);
            assert!(parsed.is_default && !parsed.scoped, "{source}");
            assert_eq!(parsed.priority, priority, "{source}");
        }
        assert!(!attribute("attribute [instance] d").is_default);
        assert_eq!(
            attribute("attribute [default_instance 7] A.«b.c» «default_instance»").declarations,
            [
                Name::from_components(["A", "b.c"]),
                Name::from_components(["default_instance"])
            ]
        );
        for source in [
            "attribute [local default_instance] d",
            "attribute [scoped default_instance] d",
            "attribute [-default_instance] d",
            "attribute [«default_instance»] d",
            "attribute [default_instance 4294967296] d",
            "attribute [default_instance -1] d",
            "attribute [default_instance 0xff] d",
            "attribute [default_instance 1_000] d",
            "attribute [default_instance (7] d",
            "attribute [default_instance ()] d",
            "attribute [default_instance high + 1] d",
            "attribute [default_instance, simp] d",
            "attribute [default_instance]",
        ] {
            assert!(parse_command(source.as_bytes()).is_err(), "{source}");
        }
    }

    #[test]
    fn malformed_and_unsupported_effects_never_disappear() {
        for source in [
            "attribute [instance]",
            "attribute [instance 4294967296] d",
            "attribute [instance -1] d",
            "attribute [instance 0xff] d",
            "attribute [instance 1_000] d",
            "attribute [instance higher] d",
            "attribute [instance 7 8] d",
            "attribute [instance, simp] d",
            "attribute [instance] d, e",
            "attribute [instance] d in",
            "attribute [instance] d := 0",
            "attribute [instance] d [simp]",
            "attribute [scoped instance]",
            "attribute [scoped instance 4294967296] d",
            "attribute [scoped instance, simp] d",
            "attribute [scoped local instance] d",
            "attribute [«instance»] d",
        ] {
            assert!(parse_command(source.as_bytes()).is_err(), "{source}");
        }
    }

    /// `local` (`attrKind`) is read beside `scoped`; `scoped local` is no kind.
    #[test]
    fn a_local_instance_attribute_is_read() {
        let local = attribute("attribute [local instance 2000] d e");
        assert!(local.local && !local.scoped);
        assert_eq!(local.priority, 2000);
        assert_eq!(local.declarations.len(), 2);
        assert!(!attribute("attribute [instance] d").local);
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
        assert!(matches!(
            parse_command(commands[2].1).unwrap(),
            Some(ScopeCommand::Instance(_))
        ));
        let bad = "/- 😀 -/\r\nattribute [instance 4294967296] d";
        let error = parse_command(bad.as_bytes()).unwrap_err();
        assert_eq!(
            error.primary_offset(),
            Some(BytePos(bad.find("4294967296").unwrap()))
        );
    }
}
