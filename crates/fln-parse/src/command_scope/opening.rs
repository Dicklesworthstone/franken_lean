//! Typed selective opens over the same lexer used by the source command driver.
use super::*;

pub(super) fn parse(
    view: &SourceView,
    tokens: &[LexedToken],
    source_len: usize,
) -> Result<Option<ScopeCommand>, DefinitionParseError> {
    let symbol = |at: usize, text: &str| matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text);
    if !symbol(0, "open") || !symbol(2, "renaming") {
        return Ok(None);
    }
    let bad = |at: usize| NatDefinitionParseError::OutsideSeedGrammar {
        at: tokens.get(at).map_or(BytePos(source_len), |token| {
            view.to_original(token.extent.start())
        }),
        expected: NatDefinitionExpectation::EndOfCommand,
    };
    let ident = |at: usize| match tokens.get(at).map(|t| &t.kind) {
        Some(TokenKind::Ident(name)) => Ok(name.clone()),
        _ => Err(bad(at)),
    };
    let namespace = ident(1)?;
    let mut at = 3;
    let mut renames = Vec::new();
    loop {
        if renames.len() >= 4096 {
            return Err(bad(at));
        }
        let from = ident(at)?;
        at += 1;
        if !symbol(at, "->") && !symbol(at, "→") {
            return Err(bad(at));
        }
        at += 1;
        let to = ident(at)?;
        renames.push((from, to));
        at += 1;
        if at == tokens.len() {
            break;
        }
        if !symbol(at, ",") {
            return Err(bad(at));
        }
        at += 1;
    }
    Ok(Some(ScopeCommand::OpenRenaming { namespace, renames }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn renaming_keeps_structural_names_comments_and_arrow_spellings() {
        let source = "/- 🦀 -/\r\nopen Library renaming «a.b» /- from -/ -> «c.d», x → y";
        let Some(ScopeCommand::OpenRenaming { namespace, renames }) =
            super::super::parse(source.as_bytes()).unwrap()
        else {
            panic!("renaming command expected");
        };
        assert_eq!(namespace, Name::from_components(["Library"]));
        assert_eq!(
            renames,
            vec![
                (
                    Name::from_components(["a.b"]),
                    Name::from_components(["c.d"])
                ),
                (Name::from_components(["x"]), Name::from_components(["y"])),
            ]
        );
        let tree = trees::tree(source.as_bytes()).unwrap().unwrap();
        assert_eq!(tree.kind(), Some(&parser_kind(&["Command", "open"])));
    }

    #[test]
    fn malformed_renamings_report_original_offsets_instead_of_dropping_effects() {
        for source in [
            "open Library renaming",
            "open Library renaming x",
            "open Library renaming x ->",
            "open Library renaming x y",
            "open Library renaming x -> y,",
            "open Library renaming x -> y z",
            "open Library renaming x -> y, 1 -> z",
            "open Library renaming x -> (y)",
            "open Library «renaming» x -> y",
        ] {
            assert!(super::super::parse(source.as_bytes()).is_err(), "{source}");
        }
        let source = "/- 🦀 -/\r\nopen Library renaming x -> y, 1 -> z";
        assert_eq!(
            super::super::parse(source.as_bytes())
                .unwrap_err()
                .primary_offset(),
            Some(BytePos(source.find("1 ->").unwrap()))
        );
    }

    #[test]
    fn renamed_command_wrappers_preserve_the_body_and_partition() {
        let source = "/- 🦀 -/\r\nopen Library renaming x -> y in\r\ntheorem yes : y = 7 := by rfl\r\ndef after : Nat := 8";
        let parts = partition(source.as_bytes()).unwrap();
        assert_eq!(parts.len(), 2);
        assert_eq!([parts[0].1, parts[1].1].concat(), source.as_bytes());
        let Some(ScopeCommand::In { head, body }) = super::super::parse(parts[0].1).unwrap() else {
            panic!("temporary scope expected");
        };
        assert!(matches!(
            super::super::parse(&parts[0].1[..head]).unwrap(),
            Some(ScopeCommand::OpenRenaming { .. })
        ));
        assert_eq!(body, source.find("theorem").unwrap());
        assert_eq!(wrapper_body(parts[0].1).unwrap(), Some(body));
    }
}
