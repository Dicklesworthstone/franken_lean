//! Lower generated selective-open trees to their lexical scope transitions.
use super::*;

pub(super) fn parse(source: &[u8]) -> Result<Option<ScopeCommand>, DefinitionParseError> {
    let parsed = crate::parse_source_command(source)?;
    let syntax = parsed.syntax();
    if crate::extensions::is_active_command_macro(syntax) {
        return Ok(None);
    }
    Ok(selective_open(syntax))
}

fn selective_open(syntax: &Syntax) -> Option<ScopeCommand> {
    let Syntax::Node { kind, args, .. } = syntax else {
        return None;
    };
    let [
        _,
        Syntax::Node {
            kind: form,
            args: fields,
            ..
        },
    ] = args.as_slice()
    else {
        return None;
    };
    if kind != &parser_kind(&["Command", "open"]) {
        return None;
    }
    let [
        Syntax::Ident { val: namespace, .. },
        _,
        Syntax::Node { args: items, .. },
    ] = fields.as_slice()
    else {
        return None;
    };
    if form == &parser_kind(&["Command", "openHiding"]) {
        let names = items
            .iter()
            .map(|item| match item {
                Syntax::Ident { val, .. } => Some(val.clone()),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        return Some(ScopeCommand::OpenHiding {
            namespace: namespace.clone(),
            names,
        });
    }
    if form != &parser_kind(&["Command", "openRenaming"]) {
        return None;
    }
    let mut renames = Vec::new();
    for item in items.iter().step_by(2) {
        let Syntax::Node { kind, args, .. } = item else {
            return None;
        };
        let [
            Syntax::Ident { val: from, .. },
            _,
            Syntax::Ident { val: to, .. },
        ] = args.as_slice()
        else {
            return None;
        };
        if kind != &parser_kind(&["Command", "openRenamingItem"]) {
            return None;
        }
        renames.push((from.clone(), to.clone()));
    }
    Some(ScopeCommand::OpenRenaming {
        namespace: namespace.clone(),
        renames,
    })
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

    #[test]
    fn hiding_keeps_exact_names_and_command_local_scope() {
        let source = "/- 🦀 -/\r\nopen Library hiding «a.b» x.y in\r\ntheorem yes : kept = 7 := by rfl\r\ndef after : Nat := 8";
        let parts = partition(source.as_bytes()).unwrap();
        assert_eq!(parts.len(), 2);
        assert_eq!([parts[0].1, parts[1].1].concat(), source.as_bytes());
        let Some(ScopeCommand::In { head, body }) = super::super::parse(parts[0].1).unwrap() else {
            panic!("temporary scope expected");
        };
        assert_eq!(
            super::super::parse(&parts[0].1[..head]).unwrap(),
            Some(ScopeCommand::OpenHiding {
                namespace: Name::from_components(["Library"]),
                names: vec![
                    Name::from_components(["a.b"]),
                    Name::from_components(["x", "y"]),
                ],
            })
        );
        assert_eq!(body, source.find("theorem").unwrap());
        assert_eq!(wrapper_body(parts[0].1).unwrap(), Some(body));
        for bad in [
            "open Library hiding",
            "open Library hiding (x)",
            "open Library hiding x, y",
            "open Library hiding x -> y",
            "open Library hiding\nx",
        ] {
            assert!(super::super::parse(bad.as_bytes()).is_err(), "{bad}");
        }
    }
}
