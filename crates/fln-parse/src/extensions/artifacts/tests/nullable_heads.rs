//! Nullable parser prefixes retain command boundaries across real imports.
use super::*;

fn unary(alias: &str, body: Descr) -> Descr {
    Descr::Unary(name(alias), Box::new(body))
}

fn choice(left: Descr, right: Descr) -> Descr {
    Descr::Binary(name("orelse"), Box::new(left), Box::new(right))
}

fn separated(item: Descr) -> Descr {
    Descr::SepBy {
        item: Box::new(item),
        separator: ",".into(),
        parser: Box::new(symbol(",")),
        trailing: false,
        at_least_one: false,
    }
}

fn command(body: Descr, scope: Option<&str>) -> ImportedSyntaxEntry {
    parser(
        "Library.nullableCommand",
        "command",
        scope,
        Descr::Node {
            kind: name("Library.nullableCommand"),
            prec: LEAD_PREC,
            body: Box::new(body),
        },
    )
}

#[test]
fn native_imported_nullable_prefixes_partition_and_parse_complete_commands() {
    let cases: &[(&str, &[&str])] = &[
        (
            r#"optional("native_maybe ") "native_done " ident"#,
            &["native_done x", "native_maybe native_done y"],
        ),
        (
            r#"many("native_again ") "native_done " ident"#,
            &["native_done x", "native_again native_again native_done y"],
        ),
        (
            r#"notFollowedBy("native_blocked ") "native_done " ident"#,
            &["native_done x"],
        ),
        (
            r#"sepBy("native_item", ",") "native_done " ident"#,
            &["native_done x", "native_item,native_item native_done y"],
        ),
        (r#"ppSpace "native_done " ident"#, &["native_done x"]),
        (r#"orelse("native_done ", ident)"#, &["native_done"]),
    ];
    for (items, invocations) in cases {
        let mut library = grammar();
        let declaration = format!("syntax (name := Library.nativeNullable) {items} : command");
        let syntax = parse(&library, &declaration).unwrap();
        library.declare(&syntax).unwrap();
        let mut consumer = grammar();
        consumer
            .import_native(&library.export_native().unwrap())
            .unwrap();
        let source = format!(
            "def before := 0\r\n{}\r\ndef after := 1\r\n",
            invocations.join("\r\n")
        );
        let commands = with_grammar(&consumer.grammar(), || {
            crate::command_scope::partition(source.as_bytes())
        })
        .unwrap();
        assert_eq!(commands.len(), invocations.len() + 2, "{items}");
        for (index, (at, bytes)) in commands.iter().enumerate() {
            assert_eq!(*bytes, &source.as_bytes()[at.0..at.0 + bytes.len()]);
            let parsed = parse(&consumer, std::str::from_utf8(bytes).unwrap()).unwrap();
            if index > 0 && index + 1 < commands.len() {
                assert!(contains(&parsed, "Library.nativeNullable"), "{items}");
            }
        }
        assert_eq!(
            commands
                .iter()
                .flat_map(|(_, bytes)| bytes.iter().copied())
                .collect::<Vec<_>>(),
            source.as_bytes()
        );
        assert!(consumer.export_native().unwrap().is_empty());
    }
}

#[test]
fn scoped_artifact_nullable_prefixes_partition_without_activating_syntax() {
    for (prefix, invocations) in [
        (
            unary("optional", symbol("artifact_prefix")),
            vec!["artifact_done x", "artifact_prefix artifact_done y"],
        ),
        (
            unary("many", symbol("artifact_prefix")),
            vec![
                "artifact_done x",
                "artifact_prefix artifact_prefix artifact_done y",
            ],
        ),
        (
            unary("notFollowedBy", symbol("artifact_prefix")),
            vec!["artifact_done x"],
        ),
        (
            separated(symbol("artifact_prefix")),
            vec![
                "artifact_done x",
                "artifact_prefix,artifact_prefix artifact_done y",
            ],
        ),
    ] {
        let mut file = grammar();
        file.import_artifact(&ImportedSyntaxModule {
            entries: vec![
                token("artifact_prefix", Some("NullableCommands")),
                token("artifact_done", Some("NullableCommands")),
                command(
                    sequence(
                        prefix,
                        sequence(symbol("artifact_done"), Descr::Const(name("ident"))),
                    ),
                    Some("NullableCommands"),
                ),
            ],
        })
        .unwrap();
        let source = format!(
            "section\r\nopen scoped NullableCommands\r\n{}\r\nend\r\ndef after := 1\r\n",
            invocations.join("\r\n")
        );
        let commands = with_grammar(&file.grammar(), || {
            crate::command_scope::partition(source.as_bytes())
        })
        .unwrap();
        assert_eq!(commands.len(), invocations.len() + 4);
        assert!(!file.grammar().table().contains("artifact_done"));
        for invocation in &invocations {
            assert!(parse(&file, invocation).is_err());
        }
        file.apply(&ScopeCommand::Section(None));
        file.apply(&ScopeCommand::OpenScoped(vec![name("NullableCommands")]));
        for (index, invocation) in invocations.iter().enumerate() {
            assert!(contains(
                &parse(&file, invocation).unwrap(),
                "Library.nullableCommand"
            ));
            assert_eq!(
                commands[index + 2].1,
                format!("{invocation}\r\n").as_bytes()
            );
        }
        assert!(parse(&file, "artifact_prefix").is_err());
        assert!(parse(&file, "artifact_done").is_err());
        file.apply(&ScopeCommand::End(None));
        assert!(parse(&file, "artifact_done x").is_err());
        assert!(!file.grammar().table().contains("artifact_done"));
        assert_eq!(
            commands
                .iter()
                .flat_map(|(_, bytes)| bytes.iter().copied())
                .collect::<Vec<_>>(),
            source.as_bytes()
        );
    }
}

#[test]
fn incomplete_or_empty_artifact_command_starts_refuse_transactionally() {
    for body in [
        sequence(Descr::Cat(name("term"), 0), symbol("artifact_done")),
        sequence(
            unary("optional", Descr::Cat(name("term"), 0)),
            symbol("artifact_done"),
        ),
        choice(symbol("artifact_done"), Descr::Cat(name("term"), 0)),
        sequence(
            unary("notFollowedBy", Descr::Const(name("unknownAlias"))),
            symbol("artifact_done"),
        ),
        sequence(
            unary(
                "optional",
                Descr::NonReservedSymbol("artifact_prefix".into(), true),
            ),
            symbol("artifact_done"),
        ),
        unary("optional", symbol("artifact_done")),
        sequence(
            unary("many", unary("optional", symbol("artifact_prefix"))),
            symbol("artifact_done"),
        ),
        sequence(
            separated(unary("optional", symbol("artifact_prefix"))),
            symbol("artifact_done"),
        ),
    ] {
        let mut file = grammar();
        let before = file.grammar();
        let generation = file.generation;
        let result = file.import_artifact(&ImportedSyntaxModule {
            entries: vec![
                token("artifact_done", None),
                token("artifact_prefix", None),
                command(body.clone(), None),
            ],
        });
        assert!(result.is_err(), "unsupported start was admitted: {body:?}");
        assert_eq!(file.generation, generation);
        assert!(Rc::ptr_eq(&before, &file.grammar()));
        assert!(!file.grammar().table().contains("artifact_done"));
        assert!(file.artifact.imported.is_empty());
        assert_eq!(file.artifact.work, 0);
    }
}

#[test]
fn nullable_prefixes_check_every_builtin_head_without_promoting_later_atoms() {
    for prefix in [
        unary("optional", symbol("artifact_prefix")),
        unary("many", symbol("artifact_prefix")),
        unary("notFollowedBy", symbol("artifact_prefix")),
        separated(symbol("artifact_prefix")),
        choice(symbol("artifact_prefix"), Descr::Const(name("ppSpace"))),
    ] {
        let mut file = grammar();
        assert_eq!(
            file.import_artifact(&ImportedSyntaxModule {
                entries: vec![
                    token("artifact_prefix", None),
                    command(sequence(prefix, symbol("def")), None),
                ],
            }),
            Err("artifact leading parser overlaps a builtin token")
        );
        assert!(!file.grammar().table().contains("artifact_prefix"));
    }

    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            token("artifact_prefix", None),
            token("artifact_done", None),
            command(
                sequence(
                    unary("optional", symbol("artifact_prefix")),
                    sequence(symbol("artifact_done"), symbol("def")),
                ),
                None,
            ),
        ],
    })
    .unwrap();
    let source =
        b"def before := 0\nartifact_done def\nartifact_prefix artifact_done def\ndef after := 1\n";
    let commands =
        with_grammar(&file.grammar(), || crate::command_scope::partition(source)).unwrap();
    assert_eq!(commands.len(), 4);
    for (_, bytes) in &commands[1..3] {
        assert!(contains(
            &parse(&file, std::str::from_utf8(bytes).unwrap()).unwrap(),
            "Library.nullableCommand"
        ));
    }
}
