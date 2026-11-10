//! Pure MacroM construction compiles to the existing exported template program.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::extensions::{FileGrammar, with_grammar};
use fln_parse::parse_source_command;
use fln_syntax::tree::Syntax;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn grammar() -> FileGrammar {
    FileGrammar::new(false, &[], Some(name("Construct")))
        .unwrap()
        .own_syntax_only()
}

fn pure(name_: &Name) -> bool {
    ["pure", "Pure.pure", "_root_.Pure.pure"]
        .into_iter()
        .any(|candidate| *name_ == name(candidate))
}

fn declare(file: &mut FileGrammar, source: &str) -> Result<(), &'static str> {
    let parsed = with_grammar(&file.grammar(), || parse_source_command(source.as_bytes()))
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    file.declare_with_macro_pure(parsed.syntax(), &pure)
        .map(|_| ())
}

fn expanded(file: &mut FileGrammar, source: &str) -> Syntax {
    let parsed = with_grammar(&file.grammar(), || parse_source_command(source.as_bytes()))
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    let expanded = file.expand(parsed.syntax()).unwrap();
    let mut pending = vec![&expanded];
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            assert!(
                !file.rules().any(|(registered, _)| registered == kind),
                "registered macro stayed unexpanded: {source}: {expanded:?}"
            );
            pending.extend(args);
        }
    }
    expanded
}

fn identifiers(syntax: &Syntax) -> Vec<Name> {
    let mut pending = vec![syntax];
    let mut found = Vec::new();
    while let Some(syntax) = pending.pop() {
        match syntax {
            Syntax::Ident { val, .. } => found.push(val.clone()),
            Syntax::Node { args, .. } => pending.extend(args.iter().rev()),
            _ => {}
        }
    }
    found
}

#[test]
fn returning_captures_preserves_their_names_without_fresh_hygiene() {
    for body in [
        "return x",
        "pure x",
        "Pure.pure x",
        "do return x",
        "do pure x",
        "do { let y := x; let z := y; return z }",
        "let y := x; return y",
        "do { let y ← (do { return x }); return y }",
    ] {
        let mut file = grammar();
        declare(
            &mut file,
            &format!("macro \"pass! \" x:term : term => {body}"),
        )
        .unwrap();
        let tree = expanded(&mut file, "def answer := pass! supplied");
        assert!(
            identifiers(&tree).contains(&name("supplied")),
            "{body}: {tree:?}"
        );
    }
}

#[test]
fn monadic_quotation_binds_compose_and_aliases_keep_lexical_scope() {
    let mut file = grammar();
    declare(
        &mut file,
        r#"macro "compose! " x:term : term => do {
            let saved := x;
            let q ← `(Nat.add $x 1);
            let x ← (do { let saved := q; return saved });
            let action := `(Nat.add $x $saved);
            action
        }"#,
    )
    .unwrap();
    let tree = expanded(&mut file, "def answer := compose! supplied");
    let names = identifiers(&tree);
    assert_eq!(names.iter().filter(|n| **n == name("supplied")).count(), 2);
    let additions: Vec<_> = names
        .iter()
        .filter(|n| n.erase_macro_scopes() == name("Nat.add"))
        .collect();
    assert_eq!(additions.len(), 2, "{tree:?}");
    assert_eq!(
        additions[0], additions[1],
        "quotations share the invocation scope"
    );
    assert_ne!(*additions[0], name("Nat.add"));
}

#[test]
fn pure_construction_replays_across_module_boundaries_and_rule_fallbacks() {
    let mut producer = grammar();
    declare(&mut producer, "syntax \"choose! \" term : term").unwrap();
    declare(
        &mut producer,
        "macro_rules | `(choose! $x) => do { let result := x; return result }",
    )
    .unwrap();
    declare(
        &mut producer,
        "macro_rules | `(choose! 0) => do { let result ← `(42); return result }",
    )
    .unwrap();
    let exported = producer.export_native().unwrap();
    let mut consumer = grammar();
    consumer.import_native(&exported).unwrap();
    let tree = expanded(&mut consumer, "def result := choose! supplied");
    assert!(identifiers(&tree).contains(&name("supplied")));
    let tree = expanded(&mut consumer, "def result := choose! 0");
    assert!(format!("{tree:?}").contains("42"));
    assert!(consumer.export_native().unwrap().is_empty());
}

#[test]
fn monadic_and_capture_types_refuse_before_publishing_a_rule() {
    for declaration in [
        r#"macro "bad! " x:term : term => return `(Nat.add $x 1)"#,
        r#"macro "bad! " x:term : term => pure `(Nat.add $x 1)"#,
        r#"macro "bad! " x:term : term => do { let y ← x; return y }"#,
        r#"macro "bad! " x:term : term => do { let y := `(Nat.add $x 1); return y }"#,
        r#"macro "bad! " x:term : tactic => return x"#,
        r#"macro "bad! " xs:term,* : term => return xs"#,
        r#"macro "bad! " x:(term)? : term => return x"#,
        r#"macro "bad! " x:term : term => do { let y := `(Nat.add $x 1); `($y) }"#,
        r#"macro "bad! " x:term : term => do { let y ← `(Nat.add $x 1); `($y:ident) }"#,
    ] {
        let mut file = grammar();
        assert!(declare(&mut file, declaration).is_err(), "{declaration}");
        assert!(file.rules().next().is_none(), "{declaration}");
        assert!(file.declared().is_empty(), "{declaration}");
    }
}

#[test]
fn unsupported_effects_and_shadowed_pure_do_not_become_templates() {
    for body in [
        "do { Lean.Macro.throwUnsupported; return x }",
        "do { let mut y := x; return y }",
        "do { let pure := x; pure x }",
        "do { let y ← unknownAction; return x }",
        "do { let y ← (do { let privateValue := x; return privateValue }); return privateValue }",
    ] {
        let mut file = grammar();
        declare(
            &mut file,
            &format!("macro \"blocked! \" x:term : term => {body}"),
        )
        .unwrap();
        assert!(file.rules().next().is_none(), "{body}");
    }
    let mut file = grammar();
    let parsed = with_grammar(&file.grammar(), || {
        parse_source_command(b"macro \"blocked! \" x:term : term => pure x")
    })
    .unwrap();
    file.declare_with_macro_pure(parsed.syntax(), &|_| false)
        .unwrap();
    assert!(file.rules().next().is_none());
}

#[test]
fn captured_literal_kinds_can_return_as_terms_but_sequence_aliases_remain_sequences() {
    for category in ["ident", "num", "str"] {
        let mut file = grammar();
        declare(
            &mut file,
            &format!("macro \"literal! \" x:{category} : term => return x"),
        )
        .unwrap();
        let operand = match category {
            "ident" => "supplied",
            "num" => "42",
            _ => "\"hello\"",
        };
        expanded(&mut file, &format!("def answer := literal! {operand}"));
    }
    let mut file = grammar();
    declare(
        &mut file,
        r#"macro "list![" xs:term,* "]" : term => do {
            let ys := xs;
            `([$ys,*])
        }"#,
    )
    .unwrap();
    let tree = expanded(&mut file, "def answer := list![a, b]");
    let names = identifiers(&tree);
    assert!(names.contains(&name("a")) && names.contains(&name("b")));
}

#[test]
fn duplicating_construction_is_bounded_and_a_refusal_leaves_the_grammar_reusable() {
    let mut body = String::from("do { let a0 ← `(Nat.add $x $x); ");
    for index in 1..16 {
        body.push_str(&format!(
            "let a{index} ← `(Nat.add $a{} $a{}); ",
            index - 1,
            index - 1
        ));
    }
    body.push_str("return a15 }");
    let mut file = grammar();
    let refused = declare(
        &mut file,
        &format!("macro \"grow! \" x:term : term => {body}"),
    )
    .unwrap_err();
    assert!(refused.contains("budget"), "{refused}");
    assert!(file.rules().next().is_none());
    assert!(file.declared().is_empty());
    declare(
        &mut file,
        r#"macro "retry! " x:term : term => do { let y := x; return y }"#,
    )
    .unwrap();
    let tree = expanded(&mut file, "def answer := retry! supplied");
    assert!(identifiers(&tree).contains(&name("supplied")));

    // An oversized replacement must also leave an existing macro_rules chain
    // intact, rather than silently publishing an unsupported-rule barrier.
    declare(&mut file, r#"syntax "growRule! " term : term"#).unwrap();
    declare(&mut file, "macro_rules | `(growRule! $x) => return x").unwrap();
    let before = file.export_native().unwrap();
    let refused = declare(
        &mut file,
        &format!("macro_rules | `(growRule! $x) => {body}"),
    )
    .unwrap_err();
    assert!(refused.contains("budget"), "{refused}");
    assert_eq!(file.export_native().unwrap(), before);
    let tree = expanded(&mut file, "def stillUsable := growRule! supplied");
    assert!(identifiers(&tree).contains(&name("supplied")));
}
