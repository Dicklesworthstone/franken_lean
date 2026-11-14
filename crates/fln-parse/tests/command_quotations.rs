//! Command quotation envelopes and captures from the pinned Lean frontend.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::extensions::{FileGrammar, with_grammar};
use fln_parse::parse_source_command;
use fln_syntax::tree::Syntax;

fn nodes<'a>(syntax: &'a Syntax, name: &[&str]) -> Vec<&'a Syntax> {
    let expected = Name::from_components(name.iter().copied());
    let mut pending = vec![syntax];
    let mut found = Vec::new();
    while let Some(node) = pending.pop() {
        if node.kind() == Some(&expected) {
            found.push(node);
        }
        if let Syntax::Node { args, .. } = node {
            pending.extend(args.iter().rev());
        }
    }
    found
}

fn declare(grammar: &mut FileGrammar, source: &str) -> Syntax {
    let active = grammar.grammar();
    let parsed = with_grammar(&active, || parse_source_command(source.as_bytes()))
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
    grammar.declare(parsed.syntax()).unwrap();
    parsed.syntax().clone()
}

#[test]
fn command_quotations_preserve_their_envelope_and_identifier_captures() {
    let mut grammar = FileGrammar::new(false, &[], None).unwrap();
    for (source, capture_kind) in [
        (
            r#"macro "named_value " n:ident " := " v:term : command => `(def $n : Nat := $v)"#,
            vec!["Lean", "Parser", "Command", "declId", "antiquot"],
        ),
        (
            r#"macro "named_theorem " n:ident " : " ty:term " := " p:term : command => `(theorem $n:ident : $ty := $p)"#,
            vec!["ident", "antiquot"],
        ),
    ] {
        let syntax = declare(&mut grammar, source);
        let quoted = nodes(&syntax, &["Lean", "Parser", "Command", "quot"]);
        assert_eq!(quoted.len(), 1);
        assert_eq!(nodes(quoted[0], &capture_kind).len(), 1);
        assert_eq!(nodes(&syntax, &["Lean", "Parser", "Term", "quot"]).len(), 0);
    }
    let active = grammar.grammar();
    let parsed = with_grammar(&active, || {
        parse_source_command(b"named_value answer := 42")
    })
    .unwrap();
    assert!(with_grammar(&active, || {
        fln_parse::extensions::is_active_command_macro(parsed.syntax())
    }));
    let expanded = grammar.expand(parsed.syntax()).unwrap();
    let identifiers = nodes(&expanded, &["Lean", "Parser", "Command", "declId"]);
    assert_eq!(identifiers.len(), 1);
    let Syntax::Node { args, .. } = identifiers[0] else {
        unreachable!()
    };
    assert!(
        matches!(&args[0], Syntax::Ident { val, .. } if *val == Name::from_components(["answer"]))
    );
    let declaration = parsed.with_expanded_command_declaration(expanded).unwrap();
    assert!(declaration.into_definition().is_some());
}

#[test]
fn command_captures_are_distinct_from_ambiguous_term_captures() {
    let mut grammar = FileGrammar::new(false, &[], None).unwrap();
    let syntax = declare(
        &mut grammar,
        r#"macro "pass_command " c:command : command => `($c:command)"#,
    );
    let quoted = nodes(&syntax, &["Lean", "Parser", "Command", "quot"]);
    assert_eq!(quoted.len(), 1);
    assert_eq!(
        nodes(quoted[0], &["command", "pseudo", "antiquot"]).len(),
        1
    );
    let term = declare(
        &mut grammar,
        r#"macro "term_capture " x:term : term => `($x)"#,
    );
    assert_eq!(nodes(&term, &["Lean", "Parser", "Term", "quot"]).len(), 1);
    assert!(nodes(&term, &["Lean", "Parser", "Command", "quot"]).is_empty());

    let active = grammar.grammar();
    let parsed = with_grammar(&active, || {
        parse_source_command(b"pass_command def callerName : Nat := 7")
    })
    .unwrap();
    let expanded = grammar.expand(parsed.syntax()).unwrap();
    let expected = parse_source_command(b"def callerName : Nat := 7").unwrap();
    assert_eq!(expanded.kind(), expected.syntax().kind());
    let declarations = nodes(&expanded, &["Lean", "Parser", "Command", "declId"]);
    let Syntax::Node { args, .. } = declarations[0] else {
        unreachable!()
    };
    assert!(
        matches!(&args[0], Syntax::Ident { val, .. } if *val == Name::from_components(["callerName"]))
    );
}

#[test]
fn quoted_macros_preserve_string_captures_and_the_inner_escape_frame() {
    let mut grammar = FileGrammar::new(false, &[], None).unwrap();
    let syntax = declare(
        &mut grammar,
        r#"macro "make_identity " head:str : command => `(macro $head:str x:term : term => `($$x))"#,
    );
    assert_eq!(
        nodes(&syntax, &["Lean", "Parser", "Command", "quot"]).len(),
        1
    );
    assert_eq!(nodes(&syntax, &["Lean", "Parser", "Term", "quot"]).len(), 1);
    assert_eq!(nodes(&syntax, &["str", "antiquot"]).len(), 1);
    let captures = nodes(&syntax, &["term", "pseudo", "antiquot"]);
    let Syntax::Node { args, .. } = captures[0] else {
        unreachable!()
    };
    assert!(matches!(&args[1], Syntax::Node { args, .. } if args.len() == 1));
}

#[test]
fn declaration_name_coercions_refuse_non_identifier_captures() {
    for source in [
        r#"macro "bad_term_name " n:term : command => `(def $n : Nat := 1)"#,
        r#"macro "bad_string_name " n:str : command => `(def $n : Nat := 1)"#,
        r#"macro "bad_optional_name " n:ident? : command => `(def $n : Nat := 1)"#,
    ] {
        let mut grammar = FileGrammar::new(false, &[], None).unwrap();
        let active = grammar.grammar();
        let parsed = with_grammar(&active, || parse_source_command(source.as_bytes())).unwrap();
        assert_eq!(
            grammar.declare(parsed.syntax()).unwrap_err(),
            "a macro syntax construction with incompatible value types",
            "{source}"
        );
    }
}

#[test]
fn command_quotation_slots_refuse_wrong_capture_kinds_and_trailing_commands() {
    let grammar = FileGrammar::new(false, &[], None).unwrap();
    let active = grammar.grammar();
    for source in [
        r#"macro "bad " n:term : command => `(def $n:term : Nat := 1)"#,
        r#"macro "bad " s:ident : command => `(macro $s:ident x:term : term => `($$x))"#,
        r#"macro "bad " c:term : command => `(command| $c:term)"#,
        r#"macro "bad" : command => `(def a : Nat := 1 def b : Nat := 2)"#,
        "def $outside : Nat := 1",
    ] {
        assert!(
            with_grammar(&active, || parse_source_command(source.as_bytes())).is_err(),
            "{source}"
        );
    }
    // A refusal must restore the thread-local quotation depth.
    assert!(parse_source_command(b"def escaped : Nat := $x").is_err());
}
