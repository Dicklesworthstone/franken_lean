//! Named pattern syntax must stay a pattern across collection and do parsers.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::parse_definition;
use fln_syntax::source::SourceInfo;
use fln_syntax::tree::Syntax;

fn nodes<'a>(syntax: &'a Syntax, kind: &Name) -> Vec<&'a [Syntax]> {
    let mut pending = vec![syntax];
    let mut found = Vec::new();
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node {
            kind: actual, args, ..
        } = syntax
        {
            if actual == kind {
                found.push(args.as_slice());
            }
            pending.extend(args.iter().rev());
        }
    }
    found
}
fn named() -> Name {
    Name::from_components(["Lean", "Parser", "Term", "namedPattern"])
}

#[test]
fn record_patterns_keep_nested_aliases_fields_ellipsis_and_original_spans() {
    for source in [
        "def f : R -> Nat\r\n | { «𝒃» /-field-/ := all@(.some x), nested := { value := y, .. }, .. : R } => x\r\n",
        "def f (r : R) : Nat := match r with | { parent.value := x, other := _ } => x",
        "def f : R -> Nat | { value := x\n                     other := y } => x",
    ] {
        let parsed = parse_definition(source.as_bytes())
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
        let records = nodes(
            parsed.syntax(),
            &Name::from_components(["Lean", "Parser", "Term", "structInst"]),
        );
        assert!(!records.is_empty());
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        for record in records {
            assert_eq!(record.len(), 6);
            for (index, spelling) in [(0, "{"), (5, "}")] {
                let Syntax::Atom {
                    info: SourceInfo::Original { pos, end_pos, .. },
                    val,
                } = &record[index]
                else {
                    panic!("record punctuation lost original span")
                };
                assert_eq!(val, spelling);
                assert_eq!(
                    &parsed.source_view().normalized().as_bytes()[pos.0..end_pos.0],
                    spelling.as_bytes()
                );
            }
        }
    }
}

#[test]
fn malformed_record_patterns_are_not_accepted_as_constructor_binders() {
    for source in [
        "def f : R -> Nat | { value := } => 0",
        "def f : R -> Nat | { value := x, , other := y } => 0",
        "def f : R -> Nat | { .., value := x } => 0",
        "def f : R -> Nat | { value := x : } => 0",
        "def f : R -> Nat | { old with value := x } => 0",
        "def f : R -> Nat | { value := (x } => 0",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}

#[test]
fn named_constructor_arguments_keep_labels_nested_patterns_and_original_spans() {
    let source =
        "def f : T -> Nat\r\n  | .mk («𝒃» /-label-/ := whole@(.some x)) (a := _) .. => x\r\n";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    let arguments = nodes(
        parsed.syntax(),
        &Name::from_components(["Lean", "Parser", "Term", "namedArgument"]),
    );
    assert_eq!(arguments.len(), 2);
    assert_eq!(arguments[0].len(), 5);
    assert!(
        matches!(&arguments[0][1], Syntax::Ident { val, .. } if val == &Name::from_components(["𝒃"]))
    );
    assert_eq!(arguments[0][3].kind(), Some(&named()));
    assert_eq!(nodes(parsed.syntax(), &named()).len(), 1);
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    for argument in arguments {
        for (index, spelling) in [(0, "("), (2, ":="), (4, ")")] {
            let Syntax::Atom {
                info: SourceInfo::Original { pos, end_pos, .. },
                val,
            } = &argument[index]
            else {
                panic!("named-argument punctuation must retain original spans")
            };
            assert_eq!(val, spelling);
            assert_eq!(
                &parsed.source_view().normalized().as_bytes()[pos.0..end_pos.0],
                spelling.as_bytes()
            );
        }
    }
}

#[test]
fn collections_preserve_nested_aliases_as_constructor_arguments() {
    for (source, count) in [
        (
            "def f : List Nat -> List Nat | outer@(inner@(x :: xs)) => inner | [] => []",
            2,
        ),
        (
            "def f : List Nat -> List Nat | whole@ /-trivia-/ (x :: xs) => whole | [] => []",
            1,
        ),
        ("def f : List Nat -> Nat | x@a :: rest => x | [] => 0", 1),
        (
            "def f : List (List Nat) -> Nat | [whole@(x :: xs)] => x | _ => 0",
            1,
        ),
        (
            "def f : List Nat -> List Nat | whole@([x, y]) => whole | _ => []",
            1,
        ),
        (
            "def f : Option (List Nat) -> List Nat | .some whole@([x]) => whole | _ => []",
            1,
        ),
    ] {
        let parsed = parse_definition(source.as_bytes())
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
        assert_eq!(nodes(parsed.syntax(), &named()).len(), count, "{source}");
    }
}

#[test]
fn an_unparenthesized_alias_binds_tighter_than_cons() {
    let parsed = parse_definition(b"def f : List Nat -> Nat | x@a :: rest => x | [] => 0").unwrap();
    let cons = nodes(parsed.syntax(), &Name::from_components(["term_::_"]));
    assert_eq!(cons.len(), 1);
    assert_eq!(cons[0][0].kind(), Some(&named()));
    assert!(
        matches!(&cons[0][2], Syntax::Ident { val, .. } if val == &Name::from_components(["rest"]))
    );
}

#[test]
fn do_headers_use_named_pattern_slots_not_explicit_application() {
    for arrow in ["<-", "←", ":="] {
        let source = format!(
            "def f : Nat := do\r\n  let «𝒙»@(Pair.mk x y) /-keep-/ {arrow} action\r\n  return x"
        );
        let parsed = parse_definition(source.as_bytes()).unwrap();
        let aliases = nodes(parsed.syntax(), &named());
        assert_eq!(aliases.len(), 1, "{source}");
        let alias = aliases[0];
        assert_eq!(alias.len(), 4);
        assert!(
            matches!(&alias[0], Syntax::Ident {val, ..} if val == &Name::from_components(["𝒙"]))
        );
        assert!(
            matches!(&alias[2], Syntax::Node {kind,args,..} if kind == &Name::from_components(["null"]) && args.is_empty())
        );
        let Syntax::Atom {
            info: SourceInfo::Original { pos, end_pos, .. },
            val,
        } = &alias[1]
        else {
            panic!("source @ must retain its original span")
        };
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(val, "@");
        assert_eq!(
            &parsed.source_view().normalized().as_bytes()[pos.0..end_pos.0],
            b"@"
        );
    }
}

#[test]
fn named_equality_assumptions_are_not_reclassified_as_do_annotations() {
    for source in [
        "def f : Nat := do let whole@h : Nat <- action; return whole",
        "def f : Nat := do let whole@h:Nat := value; return whole",
        "def f : Nat := do let whole@h:(Pair.mk x y) <- action; return x",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
    // A parenthesized payload is complete before the binding's type annotation.
    let parsed =
        parse_definition(b"def f : Nat := do let whole@(Pair.mk x y) : Pair <- action; return x")
            .unwrap();
    assert_eq!(nodes(parsed.syntax(), &named()).len(), 1);
    // Ordinary named bindings and explicit calls outside patterns are untouched.
    let parsed = parse_definition(b"def f : Nat := do let x : Nat <- @action; return x").unwrap();
    assert!(nodes(parsed.syntax(), &named()).is_empty());
}

#[test]
fn nested_collection_aliases_parse_on_a_small_host_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut pattern = String::from("[x]");
            for index in 0..256 {
                pattern = format!("a{index}@({pattern})");
            }
            let source = format!("def f : List Nat -> Nat | {pattern} => x | _ => 0");
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(nodes(parsed.syntax(), &named()).len(), 256);
        })
        .unwrap()
        .join()
        .unwrap();
}
