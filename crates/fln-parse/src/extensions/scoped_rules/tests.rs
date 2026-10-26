use super::*;

fn grammar(name: &str) -> FileGrammar {
    FileGrammar::new(false, &[], Some(Name::from_components([name])))
        .unwrap()
        .own_syntax_only()
}
fn declare(file: &mut FileGrammar, source: &str) {
    if let Some(control) = crate::command_scope::parse(source.as_bytes()).unwrap() {
        file.apply(&control);
    } else {
        let parsed = with_grammar(&file.grammar(), || {
            crate::parse_source_command(source.as_bytes())
        })
        .unwrap();
        file.declare(parsed.syntax()).unwrap();
    }
}
fn key() -> Name {
    Name::from_components(["picked"])
}
fn base() -> FileGrammar {
    let mut file = grammar("Core");
    declare(&mut file, "syntax (name := picked) \"picked! \" num : term");
    declare(&mut file, "macro_rules | `(picked! $n:num) => `($n)");
    file
}
fn scoped() -> FileGrammar {
    let mut file = base();
    declare(&mut file, "namespace Choice");
    declare(&mut file, "scoped macro_rules | `(picked! 0) => `(42)");
    declare(&mut file, "end Choice");
    file
}
fn count(grammar: &ActiveGrammar) -> usize {
    grammar.expander.as_ref().unwrap().rules[&key()]
        .cases()
        .count()
}

#[test]
fn namespace_activation_snapshots_and_temporary_views_are_independent() {
    let mut file = scoped();
    let before = file.grammar();
    assert_eq!(count(&before), 1);
    let temporary = file.grammar_opening(&[Name::from_components(["Choice"])]);
    assert_eq!(count(&temporary), 2);
    assert_eq!(count(&file.grammar()), 1);
    declare(&mut file, "section");
    declare(&mut file, "open scoped Choice");
    let active = file.grammar();
    assert_eq!(count(&active), 2);
    declare(&mut file, "end");
    assert_eq!(count(&file.grammar()), 1);
    assert_eq!(count(&active), 2);
    assert_eq!(count(&temporary), 2);
    assert_eq!(count(&before), 1);
}

#[test]
fn malformed_imported_scope_metadata_is_rejected_before_any_mutation() {
    let module = scoped().export_native().unwrap();
    for shape in 0..3 {
        let mut invalid = module.clone();
        match shape {
            0 => {
                invalid.rule_scopes.get_mut(&key()).unwrap().pop();
            }
            1 => {
                invalid
                    .rule_scopes
                    .insert(Name::from_components(["orphan"]), vec![None]);
            }
            _ => {
                invalid.rule_scopes.get_mut(&key()).unwrap()[0] = Some(Name::anonymous());
            }
        }
        let mut file = grammar("Consumer");
        let before = file.grammar();
        let generation = file.generation;
        assert!(file.import_native(&invalid).is_err());
        assert_eq!(file.generation, generation);
        assert!(file.export_native().unwrap().is_empty());
        assert!(Rc::ptr_eq(&file.grammar(), &before));
        file.import_native(&module).unwrap();
        assert_eq!(count(&file.grammar()), 1);
        declare(&mut file, "open scoped Choice");
        assert_eq!(count(&file.grammar()), 2);
    }
}

#[test]
fn local_expiry_and_exports_keep_scope_vectors_aligned() {
    let mut file = scoped();
    declare(&mut file, "section");
    declare(&mut file, "open scoped Choice");
    declare(&mut file, "local macro_rules | `(picked! 1) => `(11)");
    declare(&mut file, "macro_rules | `(picked! 2) => `(22)");
    assert_eq!(count(&file.grammar()), 4);
    let inside = file.export_native().unwrap();
    assert_eq!(inside.rules[&key()].cases().count(), 3);
    assert_eq!(
        inside.rule_scopes[&key()],
        vec![None, Some(Name::from_components(["Choice"])), None]
    );
    declare(&mut file, "end");
    assert_eq!(file.export_native().unwrap(), inside);
    assert_eq!(count(&file.grammar()), 2);
    declare(&mut file, "open scoped Choice");
    assert_eq!(count(&file.grammar()), 3);
}

#[test]
fn unsupported_scoped_registration_preserves_every_earlier_meaning() {
    let mut file = scoped();
    declare(&mut file, "namespace Choice");
    let before = file.export_native().unwrap();
    let generation = file.generation;
    let source = "scoped macro_rules | `(picked! 0) => `(7) | `($n) => `($n)";
    let parsed = with_grammar(&file.grammar(), || {
        crate::parse_source_command(source.as_bytes())
    })
    .unwrap();
    assert!(file.declare(parsed.syntax()).is_err());
    assert_eq!(file.generation, generation);
    assert_eq!(file.export_native().unwrap(), before);
    assert_eq!(count(&file.grammar()), 2);
}

#[test]
fn dependent_open_views_match_separate_commands_without_leaking_temporary_prefixes() {
    let make = || {
        let mut file = base();
        declare(&mut file, "namespace Library.Parser.Term");
        declare(&mut file, "scoped macro_rules | `(picked! 0) => `(42)");
        declare(&mut file, "end Library.Parser.Term");
        file
    };
    let names: Vec<_> = ["Library", "Parser", "Term"]
        .map(|name| Name::from_components([name]))
        .into();
    let mut grouped = make();
    let inactive = grouped.grammar();
    let temporary = grouped.grammar_opening(&names);
    assert_eq!(count(&temporary), 2);
    assert_eq!(count(&inactive), 1);
    assert!(grouped.top().opens.is_empty());
    declare(&mut grouped, "open Library Parser Term");
    let mut separate = make();
    for source in ["open Library", "open Parser", "open Term"] {
        declare(&mut separate, source);
    }
    let expected = vec![
        Name::from_components(["Library"]),
        Name::from_components(["Library", "Parser"]),
        Name::from_components(["Library", "Parser", "Term"]),
    ];
    assert_eq!(grouped.top().opens, expected);
    assert_eq!(separate.top().opens, expected);
    assert_eq!(count(&grouped.grammar()), 2);
    assert_eq!(count(&separate.grammar()), 2);
    let mut scoped_only = make();
    declare(&mut scoped_only, "open scoped Library Parser Term");
    assert!(scoped_only.top().opens.is_empty());
    assert_eq!(count(&scoped_only.grammar()), 1);
    // Repeating a simple open must not manufacture new activation epochs.
    let before = grouped.grammar();
    declare(&mut grouped, "open Library Parser Term");
    assert!(Rc::ptr_eq(&before, &grouped.grammar()));
}

#[test]
fn grammar_namespace_lookup_compares_structural_names_not_printed_prefixes() {
    let mut file = base();
    declare(&mut file, "namespace «Library.Parser».Term");
    declare(&mut file, "scoped macro_rules | `(picked! 0) => `(42)");
    declare(&mut file, "end «Library.Parser».Term");
    assert!(file.has_grammar_namespace(&Name::from_components(["Library.Parser"])));
    assert!(!file.has_grammar_namespace(&Name::from_components(["Library", "Parser"])));
    assert!(!file.has_grammar_namespace(&Name::from_components(["Library"])));
    assert!(!file.has_grammar_namespace(&key()));
    declare(&mut file, "open «Library.Parser» Term");
    assert_eq!(count(&file.grammar()), 2);
    assert_eq!(
        file.top().opens.last(),
        Some(&Name::from_components(["Library.Parser", "Term"]))
    );
}
