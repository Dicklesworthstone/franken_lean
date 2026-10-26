use super::*;

fn grammar(module: &str) -> FileGrammar {
    FileGrammar::new(false, &[], Some(Name::from_components([module])))
        .unwrap()
        .own_syntax_only()
}
fn declare(grammar: &mut FileGrammar, source: &str) {
    if let Some(control) = crate::command_scope::parse(source.as_bytes()).unwrap() {
        grammar.apply(&control);
    } else {
        let parsed = with_grammar(&grammar.grammar(), || {
            crate::parse_source_command(source.as_bytes())
        })
        .unwrap();
        grammar.declare(parsed.syntax()).unwrap();
    }
}
fn base() -> FileGrammar {
    let mut g = grammar("Core");
    declare(&mut g, "syntax (name := selected) \"select! \" num : term");
    declare(&mut g, "macro_rules | `(select! $n:num) => `($n)");
    g
}
fn key() -> Name {
    Name::from_components(["selected"])
}

#[test]
fn scope_exit_preserves_old_grammar_snapshots_and_invalidates_new_ones() {
    let mut g = base();
    let original = g.grammar();
    declare(&mut g, "section");
    declare(&mut g, "local macro_rules | `(select! 0) => `(10)");
    let inside = g.grammar();
    assert_eq!(
        inside.expander.as_ref().unwrap().rules[&key()]
            .cases()
            .count(),
        2
    );
    declare(&mut g, "end");
    let outside = g.grammar();
    assert_eq!(
        outside.expander.as_ref().unwrap().rules[&key()]
            .cases()
            .count(),
        1
    );
    assert_eq!(
        inside.expander.as_ref().unwrap().rules[&key()]
            .cases()
            .count(),
        2
    );
    assert_eq!(
        original.expander.as_ref().unwrap().rules[&key()]
            .cases()
            .count(),
        1
    );
    assert!(!Rc::ptr_eq(&inside, &outside));
    assert!(g.local_rule_depths.is_empty());
}

#[test]
fn imported_clauses_insert_after_local_prefix_with_aligned_lifetimes() {
    let module = base().export_native().unwrap();
    let mut extension = grammar("Extension");
    extension.import_native(&module).unwrap();
    declare(&mut extension, "macro_rules | `(select! 1) => `(21)");
    let delta = extension.export_native().unwrap();
    let mut consumer = grammar("Consumer");
    consumer.import_native(&module).unwrap();
    declare(&mut consumer, "section");
    declare(&mut consumer, "local macro_rules | `(select! 0) => `(10)");
    consumer.import_native(&delta).unwrap();
    assert_eq!(
        consumer.local_rule_depths[&key()],
        vec![Some(2), None, None]
    );
    assert!(consumer.export_native().unwrap().is_empty());
    declare(&mut consumer, "macro_rules | `(select! 2) => `(32)");
    declare(&mut consumer, "end");
    assert_eq!(consumer.rules[&key()].cases().count(), 3);
    assert_eq!(consumer.native_rule_counts[&key()], 2);
    assert_eq!(
        consumer.export_native().unwrap().rules[&key()]
            .cases()
            .count(),
        1
    );
    assert!(consumer.local_rule_depths.is_empty());
}

#[test]
fn mismatched_locality_metadata_refuses_export_and_import_without_mutation() {
    let module = base().export_native().unwrap();
    let mut extension = grammar("Extension");
    extension.import_native(&module).unwrap();
    declare(&mut extension, "macro_rules | `(select! 1) => `(21)");
    let delta = extension.export_native().unwrap();
    let mut consumer = grammar("Consumer");
    consumer.import_native(&module).unwrap();
    declare(&mut consumer, "local macro_rules | `(select! 0) => `(10)");
    consumer.local_rule_depths.get_mut(&key()).unwrap().pop();
    let before = Arc::clone(&consumer.rules);
    let counts = consumer.native_rule_counts.clone();
    assert!(consumer.export_native().is_err());
    assert!(consumer.import_native(&delta).is_err());
    assert_eq!(consumer.rules, before);
    assert_eq!(consumer.native_rule_counts, counts);
}

#[test]
fn multiple_clauses_and_scope_depth_reuse_do_not_resurrect_expired_locals() {
    let mut g = base();
    for _ in 0..3 {
        declare(&mut g, "section");
        declare(
            &mut g,
            "local macro_rules | `(select! 0) => `(10) | `(select! 1) => `(11)",
        );
        assert_eq!(g.local_rule_depths[&key()], vec![Some(2), Some(2), None]);
        assert_eq!(g.export_native().unwrap().rules[&key()].cases().count(), 1);
        declare(&mut g, "end");
        assert_eq!(g.rules[&key()].cases().count(), 1);
        assert!(g.local_rule_depths.is_empty());
    }
}

fn try_declare(g: &mut FileGrammar, source: &str) -> Result<(), &'static str> {
    let parsed = with_grammar(&g.grammar(), || {
        crate::parse_source_command(source.as_bytes())
    })
    .expect("the registration itself is well-formed syntax");
    g.declare(parsed.syntax()).map(|_| ())
}

fn refused_without_mutation(g: &mut FileGrammar, source: &str) {
    let rules = Arc::clone(&g.rules);
    let interpolation = Arc::clone(&g.interpolation_kinds);
    let depths = g.local_rule_depths.clone();
    let inherited = g.native_rule_counts.clone();
    let generation = g.generation;
    let export = g.native_export_refusal;
    assert!(try_declare(g, source).is_err(), "{source}");
    assert_eq!(g.rules, rules);
    assert_eq!(g.interpolation_kinds, interpolation);
    assert_eq!(g.local_rule_depths, depths);
    assert_eq!(g.native_rule_counts, inherited);
    assert_eq!(g.generation, generation);
    assert_eq!(g.native_export_refusal, export);
}

#[test]
fn mixed_local_registration_refuses_all_targets_before_mutation() {
    let mut g = base();
    refused_without_mutation(
        &mut g,
        "local macro_rules | `(select! 0) => `(10) | `($term) => `(num| 2)",
    );
    // A refused builtin override neither shadows the known rule nor prevents
    // the same native clause from being installed in a subsequent request.
    declare(&mut g, "local macro_rules | `(select! 0) => `(10)");
    assert_eq!(g.rules[&key()].cases().count(), 2);
    assert_eq!(g.export_native().unwrap().rules[&key()].cases().count(), 1);
}

#[test]
fn local_clause_limit_refuses_without_erasing_the_global_chain() {
    let mut g = base();
    let single = modules::flat_case(&g.rules[&key()]);
    let mut many = single.clone();
    many.fallbacks = vec![single; MAX_TEMPLATE_NODES - 1];
    Arc::make_mut(&mut g.rules).insert(key(), Arc::new(many));
    let exported = g.export_native().unwrap();
    refused_without_mutation(&mut g, "local macro_rules | `(select! 0) => `(10)");
    assert_eq!(g.export_native().unwrap(), exported);
}

#[test]
fn malformed_local_template_does_not_change_other_valid_clauses() {
    let mut g = base();
    refused_without_mutation(
        &mut g,
        "local macro_rules | `(select! 0) => `(10) | `(select! $n:num) => `($unbound)",
    );
    refused_without_mutation(
        &mut g,
        "local macro_rules (kind := unavailableKind) | `(select! 0) => `(10)",
    );
    assert_eq!(g.rules[&key()].cases().count(), 1);
}
