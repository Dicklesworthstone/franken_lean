//! Module-local macro deltas are distinct from inherited fallback chains.
use super::tests::{declare, grammar, parses};
use super::*;

fn library() -> (FileGrammar, Name) {
    let mut file = grammar("Core");
    declare(
        &mut file,
        "syntax (name := chooseSyntax) \"choose! \" term:max : term",
    );
    declare(&mut file, "macro_rules | `(choose! $x) => `($x)");
    (file, Name::from_components(["chooseSyntax"]))
}
fn cases(file: &FileGrammar, kind: &Name) -> usize {
    file.rules.get(kind).map_or(0, |rule| rule.cases().count())
}

#[test]
fn exports_are_deltas_and_a_forwarding_module_has_no_macro_effect() {
    let (core, kind) = library();
    let mut extension = grammar("Extension");
    extension
        .import_native(&core.export_native().unwrap())
        .unwrap();
    assert!(extension.export_native().unwrap().is_empty());
    declare(
        &mut extension,
        "macro_rules | `(choose! 0) => `(1) | `(choose! 1) => `(2)",
    );
    let delta = extension.export_native().unwrap();
    assert!(delta.declarations.is_empty());
    assert_eq!(delta.rules[&kind].cases().count(), 2);
    assert_eq!(cases(&extension, &kind), 3);
    let mut forward = grammar("Forward");
    forward
        .import_native(&core.export_native().unwrap())
        .unwrap();
    forward.import_native(&delta).unwrap();
    assert_eq!(cases(&forward, &kind), 3);
    assert!(forward.export_native().unwrap().is_empty());
    let before = cases(&forward, &kind);
    forward
        .import_native(&forward.export_native().unwrap())
        .unwrap();
    assert_eq!(cases(&forward, &kind), before);
}

#[test]
fn importing_a_new_delta_retains_the_callers_own_rule_prefix() {
    let (core, kind) = library();
    let mut extension = grammar("Extension");
    extension
        .import_native(&core.export_native().unwrap())
        .unwrap();
    declare(&mut extension, "macro_rules | `(choose! 0) => `(1)");
    let mut consumer = grammar("Consumer");
    consumer
        .import_native(&core.export_native().unwrap())
        .unwrap();
    declare(&mut consumer, "macro_rules | `(choose! 0) => `(2)");
    let own = consumer.export_native().unwrap();
    consumer
        .import_native(&extension.export_native().unwrap())
        .unwrap();
    assert_eq!(cases(&consumer, &kind), 3);
    assert_eq!(consumer.export_native().unwrap(), own);
    assert_eq!(consumer.rules[&kind].rhs, own.rules[&kind].rhs);
}

#[test]
fn missing_target_refuses_before_installing_any_category_or_rule() {
    let (core, kind) = library();
    let mut consumer = grammar("Consumer");
    let exported = core.export_native().unwrap();
    let mut orphan = NativeSyntaxModule {
        rules: exported.rules.clone(),
        ..NativeSyntaxModule::default()
    };
    orphan
        .categories
        .insert(Name::from_components(["fresh"]), IdentBehavior::Default);
    assert!(consumer.import_native(&orphan).is_err());
    assert!(
        !consumer
            .categories
            .contains_key(&Name::from_components(["fresh"]))
    );
    assert_eq!(cases(&consumer, &kind), 0);
    assert!(consumer.native_rule_counts.is_empty());
    consumer.import_native(&exported).unwrap();
    consumer.import_native(&orphan).unwrap();
    assert!(
        consumer
            .categories
            .contains_key(&Name::from_components(["fresh"]))
    );
}

#[test]
fn combined_fallback_budget_is_checked_before_publication() {
    let (core, kind) = library();
    let mut consumer = grammar("Consumer");
    consumer
        .import_native(&core.export_native().unwrap())
        .unwrap();
    let mut incoming = flat_case(&core.rules[&kind]);
    incoming.fallbacks = (1..MAX_TEMPLATE_NODES)
        .map(|_| flat_case(&core.rules[&kind]))
        .collect();
    let mut invalid = NativeSyntaxModule {
        rules: BTreeMap::from([(kind.clone(), Arc::new(incoming))]),
        ..NativeSyntaxModule::default()
    };
    invalid
        .categories
        .insert(Name::from_components(["fresh"]), IdentBehavior::Default);
    assert_eq!(
        consumer.import_native(&invalid),
        Err("native macro rule alternatives past the budget")
    );
    assert_eq!(cases(&consumer, &kind), 1);
    assert!(
        !consumer
            .categories
            .contains_key(&Name::from_components(["fresh"]))
    );
    assert!(consumer.export_native().unwrap().is_empty());
    assert!(parses(&consumer, "def x := choose! 2"));
}

#[test]
fn unsupported_imported_registration_cannot_resurrect_an_old_rule_on_replay() {
    let (core, kind) = library();
    let mut consumer = grammar("Consumer");
    consumer
        .import_native(&core.export_native().unwrap())
        .unwrap();
    declare(
        &mut consumer,
        "macro_rules | `(choose! $x) => do pure `($x)",
    );
    assert_eq!(cases(&consumer, &kind), 0);
    assert!(consumer.export_native().is_err());
}
