//! Scoped dictionaries are real source elaboration inputs, never unchecked proofs.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_elab::instances::{self, InstanceRegistry, imported, scoped};
use fln_elab::source::scope::{self, SourceScope};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn base() -> Engine {
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    seed.check_source_files(
        &[br#"
class Pick where
  value : Nat
def fallback : Pick := Pick.mk 1
def alpha : Pick := Pick.mk 2
def omega : Pick := Pick.mk 3
def later : Pick := Pick.mk 4
def chosen [p : Pick] : Nat := Pick.value
"#],
        &KVMap::new(),
        limits(),
    )
    .unwrap()
    .into_complete()
    .unwrap()
    .engine
}
fn names(env: &fln::Environment, active: &scoped::ActiveScopes) -> Vec<Name> {
    InstanceRegistry::read_with_scopes(env, active)
        .unwrap()
        .candidates(&n("Pick"))
        .iter()
        .map(|row| row.declaration.clone())
        .collect()
}
fn prove(env: fln::Environment, active: scoped::ActiveScopes, expected: u32) {
    let engine = Engine::from_environment(env);
    let source = format!("theorem selected : chosen = {expected} := by rfl");
    let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
    let scope = SourceScope {
        instance_scopes: active,
        ..SourceScope::default()
    };
    let candidate = scope::elaborate_definition(
        parsed.syntax(),
        engine.environment(),
        limits().admission.kernel,
        &scope,
    )
    .unwrap();
    let admitted = engine
        .admit_declarations(&[candidate], &KVMap::new(), limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(admitted.engine.environment().contains(&n("selected")));
    assert!(!engine.environment().contains(&n("selected")));
}

#[test]
fn imported_scoped_dictionaries_are_dormant_until_lexically_activated() {
    let base = base();
    let env = instances::register_instance(base.environment(), &n("fallback"), 1000).unwrap();
    let env = imported::register_instance(
        &env,
        &n("alpha"),
        &imported::InstanceParameters {
            priority: 1000,
            synth_order: vec![],
            scope: Some(n("Alpha")),
        },
    )
    .unwrap();
    let root = Engine::from_environment(env.clone()).logical_root(&KVMap::new());
    assert_eq!(
        names(&env, &scoped::ActiveScopes::default()),
        [n("fallback")]
    );
    prove(env.clone(), scoped::ActiveScopes::default(), 1);
    let mut active = scoped::ActiveScopes::default();
    active.activate(&env, &n("Alpha")).unwrap();
    assert_eq!(names(&env, &active), [n("alpha"), n("fallback")]);
    prove(env.clone(), active, 2);
    assert_eq!(
        Engine::from_environment(env.clone()).logical_root(&KVMap::new()),
        root
    );
    assert_eq!(
        InstanceRegistry::read(&env).unwrap().candidates(&n("Pick"))[0].declaration,
        n("fallback")
    );
}

#[test]
fn activation_order_not_namespace_sort_order_selects_equal_priority_instances() {
    let base = base();
    let env = scoped::register(base.environment(), &n("Alpha"), &n("alpha"), 1000).unwrap();
    let env = scoped::register(&env, &n("Omega"), &n("omega"), 1000).unwrap();
    for (first, second, winner) in [("Alpha", "Omega", 3), ("Omega", "Alpha", 2)] {
        let mut active = scoped::ActiveScopes::default();
        active.activate(&env, &n(first)).unwrap();
        let saved = active.clone();
        active.activate(&env, &n(second)).unwrap();
        // Repeated opening is not reinsertion and cannot switch the winner.
        active.activate(&env, &n(first)).unwrap();
        prove(env.clone(), active, winner);
        prove(env.clone(), saved, if first == "Alpha" { 2 } else { 3 });
    }
}

#[test]
fn later_registrations_share_the_activation_timeline_and_priority_still_wins() {
    let base = base();
    let env = scoped::register(base.environment(), &n("Alpha"), &n("alpha"), 1000).unwrap();
    let mut active = scoped::ActiveScopes::default();
    active.activate(&env, &n("Alpha")).unwrap();
    let env = instances::register_instance(&env, &n("fallback"), 1000).unwrap();
    prove(env.clone(), active.clone(), 1);
    let env = scoped::register(&env, &n("Alpha"), &n("later"), 1000).unwrap();
    assert_eq!(
        names(&env, &active),
        [n("later"), n("fallback"), n("alpha")]
    );
    prove(env.clone(), active.clone(), 4);
    let env = scoped::register(&env, &n("Alpha"), &n("alpha"), 2000).unwrap();
    prove(env.clone(), active.clone(), 2);
    // Returning to equal priority keeps alpha's original slot, not the update time.
    let env = scoped::register(&env, &n("Alpha"), &n("alpha"), 1000).unwrap();
    prove(env, active, 4);
}

#[test]
fn opening_before_a_namespace_has_registrations_does_not_lose_future_instances() {
    let base = base();
    let mut active = scoped::ActiveScopes::default();
    active.activate(base.environment(), &n("Future")).unwrap();
    let env = scoped::register(base.environment(), &n("Future"), &n("alpha"), 1000).unwrap();
    prove(env, active, 2);
}

#[test]
fn foreign_or_shortened_journals_cannot_reuse_lexical_activation_markers() {
    let base = base();
    let env = scoped::register(base.environment(), &n("Alpha"), &n("alpha"), 1000).unwrap();
    let mut active = scoped::ActiveScopes::default();
    active.activate(&env, &n("Alpha")).unwrap();
    let saved = active.clone();
    assert!(InstanceRegistry::read_with_scopes(base.environment(), &active).is_err());
    let other = scoped::register(base.environment(), &n("Alpha"), &n("omega"), 1000).unwrap();
    assert!(InstanceRegistry::read_with_scopes(&other, &active).is_err());
    assert!(active.activate(&other, &n("Omega")).is_err());
    assert_eq!(active, saved);
    assert_eq!(names(&env, &active), [n("alpha")]);
}

#[test]
fn invalid_registration_and_activation_publish_nothing() {
    let base = base();
    let env = scoped::register(base.environment(), &n("Alpha"), &n("alpha"), 1000).unwrap();
    for (namespace, declaration) in [
        (Name::anonymous(), n("omega")),
        (n("Beta"), n("missing")),
        (n("Beta"), n("Pick")),
        (n("Beta"), n("alpha")),
    ] {
        assert!(scoped::register(&env, &namespace, &declaration, 1000).is_err());
    }
    assert!(instances::set_instance(&env, &n("alpha"), 1000).is_err());
    assert!(instances::register_instance(&env, &n("alpha"), 1000).is_err());
    let mut active = scoped::ActiveScopes::default();
    assert!(active.activate(&env, &Name::anonymous()).is_err());
    assert_eq!(active, scoped::ActiveScopes::default());
    active.activate(&env, &n("Alpha")).unwrap();
    prove(env, active, 2);
}
