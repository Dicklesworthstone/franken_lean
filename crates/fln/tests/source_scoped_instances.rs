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
            keys: Vec::new(),
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

fn checked(base: &Engine, source: &str) -> fln::SourceFileCheck {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
}

#[test]
fn source_scoped_attributes_and_ordinary_open_check_real_proofs() {
    let result = checked(
        &base(),
        include_str!("../../../examples/native_scoped_instances.lean"),
    );
    assert_eq!(result.theorems, 5);
    assert!(result.scope.instance_scopes.is_active(&n("Alternative")));
    assert!(result.scope.opened.contains(&n("Alternative")));
    assert_eq!(
        InstanceRegistry::read(result.engine.environment())
            .unwrap()
            .candidates(&n("Selection"))[0]
            .declaration,
        n("fallbackSelection")
    );
}

#[test]
fn compound_namespace_exit_restores_each_intermediate_activation() {
    let result = checked(
        &base(),
        r#"
attribute [instance] fallback
namespace A
attribute [scoped instance] omega
namespace B
attribute [scoped instance] alpha
end A.B
namespace A.B
theorem nested : chosen = 2 := by rfl
end B
theorem parent : chosen = 3 := by rfl
end A
theorem outside : chosen = 1 := by rfl
"#,
    );
    assert_eq!(result.theorems, 3);
    assert!(!result.scope.instance_scopes.is_active(&n("A")));
    assert!(!result.scope.instance_scopes.is_active(&n("A.B")));
}

#[test]
fn scoped_opening_does_not_open_names_and_file_boundaries_restore_visibility() {
    let base = checked(
        &base(),
        r#"
attribute [instance] fallback
namespace Alternative
def hidden : Nat := 7
attribute [scoped instance] alpha
end Alternative
"#,
    )
    .engine;
    assert!(
        base.check_source_files(
            &[b"open scoped Alternative\ndef wrong : Nat := hidden"],
            &KVMap::new(),
            limits()
        )
        .is_err()
    );
    let one = b"open scoped Alternative\ntheorem enabled : chosen = 2 := by rfl";
    let two = b"theorem disabled : chosen = 1 := by rfl";
    let result = base
        .check_source_files(&[one.as_slice(), two.as_slice()], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.theorems, 2);
    assert!(!result.scope.instance_scopes.is_active(&n("Alternative")));
    checked(
        &base,
        "open Alternative\ndef visible : Nat := hidden\ntheorem enabled : chosen = 2 := by rfl",
    );
}

#[test]
fn source_activation_order_and_later_global_registrations_are_not_reordered() {
    checked(
        &base(),
        r#"
attribute [instance] fallback
namespace Alpha
attribute [scoped instance] alpha
end Alpha
namespace Omega
attribute [scoped instance] omega
end Omega
open scoped Omega Alpha
theorem lastOpened : chosen = 2 := by rfl
open scoped Omega
theorem repeatedOpen : chosen = 2 := by rfl
attribute [instance] later
theorem newerGlobal : chosen = 4 := by rfl
namespace Alpha
attribute [scoped instance 2000] alpha
end Alpha
theorem reprioritized : chosen = 2 := by rfl
namespace Alpha
attribute [scoped instance] alpha
end Alpha
theorem originalSlot : chosen = 4 := by rfl
"#,
    );
}

#[test]
fn failed_scoped_commands_publish_neither_declarations_nor_partial_registrations() {
    let base = base();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "attribute [scoped instance] alpha",
        "namespace Alpha\nattribute [scoped instance] alpha missing",
        "namespace Alpha\nattribute [scoped instance] alpha Pick",
        "namespace Alpha\nattribute [scoped instance] alpha\nend Alpha\nopen scoped Alpha Missing",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(
            InstanceRegistry::read(base.environment())
                .unwrap()
                .instance_namespaces()
                .next()
                .is_none()
        );
    }
    checked(
        &base,
        "namespace Alpha\nattribute [scoped instance] alpha\nend Alpha\nopen scoped Alpha\ntheorem recovered : chosen = 2 := by rfl",
    );
}

#[test]
fn coercion_search_uses_the_same_scoped_view_as_ordinary_instance_search() {
    let seed = Engine::with_coercion_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let base = checked(
        &seed,
        r#"
structure Box where
  value : Nat
namespace Conversions
def boxToNat : Coe Box Nat := Coe.mk (fun b => b.value)
attribute [scoped instance] boxToNat
end Conversions
"#,
    )
    .engine;
    assert!(
        base.check_source_files(&[b"def absent : Nat := Box.mk 17"], &KVMap::new(), limits())
            .is_err()
    );
    checked(
        &base,
        "open scoped Conversions\ndef converted : Nat := Box.mk 17\ntheorem correct : converted = 17 := by rfl",
    );
}

#[test]
fn module_replay_preserves_dormancy_and_cache_invalidation_tracks_scoped_updates() {
    use fln::source_check::modules::{
        SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
    };
    let base = base();
    let names = [n("Library"), n("Consumer")];
    let library = "attribute [instance] fallback\nnamespace Alternative\nattribute [scoped instance 2000] alpha\nend Alternative\nopen scoped Alternative";
    let changed = library.replace("2000", "1");
    let consumer = "import Library\ntheorem dormant : chosen = 1 := by rfl\nopen scoped Alternative\ntheorem active : chosen = 2 := by rfl";
    let updated = consumer.replace("chosen = 2", "chosen = 1");
    let mut session = SourceModuleSession::new(
        base,
        KVMap::new(),
        SourceModuleCheckLimits::new(limits()),
        SourceModuleCacheLimits::default(),
    );
    let run = |session: &mut SourceModuleSession, lib: &str, user: &str| {
        session.check(
            &[
                fln::SourceModuleInput {
                    name: &names[0],
                    source: lib.as_bytes(),
                },
                fln::SourceModuleInput {
                    name: &names[1],
                    source: user.as_bytes(),
                },
            ],
            &names[1],
        )
    };
    let first = run(&mut session, library, consumer)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(first.elaborated_modules, 2);
    let root = first.checked.checked.result_logical_root;
    let warm = run(&mut session, library, consumer)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(warm.reused_modules, 2);
    assert_eq!(warm.checked.checked.result_logical_root, root);
    assert!(run(&mut session, &changed, consumer).is_err());
    assert_eq!(
        run(&mut session, library, consumer)
            .unwrap()
            .into_complete()
            .unwrap()
            .reused_modules,
        2
    );
    let replaced = run(&mut session, &changed, &updated)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(replaced.elaborated_modules, 2);
    assert_ne!(replaced.checked.checked.result_logical_root, root);
}

#[test]
fn cursor_inspection_and_warm_prefixes_retain_original_scope_chronology() {
    use fln::source_check::inspect::{ObservationKind, SourceObservation};
    use fln::source_check::modules::{
        SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
    };
    let source = "attribute [instance] fallback\nnamespace Alternative\nattribute [scoped instance] alpha\nend Alternative\nopen scoped Alternative\nattribute [instance] later\ntheorem pending : chosen = 4 := by rfl";
    let module = n("Main");
    let inputs = [fln::SourceModuleInput {
        name: &module,
        source: source.as_bytes(),
    }];
    let mut session = SourceModuleSession::new(
        base(),
        KVMap::new(),
        SourceModuleCheckLimits::new(limits()),
        SourceModuleCacheLimits::default(),
    );
    for warm in [false, true] {
        let inspected = session
            .inspect(&inputs, &module, source.len(), ObservationKind::Goals)
            .unwrap()
            .into_complete()
            .unwrap();
        assert!(
            matches!(inspected.observation, Some(SourceObservation::Goals { ref goals, .. }) if goals.is_empty())
        );
        assert_eq!(inspected.prefix.reused_modules, usize::from(warm));
        let env = inspected.prefix.checked.checked.engine.environment();
        assert!(!env.contains(&n("pending")));
        assert_eq!(names(env, &inspected.scope.instance_scopes)[0], n("later"));
    }
    session
        .check(&inputs, &module)
        .unwrap()
        .into_complete()
        .unwrap();
}

#[test]
fn damaged_scoped_journal_rows_are_refused_instead_of_becoming_global_candidates() {
    let base = base();
    let env = scoped::register(base.environment(), &n("Alternative"), &n("alpha"), 1000).unwrap();
    let registry_name = n("FrankenLean.sourceInstances.v1");
    let bytes = env
        .extension(&registry_name)
        .unwrap()
        .entries()
        .last()
        .unwrap()
        .payload
        .to_vec();
    let mut extra = bytes.clone();
    extra.push(0);
    for payload in [
        bytes[..bytes.len() - 1].to_vec(),
        extra,
        b"FLNINST\x01\x03".to_vec(),
    ] {
        let damaged = base
            .environment()
            .push_extension_entry(&registry_name, payload)
            .unwrap();
        assert!(InstanceRegistry::read(&damaged).is_err());
        let mut active = scoped::ActiveScopes::default();
        assert!(active.activate(&damaged, &n("Alternative")).is_err());
        assert_eq!(active, scoped::ActiveScopes::default());
    }
    let mut active = scoped::ActiveScopes::default();
    active.activate(&env, &n("Alternative")).unwrap();
    prove(env, active, 2);
}
