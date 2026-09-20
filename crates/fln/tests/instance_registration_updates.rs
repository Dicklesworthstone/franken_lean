//! Registry changes consumed by real source elaboration and both checkers.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_elab::instances::{InstanceRegistry, InstanceRegistryError, register_instance, set_instance};

fn n(name: &str) -> Name {
    Name::from_components(name.split('.'))
}
fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}
fn base() -> Engine {
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    checked(
        &seed,
        "def seven : Inhabited Nat := Inhabited.mk 7\n\
         def nine : Inhabited Nat := Inhabited.mk 9\n\
         def notAClass : Nat := 12",
    )
}

#[test]
fn setting_an_attribute_adds_a_checked_dictionary_without_changing_the_snapshot() {
    let base = base();
    let before = base.logical_root(&KVMap::new());
    let next = set_instance(base.environment(), &n("seven"), 2000).unwrap();
    assert_ne!(before, next.logical_root(&KVMap::new()));
    assert_eq!(before, base.logical_root(&KVMap::new()));
    checked(
        &Engine::from_environment(next),
        "theorem selected : default = 7 := by rfl",
    );
    checked(&base, "theorem original : default = 0 := by rfl");
}

#[test]
fn lowering_priority_removes_the_old_priority_from_candidate_selection() {
    let base = base();
    let first = register_instance(base.environment(), &n("seven"), 4000).unwrap();
    let second = set_instance(&first, &n("nine"), 3000).unwrap();
    let lower = set_instance(&second, &n("seven"), 2000).unwrap();
    let registry = InstanceRegistry::read(&lower).unwrap();
    let copies: Vec<_> = registry
        .candidates(&n("Inhabited"))
        .iter()
        .filter(|entry| entry.declaration == n("seven"))
        .collect();
    assert_eq!(copies.len(), 1);
    assert_eq!(copies[0].priority, 2000);
    checked(
        &Engine::from_environment(lower),
        "theorem selected : default = 9 := by rfl",
    );
    checked(
        &Engine::from_environment(second),
        "theorem earlier : default = 7 := by rfl",
    );
}

#[test]
fn updating_a_priority_keeps_the_original_equal_priority_position() {
    let base = base();
    let first = set_instance(base.environment(), &n("seven"), 2000).unwrap();
    let old_order = InstanceRegistry::read(&first).unwrap()
        .candidates(&n("Inhabited"))[0].order;
    let second = set_instance(&first, &n("nine"), 3000).unwrap();
    let equal = set_instance(&second, &n("seven"), 3000).unwrap();
    let registry = InstanceRegistry::read(&equal).unwrap();
    let seven = registry.candidates(&n("Inhabited")).iter()
        .find(|entry| entry.declaration == n("seven")).unwrap();
    assert_eq!(seven.order, old_order);
    // The pin replaces a matching DiscrTree value in its existing slot. Merely
    // updating the earlier dictionary must not make it newer than `nine`.
    checked(
        &Engine::from_environment(equal.clone()),
        "theorem tied : default = 9 := by rfl",
    );
    let higher = set_instance(&equal, &n("seven"), 4000).unwrap();
    checked(
        &Engine::from_environment(higher),
        "theorem raised : default = 7 := by rfl",
    );
}

#[test]
fn strict_registration_remains_strict_after_an_attribute_update() {
    let base = base();
    let first = set_instance(base.environment(), &n("seven"), 2000).unwrap();
    let updated = set_instance(&first, &n("seven"), 3000).unwrap();
    assert!(matches!(
        register_instance(&updated, &n("seven"), 4000),
        Err(InstanceRegistryError::DuplicateInstance(name)) if name == n("seven")
    ));
    let registry = InstanceRegistry::read(&updated).unwrap();
    assert_eq!(registry.candidates(&n("Inhabited")).iter()
        .filter(|entry| entry.declaration == n("seven")).count(), 1);
}

#[test]
fn updates_preserve_the_exact_importable_journal_prefix() {
    let base = base();
    let first = set_instance(base.environment(), &n("seven"), 2000).unwrap();
    let second = set_instance(&first, &n("seven"), 500).unwrap();
    let name = n("FrankenLean.sourceInstances.v1");
    let old = first.extension(&name).unwrap();
    let new = second.extension(&name).unwrap();
    assert_eq!(old.descriptor, new.descriptor);
    assert_eq!(new.len(), old.len() + 1);
    for (old, new) in old.entries().zip(new.entries()) {
        assert_eq!(old, new);
    }
}

#[test]
fn bad_registrations_and_malformed_update_rows_fail_closed() {
    let base = base();
    assert!(set_instance(base.environment(), &n("absent"), 1000).is_err());
    assert!(set_instance(base.environment(), &n("notAClass"), 1000).is_err());
    let env = set_instance(base.environment(), &n("seven"), 2000).unwrap();
    let name = n("FrankenLean.sourceInstances.v1");
    let payload = env.extension(&name).unwrap().entries().last().unwrap()
        .payload.to_vec();
    assert_eq!(payload[8], 2);
    let mut unknown = payload.clone();
    unknown[8] = 255;
    let truncated = payload[..payload.len() - 1].to_vec();
    let mut trailing = payload;
    trailing.push(0);
    for bad in [unknown, truncated, trailing] {
        let corrupt = env.push_extension_entry(&name, bad).unwrap();
        assert!(InstanceRegistry::read(&corrupt).is_err());
        assert!(set_instance(&corrupt, &n("nine"), 3000).is_err());
    }
    checked(
        &Engine::from_environment(env),
        "theorem intact : default = 7 := by rfl",
    );
}
