//! Imported search policy must affect real elaboration, while every produced
//! declaration still passes the ordinary K1 and independent-checker council.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_elab::instances::{
    InstanceRegistry,
    imported::{self, ClassParameters, InstanceParameters},
};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn seed() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, text: &str) -> Engine {
    base.check_source_files(&[text.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{text}\n{error:?}"))
        .into_complete()
        .unwrap()
        .engine
}
fn transfer(annotation: &str) -> Engine {
    checked(
        &seed(),
        &format!(
            r#"
class Transfer (A : Type) (B : {annotation} Type) where
  convert : A -> B
instance (priority := 500) boolean : Transfer Nat Bool := Transfer.mk (fun x => true)
instance (priority := 2000) natural : Transfer Nat Nat := Transfer.mk (fun x => x + 1)
def transfer {{A B : Type}} [d : Transfer A B] (x : A) : B := Transfer.convert x
def explicit (B : Type) [d : Transfer Nat B] (x : Nat) : B := Transfer.convert x
"#
        ),
    )
}

#[test]
fn imported_outputs_drive_inference_instead_of_guessing_from_types() {
    let base = transfer("");
    assert!(
        base.check_source_files(&[b"def inferred := transfer 4"], &KVMap::new(), limits())
            .is_err()
    );
    let before = base.logical_root(&KVMap::new());
    let env = imported::register_class(
        base.environment(),
        &n("Transfer"),
        &ClassParameters {
            out_params: vec![1],
            out_level_params: vec![],
        },
    )
    .unwrap();
    let imported = Engine::from_environment(env);
    assert_ne!(before, imported.logical_root(&KVMap::new()));
    checked(
        &imported,
        "def inferred := transfer 4\ntheorem result : inferred = 5 := by rfl",
    );
    assert_eq!(before, base.logical_root(&KVMap::new()));
}

#[test]
fn latest_class_entry_replaces_output_policy_without_changing_declarations() {
    let base = transfer("outParam");
    assert!(
        base.check_source_files(&[b"def result := explicit Bool 4"], &KVMap::new(), limits())
            .is_err()
    );
    let env = imported::register_class(
        base.environment(),
        &n("Transfer"),
        &ClassParameters {
            out_params: vec![1],
            out_level_params: vec![],
        },
    )
    .unwrap();
    let env = imported::register_class(
        &env,
        &n("Transfer"),
        &ClassParameters {
            out_params: vec![],
            out_level_params: vec![],
        },
    )
    .unwrap();
    assert_eq!(
        env.find(&n("Transfer")),
        base.environment().find(&n("Transfer"))
    );
    checked(
        &Engine::from_environment(env),
        "def result := explicit Bool 4\ntheorem chosen : result = true := by rfl",
    );
}

#[test]
fn imported_synthesis_order_changes_observable_dictionary_selection() {
    let base = checked(
        &seed(),
        r#"
class First (B : outParam Type) where
  tag : Nat
class Second (B : outParam Type) where
  tag : Nat
instance (priority := 2000) firstNat : First Nat := First.mk 7
instance (priority := 1000) firstBool : First Bool := First.mk 9
instance (priority := 2000) secondBool : Second Bool := Second.mk 11
instance (priority := 1000) secondNat : Second Nat := Second.mk 13
class Root where
  tag : Nat
instance combined {B : Type} [x : First B] [y : Second B] : Root := Root.mk (@First.tag B x)
"#,
    );
    // The pin's own order solves `First B` first: `firstNat` (priority 2000) fixes `B` to
    // `Nat`, and `Second Nat` follows, so the tag is 7 (v4.32.0, 2026-10-07: `= 7` checks,
    // `= 9` is refused). The imported order below starts from `Second B` instead.
    checked(
        &base,
        "def original : Nat := Root.tag\ntheorem originalValue : original = 7 := by rfl",
    );
    let env = imported::register_instance(
        base.environment(),
        &n("combined"),
        &InstanceParameters {
            priority: 1000,
            synth_order: vec![2, 1],
            scope: None,
            keys: Vec::new(),
        },
    )
    .unwrap();
    checked(
        &Engine::from_environment(env),
        "def reordered : Nat := Root.tag\ntheorem reorderedValue : reordered = 9 := by rfl",
    );
}

#[test]
fn malformed_or_unadmitted_metadata_is_failure_atomic() {
    let base = transfer("outParam");
    let before = base.logical_root(&KVMap::new());
    for parameters in [
        ClassParameters {
            out_params: vec![2],
            out_level_params: vec![],
        },
        ClassParameters {
            out_params: vec![1, 1],
            out_level_params: vec![],
        },
        ClassParameters {
            out_params: vec![],
            out_level_params: vec![0],
        },
    ] {
        assert!(imported::register_class(base.environment(), &n("Transfer"), &parameters).is_err());
    }
    for declaration in ["missing", "transfer"] {
        assert!(
            imported::register_instance(
                base.environment(),
                &n(declaration),
                &InstanceParameters {
                    priority: 1000,
                    synth_order: vec![],
                    scope: None,
                    keys: Vec::new(),
                }
            )
            .is_err()
        );
    }
    for parameters in [
        InstanceParameters {
            priority: 1000,
            synth_order: vec![0],
            scope: None,
            keys: Vec::new(),
        },
        InstanceParameters {
            priority: 1000,
            synth_order: vec![],
            scope: Some(Name::anonymous()),
            keys: Vec::new(),
        },
    ] {
        assert!(
            imported::register_instance(base.environment(), &n("natural"), &parameters).is_err()
        );
    }
    assert_eq!(before, base.logical_root(&KVMap::new()));
    checked(&base, "theorem recovery : explicit Nat 4 = 5 := by rfl");
}

#[test]
fn scoped_imports_are_not_global_instances() {
    let base = checked(
        &seed(),
        "def privateDictionary : Inhabited Nat := Inhabited.mk 37",
    );
    let env = imported::register_instance(
        base.environment(),
        &n("privateDictionary"),
        &InstanceParameters {
            priority: 10000,
            synth_order: vec![],
            scope: Some(n("Feature")),
            keys: Vec::new(),
        },
    )
    .unwrap();
    let registry = InstanceRegistry::read(&env).unwrap();
    assert!(
        registry
            .candidates(&n("Inhabited"))
            .iter()
            .all(|entry| entry.declaration != n("privateDictionary"))
    );
    assert_eq!(
        registry
            .imported_instance_parameters(&n("privateDictionary"))
            .unwrap()
            .scope,
        Some(n("Feature"))
    );
    checked(
        &Engine::from_environment(env),
        "theorem dormant : default = 0 := by rfl",
    );
}
