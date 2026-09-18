//! Proof-indexed class selection through both ordinary checking engines.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};

const EXAMPLE: &str = include_str!("../../../examples/native_proof_indices.lean");
fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, files: &[&[u8]]) -> fln::SourceFileCheck {
    base.check_source_files(files, &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("source checking failed: {e:?}"))
        .into_complete()
        .unwrap()
}

#[test]
fn proof_indexed_dictionaries_are_reused_and_preserve_local_priority() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    let result = checked(&base, &[EXAMPLE.as_bytes()]);
    assert_eq!((result.commands, result.theorems), (7, 3));
    for name in [
        "Evidence",
        "reuse",
        "reused",
        "newest",
        "newest_selected",
        "selected_at",
    ] {
        assert!(
            result
                .engine
                .environment()
                .contains(&Name::from_components([name]))
        );
    }
    assert_eq!(base.logical_root(&KVMap::new()), before);
}

#[test]
fn different_propositions_data_indices_and_unsolved_proofs_are_not_erased() {
    let base = checked(&engine(), &[EXAMPLE.as_bytes()]).engine;
    let before = base.logical_root(&KVMap::new());
    for bad in [
        "def bad (P Q : Prop) (h : P) (k : Q) [Evidence P h] : Evidence Q k := inferInstance",
        "def bad (P : Nat -> Prop) (h : P 0) (k : P 1) [Evidence (P 0) h] : Evidence (P 1) k := inferInstance",
        "theorem bad (P : Prop) (h k : P) (first : Evidence P h) (second : Evidence P k) : newest P h k first second = first := by rfl",
        "def bad (P : Prop) (h : P) : Evidence P h := _",
    ] {
        assert!(
            base.check_source_files(&[bad.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{bad}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(!base.environment().contains(&Name::from_components(["bad"])));
    }
    checked(&base, &[b"theorem recovery : 7 = 7 := by rfl"]);
}

#[test]
fn proof_indexed_classes_and_instances_remain_usable_across_source_files() {
    let base = engine();
    let prefix = b"class Evidence (P : Prop) (proof : P) where\n  value : Nat";
    let suffix =
        b"def imported (P : Prop) (h k : P) [Evidence P h] : Evidence P k := inferInstance";
    let result = checked(&base, &[prefix, suffix]);
    assert_eq!(result.commands, 2);
    assert!(
        result
            .engine
            .environment()
            .contains(&Name::from_components(["imported"]))
    );
}
