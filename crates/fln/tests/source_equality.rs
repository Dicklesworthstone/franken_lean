//! Actual source proofs admitted by both independent checker seats.
#![forbid(unsafe_code)]
use fln::{Engine, EngineAdmissionLimits};
use fln_core::{name::Name, options::KVMap, outcome::Outcome};
use fln_env::constants::ConstantInfo;
use fln_kernel::verdict::Budget;
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
#[test]
fn equality_proofs_use_the_engine_council_not_the_execution_path() {
    let base = engine();
    let options = KVMap::new();
    let first = base
        .admit_source_declaration(
            b"theorem reflexive (x : Nat) : x = x := by rfl",
            &options,
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["reflexive"]))
    );
    assert!(matches!(
        first
            .engine
            .environment()
            .find(&Name::from_components(["reflexive"])),
        Some(ConstantInfo::Thm(_))
    ));
    let second = first
        .engine
        .admit_source_declaration(
            b"theorem reuse (x : Nat) : x = x := by apply reflexive",
            &options,
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        second
            .engine
            .environment()
            .contains(&Name::from_components(["reuse"]))
    );
}
#[test]
fn arithmetic_conversion_is_independently_rechecked() {
    engine()
        .admit_source_declaration(
            b"theorem arithmetic : 2 + 3 = 5 := by rfl",
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
}
#[test]
fn failed_source_proof_returns_no_advanced_engine() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    assert!(
        base.admit_source_declaration(b"theorem false : 1 = 2 := by rfl", &options, limits())
            .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["false"]))
    );
}
#[test]
fn source_admission_preserves_resource_nonanswers() {
    let base = engine();
    let options = KVMap::new();
    let mut low = limits();
    low.kernel = low.kernel.narrowed(0, 32);
    let result = base
        .admit_source_declaration(
            b"theorem test (P : Prop) : P -> P := by intro h; exact h",
            &options,
            low,
        )
        .unwrap();
    assert!(matches!(result, Outcome::Inconclusive(_)));
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["test"]))
    );
}
