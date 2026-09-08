//! Whole-file checking, including proof reuse and failure-atomic snapshots.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckError,
    SourceCheckLimits,
};
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
#[test]
fn whole_files_admit_theorems_without_executing_proofs_or_functions() {
    let base = engine();
    let opts = KVMap::new();
    let root = base.logical_root(&opts);
    let first=b"def identity (x : Nat) : Nat := x\r\ntheorem eqself (x : Nat) : identity x = x := by rfl\r\n";
    let second=b"theorem reuse (x : Nat) : identity x = x := by apply eqself\ntheorem symm (x y : Nat) (h : x = y) : y = x := by rw [h]";
    let result = base
        .check_source_files(&[first, second], &opts, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((result.files, result.commands, result.theorems), (2, 4, 3));
    assert_eq!(result.base_logical_root, root);
    assert_eq!(base.logical_root(&opts), root);
    assert_ne!(result.result_logical_root, root);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["identity"]))
    );
    assert!(
        result
            .engine
            .environment()
            .contains(&Name::from_components(["symm"]))
    );
}
#[test]
fn late_failure_exposes_no_successor_and_reports_the_correct_file_offset() {
    let base = engine();
    let opts = KVMap::new();
    let root = base.logical_root(&opts);
    let prefix = b"theorem good (x : Nat) : x = x := by rfl\r\n";
    let mut text = prefix.to_vec();
    text.extend_from_slice(b"theorem bad : 1 = 2 := by rfl");
    let error = base
        .check_source_files(&[b"def prior : Nat := 0", &text], &opts, limits())
        .unwrap_err();
    assert!(
        matches!(error,SourceCheckError::Command {file:1,command:2,offset,..} if offset==prefix.len())
    );
    assert_eq!(error.disposition(), ("kernel-rejection", true, 1));
    assert_eq!(base.logical_root(&opts), root);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["prior"]))
    );
}
#[test]
fn aggregate_limits_and_empty_or_unsupported_inputs_are_not_success() {
    let base = engine();
    let opts = KVMap::new();
    let source = b"def first : Nat := 1";
    let mut low = limits();
    low.max_bytes = source.len();
    assert!(matches!(
        base.check_source_files(&[source, source], &opts, low),
        Err(SourceCheckError::Limit { .. })
    ));
    low = limits();
    low.max_commands = 1;
    assert!(matches!(
        base.check_source_files(&[b"def a : Nat := 1\ndef b : Nat := 2"], &opts, low),
        Err(SourceCheckError::Limit { .. })
    ));
    assert!(matches!(
        base.check_source_files(&[], &opts, limits()),
        Err(SourceCheckError::EmptyInput)
    ));
    for source in [
        b"".as_slice(),
        b"import Init\ndef a : Nat := 1",
        b"#eval 1",
        b"#check Nat",
    ] {
        assert!(base.check_source_files(&[source], &opts, limits()).is_err());
    }
}
#[test]
fn kernel_nonanswers_remain_nonanswers_not_false_proofs() {
    let base = engine();
    let mut low = limits();
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    let result = base
        .check_source_files(
            &[b"theorem test (P : Prop) : P -> P := by intro h; exact h"],
            &KVMap::new(),
            low,
        )
        .unwrap();
    assert!(matches!(result, Outcome::Inconclusive(_)));
}
