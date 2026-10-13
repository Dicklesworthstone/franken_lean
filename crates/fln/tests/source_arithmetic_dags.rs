//! Shared arithmetic must complete through the public, dual-checker source path.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_env::constants::ConstantInfo;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn base() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn circuit(depth: u32, start: u64, expected: u64) -> String {
    let mut source = String::from("def circuit (start : Nat) : Nat :=\n  let n0 : Nat := start\n");
    for n in 1..=depth {
        source.push_str(&format!(
            "  let n{n} : Nat := Nat.add n{} n{}\n",
            n - 1,
            n - 1
        ));
    }
    source.push_str(&format!(
        "  n{depth}\ntheorem computes : circuit {start} = {expected} := by rfl\n"
    ));
    source
}
fn bounded() -> SourceCheckLimits {
    let mut limits = limits();
    // Narrow the actual checker arithmetic allowance. The old tree evaluator
    // fails quickly here, without a machine-speed-dependent timeout assertion.
    limits.checker.admission.inference.defeq.nat.max_steps = 5_000;
    limits.checker.admission.conversion.nat.max_steps = 5_000;
    SourceCheckLimits::new(limits)
}
#[test]
fn large_shared_source_arithmetic_is_admitted_under_a_small_checker_budget() {
    let base = base();
    let options = KVMap::new();
    let original = base.logical_root(&options);
    for (depth, start) in [(32, 3), (40, 7)] {
        let source = if depth == 32 {
            include_str!("../../fln-parse/tests/fixtures/shared_arithmetic.lean").to_owned()
        } else {
            circuit(depth, start, start << depth)
        };
        let checked = base
            .check_source_files(&[source.as_bytes()], &options, bounded())
            .unwrap_or_else(|e| panic!("{e:?}"))
            .into_complete()
            .expect("both checking engines must complete");
        assert!(matches!(
            checked
                .engine
                .environment()
                .find(&Name::from_components(["computes"])),
            Some(ConstantInfo::Thm(_))
        ));
        assert_eq!(checked.theorems, 1);
        assert_eq!(base.logical_root(&options), original);
    }
}
#[test]
fn a_wrong_result_cannot_publish_a_theorem_and_corrected_source_recovers() {
    let base = base();
    let options = KVMap::new();
    let original = base.logical_root(&options);
    let wrong = circuit(32, 3, (3_u64 << 32) + 1);
    let error = base
        .check_source_files(&[wrong.as_bytes()], &options, bounded())
        .unwrap_err();
    assert_eq!(
        error.disposition().2,
        1,
        "wrong result is not a resource stop: {error:?}"
    );
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["computes"]))
    );
    assert_eq!(base.logical_root(&options), original);
    let right = circuit(32, 3, 3_u64 << 32);
    base.check_source_files(&[right.as_bytes()], &options, bounded())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(base.logical_root(&options), original);
}
