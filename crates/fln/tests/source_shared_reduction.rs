//! Real source elaboration must not exhaust on repeated recursive demands.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

const NESTED: &str = "def result : Nat := by first | exact (let rec go (a n : Nat) : Nat := match n with | .zero => a | .succ k => let rec inner (b m : Nat) : Nat := match m with | .zero => b | .succ j => inner (b + 1) j; go (inner a 1) k; go 10 32) | exact 0\n";

#[test]
fn recursive_demand_reuse_proves_the_right_value_but_never_the_wrong_one() {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let base = Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let original = base.logical_root(&options);
    let wrong = format!("{NESTED}theorem wrong : result = 43 := by rfl");
    let error = base
        .check_source_files(
            &[wrong.as_bytes()],
            &options,
            SourceCheckLimits::new(admission),
        )
        .unwrap_err();
    assert_eq!(
        error.disposition().2,
        1,
        "wrong value must be rejected, not run out of resources: {error:?}"
    );
    assert_eq!(base.logical_root(&options), original);
    let valid = format!("{NESTED}theorem computes : result = 42 := by rfl");
    let checked = base
        .check_source_files(
            &[valid.as_bytes()],
            &options,
            SourceCheckLimits::new(admission),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        checked
            .engine
            .environment()
            .contains(&fln::Name::from_components(["computes"]))
    );
    assert_eq!(base.logical_root(&options), original);
}

fn doubling_source(depth: u32, value: u64) -> String {
    let mut text = String::from("def answer : Nat :=\n  let n0 : Nat := 1\n");
    for n in 1..=depth {
        text.push_str(&format!(
            "  let n{n} : Nat := Nat.add n{} n{}\n",
            n - 1,
            n - 1
        ));
    }
    text.push_str(&format!(
        "  n{depth}\ntheorem computes : answer = {value} := by rfl\n"
    ));
    text
}

#[test]
fn shared_source_let_circuits_finish_through_both_checkers() {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let source = doubling_source(16, 1 << 16);
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission),
        )
        .unwrap()
        .into_complete()
        .unwrap();
}
