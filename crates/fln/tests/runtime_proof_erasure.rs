//! Checked proof terms are not executable dependencies.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, VmExit};
fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn run(source: &str, expected: &str) -> u64 {
    let batch = Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &batch.executions.last().unwrap().exit else {
        panic!("VM return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
    value.usage.steps
}
#[test]
fn explicit_dependent_and_higher_order_proof_arguments_execute() {
    run(
        "def keep (n : Nat) (h : n = n) : Nat := n\n#eval keep 42 (by rfl)",
        "42",
    );
    run(
        "theorem refl (n : Nat) : n = n := by rfl\ndef keep (n : Nat) (h : n = n) : Nat := n\n#eval keep 42 (refl 42)",
        "42",
    );
    run(
        "def keep (n : Nat) (h : forall k : Nat, k = k) : Nat := n\n#eval keep 42 (by intro k; rfl)",
        "42",
    );
}
#[test]
fn proof_lets_and_local_callbacks_keep_capture_indices() {
    run(
        "def keep (n : Nat) : Nat := let h : n = n := by rfl; let f (k : Nat) (hk : k = k) : Nat := n + k; f 2 (by rfl)\n#eval keep 40",
        "42",
    );
    run(
        "def use (f : (n : Nat) -> n = n -> Nat) : Nat := f 42 (by rfl)\n#eval use (fun n h => n)",
        "42",
    );
}
#[test]
fn proof_computation_is_erased_but_unused_runtime_values_are_strict() {
    let prefix = "def work (n : Nat) : Nat := match n with | .zero => 0 | .succ k => work k + 1\ndef evidence (n : Nat) : 0 = 0 := let unused : Nat := work n; by rfl\ndef keep (h : 0 = 0) : Nat := 42\n";
    let cheap = run(&format!("{prefix}#eval keep (evidence 0)"), "42");
    let expensive = run(&format!("{prefix}#eval keep (evidence 1000000)"), "42");
    assert_eq!(cheap, expensive, "proof computations reached the VM");
    let strict = run(
        &format!("{prefix}#eval let unused : Nat := work 60; keep (by rfl)"),
        "42",
    );
    assert!(strict > cheap + 60, "non-proof computation was erased");
}
#[test]
fn partial_and_polymorphic_proof_calls_retain_runtime_arguments() {
    run(
        "def keep (h : 0 = 0) (n : Nat) : Nat := n\ndef pass (f : Nat -> Nat) : Nat := f 42\n#eval pass (keep (by rfl))",
        "42",
    );
    run(
        "def keep {A : Type} (x : A) (h : x = x) : A := x\n#eval keep 42 (by rfl)",
        "42",
    );
    run("#eval (fun (n : Nat) (h : n = n) => n) 42 (by rfl)", "42");
}
#[test]
fn rejected_proofs_and_resource_stops_do_not_publish() {
    let base = Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for source in [
        "def keep (h : 0 = 1) : Nat := 42\n#eval keep (by rfl)",
        "def bad : 0 = 1 := by rfl\ndef answer : Nat := 42",
        "def keep (n : Nat) (h : n = n) : Nat := n\n#eval keep 42 (by rfl)\ntheorem bad : 0 = 1 := by rfl",
    ] {
        assert!(
            base.execute_source_definitions(&[source.as_bytes()], &options, limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&options), root);
    }
    let source = b"def keep (n : Nat) (h : n = n) : Nat := n\n#eval keep 42 (by rfl)";
    let mut small = limits();
    small.ingress.max_nodes = 1;
    assert!(
        base.execute_source_definitions(&[source], &options, small)
            .is_err()
    );
    let mut small = limits();
    small.vm.max_steps = 1;
    assert!(matches!(
        base.execute_source_definitions(&[source], &options, small)
            .unwrap(),
        fln::Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
    let run = || {
        base.execute_source_definitions(&[source], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let first = run();
    let second = run();
    assert_eq!(
        first.executions.last().unwrap().flbc_artifact,
        second.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(
        first.engine.logical_root(&options),
        second.engine.logical_root(&options)
    );
}
