//! Strict computation at higher-order callable boundaries.
#![forbid(unsafe_code)]
use fln::Budget;
use fln::{Engine, EngineAdmissionLimits, EngineExecutionLimits};
use fln_core::options::KVMap;

fn run(source: &str, expected: &str) -> u64 {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let report = engine
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(value) = &report.executions.last().unwrap().exit else {
        panic!("expected return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected)
    );
    value.usage.steps
}

#[test]
fn local_closure_performs_strict_work_before_returning_a_callback() {
    run(
        "def use (x : Nat) : Nat := let f : Nat -> Nat -> Nat := (fun (n : Nat) => by let y := n + x; exact fun (k : Nat) => y + k); let g := f 1; g 1\n#eval use 40",
        "42",
    );
}

#[test]
fn nonempty_vector_heads_return_captured_callbacks() {
    run(
        "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\ndef first {A : Type} (n : Nat) (xs : Vec A (Nat.succ n)) : A := match xs with | .cons k x tail => x\ndef use (offset : Nat) : Nat := let f := first 0 (Vec.cons 0 (fun (n k : Nat) => n + k + offset) Vec.nil); List.foldl Nat.add 0 (List.map (f 1) [1, 1])\n#eval use 19",
        "42",
    );
}

#[test]
fn recursively_staged_result_abis_are_not_coerced_to_flat_interfaces() {
    let definitions = "def use (offset : Nat) : Nat := let f : Nat -> Nat -> Nat -> Nat := (by intro x; let a := x + offset; intro y; let b := a + y; intro z; exact b + z); let g := f 1; let h := g 2; h 3";
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    engine
        .check_source_files(
            &[definitions.as_bytes()],
            &options,
            fln::SourceCheckLimits::new(EngineAdmissionLimits::new(limits.kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let source = format!("{definitions}\n#eval use 36");
    let error = engine
        .execute_source_definitions(&[source.as_bytes()], &options, limits)
        .unwrap_err();
    assert!(
        matches!(error, fln::EngineExecutionError::BatchCommand { error, .. }
        if matches!(*error, fln::EngineExecutionError::Ingress(fln_comp::ingress::IngressError::LambdaResultType { .. })))
    );
    assert_eq!(root, engine.logical_root(&options));
    run("#eval 42", "42");
}

#[test]
fn returned_callbacks_keep_multiple_arguments_and_partial_applications() {
    run(
        "def use (offset : Nat) : Nat := let f : Nat -> Nat -> Nat -> Nat := (fun x => by let a := x + offset; exact fun y z => a + y + z); let g := f 1; let h := g 2; h 3\n#eval use 36",
        "42",
    );
}

#[test]
fn a_staged_closure_can_be_saturated_in_one_application() {
    run(
        "def use (offset : Nat) : Nat := let f : Nat -> Nat -> Nat := (fun x => by let a := x + offset; exact fun y => a + y); f 1 2\n#eval use 39",
        "42",
    );
}

#[test]
fn staged_owned_values_survive_collection_storage_and_recursive_consumers() {
    run(
        "structure Handler where run : Nat -> Nat\ndef use (prefix : String) : Nat := let f : String -> Nat -> Nat := (fun s => by let text := prefix ++ s; exact fun n => n + String.length text); let h := Handler.mk (f \"abc\"); List.foldl Nat.add 0 (List.map h.run [17, 17])\n#eval use \"x\"",
        "42",
    );
}

#[test]
fn unused_completed_prefix_is_strict_and_repeated_calls_share_its_work() {
    let prefix = "def expensive (n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun k ih => ih) n\ndef use (cost : Nat) : Nat := let f : Nat -> Nat -> Nat := (fun n => by let y := expensive n; exact fun k => y + k); let g := f cost; 42\n";
    let cheap = run(&format!("{prefix}#eval use 0"), "42");
    let costly = run(&format!("{prefix}#eval use 100"), "42");
    assert!(
        costly > cheap + 100,
        "discarding the callback discarded its strict prefix"
    );
    let once = "def expensive (n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun k ih => ih) n\ndef use (cost : Nat) : Nat := let f : Nat -> Nat -> Nat := (fun n => by let y := expensive n; exact fun k => y + k); let g := f cost; g 42\n";
    let twice = once.replace("g 42", "g 20 + g 22");
    let once_delta =
        run(&format!("{once}#eval use 100"), "42") - run(&format!("{once}#eval use 0"), "42");
    let twice_delta =
        run(&format!("{twice}#eval use 100"), "42") - run(&format!("{twice}#eval use 0"), "42");
    assert_eq!(
        once_delta, twice_delta,
        "each callback invocation recomputed its prefix"
    );
}

#[test]
fn constructing_but_not_calling_a_staged_lambda_is_lazy() {
    let prefix = "def expensive (n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun k ih => ih) n\ndef use (cost : Nat) : Nat := let f : Nat -> Nat -> Nat := (fun n => by let y := expensive cost; exact fun k => y + k + n); 42\n";
    assert_eq!(
        run(&format!("{prefix}#eval use 0"), "42"),
        run(&format!("{prefix}#eval use 100000"), "42")
    );
}

#[test]
fn invalid_callback_types_and_budget_exhaustion_leave_the_input_unchanged() {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let source = "def use (x : Nat) : Nat := let f : Nat -> Nat -> Nat := (by intro n; let y := n + x; exact fun k => y + k); let g := f 1; g 1\n#eval use 40";
    let invalid = source.replace("let y := n + x", "let y : String := n + x");
    assert!(!matches!(
        engine.execute_source_definitions(&[invalid.as_bytes()], &options, limits),
        Ok(fln::Outcome::Complete(_))
    ));
    let mut bounded = limits;
    bounded.ingress.max_nodes = 5;
    assert!(!matches!(
        engine.execute_source_definitions(&[source.as_bytes()], &options, bounded),
        Ok(fln::Outcome::Complete(_))
    ));
    assert_eq!(root, engine.logical_root(&options));
    run(source, "42");
}
