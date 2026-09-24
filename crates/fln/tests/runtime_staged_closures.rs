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
fn recursively_staged_results_keep_each_actual_call_boundary() {
    run(
        "def use (offset : Nat) : Nat := let f : Nat -> Nat -> Nat -> Nat := (by intro x; let a := x + offset; intro y; let b := a + y; intro z; exact b + z); let g := f 1; let h := g 2; h 3\n#eval use 36",
        "42",
    );
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

#[test]
fn four_stages_support_aliases_mixed_arities_and_direct_saturation() {
    let definitions = "def use (offset : Nat) : Nat := let f : Nat -> Nat -> Nat -> Nat -> Nat -> Nat := (by intro a; let first := a + offset; intro b c; let middle := first + b + c; intro d; let last := middle + d; intro e; exact last + e); let g := f 1; let alias := g; let h := alias 2; let i := h 3; let j := i 4; j 5";
    run(&format!("{definitions}\n#eval use 27"), "42");
    run(
        &format!(
            "{}\n#eval use 27",
            definitions.replace(
                "let g := f 1; let alias := g; let h := alias 2; let i := h 3; let j := i 4; j 5",
                "f 1 2 3 4 5"
            )
        ),
        "42",
    );
}

#[test]
fn nested_stages_keep_owned_strings_records_and_returned_payloads_alive() {
    run(
        "structure Box where value : Nat\ndef use (prefix : String) : Nat := let f : String -> Nat -> Nat -> Box := (by intro suffix; let text := prefix ++ suffix; intro n; let box := Box.mk (n + String.length text); intro k; exact Box.mk (box.value + k)); let g := f \"abcd\"; let h := g 30; let a := h 3; let b := h 4; a.value + b.value\n#eval use \"x\"",
        "77",
    );
}

#[test]
fn nested_stages_capture_callbacks_from_the_outer_scope() {
    run(
        "def use (offset : Nat) : Nat := let add : Nat -> Nat := fun n => n + offset; let f : Nat -> Nat -> Nat -> Nat := (by intro x; let a := add x; intro y; let b := a + y; intro z; exact b + z); let p := f 1; let q := p 2; q 3\n#eval use 36",
        "42",
    );
}

#[test]
fn each_completed_stage_keeps_its_own_strict_work_and_sharing() {
    let definitions = "def expensive (n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun k ih => ih) n\ndef use (a b c : Nat) : Nat := let f : Nat -> Nat -> Nat -> Nat := (by intro x; let first := expensive a; intro y; let second := expensive b; intro z; let third := expensive c; exact first + second + third + x + y + z); let g := f 10; let h := g 20; h 12";
    let steps = |a, b, c, source: &str| run(&format!("{source}\n#eval use {a} {b} {c}"), "42");
    let baseline = steps(0, 0, 0, definitions);
    let deltas: Vec<_> = [(20, 0, 0), (0, 20, 0), (0, 0, 20)]
        .into_iter()
        .map(|(a, b, c)| steps(a, b, c, definitions) - baseline)
        .collect();
    assert!(deltas.iter().all(|d| *d > 20));
    assert!(deltas.iter().all(|d| *d == deltas[0]));
    let twice = definitions
        .replace("h 12", "h 0 + h (0 - 1)")
        .replace("f 10", "f 1");
    let zero = steps(0, 0, 0, &twice);
    assert_eq!(steps(20, 0, 0, &twice) - zero, deltas[0]);
    assert_eq!(steps(0, 20, 0, &twice) - zero, deltas[1]);
    assert_eq!(steps(0, 0, 20, &twice) - zero, 2 * deltas[2]);
    // The third stage is never called: discard the completed second stage.
    let unused = definitions.replace("h 12", "42");
    let zero = steps(0, 0, 0, &unused);
    assert_eq!(steps(20, 0, 0, &unused) - zero, deltas[0]);
    assert_eq!(steps(0, 20, 0, &unused) - zero, deltas[1]);
    assert_eq!(steps(0, 0, 10000, &unused), zero);
}

#[test]
fn nested_stages_are_not_silently_converted_to_flat_callback_arguments() {
    let source = "def apply (f : Nat -> Nat -> Nat) : Nat := f 1 2\ndef use (offset : Nat) : Nat := let f : Nat -> Nat -> Nat := (by intro x; let n := x + offset; intro y; exact n + y); apply f\n#eval use 39";
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let error = engine
        .execute_source_definitions(&[source.as_bytes()], &options, limits)
        .unwrap_err();
    assert!(
        matches!(error, fln::EngineExecutionError::BatchCommand { error, .. } if matches!(*error, fln::EngineExecutionError::Ingress(fln_comp::ingress::IngressError::FunctionArgumentType { .. })))
    );
    assert_eq!(engine.logical_root(&options), root);
}
