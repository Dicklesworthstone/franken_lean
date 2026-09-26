//! Computed closures returning captured, partially applied staged callbacks.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits};
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
        panic!("expected a native return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected)
    );
    value.usage.steps
}

const CAPTURED: &str = "def use (offset : Nat) : Nat := let f : Nat -> Nat -> Nat -> Nat := (by intro x; let a := offset + x; intro y; let b := a + y; intro z; exact b + z); let g := f 1; let keep : Nat -> Nat -> Nat -> Nat := (by let marker := offset + 0; exact fun ignored => g); let h := keep 0; let k := h 2; k 3\n#eval use 36";

#[test]
fn computed_closures_return_captured_callback_stages() {
    run(CAPTURED, "42");
    run(&CAPTURED.replace("let k := h 2; k 3", "h 2 3"), "42");
    run(
        &CAPTURED.replace(
            "exact fun ignored => g",
            "exact fun ignored => (let alias := g; alias)",
        ),
        "42",
    );
}

#[test]
fn captured_stages_retain_owned_string_environments() {
    run(
        "def use (prefix : String) : Nat := let f : String -> Nat -> Nat -> Nat := (by intro suffix; let text := prefix ++ suffix; intro n; let base := n + String.length text; intro k; exact base + k); let g := f \"abc\"; let keep : Nat -> Nat -> Nat -> Nat := (by let marker := String.length prefix; exact fun ignored => g); let h := keep 0; let k := h 30; k 8\n#eval use \"x\"",
        "42",
    );
}

#[test]
fn returning_a_captured_stage_does_not_recompute_its_completed_prefix() {
    let source = "def expensive (n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun k ih => ih) n\ndef use (cost : Nat) : Nat := let f : Nat -> Nat -> Nat -> Nat := (by intro x; let work := expensive cost; intro y; let a := work + x + y; intro z; exact a + z); let g := f 1; let keep : Nat -> Nat -> Nat -> Nat := (by let marker := cost + 0; exact fun ignored => g); let h := keep 0; h 20 21\n";
    let repeated = source.replace("h 20 21", "h 9 11 + h 9 11");
    let once = run(&format!("{source}#eval use 100"), "42")
        - run(&format!("{source}#eval use 0"), "42");
    let twice = run(&format!("{repeated}#eval use 100"), "42")
        - run(&format!("{repeated}#eval use 0"), "42");
    assert!(once > 100, "the completed strict prefix was dropped");
    assert_eq!(
        once, twice,
        "returning/reusing a capture repeated its producer"
    );
}

#[test]
fn invalid_capture_types_and_resource_stops_publish_no_successor() {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let bad = CAPTURED.replace("let k := h 2", "let k := h \"wrong\"");
    assert!(!matches!(
        engine.execute_source_definitions(&[bad.as_bytes()], &options, limits),
        Ok(fln::Outcome::Complete(_))
    ));
    let mut bounded = limits;
    bounded.ingress.max_nodes = 5;
    assert!(!matches!(
        engine.execute_source_definitions(&[CAPTURED.as_bytes()], &options, bounded),
        Ok(fln::Outcome::Complete(_))
    ));
    assert_eq!(engine.logical_root(&options), root);
    run(CAPTURED, "42");
}
