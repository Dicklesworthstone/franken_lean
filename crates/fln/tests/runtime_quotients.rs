//! Checked quotient programs compile to FIR/FLBC and execute on Golem.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Outcome, VmExit};

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}
fn execute(source: &str, expected: &str) -> u64 {
    let run = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &run.executions.last().unwrap().exit else {
        panic!("quotient execution did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
    value.usage.steps
}

const READ: &str = r#"
def Q : Type := Quot (fun (a b : Nat) => a = b)
def readQ (q : Q) : Nat :=
  Quot.lift (fun (n : Nat) => n) (fun (a b : Nat) (h : a = b) => h) q
"#;

#[test]
fn quotient_values_cross_function_arguments_records_and_branches() {
    execute(&format!("{READ}\n#eval readQ (Quot.mk (fun a b => a = b) 42)"), "42");
    execute(
        &format!("{READ}\nstructure Wrapped where\n  payload : Q\ndef use (w : Wrapped) : Nat := readQ w.payload\n#eval use {{ payload := Quot.mk (fun a b => a = b) 42 }}"),
        "42",
    );
    execute(
        &format!("{READ}\ndef choose (b : Bool) : Q := if b then Quot.mk (fun a b => a = b) 42 else Quot.mk (fun a b => a = b) 7\n#eval readQ (choose true)"),
        "42",
    );
}

#[test]
fn owned_strings_and_constructor_carriers_use_their_existing_representations() {
    execute(
        r#"
def echo (q : Quot (fun (a b : String) => a = b)) : String :=
  Quot.lift (fun (s : String) => s) (fun (a b : String) (h : a = b) => h) q
#eval let suffix : String := "xyz"; String.length (echo (Quot.mk (fun a b => a = b) ("a" ++ suffix)))
"#,
        "4",
    );
    execute(
        r#"
structure Box where
  value : Nat
def unbox (q : Quot (fun (a b : Box) => a.value = b.value)) : Nat :=
  Quot.lift (fun (a : Box) => a.value) (fun (a b : Box) (h : a.value = b.value) => h) q
#eval unbox (Quot.mk (fun (a b : Box) => a.value = b.value) { value := 42 })
"#,
        "42",
    );
}

#[test]
fn ignored_representatives_still_run_once_and_resource_stops_do_not_publish() {
    let source = r#"
def count (n : Nat) : Nat := match n with | .zero => 0 | .succ k => count k + 1
def ignoreQ (q : Quot (fun (a b : Nat) => True)) : Nat :=
  Quot.lift (fun (n : Nat) => 42) (fun (a b : Nat) (h : True) => rfl) q
#eval ignoreQ (Quot.mk (fun (a b : Nat) => True) (count 30))
"#;
    let idle = execute(&source.replace("count 30", "count 0"), "42");
    let busy = execute(source, "42");
    assert!(busy > idle + 30, "representative work disappeared: {idle} vs {busy}");
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let mut bounded = limits();
    bounded.vm.max_steps = idle;
    assert!(matches!(
        base.execute_source_definitions(&[source.as_bytes()], &options, bounded).unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn invalid_respectfulness_is_rejected_before_erasure_and_retry_is_deterministic() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for source in [
        "#eval Quot.lift (fun (n : Nat) => n) (fun (a b : Nat) (h : True) => rfl) (Quot.mk (fun (a b : Nat) => True) 42)",
        "#eval Quot.lift (fun (n : Nat) => n) _ (Quot.mk (fun (a b : Nat) => a = b) 42)",
        "def forged : Nat := Quot.lift (fun (n : Nat) => n) (fun (a b : Nat) (h : True) => rfl) (Quot.mk (fun (a b : Nat) => True) 42)\n#eval 7",
    ] {
        assert!(base.execute_source_definitions(&[source.as_bytes()], &options, limits()).is_err());
        assert_eq!(base.logical_root(&options), root);
    }
    let source = format!("{READ}\n#eval readQ (Quot.mk (fun a b => a = b) 42)");
    let run = || {
        base.execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let first = run();
    let second = run();
    assert_eq!(first.result_logical_root, second.result_logical_root);
    assert_eq!(
        first.executions.last().unwrap().flbc_artifact,
        second.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(base.logical_root(&options), root);
}
