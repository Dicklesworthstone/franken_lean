//! Captured predicates are static Prop metadata; their decision functions run.
#![forbid(unsafe_code)]

use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits, VmExit,
};

const COMMON: &str = r#"
def applyDecision (p : Nat → Prop) (d : (x : Nat) → Decidable (p x)) (x : Nat) : Bool :=
  @decide (p x) (d x)
def forwardDecision (p : Nat → Prop) (d : (x : Nat) → Decidable (p x)) (x : Nat) : Bool :=
  applyDecision p d x
def same (n m : Nat) : Bool :=
  applyDecision (fun k => k = n) (fun k => Nat.decEq k n) m
def sameForwarded (n m : Nat) : Bool :=
  forwardDecision (fun k => k = n) (fun k => Nat.decEq k n) m
"#;

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn checked(extra: &str) -> Engine {
    let source = format!("{COMMON}\n{extra}");
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits().admission()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("predicate and decision declarations pass both checking engines")
        .engine
}

fn execute_and_replay(
    engine: &Engine,
    source: &str,
    expected: &[&str],
    limits: EngineExecutionLimits,
) {
    let report = engine
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits)
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("predicate specialization executes within its budget");
    assert_eq!(report.executions.len(), expected.len());
    for (execution, expected) in report.executions.iter().zip(expected) {
        let VmExit::Returned(value) = &execution.exit else {
            panic!("decision evaluation did not return")
        };
        assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some(*expected));
        let replay =
            fln::execute_flbc_artifact(&execution.flbc_artifact, &KVMap::new(), Default::default())
                .unwrap()
                .into_complete()
                .expect("serialized predicate specialization replays");
        let VmExit::Returned(value) = replay else {
            panic!("decision artifact did not return")
        };
        assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some(*expected));
    }
}

#[test]
fn captured_and_forwarded_predicates_keep_the_supplied_decisions() {
    let engine = checked("");
    execute_and_replay(
        &engine,
        "#eval if same 7 7 then 42 else 0\n#eval if same 7 8 then 1 else 0\n#eval if sameForwarded 7 7 then 42 else 0\n#eval if sameForwarded 7 8 then 1 else 0\n#eval if sameForwarded 8 8 then 42 else 0",
        &["42", "0", "42", "0", "42"],
        limits(),
    );
}

#[test]
fn local_helpers_erase_predicate_parameters_without_executing_them() {
    let engine = checked(
        r#"
def localDecision (n m : Nat) : Bool :=
  let apply (p : Nat → Prop) (d : (x : Nat) → Decidable (p x)) (x : Nat) : Bool :=
    @decide (p x) (d x)
  apply (fun k => k = n) (fun k => Nat.decEq k n) m
def literalDecision (n m : Nat) : Bool :=
  (fun (p : Nat → Prop) (d : (x : Nat) → Decidable (p x)) (x : Nat) => @decide (p x) (d x))
    (fun k => k = n) (fun k => Nat.decEq k n) m
"#,
    );
    execute_and_replay(
        &engine,
        "#eval if localDecision 7 7 then 42 else 0\n#eval if localDecision 7 8 then 1 else 0\n#eval if literalDecision 7 7 then 42 else 0\n#eval if literalDecision 7 8 then 1 else 0",
        &["42", "0", "42", "0"],
        limits(),
    );
}

#[test]
fn multi_argument_predicates_preserve_the_decision_functions_runtime_captures() {
    let engine = checked(
        r#"
def applyBinaryDecision (p : Nat → Nat → Prop) (d : (x y : Nat) → Decidable (p x y)) (x y : Nat) : Bool :=
  @decide (p x y) (d x y)
def shifted (n x y : Nat) : Bool :=
  applyBinaryDecision (fun a b => a + n = b) (fun a b => Nat.decEq (a + n) b) x y
"#,
    );
    execute_and_replay(
        &engine,
        "#eval if shifted 3 4 7 then 42 else 0\n#eval if shifted 3 4 8 then 1 else 0\n#eval if shifted 4 4 8 then 42 else 0",
        &["42", "0", "42"],
        limits(),
    );
}

#[test]
fn erasing_predicate_metadata_never_erases_decision_computation() {
    let engine = checked(
        r#"
def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k
def slowDecision (n k : Nat) : Decidable (k = n) :=
  let spent := spend 100000
  Nat.decEq k n
def ignoreDecision (p : Nat → Prop) (d : (x : Nat) → Decidable (p x)) : Nat := 42
"#,
    );
    let before = engine.logical_root(&KVMap::new());
    let mut budget = limits();
    budget.vm.max_steps = 5000;
    // Constructing an uncalled decision lambda does not run its body.
    execute_and_replay(
        &engine,
        "#eval ignoreDecision (fun k => k = 7) (fun k => slowDecision 7 k)",
        &["42"],
        budget,
    );
    let execution = engine
        .execute_source_definitions(
            &[b"#eval if applyDecision (fun k => k = 7) (fun k => slowDecision 7 k) 7 then 42 else 0"],
            &KVMap::new(),
            budget,
        )
        .unwrap();
    let fln::Outcome::Inconclusive(reason) = execution else {
        panic!("the supplied decision procedure must exceed this step budget")
    };
    let fln_core::outcome::InconclusiveCause::ResourceExhausted { usage } = reason.cause else {
        panic!("decision computation must stop for its execution budget")
    };
    assert_eq!(usage.reason, fln_core::diag::ResourceReason::ExecutionSteps);
    assert_eq!(usage.allowed, budget.vm.max_steps);
    assert!(usage.observed > usage.allowed);
    assert_eq!(before, engine.logical_root(&KVMap::new()));
    execute_and_replay(
        &engine,
        "#eval if sameForwarded 7 7 then 42 else 0",
        &["42"],
        budget,
    );
}
