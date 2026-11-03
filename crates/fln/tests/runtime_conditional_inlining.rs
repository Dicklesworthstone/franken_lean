//! Macro-inline Prelude conditionals keep only the selected branch executable.
#![forbid(unsafe_code)]

use fln::{
    Budget, ClosedVmValue, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap,
    SourceCheckLimits, VmExit,
};
use fln_core::outcome::Outcome;

fn limits() -> EngineExecutionLimits {
    let mut limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    limits.vm.max_steps = 2000;
    limits.vm.max_stack_depth = 256;
    limits
}

fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}

const SPEND: &str =
    "def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1\n";

#[test]
fn canonical_conditionals_delay_both_branches_and_keep_the_selected_result() {
    let base = engine();
    for query in [
        "#eval ite True 42 (spend 10000)",
        "#eval ite False (spend 10000) 42",
        "#eval dite True (fun _ => 42) (fun _ => spend 10000)",
        "#eval dite False (fun _ => spend 10000) (fun _ => 42)",
        "def choose (b : Bool) : Nat := ite (b = true) 42 (spend 10000)\n#eval choose true",
    ] {
        let source = format!("{SPEND}{query}");
        let execution = base
            .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
            .unwrap_or_else(|error| panic!("{query}: {error:?}"))
            .into_complete()
            .unwrap_or_else(|error| panic!("{query}: evaluation did not finish: {error:?}"));
        let VmExit::Returned(value) = &execution.executions.last().unwrap().exit else {
            panic!("{query}: no return value");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some("42"),
            "{query}"
        );
    }
}

#[test]
fn selected_branches_and_ordinary_arguments_still_execute_before_returning() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for query in [
        "#eval ite True (spend 10000) 42",
        "#eval ite False 42 (spend 10000)",
        "def keep (answer ignored : Nat) : Nat := answer\n#eval keep 42 (spend 10000)",
    ] {
        let source = format!("{SPEND}{query}");
        assert!(matches!(
            base.execute_source_definitions(&[source.as_bytes()], &options, limits())
                .unwrap_or_else(|error| panic!("{query}: {error:?}")),
            Outcome::Inconclusive(_)
        ));
        assert_eq!(base.logical_root(&options), root);
    }
}

#[test]
fn failed_conditionals_leave_a_deterministic_clean_retry() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    assert!(
        base.execute_source_definitions(&[b"#eval ite True 42 false"], &options, limits())
            .is_err()
    );
    let source = b"#eval ite True 42 0";
    let run = || {
        base.execute_source_definitions(&[source], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let first = run();
    let retry = run();
    assert_eq!(
        first.executions[0].flbc_artifact,
        retry.executions[0].flbc_artifact
    );
    assert_eq!(base.logical_root(&options), root);
}

/// The simplifier indexes a rule by its actual head. Definitional equivalence
/// with an expanded recursor is not enough to retrieve an `ite`/`dite` rule.
#[test]
fn source_conditionals_are_rewritten_by_their_canonical_lemma_heads() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = br#"
theorem rewriteProp (p : Prop) [Decidable p] (x y : Nat)
    (rule : ite p x y = x) : (if p then x else y) = x := by
  simp only [rule]
theorem rewriteBool (b : Bool) (x y : Nat)
    (rule : ite (b = true) x y = x) : (if b then x else y) = x := by
  simp only [rule]
theorem rewriteDependent (p : Prop) [Decidable p]
    (yes : p -> Nat) (no : Not p -> Nat) (value : Nat)
    (rule : dite p yes no = value) :
    (if evidence : p then yes evidence else no evidence) = value := by
  simp only [rule]
"#;
    let checked = base
        .check_source_files(
            &[source],
            &options,
            SourceCheckLimits::new(limits().admission()),
        )
        .unwrap_or_else(|error| panic!("canonical conditional rewrite: {error:?}"))
        .into_complete()
        .expect("the source proofs pass both checking engines");
    for theorem in ["rewriteProp", "rewriteBool", "rewriteDependent"] {
        assert!(
            checked
                .engine
                .environment()
                .contains(&fln::Name::from_components([theorem])),
            "{theorem}"
        );
    }
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn source_conditionals_keep_proof_branches_recursion_and_owned_results_on_replay() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = br#"
def count (n : Nat) (b : Bool) : Nat :=
  match n with
  | .zero => 0
  | .succ k => if b then count k b + 1 else count k b + 2
def dependent (p : Prop) [Decidable p] (yes : p -> Nat) (no : Not p -> Nat) : Nat :=
  if evidence : p then yes evidence else no evidence
def chooseText (b : Bool) (stem : String) : String :=
  if b then stem ++ "yes" else stem ++ "no"
#eval count 4 true
#eval count 4 false
#eval dependent True (fun _ => 42) (fun _ => count 10000 true)
#eval dependent False (fun _ => count 10000 true) (fun _ => 17)
#eval chooseText true "owned-"
#eval chooseText false "owned-"
"#;
    let run = || {
        base.execute_source_definitions(&[source], &options, limits())
            .unwrap_or_else(|error| panic!("conditional execution: {error:?}"))
            .into_complete()
            .expect("only the selected conditional branch executes")
    };
    let first = run();
    let retry = run();
    let expected = [
        ClosedVmValue::Scalar(4),
        ClosedVmValue::Scalar(8),
        ClosedVmValue::Scalar(42),
        ClosedVmValue::Scalar(17),
        ClosedVmValue::String("owned-yes".to_owned()),
        ClosedVmValue::String("owned-no".to_owned()),
    ];
    assert_eq!(first.source_evaluation_indices.len(), expected.len());
    assert_eq!(first.result_logical_root, retry.result_logical_root);
    assert_eq!(
        first.source_evaluation_indices,
        retry.source_evaluation_indices
    );
    for (&index, expected) in first.source_evaluation_indices.iter().zip(expected) {
        let execution = &first.executions[index];
        assert_eq!(
            fln::closed_vm_value(&execution.exit).unwrap(),
            Some(expected.clone())
        );
        let replay = fln::execute_flbc_artifact(
            &execution.flbc_artifact,
            &options,
            fln::FlbcExecutionLimits {
                codec: limits().flbc_codec,
                vm: limits().vm,
            },
        )
        .unwrap()
        .into_complete()
        .expect("serialized conditional code executes with the original budgets");
        assert_eq!(fln::closed_vm_value(&replay).unwrap(), Some(expected));
        assert_eq!(
            execution.flbc_artifact,
            retry.executions[index].flbc_artifact
        );
    }
    assert_eq!(base.logical_root(&options), root);
}
