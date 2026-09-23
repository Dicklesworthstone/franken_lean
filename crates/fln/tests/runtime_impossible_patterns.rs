//! Constructor discrimination stays in Prop; impossible data arms never cast
//! between incompatible runtime layouts. Both admission seats check the proof.
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
fn run(source: &str, expected: &str) {
    run_with_limits(source, expected, limits());
}
fn run_with_limits(source: &str, expected: &str, limits: EngineExecutionLimits) {
    let batch = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits)
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &batch.executions.last().unwrap().exit else {
        panic!("native return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected)
    );
}
const VEC: &str = "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n";
const HEAD: &str = "def first {A : Type} (n : Nat) (xs : Vec A (Nat.succ n)) : A := match xs with | .cons k x tail => x\n";

#[test]
fn natural_nonempty_vector_pattern_does_not_require_a_manual_false_branch() {
    run(
        &format!("{VEC}{HEAD}#eval first 0 (Vec.cons 0 42 Vec.nil)"),
        "42",
    );
}
#[test]
fn impossible_branches_return_polymorphic_objects_and_strings() {
    run(
        &format!(
            "{VEC}{HEAD}structure Payload where value : Nat\n#eval (first 0 (Vec.cons 0 (Payload.mk 42) Vec.nil)).value"
        ),
        "42",
    );
    run(
        &format!("{VEC}{HEAD}#eval String.length (first 0 (Vec.cons 0 \"abc\" Vec.nil))"),
        "3",
    );
}
#[test]
fn a_boolean_index_refutes_an_arm_with_a_different_payload_layout() {
    run(
        "inductive Choice : Bool -> Type where | yes (n : Nat) : Choice true | no (s : String) : Choice false\ndef get (x : Choice true) : Nat := match x with | .yes n => n\n#eval get (Choice.yes 42)",
        "42",
    );
}
#[test]
fn several_omitted_literal_index_arms_are_proof_checked() {
    run(
        "inductive Tag : Nat -> Type where | a : Tag 0 | b : Tag 1 | c : Tag 2 | d (n : Nat) : Tag 18446744073709551616\ndef get (x : Tag 18446744073709551616) : Nat := match x with | .d n => n\n#eval get (Tag.d 42)",
        "42",
    );
}
#[test]
fn dependent_tail_results_and_nested_matches_preserve_the_refined_index() {
    let source = format!(
        "{VEC}{HEAD}def rest (n : Nat) (xs : Vec Nat (Nat.succ n)) : Vec Nat n := match xs with | .cons k x tail => tail\n#eval first 0 (rest 1 (Vec.cons 1 7 (Vec.cons 0 42 Vec.nil)))"
    );
    // Scope-transform preflight now charges only work the core actually visits.
    // The default preparation budget is unchanged; this composition fits it.
    run(&source, "42");
}
#[test]
fn source_cases_and_contradiction_tactics_use_the_same_checked_empty_path() {
    run(
        &format!(
            "{VEC}def first (n : Nat) (xs : Vec Nat (Nat.succ n)) : Nat := by cases xs with | cons k x tail => exact x\n#eval first 0 (Vec.cons 0 42 Vec.nil)"
        ),
        "42",
    );
    run(
        "def ignore (f : true = false -> Nat) : Nat := 42\n#eval ignore (fun h => by contradiction)",
        "42",
    );
    run(
        "def ignore (f : true = false -> String) : Nat := 42\n#eval ignore (fun h => by injection h)",
        "42",
    );
}
#[test]
fn inhabited_omissions_and_ill_typed_supplied_impossible_arms_still_reject() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for source in [
        format!("{VEC}def bad (n : Nat) (xs : Vec Nat n) : Nat := match xs with | .cons k x tail => x\n#eval 42"),
        "inductive Choice : Bool -> Type where | yes (n : Nat) : Choice true | no (s : String) : Choice false\ndef bad (x : Choice true) : Nat := match x with | .yes n => n | .no s => s\n#eval 42".to_owned(),
        format!("{VEC}{HEAD}#eval first 0 Vec.nil"),
    ] {
        assert!(!matches!(base.execute_source_definitions(&[source.as_bytes()], &options, limits()), Ok(Outcome::Complete(_))), "{source}");
        assert_eq!(base.logical_root(&options), root);
    }
    run(
        &format!("{VEC}{HEAD}#eval first 0 (Vec.cons 0 42 Vec.nil)"),
        "42",
    );
}
#[test]
fn nonanswer_in_constructor_discrimination_keeps_the_input_and_recovers() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = format!("{VEC}{HEAD}#eval first 0 (Vec.cons 0 42 Vec.nil)");
    let mut bounded = limits();
    bounded.kernel.steps = 1;
    assert!(!matches!(
        base.execute_source_definitions(&[source.as_bytes()], &options, bounded),
        Ok(Outcome::Complete(_))
    ));
    assert_eq!(base.logical_root(&options), root);
    run(&source, "42");
}

#[test]
fn escaping_proof_continuations_remain_an_explicit_closure_conversion_boundary() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let definitions = format!(
        "{VEC}{HEAD}def use (offset : Nat) : Nat := let f := first 0 (Vec.cons 0 (fun (n : Nat) => n + offset) Vec.nil); f 2"
    );
    // This is valid logical source. The generated same-constructor proof
    // continuation performs strict work and returns a closure: the flat native
    // callable interface cannot represent that escaping intermediate yet.
    base.check_source_files(
        &[definitions.as_bytes()],
        &options,
        fln::SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    let source = format!("{definitions}\n#eval use 40");
    let error = base
        .execute_source_definitions(&[source.as_bytes()], &options, limits())
        .unwrap_err();
    assert!(
        matches!(error, fln::EngineExecutionError::BatchCommand { error, .. }
        if matches!(*error, fln::EngineExecutionError::Ingress(fln_comp::ingress::IngressError::UnknownLambda { .. })))
    );
    assert_eq!(base.logical_root(&options), root);
}
