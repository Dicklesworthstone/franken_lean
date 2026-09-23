//! Empty branches remain checked, but compile to explicit non-returning code.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, VmExit};
fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}
fn run(source: &str, expected: &str) -> u64 {
    let batch = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
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
    value.usage.steps
}
#[test]
fn checked_decision_branch_can_eliminate_a_refutation() {
    run(
        "def onlyTrue [d : Decidable True] : Nat := if hb : True then 42 else False.elim (hb True.intro)\n#eval @onlyTrue (Decidable.isTrue True.intro)",
        "42",
    );
}
const VEC: &str = "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n";
#[test]
fn a_nonempty_vector_head_uses_checked_false_elimination() {
    run(
        &format!(
            "{VEC}def first (n : Nat) (xs : Vec Nat n) (h : (n = 0 -> False)) : Nat := Vec.rec (motive := fun k _ => (k = 0 -> False) -> Nat) (fun h => False.rec (motive := fun _ => Nat) (h (by rfl))) (fun k x tail ih h => x) xs h\n#eval first 1 (Vec.cons 0 42 Vec.nil) (by decide)"
        ),
        "42",
    );
}

const FIRST: &str = "def first {A : Type} (n : Nat) (xs : Vec A n) (h : n = 0 -> False) : A := Vec.rec (motive := fun k _ => (k = 0 -> False) -> A) (fun h => False.elim (h (by rfl))) (fun k x tail ih h => x) xs h\n";
#[test]
fn empty_branches_can_return_owned_objects_and_closures() {
    run(
        &format!(
            "{VEC}{FIRST}structure Payload where value : Nat\n#eval (first 1 (Vec.cons 0 (Payload.mk 42) Vec.nil) (by decide)).value"
        ),
        "42",
    );
    run(
        &format!(
            "{VEC}{FIRST}def apply (offset : Nat) : Nat := let f := first 1 (Vec.cons 0 (fun (n : Nat) => n + offset) Vec.nil) (by decide); f 2\n#eval apply 40"
        ),
        "42",
    );
}
#[test]
fn string_and_boolean_empty_results_keep_their_own_types() {
    run(
        &format!(
            "{VEC}{FIRST}#eval String.length (first 1 (Vec.cons 0 \"hello\" Vec.nil) (by decide))"
        ),
        "5",
    );
    run(
        &format!(
            "{VEC}{FIRST}#eval if first 1 (Vec.cons 0 true Vec.nil) (by decide) then 42 else 0"
        ),
        "42",
    );
}
#[test]
fn false_elimination_under_captured_and_curried_callbacks_is_compiled_lazily() {
    run(
        "def ignore (f : False -> Nat) : Nat := 42\ndef make (offset : Nat) : Nat := ignore (fun h => offset + False.elim h)\n#eval make 7",
        "42",
    );
    run(
        "def ignore (f : False -> Nat) : Nat := 42\n#eval ignore (fun h => False.rec (motive := fun _ => Nat -> Nat) h 7)",
        "42",
    );
    run(
        "def ignore (f : False -> Nat -> Nat) : Nat := 42\n#eval ignore (fun h n => False.elim h)",
        "42",
    );
}
#[test]
fn unused_recursive_work_stays_lazy_but_ordinary_fields_stay_strict() {
    let prefix = format!(
        "{VEC}{FIRST}def expensive (n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun k ih => ih) n\n"
    );
    let small = run(
        &format!("{prefix}#eval first 1 (Vec.cons 0 42 Vec.nil) (by decide)"),
        "42",
    );
    let large = run(
        &format!(
            "{prefix}#eval first 2 (Vec.cons 1 42 (Vec.cons 0 (expensive 100) Vec.nil)) (by decide)"
        ),
        "42",
    );
    assert!(large > small + 100, "constructor fields still execute");
}
#[test]
fn invalid_false_evidence_and_failed_runs_do_not_publish() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "#eval False.elim (by exact True.intro)",
        "def impossible : False := by rfl\n#eval 42",
    ] {
        assert!(
            base.execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err()
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    let source = format!("{VEC}{FIRST}#eval first 1 (Vec.cons 0 42 Vec.nil) (by decide)");
    let mut bounded = limits();
    bounded.ingress.max_nodes = 1;
    assert!(
        base.execute_source_definitions(&[source.as_bytes()], &KVMap::new(), bounded)
            .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    run(&source, "42");
}
#[test]
fn runtime_empty_branches_do_not_change_the_checked_environment() {
    let source =
        format!("{VEC}{FIRST}def selected : Nat := first 1 (Vec.cons 0 42 Vec.nil) (by decide)");
    let base = engine();
    let checked = base
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            fln::SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let executed = base
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &executed.executions.last().unwrap().exit else {
        panic!("checked source must also execute");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
    assert_eq!(
        checked.engine.logical_root(&KVMap::new()),
        executed.engine.logical_root(&KVMap::new())
    );
}
#[test]
fn empty_data_can_be_nested_and_eliminated_without_a_fake_constructor() {
    run(
        "inductive Void : Type where\ndef optional (x : Option Void) : Nat := match x with | .none => 42 | .some h => Void.rec (motive := fun _ => Nat) h\n#eval optional Option.none",
        "42",
    );
    run(
        "inductive Void (A : Type) : Type where\ndef optional (x : Option (Void Nat)) : Nat := match x with | .none => 42 | .some h => Void.rec (motive := fun _ => Nat) h\n#eval optional Option.none",
        "42",
    );
}
#[test]
fn user_empty_propositions_and_indexed_empty_data_are_eliminated() {
    run(
        "inductive Never (n : Nat) : Prop where\ndef ignore (f : Never 3 -> Nat) : Nat := 42\n#eval ignore (fun h => Never.rec (motive := fun _ => Nat) h)",
        "42",
    );
    run(
        "inductive VoidAt : Nat -> Type where\ndef optional (n : Nat) (x : Option (VoidAt n)) : Nat := match x with | .none => 42 | .some h => VoidAt.rec (motive := fun k _ => Nat) h\n#eval optional 5 Option.none",
        "42",
    );
}
