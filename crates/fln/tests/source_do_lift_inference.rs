//! Unannotated action binds infer the lifted element through ordinary source
//! elaboration, both admission checkers, and the native compiler/interpreter.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits, VmExit,
};

const CLASSES: &str = r#"
class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
class MonadLiftT (m n : Type -> Type) where
  monadLift : {A : Type} -> m A -> n A
def liftM {m n : Type -> Type} [inst : MonadLiftT m n] {A : Type} (x : m A) : n A := @MonadLiftT.monadLift m n inst A x
"#;

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn seed() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
        .engine
}

#[test]
fn unannotated_do_binds_infer_the_element_of_an_abstract_lift() {
    let base = checked(&seed(), CLASSES);
    checked(
        &base,
        r#"
def lifted {M N : Type -> Type} [Pure N] [Bind N] [MonadLiftT M N] {A : Type} (action : M A) : N A := do
  let x ← action
  return x
def discard {M N : Type -> Type} [Pure N] [Bind N] [MonadLiftT M N] (action : M Nat) : N Nat := do
  action
  return 7
"#,
    );
}

#[test]
fn absent_lift_refuses_the_do_program_and_the_engine_recovers() {
    let base = checked(&seed(), CLASSES);
    let root = base.logical_root(&KVMap::new());
    let invalid = "def bad {M N : Type -> Type} [Pure N] [Bind N] (action : M Nat) : N Nat := do\n  let x ← action\n  return x";
    assert!(
        base.check_source_files(&[invalid.as_bytes()], &KVMap::new(), limits())
            .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    checked(
        &base,
        "def recovered {M N : Type -> Type} [Pure N] [Bind N] [MonadLiftT M N] (action : M Nat) : N Nat := do\n  let x ← action\n  return x",
    );
}

#[test]
fn a_function_backed_action_lifts_and_runs_once_on_golem() {
    let source = format!(
        "{CLASSES}{}",
        r#"
def ReaderLike (A : Type) : Type := Nat -> A
structure Result (A : Type) where
  value : A
  state : Nat
def StateLike (A : Type) : Type := Nat -> Result A
instance statePure : Pure StateLike := { pure := fun value state => { value := value, state := state } }
def stateNext {A B : Type} (r : Result A) (next : A -> StateLike B) : Result B := next r.value r.state
instance stateBind : Bind StateLike := { bind := fun action next state => stateNext (action state) next }
instance readLift : MonadLiftT ReaderLike StateLike := { monadLift := fun action state => { value := action state, state := state + 1 } }
def read : ReaderLike Nat := fun n => n
def program : StateLike Nat := do
  let x ← read
  let y ← read
  return (x * 10 + y)
def score (result : Result Nat) : Nat := result.value + result.state
#eval score (program 3)
"#
    );
    let run = seed()
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|error| panic!("{error:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &run.executions.last().unwrap().exit else {
        panic!("Golem did not return");
    };
    // The two binds read 3 then 4, incrementing the state once each: 34 + 5.
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("39")
    );
}
