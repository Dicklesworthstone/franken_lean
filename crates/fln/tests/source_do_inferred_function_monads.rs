//! Unannotated binds recover a function-backed monad from its action's type.
//! Every example uses ordinary source classes, both checkers, and native Golem.
#![forbid(unsafe_code)]

use fln::{
    Budget, CheckerAdmissionGround, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap,
    SourceCheckLimits, VmExit,
};

const SOURCE: &str = r#"
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
structure Result (A : Type) where
  value : A
  state : Nat
def StateLike (A : Type) : Type := Nat -> Result A
def StateAlias (A : Type) : Type := StateLike A
attribute [reducible] StateAlias
def nextState {A B : Type} (r : Result A) (next : A -> StateLike B) : Result B := next r.value r.state
instance stateBind : Bind StateLike := { bind := fun action next state => nextState (action state) next }
def mark (n : Nat) : StateLike Nat := fun state => { value := state, state := state * 10 + n }
def markAlias := mark
def finish (value : Nat) : StateLike Nat := fun state => { value := value, state := state }
def score (result : Result Nat) := result.value * 1000 + result.state
"#;

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn seed() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}

fn execute(source: &str, expected: &str) {
    let base = seed()
        .check_source_files(
            &[SOURCE.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let batch = base
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    for execution in &batch.executions {
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
    }
    let VmExit::Returned(result) = &batch.executions.last().unwrap().exit else {
        panic!("the checked program did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some(expected)
    );
}

#[test]
fn unannotated_function_monad_binds_preserve_state_order_and_alias_calls() {
    execute(
        r#"
def inferred := do
  let first ← mark 1
  let second ← markAlias 2
  finish (first * 100 + second)
#eval score (inferred 3)
"#,
        // The actions see 3 then 31, and leave state 312.
        "331312",
    );
    execute(
        r#"
def fromAction (action : StateAlias Nat) := do
  let first ← action
  let second ← markAlias 2
  finish (first * 100 + second)
#eval score (fromAction (mark 1) 3)
"#,
        "331312",
    );
}

#[test]
fn recovering_a_monad_never_invents_bind_or_accepts_a_wrong_continuation() {
    let limits = SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel));
    let base = seed()
        .check_source_files(&[SOURCE.as_bytes()], &KVMap::new(), limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad (action : Nat -> Nat) := do\n  let value ← action\n  finish value",
        "def Other (A : Type) : Type := Nat -> A\ndef bad (action : Other Nat) := do\n  let value ← action\n  action",
        "def bad := do\n  let value : Bool ← mark 1\n  finish value",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits)
                .is_err(),
            "{source} must retain its ordinary source refusal"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    let recovery = "def recovered := do\n  let value ← mark 1\n  finish value";
    base.check_source_files(&[recovery.as_bytes()], &KVMap::new(), limits)
        .unwrap()
        .into_complete()
        .unwrap();
}

#[test]
fn inferred_global_and_local_action_aliases_keep_their_monad_constructor() {
    execute(
        r#"
def savedMark := mark 1
def savedAlias := savedMark
def inferred := do
  let first ← savedAlias
  let second ← markAlias 2
  finish (first * 100 + second)
#eval score (inferred 3)
"#,
        "331312",
    );
    execute(
        r#"
def inferred := do
  let saved := mark 1
  let alias := saved
  let first ← alias
  let second ← markAlias 2
  finish (first * 100 + second)
#eval score (inferred 3)
"#,
        "331312",
    );
}
