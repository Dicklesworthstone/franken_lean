//! Unannotated exception actions retain their named function-backed monad.
#![forbid(unsafe_code)]

use fln::{
    Budget, CheckerAdmissionGround, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap,
    SourceCheckLimits, VmExit,
};

const FIXTURE: &str = r#"
class MonadExcept (E : outParam Type) (m : Type -> Type) where
  throw : {A : Type} -> E -> m A
  tryCatch : {A : Type} -> m A -> (E -> m A) -> m A
class MonadExceptOf (E : Type) (m : Type -> Type) where
  throw : {A : Type} -> E -> m A
  tryCatch : {A : Type} -> m A -> (E -> m A) -> m A
def tryCatchThe (E : Type) {m : Type -> Type} [inst : MonadExceptOf E m] {A : Type} (x : m A) (handler : E -> m A) : m A := @MonadExceptOf.tryCatch E m inst A x handler
inductive Attempt (A : Type) where
  | ok (value : A)
  | error (value : Nat)
structure Report (A : Type) where
  output : Attempt A
  state : Nat
def StateExcept (A : Type) : Type := Nat -> Report A
def StateAlias (A : Type) : Type := StateExcept A
attribute [reducible] StateAlias
def stateCatch {A : Type} (x : StateExcept A) (handler : Nat -> StateExcept A) : StateExcept A := fun state =>
  let report := x state
  match report.output with
  | Attempt.ok value => Report.mk (Attempt.ok value) report.state
  | Attempt.error error => handler error report.state
instance stateException : MonadExcept Nat StateExcept := MonadExcept.mk (fun {A : Type} (error : Nat) (state : Nat) => @Report.mk A (@Attempt.error A error) state) (fun {A : Type} (x : StateExcept A) (handler : Nat -> StateExcept A) => @stateCatch A x handler)
instance stateExceptionOf : MonadExceptOf Nat StateExcept := MonadExceptOf.mk (fun {A : Type} (error : Nat) (state : Nat) => @Report.mk A (@Attempt.error A error) state) (fun {A : Type} (x : StateExcept A) (handler : Nat -> StateExcept A) => @stateCatch A x handler)
def succeed (value : Nat) : StateExcept Nat := fun state => Report.mk (Attempt.ok value) (state * 10 + 1)
def fail (error : Nat) : StateExcept Nat := fun state => Report.mk (Attempt.error error) (state * 10 + 1)
def failAlias := fail
def recover (error : Nat) : StateExcept Nat := fun state => Report.mk (Attempt.ok (error + 10)) (state * 10 + 2)
def observed (action : StateExcept Nat) : Nat :=
  let report := action 3
  match report.output with
  | Attempt.ok value => report.state * 1000 + value
  | Attempt.error error => report.state * 1000 + 100 + error
"#;

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
        .engine
}

fn base() -> Engine {
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    checked(&seed, FIXTURE)
}

fn execute(base: &Engine, source: &str, expected: &[&str]) {
    let (definitions, evaluations) = source.split_once("#eval").unwrap();
    let engine = checked(base, definitions);
    let queries = format!("#eval{evaluations}");
    let run = engine
        .execute_source_definitions(
            &[queries.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(run.executions.len(), expected.len());
    for (execution, expected) in run.executions.iter().zip(expected) {
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        let VmExit::Returned(value) = &execution.exit else {
            panic!("{:?}", execution.exit)
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(*expected)
        );
    }
}

#[test]
fn protected_actions_infer_the_monad_before_lazy_and_typed_handlers() {
    execute(
        &base(),
        r#"
def inferred := do
  try
    fail 5
  catch error =>
    recover error
def success := do
  try
    succeed 7
  catch error =>
    recover error
def typed := do
  try
    failAlias 5
  catch error : Nat =>
    recover error
def fromAction (action : StateAlias Nat) := do
  try
    action
  catch error =>
    recover error
def generic {M : Type -> Type} [MonadExcept Nat M] (action : M Nat) := do
  try
    action
  catch _ =>
    action
def nested := do
  try
    try
      fail 5
    catch inner =>
      fail (inner + 1)
  catch outer =>
    recover outer
#eval observed inferred
#eval observed success
#eval observed typed
#eval observed (fromAction (fail 5))
#eval observed (generic (fail 5))
#eval observed nested
"#,
        &["312015", "31007", "312015", "312015", "311105", "3112016"],
    );
}

#[test]
fn inferred_catches_keep_dictionary_and_handler_type_checks() {
    let engine = base();
    let root = engine.logical_root(&KVMap::new());
    for source in [
        "def bad := do { try { fail 5 } catch _ => { true } }",
        "def bad := do { try { fail 5 } catch _ : Bool => { recover 0 } }",
        "def bad : Nat := do { try { fail 5 } catch error => { recover error } }",
        "def Other (A : Type) : Type := Bool -> Report A\ndef bad (action : Other Nat) := do { try { action } catch _ => { action } }",
        "def bad := do { try { fail 5 } catch error => { recover error }; recover error }",
    ] {
        assert!(
            engine
                .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source} must keep its ordinary source refusal"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
    execute(
        &engine,
        "def recovered := do { try { fail 5 } catch error => { recover error } }\n#eval observed recovered",
        &["312015"],
    );
}
