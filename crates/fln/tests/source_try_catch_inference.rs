//! Unannotated exception actions retain their named function-backed monad.
#![forbid(unsafe_code)]

use fln::{
    Budget, CheckerAdmissionGround, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap,
    SourceCheckLimits, VmExit,
};

const FIXTURE: &str = r#"
class Pure (m : Type -> Type) where
  pure : {A : Type} -> A -> m A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
class Monad (m : Type -> Type) extends Pure m, Bind m where
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
def stateBind {A B : Type} (x : StateExcept A) (next : A -> StateExcept B) : StateExcept B := fun state =>
  let report := x state
  match report.output with
  | Attempt.ok value => next value report.state
  | Attempt.error error => Report.mk (Attempt.error error) report.state
instance stateMonad : Monad StateExcept := {
  pure := fun value state => Report.mk (Attempt.ok value) state
  bind := fun action next => stateBind action next
}
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
        // `queries` holds only `#eval` commands, and #eval's auxiliary is
        // unsafe at the pin (BuiltinEvalCommand.lean:92).
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::UnsafeQuarantine
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
def generic {M : Type -> Type} [Monad M] [MonadExcept Nat M] (action : M Nat) := do
  try
    action
  catch _ =>
    action
def nested := do
  try {
    try
      fail 5
    catch inner =>
      fail (inner + 1)
  } catch outer =>
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

#[test]
fn omitted_result_families_infer_monads_from_value_parameters() {
    execute(
        &base(),
        r#"
def fromTypeKnown (A : Type) : StateAlias Nat := do
  try
    fail 5
  catch error =>
    recover error
def fromParameters (A : Type) (tag : Nat) (action : StateAlias Nat) := do
  try
    action
  catch error =>
    recover (error + tag)
def genericResult {A : Type} {M : Type -> Type} [Monad M] [MonadExcept Nat M] (action : M A) := do
  try
    action
  catch _ =>
    action
def choose {M : Type -> Type} [Monad M] (action : M Nat) : M Nat := action
def viaExpected := choose (do succeed 7)
def concrete : StateAlias Nat := do
  succeed 7
theorem parameter_result : observed (fromParameters Bool 2 (fail 5)) = 312017 := rfl
#eval observed (fromTypeKnown Bool)
#eval observed (fromParameters Bool 2 (fail 5))
#eval observed (genericResult (fail 5))
#eval observed viaExpected
#eval observed concrete
"#,
        &["312015", "312017", "311105", "31007", "31007"],
    );
}

#[test]
fn inferred_do_blocks_still_require_dictionaries_and_written_result_types() {
    let engine = checked(
        &base(),
        r#"
inductive Bare (A : Type) where
  | wrap (value : A)
def bareValue : Bare Nat := Bare.wrap 7
def choose {M : Type -> Type} [Monad M] (action : M Nat) : M Nat := action
def boolAction : StateExcept Bool := fun state => Report.mk (Attempt.ok true) state
"#,
    );
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for source in [
        "def missingKnown : Bare Nat := do bareValue",
        "def missingUnknown := do bareValue",
        "def missingParameter (action : Bare Nat) := do action",
        "def missingTypeParameter (A : Type) := do bareValue",
        // At the pin, a final type-valued argument is examined before the
        // unknown-head fallback. This would need a dictionary for the constant
        // monad `fun A => StateExcept Nat`, which has not been provided.
        "def inferredTypeParameter (A : Type) := do succeed 7",
        // The unknown monad in choose's argument is not an omitted result
        // family: its written Nat parameter must constrain the nested block.
        "def wrongResult := choose (do boolAction)",
        "def notMonadic : Nat := do succeed 7",
    ] {
        assert!(
            engine
                .check_source_files(&[source.as_bytes()], &options, limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(engine.logical_root(&options), root);
    }
    checked(&engine, "def direct : Bare Nat := bareValue");
    execute(
        &engine,
        "def retry (action : StateAlias Nat) := do { try { action } catch error => { recover error } }\n#eval observed (retry (fail 5))",
        &["312015"],
    );
}
