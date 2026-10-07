//! Nonlocal returns cross handlers and cleanup as checked data, never VM jumps.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Outcome,
    SourceCheckLimits, VmExit,
};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn checked(engine: &Engine, source: &str) -> Engine {
    engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .expect("complete admission")
        .engine
}
fn engine() -> Engine {
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    checked(
        &seed,
        r#"
class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
class Functor (f : Type -> Type) where
  map : {A B : Type} -> (A -> B) -> f A -> f B
class MonadExcept (E : outParam Type) (m : Type -> Type) where
  throw : {A : Type} -> E -> m A
  tryCatch : {A : Type} -> m A -> (E -> m A) -> m A
class MonadExceptOf (E : Type) (m : Type -> Type) where
  tryCatch : {A : Type} -> m A -> (E -> m A) -> m A
structure Prod (A B : Type) where
  fst : A
  snd : B
class MonadFinally (m : Type -> Type) where
  tryFinally' : {A B : Type} -> m A -> (Option A -> m B) -> m (Prod A B)
def tryCatchThe (E : Type) {m : Type -> Type} [inst : MonadExceptOf E m] {A : Type} (action : m A) (handler : E -> m A) : m A := @MonadExceptOf.tryCatch E m inst A action handler
def tryFinally {m : Type -> Type} {A B : Type} [MonadFinally m] [Functor m] (action : m A) (cleanup : m B) : m A := Functor.map (f := m) (fun (p : Prod A B) => p.fst) (MonadFinally.tryFinally' (m := m) action (fun _ => cleanup))
inductive Fault where
  | code : Nat -> Fault
  | missing : Fault
inductive Result (A : Type) where
  | ok : A -> Result A
  | error : Fault -> Result A
structure Audit (A : Type) where
  result : Result A
  trace : Nat
def Logged (A : Type) := Nat -> Audit A
def pureLogged {A : Type} (value : A) : Logged A := fun trace => Audit.mk (Result.ok value) trace
def failLogged {A : Type} (code : Nat) : Logged A := fun trace => Audit.mk (Result.error (Fault.code code)) trace
def mark (digit : Nat) : Logged PUnit := fun trace => Audit.mk (Result.ok PUnit.unit) (trace * 10 + digit)
def bindLogged {A B : Type} (action : Logged A) (next : A -> Logged B) : Logged B := fun trace =>
  let prior := action trace
  match prior.result with
  | .ok value => next value prior.trace
  | .error error => Audit.mk (Result.error error) prior.trace
def catchLogged {A : Type} (action : Logged A) (handler : Fault -> Logged A) : Logged A := fun trace =>
  let prior := action trace
  match prior.result with
  | .ok value => prior
  | .error error => handler error prior.trace
def mapLogged {A B : Type} (f : A -> B) (action : Logged A) : Logged B := fun trace =>
  let prior := action trace
  match prior.result with
  | .ok value => Audit.mk (Result.ok (f value)) prior.trace
  | .error error => Audit.mk (Result.error error) prior.trace
def resultOption {A : Type} (result : Result A) : Option A := match result with
  | .ok value => Option.some value
  | .error error => Option.none
def finishLogged {A B : Type} (action : Logged A) (cleanup : Option A -> Logged B) : Logged (Prod A B) := fun trace =>
  let prior := action trace
  let after := cleanup (resultOption prior.result) prior.trace
  match after.result with
  | .error error => Audit.mk (Result.error error) after.trace
  | .ok b => match prior.result with
    | .error error => Audit.mk (Result.error error) after.trace
    | .ok a => Audit.mk (Result.ok (Prod.mk a b)) after.trace
instance loggedPure : Pure Logged := { pure := fun value => pureLogged value }
instance loggedBind : Bind Logged := { bind := fun action next => bindLogged action next }
instance loggedFunctor : Functor Logged := { map := fun f action => mapLogged f action }
instance loggedExcept : MonadExcept Fault Logged := { throw := fun error => fun trace => Audit.mk (Result.error error) trace, tryCatch := fun action handler => catchLogged action handler }
instance loggedExceptOf : MonadExceptOf Fault Logged := { tryCatch := fun action handler => catchLogged action handler }
instance loggedFinally : MonadFinally Logged := { tryFinally' := fun action cleanup => finishLogged action cleanup }
def observe (result : Result Nat) : Nat := match result with
  | .ok n => n
  | .error error => match error with
    | .code n => n + 1000
    | .missing => 9999
"#,
    )
}
fn executed(source: &str, expected: &[&str]) {
    let run = engine()
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .expect("complete execution");
    let values: Vec<_> = run.executions[run.executions.len() - expected.len()..]
        .iter()
        .map(|e| {
            let VmExit::Returned(value) = &e.exit else {
                panic!("{:?}", e.exit)
            };
            fln_vm::interpreter::nat_decimal(&value.value).expect("Nat result")
        })
        .collect();
    assert_eq!(values, expected);
}

#[test]
fn return_from_body_skips_suffix_but_normal_completion_resumes_once() {
    executed(
        r#"
def program (early : Bool) : Logged Nat := do
  try
    mark 1
    if early then
      return 42
    mark 2
  catch e =>
    mark 9
  mark 3
  return 7
#eval (program true 0).trace
#eval observe (program true 0).result
#eval (program false 0).trace
#eval observe (program false 0).result
"#,
        &["1", "42", "123", "7"],
    );
}

#[test]
fn a_pattern_handler_can_return_after_recovery_and_cleanup_still_runs() {
    executed(
        r#"
def program : Logged Nat := do
  try
    mark 1
    failLogged 40
  catch
  | .code n => mark 2; return (n + 2)
  | .missing => return 0
  finally
    mark 3
  mark 9
  return 7
#eval (program 0).trace
#eval observe (program 0).result
"#,
        &["123", "42"],
    );
}

#[test]
fn cleanup_overrides_a_pending_return_and_suffix_errors_are_not_recaught() {
    executed(
        r#"
def overridden : Logged Nat := do
  try
    mark 1
    return 42
  catch _ => mark 9
  finally
    mark 2
    failLogged (A := Bool) 8
  mark 9
  return 7
def outside (early : Bool) : Logged Nat := do
  try
    mark 1
    if early then return 42
    mark 2
  catch _ => mark 9
  finally
    mark 3
  mark 4
  failLogged 8
#eval (overridden 0).trace
#eval observe (overridden 0).result
#eval (outside true 0).trace
#eval observe (outside true 0).result
#eval (outside false 0).trace
#eval observe (outside false 0).result
"#,
        &["12", "1008", "13", "42", "1234", "1008"],
    );
}

#[test]
fn nested_handlers_forward_returns_after_inner_then_outer_cleanup() {
    executed(
        r#"
def nested (early : Bool) : Logged Nat := do
  try
    try
      mark 1
      if early then return 42
      mark 2
    catch _ => mark 9
    finally
      mark 3
    mark 4
  catch _ => mark 9
  finally
    mark 5
  mark 6
  return 7
#eval (nested true 0).trace
#eval observe (nested true 0).result
#eval (nested false 0).trace
#eval observe (nested false 0).result
"#,
        &["135", "42", "123456", "7"],
    );
}

#[test]
fn an_inner_cleanup_error_can_be_caught_before_an_outer_return() {
    executed(
        r#"
def nested : Logged Nat := do
  try
    try
      mark 1
      return 42
    finally
      mark 2
      failLogged (A := Bool) 40
    mark 9
  catch
  | .code n => mark 3; return (n + 2)
  | .missing => return 0
  finally
    mark 4
  mark 9
  return 7
#eval (nested 0).trace
#eval observe (nested 0).result
"#,
        &["1234", "42"],
    );
}

#[test]
fn a_returning_try_in_a_conditional_skips_the_enclosing_suffix() {
    executed(
        r#"
def branch (which : Bool) : Logged Nat := do
  if which then
    try
      mark 1
      return 42
    catch _ => mark 9
    finally
      mark 2
  else
    mark 3
  mark 4
  return 7
#eval (branch true 0).trace
#eval observe (branch true 0).result
#eval (branch false 0).trace
#eval observe (branch false 0).result
"#,
        &["12", "42", "34", "7"],
    );
}

#[test]
fn generic_result_types_and_typed_handlers_are_checked_without_injectivity() {
    let engine = engine();
    checked(
        &engine,
        r#"
def generic {M : Type -> Type} {E A : Type} [Pure M] [Bind M]
    [MonadExcept E M] (early : Bool) (value : A) (action : M PUnit) : M A := do
  try
    if early then return value
    action
  catch _ => action
  return value
def typed {M : Type -> Type} {E A : Type} [Pure M] [Bind M]
    [MonadExceptOf E M] (early : Bool) (value : A) (action : M PUnit) : M A := do
  try
    if early then return value
    action
  catch _ : E => action
  return value
"#,
    );
}

#[test]
fn inactive_returns_and_outside_suffixes_keep_type_and_scope_obligations() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    for source in [
        "def bad : Logged Nat := do { try { if false then return true; mark 1 } catch _ => mark 2; return 42 }",
        "def bad : Logged Nat := do { try { return 42 } catch _ => mark 2; unknown }",
        "def bad : Logged Nat := do { try { failLogged 1 } catch error => { return 42 }; return error }",
        "def bad : Logged Nat := do { try { return 42 } finally { return PUnit.unit }; return 0 }",
        "def bad : Logged Nat := do { try { return 42; unknown } catch _ => mark 2; return 0 }",
        "def bad : Logged Nat := do { try { break } catch _ => mark 2; return 0 }",
    ] {
        assert!(
            engine
                .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
    checked(
        &engine,
        "def good : Logged Nat := do { try { return 42 } catch _ => mark 2; return 7 }",
    );
}

#[test]
fn an_owned_return_payload_survives_cleanup_without_running_the_suffix() {
    executed(
        r#"
def program (text : String) : Logged String := do
  try
    mark 1
    return (String.append text "abc")
  catch _ => return "wrong"
  finally
    mark 2
  mark 9
  return "fallthrough"
def size (result : Result String) : Nat := match result with
  | .ok text => String.length text
  | .error _ => 999
#eval (program "hi" 0).trace
#eval size (program "hi" 0).result
"#,
        &["12", "5"],
    );
}

#[test]
fn exhaustion_cannot_be_caught_and_retry_preserves_artifacts_and_results() {
    let engine = engine();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let source = b"def program : Logged Nat := do { try { mark 1; return 42 } catch _ => { return 999 } finally { mark 2 }; mark 9; return 7 }\n#eval (program 0).trace\n#eval observe (program 0).result";
    let normal = EngineExecutionLimits::new(limits().admission.kernel);
    let mut stopped = normal;
    stopped.vm.max_steps = 1;
    assert!(matches!(
        engine
            .execute_source_definitions(&[source], &options, stopped)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(engine.logical_root(&options), root);
    let first = engine
        .execute_source_definitions(&[source], &options, normal)
        .unwrap()
        .into_complete()
        .unwrap();
    let second = engine
        .execute_source_definitions(&[source], &options, normal)
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(first.executions.len() >= 2);
    assert_eq!(first.executions.len(), second.executions.len());
    for (a, b) in first.executions.iter().zip(&second.executions) {
        assert_eq!(a.flbc_artifact, b.flbc_artifact);
        assert_eq!(a.result_logical_root, b.result_logical_root);
    }
    for (execution, expected) in first.executions.iter().rev().take(2).zip(["42", "12"]) {
        let VmExit::Returned(result) = &execution.exit else {
            panic!("complete return transfer")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
            Some(expected)
        );
    }
    assert_eq!(engine.logical_root(&options), root);
}

#[test]
fn a_value_bearing_nested_completion_is_not_silently_discarded() {
    let engine = engine();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    // These need both a normal value and a nonlocal return payload. The first
    // packet profile explicitly refuses that boundary instead of skipping the
    // value continuation or moving it into the handler's dynamic extent.
    for source in [
        "def program (early : Bool) : Logged Nat := do\n  let n : Nat ← do\n    try\n      if early then return 42\n      pureLogged (5 : Nat)\n    catch _ => pureLogged (6 : Nat)\n  return (n + 1)",
        "def program (early : Bool) : Logged Nat := do\n  do\n    try\n      if early then return 42\n      mark 1\n    catch _ => mark 2\n  mark 3\n  return 7",
    ] {
        assert!(
            engine
                .check_source_files(&[source.as_bytes()], &options, limits())
                .is_err()
        );
        assert_eq!(engine.logical_root(&options), root);
    }
}
