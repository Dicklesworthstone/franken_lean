//! Real checked state/error dictionaries make cleanup ordering observable in Golem.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits, VmExit,
};
fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap()
        .engine
}
const FIXTURE: &str = r#"
structure Prod (A B : Type) where
  fst : A
  snd : B
class Pure (m : Type -> Type) where
  pure : {A : Type} -> A -> m A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
class Functor (m : Type -> Type) where
  map : {A B : Type} -> (A -> B) -> m A -> m B
class MonadExcept (E : outParam Type) (m : Type -> Type) where
  throw : {A : Type} -> E -> m A
  tryCatch : {A : Type} -> m A -> (E -> m A) -> m A
class MonadFinally (m : Type -> Type) where
  tryFinally' : {A B : Type} -> m A -> (Option A -> m B) -> m (Prod A B)
def tryFinally {m : Type -> Type} {A B : Type} [fin : MonadFinally m] [mapping : Functor m] (x : m A) (cleanup : m B) : m A :=
  @Functor.map m mapping (Prod A B) A (fun (p : Prod A B) => p.fst) (@MonadFinally.tryFinally' m fin A B x (fun _ => cleanup))
inductive Attempt (E A : Type) where
  | ok (value : A)
  | error (value : E)
structure Report (A : Type) where
  output : Attempt Nat A
  state : Nat
def Logged (A : Type) : Type := Nat -> Report A
def loggedBind {A B : Type} (x : Logged A) (f : A -> Logged B) : Logged B := fun s =>
  let r := x s
  match r.output with
  | Attempt.ok a => f a r.state
  | Attempt.error e => Report.mk (Attempt.error e) r.state
def loggedCatch {A : Type} (x : Logged A) (f : Nat -> Logged A) : Logged A := fun s =>
  let r := x s
  match r.output with
  | Attempt.ok a => Report.mk (Attempt.ok a) r.state
  | Attempt.error e => f e r.state
def loggedMap {A B : Type} (f : A -> B) (x : Logged A) : Logged B := fun s =>
  let r := x s
  match r.output with
  | Attempt.ok a => Report.mk (Attempt.ok (f a)) r.state
  | Attempt.error e => Report.mk (Attempt.error e) r.state
def loggedFinally {A B : Type} (x : Logged A) (f : Option A -> Logged B) : Logged (Prod A B) := fun s =>
  let r := x s
  match r.output with
  | Attempt.ok a =>
    let c := f (Option.some a) r.state
    match c.output with
    | Attempt.ok b => Report.mk (Attempt.ok (Prod.mk a b)) c.state
    | Attempt.error e => Report.mk (Attempt.error e) c.state
  | Attempt.error e =>
    let c := f Option.none r.state
    match c.output with
    | Attempt.ok b => Report.mk (Attempt.error e) c.state
    | Attempt.error other => Report.mk (Attempt.error other) c.state
instance loggedPure : Pure Logged := Pure.mk (fun a s => Report.mk (Attempt.ok a) s)
instance loggedBinding : Bind Logged := Bind.mk (fun a f => loggedBind a f)
instance loggedFunctor : Functor Logged := Functor.mk (fun f a => loggedMap f a)
instance loggedException : MonadExcept Nat Logged := MonadExcept.mk (fun {A : Type} (e : Nat) (s : Nat) => @Report.mk A (@Attempt.error Nat A e) s) (fun {A : Type} (x : Logged A) (f : Nat -> Logged A) => @loggedCatch A x f)
instance loggedFinalizer : MonadFinally Logged := MonadFinally.mk (fun x f => loggedFinally x f)
def succeed {A : Type} (a : A) : Logged A := @Pure.pure Logged loggedPure A a
def raise {A : Type} (e : Nat) : Logged A := @MonadExcept.throw Nat Logged loggedException A e
def mark (n : Nat) : Logged Nat := fun s => Report.mk (Attempt.ok n) (s * 10 + n)
def observed (action : Logged Nat) : Nat :=
  let r := action 0
  match r.output with
  | Attempt.ok n => r.state * 1000 + n
  | Attempt.error e => r.state * 1000 + 100 + e
"#;
fn base() -> Engine {
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    checked(&seed, FIXTURE)
}
fn execute(engine: &Engine, source: &str, expected: &[&str]) {
    let (defs, queries) = source.split_once("#eval").unwrap();
    let engine = checked(engine, defs);
    let query = format!("#eval{queries}");
    let run = engine
        .execute_source_definitions(
            &[query.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(run.executions.len(), expected.len());
    for (actual, expected) in run.executions.iter().zip(expected) {
        let VmExit::Returned(value) = &actual.exit else {
            panic!("{:?}", actual.exit)
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(*expected)
        );
    }
}
#[test]
fn cleanup_runs_once_after_success_and_failure() {
    execute(
        &base(),
        r#"
def success : Logged Nat := do
  try
    mark 1
    return 7
  finally
    mark 2
def failure : Logged Nat := do
  try
    mark 1
    raise (5 : Nat)
  finally
    mark 2
#eval observed success
#eval observed failure
"#,
        &["12007", "12105"],
    );
}
#[test]
fn cleanup_encloses_handlers_and_rethrows() {
    execute(
        &base(),
        r#"
def recovered : Logged Nat := do
  try
    mark 1
    raise (5 : Nat)
  catch e =>
    mark 2
    succeed (e + 2)
  finally
    mark 3
def rethrown : Logged Nat := do
  try
    mark 1
    raise (5 : Nat)
  catch e =>
    mark 2
    raise (e + 1)
  finally
    mark 3
#eval observed recovered
#eval observed rethrown
"#,
        &["123007", "123106"],
    );
}
#[test]
fn finalizer_error_takes_precedence_over_action_error_or_value() {
    execute(
        &base(),
        r#"
def replacedValue : Logged Nat := do
  try
    mark 1
    return 7
  finally
    mark 2
    (raise (9 : Nat) : Logged Nat)
def replacedError : Logged Nat := do
  try
    mark 1
    raise (5 : Nat)
  finally
    mark 2
    (raise (9 : Nat) : Logged Nat)
#eval observed replacedValue
#eval observed replacedError
"#,
        &["12109", "12109"],
    );
}
#[test]
fn nested_finalizers_and_following_statements_keep_order() {
    execute(
        &base(),
        r#"
def nested : Logged Nat := do
  try
    try
      mark 1
      succeed (7 : Nat)
    finally
      mark 2
  finally
    mark 3
def followed : Logged Nat := do
  try
    mark 1
    succeed (7 : Nat)
  finally
    mark 2
  mark 3
  return 42
#eval observed nested
#eval observed followed
"#,
        &["123007", "123042"],
    );
}
#[test]
fn generic_cleanup_uses_only_the_admitted_finally_and_functor_contracts() {
    checked(
        &base(),
        r#"
def ensure {m : Type -> Type} {A B : Type} [MonadFinally m] [Functor m] (x : m A) (cleanup : m B) : m A := do
  try
    x
  finally
    cleanup
"#,
    );
}
#[test]
fn invalid_cleanup_or_bare_try_refuses_atomically() {
    let engine = base();
    let root = engine.logical_root(&KVMap::new());
    for source in [
        "def bad : Logged Nat := do { try { succeed (7 : Nat) } }",
        "def bad : Logged Nat := do { try { succeed (7 : Nat) } finally { return 8 } }",
        "def bad : Logged Nat := do { try { succeed (7 : Nat) } finally { break } }",
        "def bad : Logged Nat := do { try { succeed (7 : Nat) } finally { continue } }",
        "def bad : Logged Nat := do { try { succeed (7 : Nat) } finally { missing } }",
        "def bad : Logged Nat := do { try { succeed (7 : Nat) } catch e => { succeed e } finally { succeed e } }",
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
        "def good : Logged Nat := do { try { return 42 } finally { mark 1 } }",
    );
}

#[test]
fn interruption_is_not_caught_and_retry_reproduces_cleanup_and_artifact() {
    let engine = checked(
        &base(),
        "def run : Logged Nat := do { try { mark 1; raise (5 : Nat) } catch e => { succeed (e + 2) } finally { mark 2 } }",
    );
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let source = b"#eval observed run";
    let mut small = EngineExecutionLimits::new(limits().admission.kernel);
    small.vm.max_steps = 1;
    assert!(matches!(
        engine
            .execute_source_definitions(&[source], &options, small)
            .unwrap(),
        fln::Outcome::Inconclusive(_)
    ));
    assert_eq!(engine.logical_root(&options), root);
    let run = || {
        engine
            .execute_source_definitions(
                &[source],
                &options,
                EngineExecutionLimits::new(limits().admission.kernel),
            )
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let first = run();
    let second = run();
    assert_eq!(
        first.executions[0].flbc_artifact,
        second.executions[0].flbc_artifact
    );
    assert_eq!(
        first.engine.logical_root(&options),
        second.engine.logical_root(&options)
    );
    let VmExit::Returned(value) = &second.executions[0].exit else {
        panic!("normal retry")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("12007")
    );
}
