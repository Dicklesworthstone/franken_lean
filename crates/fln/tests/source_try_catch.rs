//! Native exception syntax -> admitted dictionary calls -> both checkers -> Golem.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits, VmExit,
};
fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn checked(base: &Engine, s: &str) -> Engine {
    base.check_source_files(&[s.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{s}\n{e:?}"))
        .into_complete()
        .unwrap()
        .engine
}
const CLASSES: &str = r#"
class Pure (m : Type -> Type) where
  pure : {A : Type} -> A -> m A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
class MonadExcept (E : outParam Type) (m : Type -> Type) where
  throw : {A : Type} -> E -> m A
  tryCatch : {A : Type} -> m A -> (E -> m A) -> m A
class MonadExceptOf (E : Type) (m : Type -> Type) where
  throw : {A : Type} -> E -> m A
  tryCatch : {A : Type} -> m A -> (E -> m A) -> m A
def tryCatchThe (E : Type) {m : Type -> Type} [inst : MonadExceptOf E m] {A : Type} (x : m A) (handler : E -> m A) : m A := @MonadExceptOf.tryCatch E m inst A x handler
"#;
const TRIAL: &str = r#"
inductive Attempt (E A : Type) where
  | ok (value : A)
  | error (value : E)
def Trial (A : Type) : Type := Attempt Nat A
def trialBind {A B : Type} (x : Trial A) (f : A -> Trial B) : Trial B :=
  match x with
  | Attempt.ok a => f a
  | Attempt.error e => Attempt.error e
def trialCatch {A : Type} (x : Trial A) (f : Nat -> Trial A) : Trial A :=
  match x with
  | Attempt.ok a => Attempt.ok a
  | Attempt.error e => f e
instance trialPure : Pure Trial := Pure.mk (fun a => Attempt.ok a)
instance trialBinding : Bind Trial := Bind.mk (fun a f => trialBind a f)
instance trialException : MonadExcept Nat Trial := MonadExcept.mk (fun {A : Type} (e : Nat) => @Attempt.error Nat A e) (fun {A : Type} (a : Trial A) (f : Nat -> Trial A) => @trialCatch A a f)
instance trialExceptionOf : MonadExceptOf Nat Trial := MonadExceptOf.mk (fun {A : Type} (e : Nat) => @Attempt.error Nat A e) (fun {A : Type} (a : Trial A) (f : Nat -> Trial A) => @trialCatch A a f)
def succeed {A : Type} (x : A) : Trial A := @Pure.pure Trial trialPure A x
def raise {A : Type} (e : Nat) : Trial A := @MonadExcept.throw Nat Trial trialException A e
def result (x : Trial Nat) : Nat := match x with | Attempt.ok n => n | Attempt.error e => e + 100
"#;
fn base() -> Engine {
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    checked(&checked(&seed, CLASSES), TRIAL)
}
fn execute(engine: &Engine, s: &str, expected: &[&str]) {
    let (definitions, evaluations) = s.split_once("#eval").expect("evaluation query");
    let engine = checked(engine, definitions);
    let evaluations = format!("#eval{evaluations}");
    let run = engine
        .execute_source_definitions(
            &[evaluations.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|e| panic!("{s}\n{e:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(run.executions.len(), expected.len());
    for (e, n) in run.executions.iter().zip(expected) {
        let VmExit::Returned(v) = &e.exit else {
            panic!("{:?}", e.exit)
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&v.value).as_deref(),
            Some(*n)
        );
    }
}
#[test]
fn terminal_catches_select_only_the_matching_path() {
    execute(
        &base(),
        r#"
def good : Trial Nat := do
  try
    return 7
  catch e =>
    return (e + 9)
def bad : Trial Nat := do
  try
    raise (5 : Nat)
  catch e =>
    return (e + 9)
#eval result good
#eval result bad
"#,
        &["7", "14"],
    );
}
#[test]
fn typed_handlers_and_rethrows_compose_left_to_right() {
    execute(
        &base(),
        r#"
def run : Trial Nat := do
  try
    raise (3 : Nat)
  catch e : Nat =>
    raise (e + 1)
  catch e : Nat =>
    return (e + 2)
#eval result run
"#,
        &["6"],
    );
}
#[test]
fn caught_action_resumes_the_outer_sequence_once() {
    execute(
        &base(),
        r#"
def run : Trial Nat := do
  try
    raise (3 : Nat)
  catch e =>
    succeed (e + 4)
  return 42
#eval result run
"#,
        &["42"],
    );
}
#[test]
fn generic_handlers_use_the_callers_dictionary() {
    checked(
        &base(),
        r#"
def recover {M : Type -> Type} [Pure M] [Bind M] [MonadExcept Nat M] (x : M Nat) : M Nat := do
  try
    x
  catch e =>
    return (e + 1)
"#,
    );
}
#[test]
fn bad_handlers_do_not_publish_and_valid_retry_recovers() {
    let engine = base();
    let root = engine.logical_root(&KVMap::new());
    for s in [
        "def bad : Trial Nat := do { try { return 1 } catch e => { return true } }",
        "def bad : Trial Nat := do { try { return 1 }; return 2 }",
        "def bad : Trial Nat := do { try { return 1 } catch e : Bool => { return 2 } }",
    ] {
        assert!(
            engine
                .check_source_files(&[s.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{s}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
    checked(
        &engine,
        "def good : Trial Nat := do { try { return 1 } catch e => { return e } }",
    );
    // A handler return crosses the completed exception region, rather than
    // becoming ordinary fallthrough to the following return.
    execute(
        &engine,
        "def recovered : Trial Nat := do { try { raise (1 : Nat) } catch e => { return e }; return 2 }\n#eval result recovered",
        &["1"],
    );
}

#[test]
fn wildcard_handlers_and_nested_regions_execute_without_leaking_scope() {
    execute(
        &base(),
        r#"
def nested : Trial Nat := do
  try
    try
      raise (3 : Nat)
    catch inner =>
      raise (inner + 1)
  catch outer =>
    return (outer + 2)
def ignored : Trial Nat := do { try { raise (3 : Nat) } catch _ => { return 42 } }
#eval result nested
#eval result ignored
"#,
        &["6", "42"],
    );
}

#[test]
fn handler_is_lazy_and_does_not_catch_the_following_sequence() {
    execute(
        &base(),
        r#"
def success : Trial Nat := do { try { succeed (7 : Nat) } catch e => { raise (999 : Nat) } }
def suffix : Trial Nat := do
  try
    succeed (7 : Nat)
  catch e =>
    succeed (999 : Nat)
  raise (12 : Nat)
#eval result success
#eval result suffix
"#,
        &["7", "112"],
    );
}

#[test]
fn rejected_handler_scopes_do_not_hide_invalid_or_unsupported_code() {
    let engine = base();
    let before = engine.logical_root(&KVMap::new());
    for source in [
        "def bad : Trial Nat := do { try { succeed (7 : Nat) } catch e => { missing e } }",
        "def bad : Trial Nat := do { try { succeed (7 : Nat) } catch e => { succeed e }; succeed e }",
        "def bad : Trial Nat := do { try { succeed (7 : Nat) } finally { succeed (1 : Nat) } }",
        "def bad : Trial Nat := do { try { break } catch e => { return e } }",
    ] {
        assert!(
            engine
                .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), before);
    }
}
