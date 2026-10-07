//! Pattern handlers are ordinary checked matches inside lazy handler lambdas.
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
fn environment() -> Engine {
    let engine = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    checked(
        &engine,
        r#"
class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
class MonadExcept (E : outParam Type) (m : Type -> Type) where
  throw : {A : Type} -> E -> m A
  tryCatch : {A : Type} -> m A -> (E -> m A) -> m A
class MonadExceptOf (E : Type) (m : Type -> Type) where
  tryCatch : {A : Type} -> m A -> (E -> m A) -> m A
def tryCatchThe (E : Type) {m : Type -> Type} [inst : MonadExceptOf E m] {A : Type} (action : m A) (handler : E -> m A) : m A := @MonadExceptOf.tryCatch E m inst A action handler
inductive Failure where
  | code : Nat -> Failure
  | missing : Failure
inductive Rescue (A : Type) where
  | ok : A -> Rescue A
  | error : Failure -> Rescue A
def bindRescue {A B : Type} (action : Rescue A) (next : A -> Rescue B) : Rescue B :=
  match action with
  | .ok value => next value
  | .error error => Rescue.error error
def catchRescue {A : Type} (action : Rescue A) (handler : Failure -> Rescue A) : Rescue A :=
  match action with
  | .ok value => Rescue.ok value
  | .error error => handler error
instance rescuePure : Pure Rescue := { pure := fun value => Rescue.ok value }
instance rescueBind : Bind Rescue := { bind := fun value next => bindRescue value next }
instance rescueExcept : MonadExcept Failure Rescue := { throw := fun error => Rescue.error error, tryCatch := fun action handler => catchRescue action handler }
instance rescueExceptOf : MonadExceptOf Failure Rescue := { tryCatch := fun action handler => catchRescue action handler }
def failureNumber (error : Failure) : Nat := match error with
  | .code n => n + 1000
  | .missing => 9999
def observe (action : Rescue Nat) : Nat := match action with
  | .ok value => value
  | .error error => failureNumber error
"#,
    )
}
fn executed(source: &str, expected: &[&str]) {
    executed_with(&environment(), source, expected);
}
fn executed_with(engine: &Engine, source: &str, expected: &[&str]) {
    let run = engine
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .expect("complete execution");
    assert!(run.executions.len() >= expected.len());
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
fn constructor_patterns_bind_payloads_and_preserve_success() {
    executed(
        r#"
def recovered : Rescue Nat := do
  try
    Rescue.error (Failure.code 40)
  catch
  | .code n => return (n + 2)
  | .missing => return 0
def success : Rescue Nat := do
  try
    Rescue.ok 42
  catch
  | .code n => return n
  | .missing => return 0
#eval observe recovered
#eval observe success
"#,
        &["42", "42"],
    );
}

#[test]
fn nested_matches_and_shadowed_payload_names_keep_lexical_scope() {
    executed(
        r#"
def choose (n : Nat) : Rescue Nat := do
  try
    Rescue.error (Failure.code 41)
  catch
  | .code n =>
    let n := match n with
      | .zero => 0
      | .succ k => k + 2
    return n
  | .missing => return n
#eval observe (choose 99)
"#,
        &["42"],
    );
}

#[test]
fn mixed_handlers_catch_prior_rethrows_in_source_order() {
    executed(
        r#"
def chain : Rescue Nat := do
  try
    Rescue.error (Failure.code 39)
  catch
  | .code n => Rescue.error (Failure.code (n + 1))
  | .missing => Rescue.error Failure.missing
  catch error : Failure =>
    match error with
    | .code n => Rescue.error (Failure.code (n + 1))
    | .missing => Rescue.error Failure.missing
  catch
  | .code n => return (n + 1)
  | .missing => return 0
#eval observe chain
"#,
        &["42"],
    );
}

#[test]
fn nested_regions_dispatch_to_their_own_pattern_handlers() {
    executed(
        r#"
def nested : Rescue Nat := do
  try
    Rescue.error (Failure.code 39)
  catch
  | .code n =>
    try
      Rescue.error (Failure.code (n + 1))
    catch
    | .code n => return (n + 2)
    | .missing => return 1
  | .missing => return 0
#eval observe nested
"#,
        &["42"],
    );
}

#[test]
fn a_successful_action_does_not_evaluate_pattern_handlers_or_catch_the_suffix() {
    executed(
        r#"
def suffix : Rescue Nat := do
  try
    Rescue.ok PUnit.unit
  catch
  | .code n => Rescue.error (Failure.code 7)
  | .missing => Rescue.error (Failure.code 8)
  Rescue.error (Failure.code 42)
#eval observe suffix
"#,
        &["1042"],
    );
}

#[test]
fn a_generic_dictionary_determines_the_exception_before_dot_patterns() {
    checked(
        &environment(),
        r#"
def generic {M : Type -> Type} [Pure M] [MonadExcept Failure M] (action : M Nat) : M Nat := do
  try
    action
  catch
  | .code n => return n
  | .missing => return 42
"#,
    );
}

#[test]
fn coverage_wrong_types_and_escaping_bindings_cannot_publish() {
    let engine = environment();
    let before = engine.logical_root(&KVMap::new());
    for source in [
        "def bad : Rescue Nat := do { try { Rescue.ok 42 } catch | .code n => { return n } }",
        "def bad : Rescue Nat := do { try { Rescue.ok 42 } catch | .code n => { return n } | .missing => { return true } }",
        "def bad : Rescue Nat := do { try { Rescue.ok 42 } catch | .code n => { return n } | .missing => { return absent } }",
        "def bad : Rescue Nat := do { try { Rescue.ok PUnit.unit } catch | .code n => { Rescue.ok PUnit.unit } | .missing => { Rescue.ok PUnit.unit }; return n }",
        "def bad {M : Type -> Type} [Pure M] (action : M Nat) : M Nat := do { try { action } catch | .code n => { return n } | .missing => { return 0 } }",
    ] {
        assert!(
            engine
                .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), before);
    }
    checked(
        &engine,
        "def recovered : Rescue Nat := do { try { Rescue.error Failure.missing } catch | .code n => { return n } | .missing => { return 42 } }",
    );
}

fn cleanup_environment() -> Engine {
    checked(
        &environment(),
        r#"
structure Prod (A B : Type) where
  fst : A
  snd : B
class Functor (f : Type -> Type) where
  map : {A B : Type} -> (A -> B) -> f A -> f B
class MonadFinally (m : Type -> Type) where
  tryFinally' : {A B : Type} -> m A -> (Option A -> m B) -> m (Prod A B)
def tryFinally {m : Type -> Type} {A B : Type} [MonadFinally m] [Functor m] (action : m A) (cleanup : m B) : m A :=
  Functor.map (f := m) (fun (p : Prod A B) => p.fst) (MonadFinally.tryFinally' (m := m) action (fun _ => cleanup))
def mapRescue {A B : Type} (f : A -> B) (action : Rescue A) : Rescue B := match action with
  | .ok a => Rescue.ok (f a)
  | .error e => Rescue.error e
def finishRescue {A B : Type} (action : Rescue A) (cleanup : Option A -> Rescue B) : Rescue (Prod A B) := match action with
  | .ok a => match cleanup (Option.some a) with
    | .ok b => Rescue.ok (Prod.mk a b)
    | .error e => Rescue.error e
  | .error e => match cleanup Option.none with
    | .ok b => Rescue.error e
    | .error next => Rescue.error next
instance rescueFunctor : Functor Rescue := { map := fun f action => mapRescue f action }
instance rescueFinally : MonadFinally Rescue := { tryFinally' := fun action cleanup => finishRescue action cleanup }
"#,
    )
}

#[test]
fn finalizers_stay_outside_pattern_dispatch_and_override_rethrows() {
    executed_with(
        &cleanup_environment(),
        r#"
def cleaned : Rescue Nat := do
  try
    Rescue.error (Failure.code 40)
  catch
  | .code n => return (n + 2)
  | .missing => return 0
  finally
    Rescue.ok true
def overridden : Rescue Nat := do
  try
    Rescue.error (Failure.code 40)
  catch
  | .code n => Rescue.error (Failure.code (n + 1))
  | .missing => Rescue.error Failure.missing
  finally
    Rescue.error (A := Bool) (Failure.code 42)
#eval observe cleaned
#eval observe overridden
"#,
        &["42", "1042"],
    );
}

#[test]
fn runtime_exhaustion_is_not_a_catchable_error_and_retry_is_deterministic() {
    let engine = environment();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let source = b"def recovered : Rescue Nat := do { try { Rescue.error (Failure.code 40) } catch | .code n => { return (n + 2) } | .missing => { return 0 } }\n#eval observe recovered";
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
    assert_eq!(first.executions.len(), second.executions.len());
    for (a, b) in first.executions.iter().zip(&second.executions) {
        assert_eq!(a.flbc_artifact, b.flbc_artifact);
        assert_eq!(a.result_logical_root, b.result_logical_root);
    }
    let VmExit::Returned(result) = &first.executions.last().unwrap().exit else {
        panic!("complete recovery")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some("42")
    );
    assert_eq!(engine.logical_root(&options), root);
}
