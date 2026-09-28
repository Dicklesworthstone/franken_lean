//! Native refutable do binds: parse, elaborate and admit with both checkers.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

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
def Id (A : Type) : Type := A
instance idPure : Pure Id := { pure := fun a => a }
instance idBind : Bind Id := { bind := fun a k => k a }
inductive Maybe (A : Type) where
  | none
  | some (value : A)
"#,
    )
}
#[test]
fn successful_and_failed_monadic_patterns_have_distinct_continuations() {
    checked(
        &engine(),
        r#"
def unwrap (action : Id (Maybe Nat)) : Id Nat := do
  let Maybe.some x ← action | return 0
  return (x + 1)
theorem found : unwrap (Maybe.some 41) = 42 := by rfl
theorem absent : unwrap Maybe.none = 0 := by rfl
"#,
    );
}
#[test]
fn pure_patterns_use_the_same_checked_failure_and_success_scopes() {
    checked(
        &engine(),
        r#"
def unwrapPure (value : Maybe Nat) : Id Nat := do
  let (Maybe.some x) := value | return 0
  return (x + 1)
theorem foundPure : unwrapPure (Maybe.some 41) = 42 := by rfl
theorem absentPure : unwrapPure Maybe.none = 0 := by rfl
"#,
    );
}

#[test]
fn annotated_nested_patterns_and_abstract_monads_preserve_expected_types() {
    checked(
        &engine(),
        r#"
def unwrapGeneric {M : Type -> Type} [Pure M] [Bind M]
    (action : M (Maybe (Maybe Nat))) : M Nat := do
  let Maybe.some (Maybe.some x) : Maybe (Maybe Nat) ← action | return 0
  return x
theorem nestedFound : unwrapGeneric (M := Id) (Maybe.some (Maybe.some 42)) = 42 := by rfl
theorem innerMissing : unwrapGeneric (M := Id) (Maybe.some Maybe.none) = 0 := by rfl
theorem outerMissing : unwrapGeneric (M := Id) Maybe.none = 0 := by rfl
"#,
    );
}

#[test]
fn effectful_subjects_execute_once_and_only_the_selected_branch_runs() {
    checked(
        &engine(),
        r#"
structure Result (A : Type) where
  value : A
  state : Nat
def State (A : Type) : Type := Nat -> Result A
instance statePure : Pure State := { pure := fun value state => { value := value, state := state } }
def stateNext {A B : Type} (r : Result A) (next : A -> State B) : Result B := next r.value r.state
instance stateBind : Bind State := { bind := fun action next state => stateNext (action state) next }
def mark (n : Nat) : State Nat := fun s => { value := s, state := s * 10 + n }
def subject (value : Maybe Nat) : State (Maybe Nat) := fun s => { value := value, state := s * 10 + 1 }
def traced (value : Maybe Nat) : State Nat := do
  let Maybe.some x ← subject value |
    let _ ← mark 2
    return 99
  let _ ← mark 3
  return x
theorem failureTrace : (traced Maybe.none 0).state = 12 := by rfl
theorem failureValue : (traced Maybe.none 0).value = 99 := by rfl
theorem successTrace : (traced (Maybe.some 42) 0).state = 13 := by rfl
theorem successValue : (traced (Maybe.some 42) 0).value = 42 := by rfl
"#,
    );
}

#[test]
fn monadic_failure_is_not_confused_with_pattern_failure() {
    checked(
        &engine(),
        r#"
def maybeBind {A B : Type} (action : Maybe A) (next : A -> Maybe B) : Maybe B :=
  match action with
  | Maybe.none => Maybe.none
  | Maybe.some value => next value
instance maybePure : Pure Maybe := { pure := fun value => Maybe.some value }
instance maybeBinder : Bind Maybe := { bind := fun action next => maybeBind action next }
def unpack (action : Maybe (Maybe Nat)) : Maybe Nat := do
  let Maybe.some x ← action | return 99
  return x
theorem failedAction : unpack Maybe.none = Maybe.none := by rfl
theorem failedPattern : unpack (Maybe.some Maybe.none) = Maybe.some 99 := by rfl
theorem successfulPattern : unpack (Maybe.some (Maybe.some 42)) = Maybe.some 42 := by rfl
"#,
    );
}

#[test]
fn fallback_locals_shadow_only_their_own_branch_and_nested_returns_do_not_escape() {
    checked(
        &engine(),
        r#"
def scoped (x : Nat) (value : Maybe Nat) : Id Nat := do
  let Maybe.some x ← value |
    let y ← (do { return (x + 1) })
    return y
  return x
theorem failedScope : scoped 40 Maybe.none = 41 := by rfl
theorem successScope : scoped 40 (Maybe.some 42) = 42 := by rfl
def nestedFailure (first second : Maybe Nat) : Id Nat := do
  let Maybe.some x ← first |
    let Maybe.some y ← second | return 0
    return y
  return x
theorem secondBranch : nestedFailure Maybe.none (Maybe.some 42) = 42 := by rfl
theorem bothMissing : nestedFailure Maybe.none Maybe.none = 0 := by rfl
"#,
    );
}

#[test]
fn invalid_branches_types_and_scopes_never_publish_partial_declarations() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : Id Nat := do\n  let Maybe.some x ← (Maybe.some 1 : Id (Maybe Nat)) | return unknown\n  return x",
        "def bad : Id Nat := do\n  let Maybe.some x ← (Maybe.none : Id (Maybe Nat)) | return 0\n  return unknown",
        "def bad : Id Nat := do\n  let Maybe.some x : Bool ← (Maybe.some 1 : Id (Maybe Nat)) | return 0\n  return x",
        "def bad : Id Nat := do\n  let Maybe.some x ← (Maybe.some 1 : Id (Maybe Nat)) | return x\n  return x",
        "def bad (value : Maybe Nat) : Id Nat := do\n  let Maybe.some x ← value |\n    let hidden := 1\n    return hidden\n  return hidden",
        "def bad : Id Nat := do\n  let _ ← (1 : Id Nat) | return unknown\n  return 42",
        "def bad : Id Nat := do\n  let (Maybe.some x) := Maybe.some 1 | return true\n  return x",
        "def bad (value : Maybe Nat) : Id Nat := do\n  let Maybe.some x ← value | break\n  return x",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    checked(&base, "def recovery : Id Nat := do return 42");
}

#[test]
fn selected_failure_and_success_branches_execute_on_golem() {
    use fln::{EngineExecutionLimits, VmExit};
    let source = r#"
def result (value : Maybe Nat) : Id Nat := do
  let Maybe.some x ← value | return 17
  return (x + 1)
#eval result Maybe.none
#eval result (Maybe.some 41)
"#;
    let run = engine()
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        run.executions.len(),
        3,
        "one function and two eval commands"
    );
    let values: Vec<_> = run.executions[1..]
        .iter()
        .map(|execution| {
            let VmExit::Returned(result) = &execution.exit else {
                panic!("native branch did not return")
            };
            fln_vm::interpreter::nat_decimal(&result.value).unwrap()
        })
        .collect();
    assert_eq!(values, ["17", "42"]);
}
