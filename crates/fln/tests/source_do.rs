//! Native source do -> typeclass elaboration -> both ordinary checkers.
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
"#,
    )
}
#[test]
fn named_binds_pure_lets_and_returns_are_council_checked() {
    checked(
        &engine(),
        r#"
def work : Id Nat := do
  let a ← (7 : Id Nat)
  let b : Nat := a + 1
  return b
theorem value : work = 8 := by rfl
"#,
    );
}
#[test]
fn abstract_monads_use_local_dictionary_parameters() {
    checked(
        &engine(),
        r#"
def map {M : Type -> Type} [Pure M] [Bind M] {A B : Type} (f : A -> B) (action : M A) : M B := do
  let x ← action
  return (f x)
def seq {M : Type -> Type} [Bind M] {A B : Type} (x : M A) (y : M B) : M B := do
  x
  y
"#,
    );
}

#[test]
fn direct_dictionary_calls_are_the_same_elaboration_path() {
    checked(
        &engine(),
        r#"
def mapping {M : Type -> Type} [Pure M] [Bind M] {A B : Type} (f : A -> B) (action : M A) : M B := Bind.bind (m := M) action (fun x => Pure.pure (f x))
"#,
    );
}

#[test]
fn nested_do_and_shadowing_preserve_their_own_result_monads() {
    checked(
        &engine(),
        r#"
def nested : Id Nat := do
  let n : Nat ← do
    let n ← (7 : Id Nat)
    return (n + 1)
  let n ← (n + 2 : Id Nat)
  return n
theorem nestedValue : nested = 10 := by rfl
def privateBind (bind : Nat) : Id Nat := do
  let x ← (bind : Id Nat)
  (1 : Id Nat)
  return x
theorem scopeValue : privateBind 7 = 7 := by rfl
"#,
    );
}

#[test]
fn state_actions_are_sequential_and_run_exactly_once() {
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
def program : State Nat := do
  let x ← mark 1
  let y ← mark 2
  return (x * 100 + y)
theorem stateOrder : (program 0).state = 12 := by rfl
theorem stateValue : (program 0).value = 1 := by rfl
"#,
    );
}

#[test]
fn failing_monadic_actions_do_not_run_the_continuation() {
    checked(
        &engine(),
        r#"
inductive Maybe (A : Type) where
  | none
  | some (value : A)
def maybeBind {A B : Type} (action : Maybe A) (next : A -> Maybe B) : Maybe B :=
  match action with
  | Maybe.none => Maybe.none
  | Maybe.some value => next value
instance maybePure : Pure Maybe := { pure := fun value => Maybe.some value }
instance maybeBinder : Bind Maybe := { bind := fun action next => maybeBind action next }
def failure : Maybe Nat := do
  let x ← (Maybe.none : Maybe Nat)
  return (x + 1)
def success : Maybe Nat := do
  let x ← Maybe.some 41
  return (x + 1)
theorem failed : failure = Maybe.none := by rfl
theorem succeeded : success = Maybe.some 42 := by rfl
"#,
    );
}

#[test]
fn invalid_actions_missing_dictionaries_and_scope_escapes_preserve_the_engine() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad {M : Type -> Type} {A : Type} (x : A) : M A := do return x",
        "def bad {M : Type -> Type} [Pure M] {A : Type} (action : M A) : M A := do let x ← action; return x",
        "def bad : Id Nat := do let x ← (true : Id Bool); return x",
        "def bad : Id Nat := do let x : Bool ← (7 : Id Nat); return 0",
        "def bad : Id Nat := do let x ← x; return x",
        "def bad : Id Nat := do let n ← (do let hidden := 7; return hidden); return hidden",
        "def bad (P : Prop) : Id Nat := do let unused : P := 0; return 7",
        "def bad : Id Nat := do return 7; return 8",
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
fn ordinary_conditional_and_match_terms_remain_inside_do_actions() {
    checked(
        &engine(),
        r#"
def conditional : Id Nat := do
  let x ← ((if true then 7 else 8) : Id Nat)
  return (x + 1)
theorem conditionalValue : conditional = 8 := by rfl
def matched : Id Nat := do
  let x ← ((match true with | true => 7 | false => 8) : Id Nat)
  return (x + 1)
theorem matchedValue : matched = 8 := by rfl
"#,
    );
}

#[test]
fn do_programs_execute_through_golem() {
    use fln::{EngineExecutionLimits, VmExit};
    let source = "def runDo : Id Nat := do let x ← (17 : Id Nat); return (x + 25)\n#eval runDo";
    let result = engine()
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|e| panic!("{e:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
        panic!("not returned")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
}
