//! Pattern binds exercise parsing, inference, both checkers and native execution.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

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
instance idOfNat {A : Type} {n : Nat} [inst : OfNat A n] : OfNat (Id A) n := inst
structure Pair where
  first : Nat
  second : Nat
structure Wrapped where
  pair : Pair
"#,
    )
}

#[test]
fn constructor_patterns_destructure_monadic_results() {
    checked(
        &engine(),
        r#"
def addPair (action : Id Pair) : Id Nat := do
  let Pair.mk a b ← action
  return (a + b)
def annotated (action : Id Pair) : Id Nat := do {
  let Pair.mk a b : Pair <- action;
  return (a * 10 + b)
}
theorem added : addPair (Pair.mk 20 22) = 42 := by rfl
theorem annotatedValue : annotated (Pair.mk 4 2) = 42 := by rfl
"#,
    );
}

#[test]
fn nested_patterns_wildcards_and_shadowing_preserve_scope() {
    checked(
        &engine(),
        r#"
def nested (a : Nat) (action : Id Wrapped) : Id Nat := do
  let Wrapped.mk (Pair.mk a _) ← action
  let _ ← (a + 1 : Id Nat)
  return a
theorem nestedValue : nested 100 (Wrapped.mk (Pair.mk 42 9)) = 42 := by rfl
def fromOuter (x : Nat) : Id Nat := do
  let Pair.mk x y ← (Pair.mk x 2 : Id Pair)
  return (x + y)
theorem outerValue : fromOuter 40 = 42 := by rfl
"#,
    );
}

#[test]
fn abstract_monads_use_existing_local_bind_and_pure_dictionaries() {
    checked(
        &engine(),
        r#"
def sumAction {M : Type -> Type} [Pure M] [Bind M] (action : M Pair) : M Nat := do
  let Pair.mk a b ← action
  return (a + b)
def discard {M : Type -> Type} [Pure M] [Bind M] {A : Type} (action : M A) : M Nat := do
  let _ ← action
  return 42
"#,
    );
}

#[test]
fn state_actions_run_once_and_continuations_remain_sequential() {
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
def markPair : State Pair := fun s => { value := Pair.mk s 2, state := s * 10 + 1 }
def mark (n : Nat) : State Nat := fun s => { value := s, state := s * 10 + n }
def program : State Nat := do
  let Pair.mk x y ← markPair
  let _ ← mark y
  return x
theorem stateOrder : (program 0).state = 12 := by rfl
theorem stateValue : (program 0).value = 0 := by rfl
"#,
    );
}

#[test]
fn failed_actions_do_not_evaluate_the_pattern_continuation() {
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
def unpack (action : Maybe Pair) : Maybe Nat := do
  let Pair.mk x y ← action
  return (x + y)
theorem stopped : unpack Maybe.none = Maybe.none := by rfl
theorem succeeded : unpack (Maybe.some (Pair.mk 20 22)) = Maybe.some 42 := by rfl
"#,
    );
}

#[test]
fn invalid_patterns_and_annotations_cannot_publish_declarations() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : Id Nat := do let Pair.mk x x ← (Pair.mk 1 2 : Id Pair); return x",
        "def bad : Id Nat := do let Pair.mk x y : Bool ← (Pair.mk 1 2 : Id Pair); return x",
        "def bad : Id Nat := do let Pair.mk x y ← (7 : Id Nat); return x",
        "def bad : Id Nat := do let Pair.mk x y ← (Pair.mk 1 2 : Id Pair); return hidden",
        "def bad (flag : Bool) : Id Nat := do let (true) ← (flag : Id Bool); return 7",
        "def bad : Id Nat := do let _ : Bool ← (7 : Id Nat); return 42",
        "def bad : Id Nat := do let _ ← unknown; return 42",
        "def bad : Id Nat := do let Pair.mk x y ← (do let hidden := 7; return (Pair.mk hidden 2)); return hidden",
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
fn destructuring_runs_through_golem_not_just_syntax_expansion() {
    use fln::{EngineExecutionLimits, VmExit};
    let source = r#"
def runPattern : Id Nat := do
  let Pair.mk x y ← (Pair.mk 20 22 : Id Pair)
  return (x + y)
#eval runPattern
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
    let VmExit::Returned(result) = &run.executions.last().unwrap().exit else {
        panic!("pattern program did not return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some("42")
    );
}

#[test]
fn guarded_returns_keep_pattern_locals_out_of_the_outer_continuation() {
    checked(
        &engine(),
        r#"
def guarded (flag : Bool) (action : Id Pair) : Id Nat := do
  let Pair.mk x y ← action
  if flag then
    let Pair.mk y x ← (Pair.mk (x + 1) (y + 1) : Id Pair)
    return y
  return (x + y)
def outer (x : Nat) (flag : Bool) : Id Nat := do
  if flag then
    let Pair.mk x y ← (Pair.mk 1 2 : Id Pair)
    return (x + y)
  return x
theorem early : guarded true (Pair.mk 20 22) = 21 := by rfl
theorem fallthrough : guarded false (Pair.mk 20 22) = 42 := by rfl
theorem branchScope : outer 40 true = 3 := by rfl
theorem suffixScope : outer 40 false = 40 := by rfl
"#,
    );
}

#[test]
fn pure_destructuring_composes_with_monadic_patterns_and_shadowing() {
    checked(
        &engine(),
        r#"
def pureParts (x : Nat) : Id Nat := do
  let (Wrapped.mk (Pair.mk x y)) : Wrapped := Wrapped.mk (Pair.mk x 2)
  let _ : Nat := y
  let Pair.mk a b ← (Pair.mk x y : Id Pair)
  return (a + b)
theorem purePartsValue : pureParts 40 = 42 := by rfl
"#,
    );
}

#[test]
fn unused_pure_patterns_do_not_erase_invalid_values_or_annotations() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : Id Nat := do let _ : Bool := 7; return 42",
        "def bad : Id Nat := do let _ := unknown; return 42",
        "def bad : Id Nat := do let (Pair.mk x x) := Pair.mk 1 2; return x",
        "def bad : Id Nat := do let (Pair.mk x y) : Bool := Pair.mk 1 2; return x",
        "def bad (flag : Bool) : Id Nat := do let (true) := flag; return 42",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    checked(&base, "def recovered : Id Nat := do let _ := 7; return 42");
}

#[test]
fn dependent_field_types_survive_pure_destructuring() {
    checked(
        &engine(),
        r#"
structure Package where
  domain : Type
  value : domain
  tag : Nat
def unpackPackage (p : Package) : Id Nat := do
  let (Package.mk A value tag) := p
  let _ : A := value
  return tag
theorem packageValue : unpackPackage (Package.mk Nat 7 42) = 42 := by rfl
"#,
    );
}

#[test]
fn pure_and_monadic_patterns_compose_with_if_let_and_execute_early_returns() {
    use fln::{EngineExecutionLimits, VmExit};
    let source = r#"
inductive Choice where
  | empty
  | pair (value : Pair)
def choose (choice : Choice) : Id Nat := do
  let (Pair.mk x y) := Pair.mk 20 22
  if let Choice.pair (Pair.mk x y) := choice then
    let Pair.mk y x ← (Pair.mk y x : Id Pair)
    return (x * 10 + y)
  return (x + y)
theorem earlyPattern : choose (Choice.pair (Pair.mk 4 2)) = 42 := by rfl
theorem laterPattern : choose Choice.empty = 42 := by rfl
def runNat (x : Id Nat) : Nat := x
#eval runNat (choose (Choice.pair (Pair.mk 4 2))) + runNat (choose Choice.empty)
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
    let VmExit::Returned(result) = &run.executions.last().unwrap().exit else {
        panic!("mixed destructuring program did not return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some("84")
    );
}
