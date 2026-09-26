//! Real source -> class inference -> declaration council -> Golem regressions.
//! The miniature libraries are ordinary source declarations, not trusted fixtures.
use super::{checked, limits};
use fln::{Engine, EngineExecutionLimits, KVMap, VmExit};

fn engine() -> Engine {
    checked(
        &super::engine(),
        r#"
inductive PUnit : Type where
  | unit
inductive ForInStep (A : Type) where
  | done (value : A)
  | yield (value : A)
class ForIn (m : Type -> Type) (R : Type) (A : outParam Type) where
  forIn : {B : Type} -> R -> B -> (A -> B -> m (ForInStep B)) -> m B
def stepValue {A : Type} (step : ForInStep A) : A :=
  match step with
  | ForInStep.done value => value
  | ForInStep.yield value => value
def boolFor {B : Type} (xs : Bool) (b : B) (f : Nat -> B -> Id (ForInStep B)) : Id B :=
  if xs then stepValue (f 42 b) else b
instance idBoolFor : ForIn Id Bool Nat := { forIn := fun xs b f => boolFor xs b f }
"#,
    )
}

fn state_engine() -> Engine {
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
structure Two where
  first : Nat
  second : Nat
def finishTwo {B : Type} (n : Nat) (f : Nat -> B -> State (ForInStep B)) (step : ForInStep B) : State B :=
  match step with
  | ForInStep.done value => Pure.pure (f := State) value
  | ForInStep.yield value => Bind.bind (m := State) (f n value) (fun last => Pure.pure (f := State) (stepValue last))
def forTwo {B : Type} (xs : Two) (b : B) (f : Nat -> B -> State (ForInStep B)) : State B :=
  Bind.bind (m := State) (f xs.first b) (fun step => finishTwo xs.second f step)
instance stateTwoFor : ForIn State Two Nat := { forIn := fun xs b f => forTwo xs b f }
def items : Two := { first := 1, second := 2 }
def mark (n : Nat) : State PUnit := fun s => { value := PUnit.unit, state := s * 100 + n }
"#,
    )
}

#[test]
fn abstract_collections_and_monads_use_local_dictionaries() {
    checked(
        &engine(),
        r#"
def visit {M : Type -> Type} [Pure M] [Bind M] {R A : Type} [ForIn M R A] (xs : R) (action : A -> M PUnit) : M PUnit := do
  for x in xs do
    action x
def followed {M : Type -> Type} [Pure M] [Bind M] {R A : Type} [ForIn M R A] (xs : R) (action : A -> M PUnit) : M Nat := do
  for x in xs do { action x }
  return 17
"#,
    );
}

#[test]
fn identity_alias_empty_iteration_and_namespace_shadowing_are_checked() {
    checked(
        &engine(),
        r#"
def identityLoop : Id PUnit := do
  for x in true do
    Pure.pure (f := Id) PUnit.unit
theorem identityValue : identityLoop = PUnit.unit := by rfl
def emptyLoop : Id Nat := do
  for x in false do { Pure.pure (f := Id) PUnit.unit }
  return 17
theorem emptyValue : emptyLoop = 17 := by rfl
namespace Shadow
def ForIn.forIn : Nat := 0
def ForInStep.yield : Nat := 0
def PUnit : Type := Nat
def value (x : Nat) : Id Nat := do
  for x in true do { Pure.pure (f := Id) _root_.PUnit.unit }
  return x
theorem outerScope : value 9 = 9 := by rfl
end Shadow
"#,
    );
}

#[test]
fn state_effects_are_ordered_once_and_loop_binders_do_not_escape() {
    checked(
        &state_engine(),
        r#"
def walk (x : Nat) : State Nat := do
  for x in items do
    let y := x
    mark y
  return x
theorem order : (walk 9 0).state = 102 := by rfl
theorem outerValue : (walk 9 0).value = 9 := by rfl
def nestedWalk : State PUnit := do
  for x in items do
    for y in items do
      mark (x * 10 + y)
theorem nestedOrder : (nestedWalk 0).state = 11122122 := by rfl
"#,
    );
}

#[test]
fn invalid_actions_dictionaries_and_nonlocal_returns_leave_engine_unchanged() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : Id PUnit := do for x in true do (7 : Id Nat)",
        "def bad : Id PUnit := do for x in 7 do Pure.pure (f := Id) PUnit.unit",
        "def bad {M : Type -> Type} [Pure M] [Bind M] (action : Nat -> M PUnit) : M PUnit := do for x in true do action x",
        "def bad : Id PUnit := do for x in true do return PUnit.unit",
        "def bad : Id Nat := do for x in true do { Pure.pure (f := Id) PUnit.unit }; return x",
        "def bad : Id PUnit := do for x in false do unknownAction x",
        "def bad : Id PUnit := do for h : x in true do Pure.pure (f := Id) PUnit.unit",
        "def bad : Id PUnit := do for x in true, y in true do Pure.pure (f := Id) PUnit.unit",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    checked(&base, "def recovery : Id PUnit := do for x in true do Pure.pure (f := Id) PUnit.unit");
}

#[test]
fn source_for_loops_execute_through_golem_without_a_new_runtime_primitive() {
    let source = r#"
def run : State Nat := do
  for x in items do
    mark x
  return 7
#eval (run 0).state
"#;
    let result = state_engine()
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|e| panic!("{e:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
        panic!("for loop did not return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("102")
    );
}
