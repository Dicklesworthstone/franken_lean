//! Dependent iteration uses ordinary source classes and both admission seats.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits, VmExit};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)))
}
fn checked(base: &Engine, text: &str) -> Engine {
    base.check_source_files(&[text.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{text}\n{e:?}"))
        .into_complete().unwrap().engine
}
fn engine() -> Engine {
    let seed = Engine::with_source_seed(limits().admission).unwrap().into_complete().unwrap();
    checked(&seed, r#"
class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
def Id (A : Type) : Type := A
instance idPure : Pure Id := { pure := fun a => a }
instance idBind : Bind Id := { bind := fun a k => k a }
inductive PUnit : Type where
  | unit
inductive ForInStep (A : Type) where
  | done (value : A)
  | yield (value : A)
class Membership (A R : Type) where
  mem : R -> A -> Prop
class ForIn' (m : Type -> Type) (R : Type) (A : outParam Type) (d : outParam (Membership A R)) where
  forIn' : {B : Type} -> (xs : R) -> B -> ((a : A) -> @Membership.mem A R d xs a -> B -> m (ForInStep B)) -> m B
def stepValue {A : Type} (step : ForInStep A) : A :=
  match step with
  | ForInStep.done value => value
  | ForInStep.yield value => value
instance memberNat : Membership Nat Nat := { mem := fun xs a => a = xs }
def natFor {B : Type} (xs : Nat) (b : B) (f : (a : Nat) -> a = xs -> B -> Id (ForInStep B)) : Id B :=
  stepValue (f xs (by rfl) b)
instance natIteration : ForIn' Id Nat Nat memberNat := { forIn' := fun xs b f => natFor xs b f }
def checkWitness (xs x : Nat) (h : x = xs) : Id PUnit := PUnit.unit
"#)
}

#[test]
fn actual_membership_proof_is_usable_inside_the_loop_and_does_not_escape() {
    checked(&engine(), r#"
def visit (n : Nat) : Id Nat := do
  for h : x in n do
    checkWitness n x h
  return n
theorem value : visit 42 = 42 := by rfl
def shadow (h : Nat) : Id Nat := do
  for h : x in 7 do
    checkWitness 7 x h
  return h
theorem outerScope : shadow 9 = 9 := by rfl
"#);
}

#[test]
fn arbitrary_collection_predicates_come_from_the_local_dictionary() {
    checked(&engine(), r#"
def dependentVisit {M : Type -> Type} [Pure M] [Bind M] {R A : Type}
    (d : Membership A R) [ForIn' M R A d] (xs : R)
    (action : (x : A) -> @Membership.mem A R d xs x -> M PUnit) : M PUnit := do
  for h : x in xs do
    action x h
"#);
}

#[test]
fn wildcard_and_nested_dependent_loops_keep_fresh_element_and_witness_scopes() {
    checked(&engine(), r#"
def ignored : Id Nat := do
  for h : _ in 7 do break
  return 42
theorem ignoredValue : ignored = 42 := by rfl
def nested : Id PUnit := do
  for hx : x in 7 do
    for hy : y in x do
      checkWitness 7 x hx
      checkWitness x y hy
      continue
"#);
}

#[test]
fn namespace_shadowing_cannot_redirect_the_generated_dependent_operation() {
    checked(&engine(), r#"
namespace ShadowIteration
def ForIn'.forIn' : Nat := 0
def ForInStep.done : Nat := 0
def run : Id Nat := do
  for h : x in 7 do
    checkWitness 7 x h
    break
  return 19
theorem value : run = 19 := by rfl
end ShadowIteration
"#);
}

#[test]
fn invalid_witnesses_and_missing_dependent_dictionaries_leave_the_engine_unchanged() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : Id PUnit := do for h : x in 7 do checkWitness 8 x h",
        "def bad : Id Nat := do { for h : x in 7 do { break }; return x }",
        "def bad : Id Nat := do { for h : x in 7 do { break }; return h }",
        "def bad : Id PUnit := do for h : x in true do Pure.pure (f := Id) PUnit.unit",
        "def bad : Id PUnit := do for h : x in h do checkWitness 7 x h",
        "def bad : Id PUnit := do for _ : x in 7 do break",
        "def bad : Id PUnit := do for h : x in 7 do return PUnit.unit",
    ] {
        assert!(base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits()).is_err(), "{source}");
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    checked(&base, "def recovery : Id PUnit := do for h : x in 7 do checkWitness 7 x h");
}

#[test]
fn dependent_iteration_executes_after_proof_erasure_on_golem() {
    let source = r#"
structure Result (A : Type) where
  value : A
  state : Nat
def State (A : Type) : Type := Nat -> Result A
instance statePure : Pure State := { pure := fun value state => { value := value, state := state } }
def stateNext {A B : Type} (r : Result A) (next : A -> State B) : Result B := next r.value r.state
instance stateBind : Bind State := { bind := fun action next state => stateNext (action state) next }
def natForState {B : Type} (xs : Nat) (b : B) (f : (a : Nat) -> a = xs -> B -> State (ForInStep B)) : State B :=
  Bind.bind (m := State) (f xs (by rfl) b) (fun step => Pure.pure (f := State) (stepValue step))
instance natStateIteration : ForIn' State Nat Nat memberNat := { forIn' := fun xs b f => natForState xs b f }
def markWitness (xs x : Nat) (h : x = xs) : State PUnit := fun s => { value := PUnit.unit, state := s * 10 + x }
def run : State Nat := do
  for h : x in 7 do
    markWitness 7 x h
    continue
  return 42
#eval (run 3).state
"#;
    let result = engine().execute_source_definitions(
        &[source.as_bytes()], &KVMap::new(), EngineExecutionLimits::new(limits().admission.kernel),
    ).unwrap_or_else(|e| panic!("{e:?}")).into_complete().unwrap();
    let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
        panic!("dependent loop did not return")
    };
    assert_eq!(fln_vm::interpreter::nat_decimal(&value.value).as_deref(), Some("37"));
}

mod unless_tests;
