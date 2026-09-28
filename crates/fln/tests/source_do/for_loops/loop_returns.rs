//! Nonlocal returns use ordinary source dictionaries, both checkers and Golem.
use super::*;

#[test]
fn loop_returns_skip_later_iterations_and_the_enclosing_suffix() {
    checked(
        &state_engine(),
        r#"
def search (stop : Nat) : State Nat := do
  mark 8
  for x in items do
    mark x
    if x == stop then
      return (x + 40)
    mark 7
  mark 9
  return 0
theorem first : (search 1 0).value = 41 := by rfl
theorem firstEffects : (search 1 0).state = 801 := by rfl
theorem second : (search 2 0).value = 42 := by rfl
theorem secondEffects : (search 2 0).state = 8010702 := by rfl
theorem absent : (search 3 0).value = 0 := by rfl
theorem absentEffects : (search 3 0).state = 80107020709 := by rfl
"#,
    );
}

#[test]
fn nested_returns_propagate_but_break_and_continue_keep_their_own_scope() {
    checked(
        &state_engine(),
        r#"
def nested (stop : Nat) : State Nat := do
  for x in items do
    for y in items do
      mark (x * 10 + y)
      if y == 1 then continue
      if x == stop then return (x * 10 + y)
      break
    mark 9
  mark 8
  return 0
theorem first : (nested 1 0).value = 12 := by rfl
theorem firstEffects : (nested 1 0).state = 1112 := by rfl
theorem second : (nested 2 0).value = 22 := by rfl
theorem secondEffects : (nested 2 0).state = 1112092122 := by rfl
theorem absent : (nested 3 0).value = 0 := by rfl
"#,
    );
}

#[test]
fn abstract_result_types_and_monads_keep_expected_type_information() {
    checked(
        &engine(),
        r#"
def find {M : Type -> Type} [Pure M] [Bind M] {R A B : Type} [ForIn M R A]
    (xs : R) (stop : A -> Bool) (value : A -> B) (fallback : B) : M B := do
  for x in xs do
    if stop x then return (value x)
  return fallback
structure Answer where
  value : Nat
def named : Id Answer := do
  for x in true do return { value := x }
  return { value := 0 }
theorem constructorExpected : named.value = 42 := by rfl
"#,
    );
}

#[test]
fn empty_loops_and_nested_do_expressions_have_distinct_return_scopes() {
    checked(
        &engine(),
        r#"
def empty : Id Nat := do
  for x in false do return x
  return 9
theorem emptyValue : empty = 9 := by rfl
def separate : Id Nat := do
  for x in true do
    let value <- do
      if true then return (x + 1)
      return x
    Pure.pure (f := Id) PUnit.unit
  return 7
theorem separateValue : separate = 7 := by rfl
"#,
    );
}

#[test]
fn pattern_and_match_arms_return_through_loops_without_capturing_the_suffix() {
    checked(
        &state_engine(),
        r#"
def patterns (x : Nat) (stop : Bool) : State Nat := do
  for y in items do
    match (if stop then Option.some y else Option.none) with
    | .some x =>
      unless x == 1 do
        let value <- Pure.pure (f := State) (x + 40)
        mark x
        return value
    | .none =>
      mark y
  mark x
  return x
theorem early : (patterns 9 true 0).value = 42 := by rfl
theorem earlyEffects : (patterns 9 true 0).state = 2 := by rfl
theorem normal : (patterns 9 false 0).value = 9 := by rfl
theorem normalEffects : (patterns 9 false 0).state = 10209 := by rfl
def guard : State Nat := do
  for x in items do
    if let .some n <- Pure.pure (f := State) (Option.some x) then
      if n == 2 then return n
  return 0
theorem guardValue : (guard 0).value = 2 := by rfl
"#,
    );
}

#[test]
fn returning_bool_function_and_list_values_preserves_the_outer_result_type() {
    checked(
        &engine(),
        r#"
def boolResult : Id Bool := do
  for x in true do return false
  return true
theorem boolValue : boolResult = false := by rfl
def functionResult : Id (Nat -> Nat) := do
  for x in true do return (fun y => x + y)
  return (fun y => y)
theorem functionValue : functionResult 3 = 45 := by rfl
def listResult : Id (List Nat) := do
  for x in true do return [x]
  return []
theorem listValue : listResult = [42] := by rfl
"#,
    );
}

#[test]
fn terminal_unit_loops_return_and_no_return_paths_have_a_checked_unit_default() {
    checked(
        &engine(),
        r#"
def unitResult : Id PUnit := do
  for x in true do return PUnit.unit
theorem unitValue : unitResult = PUnit.unit := by rfl
def emptyUnit : Id PUnit := do
  for x in false do return PUnit.unit
theorem emptyUnitValue : emptyUnit = PUnit.unit := by rfl
"#,
    );
}

#[test]
fn shadowed_library_names_and_proof_binders_do_not_capture_generated_control() {
    checked(
        &state_engine(),
        r#"
namespace ShadowReturn
def Option.none : Nat := 0
def Option.some : Nat := 0
def ForInStep.done : Nat := 0
def value (h : Nat) (stop : Bool) : State Nat := do
  for x in items do
    if h : stop = true then return x
  return h
theorem early : (value 9 true 0).value = 1 := by rfl
theorem normal : (value 9 false 0).value = 9 := by rfl
end ShadowReturn
"#,
    );
}

#[test]
fn invalid_unchosen_returns_and_skipped_suffixes_never_publish() {
    let base = state_engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : State Nat := do { for x in items do { return true }; return 0 }",
        "def bad : State Nat := do { for x in items do { if false then return missing }; return 0 }",
        "def bad : State Nat := do { for x in items do { return 7 }; let hidden : Bool := 7; return 0 }",
        "def bad : State Nat := do { for x in items do { return 7 }; return x }",
        "def bad : State Nat := do { for x in items do { return 7 }; missing; return 0 }",
        "def bad : State Nat := do { for x in items do { for y in items do { return 7 }; missing }; return 0 }",
        "def bad : State Nat := do { for x in items do { if false then { return 7 }; (do break) }; return 0 }",
        "def bad : State Nat := do { for x in items do { return 7 } }",
    ] {
        fln_parse::parse_definition(source.as_bytes())
            .unwrap_or_else(|e| panic!("negative must reach elaboration: {source}: {e:?}"));
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    checked(
        &base,
        "def recovery : State Nat := do { for x in items do { return 7 }; return 0 }",
    );
}

#[test]
fn nonlocal_return_values_and_effects_execute_through_golem() {
    let base = checked(
        &state_engine(),
        r#"
def execute (stop : Nat) : State Nat := do
  for x in items do
    for y in items do
      mark (x * 10 + y)
      if x == stop then
        if y == 2 then return (x * 10 + y)
    mark 9
  mark 8
  return 0
"#,
    );
    for (query, expected) in [
        ("#eval (execute 1 0).value", "12"),
        ("#eval (execute 1 0).state", "1112"),
        ("#eval (execute 2 0).value", "22"),
        ("#eval (execute 2 0).state", "1112092122"),
        ("#eval (execute 3 0).value", "0"),
        ("#eval (execute 3 0).state", "11120921220908"),
    ] {
        let run = base
            .execute_source_definitions(
                &[query.as_bytes()],
                &KVMap::new(),
                EngineExecutionLimits::new(limits().admission.kernel),
            )
            .unwrap_or_else(|e| panic!("{query}: {e:?}"))
            .into_complete()
            .unwrap();
        let VmExit::Returned(result) = &run.executions.last().unwrap().exit else {
            panic!("loop did not return")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
            Some(expected),
            "{query}"
        );
    }
}

#[test]
fn failed_monadic_actions_are_not_confused_with_returning_an_option_value() {
    checked(
        &engine(),
        r#"
def optionBind {A B : Type} (action : Option A) (next : A -> Option B) : Option B :=
  match action with
  | .none => Option.none
  | .some value => next value
instance optionPure : Pure Option := { pure := fun value => Option.some value }
instance optionBinder : Bind Option := { bind := fun action next => optionBind action next }
def boolOptionFor {B : Type} (xs : Bool) (b : B) (f : Nat -> B -> Option (ForInStep B)) : Option B :=
  if xs then optionBind (f 42 b) (fun step => Option.some (stepValue step)) else Option.some b
instance optionIteration : ForIn Option Bool Nat := { forIn := fun xs b f => boolOptionFor xs b f }
def failed : Option Nat := do
  for x in true do
    let y : Nat <- Option.none
    return y
  return 9
theorem failureValue : failed = Option.none := by rfl
def nestedOption : Id (Option Nat) := do
  for x in true do return Option.none
  return (Option.some 9)
theorem returnedNone : nestedOption = Option.none := by rfl
"#,
    );
}

#[test]
fn membership_evidence_survives_a_dependent_return_from_the_callback() {
    checked(
        &engine(),
        r#"
class Membership (A R : Type) where
  mem : R -> A -> Prop
class ForIn' (m : Type -> Type) (R : Type) (A : outParam Type) (d : outParam (Membership A R)) where
  forIn' : {B : Type} -> (xs : R) -> B -> ((a : A) -> @Membership.mem A R d xs a -> B -> m (ForInStep B)) -> m B
instance memberNat : Membership Nat Nat := { mem := fun xs a => a = xs }
def natFor {B : Type} (xs : Nat) (b : B) (f : (a : Nat) -> a = xs -> B -> Id (ForInStep B)) : Id B :=
  stepValue (f xs (by rfl) b)
instance natIteration : ForIn' Id Nat Nat memberNat := { forIn' := fun xs b f => natFor xs b f }
structure Found (n : Nat) where
  value : Nat
  evidence : value = n
def witnessed (n : Nat) : Id (Found n) := do
  for h : x in n do return { value := x, evidence := h }
  return { value := n, evidence := by rfl }
theorem witnessValue : (witnessed 7).value = 7 := by rfl
"#,
    );
}

#[test]
fn formerly_unsupported_well_typed_loop_returns_now_have_positive_coverage() {
    checked(
        &engine(),
        r#"
def terminal : Id PUnit := do for x in true do return PUnit.unit
def conditional : Id PUnit := do for x in true do { if false then { return PUnit.unit }; Pure.pure (f := Id) PUnit.unit }
def matched : Id PUnit := do for x in true do match true with | true => { return PUnit.unit } | false => { Pure.pure (f := Id) PUnit.unit }
"#,
    );
    checked(
        &state_engine(),
        r#"
def conditional : State PUnit := do for x in items do if true then return PUnit.unit else mark x
def early : State Nat := do { for x in items do { if true then { return 7 } }; return 9 }
theorem value : (early 0).value = 7 := by rfl
"#,
    );
}

#[test]
fn return_accumulators_do_not_raise_the_monads_input_universe() {
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    checked(
        &seed,
        r#"
universe u v w
class Pure (f : Type u -> Type v) where
  pure : {A : Type u} -> A -> f A
class Bind (m : Type u -> Type v) where
  bind : {A B : Type u} -> m A -> (A -> m B) -> m B
inductive PUnit : Type where
  | unit
inductive ForInStep (A : Type u) where
  | done (value : A)
  | yield (value : A)
class ForIn (m : Type u -> Type v) (R : Type w) (A : outParam (Type w)) where
  forIn : {B : Type u} -> R -> B -> (A -> B -> m (ForInStep B)) -> m B
def find {M : Type u -> Type v} [Pure M] [Bind M] {R A : Type w} [ForIn M R A] {B : Type u}
    (xs : R) (stop : A -> Bool) (value : A -> B) (fallback : B) : M B := do
  for x in xs do
    if stop x then return (value x)
  return fallback
"#,
    );
}
