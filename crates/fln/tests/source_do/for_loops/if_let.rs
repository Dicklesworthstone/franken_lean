//! Real pattern conditions pass source checking, both council seats, and Golem.
use super::*;

fn library() -> Engine {
    checked(
        &state_engine(),
        r#"
inductive Choice (A : Type) where
  | missing
  | found (value : A)
def fetch (flag : Bool) : State (Choice Nat) := fun s =>
  { value := if flag then Choice.found 7 else Choice.missing, state := s * 100 + 1 }
"#,
    )
}

#[test]
fn constructor_patterns_choose_branches_and_support_guarded_early_returns() {
    checked(
        &library(),
        r#"
def choose (item : Choice Nat) : Id Nat := do
  if let Choice.found x := item then
    return x
  return 9
theorem found : choose (Choice.found 7) = 7 := by rfl
theorem missing : choose Choice.missing = 9 := by rfl
def nested (item : Choice (Choice Nat)) : Id Nat := do
  if let Choice.found (Choice.found x) := item then return x
  return 9
theorem nestedFound : nested (Choice.found (Choice.found 42)) = 42 := by rfl
theorem nestedMissing : nested (Choice.found Choice.missing) = 9 := by rfl
theorem outerMissing : nested Choice.missing = 9 := by rfl
"#,
    );
}

const EFFECTS: &str = r#"
def run (flag : Bool) : State Nat := do
  if let Choice.found n <- fetch flag then
    mark n
  else
    mark 3
  mark 9
  return 42
theorem foundEffects : (run true 0).state = 10709 := by rfl
theorem missingEffects : (run false 0).state = 10309 := by rfl
def early (flag : Bool) : State Nat := do
  if let .found n ← fetch flag then
    mark n
    return n
  mark 9
  return 42
theorem earlyEffects : (early true 0).state = 107 := by rfl
theorem fallthroughEffects : (early false 0).state = 109 := by rfl
theorem earlyValue : (early true 0).value = 7 := by rfl
"#;

#[test]
fn monadic_patterns_evaluate_the_action_once_and_preserve_return_scope() {
    checked(&library(), EFFECTS);
}

#[test]
fn generic_patterns_use_existing_local_monad_dictionaries() {
    checked(
        &library(),
        r#"
def chooseGeneric {M : Type -> Type} [Pure M] {A : Type}
    (item : Choice A) (fallback : A) : M A := do
  if let .found x := item then return x
  return fallback
def fetchGeneric {M : Type -> Type} [Pure M] [Bind M] {A : Type}
    (action : M (Choice A)) (fallback : A) : M A := do
  if let .found x <- action then return x
  return fallback
"#,
    );
}

#[test]
fn pattern_bound_variables_cannot_capture_else_or_the_shared_continuation() {
    checked(
        &library(),
        r#"
def scope (x : Nat) (item : Choice Nat) : State Nat := do
  if let .found x := item then mark x else mark x
  mark x
  return x
theorem yesScope : (scope 9 (Choice.found 7) 0).state = 709 := by rfl
theorem noScope : (scope 9 Choice.missing 0).state = 909 := by rfl
theorem outerScope : (scope 9 (Choice.found 7) 0).value = 9 := by rfl
"#,
    );
}

#[test]
fn pattern_guards_forward_continue_and_break_to_the_current_loop() {
    checked(
        &library(),
        r#"
def pick (n : Nat) : Choice Nat := if n == 1 then Choice.found 7 else Choice.missing
def skipping : State Nat := do
  for x in items do
    if let .found y := pick x then
      mark y
      continue
    mark x
  return 42
theorem skipEffects : (skipping 0).state = 702 := by rfl
def stopping : State Nat := do
  for x in items do
    if let .found y := pick x then
      mark y
      break
    mark x
  mark 9
  return 42
theorem stopEffects : (stopping 0).state = 709 := by rfl
"#,
    );
}

#[test]
fn numeric_and_collection_patterns_use_the_same_checked_matrix_compiler() {
    checked(
        &library(),
        r#"
def zero (n : Nat) : Id Nat := do
  if let 0 := n then return 7
  return 9
theorem zeroValue : zero 0 = 7 := by rfl
theorem successorValue : zero 3 = 9 := by rfl
def head (xs : List Nat) : Id Nat := do
  if let x :: _ := xs then return x
  return 9
theorem headValue : head [7, 8] = 7 := by rfl
theorem emptyValue : head [] = 9 := by rfl
"#,
    );
}

#[test]
fn both_arms_and_skipped_continuations_still_need_valid_types() {
    let base = library();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : Id Nat := do { if let .found x := (Choice.missing : Choice Nat) then { return missingName }; return 9 }",
        "def bad : Id Nat := do { if let .found x := Choice.found 7 then return x else return missingName }",
        "def bad : Id Nat := do { if let .found x := Choice.found 7 then { return x }; return x }",
        "def bad : Id Nat := do { if let .found x := Choice.found 7 then { return true }; return 9 }",
        "def bad : Id Nat := do { if let .found x := Choice.found 7 then { return x } else { return 9 }; let bad : Bool := 7; return 4 }",
        "def bad : State Nat := do { if let .found x <- (7 : State Nat) then { return x }; return 9 }",
    ] {
        fln_parse::parse_definition(source.as_bytes())
            .unwrap_or_else(|e| panic!("parse {source}: {e:?}"));
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    checked(
        &base,
        "def recovery : Id Nat := do { if let .found x := Choice.found 7 then { return x }; return 9 }",
    );
}

#[test]
fn pattern_conditions_execute_on_golem_without_new_runtime_instructions() {
    let base = checked(&library(), EFFECTS);
    for (query, expected) in [
        ("#eval (run true 0).state", "10709"),
        ("#eval (run false 0).state", "10309"),
        ("#eval (early true 0).state", "107"),
        ("#eval (early false 0).state", "109"),
        ("#eval (early true 0).value", "7"),
    ] {
        let result = base
            .execute_source_definitions(
                &[query.as_bytes()],
                &KVMap::new(),
                EngineExecutionLimits::new(limits().admission.kernel),
            )
            .unwrap_or_else(|e| panic!("{query}: {e:?}"))
            .into_complete()
            .unwrap();
        let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
            panic!("pattern condition did not return")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}

#[test]
fn monadic_pattern_guards_inside_nested_blocks_keep_loop_control_and_effect_order() {
    let source = r#"
def visit : State Nat := do
  for x in items do
    if let .found y <- fetch (x == 1) then
      unless false do
        mark y
        continue
    mark x
  mark 9
  return 42
theorem effects : (visit 0).state = 107010209 := by rfl
#eval (visit 0).state
"#;
    let result = library()
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|error| panic!("{error:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
        panic!("monadic loop guard did not return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("107010209")
    );
}
