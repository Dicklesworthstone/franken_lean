//! Native source matches share the same checked branch and runtime pipeline.
use super::*;

const PROGRAMS: &str = r#"
def matched (flag : Bool) : State Nat := do
  match flag with
  | true =>
    let x := 1
    mark x
    mark (x + 1)
  | false =>
    mark 3
  mark 9
  return 42
theorem yesTrace : (matched true 0).state = 10209 := by rfl
theorem noTrace : (matched false 0).state = 309 := by rfl
def loopMatched : State Nat := do
  for x in items do
    match x with
    | 1 =>
      mark x
      continue
    | _ =>
      mark x
    mark (x + 10)
  mark 9
  return 42
theorem continueTrace : (loopMatched 0).state = 1021209 := by rfl
def earlyMatch (flag : Bool) : State Nat := do
  match flag with
  | true =>
    mark 1
    return 7
  | false =>
    mark 2
  mark 9
  return 42
theorem returnTrace : (earlyMatch true 0).state = 1 := by rfl
theorem returnValue : (earlyMatch true 0).value = 7 := by rfl
theorem fallTrace : (earlyMatch false 0).state = 209 := by rfl
"#;

#[test]
fn statement_match_effects_returns_and_continue_have_distinct_traces() {
    checked(&state_engine(), PROGRAMS);
}

#[test]
fn braced_arms_and_terminal_values_use_ordinary_constructor_coverage() {
    checked(
        &engine(),
        r#"
inductive Choice (A : Type) where
  | absent
  | found (value : A)
def choose (x : Choice Nat) : Id Nat := do
  match x with
  | .found n => { let m := n + 1; return m }
  | .absent => { let n <- (23 : Id Nat); return n }
theorem selected : choose (Choice.found 41) = 42 := by rfl
theorem absent : choose Choice.absent = 23 := by rfl
def termBranches (x : Bool) : Id Nat := do
  match x with
  | true => (17 : Id Nat)
  | false => (23 : Id Nat)
theorem termResult : termBranches false = 23 := by rfl
"#,
    );
}

#[test]
fn nested_compounds_and_matches_inside_branches_keep_one_control_scope() {
    checked(
        &state_engine(),
        r#"
def nested (a b : Bool) : State Nat := do
  if a then
    match b with
    | true =>
      mark 1
      return 7
    | false =>
      mark 2
  else
    mark 3
  mark 9
  return 42
theorem stopped : (nested true true 0).state = 1 := by rfl
theorem resumeInner : (nested true false 0).state = 209 := by rfl
theorem resumeOuter : (nested false false 0).state = 309 := by rfl
def innerLoop : State PUnit := do
  for x in items do
    for y in items do
      match y with
      | 1 =>
        mark (x * 10 + y)
        break
      | _ =>
        mark 99
    mark (x * 10 + 9)
theorem innerOnly : (innerLoop 0).state = 11192129 := by rfl
"#,
    );
}

#[test]
fn arm_locals_and_discriminant_proofs_cannot_capture_the_suffix() {
    checked(
        &state_engine(),
        r#"
def scoped (h : Nat) (flag : Bool) : State Nat := do
  match h : flag with
  | true =>
    let h := 1
    mark h
  | false =>
    mark 2
  mark h
  return h
theorem outerLocal : (scoped 9 true 0).state = 109 := by rfl
theorem outerValue : (scoped 9 true 0).value = 9 := by rfl
def nestedDo : State Nat := do
  match true with
  | true =>
    let n <- (do return 7)
    mark n
  | false =>
    mark 2
  mark 9
  return 42
theorem independentReturn : (nestedDo 0).state = 709 := by rfl
"#,
    );
}

#[test]
fn multiple_discriminants_nested_patterns_and_lists_use_the_existing_matrix_compiler() {
    checked(
        &engine(),
        r#"
inductive Choice (A : Type) where
  | absent
  | found (value : A)
def multi (a b : Bool) : Id Nat := do
  match a, b with
  | true, true =>
    let n := 7
    return n
  | _, _ =>
    return 9
theorem first : multi true true = 7 := by rfl
theorem other : multi true false = 9 := by rfl
def nestedPattern (x : Choice (Choice Nat)) : Id Nat := do
  match x with
  | .found (.found n) =>
    let y := n + 1
    return y
  | _ =>
    return 0
theorem nestedValue : nestedPattern (Choice.found (Choice.found 41)) = 42 := by rfl
def head (xs : List Nat) : Id Nat := do
  match xs with
  | x :: _ =>
    let y := x + 1
    return y
  | [] =>
    return 9
theorem listHead : head [41, 7] = 42 := by rfl
theorem emptyList : head [] = 9 := by rfl
"#,
    );
}

#[test]
fn abstract_monadic_action_branches_and_return_values_use_local_dictionaries() {
    checked(
        &engine(),
        r#"
def genericMatch {M : Type -> Type} [Pure M] [Bind M] (flag : Bool) (action : M PUnit) : M Nat := do
  match flag with
  | true =>
    action
    return 7
  | false =>
    action
    action
  return 42
def genericLoopMatch {M : Type -> Type} [Pure M] [Bind M] {R : Type} [ForIn M R Nat]
    (xs : R) (action : Nat -> M PUnit) : M PUnit := do
  for x in xs do
    match x with
    | 1 =>
      action x
      break
    | _ =>
      action x
      continue
"#,
    );
}

#[test]
fn incomplete_patterns_unchosen_errors_and_escaping_scopes_do_not_publish() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad (b : Bool) : Id Nat := do match b with | true => { return 7 }",
        "def bad : Id Nat := do match true with | true => { return 7 } | false => { return missing }",
        "def bad : Id Nat := do match true with | true => { return 7 } | false => { return false }",
        "def bad : Id Nat := do { match true with | true => { return 7 } | false => { return 8 }; return missing }",
        "def bad : Id Nat := do { match true with | true => { let x := 7; Pure.pure (f := Id) PUnit.unit } | false => { Pure.pure (f := Id) PUnit.unit }; return x }",
        "def bad : Id PUnit := do match true with | true => { break } | false => { Pure.pure (f := Id) PUnit.unit }",
        "def bad : Id PUnit := do match true with | true => { Pure.pure (f := Id) PUnit.unit } | false => { continue }",
        "def bad : Id PUnit := do for x in true do match true with | true => { return 7 } | false => { Pure.pure (f := Id) PUnit.unit }",
        "def bad : Id PUnit := do match true with | true => { let unused : Bool := 7; Pure.pure (f := Id) PUnit.unit } | false => { Pure.pure (f := Id) PUnit.unit }",
        "def bad : Id Nat := do match ← missing with | _ => { return 7 }",
        "def bad : Id Nat := do match ← (7 : Id Nat) with | true => { return 7 } | false => { return 9 }",
        "def bad : Id Nat := do match ← (true : Id Bool) with | true => { return 7 } | false => { return missing }",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    checked(
        &base,
        "def recovery : Id Nat := do match true with | true => { return 7 } | false => { return 9 }",
    );
}

#[test]
fn match_branch_traces_execute_on_golem() {
    let base = checked(&state_engine(), PROGRAMS);
    for (query, expected) in [
        ("#eval (matched true 0).state", "10209"),
        ("#eval (matched false 0).state", "309"),
        ("#eval (loopMatched 0).state", "1021209"),
        ("#eval (earlyMatch true 0).state", "1"),
        ("#eval (earlyMatch false 0).state", "209"),
        ("#eval (earlyMatch true 0).value", "7"),
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
            panic!("match did not return")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}

#[test]
fn a_monadic_match_runs_its_action_once_before_only_the_selected_arm() {
    let base = checked(
        &state_engine(),
        r#"
inductive Choice (A : Type) where
  | absent
  | found (value : A)
def fetch (flag : Bool) : State (Choice Nat) := fun s =>
  { value := if flag then Choice.found 7 else Choice.absent, state := s * 100 + 1 }
def run (flag : Bool) : State Nat := do
  match ← fetch flag with
  | .found n =>
    mark n
    return n
  | .absent =>
    mark 2
  mark 9
  return 42
theorem selectedTrace : (run true 0).state = 107 := by rfl
theorem fallbackTrace : (run false 0).state = 10209 := by rfl
def guarded : State PUnit := do
  for x in items do
    match <- fetch (x == 1) with
    | .found n =>
      mark n
      continue
    | .absent =>
      mark x
      break
theorem loopOrder : (guarded 0).state = 1070102 := by rfl
def generic {M : Type -> Type} [Pure M] [Bind M] (action : M (Choice Nat)) : M Nat := do
  match ← action with
  | .found n => return n
  | .absent => Pure.pure (f := M) PUnit.unit
  return 42
"#,
    );
    for (query, expected) in [
        ("#eval (run true 0).state", "107"),
        ("#eval (run false 0).state", "10209"),
        ("#eval (run true 0).value", "7"),
        ("#eval (guarded 0).state", "1070102"),
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
            panic!("monadic match did not return")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}
