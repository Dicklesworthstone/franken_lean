//! Value-producing exception regions preserve normal values and nonlocal exits.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits, VmExit,
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
fn base() -> Engine {
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let engine = checked(&seed, include_str!("fixtures/exception_loops/Prelude.lean"));
    checked(
        &engine,
        "inductive Sum (α : Type u) (β : Type v) where | inl (val : α) | inr (val : β)",
    )
}
fn execute(engine: &Engine, source: &str, expected: &[&str]) {
    let (defs, queries) = source.split_once("#eval").unwrap();
    let engine = checked(engine, defs);
    let queries = format!("#eval{queries}");
    let run = engine
        .execute_source_definitions(
            &[queries.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .expect("complete execution");
    let found: Vec<_> = run
        .executions
        .iter()
        .map(|e| {
            let VmExit::Returned(value) = &e.exit else {
                panic!("{:?}", e.exit)
            };
            fln_vm::interpreter::nat_decimal(&value.value).expect("Nat observation")
        })
        .collect();
    assert_eq!(found, expected);
}
#[test]
fn a_terminal_exception_in_a_bound_block_preserves_normal_values_and_returns() {
    execute(
        &base(),
        include_str!("../../fln-parse/tests/fixtures/exception_value_returns.lean"),
        &["13042", "135007"],
    );
}
#[test]
fn local_returns_in_finalizer_actions_do_not_escape_the_exception_region() {
    execute(
        &base(),
        r#"
def program : Logged Nat := do
  try
    note 1
    return 42
  finally
    let action : Logged Nat := do
      return 7
    let value ← action
    note value
#eval observed program
"#,
        &["17042"],
    );
}

#[test]
fn value_handlers_distinguish_success_recovery_and_nonlocal_return() {
    execute(
        &base(),
        r#"
def choose (fail early : Bool) : Logged Nat := do
  let b : Bool ← do
    try
      note 1
      if fail then (raise (4 : Nat) : Logged Bool) else succeed true
    catch e =>
      note e
      if early then return 42 else succeed false
    finally
      note 3
  note (if b then 5 else 6)
  return 7
#eval observed (choose false true)
#eval observed (choose true false)
#eval observed (choose true true)
"#,
        &["135007", "1436007", "143042"],
    );
}

#[test]
fn outside_continuation_errors_are_not_caught_by_the_value_region() {
    execute(
        &base(),
        r#"
def choose (early : Bool) : Logged Nat := do
  let b : Bool ← do
    try
      note 1
      if early then return 42 else succeed true
    catch e =>
      note 9
      succeed false
    finally
      note 3
  note (if b then 5 else 6)
  (raise (4 : Nat) : Logged PUnit)
  return 7
#eval observed (choose true)
#eval observed (choose false)
"#,
        &["13042", "135104"],
    );
}

#[test]
fn nested_value_regions_keep_payloads_and_cleanup_order() {
    execute(
        &base(),
        r#"
def choose (early : Bool) : Logged Nat := do
  let b : Bool ← do
    try
      note 1
      let n : Nat ← do
        try
          note 2
          if early then return 42 else succeed 5
        finally
          note 3
      note n
      succeed true
    finally
      note 4
  note (if b then 6 else 7)
  return 8
#eval observed (choose true)
#eval observed (choose false)
"#,
        &["1234042", "123546008"],
    );
}

#[test]
fn cleanup_failure_overrides_both_a_value_and_an_early_return() {
    execute(
        &base(),
        r#"
def choose (early : Bool) : Logged Nat := do
  let b : Bool ← do
    try
      note 1
      if early then return 42 else succeed true
    finally
      note 3
      (raise (4 : Nat) : Logged PUnit)
  note (if b then 5 else 6)
  return 7
#eval observed (choose true)
#eval observed (choose false)
"#,
        &["13104", "13104"],
    );
}

#[test]
fn normal_types_and_return_types_remain_independent_and_checked() {
    let engine = base();
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    for source in [
        "def bad : Logged Nat := do { let b : Bool ← do { try { if true then return 42 else succeed (9 : Nat) } finally { note 3 } }; return 7 }",
        "def bad : Logged Nat := do { let b : Bool ← do { try { if true then return true else succeed false } finally { note 3 } }; return 7 }",
        "def bad : Logged Nat := do { let b : Bool ← do { try { succeed true } catch e => { if true then return true else succeed false } }; return 7 }",
        "def bad : Logged Nat := do { let b : Bool ← do { try { if true then return 42 else succeed true } finally { return 7 } }; return 7 }",
        "def bad : Logged Nat := do { let b : Bool ← do { try { let hidden := 4; if true then return 42 else succeed true } finally { note hidden } }; return 7 }",
        "def bad : Logged Nat := do { let b : Bool ← do { try { if true then return 42 else succeed true } finally { note 3 } }; note hidden; return 7 }",
    ] {
        assert!(
            engine
                .check_source_files(&[source.as_bytes()], &options, limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(engine.logical_root(&options), before);
    }
    execute(
        &engine,
        "def recovered : Logged Nat := do { let b : Bool ← do { try { if true then return 42 else succeed true } finally { note 3 } }; return 7 }\n#eval observed recovered",
        &["3042"],
    );
}

#[test]
fn generic_value_regions_require_only_the_existing_dictionaries() {
    checked(
        &base(),
        r#"
def genericValue {M : Type -> Type} [Pure M] [Bind M] [Functor M]
    [MonadExcept Nat M] [MonadFinally M] {A B : Type}
    (action : M A) (cleanup : M PUnit) (consume : A -> M B)
    (early : Bool) (value : B) : M B := do
  let a : A ← do
    try
      if early then return value else action
    finally
      cleanup
  consume a
"#,
    );
}
