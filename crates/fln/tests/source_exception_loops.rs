//! Checked ForIn/exception dictionaries execute loop exits after cleanup, not VM jumps.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits, VmExit,
};

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
fn base() -> Engine {
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    checked(&seed, include_str!("fixtures/exception_loops/Prelude.lean"))
}
fn execute(base: &Engine, source: &str, expected: &[&str]) {
    let (defs, queries) = source.split_once("#eval").unwrap();
    let engine = checked(base, defs);
    let query = format!("#eval{queries}");
    let run = engine
        .execute_source_definitions(
            &[query.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(run.executions.len(), expected.len());
    for (execution, expected) in run.executions.iter().zip(expected) {
        let VmExit::Returned(value) = &execution.exit else {
            panic!("{:?}", execution.exit)
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(*expected)
        );
    }
}

#[test]
fn break_and_continue_cross_cleanup_with_distinct_iteration_behavior() {
    execute(
        &base(),
        r#"
def stops : Logged Nat := do
  for n in items do
    try
      note n
      break
    finally
      note 3
    note 9
  return 7
def continues : Logged Nat := do
  for n in items do
    try
      note n
      continue
    finally
      note 3
    note 9
  return 7
#eval observed stops
#eval observed continues
"#,
        &["13007", "1323007"],
    );
}

#[test]
fn conditional_exits_and_normal_completion_do_not_replay_the_suffix() {
    execute(
        &base(),
        r#"
def conditional (stop : Bool) : Logged Nat := do
  for n in items do
    try
      if stop then
        note n
        break
      else
        note 4
    finally
      note 3
    note 8
  return 7
def skipFirst : Logged Nat := do
  for n in items do
    try
      if n == 1 then
        note n
        continue
      else
        note n
    finally
      note 3
    note 8
  return 7
#eval observed (conditional true)
#eval observed (conditional false)
#eval observed skipFirst
"#,
        &["13007", "438438007", "13238007"],
    );
}

#[test]
fn handlers_can_exit_and_success_never_runs_the_handler() {
    execute(
        &base(),
        r#"
def handlerStop : Logged Nat := do
  for n in items do
    try
      note n
      (raise (4 : Nat) : Logged PUnit)
    catch e =>
      note e
      break
    finally
      note 3
    note 8
  return 7
def handlerContinue : Logged Nat := do
  for n in items do
    try
      note n
      (raise (4 : Nat) : Logged PUnit)
    catch e =>
      note e
      continue
    finally
      note 3
    note 8
  return 7
def inactive : Logged Nat := do
  for n in items do
    try
      note n
    catch e =>
      note e
      break
    finally
      note 3
    note 8
  return 7
#eval observed handlerStop
#eval observed handlerContinue
#eval observed inactive
"#,
        &["143007", "143243007", "138238007"],
    );
}

#[test]
fn nested_exception_regions_finish_all_cleanup_before_the_loop_exits() {
    execute(
        &base(),
        r#"
def nested : Logged Nat := do
  for n in items do
    try
      note n
      try
        note 4
        continue
      finally
        note 5
      note 8
    finally
      note 6
    note 9
  return 7
#eval observed nested
"#,
        &["14562456007"],
    );
}

#[test]
fn cleanup_error_overrides_a_pending_break_or_continue() {
    execute(
        &base(),
        r#"
def broken : Logged Nat := do
  for n in items do
    try
      note n
      break
    finally
      note 3
      (raise (5 : Nat) : Logged PUnit)
    note 8
  return 7
def skipped : Logged Nat := do
  for n in items do
    try
      note n
      continue
    finally
      note 3
      (raise (5 : Nat) : Logged PUnit)
    note 8
  return 7
#eval observed broken
#eval observed skipped
"#,
        &["13105", "13105"],
    );
}

#[test]
fn outside_suffix_errors_are_not_caught_by_the_completed_region() {
    execute(
        &base(),
        r#"
def outside : Logged Nat := do
  for n in items do
    try
      if n == 2 then
        break
      else
        note n
    catch e =>
      note 9
      continue
    finally
      note 3
    (raise (5 : Nat) : Logged PUnit)
  return 7
#eval observed outside
"#,
        &["13105"],
    );
}

#[test]
fn nested_loops_keep_their_own_exit_targets() {
    execute(
        &base(),
        r#"
def nestedLoops : Logged Nat := do
  for n in items do
    try
      for k in items do
        try
          note k
          break
        finally
          note 3
      note n
      continue
    finally
      note 4
    note 9
  return 7
#eval observed nestedLoops
"#,
        &["13141324007"],
    );
}

#[test]
fn invalid_exit_scopes_handlers_and_finalizers_refuse_atomically() {
    let engine = base();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for source in [
        "def bad : Logged Nat := do { try { break } finally { note 1 }; return 7 }",
        "def bad : Logged Nat := do { try { continue } catch e => { note e }; return 7 }",
        "def bad : Logged Nat := do { for n in items do { try { break; unknown } finally { note 1 } }; return 7 }",
        "def bad : Logged Nat := do { for n in items do { try { break } catch e => { unknown e } }; return 7 }",
        "def bad : Logged Nat := do { for n in items do { try { note n } finally { continue } }; return 7 }",
        "def bad : Logged Nat := do { for n in items do { try { continue } finally { note true } }; return 7 }",
    ] {
        assert!(
            engine
                .check_source_files(&[source.as_bytes()], &options, limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(engine.logical_root(&options), root);
    }
    execute(
        &engine,
        "def recovered : Logged Nat := do { for n in items do { try { break } finally { note n } }; return 7 }\n#eval observed recovered",
        &["1007"],
    );
}

#[test]
fn vm_exhaustion_is_not_a_source_exception_and_retry_is_deterministic() {
    let engine = checked(
        &base(),
        "def run : Logged Nat := do { for n in items do { try { note n; continue } catch e => { note 9; break } finally { note 3 }; note 8 }; return 7 }",
    );
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let mut small = EngineExecutionLimits::new(limits().admission.kernel);
    small.vm.max_steps = 1;
    assert!(matches!(
        engine
            .execute_source_definitions(&[b"#eval observed run"], &options, small)
            .unwrap(),
        fln::Outcome::Inconclusive(_)
    ));
    assert_eq!(engine.logical_root(&options), root);
    let run = || {
        engine
            .execute_source_definitions(
                &[b"#eval observed run"],
                &options,
                EngineExecutionLimits::new(limits().admission.kernel),
            )
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let first = run();
    let second = run();
    assert_eq!(
        first.executions[0].flbc_artifact,
        second.executions[0].flbc_artifact
    );
    assert_eq!(
        first.engine.logical_root(&options),
        second.engine.logical_root(&options)
    );
    let VmExit::Returned(value) = &second.executions[0].exit else {
        panic!("retry must complete")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("1323007")
    );
}

#[test]
fn generic_loop_and_exception_dictionaries_remain_ordinary_source_parameters() {
    checked(
        &base(),
        r#"
def generic {M : Type -> Type} [Pure M] [Bind M] [Functor M]
    [MonadExcept Nat M] [MonadFinally M] {R A : Type} [ForIn M R A]
    (xs : R) (action : A -> M PUnit) (cleanup : M PUnit) : M PUnit := do
  for x in xs do
    try
      action x
      continue
    catch e =>
      break
    finally
      cleanup
"#,
    );
}
