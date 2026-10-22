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
fn bare_nested_loop_blocks_forward_exits_without_running_the_outer_suffix() {
    execute(
        &base(),
        r#"
def nestedStop : Logged Nat := do
  for n in items do
    do
      note n
      break
    note 9
  return 7
def nestedContinue : Logged Nat := do
  for n in items do
    do
      note n
      continue
    note 9
  return 7
def nestedFallthrough : Logged Nat := do
  for n in items do
    do
      note n
    note 9
  return 7
#eval observed nestedStop
#eval observed nestedContinue
#eval observed nestedFallthrough
"#,
        &["1007", "12007", "1929007"],
    );
}

#[test]
fn nested_loop_blocks_keep_cleanup_order_and_the_outer_lexical_scope() {
    execute(
        &base(),
        r#"
def nestedCleanup (stop : Bool) : Logged Nat := do
  for n in items do
    try
      do
        note n
        do
          if stop then break else continue
    finally
      note 3
    note 9
  return 7
def nestedScope : Logged Nat := do
  for n in items do
    do
      let n := 4
      note n
    note n
  return 7
#eval observed (nestedCleanup true)
#eval observed (nestedCleanup false)
#eval observed nestedScope
"#,
        // Bare `do` shares the surrounding lexical scope at the pin. Both
        // uses in each iteration therefore see the inner `n := 4`.
        &["13007", "1323007", "4444007"],
    );
}

#[test]
fn nested_cleanup_blocks_preserve_typing_and_term_do_scope_boundaries() {
    let engine = base();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for source in [
        // A discarded loop action still has to return Unit.
        "def bad : Logged Nat := do { for n in items do { try { do { mark n } } finally { note 3 }; note 9 }; return 7 }",
        // Parenthesized term-do owns a distinct loop scope.
        "def bad : Logged Nat := do { for n in items do { try { (do { break } : Logged PUnit) } finally { note 3 } }; return 7 }",
        // Dead branches are not permission to skip type checking.
        "def bad : Logged Nat := do { for n in items do { try { do { if false then note true else continue } } finally { note 3 } }; return 7 }",
        // A parenthesized term-do has its own lexical scope. Bare statement
        // `do` deliberately shares the surrounding continuation instead.
        "def bad : Logged Nat := do { for n in items do { try { (do { let hidden := n; note hidden } : Logged PUnit); note hidden } finally { note 3 } }; return 7 }",
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
        "def recovered : Logged Nat := do { for n in items do { try { do { note n; continue } } finally { note 3 }; note 9 }; return 7 }\n\
         def sharedScope : Logged Nat := do { for n in items do { try { do { let hidden := n; note hidden }; note hidden } finally { note 3 } }; return 7 }\n\
         #eval observed recovered\n#eval observed sharedScope",
        &["1323007", "113223007"],
    );
}

#[test]
fn nested_value_bindings_inside_cleanup_keep_typed_values_and_loop_exits() {
    execute(
        &base(),
        r#"
def boundContinue (early : Bool) : Logged Nat := do
  for n in items do
    try
      let b : Bool ← do
        note n
        if early then continue
        succeed false
      note (if b then 5 else 6)
    finally
      note 3
    note 9
  return 7
def boundStop : Logged Nat := do
  for n in items do
    try
      let value : Nat ← do
        note n
        if n == 1 then break
        succeed 4
      note value
    finally
      note 3
    note 9
  return 7
#eval observed (boundContinue true)
#eval observed (boundContinue false)
#eval observed boundStop
"#,
        &["1323007", "16392639007", "13007"],
    );
}

#[test]
fn terminal_value_branches_and_nested_bindings_share_the_right_completion() {
    execute(
        &base(),
        r#"
def tailChoice (early : Bool) : Logged Nat := do
  for n in items do
    try
      let value : Nat ← do
        note n
        if early then continue else succeed (n + 4)
      note value
    finally
      note 3
    note 9
  return 7
def tailMatch : Logged Nat := do
  for n in items do
    try
      let value : Nat ← do
        note n
        match n with
        | Nat.zero => continue
        | Nat.succ k => succeed (k + 4)
      note value
    finally
      note 3
    note 9
  return 7
def nestedValues : Logged Nat := do
  for n in items do
    try
      let n : Nat ← do
        note n
        let value : Bool ← do
          if n == 1 then continue else succeed true
        if value then succeed 4 else succeed 5
      note n
    finally
      note 3
    note 9
  return 7
#eval observed (tailChoice true)
#eval observed (tailChoice false)
#eval observed tailMatch
#eval observed nestedValues
"#,
        &["1323007", "15392639007", "14392539007", "132439007"],
    );
}

#[test]
fn bound_actions_in_handlers_keep_nonlocal_returns_and_cleanup_effects() {
    execute(
        &base(),
        r#"
def boundReturn (early : Bool) : Logged Nat := do
  for n in items do
    try
      let value : Bool ← do
        note n
        if early then return 42 else succeed true
      note (if value then 5 else 6)
    finally
      note 3
    note 9
  return 7
def handlerValue : Logged Nat := do
  for n in items do
    try
      note n
      (raise (4 : Nat) : Logged PUnit)
    catch e =>
      let value ← do
        note e
        if n == 1 then continue
        succeed 5
      note value
    finally
      note 3
    note 9
  return 7
#eval observed (boundReturn true)
#eval observed (boundReturn false)
#eval observed handlerValue
"#,
        &["13042", "15392539007", "14324539007"],
    );
}

#[test]
fn nested_value_refusals_keep_annotations_types_and_lexical_boundaries() {
    let engine = base();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for source in [
        // Binding an action's result cannot erase its declared carrier.
        "def bad : Logged Nat := do { for n in items do { try { let b : Bool ← do { succeed n }; note n } finally { note 3 } }; return 7 }",
        // Inactive branches still need the normal completion's carrier.
        "def bad : Logged Nat := do { for n in items do { try { let b : Bool ← do { if true then continue else succeed n }; note n } finally { note 3 } }; return 7 }",
        // A dead normal continuation does not erase a malformed annotation.
        "def bad : Logged Nat := do { for n in items do { try { let b : 1 ← do { continue }; note n } finally { note 3 } }; return 7 }",
        // Absent else supplies Unit, not a guessed Bool value.
        "def bad : Logged Nat := do { for n in items do { try { let b : Bool ← do { if true then continue }; note n } finally { note 3 } }; return 7 }",
        // Parenthesized do owns its own loop scope even as a bound action.
        "def bad : Logged Nat := do { for n in items do { try { let b : Bool ← (do { continue }); note n } finally { note 3 } }; return 7 }",
        // A nested body's local cannot become free in the continuation.
        "def bad : Logged Nat := do { for n in items do { try { let b : Nat ← do { let hidden := n; succeed hidden }; note hidden } finally { note 3 } }; return 7 }",
        // A bound normal value cannot change an outer return's type.
        "def bad : Logged Nat := do { for n in items do { try { let b : Bool ← do { if true then return true else succeed false }; note n } finally { note 3 } }; return 7 }",
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
        "def recovered : Logged Nat := do { for n in items do { try { let b : Bool ← do { note n; if n == 1 then continue else succeed true }; note (if b then 4 else 5) } finally { note 3 } }; return 7 }\n#eval observed recovered",
        &["13243007"],
    );
}

#[test]
fn generic_nested_binding_values_do_not_need_new_monad_or_loop_instances() {
    checked(
        &base(),
        r#"
def genericBound {M : Type -> Type} [Pure M] [Bind M] [Functor M]
    [MonadExcept Nat M] [MonadFinally M] {R A B : Type} [ForIn M R A]
    (xs : R) (stop : Bool) (normal : A -> M B)
    (consume : B -> M PUnit) (cleanup : M PUnit) : M PUnit := do
  for x in xs do
    try
      let value : B ← do
        if stop then continue
        normal x
      consume value
    finally
      cleanup
"#,
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

#[test]
fn mixed_return_break_continue_paths_share_the_checked_loop_packet() {
    execute(
        &base(),
        r#"
def choose (mode : Nat) : Logged Nat := do
  for n in items do
    try
      note n
      if mode == 0 then
        break
      else
        if mode == 1 then
          continue
        else
          return 42
    finally
      note 3
    note 9
  note 8
  return 7
#eval observed (choose 0)
#eval observed (choose 1)
#eval observed (choose 2)
"#,
        &["138007", "13238007", "13042"],
    );
}

#[test]
fn return_in_a_handler_exits_the_function_after_cleanup() {
    execute(
        &base(),
        r#"
def handlerReturn : Logged Nat := do
  for n in items do
    try
      note n
      (raise (4 : Nat) : Logged PUnit)
    catch e =>
      note e
      return (e + 38)
    finally
      note 3
    note 9
  return 7
def cleanupFailure : Logged Nat := do
  for n in items do
    try
      note n
      return 42
    finally
      note 3
      (raise (5 : Nat) : Logged PUnit)
    note 9
  return 7
#eval observed handlerReturn
#eval observed cleanupFailure
"#,
        &["143042", "13105"],
    );
}

#[test]
fn returns_cross_nested_regions_without_entering_either_suffix() {
    execute(
        &base(),
        r#"
def nestedReturn : Logged Nat := do
  for n in items do
    try
      note n
      try
        note 2
        return 42
      finally
        note 3
      note 8
    finally
      note 4
    note 9
  return 7
#eval observed nestedReturn
"#,
        &["1234042"],
    );
}

#[test]
fn owned_return_payloads_survive_loop_and_finalizer_closures() {
    execute(
        &base(),
        r#"
def owned (text : String) : Logged String := do
  for n in items do
    try
      let payload := String.append text "!"
      note n
      return payload
    finally
      note 3
    note 9
  return "unreachable"
def measure : Logged Nat := loggedMap (fun s => String.length s) (owned "value")
#eval observed measure
"#,
        &["13006"],
    );
}

#[test]
fn generic_nonlocal_returns_need_no_new_instance_or_trust_primitive() {
    checked(
        &base(),
        r#"
def genericReturn {M : Type -> Type} [Pure M] [Bind M] [Functor M]
    [MonadExcept Nat M] [MonadFinally M] {R A : Type} [ForIn M R A]
    (xs : R) (action : A -> M PUnit) (cleanup : M PUnit) (value : A) : M A := do
  for x in xs do
    try
      action x
      return x
    catch e =>
      continue
    finally
      cleanup
  return value
"#,
    );
}

#[test]
fn incorrect_return_values_inside_inactive_handlers_are_checked() {
    let engine = base();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for source in [
        "def bad : Logged Nat := do { for n in items do { try { return true } finally { note n } }; return 7 }",
        "def bad : Logged Nat := do { for n in items do { try { note n } catch e => { return true } }; return 7 }",
        "def bad : Logged Nat := do { for n in items do { try { return 42 } finally { return 7 } }; return 7 }",
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
        "def recovered : Logged Nat := do { for n in items do { try { return 42 } finally { note n } }; return 7 }\n#eval observed recovered",
        &["1042"],
    );
}

#[test]
fn nested_returning_loops_preserve_the_outermost_result_type() {
    execute(
        &base(),
        r#"
def nestedLoops : Logged Nat := do
  for n in items do
    note n
    for k in items do
      try
        note k
        return 42
      finally
        note 3
      note 8
    note 9
  return 7
#eval observed nestedLoops
"#,
        &["113042"],
    );
}

#[test]
fn pattern_handlers_transport_payload_returns_and_local_breaks() {
    execute(
        &base(),
        r#"
def patternExit (code : Nat) : Logged Nat := do
  for n in items do
    try
      note n
      (raise code : Logged PUnit)
    catch
    | Nat.zero => break
    | Nat.succ e => return (e + 39)
    finally
      note 3
    note 8
  return 7
#eval observed (patternExit 0)
#eval observed (patternExit 4)
"#,
        &["13007", "13042"],
    );
}
