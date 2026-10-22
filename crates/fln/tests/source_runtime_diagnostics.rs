//! Ordinary checked diagnostic functions reach the native VM implementation.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits};
use std::process::Command;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn base() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .unwrap()
    .engine
}
const PANIC: &str = r#"
def panicCore {α : Sort u} [Inhabited α] (msg : String) : α := default
def panic {α : Sort u} [Inhabited α] (msg : String) : α := panicCore msg
"#;
fn run(base: &Engine, source: &str) -> fln::DefinitionBatchExecution {
    base.execute_source_definitions(
        &[source.as_bytes()],
        &KVMap::new(),
        EngineExecutionLimits::new(limits().kernel),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .unwrap()
}
fn native_panic() -> Engine {
    let engine = checked(&base(), PANIC);
    decorate(&engine, "lean_panic_fn_borrowed")
}
fn decorate(engine: &Engine, symbol: &str) -> Engine {
    Engine::from_environment(
        fln_elab::externs::register(
            engine.environment(),
            &fln::Name::from_components(["panicCore"]),
            vec![fln_elab::externs::ExternEntry::Standard {
                backend: fln::Name::from_components(["all"]),
                symbol: symbol.to_owned(),
            }],
        )
        .unwrap(),
    )
}
fn parent(case: &str, expected_stderr: &str) -> bool {
    if std::env::var("FLN_SOURCE_DIAGNOSTIC_CASE").as_deref() == Ok(case) {
        return false;
    }
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", case, "--nocapture", "--test-threads=1"])
        .env("FLN_SOURCE_DIAGNOSTIC_CASE", case)
        .env("RUST_BACKTRACE", "0")
        .env("LEAN_BACKTRACE", "0")
        .env_remove("LEAN_ABORT_ON_PANIC")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("1 passed; 0 failed; 0 ignored;"));
    assert_eq!(String::from_utf8(output.stderr).unwrap(), expected_stderr);
    true
}
#[test]
fn panic_returns_checked_nat_default() {
    if parent("panic_returns_checked_nat_default", "recover\n") {
        return;
    }
    let result = run(&native_panic(), "#eval (panic \"recover\" : Nat)");
    assert_eq!(
        fln::closed_vm_value(&result.executions[0].exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(0))
    );
}

#[test]
fn one_panic_row_preserves_distinct_result_types_and_strict_uses() {
    if parent(
        "one_panic_row_preserves_distinct_result_types_and_strict_uses",
        "nat\nstring\n",
    ) {
        return;
    }
    let result = run(
        &native_panic(),
        r#"#eval let first : Nat := panic "nat"; let second : String := panic "string"; first + second.length"#,
    );
    assert_eq!(
        fln::closed_vm_value(&result.executions[0].exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(0))
    );
}
#[test]
fn panic_returns_constructor_and_callable_defaults_without_erasing_them() {
    if parent(
        "panic_returns_constructor_and_callable_defaults_without_erasing_them",
        "constructor\ncallback\n",
    ) {
        return;
    }
    let engine = checked(
        &native_panic(),
        r#"
structure Payload where
  value : Nat
instance : Inhabited Payload := Inhabited.mk (Payload.mk 42)
instance : Inhabited (Nat -> Nat) := Inhabited.mk (fun n => n + 21)
def constructorResult : Nat := (panic "constructor" : Payload).value
def callbackResult : Nat := (panic "callback" : Nat -> Nat) 21
"#,
    );
    for query in ["#eval constructorResult", "#eval callbackResult"] {
        let result = run(&engine, query);
        assert_eq!(
            fln::closed_vm_value(&result.executions[0].exit).unwrap(),
            Some(fln::ClosedVmValue::Scalar(42))
        );
    }
}
#[test]
fn panic_partial_application_keeps_the_native_call() {
    if parent(
        "panic_partial_application_keeps_the_native_call",
        "staged\npartial\nlocal\n",
    ) {
        return;
    }
    let engine = checked(
        &native_panic(),
        r#"
def staged : String -> Nat := @panicCore Nat instInhabitedNat
def consume (f : String -> Nat) : Nat := f "partial"
def once (message : String) : Nat := let f := @panicCore Nat instInhabitedNat; f message
"#,
    );
    for query in [
        "#eval staged \"staged\"",
        "#eval consume staged",
        "#eval once \"local\"",
    ] {
        let result = run(&engine, query);
        assert_eq!(
            fln::closed_vm_value(&result.executions[0].exit).unwrap(),
            Some(fln::ClosedVmValue::Scalar(0))
        );
    }
}
#[test]
fn absent_extern_keeps_the_ordinary_logical_definition() {
    if parent("absent_extern_keeps_the_ordinary_logical_definition", "") {
        return;
    }
    let result = run(
        &checked(&base(), PANIC),
        "#eval (panic \"silent logical definition\" : Nat)",
    );
    assert_eq!(
        fln::closed_vm_value(&result.executions[0].exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(0))
    );
}

#[test]
fn discarded_and_repeated_panics_are_not_removed_or_coalesced() {
    if parent(
        "discarded_and_repeated_panics_are_not_removed_or_coalesced",
        "discarded\nrepeat\nrepeat\n",
    ) {
        return;
    }
    let result = run(
        &native_panic(),
        r#"#eval let discarded : Nat := panic "discarded"; let a : String := panic "repeat"; let b : String := panic "repeat"; 42"#,
    );
    assert_eq!(
        fln::closed_vm_value(&result.executions[0].exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(42))
    );
}
fn cause(mut error: fln::EngineExecutionError) -> fln::EngineExecutionError {
    while let fln::EngineExecutionError::BatchCommand { error: inner, .. } = error {
        error = *inner;
    }
    error
}
#[test]
fn changed_extern_contracts_and_private_collisions_refuse_without_output_or_publication() {
    if parent(
        "changed_extern_contracts_and_private_collisions_refuse_without_output_or_publication",
        "",
    ) {
        return;
    }
    let logical = checked(&base(), PANIC);
    let altered = checked(
        &base(),
        &PANIC.replace(":= default", ":= let value : α := default; value"),
    );
    let collision = checked(&native_panic(), "def _fln_runtime_diagnostic_object := Nat");
    for engine in [
        decorate(&logical, "foreign_panic"),
        decorate(&altered, "lean_panic_fn_borrowed"),
        collision,
    ] {
        let root = engine.logical_root(&KVMap::new());
        let error = engine
            .execute_source_definitions(
                &[b"#eval (panic \"must not print\" : Nat)"],
                &KVMap::new(),
                EngineExecutionLimits::new(limits().kernel),
            )
            .unwrap_err();
        assert!(matches!(
            cause(error),
            fln::EngineExecutionError::Ingress(fln::IngressError::UnsupportedNode { .. })
        ));
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}
#[test]
fn diagnostic_preparation_is_bounded_and_execution_can_be_retried() {
    if parent(
        "diagnostic_preparation_is_bounded_and_execution_can_be_retried",
        "retry\n",
    ) {
        return;
    }
    let engine = native_panic();
    let root = engine.logical_root(&KVMap::new());
    let source = b"#eval (panic \"retry\" : Nat)";
    let mut bounded = EngineExecutionLimits::new(limits().kernel);
    bounded.ingress.max_nodes = 1;
    let error = engine
        .execute_source_definitions(&[source], &KVMap::new(), bounded)
        .unwrap_err();
    assert!(matches!(
        cause(error),
        fln::EngineExecutionError::Ingress(fln::IngressError::ResourceLimit { .. })
    ));
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    let result = run(&engine, std::str::from_utf8(source).unwrap());
    assert_eq!(
        fln::closed_vm_value(&result.executions[0].exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(0))
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

const TRACE_SOURCE: &str = r#"
inductive Unit where
  | unit
class ToString (α : Type u) where
  toString : α -> String
instance : ToString String := ToString.mk (fun value => value)
instance : ToString Nat := ToString.mk (fun _ => "number")
def dbgTrace {α : Type u} (message : String) (continuation : Unit -> α) : α :=
  continuation Unit.unit
"#;

fn native_trace() -> Engine {
    let engine = checked(&base(), TRACE_SOURCE);
    decorate_trace(&engine, "lean_dbg_trace")
}

fn decorate_trace(engine: &Engine, symbol: &str) -> Engine {
    Engine::from_environment(
        fln_elab::externs::register(
            engine.environment(),
            &fln::Name::from_components(["dbgTrace"]),
            vec![fln_elab::externs::ExternEntry::Standard {
                backend: fln::Name::from_components(["all"]),
                symbol: symbol.to_owned(),
            }],
        )
        .unwrap(),
    )
}

#[test]
fn source_debug_traces_evaluate_message_and_continuation_once_in_order() {
    if parent(
        "source_debug_traces_evaluate_message_and_continuation_once_in_order",
        "message\nouter\nbody\n",
    ) {
        return;
    }
    let result = run(
        &native_trace(),
        r#"#eval dbg_trace (dbg_trace "message"; "outer"); dbg_trace "body"; 42"#,
    );
    assert_eq!(
        fln::closed_vm_value(&result.executions[0].exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(42))
    );
}

#[test]
fn source_debug_trace_uses_interpolation_instances_and_linebreak_continuations() {
    if parent(
        "source_debug_trace_uses_interpolation_instances_and_linebreak_continuations",
        "λ {literal}: number\nnumber\n",
    ) {
        return;
    }
    let engine = native_trace();
    let root = engine.logical_root(&KVMap::new());
    let invalid = engine
        .check_source_files(
            &[br#"def invalid : Nat := dbg_trace "\{literal\}"; 42"#],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .expect_err("only the opening interpolation brace has an escape at the pin");
    assert_eq!(invalid.disposition(), ("input", false, 1));
    assert!(matches!(
        invalid,
        fln::SourceCheckError::Command { error, .. }
            if matches!(*error, fln::EngineExecutionError::Frontend(
                fln::NatDefinitionFrontendError::Parse(_)))
    ));
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    let result = run(
        &engine,
        r#"#eval
  dbg_trace "λ \{literal}: {42}"
  dbg_trace (40 + 2)
  42"#,
    );
    assert_eq!(
        fln::closed_vm_value(&result.executions[0].exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(42))
    );
}

#[test]
fn source_debug_trace_retains_callable_results_and_skips_dead_branches() {
    if parent(
        "source_debug_trace_retains_callable_results_and_skips_dead_branches",
        "closure\nlive\n",
    ) {
        return;
    }
    let engine = native_trace();
    for source in [
        r#"#eval (dbg_trace "closure"; fun n : Nat => n + 2) 40"#,
        r#"#eval if false then (dbg_trace "dead"; 0) else (dbg_trace "live"; 42)"#,
    ] {
        let result = run(&engine, source);
        assert_eq!(
            fln::closed_vm_value(&result.executions[0].exit).unwrap(),
            Some(fln::ClosedVmValue::Scalar(42))
        );
    }
}

#[test]
fn source_debug_trace_globals_resist_shadowing_and_partial_calls_stay_effectful() {
    if parent(
        "source_debug_trace_globals_resist_shadowing_and_partial_calls_stay_effectful",
        "global\npartial\n",
    ) {
        return;
    }
    let engine = checked(
        &native_trace(),
        r#"
namespace Shadow
def dbgTrace (_message : String) (_body : Unit -> Nat) : Nat := 0
def toString (_value : String) : String := "shadowed"
def traced (message : String) : Nat := dbg_trace message; 42
end Shadow
def later : String -> (Unit -> Nat) -> Nat := @dbgTrace Nat
"#,
    );
    for source in [
        r#"#eval Shadow.traced "global""#,
        r#"#eval later "partial" (fun _ => 42)"#,
    ] {
        let result = run(&engine, source);
        assert_eq!(
            fln::closed_vm_value(&result.executions[0].exit).unwrap(),
            Some(fln::ClosedVmValue::Scalar(42))
        );
    }
}

#[test]
fn changed_trace_contracts_refuse_without_reporting_or_publication() {
    if parent(
        "changed_trace_contracts_refuse_without_reporting_or_publication",
        "",
    ) {
        return;
    }
    let logical = checked(&base(), TRACE_SOURCE);
    let altered = checked(
        &base(),
        &TRACE_SOURCE.replace(
            "continuation Unit.unit",
            "let result := continuation Unit.unit; result",
        ),
    );
    let collision = checked(&native_trace(), "def _fln_runtime_debug_trace := Nat");
    for engine in [
        decorate_trace(&logical, "foreign_trace"),
        decorate_trace(&altered, "lean_dbg_trace"),
        collision,
    ] {
        let root = engine.logical_root(&KVMap::new());
        let error = engine
            .execute_source_definitions(
                &[br#"#eval dbg_trace "must not print"; 42"#],
                &KVMap::new(),
                EngineExecutionLimits::new(limits().kernel),
            )
            .unwrap_err();
        assert!(matches!(
            cause(error),
            fln::EngineExecutionError::Ingress(fln::IngressError::UnsupportedNode { .. })
        ));
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn trace_without_an_extern_keeps_its_ordinary_checked_definition() {
    if parent(
        "trace_without_an_extern_keeps_its_ordinary_checked_definition",
        "",
    ) {
        return;
    }
    let result = run(
        &checked(&base(), TRACE_SOURCE),
        r#"#eval dbg_trace "logical definition"; 42"#,
    );
    assert_eq!(
        fln::closed_vm_value(&result.executions[0].exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(42))
    );
}

#[test]
fn tracing_and_panicking_share_the_checked_diagnostic_transport() {
    if parent(
        "tracing_and_panicking_share_the_checked_diagnostic_transport",
        "before\npanic\nafter\n",
    ) {
        return;
    }
    let engine = decorate(&checked(&native_trace(), PANIC), "lean_panic_fn_borrowed");
    let result = run(
        &engine,
        r#"#eval dbg_trace "before"; let recovered : Nat := panic "panic"; dbg_trace "after"; recovered + 42"#,
    );
    assert_eq!(
        fln::closed_vm_value(&result.executions[0].exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(42))
    );
}

#[test]
fn source_debug_trace_accepts_the_checked_punit_unit_aliases() {
    if parent(
        "source_debug_trace_accepts_the_checked_punit_unit_aliases",
        "alias\n",
    ) {
        return;
    }
    let source = TRACE_SOURCE.replace(
        "inductive Unit where\n  | unit",
        // The source seed already contains the admitted PUnit family.
        "abbrev Unit : Type := PUnit.{1}\nabbrev Unit.unit : Unit := PUnit.unit",
    );
    let logical = checked(&base(), &source);
    let engine = decorate_trace(&logical, "lean_dbg_trace");
    let result = run(&engine, r#"#eval dbg_trace "alias"; 42"#);
    assert_eq!(
        fln::closed_vm_value(&result.executions[0].exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(42))
    );
}
