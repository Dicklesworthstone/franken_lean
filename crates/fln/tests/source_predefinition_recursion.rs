//! Ordinary predefinitions bind self before tactic alternatives are selected.
//! Compare source acceptance with the pin and let both native checkers judge
//! the exact result equations; no unchecked recursive constant is installed.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};
use std::{path::PathBuf, process::Command};

const DECREASING: &str = "def down (n : Nat) : Nat := match n with | .zero => 0 | .succ k => (by first | exact down k | exact 42)";
const ROOT_QUALIFIED_RECURSION: &str = r#"inductive Branch where
  | stop
  | left (child : Branch)
  | right (child : Branch)
namespace Q
def f (x : Branch) : Nat := match x with
  | .stop => 0
  | .left _t => (by first | exact _root_.Q.f _t | exact 42)
  | .right t => f t
end Q
"#;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .expect("source seed")
        .into_complete()
        .expect("source seed passes both checkers")
}

fn oracle(label: &str, source: &str, accepted: bool) {
    oracle_output(label, source, accepted, "");
}

fn oracle_output(label: &str, source: &str, accepted: bool, expected_stdout: &str) {
    let binary = std::env::var_os("FLN_REFERENCE_LEAN")
        .or_else(|| std::env::var_os("FLN_REFERENCE_BIN"))
        .map(PathBuf::from)
        .filter(|path| path.is_file());
    let Some(binary) = binary else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "predefinition source differential requires the pinned executable"
        );
        eprintln!("SKIP reference probe {label}: executable unavailable");
        return;
    };
    let path = std::env::temp_dir().join(format!(
        "fln-predefinition-{}-{}-{label}.lean",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock")
            .as_nanos()
    ));
    std::fs::write(&path, format!("import Init\n{source}\n")).expect("oracle input");
    let output = Command::new(binary)
        .arg(&path)
        .output()
        .expect("run pinned predefinition probe");
    assert_eq!(
        output.status.code(),
        Some(if accepted { 0 } else { 1 }),
        "pin {label}: {}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    if accepted {
        assert!(
            output.stdout == expected_stdout.as_bytes() && output.stderr.is_empty(),
            "pin {label}: {}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

fn evaluated(base: &Engine, label: &str, source: &str, expected: &str) {
    oracle_output(label, source, true, &format!("{expected}\n"));
    let before = base.logical_root(&KVMap::new());
    let checked = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            fln::EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{label}: {error:?}"))
        .into_complete()
        .unwrap_or_else(|reason| panic!("{label}: {reason:?}"));
    let fln::VmExit::Returned(result) = &checked.executions.last().expect("evaluation").exit else {
        panic!("{label}: recursive program did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some(expected),
        "{label}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
}

fn accepted(base: &Engine, label: &str, source: &str) {
    oracle(label, source, true);
    let before = base.logical_root(&KVMap::new());
    let checked = base
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{label}: {error:?}"))
        .into_complete()
        .unwrap_or_else(|reason| panic!("{label}: {reason:?}"));
    assert!(checked.theorems > 0, "{label}: result equation checked");
    assert_eq!(base.logical_root(&KVMap::new()), before);
}

fn refused(base: &Engine, label: &str, source: &str) {
    oracle(label, source, false);
    let before = base.logical_root(&KVMap::new());
    let Err(error) = base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    ) else {
        panic!("{label}: the pin-refused recursive program was admitted");
    };
    assert!(
        !matches!(
            error.disposition().0,
            "resource" | "inconclusive" | "internal-fault"
        ),
        "{label}: {error:?}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
}

#[test]
fn decreasing_self_calls_win_first_and_try_before_fallback() {
    let base = engine();
    accepted(
        &base,
        "first_decreasing",
        &format!("{DECREASING}\ntheorem result : down 3 = 0 := by rfl"),
    );
    accepted(
        &base,
        "try_decreasing",
        "def down (n : Nat) : Nat := match n with\n | .zero => 0\n | .succ k => by\n   try exact down k\n   all_goals exact 42\ntheorem result : down 3 = 0 := by rfl",
    );
    accepted(
        &base,
        "inferred_result",
        "def down (n : Nat) := match n with | .zero => 0 | .succ k => (by first | exact down k | exact 42)\ntheorem result : down 3 = 0 := by rfl",
    );
    accepted(
        &base,
        "written_lambda",
        "def down : Nat → Nat := fun n => match n with | .zero => 0 | .succ k => (by first | exact down k | exact 42)\ntheorem result : down 3 = 0 := by rfl",
    );
    accepted(
        &base,
        "inferred_written_lambda",
        "def down := fun (n : Nat) => match n with | .zero => 0 | .succ k => (by first | exact down k | exact 42)\ntheorem result : down 3 = 0 := by rfl",
    );
    accepted(
        &base,
        "namespace",
        "namespace Nested\ndef down (n : Nat) : Nat := match n with | .zero => 0 | .succ k => (by first | exact Nested.down k | exact 42)\nend Nested\ntheorem result : Nested.down 3 = 0 := by rfl",
    );
    accepted(
        &base,
        "root_qualified_stays_global_on_recursive_retry",
        &format!(
            "{ROOT_QUALIFIED_RECURSION}\ntheorem leftValue : Q.f (Branch.left Branch.stop) = 42 := by rfl\ntheorem rightValue : Q.f (Branch.right Branch.stop) = 0 := by rfl"
        ),
    );
    accepted(
        &base,
        "method_self",
        "def Nat.down (n : Nat) : Nat := match n with | .zero => 0 | .succ k => (by first | exact k.down | exact 42)\ntheorem result : Nat.down 3 = 0 := by rfl",
    );
    // The pin compiles the captured helper as an irreducible mutual WF group.
    // Its helper names differ from the native local closure; compare the real
    // evaluated result while both engines still check the source declarations.
    evaluated(
        &base,
        "opaque_local_capture",
        "def down (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let rec step : Nat := (by first | exact down k | exact 42); step\n#eval down 3",
        "0",
    );
    accepted(
        &base,
        "private_self_hidden_on_retry",
        "def down (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let pick : Nat → Nat := (by first | assumption | exact (fun _ => 7)); down k + pick 0\ntheorem result : down 3 = 21 := by rfl",
    );
    accepted(
        &base,
        "discarded_nondecreasing_trial",
        "def down (n : Nat) : Nat := match n with\n | .zero => 0\n | .succ k => (by\n   first\n   | have _v : Nat := down n\n     fail\n   | exact down k)\ntheorem result : down 3 = 0 := by rfl",
    );
}

#[test]
fn fallback_value_cannot_be_published_for_a_selected_recursive_branch() {
    refused(
        &engine(),
        "wrong_fallback_value",
        &format!("{DECREASING}\ntheorem wrong : down 3 = 42 := by rfl"),
    );
    refused(
        &engine(),
        "root_qualified_is_not_reinterpreted_as_recursive_self",
        &format!(
            "{ROOT_QUALIFIED_RECURSION}\ntheorem wrong : Q.f (Branch.left Branch.stop) = 0 := by rfl"
        ),
    );
}

#[test]
fn selected_nondecreasing_self_calls_cannot_hide_behind_first() {
    let base = engine();
    for (label, source) in [
        (
            "nondecreasing",
            "def loop (n : Nat) : Nat := by first | exact loop n | exact 42",
        ),
        (
            "nondecreasing_match",
            "def loop (n : Nat) : Nat := match n with | .zero => 0 | .succ _k => (by first | exact loop n | exact 42)",
        ),
        (
            "nondecreasing_outer_first",
            "def loop (n : Nat) : Nat := by first | exact (match n with | .zero => 0 | .succ _k => loop n) | exact 42",
        ),
        (
            "recursive_constant",
            "def loop : Nat := by first | exact loop | exact 42",
        ),
        (
            "unused_recursive_value",
            "def loop (n : Nat) : Nat := by first | exact (let _ignored := loop n; 7) | exact 42",
        ),
        (
            "lambda_domain_preserves_header_constraint",
            "def broken := fun (n : (by guard_expr (broken : Nat) = broken; exact Nat)) => n",
        ),
    ] {
        refused(&base, label, source);
    }
}

#[test]
fn discarded_recursive_trials_remain_nonrecursive_and_keep_lexical_scope() {
    let base = engine();
    for (label, source) in [
        (
            "discarded_self",
            "def chosen (_n : Nat) : Nat := by\n first\n | have _v : Nat := chosen _n\n   fail\n | exact 42\ntheorem result : chosen 3 = 42 := by rfl",
        ),
        (
            "mismatched_self",
            "def chosen (_n : Nat) : Nat := by\n first\n | have _v : Bool := chosen _n\n   exact 7\n | exact 42\ntheorem result : chosen 3 = 42 := by rfl",
        ),
        (
            "unrelated_unknown",
            "def chosen : Nat := by first | exact missing | exact 42\ntheorem result : chosen = 42 := by rfl",
        ),
        (
            "hidden_from_assumption",
            "def chosen : Nat := by first | assumption | exact 42\ntheorem result : chosen = 42 := by rfl",
        ),
        (
            "hidden_from_instance_search",
            "class Choice where value : Nat\ninstance : Choice := ⟨7⟩\n@[reducible] def chosen : Choice := inferInstance\ntheorem result : chosen.value = 7 := by rfl",
        ),
        (
            "opaque_local_stays_nonrecursive",
            "def chosen : Nat := let rec helper : Nat := 42; helper\ntheorem result : chosen = 42 := by rfl",
        ),
        (
            "lambda_domain_constrains_tactic_choice",
            "def constrained := fun (n : (by guard_expr (constrained : Nat → Bool) = constrained; exact Nat)) => by first | exact 0 | exact true\ntheorem result : constrained 3 = true := by rfl",
        ),
        (
            "parameter_shadow",
            "def chosen (chosen : Nat) : Nat := by first | exact chosen | exact 42\ntheorem result : chosen 7 = 7 := by rfl",
        ),
        (
            "local_shadow",
            "def chosen : Nat := let chosen := 7; by first | exact chosen | exact 42\ntheorem result : chosen = 7 := by rfl",
        ),
        (
            "root_qualified_is_global",
            "namespace Q\ndef chosen (_n : Nat) : Nat := by first | exact _root_.Q.chosen _n | exact 42\nend Q\ntheorem result : Q.chosen 3 = 42 := by rfl",
        ),
        (
            "explicit_universes_need_a_global",
            "def chosen.{u} (_α : Type u) (_n : Nat) : Nat := by first | exact chosen.{u} _α _n | exact 42\ntheorem result : chosen Nat 3 = 42 := by rfl",
        ),
    ] {
        accepted(&base, label, source);
    }
}

#[test]
fn exhausted_checking_cannot_turn_a_recursive_trial_into_fallback_success() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    let mut stopped = limits();
    stopped.kernel.steps = 0;
    let result = base.check_source_files(
        &[DECREASING.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(stopped),
    );
    assert!(
        matches!(result, Ok(Outcome::Inconclusive(_)))
            || result
                .as_ref()
                .is_err_and(|error| matches!(error.disposition().0, "resource" | "inconclusive")),
        "zero kernel budget: {result:?}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
}

#[test]
fn guard_tactics_retain_elaboration_constraints_and_explicit_self_access() {
    let base = engine();
    for (label, source) in [
        (
            "explicit_guard_self",
            "def chosen : Nat := by\n first\n | guard_hyp chosen : Nat\n   exact 7\n | exact 42\ntheorem result : chosen = 7 := by rfl",
        ),
        (
            "explicit_guard_function_self",
            "def chosen (_n : Nat) : Nat := by\n first\n | guard_hyp chosen : Nat → Nat\n   exact 7\n | exact 42\ntheorem result : chosen 3 = 7 := by rfl",
        ),
        (
            "guard_expr_retains_parameter_type",
            "def chosen (_x) := by\n guard_expr (_x : Nat) = _x\n exact true\ntheorem result : @chosen = fun (_ : Nat) => true := by rfl",
        ),
        (
            "guard_target_retains_parameter_type",
            "def chosen (_x) := by\n guard_target = (let _w : Nat := _x; Nat)\n exact 7\ntheorem result : @chosen = fun (_ : Nat) => 7 := by rfl",
        ),
    ] {
        accepted(&base, label, source);
    }
}
