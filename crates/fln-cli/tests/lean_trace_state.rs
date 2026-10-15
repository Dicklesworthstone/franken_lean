//! Installed Lean front door: raw traces and guards, not a synthetic formatter call.
#![forbid(unsafe_code)]
use std::{
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn lean(source: &str) -> Output {
    let dir = std::env::temp_dir().join(format!(
        "fln-traces-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&dir).unwrap();
    let path = dir.join("Main.lean");
    // A source-defined prelude makes this installed-binary test independent of
    // an external Init.olean installation. It is checked, not a fabricated seed.
    let source = format!("prelude\ninductive Fact : Prop | mk\n{source}");
    std::fs::write(&path, &source).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&path)
        .output()
        .unwrap();
    assert_eq!(std::fs::read_to_string(path).unwrap(), source);
    result
}
fn success(source: &str, expected: &str) {
    let output = lean(source);
    assert_eq!(output.status.code(), Some(0), "{source}\n{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
}
#[test]
fn raw_trace_prints_goals_and_empty_state_in_original_command_order() {
    success(
        "#check Fact\nexample (a b : Fact) : Fact := by\n  trace_state\n  exact a\n  trace_state\n#check Fact.mk",
        "Fact : Prop\na b : Fact\n⊢ Fact\n\nFact.mk : Fact\n",
    );
}
#[test]
fn guard_captures_traces_from_failed_choices_and_leaves_neighbours_visible() {
    success(
        "#check Fact\n/-- info: h : Fact\n⊢ Fact -/\n#guard_msgs in\nexample (h : Fact) : Fact := by\n  first | (trace_state; fail) | exact h\n#check Fact.mk",
        "Fact : Prop\nFact.mk : Fact\n",
    );
}
#[test]
fn guard_filter_drops_trace_without_disabling_proof_checking() {
    success(
        "#guard_msgs (drop info) in\nexample : Fact := by trace_state; constructor\n#check Fact.mk",
        "Fact.mk : Fact\n",
    );
    let rejected =
        lean("#guard_msgs (drop info) in\nexample (P : Prop) : P := by trace_state; constructor");
    assert_eq!(rejected.status.code(), Some(1), "{rejected:?}");
    assert!(rejected.stdout.is_empty());
}
#[test]
fn later_bad_proof_never_publishes_earlier_buffered_traces() {
    let output = lean(
        "example : Fact := by trace_state; constructor\nexample (P : Prop) : P := by constructor",
    );
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty());
}
