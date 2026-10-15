//! Raw trace observations travel beside ordinary checked source admission.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name,
    SourceCommandBatchExecution,
};

fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
    .unwrap()
    .into_complete()
    .unwrap()
}
fn run(base: &Engine, source: &str) -> SourceCommandBatchExecution {
    base.execute_source_commands_with_checks(
        source.as_bytes(),
        &KVMap::new(),
        EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
    )
    .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
    .into_complete()
    .unwrap()
}
fn texts(result: &SourceCommandBatchExecution) -> Vec<&str> {
    result
        .traces
        .iter()
        .map(|row| row.message.as_str())
        .collect()
}

#[test]
fn snapshots_group_hypotheses_and_retain_let_values_without_executing_examples() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let source = "example (a b : Nat) (h : a = b) : a = b := by\n  let x : Nat := 7\n  trace_state\n  exact h\n  trace_state\n";
    let result = run(&base, source);
    assert_eq!(
        texts(&result),
        ["a b : Nat\nh : a = b\nx : Nat := 7\n⊢ a = b", ""]
    );
    assert_eq!(result.batch.engine.logical_root(&KVMap::new()), root);
    assert!(result.batch.executions.is_empty());
    assert_eq!(result.checks.len(), 1);
}

#[test]
fn failed_choices_retain_raw_observations_but_not_failed_proofs() {
    let result = run(
        &engine(),
        "example (h : True) : True := by\n  first | (trace_state; fail) | exact h\n  trace_state",
    );
    assert_eq!(texts(&result), ["h : True\n⊢ True", ""]);
}

#[test]
fn theorem_traces_have_original_crlf_offsets_and_keep_checked_declarations() {
    let base = engine();
    let source = "-- 𝛼\r\ntheorem traced (h : True) : True := by\r\n  trace_state\r\n  exact h\r\n";
    let result = run(&base, source);
    assert_eq!(texts(&result), ["h : True\n⊢ True"]);
    assert_eq!(result.traces[0].at.0, source.find("trace_state").unwrap());
    assert!(
        result
            .batch
            .engine
            .environment()
            .contains(&Name::from_components(["traced"]))
    );
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["traced"]))
    );
}

#[test]
fn attributed_and_noncomputable_definitions_keep_the_same_effects() {
    let source = "@[simp] theorem traced : True := by trace_state; constructor\nnoncomputable def value : Nat := by trace_state; exact 7";
    let base = engine();
    let observed = run(&base, source);
    let plain = run(&base, &source.replace("trace_state; ", ""));
    assert_eq!(texts(&observed), ["⊢ True", "⊢ Nat"]);
    assert_eq!(
        observed.batch.engine.logical_root(&KVMap::new()),
        plain.batch.engine.logical_root(&KVMap::new())
    );
}

#[test]
fn failed_later_source_returns_no_trace_batch_or_engine_successor() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    assert!(base.execute_source_commands_with_checks(
        b"theorem first : True := by trace_state; constructor\ntheorem bad : False := by trace_state; constructor",
        &KVMap::new(), EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))).is_err());
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["first"]))
    );
    assert_eq!(
        texts(&run(&base, "example : True := by trace_state; constructor")),
        ["⊢ True"]
    );
}

#[test]
fn constructor_goals_keep_their_case_tags_and_focus_boundaries() {
    let result = run(
        &engine(),
        "example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by\n  constructor\n  trace_state\n  · trace_state; exact hp\n  · trace_state; exact hq",
    );
    let left = "case left\nP Q : Prop\nhp : P\nhq : Q\n⊢ P";
    let right = "case right\nP Q : Prop\nhp : P\nhq : Q\n⊢ Q";
    assert_eq!(
        texts(&result),
        [
            format!("{left}\n\n{right}"),
            left.to_owned(),
            right.to_owned()
        ]
    );
}

#[test]
fn automatic_and_shadowed_introductions_have_distinct_readable_names() {
    let base = engine();
    assert_eq!(
        texts(&run(
            &base,
            "example : (x : Nat) -> x = x := by intro; trace_state; rfl"
        )),
        ["x✝ : Nat\n⊢ x✝ = x✝"]
    );
    assert_eq!(
        texts(&run(
            &base,
            "example (x : Nat) : (x : Nat) -> x = x := by intro x; trace_state; rfl"
        )),
        ["x✝ x : Nat\n⊢ x = x"]
    );
}

#[test]
fn entry_points_without_a_trace_output_channel_refuse_instead_of_dropping_it() {
    let base = engine();
    let source = b"theorem traceWithoutOwner : True := by trace_state; constructor";
    assert!(
        base.admit_source_declaration(
            source,
            &KVMap::new(),
            EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
        )
        .is_err()
    );
}

#[test]
fn literal_messages_share_order_and_backtracking_without_goal_inspection() {
    let base = engine();
    let source = "example (P : Prop) (h : P) : P := by\n  first | (trace \"first branch\"; fail) | exact h\n  trace \"after proof\"\n  trace_state\n";
    let result = run(&base, source);
    assert_eq!(texts(&result), ["first branch", "after proof", ""]);
    assert_eq!(
        result
            .traces
            .iter()
            .map(|t| t.is_goal_state)
            .collect::<Vec<_>>(),
        [false, false, true]
    );
    assert_eq!(result.traces[0].at.0, source.find("trace \"").unwrap());
    assert_eq!(
        result.batch.engine.logical_root(&KVMap::new()),
        base.logical_root(&KVMap::new())
    );
}

#[test]
fn trace_message_decoding_preserves_unicode_escapes_and_empty_messages() {
    let result = run(
        &engine(),
        r#"example : True := by
  trace "first\nsecond\t\"λ\"\\"
  trace ""
  constructor
"#,
    );
    assert_eq!(texts(&result), ["first\nsecond\t\"λ\"\\", ""]);
}

#[test]
fn literal_trace_refuses_terms_extra_tokens_and_missing_diagnostic_owners() {
    let base = engine();
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    assert!(
        base.admit_source_declaration(
            b"theorem bad : True := by trace \"visible\"; constructor",
            &KVMap::new(),
            limits,
        )
        .is_err()
    );
    for source in [
        "example : True := by trace; constructor",
        "example : True := by trace True; constructor",
        "example : True := by trace \"one\" \"two\"; constructor",
        "example : True := by trace (\"one\"); constructor",
    ] {
        assert!(
            base.execute_source_commands_with_checks(
                source.as_bytes(),
                &KVMap::new(),
                EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
            )
            .is_err(),
            "{source}"
        );
    }
    let fresh = run(&base, "example : True := by trace \"fresh\"; constructor");
    assert_eq!(texts(&fresh), ["fresh"]);
}

#[test]
fn pinned_trace_state_backtracking_fixture_matches_its_unchanged_expected_output() {
    // Unmodified tests/elab input and expected output from the Reference pin
    // in SUITE.lock. Neither is regenerated from the native implementation.
    let source = include_str!("fixtures/traceStateBacktracking.lean");
    let expected = include_str!("fixtures/traceStateBacktracking.lean.out.expected");
    let result = run(&engine(), source);
    let actual = result
        .traces
        .iter()
        .map(|row| format!("{}\n", row.message))
        .collect::<String>();
    assert_eq!(actual, expected);
}
