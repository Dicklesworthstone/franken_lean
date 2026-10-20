//! `#guard_msgs` in the engine (bead `fln-guard-msgs-lls1`): the guarded command runs as written
//! and its guard is reported with the batch, at its command's index, for a presentation to judge.
//! Every door that has no judge refuses a guard as not implemented (a non-answer), never runs
//! the command unjudged; so do the shapes no presentation here can judge.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionError, EngineExecutionLimits, KVMap,
    SourceCheckLimits, SourceGuard, SourceSeverity,
};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn seed() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn not_implemented(error: &EngineExecutionError) -> bool {
    match error {
        EngineExecutionError::BatchCommand { error, .. } => not_implemented(error),
        EngineExecutionError::NotImplemented { .. } => true,
        _ => false,
    }
}

#[test]
fn guards_are_reported_at_their_commands_and_the_command_still_runs() {
    let source = b"#eval 1\n/-- info: 4 -/\n#guard_msgs in\n#eval 2 + 2\ndef x : Nat := 3\n";
    let completed = seed()
        .execute_source_commands_with_checks(
            source,
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        completed.guards,
        [SourceGuard {
            command_index: 1,
            expected: "info: 4".to_owned(),
            spec: Default::default(),
        }]
    );
    assert_eq!(completed.execution_command_indices, [0, 1, 2]);
}

/// An `example` or `#check` declares nothing: under a guard expecting an error, its
/// elaboration refusal is logged at error severity for the presentation to judge, and the
/// stream continues. Unguarded, the same refusal still ends the batch.
#[test]
fn a_guarded_example_logs_its_elaboration_error() {
    let execution = EngineExecutionLimits::new(limits().kernel);
    let source = b"/-- error: Unknown identifier `nope` -/\n#guard_msgs in\nexample : Nat := nope\ndef y : Nat := 2\n";
    let completed = seed()
        .execute_source_commands_with_checks(source, &KVMap::new(), execution)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        completed
            .warnings
            .iter()
            .map(|warning| (
                warning.command_index,
                warning.severity,
                warning.message.as_str()
            ))
            .collect::<Vec<_>>(),
        [(0, SourceSeverity::Error, "Unknown identifier `nope`")]
    );
    assert_eq!(completed.execution_command_indices, [1]);
    assert!(
        seed()
            .execute_source_commands_with_checks(
                b"example : Nat := nope\n",
                &KVMap::new(),
                execution
            )
            .is_err()
    );
}

#[test]
fn doors_without_a_judge_and_unjudgeable_guards_are_not_implemented() {
    let engine = seed();
    let execution = EngineExecutionLimits::new(limits().kernel);
    let guarded = b"/-- info: 4 -/\n#guard_msgs in\n#eval 2 + 2\n";
    // No per-command outputs here, so nothing could judge the guard.
    let error = engine
        .execute_source_definitions(&[guarded], &KVMap::new(), execution)
        .unwrap_err();
    assert!(not_implemented(&error), "{error:?}");
    // A check-only pass prints nothing: a capability non-answer, exit 5.
    let error = engine
        .check_source_files(&[guarded], &KVMap::new(), SourceCheckLimits::new(limits()))
        .unwrap_err();
    assert_eq!(error.disposition(), ("capability", false, 5), "{error:?}");
    // Shapes whose messages this engine cannot produce as the pin does.
    for source in [
        "/-- error: boom -/\n#guard_msgs in\n#eval 2 + 2\n",
        // The pin would still add a failing definition, which this engine cannot reproduce.
        "/-- error: Unknown identifier `nope` -/\n#guard_msgs in\ndef x : Nat := nope\n",
        "/-- warning: unused -/\n#guard_msgs in\ndef x : Nat := 1\n",
        "/-- info: 4 -/\n#guard_msgs (drop error) in\n#eval 2 + 2\n",
        "#guard_msgs in\n#guard_msgs in\n#eval 2 + 2\n",
    ] {
        let error = engine
            .execute_source_commands_with_checks(source.as_bytes(), &KVMap::new(), execution)
            .unwrap_err();
        assert!(not_implemented(&error), "{source}: {error:?}");
    }
}
