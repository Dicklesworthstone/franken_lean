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

/// A field-notation receiver whose type head no parameter has is refused with the pin's
/// message, read from v4.32.0 for these sources: the function, the head (` ...` when it
/// takes arguments), and the receiver inline, or on its own line when longer than thirty
/// characters. A different message is a mismatch, a non-answer.
#[test]
fn a_guarded_field_receiver_refusal_prints_the_pins_message() {
    let execution = EngineExecutionLimits::new(limits().kernel);
    let note = "\n\nNote: Such a parameter must be explicit, or implicit with a unique name, to be used by field notation";
    let prefix = "def Box (n : Nat) := Nat\ndef Tag := Nat\ndef Nat.twice (n m : Nat) : Nat := n\n\
                  namespace Box\nexport Nat (twice)\nend Box\nnamespace Tag\nexport Nat (twice)\nend Tag\n";
    for (command, message) in [
        (
            "example (x y : Box 1) : Nat := x.twice y",
            "Invalid field notation: Function `Nat.twice` does not have a usable parameter of type `Box ...` for which to substitute `x`",
        ),
        (
            "example (aVeryLongReceiverNameIndeedSoLong y : Box 1) : Nat := aVeryLongReceiverNameIndeedSoLong.twice y",
            "Invalid field notation: Function `Nat.twice` does not have a usable parameter of type `Box ...` for which to substitute\n  aVeryLongReceiverNameIndeedSoLong",
        ),
        (
            "example (t y : Tag) : Nat := t.twice y",
            "Invalid field notation: Function `Nat.twice` does not have a usable parameter of type `Tag` for which to substitute `t`",
        ),
    ] {
        let expected = format!("{message}{note}");
        let source = format!("{prefix}/--\nerror: {expected}\n-/\n#guard_msgs in\n{command}\n");
        let completed = seed()
            .execute_source_commands_with_checks(source.as_bytes(), &KVMap::new(), execution)
            .unwrap()
            .into_complete()
            .unwrap();
        let logged: Vec<_> = completed
            .warnings
            .iter()
            .filter(|warning| warning.severity == SourceSeverity::Error)
            .map(|warning| warning.message.as_str())
            .collect();
        assert_eq!(logged, [expected.as_str()], "{command}");
    }
}

/// A definition whose code generation fails is kept at the pin: `addAndCompile` logs "failed to
/// compile definition, …" after kernel admission. Under a guard expecting that error, it is
/// admitted uncompiled and the pin's message is logged; a later proof still unfolds it. The
/// pinned v4.32.0 accepts this program and refuses its unguarded form.
#[test]
fn a_guarded_definition_with_a_noncomputable_dependency_is_kept_uncompiled() {
    let execution = EngineExecutionLimits::new(limits().kernel);
    let message = "failed to compile definition, consider marking it as 'noncomputable' because \
                   it depends on 'a', which is 'noncomputable'";
    let source = format!(
        "noncomputable def a : Nat := 7\n/--\nerror: {message}\n-/\n#guard_msgs in\n\
         def b : Nat := a\ntheorem t : b = 7 := rfl\n"
    );
    let completed = seed()
        .execute_source_commands_with_checks(source.as_bytes(), &KVMap::new(), execution)
        .unwrap()
        .into_complete()
        .unwrap();
    let logged: Vec<_> = completed
        .warnings
        .iter()
        .filter(|warning| warning.severity == SourceSeverity::Error)
        .map(|warning| (warning.command_index, warning.message.as_str()))
        .collect();
    assert_eq!(logged, [(1, message)]);
    assert!(
        seed()
            .execute_source_commands_with_checks(
                b"noncomputable def a : Nat := 7\ndef b : Nat := a\n",
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
