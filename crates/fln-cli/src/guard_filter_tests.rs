//! Severity policies over real checked commands, plus retained diagnostic routing.
use super::*;

fn execute(source: &str) -> Result<fln::SourceCommandBatchExecution, fln::EngineExecutionError> {
    let admission = fln::EngineAdmissionLimits::new(fln::Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = fln::Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    engine
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &fln::KVMap::new(),
            fln::EngineExecutionLimits::new(admission.kernel),
        )
        .map(|result| result.into_complete().unwrap())
}

fn render(source: &str) -> MultiplexerOutput {
    let completed = execute(source).unwrap();
    render_lean_source_commands(&completed, WarningSink::Unreachable)
}

#[test]
fn guard_filters_check_drop_and_pass_preserve_command_order() {
    for (spec, expected, stdout) in [
        ("info", "info: 4", "1\n3\n"),
        ("check info", "info: 4", "1\n3\n"),
        ("drop info", "", "1\n3\n"),
        ("pass info", "", "1\n4\n3\n"),
        ("drop warning", "", "1\n4\n3\n"),
        ("pass all, drop info", "", "1\n4\n3\n"),
        ("drop info, pass all", "", "1\n3\n"),
        ("pass error, drop all", "", "1\n3\n"),
        ("drop warning, info", "info: 4", "1\n3\n"),
    ] {
        let source =
            format!("#eval 1\n/-- {expected} -/\n#guard_msgs ({spec}) in\n#eval 2 + 2\n#eval 3\n");
        let output = render(&source);
        assert_eq!(output.exit_code, 0, "{spec}: {}", output.stderr);
        assert_eq!(output.stdout, stdout, "{spec}");
    }
    // A checked expectation does not match an info message that was passed through.
    let output = render("/-- info: 4 -/\n#guard_msgs (pass info) in\n#eval 4\n");
    assert_eq!(output.exit_code, 1);
}

#[test]
fn guard_filters_apply_to_check_without_fabricating_rendering_certainty() {
    for spec in ["info", "drop warning, info"] {
        let output = render(&format!(
            "/-- info: 1 : Nat -/\n#guard_msgs ({spec}) in\n#check 1\n"
        ));
        assert_eq!(output.exit_code, 0, "{}", output.stderr);
        assert!(output.stdout.is_empty());
    }
    let output = render("#guard_msgs (drop info) in\n#check 1\n");
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert!(output.stdout.is_empty());
    let output = render("#guard_msgs (pass info) in\n#check 1\n");
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert_eq!(output.stdout, "1 : Nat\n");
    let output = render("/-- info: 1 : Int -/\n#guard_msgs (info) in\n#check 1\n");
    assert_eq!(output.exit_code, CAPABILITY_NOT_IMPLEMENTED_EXIT);
}

fn warning_batch(source: &str) -> fln::SourceCommandBatchExecution {
    let mut completed = execute(source).unwrap();
    // The warning producer has its own source tests. Here exercise the same typed
    // diagnostic payload at the presentation boundary without importing sorryAx.
    completed.warnings.push(fln::SourceWarning {
        command_index: 0,
        at: fln_parse::BytePos(0),
        message: "declaration uses `sorry`".to_owned(),
        severity: fln::SourceSeverity::Warning,
    });
    completed
}

#[test]
fn guard_filters_route_positioned_warnings_and_sort_before_matching() {
    let source = "/-- info: 4 -/\n#guard_msgs (drop warning, info) in\n#eval 4\n";
    let output = render_lean_source_commands(&warning_batch(source), WarningSink::Unreachable);
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert!(output.stdout.is_empty());

    let source = "/-- info: 4 -/\n#guard_msgs (info) in\n#eval 4\n";
    let output = render_lean_source_commands(
        &warning_batch(source),
        WarningSink::Print {
            file: "Main.lean",
            source: source.as_bytes(),
        },
    );
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert!(output.stdout.starts_with("Main.lean:"));
    assert!(
        output
            .stdout
            .ends_with("warning: declaration uses `sorry`\n")
    );

    let source = "/-- info: 4\n---\nwarning: declaration uses `sorry` -/\n#guard_msgs (ordering := sorted) in\n#eval 4\n";
    let output = render_lean_source_commands(&warning_batch(source), WarningSink::Unreachable);
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert!(output.stdout.is_empty());
    let source = source.replace("sorted", "exact");
    let output = render_lean_source_commands(&warning_batch(&source), WarningSink::Unreachable);
    assert_eq!(output.exit_code, 1);
}

#[test]
fn guard_filters_never_ignore_errors_or_unsupported_positions() {
    for spec in [
        "drop error",
        "drop all",
        "drop all, pass error",
        "positions := true",
    ] {
        let error = execute(&format!("#guard_msgs ({spec}) in\n#eval 4\n")).unwrap_err();
        assert_eq!(
            execution_error_disposition(&error),
            ("capability", false, 5),
            "{spec}: {error}"
        );
    }
    let error = execute("#guard_msgs (pass error, drop all) in\n#check missingGuardSpecName\n")
        .unwrap_err();
    assert_ne!(execution_error_disposition(&error).2, 0);
}

#[test]
fn guard_filters_reject_ambiguous_retained_guard_tables() {
    let mut completed = execute("#guard_msgs in\ndef x : Nat := 1\n").unwrap();
    completed.guards.push(completed.guards[0].clone());
    let output = render_lean_source_commands(&completed, WarningSink::Unreachable);
    assert_eq!(output.exit_code, 4);
    assert!(output.stdout.is_empty());
    completed.guards.pop();
    completed.guards[0].command_index = completed.command_count;
    let output = render_lean_source_commands(&completed, WarningSink::Unreachable);
    assert_eq!(output.exit_code, 4);
}

#[test]
fn trace_state_and_trace_message_match_pinned_lean_cases() {
    // 1. traceStateBacktracking.lean: traces survive failed tactic branches (`CoreM.lean:407-410`).
    let backtracking = concat!(
        "example (h : 0 = 1) : False := by\n",
        "  first | trace_state; fail | contradiction\n\n",
        "example (h : 0 = 1) : False := by\n",
        "  first | trace \"first branch\"; fail | contradiction\n",
    );
    let output = render(backtracking);
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert_eq!(output.stdout, "h : 0 = 1\n⊢ False\nfirst branch\n");

    // 2. 813.lean: universe generalization instantiates `Sort u_1` in `trace_state`.
    let case_813 = concat!(
        "def Function.const {α : Sort u} (β : Sort v) (a : α) (b : β) : α := a\n",
        "open Function\n",
        "theorem constApply {y : β} {x : α} : const α y x = y := rfl\n",
        "example (p : Nat → Prop) (h : p 1) : p (const Nat 1 2) := by simp only [constApply]; trace_state; exact h\n",
        "example (p : α → Prop) (h : p a) : p (const Nat a 2) := by simp only [constApply]; trace_state; exact h\n",
        "example (f : α → α) (p : α → Prop) (h : p (f a)) : p (const Nat (f a) 2) := by simp only [constApply]; trace_state; exact h\n",
    );
    let output = render(case_813);
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert_eq!(
        output.stdout,
        concat!(
            "p : Nat → Prop\nh : p 1\n⊢ p 1\n",
            "α : Sort u_1\na : α\np : α → Prop\nh : p a\n⊢ p a\n",
            "α : Sort u_1\na : α\nf : α → α\np : α → Prop\nh : p (f a)\n⊢ p (f a)\n",
        )
    );

    // The following two cases need the sorry/Unit prelude and the default
    // `ne_eq` simp rule, which the bounded source seed deliberately omits.
    // Admit that support through the ordinary
    // source/checker path; warnings and traces still come from real commands.
    let admission = fln::EngineAdmissionLimits::new(fln::Budget::for_stack_bytes(2 * 1024 * 1024));
    let sorry_engine = fln::Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[b"abbrev Unit : Type := PUnit.{1}\n\
                @[simp] theorem ne_eq.{u} {A : Sort u} (a b : A) : (Ne a b) = Not (a = b) := rfl\n\
                inductive Lean.Name where\n\
                  | anonymous\n\
                  | str (pre : Lean.Name) (value : String)\n\
                  | num (pre : Lean.Name) (value : Nat)\n\
                axiom sorryAx.{u} (A : Sort u) (synthetic : Bool) : A"],
            &fln::KVMap::new(),
            fln::SourceCheckLimits::new(admission),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let unbound_axiom = sorry_engine
        .execute_source_commands_with_checks(
            b"example : Unit := sorry",
            &fln::KVMap::new(),
            fln::EngineExecutionLimits::new(admission.kernel),
        )
        .expect_err("a data-valued axiom without an executable binding remains noncomputable");
    assert!(
        format!("{unbound_axiom:?}").contains("NoncomputableDependency"),
        "{unbound_axiom:?}"
    );
    // Init.Prelude gives this admitted axiom @[extern "lean_sorry"]. Supply
    // that real metadata through the same journal used by imported attributes.
    let sorry_engine = fln::Engine::from_environment(
        fln_elab::externs::register(
            sorry_engine.environment(),
            &fln::Name::from_components(["sorryAx"]),
            vec![fln_elab::externs::ExternEntry::Standard {
                backend: fln::Name::from_components(["all"]),
                symbol: "lean_sorry".to_owned(),
            }],
        )
        .unwrap(),
    );
    let unavailable_macro = sorry_engine
        .execute_source_commands_with_checks(
            b"example : Unit := by sorry",
            &fln::KVMap::new(),
            fln::EngineExecutionLimits::new(admission.kernel),
        )
        .expect_err("the bounded prelude does not import Init.Tactics's sorry macro");
    assert!(
        format!("{unavailable_macro:?}").contains("tacticSorry"),
        "{unavailable_macro:?}"
    );
    let execute_sorry = |source: &str| {
        // Init.Tactics expands `sorry` to `exact sorry`. Exercise that term
        // expansion here; source_imported_execution covers the imported macro.
        // Declaration positions precede the expansion and stay unchanged.
        let source = source.replace("\n  sorry\n", "\n  exact sorry\n");
        sorry_engine
            .execute_source_commands_with_checks(
                source.as_bytes(),
                &fln::KVMap::new(),
                fln::EngineExecutionLimits::new(admission.kernel),
            )
            .unwrap()
            .into_complete()
            .unwrap()
    };

    // 3. 1027.lean: `simp_all` followed by `trace_state` and `sorry`.
    let case_1027 = "example (h : x ≠ 0) : Unit := by\n  simp_all\n  trace_state\n  sorry\n";
    let completed = execute_sorry(case_1027);
    let output = render_lean_source_commands(
        &completed,
        WarningSink::Print {
            file: "1027.lean",
            source: case_1027.as_bytes(),
        },
    );
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert_eq!(
        output.stdout,
        "x : Nat\nh : ¬x = 0\n⊢ Unit\n1027.lean:1:0: warning: declaration uses `sorry`\n"
    );

    // 4. 1235.lean: `generalize` followed by `trace_state` and `sorry`.
    let case_1235 = concat!(
        "opaque f (a b : Nat) : Nat\n",
        "example : f 1 2 = f 2 1 := by\n",
        "  generalize h : f 1 = g\n",
        "  trace_state\n",
        "  sorry\n",
    );
    let completed = execute_sorry(case_1235);
    let output = render_lean_source_commands(
        &completed,
        WarningSink::Print {
            file: "1235.lean",
            source: case_1235.as_bytes(),
        },
    );
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert_eq!(
        output.stdout,
        "g : Nat → Nat\nh : f 1 = g\n⊢ g 2 = f 2 1\n1235.lean:2:0: warning: declaration uses `sorry`\n"
    );

    // 5. Guarded `trace_state`, literal messages, closed goals and filter policies.
    let guarded = concat!(
        "/--\ntrace: x : Nat\n⊢ x = x\n-/\n",
        "#guard_msgs in\n",
        "theorem t1 (x : Nat) : x = x := by\n  trace_state\n  rfl\n\n",
        "/-- trace: -/\n",
        "#guard_msgs in\n",
        "theorem t2 : True := by\n  trivial\n  trace_state\n\n",
        "/-- trace: hello -/\n",
        "#guard_msgs (trace) in\n",
        "theorem t3 : True := by\n  trace \"hello\"\n  trivial\n\n",
        "#guard_msgs (drop trace) in\n",
        "theorem t4 : True := by\n  trace_state\n  trivial\n\n",
        "#guard_msgs (pass trace) in\n",
        "theorem t5 : True := by\n  trace \"passed\"\n  trivial\n",
    );
    let output = render(guarded);
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert_eq!(output.stdout, "passed\n");

    // Mismatch on `trace_state` returns capability non-answer (exit 5), while mismatch on
    // literal `trace "msg"` returns guard-msgs failure (exit 1).
    let mismatch_goal = render(
        "/-- trace: wrong -/\n#guard_msgs in\ntheorem m1 : True := by\n  trace_state\n  trivial\n",
    );
    assert_eq!(mismatch_goal.exit_code, CAPABILITY_NOT_IMPLEMENTED_EXIT);
    // The pin prints an empty trace after proof closure, not `no goals`.
    // A mismatch there still carries raw-goal printer uncertainty.
    let mismatch_closed_goal = render(
        "/-- trace: no goals -/\n#guard_msgs in\ntheorem closed : True := by\n  trivial\n  trace_state\n",
    );
    assert_eq!(
        mismatch_closed_goal.exit_code,
        CAPABILITY_NOT_IMPLEMENTED_EXIT
    );
    let missing_trace = render(
        "/-- trace: unknown class -/\n#guard_msgs in\ntheorem silent : True := by trivial\n",
    );
    assert_eq!(missing_trace.exit_code, CAPABILITY_NOT_IMPLEMENTED_EXIT);
    let mixed_goal = render(
        "/-- trace: wrong -/\n#guard_msgs in\ntheorem mixed : True := by\n  trace \"literal\"\n  trace_state\n  trivial\n",
    );
    assert_eq!(mixed_goal.exit_code, CAPABILITY_NOT_IMPLEMENTED_EXIT);

    let mismatch_msg = render(
        "/-- trace: wrong -/\n#guard_msgs in\ntheorem m2 : True := by\n  trace \"actual\"\n  trivial\n",
    );
    assert_eq!(mismatch_msg.exit_code, 1);
}
