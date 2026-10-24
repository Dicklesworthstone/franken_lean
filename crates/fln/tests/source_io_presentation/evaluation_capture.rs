//! Actual imported output and diagnostic effects under the Lean evaluation door.
#![forbid(unsafe_code)]

use super::*;

fn assert_pure_format(execution: &fln::DefinitionExecution, expected: &str) {
    assert_eq!(
        execution.evaluation_presentation(),
        Some(EvaluationResultPresentation::Format { width: 120 }),
    );
    assert!(execution.io_evaluation_outcome().unwrap().is_none());
    assert_eq!(
        fln::source_format::render_vm(
            execution.engine.environment(),
            &execution.runtime_type,
            &execution.exit,
            120,
            Default::default(),
        )
        .unwrap(),
        expected,
    );
}

#[test]
fn admitted_evaluations_capture_streams_traces_and_panics_without_process_leaks() {
    const CHILD: &str = "FLN_IO_PRESENTATION_CAPTURE_CHILD";
    const TEST: &str = "evaluation_capture::admitted_evaluations_capture_streams_traces_and_panics_without_process_leaks";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            // Keep libtest's capture enabled: fixture progress uses Rust's
            // eprintln!, whereas leaked runtime stream writes reach the actual
            // process handles and remain observable in these pipes.
            .args(["--exact", TEST, "--test-threads=1"])
            .env(CHILD, "1")
            .env("LEAN_BACKTRACE", "0")
            .env_remove("LEAN_ABORT_ON_PANIC")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "child failed: stdout={} stderr={}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
        assert!(
            output.stderr.is_empty(),
            "evaluation leaked process stderr: {}",
            String::from_utf8_lossy(&output.stderr),
        );
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains("1 passed; 0 failed"), "{stdout}");
        for leaked in [
            "capture trace λ",
            "capture recoverable",
            "out:err",
            "before:failure",
        ] {
            assert!(
                !stdout.contains(leaked),
                "evaluation leaked process stdout: {stdout}"
            );
        }
        return;
    }

    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let Some(engine) = imported() else { return };
            let original = engine.logical_root(&KVMap::new());
            let result = run(
                engine,
                concat!(
                    "#eval (dbgTrace \"capture trace λ\" (fun _ => (7 : Nat)))\n",
                    "#eval (panic! \"capture recoverable\" : Nat)\n",
                    "#eval show IO Nat from do\n",
                    "  IO.print \"out:\"\n",
                    "  IO.eprint \"err\"\n",
                    "  IO.eprintln \" λ\"\n",
                    "  IO.println \"done\"\n",
                    "  return 42\n",
                    "#eval (13 : Nat)\n",
                ),
            );
            assert_eq!(result.batch.executions.len(), 4);
            let executions = &result.batch.executions;
            assert_eq!(
                executions[0].captured_stdout(),
                Some("capture trace λ\n".as_bytes())
            );
            assert_pure_format(&executions[0], "7");
            assert_eq!(
                executions[1].captured_stdout(),
                Some(
                    b"PANIC at _private.0._eval [anonymous]:2:7: capture recoverable\n".as_slice()
                ),
            );
            assert_pure_format(&executions[1], "0");
            assert_eq!(
                executions[2].captured_stdout(),
                Some("out:err λ\ndone\n".as_bytes())
            );
            assert_format(&executions[2], "42", None);
            assert_eq!(executions[3].captured_stdout(), Some(&[][..]));
            assert_pure_format(&executions[3], "13");
            assert_eq!(result.batch.engine.logical_root(&KVMap::new()), original);

            let silent = run(
                engine,
                "#eval show IO Unit from do\n  IO.eprintln \"silent result\"",
            );
            let execution = &silent.batch.executions[0];
            assert_eq!(
                execution.evaluation_presentation(),
                Some(EvaluationResultPresentation::IoUnit)
            );
            assert!(matches!(
                execution.io_evaluation_outcome().unwrap(),
                Some(IoEvaluationOutcome::Returned { .. })
            ));
            assert_eq!(
                execution.captured_stdout(),
                Some(b"silent result\n".as_slice())
            );

            let guarded = run(
                engine,
                concat!(
                    "/--\ninfo: guarded trace\n---\ninfo: 9\n-/\n",
                    "#guard_msgs in\n#eval (dbgTrace \"guarded trace\" (fun _ => (9 : Nat)))",
                ),
            );
            let execution = &guarded.batch.executions[0];
            assert_eq!(
                execution.captured_stdout(),
                Some(b"guarded trace\n".as_slice())
            );
            assert_pure_format(execution, "9");

            let failed = run(
                engine,
                concat!(
                    "#eval show IO Nat from do\n",
                    "  IO.print \"before:\"\n",
                    "  IO.eprintln \"failure\"\n",
                    "  throw (IO.userError \"expected capture failure\")",
                ),
            );
            let execution = &failed.batch.executions[0];
            assert_eq!(
                execution.captured_stdout(),
                Some(b"before:failure\n".as_slice())
            );
            let Some(IoEvaluationOutcome::Raised { runtime_type, exit }) =
                execution.io_evaluation_outcome().unwrap()
            else {
                panic!("the output prefix must accompany the checked IO exception");
            };
            assert_eq!(runtime_type, Expr::const_(name("IO.Error"), vec![]));
            assert_eq!(
                error_message(&execution.engine, &exit),
                "expected capture failure"
            );

            let after_failure = run(engine, "#eval (pure 17 : IO Nat)");
            let execution = &after_failure.batch.executions[0];
            assert_eq!(execution.captured_stdout(), Some(&[][..]));
            assert_format(execution, "17", None);
            assert_eq!(engine.logical_root(&KVMap::new()), original);
        })
        .unwrap()
        .join()
        .unwrap();
}
