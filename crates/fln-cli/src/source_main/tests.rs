use super::*;
use crate::{LeanCommand, parse_lean_command};

fn words(values: &[&str]) -> Vec<OsString> {
    values.iter().map(OsString::from).collect()
}

#[test]
fn run_switch_preserves_every_later_argument_without_option_processing() {
    for switch in ["--run", "-r"] {
        let parsed = parse_lean_command(words(&[
            "--fln-max-steps",
            "123",
            switch,
            "Main.lean",
            "λ🙂",
            "",
            "a b",
            "--help",
            "--",
            "--fln-max-steps=0",
            "--jobs=8",
            "\"\\\n",
        ]))
        .unwrap();
        let LeanCommand::Run {
            path,
            arguments,
            vm_limits,
            ..
        } = parsed
        else {
            panic!("the run switch must select executable source");
        };
        assert_eq!(path, PathBuf::from("Main.lean"));
        assert_eq!(vm_limits.max_steps, 123);
        assert_eq!(
            arguments.unwrap(),
            [
                "λ🙂",
                "",
                "a b",
                "--help",
                "--",
                "--fln-max-steps=0",
                "--jobs=8",
                "\"\\\n",
            ]
        );
    }
    let LeanCommand::Run {
        path, arguments, ..
    } = parse_lean_command(words(&["--run", "-script.lean", "--run"])).unwrap()
    else {
        panic!("dash-prefixed file must be a run path");
    };
    assert_eq!(path, PathBuf::from("-script.lean"));
    assert_eq!(arguments.unwrap(), ["--run"]);
    assert!(matches!(
        parse_lean_command(words(&["--", "--run"])).unwrap(),
        LeanCommand::Source { path, .. } if path == std::path::Path::new("--run")
    ));
}

#[test]
fn run_rejects_missing_paths_and_conflicting_frontend_modes() {
    for values in [
        vec!["--run"],
        vec!["-r"],
        vec!["--run", ""],
        vec!["--stdin", "--run", "Main.lean"],
        vec!["--src-deps", "--run", "Main.lean"],
        vec!["First.lean", "--run", "Second.lean"],
    ] {
        assert!(parse_lean_command(words(&values)).is_err(), "{values:?}");
    }
}

#[test]
fn argv_bounds_charge_utf8_and_empty_arguments_before_source_io() {
    assert_eq!(arguments(words(&["λ", ""]), 4).unwrap(), ["λ", ""]);
    assert_eq!(
        arguments(words(&["λ", ""]), 3),
        Err(ArgumentsError::Limit { limit: 3 })
    );
    assert_eq!(
        arguments(words(&["", ""]), 1),
        Err(ArgumentsError::Limit { limit: 1 })
    );
    assert!(arguments(Vec::new(), 0).unwrap().is_empty());

    let output = crate::run_lean(words(&[
        "--max-bytes=1",
        "--run",
        "/missing/Main.lean",
        "too big",
    ]));
    assert_eq!(output.exit_code, 3);
    assert!(output.stdout.is_empty());
    assert!(
        output
            .stderr
            .starts_with("lean: resource: script arguments")
    );
    assert!(!output.stderr.contains("could not read"));
}

#[cfg(unix)]
#[test]
fn argv_utf8_refusal_is_lossless_and_precedes_source_io() {
    use std::os::unix::ffi::OsStringExt;
    let output = crate::run_lean([
        OsString::from("--run"),
        OsString::from("/missing/Main.lean"),
        OsString::from_vec(vec![0xff]),
    ]);
    assert_eq!(output.exit_code, 1);
    assert!(output.stdout.is_empty());
    assert!(
        output
            .stderr
            .contains("script argument 0 is not valid UTF-8")
    );
    assert!(!output.stderr.contains("could not read"));
}

fn empty_commands() -> (fln::SourceCommandBatchExecution, fln::EngineExecutionLimits) {
    let limits = fln::EngineExecutionLimits::new(fln::Budget::for_stack_bytes(
        crate::SOURCE_RUN_KERNEL_STACK_BYTES,
    ));
    let commands = fln::Engine::from_environment(fln::Environment::new())
        .execute_source_commands_with_checks(b"", &fln::KVMap::new(), limits)
        .unwrap()
        .into_complete()
        .unwrap();
    (commands, limits)
}

#[test]
fn failed_frontend_never_invokes_main_and_keeps_its_disposition() {
    let (commands, limits) = empty_commands();
    let frontend = MultiplexerOutput {
        stdout: "accepted prefix\n".to_owned(),
        stderr: "frontend refusal\n".to_owned(),
        exit_code: 5,
    };
    let result = execute(&commands, &[], limits, frontend);
    assert_eq!(result.stdout, "accepted prefix\n");
    assert_eq!(result.stderr, "frontend refusal\n");
    assert_eq!(result.exit_code, 5);
}

#[test]
fn missing_main_keeps_prior_frontend_output_and_unwinds_capture() {
    let (commands, limits) = empty_commands();
    let result = execute(
        &commands,
        &[],
        limits,
        MultiplexerOutput::success("42\n".to_owned()),
    );
    assert_eq!(result.stdout, "42\n");
    assert_eq!(result.exit_code, 1);
    assert!(
        result
            .stderr
            .contains("unknown executable declaration `main`")
    );
    let next = fln::StdoutCapture::begin(0).unwrap().finish();
    assert!(next.error.is_none());
    assert!(next.bytes.is_empty());
}
