use super::{MultiplexerOutput, write_output};
use fln_rt::obj::Obj;
use std::io::{BufRead, Read, Write};
use std::process::{Command, ExitCode, Stdio};

const CHILD: &str = "FLN_TEST_NATIVE_STDOUT_PUBLICATION";
const TEST: &str = "output::tests::native_stdout_publication_child";
const READY: &[u8] = b"\nFLN_NATIVE_STDOUT_READY\n";
const EFFECTS: &str = "unit-effect λ\0\nrecord-effect 🙂\n";
const RESULT: &str = "\"io record λ\"\n";

fn child(mode: &str) -> Command {
    let mut command = Command::new(std::env::current_exe().expect("test executable"));
    command
        .args(["--exact", TEST, "--nocapture", "--test-threads=1"])
        .env(CHILD, mode);
    command
}

fn native_effects() {
    let stdout = Obj::stdio_stdout().expect("exact native stdout stream");
    let put_str = stdout.try_ctor_child(4).expect("native putStr method");
    for text in ["unit-effect λ\0\n", "record-effect 🙂\n"] {
        let packet = put_str
            .try_stdio_put_str(&Obj::mk_string(text), &Obj::mk_nat(0))
            .expect("native buffered write");
        assert_eq!(
            packet.try_ctor_child(0).expect("write status").unbox(),
            1,
            "fwrite accepted each native effect"
        );
    }
}

#[test]
fn native_stdout_publication_child() {
    let Ok(mode) = std::env::var(CHILD) else {
        return;
    };
    #[cfg(unix)]
    if mode == "broken-driver" {
        assert_broken_pipe_flush_failure();
        std::process::exit(0);
    }
    let broken = mode == "broken";
    if !broken {
        let mut out = std::io::stdout().lock();
        out.write_all(READY).unwrap();
        out.flush().unwrap();
    }
    if mode == "same-thread" {
        native_effects();
    } else {
        std::thread::spawn(native_effects).join().unwrap();
    }
    if broken {
        // Confirm the native writes completed before the parent removes the
        // pipe's reader. Rust has no pending bytes when publication begins.
        let mut out = std::io::stdout().lock();
        out.write_all(READY).unwrap();
        out.flush().unwrap();
        drop(out);
        let mut release = [0];
        std::io::stdin().read_exact(&mut release).unwrap();
        assert_eq!(release, [1]);
    }
    let (text, diagnostic, status) = match mode.as_str() {
        "same-thread" | "worker" => (RESULT, "accepted diagnostic\n", 7),
        "silent" => ("", "", 3),
        "broken" => ("", "", 0),
        _ => panic!("unknown child mode"),
    };
    let code = write_output(MultiplexerOutput {
        stdout: text.to_owned(),
        stderr: diagnostic.to_owned(),
        exit_code: status,
    });
    // Exit before libtest can append its own status to the measured stream.
    // A host write failure is the only permitted override of the saved code.
    let status = if code == ExitCode::from(status) {
        i32::from(status)
    } else {
        assert_eq!(code, ExitCode::from(1));
        1
    };
    std::process::exit(status);
}

#[test]
fn native_stdout_precedes_cli_results_and_survives_silent_failure() {
    for mode in ["same-thread", "worker", "silent"] {
        let output = child(mode).output().expect("run piped publication child");
        let start = output
            .stdout
            .windows(READY.len())
            .position(|bytes| bytes == READY)
            .expect("child reached publication test")
            + READY.len();
        let (expected, diagnostic, status) = if mode == "silent" {
            (EFFECTS.to_owned(), "", 3)
        } else {
            (format!("{EFFECTS}{RESULT}"), "accepted diagnostic\n", 7)
        };
        assert_eq!(output.status.code(), Some(status), "mode {mode}");
        assert_eq!(&output.stdout[start..], expected.as_bytes(), "mode {mode}");
        assert_eq!(output.stderr, diagnostic.as_bytes(), "mode {mode}");
    }
}

#[cfg(unix)]
fn assert_broken_pipe_flush_failure() {
    let mut child = child("broken")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run flush-failure child");
    let mut stdout = std::io::BufReader::new(child.stdout.take().unwrap());
    let mut line = Vec::new();
    loop {
        line.clear();
        assert_ne!(stdout.read_until(b'\n', &mut line).unwrap(), 0);
        if line == b"FLN_NATIVE_STDOUT_READY\n" {
            break;
        }
    }
    // Closing the sole reader makes the already buffered native write fail at
    // fflush. An empty Rust response cannot independently trigger that error.
    drop(stdout);
    child.stdin.take().unwrap().write_all(&[1]).unwrap();
    let output = child.wait_with_output().expect("wait for flush refusal");
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stderr.is_empty(), "{:?}", output.stderr);
}

#[cfg(unix)]
#[test]
fn native_stdout_flush_failure_is_not_success_with_empty_cli_output() {
    // Create the measured pipe only after this driver's exec. A concurrently
    // spawning test can otherwise fork with its reader still open: CLOEXEC
    // closes that copy at exec, but not during the fork-to-exec interval.
    // The driver runs exactly one test and retains the original EPIPE probe.
    let output = child("broken-driver")
        .output()
        .expect("run isolated flush probe");
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert!(output.stderr.is_empty(), "{:?}", output.stderr);
}
