//! Ordinary loops through the installed front doors (bead `fln-golem-ordinary-loops-fbj6`).
//!
//! Measured on 2026-10-07 at `71ec8bff`: `lean` refused every one of these with
//! `RecursionDepth { limit: 1000 }` or `ExecutionSteps`, because the doors ran user
//! programs under the interpreter's probe budget. The pinned Reference prints the
//! values asserted here (recorded that day from `lean` v4.32.0 on the same shapes;
//! each is also a closed-form fact: a triangular number, a list sum, a tree size).
//!
//! What this does not establish: speed. Non-tail recursion still needs frames;
//! `the_frame_ceiling_is_a_typed_stop_never_a_crash` pins that exhaustion is
//! exit 3 and not a host stack overflow. The execution-ceiling cases exercise
//! the caller's limits through source, import, standard-input, and replay paths.
#![forbid(unsafe_code)]
use std::{
    path::Path,
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);

fn directory() -> std::path::PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-ordinary-loops-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

fn lean(source: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(source)
        .output()
        .unwrap()
}

fn expect_output(name: &str, program: &str, expected: &str) {
    let dir = directory();
    let source = dir.join("Main.lean");
    std::fs::write(&source, program).unwrap();
    let output = lean(&source);
    eprintln!(
        "{name}: exit={:?} stdout={:?} stderr_bytes={}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout).trim(),
        output.stderr.len()
    );
    assert!(output.status.success(), "{name}: {output:?}");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout).trim(),
        expected,
        "{name}"
    );
    assert!(output.stderr.is_empty(), "{name}: {output:?}");
}

const SUM_TO: &str = "def sumTo : Nat → Nat\n  | 0 => 0\n  | n + 1 => (n + 1) + sumTo n\n";

#[test]
fn a_ten_thousand_iteration_recursion_prints_its_answer() {
    expect_output(
        "sumTo 10000",
        &format!("{SUM_TO}#eval sumTo 10000\n"),
        "50005000",
    );
}

#[test]
fn a_recursion_past_the_old_frame_and_step_ceilings_prints_its_answer() {
    // 200,000 calls is about 600,000 frames and 4.4 million instructions,
    // against the probe budget's 1,000 frames and 1,000,000 instructions.
    expect_output(
        "sumTo 200000",
        &format!("{SUM_TO}#eval sumTo 200000\n"),
        "20000100000",
    );
}

#[test]
fn building_and_folding_a_long_list_prints_its_answer() {
    expect_output(
        "list fold",
        "def build : Nat → List Nat → List Nat\n  | 0, acc => acc\n  | n + 1, acc => build n (n :: acc)\n#eval (build 20000 []).foldl (· + ·) 0\n",
        "199990000",
    );
}

#[test]
fn a_tree_of_a_hundred_thousand_nodes_is_past_the_old_step_ceiling() {
    // Depth 16: 131,071 nodes, more than one million instructions, shallow frames.
    expect_output(
        "tree size",
        "inductive T where\n  | leaf : T\n  | node : T → T → T\ndef mk : Nat → T\n  | 0 => .leaf\n  | n + 1 => .node (mk n) (mk n)\ndef T.size : T → Nat\n  | .leaf => 1\n  | .node l r => l.size + r.size + 1\n#eval (mk 16).size\n",
        "131071",
    );
}

#[test]
fn an_emitted_artifact_replays_under_the_same_budget_it_ran_under() {
    let dir = directory();
    let source = dir.join("Main.lean");
    let artifact = dir.join("main.flbc");
    std::fs::write(&source, format!("{SUM_TO}#eval sumTo 10000\n")).unwrap();
    let run = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(&artifact)
        .arg(&source)
        .output()
        .unwrap();
    assert!(run.status.success(), "{run:?}");
    let replay = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["flbc", "run", "--json"])
        .arg(&artifact)
        .output()
        .unwrap();
    eprintln!(
        "replay: exit={:?} stdout={}",
        replay.status.code(),
        String::from_utf8_lossy(&replay.stdout).trim()
    );
    assert!(replay.status.success(), "{replay:?}");
    assert!(
        String::from_utf8_lossy(&replay.stdout).contains("\"returnValue\":50005000"),
        "{replay:?}"
    );
}

#[test]
fn the_frame_ceiling_is_a_typed_stop_never_a_crash() {
    // A genuine non-tail recursion under a deliberately small frame ceiling:
    // it must stop without a signal, host overflow, or buffered output escaping.
    let dir = directory();
    let source = dir.join("Main.lean");
    std::fs::write(&source, format!("{SUM_TO}#eval sumTo 5000\n")).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg("--fln-max-frames=32")
        .arg(&source)
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    eprintln!(
        "ceiling: exit={:?} stderr={}",
        output.status.code(),
        stderr.trim().chars().take(160).collect::<String>()
    );
    assert_eq!(output.status.code(), Some(3), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    assert!(
        stderr.contains("RecursionDepth { limit: 32 }"),
        "{output:?}"
    );
}

#[test]
fn caller_execution_ceilings_reach_both_source_doors_and_artifact_replay() {
    let dir = directory();
    let source = dir.join("Main.lean");
    let artifact = dir.join("main.flbc");
    std::fs::write(&source, format!("{SUM_TO}#eval sumTo 30\n")).unwrap();
    let emitted = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(&artifact)
        .arg(&source)
        .output()
        .unwrap();
    assert!(emitted.status.success(), "{emitted:?}");

    for (binary, prefix, path) in [
        (env!("CARGO_BIN_EXE_lean"), vec![], &source),
        (env!("CARGO_BIN_EXE_fln"), vec!["run", "--json"], &source),
        (
            env!("CARGO_BIN_EXE_fln"),
            vec!["flbc", "run", "--json"],
            &artifact,
        ),
    ] {
        for (flag, reason) in [
            ("--fln-max-steps=0", "ExecutionSteps"),
            ("--fln-max-frames=0", "RecursionDepth"),
        ] {
            let output = Command::new(binary)
                .args(&prefix)
                .arg(flag)
                .arg(path)
                .output()
                .unwrap();
            assert_eq!(
                output.status.code(),
                Some(3),
                "{prefix:?} {flag}: {output:?}"
            );
            assert!(output.stdout.is_empty(), "{output:?}");
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(stderr.contains(reason), "{output:?}");
            if !prefix.is_empty() {
                assert!(stderr.contains("\"authority\":false"), "{output:?}");
            }
        }
        let completed = Command::new(binary)
            .args(&prefix)
            .args(["--fln-max-steps", "100000", "--fln-max-frames=128"])
            .arg(path)
            .output()
            .unwrap();
        assert!(completed.status.success(), "{prefix:?}: {completed:?}");
        assert!(String::from_utf8_lossy(&completed.stdout).contains("465"));
    }
}

#[test]
fn source_imports_and_stdin_cannot_bypass_an_execution_ceiling() {
    use std::io::Write;
    use std::process::Stdio;

    let dir = directory();
    let source = dir.join("Main.lean");
    std::fs::write(dir.join("Local.lean"), format!("{SUM_TO}#eval sumTo 30\n")).unwrap();
    std::fs::write(&source, "import Local\n#eval sumTo 2\n").unwrap();
    for (binary, prefix) in [
        (env!("CARGO_BIN_EXE_lean"), vec![]),
        (env!("CARGO_BIN_EXE_fln"), vec!["run", "--json"]),
    ] {
        let control = Command::new(binary)
            .args(&prefix)
            .arg(&source)
            .output()
            .unwrap();
        assert!(control.status.success(), "{control:?}");
        let stopped = Command::new(binary)
            .args(&prefix)
            .args(["--fln-max-steps", "0"])
            .arg(&source)
            .output()
            .unwrap();
        assert_eq!(stopped.status.code(), Some(3), "{stopped:?}");
        assert!(stopped.stdout.is_empty(), "{stopped:?}");
        assert!(String::from_utf8_lossy(&stopped.stderr).contains("ExecutionSteps"));
    }

    for (limit, expected_exit) in [("0", 3), ("100", 0)] {
        let mut child = Command::new(env!("CARGO_BIN_EXE_lean"))
            .args(["--stdin", "--fln-max-steps", limit])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child
            .stdin
            .take()
            .unwrap()
            .write_all(b"#check Nat\n#eval 42\n")
            .unwrap();
        let output = child.wait_with_output().unwrap();
        assert_eq!(output.status.code(), Some(expected_exit), "{output:?}");
        if expected_exit == 3 {
            assert!(output.stdout.is_empty(), "{output:?}");
            assert!(String::from_utf8_lossy(&output.stderr).contains("ExecutionSteps"));
        } else {
            assert_eq!(String::from_utf8_lossy(&output.stdout), "Nat : Type\n42\n");
        }
    }
}

#[test]
fn a_resource_stop_does_not_publish_a_source_artifact() {
    let dir = directory();
    let source = dir.join("Main.lean");
    let artifact = dir.join("stopped.flbc");
    std::fs::write(&source, "#eval 42\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--fln-max-steps=0", "--emit-flbc"])
        .arg(&artifact)
        .arg(&source)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(3), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    assert!(
        !artifact.exists(),
        "a stopped program published an artifact"
    );
}
