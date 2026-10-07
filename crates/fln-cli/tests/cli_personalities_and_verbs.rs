//! Integration tests for new fln multiplexer verbs (diff, goals, doctor, serve-mcp,
//! replay, cache, build explain, olean verify-rebuild over module-system chains) and
//! toolchain personalities (leanc, lake).
#![forbid(unsafe_code)]

use std::process::Command;

/// A fresh directory under the system temp root, removed when dropped.
struct TempDir(std::path::PathBuf);

impl TempDir {
    fn new(label: &str) -> Self {
        Self::under(&std::env::temp_dir(), label)
    }

    fn under(base: &std::path::Path, label: &str) -> Self {
        let dir = base.join(format!(
            "fln-cli-verbs-{label}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        Self(dir)
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Whether `fln doctor` takes `dir` for a franken_lean checkout: an ancestor holding both
/// `SUITE.lock` and `Cargo.toml`, the rule its checkout-pins check applies.
fn inside_a_checkout(dir: &std::path::Path) -> bool {
    dir.ancestors()
        .any(|dir| dir.join("SUITE.lock").is_file() && dir.join("Cargo.toml").is_file())
}

fn doctor_json(cwd: &std::path::Path, elan_home: Option<&std::path::Path>) -> (i32, String) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
    command.args(["doctor", "--json"]).current_dir(cwd);
    if let Some(elan_home) = elan_home {
        command.env("ELAN_HOME", elan_home);
    }
    let output = command.output().expect("run fln doctor --json");
    (
        output.status.code().expect("exit code"),
        String::from_utf8(output.stdout).expect("utf8 stdout"),
    )
}

#[test]
fn doctor_runs_the_real_pipeline_and_checks_the_checkout_pins() {
    // The test runs inside the franken_lean checkout, so the pin check applies.
    let checkout = fln_core::checked_manifest_dir!();
    let (code, stdout) = doctor_json(&checkout, None);
    assert_eq!(code, 0, "{stdout}");
    assert!(stdout.contains("\"schema\":\"fln.doctor/2\""), "{stdout}");
    assert!(stdout.contains("\"status\":\"ok\""), "{stdout}");
    assert!(
        stdout.contains("{\"name\":\"source_pipeline_smoke\",\"required\":true,\"status\":\"ok\""),
        "{stdout}"
    );
    assert!(
        stdout.contains("{\"name\":\"checkout_pins\",\"required\":true,\"status\":\"ok\""),
        "{stdout}"
    );
    // Planned subsystems are named, never claimed.
    assert!(stdout.contains("\"bead\":\"franken_lean-g3k\""), "{stdout}");
    assert!(!stdout.contains("dual-engine"), "{stdout}");
}

#[test]
fn doctor_fails_when_run_in_a_checkout_pinned_to_another_reference() {
    let dir = TempDir::new("doctor-pins");
    let real_lock = std::fs::read_to_string(fln_core::checked_workspace_root!().join("SUITE.lock"))
        .expect("read SUITE.lock");
    let other_lock: String = real_lock
        .lines()
        .map(|line| {
            if line.starts_with("reference ") {
                "reference leanprover/lean4 tag=v4.99.0 commit=0000000000000000000000000000000000000000 tree=0000000000000000000000000000000000000000".to_owned()
            } else {
                line.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    std::fs::write(dir.0.join("SUITE.lock"), other_lock).unwrap();
    std::fs::write(dir.0.join("Cargo.toml"), "[workspace]\n").unwrap();
    let (code, stdout) = doctor_json(&dir.0, None);
    assert_eq!(code, 1, "{stdout}");
    assert!(stdout.contains("\"status\":\"failed\""), "{stdout}");
    assert!(
        stdout.contains("{\"name\":\"checkout_pins\",\"required\":true,\"status\":\"mismatch\""),
        "{stdout}"
    );
}

#[test]
fn doctor_reports_a_missing_reference_toolchain_without_failing() {
    // rch rewrites TMPDIR into the synced worktree on its workers, so the system temp
    // directory can itself sit inside a checkout; `/tmp` is the fallback outside one.
    let mut outside = TempDir::new("doctor-outside");
    if inside_a_checkout(&outside.0) {
        outside = TempDir::under(std::path::Path::new("/tmp"), "doctor-outside");
    }
    assert!(
        !inside_a_checkout(&outside.0),
        "no directory outside a checkout: {}",
        outside.0.display()
    );
    let empty_elan = TempDir::new("doctor-elan");
    let (code, stdout) = doctor_json(&outside.0, Some(&empty_elan.0));
    assert_eq!(
        code, 0,
        "the Reference is oracle apparatus, not a product dependency: {stdout}"
    );
    assert!(
        stdout.contains(
            "{\"name\":\"reference_oracle_toolchain\",\"required\":false,\"status\":\"missing\""
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "{\"name\":\"checkout_pins\",\"required\":false,\"status\":\"not_applicable\""
        ),
        "{stdout}"
    );
}

#[test]
fn unimplemented_verbs_exit_five_with_a_typed_notice() {
    for (args, expected_gate) in [
        (vec!["serve-mcp"], "G6"),
        (vec!["replay"], "G5"),
        (vec!["replay", "trace.bundle"], "G5"),
        (vec!["cache", "stats"], "G2"),
        (vec!["cache", "inspect"], "G2"),
        (vec!["cache", "clear"], "G2"),
        (vec!["doctor", "--sql"], "G5"),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(&args)
            .output()
            .expect("run verb");
        assert_eq!(output.status.code(), Some(5), "{args:?}");
        let stderr = String::from_utf8(output.stderr).expect("utf8 stderr");
        assert!(stderr.contains("not implemented"), "{args:?}: {stderr}");
        assert!(stderr.contains(expected_gate), "{args:?}: {stderr}");

        let mut json_args = args.clone();
        json_args.push("--json");
        let json_output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(&json_args)
            .output()
            .expect("run verb --json");
        assert_eq!(json_output.status.code(), Some(5), "{json_args:?}");
        let json_stderr = String::from_utf8(json_output.stderr).expect("utf8 stderr");
        assert!(json_stderr.contains("\"schema\":\"fln.capability-notice/2\""));
        assert!(json_stderr.contains("\"status\":\"not_implemented\""));
        assert!(json_stderr.contains("\"exit_code\":5"));
    }

    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .arg("build")
        .output()
        .expect("run build");
    assert_eq!(output.status.code(), Some(5));

    // A3: the --sql refusal points at the bead that owns the build database.
    let sql = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["doctor", "--sql"])
        .output()
        .expect("run doctor --sql");
    assert_eq!(sql.status.code(), Some(5));
    assert!(String::from_utf8_lossy(&sql.stderr).contains("franken_lean-05g"));
}

#[test]
fn check_olean_continue_refuses_receipts_a_single_file_and_repeats() {
    let manifest = fln_core::checked_manifest_dir!().join("Cargo.toml");
    let crate_dir = fln_core::checked_manifest_dir!();
    let run = |args: &[&std::ffi::OsStr]| {
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .arg("check-olean")
            .args(args)
            .output()
            .expect("run fln check-olean");
        (
            output.status.code(),
            String::from_utf8(output.stderr).expect("utf8 stderr"),
        )
    };
    let (code, stderr) = run(&[
        "--continue".as_ref(),
        "--receipts".as_ref(),
        "receipts.jsonl".as_ref(),
        crate_dir.as_os_str(),
    ]);
    assert_eq!(code, Some(1), "{stderr}");
    assert!(stderr.contains("writes no receipt set"), "{stderr}");

    let (code, stderr) = run(&["--continue".as_ref(), manifest.as_os_str()]);
    assert_eq!(code, Some(1), "{stderr}");
    assert!(
        stderr.contains("--continue requires a closed module-set root"),
        "{stderr}"
    );

    let (code, stderr) = run(&[
        "--continue".as_ref(),
        "--continue".as_ref(),
        crate_dir.as_os_str(),
    ]);
    assert_eq!(code, Some(2), "{stderr}");
    assert!(
        stderr.contains("--continue may be supplied at most once"),
        "{stderr}"
    );

    // --progress streams frontier rows, so it means nothing without --continue.
    let (code, stderr) = run(&["--progress".as_ref(), crate_dir.as_os_str()]);
    assert_eq!(code, Some(2), "{stderr}");
    assert!(stderr.contains("it requires --continue"), "{stderr}");
    let (code, stderr) = run(&[
        "--continue".as_ref(),
        "--progress".as_ref(),
        "--progress".as_ref(),
        crate_dir.as_os_str(),
    ]);
    assert_eq!(code, Some(2), "{stderr}");
    assert!(
        stderr.contains("--progress may be supplied at most once"),
        "{stderr}"
    );

    // --jobs schedules frontier modules, so it too needs --continue, and it takes
    // one positive count.
    let (code, stderr) = run(&["--jobs".as_ref(), "2".as_ref(), crate_dir.as_os_str()]);
    assert_eq!(code, Some(2), "{stderr}");
    assert!(stderr.contains("it requires --continue"), "{stderr}");
    for bad in ["0", "two", "-1"] {
        let (code, stderr) = run(&[
            "--continue".as_ref(),
            "--jobs".as_ref(),
            bad.as_ref(),
            crate_dir.as_os_str(),
        ]);
        assert_eq!(code, Some(2), "{bad}: {stderr}");
        assert!(
            stderr.contains("--jobs takes a positive thread count"),
            "{stderr}"
        );
    }
    let (code, stderr) = run(&[
        "--continue".as_ref(),
        "--jobs=2".as_ref(),
        "--jobs".as_ref(),
        "3".as_ref(),
        crate_dir.as_os_str(),
    ]);
    assert_eq!(code, Some(2), "{stderr}");
    assert!(
        stderr.contains("--jobs may be supplied at most once"),
        "{stderr}"
    );
    // A thread count changes no answer: the same set, the same result.
    let serial = run(&["--continue".as_ref(), crate_dir.as_os_str()]);
    let parallel = run(&[
        "--continue".as_ref(),
        "--jobs".as_ref(),
        "2".as_ref(),
        crate_dir.as_os_str(),
    ]);
    assert_eq!(parallel, serial);
}

/// Run `fln check-olean` with `args`, returning exit code, stdout and stderr.
fn check_olean_run(args: &[&std::ffi::OsStr]) -> (Option<i32>, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .arg("check-olean")
        .args(args)
        .output()
        .expect("run fln check-olean");
    (
        output.status.code(),
        String::from_utf8(output.stdout).expect("utf8 stdout"),
        String::from_utf8(output.stderr).expect("utf8 stderr"),
    )
}

/// `check-olean --continue ROOT...`: further roots join the module set, so a
/// library is checked together with the libraries it imports. Two paths are a
/// usage error without --continue; a module found under two roots, or a root
/// that is not a directory, is refused before anything is checked; and the
/// modules of every root reach the frontier.
#[test]
fn check_olean_continue_joins_module_set_roots() {
    let first = TempDir::new("roots-first");
    let second = TempDir::new("roots-second");
    for root in [&first.0, &second.0] {
        std::fs::create_dir_all(root.join("Shared")).unwrap();
        std::fs::write(root.join("Shared").join("Twice.olean"), b"not decoded").unwrap();
    }
    let (code, _, stderr) = check_olean_run(&[first.0.as_os_str(), second.0.as_os_str()]);
    assert_eq!(code, Some(2), "{stderr}");
    assert!(
        stderr.contains("several module-set roots with --continue"),
        "{stderr}"
    );
    let (code, _, stderr) = check_olean_run(&[
        "--continue".as_ref(),
        first.0.as_os_str(),
        second.0.as_os_str(),
    ]);
    assert_eq!(code, Some(1), "{stderr}");
    assert!(
        stderr.contains("module Shared.Twice is found under more than one root"),
        "{stderr}"
    );
    let file = first.0.join("Shared").join("Twice.olean");
    let (code, _, stderr) = check_olean_run(&[
        "--continue".as_ref(),
        second.0.as_os_str(),
        file.as_os_str(),
    ]);
    assert_eq!(code, Some(1), "{stderr}");
    assert!(stderr.contains("must be a real directory"), "{stderr}");

    // Distinct modules under two roots both reach the frontier. These bytes do
    // not decode, so each fails; what is checked is that the second root's
    // module is in the set at all.
    let other = TempDir::new("roots-other");
    std::fs::create_dir_all(other.0.join("Other")).unwrap();
    std::fs::write(other.0.join("Other").join("Once.olean"), b"not decoded").unwrap();
    let (code, stdout, stderr) = check_olean_run(&[
        "--continue".as_ref(),
        "--json".as_ref(),
        first.0.as_os_str(),
        other.0.as_os_str(),
    ]);
    assert_eq!(code, Some(1), "{stdout}{stderr}");
    assert!(stdout.contains("\"modules\":2"), "{stdout}");
    assert!(stdout.contains("\"module\":\"Shared.Twice\""), "{stdout}");
    assert!(stdout.contains("\"module\":\"Other.Once\""), "{stdout}");
}

/// The joined roots resolve imports across roots. `Init.Coe` imports
/// `Init.Prelude`: alone, its root fails with that import named; with
/// Prelude's root joined, both are checked and accepted. It needs the pinned
/// toolchain, and checking `Init.Prelude` in a debug build took 108 s, so it
/// runs on demand:
///
/// `cargo test -p fln-cli --test cli_personalities_and_verbs \
///   check_olean_continue_resolves_imports_across_roots -- --ignored --exact`
#[test]
#[ignore = "cost: checks Init.Prelude through the council; needs the pinned toolchain"]
fn check_olean_continue_resolves_imports_across_roots() {
    let library = std::env::var_os("ELAN_HOME")
        .map(std::path::PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| std::path::PathBuf::from(home).join(".elan"))
        })
        .map(|elan| {
            elan.join("toolchains")
                .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                .join("lib")
                .join("lean")
        })
        .filter(|library| library.join("Init").join("Coe.olean").is_file())
        .expect("the pinned toolchain library, with Init.Coe");
    let prelude = TempDir::new("roots-prelude");
    let coe = TempDir::new("roots-coe");
    // Each module is copied with its `.olean.server` and `.olean.private` parts.
    for (root, module) in [(&prelude.0, "Prelude"), (&coe.0, "Coe")] {
        std::fs::create_dir_all(root.join("Init")).unwrap();
        for part in ["olean", "olean.server", "olean.private"] {
            let file = format!("{module}.{part}");
            std::fs::copy(
                library.join("Init").join(&file),
                root.join("Init").join(&file),
            )
            .unwrap();
        }
    }
    let (code, stdout, stderr) =
        check_olean_run(&["--continue".as_ref(), "--json".as_ref(), coe.0.as_os_str()]);
    assert_eq!(code, Some(1), "{stdout}{stderr}");
    assert!(stdout.contains("\"failed\":1"), "{stdout}");
    assert!(stdout.contains("Init.Prelude"), "{stdout}");
    let (code, stdout, stderr) = check_olean_run(&[
        "--continue".as_ref(),
        "--json".as_ref(),
        coe.0.as_os_str(),
        prelude.0.as_os_str(),
    ]);
    assert_eq!(code, Some(0), "{stdout}{stderr}");
    assert!(stdout.contains("\"accepted\":2"), "{stdout}");
    assert!(stdout.contains("\"blocked\":0"), "{stdout}");
}

/// A3 criterion 2: the K2 line is tied to the engines the kernel crate exports, in
/// both directions, so doctor cannot claim or deny a second engine the code lacks.
#[test]
fn doctor_k2_line_follows_the_kernel_engine_list() {
    let crate_dir = fln_core::checked_manifest_dir!();
    let (code, stdout) = doctor_json(&crate_dir, None);
    assert!(code == 0 || code == 1, "{stdout}");
    let k2_row =
        "{\"subsystem\":\"kernel engine K2 (NbE accelerator)\",\"bead\":\"franken_lean-g3k\"}";
    let kernel_has_only_k1 = fln::EngineId::IMPLEMENTED
        .iter()
        .all(|engine| engine.is(fln::EngineId::K1));
    assert!(kernel_has_only_k1, "the kernel still implements only K1");
    assert_eq!(
        stdout.contains(k2_row),
        kernel_has_only_k1,
        "doctor lists K2 as not implemented exactly while the kernel lacks it: {stdout}"
    );
}

#[test]
fn doctor_refuses_unknown_arguments() {
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["doctor", "--all-systems-go"])
        .output()
        .expect("run doctor with a bogus flag");
    assert_eq!(output.status.code(), Some(2));
}

#[test]
fn multiplexer_diff_verb_routes_to_olean_diff() {
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["diff", "--help"])
        .output()
        .expect("run fln diff --help");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("Usage:"));
}

fn temp_file(text: &str) -> (TempDir, std::path::PathBuf) {
    let dir = TempDir::new("goals");
    let path = dir.0.join("goal_test.lean");
    std::fs::write(&path, text).unwrap();
    (dir, path)
}

#[test]
fn multiplexer_goals_verb_inspects_proof_goals() {
    let text = include_str!("../../../examples/native_goal_control.lean");
    let (_dir, file_path) = temp_file(text);
    let path_str = file_path.to_str().unwrap();

    // Test with PATH:LINE:COL
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .arg("goals")
        .arg(format!("{path_str}:7:3"))
        .output()
        .expect("run fln goals");
    assert!(
        output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("goal") || stdout.contains("⊢"), "{stdout}");

    // Test with --json and --line --col
    let json_output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["goals", "--json", "--line", "7", "--col", "3", path_str])
        .output()
        .expect("run fln goals --json");
    assert!(
        json_output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&json_output.stderr)
    );
    let json_stdout = String::from_utf8(json_output.stdout).expect("utf8 stdout");
    assert!(
        json_stdout.contains("\"schema\":\"fln.goals/1\""),
        "{json_stdout}"
    );
    assert!(json_stdout.contains("\"goals\""), "{json_stdout}");
}

#[test]
fn leanc_personality_respects_cli_transcripts() {
    // leanc --version
    let output = Command::new(env!("CARGO_BIN_EXE_leanc"))
        .arg("--version")
        .output()
        .expect("run leanc --version");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("leanc"));
    assert!(stdout.contains("4.32.0"));

    // leanc --help
    let output = Command::new(env!("CARGO_BIN_EXE_leanc"))
        .arg("--help")
        .output()
        .expect("run leanc --help");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("Usage: leanc"));

    // An option leanc does not define belongs to the C compiler, as at the pin
    // (whose leanc hands it to clang). So leanc's answer must be the host
    // compiler's own answer, for the census's probe string and for any other
    // string alike. This used to assert a message leanc made up for the probe
    // string only (bead fln-front-door-residuals-0f6x).
    for unknown in ["--fln-census-unknown", "--some-other-unknown-flag"] {
        let ours = Command::new(env!("CARGO_BIN_EXE_leanc"))
            .env_remove("LEAN_CC")
            .arg(unknown)
            .output()
            .expect("run leanc with an unknown option");
        match Command::new("cc").arg(unknown).output() {
            Ok(host) => {
                assert_eq!(ours.status.code(), host.status.code(), "{unknown}");
                assert_eq!(ours.stderr, host.stderr, "{unknown}");
                assert!(!ours.status.success(), "{unknown}");
            }
            Err(_) => {
                let stderr = String::from_utf8_lossy(&ours.stderr);
                assert_eq!(ours.status.code(), Some(1), "{unknown}");
                assert!(stderr.contains("is unavailable"), "{unknown}: {stderr}");
            }
        }
    }
}

#[test]
fn lake_personality_respects_cli_transcripts() {
    // lake (bare usage)
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .output()
        .expect("run lake");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("Lake version 5.0.0-src"));
    assert!(stdout.contains("COMMANDS:"));

    // lake --help
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .arg("--help")
        .output()
        .expect("run lake --help");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("Lake version 5.0.0-src"));

    // lake --version
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .arg("--version")
        .output()
        .expect("run lake --version");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("Lake version 5.0.0-src"));
    assert!(stdout.contains("4.32.0"));

    // lake help build
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["help", "build"])
        .output()
        .expect("run lake help build");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("Build targets"));

    // lake help query
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["help", "query"])
        .output()
        .expect("run lake help query");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("Build targets and output results"));

    // lake help env
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["help", "env"])
        .output()
        .expect("run lake help env");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("Execute a command in Lake's environment"));

    // lake --json help query
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--json", "help", "query"])
        .output()
        .expect("run lake --json help query");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("Build targets and output results"));

    // lake --fln-census-unknown help: the pin's exact words (see the table in
    // `lake_refuses_every_option_the_pin_does_not_define`).
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--fln-census-unknown", "help"])
        .output()
        .expect("run lake --fln-census-unknown help");
    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8(output.stderr).expect("utf8 stderr");
    assert_eq!(
        stderr,
        "error: unknown long option '--fln-census-unknown'\n"
    );
}

/// Bead `fln-front-door-residuals-0f6x`. `lake` used to give the pin's
/// unknown-option error only for the literal string the CLI census probes with,
/// and exit 0 for every other unknown option. The option set now comes from the
/// extracted census, so any string the pin does not define is refused.
///
/// Each row is the pinned `lake` v4.32.0's own first stderr line and exit code
/// for that argv, recorded on 2026-10-07. The last three rows are the other
/// direction: options the pin DOES define must not be refused, and a value the
/// pin attaches to an option must not be read as a command.
#[test]
fn lake_refuses_every_option_the_pin_does_not_define() {
    let rows: [(&[&str], &str); 9] = [
        (
            &["--fln-census-unknown", "help"],
            "error: unknown long option '--fln-census-unknown'",
        ),
        (&["--zzz=1", "help"], "error: unknown long option '--zzz'"),
        (&["--unknown"], "error: unknown long option '--unknown'"),
        (&["-Zfoo", "help"], "error: unknown short option '-Z'"),
        (&["help", "--zzz"], "error: unknown long option '--zzz'"),
        (&["build", "-Z"], "error: unknown short option '-Z'"),
        (&["-K", "a=b", "zzz"], "error: unknown command 'zzz'"),
        (
            &["--log-level", "info", "zzz"],
            "error: unknown command 'zzz'",
        ),
        (
            &["-q", "-v", "--wfail", "zzz"],
            "error: unknown command 'zzz'",
        ),
    ];
    for (argv, expected) in rows {
        let output = Command::new(env!("CARGO_BIN_EXE_lake"))
            .args(argv)
            .output()
            .expect("run lake");
        let stderr = String::from_utf8(output.stderr).expect("utf8 stderr");
        eprintln!(
            "lake {argv:?}: exit={:?} stderr={stderr:?}",
            output.status.code()
        );
        assert_eq!(output.status.code(), Some(1), "{argv:?}");
        assert_eq!(stderr.lines().next(), Some(expected), "{argv:?}");
        assert!(output.stdout.is_empty(), "{argv:?}");
    }
}

/// A command the pin has and this build does not is the typed not-implemented
/// exit. It used to exit 1 with "requires Lake workspace configuration", which
/// reads as the user's mistake.
#[test]
fn lake_commands_without_an_implementation_say_so() {
    for command in ["test", "query", "lint", "lean"] {
        let output = Command::new(env!("CARGO_BIN_EXE_lake"))
            .arg(command)
            .output()
            .expect("run lake");
        let stderr = String::from_utf8(output.stderr).expect("utf8 stderr");
        eprintln!(
            "lake {command}: exit={:?} stderr={stderr:?}",
            output.status.code()
        );
        assert_eq!(output.status.code(), Some(5), "{command}");
        assert!(
            stderr.starts_with(&format!("lake {command}: not implemented")),
            "{command}: {stderr}"
        );
    }
}

/// `fln why-trusts` stops at `--max-nodes`. A stopped walk has not seen the
/// closure, so "axioms: none" from it is not an answer: the exit must be the
/// inconclusive one. It used to be 0.
#[test]
fn a_why_trusts_walk_cut_short_is_inconclusive_not_an_answer() {
    let temp = TempDir::new("why-trusts-limit");
    let source = temp.0.join("Main.lean");
    let snapshot = temp.0.join("main.olean");
    std::fs::write(
        &source,
        "def base : Nat := 6 * 7\ndef answer : Nat := base + 1\n#eval answer\n",
    )
    .unwrap();
    let run = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--emit-olean-snapshot"])
        .arg(&snapshot)
        .arg(&source)
        .output()
        .expect("run fln run");
    assert!(run.status.success(), "{run:?}");

    let complete = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["why-trusts", "answer"])
        .arg(&snapshot)
        .output()
        .expect("run fln why-trusts");
    let complete_stdout = String::from_utf8(complete.stdout).expect("utf8 stdout");
    eprintln!(
        "complete: exit={:?} {complete_stdout:?}",
        complete.status.code()
    );
    assert_eq!(complete.status.code(), Some(0), "{complete_stdout}");
    let complete_axioms = complete_stdout
        .lines()
        .find_map(|line| line.strip_prefix("axioms: "))
        .unwrap_or_else(|| panic!("a complete walk states its axioms: {complete_stdout}"));
    assert!(!complete_stdout.contains("(partial)"), "{complete_stdout}");
    assert!(!complete_stdout.contains("truncated"), "{complete_stdout}");

    let cut = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["why-trusts", "--max-nodes", "1", "answer"])
        .arg(&snapshot)
        .output()
        .expect("run fln why-trusts --max-nodes 1");
    let cut_stdout = String::from_utf8(cut.stdout).expect("utf8 stdout");
    let cut_stderr = String::from_utf8(cut.stderr).expect("utf8 stderr");
    eprintln!(
        "cut: exit={:?} {cut_stdout:?} {cut_stderr:?}",
        cut.status.code()
    );
    assert_eq!(cut.status.code(), Some(3), "{cut_stdout}");
    let cut_axioms = cut_stdout
        .lines()
        .find_map(|line| line.strip_prefix("axioms (partial): "))
        .unwrap_or_else(|| panic!("a cut walk labels its axioms partial: {cut_stdout}"));
    assert!(
        cut_stdout.contains("truncated by --max-nodes"),
        "{cut_stdout}"
    );
    assert!(cut_stderr.contains("inconclusive"), "{cut_stderr}");
    // Why the exit code matters: on this very snapshot the complete walk
    // reaches an axiom and the one-node walk reaches none. Exit 0 with
    // "axioms: none" was a false answer to a trust question.
    assert_ne!(complete_axioms, "none", "{complete_stdout}");
    assert_eq!(cut_axioms, "none", "{cut_stdout}");
}

#[test]
fn multiplexer_verify_capsule_help_and_errors() {
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["verify-capsule", "--help"])
        .output()
        .expect("run fln verify-capsule --help");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("fln verify-capsule"));
    assert!(stdout.contains(".flnpack"));

    // Missing file
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["verify-capsule", "nonexistent_file_12345.flnpack"])
        .output()
        .expect("run fln verify-capsule nonexistent");
    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8(output.stderr).expect("utf8 stderr");
    assert!(stderr.contains("cannot open"));

    // Missing file with --json
    let json_output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["verify-capsule", "--json", "nonexistent_file_12345.flnpack"])
        .output()
        .expect("run fln verify-capsule --json nonexistent");
    assert_eq!(json_output.status.code(), Some(1));
    let json_stderr = String::from_utf8(json_output.stderr).expect("utf8 stderr");
    assert!(json_stderr.contains("\"schema\":\"fln.verify-capsule/2\""));
    assert!(json_stderr.contains("\"outcome\":\"error\""));
}

#[test]
fn multiplexer_verify_capsule_verifies_valid_cartridge() {
    use fln::{ContentRoot, EpochId};
    use fln_hash::cartridge::{
        CartridgeBuilderV1, CartridgeObjectKindV1, ObjectPortabilityV1, ObjectRequirementV1,
    };

    let epoch = EpochId::new(4_032_000);
    let env_root = ContentRoot::new([42; 32]);
    let mut builder = CartridgeBuilderV1::new(epoch, env_root)
        .with_chunk_size(1024)
        .expect("chunk size");
    let receipt = builder.add_object(
        CartridgeObjectKindV1::Receipt,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        b"receipt-data".to_vec(),
    );
    builder.add_root_receipt(receipt);
    builder.add_object(
        CartridgeObjectKindV1::Declaration,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        b"def test_const : Nat := 42".to_vec(),
    );
    let archive = builder.build().expect("build archive");
    let bytes = archive.to_canonical_bytes().expect("encode archive");

    let temp_dir_guard = TempDir::new("capsule");
    let temp_dir = temp_dir_guard.0.clone();
    let capsule_path = temp_dir.join("test.flnpack");
    std::fs::write(&capsule_path, &bytes).unwrap();

    // Human output
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["verify-capsule", capsule_path.to_str().unwrap()])
        .output()
        .expect("run fln verify-capsule");
    assert!(
        output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("fln verify-capsule: integrity verified for capsule at"));
    assert!(stdout.contains("not replayed through a checker"));
    assert!(stdout.contains("capsule integrity verification passed."));

    // JSON output
    let json_output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["verify-capsule", "--json", capsule_path.to_str().unwrap()])
        .output()
        .expect("run fln verify-capsule --json");
    assert!(
        json_output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&json_output.stderr)
    );
    let json_stdout = String::from_utf8(json_output.stdout).expect("utf8 stdout");
    assert!(json_stdout.contains("\"schema\":\"fln.verify-capsule/2\""));
    assert!(json_stdout.contains("\"outcome\":\"complete\""));
    assert!(json_stdout.contains("\"status\":\"integrity_verified\""));
    assert!(json_stdout.contains("\"transport_state\":\"complete\""));
    // A decoded certificate is not a replayed one; the report must say so.
    assert!(json_stdout.contains("\"certificate_replay\":\"not_implemented\""));
    assert!(!json_stdout.contains("certificates_verified"));
}

#[test]
fn leanc_personality_print_flags_support() {
    let output = Command::new(env!("CARGO_BIN_EXE_leanc"))
        .env("LEAN_SYSROOT", "/custom/lean/sysroot")
        .arg("--print-cflags")
        .output()
        .expect("run leanc --print-cflags");
    assert!(
        output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(
        stdout.contains("-I /custom/lean/sysroot/include"),
        "stdout: {stdout}"
    );

    let output_ld = Command::new(env!("CARGO_BIN_EXE_leanc"))
        .env("LEAN_SYSROOT", "/custom/lean/sysroot")
        .arg("--print-ldflags")
        .output()
        .expect("run leanc --print-ldflags");
    assert!(
        output_ld.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&output_ld.stderr)
    );
    let stdout_ld = String::from_utf8(output_ld.stdout).expect("utf8 stdout");
    assert!(
        stdout_ld.contains("-I /custom/lean/sysroot/include"),
        "stdout: {stdout_ld}"
    );
    assert!(
        stdout_ld.contains("-L /custom/lean/sysroot/lib/lean"),
        "stdout: {stdout_ld}"
    );
}

#[test]
fn lake_personality_package_lifecycle_init_new_and_clean() {
    let temp_parent_guard = TempDir::new("lake-cli");
    let temp_parent = temp_parent_guard.0.clone();

    // 1. lake clean in empty dir fails with error code 1
    let empty_dir = temp_parent.join("empty");
    std::fs::create_dir_all(&empty_dir).unwrap();
    let clean_fail = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", empty_dir.to_str().unwrap(), "clean"])
        .output()
        .expect("run lake clean in empty dir");
    assert_eq!(clean_fail.status.code(), Some(1));
    let clean_fail_stderr = String::from_utf8(clean_fail.stderr).expect("utf8 stderr");
    assert!(clean_fail_stderr.contains("error: no such file or directory"));

    // 2. lake new my_app in temp_parent
    let new_output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", temp_parent.to_str().unwrap(), "new", "my_app"])
        .output()
        .expect("run lake new my_app");
    assert!(
        new_output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&new_output.stderr)
    );

    let pkg_dir = temp_parent.join("my_app");
    assert!(pkg_dir.join("lakefile.toml").exists());
    assert!(pkg_dir.join("lean-toolchain").exists());
    assert!(pkg_dir.join("Main.lean").exists());
    assert!(pkg_dir.join("MyApp.lean").exists());

    // 3. Create .lake/build and lake clean
    let build_dir = pkg_dir.join(".lake").join("build");
    std::fs::create_dir_all(&build_dir).unwrap();
    std::fs::write(build_dir.join("temp.olean"), b"test").unwrap();
    assert!(build_dir.exists());

    let clean_output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", pkg_dir.to_str().unwrap(), "clean"])
        .output()
        .expect("run lake clean in valid pkg");
    assert!(
        clean_output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&clean_output.stderr)
    );
    assert!(!build_dir.exists());

    // 4. lake clean with --json
    let clean_json = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", pkg_dir.to_str().unwrap(), "--json", "clean"])
        .output()
        .expect("run lake clean --json");
    assert!(clean_json.status.success());
    let clean_json_stdout = String::from_utf8(clean_json.stdout).expect("utf8 stdout");
    assert!(clean_json_stdout.contains("\"schema\":\"fln.lake-clean/1\""));
    assert!(clean_json_stdout.contains("\"status\":\"success\""));

    // 5. lake init in another dir
    let init_dir = temp_parent.join("init_pkg");
    std::fs::create_dir_all(&init_dir).unwrap();
    let init_output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args([
            "--dir",
            init_dir.to_str().unwrap(),
            "--json",
            "init",
            "cool_math",
        ])
        .output()
        .expect("run lake init --json");
    assert!(init_output.status.success());
    let init_json_stdout = String::from_utf8(init_output.stdout).expect("utf8 stdout");
    assert!(init_json_stdout.contains("\"schema\":\"fln.lake-init/1\""));
    assert!(init_json_stdout.contains("\"package\":\"cool_math\""));
    assert!(init_dir.join("lakefile.toml").exists());
    assert!(init_dir.join("CoolMath.lean").exists());
}

#[test]
fn lake_personality_update_env_and_exe() {
    let temp_parent_guard = TempDir::new("lake-update");
    let temp_parent = temp_parent_guard.0.clone();

    let pkg_dir = temp_parent.join("my_project");
    let toml_content = r#"
name = "my_project"
version = "0.1.0"
defaultTargets = ["my_project"]

[[require]]
name = "batteries"
git = "https://github.com/leanprover-community/batteries.git"
rev = "v4.32.0"
"#;
    std::fs::create_dir_all(&pkg_dir).unwrap();
    std::fs::write(pkg_dir.join("lakefile.toml"), toml_content).unwrap();

    // 1. lake update with a requirement: nothing can fetch it, so the answer
    // is the typed not-implemented exit and NO manifest. This step used to
    // assert exit 0 and a manifest naming "batteries", which the binary wrote
    // by copying the requested rev (bead fln-front-door-residuals-0f6x).
    let update_output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", pkg_dir.to_str().unwrap(), "update"])
        .output()
        .expect("run lake update");
    let update_stderr = String::from_utf8_lossy(&update_output.stderr);
    assert_eq!(
        update_output.status.code(),
        Some(5),
        "stderr: {update_stderr}"
    );
    assert!(update_output.stdout.is_empty());
    assert!(
        update_stderr.contains("lake update: not implemented")
            && update_stderr.contains("batteries")
            && update_stderr.contains("no manifest was written"),
        "{update_stderr}"
    );
    assert!(!pkg_dir.join("lake-manifest.json").exists());

    // 2. lake update --json: the same refusal, typed.
    let update_json = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", pkg_dir.to_str().unwrap(), "--json", "update"])
        .output()
        .expect("run lake update --json");
    assert_eq!(update_json.status.code(), Some(5));
    let update_json_stderr = String::from_utf8(update_json.stderr).expect("utf8 stderr");
    assert!(update_json_stderr.contains("\"status\":\"not_implemented\""));
    assert!(update_json_stderr.contains("\"command\":\"lake update\""));
    assert!(!pkg_dir.join("lake-manifest.json").exists());

    // 2b. With no requirements there is nothing to resolve: exit 0 and a
    // manifest with an empty package list.
    let bare_dir = temp_parent.join("bare_project");
    std::fs::create_dir_all(&bare_dir).unwrap();
    std::fs::write(
        bare_dir.join("lakefile.toml"),
        "name = \"bare_project\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    let bare_update = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", bare_dir.to_str().unwrap(), "--json", "update"])
        .output()
        .expect("run lake update without requirements");
    assert!(bare_update.status.success(), "{bare_update:?}");
    let bare_stdout = String::from_utf8(bare_update.stdout).expect("utf8 stdout");
    assert!(bare_stdout.contains("\"schema\":\"fln.lake-update/1\""));
    assert!(bare_stdout.contains("\"packages_count\":0"));
    let manifest_content = std::fs::read_to_string(bare_dir.join("lake-manifest.json")).unwrap();
    assert!(manifest_content.contains("\"name\": \"bare_project\""));

    // 3. lake env. The sysroot is where the toolchain is installed. A test
    // binary is in no toolchain layout, so with LEAN_SYSROOT unset there is
    // nothing to report: it used to print `LEAN_SYSROOT=/usr/local` and exit 0.
    let env_unknown = Command::new(env!("CARGO_BIN_EXE_lake"))
        .arg("env")
        .env_remove("LEAN_SYSROOT")
        .output()
        .expect("run lake env");
    assert_eq!(env_unknown.status.code(), Some(5), "{env_unknown:?}");
    assert!(env_unknown.stdout.is_empty());
    let env_unknown_stderr = String::from_utf8(env_unknown.stderr).expect("utf8 stderr");
    assert!(env_unknown_stderr.starts_with("lake env: not implemented: "));
    assert!(!env_unknown_stderr.contains("/usr/local"));
    // A command is not run in an invented environment either.
    let env_unknown_run = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["env", "echo", "must_not_run"])
        .env_remove("LEAN_SYSROOT")
        .output()
        .expect("run lake env echo without a sysroot");
    assert_eq!(env_unknown_run.status.code(), Some(5));
    assert!(env_unknown_run.stdout.is_empty());

    let sysroot = temp_parent.join("sysroot");
    let env_output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .arg("env")
        .env("LEAN_SYSROOT", &sysroot)
        .output()
        .expect("run lake env");
    assert!(env_output.status.success());
    let env_stdout = String::from_utf8(env_output.stdout).expect("utf8 stdout");
    assert!(env_stdout.contains(&format!("LEAN_SYSROOT={}\n", sysroot.display())));
    assert!(env_stdout.contains(&format!(
        "LEAN_PATH={}\n",
        sysroot.join("lib").join("lean").display()
    )));
    assert!(env_stdout.contains("ELAN_TOOLCHAIN="));

    // 4. lake env echo hello
    let env_echo = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["env", "echo", "testing_lake_env_propagation"])
        .env("LEAN_SYSROOT", &sysroot)
        .output()
        .expect("run lake env echo");
    assert!(env_echo.status.success());
    let env_echo_stdout = String::from_utf8(env_echo.stdout).expect("utf8 stdout");
    assert!(env_echo_stdout.contains("testing_lake_env_propagation"));

    // 5. lake env with nonexistent command exits 255
    let env_missing = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["env", "nonexistent_command_12345_xyz"])
        .env("LEAN_SYSROOT", &sysroot)
        .output()
        .expect("run lake env missing");
    assert_eq!(env_missing.status.code(), Some(255));
    let env_missing_stderr = String::from_utf8(env_missing.stderr).expect("utf8 stderr");
    assert!(env_missing_stderr.contains("could not execute external process"));

    // 6. lake exe without target exits 1 with "missing executable target"
    let exe_no_target = Command::new(env!("CARGO_BIN_EXE_lake"))
        .arg("exe")
        .output()
        .expect("run lake exe without target");
    assert_eq!(exe_no_target.status.code(), Some(1));
    let exe_no_target_stderr = String::from_utf8(exe_no_target.stderr).expect("utf8 stderr");
    assert!(exe_no_target_stderr.contains("error: missing executable target"));

    // 7. lake exe with target in empty directory exits 1 with "no such file or directory"
    let empty_dir = temp_parent.join("empty");
    std::fs::create_dir_all(&empty_dir).unwrap();
    let exe_empty = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", empty_dir.to_str().unwrap(), "exe", "my_target"])
        .output()
        .expect("run lake exe in empty dir");
    assert_eq!(exe_empty.status.code(), Some(1));
    let exe_empty_stderr = String::from_utf8(exe_empty.stderr).expect("utf8 stderr");
    assert!(exe_empty_stderr.contains("error: no such file or directory"));
}

#[test]
fn lake_personality_build_and_check_build() {
    let temp_parent_guard = TempDir::new("lake-build");
    let temp_parent = temp_parent_guard.0.clone();

    let pkg_dir = temp_parent.join("calc_proj");
    std::fs::create_dir_all(&pkg_dir).unwrap();
    // 1. Scaffold package using lake init
    let init_res = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", pkg_dir.to_str().unwrap(), "init", "calc_proj"])
        .output()
        .expect("run lake init");
    assert!(init_res.status.success());

    // 2. lake check-build
    let check_res = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", pkg_dir.to_str().unwrap(), "check-build"])
        .output()
        .expect("run lake check-build");
    assert!(check_res.status.success());
    let check_stdout = String::from_utf8(check_res.stdout).expect("utf8 stdout");
    assert!(check_stdout.is_empty());

    // 3. lake check-build --json
    let check_json = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", pkg_dir.to_str().unwrap(), "--json", "check-build"])
        .output()
        .expect("run lake check-build --json");
    assert!(check_json.status.success());
    let check_json_stdout = String::from_utf8(check_json.stdout).expect("utf8 stdout");
    assert!(check_json_stdout.contains("\"schema\":\"fln.lake-check-build/1\""));
    assert!(check_json_stdout.contains("\"package\":\"calc_proj\""));

    // 4. lake build (initial)
    let build1 = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", pkg_dir.to_str().unwrap(), "build"])
        .output()
        .expect("run lake build 1");
    assert_eq!(build1.status.code(), Some(1));
    let build1_stdout = String::from_utf8(build1.stdout).expect("utf8 stdout");
    assert!(build1_stdout.is_empty());
    assert!(String::from_utf8_lossy(&build1.stderr).contains("unavailable"));
    assert!(!pkg_dir.join(".lake").exists());

    // 5. lake build (cached)
    let build2 = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", pkg_dir.to_str().unwrap(), "build"])
        .output()
        .expect("run lake build 2");
    assert_eq!(build2.status.code(), Some(1));
    let build2_stdout = String::from_utf8(build2.stdout).expect("utf8 stdout");
    assert!(build2_stdout.is_empty());

    // 6. lake build --json
    let build_json = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", pkg_dir.to_str().unwrap(), "--json", "build"])
        .output()
        .expect("run lake build --json");
    assert_eq!(build_json.status.code(), Some(1));
    let build_json_stdout = String::from_utf8(build_json.stdout).expect("utf8 stdout");
    assert!(build_json_stdout.is_empty());
    let build_json_stderr = String::from_utf8(build_json.stderr).unwrap();
    assert!(build_json_stderr.contains("\"schema\":\"fln.lake-build/2\""));
    assert!(build_json_stderr.contains("\"status\":\"unsupported\""));
    assert!(!build_json_stderr.contains("targets_cached"));

    // 7. lake build in unconfigured dir exits 1 with Reference error
    let empty_dir = temp_parent.join("empty_build");
    std::fs::create_dir_all(&empty_dir).unwrap();
    let build_empty = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", empty_dir.to_str().unwrap(), "build"])
        .output()
        .expect("run lake build empty");
    assert_eq!(build_empty.status.code(), Some(1));
    let build_empty_stderr = String::from_utf8(build_empty.stderr).expect("utf8 stderr");
    assert!(build_empty_stderr.contains("error: no such file or directory"));
}

#[test]
fn fln_build_explain_refuses_without_recorded_provenance() {
    let temp_parent_guard = TempDir::new("build-explain");
    let temp_parent = temp_parent_guard.0.clone();

    let pkg_dir = temp_parent.join("geom_pkg");
    std::fs::create_dir_all(&pkg_dir).unwrap();
    let init_res = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", pkg_dir.to_str().unwrap(), "init", "geom_pkg"])
        .output()
        .expect("init geom_pkg");
    assert!(init_res.status.success());

    // No build has run: there is no evidence supporting either decision.
    let explain_init = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["build", "explain", "--dir", pkg_dir.to_str().unwrap()])
        .output()
        .expect("run fln build explain initial");
    assert_eq!(explain_init.status.code(), Some(5));
    let explain_init_stdout = String::from_utf8(explain_init.stdout).expect("utf8 stdout");
    assert!(explain_init_stdout.is_empty());
    assert!(String::from_utf8_lossy(&explain_init.stderr).contains("provenance is unavailable"));

    // 2. fln build explain --json
    let explain_json = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args([
            "build",
            "explain",
            "--json",
            "--dir",
            pkg_dir.to_str().unwrap(),
        ])
        .output()
        .expect("run fln build explain --json");
    assert_eq!(explain_json.status.code(), Some(5));
    let explain_json_stdout = String::from_utf8(explain_json.stdout).expect("utf8 stdout");
    assert!(explain_json_stdout.is_empty());
    let explain_json_stderr = String::from_utf8(explain_json.stderr).unwrap();
    assert!(explain_json_stderr.contains("\"schema\":\"fln.build-explain/2\""));
    assert!(explain_json_stderr.contains("\"status\":\"unsupported\""));
    assert!(!explain_json_stderr.contains("cache_outcome"));

    // 3. Build package
    Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", pkg_dir.to_str().unwrap(), "build"])
        .output()
        .expect("lake build");

    // A failed build does not create evidence for a subsequent cache hit.
    let explain_cached = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["build", "explain", "--dir", pkg_dir.to_str().unwrap()])
        .output()
        .expect("run fln build explain cached");
    assert_eq!(explain_cached.status.code(), Some(5));
    let explain_cached_stdout = String::from_utf8(explain_cached.stdout).expect("utf8 stdout");
    assert!(explain_cached_stdout.is_empty());

    // 5. Touch source with internal proof update
    let src = pkg_dir.join("GeomPkg.lean");
    std::fs::write(&src, "def hello := \"world internal update\"\n").unwrap();

    // Changing source cannot establish early cutoff without a prior record.
    let explain_sound = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["build", "explain", "--dir", pkg_dir.to_str().unwrap()])
        .output()
        .expect("run fln build explain sound");
    assert_eq!(explain_sound.status.code(), Some(5));
    let explain_sound_stdout = String::from_utf8(explain_sound.stdout).expect("utf8 stdout");
    assert!(explain_sound_stdout.is_empty());

    // 5b. fln build explain with --faithful-invalidation
    let explain_faithful = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args([
            "build",
            "explain",
            "--faithful-invalidation",
            "--dir",
            pkg_dir.to_str().unwrap(),
        ])
        .output()
        .expect("run fln build explain faithful");
    assert_eq!(explain_faithful.status.code(), Some(5));
    let explain_faithful_stdout = String::from_utf8(explain_faithful.stdout).expect("utf8 stdout");
    assert!(explain_faithful_stdout.is_empty());
    assert!(
        String::from_utf8_lossy(&explain_faithful.stderr).contains("provenance is unavailable")
    );
    assert!(!pkg_dir.join(".lake").exists());
}

// ---- olean verify-rebuild over module-system chains ------------------------

/// The parts of a module image, in load order, as `fln` names them.
const CHAIN_PARTS: [&str; 3] = [".olean", ".olean.server", ".olean.private"];

/// One part of the committed `prelude.olean` chain. Its three files are the
/// pinned v4.32.0 stdlib's `Init/Prelude.olean`, `.olean.server` and
/// `.olean.private`, byte for byte (held against the installed pin by
/// `olean_verify_rebuild_chain_fixture_is_the_pinned_init_prelude`), so these
/// cells run on real Reference output without needing the pin installed.
fn prelude_chain_part(part: &str) -> std::path::PathBuf {
    let suffix = part.strip_prefix(".olean").expect("a module part suffix");
    fln_core::checked_workspace_root!()
        .join("crates/fln-conformance/fixtures/tag_attributes")
        .join(format!("prelude.olean{suffix}"))
}

/// Copy the chain's `parts` into `dir` under the module stem `Prelude`.
fn copy_prelude_chain(dir: &std::path::Path, parts: &[&str]) {
    for part in parts {
        let suffix = part.strip_prefix(".olean").expect("a module part suffix");
        std::fs::copy(
            prelude_chain_part(part),
            dir.join(format!("Prelude.olean{suffix}")),
        )
        .expect("copy a pinned chain part");
    }
}

/// Run `fln olean verify-rebuild` with `args`.
fn verify_rebuild_run(args: &[&std::ffi::OsStr]) -> (Option<i32>, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["olean", "verify-rebuild"])
        .args(args)
        .output()
        .expect("run fln olean verify-rebuild");
    (
        output.status.code(),
        String::from_utf8(output.stdout).expect("utf8 stdout"),
        String::from_utf8(output.stderr).expect("utf8 stderr"),
    )
}

/// The robot row of `part`, from its opening brace to the next row or the end.
fn chain_row<'a>(robot: &'a str, part: &str) -> &'a str {
    let anchor = format!("{{\"part\":\"{part}\",");
    let start = robot
        .find(&anchor)
        .unwrap_or_else(|| panic!("no {part} row in {robot}"));
    let rest = &robot[start + anchor.len()..];
    &rest[..rest.find("{\"part\":").unwrap_or(rest.len())]
}

/// The unsigned integer member `key` of a robot row.
fn row_u64(row: &str, key: &str) -> u64 {
    let needle = format!("\"{key}\":");
    let at = row
        .find(&needle)
        .unwrap_or_else(|| panic!("no {key} in {row}"))
        + needle.len();
    row[at..]
        .chars()
        .take_while(char::is_ascii_digit)
        .collect::<String>()
        .parse()
        .unwrap_or_else(|_| panic!("{key} is not an unsigned integer in {row}"))
}

/// A real module-system chain verifies end to end through the binary, from
/// whichever part PATH names: every part rebuilt byte-identically, reported
/// per part in load order, with the companions really crossing into their
/// predecessors. Before the chain door, the two companion PATHs were refused
/// as `PtrOutOfBounds` and the exported PATH reported one part.
#[test]
fn olean_verify_rebuild_verifies_a_real_module_chain_from_any_part() {
    let sizes = CHAIN_PARTS.map(|part| {
        std::fs::metadata(prelude_chain_part(part))
            .expect("pinned chain part")
            .len()
    });
    let mut robots = Vec::new();
    for part in CHAIN_PARTS {
        let path = prelude_chain_part(part);
        let (code, robot, stderr) = verify_rebuild_run(&["--json".as_ref(), path.as_os_str()]);
        assert_eq!(code, Some(0), "{part}: {robot}{stderr}");
        assert!(stderr.is_empty(), "{stderr}");
        assert!(
            robot.starts_with(
                "{\"schema\":\"fln.olean-rebuild-chain/1\",\"outcome\":\"complete\",\"parts\":3,"
            ),
            "{robot}"
        );
        assert_eq!(
            row_u64(&robot[..robot.find("\"rows\":").expect("rows")], "bytes"),
            sizes.iter().sum::<u64>(),
            "the chain total is every part's bytes"
        );
        let mut previous = 0;
        for (index, name) in CHAIN_PARTS.iter().enumerate() {
            let at = robot
                .find(&format!("{{\"part\":\"{name}\","))
                .unwrap_or_else(|| panic!("no {name} row in {robot}"));
            assert!(at > previous, "rows are in load order: {robot}");
            previous = at;
            let row = chain_row(&robot, name);
            assert!(row.contains("\"byteIdentity\":true"), "{row}");
            assert!(row.contains("\"findings\":0"), "{row}");
            assert_eq!(row_u64(row, "bytes"), sizes[index], "{name} bytes");
            assert!(row_u64(row, "objects") > 0, "{row}");
            // Anti-vacuity: the exported part is standalone and each companion
            // really holds pointers into the parts before it, so the
            // cross-part rebuild is what was measured.
            let crossing = row_u64(row, "dependencyPointers");
            if index == 0 {
                assert_eq!(crossing, 0, "{row}");
            } else {
                assert!(
                    crossing > 0,
                    "{name} never crossed into a predecessor: {row}"
                );
            }
        }
        robots.push(robot);
    }
    assert!(
        robots.iter().all(|robot| *robot == robots[0]),
        "every part of one chain yields the same report"
    );

    let server = prelude_chain_part(".olean.server");
    let (code, human, stderr) = verify_rebuild_run(&[server.as_os_str()]);
    assert_eq!(code, Some(0), "{human}{stderr}");
    assert!(stderr.is_empty(), "{stderr}");
    assert!(human.starts_with(
        "pinned .olean rebuild audit: complete\n\
         module-system chain: 3 parts (.olean, .olean.server, .olean.private), \
         each rebuilt against the parts loaded before it\n"
    ));
    assert!(human.contains(&format!("bytes: {}\n", sizes.iter().sum::<u64>())));
    assert!(human.contains("byte identity: exact\n"));
    assert!(human.contains("findings: 0\n"));
    for (part, size) in CHAIN_PARTS.iter().zip(sizes) {
        assert!(
            human.contains(&format!("part {part}: {size} bytes, byte identity exact, ")),
            "{human}"
        );
    }
}

/// A one-byte corruption planted in a companion is refused typed and named:
/// the refusal is that part's, never another's. The private-part plant lands
/// in a pointer word that crosses into the exported part, which the bytes
/// themselves are checked to confirm before planting. The uncorrupted copy in
/// the same layout is the control.
#[test]
fn olean_verify_rebuild_names_the_corrupted_companion() {
    let control = TempDir::new("rebuild-control");
    copy_prelude_chain(&control.0, &CHAIN_PARTS);
    let (code, robot, stderr) = verify_rebuild_run(&[
        "--json".as_ref(),
        control.0.join("Prelude.olean").as_os_str(),
    ]);
    assert_eq!(
        code,
        Some(0),
        "the unplanted copy verifies: {robot}{stderr}"
    );

    let header = fln_olean::format::OLEAN_HEADER_SIZE;
    let base_field = fln_olean::format::OLEAN_HEADER_FIELDS
        .iter()
        .find(|field| field.name == "base_addr")
        .expect("generated base_addr field");
    let word = |bytes: &[u8], at: usize| {
        u64::from_le_bytes(bytes[at..at + 8].try_into().expect("an 8-byte word"))
    };
    let exported = std::fs::read(prelude_chain_part(".olean")).expect("exported part");
    let exported_base = word(&exported, base_field.offset);
    let mut private = std::fs::read(prelude_chain_part(".olean.private")).expect("private part");
    // The first object after the root slot is a persistent constructor with
    // at least one field, and that field points into the exported part.
    let object = header + 8;
    let object_header = word(&private, object);
    let packed = (object_header >> 32) as u32;
    assert_eq!(object_header & 0xffff_ffff, 0, "a persistent header");
    assert!(
        (packed >> 24) as u8 <= fln_rt::abi::TAG_MAX_CTOR_TAG,
        "a constructor"
    );
    assert!((packed >> 16) & 0xff >= 1, "with a field");
    let field = object + 8;
    let pointer = word(&private, field);
    assert_eq!(pointer & 7, 0, "an aligned pointer word");
    assert!(
        (exported_base..exported_base + exported.len() as u64).contains(&pointer),
        "the field crosses into the exported part: {pointer:#x}"
    );
    private[field] ^= 0x04;

    let planted = TempDir::new("rebuild-private-flip");
    copy_prelude_chain(&planted.0, &[".olean", ".olean.server"]);
    std::fs::write(planted.0.join("Prelude.olean.private"), &private).expect("plant");
    for part in CHAIN_PARTS {
        let suffix = part.strip_prefix(".olean").expect("suffix");
        let path = planted.0.join(format!("Prelude.olean{suffix}"));
        let (code, stdout, robot) = verify_rebuild_run(&["--json".as_ref(), path.as_os_str()]);
        assert_eq!(code, Some(1), "{stdout}{robot}");
        assert!(stdout.is_empty(), "{stdout}");
        assert!(
            robot.starts_with(
                "{\"schema\":\"fln.olean-rebuild-chain/1\",\"outcome\":\"error\",\
                 \"class\":\"rebuild\",\"part\":\".olean.private\","
            ),
            "{robot}"
        );
        assert!(robot.contains("not 8-byte aligned"), "{robot}");
    }
    let (code, stdout, human) = verify_rebuild_run(&[planted.0.join("Prelude.olean").as_os_str()]);
    assert_eq!(code, Some(1), "{stdout}{human}");
    assert!(
        human.starts_with("fln olean verify-rebuild: rebuild: .olean.private rebuild: pointer "),
        "{human}"
    );

    // A plant in the server part moves the attribution with it, and the
    // intact private part behind it is not blamed.
    let original_server = std::fs::read(prelude_chain_part(".olean.server")).expect("server part");
    let mut server = original_server.clone();
    server[0] ^= u8::MAX;
    let planted = TempDir::new("rebuild-server-flip");
    copy_prelude_chain(&planted.0, &[".olean", ".olean.private"]);
    std::fs::write(planted.0.join("Prelude.olean.server"), &server).expect("plant");
    let path = planted.0.join("Prelude.olean.private");
    let (code, stdout, robot) = verify_rebuild_run(&["--json".as_ref(), path.as_os_str()]);
    assert_eq!(code, Some(1), "{stdout}{robot}");
    assert!(
        robot.contains("\"class\":\"rebuild\",\"part\":\".olean.server\","),
        "{robot}"
    );
    assert!(robot.contains("bad magic"), "{robot}");

    // A nonzero byte in a companion's inter-object padding parses cleanly and
    // copies through, so only the rebuild's padding audit sees it: a typed
    // `finding` naming that part. The first server object is a string whose
    // payload ends short of the next 8-byte boundary, checked before planting.
    let mut server = original_server;
    let string = header + 8;
    assert_eq!(
        (word(&server, string) >> 56) as u8,
        fln_rt::abi::TAG_STRING,
        "a string object"
    );
    let capacity = usize::try_from(word(&server, string + 16)).expect("capacity");
    let pad = string + 32 + capacity;
    assert!(
        !pad.is_multiple_of(8) && server[pad] == 0,
        "zero padding follows the string"
    );
    server[pad] = 0x5a;
    let planted = TempDir::new("rebuild-server-padding");
    copy_prelude_chain(&planted.0, &[".olean", ".olean.private"]);
    std::fs::write(planted.0.join("Prelude.olean.server"), &server).expect("plant");
    let path = planted.0.join("Prelude.olean");
    let (code, stdout, robot) = verify_rebuild_run(&["--json".as_ref(), path.as_os_str()]);
    assert_eq!(code, Some(1), "{stdout}{robot}");
    assert!(
        robot.contains("\"class\":\"finding\",\"part\":\".olean.server\","),
        "{robot}"
    );
    assert!(robot.contains("nonzero padding: 1 of"), "{robot}");
}

/// A part whose predecessor is absent is refused typed, naming the absent
/// part, from every PATH in the chain. Absent TRAILING parts are not a gap:
/// what remains is a load-order prefix, verified as such.
#[test]
fn olean_verify_rebuild_refuses_a_part_without_its_predecessor() {
    let no_exported = TempDir::new("rebuild-no-exported");
    copy_prelude_chain(&no_exported.0, &[".olean.server", ".olean.private"]);
    let no_server = TempDir::new("rebuild-no-server");
    copy_prelude_chain(&no_server.0, &[".olean", ".olean.private"]);
    for (dir, paths, missing) in [
        (&no_exported, [".olean.server", ".olean.private"], ".olean"),
        (&no_server, [".olean", ".olean.private"], ".olean.server"),
    ] {
        for part in paths {
            let suffix = part.strip_prefix(".olean").expect("suffix");
            let path = dir.0.join(format!("Prelude.olean{suffix}"));
            let (code, stdout, robot) = verify_rebuild_run(&["--json".as_ref(), path.as_os_str()]);
            assert_eq!(code, Some(1), "{part}: {stdout}{robot}");
            assert!(stdout.is_empty(), "{stdout}");
            assert!(
                robot.starts_with(&format!(
                    "{{\"schema\":\"fln.olean-rebuild-chain/1\",\"outcome\":\"error\",\
                     \"class\":\"missing-predecessor\",\"part\":\"{missing}\","
                )),
                "{part}: {robot}"
            );
            let absent = dir.0.join(format!(
                "Prelude.olean{}",
                missing.strip_prefix(".olean").expect("suffix")
            ));
            assert!(
                robot.contains(&format!("{} is absent", absent.display())),
                "{robot}"
            );
        }
    }
    let (code, stdout, human) =
        verify_rebuild_run(&[no_exported.0.join("Prelude.olean.server").as_os_str()]);
    assert_eq!(code, Some(1), "{stdout}{human}");
    assert!(
        human.starts_with(
            "fln olean verify-rebuild: missing-predecessor: .olean.server cannot be \
             rebuilt without its predecessor .olean"
        ),
        "{human}"
    );

    let prefix = TempDir::new("rebuild-prefix");
    copy_prelude_chain(&prefix.0, &[".olean", ".olean.server"]);
    let (code, robot, stderr) = verify_rebuild_run(&[
        "--json".as_ref(),
        prefix.0.join("Prelude.olean.server").as_os_str(),
    ]);
    assert_eq!(code, Some(0), "{robot}{stderr}");
    assert!(
        robot.contains("\"outcome\":\"complete\",\"parts\":2,"),
        "{robot}"
    );
    assert!(robot.contains("{\"part\":\".olean.server\","), "{robot}");
    assert!(!robot.contains(".olean.private"), "{robot}");
}

/// `--max-bytes` bounds the chain's parts together, exactly: the sum is
/// admitted, one byte less is a typed resource stop naming the part that
/// crossed it, and a bound below PATH alone stops on PATH.
#[test]
fn olean_verify_rebuild_bounds_the_whole_chain() {
    let total: u64 = CHAIN_PARTS
        .iter()
        .map(|part| {
            std::fs::metadata(prelude_chain_part(part))
                .expect("pinned chain part")
                .len()
        })
        .sum();
    let exported = prelude_chain_part(".olean");
    let at_bound = total.to_string();
    let (code, robot, stderr) = verify_rebuild_run(&[
        "--json".as_ref(),
        "--max-bytes".as_ref(),
        at_bound.as_ref(),
        exported.as_os_str(),
    ]);
    assert_eq!(code, Some(0), "{robot}{stderr}");
    assert!(
        robot.contains("\"outcome\":\"complete\",\"parts\":3,"),
        "{robot}"
    );

    let below = (total - 1).to_string();
    let (code, stdout, robot) = verify_rebuild_run(&[
        "--json".as_ref(),
        "--max-bytes".as_ref(),
        below.as_ref(),
        exported.as_os_str(),
    ]);
    assert_eq!(code, Some(3), "{stdout}{robot}");
    assert!(stdout.is_empty(), "{stdout}");
    assert!(
        robot.contains("\"class\":\"resource\",\"part\":\".olean.private\","),
        "{robot}"
    );
    assert!(
        robot.contains(&format!("module chain's {below}-byte input limit")),
        "{robot}"
    );

    let (code, stdout, robot) = verify_rebuild_run(&[
        "--json".as_ref(),
        "--max-bytes".as_ref(),
        "100".as_ref(),
        prelude_chain_part(".olean.server").as_os_str(),
    ]);
    assert_eq!(code, Some(3), "{stdout}{robot}");
    assert!(
        robot.contains("\"class\":\"resource\",\"part\":\".olean.server\","),
        "{robot}"
    );
}

/// The committed chain the cells above use is the installed pin's
/// `Init/Prelude` chain, and the installed pin's own files verify in place.
/// Typed skip without the pin; `FLN_REQUIRE_REFERENCE` turns the skip into a
/// failure.
#[test]
fn olean_verify_rebuild_chain_fixture_is_the_pinned_init_prelude() {
    let library = std::env::var_os("HOME")
        .map(std::path::PathBuf::from)
        .map(|home| {
            home.join(".elan/toolchains")
                .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                .join("lib/lean/Init")
        })
        .filter(|init| init.join("Prelude.olean.private").is_file());
    let Some(init) = library else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "FLN_REQUIRE_REFERENCE is set but the pinned Reference Init/Prelude chain is absent"
        );
        eprintln!("SKIP: pinned Reference Init/Prelude chain not installed");
        return;
    };
    for part in CHAIN_PARTS {
        let suffix = part.strip_prefix(".olean").expect("suffix");
        assert!(
            std::fs::read(prelude_chain_part(part)).expect("fixture part")
                == std::fs::read(init.join(format!("Prelude.olean{suffix}"))).expect("pin part"),
            "the committed {part} is the pinned Init/Prelude{part}"
        );
    }
    let in_place = init.join("BinderNameHint.olean.private");
    let (code, robot, stderr) = verify_rebuild_run(&["--json".as_ref(), in_place.as_os_str()]);
    assert_eq!(code, Some(0), "{robot}{stderr}");
    assert!(
        robot.contains("\"outcome\":\"complete\",\"parts\":3,"),
        "{robot}"
    );
}

/// Every file under `root` by relative path, without `.git` and
/// `lean-toolchain`.
fn scaffold_tree(root: &std::path::Path) -> std::collections::BTreeMap<String, Vec<u8>> {
    let mut out = std::collections::BTreeMap::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(dir) = pending.pop() {
        for entry in std::fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            let name = path.file_name().unwrap().to_string_lossy().into_owned();
            if path.is_dir() {
                if name != ".git" {
                    pending.push(path);
                }
            } else if name != "lean-toolchain" {
                let relative = path.strip_prefix(root).unwrap().display().to_string();
                out.insert(relative, std::fs::read(&path).unwrap());
            }
        }
    }
    out
}

/// `lake new` writes the pin's `std` tree, refuses the templates it does not
/// write, and `lake clean` removes the directory the package builds into.
///
/// Where the pinned toolchain is installed, the pinned `lake new demo` runs
/// beside ours and every file is compared. Two things are left out of the
/// comparison and are differences, not agreements: `lean-toolchain`, because
/// the pin writes the toolchain name its launcher gave it, and `.git`, because
/// this implementation spawns git only to fetch dependencies. Typed skip
/// without the pin; `FLN_REQUIRE_REFERENCE` turns the skip into a failure.
#[test]
fn lake_new_writes_the_tree_the_pinned_lake_writes() {
    let guard = TempDir::new("lake-new-pin");
    let root = guard.0.clone();
    let ours_parent = root.join("ours");
    std::fs::create_dir_all(&ours_parent).unwrap();
    let lake = |args: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_lake"))
            .arg("--dir")
            .arg(&ours_parent)
            .args(args)
            .output()
            .expect("run lake")
    };

    let created = lake(&["new", "demo"]);
    assert!(created.status.success(), "{created:?}");
    let ours = scaffold_tree(&ours_parent.join("demo"));
    assert_eq!(
        ours.keys().map(String::as_str).collect::<Vec<_>>(),
        [
            ".github/workflows/lean_action_ci.yml",
            ".gitignore",
            "Demo.lean",
            "Demo/Basic.lean",
            "Main.lean",
            "README.md",
            "lakefile.toml",
        ]
    );
    // The line the old scaffold got wrong: the pin indents the body of `main`.
    assert_eq!(
        String::from_utf8_lossy(&ours["Main.lean"]),
        "import Demo\n\ndef main : IO Unit :=\n  IO.println s!\"Hello, {hello}!\"\n"
    );

    // A template the pin has and this does not write: said so, and nothing made.
    // It used to exit 0 and write the default project whatever was asked for.
    let math = lake(&["new", "mathy", "math"]);
    assert_eq!(math.status.code(), Some(5), "{math:?}");
    assert!(
        String::from_utf8_lossy(&math.stderr)
            .starts_with("lake new: not implemented: the `math` template")
    );
    assert!(!ours_parent.join("mathy").exists());
    // A template the pin does not have: the pin's own words.
    let unknown = lake(&["new", "x", "zzz"]);
    assert_eq!(unknown.status.code(), Some(1));
    assert_eq!(
        String::from_utf8_lossy(&unknown.stderr),
        "error: unknown package template `zzz`\n"
    );
    assert!(!ours_parent.join("x").exists());

    // `lake clean` removes the configured build directory. It used to remove
    // `.lake/build` whatever the package said, and report success.
    let cleaned = lake(&["new", "cleanme"]);
    assert!(cleaned.status.success(), "{cleaned:?}");
    let package = ours_parent.join("cleanme");
    std::fs::write(
        package.join("lakefile.toml"),
        "name = \"cleanme\"\nbuildDir = \"out\"\n\n[[lean_lib]]\nname = \"Cleanme\"\n",
    )
    .unwrap();
    for built in ["out/lib", ".lake/build/lib"] {
        std::fs::create_dir_all(package.join(built)).unwrap();
    }
    let clean = Command::new(env!("CARGO_BIN_EXE_lake"))
        .arg("--dir")
        .arg(&package)
        .arg("clean")
        .output()
        .expect("run lake clean");
    assert!(clean.status.success(), "{clean:?}");
    assert!(
        !package.join("out").exists(),
        "the configured build directory survived"
    );
    assert!(
        package.join(".lake/build").exists(),
        "another directory was removed"
    );

    let pinned = std::env::var_os("HOME")
        .map(std::path::PathBuf::from)
        .map(|home| {
            home.join(".elan/toolchains")
                .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                .join("bin/lake")
        })
        .filter(|lake| lake.is_file());
    let Some(pinned) = pinned else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "FLN_REQUIRE_REFERENCE is set but the pinned lake is absent"
        );
        println!("SKIP: no pinned lake; the scaffold was not compared with the pin's");
        return;
    };
    let pin_parent = root.join("pin");
    std::fs::create_dir_all(&pin_parent).unwrap();
    let theirs = Command::new(&pinned)
        .args(["new", "demo"])
        .current_dir(&pin_parent)
        .output()
        .expect("run the pinned lake new");
    assert!(theirs.status.success(), "{theirs:?}");
    let theirs = scaffold_tree(&pin_parent.join("demo"));
    assert_eq!(
        ours.keys().collect::<Vec<_>>(),
        theirs.keys().collect::<Vec<_>>(),
        "the two scaffolds hold different files"
    );
    for (path, bytes) in &theirs {
        assert!(
            &ours[path] == bytes,
            "{path} differs from the pin's:\nours: {:?}\npin:  {:?}",
            String::from_utf8_lossy(&ours[path]),
            String::from_utf8_lossy(bytes)
        );
    }
}
