//! Integration tests for new fln multiplexer verbs (diff, goals, doctor, serve-mcp,
//! replay, cache, build explain) and toolchain personalities (leanc, lake).
#![forbid(unsafe_code)]

use std::process::Command;

#[test]
fn multiplexer_doctor_verb_reports_healthy_audit() {
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .arg("doctor")
        .output()
        .expect("run fln doctor");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("fln doctor: environment and subsystem audit"));
    assert!(stdout.contains("reference pin: v4.32.0"));
    assert!(stdout.contains("all core subsystem checks passed"));

    let json_output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["doctor", "--json"])
        .output()
        .expect("run fln doctor --json");
    assert!(json_output.status.success());
    let json_stdout = String::from_utf8(json_output.stdout).expect("utf8 stdout");
    assert!(json_stdout.contains("\"schema\":\"fln.doctor/1\""));
    assert!(json_stdout.contains("\"status\":\"healthy\""));
    assert!(json_stdout.contains("\"kernel_checker\""));
}

#[test]
fn multiplexer_capability_notices_are_typed_and_exit_cleanly() {
    for (verb, expected_gate, expected_desc) in [
        ("serve-mcp", "G6", "Envoy"),
        ("replay", "G5", "Palimpsest"),
        ("cache", "G2", "Ledger"),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .arg(verb)
            .output()
            .expect("run verb");
        assert!(output.status.success());
        let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
        assert!(stdout.contains(expected_gate), "verb {verb}: {stdout}");
        assert!(stdout.contains(expected_desc), "verb {verb}: {stdout}");

        let json_output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args([verb, "--json"])
            .output()
            .expect("run verb --json");
        assert!(json_output.status.success());
        let json_stdout = String::from_utf8(json_output.stdout).expect("utf8 stdout");
        assert!(json_stdout.contains("\"schema\":\"fln.capability-notice/1\""));
        assert!(json_stdout.contains(&format!("\"command\":\"{verb}\"")));
        assert!(json_stdout.contains(&format!("\"gate\":\"{expected_gate}\"")));
    }

    // Test build explain
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["build", "explain"])
        .output()
        .expect("run build explain");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("G2"));
    assert!(stdout.contains("Ledger"));
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

fn temp_file(text: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "fln-goals-test-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("goal_test.lean");
    std::fs::write(&path, text).unwrap();
    path
}

#[test]
fn multiplexer_goals_verb_inspects_proof_goals() {
    let text = include_str!("../../../examples/native_goal_control.lean");
    let file_path = temp_file(text);
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
    assert!(json_stdout.contains("\"schema\":\"fln.goals/1\""), "{json_stdout}");
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

    // leanc --fln-census-unknown
    let output = Command::new(env!("CARGO_BIN_EXE_leanc"))
        .arg("--fln-census-unknown")
        .output()
        .expect("run leanc --fln-census-unknown");
    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8(output.stderr).expect("utf8 stderr");
    assert!(stderr.contains("unrecognized command-line option"));
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

    // lake --fln-census-unknown help
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--fln-census-unknown", "help"])
        .output()
        .expect("run lake --fln-census-unknown help");
    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8(output.stderr).expect("utf8 stderr");
    assert!(stderr.contains("unknown option"));
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
    assert!(json_stderr.contains("\"schema\":\"fln.verify-capsule/1\""));
    assert!(json_stderr.contains("\"outcome\":\"error\""));
}

#[test]
fn multiplexer_verify_capsule_verifies_valid_cartridge() {
    use fln_hash::cartridge::{
        CartridgeBuilderV1, CartridgeObjectKindV1, ObjectPortabilityV1, ObjectRequirementV1,
    };
    use fln::{ContentRoot, EpochId};

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

    let temp_dir = std::env::temp_dir().join(format!(
        "fln-capsule-test-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&temp_dir).unwrap();
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
    assert!(stdout.contains("fln verify-capsule: verified capsule at"));
    assert!(stdout.contains("capsule verification passed."));

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
    assert!(json_stdout.contains("\"schema\":\"fln.verify-capsule/1\""));
    assert!(json_stdout.contains("\"outcome\":\"complete\""));
    assert!(json_stdout.contains("\"status\":\"verified\""));
    assert!(json_stdout.contains("\"transport_state\":\"complete\""));
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
    let temp_parent = std::env::temp_dir().join(format!(
        "fln-lake-cli-test-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&temp_parent).unwrap();

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
    let temp_parent = std::env::temp_dir().join(format!(
        "fln-lake-update-test-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&temp_parent).unwrap();

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

    // 1. lake update
    let update_output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", pkg_dir.to_str().unwrap(), "update"])
        .output()
        .expect("run lake update");
    assert!(
        update_output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&update_output.stderr)
    );
    assert!(pkg_dir.join("lake-manifest.json").exists());

    let manifest_content = std::fs::read_to_string(pkg_dir.join("lake-manifest.json")).unwrap();
    assert!(manifest_content.contains("\"name\": \"my_project\""));
    assert!(manifest_content.contains("\"batteries\""));

    // 2. lake update --json
    let update_json = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", pkg_dir.to_str().unwrap(), "--json", "update"])
        .output()
        .expect("run lake update --json");
    assert!(update_json.status.success());
    let update_json_stdout = String::from_utf8(update_json.stdout).expect("utf8 stdout");
    assert!(update_json_stdout.contains("\"schema\":\"fln.lake-update/1\""));
    assert!(update_json_stdout.contains("\"package\":\"my_project\""));

    // 3. lake env (bare)
    let env_output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .arg("env")
        .output()
        .expect("run lake env");
    assert!(env_output.status.success());
    let env_stdout = String::from_utf8(env_output.stdout).expect("utf8 stdout");
    assert!(env_stdout.contains("LEAN_SYSROOT="));
    assert!(env_stdout.contains("LEAN_PATH="));
    assert!(env_stdout.contains("ELAN_TOOLCHAIN="));

    // 4. lake env echo hello
    let env_echo = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["env", "echo", "testing_lake_env_propagation"])
        .output()
        .expect("run lake env echo");
    assert!(env_echo.status.success());
    let env_echo_stdout = String::from_utf8(env_echo.stdout).expect("utf8 stdout");
    assert!(env_echo_stdout.contains("testing_lake_env_propagation"));

    // 5. lake env with nonexistent command exits 255
    let env_missing = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["env", "nonexistent_command_12345_xyz"])
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
    let temp_parent = std::env::temp_dir().join(format!(
        "fln-lake-build-test-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&temp_parent).unwrap();

    let pkg_dir = temp_parent.join("calc_proj");
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
    assert!(check_stdout.contains("Build configuration validated"));

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
    assert!(build1.status.success());
    let build1_stdout = String::from_utf8(build1.stdout).expect("utf8 stdout");
    assert!(build1_stdout.contains("Built calc_proj (1 built, 0 cached)"));
    assert!(pkg_dir.join(".lake/build/lib/calc_proj.olean").exists());

    // 5. lake build (cached)
    let build2 = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", pkg_dir.to_str().unwrap(), "build"])
        .output()
        .expect("run lake build 2");
    assert!(build2.status.success());
    let build2_stdout = String::from_utf8(build2.stdout).expect("utf8 stdout");
    assert!(build2_stdout.contains("Built calc_proj (0 built, 1 cached)"));

    // 6. lake build --json
    let build_json = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", pkg_dir.to_str().unwrap(), "--json", "build"])
        .output()
        .expect("run lake build --json");
    assert!(build_json.status.success());
    let build_json_stdout = String::from_utf8(build_json.stdout).expect("utf8 stdout");
    assert!(build_json_stdout.contains("\"schema\":\"fln.lake-build/1\""));
    assert!(build_json_stdout.contains("\"package\":\"calc_proj\""));
    assert!(build_json_stdout.contains("\"targets_cached\":1"));

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
fn fln_build_explain_dual_rebuild_decisions() {
    let temp_parent = std::env::temp_dir().join(format!(
        "fln-build-explain-test-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&temp_parent).unwrap();

    let pkg_dir = temp_parent.join("geom_pkg");
    Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", pkg_dir.to_str().unwrap(), "init", "geom_pkg"])
        .output()
        .expect("init geom_pkg");

    // 1. fln build explain before build (initial rebuild)
    let explain_init = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["build", "explain", "--dir", pkg_dir.to_str().unwrap()])
        .output()
        .expect("run fln build explain initial");
    assert!(explain_init.status.success());
    let explain_init_stdout = String::from_utf8(explain_init.stdout).expect("utf8 stdout");
    assert!(explain_init_stdout.contains("Target: geom_pkg"));
    assert!(explain_init_stdout.contains("Reference decision: rebuild"));
    assert!(explain_init_stdout.contains("Native decision:    rebuild"));
    assert!(explain_init_stdout.contains("Cache outcome:      miss"));

    // 2. fln build explain --json
    let explain_json = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["build", "explain", "--json", "--dir", pkg_dir.to_str().unwrap()])
        .output()
        .expect("run fln build explain --json");
    assert!(explain_json.status.success());
    let explain_json_stdout = String::from_utf8(explain_json.stdout).expect("utf8 stdout");
    assert!(explain_json_stdout.contains("\"schema\":\"fln.build-explain/1\""));
    assert!(explain_json_stdout.contains("\"reference_decision\":\"rebuild\""));
    assert!(explain_json_stdout.contains("\"native_decision\":\"rebuild\""));
    assert!(explain_json_stdout.contains("\"cache_outcome\":\"miss\""));

    // 3. Build package
    Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--dir", pkg_dir.to_str().unwrap(), "build"])
        .output()
        .expect("lake build");

    // 4. fln build explain after build (cached)
    let explain_cached = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["build", "explain", "--dir", pkg_dir.to_str().unwrap()])
        .output()
        .expect("run fln build explain cached");
    assert!(explain_cached.status.success());
    let explain_cached_stdout = String::from_utf8(explain_cached.stdout).expect("utf8 stdout");
    assert!(explain_cached_stdout.contains("Reference decision: cached"));
    assert!(explain_cached_stdout.contains("Native decision:    cached"));
    assert!(explain_cached_stdout.contains("Cache outcome:      hit"));

    // 5. Touch source with internal proof update
    std::thread::sleep(std::time::Duration::from_millis(50));
    let src = pkg_dir.join("GeomPkg.lean");
    std::fs::write(&src, "def hello := \"world internal update\"\n").unwrap();

    // 5a. fln build explain in native sound mode: early-cutoff
    let explain_sound = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["build", "explain", "--dir", pkg_dir.to_str().unwrap()])
        .output()
        .expect("run fln build explain sound");
    assert!(explain_sound.status.success());
    let explain_sound_stdout = String::from_utf8(explain_sound.stdout).expect("utf8 stdout");
    assert!(explain_sound_stdout.contains("Reference decision: rebuild"));
    assert!(explain_sound_stdout.contains("Native decision:    cached"));
    assert!(explain_sound_stdout.contains("early-cutoff"));
    assert!(explain_sound_stdout.contains("Cache outcome:      hit"));

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
    assert!(explain_faithful.status.success());
    let explain_faithful_stdout = String::from_utf8(explain_faithful.stdout).expect("utf8 stdout");
    assert!(explain_faithful_stdout.contains("Reference decision: rebuild"));
    assert!(explain_faithful_stdout.contains("Native decision:    rebuild"));
    assert!(explain_faithful_stdout.contains("faithful-invalidation enabled"));
    assert!(explain_faithful_stdout.contains("Cache outcome:      miss"));
}




