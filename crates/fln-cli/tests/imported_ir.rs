//! Installed CLI: real Reference IR -> checked lowering -> native Golem.
#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::Command;

fn partition() -> Option<PathBuf> {
    let path = std::env::var_os("FLN_BUILTIN_PARTITION")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            fln_core::checked_workspace_root!().join("contracts/builtin_partition.tsv")
        });
    if path.is_file() {
        Some(path)
    } else {
        eprintln!(
            "SKIP imported IR installed CLI: materialize the pinned census at {}",
            path.display()
        );
        None
    }
}

fn command(entry: &str, args: &[&str], policy: &PathBuf) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["ir", "run", "--json", "--entry", entry, "--partition"])
        .arg(policy)
        .args(args)
        .arg(
            fln_core::checked_workspace_root!()
                .join("crates/fln-olean/fixtures/ir/Init.Data.Nat.Basic.ir"),
        )
        .output()
        .unwrap()
}

#[test]
fn installed_command_executes_pinned_ir_and_reports_its_producer() {
    let Some(policy) = partition() else {
        return;
    };
    for (entry, args, expected) in [
        ("Nat.min", ["--nat", "42", "--nat", "9"], 9),
        ("Nat.max", ["--nat", "42", "--nat", "9"], 42),
        ("Nat.blt", ["--nat", "2", "--nat", "3"], 1),
    ] {
        let output = command(entry, &args, &policy);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stderr.is_empty());
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains("\"outcome\":\"complete\""), "{stdout}");
        assert!(
            stdout.contains(&format!("\"value\":{expected},")),
            "{stdout}"
        );
        assert!(stdout.contains("\"producer\":\"reference\""), "{stdout}");
        assert!(stdout.contains("\"authority\":false"), "{stdout}");
        assert!(
            stdout.contains("\"nativeExterns\":[\"extern:Nat."),
            "{stdout}"
        );
    }
}

#[test]
fn installed_execution_budget_is_inconclusive_and_cannot_publish_a_value() {
    let Some(policy) = partition() else {
        return;
    };
    let output = command(
        "Nat.blt",
        &["--nat", "2", "--nat", "3", "--fln-max-steps", "1"],
        &policy,
    );
    assert_eq!(output.status.code(), Some(3));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("\"outcome\":\"inconclusive\""), "{stderr}");
    assert!(stderr.contains("\"value\":null"), "{stderr}");
    assert!(stderr.contains("\"producer\":\"reference\""), "{stderr}");
}

#[test]
fn installed_command_does_not_reclassify_native_api_or_missing_census_rows() {
    let Some(policy) = partition() else {
        return;
    };
    let overridden = command(
        "Nat.blt",
        &["--nat", "2", "--nat", "3", "--user", "Nat.blt"],
        &policy,
    );
    assert_eq!(overridden.status.code(), Some(1));
    assert!(overridden.stdout.is_empty());
    assert!(
        String::from_utf8(overridden.stderr)
            .unwrap()
            .contains("policy-refusal")
    );
    let unknown = command("Nat.blt._boxed", &["--nat", "2", "--nat", "3"], &policy);
    assert_eq!(unknown.status.code(), Some(3));
    assert!(unknown.stdout.is_empty());
    assert!(
        String::from_utf8(unknown.stderr)
            .unwrap()
            .contains("unclassified")
    );
}

#[test]
fn cli_rejects_missing_policy_and_malformed_arguments_before_running() {
    for args in [
        vec!["ir", "run"],
        vec!["ir", "run", "--entry", "Nat.min", "input.ir"],
        vec![
            "ir",
            "run",
            "--entry",
            "Nat.min",
            "--partition",
            "p.tsv",
            "--nat",
            "-1",
            "input.ir",
        ],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(args)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
    }
}

#[test]
fn installed_global_initialization_requires_a_unique_flag_and_verified_policy() {
    let duplicate = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args([
            "ir",
            "run",
            "--entry",
            "Nat.min",
            "--partition",
            "p.tsv",
            "--initialize-globals",
            "--initialize-globals",
            "input.ir",
        ])
        .output()
        .unwrap();
    assert_eq!(duplicate.status.code(), Some(2));
    assert!(duplicate.stdout.is_empty());
    assert!(
        String::from_utf8_lossy(&duplicate.stderr)
            .contains("--initialize-globals may be supplied only once")
    );

    let root = module_root();
    let unverified = root.join("unverified.tsv");
    std::fs::write(&unverified, b"constant_count\t0\n").unwrap();
    for capture in [vec![], vec!["--capture-output", "0"]] {
        let mut args = vec!["--initialize-globals", "--nat", "7", "--nat", "3"];
        args.extend(capture);
        let output = command("Nat.min", &args, &unverified);
        assert_eq!(output.status.code(), Some(1));
        assert!(output.stdout.is_empty());
        let error = String::from_utf8(output.stderr).unwrap();
        assert!(error.contains("\"class\":\"policy-refusal\""), "{error}");
        assert!(!error.contains("\"outcome\":\"complete\""), "{error}");
    }

    let help = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["ir", "run", "--help"])
        .output()
        .unwrap();
    assert!(help.status.success());
    assert!(String::from_utf8_lossy(&help.stdout).contains("--initialize-globals"));
}

fn module_root() -> PathBuf {
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let tick = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "fln-installed-ir-modules-{}-{tick}-{}",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&root).unwrap();
    root
}

/// The import graph is generated test data; executable code is the retained
/// compiler-produced Nat.Basic IR fixture, not a fabricated implementation.
fn write_import_table(root: &Path, name: &str, imports: &[&str], code: bool) -> usize {
    let imports: Vec<_> = imports
        .iter()
        .map(|name| fln::OleanModuleImport {
            module: fln::Name::from_components(name.split('.')),
            import_all: false,
            is_exported: false,
            is_meta: false,
        })
        .collect();
    let olean = fln::encode_olean_module(
        fln::OleanModuleWriteInput {
            is_module: false,
            imports: &imports,
            constants: &[],
            extra_const_names: &[],
        },
        fln::OleanWriteHeader {
            version: fln::OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: fln::OLEAN_PIN_TAG.strip_prefix('v').unwrap(),
            githash: fln::OLEAN_PIN_COMMIT,
            base_addr: fln::OLEAN_REGION_ALIGN as u64,
        },
        fln::OleanWriteBudget::default(),
    )
    .unwrap()
    .bytes;
    let path = root.join(name.replace('.', "/"));
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path.with_extension("olean"), &olean).unwrap();
    let mut bytes = olean.len();
    if code {
        let ir = include_bytes!("../../fln-olean/fixtures/ir/Init.Data.Nat.Basic.ir");
        std::fs::write(path.with_extension("ir"), ir).unwrap();
        bytes += ir.len();
    }
    bytes
}

fn module_command(root: &Path, policy: &Path, extra: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["ir", "run", "--json", "--entry", "Nat.min", "--partition"])
        .arg(policy)
        .args(["--module", "Root", "--search-path"])
        .arg(root)
        .args(["--nat", "42", "--nat", "9"])
        .args(extra)
        .output()
        .unwrap()
}

#[test]
fn installed_module_mode_executes_transitive_ir_and_reports_missing_companions() {
    let Some(policy) = partition() else {
        return;
    };
    let root = module_root();
    let total = write_import_table(&root, "Root", &["Left", "Right"], false)
        + write_import_table(&root, "Left", &["Code.Nat"], false)
        + write_import_table(&root, "Right", &["Code.Nat"], false)
        + write_import_table(&root, "Code.Nat", &[], true);
    let output = module_command(&root, &policy, &["--max-bytes", &total.to_string()]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"value\":9,"), "{stdout}");
    assert!(
        stdout.contains("\"loadedModules\":[\"Left\",\"Right\",\"Root\",\"Code.Nat\"]"),
        "{stdout}"
    );
    assert!(
        stdout.contains("\"missingIrModules\":[\"Left\",\"Right\",\"Root\"]"),
        "{stdout}"
    );
    assert!(
        stdout.contains(&format!("\"artifactBytes\":{total}")),
        "{stdout}"
    );
    assert!(stdout.contains("\"producer\":\"reference\""), "{stdout}");
    assert!(stdout.contains("\"authority\":false"), "{stdout}");
    let again = module_command(&root, &policy, &["--module", "Right", "--module", "Root"]);
    assert!(again.status.success());
    assert_eq!(again.stdout, stdout.as_bytes());

    let limited = module_command(&root, &policy, &["--max-bytes", &(total - 1).to_string()]);
    assert_eq!(limited.status.code(), Some(3));
    assert!(limited.stdout.is_empty());
    assert!(String::from_utf8_lossy(&limited.stderr).contains("\"class\":\"resource\""));
    assert_eq!(
        module_command(&root, &policy, &[]).stdout,
        stdout.as_bytes()
    );

    let overridden = module_command(&root, &policy, &["--user", "Nat.min"]);
    assert_eq!(overridden.status.code(), Some(1));
    assert!(overridden.stdout.is_empty());
    assert!(String::from_utf8_lossy(&overridden.stderr).contains("policy-refusal"));
}

#[test]
fn installed_module_mode_refuses_missing_corrupt_and_unavailable_code() {
    let Some(policy) = partition() else {
        return;
    };
    let missing = module_root();
    write_import_table(&missing, "Root", &["Absent"], false);
    let output = module_command(&missing, &policy, &[]);
    assert_eq!(output.status.code(), Some(3));
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains("missing-module"));
    assert!(String::from_utf8_lossy(&output.stderr).contains("Absent"));

    let corrupt = module_root();
    write_import_table(&corrupt, "Root", &[], false);
    std::fs::write(corrupt.join("Root.ir"), b"malformed IR").unwrap();
    let output = module_command(&corrupt, &policy, &[]);
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains("\"class\":\"codec\""));

    let no_code = module_root();
    write_import_table(&no_code, "Root", &[], false);
    let later = module_root();
    write_import_table(&later, "Root", &[], true);
    let output = module_command(
        &no_code,
        &policy,
        &["--search-path", later.to_str().unwrap()],
    );
    assert_eq!(output.status.code(), Some(3));
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains("missing declaration Nat.min"));
}

#[test]
fn module_discovery_cannot_replace_the_pinned_execution_partition() {
    let root = module_root();
    write_import_table(&root, "Root", &[], true);
    let policy = root.join("untrusted-partition.tsv");
    std::fs::write(&policy, b"constant_count\t0\n").unwrap();
    let output = module_command(&root, &policy, &[]);
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains("policy-refusal"));
}

fn live_output_reference() -> Option<PathBuf> {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let lib = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(lib.parent()?.parent()?.join("bin/lean"))
        });
    assert!(
        reference.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference is required for installed output capture"
    );
    let reference = reference?;
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(
        String::from_utf8(version.stdout).unwrap().trim(),
        fln::OLEAN_PIN_COMMIT
    );
    Some(reference)
}

fn output_command(
    artifact: &Path,
    policy: &Path,
    users: &[String],
    entry: &str,
    arguments: &[&str],
    max_output: Option<usize>,
) -> std::process::Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
    command
        .args(["ir", "run", "--json", "--entry", entry, "--partition"])
        .arg(policy)
        .args(arguments)
        .arg(artifact)
        .stdin(std::process::Stdio::null());
    for user in users {
        command.arg("--user").arg(user);
    }
    if let Some(max_bytes) = max_output {
        command.arg("--capture-output").arg(max_bytes.to_string());
    }
    command.output().unwrap()
}

#[test]
fn installed_capture_runs_pinned_io_preserving_output_raw_return_and_stopped_prefix() {
    let Some(policy) = partition() else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned execution census is required for installed output capture"
        );
        return;
    };
    let Some(reference) = live_output_reference() else {
        eprintln!("SKIP installed captured IR: requires the pinned Reference");
        return;
    };
    let root = module_root();
    let source = include_str!("../../fln-olean/fixtures/ir/NativeOutputModule.lean");
    std::fs::write(root.join("NativeOutputModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&root)
        .args(["-o", "NativeOutputModule.olean", "NativeOutputModule.lean"])
        .output()
        .unwrap();
    assert!(
        generated.status.success(),
        "{}{}",
        String::from_utf8_lossy(&generated.stdout),
        String::from_utf8_lossy(&generated.stderr),
    );
    let artifact = root.join("NativeOutputModule.ir");
    let module =
        fln::decode_ir_artifact(&std::fs::read(&artifact).unwrap(), 32 * 1024 * 1024).unwrap();
    let users: Vec<_> = module
        .decls
        .iter()
        .filter_map(|declaration| match declaration {
            fln_olean::ir::IrDecl::Function { name, .. } => {
                let text = name.to_display_string();
                assert_eq!(fln::Name::from_components(text.split('.')), *name);
                Some(text)
            }
            _ => None,
        })
        .collect();
    let run = |entry, arguments: &[&str], max_output| {
        output_command(&artifact, &policy, &users, entry, arguments, max_output)
    };
    let arguments = ["--string", "α", "--erased"];

    let denied = run("localOutputAction", &arguments, None);
    assert_eq!(denied.status.code(), Some(3));
    assert!(denied.stdout.is_empty());
    assert!(String::from_utf8_lossy(&denied.stderr).contains("effectful native call"));

    std::fs::write(
        root.join("Oracle.lean"),
        format!("{source}\n#eval localOutputAction \"α\"\n"),
    )
    .unwrap();
    let oracle = Command::new(&reference)
        .current_dir(&root)
        .arg("Oracle.lean")
        .output()
        .unwrap();
    assert!(
        oracle.status.success(),
        "{}",
        String::from_utf8_lossy(&oracle.stderr)
    );
    assert_eq!(oracle.stdout, "αtail\0🙂\n42\n".as_bytes());

    let complete = run("localOutputAction", &arguments, Some(12));
    assert!(
        complete.status.success(),
        "{}",
        String::from_utf8_lossy(&complete.stderr)
    );
    assert!(complete.stderr.is_empty());
    let stdout = String::from_utf8(complete.stdout).unwrap();
    assert!(!stdout.contains('\0'));
    assert!(
        stdout.starts_with('{') && stdout.ends_with("}\n"),
        "{stdout}"
    );
    for expected in [
        "\"outcome\":\"complete\"",
        "\"value\":null",
        "\"valueKind\":\"constructor:0\"",
        "\"encoding\":\"utf-8\"",
        "\"data\":\"αtail\\u0000🙂\\n\"",
        "\"byteLength\":12,\"maxBytes\":12",
        "\"producer\":\"reference\"",
        "\"authority\":false",
    ] {
        assert!(stdout.contains(expected), "{expected}: {stdout}");
    }

    for (limit, prefix, count) in [(11, "α", 2), (0, "", 0)] {
        let stopped = run("localOutputAction", &arguments, Some(limit));
        assert_eq!(stopped.status.code(), Some(3));
        assert!(stopped.stdout.is_empty());
        let error = String::from_utf8(stopped.stderr).unwrap();
        assert!(error.contains("\"outcome\":\"inconclusive\""), "{error}");
        assert!(error.contains("\"value\":null"), "{error}");
        assert!(error.contains("\"valueKind\":null"), "{error}");
        assert!(error.contains(&format!("\"data\":\"{prefix}\"")), "{error}");
        assert!(
            error.contains(&format!("\"byteLength\":{count},\"maxBytes\":{limit}")),
            "{error}"
        );
    }
    assert_eq!(
        run("localOutputAction", &arguments, Some(12)).stdout,
        stdout.as_bytes()
    );

    let read = run("localOutputRead", &["--erased"], Some(12));
    assert_eq!(read.status.code(), Some(3));
    assert!(read.stdout.is_empty());
    let error = String::from_utf8(read.stderr).unwrap();
    assert!(
        error.contains("captured Reference output does not authorize stream reads"),
        "{error}"
    );
    assert!(error.contains("\"data\":\"\",\"byteLength\":0"), "{error}");
}

#[test]
fn installed_named_globals_execute_their_dependency_closure_only_when_requested() {
    let Some(policy) = partition() else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned execution census is required for installed global initialization"
        );
        return;
    };
    let Some(reference) = live_output_reference() else {
        eprintln!("SKIP installed named globals: requires the pinned Reference");
        return;
    };
    let root = module_root();
    let source = format!(
        "{}\n@[noinline] def cliInitializedNat (n : Nat) : Nat := rememberedCounter + n\n",
        include_str!("../../fln-olean/fixtures/ir/InitializedGlobalsModule.lean")
    );
    std::fs::write(root.join("InitializedGlobalsCli.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&root)
        .args([
            "-o",
            "InitializedGlobalsCli.olean",
            "InitializedGlobalsCli.lean",
        ])
        .output()
        .unwrap();
    assert!(
        generated.status.success(),
        "{}{}",
        String::from_utf8_lossy(&generated.stdout),
        String::from_utf8_lossy(&generated.stderr)
    );
    let artifact = root.join("InitializedGlobalsCli.ir");
    let module =
        fln::decode_ir_artifact(&std::fs::read(&artifact).unwrap(), 32 * 1024 * 1024).unwrap();
    let users: Vec<_> = module
        .decls
        .iter()
        .filter_map(|declaration| match declaration {
            fln_olean::ir::IrDecl::Function { name, .. } => {
                let text = name.to_display_string();
                assert_eq!(fln::Name::from_components(text.split('.')), *name);
                Some(text)
            }
            _ => None,
        })
        .collect();
    let run = |arguments: &[&str], capture| {
        output_command(
            &artifact,
            &policy,
            &users,
            "cliInitializedNat",
            arguments,
            capture,
        )
    };
    let denied = run(&["--nat", "2"], None);
    assert_eq!(denied.status.code(), Some(3));
    assert!(denied.stdout.is_empty());
    assert!(!String::from_utf8_lossy(&denied.stderr).contains("\"outcome\":\"complete\""));

    for capture in [None, Some(0)] {
        let output = run(&["--initialize-globals", "--nat", "2"], capture);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stderr.is_empty());
        let stdout = String::from_utf8(output.stdout).unwrap();
        for expected in [
            "\"outcome\":\"complete\"",
            "\"value\":42,",
            "\"initializeGlobals\":true",
            "\"initializationFailure\":null",
            "\"name\":\"initializeSharedCounter\"",
            "\"name\":\"initializeRememberedCounter\"",
            "\"producer\":\"reference\"",
            "\"authority\":false",
        ] {
            assert!(stdout.contains(expected), "{expected}: {stdout}");
        }
        if capture.is_some() {
            assert!(
                stdout.contains("\"byteLength\":0,\"maxBytes\":0"),
                "{stdout}"
            );
        }
        assert_eq!(
            run(&["--initialize-globals", "--nat", "2"], capture).stdout,
            stdout.as_bytes()
        );
    }
}
