//! Installed Lake executables: real source closure, Golem main, argv and status.
#![forbid(unsafe_code)]

use std::{
    ffi::OsString,
    path::PathBuf,
    process::{Command, Output},
    sync::{
        Mutex, MutexGuard, OnceLock,
        atomic::{AtomicUsize, Ordering},
    },
};

static NEXT: AtomicUsize = AtomicUsize::new(0);
static IMPORT_STORE: OnceLock<PathBuf> = OnceLock::new();
static EXECUTION: Mutex<()> = Mutex::new(());

fn serial_execution() -> MutexGuard<'static, ()> {
    EXECUTION
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

struct Package(PathBuf);

impl Package {
    fn new(config: &str) -> Self {
        Self::with_configuration("lakefile.toml", config)
    }

    fn with_configuration(file: &str, config: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-lake-executable-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        std::fs::create_dir(&path).unwrap();
        let package = Self(path);
        package.write(file, config);
        package
    }

    fn write(&self, relative: &str, source: &str) {
        let path = self.0.join(relative);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, source).unwrap();
    }

    fn run(&self, arguments: &[&str], reference: Option<&Reference>) -> Output {
        self.run_with_jobs(arguments, reference, 2)
    }

    fn run_with_jobs(
        &self,
        arguments: &[&str],
        reference: Option<&Reference>,
        jobs: usize,
    ) -> Output {
        let store = IMPORT_STORE.get_or_init(|| {
            let path = std::env::temp_dir().join(format!(
                "fln-lake-executable-imports-{}",
                std::process::id(),
            ));
            std::fs::create_dir_all(&path).unwrap();
            path
        });
        Command::new(env!("CARGO_BIN_EXE_lake"))
            .arg("--dir")
            .arg(&self.0)
            .arg("--jobs")
            .arg(jobs.to_string())
            .args(arguments)
            .current_dir(std::env::temp_dir())
            .env(
                "LEAN_PATH",
                reference.map_or_else(|| self.0.join("absent-imports"), |r| r.lib.clone()),
            )
            .env("FLN_IMPORT_REUSE_DIR", store)
            .output()
            .unwrap()
    }
}

impl Drop for Package {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

struct Reference {
    lake: PathBuf,
    lib: PathBuf,
}

fn reference() -> Option<&'static Reference> {
    static REFERENCE: OnceLock<Option<Reference>> = OnceLock::new();
    REFERENCE
        .get_or_init(|| {
            let row = include_str!("../../../SUITE.lock")
                .lines()
                .find(|line| line.starts_with("reference leanprover/lean4 "))
                .unwrap();
            let field = |key: &str| {
                row.split_whitespace()
                    .find_map(|word| word.strip_prefix(key))
                    .unwrap()
            };
            let lean = std::env::var_os("FLN_REFERENCE_LEAN")
                .or_else(|| std::env::var_os("FLN_REFERENCE_BIN"))
                .map(PathBuf::from)
                .or_else(|| {
                    std::env::var_os("FLN_REFERENCE_LIB")
                        .map(|path| PathBuf::from(path).join("../../bin/lean"))
                })
                .or_else(|| {
                    std::env::var_os("HOME").map(|home| {
                        PathBuf::from(home)
                            .join(".elan/toolchains")
                            .join(format!("leanprover--lean4---{}", field("tag=")))
                            .join("bin/lean")
                    })
                })
                .filter(|binary| binary.is_file());
            let Some(lean) = lean else {
                assert!(
                    std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                    "pinned Reference required for Lake executable tests",
                );
                eprintln!("SKIP: pinned Reference absent; executable rejection controls still run");
                return None;
            };
            let pin = Command::new(&lean).arg("--githash").output().unwrap();
            assert!(pin.status.success(), "{pin:?}");
            assert_eq!(
                String::from_utf8(pin.stdout).unwrap().trim(),
                field("commit=")
            );
            let lib = std::env::var_os("FLN_REFERENCE_LIB")
                .map(PathBuf::from)
                .unwrap_or_else(|| lean.parent().unwrap().join("../lib/lean"));
            assert!(
                lib.join("Init/System/IO.olean").is_file(),
                "{}",
                lib.display()
            );
            let lake = lean.with_file_name("lake");
            assert!(lake.is_file(), "{}", lake.display());
            Some(Reference { lake, lib })
        })
        .as_ref()
}

fn text(bytes: &[u8]) -> &str {
    std::str::from_utf8(bytes).unwrap()
}

const CONFIG: &str = concat!(
    "name = \"program\"\n",
    "srcDir = \"src\"\n",
    "buildDir = \"artifacts\"\n",
    "[[lean_lib]]\n",
    "name = \"Core\"\n",
    "roots = [\"Shared\"]\n",
    "srcDir = \"library\"\n",
    "[[lean_exe]]\n",
    "name = \"runner\"\n",
    "root = \"App.Main\"\n",
    "srcDir = \"application\"\n",
);

const LEAN_CONFIG: &str = r#"import Lake
open System Lake DSL
def entryName (suffix : String) : Lean.Name :=
  Lean.Name.str (Lean.Name.str Lean.Name.anonymous "App") suffix
package program where
  srcDir := FilePath.mk ("s" ++ "rc")
  buildDir := FilePath.mk "artifacts"
lean_lib Core where
  roots := #[`Shared]
  srcDir := FilePath.mk ("lib" ++ "rary")
@[default_target] lean_exe runner where
  root := entryName "Main"
  srcDir := FilePath.mk ("appli" ++ "cation")
"#;

const LIBRARY: &str = concat!(
    "prelude\nimport Init.System.IO\n",
    "def Shared.decorate (value : String) : String := \"prefix:\" ++ value\n",
);

const MAIN: &str = concat!(
    "prelude\nimport Shared\n",
    "def main (args : List String) : IO UInt32 := do\n",
    "  for value in args do\n",
    "    IO.println (Shared.decorate value)\n",
    "  pure 7\n",
);

fn executable() -> Package {
    let package = Package::new(CONFIG);
    package.write("src/library/Shared.lean", LIBRARY);
    package.write("src/application/App/Main.lean", MAIN);
    package
}

#[test]
fn configured_root_library_directory_and_raw_argv_match_the_reference() {
    let _guard = serial_execution();
    let Some(reference) = reference() else {
        return;
    };
    let native = executable();
    let oracle = executable();
    let args = [
        "--help",
        "--version",
        "--json",
        "--jobs=0",
        "--import-posture=invalid",
        "--fln-max-steps=0",
        "--dir",
        "/missing",
        "--",
        "",
        "λ🙂",
        "a b",
    ];
    let mut command = vec!["exe", "runner"];
    command.extend(args);
    let output = native.run_with_jobs(&command, Some(reference), 1);
    let expected = args.map(|arg| format!("prefix:{arg}\n")).join("");
    assert_eq!(output.status.code(), Some(7), "{output:?}");
    assert_eq!(text(&output.stdout), expected, "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert!(!native.0.join("artifacts").exists());

    // The oracle builds and runs this same package through real Lake, rather
    // than treating our source parser or target planner as its own oracle.
    let output = Command::new(&reference.lake)
        .arg("--dir")
        .arg(&oracle.0)
        .args(&command)
        .env("LEAN_PATH", &reference.lib)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(7), "{output:?}");
    assert_eq!(text(&output.stdout), expected, "{output:?}");

    let alias = native.run(&["exec", "runner", "alias"], Some(reference));
    assert_eq!(alias.status.code(), Some(7), "{alias:?}");
    assert_eq!(text(&alias.stdout), "prefix:alias\n");
}

#[test]
fn checked_lean_configuration_computes_executable_roots_and_refuses_invalid_values() {
    let _guard = serial_execution();
    let Some(reference) = reference() else {
        return;
    };
    let package = Package::with_configuration("lakefile.lean", LEAN_CONFIG);
    let oracle = Package::with_configuration("lakefile.lean", LEAN_CONFIG);
    for package in [&package, &oracle] {
        package.write("src/library/Shared.lean", LIBRARY);
        package.write("src/application/App/Main.lean", MAIN);
    }

    let presence = package.run(&["check-build"], Some(reference));
    assert!(presence.status.success(), "{presence:?}");
    let unavailable = package.run(&["build"], Some(reference));
    assert_eq!(unavailable.status.code(), Some(1), "{unavailable:?}");
    assert!(
        text(&unavailable.stderr).contains("default library and executable facets are unavailable"),
        "{unavailable:?}",
    );
    let output = package.run(&["exe", "runner", "computed"], Some(reference));
    assert_eq!(output.status.code(), Some(7), "{output:?}");
    assert_eq!(text(&output.stdout), "prefix:computed\n", "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert!(!package.0.join("artifacts").exists());

    let oracle = Command::new(&reference.lake)
        .arg("--dir")
        .arg(&oracle.0)
        .args(["exe", "runner", "computed"])
        .env("LEAN_PATH", &reference.lib)
        .output()
        .unwrap();
    assert_eq!(oracle.status.code(), output.status.code(), "{oracle:?}");
    assert_eq!(oracle.stdout, output.stdout, "{oracle:?}");

    package.write(
        "src/application/App/Other.lean",
        "prelude\nimport Shared\ndef main : IO UInt32 := do\n  IO.println \"other\"\n  pure 11\n",
    );
    package.write(
        "lakefile.lean",
        &LEAN_CONFIG.replace("root := entryName \"Main\"", "root := entryName \"Other\""),
    );
    let changed = package.run(&["exe", "runner"], Some(reference));
    assert_eq!(changed.status.code(), Some(11), "{changed:?}");
    assert_eq!(text(&changed.stdout), "other\n", "{changed:?}");
    assert!(changed.stderr.is_empty(), "{changed:?}");

    for invalid in [
        LEAN_CONFIG.replace("root := entryName \"Main\"", "root := (42 : Nat)"),
        LEAN_CONFIG.replace(
            "root := entryName \"Main\"",
            "root := Lean.Name.str Lean.Name.anonymous \"../escape\"",
        ),
        LEAN_CONFIG.replace(
            "root := entryName \"Main\"",
            "root := Lean.Name.num Lean.Name.anonymous 1",
        ),
        format!(
            "{LEAN_CONFIG}lean_exe other where\n  root := entryName \"Main\"\n  srcDir := \"other\"\n"
        ),
        LEAN_CONFIG.replace(
            "srcDir := FilePath.mk (\"appli\" ++ \"cation\")",
            "srcDir := FilePath.mk (\"appli\" ++ \"cation\")\n  moreLinkArgs := #[\"-unexpected\"]",
        ),
    ] {
        package.write("lakefile.lean", &invalid);
        let refused = package.run(&["exe", "runner", "must not print"], Some(reference));
        assert_eq!(refused.status.code(), Some(1), "{invalid}\n{refused:?}");
        assert!(refused.stdout.is_empty(), "{invalid}\n{refused:?}");
        assert!(!package.0.join("artifacts").exists());
    }
    package.write("lakefile.lean", LEAN_CONFIG);
    let repaired = package.run(&["exe", "runner", "repaired"], Some(reference));
    assert_eq!(repaired.status.code(), Some(7), "{repaired:?}");
    assert_eq!(text(&repaired.stdout), "prefix:repaired\n", "{repaired:?}");

    let default = Package::with_configuration(
        "lakefile.lean",
        "import Lake\nopen Lake DSL\npackage defaulted\nlean_exe Main\n",
    );
    default.write(
        "Main.lean",
        "def main : IO Unit := IO.println \"default-root\"\n",
    );
    let output = default.run(&["exe", "Main"], Some(reference));
    assert!(output.status.success(), "{output:?}");
    assert_eq!(text(&output.stdout), "default-root\n", "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
}

#[test]
fn native_execution_rechecks_changed_library_source_and_preserves_nonzero_status() {
    let _guard = serial_execution();
    let Some(reference) = reference() else {
        return;
    };
    let package = executable();
    let first = package.run(&["exe", "runner", "same"], Some(reference));
    assert_eq!(first.status.code(), Some(7), "{first:?}");
    assert_eq!(text(&first.stdout), "prefix:same\n");
    package.write(
        "src/library/Shared.lean",
        "prelude\nimport Init.System.IO\ndef Shared.decorate (value : String) : String := \"changed:\" ++ value\n",
    );
    let next = package.run(&["exe", "runner", "same"], Some(reference));
    assert_eq!(next.status.code(), Some(7), "{next:?}");
    assert_eq!(text(&next.stdout), "changed:same\n");
    assert!(!package.0.join("artifacts").exists());
}

#[test]
fn ordinary_executable_loads_implicit_init() {
    let _guard = serial_execution();
    let Some(reference) = reference() else {
        return;
    };
    let package = Package::new(SIMPLE_CONFIG);
    package.write(
        "Main.lean",
        "def main : IO Unit := IO.println \"implicit-init\"\n",
    );
    let output = package.run(&["exe", "runner"], Some(reference));
    assert!(output.status.success(), "{output:?}");
    assert_eq!(text(&output.stdout), "implicit-init\n", "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert!(!package.0.join(".lake/build").exists());
}

#[test]
fn frontend_output_and_main_are_each_executed_once() {
    let _guard = serial_execution();
    let Some(reference) = reference() else {
        return;
    };
    let package = executable();
    package.write(
        "src/application/App/Main.lean",
        "prelude\nimport Shared\n#eval IO.println \"frontend\"\ndef main : IO Unit := IO.println \"main\"\n",
    );
    let output = package.run(&["exe", "runner"], Some(reference));
    assert!(output.status.success(), "{output:?}");
    assert_eq!(text(&output.stdout), "frontend\nmain\n", "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
}

#[test]
fn checked_main_contract_and_vm_nonanswers_keep_their_dispositions() {
    let _guard = serial_execution();
    let Some(reference) = reference() else {
        return;
    };
    let package = executable();
    package.write(
        "src/application/App/Main.lean",
        "prelude\nimport Shared\ndef main : IO UInt32 := pure 300\n",
    );
    let output = package.run(&["exe", "runner"], Some(reference));
    assert_eq!(output.status.code(), Some(44), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");

    let stopped = package.run(&["--fln-max-steps", "1", "exe", "runner"], Some(reference));
    assert_eq!(stopped.status.code(), Some(3), "{stopped:?}");
    assert!(stopped.stdout.is_empty(), "{stopped:?}");
    assert!(
        text(&stopped.stderr).contains("inconclusive"),
        "{stopped:?}"
    );

    package.write(
        "src/application/App/Main.lean",
        "prelude\nimport Shared\ndef main : Nat := 1\n",
    );
    let invalid = package.run(&["exe", "runner"], Some(reference));
    assert_eq!(invalid.status.code(), Some(1), "{invalid:?}");
    assert!(invalid.stdout.is_empty(), "{invalid:?}");
    assert!(
        text(&invalid.stderr).contains("main` function must have type"),
        "{invalid:?}"
    );
}

#[test]
fn bad_dependency_cannot_run_main_and_repair_recovers() {
    let _guard = serial_execution();
    let Some(reference) = reference() else {
        return;
    };
    let package = executable();
    package.write(
        "src/library/Shared.lean",
        &format!("{LIBRARY}theorem impossible (P Q : Prop) (h : P) : Q := h\n"),
    );
    let refused = package.run(&["exe", "runner", "must not print"], Some(reference));
    assert_eq!(refused.status.code(), Some(1), "{refused:?}");
    assert!(refused.stdout.is_empty(), "{refused:?}");
    let diagnostic = text(&refused.stderr);
    assert!(diagnostic.contains("module `Shared`"), "{refused:?}");
    assert!(diagnostic.contains("NotDefEq"), "{refused:?}");
    assert!(!package.0.join("artifacts").exists());
    package.write("src/library/Shared.lean", LIBRARY);
    let recovered = package.run(&["exe", "runner", "recovered"], Some(reference));
    assert_eq!(recovered.status.code(), Some(7), "{recovered:?}");
    assert_eq!(text(&recovered.stdout), "prefix:recovered\n");
}

const SIMPLE_CONFIG: &str =
    "name = \"isolated\"\n[[lean_exe]]\nname = \"runner\"\nroot = \"Main\"\n";

#[test]
fn unknown_targets_and_undeclared_source_imports_are_refused() {
    let package = Package::new(SIMPLE_CONFIG);
    package.write("Main.lean", "prelude\nimport Loose\n");
    package.write(
        "Loose.lean",
        "prelude\ntheorem valid (P : Prop) (h : P) : P := h\n",
    );
    let unknown = package.run(&["exe", "missing"], None);
    assert_eq!(unknown.status.code(), Some(1), "{unknown:?}");
    assert!(
        text(&unknown.stderr).contains("unknown executable"),
        "{unknown:?}"
    );
    let loose = package.run(&["exe", "runner"], None);
    assert_eq!(loose.status.code(), Some(1), "{loose:?}");
    assert!(text(&loose.stderr).contains("import `Loose`"), "{loose:?}");
    assert!(loose.stdout.is_empty(), "{loose:?}");

    package.write(
        "lakefile.toml",
        &format!("{SIMPLE_CONFIG}[[lean_lib]]\nname = \"Loose\"\n"),
    );
    let declared = package.run(&["exe", "runner"], None);
    assert_eq!(declared.status.code(), Some(1), "{declared:?}");
    assert!(
        text(&declared.stderr).contains("unknown executable declaration `main`"),
        "{declared:?}"
    );
    let library = package.run(&["exe", "Loose"], None);
    assert_eq!(library.status.code(), Some(1), "{library:?}");
    assert!(
        text(&library.stderr).contains("unknown executable"),
        "{library:?}"
    );
}

#[test]
fn executable_targets_cannot_alias_the_same_root_module() {
    let config = format!(
        "{SIMPLE_CONFIG}[[lean_exe]]\nname = \"other\"\nroot = \"Main\"\nsrcDir = \"other\"\n",
    );
    let package = Package::new(&config);
    package.write("Main.lean", "prelude\n");
    let refused = package.run(&["exe", "runner"], None);
    assert_eq!(refused.status.code(), Some(1), "{refused:?}");
    assert!(
        text(&refused.stderr).contains("share root module `Main`"),
        "{refused:?}",
    );
    assert!(refused.stdout.is_empty(), "{refused:?}");

    // Only the selected executable is read. Distinct, unused targets need not
    // have source files before this program can reach its main check.
    package.write(
        "lakefile.toml",
        &format!(
            "{SIMPLE_CONFIG}[[lean_exe]]\nname = \"other\"\nroot = \"Other\"\nsrcDir = \"other\"\n",
        ),
    );
    let distinct = package.run(&["exe", "runner"], None);
    assert_eq!(distinct.status.code(), Some(1), "{distinct:?}");
    assert!(
        text(&distinct.stderr).contains("unknown executable declaration `main`"),
        "{distinct:?}",
    );
}

#[test]
fn source_cycles_and_directory_escape_never_execute() {
    let package = Package::new(&format!("{SIMPLE_CONFIG}[[lean_lib]]\nname = \"Lib\"\n",));
    package.write("Main.lean", "prelude\nimport Lib.A\n");
    package.write("Lib/A.lean", "prelude\nimport Lib.B\n");
    package.write("Lib/B.lean", "prelude\nimport Lib.A\n");
    let cycle = package.run(&["exe", "runner"], None);
    assert_eq!(cycle.status.code(), Some(1), "{cycle:?}");
    assert!(
        text(&cycle.stderr).to_lowercase().contains("cycl"),
        "{cycle:?}"
    );
    assert!(cycle.stdout.is_empty(), "{cycle:?}");

    package.write(
        "lakefile.toml",
        "name = \"escape\"\nsrcDir = \"..\"\n[[lean_exe]]\nname = \"runner\"\nroot = \"Main\"\n",
    );
    let escaped = package.run(&["exe", "runner"], None);
    assert_eq!(escaped.status.code(), Some(1), "{escaped:?}");
    assert!(
        text(&escaped.stderr).contains("must stay within the package"),
        "{escaped:?}"
    );
    assert!(escaped.stdout.is_empty(), "{escaped:?}");
}

#[cfg(unix)]
#[test]
fn source_symlinks_are_refused_before_their_targets_are_read() {
    let package = Package::new(SIMPLE_CONFIG);
    let outside = Package::new(SIMPLE_CONFIG);
    outside.write("Main.lean", "prelude\n");
    std::os::unix::fs::symlink(outside.0.join("Main.lean"), package.0.join("Main.lean")).unwrap();
    let output = package.run(&["exe", "runner"], None);
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(
        text(&output.stderr).contains("refusing symlink"),
        "{output:?}"
    );
    assert!(output.stdout.is_empty(), "{output:?}");
}

#[test]
fn executable_arguments_are_bounded_before_configuration_is_loaded() {
    let package = Package::new("not valid configuration");
    let output = fln_cli::run_lake([
        OsString::from("--dir"),
        package.0.as_os_str().to_owned(),
        OsString::from("exe"),
        OsString::from("runner"),
        OsString::from("x".repeat(fln_cli::SOURCE_RUN_DEFAULT_MAX_BYTES)),
    ]);
    assert_eq!(output.exit_code, 3, "{output:?}");
    assert!(
        output.stderr.contains("script arguments exceed"),
        "{output:?}"
    );
    assert!(!output.stderr.contains("configuration"), "{output:?}");
}

#[cfg(unix)]
#[test]
fn non_utf8_program_arguments_are_not_lossily_rewritten_or_parsed_as_lake_options() {
    use std::os::unix::ffi::OsStringExt;
    let package = Package::new("not valid configuration");
    let output = fln_cli::run_lake([
        OsString::from("--dir"),
        package.0.as_os_str().to_owned(),
        OsString::from("exe"),
        OsString::from("runner"),
        OsString::from_vec(vec![0xff]),
    ]);
    assert_eq!(output.exit_code, 1, "{output:?}");
    assert!(
        output
            .stderr
            .contains("script argument 0 is not valid UTF-8"),
        "{output:?}"
    );
    assert!(!output.stderr.contains("configuration"), "{output:?}");
}

#[test]
fn leading_options_restart_after_the_command_and_end_before_program_arguments() {
    let package = Package::new(SIMPLE_CONFIG);
    package.write("Main.lean", "prelude\n");
    for args in [
        vec![
            "--",
            "exe",
            "--import-posture",
            "recheck",
            "runner",
            "--import-posture",
            "invalid",
        ],
        vec!["exe", "--", "runner", "--jobs=0"],
        vec!["--", "exe", "--", "runner", "--help"],
    ] {
        let output = package.run(&args, None);
        assert_eq!(output.status.code(), Some(1), "{args:?}: {output:?}");
        assert!(
            text(&output.stderr).contains("unknown executable declaration `main`"),
            "{args:?}: {output:?}",
        );
        assert!(output.stdout.is_empty(), "{output:?}");
    }
    let duplicate = package.run(
        &[
            "--import-posture=recheck",
            "exe",
            "--import-posture=recheck",
            "runner",
        ],
        None,
    );
    assert_eq!(duplicate.status.code(), Some(1), "{duplicate:?}");
    assert!(
        text(&duplicate.stderr).contains("--import-posture may be supplied at most once"),
        "{duplicate:?}",
    );
}

#[test]
fn directory_option_values_are_never_commands_or_posture_options() {
    let package = Package::new(SIMPLE_CONFIG);
    for directory in ["exe", "--import-posture=invalid"] {
        package.write(&format!("{directory}/lakefile.toml"), SIMPLE_CONFIG);
        package.write(&format!("{directory}/Main.lean"), "prelude\n");
        let output = Command::new(env!("CARGO_BIN_EXE_lake"))
            .current_dir(&package.0)
            .args(["--dir", directory, "exe", "runner"])
            .env("LEAN_PATH", package.0.join("absent-imports"))
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(
            text(&output.stderr).contains("unknown executable declaration `main`"),
            "{directory}: {output:?}",
        );
        assert!(output.stdout.is_empty(), "{output:?}");
    }
}

#[test]
fn help_names_the_native_execution_contract_without_claiming_linked_artifacts() {
    let output = fln_cli::run_lake(["help", "exe"].map(OsString::from));
    assert_eq!(output.exit_code, 0, "{output:?}");
    assert!(
        output.stdout.contains("runs main once on Golem"),
        "{output:?}"
    );
    assert!(
        output.stdout.contains("does not emit a native binary"),
        "{output:?}"
    );
}
