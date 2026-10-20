//! Exact upstream regression gate for fln-noncomputable-check-false-refusal-bhf2.
//! Success requires both original sources to compile with the pin's stdout,
//! live noncomputable dependencies to remain refused, and recursive execution.
//! The Reference is used only as an external differential oracle in these tests.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const NONCOMP: &str = include_str!("../../../vendor/lean4-src/tests/elab/noncomp.lean");
const WF: &str = include_str!("../../../vendor/lean4-src/tests/elab/wfLean3Issue.lean");

fn reference() -> Option<(PathBuf, PathBuf)> {
    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                    .join("lib/lean")
            })
        });
    let found = library.and_then(|library| {
        let compiler = library.parent()?.parent()?.join("bin/lean");
        (compiler.is_file() && library.join("Init.olean").is_file()).then_some((library, compiler))
    });
    let Some((library, compiler)) = found else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "FLN_REQUIRE_REFERENCE requires both the pinned compiler and its lib/lean"
        );
        eprintln!(
            "SKIP: exact noncomputability regressions require the pinned compiler and lib/lean"
        );
        return None;
    };
    let version = Command::new(&compiler)
        .arg("--version")
        .output()
        .expect("read Reference version");
    assert!(version.status.success());
    let version = String::from_utf8(version.stdout).expect("Reference version is UTF-8");
    assert!(
        version.split_whitespace().any(|word| {
            word.trim_end_matches(',') == fln::OLEAN_PIN_TAG.trim_start_matches('v')
        }),
        "wrong Reference toolchain: {version}"
    );
    Some((
        library.canonicalize().unwrap(),
        compiler.canonicalize().unwrap(),
    ))
}

fn workspace(label: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-noncomputable-regression-{label}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

fn execute(binary: &Path, library: &Path, root: &Path, source: &Path, native: bool) -> Output {
    let mut command = Command::new(binary);
    command
        .arg(source)
        .current_dir(root)
        .env("LEAN_PATH", library);
    if native {
        command.env("FLN_IMPORT_REUSE_DIR", root.join("import-records"));
    }
    command.output().expect("execute the real compiler process")
}

fn compare(label: &str, source: &str, accepts: bool, stdout: Option<&[u8]>) {
    let Some((library, reference)) = reference() else {
        return;
    };
    let root = workspace(label);
    let path = root.join(format!("{label}.lean"));
    // Preserve the original upstream source, including its ordinary implicit
    // Init import. No reduced header, retagged definition or larger budget.
    std::fs::write(&path, source.as_bytes()).unwrap();
    let pinned = execute(&reference, &library, &root, &path, false);
    assert_eq!(
        pinned.status.success(),
        accepts,
        "Reference changed {label}: stdout={} stderr={}",
        String::from_utf8_lossy(&pinned.stdout),
        String::from_utf8_lossy(&pinned.stderr)
    );
    let native = execute(
        Path::new(env!("CARGO_BIN_EXE_lean")),
        &library,
        &root,
        &path,
        true,
    );
    if accepts {
        assert!(
            native.status.success(),
            "native failed {label}: stdout={} stderr={}",
            String::from_utf8_lossy(&native.stdout),
            String::from_utf8_lossy(&native.stderr)
        );
        assert_eq!(
            native.stdout, pinned.stdout,
            "{label}: exact stdout mismatch"
        );
        assert_eq!(native.stderr, pinned.stderr, "{label}: unexpected stderr");
        if let Some(expected) = stdout {
            assert_eq!(native.stdout, expected, "{label}: actual evaluation result");
        }
    } else {
        assert_eq!(
            pinned.status.code(),
            Some(1),
            "{label}: Reference did not reject normally"
        );
        assert_eq!(
            native.status.code(),
            Some(1),
            "{label}: resource stops, crashes and unsupported capabilities are not this rejection: stdout={} stderr={}",
            String::from_utf8_lossy(&native.stdout),
            String::from_utf8_lossy(&native.stderr)
        );
        let diagnostic = format!(
            "{}{}",
            String::from_utf8_lossy(&native.stdout),
            String::from_utf8_lossy(&native.stderr)
        );
        assert!(
            diagnostic.contains("failed to compile definition")
                && diagnostic.contains("noncomputable"),
            "{label}: refused for the wrong reason: {diagnostic}"
        );
    }
}

#[test]
fn original_noncomp_fixture_compiles_with_exact_reference_output() {
    compare("noncomp", NONCOMP, true, None);
}

#[test]
fn original_wf_lean3_issue_compiles_with_exact_reference_output() {
    compare("wfLean3Issue", WF, true, None);
}

#[test]
fn original_wf_lean3_issue_executes_recursive_calls_in_the_native_vm() {
    compare(
        "wfLean3IssueEval",
        &format!("{WF}\n#eval foo 2 2\n"),
        true,
        Some(b"14\n"),
    );
}

#[test]
fn a_value_using_classical_choose_remains_noncomputable() {
    compare(
        "classicalChoose",
        "def rejected : Nat := Classical.choose (show ∃ x : Nat, x = 1 from ⟨1, rfl⟩)\n",
        false,
        None,
    );
}

#[test]
fn a_value_calling_a_noncomputable_definition_remains_noncomputable() {
    compare(
        "liveDependency",
        "noncomputable def hidden : Nat := 7\ndef rejected : Nat := hidden + 1\n",
        false,
        None,
    );
}

#[test]
fn parameterized_record_projection_matches_reference() {
    compare(
        "recordProjection",
        r#"
noncomputable def hidden : Nat := Classical.choose (show ∃ x : Nat, x = 5 from ⟨5, rfl⟩)
structure ParamRecord (n : Nat) where
  value : Nat
def record : ParamRecord hidden := { value := 42 }
def projected : Nat := record.value
#eval projected
#eval @ParamRecord.value hidden record
#eval let get : ParamRecord hidden -> Nat := @ParamRecord.value hidden; get record
"#,
        true,
        Some(b"42\n42\n42\n"),
    );
}
