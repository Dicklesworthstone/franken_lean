//! `if b then t else e` on a `Bool` `b`, as the pin's `ite (b = true) t e` (the `boolToProp`
//! coercion), and `if h : b`, as its `dite` with `h : b = true`. The branches are checked against the
//! same expected type: `b` is never replaced by a constructor inside them. A match on `b` itself
//! used to be the elaboration here. It accepted `if b then Or.inl rfl else Or.inr rfl` against
//! `b = true ∨ b = false`, and a dependent `if b then (0 : Nat) else true`, both of which the pin
//! refuses. It also refused a branch statement after an undefaulted `let x := 1` in `do`, which
//! reverted `x` and lost the expected monad's `Id`. Every program here was run through the pinned
//! `lean` v4.32.0 with the same header first (2026-10-11), with the same verdict.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const CORE: &str = "prelude\nimport Init.Core\n";
const DO: &str = "prelude\nimport Init.Data.List.Control\nimport Init.Control.Id\n";

fn pinned_lib() -> Option<PathBuf> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                    .join("lib/lean")
            })
        })
        .filter(|lib| lib.join("Init/Data/List/Control.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference library is required"
    );
    if lib.is_none() {
        eprintln!("SKIP: pinned Reference lib/lean absent");
    }
    lib
}

fn workspace(case: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-bool-conditions-{case}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// `fln check-source --json` on `header` + `program`: (exit code, stdout, stderr).
fn check(
    lib: &Path,
    root: &Path,
    name: &str,
    header: &str,
    program: &str,
) -> (i32, String, String) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{header}{program}")).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(&entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed CLI");
    (
        output.status.code().expect("normal process exit"),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

#[test]
fn boolean_conditions_decide_without_refining_the_branches() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("accepted");
    for (name, header, program) in [
        (
            "values",
            CORE,
            "def f (b : Bool) : Nat := if b then 1 else 2\ntheorem t : f true = 1 := rfl\ntheorem u : f false = 2 := rfl\n",
        ),
        (
            "named",
            CORE,
            "def g (b : Bool) : Nat := if h : b then 1 else 2\ntheorem t : g false = 2 := rfl\ntheorem u : g true = 1 := rfl\n",
        ),
        (
            "named_nested",
            CORE,
            "def g (b : Bool) : Nat := if h : b then (if h2 : b = true then 3 else 4) else 2\ntheorem t : g true = 3 := rfl\n",
        ),
        (
            "after_numeral",
            DO,
            "def g (b : Bool) : Id Nat := do\n  let x := 1\n  if b then pure () else pure ()\n  return x\n",
        ),
        (
            "bound_after_numeral",
            DO,
            "def g (b : Bool) : Id Nat := do\n  let x := 1\n  let x : Nat ← if b then pure 10 else pure x\n  return x\n",
        ),
        (
            "bound_unannotated",
            DO,
            "def g (b : Bool) : Id Nat := do\n  let x ← if b then pure 10 else pure 1\n  return x\n",
        ),
    ] {
        let (code, _, stderr) = check(&lib, &root, name, header, program);
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
    }
}

#[test]
fn branches_that_need_the_condition_refined_are_refused() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("refused");
    for (name, program, pin) in [
        (
            "refined_proof",
            "def f (b : Bool) : b = true ∨ b = false := if b then Or.inl rfl else Or.inr rfl\n",
            "Type mismatch",
        ),
        (
            "refined_type",
            "def k (b : Bool) : (if b then Nat else Bool) := if b then (0 : Nat) else true\n",
            "Type mismatch",
        ),
    ] {
        let (code, _, _) = check(&lib, &root, name, CORE, program);
        assert_ne!(code, 0, "{name} was accepted; the pin: {pin}\n{program}");
    }
}
