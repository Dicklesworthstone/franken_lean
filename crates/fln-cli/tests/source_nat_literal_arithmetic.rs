//! Literal arithmetic by `rfl` over the pinned `Init.Core` closure, where `Nat.add`, `Nat.mul`,
//! `Nat.sub`, `Nat.div`, `Nat.mod`, `Nat.beq` and `Nat.ble` borrow their operands
//! (`(@& Nat) → (@& Nat) → Nat`, vendored Init/Prelude.lean). `@&` is a `borrowed` annotation that
//! stays in the declaration's type. The unifier's literal folding (the pin's `reduceBinNatOp`)
//! must still recognize these operations. Before, it refused them, and `(1 + 2) * (3 + 4) = 21`
//! unfolded `Nat.mul` structurally into the unification step limit. Every program here was run
//! through the pinned `lean` v4.32.0 with the same header first (2026-10-11), with the same verdict.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Core\n";

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
        .filter(|lib| lib.join("Init/Core.olean").is_file());
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
        "fln-nat-literal-arithmetic-{case}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// `fln check-source --json` on `HEADER` + `program`: (exit code, stdout, stderr).
fn check(lib: &Path, root: &Path, name: &str, program: &str) -> (i32, String, String) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
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
fn literal_arithmetic_folds_through_borrowed_operations() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("accepted");
    for (name, program) in [
        ("nested", "theorem t : (1 + 2) * (3 + 4) = 21 := rfl\n"),
        ("large", "theorem t : 12345 * 6789 = 83810205 := rfl\n"),
        ("truncated", "theorem t : 100 - 200 = 0 := rfl\n"),
        ("division", "theorem t : 10 / 3 = 3 := rfl\n"),
        ("remainder", "theorem t : 10 % 3 = 1 := rfl\n"),
        ("beq", "theorem t : (5 == 5) = true := rfl\n"),
        ("ble", "theorem t : Nat.ble 3 5 = true := rfl\n"),
        ("succ", "theorem t : Nat.succ (2 * 3) = 7 := rfl\n"),
        (
            "definition",
            "def n := (1 + 2) * (3 + 4)\ntheorem t : n = 21 := rfl\n",
        ),
        (
            "function",
            "def f (x : Nat) := x * x + 1\ntheorem t : f 12 = 145 := rfl\n",
        ),
    ] {
        let (code, stdout, stderr) = check(&lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stdout}\n{stderr}");
    }
}

#[test]
fn wrong_literal_arithmetic_is_refused_as_at_the_pin() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("refused");
    // The pin: "Not a definitional equality" for each.
    for (name, program) in [
        ("nested", "theorem t : (1 + 2) * (3 + 4) = 20 := rfl\n"),
        ("large", "theorem t : 12345 * 6789 = 83810206 := rfl\n"),
        ("subtraction", "theorem t : 100 - 2 = 97 := rfl\n"),
        ("division", "theorem t : 10 / 3 = 4 := rfl\n"),
        ("remainder", "theorem t : 10 % 3 = 2 := rfl\n"),
        ("beq", "theorem t : (5 == 6) = true := rfl\n"),
        ("ble", "theorem t : Nat.ble 5 3 = true := rfl\n"),
        ("succ", "theorem t : Nat.succ (2 * 3) = 6 := rfl\n"),
        (
            "definition",
            "def n := (1 + 2) * (3 + 4)\ntheorem t : n = 22 := rfl\n",
        ),
        (
            "function",
            "def f (x : Nat) := x * x + 1\ntheorem t : f 12 = 144 := rfl\n",
        ),
    ] {
        let (code, stdout, stderr) = check(&lib, &root, name, program);
        assert_ne!(
            code, 0,
            "{name} accepted (the pin: Not a definitional equality): {program}\n{stdout}"
        );
        assert!(stderr.contains("\"outcome\""), "{name}: {stderr}");
    }
}
