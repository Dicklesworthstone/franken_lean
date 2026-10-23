//! Index notation (`Init/GetElem.lean`), checked over the pinned `Init.GetElem` closure. Each form
//! expands as its macro does:
//! - `x[i]` is `getElem x i (by get_elem_tactic)`;
//! - `x[i]'h` is `getElem x i h`;
//! - `x[i]?` is `getElem? x i`;
//! - `x[i]!` is `getElem! x i`.
//!
//! The proof is attempted by `done`, `assumption` and then `omega`, one of the pin's
//! `get_elem_tactic_extensible` rules, where its closure declares it. Where the pin goes on to its
//! other rules (`simp +arith`, `trivial`, ...), the index is refused here. Every
//! program here was run through the pinned `lean` v4.32.0 with the same header first
//! (2026-10-11), with the same verdict.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.GetElem\n";

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
        .filter(|lib| lib.join("Init/GetElem.olean").is_file());
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
        "fln-index-notation-{case}-{}-{}",
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
fn index_notation_elaborates_as_its_macros() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("accepted");
    for (name, program) in [
        (
            "assumption",
            "def g (xs : List Nat) (i : Nat) (h : i < xs.length) : Nat := xs[i]\n",
        ),
        (
            "dite",
            "def g (xs : Array Nat) (i : Nat) : Nat := if h : i < xs.size then xs[i] else 0\n",
        ),
        (
            "proof",
            "def g (xs : List Nat) (i : Nat) (h : i < xs.length) : Nat := xs[i]'h\n",
        ),
        ("optional", "def g (xs : List Nat) : Option Nat := xs[0]?\n"),
        (
            "optional_rfl",
            "theorem t : [1, 2, 3][1]? = some 2 := rfl\n",
        ),
        (
            "same_element",
            "theorem t (xs : List Nat) (i : Nat) (h : i < xs.length) : xs[i] = xs[i]'h := rfl\n",
        ),
    ] {
        let (code, stdout, stderr) = check(&lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stdout}\n{stderr}");
    }
}

#[test]
fn index_notation_refusals_match_the_pin() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("refused");
    for (name, program, pin) in [
        (
            "no_proof",
            "def g (xs : List Nat) (i : Nat) : Nat := xs[i]\n",
            "failed to prove index is valid",
        ),
        (
            "conjunction",
            "def g (xs : List Nat) (i : Nat) (h : i < xs.length ∧ True) : Nat := xs[i]\n",
            "failed to prove index is valid",
        ),
        (
            "wrong_proof",
            "def g (xs : List Nat) (i : Nat) (h : i < 5) : Nat := xs[i]'h\n",
            "Application type mismatch",
        ),
        (
            "wrong_value",
            "theorem t : [1, 2, 3][1]? = some 3 := rfl\n",
            "Not a definitional equality",
        ),
        (
            "type",
            "def g (xs : List Nat) : Bool := xs[0]?\n",
            "Type mismatch",
        ),
        (
            "not_inhabited",
            "structure E where\n  x : Nat\n  h : x = x + 1\ndef g (xs : Array E) : E := xs[0]!\n",
            "failed to synthesize instance of type class",
        ),
    ] {
        let (code, stdout, stderr) = check(&lib, &root, name, program);
        assert_ne!(
            code, 0,
            "{name} accepted (the pin: {pin}): {program}\n{stdout}"
        );
        assert!(stderr.contains("\"outcome\""), "{name}: {stderr}");
    }
}
