//! A global lemma named in a `simp` call is retrieved as the pin's discrimination tree retrieves
//! it: by its left side's keys, arguments included (`mkSimpTheoremFromConst`,
//! `noIndexAtArgs := false`, vendored `Lean/Meta/Tactic/Simp/SimpTheorems.lean`). So `g 2 = 5`
//! is no candidate at `g (1 + 1)`, whose argument is an `HAdd.hAdd` application, not the numeral
//! `2`, even though the two unify. A hypothesis is keyed with its arguments as stars, and a
//! `no_index` argument is a star (`pushArgs`). Through `fln check-source` over `prelude`,
//! `Init.SimpLemmas` and `Init.Data.Nat.Basic`. Every program is compared with the pinned `lean`
//! v4.32.0 whenever it is present.
#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.SimpLemmas\nimport Init.Data.Nat.Basic\n";

const DEFINITIONS: &str = "def g (n : Nat) : Nat := n\naxiom g2 : g 2 = 5\n\
     def fib : Nat → Nat\n  | 0 => 0\n  | 1 => 1\n  | n+2 => fib (n+1) + fib n\n\
     theorem fib_two : fib 2 = 1 := rfl\n";

/// Accepted at the pin and here.
const ACCEPTED: &[(&str, &str)] = &[
    ("same_numeral", "example : g 2 = 5 := by simp only [g2]\n"),
    // `Nat.succ 1` is the numeral key `2` at the pin (`toNatLit?`).
    (
        "successor_numeral",
        "example : g (Nat.succ 1) = 5 := by simp only [g2]\n",
    ),
    // A hypothesis keys its arguments as stars, so it is a candidate and unifies.
    (
        "hypothesis",
        "example (h : fib 2 = 1) : fib (1 + 1) = 1 := by simp only [h]\n",
    ),
    // `tests/elab/1253.lean`: a `no_index` argument is a star.
    (
        "no_index_argument",
        "inductive Foo (f : Fin n) : Nat → Prop\n  | mk : Foo f f.val\n\
         theorem foo {f : Fin n} : Foo f (no_index f.val) := .mk\n\
         example (hf : f < n) : Foo ⟨f, hf⟩ f := by simp only [foo]\n\
         example (f : Fin n) : Foo f f.val := by simp only [foo]\n",
    ),
];

/// Rejected at the pin ("`simp` made no progress") and here: the lemma is no candidate.
const REJECTED: &[(&str, &str)] = &[
    ("sum", "example : g (1 + 1) = 5 := by simp only [g2]\n"),
    (
        "plus_zero",
        "example : g (2 + 0) = 5 := by simp only [g2]\n",
    ),
    (
        "zero_plus",
        "example : g (0 + 2) = 5 := by simp only [g2]\n",
    ),
    // `tests/elab/simpDecide.lean`'s `fail_if_success { simp only [fib_two] }`.
    (
        "rfl_theorem",
        "example : 1 = fib (1 + 1) := by simp only [fib_two]\n",
    ),
];

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
        .filter(|lib| lib.join("Init/Data/Nat/Basic.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference library is required"
    );
    if lib.is_none() {
        eprintln!("SKIP: pinned Reference lib/lean absent");
    }
    lib
}

fn workspace() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-simp-explicit-keys-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// `fln check-source` on `HEADER` + `DEFINITIONS` + `program`, and the pinned binary's exit code
/// when present.
fn check(lib: &Path, root: &Path, name: &str, program: &str) -> (i32, String, Option<i32>) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{HEADER}{DEFINITIONS}{program}")).unwrap();
    let pinned = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file());
    assert!(
        pinned.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference binary is required"
    );
    let theirs = pinned.map(|pinned| {
        Command::new(pinned)
            .arg(&entry)
            .env("LEAN_PATH", lib)
            .output()
            .expect("run the pinned lean")
            .status
            .code()
            .expect("normal pinned exit")
    });
    let ours = Command::new(env!("CARGO_BIN_EXE_fln"))
        .arg("check-source")
        .arg(&entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed CLI");
    (
        ours.status.code().expect("normal process exit"),
        String::from_utf8_lossy(&ours.stderr).into_owned(),
        theirs,
    )
}

#[test]
fn an_explicit_global_lemma_is_retrieved_by_its_keys() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    // One workspace, so the import closure is admitted once for every program.
    let root = workspace();
    for (name, program) in ACCEPTED {
        let (code, stderr, pinned) = check(&lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
        assert_eq!(pinned.unwrap_or(0), 0, "{name}: the pinned lean rejects it");
    }
    for (name, program) in REJECTED {
        let (code, stderr, pinned) = check(&lib, &root, name, program);
        assert_ne!(code, 0, "{name}: accepted {program}");
        assert!(
            stderr.contains("made no progress"),
            "{name}: not simp's own failure\n{stderr}"
        );
        assert_ne!(pinned.unwrap_or(1), 0, "{name}: the pinned lean accepts it");
    }
}

/// Closed at the pin and here: the sides agree up to Nat offsets under the head, which the pin's
/// `isDefEq` compares before reducing (`offsetCnstrs`, `isDefEqOffset`, vendored
/// `Lean/Meta/Offset.lean`). simp's `eq_self` and `rw`'s closing `rfl` both use it, at reducible
/// transparency.
const OFFSET_CLOSED: &[(&str, &str)] = &[
    ("numeral", "example : g (1 + 1) = g 2 := by simp only\n"),
    (
        "successor",
        "example (x : Nat) : g (x + 1) = g (Nat.succ x) := by simp only\n",
    ),
    (
        "nested",
        "example (x : Nat) : g (x + 1 + 1) = g (x + 2) := by simp only\n",
    ),
    (
        "rw_numeral",
        "example (a : Nat) (h : a = 1 + 1) : g a = g 2 := by rw [h]\n",
    ),
    (
        "rw_successor",
        "example (x a : Nat) (h : a = x + 1) : g a = g (Nat.succ x) := by rw [h]\n",
    ),
];

/// Left open at the pin and here: the offsets differ, or the heads do.
const OFFSET_OPEN: &[(&str, &str)] = &[
    (
        "other_numeral",
        "example : g (1 + 1) = g 3 := by simp only\n",
    ),
    (
        "other_successor",
        "example (x : Nat) : g (x + 2) = g (Nat.succ x) := by simp only\n",
    ),
    (
        "rw_other_numeral",
        "example (a : Nat) (h : a = 1 + 1) : g a = g 3 := by rw [h]\n",
    ),
    (
        "other_head",
        "def k (n : Nat) : Nat := n\nexample : g 2 = k 2 := by simp only\n",
    ),
];

#[test]
fn a_reflexive_close_compares_nat_offsets_under_any_head() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    for (name, program) in OFFSET_CLOSED {
        let (code, stderr, pinned) = check(&lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
        assert_eq!(pinned.unwrap_or(0), 0, "{name}: the pinned lean rejects it");
    }
    for (name, program) in OFFSET_OPEN {
        let (code, stderr, pinned) = check(&lib, &root, name, program);
        assert_ne!(code, 0, "{name}: accepted {program}");
        assert!(
            stderr.contains("made no progress") || stderr.contains("unsolved goals"),
            "{name}: not the tactic's own failure\n{stderr}"
        );
        assert_ne!(pinned.unwrap_or(1), 0, "{name}: the pinned lean accepts it");
    }
}

#[test]
fn a_required_reference_without_its_binary_is_refused_before_comparison() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let partial_lib = root.join("lib/lean");
    let prerequisite = Path::new("Init/Data/Nat/Basic.olean");
    std::fs::create_dir_all(partial_lib.join(prerequisite).parent().unwrap()).unwrap();
    // Preserve the real artifact that pinned_lib checks. The executable is
    // deliberately absent; the child must refuse before invoking either prover.
    std::fs::copy(lib.join(prerequisite), partial_lib.join(prerequisite)).unwrap();
    let output = Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "an_explicit_global_lemma_is_retrieved_by_its_keys",
            "--nocapture",
        ])
        .env("FLN_REQUIRE_REFERENCE", "1")
        .env("FLN_REFERENCE_LIB", partial_lib)
        .output()
        .expect("run the actual comparison with the oracle executable absent");
    assert!(!output.status.success(), "a required oracle was absent");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("the pinned Reference binary is required"),
        "the child failed for another reason: {stderr}"
    );
}
