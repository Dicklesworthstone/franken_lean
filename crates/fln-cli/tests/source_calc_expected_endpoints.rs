//! `calc` endpoints the expected type determines, through the installed drop-in `lean` over
//! `prelude` with `Init.NotationExtra`, `Init.Tactics` and `Init.Data.Nat.Basic`. The pin elaborates a
//! step's `by` block as a postponed synthetic hole and synthesizes it only after `elabCalc` has
//! unified the composed relation with the expected type (`ensureHasType`, vendored
//! `Lean/Elab/Calc.lean`). So in `calc _ < 4 := by decide` against `3 < 5` the tactic sees `3 < 4`.
//! Elaborated eagerly, the block met `?a < 4`, and the hole was left unresolved
//! (upstream `tests/elab/2095.lean`). A second test judges steps proved by hypotheses against
//! relations whose numerals have no type yet.
//!
//! Every program was run through the pinned `lean` v4.32.0 with the same header first (2026-10-29),
//! and the pin is consulted again when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str =
    "prelude\nimport Init.NotationExtra\nimport Init.Tactics\nimport Init.Data.Nat.Basic\n";

/// Programs the pin accepts, printing nothing: holes on either end that only the expected type
/// fixes, in term and tactic mode, with an equality step between, and a one-step chain.
const ACCEPTED: &[&str] = &[
    "example : 3 < 5 :=\n  calc\n    _ < 4 := by decide\n    _ < _ := by decide\n",
    "example : 3 < 5 := by\n  calc\n    _ < 4 := by decide\n    _ < _ := by decide\n",
    "example : 3 < 5 := by\n  calc\n    3 < 4 := by decide\n    _ < _ := by decide\n",
    "example : 3 < 5 := by\n  calc\n    _ < 4 := by decide\n    _ = 4 := by rfl\n    _ < _ := by decide\n",
    "example : 3 < 4 := by\n  calc\n    _ < 4 := by decide\n",
];

/// Programs the pin rejects: a chain that ends past the goal, a step `decide` refutes once its
/// endpoint is known, and `rfl` on a strict inequality.
const REFUSED: &[&str] = &[
    "example : 3 < 5 :=\n  calc\n    _ < 4 := by decide\n    _ < 6 := by decide\n",
    "example : 3 < 5 :=\n  calc\n    _ < 2 := by decide\n    _ < _ := by decide\n",
    "example : 3 < 5 :=\n  calc\n    _ < 4 := by rfl\n    _ < _ := by decide\n",
];

/// Programs the pin accepts, printing nothing, whose steps are proved by hypotheses against
/// relations with numerals: `_ < 4 := h` with `h : a < 4`, where the step's relation is
/// `@LT.lt ?α ?inst ?x (OfNat.ofNat ?β 4 ?i)` until something fixes `?α` and `?β`.
const HYPOTHESES: &[&str] = &[
    "example (h : 3 < 4) (k : 4 < 5) : 3 < 5 :=\n  calc\n    _ < 4 := h\n    _ < _ := k\n",
    "example (h : 3 < 4) (k : 4 < 5) : 3 < 5 :=\n  calc\n    3 < 4 := h\n    _ < 5 := k\n",
    "example (a : Nat) (h : a < 4) (k : 4 < 5) : a < 5 :=\n  calc\n    _ < 4 := h\n    _ < _ := k\n",
    "example (h : (3:Nat) < 4) (k : (4:Nat) < 5) : (3:Nat) < 5 :=\n  calc\n    _ < 4 := h\n    _ < _ := k\n",
    "example (a : Nat) (h : a < 4) (k : 4 < 5) : a < 5 :=\n  calc\n    _ < 4 := h\n    (4 : Nat) < 5 := k\n",
    "example (a : Nat) (h : a < 4) (k : 4 < 5) : a < 5 :=\n  calc\n    _ < 4 := h\n    _ < (5 : Nat) := k\n",
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

fn workspace() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-calc-endpoints-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The pinned `lean`'s exit code and stdout on `entry`, when the binary is present.
fn pinned(lib: &Path, entry: &Path) -> Option<(i32, String)> {
    let lean = lib.parent()?.parent()?.join("bin/lean");
    if !lean.is_file() {
        return None;
    }
    let output = Command::new(lean)
        .arg(entry)
        .env("LEAN_PATH", lib)
        .output()
        .expect("run the pinned lean");
    Some((
        output.status.code().expect("normal pinned exit"),
        String::from_utf8(output.stdout).unwrap(),
    ))
}

/// The installed `lean` on `entry`: its exit code, stdout and stderr.
fn ours(lib: &Path, root: &Path, entry: &Path) -> (i32, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run lean");
    (
        output.status.code().expect("normal exit"),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

#[test]
fn calc_step_tactics_see_endpoints_the_expected_type_fixes() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    for (index, program) in ACCEPTED.iter().enumerate() {
        let entry = root.join(format!("Accepted{index}.lean"));
        std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
        if let Some((code, stdout)) = pinned(&lib, &entry) {
            assert_eq!((code, stdout.as_str()), (0, ""), "the pin moved: {program}");
        }
        let (code, stdout, stderr) = ours(&lib, &root, &entry);
        assert_eq!((code, stdout.as_str()), (0, ""), "{program}: {stderr}");
    }
    for (index, program) in REFUSED.iter().enumerate() {
        let entry = root.join(format!("Refused{index}.lean"));
        std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
        if let Some((code, _)) = pinned(&lib, &entry) {
            assert_eq!(code, 1, "the pin rejects {program}");
        }
        let (code, stdout, stderr) = ours(&lib, &root, &entry);
        assert_ne!(code, 0, "{program}: {stdout}");
        assert!(stderr.contains("refused"), "{program}: {stderr}");
    }
}

/// A hypothesis's type meets its step's relation argument by argument, as the pin's
/// `tryHeuristic` compares two applications of one definition before unfolding either
/// (vendored `Lean/Meta/ExprDefEq.lean`), so `h : a < 4` fixes `?α` and `?β` above. Each type was
/// reduced first, to `Nat.le (a + 1) 4` against the stuck `@LT.lt ?α ?inst ..`, which left both
/// open, and every later instance pass searched for `OfNat ?β 4` and `LT ?α` again. Five of
/// these programs were refused, three by the heartbeat limit; the sixth passed.
#[test]
fn calc_steps_proved_by_hypotheses_fix_their_numerals() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    for (index, program) in HYPOTHESES.iter().enumerate() {
        let entry = root.join(format!("Hypotheses{index}.lean"));
        std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
        if let Some((code, stdout)) = pinned(&lib, &entry) {
            assert_eq!((code, stdout.as_str()), (0, ""), "the pin moved: {program}");
        }
        let (code, stdout, stderr) = ours(&lib, &root, &entry);
        assert_eq!((code, stdout.as_str()), (0, ""), "{program}: {stderr}");
    }
}
