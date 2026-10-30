//! Tactic `match` over `Nat` numerals, through the installed drop-in `lean` over `prelude` with
//! `Init.Tactics`. The tactic is `refine no_implicit_lambda% (match … with | p => ?rhs …)` followed
//! by each alternative's block (vendored `Lean/Elab/Tactic/Match.lean`).
//!
//! Patterns such as `0` and `k + 1` are elaborated through the eliminator, whose alternatives were
//! finished as `exact` finishes its term, refusing every hole they opened, so each alternative's
//! `?rhs` was refused: "proof script left 1 unsolved goals". At the pin a match alternative is a
//! term, and the enclosing `refine` collects its holes as goals. An untyped numeral discriminant
//! (`match 0 with`) was refused too, because `refine` and `exact` applied no default instance; the
//! pin's tactic `elabTerm` ends with `synthesizeSyntheticMVars (postpone := .no)`
//! (`Lean/Elab/Tactic/ElabTerm.lean:29-60`).
//!
//! Every program was run through the pinned `lean` v4.32.0 with the same header first (2026-10-29),
//! and the pin is consulted again when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Tactics\n";

/// Programs the pin accepts, printing nothing, whose alternatives are elaborated through the
/// eliminator: each was refused with an unsolved goal.
const ALTERNATIVES: &[&str] = &[
    "example (n : Nat) : 1 = 1 := by\n  match n with\n  | 0 => rfl\n  | _ + 1 => rfl\n",
    "example (n : Nat) : n + 0 = n := by\n  match n with\n  | 0 => rfl\n  | k + 1 => rfl\n",
    "example (n : Nat) : 1 = 1 := by\n  match n with\n  | 0 => rfl\n  | Nat.succ _ => rfl\n",
    "example (n : Nat) : 1 = 1 := by\n  match n with\n  | 0 => ?a\n  | _ + 1 => ?b\n  case a => rfl\n  case b => rfl\n",
    "example (n : Nat) : 1 = 1 := by\n  refine (match n with | 0 => ?a | _ + 1 => ?b)\n  case a => rfl\n  case b => rfl\n",
];

/// Programs the pin accepts, printing nothing, whose numeral discriminant has no type until a
/// default instance makes it `Nat`.
const DEFAULTS: &[&str] = &[
    "example : 1 = 1 := by\n  match 0 with\n  | _ => rfl\n",
    "example : True := by\n  match 0 with\n  | _ => exact True.intro\n",
    "example : True := by exact match 0 with | _ => True.intro\n",
];

/// Programs the pin rejects: a goal left without its `case`, holes `exact` may not leave, a wrong
/// alternative, and a numeral goal that is false.
const REFUSED: &[&str] = &[
    "example (n : Nat) : 1 = 1 := by\n  refine (match n with | 0 => ?a | _ + 1 => ?b)\n  case a => rfl\n",
    "example (n : Nat) : 1 = 1 := by\n  exact (match n with | 0 => ?a | _ + 1 => ?b)\n",
    "example (n : Nat) : n = 0 := by\n  match n with\n  | 0 => rfl\n  | _ + 1 => rfl\n",
    "example : 1 = 2 := by\n  match 0 with\n  | _ => rfl\n",
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
        "fln-tactic-match-numerals-{}-{}",
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

/// Each program must be accepted silently by the pin and here.
fn accepted(lib: &Path, root: &Path, tag: &str, programs: &[&str]) {
    for (index, program) in programs.iter().enumerate() {
        let entry = root.join(format!("{tag}{index}.lean"));
        std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
        if let Some((code, stdout)) = pinned(lib, &entry) {
            assert_eq!((code, stdout.as_str()), (0, ""), "the pin moved: {program}");
        }
        let (code, stdout, stderr) = ours(lib, root, &entry);
        assert_eq!((code, stdout.as_str()), (0, ""), "{program}: {stderr}");
    }
}

#[test]
fn numeral_pattern_alternatives_leave_their_holes_to_the_refinement() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    accepted(&lib, &root, "Alternatives", ALTERNATIVES);
}

#[test]
fn an_untyped_numeral_discriminant_takes_its_default_instance() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    accepted(&lib, &root, "Defaults", DEFAULTS);
}

/// A written `exact` still elaborates in its own refinement, whose final unification assigns the
/// holes it opened (bead fln-refine-final-unification-synthetic-holes-n15v); only alternatives
/// leave theirs to the enclosing elaboration.
#[test]
fn exact_still_assigns_its_own_holes() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    accepted(
        &lib,
        &root,
        "Exact",
        &["example (n : Nat) : n = n := by exact Eq.refl ?_\n"],
    );
}

#[test]
fn holes_and_wrong_alternatives_are_still_refused() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
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
