//! `simp +arith` over `Nat` (vendored `Lean/Meta/Tactic/Simp/Arith/Nat/*.lean`, the `simpArith`
//! post step of `Lean/Meta/Tactic/Simp/Rewrite.lean:303`): linear constraints and terms are
//! normalized by reflection over `Init/Data/Nat/Linear.lean`, so every rewrite is a
//! `Nat.Linear.*` proof the kernel decides. Through `fln check-source` over `prelude` +
//! `Init.Data.Nat.Linear`. Every program here was run through the pinned `lean` v4.32.0 with
//! the same header first (2026-10-23), with the verdict recorded below, and is compared with
//! the pinned binary again when it is present. The normal forms are the pin's: each
//! `guard_target =ₛ` and `guard_hyp … :ₛ` below holds there.
#![forbid(unsafe_code)]
#[path = "source_simp_arith/int.rs"]
mod int;

use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Data.Nat.Linear\nimport Init.Guard\n";

/// Accepted at the pin and here.
const ACCEPTED: &[(&str, &str)] = &[
    // `tests/elab/1236.lean`.
    (
        "scaled_side",
        "example (x : Nat) : x ≤ x * 2 := by simp +arith\n",
    ),
    (
        "offsets",
        "example (x : Nat) : x + 1 ≤ x + 2 := by simp +arith\n",
    ),
    (
        "doubling",
        "example (x : Nat) : 2 * x = x + x := by simp +arith\n",
    ),
    // `tests/elab/simpArith1.lean`'s `ex1`, through the structure-instance configuration.
    (
        "configuration_structure",
        "example (a b c : Nat) : a + b < b + 1 + a + c := by\n  simp (config := { arith := true })\n",
    ),
    // `tests/elab/simpCnstr1.lean`: normalized, not closed, then finished by `exact`.
    (
        "normal_form_left_open",
        "example (a b : Nat) (h : a ≤ 2) : a + b + 1 + a < b + 4 + a := by\n  simp +arith\n  \
         guard_target =ₛ a ≤ 2\n  exact h\n",
    ),
    (
        "negated_constraint",
        "example (a b : Nat) (h : 3 ≤ a) : ¬ (a + b + 1 + a < b + 4 + a) := by\n  simp +arith\n  \
         guard_target =ₛ 3 ≤ a\n  exact h\n",
    ),
    (
        "unsatisfiable_goal",
        "example (a : Nat) (h : False) : 4 = 8 + a := by\n  simp +arith\n  guard_target =ₛ False\n  \
         exact h\n",
    ),
    // `tests/elab/simp_nat_arith.lean`.
    (
        "terms_under_a_function",
        "example (f : Nat → Nat) (x y : Nat) : f (2*x + y) = f (y + x + x) := by\n  simp +arith\n",
    ),
    (
        "both_sides_of_an_iff",
        "example (x y : Nat) : (2*x + y = 4) ↔ (y + x + x = 4) := by\n  simp +arith\n",
    ),
    // `tests/elab/simpArithCacheIssue.lean`: `simp +arith only` normalizes the maximal terms.
    (
        "only_maximal_terms",
        "example (x y : Nat) (h : y = 0) : id ((x + x) + y) = id (x + x) := by\n  simp +arith only\n  \
         guard_target =ₛ id (2 * x + y) = id (2 * x)\n  simp [h]\n",
    ),
    // `tests/elab/simpArith1.lean`'s `ex5` and `ex6`: a hypothesis normalized to `False`
    // closes the goal; one normalized otherwise is rewritten in place.
    (
        "hypothesis_to_false",
        "theorem ex5 (a b c d : Nat) (h : a + d + b > b + 1 + (a + (c + c) + d)) : False := by\n  \
         simp +arith at h\n",
    ),
    (
        "hypothesis_rewritten",
        "theorem ex6 (a b : Nat) (p : Nat → Prop) (h : p (a + 1 + a + 2 + b)) : p (2*a + b + 3) := by\n  \
         simp +arith at h\n  guard_hyp h :ₛ p (2 * a + b + 3)\n  assumption\n",
    ),
];

/// Rejected at the pin and here.
const REJECTED: &[(&str, &str)] = &[
    // Already normal: "`simp` made no progress".
    (
        "no_progress",
        "example (x : Nat) : x ≤ 3 := by simp +arith\n",
    ),
    // Not the pin's normal form.
    (
        "other_normal_form",
        "example (a b : Nat) (h : a ≤ 2) : a + b + 1 + a < b + 4 + a := by\n  simp +arith\n  \
         guard_target =ₛ a + 1 ≤ 3\n  exact h\n",
    ),
];

/// Refused here as unsupported: configuration other than `arith`.
const REFUSED: &[(&str, &str, &str)] = &[(
    "other_configuration",
    "example (x : Nat) : x + 0 = x := by simp (config := { decide := true })\n",
    "expected default simplification configuration",
)];

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
        .filter(|lib| lib.join("Init/Data/Nat/Linear.olean").is_file());
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
        "fln-simp-arith-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// `fln check-source` on `HEADER` + `program`, and the pinned binary's exit code when present.
fn check(lib: &Path, root: &Path, name: &str, program: &str) -> (i32, String, Option<i32>) {
    check_with_header(lib, root, name, HEADER, program)
}

fn check_with_header(
    lib: &Path,
    root: &Path,
    name: &str,
    header: &str,
    program: &str,
) -> (i32, String, Option<i32>) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{header}{program}")).unwrap();
    let theirs = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file())
        .map(|pinned| {
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
fn simp_arith_normalizes_nat_linear_arithmetic_as_the_pin_does() {
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
            !stderr.contains("unexpected syntax"),
            "{name}: refused as unsupported, not rejected\n{stderr}"
        );
        assert_ne!(pinned.unwrap_or(1), 0, "{name}: the pinned lean accepts it");
    }
    for (name, program, refusal) in REFUSED {
        let (code, stderr, _) = check(&lib, &root, name, program);
        assert_ne!(code, 0, "{name}: accepted {program}");
        assert!(
            stderr.contains(refusal),
            "{name}: not the typed refusal\n{stderr}"
        );
    }
}
