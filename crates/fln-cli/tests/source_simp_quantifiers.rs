//! Quantified goals and hypotheses use the same checked simplifier in the CLI.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

#[test]
fn quantified_simp_keeps_its_binders_and_never_publishes_unproved_prefixes() {
    let root = std::env::temp_dir().join(format!("fln-simp-quantified-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let file = root.join("Quantified.lean");
    for (source, accepted, safety) in [
        (
            // `simp only []` leaves `∀ a, True` at the pin; the closing needs `implies_true`'s
            // statement selected, which the seed has no declaration of.
            "theorem t (f g : Nat -> Nat) (P : Nat -> Prop) (h : (n : Nat) -> f n = g n) (ready : (n : Nat) -> P (g n)) : (n : Nat) -> P (f n) := by\n  simp only [h]\n  guard_target = (n : Nat) -> P (g n)\n  exact ready\nuniverse u\ntheorem implies_true_eq (α : Sort u) : (α -> True) = True :=\n  propext (Iff.intro (fun _ => True.intro) (fun _ _ => True.intro))\ntheorem reflexive (A : Type) : (a : A) -> a = a := by simp only [implies_true_eq]\n",
            true,
            false,
        ),
        (
            "def prefix : Nat := 7\ntheorem bad (f g : Nat -> Nat) (h : f 0 = g 0) : (n : Nat) -> f n = g n := by simp only [h]",
            false,
            false,
        ),
        (
            // The closing rule is selected so the goal closes and the kernel sees the unsafe
            // proof; without it the pin reports unsolved goals `∀ n, True` as well.
            "unsafe def forged (f g : Nat -> Nat) (n : Nat) : f n = g n := forged f g n\nuniverse u\ntheorem implies_true_eq (α : Sort u) : (α -> True) = True :=\n  propext (Iff.intro (fun _ => True.intro) (fun _ _ => True.intro))\ntheorem bad (f g : Nat -> Nat) : (n : Nat) -> f n = g n := by simp only [forged f g, implies_true_eq]",
            false,
            true,
        ),
        (
            "theorem t (f g : Nat -> Nat) (P : Nat -> Prop) (h : (n : Nat) -> f n = g n) (ready : (n : Nat) -> P (f n)) : (n : Nat) -> P (g n) := by simpa only [h] using ready",
            true,
            false,
        ),
    ] {
        std::fs::write(&file, source).unwrap();
        let result = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&file)
            .output()
            .unwrap();
        assert_eq!(
            result.status.code(),
            Some(if accepted { 0 } else { 1 }),
            "{source}\n{}",
            String::from_utf8_lossy(&result.stderr)
        );
        if accepted {
            assert!(result.stderr.is_empty());
            let text = String::from_utf8(result.stdout).unwrap();
            assert!(text.contains("\"authority\":true"), "{text}");
            assert!(text.contains("\"executed\":false"), "{text}");
        } else {
            assert!(result.stdout.is_empty());
            let text = String::from_utf8(result.stderr).unwrap();
            assert!(
                text.contains(if safety {
                    "SafetyViolation"
                } else {
                    "\"authority\":false"
                }),
                "{text}"
            );
        }
        assert_eq!(std::fs::read_to_string(&file).unwrap(), source);
    }
}

/// Programs over `prelude` + `Init.SimpLemmas`, where `implies_true` (`Init/SimpLemmas.lean:279`)
/// is in the default simp set. The pin's simp closes a goal only once its result is `True`
/// (`simpTargetCore`, `Lean/Meta/Tactic/Simp/Main.lean:784`): a quantified goal whose leaf
/// closes by `eq_self` becomes `∀ y, True`, and `True` only through `implies_true`. Every
/// program was run through the pinned `lean` v4.32.0 with this header first (2026-10-23), with
/// the verdict recorded below, and is compared with the pinned binary again when present.
const CLOSING_HEADER: &str = "prelude\nimport Init.SimpLemmas\n";

/// Accepted at the pin and here.
const CLOSING_ACCEPTED: &[(&str, &str)] = &[
    (
        "default_set_binder",
        "example : ∀ y : Nat, y + 0 = y := by simp\n",
    ),
    (
        "default_set_truth",
        "example : ∀ y : Nat, True := by simp\n",
    ),
    (
        "unquantified_only",
        "example (y : Nat) : y + 0 = y := by simp only [Nat.add_zero]\n",
    ),
    (
        "only_with_implies_true",
        "example : ∀ y : Nat, y + 0 = y := by simp only [Nat.add_zero, implies_true]\n",
    ),
    (
        "only_reflexive_with_implies_true",
        "example : ∀ y : Nat, y = y := by simp only [implies_true]\n",
    ),
    (
        "nested_with_implies_true",
        "example : ∀ x y : Nat, x + 0 = x := by simp only [Nat.add_zero, implies_true]\n",
    ),
    (
        "proposition_binder_with_implies_true",
        "example (P : Prop) : P → 0 + 0 = 0 + 0 := by simp only [implies_true]\n",
    ),
    // The pin selects a rule by its statement, not its name.
    (
        "same_statement_other_name",
        "theorem my_true (α : Sort u) : (α → True) = True := implies_true α\n\
         example : ∀ y : Nat, y + 0 = y := by simp only [Nat.add_zero, my_true]\n",
    ),
    (
        "simp_all_default_set",
        "example : ∀ y : Nat, y + 0 = y := by simp_all\n",
    ),
    (
        "simp_all_only_with_implies_true",
        "example : ∀ y : Nat, y + 0 = y := by simp_all only [Nat.add_zero, implies_true]\n",
    ),
    (
        "simpa_default_set",
        "example : ∀ y : Nat, y + 0 = y := by simpa\n",
    ),
    (
        "simpa_only_with_implies_true",
        "example : ∀ y : Nat, y + 0 = y := by simpa only [Nat.add_zero, implies_true]\n",
    ),
    (
        "simpa_using",
        "example (h : ∀ y : Nat, y + 0 = y) : ∀ y : Nat, y + 0 = y := by\n  \
         simpa only [Nat.add_zero] using h\n",
    ),
    (
        "hypothesis_location",
        "example (h : ∀ y : Nat, y + 0 = y) : True := by simp only [Nat.add_zero] at h; trivial\n",
    ),
    // The goal `simp only` leaves open is finished by later tactics.
    (
        "left_open_then_default_set",
        "example : ∀ y : Nat, y + 0 = y := by simp only [Nat.add_zero]; simp\n",
    ),
    (
        "left_open_then_intro",
        "example : ∀ y : Nat, y + 0 = y := by simp only [Nat.add_zero]; intro y; trivial\n",
    ),
];

/// Rejected at the pin and here, with this implementation's reason. The pin's reason is
/// "unsolved goals ⊢ ∀ (y : Nat), True" unless noted.
const CLOSING_REJECTED: &[(&str, &str, &str)] = &[
    (
        "only_binder",
        "example : ∀ y : Nat, y + 0 = y := by simp only [Nat.add_zero]\n",
        "unsolved goals",
    ),
    (
        "only_under_function",
        "example (f : Nat → Nat) : ∀ y : Nat, f (y + 0) = f y := by simp only [Nat.add_zero]\n",
        "unsolved goals",
    ),
    // The pin: "`simp` made no progress".
    (
        "only_empty_truth",
        "example : ∀ y : Nat, True := by simp only []\n",
        "made no progress",
    ),
    // The pin rewrites `y = y` to `True` by `eq_self`, leaving `∀ y, True` unsolved; this
    // implementation has no such rewrite and reports no progress.
    (
        "only_empty_reflexive",
        "example : ∀ y : Nat, y = y := by simp only []\n",
        "made no progress",
    ),
    // The pin: "unsolved goals ⊢ P → True".
    (
        "only_empty_proposition_binder",
        "example (P : Prop) : P → 0 + 0 = 0 + 0 := by simp only []\n",
        "made no progress",
    ),
    (
        "only_nested",
        "example : ∀ x y : Nat, x + 0 = x := by simp only [Nat.add_zero]\n",
        "unsolved goals",
    ),
    (
        "only_equivalence",
        "example (P : Nat → Prop) : ∀ y : Nat, (P (y + 0) ↔ P y) := by simp only [Nat.add_zero]\n",
        "unsolved goals",
    ),
    (
        "default_set_without_implies_true",
        "example : ∀ y : Nat, y + 0 = y := by simp [-implies_true]\n",
        "unsolved goals",
    ),
    // A reversed rule does not rewrite `α → True`.
    (
        "only_reversed_implies_true",
        "example : ∀ y : Nat, y + 0 = y := by simp only [Nat.add_zero, ← implies_true]\n",
        "unsolved goals",
    ),
    (
        "simp_all_only",
        "example : ∀ y : Nat, y + 0 = y := by simp_all only [Nat.add_zero]\n",
        "unsolved goals",
    ),
    // The pin: "unsolved goals h : ∀ (y : Nat), True ⊢ ∀ (y : Nat), True".
    (
        "simp_all_only_with_hypothesis",
        "example (h : ∀ y : Nat, y + 0 = y) : ∀ y : Nat, y + 0 = y := by\n  \
         simp_all only [Nat.add_zero]\n",
        "unsolved goals",
    ),
    // The pin: "Tactic `assumption` failed".
    (
        "simpa_only",
        "example : ∀ y : Nat, y + 0 = y := by simpa only [Nat.add_zero]\n",
        "no local assumption matches the goal",
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
        .filter(|lib| lib.join("Init/SimpLemmas.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference library is required"
    );
    if lib.is_none() {
        eprintln!("SKIP: pinned Reference lib/lean absent");
    }
    lib
}

/// `fln check-source` on `CLOSING_HEADER` + `program`, and the pinned binary's exit code when
/// present.
fn check_closing(lib: &Path, root: &Path, name: &str, program: &str) -> (i32, String, Option<i32>) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{CLOSING_HEADER}{program}")).unwrap();
    let ours = Command::new(env!("CARGO_BIN_EXE_fln"))
        .arg("check-source")
        .arg(&entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed CLI");
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
    (
        ours.status.code().expect("normal process exit"),
        String::from_utf8_lossy(&ours.stderr).into_owned(),
        theirs,
    )
}

#[test]
fn quantified_goals_close_only_when_the_rule_set_turns_the_result_into_true() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    // One workspace, so the import closure is admitted once for every program.
    let root = std::env::temp_dir().join(format!(
        "fln-simp-quantified-closing-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&root).unwrap();
    for (name, program) in CLOSING_ACCEPTED {
        let (code, stderr, pinned) = check_closing(&lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
        assert_eq!(pinned.unwrap_or(0), 0, "{name}: the pinned lean rejects it");
    }
    for (name, program, reason) in CLOSING_REJECTED {
        let (code, stderr, pinned) = check_closing(&lib, &root, name, program);
        assert_ne!(code, 0, "{name}: accepted {program}");
        assert!(
            stderr.contains(reason),
            "{name}: not rejected for `{reason}`\n{stderr}"
        );
        assert_ne!(pinned.unwrap_or(1), 0, "{name}: the pinned lean accepts it");
    }
}
