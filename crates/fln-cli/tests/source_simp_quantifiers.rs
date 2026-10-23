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
    // `eq_self` rewrites `y = y` to `True`, leaving `∀ y, True` unsolved.
    (
        "only_empty_reflexive",
        "example : ∀ y : Nat, y = y := by simp only []\n",
        "unsolved goals",
    ),
    // The pin: "unsolved goals ⊢ P → True".
    (
        "only_empty_proposition_binder",
        "example (P : Prop) : P → 0 + 0 = 0 + 0 := by simp only []\n",
        "unsolved goals",
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

/// `eq_self` and `iff_self` are rules of every simp set: `simp only` starts from them
/// (`simpOnlyBuiltins`, `Lean/Elab/Tactic/Simp.lean:512,565`) and the default set has them as
/// `@[simp]` lemmas (`Init/SimpLemmas.lean:36,272`). They rewrite each reflexive `=` and `↔` to
/// `True` wherever simp visits, binders and hypotheses included, matching at reducible
/// transparency with the pin's Nat offsets and literals; a goal closes only once it is `True`.
/// Accepted at the pin and here, over `CLOSING_HEADER`.
const BUILTINS_ACCEPTED: &[(&str, &str)] = &[
    (
        "reflexive",
        "example (n : Nat) : n = n := by simp only []\n",
    ),
    (
        "reflexive_application",
        "example (f : Nat → Nat) (n : Nat) : f n = f n := by simp only []\n",
    ),
    (
        "equivalence",
        "example (P : Prop) : P ↔ P := by simp only []\n",
    ),
    ("literal_sum", "example : 2 + 2 = 4 := by simp only []\n"),
    (
        "literal_difference",
        "example : 10 - 3 = 7 := by simp only []\n",
    ),
    (
        "literal_remainder",
        "example : 7 % 3 = 1 := by simp only []\n",
    ),
    (
        "offset_successor",
        "example (n : Nat) : n + 1 = Nat.succ n := by simp only []\n",
    ),
    (
        "offsets",
        "example (x : Nat) : x + 2 + 3 = x + 5 := by simp only []\n",
    ),
    (
        "abbreviation",
        "abbrev myid (x : Nat) : Nat := x\nexample (x : Nat) : myid x = x := by simp only []\n",
    ),
    (
        "zero_offset_by_rule",
        "example (n : Nat) : n + 0 = n := by simp\n",
    ),
    // The goal left open is the pin's: `exact` would not check against `∀ y, y = y`.
    (
        "residual_under_binder",
        "example : ∀ y : Nat, y + 0 = y := by simp only [Nat.add_zero]; exact fun _ => True.intro\n",
    ),
    (
        "residual_equivalence_under_binder",
        "example (P : Nat → Prop) : ∀ y : Nat, (P y ↔ P y) := by\n  \
         simp only []; exact fun _ => True.intro\n",
    ),
    (
        "residual_conjunct",
        "example (P : Prop) (h : P) (y : Nat) : P ∧ y = y := by simp only []; exact ⟨h, True.intro⟩\n",
    ),
    (
        "residual_proposition_binder",
        "example (P : Prop) : P → 0 + 0 = 0 + 0 := by simp only []; exact fun _ => True.intro\n",
    ),
    (
        "residual_offset_under_binder",
        "example : ∀ n : Nat, n + 1 = Nat.succ n := by simp only []; exact fun _ => True.intro\n",
    ),
    (
        "argument_then_root",
        "example (f : Prop → Nat) (y : Nat) : f (y = y) = f True := by simp only []\n",
    ),
    (
        "hypothesis",
        "example (n : Nat) (h : n = n) : True := by simp only [] at h; exact h\n",
    ),
    (
        "quantified_hypothesis",
        "example (h : ∀ y : Nat, y + 0 = y) : True := by simp only [Nat.add_zero] at h; exact h 0\n",
    ),
    (
        "simpa_against_rewritten_assumption",
        "example (h : ∀ y : Nat, True) : ∀ y : Nat, y + 0 = y := by simpa only [Nat.add_zero]\n",
    ),
    (
        "simpa_using_reflexive",
        "example (n : Nat) (h : n = n) : True := by simpa only [] using h\n",
    ),
    (
        "simp_all_rewritten_hypothesis",
        "example (h : ∀ y : Nat, y + 0 = y) : ∀ y : Nat, y + 0 = y := by\n  \
         simp_all only [Nat.add_zero]; exact h\n",
    ),
];

/// Rejected at the pin and here, both with "`simp` made no progress": no rule applies, and only
/// a `True` result closes a goal.
const BUILTINS_REJECTED: &[(&str, &str)] = &[
    // Reducible transparency does not unfold `Nat.add`, and the pin's offset test leaves
    // `n + 0` against `n` undecided.
    (
        "zero_offset",
        "example (n : Nat) : n + 0 = n := by simp only []\n",
    ),
    (
        "zero_offset_hypothesis",
        "example (n : Nat) (h : n + 0 = n) : True := by simp only [] at h; trivial\n",
    ),
    // `foo` cannot rewrite (its premise is never discharged); the goal is not `True`.
    (
        "zero_offset_unused_rule",
        "theorem foo (n : Nat) (h : ∀ y : Nat, y = y) : n + 0 = n := Nat.add_zero n\n\
         example (n : Nat) : n + 0 = n := by simp only [foo]\n",
    ),
    (
        "erased_eq_self",
        "example (n : Nat) : n = n := by simp only [-eq_self]\n",
    ),
    (
        "erased_iff_self",
        "example (P : Prop) : P ↔ P := by simp only [-iff_self]\n",
    ),
    (
        "default_set_without_eq_self",
        "example (n : Nat) : n = n := by simp [-eq_self]\n",
    ),
    (
        "erased_under_binder",
        "example : ∀ y : Nat, y = y := by simp only [-eq_self]\n",
    ),
    (
        "heterogeneous",
        "example (a : Nat) : HEq a a := by simp only []\n",
    ),
    (
        "literal_mismatch",
        "example : 2 + 2 = 5 := by simp only []\n",
    ),
    (
        "offset_mismatch",
        "example (x : Nat) : x + 2 + 3 = x + 6 := by simp only []\n",
    ),
    (
        "identity",
        "example (x : Nat) : id x = x := by simp only []\n",
    ),
    (
        "definition",
        "def mydef (x : Nat) : Nat := x\nexample (x : Nat) : mydef x = x := by simp only []\n",
    ),
    (
        "zero_left",
        "example (n : Nat) : 0 + n = n := by simp only []\n",
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
    for (name, program) in CLOSING_ACCEPTED.iter().chain(BUILTINS_ACCEPTED) {
        let (code, stderr, pinned) = check_closing(&lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
        assert_eq!(pinned.unwrap_or(0), 0, "{name}: the pinned lean rejects it");
    }
    let rejected = CLOSING_REJECTED.iter().copied().chain(
        BUILTINS_REJECTED
            .iter()
            .map(|&(name, program)| (name, program, "made no progress")),
    );
    for (name, program, reason) in rejected {
        let (code, stderr, pinned) = check_closing(&lib, &root, name, program);
        assert_ne!(code, 0, "{name}: accepted {program}");
        assert!(
            stderr.contains(reason),
            "{name}: not rejected for `{reason}`\n{stderr}"
        );
        assert_ne!(pinned.unwrap_or(1), 0, "{name}: the pinned lean accepts it");
    }
}
