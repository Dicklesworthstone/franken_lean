//! The configuration slot of `simp`, `simp_all` and `dsimp` (`Lean.Meta.Simp.Config`,
//! `Lean.Meta.DSimp.Config`, vendored `src/Init/MetaTypes.lean`): a field set to its declared
//! default is accepted and changes nothing; `decide` (the pin's `simpUsingDecide`,
//! `Lean/Meta/Tactic/Simp/Rewrite.lean:286`) and `failIfUnchanged` are honoured; any other field
//! set away from its default is refused as unsupported. Through `fln check-source` over
//! `prelude`, `Init.SimpLemmas` and `Init.Guard`. Every accepted and rejected program is compared
//! with the pinned `lean` v4.32.0 whenever it is present.
#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.SimpLemmas\nimport Init.Guard\n";

/// Accepted at the pin and here.
const ACCEPTED: &[(&str, &str)] = &[
    // `tests/elab/simpDecide.lean`.
    (
        "decide_closes_the_goal",
        "example : 0 < 4 := by\n  simp (config := { decide := true }) only\n",
    ),
    (
        "decide_as_a_positive_item",
        "example : 2 + 2 = 4 ∧ 3 < 5 := by simp +decide only\n",
    ),
    (
        "decide_as_a_value_item",
        "example : 2 + 2 = 4 := by simp (decide := true) only\n",
    ),
    // A closed hypothesis decided `False` closes the goal (`eq_false_of_decide`).
    (
        "decide_a_hypothesis_false",
        "example (h : 5 < 3) : 7 = 8 := by simp +decide only at h\n",
    ),
    // `tests/elab/2182.lean`: `decide := false` is the default.
    (
        "default_decide",
        "example : (¬ False) = True := by simp (config := { decide := false })\n",
    ),
    (
        "defaults_change_nothing",
        "example (x : Nat) : x = x := by\n  \
         simp (config := { zeta := true, beta := true }) +implicitDefEqProofs -contextual\n",
    ),
    // `tests/elab/simp_failIfUnchanged.lean`: unchanged, the goal stays.
    (
        "unchanged_goal_left_open",
        "example (h : False) : False := by\n  simp (config := { failIfUnchanged := false }) only\n  \
         exact h\n",
    ),
    (
        "unchanged_hypothesis_left_open",
        "example (n : Nat) (h : n = 3) : n = 3 := by\n  \
         simp (config := { failIfUnchanged := false }) only at h\n  exact h\n",
    ),
    (
        "unchanged_dsimp_left_open",
        "example (h : False) : False := by\n  dsimp (config := { failIfUnchanged := false }) only\n  \
         exact h\n",
    ),
    // A later `(config := …)` resets the items before it.
    (
        "configuration_resets_earlier_items",
        "example : 0 < 4 := by\n  \
         fail_if_success simp -failIfUnchanged (config := { decide := false }) only\n  \
         simp +decide only\n",
    ),
];

/// Rejected at the pin and here.
const REJECTED: &[(&str, &str)] = &[
    // `failIfUnchanged := true` is the default: "`simp` made no progress".
    (
        "unchanged_fails",
        "example (h : False) : False := by\n  simp (config := { failIfUnchanged := true }) only\n  \
         exact h\n",
    ),
    // Decided `False`, the goal is left `False`.
    (
        "decided_false_goal",
        "example : 5 < 3 := by simp +decide only\n",
    ),
    // Without `decide`, `simp only` cannot close it.
    ("undecided", "example : 0 < 4 := by simp only\n"),
];

/// Refused here as unsupported: a field this engine does not honour set away from its default,
/// or a configuration term other than a structure instance of Boolean literals.
const REFUSED: &[(&str, &str)] = &[
    (
        "unhonoured_field",
        "example (x : Nat) : x = x := by simp (config := { zeta := false })\n",
    ),
    (
        "unhonoured_negative_item",
        "example (x : Nat) : x = x := by simp -zeta\n",
    ),
    (
        "configuration_term",
        "example (x : Nat) : x = x := by simp (config := Lean.Meta.Simp.neutralConfig)\n",
    ),
    ("dsimp_decide", "example : 0 < 4 := by dsimp +decide only\n"),
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

fn workspace() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-simp-config-{}-{}",
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
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
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
fn simp_configuration_is_read_as_the_pin_reads_it() {
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
    for (name, program) in REFUSED {
        let (code, stderr, _) = check(&lib, &root, name, program);
        assert_ne!(code, 0, "{name}: accepted {program}");
        assert!(
            stderr.contains("expected default simplification configuration"),
            "{name}: not the typed refusal\n{stderr}"
        );
    }
}

#[test]
fn default_conditional_presteps_preserve_the_selected_branch_and_scope() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let program = r#"
set_option simprocs true in
example (p : Prop) [Decidable p] (h : p) (a b : Nat) :
    (if p then a else b) = a := by simp [h, -ite_true]
example (p : Prop) [Decidable p] (h : p) (a b : Nat) :
    (if p then a else b) = a := by simp [h]
example (p : Prop) [Decidable p] (h : ¬ p) (a b : Nat) :
    (if p then a else b) = b := by simp [h]
example (p : Prop) [Decidable p] (h : p) (f : p → Nat) (g : ¬ p → Nat) :
    dite p f g = f h := by simp [h]
example (p : Prop) [Decidable p] (h : ¬ p) (f : p → Nat) (g : ¬ p → Nat) :
    dite p f g = g h := by simp [h]
example (p : Prop) [Decidable p] (h : p) (b : Nat) :
    (fun n : Nat => if p then n else b) = (fun n : Nat => n) := by simp [h]
example (p : Prop) [Decidable p] (h : p) (a b c : Nat)
    (hx : (if p then a else b) = c) : a = c := by
  simp [h] at hx
  exact hx
example (p : Prop) [Decidable p] (h : p) (a b : Nat) :
    (if p then a else b) = a := by
  conv => lhs; simp [h]
example (p : Prop) [Decidable p] (h : p) (a b c : Nat) (ha : a = c) :
    (if p then a else b) = c := by simpa [h] using ha
example (p : Prop) [Decidable p] (h : p) (f g : Nat → Nat) (n : Nat) :
    (if p then f else g) n = f n := by simp [h]
example (p : Prop) [Decidable p] (h : p) (f g : Nat → Nat) :
    (fun n => (if p then f else g) n) = f := by simp [h]
-- A selected fact must not rewrite the proposition inside proof arguments.
example (p : Prop) (h1 h2 : p) (f : p → Nat) :
    f (of_eq_true (propext (iff_true_intro h1))) = f h2 := by simp [h1]
example (p : Prop) (h : ¬ p) (g : ¬ p → Nat) :
    g (of_eq_false (propext (Iff.intro h
      (fun hf : False => False.rec (motive := fun _ => p) hf)))) = g h := by simp [h]
-- Skipping proof arguments must retain function and partial-application rules.
example (f g : Nat → Nat) (h : f = g) (x : Nat) :
    f x = g x := by simp only [h]
example (f : Nat → Nat → Nat) (g : Nat → Nat) (a b : Nat)
    (h : f a = g) : f a b = g b := by simp only [h]
example (f : Nat → Nat → Nat) (g : Nat → Nat) (a b : Nat)
    (k : Nat → (Nat → Nat) → Nat) (h : f a = g) :
    k (f a b) (f a) = k (g b) g := by simp only [h]
-- A later proof dependency does not freeze the earlier data argument.
example (f : (n : Nat) → n = n → Nat) (a b : Nat) (h : a = b) :
    f a rfl = f b rfl := by simp only [h]
"#;
    let (code, stderr, pinned) = check(&lib, &root, "conditional_scopes", program);
    assert_eq!(code, 0, "{stderr}");
    assert_eq!(
        pinned.unwrap_or(0),
        0,
        "the pinned lean rejects the controls"
    );
    for (name, program) in [
        (
            "simprocs_option_disables_conditional_presteps",
            "set_option simprocs false in\nexample (p : Prop) [Decidable p] (h : p) (a b : Nat) :\n    (if p then a else b) = a := by simp [h, -ite_true]\n",
        ),
        (
            "only_has_no_default_conditional_presteps",
            "example (p : Prop) [Decidable p] (h : p) (a b : Nat) :\n    (if p then a else b) = a := by simp only [h]\n",
        ),
        (
            "a_symbolic_condition_does_not_choose_a_branch",
            "example (p : Prop) [Decidable p] (a b : Nat) :\n    (if p then a else b) = a := by simp\n",
        ),
        (
            "a_proven_condition_does_not_choose_the_wrong_branch",
            "example (p : Prop) [Decidable p] (h : p) (a b : Nat) :\n    (if p then a else b) = b := by simp [h]\n",
        ),
        (
            "proof_irrelevance_does_not_bypass_erased_eq_self",
            "example (p : Prop) (h1 h2 : p) (f : p → Nat) :\n    f h1 = f h2 := by simp [-eq_self]\n",
        ),
    ] {
        let (code, stderr, pinned) = check(&lib, &root, name, program);
        assert_ne!(code, 0, "{name}: accepted {program}");
        assert!(
            stderr.contains("made no progress") || stderr.contains("unsolved goals"),
            "{name}: not the tactic's own refusal\n{stderr}"
        );
        assert_ne!(pinned.unwrap_or(1), 0, "{name}: the pinned lean accepts it");
    }
}

#[test]
fn conditional_simp_does_not_expand_both_recursive_branches() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    // All four unchanged pin probes: ite/dite, true/false. At depth 32,
    // rewriting both branches before the condition exceeds the work limit.
    let program = format!(
        "import Init.Data.Nat.Basic\n{}",
        include_str!("../../../vendor/lean4-src/tests/elab/simpIfPre.lean")
    );
    let (code, stderr, pinned) = check(&lib, &root, "conditional_recursion", &program);
    assert_eq!(code, 0, "{stderr}");
    assert_eq!(pinned.unwrap_or(0), 0, "the pinned lean rejects simpIfPre");
}
