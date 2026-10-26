//! `simp?` and `simp_all?` (vendored `src/Lean/Elab/Tactic/SimpTrace.lean`) through the drop-in
//! `lean` over `prelude` with `Init`'s simp lemmas: the tactic is this engine's `simp`, and its
//! information message is the `simp only` call the pin's simplifier prints (`mkSimpOnly`,
//! `src/Lean/Elab/Tactic/Simp.lean:618-669`; `addSuggestion`,
//! `src/Lean/Meta/Tactic/TryThis.lean:92-103`). Every program here was run through the pinned
//! `lean` v4.32.0 with the same header first (2026-10-23), runs through it again in this test,
//! and must print exactly what the pin prints. A call outside the reproduced fragment is a typed
//! refusal, never a different suggestion.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const HEADER: &str = "prelude\nimport Init.Tactics\nimport Init.SimpLemmas\nimport Init.Data.Nat.Basic\nimport Init.Classical\nimport Init.PropLemmas\nimport Init.Data.List.Basic\n";

/// Each program, the `Try this:` messages it prints, and what it shows.
const PROGRAMS: &[(&str, usize, &str)] = &[
    // The default set: `Nat.add_sub_cancel` rewrites, and `eq_self`, which closes the goal, is not
    // printed (`simpOnlyBuiltins`).
    (
        "default_set",
        1,
        "example (a b : Nat) : a + b - b = a := by simp?\n",
    ),
    // A hypothesis argument is printed as written (`.stx`), when its rewrite happens: before
    // `Nat.add_zero`, which rewrites the term it produced.
    (
        "hypothesis_argument",
        1,
        "example (a : Nat) (h : a = 1) : a + 0 = 1 := by simp? [h]\n",
    ),
    // `at h`: the location follows the rule list.
    (
        "at_hypothesis",
        1,
        "example (a b : Nat) (h : a + 0 = b) : a = b := by\n  simp? at h\n  exact h\n",
    ),
    // `at *`: every non-dependent propositional hypothesis, then the goal (`getNondepPropHyps`).
    (
        "at_wildcard",
        1,
        "example (a b : Nat) (h : a + 0 = b) (h2 : b * 1 = 3) : a = 3 := by\n  simp? at *\n  rw [h, h2]\n",
    ),
    // `at h k ⊢`.
    (
        "at_hypotheses_and_goal",
        1,
        "example (a b : Nat) (h : a + 0 = b) (k : b * 1 = 2) : a = 2 := by\n  simp? at h k ⊢\n  rw [h, k]\n",
    ),
    // `simp_all?` naming a let variable, which `mkSimpOnly` keeps (`tests/elab/3519.lean`).
    (
        "simp_all_let",
        1,
        "example {P : Nat → Prop} : let x := 0; P x := by\n  intro x\n  simp_all? [x]\n  sorry\n",
    ),
    // `← h` is printed as written.
    (
        "reversed_hypothesis",
        1,
        "example (a b : Nat) (h : a = b) : b + 0 = a := by simp? [← h]\n",
    ),
    // `[*]`: the hypotheses are `.fvar` theorems, printed after the rest (`mkSimpOnly`'s
    // `localsOrStar`).
    (
        "star",
        1,
        "example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by simp? [*]\n",
    ),
    // An erased default theorem leaves another to rewrite.
    (
        "erased_default",
        1,
        "example (a : Nat) : 0 + a = a := by simp? [-Nat.add_zero]\n",
    ),
    // A theorem is printed by its shortest name that resolves to it here
    // (`unresolveNameGlobalAvoidingLocals`): `bar` in `namespace Foo` and under `open Foo`,
    // `Foo.bar` outside.
    (
        "namespaces",
        3,
        "namespace Foo\ntheorem bar (n : Nat) : n + 0 = n := Nat.add_zero n\nexample (a : Nat) : a + 0 = a := by simp? only [bar]\nend Foo\nexample (a : Nat) : a + 0 = a := by simp? only [Foo.bar]\nopen Foo in\nexample (a : Nat) : a + 0 = a := by simp? only [bar]\n",
    ),
    // A rule list wider than the pin's 120 columns fills its lines, continued at four spaces.
    (
        "wrapped_list",
        1,
        "example (x00 x01 x02 x03 x04 x05 x06 x07 x08 x09 : Nat) (hypothesis_number_01 : x00 = x01) (hypothesis_number_02 : x01 = x02) (hypothesis_number_03 : x02 = x03) (hypothesis_number_04 : x03 = x04) (hypothesis_number_05 : x04 = x05) (hypothesis_number_06 : x05 = x06) (hypothesis_number_07 : x06 = x07) (hypothesis_number_08 : x07 = x08) (hypothesis_number_09 : x08 = x09) : x00 = x09 := by\n  simp? only [hypothesis_number_01, hypothesis_number_02, hypothesis_number_03, hypothesis_number_04, hypothesis_number_05, hypothesis_number_06, hypothesis_number_07, hypothesis_number_08, hypothesis_number_09]\n",
    ),
    // The location stays on the rule list's last line and counts toward its width.
    (
        "wrapped_list_at_hypothesis",
        1,
        "example (x00 x01 x02 x03 x04 y : Nat) (hypothesis_number_01 : x00 = x01) (hypothesis_number_02 : x01 = x02) (hypothesis_number_03 : x02 = x03) (hypothesis_number_04 : x03 = x04) (hh : x00 + 0 = y) : x04 = y := by\n  simp? only [hypothesis_number_01, hypothesis_number_02, hypothesis_number_03, hypothesis_number_04, Nat.add_zero] at hh\n  exact hh\n",
    ),
    // `#guard_msgs` reads the suggestion as an `info:` message.
    (
        "guarded",
        0,
        "/--\ninfo: Try this:\n  [apply] simp only [h, Nat.add_zero]\n-/\n#guard_msgs in\nexample (a : Nat) (h : a = 1) : a + 0 = 1 := by simp? [h]\n",
    ),
    // Nothing printed was used: `simp only`, without brackets (`setSimpParams`).
    (
        "empty_simp_only",
        1,
        "example (x : Nat) : x = x := by simp? only\n",
    ),
    // A named let variable is printed after the theorems, and `Nat.reduceMul` evaluates a literal
    // product (`tests/elab/3501.lean`, `6655.lean`).
    (
        "let_variables",
        3,
        "example : True := by\n  let a := 10\n  have : a * 2 = 10 * 2 := by\n    simp? [a]\n  have : a + 0 = 10 := by\n    simp? [a]\n  have : 1 = 1 := by simp?\n  trivial\n",
    ),
    // A non-recursive definition named in the list unfolds before its arguments are simplified, so
    // it is printed first.
    (
        "unfold_by_name",
        1,
        "def g (n : Nat) := n + 1\nexample (a : Nat) : g (a + 0) = a + 1 := by simp? [g]\n",
    ),
    // A conditional theorem's premise simplifies to `True` first: the rule that did it precedes the
    // theorem.
    (
        "discharged_premise",
        1,
        "example (a : Nat) (h : 3 ≤ a) : a - 3 + 3 = a := by simp? [h]\n",
    ),
    // Literal arithmetic is the builtin procedures `Nat.reduceMul` and `Nat.reduceAdd`, innermost
    // first.
    (
        "nat_literal_procedures",
        1,
        "example : 2 * 3 + 1 = 7 := by simp?\n",
    ),
    // A non-dependent arrow simplifies both sides, then `imp_self` rewrites it.
    (
        "implication",
        1,
        "example (a b : Nat) : a + 0 = b + 0 → a = b := by simp?\n",
    ),
    // The information message precedes the command's raw traces, which `addTraceAsMessages` adds
    // last.
    (
        "before_raw_trace",
        1,
        "example (a : Nat) (h : a = 1) : a + 0 = 1 := by\n  trace_state\n  simp? [h]\n",
    ),
    // A named let variable the rule mentions and the goal does not is unfolded by unification and
    // printed after the rest (`tests/elab/zetaDeltaTryThisIssue.lean`).
    (
        "let_variable_through_a_rule",
        1,
        "opaque f : Nat → Nat\nexample (a : Nat) : True := by\n  let x := a\n  have h1 : f x = 2 := sorry\n  suffices f a = 2 by sorry\n  simp? only [h1, x]\n",
    ),
    // The theorem being declared is a local of its own body, so `A.B` cannot name `N.A.B` there
    // (`tests/elab/6706.lean`).
    (
        "auxiliary_declaration_names",
        1,
        "def P := True\ntheorem N.A.B : P := trivial\ntheorem N.X.A.B : P := by\n  simp? [N.A.B]\n",
    ),
    // Discharged premises record their rules first, a failed attempt's (`indicator_of`) none
    // (`tests/elab/3710.lean`, its definitions `noncomputable`).
    (
        "discharge_chain",
        1,
        "def Set' := Nat → Prop\nnamespace Set'\nnoncomputable def singleton (a : Nat) : Set' := fun b ↦ b = a\nnoncomputable def compl (s : Set') : Set' := fun x ↦ ¬ s x\n@[simp]\ntheorem compl_iff (s : Set') (x : Nat) : s.compl x ↔ ¬ s x := Iff.rfl\n@[simp]\ntheorem singleton_iff {a b : Nat} : singleton b a ↔ a = b := Iff.rfl\nopen Classical\nnoncomputable def indicator (s : Set') (x : Nat) : Nat := if s x then 1 else 0\n@[simp]\ntheorem indicator_of {s : Set'} {a : Nat} (h : s a) : indicator s a = 1 := if_pos h\n@[simp]\ntheorem indicator_of_not {s : Set'} {a : Nat} (h : ¬ s a) : indicator s a = 0 := if_neg h\ntheorem test : indicator (compl <| singleton 0) 0 = 0 := by\n  simp?\nend Set'\n",
    ),
    // A failed alternative discards its suggestion with its state (`Core.SavedState.restore`).
    (
        "backtracked_attempt",
        0,
        "example (a b : Nat) (h : b = a) : a + 0 = b := by\n  first\n  | (simp?; done)\n  | (simp; exact h.symm)\n",
    ),
    // So does a failed `try`.
    (
        "tried_attempt",
        0,
        "example (a b : Nat) (h : b = a) : a + 0 = b := by\n  try (simp?; done)\n  simp\n  exact h.symm\n",
    ),
    // Two default theorems rewrite `0 * 0`: the one whose key has `*` where the other has `0`,
    // `Nat.mul_zero`, comes first in the discrimination tree.
    (
        "discrimination_tree_order",
        1,
        "example (b : Nat) : 0 * 0 = b * 0 := by simp?\n",
    ),
    // A hypothesis `p` rewrites `p` to `True` and `¬ q` rewrites `q` to `False`.
    (
        "proposition_hypotheses",
        1,
        "example (p q : Prop) (hp : p) (hq : ¬q) : p ∧ ¬q := by simp? [hp, hq]\n",
    ),
    // A quantified hypothesis is a theorem with pattern variables, recorded once.
    (
        "quantified_hypothesis",
        1,
        "example (f : Nat → Nat) (h : ∀ x, f x = x) (a : Nat) : f (f a) = a := by simp? [h]\n",
    ),
    // `a ≠ b` rewrites `a = b` to `False`.
    (
        "disequation_hypothesis",
        1,
        "example (a b : Nat) (h : a ≠ b) : ¬ (a = b) := by simp? [h]\n",
    ),
    // Default `List` and `Nat` theorems, innermost first.
    (
        "list_lemmas",
        1,
        "example (xs : List Nat) : (xs ++ []).length + 0 = xs.length := by simp?\n",
    ),
    // A hypothesis inside implications, then `implies_true` and `and_self`.
    (
        "implications_under_and",
        1,
        "example (p q r : Prop) (hq : q) : (p → q) ∧ (r → q) := by simp? [hq]\n",
    ),
    // `Nat.reduceSub`, then `Nat.reduceMod` on its result.
    (
        "nat_literal_subtraction_and_remainder",
        1,
        "example : (10 - 3) % 4 = 3 := by simp?\n",
    ),
];

/// Accepted at the pin, refused here: a configuration is outside the reproduced fragment.
const REFUSED: &str = "example (a : Nat) : a + 1 ≤ a + 2 := by simp? +arith\n";

fn pinned_toolchain() -> Option<PathBuf> {
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
        "fln-simp-suggestions-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// This crate's `lean` and the pinned `lean` on `HEADER` + `program`.
fn outputs(lib: &Path, root: &Path, name: &str, program: &str) -> (Output, Output) {
    let entry = format!("{name}.lean");
    std::fs::write(root.join(&entry), format!("{HEADER}{program}")).unwrap();
    let run = |binary: &Path| {
        Command::new(binary)
            .arg(&entry)
            .current_dir(root)
            .env("LEAN_PATH", lib)
            .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
            .output()
            .expect("run lean")
    };
    let pinned = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .expect("the pinned toolchain's lean");
    (run(Path::new(env!("CARGO_BIN_EXE_lean"))), run(&pinned))
}

#[test]
fn suggestions_match_the_pin() {
    let Some(lib) = pinned_toolchain() else {
        return;
    };
    let root = workspace();
    for &(name, suggestions, program) in PROGRAMS {
        let (ours, pinned) = outputs(&lib, &root, name, program);
        for (output, binary) in [(&ours, "this crate's lean"), (&pinned, "the pinned lean")] {
            assert_eq!(
                output.status.code(),
                Some(0),
                "{name}: {binary}\n{}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        let ours = String::from_utf8(ours.stdout).expect("UTF-8 output");
        let pinned = String::from_utf8(pinned.stdout).expect("UTF-8 output");
        assert_eq!(ours, pinned, "{name}: {program}");
        // The programs must actually print, or drop, the suggestions they are about.
        assert_eq!(
            ours.matches("Try this:").count(),
            suggestions,
            "{name}: {ours}"
        );
    }
}

#[test]
fn a_call_outside_the_fragment_is_a_typed_refusal() {
    let Some(lib) = pinned_toolchain() else {
        return;
    };
    let root = workspace();
    let (ours, pinned) = outputs(&lib, &root, "refused", REFUSED);
    assert_eq!(pinned.status.code(), Some(0));
    assert!(String::from_utf8_lossy(&pinned.stdout).contains("Try this:"));
    assert_ne!(ours.status.code(), Some(0));
    assert!(ours.stdout.is_empty());
    let stderr = String::from_utf8_lossy(&ours.stderr);
    assert!(
        stderr.contains("simp suggestion outside the fragment this engine reproduces"),
        "{stderr}"
    );
}
