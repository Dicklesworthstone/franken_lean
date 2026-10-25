//! Permutation rules in `simp` (ordered rewriting): a rule whose sides are equal up to its pattern
//! variables (`Nat.add_comm`, `and_left_comm`, a hypothesis `∀ x y, f x y = f y x`) rewrites a
//! term only to one the pin's `acLt` orders below it (vendored
//! `src/Lean/Meta/Tactic/Simp/Rewrite.lean:143-150`, `src/Lean/Meta/ACLt.lean`), and the rules of
//! a call holding one are taken in the pin's order: the node its post-order traversal reaches
//! first, there the candidate its discrimination tree returns first. The normal form simp reaches
//! is the pin's, so each accepted program closes its goal with an `exact h` whose `h` states only
//! that form, or closes it by `eq_self`; `simp?` prints the pin's suggestion.
//!
//! Through the drop-in `lean` over `prelude` with `Init.Data.Nat.Basic` and `Init.PropLemmas`.
//! Every program here was run through the pinned `lean` v4.32.0 with the same header first
//! (2026-10-24), with the same verdict; an accepted program's output is the pin's byte for byte,
//! and both are compared again when the pinned binary is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const HEADER: &str = "prelude\nimport Init.Data.Nat.Basic\nimport Init.PropLemmas\n";

const ACCEPTED: &[(&str, &str)] = &[
    // The three measured refusals that opened this work.
    (
        "comm_closes",
        "example (a b : Nat) : a + b = b + a := by simp [Nat.add_comm]\n",
    ),
    (
        "comm_left_comm_closes",
        "example (a b c : Nat) : a + b + c = c + b + a := by simp [Nat.add_comm, Nat.add_left_comm]\n",
    ),
    (
        "comm_at_wildcard",
        "example (a b : Nat) (h : b + a = 3) : a + b = 3 := by simp [Nat.add_comm] at *; exact h\n",
    ),
    // Locals are ordered by declaration, so `a + b` is the normal form, in the goal and in `h`.
    (
        "goal_reordered",
        "example (a b : Nat) (p : Nat → Prop) (h : p (a + b)) : p (b + a) := by simp only [Nat.add_comm]; exact h\n",
    ),
    (
        "hypothesis_reordered",
        "example (a b : Nat) (p : Nat → Prop) (h : p (b + a)) : p (a + b) := by simp only [Nat.add_comm] at h; exact h\n",
    ),
    // `upstream tests/elab/12136.lean`: a section variable is declared before the binders.
    (
        "section_variable_order",
        "variable {a : Nat}\ntheorem t (b : Nat) (p : Nat → Prop) (h : p (a + b)) : p (b + a) := by\n  simp only [Nat.add_comm]; exact h\n",
    ),
    // A sum before a numeral (`HAdd.hAdd` precedes `OfNat.ofNat` by name), a variable before an
    // application, an application before a numeral's literal argument.
    (
        "numerals_after_sums",
        "example (a b : Nat) (p : Nat → Prop) (h : p (a + (1 + (b + a * 2)))) : p (b + a * 2 + 1 + a) := by simp only [Nat.add_comm]; exact h\n",
    ),
    (
        "numeral_factor_last",
        "example (a : Nat) (p : Nat → Prop) (h : p (a * 2)) : p (2 * a) := by simp only [Nat.mul_comm]; exact h\n",
    ),
    (
        "applications_after_variables",
        "example (x y : Nat) (f : Nat → Nat) (p : Nat → Prop) (h : p (x + (f x + f y) + 1)) : p (f y + f x + x + 1) := by simp only [Nat.add_comm]; exact h\n",
    ),
    // Literal values, not their spelling: `2 * a` before `10 * a`.
    (
        "literal_values",
        "example (a : Nat) (p : Nat → Prop) (h : p (2 * a + 10 * a)) : p (10 * a + 2 * a) := by simp only [Nat.add_comm]; exact h\n",
    ),
    (
        "string_literals",
        "opaque f : String → Nat\nexample (p : Nat → Prop) (h : p (f \"a\" + f \"b\")) : p (f \"b\" + f \"a\") := by simp only [Nat.add_comm]; exact h\n",
    ),
    // Constants by `Name.lt`, prefix first.
    (
        "constant_names",
        "opaque Foo.a : Nat → Nat\nopaque Bar.z : Nat → Nat\nexample (x : Nat) (p : Nat → Prop) (h : p (Bar.z x + Foo.a x)) : p (Foo.a x + Bar.z x) := by simp only [Nat.add_comm]; exact h\n",
    ),
    // The shorter application first.
    (
        "argument_count",
        "example (a b : Nat) (f : Nat → Nat) (g : Nat → Nat → Nat) (p : Nat → Prop) (h : p (f a + g a b)) : p (g a b + f a) := by simp only [Nat.add_comm]; exact h\n",
    ),
    // Binders compare domain, then body.
    (
        "lambdas",
        "opaque F : (Nat → Nat) → Nat\nexample (p : Nat → Prop) (h : p (F (fun x => x) + F (fun x => x + 1))) : p (F (fun x => x + 1) + F (fun x => x)) := by simp only [Nat.add_comm]; exact h\n",
    ),
    // Compared terms are reduced at reducible transparency: `c ≥ d` is `d ≤ c` and so comes
    // after `b ≤ a`, though `GE.ge` precedes `LE.le` by name.
    (
        "reducible_heads",
        "example (a b c d : Nat) (h : b ≤ a ∧ c ≥ d) : c ≥ d ∧ b ≤ a := by simp only [and_comm]; exact h\n",
    ),
    // A let variable is compared as its value (`zetaDelta`): `c` is `a`, before `b`.
    (
        "let_variable_value",
        "example (a b : Nat) (p : Nat → Prop) (h : p (a + b)) : p (b + a) := by\n  let c := a\n  show p (b + c)\n  simp only [Nat.add_comm]\n  exact h\n",
    ),
    // An abbreviation is unfolded (`upstream tests/elab/1815.lean`).
    (
        "abbreviations",
        "variable {α : Type} [Mul α] [Inhabited α]\nabbrev Left (a : α) : α := a * default\nabbrev Right (a : α) : α := default * a\naxiom mul_comm' (a b : α) : a * b = b * a\nexample (a : α) : Left a = Right a := by simp [mul_comm']\n",
    ),
    // `have` bodies are compared as their values (`upstream tests/elab/968.lean`).
    (
        "have_values",
        "example (p q r : Prop) : ((have x := p; x) ∧ (have x := q; x) ∧ (have x := r; x)) = ((have x := r; x) ∧ (have x := p; x) ∧ (have x := q; x)) := by simp only [and_comm, and_left_comm]\n",
    ),
    // Instance arguments are not compared.
    (
        "class_operation",
        "class Op (α : Type) where op : α → α → α\naxiom op_comm {α : Type} [Op α] (a b : α) : Op.op a b = Op.op b a\nexample {α : Type} [Op α] (a b : α) (p : α → Prop) (h : p (Op.op a b)) : p (Op.op b a) := by simp only [op_comm]; exact h\n",
    ),
    (
        "axiom_nested",
        "opaque f : Bool → Bool → Bool\naxiom f_comm (a b : Bool) : f a b = f b a\nexample (a b c : Bool) (p : Bool → Prop) (h : p (f c (f a b))) : p (f (f b a) c) := by simp only [f_comm]; exact h\n",
    ),
    // `↔` rules: `and`, `or`, `=` and `≠` commute.
    (
        "and_left_comm",
        "example (p q r : Prop) (h : p ∧ q ∧ r) : r ∧ q ∧ p := by simp only [and_comm, and_left_comm]; exact h\n",
    ),
    (
        "or_left_comm",
        "example (p q r : Prop) (h : p ∨ q ∨ r) : r ∨ q ∨ p := by simp only [or_comm, or_left_comm]; exact h\n",
    ),
    (
        "eq_comm",
        "example (a b : Nat) (h : a = b) : b = a := by simp only [eq_comm]; exact h\n",
    ),
    (
        "ne_comm",
        "example (a b : Nat) (h : a ≠ b) : b ≠ a := by simp only [ne_comm]; exact h\n",
    ),
    // A reversed permutation is one too; a partially applied one is not, and rewrites once.
    (
        "reversed",
        "example (a b : Nat) (p : Nat → Prop) (h : p (a + b)) : p (b + a) := by simp only [← Nat.add_comm]; exact h\n",
    ),
    (
        "partially_applied",
        "example (a b : Nat) (p : Nat → Prop) (h : p (b + a)) : p (a + b) := by simp only [Nat.add_comm a]; exact h\n",
    ),
    // A hypothesis with pattern variables.
    (
        "hypothesis_rule",
        "example (f : Nat → Nat → Nat) (hf : ∀ x y, f x y = f y x) (a b : Nat) (p : Nat → Prop) (h : p (f b a)) : p (f a b) := by simp only [hf] at h; exact h\n",
    ),
    // Beneath a binder the bound variable is the last local.
    (
        "under_binder",
        "example (a : Nat) (p : (Nat → Nat) → Prop) (h : p (fun x => a + x)) : p (fun x => x + a) := by simp only [Nat.add_comm]; exact h\n",
    ),
    (
        "quantified_default_set",
        "example (a : Nat) : ∀ x, x + a = a + x := by simp [Nat.add_comm]\n",
    ),
    // The rules' order decides the normal form. At `(a + b) + c` the pin tries `Nat.add_comm`
    // before `Nat.add_assoc`, however they are listed: its key has a variable where
    // `Nat.add_assoc`'s has `+`. So `Nat.add_assoc` is never used.
    (
        "comm_before_assoc_listed_second",
        "set_option linter.unusedSimpArgs false in\nexample (a b c : Nat) (p : Nat → Prop) (h : p (c + (a + b))) : p ((a + b) + c) := by simp only [Nat.add_assoc, Nat.add_comm]; exact h\n",
    ),
    (
        "comm_before_assoc_listed_first",
        "set_option linter.unusedSimpArgs false in\nexample (a b c : Nat) (p : Nat → Prop) (h : p (c + (a + b))) : p ((a + b) + c) := by simp only [Nat.add_comm, Nat.add_assoc]; exact h\n",
    ),
    (
        "four_summands",
        "set_option linter.unusedSimpArgs false in\nexample (a b c d : Nat) (p : Nat → Prop) (h : p (a + (b + (c + d)))) : p ((d + c) + (b + a)) := by simp only [Nat.add_assoc, Nat.add_comm]; exact h\n",
    ),
    (
        "four_summands_comm_only",
        "example (a b c d : Nat) (p : Nat → Prop) (h : p (a + b + (c + d))) : p ((d + c) + (b + a)) := by simp only [Nat.add_comm]; exact h\n",
    ),
    // Inner nodes first: `a + 0` becomes `a`, then the sum reorders.
    (
        "with_add_zero",
        "example (a b : Nat) (p : Nat → Prop) (h : p (a + b)) : p (b + (a + 0)) := by simp only [Nat.add_comm, Nat.add_zero]; exact h\n",
    ),
    (
        "products_and_sums",
        "example (a b c : Nat) (p : Nat → Prop) (h : p (a * (b * c))) : p (c * (b * a)) := by simp only [Nat.mul_comm, Nat.mul_left_comm]; exact h\n",
    ),
    // `attribute [local simp]` rules (`upstream tests/elab/ACltBug.lean`).
    (
        "local_simp_attributes",
        "attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm\nattribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm\nexample (w x y z : Nat) (p : Nat → Prop) (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by simp at *; assumption\n",
    ),
    // Every simplifier entry point: `simpa`, `simp_all`, conversion mode.
    (
        "simpa",
        "example (a b : Nat) (p : Nat → Prop) (h : p (b + a)) : p (a + b) := by simpa [Nat.add_comm] using h\n",
    ),
    (
        "simp_all",
        "example (a b : Nat) (h1 : b + a = 5) (h2 : a + b = 5 → False) : False := by simp_all [Nat.add_comm]\n",
    ),
    (
        "conv",
        "example (a b : Nat) (p : Nat → Prop) (h : p (a + b)) : p (b + a) := by\n  conv =>\n    arg 1\n    simp only [Nat.add_comm]\n  exact h\n",
    ),
];

/// Programs whose output is a `Try this:` suggestion, with how many they print.
const SUGGESTED: &[(&str, usize, &str)] = &[
    (
        "suggest_comm",
        1,
        "example (a b : Nat) : a + b = b + a := by simp? [Nat.add_comm]\n",
    ),
    (
        "suggest_comm_left_comm",
        1,
        "example (a b c : Nat) : a + b + c = c + b + a := by simp? [Nat.add_comm, Nat.add_left_comm]\n",
    ),
    // `Nat.add_left_comm` is never used, so it is not printed.
    (
        "suggest_drops_unused",
        1,
        "example (a b c : Nat) (p : Nat → Prop) (h : p (a + (b + c))) : p (c + b + a) := by simp? only [Nat.add_comm, Nat.add_left_comm]; exact h\n",
    ),
    (
        "suggest_at_hypothesis",
        1,
        "example (a b : Nat) (p : Nat → Prop) (h : p (b + a)) : p (a + b) := by\n  simp? only [Nat.add_comm] at h\n  exact h\n",
    ),
];

const REFUSED: &[(&str, &str)] = &[
    // The normal form is `a + b`, so `h` no longer closes the goal.
    (
        "other_normal_form",
        "example (a b : Nat) (p : Nat → Prop) (h : p (b + a)) : p (b + a) := by simp only [Nat.add_comm]; exact h\n",
    ),
    // Already ordered: nothing rewrites, and `simp` made no progress.
    (
        "already_ordered",
        "example (a b : Nat) (p : Nat → Prop) (h : p (a + b)) : p (a + b) := by simp only [Nat.add_comm]; exact h\n",
    ),
    (
        "hypothesis_already_ordered",
        "example (a b : Nat) (p : Nat → Prop) (h : p (a + b)) : p (b + a) := by simp only [Nat.add_comm] at h; exact h\n",
    ),
    (
        "literal_values_ordered",
        "example (a : Nat) (p : Nat → Prop) (h : p (2 * a + 10 * a)) : p (2 * a + 10 * a) := by simp only [Nat.add_comm]; exact h\n",
    ),
    (
        "reduced_heads_ordered",
        "example (a b c d : Nat) (h : c ≥ d ∧ b ≤ a) : c ≥ d ∧ b ≤ a := by simp only [and_comm]; exact h\n",
    ),
    (
        "numeral_not_first",
        "example (a : Nat) (p : Nat → Prop) (h : p (2 * a)) : p (a * 2) := by simp only [Nat.mul_comm]; exact h\n",
    ),
    // `Nat.add_comm` first leaves `c + (a + b)`, not the associated form.
    (
        "not_the_associated_form",
        "example (a b c : Nat) (p : Nat → Prop) (h : p (a + (b + c))) : p ((a + b) + c) := by simp only [Nat.add_comm, Nat.add_assoc]; exact h\n",
    ),
    (
        "abbreviation_not_unfolded_away",
        "variable {α : Type} [Mul α] [Inhabited α]\nabbrev Left (a : α) : α := a * default\naxiom mul_comm' (a b : α) : a * b = b * a\nexample (a : α) (p : α → Prop) (h : p (default * a)) : p (Left a) := by simp only [mul_comm']; exact h\n",
    ),
    // Two closed equations that undo each other are no permutation: the pin loops until its
    // step limit, this engine refuses the cycle.
    (
        "genuine_cycle",
        "example (P : Nat → Prop) (x y : Nat) (h : x = y) (k : y = x) : P x := by simp only [h, k]\n",
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
        "fln-simp-permutation-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// This crate's `lean` on `HEADER` + `program`, and the pinned `lean` when present.
fn outputs(lib: &Path, root: &Path, name: &str, program: &str) -> (Output, Option<Output>) {
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
        .filter(|lean| lean.is_file())
        .map(|pinned| run(&pinned));
    (run(Path::new(env!("CARGO_BIN_EXE_lean"))), pinned)
}

#[test]
fn permutation_rules_reach_the_pins_normal_form() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    for (name, program) in ACCEPTED {
        let (ours, pinned) = outputs(&lib, &root, name, program);
        assert_eq!(
            ours.status.code(),
            Some(0),
            "{name}: {program}\n{}",
            String::from_utf8_lossy(&ours.stderr)
        );
        if let Some(pinned) = pinned {
            assert_eq!(pinned.status.code(), Some(0), "{name}: the pin refuses it");
            assert_eq!(
                String::from_utf8_lossy(&ours.stdout),
                String::from_utf8_lossy(&pinned.stdout),
                "{name}: {program}"
            );
        }
    }
    for (name, program) in REFUSED {
        let (ours, pinned) = outputs(&lib, &root, name, program);
        assert_ne!(ours.status.code(), Some(0), "{name}: accepted {program}");
        if let Some(pinned) = pinned {
            assert_ne!(pinned.status.code(), Some(0), "{name}: the pin accepts it");
        }
    }
}

#[test]
fn suggestions_with_permutation_rules_are_the_pins() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    for &(name, suggestions, program) in SUGGESTED {
        let (ours, pinned) = outputs(&lib, &root, name, program);
        assert_eq!(
            ours.status.code(),
            Some(0),
            "{name}: {program}\n{}",
            String::from_utf8_lossy(&ours.stderr)
        );
        let ours = String::from_utf8(ours.stdout).expect("UTF-8 output");
        assert_eq!(
            ours.matches("Try this:").count(),
            suggestions,
            "{name}: {ours}"
        );
        if let Some(pinned) = pinned {
            assert_eq!(pinned.status.code(), Some(0), "{name}: the pin refuses it");
            assert_eq!(
                ours,
                String::from_utf8(pinned.stdout).expect("UTF-8 output"),
                "{name}: {program}"
            );
        }
    }
}
