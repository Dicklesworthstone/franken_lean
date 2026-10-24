//! `rw` rewrites the goal as the pin's `kabstract` abstracts it and closes it with the pin's
//! reducible `rfl`, judged against the pinned `lean`.
//!
//! The pin's `rw` is `rewrite` then `try (with_reducible rfl)` (`Init/Tactics.lean:605-609`).
//! `rewrite` abstracts the rule's left side with `kabstract` (`Lean/Meta/KAbstract.lean`): a
//! local only where it occurs, any other pattern only at subterms with its head symbol and
//! argument count, by `isDefEq` under `Rewrite.Config` (reducible, offset constraints;
//! `Init/Meta/Defs.lean:1732-1734`), and instantiates the motive with the right side, nothing
//! more. The closing `rfl` is reducible (`Eq.refl`, `HEq.refl`, `Iff.refl`), so `n + 0 = n`
//! stays open: `isDefEqOffset` (`Lean/Meta/Offset.lean:116`) leaves an offset against a bare
//! term undecided and `Nat.add` does not unfold at reducible transparency.
//!
//! Every program was run through the pinned `lean` v4.32.0 with `HEADER` first (2026-10-23;
//! the headerless verdicts are the same), and is compared with the pinned binary again when
//! present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.SimpLemmas\n";

/// Accepted at the pin and here.
const ACCEPTED: &[(&str, &str)] = &[
    (
        "reflexive_result",
        "example (n m : Nat) (h : m = n) : m = n := by rw [h]\n",
    ),
    (
        "symmetric",
        "example (n m : Nat) (h : m = n) : n = m := by rw [h]\n",
    ),
    (
        "reverse",
        "example (n m : Nat) (h : n = m) : m = n := by rw [← h]\n",
    ),
    (
        "two_rules",
        "example (a b c : Nat) (h1 : a = b) (h2 : c = b) : a = c := by rw [h1, h2]\n",
    ),
    // Literal arithmetic and offsets close through `isDefEqOffset`/`evalNat`.
    (
        "literal_sum",
        "example (n : Nat) (h : n = 2) : n + 2 = 4 := by rw [h]\n",
    ),
    (
        "literal_zero_offset",
        "example (n : Nat) (h : n = 0) : n + 0 = 0 := by rw [h]\n",
    ),
    (
        "literal_zero_left",
        "example (n : Nat) (h : n = 3) : 0 + n = 3 := by rw [h]\n",
    ),
    (
        "literal_product",
        "example (n : Nat) (h : n = 2) : n * 3 = 6 := by rw [h]\n",
    ),
    (
        "literal_power",
        "example (n : Nat) (h : n = 2) : n ^ 3 = 8 := by rw [h]\n",
    ),
    (
        "literal_quotient_remainder",
        "example (n : Nat) (h : n = 7) : n / 2 + n % 2 = 4 := by rw [h]\n",
    ),
    (
        "offsets_equal",
        "example (n m : Nat) (h : m = n) : m + 1 = n + 1 := by rw [h]\n",
    ),
    (
        "offset_successor",
        "example (n m : Nat) (h : m = n) : m + 1 = Nat.succ n := by rw [h]\n",
    ),
    (
        "offsets_combined",
        "example (n m : Nat) (h : m = n) : m + 2 + 3 = n + 5 := by rw [h]\n",
    ),
    (
        "zero_offsets_both_sides",
        "example (n m : Nat) (h : m = n) : m + 0 = n + 0 := by rw [h]\n",
    ),
    (
        "abbreviation",
        "abbrev myid (x : Nat) : Nat := x\n\
         example (n m : Nat) (h : m = n) : myid m = n := by rw [h]\n",
    ),
    (
        "library_rule",
        "example (n : Nat) : n + 0 = n := by rw [Nat.add_zero]\n",
    ),
    // The goal `rw` leaves open is the pin's: later tactics finish it.
    (
        "rewrite_then_rfl",
        "example (n m : Nat) (h : m = n) : m + 0 = n := by rewrite [h]; rfl\n",
    ),
    (
        "open_goal_then_exact",
        "example (n m : Nat) (h : m = n) : m + 0 = n := by rw [h]; exact Nat.add_zero n\n",
    ),
    (
        "hypothesis_then_exact",
        "example (n m : Nat) (h : m = n) (h' : m + 0 = n) : n + 0 = n := by rw [h] at h'; exact h'\n",
    ),
    (
        "hypothesis_then_closing",
        "example (n m : Nat) (h : m = n) (h' : m = 0) : n = n := by rw [h] at h'\n",
    ),
    (
        "wildcard",
        "example (n m : Nat) (h : m = n) (h' : m = 0) : m = n := by rw [h] at *\n",
    ),
    (
        "under_binder",
        "example (n m : Nat) (h : m = n) : (fun x : Nat => x + m) = (fun x => x + n) := by rw [h]\n",
    ),
    // `Iff.refl` is the pin's `@[refl]` lemma for `↔` (`Init/Core.lean:1035,1042`).
    (
        "equivalence",
        "example (P Q : Prop) (h : P = Q) : P ↔ Q := by rw [h]\n",
    ),
    (
        "equivalence_rule",
        "example (P Q : Prop) (h : P ↔ Q) : P ↔ Q := by rw [h]\n",
    ),
    (
        "equivalence_reversed_rule",
        "example (P Q : Prop) (h : P ↔ Q) : Q ↔ P := by rw [h]\n",
    ),
    (
        "equivalence_compound",
        "example (P Q : Prop) (h : P = Q) : (P ∧ True) ↔ (Q ∧ True) := by rw [h]\n",
    ),
    (
        "equivalence_abbreviation",
        "abbrev Q (P : Prop) : Prop := P\nexample (P R : Prop) (h : P = R) : Q P ↔ R := by rw [h]\n",
    ),
    (
        "equivalence_after_hypothesis",
        "example (P Q : Prop) (h : P = Q) (k : P) : Q ↔ Q := by rw [h] at k\n",
    ),
    (
        "heterogeneous",
        "example (a b : Nat) (h : a = b) : HEq a b := by rw [h]\n",
    ),
    // Occurrence selection with offset constraints (`?x + 1 =?= 5` gives `?x := 4`).
    (
        "offset_pattern_offset",
        "example (f : Nat → Nat) (h : ∀ x, f (x + 1) = x) (n : Nat) : f (n + 1) = n := by rw [h]\n",
    ),
    (
        "offset_pattern_literal",
        "example (f : Nat → Nat) (h : ∀ x, f (x + 1) = x) : f 5 = 4 := by rw [h]\n",
    ),
    (
        "offset_pattern_difference",
        "example (f : Nat → Nat) (h : ∀ x, f (x + 1) = x) (n : Nat) : f (n + 3) = n + 2 := by rw [h]\n",
    ),
    (
        "offset_pattern_successors",
        "example (f : Nat → Nat) (h : ∀ x, f (x + 2) = x) : f (Nat.succ (Nat.succ 3)) = 3 := by rw [h]\n",
    ),
    (
        "successor_pattern_literal",
        "example (f : Nat → Nat) (h : ∀ x, f (Nat.succ x) = x) : f 5 = 4 := by rw [h]\n",
    ),
    (
        "reversed_offset_pattern",
        "example (f : Nat → Nat) (h : ∀ x, x = f (x + 1)) : f 5 = 4 := by rw [← h]\n",
    ),
    (
        "offset_pattern_hypothesis",
        "example (f : Nat → Nat) (h : ∀ x, f (x + 1) = x) (k : f 5 = 4) : True := by rw [h] at k; trivial\n",
    ),
    (
        "primitive_addition_argument",
        "example (f : Nat → Nat) (n : Nat) (h : f (Nat.add n 1) = 0) : f (n + 1) = 0 := by rw [h]\n",
    ),
    // `?x + 0 =?= a + 0 + 0` cancels the whole offset: `?x := a`, so the goal is `a = a`.
    (
        "nested_zero_offsets_rule",
        "example (a : Nat) (h : ∀ x : Nat, x + 0 = x) : a + 0 + 0 = a := by rw [h]\n",
    ),
    (
        "nested_zero_offsets_library",
        "example (a : Nat) : a + 0 + 0 = a := by rw [Nat.add_zero]\n",
    ),
    (
        "abbreviation_argument",
        "abbrev two : Nat := 2\nexample (f : Nat → Nat) (h : f 2 = 0) : f two = 0 := by rw [h]\n",
    ),
    // Every instance of the pattern is abstracted, not only its exact copies.
    (
        "numeral_every_instance",
        "example (h : (2 : Nat) = 3) : (2 : Nat) + 2 = 6 := by rw [h]\n",
    ),
    (
        "numeral_in_argument",
        "example (h : (6 : Nat) = 6) (f : Nat → Nat) : f 6 = f 6 := by rw [h]\n",
    ),
    (
        "abbreviation_second_instance",
        "abbrev two : Nat := 2\nexample (f : Nat → Nat) (h : f 2 = 0) : f 2 + f two = 0 := by rw [h]\n",
    ),
    (
        "local_definition_closing",
        "example (n : Nat) : let m := n; m = n := by intro m; rw [show n = n from rfl]\n",
    ),
];

/// Rejected at the pin and here. `UNSOLVED`: the pin reports "unsolved goals" with the goal
/// noted; `NO_OCCURRENCE`: the pin's "Did not find an occurrence of the pattern".
const UNSOLVED: &str = "unsolved goals";
const NO_OCCURRENCE: &str = "rewrite found no matching occurrence";
const REJECTED: &[(&str, &str, &str)] = &[
    // ⊢ n + 0 = n
    (
        "zero_offset",
        "example (n m : Nat) (h : m = n) : m + 0 = n := by rw [h]\n",
        UNSOLVED,
    ),
    // ⊢ 0 + n = n
    (
        "zero_left",
        "example (n m : Nat) (h : m = n) : 0 + m = n := by rw [h]\n",
        UNSOLVED,
    ),
    // ⊢ n * 1 = n
    (
        "one_factor",
        "example (n m : Nat) (h : m = n) : m * 1 = n := by rw [h]\n",
        UNSOLVED,
    ),
    // ⊢ 2 + 2 = 5
    (
        "literal_mismatch",
        "example (n : Nat) (h : n = 2) : n + 2 = 5 := by rw [h]\n",
        UNSOLVED,
    ),
    // ⊢ n + 2 + 3 = n + 6
    (
        "offset_mismatch",
        "example (n m : Nat) (h : m = n) : m + 2 + 3 = n + 6 := by rw [h]\n",
        UNSOLVED,
    ),
    // ⊢ n + 0 = n
    (
        "zero_offset_both_occurrences",
        "example (n m : Nat) (h : m = n) : m + 0 = m := by rw [h]\n",
        UNSOLVED,
    ),
    (
        "zero_offset_reverse",
        "example (n m : Nat) (h : n = m) : m + 0 = n := by rw [← h]\n",
        UNSOLVED,
    ),
    (
        "zero_offset_two_rules",
        "example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a + 0 = c := by rw [h1, h2]\n",
        UNSOLVED,
    ),
    // ⊢ mydef n = n
    (
        "definition",
        "def mydef (x : Nat) : Nat := x\n\
         example (n m : Nat) (h : m = n) : mydef m = n := by rw [h]\n",
        UNSOLVED,
    ),
    (
        "identity",
        "example (n m : Nat) (h : m = n) : id m = n := by rw [h]\n",
        UNSOLVED,
    ),
    // `f (n + 0)` is the instance; the goal left is `n + 0 = n`.
    (
        "rule_instance_offset",
        "example (f : Nat → Nat) (h : ∀ x, f x = x) (n : Nat) : f (n + 0) = n := by rw [h]\n",
        UNSOLVED,
    ),
    (
        "rewrite_does_not_close",
        "example (n m : Nat) (h : m = n) : m = n := by rewrite [h]\n",
        UNSOLVED,
    ),
    // `rw … at h` tries `rfl` on the main goal, `n + 0 = n`.
    (
        "hypothesis_location_main_goal",
        "example (n m : Nat) (h : m = n) (h' : m = 0) : n + 0 = n := by rw [h] at h'\n",
        UNSOLVED,
    ),
    (
        "target_location",
        "example (n m : Nat) (h : m = n) : m + 0 = n := by rw [h] at ⊢\n",
        UNSOLVED,
    ),
    (
        "wildcard_location",
        "example (n m : Nat) (h : m = n) (h' : m = 0) : m + 0 = n := by rw [h] at *\n",
        UNSOLVED,
    ),
    (
        "under_binder_offset",
        "example (n m : Nat) (h : m = n) : (fun x : Nat => x + (m + 0)) = (fun x => x + n) := by rw [h]\n",
        UNSOLVED,
    ),
    (
        "equivalence_offset",
        "example (P : Nat → Prop) (n m : Nat) (h : m = n) : P (m + 0) ↔ P n := by rw [h]\n",
        UNSOLVED,
    ),
    (
        "equivalence_definition",
        "def Q (P : Prop) : Prop := P\nexample (P R : Prop) (h : P = R) : Q P ↔ R := by rw [h]\n",
        UNSOLVED,
    ),
    (
        "heterogeneous_offset",
        "example (a b : Nat) (h : a = b) : HEq (a + 0) b := by rw [h]\n",
        UNSOLVED,
    ),
    (
        "heterogeneous_right_offset",
        "example (a b : Nat) (h : a = b) : HEq a (b + 0) := by rw [h]\n",
        UNSOLVED,
    ),
    // `True` is not closed by `rfl`.
    (
        "true_result",
        "example (P : Prop) (h : P = True) : P := by rw [h]\n",
        UNSOLVED,
    ),
    // The local `m := n + 0` is unfolded, and `n + 0 = n` is not closed.
    (
        "local_definition_offset",
        "example (n : Nat) : let m := n + 0; m = n := by intro m; rw [show n = n from rfl]\n",
        UNSOLVED,
    ),
    // ⊢ q.fst + 0 = q.fst
    (
        "projection_pattern",
        "example (p q : Nat × Nat) (h : p.1 = q.1) : p.1 + 0 = q.1 := by rw [h]\n",
        UNSOLVED,
    ),
    // A local pattern is abstracted only where it occurs: ⊢ b + 0 + 0 = b.
    (
        "nested_zero_offsets_local",
        "example (a b : Nat) (h : a = b) : a + 0 + 0 = b := by rw [h]\n",
        UNSOLVED,
    ),
    // `(a + b) + 0` does not match `a + b`; the inner `a + b` does: ⊢ b + a + 0 = b + a.
    (
        "sum_pattern_under_offset",
        "example (a b : Nat) (h : a + b = b + a) : a + b + 0 = b + a := by rw [h]\n",
        UNSOLVED,
    ),
    // Reducible `isDefEq` does not unfold `Nat.add` or an instance in an argument.
    (
        "zero_offset_argument",
        "example (f : Nat → Nat) (n : Nat) (h : f n = 5) : f (n + 0) = 5 := by rw [h]\n",
        NO_OCCURRENCE,
    ),
    (
        "zero_offset_pattern_argument",
        "example (f : Nat → Nat) (h : ∀ x, f (x + 0) = x) (n : Nat) : f n = n := by rw [h]\n",
        NO_OCCURRENCE,
    ),
    (
        "instance_argument",
        "example (f : Nat → Nat) (n : Nat) (h : f (Nat.mul n 2) = 0) : f (n * 2) = 0 := by rw [h]\n",
        NO_OCCURRENCE,
    ),
    // Only subterms with the pattern's head symbol are candidates.
    (
        "successor_head",
        "example (n : Nat) (h : Nat.succ n = 7) : n + 1 = 7 := by rw [h]\n",
        NO_OCCURRENCE,
    ),
    (
        "addition_head",
        "example (n : Nat) (h : n + 1 = 7) : Nat.succ n = 7 := by rw [h]\n",
        NO_OCCURRENCE,
    ),
    (
        "zero_offset_rule_bare_target",
        "example (n m : Nat) (h : m + 0 = n) : m = n := by rw [h]\n",
        NO_OCCURRENCE,
    ),
    (
        "offset_above_literal",
        "example (f : Nat → Nat) (h : ∀ x, f (x + 2) = x) : f 1 = 0 := by rw [h]\n",
        NO_OCCURRENCE,
    ),
    // The first rule already leaves `a = a`; the second finds nothing.
    (
        "nested_zero_offsets_twice",
        "example (a : Nat) (h : ∀ x : Nat, x + 0 = x) : a + 0 + 0 = a := by rw [h, h]\n",
        NO_OCCURRENCE,
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

/// `fln check-source` on `HEADER` + `program`, and the pinned binary's exit code and output
/// when present.
fn check(
    lib: &Path,
    root: &Path,
    name: &str,
    program: &str,
) -> (i32, String, Option<(i32, String)>) {
    check_under(HEADER, lib, root, name, program)
}

/// [`check`] with another header.
fn check_under(
    header: &str,
    lib: &Path,
    root: &Path,
    name: &str,
    program: &str,
) -> (i32, String, Option<(i32, String)>) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{header}{program}")).unwrap();
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
            let output = Command::new(pinned)
                .arg(&entry)
                .env("LEAN_PATH", lib)
                .output()
                .expect("run the pinned lean");
            (
                output.status.code().expect("normal pinned exit"),
                format!(
                    "{}{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                ),
            )
        });
    (
        ours.status.code().expect("normal process exit"),
        String::from_utf8_lossy(&ours.stderr).into_owned(),
        theirs,
    )
}

#[test]
fn rw_abstracts_and_closes_as_the_pin() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    // One workspace, so the import closure is admitted once for every program.
    let root = std::env::temp_dir().join(format!(
        "fln-rewrite-closing-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&root).unwrap();
    for (name, program) in ACCEPTED {
        let (code, stderr, pinned) = check(&lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
        if let Some((pinned, output)) = pinned {
            assert_eq!(pinned, 0, "{name}: the pinned lean rejects it\n{output}");
        }
    }
    for (name, program, reason) in REJECTED {
        let (code, stderr, pinned) = check(&lib, &root, name, program);
        assert_ne!(code, 0, "{name}: accepted {program}");
        assert!(
            stderr.contains(reason),
            "{name}: not rejected for `{reason}`\n{stderr}"
        );
        if let Some((pinned, output)) = pinned {
            assert_ne!(pinned, 0, "{name}: the pinned lean accepts it");
            let expected = if *reason == UNSOLVED {
                "unsolved goals"
            } else {
                "Did not find an occurrence of the pattern"
            };
            assert!(
                output.contains(expected),
                "{name}: the pinned lean does not report `{expected}`\n{output}"
            );
        }
    }
}

/// `funext` (`Init.NotationExtra`'s syntax) leaves the pointwise goal head-reduced, as the pin's
/// `apply funext` does through `instantiateMVars`, so `rw` finds `y + x + 0` in it (upstream
/// `elab/funext`). Both programs are accepted by the pinned v4.32.0 under this header
/// (2026-10-24).
#[test]
fn funext_goals_are_head_reduced_for_rw() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = std::env::temp_dir().join(format!(
        "fln-rewrite-funext-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&root).unwrap();
    let header = "prelude\nimport Init.SimpLemmas\nimport Init.NotationExtra\n";
    for (name, program) in [
        (
            "funext_named",
            "theorem ex2 : (fun y x : Nat => y + x + 0) = (fun x y : Nat => y + x) := by\n  \
             funext x y\n  rw [Nat.add_zero, Nat.add_comm]\n",
        ),
        (
            "funext_bare",
            "theorem ex6 : (fun (x : Nat) y z => x + y + z) = (fun x y z => x + (y + z)) := by\n  \
             funext\n  rw [Nat.add_assoc]\n",
        ),
    ] {
        let (code, stderr, pinned) = check_under(header, &lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
        if let Some((pinned, output)) = pinned {
            assert_eq!(pinned, 0, "{name}: the pinned lean rejects it\n{output}");
        }
    }
}
