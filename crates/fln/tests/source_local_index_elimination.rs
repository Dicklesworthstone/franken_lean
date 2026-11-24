//! Dependent elimination preserves the pin's raw-variable substitution boundary.
//!
//! These source bodies were checked individually with a `prelude` and `import Init.Core` header
//! against pinned Lean v4.32.0 on 2026-11-24. The first eleven were also checked
//! unchanged through the native public module API after importing that physical
//! Init.Core closure: all were accepted before the fix, including five that the
//! pin refuses. These regressions use the standard native source seed.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

const VEC: &str = "inductive LetIndexProbeVec (A : Type) : Nat → Type where\n  | nil : LetIndexProbeVec A 0\n  | cons (n : Nat) (x : A) (xs : LetIndexProbeVec A n) : LetIndexProbeVec A (n + 1)\n";

fn checked(source: &str, refused: bool) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let result = engine.check_source_files(
        &[source.as_bytes()],
        &options,
        SourceCheckLimits::new(limits),
    );
    if refused {
        let error = result.expect_err("the pin refuses this dependent elimination");
        assert!(
            format!("{error:?}").contains("SubstitutionLocal"),
            "expected a failed index substitution for:\n{source}\n{error:?}"
        );
        assert_eq!(engine.logical_root(&options), root);
    } else {
        result
            .unwrap_or_else(|error| panic!("the pin accepts:\n{source}\n{error:?}"))
            .into_complete()
            .unwrap();
    }
}

#[test]
fn selected_local_index_definitions_cannot_be_unfolded_to_prune_branches() {
    // Pattern typing accepts each wildcard. The later dependent elimination
    // cannot substitute `two`/`m`, a local definition, against the nil index.
    for body in [
        "def f (xs : LetIndexProbeVec Nat 2) : Nat := let two := 2; let ys : LetIndexProbeVec Nat two := xs; match ys with | .cons _ x _ => x",
        "def f (xs : LetIndexProbeVec Nat 2) : Nat := let two : Nat := 2; let ys : LetIndexProbeVec Nat two := xs; match ys with | .cons _ x _ => x",
        "def f (xs : LetIndexProbeVec Nat 2) : Nat := let two := 2; let ys : LetIndexProbeVec Nat two := xs; match (ys : LetIndexProbeVec Nat 2) with | .cons _ x _ => x",
        "def f (xs : LetIndexProbeVec Nat 2) : Nat := let two := 2; have ys : LetIndexProbeVec Nat two := xs; match ys with | .cons _ x _ => x",
        "def f (n : Nat) (xs : LetIndexProbeVec Nat (Nat.succ n)) : Nat := let m := Nat.succ n; let ys : LetIndexProbeVec Nat m := xs; match ys with | .cons _ x _ => x",
    ] {
        checked(&format!("{VEC}{body}\n"), true);
    }
}

#[test]
fn local_majors_and_unselected_let_indices_preserve_valid_matches() {
    for body in [
        "def f (xs : LetIndexProbeVec Nat 2) : Nat := match xs with | .cons _ x _ => x",
        "def f (xs : LetIndexProbeVec Nat 2) : Nat := let ys : LetIndexProbeVec Nat 2 := xs; match ys with | .cons _ x _ => x",
        "def f (xs : LetIndexProbeVec Nat 2) : Nat := let two := 2; let ys : LetIndexProbeVec Nat two := xs; match xs with | .cons _ x _ => x",
        "def f (xs : LetIndexProbeVec Nat 2) : Nat := let two := 2; let ys : LetIndexProbeVec Nat two := xs; match ys with | _ => 0",
        "def f (xs : LetIndexProbeVec Nat 2) : Nat := let two := 2; let ys : LetIndexProbeVec Nat two := xs; match ys with | whole => 0",
        "def f (n : Nat) (xs : LetIndexProbeVec Nat (Nat.succ n)) : Nat := let m := n; let ys : LetIndexProbeVec Nat (Nat.succ m) := xs; match ys with | .cons _ x _ => x",
    ] {
        checked(&format!("{VEC}{body}\n"), false);
    }
}

#[test]
fn reflexivity_and_real_variable_substitutions_remain_available() {
    // An alias of a genuine index variable can still be generalized and
    // substituted, with either a wildcard or a named constructor field.
    for field in ["_", "k"] {
        checked(
            &format!(
                "{VEC}def f (n : Nat) (xs : LetIndexProbeVec Nat n) : Nat := let m := n; let ys : LetIndexProbeVec Nat m := xs; match ys with | .nil => 0 | .cons {field} x _ => x\n"
            ),
            false,
        );
    }
    // The selected let is definitionally equal to the constructor's index.
    checked(
        "inductive LetIndexProbeZero : Nat → Type where | mk : LetIndexProbeZero 0\n\
         def f (xs : LetIndexProbeZero 0) : Nat := let m := 0; let ys : LetIndexProbeZero m := xs; match ys with | .mk => 0\n",
        false,
    );
    // When both endpoints are locals, the later constructor field is selected,
    // not the earlier let. The fixed first index prevents parameter promotion.
    for alternative in [".mk _ => 0", ".mk k => k"] {
        checked(
            &format!(
                "inductive LetIndexProbePair : Nat → Nat → Type where | mk (n : Nat) : LetIndexProbePair 0 n\n\
                 def f (xs : LetIndexProbePair 0 2) : Nat := let m := 2; let ys : LetIndexProbePair 0 m := xs; match ys with | {alternative}\n"
            ),
            false,
        );
    }
}

#[test]
fn cases_uses_the_same_local_index_substitution_boundary() {
    checked(
        &format!(
            "{VEC}def f (xs : LetIndexProbeVec Nat 2) : Nat := let two := 2; let ys : LetIndexProbeVec Nat two := xs; by cases ys with | cons n x tail => exact x\n"
        ),
        true,
    );
    checked(
        &format!(
            "{VEC}def f (xs : LetIndexProbeVec Nat 2) : Nat := by cases xs with | cons n x tail => exact x\n"
        ),
        false,
    );
}
