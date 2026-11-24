//! A match's patterns, and an application's postponed arguments, are typed as the pin types them
//! (bead `franken_lean-z8j.1.6.3`). For patterns (R2): a named pattern variable is rigid, `_` is
//! not, a top-level pattern whose type does not unify is refined only along a path to a free
//! variable, and a nested pattern is never refined. For applications (R1): see the last two tests.
//!
//! The original program verdicts were taken from pinned `lean` (v4.32.0) on 2026-10-10;
//! the alias and local-index regressions were checked individually on 2026-11-24 against
//! the same pin. `set_option trace.Elab.match true` showed the refinement steps cited.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckError, SourceCheckLimits};

fn check(source: &str) -> Result<(), SourceCheckError> {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .map(|outcome| {
            outcome.into_complete().unwrap();
        })
}

fn accepted(source: &str) {
    check(source).unwrap_or_else(|error| panic!("the pin accepts:\n{source}\n{error:?}"));
}

/// Refused for the pin's reason: a type mismatch of a pattern, not some other gap.
fn mismatched(source: &str) {
    match check(source) {
        Ok(()) => panic!("the pin refuses this program (Type mismatch):\n{source}"),
        Err(error) => assert!(
            format!("{error:?}").contains("TypeMismatch"),
            "{source}\n{error:?}"
        ),
    }
}

const VEC: &str = "inductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A 0\n  | cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (n + 1)\n";
const F: &str = "inductive F : Nat → Type where\n  | nil (n : Nat) : F n\n  | cons (n : Nat) (t : F n) : F (n + 1)\n";

/// `k + 1 =?= 2` with `k` rigid fails, and no path leads from the literal `2` (nor from
/// `Nat.succ 1`, which `whnfD` folds to it) to a variable; `_` unifies (`?m := 1`).
#[test]
fn a_named_field_against_a_literal_index_is_a_mismatch() {
    mismatched(&format!(
        "{VEC}def f (xs : Vec Nat 2) : Nat := match xs with | .cons k x _ => x\n"
    ));
    mismatched(&format!(
        "{VEC}def f (xs : Vec Nat (Nat.succ 1)) : Nat := match xs with | .cons k x _ => x\n"
    ));
    accepted(&format!(
        "{VEC}def f (xs : Vec Nat 2) : Nat := match xs with | .cons _ x _ => x\n"
    ));
    // As equations too (the pin elaborates them as a match on the parameters).
    mismatched(&format!(
        "{VEC}def f : Vec Nat 2 → Nat\n  | .cons k x _ => x\n"
    ));
}

/// Naming a fixed index does not make it a free variable: the pin unfolds
/// reducible definitions before searching for a refinement path. The named
/// constructor field remains rigid, whereas a wildcard can be assigned.
#[test]
fn reducible_index_aliases_preserve_rigid_pattern_typing() {
    for alias in ["abbrev two : Nat := 2", "def two : Nat := 2"] {
        mismatched(&format!(
            "{VEC}{alias}\ndef f (xs : Vec Nat two) : Nat := match xs with | .cons k x _ => x\n"
        ));
        accepted(&format!(
            "{VEC}{alias}\ndef f (xs : Vec Nat two) : Nat := match xs with | .cons _ x _ => x\n"
        ));
    }
    // A constructor's closed argument may itself need unfolding before whnfD
    // recognizes the whole index as a literal.
    mismatched(&format!(
        "{VEC}abbrev one : Nat := 1\ndef f (xs : Vec Nat (Nat.succ one)) : Nat := match xs with | .cons k x _ => x\n"
    ));
    accepted(&format!(
        "{VEC}abbrev one : Nat := 1\ndef f (xs : Vec Nat (Nat.succ one)) : Nat := match xs with | .cons _ x _ => x\n"
    ));
}

/// Default transparency unfolds the ordinary definition above but preserves
/// an irreducible one. Even a wildcard cannot solve the pin's opaque index.
#[test]
fn irreducible_index_aliases_stay_opaque_during_pattern_replay() {
    let source = format!(
        "{VEC}@[irreducible] def two : Nat := 2\ndef f (xs : Vec Nat two) : Nat := match xs with | .cons _ x _ => x\n"
    );
    // Native elaboration already refuses at coverage checking; retain that
    // semantic refusal without requiring the pin's earlier pattern diagnostic.
    let error = check(&source).expect_err("the pin refuses the irreducible index");
    assert!(
        format!("{error:?}").contains("EliminationCoverage"),
        "{source}\n{error:?}"
    );
}

/// The same decision applies through a type alias or a local let. Reducing
/// these wrappers must retain the original discriminant for valid variable
/// refinement, rather than treating every aliased index as a fixed literal.
#[test]
fn aliased_families_and_local_indices_keep_their_refinement_boundary() {
    mismatched(&format!(
        "{VEC}abbrev PairVec := Vec Nat 2\ndef f (xs : PairVec) : Nat := match xs with | .cons k x _ => x\n"
    ));
    accepted(&format!(
        "{VEC}abbrev PairVec := Vec Nat 2\ndef f (xs : PairVec) : Nat := match xs with | .cons _ x _ => x\n"
    ));
    mismatched(&format!(
        "{VEC}def f (xs : Vec Nat 2) : Nat := let two := 2; let ys : Vec Nat two := xs; match ys with | .cons k x _ => x\n"
    ));
    mismatched(&format!(
        "{VEC}def f (xs : Vec Nat (let two := 2; two)) : Nat := match xs with | .cons k x _ => x\n"
    ));
    accepted(&format!(
        "{VEC}def f (xs : Vec Nat (let two := 2; two)) : Nat := match xs with | .cons _ x _ => x\n"
    ));
}

/// Unfolding an alias can still expose a path to an actual free variable. Both
/// the family's head and the original index along that path matter.
#[test]
fn aliased_open_indices_still_refine() {
    accepted(&format!(
        "{VEC}abbrev next (n : Nat) := Nat.succ n\ndef f (n : Nat) (xs : Vec Nat (next n)) : Nat := match xs with | .cons k x _ => x\n"
    ));
    accepted(&format!(
        "{VEC}abbrev SV (n : Nat) := Vec Nat (Nat.succ n)\ndef f (n : Nat) (xs : SV n) : Nat := match xs with | .cons k x _ => x\n"
    ));
    accepted(&format!(
        "{VEC}abbrev idn (n : Nat) := n\ndef f (n : Nat) (xs : Vec Nat (idn n)) : Nat := match xs with | .nil => 0 | .cons k x _ => x\n"
    ));
    accepted(&format!(
        "{VEC}abbrev ident (n : Nat) := n\ndef f (n : Nat) (xs : Vec Nat (Nat.succ (ident n))) : Nat := match xs with | .cons k x _ => x\n"
    ));
}

/// A closed non-Nat constructor index has a refinement path, unlike a Nat
/// literal. Hiding it behind an alias preserves the original discriminant type:
/// the pin retries the same index and refuses instead of abstracting through
/// the definition. Its trace includes `index to include: Index.zero.succ` twice.
#[test]
fn alias_refinement_preserves_the_original_discriminant_type() {
    let family = "inductive Index where\n  | zero\n  | succ (i : Index)\ninductive Box : Index → Type where\n  | mk (i : Index) : Box (.succ i)\n";
    accepted(&format!(
        "{family}def f (x : Box (Index.succ (Index.succ Index.zero))) : Index := match x with | .mk i => i\n"
    ));
    mismatched(&format!(
        "{family}abbrev two := Index.succ (Index.succ Index.zero)\ndef f (x : Box two) : Index := match x with | .mk i => i\n"
    ));
    mismatched(&format!(
        "{family}abbrev Box2 := Box (Index.succ (Index.succ Index.zero))\ndef f (x : Box2) : Index := match x with | .mk i => i\n"
    ));
}

/// `Nat.succ n` reaches the variable `n`, which becomes a discriminant (traced: `index to
/// include: n`). `n + 1` unfolds to `Nat.succ (n.add 0)`, and the index taken from the
/// discriminant's type is `n.add 0`, already a discriminant on the retry (traced twice), so
/// the first error stands.
#[test]
fn a_refinement_path_needs_a_variable_in_the_discriminants_own_type() {
    accepted(&format!(
        "{VEC}def f (n : Nat) (xs : Vec Nat (Nat.succ n)) : Nat := match xs with | .cons k x _ => x\n"
    ));
    mismatched(&format!(
        "{VEC}def f (n : Nat) (xs : Vec Nat (n + 1)) : Nat := match xs with | .cons k x _ => x\n"
    ));
}

/// A variable index is refined; so is a literal one when the pattern's own index is a named
/// field (traced: `index to include: 3`).
#[test]
fn a_variable_on_either_side_refines() {
    accepted(&format!(
        "{VEC}def f (n : Nat) (xs : Vec Nat n) : Nat := match xs with | .nil => n | .cons k x _ => x + k + n\n"
    ));
    accepted(&format!(
        "{F}def g (n : Nat) (xs : F n) : Nat := match xs with | .nil k => k | .cons k t => k\n"
    ));
    accepted(&format!(
        "{F}def g (xs : F 3) : Nat := match xs with | .nil k => k | .cons k t => k\n"
    ));
}

/// A nested pattern is an argument, never refined: against `Vec Nat k` (`k` named) or
/// `Vec Nat 1` (after `?m := 1`) a constructor of another index is the pin's
/// `Application type mismatch`.
#[test]
fn a_nested_pattern_is_never_refined() {
    mismatched(&format!(
        "{VEC}def f (n : Nat) (xs : Vec Nat n) : Nat := match xs with | .nil => 0 | .cons k x .nil => x | .cons k x (.cons j y _) => y\n"
    ));
    mismatched(&format!(
        "{VEC}def f (xs : Vec Nat 2) : Nat := match xs with | .cons _ x (.cons j y _) => y\n"
    ));
    mismatched(&format!(
        "{VEC}def f (xs : Vec Nat 2) : Nat := match xs with | .cons k x (.cons j y _) => y\n"
    ));
}

/// Two discriminants share `n`: after the first row refines it, a named field in both
/// columns asks `j + 1 =?= k + 1` of two rigid locals, and the path found leads into `n`
/// itself, already a discriminant. One named column is fine.
#[test]
fn shared_indices_admit_one_named_column() {
    mismatched(&format!(
        "{VEC}def f (n : Nat) (xs ys : Vec Nat n) : Nat := match xs, ys with | .nil, .nil => 0 | .cons k x _, .cons j y _ => x + y\n"
    ));
    accepted(&format!(
        "{VEC}def f (n : Nat) (xs ys : Vec Nat n) : Nat := match xs, ys with | .nil, .nil => 0 | .cons k x _, .cons _ y _ => x + y\n"
    ));
    accepted(&format!(
        "{VEC}def f (n : Nat) (xs ys : Vec Nat n) : Nat := match xs, ys with | .nil, .nil => 0 | .cons _ x _, .cons j y _ => x + y\n"
    ));
    accepted(&format!(
        "{VEC}def f (n : Nat) (xs ys : Vec Nat n) : Nat := match xs, ys with | .nil, .nil => 0 | .cons _ x _, .cons _ y _ => x + y\n"
    ));
}

/// An earlier scalar column fixes the index to `Nat.succ k` with `k` rigid: a named field
/// after it asks `j + 1 =?= k + 1` of two pattern variables, and the path found leads into `n`.
#[test]
fn an_earlier_columns_pattern_fixes_the_index_rigidly() {
    mismatched(&format!(
        "{VEC}def first (n : Nat) (xs : Vec Nat n) : Nat := match n, xs with | .zero, .nil => 0 | .succ k, .cons j x tail => x\n"
    ));
    accepted(&format!(
        "{VEC}def first (n : Nat) (xs : Vec Nat n) : Nat := match n, xs with | .zero, .nil => 0 | .succ k, .cons _ x tail => x\n"
    ));
}

/// In equations a named first column is a rigid variable, which `.nil`'s index cannot meet:
/// the refinement's index is that column itself.
#[test]
fn an_equations_named_index_column_is_rigid() {
    accepted(&format!(
        "{VEC}def f : (n : Nat) → Vec Nat n → Nat\n  | _, .nil => 0\n  | _, .cons k x _ => x + k\n"
    ));
    mismatched(&format!(
        "{VEC}def f : (n : Nat) → Vec Nat n → Nat\n  | n, .nil => 0\n  | n, .cons k x _ => x + k\n"
    ));
}

/// R1: an explicit argument whose expected type is `?P a` (an implicit `{P : A → Type}` the
/// expected type was not propagated to, since the result type depends on the explicit arguments)
/// is postponed when its own type is rigid, and the placeholder that stands for it cannot meet
/// the rigid term the expected type puts there (`Witness.intro 7 true` against `… 7 true`); a
/// result type `?P 3` cannot meet `Bool` either. Each verdict is the pin's, one file per program.
#[test]
fn an_argument_the_pin_postpones_cannot_meet_the_expected_type() {
    for source in [
        "inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where\n  | intro (a : A) (value : P a) : Witness A P a value\ndef witness : Witness Nat (fun n => Bool) 7 true := Witness.intro 7 true\n",
        "inductive W (P : Nat -> Type) : (n : Nat) -> P n -> Type where\n  | mk (n : Nat) (v : P n) : W P n v\ndef w : W (fun _ => Bool) 3 true := W.mk 3 true\n",
        "inductive W (P : Nat -> Type) : (n : Nat) -> P n -> Type where\n  | mk (n : Nat) (v : P n) : W P n v\ndef w (n : Nat) : W (fun _ => Bool) n true := W.mk n true\n",
        "inductive W (P : Nat -> Type) : (n : Nat) -> P n -> Type where\n  | mk (n : Nat) (v : P n) : W P n v\ndef w (b : Bool) : W (fun _ => Bool) 3 b := W.mk 3 b\n",
        "inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where\n  | intro (a : A) (value : P a) : Witness A P a value\ndef witness : Witness Nat (fun n => Bool) 7 true := Witness.intro (7 : Nat) true\n",
        "inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where\n  | intro (a : A) (value : P a) : Witness A P a value\ndef witness : Witness Nat (fun n => Bool) 7 true := Witness.intro 7 (true : Bool)\n",
        "def g {P : Nat -> Type} (n : Nat) (v : P n) : P n := v\ndef x : (fun _ : Nat => Bool) 3 := g 3 true\n",
        "inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where\n  | intro (a : A) (value : P a) : Witness A P a value\ndef witness : Witness Nat (fun n => Bool) 7 true := by exact Witness.intro 7 true\n",
        "inductive W (P : Nat -> Type) : (n : Nat) -> P n -> Type where\n  | mk (n : Nat) (v : P n) : W P n v\ndef w : W (fun _ => Bool) 3 true := by exact W.mk 3 true\n",
    ] {
        mismatched(source);
    }
}

/// R1's accepted side: `P` given (`@`, `(P := …)`), a hole for the value, no expected type, a
/// result that does not depend on the explicit arguments (the expected type is propagated
/// first), or an earlier argument that fixes `P`.
#[test]
fn an_application_the_pin_resolves_is_accepted() {
    for source in [
        "inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where\n  | intro (a : A) (value : P a) : Witness A P a value\ndef witness : Witness Nat (fun n => Bool) 7 true := @Witness.intro Nat (fun n => Bool) 7 true\n",
        "inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where\n  | intro (a : A) (value : P a) : Witness A P a value\ndef witness : Witness Nat (fun n => Bool) 7 true := Witness.intro (P := fun n => Bool) 7 true\n",
        "inductive W (P : Nat -> Type) : (n : Nat) -> P n -> Type where\n  | mk (n : Nat) (v : P n) : W P n v\ndef w : W (fun _ => Bool) 3 true := W.mk 3 _\n",
        "inductive W (P : Nat -> Type) : (n : Nat) -> P n -> Type where\n  | mk (n : Nat) (v : P n) : W P n v\ndef w : W (fun _ => Bool) 3 true := W.mk (P := fun _ => Bool) 3 true\n",
        "inductive W (P : Nat -> Type) : (n : Nat) -> P n -> Type where\n  | mk (n : Nat) (v : P n) : W P n v\ndef w := W.mk (P := fun _ => Bool) 3 true\n",
        "inductive W (P : Nat -> Type) : (n : Nat) -> P n -> Type where\n  | mk (n : Nat) (v : P n) : W P n v\ntheorem t : W.mk (P := fun _ => Bool) 3 true = W.mk (P := fun _ => Bool) 3 true := rfl\n",
        "inductive V (P : Nat -> Type) : Type where\n  | mk (f : (n : Nat) -> P n) (n : Nat) : V P\ndef v : V (fun _ => Bool) := V.mk (fun _ => true) 3\n",
        "inductive N (P : Nat -> Type) : Type where\n  | mk (n : Nat) (v : P n) : N P\ndef x : N (fun _ => Bool) := N.mk 3 true\n",
    ] {
        accepted(source);
    }
}
