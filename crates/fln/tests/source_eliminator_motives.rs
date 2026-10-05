//! Recursor applications with an implicit motive use the pin's eliminator
//! elaboration (`elabAsElim`), bead `fln-recursor-motive-elab-as-elim-3jsg`.
//!
//! Every verdict below is the pinned Reference's (`lean` v4.32.0, commit
//! `8c9756b2`), measured on the same program on 2026-10-05. A `def` here stands
//! for the pin's `noncomputable def`: the pin's code generator does not support
//! `Chain.rec`, and FrankenLean's source check does not compile, so the
//! elaboration question is the same. FrankenLean's frontend has no
//! `noncomputable` modifier.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

const CHAIN: &str = "inductive Chain where | nil | cons (head : Nat) (tail : Chain)\n";

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn accepted(source: &str) {
    let result = engine().check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    assert!(
        matches!(result, Ok(fln::Outcome::Complete(_))),
        "the pin accepts this, FrankenLean must too:\n{source}\n{:?}",
        result.err()
    );
}

fn refused(source: &str) -> String {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    let error = e
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .err()
        .unwrap_or_else(|| panic!("the pin refuses this, FrankenLean must too:\n{source}"));
    assert_eq!(e.logical_root(&KVMap::new()), root);
    error.to_string()
}

/// The bead's table: each row with an implicit motive agrees with the pin.
#[test]
fn an_implicit_recursor_motive_is_computed_from_the_expected_type() {
    let term = "Chain.rec 0 (fun n tail ih => ih + 1) (Chain.cons 2 Chain.nil)";
    for source in [
        // `binrel%` elaborates the left side without an expected type: the
        // eliminator waits until the numeral defaults to `Nat`.
        format!("{CHAIN}theorem count : {term} = 1 := by rfl"),
        format!(
            "{CHAIN}theorem count : Chain.rec 0 (fun n tail ih => Nat.succ ih) (Chain.cons 2 Chain.nil) = 1 := by rfl"
        ),
        // The expected type is known at once.
        format!("{CHAIN}def count : Nat := {term}\ntheorem count_ok : count = 1 := by rfl"),
        "theorem count : Nat.rec 0 (fun n ih => ih + 1) 3 = 3 := by rfl".to_owned(),
        // A supplied motive keeps the ordinary elaborator.
        format!(
            "{CHAIN}theorem count : @Chain.rec (fun _ => Nat) 0 (fun n tail ih => ih + 1) (Chain.cons 2 Chain.nil) = 1 := by rfl"
        ),
        format!(
            "{CHAIN}theorem count : Chain.rec (motive := fun _ => Nat) 0 (fun n tail ih => ih + 1) (Chain.cons 2 Chain.nil) = 1 := by rfl"
        ),
    ] {
        accepted(&source);
    }
    // The motive is right, so a false computation is a kernel rejection.
    let wrong = refused(&format!("{CHAIN}theorem count : {term} = 2 := by rfl"));
    assert!(wrong.contains("kernel"), "{wrong}");
}

/// `mkMotive` abstracts the major premise (and the indices) out of the
/// expected type; `finalize` specializes it when the eliminator is
/// under-applied and generalizes extra arguments when it is over-applied.
#[test]
fn the_motive_abstracts_majors_and_follows_under_and_over_application() {
    for source in [
        format!("{CHAIN}theorem self_eq (c : Chain) : c = c := Chain.rec rfl (fun _ _ _ => rfl) c"),
        "theorem symm2 {a b : Nat} (h : a = b) : b = a := Eq.rec rfl h".to_owned(),
        format!("{CHAIN}def len : Chain -> Nat := Chain.rec 0 (fun _ _ ih => ih + 1)\ntheorem len_ok : len (Chain.cons 1 (Chain.cons 2 Chain.nil)) = 2 := by rfl"),
        "def add2 (n m : Nat) : Nat := Nat.rec (fun m => m) (fun _ ih m => Nat.succ (ih m)) n m\ntheorem add2_ok : add2 2 3 = 5 := by rfl".to_owned(),
        // An explicit motive written `_` is still computed (`False.rec`).
        "theorem absurd2 (h : False) : 1 = 2 := False.rec _ h".to_owned(),
        "theorem nested : Nat.rec 0 (fun n ih => Nat.rec ih (fun _ ih2 => ih2 + 1) n) 3 = 3 := by rfl".to_owned(),
    ] {
        accepted(&source);
    }
    // The minor premises are checked against the computed motive.
    refused(&format!(
        "{CHAIN}def bad : Nat := Chain.rec true (fun _ _ ih => ih) Chain.nil"
    ));
}

/// The pin's refusal when no expected type ever becomes available.
#[test]
fn an_eliminator_without_an_expected_type_is_refused_as_the_pin_refuses_it() {
    let message = refused(&format!(
        "{CHAIN}example := Chain.rec 0 (fun n tail ih => ih + 1) (Chain.cons 2 Chain.nil)"
    ));
    assert!(
        message.contains("failed to elaborate eliminator, expected type is not available"),
        "{message}"
    );
}
