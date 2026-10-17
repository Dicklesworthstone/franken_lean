//! Automatic closure uses the pin's offset conversion, not arbitrary Nat unfolding.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn base() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn accepted(source: &str) {
    let engine = base();
    let old = engine.logical_root(&KVMap::new());
    let checked = engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .expect("both native checkers must finish");
    assert_eq!(checked.theorems, 1);
    assert_eq!(engine.logical_root(&KVMap::new()), old);
}
fn refused(source: &str) {
    let engine = base();
    let old = engine.logical_root(&KVMap::new());
    let error = engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_err();
    assert_eq!(error.disposition().2, 1, "{source}\n{error:?}");
    assert_eq!(engine.logical_root(&KVMap::new()), old);
}
#[test]
fn reducible_offset_bases_close_in_both_orientations() {
    for declaration in ["abbrev two : Nat := 2", "@[reducible] def two : Nat := 2"] {
        for equation in ["two + 3 = 5", "5 = two + 3", "Nat.succ two = 3"] {
            accepted(&format!(
                "{declaration}\ntheorem t : {equation} := by simp only []\n"
            ));
        }
    }
}
#[test]
fn reducible_function_heads_expose_offsets_with_literal_subcomputations() {
    for (declaration, equation) in [
        ("abbrev f (n : Nat) : Nat := n + 1", "f 2 = 3"),
        (
            "@[reducible] def h (a b : Nat) : Nat := a * b + 1",
            "h 3 4 = 13",
        ),
        ("abbrev k : Nat → Nat := fun n => n + 1", "k 2 = 3"),
    ] {
        accepted(&format!(
            "{declaration}\ntheorem t : {equation} := by simp only []\n"
        ));
    }
}
#[test]
fn multiplication_does_not_unfold_its_reducible_operands() {
    for equation in ["two * two = 4", "two * 3 = 6"] {
        refused(&format!(
            "abbrev two : Nat := 2\ntheorem t : {equation} := by simp only []\n"
        ));
    }
}
#[test]
fn ordinary_definitions_stay_closed_below_reducible_heads() {
    for source in [
        "def two : Nat := 2\ntheorem t : two + 3 = 5 := by simp only []",
        "def f (n : Nat) : Nat := n + 1\nabbrev g (n : Nat) : Nat := f n\ntheorem t : g 2 = 3 := by simp only []",
    ] {
        refused(source);
    }
}
#[test]
fn offsets_cancel_without_discarding_the_symbolic_base() {
    for equation in ["n + 3 = Nat.succ (n + 2)", "n + 2 + 3 = n + 5"] {
        accepted(&format!(
            "theorem t (n : Nat) : {equation} := by simp only []\n"
        ));
    }
    refused("theorem t (n m : Nat) : n + 3 = m + 3 := by simp only []");
}

#[test]
fn arithmetic_offsets_preserve_wrong_result_refusal_and_recovery() {
    let base = base();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for result in [4, 6] {
        let source =
            format!("abbrev two : Nat := 2\ntheorem wrong : two + 3 = {result} := by simp only []");
        let error = base
            .check_source_files(&[source.as_bytes()], &options, limits())
            .unwrap_err();
        assert_eq!(error.disposition().2, 1, "{error:?}");
        assert_eq!(base.logical_root(&options), root);
    }
    let correct = "abbrev two : Nat := 2\ntheorem correct : two + 3 = 5 := by simp only []";
    base.check_source_files(&[correct.as_bytes()], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn offsets_do_not_change_heterogeneous_or_multiplication_completion() {
    for equation in ["HEq (two + 3) 5", "(two * 3) + 1 = 7"] {
        refused(&format!(
            "abbrev two : Nat := 2\ntheorem t : {equation} := by simp only []\n"
        ));
    }
}
