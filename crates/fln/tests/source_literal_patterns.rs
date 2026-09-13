//! Literal decisions preserve ordered rows and kernel typing obligations.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(source: &str) {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
}
fn reject(source: &str) {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let result = engine.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    assert!(
        result.is_err(),
        "invalid literal pattern accepted: {source}"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}
#[test]
fn natural_equations_have_exact_ordered_matches_and_a_real_fallback() {
    check(
        "def digit : Nat -> Nat | 0 => 7 | 1 => 9 | n => n + 10\n\
        theorem zero : digit 0 = 7 := by rfl\n\
        theorem one : digit 1 = 9 := by rfl\n\
        theorem other : digit 12 = 22 := by rfl",
    );
}
#[test]
fn arbitrary_precision_literals_are_not_unary_patterns() {
    check(
        "def large : Nat -> Nat | 340282366920938463463374607431768211456 => 17 | _ => 19\n\
        theorem yes : large 340282366920938463463374607431768211456 = 17 := by rfl\n\
        theorem no : large 340282366920938463463374607431768211457 = 19 := by rfl",
    );
}
#[test]
fn different_literal_spellings_are_compared_by_value() {
    check("def value : Nat -> Nat | 0x10 => 7 | _ => 9\n theorem same : value 16 = 7 := by rfl");
    for duplicate in ["0x10", "0b10000", "0o20", "1_6"] {
        reject(&format!(
            "def duplicate : Nat -> Nat | 16 => 1 | {duplicate} => 2 | _ => 3"
        ));
    }
}
#[test]
fn string_patterns_do_not_invent_an_unchecked_comparison_rule() {
    for source in [
        r#"def code : String -> Nat | "a\nb" => 7 | _ => 9"#,
        r##"def code : String -> Nat | r#"🦀"# => 9 | _ => 11"##,
    ] {
        reject(source);
    }
}
#[test]
fn mixed_literal_columns_retain_first_row_priority_and_bindings() {
    check(
        "def code : Nat -> Bool -> Nat | 1, true => 7 | _, true => 9 | 1, false => 11 | n, false => n\n\
        theorem first : code 1 true = 7 := by rfl\n\
        theorem second : code 3 true = 9 := by rfl\n\
        theorem third : code 1 false = 11 := by rfl\n\
        theorem last : code 12 false = 12 := by rfl",
    );
}
#[test]
fn literals_inside_constructor_payloads_use_the_same_matrix() {
    check(
        "inductive Maybe (A : Type) where | none | some (value : A)\n\
        def code : Maybe Nat -> Nat | .none => 0 | .some 7 => 1 | .some x => x\n\
        theorem selected : code (Maybe.some 7) = 1 := by rfl\n\
        theorem fallback : code (Maybe.some 9) = 9 := by rfl",
    );
}
#[test]
fn literal_and_constructor_overlap_preserves_order_without_large_expansion() {
    check(
        "def code : Nat -> Nat | 0 => 7 | .succ 340282366920938463463374607431768211456 => 9 | .succ k => k\n\
        theorem zero : code 0 = 7 := by rfl\n\
        theorem huge : code 340282366920938463463374607431768211457 = 9 := by rfl\n\
        theorem other : code 20 = 19 := by rfl",
    );
}
#[test]
fn literal_zero_keeps_the_structural_predecessor_available_for_recursion() {
    check(
        "def copy : Nat -> Nat | 0 => 0 | .succ k => Nat.succ (copy k)\n\
        theorem computed : copy 7 = 7 := by rfl\n\
        def withFlag : Bool -> Nat -> Nat | _, 0 => 0 | b, .succ k => Nat.succ (withFlag b k)\n\
        theorem later : withFlag false 4 = 4 := by rfl",
    );
}
#[test]
fn literal_pattern_functions_are_checked_higher_order_arguments() {
    check(
        "def apply (f : Nat -> Nat) (n : Nat) : Nat := f n\n\
        theorem used : apply (fun | 7 => 11 | _ => 13) 7 = 11 := by rfl",
    );
}
#[test]
fn finite_literal_rows_do_not_prove_coverage_even_for_a_closed_input() {
    for source in [
        "def bad : Nat := match 0 with | 0 => 7",
        "def bad : String -> Nat | \"a\" => 0 | \"b\" => 1",
    ] {
        reject(source);
    }
}
#[test]
fn wrong_literal_domains_and_foreign_constructor_patterns_are_not_erased() {
    for source in [
        "def bad : Bool -> Nat | 0 => 1 | _ => 2",
        "def bad : Nat -> Nat | \"a\" => 1 | _ => 2",
        "def bad : Nat -> Nat | 0 => 1 | \"a\" => 2 | _ => 3",
        "inductive Other where | zero | succ (n : Nat)\ndef bad : Other -> Nat | 0 => 1 | Other.succ k => k",
    ] {
        reject(source);
    }
}
#[test]
fn unused_discriminants_annotations_and_shadowed_intrinsic_names_stay_checked() {
    reject("def bad : Nat := match (1 : String) with | 0 => 0 | _ => 1");
    reject("def bad : Nat -> Nat | 0 => 7 | _ => let invalid := (1 : String); 9");
    reject("def bad : Nat -> Nat | _ => 7 | 0 => (1 : String)");
    check(
        "def good (beq : Nat) : Nat := match 7 with | 7 => beq | _ => 0\n theorem same : good 9 = 9 := by rfl",
    );
}
#[test]
fn boolean_comparisons_do_not_fabricate_dependent_equalities() {
    reject("theorem bad (n : Nat) : n = 0 := match n with | 0 => rfl | _ => rfl");
    check("def retain (n : Nat) (h : n = n) : n = n := match n with | 0 => h | _ => h");
}
#[test]
fn recursive_calls_hidden_in_literal_alternatives_remain_termination_obligations() {
    reject("def bad : Nat -> Nat | 0 => 0 | n => bad n");
    reject("def bad : Nat -> Nat | 0 => let unused := bad 0; 0 | .succ k => bad k");
}
