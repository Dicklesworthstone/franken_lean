//! Collection patterns use ordinary constructor coverage, recursion and admission.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(source: &str) -> fln::SourceFileCheck {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("ordinary source council must complete")
}

#[test]
fn literal_and_cons_patterns_select_the_correct_ordered_branch() {
    check(
        r#"
        def classify (xs : List Nat) : Nat := match xs with
          | [] => 0
          | [x] => x
          | x :: y :: rest => x + y
        theorem none : classify [] = 0 := by rfl
        theorem one : classify [17] = 17 := by rfl
        theorem two : classify [2, 3] = 5 := by rfl
        theorem longer : classify [2, 3, 99] = 5 := by rfl
        def first : List Nat -> Nat := fun | [] => 0 | x :: _ => x
        theorem first_ok : first [7, 8] = 7 := by rfl
        def keepTwo : List Nat -> List Nat
          | [] => []
          | [x] => [x]
          | x :: y :: _ => [x, y]
        theorem keep_ok : keepTwo [1, 2, 3] = [1, 2] := by rfl
    "#,
    );
}

#[test]
fn patterns_nest_across_lists_options_and_multiple_discriminants() {
    check(
        r#"
        def nested (xs : List (List Nat)) : Nat := match xs with
          | [[], [x]] => x
          | _ => 0
        theorem nested_yes : nested [[], [9]] = 9 := by rfl
        theorem nested_no : nested [[1], [9]] = 0 := by rfl
        def unwrap (xs : Option (List Nat)) : Nat := match xs with
          | Option.some [x] => x
          | _ => 0
        theorem wrapped_yes : unwrap (Option.some [11]) = 11 := by rfl
        theorem wrapped_no : unwrap (Option.some [11, 12]) = 0 := by rfl
        theorem absent : unwrap Option.none = 0 := by rfl
        def combine (xs ys : List Nat) : Nat := match xs, ys with
          | x :: _, [y] => x + y
          | _, _ => 0
        theorem combined : combine [2, 3] [5] = 7 := by rfl
        theorem unmatched : combine [2] [5, 6] = 0 := by rfl
    "#,
    );
}

#[test]
fn structurally_recursive_collection_functions_keep_the_original_recursion_root() {
    check(
        r#"
        def sum (xs : List Nat) : Nat := match xs with
          | [] => 0
          | x :: rest => x + sum rest
        theorem total : sum [1, 2, 3, 4] = 10 := by rfl
        def copy.{u} {A : Type u} (xs : List A) : List A := match xs with
          | [] => []
          | x :: rest => x :: copy rest
        theorem copied : copy [true, false] = [true, false] := by rfl
        theorem copied_type : copy [Nat] = [Nat] := by rfl
    "#,
    );
}

#[test]
fn pattern_constructors_ignore_namespace_lookalikes() {
    check(
        r#"
        namespace Shadow
        def List.nil : Nat := 91
        def List.cons (x y : Nat) : Nat := 92
        def first (xs : _root_.List Nat) : Nat := match xs with
          | [] => 0
          | x :: _ => x
        theorem yes : first [7] = 7 := by rfl
        theorem no : first [] = 0 := by rfl
        end Shadow
    "#,
    );
}

#[test]
fn incomplete_matches_bad_recursion_and_redundant_bad_rows_do_not_publish() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad (xs : List Nat) : Nat := match xs with | [x] => x",
        "def bad (xs : List Nat) : Nat := match xs with | _ => 0 | [x] => true",
        "def bad (xs : List Nat) : Nat := match xs with | [] => 0 | x :: rest => bad xs",
        "def bad (xs : List Nat) : Nat := match xs with | [] => 0 | x :: x => x",
        "def bad (x : Nat) : Nat := match x with | [] => 0 | h :: t => h",
        "def first (xs : List Nat) : Nat := match xs with | [] => 0 | x :: _ => x\ntheorem bad : first [1] = 2 := by rfl",
    ] {
        let outcome = base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        );
        assert!(!matches!(outcome, Ok(Outcome::Complete(_))), "{source}");
        assert_eq!(base.logical_root(&KVMap::new()), root, "{source}");
    }
    let recovered = base.check_source_files(
        &[b"def first (xs : List Nat) : Nat := match xs with | [] => 0 | x :: _ => x\ntheorem good : first [7] = 7 := by rfl"],
        &KVMap::new(), SourceCheckLimits::new(limits()),
    ).unwrap().into_complete().unwrap();
    assert_eq!(recovered.theorems, 1);
}
