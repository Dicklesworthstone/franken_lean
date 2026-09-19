//! Notation remains ordinary typed constructor applications and checked matches.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};

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
fn inferred_and_expected_collection_types_reach_checked_constructors() {
    let checked = check(
        r#"
        def empty : List Nat := []
        def three := [1, 2, 3,]
        def nested : List (List Nat) := [[], [1], [2, 3]]
        def prepend {A : Type} (a : A) (xs : List A) : List A := a :: xs
        theorem empty_ok : empty = List.nil := by rfl
        theorem three_ok : three = List.cons 1 (List.cons 2 (List.cons 3 List.nil)) := by rfl
        theorem head_ok : List.head? three = Option.some 1 := by rfl
        theorem tail_ok : List.tail three = [2, 3] := by rfl
        theorem nested_ok : List.length nested = 3 := by rfl
        theorem prepend_ok : prepend true [false] = [true, false] := by rfl
    "#,
    );
    assert_eq!(checked.theorems, 6);
}

#[test]
fn list_operations_compose_with_literals_lambdas_and_polymorphism() {
    check(
        r#"
        def singleton.{u} {A : Type u} (a : A) : List A := [a]
        theorem map_ok : List.map (fun n => n + 1) [1, 2, 3] = [2, 3, 4] := by rfl
        theorem append_ok : List.append [1, 2] [3] = [1, 2, 3] := by rfl
        theorem reverse_ok : List.reverse [1, 2, 3] = [3, 2, 1] := by rfl
        theorem fold_ok : List.foldl (fun n x => n * 10 + x) 0 [1, 2, 3] = 123 := by rfl
        theorem singleton_ok : singleton Nat = [Nat] := by rfl
        theorem nil_ok : (fun (xs : List Nat) => xs) [] = ([] : List Nat) := by rfl
    "#,
    );
}

#[test]
fn notation_is_not_captured_by_namespace_lookalikes() {
    check(
        r#"
        namespace Shadow
        def List.nil : Nat := 91
        def List.cons (x y : Nat) : Nat := 92
        def actual : _root_.List Nat := [1, 2]
        theorem actual_ok : actual = _root_.List.cons 1 (_root_.List.cons 2 _root_.List.nil) := by rfl
        end Shadow
    "#,
    );
}

#[test]
fn invalid_elements_and_false_equalities_do_not_publish_partial_results() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def invalid : List Nat := [true]",
        "def invalid : List Nat := [1, true, 3]",
        "def invalid : List Nat := [1] :: []",
        "def invalid : Nat := []",
        "def invalid : List Nat := 1 :: true",
        "def first : List Nat := [1]\ntheorem invalid : first = [2] := by rfl",
        "theorem invalid : ([1, 2] : List Nat) = [2, 1] := by rfl",
    ] {
        let outcome = base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        );
        assert!(!matches!(outcome, Ok(Outcome::Complete(_))), "{source}");
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["invalid"]))
        );
    }
    let recovered = base
        .check_source_files(
            &[b"def valid : List Nat := [1, 2]\ntheorem good : List.length valid = 2 := by rfl"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(recovered.theorems, 1);
}
