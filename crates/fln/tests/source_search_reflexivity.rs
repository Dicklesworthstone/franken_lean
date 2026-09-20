//! Search defaults construct proof terms checked by both declaration engines.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|problem| panic!("{source}\n{problem:?}"))
        .into_complete()
        .unwrap()
        .engine
}

#[test]
fn search_defaults_reduce_closed_arithmetic_and_preserve_local_scopes() {
    checked(
        &engine(),
        r#"
        theorem arithmetic : 2 + 3 = 5 := by solve_by_elim
        theorem reversed : 5 = 2 + 3 := by solve_by_elim
        theorem nested : (2 + 3) * 4 = 20 := by solve_by_elim
        theorem large : 18446744073709551616 + 1 = 18446744073709551617 := by solve_by_elim
        theorem localValue : 5 = 5 := let n := 2 + 3; show n = 5 from by solve_by_elim
        theorem beta : (fun (n : Nat) => n) (2 + 3) = 5 := by solve_by_elim
        theorem scope (p : Prop) (h : p) : 2 + 3 = 5 := by solve_by_elim
    "#,
    );
}

#[test]
fn arithmetic_defaults_solve_generated_premises_and_keep_dependent_choice_points() {
    checked(
        &engine(),
        r#"
        theorem premise (p : Prop) (rule : 2 + 3 = 5 -> p) : p := by solve_by_elim
        theorem conjunction : And (2 + 3 = 5) (3 * 4 = 12) := by
          constructor <;> solve_by_elim
        theorem alternative (p : Prop) (good : 2 + 3 = 5 -> p) (bad : 2 + 3 = 6 -> p) : p := by solve_by_elim
        theorem witness (P : Nat -> Prop) (p : Prop) (yes : P 5)
          (rule : (n : Nat) -> P n -> 2 + 3 = n -> p) : p := by
          let x : Nat := 5
          let y : Nat := 6
          solve_by_elim
        theorem rollback (p : Prop) (h : p) : And (2 + 3 = 5) p := by
          first | (constructor <;> solve_by_elim; fail) | (constructor <;> solve_by_elim)
    "#,
    );
}

#[test]
fn heterogeneous_arithmetic_uses_the_same_checked_reflexivity() {
    checked(
        &engine(),
        r#"
        theorem direct : HEq (2 + 3) 5 := by solve_by_elim
        theorem reversed : HEq 5 (2 + 3) := by solve_by_elim
        theorem premise (p : Prop) (rule : HEq (2 + 3) 5 -> p) : p := by solve_by_elim
        theorem simplify : HEq (2 + 3) 5 := by simp only []
    "#,
    );
}

#[test]
fn automatic_search_preserves_operand_transparency_and_original_goal_heads() {
    let base = checked(
        &engine(),
        r#"
        def identity (n : Nat) : Nat := n
        def arithmeticGoal : Prop := 2 + 3 = 5
        theorem headAlias : arithmeticGoal := by solve_by_elim
    "#,
    );
    for source in [
        "theorem bad : identity 5 = 5 := by solve_by_elim",
        "theorem bad : identity (2 + 3) = 5 := by solve_by_elim",
        "theorem bad (n : Nat) : identity n = n := by solve_by_elim",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
    }
    checked(&base, "theorem explicit : identity (2 + 3) = 5 := by rfl");
}

#[test]
fn false_or_incomplete_search_never_publishes_a_successful_prefix() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    for source in [
        "theorem bad : 2 + 3 = 6 := by solve_by_elim",
        "theorem bad : HEq (2 + 3) 6 := by solve_by_elim",
        "theorem bad : HEq (2 + 3) true := by solve_by_elim",
        "theorem bad (p : Prop) (rule : 2 + 3 = 6 -> p) : p := by solve_by_elim",
        "theorem bad (n : Nat) : n + 3 = 5 := by solve_by_elim",
    ] {
        let source = format!("def preceding : Nat := 7\n{source}");
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["preceding"]))
        );
    }
    checked(&base, "theorem recovered : 2 + 3 = 5 := by solve_by_elim");
}

#[test]
fn arithmetic_resource_stops_are_inconclusive_even_inside_search_alternatives() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    for source in [
        "theorem bounded : (1 <<< 18446744073709551616) = 0 := by solve_by_elim",
        "theorem bounded : HEq (1 <<< 18446744073709551616) 0 := by solve_by_elim",
        "theorem bounded (p : Prop) (rule : (1 <<< 18446744073709551616) = 0 -> p) : p := by solve_by_elim",
        "theorem bounded : (1 <<< 18446744073709551616) = 0 := by first | solve_by_elim | fail",
    ] {
        let problem = base
            .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
            .unwrap_err();
        assert_eq!(
            problem.disposition(),
            ("inconclusive", false, 3),
            "{source}: {problem:?}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
    }
    checked(&base, "theorem recovered : 2 + 3 = 5 := by solve_by_elim");
}
