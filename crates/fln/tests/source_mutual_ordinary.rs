//! Ordinary mutual blocks must publish a complete, dependency-ordered safe batch.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn engine() -> (Engine, EngineAdmissionLimits) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    (
        Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap(),
        limits,
    )
}
fn check(source: &str) -> Engine {
    oracle(source, true);
    let (engine, limits) = engine();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("both checkers complete")
        .engine
}

fn below_engine() -> (Engine, EngineAdmissionLimits) {
    // User inductives generate below/brecOn when the seed has the product type
    // needed by their dictionaries. Reference already provides this declaration.
    let (base, limits) = engine();
    let base = base
        .check_source_files(
            &[b"structure Prod (A : Type u) (B : Type v) where\n fst : A\n snd : B\n"],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    (base, limits)
}

fn check_below(source: &str) -> Engine {
    oracle(source, true);
    let (base, limits) = below_engine();
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("both checkers complete")
    .engine
}

const MUTUAL_VEC: &str = r#"
inductive MutualVec (A : Type u) : Nat -> Type u where
 | nil : MutualVec A 0
 | cons (n : Nat) : A -> MutualVec A n -> MutualVec A (Nat.succ n)
"#;

#[test]
fn mutual_structural_generalizes_implicit_indices_and_dependent_results() {
    let source = format!(
        "{MUTUAL_VEC}\n{}",
        r#"
mutual
 def vecLeft.{u} {A : Type u} {n : Nat} (xs : MutualVec A n) : Nat := match xs with
  | .nil => 0
  | .cons _ _ tail => vecRight tail + 1
 def vecRight.{u} {A : Type u} {n : Nat} (xs : MutualVec A n) : Nat := match xs with
  | .nil => 0
  | .cons _ _ tail => vecLeft tail + 2
end
mutual
 def vecCopyLeft.{u} {A : Type u} {n : Nat} (xs : MutualVec A n) : MutualVec A n := match xs with
  | .nil => .nil
  | .cons k a tail => .cons k a (vecCopyRight tail)
 def vecCopyRight.{u} {A : Type u} {n : Nat} (xs : MutualVec A n) : MutualVec A n := match xs with
  | .nil => .nil
  | .cons k a tail => .cons k a (vecCopyLeft tail)
end
example : vecLeft (.cons 2 11 (.cons 1 22 (.cons 0 33 .nil))) = 4 := rfl
example : vecRight (.cons 2 11 (.cons 1 22 (.cons 0 33 .nil))) = 5 := rfl
example : vecCopyLeft (.cons 1 11 (.cons 0 22 .nil)) = MutualVec.cons 1 11 (MutualVec.cons 0 22 MutualVec.nil) := rfl
example : vecCopyRight (.cons 1 11 (.cons 0 22 .nil)) = MutualVec.cons 1 11 (MutualVec.cons 0 22 MutualVec.nil) := rfl
example (A : Type u) (n : Nat) (a : A) (tail : MutualVec A n) :
 vecLeft (.cons n a tail) = vecRight tail + 1 := rfl
example (A : Type u) (n : Nat) (a : A) (tail : MutualVec A n) :
 vecCopyLeft (.cons n a tail) = MutualVec.cons n a (vecCopyRight tail) := rfl
"#
    );
    let base = check_below(&source);
    run(
        &base,
        "#eval vecLeft (.cons 2 11 (.cons 1 22 (.cons 0 33 .nil)))",
        "4",
    );
    run(
        &base,
        "#eval vecRight (.cons 2 11 (.cons 1 22 (.cons 0 33 .nil)))",
        "5",
    );
    run(
        &base,
        "#eval vecLeft (vecCopyLeft (.cons 2 11 (.cons 1 22 (.cons 0 33 .nil))))",
        "4",
    );
    run(
        &base,
        "#eval vecRight (vecCopyRight (.cons 2 11 (.cons 1 22 (.cons 0 33 .nil))))",
        "5",
    );
}

#[test]
fn mutual_structural_generalizes_varying_accumulator_before_major() {
    for hint in ["", "\n termination_by structural n"] {
        let source = format!(
            r#"
mutual
 def beforeLeft (acc n : Nat) : Nat := match n with
  | 0 => acc
  | k+1 => beforeRight (acc+1) k{hint}
 def beforeRight (acc n : Nat) : Nat := match n with
  | 0 => acc
  | k+1 => beforeLeft (acc+2) k{hint}
end
example : beforeLeft 10 3 = 14 := rfl
example : beforeRight 10 3 = 15 := rfl
example (acc n : Nat) : beforeLeft acc (n+1) = beforeRight (acc+1) n := rfl
example (acc n : Nat) : beforeRight acc (n+1) = beforeLeft (acc+2) n := rfl
"#
        );
        let base = check(&source);
        run(&base, "#eval beforeLeft 10 3", "14");
        run(&base, "#eval beforeRight 10 3", "15");
    }
}

#[test]
fn mutual_structural_generalizes_higher_order_arguments_with_mixed_binder_styles() {
    let base = check(
        r#"
mutual
 def functionLeft {f : Nat -> Nat} (n : Nat) : Nat := match n with
  | 0 => f 0
  | k+1 => functionRight (fun x => f (x+1)) k
 def functionRight (f : Nat -> Nat) (n : Nat) : Nat := match n with
  | 0 => f 0
  | k+1 => functionLeft (f := fun x => f (x+2)) k
end
example : functionLeft (f := fun x => x+10) 3 = 14 := rfl
example : functionRight (fun x => x+10) 3 = 15 := rfl
example (f : Nat -> Nat) (n : Nat) :
 functionLeft (f := f) (n+1) = functionRight (fun x => f (x+1)) n := rfl
"#,
    );
    run(&base, "#eval functionLeft (f := fun x => x+10) 3", "14");
    run(&base, "#eval functionRight (fun x => x+10) 3", "15");
}

#[test]
fn mutual_structural_generalizes_dependent_arguments_between_reordered_indices() {
    let base = check_below(
        r#"
inductive GeneralizedGrid : Nat -> Nat -> Type where
 | empty : GeneralizedGrid 0 0
 | row (rows cols : Nat) : GeneralizedGrid rows cols -> GeneralizedGrid (rows+1) cols
 | col (rows cols : Nat) : GeneralizedGrid rows cols -> GeneralizedGrid rows (cols+1)
mutual
 def gridBeforeLeft (cols seed : Nat) (_h : seed = seed) (rows : Nat) (grid : GeneralizedGrid rows cols) : Nat := match grid with
  | .empty => seed
  | .row r c tail => gridBeforeRight c (seed+1) rfl r tail
  | .col r c tail => gridBeforeRight c (seed+1) rfl r tail
 termination_by structural grid
 def gridBeforeRight (cols seed : Nat) (_h : seed = seed) (rows : Nat) (grid : GeneralizedGrid rows cols) : Nat := match grid with
  | .empty => seed
  | .row r c tail => gridBeforeLeft c (seed+2) rfl r tail
  | .col r c tail => gridBeforeLeft c (seed+2) rfl r tail
 termination_by structural grid
end
example : gridBeforeLeft 1 10 rfl 2 (.row 1 1 (.col 1 0 (.row 0 0 .empty))) = 14 := rfl
example : gridBeforeRight 1 10 rfl 2 (.row 1 1 (.col 1 0 (.row 0 0 .empty))) = 15 := rfl
example (r c seed : Nat) (tail : GeneralizedGrid r c) :
 gridBeforeLeft c seed rfl (r+1) (.row r c tail) = gridBeforeRight c (seed+1) rfl r tail := rfl
"#,
    );
    run(
        &base,
        "#eval gridBeforeLeft 1 10 rfl 2 (.row 1 1 (.col 1 0 (.row 0 0 .empty)))",
        "14",
    );
    run(
        &base,
        "#eval gridBeforeRight 1 10 rfl 2 (.row 1 1 (.col 1 0 (.row 0 0 .empty)))",
        "15",
    );
}

#[test]
fn mutual_structural_generalizes_index_dependent_proofs_and_preserves_results() {
    let source = format!(
        "{MUTUAL_VEC}\n{}",
        r#"
mutual
 def copyBeforeLeft.{u} {A : Type u} (n : Nat) (h : n = n) (xs : MutualVec A n) : MutualVec A n := match xs with
  | .nil => .nil
  | .cons k a tail => .cons k a (copyBeforeRight k rfl tail)
 termination_by structural xs
 def copyBeforeRight.{u} {A : Type u} (n : Nat) (h : n = n) (xs : MutualVec A n) : MutualVec A n := match xs with
  | .nil => .nil
  | .cons k a tail => .cons k a (copyBeforeLeft k rfl tail)
 termination_by structural xs
end
example : copyBeforeLeft 2 rfl (.cons 1 11 (.cons 0 22 .nil)) = MutualVec.cons 1 11 (MutualVec.cons 0 22 MutualVec.nil) := rfl
example : copyBeforeRight 2 rfl (.cons 1 11 (.cons 0 22 .nil)) = MutualVec.cons 1 11 (MutualVec.cons 0 22 MutualVec.nil) := rfl
example (A : Type u) (n : Nat) (a : A) (tail : MutualVec A n) :
 copyBeforeLeft (n+1) rfl (.cons n a tail) = MutualVec.cons n a (copyBeforeRight n rfl tail) := rfl
"#
    );
    check_below(&source);
}

#[test]
fn mutual_structural_generalized_arguments_preserve_termination_and_typing() {
    let (base, limits) = engine();
    let root = base.logical_root(&KVMap::new());
    for body in [
        "badRight (acc+1) (k+1)",
        "let unused := badRight (acc+1) (k+1); badRight (acc+1) k",
        "let invalid : Bool := acc; badRight (acc+1) k",
        "badRight true k",
    ] {
        let source = format!(
            r#"
mutual
 def badLeft (acc n : Nat) : Nat := match n with
  | 0 => acc
  | k+1 => {body}
 termination_by structural n
 def badRight (acc n : Nat) : Nat := match n with
  | 0 => acc
  | k+1 => badLeft (acc+2) k
 termination_by structural n
end
"#
        );
        oracle(&source, false);
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .is_err(),
            "invalid generalized component must not be admitted: {source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        for label in ["badLeft", "badRight", "badLeft._mutual"] {
            assert!(!base.environment().contains(&name(label)));
        }
    }
}

#[test]
fn mutual_structural_hint_selects_indexed_major_and_generalizes_accumulator() {
    let source = format!(
        "{MUTUAL_VEC}\n{}",
        r#"
mutual
 def accLeft.{u} {A : Type u} (n : Nat) (xs : MutualVec A n) (seed : Nat) : Nat := match xs with
  | .nil => seed
  | .cons k _ tail => accRight k tail (seed + 1)
 termination_by structural xs
 def accRight.{u} {A : Type u} (n : Nat) (xs : MutualVec A n) (seed : Nat) : Nat := match xs with
  | .nil => seed
  | .cons k _ tail => accLeft k tail (seed + 2)
 termination_by structural xs
end
example : accLeft 3 (.cons 2 11 (.cons 1 22 (.cons 0 33 .nil))) 10 = 14 := rfl
example : accRight 3 (.cons 2 11 (.cons 1 22 (.cons 0 33 .nil))) 10 = 15 := rfl
example (A : Type u) (n : Nat) (a : A) (tail : MutualVec A n) (seed : Nat) :
 accLeft (n+1) (.cons n a tail) seed = accRight n tail (seed+1) := rfl
"#
    );
    let base = check_below(&source);
    run(
        &base,
        "#eval accLeft 3 (.cons 2 11 (.cons 1 22 (.cons 0 33 .nil))) 10",
        "14",
    );
    run(
        &base,
        "#eval accRight 3 (.cons 2 11 (.cons 1 22 (.cons 0 33 .nil))) 10",
        "15",
    );
}

#[test]
fn mutual_structural_uses_family_order_for_independently_varying_indices() {
    let base = check_below(
        r#"
inductive MutualGrid : Nat -> Nat -> Type where
 | empty : MutualGrid 0 0
 | row (rows cols : Nat) : MutualGrid rows cols -> MutualGrid (rows+1) cols
 | col (rows cols : Nat) : MutualGrid rows cols -> MutualGrid rows (cols+1)
mutual
 def gridLeft (cols rows : Nat) (grid : MutualGrid rows cols) : Nat := match grid with
  | .empty => 0
  | .row r c tail => gridRight c r tail + 1
  | .col r c tail => gridRight c r tail + 1
 termination_by structural grid
 def gridRight (cols rows : Nat) (grid : MutualGrid rows cols) : Nat := match grid with
  | .empty => 0
  | .row r c tail => gridLeft c r tail + 2
  | .col r c tail => gridLeft c r tail + 2
 termination_by structural grid
end
example : gridLeft 1 2 (.row 1 1 (.col 1 0 (.row 0 0 .empty))) = 4 := rfl
example : gridRight 1 2 (.row 1 1 (.col 1 0 (.row 0 0 .empty))) = 5 := rfl
example (r c : Nat) (tail : MutualGrid r c) :
 gridLeft c (r+1) (.row r c tail) = gridRight c r tail + 1 := rfl
example (r c : Nat) (tail : MutualGrid r c) :
 gridRight (c+1) r (.col r c tail) = gridLeft c r tail + 2 := rfl
"#,
    );
    run(
        &base,
        "#eval gridLeft 1 2 (.row 1 1 (.col 1 0 (.row 0 0 .empty)))",
        "4",
    );
    run(
        &base,
        "#eval gridRight 1 2 (.row 1 1 (.col 1 0 (.row 0 0 .empty)))",
        "5",
    );
}

#[test]
fn mutual_structural_indexed_calls_preserve_termination_and_typing_obligations() {
    let (base, limits) = below_engine();
    let root = base.logical_root(&KVMap::new());
    for body in [
        r#"
mutual
 def badLeft.{u} {A : Type u} {n : Nat} (xs : MutualVec A n) : Nat := badRight xs
 termination_by structural xs
 def badRight.{u} {A : Type u} {n : Nat} (xs : MutualVec A n) : Nat := badLeft xs
 termination_by structural xs
end
"#,
        r#"
mutual
 def badLeft.{u} {A : Type u} {n : Nat} (xs : MutualVec A n) : Nat := match xs with
  | .nil => 0
  | .cons k a tail => let unused := badRight (.cons k a tail); badRight tail
 termination_by structural xs
 def badRight.{u} {A : Type u} {n : Nat} (xs : MutualVec A n) : Nat := match xs with
  | .nil => 0
  | .cons _ _ tail => badLeft tail
 termination_by structural xs
end
"#,
        r#"
mutual
 def badLeft.{u} {A : Type u} {n : Nat} (xs : MutualVec A n) : Nat := match xs with
  | .nil => 0
  | .cons k _ tail => let invalid : Bool := k; badRight tail
 termination_by structural xs
 def badRight.{u} {A : Type u} {n : Nat} (xs : MutualVec A n) : Nat := match xs with
  | .nil => 0
  | .cons _ _ tail => badLeft tail
 termination_by structural xs
end
"#,
        r#"
mutual
 def badLeft.{u} {A : Type u} (n : Nat) (xs : MutualVec A n) : Nat := match xs with
  | .nil => 0
  | .cons k a tail => badRight k (.cons k a tail)
 termination_by structural xs
 def badRight.{u} {A : Type u} (n : Nat) (xs : MutualVec A n) : Nat := match xs with
  | .nil => 0
  | .cons k _ tail => badLeft k tail
 termination_by structural xs
end
"#,
    ] {
        let source = format!("{MUTUAL_VEC}\n{body}");
        oracle(&source, false);
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .is_err(),
            "invalid indexed component must not be admitted: {source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        for label in ["MutualVec", "badLeft", "badRight", "badLeft._mutual"] {
            assert!(!base.environment().contains(&name(label)));
        }
    }
}

#[test]
fn forward_definitions_reduce_after_dependency_ordered_admission() {
    check(
        "mutual\n def first : Nat := second + 1\n def second : Nat := 41\nend\nexample : first = 42 := rfl\n",
    );
}

#[test]
fn mutual_structural_members_reduce_and_execute_their_own_components() {
    use fln_env::constants::{ConstantInfo, DefinitionSafety};
    let base = check(
        "mutual\n\
         def countLeft : Nat -> Nat\n | 0 => 7\n | n+1 => countRight n + 1\n\
         def countRight : Nat -> Nat\n | 0 => 13\n | n+1 => countLeft n + 2\n\
         end\n\
         example : countLeft 4 = 13 := rfl\n\
         example : countRight 4 = 19 := rfl\n\
         example (n : Nat) : countLeft (n+1) = countRight n + 1 := rfl\n",
    );
    for label in ["countLeft", "countRight"] {
        let Some(ConstantInfo::Defn(definition)) = base.environment().find(&name(label)) else {
            panic!("checked structural definition");
        };
        assert_eq!(definition.safety, DefinitionSafety::Safe);
        assert!(!definition.value.has_fvar());
        assert!(!definition.value.has_loose_bvars());
        let Some(ConstantInfo::Defn(companion)) = base
            .environment()
            .find(&name(&format!("{label}._unsafe_rec")))
        else {
            panic!("executable companion");
        };
        assert_eq!(companion.safety, DefinitionSafety::Partial);
    }
    run(&base, "#eval countLeft 4", "13");
    run(&base, "#eval countRight 4", "19");
}

#[test]
fn mutual_structural_preserves_implicit_and_mixed_major_binders() {
    use fln_core::expr::{BinderInfo, ExprNode};
    use fln_env::constants::ConstantInfo;

    // The Reference's getRecArgInfo considers every parameter, including implicit
    // ones. Binder styles belong to the public members, not the shared dictionary.
    for (left, right, left_style, right_style, hint) in [
        (
            "{n : Nat}",
            "{n : Nat}",
            BinderInfo::Implicit,
            BinderInfo::Implicit,
            "",
        ),
        (
            "(n : Nat)",
            "{n : Nat}",
            BinderInfo::Default,
            BinderInfo::Implicit,
            "termination_by structural n",
        ),
        (
            "{n : Nat}",
            "(n : Nat)",
            BinderInfo::Implicit,
            BinderInfo::Default,
            "termination_by structural n",
        ),
        (
            "⦃n : Nat⦄",
            "{n : Nat}",
            BinderInfo::StrictImplicit,
            BinderInfo::Implicit,
            "termination_by structural n",
        ),
    ] {
        let source = format!(
            r#"
mutual
 def left {left} (seed : Nat) : Nat := match n with
  | 0 => seed
  | k+1 => right (n := k) seed + 1
 {hint}
 def right {right} (seed : Nat) : Nat := match n with
  | 0 => seed + 6
  | k+1 => left (n := k) seed + 2
 {hint}
end
example : left (n := 4) 7 = 13 := rfl
example : right (n := 4) 7 = 19 := rfl
example (n seed : Nat) : left (n := n+1) seed = right (n := n) seed + 1 := rfl
"#
        );
        let base = check(&source);
        for (label, expected) in [("left", left_style), ("right", right_style)] {
            let Some(ConstantInfo::Defn(definition)) = base.environment().find(&name(label)) else {
                panic!("checked structural definition");
            };
            let ExprNode::ForallE { binder_info, .. } = definition.base.type_.node() else {
                panic!("member keeps its major binder");
            };
            assert_eq!(*binder_info, expected, "{label}: {source}");
            let ExprNode::Lam { binder_info, .. } = definition.value.node() else {
                panic!("member wrapper keeps its major binder");
            };
            assert_eq!(*binder_info, expected, "{label}: {source}");
        }
        run(&base, "#eval left (n := 4) 7", "13");
        run(&base, "#eval right (n := 4) 7", "19");
    }
}

#[test]
fn mutual_structural_implicit_majors_do_not_hide_nondecreasing_calls() {
    let (base, limits) = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        r#"
mutual
 def badLeft {n : Nat} : Nat := badRight (n := n)
 termination_by structural n
 def badRight {n : Nat} : Nat := badLeft (n := n)
 termination_by structural n
end
"#,
        r#"
mutual
 def badLeft (n : Nat) : Nat := match n with
  | 0 => 0
  | k+1 => let unused := badRight (n := k+2); badRight (n := k)
 termination_by structural n
 def badRight {n : Nat} : Nat := match n with
  | 0 => 1
  | k+1 => badLeft k
 termination_by structural n
end
"#,
    ] {
        oracle(source, false);
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .is_err(),
            "implicit application must preserve termination checks: {source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        for label in ["badLeft", "badRight", "badLeft._mutual"] {
            assert!(!base.environment().contains(&name(label)));
        }
    }
}

#[test]
fn mutual_structural_product_preserves_distinct_member_result_types() {
    check(
        "mutual\n\
         def count : Nat -> Nat\n | 0 => 7\n | n+1 => match flag n with | true => 1 | false => 0\n\
         def flag : Nat -> Bool\n | 0 => false\n | n+1 => match count n with | 0 => true | _ => false\n\
         end\n\
         example : count 1 = 0 := rfl\n\
         example : flag 1 = false := rfl\n\
         example : flag 2 = true := rfl\n\
         example : count 3 = 1 := rfl\n",
    );
}

#[test]
fn mutual_structural_three_member_cycle_keeps_projection_order() {
    let base = check(
        "mutual\n\
         def firstCycle : Nat -> Nat\n | 0 => 1\n | n+1 => secondCycle n\n\
         def secondCycle : Nat -> Nat\n | 0 => 2\n | n+1 => thirdCycle n\n\
         def thirdCycle : Nat -> Nat\n | 0 => 3\n | n+1 => firstCycle n\n\
         end\n\
         example : firstCycle 1 = 2 := rfl\n\
         example : firstCycle 2 = 3 := rfl\n\
         example : firstCycle 3 = 1 := rfl\n",
    );
    run(&base, "#eval secondCycle 5", "1");
}

#[test]
fn mutual_structural_generalizes_trailing_parameters_and_preserves_abbrev() {
    use fln_env::constants::{ConstantInfo, ReducibilityHints};
    let base = check(
        "mutual\n\
         def left (n seed : Nat) : Nat := match n with\n | 0 => seed\n | k+1 => right k seed 3\n\
         abbrev right (n seed extra : Nat) : Nat := match n with\n | 0 => seed + extra\n | k+1 => left k seed + extra\n\
         end\n\
         example : left 2 7 = 10 := rfl\n\
         example : right 2 7 3 = 13 := rfl\n",
    );
    let Some(ConstantInfo::Defn(right)) = base.environment().find(&name("right")) else {
        panic!("checked structural abbreviation");
    };
    assert_eq!(right.hints, ReducibilityHints::Abbrev);
    run(&base, "#eval left 2 7", "10");
    run(&base, "#eval right 2 7 3", "13");
}

#[test]
fn mutual_structural_single_member_remains_reducible_and_executable() {
    let base = check(
        "mutual\n\
         def half : Nat -> Nat\n | 0 => 0\n | 1 => 0\n | n+2 => half n + 1\n\
         termination_by structural n => n\n\
         end\n\
         example : half 8 = 4 := rfl\n\
         example (n : Nat) : half (n+2) = half n + 1 := rfl\n",
    );
    run(&base, "#eval half 8", "4");
}

#[test]
fn mutual_structural_self_recursive_components_keep_acyclic_dependencies() {
    let base = check(
        "mutual\n\
         def answer : Nat := grow 4\n\
         def grow : Nat -> Nat\n | 0 => initial\n | n+1 => grow n + 2\n\
         def initial : Nat := 3\n\
         end\n\
         example : answer = 11 := rfl\n\
         example (n : Nat) : grow (n+1) = grow n + 2 := rfl\n",
    );
    run(&base, "#eval answer", "11");
}

#[test]
fn mutual_structural_preserves_polymorphic_fixed_list_parameters() {
    // As in the course-of-values regressions, Prod enables the native family's below
    // generator. The bounded seed's built-in List intentionally has no brecOn.
    let (base, limits) = engine();
    let base = base
        .check_source_files(
            &[b"structure Prod (A : Type u) (B : Type v) where\n fst : A\n snd : B\n"],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let source = "inductive MutualList (A : Type u) where\n | nil : MutualList A\n | cons : A -> MutualList A -> MutualList A\n\
         mutual\n\
         def listLeft.{u} {A : Type u} : MutualList A -> Nat\n | .nil => 0\n | .cons _ tail => listRight tail + 1\n\
         def listRight.{u} {A : Type u} : MutualList A -> Nat\n | .nil => 0\n | .cons _ tail => listLeft tail + 2\n\
         end\n\
         example : listLeft (.cons 1 (.cons 2 (.cons 3 .nil))) = 4 := rfl\n\
         example : listRight (.cons 1 (.cons 2 (.cons 3 .nil))) = 5 := rfl\n\
         example (A : Type u) (a : A) (tail : MutualList A) : listLeft (.cons a tail) = listRight tail + 1 := rfl\n";
    oracle(source, true);
    let base = base
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("both checkers complete")
        .engine;
    run(
        &base,
        "#eval listLeft (.cons 1 (.cons 2 (.cons 3 .nil)))",
        "4",
    );
    run(
        &base,
        "#eval listRight (.cons 1 (.cons 2 (.cons 3 .nil)))",
        "5",
    );
}

#[test]
fn mutual_structural_checks_unused_initializers_and_escaping_peers() {
    let (base, limits) = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "mutual\ndef badLeft : Nat -> Nat\n | 0 => 0\n | n+1 => let unused := badRight (n+2); badRight n\ntermination_by structural n => n\ndef badRight : Nat -> Nat\n | 0 => 1\n | n+1 => badLeft n\ntermination_by structural n => n\nend",
        "mutual\ndef badLeft : Nat -> Nat\n | 0 => 0\n | n+1 => let invalid : Bool := n; badRight n\ndef badRight : Nat -> Nat\n | 0 => 1\n | n+1 => badLeft n\nend",
        "mutual\ndef badLeft : Nat -> Nat\n | 0 => 0\n | n+1 => (fun f : Nat -> Nat => f (n+1)) badRight\ntermination_by structural n => n\ndef badRight : Nat -> Nat\n | 0 => 1\n | n+1 => badLeft n\ntermination_by structural n => n\nend",
    ] {
        oracle(source, false);
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .is_err(),
            "invalid original body must not be erased: {source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&name("badLeft")));
    }
}

#[test]
fn mutual_structural_hint_never_admits_a_nondecreasing_cycle() {
    let (base, limits) = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "mutual\ndef badLeft (n : Nat) : Nat := badRight n\ntermination_by structural n\ndef badRight (n : Nat) : Nat := badLeft n\ntermination_by structural n\nend",
        "mutual\ndef badLeft : Nat -> Nat\n | 0 => 0\n | n+1 => badRight (n+2)\ntermination_by structural n => n\ndef badRight : Nat -> Nat\n | 0 => 1\n | n+1 => badLeft n\ntermination_by structural n => n\nend",
    ] {
        oracle(source, false);
        let result = base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        );
        assert!(
            result.is_err(),
            "nondecreasing component must not be admitted: {source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&name("badLeft")));
    }
    check("theorem recovered (n : Nat) : n = n := rfl");
}
#[test]
fn forward_theorems_remain_theorems_and_need_no_placeholder_axioms() {
    check(
        "mutual\n theorem first : True := second\n theorem second : True := True.intro\nend\nexample : True := first\n",
    );
}
#[test]
fn definitions_and_abbreviations_preserve_their_written_kind() {
    check(
        "mutual\n def first : Nat := second\n abbrev second : Nat := 41\nend\nexample : first = 41 := rfl\n",
    );
}

fn name(text: &str) -> fln_core::name::Name {
    fln_core::name::Name::from_components(text.split('.'))
}
fn run(base: &Engine, query: &str, expected: &str) {
    let answer = base
        .execute_source_definitions(
            &[query.as_bytes()],
            &KVMap::new(),
            fln::EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
        )
        .unwrap_or_else(|error| panic!("{query}: {error:?}"))
        .into_complete()
        .expect("runtime completed");
    let [execution] = answer.executions.as_slice() else {
        panic!("one execution");
    };
    let fln::VmExit::Returned(value) = &execution.exit else {
        panic!("{execution:?}");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected)
    );
}
#[test]
fn checked_safe_members_execute_without_unsafe_companions() {
    use fln_env::constants::{ConstantInfo, DefinitionSafety, ReducibilityHints};
    let base = check(
        "mutual\n def first (n : Nat) : Nat := second n + 1\n abbrev second (n : Nat) : Nat := n + 40\nend\n",
    );
    run(&base, "#eval first 1", "42");
    for label in ["first", "second"] {
        let Some(ConstantInfo::Defn(definition)) = base.environment().find(&name(label)) else {
            panic!("safe def");
        };
        assert_eq!(definition.safety, DefinitionSafety::Safe);
        assert!(
            !base
                .environment()
                .contains(&name(&format!("{label}._unsafe_rec")))
        );
        if label == "second" {
            assert_eq!(definition.hints, ReducibilityHints::Abbrev);
        }
    }
    let proofs = check(
        "mutual\n theorem first : True := second\n theorem second : True := True.intro\nend\n",
    );
    for label in ["first", "second"] {
        assert!(matches!(
            proofs.environment().find(&name(label)),
            Some(ConstantInfo::Thm(_))
        ));
    }
}
#[test]
fn shared_section_captures_include_peer_only_dependencies() {
    let base = check(
        "section\nvariable (unused : String) (left right : Nat)\nmutual\n def first (n : Nat) : Nat := second n + left\n def second (n : Nat) : Nat := n + right\n def independent (n : Nat) : Nat := n\nend\nend\n",
    );
    run(&base, "#eval first 7 13 5", "25");
    run(&base, "#eval second 7 13 5", "18");
    run(&base, "#eval independent 7 13 5", "5");
}

#[test]
fn recursive_section_captures_include_acyclic_peer_dependencies() {
    let base = check(
        "section\n\
         variable (unused : String) (left right : Nat)\n\
         mutual\n\
          def capturedLeft : Nat -> Nat\n\
          | 0 => left\n\
          | n+1 => capturedRight n + capturedHelper n\n\
          def capturedRight : Nat -> Nat\n\
          | 0 => right\n\
          | n+1 => capturedLeft n\n\
          def capturedHelper (n : Nat) : Nat := n + right\n\
         end\nend\n\
         example : capturedLeft 7 13 2 = 21 := rfl\n\
         example : capturedRight 7 13 2 = 26 := rfl\n",
    );
    run(&base, "#eval capturedLeft 7 13 2", "21");
    run(&base, "#eval capturedRight 7 13 2", "26");
    run(&base, "#eval capturedHelper 7 13 5", "18");
}

#[test]
fn recursive_section_captures_preserve_universes_and_structural_hint_aliases() {
    let base = check(
        "universe u\nsection\n\
         variable (unused : String) (A : Type u) (left right : A)\n\
         mutual\n\
          def capturedPickLeft : Nat -> A\n\
          | 0 => left\n\
          | n+1 => capturedPickRight n\n\
          termination_by structural n => n\n\
          def capturedPickRight : Nat -> A\n\
          | 0 => right\n\
          | n+1 => capturedPickLeft n\n\
          termination_by structural n => n\n\
         end\nend\n\
         example : capturedPickLeft Nat 7 13 2 = 7 := rfl\n\
         example : capturedPickRight Nat 7 13 2 = 13 := rfl\n",
    );
    run(&base, "#eval capturedPickLeft Nat 7 13 3", "13");
    run(&base, "#eval capturedPickRight Nat 7 13 3", "7");
}

#[test]
fn recursive_section_captures_include_instance_dictionaries() {
    let base = check(
        "universe u\nsection\n\
         variable {A : Type u} [Inhabited A]\n\
         mutual\n\
          def capturedDefaultLeft : Nat -> A\n\
          | 0 => default\n\
          | n+1 => capturedDefaultRight n\n\
          def capturedDefaultRight : Nat -> A\n\
          | 0 => default\n\
          | n+1 => capturedDefaultLeft n\n\
         end\nend\n\
         example : (capturedDefaultLeft 2 : Nat) = 0 := rfl\n",
    );
    run(&base, "#eval (capturedDefaultRight 3 : Nat)", "0");
}

#[test]
fn recursive_section_captures_preserve_singletons_and_shadowed_parameters() {
    let singleton = check(
        "section\nvariable (offset : Nat)\n\
         mutual\n\
          def capturedSelf : Nat -> Nat\n\
          | 0 => offset\n\
          | n+1 => capturedSelf n + 1\n\
         end\nend\n\
         example : capturedSelf 7 3 = 10 := rfl\n",
    );
    run(&singleton, "#eval capturedSelf 7 3", "10");
    let shadowed = check(
        "section\nvariable (value : Nat)\n\
         mutual\n\
          def capturedShadow (value : Nat) : Nat := match value with\n\
          | 0 => 0\n\
          | n+1 => capturedPeer n\n\
          def capturedPeer : Nat -> Nat\n\
          | 0 => value\n\
          | n+1 => capturedShadow n\n\
         end\nend\n\
         example : capturedShadow 7 3 = 7 := rfl\n",
    );
    run(&shadowed, "#eval capturedShadow 7 3", "7");
}

#[test]
fn recursive_section_captures_include_body_only_universes() {
    let base = check(
        "universe u\nsection\n\
         variable (A : Type u) (project : A -> Nat) (value : A)\n\
         mutual\n\
          def capturedBodyLeft : Nat -> Nat\n\
          | 0 => capturedBodyHelper 0\n\
          | n+1 => capturedBodyRight n + 1\n\
          def capturedBodyRight : Nat -> Nat\n\
          | 0 => capturedBodyHelper 1\n\
          | n+1 => capturedBodyLeft n + 2\n\
          def capturedBodyHelper (n : Nat) : Nat := project value + n\n\
         end\nend\n\
         example : capturedBodyLeft Nat (fun n => n) 40 2 = 43 := rfl\n",
    );
    for label in [
        "capturedBodyLeft",
        "capturedBodyRight",
        "capturedBodyHelper",
    ] {
        let Some(fln_env::constants::ConstantInfo::Defn(definition)) =
            base.environment().find(&name(label))
        else {
            panic!("checked definition");
        };
        assert_eq!(definition.base.level_params.len(), 1);
        assert!(!definition.base.type_.has_fvar());
        assert!(!definition.value.has_fvar());
    }
    run(&base, "#eval capturedBodyLeft Nat (fun n => n) 40 2", "43");
}

#[test]
fn invalid_recursive_section_captures_leave_predecessor_unchanged() {
    let (base, limits) = engine();
    let before = base.logical_root(&KVMap::new());
    for source in [
        "section\nvariable (offset : Nat)\nmutual\n\
         def capturedBadLeft : Nat -> Nat\n | 0 => offset\n\
         | n+1 => let invalid : Bool := offset; capturedBadRight n\n\
         def capturedBadRight : Nat -> Nat\n | 0 => offset\n\
         | n+1 => capturedBadLeft n\nend\nend\n",
        "section\nvariable (offset : Nat)\nmutual\n\
         def capturedBadLeft (n : Nat) : Nat := if n == 0 then offset else capturedBadRight n\n\
         termination_by structural n\n\
         def capturedBadRight (n : Nat) : Nat := capturedBadLeft n\n\
         termination_by structural n\nend\nend\n",
        "section\nvariable (offset : Nat)\nend\nmutual\n\
         def capturedBadLeft : Nat -> Nat\n | 0 => offset\n\
         | n+1 => capturedBadRight n\n\
         def capturedBadRight : Nat -> Nat\n | 0 => 0\n\
         | n+1 => capturedBadLeft n\nend\n",
    ] {
        oracle(source, false);
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .is_err(),
            "invalid source must not acquire a section closure: {source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(!base.environment().contains(&name("capturedBadLeft")));
    }
    let source = "def recoveredSection : Nat := 42\n";
    oracle(source, true);
    let recovered = base
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    run(&recovered, "#eval recoveredSection", "42");
}

#[test]
fn namespace_and_shadowed_parameters_do_not_create_false_cycles() {
    let base = check(
        "namespace N\nmutual\n def first (second : Nat) : Nat := second\n def second : Nat := first 42\nend\nend N\nexample : N.second = 42 := rfl\n",
    );
    run(&base, "#eval N.second", "42");
}
#[test]
fn polymorphic_forward_references_close_their_universe_parameters() {
    let base = check(
        "mutual\n def first.{u} (A : Type u) (a : A) : A := second A a\n def second.{u} (A : Type u) (a : A) : A := a\nend\nexample : first Nat 42 = 42 := rfl\n",
    );
    run(&base, "#eval first Nat 42", "42");
}
#[test]
fn every_cycle_is_refused_before_any_declaration_can_be_published() {
    for source in [
        "mutual\n def first : Nat := second\n def second : Nat := first\nend",
        "mutual\n theorem first : False := second\n theorem second : False := first\nend",
        "mutual\n def independent : Nat := 0\n def first (n : Nat) : Nat := second n\n def second (n : Nat) : Nat := first n\nend",
        "mutual\n def first (n : Nat) : Nat := first n\nend",
    ] {
        oracle(source, false);
        let (base, limits) = engine();
        let before = base.logical_root(&KVMap::new());
        let members = fln_parse::command_scope::mutual::parse(source.as_bytes())
            .unwrap()
            .unwrap();
        let result = fln_elab::source::partial::elaborate_ordinary_group(
            &members,
            base.environment(),
            limits.kernel,
            &fln_elab::source::scope::SourceScope::default(),
        );
        assert!(
            matches!(
                result,
                Err(fln_elab::NatDefinitionElabError::UnexpectedSyntax {
                    expected: "recursive ordinary mutual component requires termination elaboration"
                })
            ),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(!base.environment().contains(&name("independent")));
    }
}
#[test]
fn header_dependencies_are_not_made_valid_by_sequentializing_the_group() {
    let (base, limits) = engine();
    let source = "mutual\n def carrier : Type := Nat\n def value : carrier := 41\nend";
    oracle(source, false);
    let members = fln_parse::command_scope::mutual::parse(source.as_bytes())
        .unwrap()
        .unwrap();
    let result = fln_elab::source::partial::elaborate_ordinary_group(
        &members,
        base.environment(),
        limits.kernel,
        &fln_elab::source::scope::SourceScope::default(),
    );
    assert!(matches!(
        result,
        Err(fln_elab::NatDefinitionElabError::Inference(
            fln_elab::source::SourceInferenceError::UnknownConstant(_)
        ))
    ));
    assert!(!base.environment().contains(&name("carrier")));
}

#[test]
fn a_safe_mutual_body_cannot_acquire_unsafe_dependencies() {
    let (base, limits) = engine();
    let source = "unsafe def dangerous : Nat := 42\nmutual\n def first : Nat := second\n def second : Nat := dangerous\nend\n";
    oracle(source, false);
    let result = base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits),
    );
    assert!(
        result.is_err(),
        "unsafe dependency reached a safe declaration"
    );
    eprintln!("unsafe dependency: {:?}", result.err());
    assert!(!base.environment().contains(&name("first")));
}
#[test]
fn unhandled_modifiers_and_modern_visibility_are_not_silently_dropped() {
    let (base, limits) = engine();
    for source in [
        "mutual\n @[simp] theorem first : True := True.intro\nend",
        "mutual\n private def first : Nat := 42\nend",
        "mutual\n noncomputable def first : Nat := 42\nend",
    ] {
        let members = fln_parse::command_scope::mutual::parse(source.as_bytes())
            .unwrap()
            .unwrap();
        assert!(matches!(
            fln_elab::source::partial::elaborate_ordinary_group(
                &members,
                base.environment(),
                limits.kernel,
                &fln_elab::source::scope::SourceScope::default()
            ),
            Err(fln_elab::NatDefinitionElabError::UnexpectedSyntax { .. })
        ));
    }
    let members = fln_parse::command_scope::mutual::parse(b"mutual def first : Nat := 42 end")
        .unwrap()
        .unwrap();
    let scope = fln_elab::source::scope::SourceScope {
        private_module: Some(name("Hidden")),
        ..Default::default()
    };
    assert!(matches!(
        fln_elab::source::partial::elaborate_ordinary_group(
            &members,
            base.environment(),
            limits.kernel,
            &scope
        ),
        Err(fln_elab::NatDefinitionElabError::UnexpectedSyntax {
            expected: "ordinary mutual group outside module visibility projection"
        })
    ));
}
#[test]
fn duplicate_names_and_invalid_late_bodies_leave_the_predecessor_unchanged() {
    let (base, limits) = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "mutual\n def first : Nat := 0\n def first : Nat := 1\nend",
        "mutual\n theorem first : True := True.intro\n theorem second : False := True.intro\nend",
    ] {
        let members = fln_parse::command_scope::mutual::parse(source.as_bytes())
            .unwrap()
            .unwrap();
        let result = fln_elab::source::partial::elaborate_ordinary_group(
            &members,
            base.environment(),
            limits.kernel,
            &fln_elab::source::scope::SourceScope::default(),
        );
        assert!(result.is_err());
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&name("first")));
    }
}

fn oracle(source: &str, expected: bool) {
    use std::{
        path::PathBuf,
        process::Command,
        sync::{
            OnceLock,
            atomic::{AtomicUsize, Ordering},
        },
    };
    static REFERENCE: OnceLock<Option<PathBuf>> = OnceLock::new();
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let reference = REFERENCE.get_or_init(|| {
        let pin = include_str!("../../../SUITE.lock")
            .lines()
            .find(|line| line.starts_with("reference leanprover/lean4 "))
            .unwrap();
        let field = |key: &str| {
            pin.split_whitespace()
                .find_map(|word| word.strip_prefix(key))
                .unwrap()
        };
        let tag = field("tag=");
        let commit = field("commit=");
        let lib = std::env::var_os("FLN_REFERENCE_LIB")
            .map(PathBuf::from)
            .or_else(|| {
                std::env::var_os("HOME").map(|home| {
                    PathBuf::from(home)
                        .join(".elan/toolchains")
                        .join(format!("leanprover--lean4---{tag}"))
                        .join("lib/lean")
                })
            });
        let executable = lib
            .and_then(|lib| lib.parent()?.parent().map(|p| p.join("bin/lean")))
            .filter(|path| path.is_file());
        let Some(executable) = executable else {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "pinned Reference required"
            );
            eprintln!("SKIP: mutual differential requires the pinned compiler");
            return None;
        };
        let version = Command::new(&executable).arg("--version").output().unwrap();
        let text = String::from_utf8(version.stdout).unwrap();
        assert!(
            version.status.success()
                && text.contains(tag.trim_start_matches('v'))
                && text.contains(commit),
            "{text}"
        );
        Some(executable)
    });
    let Some(reference) = reference else {
        return;
    };
    let dir = std::env::temp_dir().join(format!("fln-ordinary-mutual-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{}.lean", NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::write(&path, source).unwrap();
    let output = Command::new(reference).arg(path).output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(if expected { 0 } else { 1 }),
        "Reference mismatch: {source}\n{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn written_universe_lists_must_agree_before_body_elaboration() {
    let (base, limits) = engine();
    for source in [
        "mutual\n def first.{u} (A : Type u) (a : A) : A := second A a\n def second.{v} (A : Type v) (a : A) : A := a\nend",
        "mutual\n def first.{u,v} : Nat := 0\n def second.{v,u} : Nat := 1\nend",
        "mutual\n def first.{u} : Nat := 0\n def second : Nat := 1\nend",
    ] {
        oracle(source, false);
        let members = fln_parse::command_scope::mutual::parse(source.as_bytes())
            .unwrap()
            .unwrap();
        assert!(matches!(
            fln_elab::source::partial::elaborate_ordinary_group(
                &members,
                base.environment(),
                limits.kernel,
                &fln_elab::source::scope::SourceScope::default()
            ),
            Err(fln_elab::NatDefinitionElabError::UnexpectedSyntax {
                expected: "ordinary mutual universe parameters mismatch"
            })
        ));
    }
}
