//! Higher-order recursive constructors are checked independently at admission.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn check(source: &str) -> Engine {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap()
        .engine
}
const TREE: &str =
    "inductive Branching where | leaf (value : Nat) | node (children : Nat -> Branching)\n";
#[test]
fn higher_order_children_support_construction_matching_and_computation() {
    check(&format!(
        r#"{TREE}
        def first (t : Branching) : Nat := match t with
          | .leaf value => value
          | .node children => match children 0 with
            | .leaf value => value
            | .node other => 99
        theorem selected : first (Branching.node (fun n => Branching.leaf (n + 7))) = 7 := by rfl
        theorem deeper : first (Branching.node (fun n => Branching.node (fun k => Branching.leaf k))) = 99 := by rfl
    "#
    ));
}
#[test]
fn induction_hypotheses_quantify_the_child_functions_arguments() {
    check(&format!(
        r#"{TREE}
        theorem principle (P : Branching -> Prop)
            (atLeaf : forall n : Nat, P (Branching.leaf n))
            (atNode : forall f : Nat -> Branching, (forall n : Nat, P (f n)) -> P (Branching.node f))
            (t : Branching) : P t := by
          induction t with
          | leaf n => exact atLeaf n
          | node f ih => exact atNode f ih
    "#
    ));
}
#[test]
fn accessibility_elimination_returns_dependent_data_without_an_axiom() {
    check(
        r#"
        inductive Accessible (A : Type) (R : A -> A -> Prop) : A -> Prop where
          | intro (x : A) (next : forall y : A, R y x -> Accessible A R y) : Accessible A R x
        def fold (A : Type) (R : A -> A -> Prop) (P : A -> Type)
            (step : forall x : A, (forall y : A, R y x -> P y) -> P x)
            (a : A) (h : Accessible A R a) : P a := by
          induction h with
          | intro x next ih => exact step x ih
    "#,
    );
}
#[test]
fn function_valued_children_with_dependent_arguments_and_indices() {
    check(
        r#"
        inductive Trace (A : Type) (B : A -> Type) : A -> Type where
          | stop (a : A) : Trace A B a
          | more (a : A) (children : forall x : A, B x -> Trace A B x) : Trace A B a
        def inspect (a : Nat) (t : Trace Nat (fun x => Bool) a) : Nat := match t with
          | .stop x => x
          | .more x next => match next 13 true with
            | .stop value => value
            | .more value child => value + 1
        theorem read : inspect 7 (Trace.more 7 (fun x p => Trace.stop x)) = 13 := by rfl
    "#,
    );
}
#[test]
fn direct_and_function_children_share_the_correct_minor_telescope() {
    check(
        r#"
        inductive Mixed (A : Type) (B : A -> Type) where
          | leaf (a : A)
          | node (a : A) (b : B a) (one : B a -> Mixed A B)
              (many : forall x : A, B x -> Mixed A B) (tail : Mixed A B)
        theorem principle (A : Type) (B : A -> Type) (P : Mixed A B -> Prop)
            (base : forall a : A, P (Mixed.leaf a))
            (step : forall a : A, forall b : B a, forall one : B a -> Mixed A B,
              forall many : (forall x : A, B x -> Mixed A B), forall tail : Mixed A B,
              (forall z : B a, P (one z)) -> (forall x : A, forall z : B x, P (many x z)) ->
              P tail -> P (Mixed.node a b one many tail)) (t : Mixed A B) : P t := by
          induction t with
          | leaf a => exact base a
          | node a b one many tail ihOne ihMany ihTail => exact step a b one many tail ihOne ihMany ihTail
    "#,
    );
}
fn reject(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let before = engine.logical_root(&KVMap::new());
    assert!(
        engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits)
            )
            .is_err(),
        "{source}"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}
#[test]
fn nonpositive_nested_nonuniform_and_oversized_children_never_publish() {
    for source in [
        "inductive Bad where | mk (next : Bad -> Bad)",
        "inductive Bad where | mk (next : (Bad -> Nat) -> Bad)",
        "inductive Box (A : Type) where | mk (a : A)\ninductive Bad where | mk (next : Nat -> Box Bad)",
        "inductive Bad (A : Type) where | mk (next : Nat -> Bad Nat)",
        "inductive Tiny : Type where | mk (next : Type -> Tiny)",
    ] {
        reject(source);
    }
}
#[test]
fn cases_does_not_expose_function_induction_hypotheses() {
    reject(&format!(
        r#"{TREE}
        theorem bad (P : Branching -> Prop)
            (atLeaf : forall n : Nat, P (Branching.leaf n))
            (atNode : forall f : Nat -> Branching, (forall n : Nat, P (f n)) -> P (Branching.node f))
            (t : Branching) : P t := by
          cases t with
          | leaf n => exact atLeaf n
          | node f => apply atNode; assumption
    "#
    ));
}
#[test]
fn higher_order_small_elimination_cannot_extract_a_hidden_witness() {
    reject(
        r#"
        inductive Hidden (A : Type) : Prop where
          | mk (witness : A) (next : Nat -> Hidden A)
        def bad (A : Type) (h : Hidden A) : A := by
          induction h with
          | mk a next ih => exact a
    "#,
    );
}
#[test]
fn invalid_unused_function_bodies_are_not_erased_by_matching() {
    reject(&format!(
        r#"{TREE}
        def ignored : Nat := match Branching.node (fun n => let bad : String := n; Branching.leaf n) with
          | .leaf value => value
          | .node children => 0
    "#
    ));
}

#[test]
fn source_calls_on_applied_function_children_compute_with_changing_arguments() {
    check(&format!(
        r#"{TREE}
        def follow (t : Branching) (route : Nat) : Nat := match t with
          | .leaf value => value
          | .node children => follow (children route) (route + 1)
        theorem selected : follow (Branching.node (fun n => Branching.leaf n)) 7 = 7 := by rfl
        theorem nested : follow (Branching.node (fun n => Branching.node (fun k => Branching.leaf (n + k)))) 3 = 7 := by rfl
    "#
    ));
}

#[test]
fn recursive_function_children_can_change_dependent_indices() {
    check(
        r#"
        inductive Trace (A : Type) (B : A -> Type) : A -> Type where
          | stop (a : A) : Trace A B a
          | more (a : A) (children : forall x : A, B x -> Trace A B x) : Trace A B a
        def read (a : Nat) (t : Trace Nat (fun x => Bool) a) : Nat := match t with
          | .stop x => x
          | .more x next => read 13 (next 13 true)
        theorem changed : read 7 (Trace.more 7 (fun x p => Trace.stop x)) = 13 := by rfl
        "#,
    );
}

const ACCESSIBLE: &str = r#"
    inductive Accessible (A : Type) (R : A -> A -> Prop) : A -> Prop where
      | intro (x : A) (next : forall y : A, R y x -> Accessible A R y) : Accessible A R x
"#;

#[test]
fn recursive_accessibility_fold_preserves_dependent_types_and_proof_arguments() {
    check(&format!(
        r#"{ACCESSIBLE}
        def foldRecursive (A : Type) (R : A -> A -> Prop) (P : A -> Type)
            (step : forall x : A, (forall y : A, R y x -> P y) -> P x)
            (a : A) (h : Accessible A R a) : P a := match h with
          | .intro x next => step x (fun y hy => foldRecursive A R P step y (next y hy))
        inductive NoEdge (x y : Nat) : Prop where
        def accessible (a : Nat) : Accessible Nat NoEdge a := Accessible.intro a (fun y h => by cases h)
        theorem folded : foldRecursive Nat NoEdge (fun x => Nat) (fun x ih => x + 1) 7 (accessible 7) = 8 := by rfl
        "#
    ));
}

#[test]
fn function_child_programs_have_universal_induction_proofs() {
    check(&format!(
        r#"{TREE}
        def erase (t : Branching) : Nat := match t with
          | .leaf value => 0
          | .node children => erase (children 3)
        theorem erased (t : Branching) : erase t = 0 := by
          induction t with
          | leaf value => rfl
          | node children ih => simp only [erase, ih 3]
        "#
    ));
}

#[test]
fn mixed_children_keep_their_argument_and_hypothesis_order() {
    check(
        r#"
        inductive Mixed where
          | leaf (value : Nat)
          | node (direct : Mixed) (one : Nat -> Mixed) (two : Nat -> Bool -> Mixed)
        def score (t : Mixed) : Nat := match t with
          | .leaf value => value
          | .node direct one two => score direct + score (one 3) + score (two 5 true)
        theorem total : score (Mixed.node (Mixed.leaf 2) (fun n => Mixed.leaf n) (fun n b => Mixed.leaf n)) = 10 := by rfl
        "#,
    );
}

#[test]
fn function_child_calls_preserve_partial_application_and_outer_lambdas() {
    check(&format!(
        r#"{TREE}
        def offset (t : Branching) (acc : Nat) : Nat := match t with
          | .leaf n => n + acc
          | .node children => let smaller := offset (children 4); smaller (acc + 1)
        theorem partial : offset (Branching.node (fun n => Branching.leaf n)) 7 = 12 := by rfl
        def under (t : Branching) : Nat -> Nat := match t with
          | .leaf n => fun x => n + x
          | .node children => fun x => under (children x) (x + 1)
        theorem captured : under (Branching.node (fun n => Branching.leaf n)) 5 = 11 := by rfl
        "#
    ));
}

#[test]
fn function_child_calls_work_in_equations_and_recursive_pattern_matrices() {
    check(&format!(
        r#"{TREE}
        def follow : Bool -> Branching -> Nat
          | true, .leaf n => n
          | false, .leaf n => n + 1
          | b, .node children => follow b (children 6)
        theorem later_column : follow false (Branching.node (fun n => Branching.leaf n)) = 7 := by rfl
        def inspect (t : Branching) (b : Bool) : Nat := match t, b with
          | .leaf n, _ => n
          | .node children, true => inspect (children 3) false
          | .node children, false => inspect (children 4) true
        theorem branch : inspect (Branching.node (fun n => Branching.node (fun k => Branching.leaf (n + k)))) true = 7 := by rfl
        "#
    ));
}

const INDEXED_FUNCTIONS: &str = r#"
    inductive Indexed : Nat -> Type where
      | leaf (index value : Nat) : Indexed index
      | node (index : Nat) (children : Nat -> Indexed index) : Indexed index
"#;

#[test]
fn fixed_index_function_children_keep_conditional_recursion_evidence() {
    check(&format!(
        r#"{INDEXED_FUNCTIONS}
        def atSeven (t : Indexed 7) (acc : Nat) : Nat := match t with
          | .leaf k value => value + acc
          | .node k children => atSeven (children 4) (acc + 1)
        theorem computed : atSeven (Indexed.node 7 (fun n => Indexed.leaf 7 n)) 3 = 8 := by rfl
        def partially (t : Indexed 7) : Nat -> Nat := match t with
          | .leaf k value => fun x => value + x
          | .node k children => fun x => partially (children x) (x + 1)
        theorem outer : partially (Indexed.node 7 (fun n => Indexed.leaf 7 n)) 5 = 11 := by rfl
        "#
    ));
}

#[test]
fn constrained_calls_check_actual_function_child_indices() {
    check(
        r#"
        inductive Free : Nat -> Type where
          | leaf (index value : Nat) : Free index
          | node (index : Nat) (children : forall n : Nat, Free n) : Free index
        def atSeven (t : Free 7) : Nat := match t with
          | .leaf k value => value
          | .node k children => atSeven (children 7)
        theorem computed : atSeven (Free.node 7 (fun n => Free.leaf n (n + 1))) = 8 := by rfl
        "#,
    );
    reject(
        r#"
        inductive Free : Nat -> Type where
          | leaf (index value : Nat) : Free index
          | node (index : Nat) (children : forall n : Nat, Free n) : Free index
        def bad (t : Free 7) : Nat := match t with
          | .leaf k value => value
          | .node k children => bad (children 6)
        "#,
    );
}

#[test]
fn recursive_child_arguments_are_themselves_checked_and_lowered() {
    check(&format!(
        r#"{TREE}
        def nestedCall (t : Branching) : Nat := match t with
          | .leaf value => value
          | .node children => nestedCall (children (nestedCall (children 2)))
        theorem computed : nestedCall (Branching.node (fun n => Branching.leaf n)) = 2 := by rfl
        "#
    ));
    for body in [
        "bad (children (bad t))",
        "let unused := bad t; bad (children 0)",
        "bad (children (let unused := bad t; 0))",
        "let children := fun n => t; bad (children 0)",
    ] {
        reject(&format!(
            "{TREE}\ndef bad (t : Branching) : Nat := match t with | .leaf n => n | .node children => {body}"
        ));
    }
}

#[test]
fn unrelated_functions_do_not_become_structural_children_by_result_type() {
    reject(&format!(
        r#"{TREE}
        def bad (other : Nat -> Branching) (t : Branching) : Nat := match t with
          | .leaf value => value
          | .node children => bad other (other 0)
        "#
    ));
    check(&format!(
        r#"{TREE}
        def alias (t : Branching) : Nat := match t with
          | .leaf n => n
          | .node children => let same := children; alias (same 9)
        theorem kept : alias (Branching.node (fun n => Branching.leaf n)) = 9 := by rfl
        "#
    ));
}

#[test]
fn discarded_child_argument_annotations_still_receive_kernel_rejection() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let source = format!(
        r#"{TREE}
        def ignore (s : String) : Nat := 0
        def bad (t : Branching) : Nat := match t with
          | .leaf n => n
          | .node children => bad (children (ignore (1 : String)))
        "#
    );
    let before = engine.logical_root(&KVMap::new());
    let error = engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .expect_err("a discarded invalid annotation is still checked");
    assert!(error.disposition().1, "{error:?}");
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn accessibility_recursion_evaluates_a_real_predecessor_call() {
    check(&format!(
        r#"{ACCESSIBLE}
        def fold (A : Type) (R : A -> A -> Prop) (P : A -> Type)
            (step : forall x : A, (forall y : A, R y x -> P y) -> P x)
            (a : A) (h : Accessible A R a) : P a := match h with
          | .intro x next => step x (fun y hy => fold A R P step y (next y hy))
        inductive Before : Bool -> Bool -> Prop where
          | edge : Before false true
        def falseAcc : Accessible Bool Before false := Accessible.intro false (fun y h => by cases h)
        def smaller (y : Bool) (h : Before y true) : Accessible Bool Before y := by
          cases h with
          | edge => exact falseAcc
        def trueAcc : Accessible Bool Before true := Accessible.intro true smaller
        def step (x : Bool) (rec : forall y : Bool, Before y x -> Nat) : Nat := by
          cases x with
          | false => exact 5
          | true => exact rec false Before.edge + 1
        theorem computed : fold Bool Before (fun x => Nat) step true trueAcc = 6 := by rfl
        "#
    ));
}

#[test]
fn function_child_arguments_retain_dependent_proof_binders() {
    check(
        r#"
        inductive Family where
          | leaf (n : Nat)
          | node (children : forall n : Nat, n = n -> Family)
        def follow (t : Family) : Nat := match t with
          | .leaf n => n
          | .node children => follow (children 7 rfl)
        theorem computed : follow (Family.node (fun n h => Family.leaf n)) = 7 := by rfl
        "#,
    );
}

#[test]
fn nested_scopes_cannot_expose_private_function_hypotheses() {
    for body in [
        "let leaked : Nat -> Nat := by assumption; follow (children 0)",
        "let leaked : Nat -> Nat := by refine ?_; assumption; follow (children 0)",
        "let children := fun n => t; follow (children 0)",
        "let child := children 0; match child with | .leaf n => n | .node grandchildren => follow (grandchildren 0)",
    ] {
        reject(&format!(
            "{TREE}\ndef follow (t : Branching) : Nat := match t with | .leaf n => n | .node children => {body}"
        ));
    }
}

#[test]
fn parameter_payload_functions_are_not_mistaken_for_recursive_fields() {
    reject(
        r#"
        inductive Box (A : Type) where | mk (payload : Nat -> A)
        def bad (b : Box (Box Nat)) : Nat := match b with
          | .mk payload => bad (Box.mk (fun n => payload n))
        "#,
    );
    reject(&format!(
        r#"{TREE}
        def bad (t : Branching) : Nat := match t with
          | .leaf n => n
          | .node children => let small : Branching := children; bad small
        "#
    ));
}

#[test]
fn function_child_calls_keep_fixed_parameters_and_dependent_results() {
    check(
        r#"
        inductive Tree (A : Type) where
          | leaf (value : A)
          | node (children : A -> Tree A)
        def pick {A : Type} (a : A) (t : Tree A) : A := match t with
          | .leaf value => value
          | .node children => pick a (children a)
        theorem computed : pick 7 (Tree.node (fun n => Tree.leaf (n + 1))) = 8 := by rfl
        "#,
    );
    reject(
        r#"
        inductive Tree (A : Type) where | leaf (a : A) | node (next : A -> Tree A)
        def bad {A : Type} (a : A) (t : Tree A) : Nat := match t with
          | .leaf value => 0
          | .node next => bad true (next a)
        "#,
    );
}

#[test]
fn function_child_lowering_retains_recursors_without_recursive_axioms() {
    use fln_core::expr::ExprNode;
    use fln_core::name::Name;
    use fln_env::constants::ConstantInfo;
    use std::collections::HashSet;
    let engine = check(&format!(
        r#"{TREE}
        def follow (t : Branching) : Nat := match t with | .leaf n => n | .node children => follow (children 0)
        "#
    ));
    let name = Name::from_components(["follow"]);
    let Some(ConstantInfo::Defn(declaration)) = engine.environment().find(&name) else {
        panic!("checked definition");
    };
    assert!(!declaration.value.has_fvar());
    assert!(!declaration.value.has_expr_mvar());
    let mut todo = vec![&declaration.value];
    let mut visited = HashSet::new();
    let mut constants = HashSet::new();
    while let Some(term) = todo.pop() {
        if !visited.insert(term.allocation_identity()) {
            continue;
        }
        match term.node() {
            ExprNode::Const { name, .. } => {
                constants.insert(name.clone());
            }
            ExprNode::App { f, a } => todo.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => todo.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => todo.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => todo.push(expr),
            _ => {}
        }
    }
    assert!(constants.contains(&Name::from_components(["Branching", "rec"])));
    assert!(!constants.contains(&name));
    assert!(constants.iter().all(|name| !matches!(
        engine.environment().find(name),
        Some(ConstantInfo::Axiom(_))
    )));
}

#[test]
fn applied_child_failures_and_budget_exhaustion_do_not_publish_a_prefix() {
    use fln::Outcome;
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = check(TREE);
    let root = engine.logical_root(&KVMap::new());
    let good = "def follow (t : Branching) : Nat := match t with | .leaf n => n | .node children => follow (children 0)";
    let bad = "def bad (t : Branching) : Nat := match t with | .leaf n => n | .node children => bad (children (bad t))";
    let mut low = SourceCheckLimits::new(limits);
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    match engine.check_source_files(&[good.as_bytes()], &KVMap::new(), low) {
        Ok(Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("expected a resource stop: {other:?}"),
    }
    for valid in [false, true, false, true] {
        let source = if valid {
            vec![good.as_bytes()]
        } else {
            vec![good.as_bytes(), bad.as_bytes()]
        };
        let result =
            engine.check_source_files(&source, &KVMap::new(), SourceCheckLimits::new(limits));
        assert_eq!(
            matches!(result, Ok(Outcome::Complete(_))),
            valid,
            "{result:?}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}
