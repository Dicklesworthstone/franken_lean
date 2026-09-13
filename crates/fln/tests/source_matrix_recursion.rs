//! The matrix compiler must preserve genuine structural children.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn check(source: &str) {
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
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
}
#[test]
fn recursive_matrix_generalizes_the_other_discriminant() {
    check(
        "def count (n : Nat) (b : Bool) : Nat := match n, b with
      | .zero, _ => 0
      | .succ k, true => count k false + 1
      | .succ k, false => count k true + 2
      theorem counted : count 3 true = 4 := by rfl",
    );
}
const SEQ: &str = "inductive Seq (A : Type) where | nil | cons (value : A) (tail : Seq A)\n";
#[test]
fn zip_recurses_on_the_first_list_and_changes_the_second() {
    check(&format!("{SEQ}
      def zipSum (xs ys : Seq Nat) : Seq Nat := match xs, ys with
        | .nil, _ => Seq.nil
        | .cons x xt, .nil => Seq.nil
        | .cons x xt, .cons y yt => Seq.cons (x + y) (zipSum xt yt)
      theorem zipped : zipSum (Seq.cons 1 (Seq.cons 2 Seq.nil)) (Seq.cons 3 (Seq.cons 4 Seq.nil)) = Seq.cons 4 (Seq.cons 6 Seq.nil) := by rfl"));
}

#[test]
fn matrix_recursion_changes_trailing_accumulators_and_three_columns() {
    check("def accumulate (n : Nat) (flag : Bool) (extra : Bool) (acc : Nat) : Nat := match n, flag, extra with
      | .zero, _, _ => acc
      | .succ k, true, _ => accumulate k false extra (acc + 1)
      | .succ k, false, true => accumulate k true false (acc + 2)
      | .succ k, false, false => accumulate k true true (acc + 3)
      theorem accumulated : accumulate 4 true true 10 = 17 := by rfl");
}

#[test]
fn polymorphic_matrix_recursion_keeps_uniform_parameters() {
    check(&format!("{SEQ}
      def zipWith {{A B C : Type}} (f : A -> B -> C) (xs : Seq A) (ys : Seq B) : Seq C := match xs, ys with
        | .nil, _ => Seq.nil
        | .cons x xt, .nil => Seq.nil
        | .cons x xt, .cons y yt => Seq.cons (f x y) (zipWith f xt yt)
      theorem zipped : zipWith (fun x y => x + y) (Seq.cons 1 (Seq.cons 2 Seq.nil)) (Seq.cons 3 (Seq.cons 4 Seq.nil)) = Seq.cons 4 (Seq.cons 6 Seq.nil) := by rfl"));
}

const VEC: &str = "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n";
#[test]
fn correlated_indexed_matrices_recurse_at_the_actual_child_index() {
    check(&format!("{VEC}
      def zipVec (n : Nat) (xs ys : Vec Nat n) : Vec Nat n := match xs, ys with
        | .nil, .nil => Vec.nil
        | .cons k x xt, .cons j y yt => Vec.cons k (x + y) (zipVec k xt yt)
      theorem zipped : zipVec 2 (Vec.cons 1 1 (Vec.cons 0 2 Vec.nil)) (Vec.cons 1 3 (Vec.cons 0 4 Vec.nil)) = Vec.cons 1 4 (Vec.cons 0 6 Vec.nil) := by rfl"));
}

const WALK: &str = "inductive Walk : Nat -> Type where | done (n : Nat) : Walk n | step (n : Nat) (child : Walk n) : Walk n\n";
#[test]
fn constrained_matrix_recursion_uses_checked_child_equations() {
    check(&format!(
        "{WALK}
      def countSeven (w : Walk 7) (flag : Bool) : Nat := match w, flag with
        | .done k, _ => k
        | .step k child, true => countSeven child false + 1
        | .step k child, false => countSeven child true + 2
      theorem counted : countSeven (Walk.step 7 (Walk.step 7 (Walk.done 7))) true = 10 := by rfl"
    ));
}

#[test]
fn nested_secondary_patterns_preserve_the_decreasing_child() {
    check(
        "inductive Maybe (A : Type) where | none | some (value : A)
      def countNested (n : Nat) (option : Maybe (Maybe Nat)) : Nat := match n, option with
        | .zero, _ => 0
        | .succ k, .none => countNested k (Maybe.some Maybe.none) + 1
        | .succ k, .some .none => countNested k (Maybe.some (Maybe.some 2)) + 2
        | .succ k, .some (.some value) => countNested k Maybe.none + value
      theorem counted : countNested 3 Maybe.none = 5 := by rfl",
    );
}

#[test]
fn nested_pattern_in_payload_is_not_a_recursive_field() {
    check(&format!("{SEQ}
      def sumNested (xs : Seq (Seq Nat)) : Nat := match xs with
        | .nil => 0
        | .cons .nil tail => sumNested tail
        | .cons (.cons x inner) tail => x + sumNested tail
      theorem summed : sumNested (Seq.cons (Seq.cons 3 Seq.nil) (Seq.cons (Seq.cons 4 Seq.nil) Seq.nil)) = 7 := by rfl"));
}

#[test]
fn partial_calls_keep_remaining_parameters_below_source_lambdas() {
    check(
        "def partial (n : Nat) (flag : Bool) (acc : Nat) : Nat := match n, flag with
      | .zero, _ => acc
      | .succ k, _ => (fun extra => partial k false (acc + extra)) 2
      theorem called : partial 3 true 7 = 13 := by rfl",
    );
    check(
        "def deferred (n : Nat) (flag : Bool) (acc : Nat) : Nat := match n, flag with
      | .zero, _ => acc
      | .succ k, _ => let rest := deferred k; rest false (acc + 1)
      theorem called : deferred 3 true 7 = 10 := by rfl",
    );
}

#[test]
fn simultaneous_pattern_bindings_do_not_capture_header_names() {
    check(
        "def swapped (n : Nat) (b : Bool) : Nat := match n, b with
      | .zero, _ => 0
      | .succ b, n => swapped b n + 1
      theorem swapped_ok : swapped 4 true = 4 := by rfl",
    );
}

#[test]
fn original_decreasing_input_is_rebound_at_each_step() {
    check(
        "def sum (n : Nat) (b : Bool) : Nat := match n, b with
      | .zero, _ => n
      | .succ k, _ => sum k b + n
      theorem sum_ok : sum 4 true = 10 := by rfl",
    );
}

#[test]
fn recursive_matrix_computations_support_universal_induction() {
    check(
        "def copy (n : Nat) (b : Bool) : Nat := match n, b with
      | .zero, _ => 0
      | .succ k, _ => Nat.succ (copy k b)
      theorem copy_ok (n : Nat) (b : Bool) : copy n b = n := by
        induction n with
        | zero => rfl
        | succ k ih => simp only [copy, ih]",
    );
}

fn reject(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let before = engine.logical_root(&KVMap::new());
    let error = engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .expect_err("invalid recursive program must refuse");
    assert!(
        !format!("{error:?}").contains("Frontend(Parse("),
        "negative fixture did not parse: {source}\n{error:?}"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn nondecreasing_recursive_calls_cannot_hide_in_unused_source() {
    for body in [
        "bad n b",
        "let unused := bad n b; 0",
        "(fun x => 0) (bad n b)",
        "let unused := (bad n b : Nat); 0",
    ] {
        reject(&format!(
            "def bad (n : Nat) (b : Bool) : Nat := match n, b with | .zero, _ => 0 | .succ k, _ => {body}"
        ));
    }
}

#[test]
fn malformed_matrix_branches_and_false_proofs_still_refuse() {
    for source in [
        "def bad (n : Nat) (b : Bool) : Nat := match n, b with | .zero, _ => 0 | .succ k, true => bad k false",
        "def bad (n : Nat) (b : Bool) : Nat := match n, b with | .zero, _ => 0 | .succ k, _ => let unused := (b : Nat); bad k false",
        "def bad (n : Nat) (b : Bool) : Nat := match n, b with | .zero, _ => 0 | .succ k, _ => let unused := (1 : String); bad k false",
        "theorem bad (n : Nat) (b : Bool) : 0 = 1 := match n, b with | .zero, _ => by rfl | .succ k, _ => bad k false",
        "def bad (n : Nat) (b : Bool) : Nat := match n, b with | _, _ => 0 | .succ k, _ => bad k b",
    ] {
        reject(source);
    }
}

#[test]
fn matrix_recursion_does_not_assume_an_arbitrary_smaller_input() {
    reject(
        "def bad (n : Nat) (b : Bool) : Nat := match n, b with | .zero, _ => 0 | .succ k, _ => bad (k + 0) b",
    );
    reject(
        "def bad (n : Nat) (b : Bool) : Nat := match n, b with | .zero, _ => 0 | .succ k, _ => bad 0 b",
    );
    reject(
        "def bad (n : Nat) (b : Bool) : Nat := match n, b with | .zero, _ => 0 | .succ (.succ k), _ => bad k b | .succ .zero, _ => 0",
    );
}

#[test]
fn separate_recursive_children_keep_separate_hypotheses_through_other_columns() {
    check("inductive Tree where | leaf (n : Nat) | fork (left right : Tree)
      def weighted (t : Tree) (flag : Bool) : Nat := match t, flag with
        | .leaf n, _ => n
        | .fork left right, true => weighted left false + weighted right true
        | .fork left right, false => weighted left true + weighted right false
      theorem counted : weighted (Tree.fork (Tree.leaf 3) (Tree.fork (Tree.leaf 5) (Tree.leaf 7))) true = 15 := by rfl");
}

#[test]
fn dependent_index_matrices_keep_the_original_index_telescope() {
    check("inductive Trace (A : Type) (P : A -> Type) : forall a : A, P a -> Type where
        | stop (a : A) (v : P a) : Trace A P a v
        | step (a : A) (v : P a) (child : Trace A P a v) : Trace A P a v
      def traceCopy {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) (b : Bool) : Trace A P a v := match t, b with
        | .stop x y, _ => Trace.stop x y
        | .step x y child, _ => Trace.step x y (traceCopy x y child b)
      def trace : Trace Nat (fun a => Bool) 3 true := Trace.step 3 true (Trace.stop 3 true)
      theorem copied : traceCopy 3 true trace false = trace := by rfl
      theorem allCopied (A : Type) (P : A -> Type) (a : A) (v : P a) (t : Trace A P a v) (b : Bool) : traceCopy a v t b = t := by
        induction t with
        | stop x y => rfl
        | step x y child ih => simp only [traceCopy, ih]; rfl");
}

#[test]
fn header_and_pattern_names_survive_nested_generated_aliases() {
    check(
        "def selectSum (n : Nat) (m : Nat) : Nat := match n, m with
      | .zero, _ => m
      | .succ m, .zero => selectSum m 0 + 1
      | .succ m, .succ n => selectSum m n + 1
      theorem selected : selectSum 3 7 = 7 := by rfl",
    );
    check(
        "def keep (n : Nat) (flag : Bool) : Nat := match n, flag with
      | .zero, _ => n
      | .succ k, _ => let k := k; keep k flag + n
      theorem kept : keep 4 true = 10 := by rfl",
    );
}

#[test]
fn pattern_elimination_retains_the_original_nonrecursive_discriminant() {
    check(
        "def original (n : Nat) (flag : Bool) : Nat := match n, flag with
      | .zero, _ => n
      | .succ k, _ => n
      theorem original_ok : original 12 true = 12 := by rfl",
    );
}

#[test]
fn generated_hypotheses_cannot_solve_user_proofs_by_assumption() {
    reject(
        "def fact (n : Nat) : 0 = 0 := match n, true with
      | .zero, _ => rfl
      | .succ k, true => fact k
      | .succ k, false => by assumption",
    );
}

#[test]
fn generated_hypotheses_cannot_supply_contradictions_or_instances() {
    reject(
        "inductive Endless where | more (child : Endless)
      inductive Void : Prop where
      def empty (e : Endless) : Void := match e, true with
        | .more child, true => empty child
        | .more child, false => by contradiction",
    );
    reject(
        "inductive Endless where | more (child : Endless)
      class Marker where value : Nat
      def marker (e : Endless) : Marker := match e, true with
        | .more child, true => marker child
        | .more child, false => inferInstance",
    );
}

#[test]
fn generated_equations_are_not_available_to_user_substitution() {
    reject(
        "inductive Endless where | more (child : Endless)
      def equal (n m : Nat) (e : Endless) : n = m := match e, true with
        | .more child, true => equal n m child
        | .more child, false => by subst n; rfl",
    );
}

#[test]
fn fixed_parameters_and_wrong_child_indices_cannot_be_changed() {
    reject(&format!(
        "{SEQ}
      def wrong (f : Nat -> Nat) (xs : Seq Nat) (flag : Bool) : Nat := match xs, flag with
        | .nil, _ => 0
        | .cons x tail, _ => wrong (fun y => y + 1) tail flag"
    ));
    reject(&format!(
        "{VEC}
      def wrong (n : Nat) (xs ys : Vec Nat n) : Vec Nat n := match xs, ys with
        | .nil, .nil => Vec.nil
        | .cons k x xt, .cons j y yt => Vec.cons k x (wrong (Nat.succ k) xt yt)"
    ));
}

#[test]
fn recursive_markers_cannot_escape_as_unapplied_or_nonroot_functions() {
    reject(
        "def bad (n : Nat) (b : Bool) : Nat := match n, b with | .zero, _ => 0 | .succ k, _ => (fun f => f k b) bad",
    );
    reject(
        "def bad (n : Nat) (b : Bool) : Nat := let saved := n; match saved, b with | .zero, _ => 0 | .succ k, _ => bad k b",
    );
    // This formerly unsupported later-column recursion now has a genuine
    // decreasing Nat argument. Keep a computation and the nondecreasing mutant.
    check(
        "def later (b : Bool) (n : Nat) : Nat := match b, n with | _, .zero => 0 | _, .succ k => Nat.succ (later b k)\n theorem checked : later true 4 = 4 := by rfl",
    );
    reject(
        "def bad (b : Bool) (n : Nat) : Nat := match b, n with | _, .zero => 0 | _, .succ k => bad b (Nat.succ k)",
    );
}

#[test]
fn resource_stops_and_invalid_suffixes_do_not_publish_a_prefix() {
    use fln::Outcome;
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let good = "def copy (n : Nat) (b : Bool) : Nat := match n, b with | .zero, _ => 0 | .succ k, _ => Nat.succ (copy k b)";
    let bad = "theorem bad : copy 1 true = 7 := by rfl";
    let mut low = SourceCheckLimits::new(limits);
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    match engine.check_source_files(&[good.as_bytes()], &KVMap::new(), low) {
        Ok(Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("expected resource nonanswer: {other:?}"),
    }
    for valid in [false, true, false, true] {
        let inputs = if valid {
            vec![good.as_bytes()]
        } else {
            vec![good.as_bytes(), bad.as_bytes()]
        };
        let result =
            engine.check_source_files(&inputs, &KVMap::new(), SourceCheckLimits::new(limits));
        assert_eq!(
            matches!(result, Ok(Outcome::Complete(_))),
            valid,
            "{result:?}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn ignored_discriminants_and_recursive_arguments_keep_actual_k1_obligations() {
    for source in [
        "def bad (n : Nat) : Nat := match n, (1 : String) with | .zero, _ => 0 | .succ k, _ => bad k",
        "def bad (n : Nat) (b : Bool) : Nat := match n, b with | .zero, _ => 0 | .succ k, _ => let alias : String := k; let unused := bad k b; 0",
    ] {
        let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
        let engine = Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap();
        let error = engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap_err();
        assert!(
            error.disposition().1,
            "expected authoritative K1 rejection, not an earlier capability refusal: {source}\n{error:?}"
        );
    }
}

#[test]
fn emitted_matrix_recursion_has_no_self_constants_free_markers_or_new_axioms() {
    use fln::Name;
    use fln_core::expr::ExprNode;
    use fln_env::constants::ConstantInfo;
    use std::collections::HashSet;
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let source = "def copied (n : Nat) (b : Bool) : Nat := match n, b with | .zero, _ => 0 | .succ k, true => Nat.succ (copied k false) | .succ k, false => Nat.succ (copied k true)";
    let output = engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let name = Name::from_components(["copied"]);
    let Some(ConstantInfo::Defn(definition)) = output.engine.environment().find(&name) else {
        panic!("checked definition")
    };
    assert!(!definition.value.has_fvar());
    assert!(!definition.value.has_expr_mvar());
    let mut constants = HashSet::new();
    let mut visited = HashSet::new();
    let mut pending = vec![&definition.value];
    while let Some(expr) = pending.pop() {
        if !visited.insert(expr.allocation_identity()) {
            continue;
        }
        match expr.node() {
            ExprNode::Const { name, .. } => {
                constants.insert(name.clone());
            }
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    assert!(constants.contains(&Name::from_components(["Nat", "rec"])));
    assert!(constants.contains(&Name::from_components(["Bool", "rec"])));
    assert!(!constants.contains(&name));
    assert!(constants.iter().all(|name| !matches!(
        output.engine.environment().find(name),
        Some(ConstantInfo::Axiom(_))
    )));
}
