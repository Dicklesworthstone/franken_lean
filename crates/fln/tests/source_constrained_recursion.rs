//! Real source recursion at constrained indices, admitted by both checkers.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn check(source: &str) -> Engine {
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
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
        .engine
}
const LOOP: &str = "inductive Loop : Nat -> Type where | base (n : Nat) : Loop n | step (n : Nat) (child : Loop n) : Loop n\n";
#[test]
fn fixed_index_recursive_copy_is_computed_by_the_real_recursor() {
    check(&format!(
        r#"{LOOP}
def copy (x : Loop 7) : Loop 7 := match x with
  | .base n => Loop.base n
  | .step n rest => Loop.step n (copy rest)
def sample : Loop 7 := Loop.step 7 (Loop.step 7 (Loop.base 7))
theorem copied : copy sample = sample := by rfl
"#
    ));
}
#[test]
fn constrained_recursion_can_change_an_accumulator() {
    check(&format!(
        r#"{LOOP}
def count (x : Loop 7) (acc : Nat) : Nat := match x with
  | .base n => acc
  | .step n rest => count rest (acc + 1)
theorem counted : count (Loop.step 7 (Loop.step 7 (Loop.base 7))) 4 = 6 := by rfl
"#
    ));
}
#[test]
fn repeated_index_recursion_has_separate_hypotheses_for_both_children() {
    check(
        r#"
inductive Tree : Nat -> Nat -> Type where
  | leaf (a b : Nat) : Tree a b
  | fork (a b : Nat) (left right : Tree a b) : Tree a b
def size (n : Nat) (tree : Tree n n) : Nat := match tree with
  | .leaf a b => 1
  | .fork a b left right => size n left + size n right
 theorem count : size 3 (Tree.fork 3 3 (Tree.leaf 3 3) (Tree.leaf 3 3)) = 2 := by rfl
"#,
    );
}

#[test]
fn constrained_recursive_copy_supports_a_universal_induction_proof() {
    check(&format!(
        r#"{LOOP}
def copy (x : Loop 7) : Loop 7 := match x with
  | .base n => Loop.base n
  | .step n rest => Loop.step n (copy rest)
theorem identity (x : Loop 7) : copy x = x := by
  induction x with
  | base n => rfl
  | step n rest ih => simp only [copy, ih]
"#
    ));
}

#[test]
fn uniform_parameters_remain_fixed_when_an_index_is_shared() {
    check(
        r#"
inductive Marked (tag : Nat) : Nat -> Type where
  | base : Marked tag tag
  | step (child : Marked tag tag) : Marked tag tag
def copy (tag : Nat) (value : Marked tag tag) : Marked tag tag := match value with
  | .base => Marked.base
  | .step child => Marked.step (copy tag child)
theorem identity : copy 9 (Marked.step (Marked.base : Marked 9 9)) = Marked.step Marked.base := by rfl
"#,
    );
}

#[test]
fn recursive_constrained_predicates_preserve_small_elimination() {
    check(
        r#"
inductive Evidence : Nat -> Prop where
  | base : Evidence 0
  | step (previous : Evidence 0) : Evidence 0
def copy (h : Evidence 0) : Evidence 0 := match h with
  | .base => Evidence.base
  | .step previous => Evidence.step (copy previous)
theorem usable (h : Evidence 0) : Evidence 0 := copy h
"#,
    );
}

#[test]
fn dependent_indices_and_changing_suffixes_keep_their_actual_types() {
    check(
        r#"
inductive Trace (A : Type) (P : A -> Type) : forall a : A, P a -> Type where
  | base (a : A) (v : P a) : Trace A P a v
  | step (a : A) (v : P a) (child : Trace A P a v) : Trace A P a v
def depth {A : Type} {P : A -> Type} (f : A -> A) (a : A) (v : P (f a))
    (t : Trace A P (f a) v) (acc : Nat) : Nat := match t with
  | .base x vx => acc
  | .step x vx child => depth f a v child (acc + 1)
def t : Trace Nat (fun n => Bool) 7 true := Trace.step 7 true (Trace.base 7 true)
theorem counted : depth Nat.succ 6 true t 4 = 5 := by rfl
"#,
    );
}

#[test]
fn dependent_arguments_before_and_after_the_input_are_generalized() {
    check(&format!(
        r#"{LOOP}
def depth (h : 7 = 7) (x : Loop 7) (e : x = x) : Nat := match x with
  | .base n => n
  | .step n rest => depth rfl rest rfl + 1
theorem counted : depth rfl (Loop.step 7 (Loop.base 7)) rfl = 8 := by rfl
"#
    ));
}

#[test]
fn polymorphic_constrained_recursion_infers_implicit_arguments() {
    check(
        r#"
inductive ListAt (A : Type) : Nat -> Type where
  | nil (n : Nat) : ListAt A n
  | cons (n : Nat) (head : A) (tail : ListAt A n) : ListAt A n
def copy {A : Type} (xs : ListAt A 3) : ListAt A 3 := match xs with
  | .nil n => ListAt.nil n
  | .cons n x tail => ListAt.cons n x (copy tail)
def sample : ListAt Nat 3 := ListAt.cons 3 11 (ListAt.nil 3)
theorem copied : copy sample = sample := by rfl
"#,
    );
}

fn reject(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    assert!(
        engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits)
            )
            .is_err(),
        "accepted invalid source: {source}"
    );
    assert_eq!(root, engine.logical_root(&KVMap::new()));
    engine
        .check_source_files(
            &[b"def recovered : Nat := 11"],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap();
}

#[test]
fn nondecreasing_calls_cannot_hide_in_unused_values_or_annotations() {
    for body in [
        "bad x",
        "let unused := bad x; 1",
        "let ignore : Nat -> Nat := fun ignored => 1; ignore (bad x)",
        "let unused := (bad rest : String); 1",
        "bad (Loop.step 7 rest)",
        "let escaped := bad; escaped rest",
    ] {
        reject(&format!(
            "{LOOP}\ndef bad (x : Loop 7) : Nat := match x with | .base n => 0 | .step n rest => {body}"
        ));
    }
}

#[test]
fn unresolved_child_indices_are_not_assumed_equal() {
    reject(
        r#"
inductive Down : Nat -> Type where | base (n : Nat) : Down n | step (n : Nat) (child : Down n) : Down (Nat.succ n)
def bad (x : Down 7) : Nat := match x with | .base n => 0 | .step n child => bad child
"#,
    );
}

#[test]
fn uniform_parameter_changes_and_false_branch_obligations_are_rejected() {
    reject(
        r#"
inductive Marked (tag : Nat) : Nat -> Type where | base : Marked tag tag | step (child : Marked tag tag) : Marked tag tag
def bad (tag : Nat) (x : Marked tag tag) : Nat := match x with | .base => 0 | .step child => bad 8 child
"#,
    );
    reject(&format!(
        "{LOOP}\ndef bad (x : Loop 7) : 0 = 1 := match x with | .base n => rfl | .step n rest => bad rest"
    ));
    reject(
        r#"
inductive Evidence : Nat -> Prop where | base : Evidence 0 | step (child : Evidence 0) : Evidence 0
def bad (h : Evidence 0) : Nat := match h with | .base => 0 | .step child => bad child + 1
"#,
    );
}

#[test]
fn user_proofs_cannot_see_the_compilers_recursive_hypotheses() {
    reject(
        "inductive Branch : Nat -> Type where | base (n : Nat) : Branch n | left (n : Nat) (child : Branch n) : Branch n | right (n : Nat) (child : Branch n) : Branch n\ndef proof (x : Branch 7) : 0 = 0 := match x with | .base n => rfl | .left n rest => proof rest | .right n rest => by assumption",
    );
}

#[test]
fn partial_child_calls_keep_their_remaining_dependent_function_arguments() {
    check(&format!(
        r#"{LOOP}
def combine (x : Loop 7) (a b : Nat) : Nat := match x with
  | .base n => a * 10 + b
  | .step n rest => let next := combine rest a; next (b + 1)
theorem counted : combine (Loop.step 7 (Loop.base 7)) 3 5 = 36 := by rfl
"#
    ));
}

#[test]
fn eta_completed_child_calls_do_not_capture_an_enclosing_lambda() {
    check(&format!(
        r#"{LOOP}
def combine (x : Loop 7) (a b : Nat) : Nat := match x with
  | .base n => a * 10 + b
  | .step n rest =>
    let next : Nat -> Nat -> Nat := fun v => combine rest v;
    next a (b + 1)
theorem counted : combine (Loop.step 7 (Loop.base 7)) 3 5 = 36 := by rfl
"#
    ));
}

#[test]
fn emitted_recursion_terms_use_admitted_recursors_not_self_constants_or_axioms() {
    use fln_core::expr::{Expr, ExprNode};
    use fln_core::name::Name;
    use fln_env::constants::ConstantInfo;
    use std::collections::HashSet;
    let engine = check(&format!(
        "{LOOP}\ndef copied (x : Loop 7) : Loop 7 := match x with | .base n => Loop.base n | .step n rest => Loop.step n (copied rest)"
    ));
    let name = Name::from_components(["copied"]);
    let Some(ConstantInfo::Defn(definition)) = engine.environment().find(&name) else {
        panic!("definition admitted");
    };
    assert!(!definition.value.has_fvar());
    assert!(!definition.value.has_expr_mvar());
    let mut todo: Vec<&Expr> = vec![&definition.value];
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
    assert!(constants.contains(&Name::from_components(["Loop", "rec"])));
    assert!(constants.contains(&Name::from_components(["Eq", "rec"])));
    assert!(!constants.contains(&name));
    assert!(constants.iter().all(|name| !matches!(
        engine.environment().find(name),
        Some(ConstantInfo::Axiom(_))
    )));
}

#[test]
fn low_budgets_and_failed_suffixes_do_not_publish_successful_prefixes() {
    use fln::Outcome;
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = check(LOOP);
    let root = engine.logical_root(&KVMap::new());
    let good = "def copied (x : Loop 7) : Loop 7 := match x with | .base n => Loop.base n | .step n rest => Loop.step n (copied rest)";
    let bad =
        "def bad (x : Loop 7) : 0 = 1 := match x with | .base n => rfl | .step n rest => bad rest";
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
