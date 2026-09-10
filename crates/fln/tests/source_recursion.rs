//! Recursive definitions become recursors, never unchecked self declarations.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_core::expr::{Expr, ExprNode};
use fln_env::constants::ConstantInfo;
use std::collections::HashSet;
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(text: &str) -> fln::SourceFileCheck {
    engine()
        .check_source_files(
            &[text.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{text}\n{error:?}"))
        .into_complete()
        .unwrap()
}
fn constants(expr: &Expr) -> HashSet<Name> {
    let mut seen = HashSet::new();
    let mut found = HashSet::new();
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        if !seen.insert(expr.allocation_identity()) {
            continue;
        }
        match expr.node() {
            ExprNode::Const { name, .. } => {
                found.insert(name.clone());
            }
            ExprNode::App { f, a } => {
                pending.push(f);
                pending.push(a);
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                pending.push(binder_type);
                pending.push(body);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                pending.push(type_);
                pending.push(value);
                pending.push(body);
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    found
}

const VEC: &str = "inductive Vec (A : Type) : Nat -> Type where\n\
  | nil : Vec A 0\n\
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n\
def two : Vec Nat 2 := Vec.cons 1 7 (Vec.cons 0 9 Vec.nil)\n";

#[test]
fn indexed_structural_copy_preserves_lengths_and_has_no_recursive_axiom() {
    let checked = check(&format!(
        "{VEC}
def copyVec {{A : Type}} (n : Nat) (xs : Vec A n) : Vec A n := match xs with
  | .nil => Vec.nil
  | .cons k x tail => Vec.cons k x (copyVec k tail)
theorem compute : copyVec 2 two = two := by rfl
theorem identity {{A : Type}} (n : Nat) (xs : Vec A n) : copyVec n xs = xs := by
  induction xs with
  | nil => rfl
  | cons k x tail ih => simp only [copyVec, ih]"
    ));
    let Some(ConstantInfo::Defn(definition)) = checked
        .engine
        .environment()
        .find(&Name::from_components(["copyVec"]))
    else {
        panic!("definition");
    };
    let dependencies = constants(&definition.value);
    assert!(dependencies.contains(&Name::from_components(["Vec", "rec"])));
    assert!(!dependencies.contains(&Name::from_components(["copyVec"])));
    assert!(!definition.value.has_fvar());
    assert!(!definition.value.has_expr_mvar());
}

#[test]
fn indexed_recursive_map_changes_the_output_family_parameter() {
    check(&format!(
        "{VEC}
def mapVec {{A B : Type}} (f : A -> B) (n : Nat) (xs : Vec A n) : Vec B n := match xs with
  | .nil => Vec.nil
  | .cons k x tail => Vec.cons k (f x) (mapVec f k tail)
theorem ok : mapVec (fun x => x + 1) 2 two = Vec.cons 1 8 (Vec.cons 0 10 Vec.nil) := by rfl"
    ));
}

#[test]
fn indexed_root_names_are_rebound_to_the_current_constructor_indices() {
    check(&format!(
        "{VEC}
def indexSum {{A : Type}} (n : Nat) (xs : Vec A n) : Nat := match xs with
  | .nil => n
  | .cons k x tail => indexSum k tail + n
theorem ok : indexSum 2 two = 3 := by rfl
def retain {{A : Type}} (n : Nat) (xs : Vec A n) : Vec A n := match xs with
  | .nil => xs
  | .cons k x tail => let used := retain k tail; xs
theorem retained : retain 2 two = two := by rfl"
    ));
}

#[test]
fn indexed_recursion_generalizes_earlier_index_dependent_proof_arguments() {
    check(&format!(
        "{VEC}
def depth {{A : Type}} (n : Nat) (h : n = n) (xs : Vec A n) : Nat := match xs with
  | .nil => 0
  | .cons k x tail => depth k rfl tail + 1
theorem ok : depth 2 rfl two = 2 := by rfl"
    ));
}

#[test]
fn indexed_recursion_generalizes_earlier_data_and_changing_accumulators() {
    check(&format!(
        "{VEC}
def walk {{A : Type}} (n : Nat) (other : Vec A n) (xs : Vec A n) (acc : Nat) : Nat := match xs with
  | .nil => acc
  | .cons k x tail => walk k tail tail (acc + n)
theorem ok : walk 2 two two 10 = 13 := by rfl
def walkPartial {{A : Type}} (n : Nat) (xs : Vec A n) (acc : Nat) : Nat := match xs with
  | .nil => acc
  | .cons k x tail => let smaller := walkPartial k tail; smaller (acc + n)
theorem partial_ok : walkPartial 2 two 10 = 13 := by rfl"
    ));
}

#[test]
fn indexed_recursion_keeps_implicit_indices_and_pattern_shadowing_distinct() {
    check(&format!(
        "{VEC}
def copyImplicit {{A : Type}} {{n : Nat}} (xs : Vec A n) : Vec A n := match xs with
  | .nil => Vec.nil
  | .cons n x xs => Vec.cons n x (copyImplicit xs)
theorem ok : copyImplicit two = two := by rfl
def count {{A : Type}} (n : Nat) (xs : Vec A n) : Nat := match xs with
  | .nil => 0
  | .cons n x xs => count n xs + 1
theorem shadowed : count 2 two = 2 := by rfl"
    ));
}

#[test]
fn indexed_recursion_tracks_each_childs_distinct_multiple_indices() {
    check(
        "inductive Path (A : Type) : A -> A -> Type where
  | refl (a : A) : Path A a a
  | step (a b c : A) (left : Path A a b) (right : Path A b c) : Path A a c
def weight {A : Type} (from to : A) (path : Path A from to) : Nat := match path with
  | .refl a => 1
  | .step a b c left right => weight a b left + weight b c right
def example : Path Nat 7 7 := Path.step 7 7 7 (Path.refl 7) (Path.refl 7)
theorem ok : weight 7 7 example = 2 := by rfl",
    );
}

#[test]
fn indexed_recursion_does_not_confuse_family_index_order_with_header_order() {
    check(
        "inductive PairIndex : Nat -> Nat -> Type where
  | stop (a b : Nat) : PairIndex a b
  | step (a b : Nat) (child : PairIndex a b) : PairIndex (Nat.succ a) b
def count (b a : Nat) (input : PairIndex a b) : Nat := match input with
  | .stop x y => a + b
  | .step x y child => count y x child + 1
theorem ok : count 5 3 (PairIndex.step 2 5 (PairIndex.stop 2 5)) = 8 := by rfl",
    );
}

#[test]
fn indexed_recursion_cannot_discard_wrong_indices_or_nondecreasing_calls() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad {A : Type} (n : Nat) (xs : Vec A n) : Nat := match xs with | .nil => 0 | .cons k x tail => bad n xs",
        "def bad {A : Type} (n : Nat) (xs : Vec A n) : Nat := match xs with | .nil => 0 | .cons k x tail => bad n tail",
        "def bad {A : Type} (n : Nat) (xs : Vec A n) : Nat := match xs with | .nil => 0 | .cons k x tail => let unused := bad (Nat.succ k) tail; 1",
        "def bad {A : Type} (fixed : Nat) (n : Nat) (xs : Vec A n) : Nat := match xs with | .nil => fixed | .cons k x tail => bad 7 k tail",
        "def bad {A : Type} (n : Nat) (xs : Vec A n) : Nat := match xs with | .nil => 0 | .cons k x tail => let escaped := bad; escaped k tail",
        "def bad {A : Type} (n : Nat) (xs : Vec A n) : Nat := match xs with | .nil => 0 | .cons k x tail => let unused := bad (let invalid : String := k; k) tail; 1",
        "def bad {A : Type} (n : Nat) (xs : Vec A n) (acc : Nat) : Nat := match xs with | .nil => acc | .cons k x tail => bad k tail (1 : String)",
    ] {
        assert!(
            base.check_source_files(
                &[VEC.as_bytes(), source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&Name::from_components(["Vec"])));
    }
    assert!(
        base.check_source_files(
            &[VEC.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_ok()
    );
}

#[test]
fn indexed_recursive_proofs_cannot_hide_a_false_base_case() {
    let base = engine();
    let bad = format!(
        "{VEC}
theorem falseChain {{A : Type}} (n : Nat) (xs : Vec A n) : 0 = 1 := match xs with
  | .nil => rfl
  | .cons k x tail => falseChain k tail"
    );
    assert!(
        base.check_source_files(
            &[bad.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err()
    );
    check(&format!(
        "{VEC}
theorem reflexiveChain {{A : Type}} (n : Nat) (xs : Vec A n) : 0 = 0 := match xs with
  | .nil => rfl
  | .cons k x tail => reflexiveChain k tail"
    ));
}
#[test]
fn primitive_nat_recursion_computes_through_both_checkers() {
    let checked = check(
        "def count (n : Nat) : Nat := match n with | .zero => 0 | .succ k => count k + 1\ntheorem ok : count 7 = 7 := by rfl",
    );
    let Some(ConstantInfo::Defn(definition)) = checked
        .engine
        .environment()
        .find(&Name::from_components(["count"]))
    else {
        panic!("definition");
    };
    let dependencies = constants(&definition.value);
    assert!(dependencies.contains(&Name::from_components(["Nat", "rec"])));
    assert!(!dependencies.contains(&Name::from_components(["count"])));
    assert!(!definition.value.has_fvar());
    assert!(!definition.value.has_expr_mvar());
}
#[test]
fn root_major_references_are_rebound_at_every_recursive_step() {
    check(
        "def sumTo (n : Nat) : Nat := match n with | .zero => n | .succ k => sumTo k + n\ntheorem ok : sumTo 4 = 10 := by rfl",
    );
    check(
        "def count (n : Nat) : Nat := match n with | .zero => 0 | .succ n => count n + 1\ntheorem ok : count 4 = 4 := by rfl",
    );
}
#[test]
fn tree_recursion_uses_the_hypothesis_for_each_distinct_child() {
    check(
        "inductive Tree where | leaf (value : Nat) | fork (left right : Tree)\ndef sum (tree : Tree) : Nat := match tree with | .leaf value => value | .fork left right => sum left + sum right\ntheorem ok : sum (Tree.fork (Tree.leaf 3) (Tree.fork (Tree.leaf 7) (Tree.leaf 11))) = 21 := by rfl",
    );
}
#[test]
fn implicit_type_arguments_and_fixed_functions_are_preserved() {
    check(
        "def iterate {A : Type} (step : A -> A) (zero : A) (n : Nat) : A := match n with | .zero => zero | .succ k => step (iterate step zero k)\ntheorem ok : iterate (fun x => x + 2) 1 3 = 7 := by rfl",
    );
}
#[test]
fn direct_child_calls_survive_nested_nonrecursive_matches_and_lets() {
    check(
        "def count (flag : Bool) (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let previous := count flag k; match flag with | true => previous + 1 | false => previous + 2\ntheorem yes : count true 3 = 3 := by rfl\ntheorem no : count false 3 = 6 := by rfl",
    );
}
#[test]
fn nondecreasing_and_escaping_calls_are_failure_atomic_even_when_unused() {
    let base = engine();
    let snapshot = base.environment().clone();
    let invalid = [
        "def loop (n : Nat) : Nat := loop n",
        "def loop (n : Nat) : Nat := match n with | .zero => 0 | .succ k => loop n",
        "def loop (n : Nat) : Nat := match n with | .zero => 0 | .succ k => loop (Nat.succ k)",
        "def loop (n : Nat) : Nat := match n with | .zero => loop n | .succ k => 1",
        "def loop (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let unused := loop n; 0",
        "def loop (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let escaped := loop; escaped k",
        "def loop (n : Nat) : Nat := (match n with | .zero => 0 | .succ k => loop k) + 1",
        "def loop (fixed n : Nat) : Nat := match n with | .zero => fixed | .succ k => loop 1 k",
    ];
    for text in invalid {
        assert!(
            base.check_source_files(
                &[text.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{text}"
        );
        assert_eq!(base.environment(), &snapshot);
    }
    assert!(
        base.check_source_files(
            &[b"def good (n : Nat) : Nat := match n with | .zero => 0 | .succ k => good k + 1"],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_ok()
    );
}
#[test]
fn lexical_self_name_shadowing_stays_nonrecursive() {
    check(
        "def same (same : Nat) : Nat := same\ndef local : Nat := let local := 3; local\ntheorem ok : same local = 3 := by rfl",
    );
}
#[test]
fn a_bad_unreachable_recursive_branch_still_reaches_kernel_checking() {
    assert!(engine().check_source_files(&[b"def count (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let bad : String := count k; 1\ndef zero : Nat := count 0"], &KVMap::new(), SourceCheckLimits::new(limits())).is_err());
}

#[test]
fn changing_accumulators_are_generalized_in_the_induction_motive() {
    check(
        "def sumAcc (n : Nat) (acc : Nat) : Nat := match n with | .zero => acc | .succ k => sumAcc k (acc + n)\ntheorem zero : sumAcc 0 7 = 7 := by rfl\ntheorem total : sumAcc 4 0 = 10 := by rfl\ntheorem shifted : sumAcc 4 7 = 17 := by rfl",
    );
    check(
        "def walk (step : Nat -> Nat) (n : Nat) (acc : Nat) : Nat := match n with | .zero => acc | .succ k => walk step k (step acc)\ntheorem ok : walk (fun x => x + 3) 4 1 = 13 := by rfl",
    );
}

#[test]
fn changing_trailing_types_and_values_preserve_dependent_telescope_order() {
    check(
        "def repeat (n : Nat) {A : Type} (step : A -> A) (acc : A) : A := match n with | .zero => acc | .succ k => repeat k step (step acc)\ntheorem ok : repeat 3 (fun x => x + 2) 1 = 7 := by rfl",
    );
    check(
        "def switch (n : Nat) (A : Type) (x : A) : Nat := match n with | .zero => 0 | .succ k => switch k Nat 5 + 1\ntheorem ok : switch 4 String \"initial\" = 4 := by rfl",
    );
}

#[test]
fn trailing_proof_domains_are_specialized_to_the_smaller_major() {
    check(
        "def steps (n : Nat) (h : n = n) : Nat := match n with | .zero => 0 | .succ k => steps k rfl + 1\ntheorem ok : steps 4 rfl = 4 := by rfl",
    );
}

#[test]
fn trailing_instances_remain_actual_recursive_call_arguments() {
    check(
        "def choose (n : Nat) [Inhabited Nat] : Nat := match n with | .zero => default | .succ k => choose k + 1\ntheorem ok : choose 3 = 3 := by rfl",
    );
}

#[test]
fn partial_recursive_values_are_safe_after_the_structural_child_is_supplied() {
    check(
        "def add (n : Nat) (m : Nat) : Nat := match n with | .zero => m | .succ k => let smaller := add k; smaller (m + 1)\ntheorem ok : add 3 5 = 8 := by rfl",
    );
}

#[test]
fn constructor_pattern_names_shadow_trailing_parameter_names() {
    check(
        "def shadow (n : Nat) (k : Nat) : Nat := match n with | .zero => k | .succ k => shadow k 1\ntheorem base : shadow 0 9 = 9 := by rfl\ntheorem step : shadow 3 9 = 1 := by rfl",
    );
}

#[test]
fn nested_recursive_calls_in_changed_arguments_are_lowered_too() {
    check(
        "def nested (n : Nat) (acc : Nat) : Nat := match n with | .zero => acc | .succ k => nested k (nested k acc + 1)\ntheorem ok : nested 3 0 = 7 := by rfl",
    );
}

#[test]
fn invalid_changed_arguments_are_not_erased_by_termination_lowering() {
    let base = engine();
    let before = base.environment().clone();
    for text in [
        "def bad (n : Nat) (acc : Nat) : Nat := match n with | .zero => acc | .succ k => bad k (bad n acc)",
        "def bad (n : Nat) (acc : Nat) : Nat := match n with | .zero => acc | .succ k => let unused := bad k (1 : String); 0",
        "def bad (fixed : Nat) (n : Nat) (acc : Nat) : Nat := match n with | .zero => acc | .succ k => bad 7 k acc",
        "def bad (n : Nat) (acc : Nat) : Nat := match n with | .zero => acc | .succ k => let escaped := bad; escaped k acc",
    ] {
        assert!(
            base.check_source_files(
                &[text.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{text}"
        );
        assert_eq!(base.environment(), &before);
    }
}

#[test]
fn recursive_results_can_be_types_and_proofs_not_only_natural_values() {
    check(
        "def Tower (n : Nat) : Type := match n with | .zero => Nat | .succ k => Tower k -> Tower k\ntheorem type_ok : Tower 1 = (Nat -> Nat) := by rfl",
    );
    check(
        "theorem proofChain (n : Nat) : 0 = 0 := match n with | .zero => rfl | .succ k => proofChain k",
    );
    assert!(engine().check_source_files(&[b"theorem falseChain (n : Nat) : 0 = 1 := match n with | .zero => falseChain n | .succ k => falseChain k"], &KVMap::new(), SourceCheckLimits::new(limits())).is_err());
}

#[test]
fn different_tree_children_receive_independent_changing_accumulators() {
    check(
        "inductive Tree where | leaf (value : Nat) | fork (left right : Tree)\ndef sumInto (tree : Tree) (acc : Nat) : Nat := match tree with | .leaf value => value + acc | .fork left right => sumInto right (sumInto left acc)\ntheorem ok : sumInto (Tree.fork (Tree.leaf 3) (Tree.fork (Tree.leaf 7) (Tree.leaf 11))) 5 = 26 := by rfl",
    );
}

#[test]
fn recursive_type_computations_supply_source_lambda_domains() {
    check(
        "def Tower (n : Nat) : Type := match n with | .zero => Nat | .succ k => Tower k -> Tower k\ndef idTower : Tower 1 := fun n => n\ndef higher : Tower 2 := fun f => f\ntheorem type_ok : idTower 9 = 9 := by rfl\ntheorem higher_ok : higher idTower 12 = 12 := by rfl",
    );
}

#[test]
fn nested_recursor_and_projection_continuations_expose_function_types() {
    check(
        "structure Shape where\n  carrier : Type\ndef shape (flag : Bool) : Shape := match flag with | true => { carrier := Nat -> Nat } | false => { carrier := String -> String }\ndef yes : (shape true).carrier := fun x => x\ndef no : (shape false).carrier := fun x => x\ntheorem yes_ok : yes 7 = 7 := by rfl\ntheorem no_ok : no \"ok\" = \"ok\" := by rfl",
    );
    check(
        "def choose (flag : Bool) : Type := match flag with | true => Nat -> Nat | false => String -> String\ndef id : choose (match false with | true => false | false => true) := fun x => x\ntheorem ok : id 9 = 9 := by rfl",
    );
}

#[test]
fn parameterized_constructor_types_reduce_without_losing_their_payload() {
    check(
        "inductive Maybe (A : Type) where | none | some (value : A)\ndef shape (m : Maybe Nat) : Type := match m with | .none => String -> String | .some n => Nat -> Nat\ndef someId : shape (Maybe.some 7) := fun x => x\ndef noneId : shape Maybe.none := fun x => x\ntheorem some_ok : someId 11 = 11 := by rfl\ntheorem none_ok : noneId \"ok\" = \"ok\" := by rfl",
    );
}

#[test]
fn huge_literal_type_selection_reduces_only_one_constructor_layer() {
    check(
        "def shape (n : Nat) : Type := match n with | .zero => String -> String | .succ k => Nat -> Nat\ndef id : shape 340282366920938463463374607431768211456 := fun x => x\ntheorem ok : id 5 = 5 := by rfl",
    );
}

#[test]
fn a_stuck_discriminant_does_not_guess_a_branch_or_erase_an_invalid_one() {
    let base = engine();
    let before = base.environment().clone();
    for text in [
        "def shape (flag : Bool) : Type := match flag with | true => Nat -> Nat | false => String\ndef bad (flag : Bool) : shape flag := fun x => x",
        "def bad : Nat := match true with | true => 1 | false => (1 : String)",
    ] {
        assert!(
            base.check_source_files(
                &[text.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{text}"
        );
        assert_eq!(base.environment(), &before);
    }
}
