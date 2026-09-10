//! Pattern matches are checked as ordinary recursor applications by both engines.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};
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
    let result = engine().check_source_files(
        &[text.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    result
        .unwrap_or_else(|error| panic!("{text}\n{error:?}"))
        .into_complete()
        .unwrap()
}
fn constants(expr: &Expr) -> HashSet<Name> {
    let mut found = HashSet::new();
    let mut seen = HashSet::new();
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
#[test]
fn bool_match_computes_both_alternatives_and_keeps_the_real_recursor() {
    let result = check(
        "def flag (b : Bool) : Nat := match b with | true => 7 | false => 3\ntheorem yes : flag true = 7 := by rfl\ntheorem no : flag false = 3 := by rfl",
    );
    let Some(ConstantInfo::Defn(def)) = result
        .engine
        .environment()
        .find(&Name::from_components(["flag"]))
    else {
        panic!("checked definition");
    };
    assert!(constants(&def.value).contains(&Name::from_components(["Bool", "rec"])));
    assert_eq!(result.theorems, 2);
}
#[test]
fn parameterized_variants_destructure_payloads_in_separate_scopes() {
    check(
        "inductive Maybe (A : Type) where | none | some (value : A)\ndef get (m : Maybe Nat) : Nat := match m with | .some n => n | .none => 0\ntheorem some_ok : get (Maybe.some 13) = 13 := by rfl\ntheorem none_ok : get Maybe.none = 0 := by rfl",
    );
    check(
        "inductive Either (A B : Type) where | left (value : A) | right (value : B)\ndef choose (e : Either Nat Nat) : Nat := match e with | Either.left x => x + 1 | Either.right x => x + 2\ntheorem left_ok : choose (Either.left 4) = 5 := by rfl\ntheorem right_ok : choose (Either.right 4) = 6 := by rfl",
    );
}
#[test]
fn direct_recursive_fields_are_destructured_without_exposing_induction_hypotheses() {
    check(
        "inductive Chain where | nil | cons (head : Nat) (tail : Chain)\ndef first (c : Chain) : Nat := match c with | .nil => 0 | .cons n _ => n\ntheorem head_ok : first (Chain.cons 9 (Chain.cons 7 Chain.nil)) = 9 := by rfl",
    );
    check(
        "def pred (n : Nat) : Nat := match n with | Nat.zero => 0 | Nat.succ k => k\ntheorem pred_ok : pred 5 = 4 := by rfl",
    );
}
#[test]
fn catch_all_binds_the_actual_whole_constructor_value() {
    check(
        "inductive Letter where | a | b | c\ndef change (x : Letter) : Letter := match x with | .a => Letter.b | rest => rest\ntheorem a_ok : change Letter.a = Letter.b := by rfl\ntheorem c_ok : change Letter.c = Letter.c := by rfl",
    );
    check(
        "def flag (b : Bool) : Nat := match b with | true => 7 | _ => 3\ntheorem no : flag false = 3 := by rfl",
    );
}
#[test]
fn nested_matches_work_inside_terms_and_record_values() {
    check(
        "def f (a b : Bool) : Nat := match a with\n  | true => match b with\n    | true => 1\n    | false => 2\n  | false => 3\ntheorem nested : f true false = 2 := by rfl",
    );
    check(
        "structure Box where\n  value : Nat\ndef boxed (b : Bool) : Box := { value := (match b with | true => 9 | false => 2) + 1 }\ntheorem nested : (boxed true).value = 10 := by rfl",
    );
}
#[test]
fn inferred_result_types_and_function_valued_branches_are_supported() {
    check(
        "def choose (b : Bool) := match b with | true => 4 | false => 2\ntheorem selected : choose true = 4 := by rfl",
    );
    check(
        "def select (b : Bool) : Nat -> Nat := match b with | true => fun x => x + 1 | false => fun x => x + 2\ntheorem chosen : select false 3 = 5 := by rfl",
    );
}
#[test]
fn dependent_record_match_refines_the_expected_type() {
    check(
        "structure Package where\n  carrier : Type\n  value : carrier\ndef extract (p : Package) : p.carrier := match p with | Package.mk A x => x\ndef packaged : Package := { carrier := Nat, value := 21 }\ntheorem extracted : extract packaged = 21 := by rfl",
    );
}
#[test]
fn proposition_valued_matches_build_proofs_for_every_branch() {
    check("theorem self (b : Bool) : b = b := match b with | true => by rfl | false => by rfl");
    check(
        "inductive Item where | number (n : Nat) | flag (b : Bool)\ntheorem self (x : Item) : x = x := match x with | .number n => by rfl | .flag b => by rfl",
    );
}
#[test]
fn all_branches_are_checked_even_when_the_discriminant_is_a_literal() {
    for text in [
        "def bad : Nat := match true with | true => 1 | false => \"wrong\"",
        "def bad : Nat := match true with | true => 1 | false => (1 : String)",
        "theorem bad : 1 = 2 := match true with | true => by rfl | false => by rfl",
    ] {
        let e = engine();
        let root = e.logical_root(&KVMap::new());
        let result = e.check_source_files(
            &[text.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        );
        let error = result.expect_err("every branch must typecheck");
        assert_eq!(
            error.disposition(),
            ("kernel-rejection", true, 1),
            "{error:?}"
        );
        assert_eq!(e.logical_root(&KVMap::new()), root);
    }
}
#[test]
fn coverage_wrong_arity_unknown_constructors_and_bad_scopes_refuse_atomically() {
    for text in [
        "def bad (b : Bool) : Nat := match b with | true => 1",
        "def bad (b : Bool) : Nat := match b with | true => 1 | true => 2 | false => 3",
        "def bad (b : Bool) : Nat := match b with | true x => 1 | false => 0",
        "def bad (b : Bool) : Nat := match b with | .bogus => 1 | _ => 0",
        "def bad (b : Bool) : Nat := match b with | Nat.zero => 1 | _ => 0",
        "def bad (b : Bool) : Nat := match b with | _ => 1 | false => 0",
        "inductive Pair where | mk (x y : Nat)\ndef bad (p : Pair) : Nat := match p with | .mk x x => x",
        "inductive Maybe where | nil | some (x : Nat)\ndef bad (m : Maybe) : Nat := match m with | .some x => x | .nil => x",
    ] {
        let e = engine();
        let root = e.logical_root(&KVMap::new());
        assert!(
            !matches!(
                e.check_source_files(
                    &[text.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits())
                ),
                Ok(Outcome::Complete(_))
            ),
            "{text}"
        );
        assert_eq!(e.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn recursive_branches_with_multiple_recursive_fields_keep_only_named_payloads_visible() {
    check(
        "inductive Tree where | leaf (n : Nat) | fork (left right : Tree)\ndef leftmost (t : Tree) : Tree := match t with | .leaf n => Tree.leaf n | .fork l r => l\ntheorem left : leftmost (Tree.fork (Tree.leaf 9) (Tree.leaf 4)) = Tree.leaf 9 := by rfl",
    );
}

#[test]
fn compact_large_nat_literals_and_zero_branches_are_checked_by_both_engines() {
    check(
        "def predecessor (n : Nat) : Nat := match n with | .zero => 0 | .succ k => k\ntheorem zero_ok : predecessor 0 = 0 := by rfl\ntheorem large_ok : predecessor 340282366920938463463374607431768211456 = 340282366920938463463374607431768211455 := by rfl",
    );
}

#[test]
fn lets_in_branches_and_matches_in_let_values_preserve_scope() {
    check(
        "def f (b : Bool) : Nat := match b with | true => let x := 7; x + 1 | false => 0\ntheorem yes : f true = 8 := by rfl",
    );
    check(
        "def f (b : Bool) : Nat := let x := match b with | true => 7 | false => 2; x + 1\ntheorem no : f false = 3 := by rfl",
    );
    check(
        "def f (b c : Bool) : Nat := match b with | true => let x := match c with | true => 7 | false => 2; x + 1 | false => 0\ntheorem no : f true false = 3 := by rfl",
    );
}

#[test]
fn redundant_catch_all_cannot_hide_an_unchecked_branch() {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    let result = e.check_source_files(
        &[b"def f (b : Bool) : Nat := match b with | true => 0 | false => 1 | _ => (0 : String)"],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    assert!(result.is_err());
    assert_eq!(e.logical_root(&KVMap::new()), root);
}

#[test]
fn matching_in_tactics_and_lambda_arguments_preserves_checked_proof_terms() {
    check(
        "theorem bool_refl (b : Bool) : b = b := by exact (match b with | true => rfl | false => rfl)",
    );
    check(
        "def applied (b : Bool) : Nat := (fun x => x + 1) (match b with | true => 5 | false => 8)\ntheorem yes : applied true = 6 := by rfl",
    );
}

#[test]
fn annotated_branch_lets_and_nested_let_values_keep_their_own_separators() {
    check(
        "def f (b : Bool) : Nat := match b with | true => let x : Nat := 7; x + 1 | false => 0\ntheorem yes : f true = 8 := by rfl",
    );
    check(
        "def f (b : Bool) : Nat := let x := match b with | true => let y := 4; y + 1 | false => 0; x + 2\ntheorem yes : f true = 7 := by rfl",
    );
}

#[test]
fn failed_matches_cannot_publish_a_successful_prefix_across_files() {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    let prefix = b"inductive Branch where | left (n : Nat) | right (n : Nat)\ndef value (b : Branch) : Nat := match b with | .left n => n | .right n => n + 1";
    let good = b"theorem result : value (Branch.right 4) = 5 := by rfl";
    let bad = b"theorem wrong : value (Branch.right 4) = 4 := by rfl";
    for (suffix, success) in [
        (good.as_slice(), true),
        (bad.as_slice(), false),
        (good.as_slice(), true),
    ] {
        let result = e.check_source_files(
            &[prefix, suffix],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        );
        if success {
            let result = result.unwrap().into_complete().unwrap();
            assert_eq!(result.commands, 3);
            assert_eq!(result.theorems, 1);
        } else {
            assert_eq!(
                result.unwrap_err().disposition(),
                ("kernel-rejection", true, 1)
            );
        }
        assert_eq!(e.logical_root(&KVMap::new()), root);
        assert!(!e.environment().contains(&Name::from_components(["Branch"])));
    }
}

#[test]
fn a_match_resource_stop_is_not_a_kernel_rejection_or_partial_success() {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    let mut bound = limits();
    bound.kernel.steps = 1;
    let result = e.check_source_files(
        &[b"def f (b : Bool) : Nat := match b with | true => 1 | false => 0"],
        &KVMap::new(),
        SourceCheckLimits::new(bound),
    );
    match result {
        Ok(Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("expected a typed nonanswer: {other:?}"),
    }
    assert_eq!(e.logical_root(&KVMap::new()), root);
}

const VEC: &str = "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n";

#[test]
fn indexed_matches_compute_with_refined_constructor_results() {
    let result = check(&format!(
        "{VEC}def get {{A : Type}} (n : Nat) (xs : Vec A n) (fallback : A) : A := match xs with | .nil => fallback | .cons k x tail => x
def rebuild {{A : Type}} (n : Nat) (xs : Vec A n) : Vec A n := match xs with | .nil => Vec.nil | .cons k x tail => Vec.cons k x tail
theorem head_ok : get 1 (Vec.cons 0 7 Vec.nil) 9 = 7 := by rfl
theorem empty_ok : get 0 Vec.nil 9 = 9 := by rfl
theorem rebuild_ok : rebuild 1 (Vec.cons 0 7 Vec.nil) = Vec.cons 0 7 Vec.nil := by rfl"
    ));
    let Some(ConstantInfo::Defn(def)) = result
        .engine
        .environment()
        .find(&Name::from_components(["rebuild"]))
    else {
        panic!("checked indexed match");
    };
    assert!(constants(&def.value).contains(&Name::from_components(["Vec", "rec"])));
    assert_eq!(result.theorems, 3);
}

#[test]
fn indexed_matches_generalize_dependent_parameters_and_preserve_shadowing() {
    check(&format!(
        "{VEC}def select {{A : Type}} (n : Nat) (xs ys : Vec A n) : Vec A n := match xs with | .nil => ys | .cons k x tail => ys
theorem same (n : Nat) (xs : Vec Nat n) (h : n = n) : n = n := match xs with | .nil => h | .cons k h tail => by assumption
theorem self (n : Nat) (xs : Vec Nat n) (h : xs = xs) : xs = xs := match xs with | .nil => h | .cons k x tail => h
theorem selected : select 1 (Vec.cons 0 7 Vec.nil) (Vec.cons 0 9 Vec.nil) = Vec.cons 0 9 Vec.nil := by rfl"
    ));
}

#[test]
fn indexed_match_captures_and_whole_patterns_keep_their_actual_types() {
    check(&format!(
        "{VEC}def original (n : Nat) (xs : Vec Nat n) : Nat := match xs with | .nil => n | .cons k x tail => n
def patternShadow (n : Nat) (xs : Vec Nat n) : Nat := match xs with | .nil => n | .cons n x tail => n
def whole {{A : Type}} (n : Nat) (xs : Vec A n) : Vec A n := match xs with | .nil => Vec.nil | rest => rest
def captured (xs : Vec Nat 0) : Vec Nat 0 := match xs with | _ => xs
def bound (xs : Vec Nat 1) : Vec Nat 1 := match xs with | rest => rest
theorem original_ok : original 1 (Vec.cons 0 7 Vec.nil) = 1 := by rfl
theorem shadow_ok : patternShadow 1 (Vec.cons 0 7 Vec.nil) = 0 := by rfl
theorem whole_ok : whole 1 (Vec.cons 0 7 Vec.nil) = Vec.cons 0 7 Vec.nil := by rfl
theorem captured_ok : captured Vec.nil = Vec.nil := by rfl
theorem bound_ok : bound (Vec.cons 0 7 Vec.nil) = Vec.cons 0 7 Vec.nil := by rfl"
    ));
}

#[test]
fn indexed_match_generalization_clears_only_unneeded_old_locals() {
    let declarations = "def useProof (n : Nat) (h : n = n) : Nat := 0\nclass Choice (n : Nat) where\n value : Nat\ndef readChoice (n : Nat) [d : Choice n] : Nat := d.value\n";
    for (local, body) in [
        ("h : n = n", "useProof n (by assumption)"),
        ("d : Choice n", "readChoice n"),
    ] {
        let name = local.split_whitespace().next().unwrap();
        for keep in [false, true] {
            let binding = if keep {
                format!("let held := {name}; ")
            } else {
                String::new()
            };
            let source = format!(
                "{VEC}{declarations}def probe (n : Nat) (xs : Vec Nat n) ({local}) : Nat := {binding}match xs with | .nil => {body} | .cons k x tail => 0"
            );
            if keep {
                check(&source);
            } else {
                let e = engine();
                let root = e.logical_root(&KVMap::new());
                assert!(
                    e.check_source_files(
                        &[source.as_bytes()],
                        &KVMap::new(),
                        SourceCheckLimits::new(limits())
                    )
                    .is_err(),
                    "old local leaked: {source}"
                );
                assert_eq!(e.logical_root(&KVMap::new()), root);
            }
        }
    }
}

#[test]
fn ordinary_dictionaries_generalize_but_instance_binders_remain_fixed() {
    let declarations = "class Choice (n : Nat) where\n value : Nat\n";
    check(&format!(
        "{VEC}{declarations}def select (n : Nat) (xs : Vec Nat n) (d : Choice n) : Choice n := match xs with | .nil => inferInstance | .cons k x tail => inferInstance"
    ));
    let bad = format!(
        "{VEC}{declarations}def select (n : Nat) (xs : Vec Nat n) [d : Choice n] : Choice n := match xs with | .nil => inferInstance | .cons k x tail => inferInstance"
    );
    let e = engine();
    assert!(
        e.check_source_files(
            &[bad.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err()
    );
}

#[test]
fn ordinary_matches_never_offer_recursive_hypotheses_to_proof_search() {
    check(
        "theorem real (n : Nat) (h : 0 = 0) : 0 = 0 := match n with | .zero => rfl | .succ k => by assumption",
    );
    for source in [
        "theorem hidden (n : Nat) : 0 = 0 := match n with | .zero => rfl | .succ k => by assumption",
        "class Choice where\n value : Nat\ndef hidden (n : Nat) : Choice := match n with | .zero => { value := 7 } | .succ k => inferInstance",
    ] {
        let e = engine();
        let root = e.logical_root(&KVMap::new());
        assert!(
            e.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "anonymous induction hypothesis leaked: {source}"
        );
        assert_eq!(e.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn indexed_match_failures_are_atomic_and_recoverable() {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    let good = "def get (n : Nat) (xs : Vec Nat n) : Nat := match xs with | .nil => 0 | .cons k x tail => x\ntheorem good : get 1 (Vec.cons 0 7 Vec.nil) = 7 := by rfl";
    for bad in [
        "def bad (n : Nat) (xs : Vec Nat n) : Vec Nat n := match xs with | .nil => xs | .cons k x tail => xs",
        "def bad (n : Nat) (xs : Vec Nat n) : Vec Nat n := let saved := xs; match xs with | .nil => saved | .cons k x tail => saved",
        "def bad (xs : Vec Nat 0) : Nat := match xs with | .nil => 0 | .cons k x tail => 1",
        "def bad (n : Nat) (xs : Vec Nat n) : Nat := match xs with | .nil => 0 | .cons k x tail => (x : String)",
        "theorem bad (n : Nat) (xs : Vec Nat n) : n = 0 := match xs with | .nil => rfl | .cons k x tail => rfl",
        "def bad (n : Nat) (xs : Vec Nat n) : Nat := match xs with | .nil => 0 | .cons k x tail => bad k tail",
        "def bad : Nat := match (Vec.nil : Vec Nat 1) with | _ => 0",
    ] {
        let result = e.check_source_files(
            &[VEC.as_bytes(), bad.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        );
        assert!(result.is_err(), "{bad}\n{result:?}");
        assert_eq!(e.logical_root(&KVMap::new()), root);
        let recovered = e
            .check_source_files(
                &[VEC.as_bytes(), good.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(recovered.theorems, 1);
        assert!(!e.environment().contains(&Name::from_components(["Vec"])));
    }
}

#[test]
fn indexed_match_resource_stop_preserves_the_source_environment() {
    let e = engine();
    let prepared = e
        .check_source_files(
            &[VEC.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = prepared.logical_root(&KVMap::new());
    let source = b"def get (n : Nat) (xs : Vec Nat n) : Nat := match xs with | .nil => 0 | .cons k x tail => x";
    let mut bound = limits();
    bound.kernel.steps = 1;
    match prepared.check_source_files(&[source], &KVMap::new(), SourceCheckLimits::new(bound)) {
        Ok(Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("expected a typed nonanswer: {other:?}"),
    }
    assert_eq!(prepared.logical_root(&KVMap::new()), root);
    assert!(
        prepared
            .check_source_files(&[source], &KVMap::new(), SourceCheckLimits::new(limits()))
            .unwrap()
            .into_complete()
            .is_some()
    );
}
