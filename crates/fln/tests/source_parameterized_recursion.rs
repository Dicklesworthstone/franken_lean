//! Generic recursive families use the ordinary source and both checker paths.
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
        .unwrap()
}
const SEQ: &str = "inductive Seq (A : Type) where | nil | cons (head : A) (tail : Seq A)\n";

#[test]
fn generic_lists_are_admitted_and_compute_with_their_real_recursor() {
    let result = check(&format!(
        "{SEQ}\
        def length {{A : Type}} (xs : Seq A) : Nat := match xs with | .nil => 0 | .cons x tail => length tail + 1\n\
        def xs : Seq Nat := Seq.cons 7 (Seq.cons 9 Seq.nil)\n\
        theorem length_ok : length xs = 2 := by rfl\n\
        theorem empty_ok : length (Seq.nil : Seq Bool) = 0 := by rfl"
    ));
    assert_eq!(result.commands, 5);
    assert_eq!(result.theorems, 2);
    assert!(
        result
            .engine
            .environment()
            .contains(&Name::from_components(["Seq", "rec"]))
    );
}

#[test]
fn generic_list_copy_has_an_open_induction_proof() {
    check(&format!(
        "{SEQ}\
        def copy {{A : Type}} (xs : Seq A) : Seq A := match xs with | .nil => Seq.nil | .cons x tail => Seq.cons x (copy tail)\n\
        theorem copy_ok {{A : Type}} (xs : Seq A) : copy xs = xs := by\n  induction xs with\n  | nil => rfl\n  | cons x tail ih => simp only [copy, ih]"
    ));
}

#[test]
fn generic_append_generalizes_the_trailing_list_argument() {
    check(&format!(
        "{SEQ}\
        def append {{A : Type}} (xs : Seq A) (ys : Seq A) : Seq A := match xs with | .nil => ys | .cons x tail => Seq.cons x (append tail ys)\n\
        theorem right_nil {{A : Type}} (xs : Seq A) : append xs Seq.nil = xs := by\n  induction xs with\n  | nil => rfl\n  | cons x tail ih => simp only [append, ih]\n\
        theorem example : append (Seq.cons 1 Seq.nil) (Seq.cons 2 Seq.nil) = Seq.cons 1 (Seq.cons 2 Seq.nil) := by rfl"
    ));
}

#[test]
fn generic_binary_trees_supply_both_induction_hypotheses() {
    check(
        "inductive Tree (A : Type) where | leaf (value : A) | fork (left right : Tree A)\n\
        def mirror {A : Type} (tree : Tree A) : Tree A := match tree with | .leaf value => Tree.leaf value | .fork left right => Tree.fork (mirror right) (mirror left)\n\
        theorem twice {A : Type} (tree : Tree A) : mirror (mirror tree) = tree := by\n  induction tree with\n  | leaf value => rfl\n  | fork left right hl hr => simp only [mirror, hl, hr]",
    );
}

#[test]
fn multiple_uniform_parameters_keep_their_order_in_all_rules() {
    check(
        "inductive Tree (A B : Type) where | left (value : A) | right (value : B) | fork (l r : Tree A B)\n\
        def copy {A B : Type} (tree : Tree A B) : Tree A B := match tree with | .left x => Tree.left x | .right y => Tree.right y | .fork l r => Tree.fork (copy l) (copy r)\n\
        theorem copy_ok {A B : Type} (tree : Tree A B) : copy tree = tree := by\n  induction tree with\n  | left x => rfl\n  | right y => rfl\n  | fork l r hl hr => simp only [copy, hl, hr]\n\
        def example : Tree Nat Bool := Tree.fork (Tree.left 11) (Tree.right true)",
    );
}

#[test]
fn dependent_parameter_types_and_constructor_fields_remain_scoped() {
    check(
        "inductive Tagged (A : Type) (tag : A) where | nil | cons (value : A) (tail : Tagged A tag)\n\
        def size {A : Type} {tag : A} (xs : Tagged A tag) : Nat := match xs with | .nil => 0 | .cons value tail => size tail + 1\n\
        theorem example : size (Tagged.cons 9 (Tagged.nil : Tagged Nat 7)) = 1 := by rfl",
    );
    check(
        "inductive Payloads (A : Type) (P : A -> Type) where | nil | cons (x : A) (value : P x) (tail : Payloads A P)\n\
        def count {A : Type} {P : A -> Type} (xs : Payloads A P) : Nat := match xs with | .nil => 0 | .cons x value tail => count tail + 1\n\
        theorem example : count (Payloads.cons 7 true (Payloads.nil : Payloads Nat (fun n => Bool))) = 1 := by rfl",
    );
}

#[test]
fn generic_families_keep_universe_and_positivity_refusals() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "inductive Bad (A : Type) : Type where | nil | cons (large : Type) (tail : Bad A)",
        "inductive Bad (A : Type) where | nil | cons (consume : Bad A -> Nat)",
        "inductive Bad (A : Type) where | nil | cons (tail : Bad Nat)",
        "inductive Bad (A B : Type) where | nil | cons (tail : Bad B A)",
    ] {
        assert!(
            !matches!(
                base.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits())
                ),
                Ok(Outcome::Complete(_))
            ),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn false_generic_proofs_and_late_failures_never_publish_a_prefix() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for proof in [
        "theorem bad : Seq.cons 1 Seq.nil = Seq.cons 2 Seq.nil := by rfl",
        "theorem bad {A : Type} (xs : Seq A) : 1 = 2 := by induction xs with | nil => rfl | cons x tail ih => rfl",
    ] {
        let error = base
            .check_source_files(
                &[SEQ.as_bytes(), proof.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .unwrap_err();
        assert_eq!(
            error.disposition(),
            ("kernel-rejection", true, 1),
            "{error:?}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&Name::from_components(["Seq"])));
    }
    check(&format!(
        "{SEQ}theorem recovery : (Seq.nil : Seq Nat) = Seq.nil := by rfl"
    ));
}

#[test]
fn generic_collection_example_proves_composition_associativity_and_involution() {
    let result = check(include_str!(
        "../../../examples/native_parameterized_recursion.lean"
    ));
    assert_eq!(result.commands, 14);
    assert_eq!(result.theorems, 7);
}
