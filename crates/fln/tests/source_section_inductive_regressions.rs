//! Section-dependent families close through the ordinary dual-checker door.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};
use fln_core::expr::{BinderInfo, ExprNode};

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
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap()
        .engine
}
fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn binders(engine: &Engine, name: &str) -> Vec<(String, BinderInfo)> {
    let mut ty = engine
        .environment()
        .find(&n(name))
        .unwrap()
        .constant_val()
        .type_
        .clone();
    let mut result = Vec::new();
    while let ExprNode::ForallE {
        binder_name,
        binder_info,
        body,
        ..
    } = ty.node()
    {
        result.push((binder_name.to_display_string(), *binder_info));
        ty = body.clone();
    }
    result
}
fn names(engine: &Engine, name: &str) -> Vec<String> {
    binders(engine, name)
        .into_iter()
        .map(|(name, _)| name)
        .collect()
}
const CHAIN: &str = "section\nvariable (A : Type u) (unused : String)\ninductive Chain where\n  | nil\n  | cons (value : A) (tail : Chain)\nend\n";

#[test]
fn section_types_are_parameters_of_data_and_recursive_occurrences() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let e = checked(
        &base,
        &format!(
            "{CHAIN}
        def singleton (x : Nat) : Chain Nat := Chain.cons x Chain.nil
        def head (xs : Chain Nat) : Nat := match xs with
          | .nil => 0
          | .cons x tail => x
        theorem value : head (singleton 7) = 7 := by rfl"
        ),
    );
    assert_eq!(names(&e, "Chain"), ["A"]);
    assert_eq!(names(&e, "Chain.cons"), ["A", "value", "tail"]);
    assert!(e.environment().contains(&n("Chain.rec")));
    assert!(!e.environment().contains(&n("A")));
    assert_eq!(root, base.logical_root(&KVMap::new()));
}

#[test]
fn generalized_families_support_structural_recursion_and_induction() {
    checked(
        &engine(),
        &format!(
            "{CHAIN}
        def copy {{A : Type u}} (xs : Chain A) : Chain A := match xs with
          | .nil => Chain.nil
          | .cons x tail => Chain.cons x (copy tail)
        theorem copy_ok {{A : Type u}} (xs : Chain A) : copy xs = xs := by
          induction xs with
          | nil => rfl
          | cons x tail ih => simp only [copy, ih]"
        ),
    );
}

#[test]
fn type_dependencies_close_transitively_and_before_written_parameters() {
    let e = checked(
        &engine(),
        "section
        variable {A : Type u} (P : A -> Type v) (x : A) (unused : Bool)
        inductive Witness (marker : Nat) where
          | intro (evidence : P x)
        end
        def value : Witness (A := Nat) (fun a => Bool) 7 0 := Witness.intro true",
    );
    assert_eq!(names(&e, "Witness"), ["A", "P", "x", "marker"]);
    assert_eq!(binders(&e, "Witness")[0].1, BinderInfo::Implicit);
    let levels = &e
        .environment()
        .find(&n("Witness"))
        .unwrap()
        .constant_val()
        .level_params;
    assert!(levels.contains(&n("u")));
    assert!(levels.contains(&n("v")));
}

#[test]
fn index_domains_and_constructor_indices_capture_section_values() {
    let e = checked(
        &engine(),
        "section
        variable (A : Type) (chosen : A)
        inductive At : A -> Type where
          | intro : At chosen
        end
        def value : At Nat 7 7 := At.intro",
    );
    assert_eq!(names(&e, "At")[..2], ["A", "chosen"]);
    checked(
        &engine(),
        "section
        variable (A : Type u)
        inductive Vec : Nat -> Type u where
          | nil : Vec 0
          | cons (n : Nat) (x : A) (tail : Vec n) : Vec (Nat.succ n)
        end
        def two : Vec Nat 2 := Vec.cons 1 7 (Vec.cons 0 9 Vec.nil)
        theorem same : two = Vec.cons 1 7 (Vec.cons 0 9 Vec.nil) := by rfl",
    );
}

#[test]
fn shadowing_scope_exit_and_theorem_selections_do_not_change_data_parameters() {
    let e = checked(
        &engine(),
        "namespace Outer
        variable (A : Type u) (h : False)
        include h
        inductive Token (A : Type v) where | put (x : A)
        section
        variable (B : Type v)
        inductive Pair where | put (a : A) (b : B)
        end
        omit h
        inductive Box where | put (a : A)
        end Outer
        def token : Outer.Token Nat := Outer.Token.put 7
        def pair : Outer.Pair Nat Bool := Outer.Pair.put 3 true
        def box : Outer.Box Nat := Outer.Box.put 9",
    );
    assert_eq!(names(&e, "Outer.Token"), ["A"]);
    assert_eq!(names(&e, "Outer.Pair"), ["A", "B"]);
    assert_eq!(names(&e, "Outer.Box"), ["A"]);
    assert_eq!(
        e.environment()
            .find(&n("Outer.Token"))
            .unwrap()
            .constant_val()
            .level_params,
        [n("v")]
    );
}

const MUTUAL: &str = "section
variable {A : Type u} (B : Type v) (unused : Nat)
mutual
  inductive Tree (tag : Nat) where
    | leaf (value : A)
    | node (children : Forest tag)
  inductive Forest (label : Nat) where
    | nil (value : B)
    | cons (head : Tree label) (tail : Forest label)
end
end
";

#[test]
fn mutual_families_share_the_union_of_sibling_dependencies() {
    let e = checked(
        &engine(),
        &format!(
            "{MUTUAL}
        def forest : Forest (A := Nat) Bool 0 := Forest.cons (Tree.leaf 7) (Forest.nil true)
        def payload (tree : Tree (A := Nat) Bool 0) : Nat := match tree with
          | .leaf n => n
          | .node xs => 0
        theorem value : payload (Tree.leaf 7) = 7 := by rfl"
        ),
    );
    assert_eq!(names(&e, "Tree"), ["A", "B", "tag"]);
    assert_eq!(names(&e, "Forest"), ["A", "B", "tag"]);
    for name in ["Tree", "Forest", "Tree.rec", "Forest.rec"] {
        let info = e.environment().find(&n(name)).unwrap();
        assert!(info.constant_val().level_params.contains(&n("u")));
        assert!(info.constant_val().level_params.contains(&n("v")));
    }
}

#[test]
fn mutual_header_dependencies_and_indexed_recursion_keep_lexical_locals() {
    let e = checked(
        &engine(),
        "section
        variable (A : Type) (P : A -> Type)
        mutual
          inductive Tree (x : A) : Nat -> Type where
            | leaf (value : P x) : Tree x 0
            | node (n : Nat) (children : Forest x n) : Tree x (Nat.succ n)
          inductive Forest (y : A) : Nat -> Type where
            | nil : Forest y 0
            | cons (n : Nat) (head : Tree y n) (tail : Forest y n) : Forest y (Nat.succ n)
        end
        end
        def value : Tree Nat (fun x => Bool) 7 0 := Tree.leaf true",
    );
    assert_eq!(names(&e, "Tree")[..3], ["A", "P", "x"]);
    assert_eq!(names(&e, "Forest")[..3], ["A", "P", "x"]);
}

#[test]
fn malformed_ascriptions_negative_occurrences_and_wrong_indices_still_refuse() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "variable (A : Type)\ninductive Bad where | mk (a : A) (f : Bad -> Nat)",
        "variable (A : Type)\ninductive Bad where | mk (a : A) : (Bad : Prop)",
        "variable (A : Type)\ninductive Bad where | mk (a : A) (x : (let unused : String := 7; A))",
        "variable (A : Type)\nmutual\n inductive Bad where | mk (a : A) (f : Other -> Nat)\n inductive Other where | mk (x : Bad)\nend",
        "variable (A : Type)\nmutual\n inductive Bad where | mk (a : A)\n inductive Other where | mk : (Other : Prop)\nend",
        "variable (A : Type)\nmutual\n inductive Bad (x : A) where | mk\n inductive Other (x : (let unused : String := 7; A)) where | mk\nend",
        "variable (A : Type) (x : A)\ninductive At : A -> Type where | mk : At x\ndef bad : At Nat 7 8 := At.mk",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(root, base.logical_root(&KVMap::new()));
        assert!(!base.environment().contains(&n("Bad")));
    }
    checked(&base, CHAIN);
}

#[test]
fn exhaustion_does_not_become_admission_and_inputs_remain_reusable() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [CHAIN, MUTUAL] {
        let mut low = limits();
        low.admission.kernel = low.admission.kernel.narrowed(0, 32);
        match base.check_source_files(&[source.as_bytes()], &KVMap::new(), low) {
            Ok(Outcome::Inconclusive(_)) => {}
            Err(e) => assert!(
                matches!(e.disposition(), ("resource" | "inconclusive", false, 3)),
                "{e:?}"
            ),
            other => panic!("exhaustion is not a verdict: {other:?}"),
        }
        assert_eq!(root, base.logical_root(&KVMap::new()));
        checked(&base, source);
    }
}

#[test]
fn automatic_parameters_produce_the_same_checked_world_as_explicit_telescopes() {
    let base = engine();
    let section = checked(&base, CHAIN);
    let explicit = checked(
        &base,
        "inductive Chain (A : Type u) where | nil | cons (value : A) (tail : Chain A)",
    );
    assert_eq!(
        section.logical_root(&KVMap::new()),
        explicit.logical_root(&KVMap::new())
    );
    let section = checked(&base, MUTUAL);
    let explicit = checked(
        &base,
        "mutual
      inductive Tree {A : Type u} (B : Type v) (tag : Nat) where
        | leaf (value : A)
        | node (children : Forest (A := A) B tag)
      inductive Forest {A : Type u} (B : Type v) (label : Nat) where
        | nil (value : B)
        | cons (head : Tree (A := A) B label) (tail : Forest (A := A) B label)
    end",
    );
    assert_eq!(
        section.logical_root(&KVMap::new()),
        explicit.logical_root(&KVMap::new())
    );
}

#[test]
fn unused_sections_do_not_pollute_empty_or_independent_families() {
    let e = checked(
        &engine(),
        "section
        variable (A : Type u) [inh : Inhabited A] (x : A)
        inductive Empty : Type where
        inductive Bit where | zero | one
        end",
    );
    assert!(names(&e, "Empty").is_empty());
    assert!(names(&e, "Bit").is_empty());
    assert!(
        e.environment()
            .find(&n("Bit"))
            .unwrap()
            .constant_val()
            .level_params
            .is_empty()
    );
}

#[test]
fn checked_source_example_uses_the_same_public_entry_point() {
    checked(
        &engine(),
        include_str!("../../../examples/native_section_inductives.lean"),
    );
}
