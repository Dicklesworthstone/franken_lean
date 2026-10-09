//! Ordinary matches on admitted mutual data use the real mutual recursors.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
use fln_elab::{
    records::RecordBudget,
    source::scope::{SourceScope, elaborate_mutual_inductives},
};
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
const TREE: &[&str] = &[
    "inductive Tree (A : Type) where | node (value : A) (children : Forest A)",
    "inductive Forest (A : Type) where | nil | cons (head : Tree A) (tail : Forest A)",
];
fn with_families(families: &[&str]) -> (Engine, EngineAdmissionLimits) {
    let (engine, limits) = engine();
    let syntax: Vec<_> = families
        .iter()
        .map(|s| {
            fln_parse::parse_definition(s.as_bytes())
                .unwrap()
                .syntax()
                .clone()
        })
        .collect();
    let candidate = elaborate_mutual_inductives(
        &syntax,
        engine.environment(),
        limits.kernel,
        RecordBudget::default(),
        &SourceScope::default(),
    )
    .unwrap();
    (
        engine
            .admit_declaration(candidate, &KVMap::new(), limits)
            .unwrap()
            .into_complete()
            .unwrap()
            .engine,
        limits,
    )
}
fn check(tail: &str) {
    let (engine, limits) = with_families(TREE);
    engine
        .check_source_files(
            &[tail.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|e| panic!("{tail}: {e:?}"))
        .into_complete()
        .unwrap();
}
#[test]
fn selected_family_in_either_position_computes_through_both_checkers() {
    check(
        "def value (t : Tree Nat) : Nat := match t with | .node x xs => x\ndef empty (xs : Forest Nat) : Bool := match xs with | .nil => true | .cons x rest => false\ndef tree : Tree Nat := Tree.node 7 (@Forest.nil Nat)\ntheorem head : value tree = 7 := by rfl\ntheorem nilCase : empty (@Forest.nil Nat) = true := by rfl\ntheorem consCase : empty (Forest.cons tree (@Forest.nil Nat)) = false := by rfl",
    );
}
#[test]
fn nested_mutual_matches_retain_cross_family_fields() {
    check(
        "def next (t : Tree Nat) : Nat := match t with | .node x xs => match xs with | .nil => x | .cons t rest => match t with | .node y ys => y\ntheorem nested : next (Tree.node 1 (Forest.cons (Tree.node 9 (@Forest.nil Nat)) (@Forest.nil Nat))) = 9 := by rfl",
    );
}
#[test]
fn sibling_motives_support_data_functions_types_and_prop() {
    check(
        "def typeOf (t : Tree Nat) : Type := match t with | .node x xs => Nat\ndef funOf (t : Tree Nat) : Nat -> Nat := match t with | .node x xs => fun y => x\ntheorem proofOf (t : Tree Nat) : 7 = 7 := match t with | .node x xs => by rfl\ntheorem typeComputes : typeOf (Tree.node 2 (@Forest.nil Nat)) = Nat := by rfl\ntheorem funComputes : funOf (Tree.node 3 (@Forest.nil Nat)) 4 = 3 := by rfl",
    );
}
#[test]
fn function_valued_sibling_hypotheses_are_not_counted_as_pattern_fields() {
    let source = "def empty (xs : F) : Bool := match xs with | .nil => true | .cons x => false\ndef inspect (t : T) : Bool := match t with | .node f => empty (f 0)\ntheorem computes : inspect (T.node (fun x => F.nil)) = true := by rfl";
    let (engine, limits) = with_families(&[
        "inductive T where | node (children : Nat -> F)",
        "inductive F where | nil | cons (x : T)",
    ]);
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|e| panic!("{e:?}"))
        .into_complete()
        .unwrap();
}
#[test]
fn invalid_untaken_branches_missing_cases_and_false_proofs_still_fail() {
    for tail in [
        "def bad (xs : Forest Nat) : Nat := match xs with | .nil => 0",
        "def bad : Nat := match (@Forest.nil Nat) with | .nil => 0 | .cons x rest => true",
        "theorem bad (x : Tree Nat) : 0 = 1 := match x with | .node n xs => by rfl",
        "def bad (xs : Forest Nat) : Nat := match xs with | .nil => 0 | .nil => 1 | .cons x rest => 2",
    ] {
        let (engine, limits) = with_families(TREE);
        let root = engine.logical_root(&KVMap::new());
        assert!(
            engine
                .check_source_files(
                    &[tail.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits)
                )
                .is_err(),
            "{tail}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn neutral_sibling_motives_do_not_require_a_default_or_positive_result_universe() {
    let (engine, limits) = with_families(&[
        "inductive T.{u} (A : Sort u) : Type u where | node (value : A) (children : F A)",
        "inductive F.{u} (A : Sort u) : Type u where | nil | cons (head : T A) (tail : F A)",
    ]);
    let source = "def value.{u} (A : Sort u) (t : T A) : A := match t with | .node a children => a\ndef first.{u} (A : Sort u) (fallback : A) (xs : F A) : A := match xs with | .nil => fallback | .cons t rest => value A t\ntheorem computes : first Nat 4 (F.cons (T.node 9 (@F.nil Nat)) (@F.nil Nat)) = 9 := by rfl";
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|e| panic!("{e:?}"))
        .into_complete()
        .unwrap();
}

#[test]
fn dependent_targets_rebind_the_selected_major_without_capturing_a_sibling() {
    check(
        "def payload (t : Tree Nat) : Type := match t with | .node n children => Nat\ndef dependent (t : Tree Nat) : payload t := match t with | .node n children => n\ntheorem dependentComputes : dependent (Tree.node 5 (@Forest.nil Nat)) = (5 : Nat) := by rfl",
    );
}

#[test]
fn mutual_type_computation_exposes_function_binders_during_source_inference() {
    check(
        "def functionType (t : Tree Nat) : Type := match t with | .node n children => Nat -> Nat\n\
         def callback : functionType (Tree.node 3 (@Forest.nil Nat)) := fun x => x\n\
         def run (f : functionType (Tree.node 3 (@Forest.nil Nat))) : Nat := f 12\n\
         theorem computes : run callback = 12 := by rfl\n\
         def forestType (xs : Forest Nat) : Type := match xs with | .nil => Nat -> Nat | .cons t rest => Bool -> Bool\n\
         def other : forestType (Forest.cons (Tree.node 1 (@Forest.nil Nat)) (@Forest.nil Nat)) := fun b => b\n\
         theorem siblingComputes : other true = true := by rfl",
    );
}

#[test]
fn indexed_polymorphic_mutual_reduction_preserves_function_children_and_universes() {
    let (engine, limits) = with_families(&[
        "inductive T.{u} (A : Type u) : A -> Type u where | node (x : A) (children : Nat -> F A x) : T A x",
        "inductive F.{u} (A : Type u) : A -> Type u where | nil (x : A) : F A x | cons (x : A) (t : T A x) : F A x",
    ]);
    let source = "def functionType.{u} (A : Type u) (x : A) (t : T A x) : Type u := match t with | .node y children => A -> A\n\
                  def run.{u} (A : Type u) (x : A) (f : functionType A x (T.node x (fun n => F.nil x))) : A := f x\n\
                  theorem atNat : run Nat 7 (fun x => x) = 7 := by rfl\n\
                  theorem atType : run (Type) Nat (fun x => x) = Nat := by rfl";
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|e| panic!("{e:?}"))
        .into_complete()
        .unwrap();
}

#[test]
fn computed_mutual_function_types_do_not_accept_wrong_arguments_or_publish_a_prefix() {
    let (engine, limits) = with_families(TREE);
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let prefix = "def functionType (xs : Forest Nat) : Type := match xs with | .nil => Nat -> Nat | .cons t rest => Bool -> Bool\n";
    for body in [
        "def bad (f : functionType (@Forest.nil Nat)) : Nat := f true",
        "def bad (f : functionType (Forest.cons (Tree.node 3 (@Forest.nil Nat)) (@Forest.nil Nat))) : Bool := f 3",
        "theorem bad (f : functionType (@Forest.nil Nat)) : f 0 = f 1 := by rfl",
    ] {
        let source = format!("{prefix}{body}");
        assert!(
            engine
                .check_source_files(
                    &[source.as_bytes()],
                    &options,
                    SourceCheckLimits::new(limits)
                )
                .is_err(),
            "{source}"
        );
        assert!(
            !engine
                .environment()
                .contains(&fln::Name::from_components(["functionType"]))
        );
        assert_eq!(engine.logical_root(&options), root);
    }
}

#[test]
fn middle_family_and_empty_sibling_use_the_correct_minor_positions() {
    let (engine, limits) = with_families(&[
        "inductive A where | a (b : B)",
        "inductive B where | stop (n : Nat) | next (c : C)",
        "inductive C where | c (a : A)",
    ]);
    let source = "def middle (b : B) : Nat := match b with | .stop n => n | .next c => 0\ntheorem middleComputes : middle (B.stop 17) = 17 := by rfl\ndef last (c : C) : A := match c with | .c a => a\ntheorem lastComputes (a : A) : last (C.c a) = a := by rfl";
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|e| panic!("{e:?}"))
        .into_complete()
        .unwrap();
    let (engine, limits) = with_families(&[
        "inductive VoidA where",
        "inductive Holder where | hold (x : VoidA)",
    ]);
    let source = "def unwrap (x : Holder) : VoidA := match x with | .hold v => v\ntheorem unwrapComputes (v : VoidA) : unwrap (Holder.hold v) = v := by rfl";
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|e| panic!("{e:?}"))
        .into_complete()
        .unwrap();
}
