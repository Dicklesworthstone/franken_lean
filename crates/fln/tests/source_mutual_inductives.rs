//! Mutual source families are candidates for the real dual-checker authority.
#![forbid(unsafe_code)]
use fln::{Budget, Declaration, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_elab::{
    records::RecordBudget,
    source::scope::{SourceScope, elaborate_mutual_inductives},
};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn candidate(
    e: &Engine,
    source: &[&str],
    scope: &SourceScope,
    budget: RecordBudget,
) -> Result<Declaration, fln_elab::NatDefinitionElabError> {
    let parsed: Vec<_> = source
        .iter()
        .map(|s| {
            fln_parse::parse_definition(s.as_bytes())
                .unwrap()
                .syntax()
                .clone()
        })
        .collect();
    elaborate_mutual_inductives(&parsed, e.environment(), limits().kernel, budget, scope)
}
fn admit(source: &[&str], scope: &SourceScope) -> Engine {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    let decl = candidate(&e, source, scope, RecordBudget::default())
        .unwrap_or_else(|e| panic!("{source:?}: {e:?}"));
    let result = e
        .admit_declaration(decl, &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source:?}: {e:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(e.logical_root(&KVMap::new()), root);
    result.engine
}
fn check(e: &Engine, source: &str) {
    e.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|e| panic!("{source}: {e:?}"))
    .into_complete()
    .unwrap();
}
fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
}

#[test]
fn forward_references_generate_both_families_and_reusable_constructors() {
    let e = admit(
        &[
            "inductive Tree where | leaf (n : Nat) | node (children : Forest)",
            "inductive Forest where | nil | cons (head : Tree) (tail : Forest)",
        ],
        &SourceScope::default(),
    );
    for name in [
        "Tree",
        "Forest",
        "Tree.leaf",
        "Tree.node",
        "Forest.nil",
        "Forest.cons",
        "Tree.rec",
        "Forest.rec",
    ] {
        assert!(e.environment().contains(&n(name)), "{name}");
    }
    check(
        &e,
        "def tree : Tree := Tree.node (Forest.cons (Tree.leaf 7) Forest.nil)\ntheorem good : tree = Tree.node (Forest.cons (Tree.leaf 7) Forest.nil) := by rfl",
    );
}
#[test]
fn shared_polymorphic_parameters_are_rebound_without_capture() {
    let e = admit(
        &[
            "inductive Tree.{u} (A : Type u) where | leaf (value : A) | node (children : Forest A)",
            "inductive Forest.{u} (B : Type u) where | nil | cons (head : Tree B) (tail : Forest B)",
        ],
        &SourceScope::default(),
    );
    check(
        &e,
        "def tree : Tree Nat := Tree.node (Forest.cons (Tree.leaf 7) Forest.nil)\ndef other : Forest Bool := Forest.cons (Tree.leaf true) Forest.nil",
    );
}
#[test]
fn dependent_shared_parameter_telescopes_align_by_identity_not_spelling() {
    let e = admit(
        &[
            "inductive Tree (A : Type) (P : A -> Type) where | leaf (x : A) (value : P x) | node (children : Forest A P)",
            "inductive Forest (B : Type) (Q : B -> Type) where | nil | cons (head : Tree B Q) (tail : Forest B Q)",
        ],
        &SourceScope::default(),
    );
    check(
        &e,
        "def forest : Forest Nat (fun x => Bool) := Forest.cons (Tree.leaf 1 true) Forest.nil",
    );
}
#[test]
fn indexed_and_function_recursive_families_reach_both_checkers() {
    for source in [
        vec![
            "inductive Tree (A : Type) : A -> Type where | node (x : A) (children : Forest A x) : Tree A x",
            "inductive Forest (A : Type) : A -> Type where | nil (x : A) : Forest A x | cons (x : A) (head : Tree A x) (tail : Forest A x) : Forest A x",
        ],
        vec![
            "inductive Tree where | node (children : Nat -> Forest)",
            "inductive Forest where | nil | cons (head : Tree) (tail : Forest)",
        ],
    ] {
        admit(&source, &SourceScope::default());
    }
}
#[test]
fn namespaces_three_families_and_empty_members_share_one_block() {
    let scope = SourceScope {
        namespace: n("Demo"),
        ..SourceScope::default()
    };
    let e = admit(
        &[
            "inductive Tree where | node (children : Forest)",
            "inductive Forest where | nil | cons (head : Tree) (tail : Forest)",
            "inductive Void : Type where",
        ],
        &scope,
    );
    for name in ["Demo.Tree", "Demo.Forest", "Demo.Void", "Demo.Void.rec"] {
        assert!(e.environment().contains(&n(name)));
    }
    check(
        &e,
        "def value : Demo.Tree := Demo.Tree.node Demo.Forest.nil",
    );
}
#[test]
fn inferred_result_universe_is_shared_even_when_a_later_member_raises_it() {
    let e = admit(
        &[
            "inductive Tree where | node (children : Forest)",
            "inductive Forest where | package (A : Type) (value : A) : Forest | cons (head : Tree) : Forest",
        ],
        &SourceScope::default(),
    );
    check(&e, "def value : Tree := Tree.node (Forest.package Nat 7)");
}
#[test]
fn negative_nonuniform_and_malformed_source_never_install_a_prefix() {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    for source in [
        vec![
            "inductive Tree where | bad (f : Forest -> Nat)",
            "inductive Forest where | nil | back (t : Tree)",
        ],
        vec![
            "inductive Tree (A : Type) where | bad (f : Forest Nat)",
            "inductive Forest (A : Type) where | nil",
        ],
        vec![
            "inductive Tree (A : Type) where | bad (f : Forest A)",
            "inductive Forest {A : Type} where | nil",
        ],
        vec![
            "inductive Tree where | bad : Forest",
            "inductive Forest where | nil",
        ],
        vec![
            "inductive Tree where | node (f : Forest)",
            "inductive Forest where | nil : (Forest : Prop)",
        ],
        vec![
            "inductive Tree : Type where | node (f : Forest)",
            "inductive Forest : Type where | bad (A : Type)",
        ],
        vec![
            "inductive Tree where | node (f : Forest)",
            "inductive Tree where | leaf",
        ],
    ] {
        let result = candidate(
            &e,
            &source,
            &SourceScope::default(),
            RecordBudget::default(),
        );
        if let Ok(decl) = result {
            assert!(
                e.admit_declaration(decl, &KVMap::new(), limits()).is_err(),
                "{source:?}"
            );
        }
        assert_eq!(e.logical_root(&KVMap::new()), root);
        assert!(!e.environment().contains(&n("Tree")));
    }
}
#[test]
fn constructor_collisions_and_resource_stops_leave_the_original_engine_reusable() {
    let e = engine();
    let source = [
        "inductive Tree where | node (f : Forest)",
        "inductive Forest where | nil",
    ];
    assert!(
        candidate(
            &e,
            &source,
            &SourceScope::default(),
            RecordBudget {
                max_nodes: 0,
                ..RecordBudget::default()
            }
        )
        .is_err()
    );
    assert!(
        candidate(
            &e,
            &source,
            &SourceScope::default(),
            RecordBudget {
                max_binders: 1,
                ..RecordBudget::default()
            }
        )
        .is_err()
    );
    let base = e
        .check_source_files(
            &[b"def Forest.nil := 0"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = base.logical_root(&KVMap::new());
    let decl = candidate(
        &base,
        &source,
        &SourceScope::default(),
        RecordBudget::default(),
    )
    .unwrap();
    assert!(
        base.admit_declaration(decl, &KVMap::new(), limits())
            .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    admit(&source, &SourceScope::default());
}
