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
// Members spell their shared parameters alike: the pin refuses differing spellings
// (`mutual_headers_are_refused_where_the_pin_refuses_them`). Both programs, with the
// uses below, are accepted at the pin (lean v4.32.0, 2026-10-06).
#[test]
fn shared_polymorphic_parameters_are_rebound_without_capture() {
    let e = admit(
        &[
            "inductive Tree.{u} (A : Type u) where | leaf (value : A) | node (children : Forest A)",
            "inductive Forest.{u} (A : Type u) where | nil | cons (head : Tree A) (tail : Forest A)",
        ],
        &SourceScope::default(),
    );
    check(
        &e,
        "def tree : Tree Nat := Tree.node (Forest.cons (Tree.leaf 7) Forest.nil)\ndef other : Forest Bool := Forest.cons (Tree.leaf true) Forest.nil",
    );
}
#[test]
fn dependent_shared_parameter_telescopes_align_by_identity() {
    let e = admit(
        &[
            "inductive Tree (A : Type) (P : A -> Type) where | leaf (x : A) (value : P x) | node (children : Forest A P)",
            "inductive Forest (A : Type) (P : A -> Type) where | nil | cons (head : Tree A P) (tail : Forest A P)",
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

const MUTUAL_FILE: &str = "mutual
  inductive Tree (A : Type) where | node (value : A) (children : Forest A)
  inductive Forest (A : Type) where | nil | cons (head : Tree A) (tail : Forest A)
end
";

const MUTUAL_PREDICATES: &str = "mutual
  inductive Even : Nat -> Prop where
    | zero : Even 0
    | succ (n : Nat) (h : Odd n) : Even (Nat.succ n)
  inductive Odd : Nat -> Prop where
    | succ (n : Nat) (h : Even n) : Odd (Nat.succ n)
end
";

#[test]
fn mutual_predicates_support_constructor_proofs_and_all_recursion_motives() {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    let source = format!(
        "{MUTUAL_PREDICATES}
theorem evenTwo : Even 2 := Even.succ 1 (Odd.succ 0 Even.zero)
theorem preserve (n : Nat) (h : Even n) : Even n :=
  @Even.rec (fun n _ => Even n) (fun n _ => Odd n)
    Even.zero (fun n h ih => Even.succ n ih) (fun n h ih => Odd.succ n ih) n h"
    );
    let checked = e
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("mutual predicate source: {error:?}"))
        .into_complete()
        .expect("both checkers admit predicates and their proofs");
    assert_eq!(checked.theorems, 2);
    for name in ["Even.rec", "Odd.rec"] {
        let Some(fln_env::constants::ConstantInfo::Rec(rec)) =
            checked.engine.environment().find(&n(name))
        else {
            panic!("missing mutual recursor {name}");
        };
        assert!(rec.base.level_params.is_empty());
        assert_eq!(rec.num_motives, 2);
        assert!(!rec.k);
    }
    assert_eq!(e.logical_root(&KVMap::new()), root);
}

#[test]
fn mutual_predicate_fields_may_live_in_higher_universes() {
    check(
        &engine(),
        "universe u
mutual
  inductive Claim (A : Sort u) : Prop where
    | datum (x : A)
    | other (h : Other A)
  inductive Other (A : Sort u) : Prop where
    | claim (h : Claim A)
end
theorem carry (A : Sort u) (x : A) : Other A := Other.claim (Claim.datum x)
theorem large : Other (Type 2) := Other.claim (Claim.datum (Type 1))",
    );
}

const POSSIBLY_PROP: &str = "universe u
mutual
  inductive Reach (A : Sort u) : Sort u where
    | here (value : A)
    | next (step : Step A)
  inductive Step (A : Sort u) : Sort u where
    | back (reach : Reach A)
end
";

#[test]
fn source_rejects_possibly_zero_result_universes_under_the_pins_default_options() {
    // The kernel permits these blocks, but the pinned source elaborator's
    // default bootstrap.inductiveCheckResultingUniverse check refuses them.
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    let refused = e
        .check_source_files(
            &[POSSIBLY_PROP.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_err();
    assert_eq!(
        refused.disposition(),
        ("elaboration", false, 1),
        "{refused:?}"
    );
    assert_eq!(e.logical_root(&KVMap::new()), root);
    assert!(!e.environment().contains(&n("Reach")));
}

#[test]
fn mutual_predicates_refuse_mixed_sorts_and_large_elimination_atomically() {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    let mixed = candidate(
        &e,
        &[
            "inductive A : Prop where | mk (b : B)",
            "inductive B : Type where | mk",
        ],
        &SourceScope::default(),
        RecordBudget::default(),
    );
    assert!(matches!(
        mixed,
        Err(fln_elab::NatDefinitionElabError::Inference(
            fln_elab::source::SourceInferenceError::Inductive(
                fln_elab::inductive::InductiveError::UnsupportedSort
            )
        ))
    ));
    let source = format!(
        "{MUTUAL_PREDICATES}
def reveal (n : Nat) (h : Even n) : Nat :=
  @Even.rec (fun _ _ => Nat) (fun _ _ => Nat)
    0 (fun n h ih => ih) (fun n h ih => ih) n h"
    );
    let refused = e
        .check_source_files(
            &[b"def beforeMutual := 7", source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_err();
    assert_eq!(
        refused.disposition(),
        ("elaboration", false, 1),
        "{refused:?}"
    );
    assert_eq!(e.logical_root(&KVMap::new()), root);
    for name in ["beforeMutual", "Even", "reveal"] {
        assert!(!e.environment().contains(&n(name)));
    }
    check(&e, MUTUAL_PREDICATES);
}

#[test]
fn source_files_admit_mutual_groups_before_using_their_eliminators() {
    let e = engine();
    let source = format!("{MUTUAL_FILE}
def value (t : Tree Nat) : Nat := match t with | .node n xs => n
def tree : Tree Nat := Tree.node 7 (@Forest.nil Nat)
theorem computed : value tree = 7 := by rfl
theorem keep (t : Tree Nat) (P : Tree Nat -> Prop) (h : P t) : P t := by cases t with | node n xs => exact h");
    let root = e.logical_root(&KVMap::new());
    let checked = e
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(checked.commands, 5);
    assert_eq!(checked.theorems, 2);
    for name in [
        "Tree",
        "Forest",
        "Tree.rec",
        "Forest.rec",
        "computed",
        "keep",
    ] {
        assert!(checked.engine.environment().contains(&n(name)), "{name}");
    }
    assert_eq!(e.logical_root(&KVMap::new()), root);
    let repeated = e
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(checked.result_logical_root, repeated.result_logical_root);
}

#[test]
fn groups_preserve_namespace_and_universe_scope_and_single_member_groups_work() {
    let e = engine();
    let source = "namespace Demo
universe u
mutual
  inductive Tree (A : Type u) where | node (value : A) (xs : Forest A)
  inductive Forest (A : Type u) where | nil | cons (t : Tree A)
end
def tree : Tree Nat := Tree.node 7 (@Forest.nil Nat)
end Demo
mutual
  inductive Flag where | off | on
end
def flag : Flag := Flag.on
def outside : Demo.Tree Nat := Demo.tree";
    let checked = e
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    for name in [
        "Demo.Tree",
        "Demo.Forest",
        "Demo.tree",
        "Flag",
        "flag",
        "outside",
    ] {
        assert!(checked.engine.environment().contains(&n(name)), "{name}");
    }
    assert!(!checked.engine.environment().contains(&n("Tree")));
}

#[test]
fn source_group_failure_never_publishes_a_family_or_a_prior_file() {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    for group in [
        "mutual inductive A where | mk (f : B -> Nat) inductive B where | mk (a : A) end",
        "mutual inductive A (T : Type) where | mk (b : B Nat) inductive B (T : Type) where | mk end",
        "mutual inductive A where | mk inductive A where | other end",
        "mutual inductive Nat where | fake inductive B where | mk end",
        "mutual inductive A where | mk inductive B where | mk : Nat end",
        "mutual inductive A where | mk inductive B where | mk",
    ] {
        let result = e.check_source_files(
            &[b"def prefix := 7", group.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        );
        assert!(result.is_err(), "{group}: {result:?}");
        assert_eq!(e.logical_root(&KVMap::new()), root);
        assert!(!e.environment().contains(&n("prefix")));
        assert!(!e.environment().contains(&n("A")));
    }
    check(&e, MUTUAL_FILE);
}

#[test]
fn mutual_source_budget_stops_are_nonanswers_with_reusable_inputs() {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    let mut low = SourceCheckLimits::new(limits());
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    match e.check_source_files(&[MUTUAL_FILE.as_bytes()], &KVMap::new(), low) {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("exhaustion is not a verdict: {other:?}"),
    }
    assert_eq!(e.logical_root(&KVMap::new()), root);
    check(&e, MUTUAL_FILE);
}

#[test]
fn source_module_cache_reuses_and_invalidates_the_whole_mutual_unit() {
    use fln::SourceModuleInput;
    use fln::source_check::modules::{
        SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
    };
    let mut session = SourceModuleSession::new(
        engine(),
        KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        SourceModuleCacheLimits::default(),
    );
    let main = n("Main");
    let data = n("Data");
    let text = "import Data\ndef sample : Tree Nat := Tree.node 7 (@Forest.nil Nat)\ntheorem valid : sample = Tree.node 7 (@Forest.nil Nat) := by rfl";
    let files = [
        SourceModuleInput {
            name: &main,
            source: text.as_bytes(),
        },
        SourceModuleInput {
            name: &data,
            source: MUTUAL_FILE.as_bytes(),
        },
    ];
    let cold = session
        .check_with_cancel(&files, &main, None)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((cold.reused_modules, cold.elaborated_modules), (0, 2));
    let warm = session
        .check_with_cancel(&files, &main, None)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (2, 0));
    assert_eq!(
        cold.checked.checked.result_logical_root,
        warm.checked.checked.result_logical_root
    );
    let invalid = [files[0], SourceModuleInput { name: &data, source: b"mutual inductive Tree where | mk (f : Forest -> Nat) inductive Forest where | mk end" }];
    assert!(session.check_with_cancel(&invalid, &main, None).is_err());
    let recovered = session
        .check_with_cancel(&files, &main, None)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(recovered.reused_modules, 2);
    assert_eq!(
        cold.checked.checked.result_logical_root,
        recovered.checked.checked.result_logical_root
    );
    let revised = format!("{MUTUAL_FILE}\ndef changed : Nat := 9");
    let revised_files = [
        files[0],
        SourceModuleInput {
            name: &data,
            source: revised.as_bytes(),
        },
    ];
    let changed = session
        .check_with_cancel(&revised_files, &main, None)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((changed.reused_modules, changed.elaborated_modules), (0, 2));
    assert_ne!(
        changed.checked.checked.result_logical_root,
        cold.checked.checked.result_logical_root
    );
}

/// The pin's header checks across a `mutual` block, each refused with its own words.
/// Every program was run headerless at the pin (lean v4.32.0) on 2026-10-06, and each
/// wording is its first error, verbatim. The order is the pin's: universe names, then the
/// parameter count over every member, then each later member's parameters (binder
/// annotation before name) against the first's.
const MUTUAL_HEADERS_REFUSED: &[(&str, &str)] = &[
    (
        "mutual\ninductive Tree (A : Type) where\n  | node (value : A) (children : Forest A)\ninductive Forest (B : Type) where\n  | nil\n  | cons (head : Tree B) (tail : Forest B)\nend\n",
        "Invalid mutually inductive types: Parameter names `B` and `A` differ but were expected to match",
    ),
    (
        "mutual\ninductive Tree (A : Type) (n : Nat) where\n  | node (children : Forest A n)\ninductive Forest (A : Type) (m : Nat) where\n  | nil\nend\n",
        "Invalid mutually inductive types: Parameter names `m` and `n` differ but were expected to match",
    ),
    (
        "mutual\ninductive Tree (A : Type) [i : Inhabited A] where\n  | node (value : A) (children : Forest A)\ninductive Forest (A : Type) [j : Inhabited A] where\n  | nil\n  | cons (head : Tree A) (tail : Forest A)\nend\n",
        "Invalid mutually inductive types: Parameter names `j` and `i` differ but were expected to match",
    ),
    (
        "mutual\ninductive X (A : Type) where\n  | x (y : Y A)\ninductive Y (A : Type) where\n  | y (z : Z A)\n  | stop\ninductive Z (C : Type) where\n  | z (x : X C)\nend\n",
        "Invalid mutually inductive types: Parameter names `C` and `A` differ but were expected to match",
    ),
    (
        "mutual\ninductive Tree (A : Type) (P : A -> Type) where | leaf (x : A) (value : P x) | node (children : Forest A P)\ninductive Forest (B : Type) (Q : B -> Type) where | nil | cons (head : Tree B Q) (tail : Forest B Q)\nend\n",
        "Invalid mutually inductive types: Parameter names `B` and `A` differ but were expected to match",
    ),
    (
        "mutual\ninductive Tree (A : Type) where\n  | node (value : A) (children : Forest A)\ninductive Forest {A : Type} where\n  | nil\n  | cons (head : Tree A) (tail : @Forest A)\nend\n",
        "Invalid mutually inductive types: Binder annotations for parameter `A` must match",
    ),
    (
        "mutual\ninductive Tree (A : Type) where\n  | node (children : Forest A)\ninductive Forest {B : Type} where\n  | nil\nend\n",
        "Invalid mutually inductive types: Binder annotations for parameter `B` must match",
    ),
    (
        "mutual\ninductive Tree (A : Type) where\n  | node (value : A) (children : Forest A)\ninductive Forest (A : Type) (n : Nat) where\n  | nil\nend\n",
        "Invalid mutually inductive types: `Forest` has 2 parameter(s), but the preceding type `Tree` has 1\n\nNote: All inductive types declared in the same `mutual` block must have the same parameters",
    ),
    (
        "mutual\ninductive Tree (A : Type) where\n  | node (children : Forest A)\ninductive Forest (B : Type) (n : Nat) where\n  | nil\nend\n",
        "Invalid mutually inductive types: `Forest` has 2 parameter(s), but the preceding type `Tree` has 1",
    ),
    (
        "namespace Ns\nmutual\ninductive Tree (A : Type) where\n  | node (children : Forest A)\ninductive Forest (A : Type) (n : Nat) where\n  | nil\nend\nend Ns\n",
        "Invalid mutually inductive types: `Forest` has 2 parameter(s), but the preceding type `Tree` has 1",
    ),
    (
        "mutual\ninductive Tree.{u} (A : Type u) where\n  | node (value : A) (children : Forest A)\ninductive Forest.{v} (A : Type v) where\n  | nil\n  | cons (head : Tree A) (tail : Forest A)\nend\n",
        "Universe parameter mismatch in mutually inductive types: `Forest` has universe parameters\n  `v`\nbut the preceding declaration `Tree` has\n  `u`\n\nNote: All inductive declarations in the same `mutual` block must have the same universe level parameters",
    ),
    (
        "mutual\ninductive Tree.{u, v} (A : Type u) (B : Type v) where\n  | node (value : A) (children : Forest A B)\ninductive Forest.{v, u} (A : Type u) (B : Type v) where\n  | nil\nend\n",
        "`Forest` has universe parameters\n  `u`, `v`\nbut the preceding declaration `Tree` has\n  `v`, `u`\n",
    ),
    (
        "mutual\ninductive Tree.{u} (A : Type u) where\n  | node (value : A) (children : Forest A)\ninductive Forest (A : Type u) where\n  | nil\n  | cons (head : Tree A) (tail : Forest A)\nend\n",
        "`Forest` has universe parameters\n  \nbut the preceding declaration `Tree` has\n  `u`\n",
    ),
    (
        "mutual\ninductive Tree.{u} (A : Type u) where\n  | node (children : Forest A)\ninductive Forest.{v} (B : Type v) where\n  | nil\nend\n",
        "`Forest` has universe parameters\n  `v`\nbut the preceding declaration `Tree` has\n  `u`\n",
    ),
    (
        "universe w x\nmutual\ninductive Tree.{u} (A : Type u) where\n  | node (value : A) (children : Forest A)\ninductive Forest.{v} (A : Type v) where\n  | nil\nend\n",
        "`Forest` has universe parameters\n  `v`, `x`, `w`\nbut the preceding declaration `Tree` has\n  `u`, `x`, `w`\n",
    ),
];

/// Accepted at the pin (exit 0, run as above): the controls a too-strict check would
/// refuse. Anonymous instance binders get generated names on both sides and are exempt
/// (lean4#4310); index names are not parameters; auto-bound names agree by spelling.
const MUTUAL_HEADERS_ACCEPTED: &[&str] = &[
    "mutual\ninductive Tree (A : Type) where\n  | node (value : A) (children : Forest A)\ninductive Forest (A : Type) where\n  | nil\n  | cons (head : Tree A) (tail : Forest A)\nend\n",
    "mutual\ninductive Tree (A : Type) [Inhabited A] where\n  | node (value : A) (children : Forest A)\ninductive Forest (A : Type) [Inhabited A] where\n  | nil\n  | cons (head : Tree A) (tail : Forest A)\nend\n",
    "mutual\ninductive Tree.{u} (A : Type u) where\n  | node (value : A) (children : Forest A)\ninductive Forest.{u} (A : Type u) where\n  | nil\n  | cons (head : Tree A) (tail : Forest A)\nend\n",
    "mutual\ninductive Tree (A : Type u) where\n  | node (value : A) (children : Forest A)\ninductive Forest (A : Type u) where\n  | nil\n  | cons (head : Tree A) (tail : Forest A)\nend\n",
    "mutual\ninductive Tree : Nat \u{2192} Type where\n  | node (n : Nat) (children : Forest n) : Tree n\ninductive Forest : (m : Nat) \u{2192} Type where\n  | nil : Forest 0\nend\n",
];

#[test]
fn mutual_headers_are_refused_where_the_pin_refuses_them() {
    for (source, wording) in MUTUAL_HEADERS_REFUSED {
        let e = engine();
        let root = e.logical_root(&KVMap::new());
        let error = e
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect_err(source);
        let text = error.to_string();
        assert!(
            text.contains(wording),
            "{source}\nmust be refused as the pin refuses it, with\n{wording}\nbut was refused with\n{text}"
        );
        let (class, authority, _) = error.disposition();
        assert_eq!(
            (class, authority),
            ("elaboration", false),
            "{source}: {text}"
        );
        assert_eq!(e.logical_root(&KVMap::new()), root, "{source}");
    }
    for source in MUTUAL_HEADERS_ACCEPTED {
        check(&engine(), source);
    }
}
