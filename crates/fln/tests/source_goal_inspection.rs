//! Native cursor observations never admit the unfinished declaration.
#![forbid(unsafe_code)]
use fln::source_check::inspect::{ObservationKind, SourceObservation};
use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits, SourceModuleInput,
};

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn session() -> SourceModuleSession {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let base = Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    SourceModuleSession::new(
        base,
        KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(admission)),
        SourceModuleCacheLimits::default(),
    )
}
fn observe(
    source: &str,
    at: usize,
    kind: ObservationKind,
) -> fln::source_check::inspect::SourceInspection {
    let module = name("Main");
    session()
        .inspect(
            &[SourceModuleInput {
                name: &module,
                source: source.as_bytes(),
            }],
            &module,
            at,
            kind,
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap()
}
fn goals(
    result: fln::source_check::inspect::SourceInspection,
) -> Vec<fln::source_check::inspect::ObservedGoal> {
    assert!(
        !result
            .prefix
            .checked
            .checked
            .engine
            .environment()
            .contains(&name("pending"))
    );
    let Some(SourceObservation::Goals { goals, .. }) = result.observation else {
        panic!("expected live goals")
    };
    goals
}
#[test]
fn empty_by_is_an_observable_unsolved_proof_not_an_admitted_theorem() {
    let source = "theorem pending (P : Prop) (h : P) : P := by";
    let found = goals(observe(source, source.len(), ObservationKind::Goals));
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].locals.len(), 2);
    let h = found[0].locals.find_by_user_name(&name("h")).unwrap();
    assert_eq!(found[0].target, h.type_);
    let module = name("Main");
    assert!(
        session()
            .check(
                &[SourceModuleInput {
                    name: &module,
                    source: source.as_bytes()
                }],
                &module
            )
            .is_err()
    );
}
#[test]
fn intro_and_constructor_produce_real_locals_and_multiple_goals() {
    let source = "theorem pending (P Q : Prop) : P -> Q -> P ∧ Q := by\n  intro hp hq\n  constructor\n  exact hp\n  exact hq";
    let found = goals(observe(
        source,
        source.find("exact hp").unwrap(),
        ObservationKind::Goals,
    ));
    assert_eq!(found.len(), 2);
    assert_eq!(
        found[0]
            .locals
            .find_by_user_name(&name("hp"))
            .unwrap()
            .type_,
        found[0].target
    );
    assert_eq!(
        found[1]
            .locals
            .find_by_user_name(&name("hq"))
            .unwrap()
            .type_,
        found[1].target
    );
}
#[test]
fn solved_proof_has_empty_goals_but_no_published_theorem() {
    let source = "theorem pending (P : Prop) (h : P) : P := by exact h";
    assert!(goals(observe(source, source.len(), ObservationKind::Goals)).is_empty());
}
#[test]
fn nested_branches_use_the_branch_context() {
    let source = "theorem pending (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by\n  cases h with\n  | inl hp => right; exact hp\n  | inr hq => left; exact hq";
    let found = goals(observe(
        source,
        source.find("exact hq").unwrap(),
        ObservationKind::Goals,
    ));
    assert_eq!(found.len(), 1);
    assert!(found[0].locals.find_by_user_name(&name("hp")).is_none());
    assert_eq!(
        found[0]
            .locals
            .find_by_user_name(&name("hq"))
            .unwrap()
            .type_,
        found[0].target
    );
}
#[test]
fn term_inspection_uses_lexical_identity_not_same_named_globals() {
    let source = "def h : Nat := 1\ntheorem pending (P : Prop) (h : P) : P := by exact h";
    let result = observe(source, source.len() - 1, ObservationKind::Term);
    let Some(SourceObservation::Term {
        expression,
        type_,
        locals,
        range,
    }) = result.observation
    else {
        panic!("expected local term")
    };
    let h = locals.find_by_user_name(&name("h")).unwrap();
    assert_eq!(expression, fln::Expr::fvar(h.id.clone()));
    assert_eq!(type_, h.type_);
    assert_eq!(&source[range], "h");
}

#[test]
fn definition_observations_survive_rollback_without_admitting_the_definition() {
    for (source, local_name) in [
        ("def pending (n : Nat) : Nat := n", "n"),
        ("def pending (n : Nat) : Nat := by exact n", "n"),
        // Unsafe definitions use the same body checkpoint as singleton partial
        // definitions, without extending inspection's partial-modifier door.
        ("unsafe def pending (n : Nat) : Nat := pending n", "n"),
        (
            "def pending (n : Nat) : Nat := match n with\n  | 0 => 0\n  | Nat.succ k => pending k",
            "k",
        ),
        // Observing the measure crosses both its own speculative checkpoint
        // and the enclosing recursive-body checkpoint.
        (
            "def pending (n : Nat) : Nat := match n with\n  | 0 => 0\n  | Nat.succ k => pending k\ntermination_by structural n",
            "n",
        ),
    ] {
        let at = source.rfind(local_name).unwrap();
        let result = observe(source, at, ObservationKind::Term);
        assert!(
            !result
                .prefix
                .checked
                .checked
                .engine
                .environment()
                .contains(&name("pending")),
            "{source}"
        );
        let Some(SourceObservation::Term {
            expression,
            type_,
            locals,
            range,
        }) = result.observation
        else {
            panic!("expected definition-body term: {source}")
        };
        let local = locals.find_by_user_name(&name(local_name)).unwrap();
        // Matching retains a source binder as a let alias to its constructor
        // field; identifier elaboration uses that field's original identity.
        assert_eq!(
            expression,
            local
                .value
                .clone()
                .unwrap_or_else(|| fln::Expr::fvar(local.id.clone())),
            "{source}"
        );
        let fln::ExprNode::FVar { id } = expression.node() else {
            panic!("expected the observed variable's local identity: {source}")
        };
        assert!(
            locals.find(id).is_some(),
            "the observed variable must stay bound"
        );
        assert_eq!(type_, fln::Expr::const_(name("Nat"), vec![]), "{source}");
        assert_eq!(&source[range], local_name, "{source}");
        assert!(
            locals
                .decls()
                .iter()
                .all(|local| !local.user_name.is_anonymous()
                    || !matches!(local.type_.node(), fln::ExprNode::ForallE { .. })),
            "an unused private self escaped in {source}"
        );
    }
}

#[test]
fn applied_global_head_is_observed_against_its_checked_prefix() {
    let source = "def Library.identity (P : Prop) (h : P) : P := h\ndef pending (P : Prop) (h : P) : P := Library.identity P h";
    let result = observe(
        source,
        source.rfind("Library.identity").unwrap() + 2,
        ObservationKind::Term,
    );
    let environment = result.prefix.checked.checked.engine.environment();
    let declared_type = environment
        .find(&name("Library.identity"))
        .unwrap()
        .constant_val()
        .type_
        .clone();
    assert!(!environment.contains(&name("pending")));
    let Some(SourceObservation::Term {
        expression,
        type_,
        range,
        ..
    }) = result.observation
    else {
        panic!("expected the applied global head")
    };
    assert_eq!(
        expression,
        fln::Expr::const_(name("Library.identity"), vec![])
    );
    assert_eq!(type_, declared_type);
    assert_eq!(&source[range], "Library.identity");
}

#[test]
fn definition_body_tactic_goals_survive_rollback_without_publishing_a_definition() {
    for source in [
        "def pending (n : Nat) : Nat := by exact n",
        "unsafe def pending (n : Nat) : Nat := by exact pending n",
        "def pending (n : Nat) : Nat := match n with\n  | 0 => 0\n  | Nat.succ k => by exact pending k",
    ] {
        let observed = goals(observe(
            source,
            source.rfind("exact").unwrap(),
            ObservationKind::Goals,
        ));
        assert_eq!(observed.len(), 1, "{source}");
        assert_eq!(
            observed[0].target,
            fln::Expr::const_(name("Nat"), vec![]),
            "{source}"
        );
        assert!(
            observed[0]
                .locals
                .decls()
                .iter()
                .all(|local| !local.user_name.is_anonymous()
                    || !matches!(local.type_.node(), fln::ExprNode::ForallE { .. })),
            "an unused private self escaped in {source}"
        );
    }
}

#[test]
fn recursive_self_hover_retains_the_binding_its_expression_needs() {
    for source in [
        "def pending (n : Nat) : Nat := match n with\n  | 0 => 0\n  | Nat.succ k => pending k",
        "unsafe def pending (n : Nat) : Nat := pending n",
    ] {
        let result = observe(
            source,
            source.rfind("pending").unwrap(),
            ObservationKind::Term,
        );
        assert!(
            !result
                .prefix
                .checked
                .checked
                .engine
                .environment()
                .contains(&name("pending")),
            "{source}"
        );
        let Some(SourceObservation::Term {
            expression,
            type_,
            locals,
            range,
        }) = result.observation
        else {
            panic!("expected a recursive-self term: {source}")
        };
        let fln::ExprNode::FVar { id } = expression.node() else {
            panic!("recursive self must retain its provisional local identity")
        };
        let binding = locals.find(id).expect("the observed self must stay bound");
        assert_eq!(type_, binding.type_);
        assert_eq!(&source[range], "pending");
    }
}

#[test]
fn observations_retain_self_dependencies_of_visible_local_types_and_values() {
    let source = "def pending (n : Nat) : Nat :=\n  let self := pending\n  let equation : self n = self n := rfl\n  by exact n";
    let observed = goals(observe(
        source,
        source.rfind("exact").unwrap(),
        ObservationKind::Goals,
    ));
    assert_eq!(observed.len(), 1);
    let locals = &observed[0].locals;
    let alias = locals.find_by_user_name(&name("self")).unwrap();
    let fln::ExprNode::FVar { id } = alias.value.as_ref().unwrap().node() else {
        panic!("expected the source let to retain its recursive-self value")
    };
    assert!(locals.find(id).is_some(), "the source let must stay closed");
    let equation = locals.find_by_user_name(&name("equation")).unwrap();
    assert!(
        equation
            .type_
            .abstract_fvar(&alias.id, 0)
            .unwrap()
            .has_loose_bvar(0),
        "the visible type must retain its source-let dependency"
    );
}

#[test]
fn a_goal_using_recursive_self_retains_its_private_binding() {
    let source = "def pending (n : Nat) : Nat := by\n  have equation : pending n = pending n := by rfl\n  exact n";
    let observed = goals(observe(
        source,
        source.find("rfl").unwrap(),
        ObservationKind::Goals,
    ));
    assert_eq!(observed.len(), 1);
    let recursive_self = observed[0]
        .locals
        .decls()
        .iter()
        .find(|local| local.user_name.is_anonymous())
        .expect("the target's recursive self must stay bound");
    assert!(
        observed[0]
            .target
            .abstract_fvar(&recursive_self.id, 0)
            .unwrap()
            .has_loose_bvar(0)
    );
}

#[test]
fn imported_and_namespaced_prefix_is_checked_before_inspection() {
    let main = name("Main");
    let lib = name("Lib");
    let source = "import Lib\nnamespace User\nopen Library\ntheorem pending (P : Prop) (h : P) : P := by exact identity h";
    let library = "namespace Library\ndef identity {P : Prop} (h : P) : P := h\nend Library";
    let found = session()
        .inspect(
            &[
                SourceModuleInput {
                    name: &main,
                    source: source.as_bytes(),
                },
                SourceModuleInput {
                    name: &lib,
                    source: library.as_bytes(),
                },
            ],
            &main,
            source.find("exact").unwrap(),
            ObservationKind::Goals,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(found.scope.namespace, name("User"));
    assert!(
        found
            .prefix
            .checked
            .checked
            .engine
            .environment()
            .contains(&name("Library.identity"))
    );
    assert!(
        !found
            .prefix
            .checked
            .checked
            .engine
            .environment()
            .contains(&name("User.pending"))
    );
    assert_eq!(goals(found).len(), 1);
}

#[test]
fn inspection_uses_checked_section_variables_instead_of_replaying_their_commands() {
    // Proof-only section parameters require explicit inclusion. Inspection must
    // preserve the checked include state, not make otherwise hidden locals live.
    let source =
        "section\nvariable (P : Prop) (h : P)\ninclude h\ntheorem pending : P := by exact h";
    let result = observe(source, source.rfind('h').unwrap(), ObservationKind::Term);
    let Some(SourceObservation::Term {
        expression,
        type_,
        locals,
        ..
    }) = result.observation
    else {
        panic!("expected a checked section-local observation")
    };
    let local = locals.find_by_user_name(&name("h")).unwrap();
    assert_eq!(expression, fln::Expr::fvar(local.id.clone()));
    assert_eq!(type_, local.type_);
    assert!(
        !result
            .prefix
            .checked
            .checked
            .engine
            .environment()
            .contains(&name("pending"))
    );
    assert!(goals(observe(source, source.len(), ObservationKind::Goals)).is_empty());
}

#[test]
fn inspection_does_not_expose_unincluded_proof_only_section_parameters() {
    let source = "section\nvariable (P : Prop) (h : P)\ntheorem pending : P := by exact h";
    let main = name("Main");
    let result = session().inspect(
        &[SourceModuleInput {
            name: &main,
            source: source.as_bytes(),
        }],
        &main,
        source.rfind('h').unwrap(),
        ObservationKind::Term,
    );
    assert!(matches!(
        result,
        Err(fln::source_check::modules::SourceModuleCheckError::Source { .. })
    ));
}
#[test]
fn bad_prefix_or_prior_tactic_is_not_presented_as_current_state() {
    for source in [
        "theorem bad : False := by exact True.intro\ntheorem pending : True := by skip",
        "theorem pending (P : Prop) : P := by\n  have bad : False := True.intro\n  skip",
    ] {
        let main = name("Main");
        assert!(
            session()
                .inspect(
                    &[SourceModuleInput {
                        name: &main,
                        source: source.as_bytes()
                    }],
                    &main,
                    source.rfind("skip").unwrap(),
                    ObservationKind::Goals
                )
                .is_err(),
            "{source}"
        );
    }
}
#[test]
fn observation_stop_is_not_swallowed_by_tactic_backtracking() {
    let source = "theorem pending (P : Prop) (h : P) : P := by first | fail | exact h";
    assert_eq!(
        goals(observe(
            source,
            source.rfind("exact").unwrap(),
            ObservationKind::Goals
        ))
        .len(),
        1
    );
}
#[test]
fn crlf_and_unicode_ranges_are_original_byte_ranges() {
    let source =
        "-- 😀\r\ndef π : Nat := 1\r\ntheorem pending (n : Nat) : n = n := by\r\n  exact rfl";
    let result = observe(source, source.rfind("rfl").unwrap(), ObservationKind::Term);
    let Some(SourceObservation::Term { range, .. }) = result.observation else {
        panic!("expected term")
    };
    assert_eq!(&source[range], "rfl");
}
#[test]
fn inspection_cannot_contaminate_later_checking_or_accept_false_proofs() {
    let mut session = session();
    let main = name("Main");
    let source = "theorem pending : False := by skip";
    let inputs = [SourceModuleInput {
        name: &main,
        source: source.as_bytes(),
    }];
    assert_eq!(
        goals(
            session
                .inspect(&inputs, &main, source.len(), ObservationKind::Goals)
                .unwrap()
                .into_complete()
                .unwrap()
        )
        .len(),
        1
    );
    assert!(session.check(&inputs, &main).is_err());
    let good = [SourceModuleInput {
        name: &main,
        source: b"theorem good : True := by exact True.intro",
    }];
    let checked = session
        .check(&good, &main)
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        !checked
            .checked
            .checked
            .engine
            .environment()
            .contains(&name("pending"))
    );
    assert!(
        checked
            .checked
            .checked
            .engine
            .environment()
            .contains(&name("good"))
    );
}

const MUTUAL_DATA: &str = "mutual
  inductive Tree (A : Type) where | node (value : A) (children : Forest A)
  inductive Forest (A : Type) where | nil | cons (head : Tree A) (tail : Forest A)
end";

#[test]
fn mutual_imports_supply_branch_locals_without_publishing_the_observed_proof() {
    let main = name("Main");
    let data = name("Data");
    let source = "import Data\ntheorem pending (t : Tree Nat) (P : Tree Nat -> Prop) (h : P t) : P t := by\n  cases t with\n  | node n xs => exact h";
    let inputs = [
        SourceModuleInput {
            name: &main,
            source: source.as_bytes(),
        },
        SourceModuleInput {
            name: &data,
            source: MUTUAL_DATA.as_bytes(),
        },
    ];
    let mut session = session();
    let result = session
        .inspect(
            &inputs,
            &main,
            source.find("exact h").unwrap(),
            ObservationKind::Goals,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let environment = result.prefix.checked.checked.engine.environment();
    for declaration in ["Tree", "Forest", "Tree.rec", "Forest.rec"] {
        assert!(environment.contains(&name(declaration)), "{declaration}");
    }
    assert!(!environment.contains(&name("pending")));
    let observed = goals(result);
    assert_eq!(observed.len(), 1);
    let goal = &observed[0];
    assert_eq!(
        goal.target,
        goal.locals.find_by_user_name(&name("h")).unwrap().type_
    );
    assert!(goal.locals.find_by_user_name(&name("t")).is_none());
    assert!(goal.locals.find_by_user_name(&name("n")).is_some());
    assert!(goal.locals.find_by_user_name(&name("xs")).is_some());
    let checked = session
        .check(&inputs, &main)
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        checked
            .checked
            .checked
            .engine
            .environment()
            .contains(&name("pending"))
    );
}

#[test]
fn an_invalid_mutual_import_cannot_reuse_a_previously_observed_environment() {
    let main = name("Main");
    let data = name("Data");
    let source = "import Data\ndef pending : Tree Nat := by";
    let inputs = [
        SourceModuleInput {
            name: &main,
            source: source.as_bytes(),
        },
        SourceModuleInput {
            name: &data,
            source: MUTUAL_DATA.as_bytes(),
        },
    ];
    let mut session = session();
    let good = session
        .inspect(&inputs, &main, source.len(), ObservationKind::Goals)
        .unwrap()
        .into_complete()
        .unwrap();
    let good_root = good.prefix.checked.checked.result_logical_root;
    let good_goals = goals(good);
    assert_eq!(good_goals.len(), 1);
    let corrupt = [inputs[0], SourceModuleInput { name: &data, source: b"mutual inductive Tree where | mk (f : Forest -> Nat) inductive Forest where | mk (t : Tree) end" }];
    assert!(
        session
            .inspect(&corrupt, &main, source.len(), ObservationKind::Goals)
            .is_err()
    );
    let recovered = session
        .inspect(&inputs, &main, source.len(), ObservationKind::Goals)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        recovered.prefix.checked.checked.result_logical_root,
        good_root
    );
    assert_eq!(goals(recovered)[0].target, good_goals[0].target);
    assert!(session.check(&inputs, &main).is_err());
}

#[test]
fn empty_nested_assertion_proofs_are_never_successfully_checked() {
    let main = name("Main");
    for source in [
        "def pending : Nat := show Nat by",
        "theorem pending : False := by",
        "theorem pending : False := show False by",
        "theorem pending : True := have missing : False := (by); True.intro",
    ] {
        let mut session = session();
        assert!(
            session
                .check(
                    &[SourceModuleInput {
                        name: &main,
                        source: source.as_bytes()
                    }],
                    &main
                )
                .is_err(),
            "{source}"
        );
        let valid = "theorem recovered : True := by exact True.intro";
        assert!(
            session
                .check(
                    &[SourceModuleInput {
                        name: &main,
                        source: valid.as_bytes()
                    }],
                    &main
                )
                .unwrap()
                .into_complete()
                .is_ok()
        );
    }
}
