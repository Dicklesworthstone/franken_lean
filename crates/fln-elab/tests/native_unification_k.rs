//! K-like reduction through the production transactional unifier.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::constraint::unify::{UnificationBudget, UnificationError, UnificationTransparency};
use fln_elab::inductive::{ConstructorSpec, InductiveSpec, inductive_declaration};
use fln_elab::mvar::MetavarKind;
use fln_elab::records::RecordBudget;
use fln_elab::txn::ElabTxn;
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_env::environment::{DeclarationBudget, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::{Budget, Verdict};
use fln_kernel::{Declaration, check};
use std::cell::Cell;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn constant(text: &str) -> Expr {
    Expr::const_(name(text), Vec::new())
}
fn nat() -> Expr {
    constant("Nat")
}
fn number(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn bvar(n: u32) -> Expr {
    Expr::bvar(n).unwrap()
}
fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}
fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default)
}
fn app(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}
fn budget() -> UnificationBudget {
    let mut result = UnificationBudget::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    result.transparency = UnificationTransparency::None;
    result
}
fn publish(env: Environment, declaration: Declaration) -> Environment {
    let Outcome::Complete(admitted) = admit(&env, declaration, budget().kernel) else {
        panic!("fixture admission did not complete");
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("fixture was rejected");
    };
    let Outcome::Complete(Published::BlockCommitted(publication)) = checked.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) else {
        panic!("fixture publication did not complete");
    };
    publication.environment
}
fn transaction() -> ElabTxn {
    let mut env = Environment::new();
    for declaration in [
        fln_elab::seed::nat_inductive_seed_declaration(),
        fln_elab::seed::eq_seed_declaration(),
        fln_elab::seed::heq_seed_declaration(),
        fln_elab::seed::bool_seed_declaration(),
    ] {
        env = publish(env, declaration);
    }
    ElabTxn::new(env, KVMap::new(), 29)
}
fn local(txn: &mut ElabTxn, text: &str, type_: Expr) -> Expr {
    let id = FVarId(name(text));
    txn.lctx
        .add_param(id.clone(), id.0.clone(), type_, BinderInfo::Default);
    Expr::fvar(id)
}
fn hole(txn: &mut ElabTxn, text: &str, type_: Expr, kind: MetavarKind) -> MVarId {
    let id = MVarId(name(text));
    txn.mvars.declare(
        id.clone(),
        id.0.clone(),
        type_,
        txn.lctx.clone(),
        kind,
        0,
        None,
    );
    id
}
fn equality_at(level: Level, type_: Expr, left: Expr, right: Expr) -> Expr {
    app(Expr::const_(name("Eq"), vec![level]), [type_, left, right])
}
fn equality(left: Expr, right: Expr) -> Expr {
    equality_at(Level::one(), nat(), left, right)
}
fn motive(result: Expr, left: Expr) -> Expr {
    lam(nat(), lam(equality(left, bvar(0)), result))
}
fn transport(left: Expr, right: Expr, proof: Expr, branch: Expr) -> Expr {
    eliminate(motive(nat(), left.clone()), left, right, proof, branch)
}
fn eliminate(motive: Expr, left: Expr, right: Expr, proof: Expr, branch: Expr) -> Expr {
    app(
        Expr::const_(name("Eq.rec"), vec![Level::one(), Level::one()]),
        [nat(), left, motive, branch, right, proof],
    )
}
fn reflexive_proof(txn: &mut ElabTxn) -> Expr {
    local(txn, "p", equality(number(7), number(7)))
}
fn unchanged(txn: &ElabTxn, before: &ElabTxn) {
    let mut expected = before.clone();
    expected.budget.heartbeats_consumed = txn.budget.heartbeats_consumed;
    assert_eq!(txn, &expected);
}
fn assignment_case() -> (ElabTxn, MVarId, Expr, Expr) {
    let mut txn = transaction();
    let out = hole(&mut txn, "out", nat(), MetavarKind::Natural);
    let proof = reflexive_proof(&mut txn);
    let left = transport(number(7), number(7), proof, Expr::mvar(out.clone()));
    (txn, out, left, number(23))
}

#[test]
fn neutral_reflexive_equality_reduces_in_both_orientations_and_all_transparencies() {
    for reverse in [false, true] {
        for transparency in [
            UnificationTransparency::None,
            UnificationTransparency::Abbreviations,
            UnificationTransparency::SafeDefinitions,
        ] {
            let mut txn = transaction();
            let p = reflexive_proof(&mut txn);
            let term = transport(number(7), number(7), p, number(23));
            let before = txn.clone();
            let mut limits = budget();
            limits.transparency = transparency;
            let (left, right) = if reverse {
                (number(23), term)
            } else {
                (term, number(23))
            };
            let report = txn.unify(&left, &right, limits).unwrap();
            assert!(report.expression_assignments.is_empty());
            assert_eq!(report.kernel_checks, 0);
            unchanged(&txn, &before);
        }
    }
}

#[test]
fn k_can_expose_a_value_assignment_without_solving_an_opaque_proof() {
    let mut txn = transaction();
    let out = hole(&mut txn, "out", nat(), MetavarKind::Natural);
    let p = hole(
        &mut txn,
        "p",
        equality(number(7), number(7)),
        MetavarKind::SyntheticOpaque,
    );
    let term = transport(
        number(7),
        number(7),
        Expr::mvar(p.clone()),
        Expr::mvar(out.clone()),
    );
    let report = txn.unify(&term, &number(23), budget()).unwrap();
    assert_eq!(report.expression_assignments, vec![out.clone()]);
    assert_eq!(report.kernel_checks, 1);
    assert_eq!(txn.mvars.get_assigned_expr(&out), Some(&number(23)));
    assert!(!txn.mvars.is_assigned(&p));
    assert!(txn.mvars.is_declared(&p));
}

#[test]
fn a_dependent_motive_keeps_its_selected_branch() {
    let mut txn = transaction();
    let family = local(&mut txn, "P", pi(nat(), Expr::sort(Level::one())));
    let p = reflexive_proof(&mut txn);
    let branch = local(&mut txn, "v", Expr::app(family.clone(), number(7)));
    let dependent = motive(Expr::app(family, bvar(1)), number(7));
    let term = eliminate(dependent, number(7), number(7), p, branch.clone());
    txn.unify(&term, &branch, budget()).unwrap();
}

#[test]
fn reductions_under_opened_binders_do_not_capture_comparison_locals() {
    let mut txn = transaction();
    let x = local(&mut txn, "x", nat());
    let p = local(&mut txn, "p", equality(x.clone(), x.clone()));
    let mut term = transport(x.clone(), x.clone(), p.clone(), x.clone());
    let ExprNode::FVar { id: p_id } = p.node() else {
        unreachable!()
    };
    let ExprNode::FVar { id: x_id } = x.node() else {
        unreachable!()
    };
    term = lam(
        equality(x.clone(), x.clone()),
        term.abstract_fvar(p_id, 0).unwrap(),
    );
    term = lam(nat(), term.abstract_fvar(x_id, 0).unwrap());
    let expected = lam(nat(), lam(equality(bvar(0), bvar(0)), bvar(1)));
    txn.lctx = fln_elab::lctx::LocalContext::new();
    let before = txn.clone();
    txn.unify(&term, &expected, budget()).unwrap();
    unchanged(&txn, &before);
}

#[test]
fn unequal_and_unknown_endpoints_are_not_guessed() {
    for unknown in [false, true] {
        let mut txn = transaction();
        let index = hole(&mut txn, "index", nat(), MetavarKind::Natural);
        let right = if unknown {
            Expr::mvar(index)
        } else {
            number(8)
        };
        let p = local(&mut txn, "p", equality(number(7), right.clone()));
        let term = transport(number(7), right, p, number(23));
        let before = txn.clone();
        assert!(matches!(
            txn.unify(&term, &number(23), budget()),
            Err(UnificationError::Deferred(_))
        ));
        unchanged(&txn, &before);
    }
}

#[test]
fn later_endpoint_inference_retries_the_original_transport() {
    let mut txn = transaction();
    let index = hole(&mut txn, "index", nat(), MetavarKind::Natural);
    let p = local(
        &mut txn,
        "p",
        equality(number(7), Expr::mvar(index.clone())),
    );
    let term = transport(number(7), Expr::mvar(index.clone()), p, number(23));
    let report = txn
        .unify_many_with(
            &[(term, number(23)), (Expr::mvar(index.clone()), number(7))],
            budget(),
            &|| false,
        )
        .unwrap();
    assert_eq!(report.expression_assignments, vec![index]);
    assert_eq!(report.kernel_checks, 1);
}

#[test]
fn polymorphic_recursor_parameters_are_instantiated_in_their_own_positions() {
    let mut txn = transaction();
    let u = Level::param(name("u"));
    let a = local(&mut txn, "A", Expr::sort(u.clone()));
    let x = local(&mut txn, "x", a.clone());
    let p = local(
        &mut txn,
        "p",
        equality_at(u.clone(), a.clone(), x.clone(), x.clone()),
    );
    let m = lam(
        a.clone(),
        lam(equality_at(u.clone(), a.clone(), x.clone(), bvar(0)), nat()),
    );
    let term = app(
        Expr::const_(name("Eq.rec"), vec![Level::one(), u]),
        [a, x.clone(), m, number(23), x, p],
    );
    txn.unify(&term, &number(23), budget()).unwrap();
}

#[test]
fn earlier_universe_assignments_are_visible_to_k_reduction() {
    let mut txn = transaction();
    let u = LMVarId(name("u"));
    let p = reflexive_proof(&mut txn);
    let term = app(
        Expr::const_(name("Eq.rec"), vec![Level::mvar(u.clone()), Level::one()]),
        [
            nat(),
            number(7),
            motive(nat(), number(7)),
            number(23),
            number(7),
            p,
        ],
    );
    txn.unify_many_with(
        &[
            (Expr::sort(Level::mvar(u)), Expr::sort(Level::one())),
            (term, number(23)),
        ],
        budget(),
        &|| false,
    )
    .unwrap();
}

#[test]
fn arguments_after_the_major_apply_to_the_function_valued_branch() {
    let mut txn = transaction();
    let p = reflexive_proof(&mut txn);
    let term = eliminate(
        motive(pi(nat(), nat()), number(7)),
        number(7),
        number(7),
        p,
        lam(nat(), bvar(0)),
    );
    txn.unify(&Expr::app(term, number(47)), &number(47), budget())
        .unwrap();
}

#[test]
fn nested_transports_are_reduced_on_heap_continuations() {
    let mut txn = transaction();
    let p = reflexive_proof(&mut txn);
    let mut term = number(23);
    for _ in 0..192 {
        term = transport(number(7), number(7), p.clone(), term);
    }
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(move || {
            let mut limits = budget();
            txn.budget.max_heartbeats = 2_000_000;
            limits.max_steps = 2_000_000;
            limits.max_visited_nodes = 2_000_000;
            txn.unify(&term, &number(23), limits).unwrap();
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn a_non_k_boolean_eliminator_remains_stuck_on_a_neutral_major() {
    let mut txn = transaction();
    let major = local(&mut txn, "flag", constant("Bool"));
    let term = app(
        Expr::const_(name("Bool.rec"), vec![Level::one()]),
        [lam(constant("Bool"), nat()), number(0), number(1), major],
    );
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&term, &number(0), budget()),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn malformed_universe_arity_does_not_gain_a_k_rule() {
    for levels in [vec![], vec![Level::one()], vec![Level::one(); 3]] {
        let mut txn = transaction();
        let p = reflexive_proof(&mut txn);
        let term = app(
            Expr::const_(name("Eq.rec"), levels),
            [
                nat(),
                number(7),
                motive(nat(), number(7)),
                number(23),
                number(7),
                p,
            ],
        );
        let before = txn.clone();
        assert!(txn.unify(&term, &number(23), budget()).is_err());
        unchanged(&txn, &before);
    }
}

#[test]
fn an_unsaturated_recursor_is_not_an_elimination() {
    let mut txn = transaction();
    let term = app(
        Expr::const_(name("Eq.rec"), vec![Level::one(), Level::one()]),
        [
            nat(),
            number(7),
            motive(nat(), number(7)),
            number(23),
            number(7),
        ],
    );
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&term, &number(23), budget()),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn arbitrary_admitted_singleton_propositions_use_their_own_rule() {
    let mut txn = transaction();
    let declaration = inductive_declaration(
        &InductiveSpec {
            name: name("Witness"),
            level_params: Vec::new(),
            parameters: Vec::new(),
            indices: Vec::new(),
            constructors: vec![ConstructorSpec {
                name: name("only"),
                fields: Vec::new(),
                result_indices: Vec::new(),
            }],
            result_level: Level::zero(),
        },
        RecordBudget::default(),
    )
    .unwrap();
    txn.env = publish(txn.env.clone(), declaration);
    let p = local(&mut txn, "w", constant("Witness"));
    let term = app(
        Expr::const_(name("Witness.rec"), vec![Level::one()]),
        [lam(constant("Witness"), nat()), number(31), p],
    );
    txn.unify(&term, &number(31), budget()).unwrap();
}

#[test]
fn exposed_assignments_still_need_kernel_validation() {
    let (mut txn, out, _, _) = assignment_case();
    let p = Expr::fvar(FVarId(name("p")));
    let term = transport(number(7), number(7), p, Expr::mvar(out));
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&term, &Expr::sort(Level::zero()), budget()),
        Err(UnificationError::AssignmentCheck { .. })
    ));
    unchanged(&txn, &before);
}

#[test]
fn an_unrelated_later_failure_rolls_back_the_k_exposed_assignment() {
    let (mut txn, _, left, right) = assignment_case();
    let before = txn.clone();
    assert!(
        txn.unify_many_with(&[(left, right), (number(0), number(1))], budget(), &|| {
            false
        })
        .is_err()
    );
    unchanged(&txn, &before);
}

#[test]
fn native_work_limits_leave_no_speculative_assignments() {
    for gate in 0..4 {
        let (mut txn, _, left, right) = assignment_case();
        let before = txn.clone();
        let mut limits = budget();
        match gate {
            0 => limits.max_steps = 0,
            1 => limits.max_visited_nodes = 0,
            2 => limits.max_assignments = 0,
            _ => limits.kernel.steps = 0,
        }
        let error = txn.unify(&left, &right, limits).unwrap_err();
        match gate {
            0 => assert!(matches!(error, UnificationError::StepLimit { .. })),
            1 => assert!(matches!(error, UnificationError::NodeLimit { .. })),
            2 => assert!(matches!(error, UnificationError::AssignmentLimit { .. })),
            _ => assert!(matches!(error, UnificationError::AssignmentCheck { .. })),
        }
        unchanged(&txn, &before);
        txn.unify(&left, &right, budget()).unwrap();
    }
}

#[test]
fn cancellation_at_entry_during_reduction_and_final_publication_rolls_back() {
    let (mut probe, _, left, right) = assignment_case();
    let calls = Cell::new(0);
    probe
        .unify_many_with(&[(left, right)], budget(), &|| {
            calls.set(calls.get() + 1);
            false
        })
        .unwrap();
    for stop in [1, calls.get() / 2, calls.get()] {
        let (mut txn, _, left, right) = assignment_case();
        let before = txn.clone();
        let count = Cell::new(0);
        let result = txn.unify_many_with(&[(left, right)], budget(), &|| {
            count.set(count.get() + 1);
            count.get() >= stop
        });
        assert!(matches!(result, Err(UnificationError::Cancelled)));
        unchanged(&txn, &before);
    }
}

#[test]
fn metadata_variants_do_not_block_the_endpoint_guard() {
    let mut txn = transaction();
    let p = reflexive_proof(&mut txn);
    let right = Expr::mdata(KVMap::new(), number(7));
    let term = transport(number(7), right, p, number(23));
    txn.unify(&term, &number(23), budget()).unwrap();
}

#[test]
fn a_malformed_proof_cannot_be_laundered_through_declaration_admission() {
    let txn = transaction();
    let candidate = Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name("badProof"),
            level_params: Vec::new(),
            type_: nat(),
        },
        value: transport(number(7), number(7), number(0), number(23)),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![name("badProof")],
    });
    assert!(matches!(
        check(&txn.env, &candidate, budget().kernel),
        Outcome::Complete(Verdict::Rejected { .. })
    ));
}

#[test]
fn identical_unresolved_indices_reduce_without_choosing_their_values() {
    let mut txn = transaction();
    let x = hole(&mut txn, "x", nat(), MetavarKind::Natural);
    let value = Expr::mvar(x.clone());
    let p = hole(
        &mut txn,
        "p",
        equality(value.clone(), value.clone()),
        MetavarKind::SyntheticOpaque,
    );
    let term = transport(value.clone(), value, Expr::mvar(p.clone()), number(23));
    let before = txn.clone();
    let report = txn.unify(&term, &number(23), budget()).unwrap();
    assert!(report.expression_assignments.is_empty());
    assert!(!txn.mvars.is_assigned(&x));
    assert!(!txn.mvars.is_assigned(&p));
    unchanged(&txn, &before);
}

#[test]
fn alpha_equivalent_function_indices_satisfy_the_guard() {
    let mut txn = transaction();
    let domain = pi(nat(), nat());
    let left = Expr::lam(name("leftName"), nat(), bvar(0), BinderInfo::Default);
    let right = Expr::lam(name("rightName"), nat(), bvar(0), BinderInfo::Default);
    let p = local(
        &mut txn,
        "p",
        equality_at(Level::one(), domain.clone(), left.clone(), right.clone()),
    );
    let m = lam(
        domain.clone(),
        lam(
            equality_at(Level::one(), domain.clone(), left.clone(), bvar(0)),
            nat(),
        ),
    );
    let term = app(
        Expr::const_(name("Eq.rec"), vec![Level::one(), Level::one()]),
        [domain, left, m, number(23), right, p],
    );
    txn.unify(&term, &number(23), budget()).unwrap();
}

fn heterogeneous(type_: Expr, value: Expr) -> Expr {
    app(
        Expr::const_(name("HEq"), vec![Level::one()]),
        [nat(), number(7), type_, value],
    )
}
fn heterogeneous_transport(type_: Expr, value: Expr, proof: Expr) -> Expr {
    let m = lam(
        Expr::sort(Level::one()),
        lam(bvar(0), lam(heterogeneous(bvar(1), bvar(0)), nat())),
    );
    app(
        Expr::const_(name("HEq.rec"), vec![Level::one(), Level::one()]),
        [nat(), number(7), m, number(23), type_, value, proof],
    )
}

#[test]
fn heterogeneous_equality_checks_both_type_and_value_indices() {
    let mut txn = transaction();
    let p = local(&mut txn, "p", heterogeneous(nat(), number(7)));
    let term = heterogeneous_transport(nat(), number(7), p);
    txn.unify(&term, &number(23), budget()).unwrap();
}

#[test]
fn heterogeneous_type_indices_are_not_synthesized_by_reduction() {
    let mut txn = transaction();
    let ty = hole(
        &mut txn,
        "B",
        Expr::sort(Level::one()),
        MetavarKind::Natural,
    );
    let type_ = Expr::mvar(ty.clone());
    let p = local(&mut txn, "p", heterogeneous(type_.clone(), number(7)));
    let term = heterogeneous_transport(type_, number(7), p);
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&term, &number(23), budget()),
        Err(UnificationError::Deferred(_))
    ));
    assert!(!txn.mvars.is_assigned(&ty));
    unchanged(&txn, &before);
}

#[test]
fn singleton_data_is_not_treated_as_a_k_proposition() {
    let mut txn = transaction();
    let declaration = inductive_declaration(
        &InductiveSpec {
            name: name("Datum"),
            level_params: Vec::new(),
            parameters: Vec::new(),
            indices: Vec::new(),
            constructors: vec![ConstructorSpec {
                name: name("only"),
                fields: Vec::new(),
                result_indices: Vec::new(),
            }],
            result_level: Level::one(),
        },
        RecordBudget::default(),
    )
    .unwrap();
    txn.env = publish(txn.env.clone(), declaration);
    let p = local(&mut txn, "d", constant("Datum"));
    let term = app(
        Expr::const_(name("Datum.rec"), vec![Level::one()]),
        [lam(constant("Datum"), nat()), number(31), p],
    );
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&term, &number(31), budget()),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn dependent_type_indices_are_inferred_through_neutral_transports() {
    let mut txn = transaction();
    let family = local(&mut txn, "P", pi(nat(), Expr::sort(Level::one())));
    let index = hole(&mut txn, "index", nat(), MetavarKind::Natural);
    let p = reflexive_proof(&mut txn);
    let term = transport(number(7), number(7), p, number(23));
    let report = txn
        .unify(
            &Expr::app(family.clone(), term),
            &Expr::app(family, Expr::mvar(index.clone())),
            budget(),
        )
        .unwrap();
    assert_eq!(report.expression_assignments, vec![index.clone()]);
    assert_eq!(txn.mvars.get_assigned_expr(&index), Some(&number(23)));
    assert_eq!(report.kernel_checks, 1);
}

#[test]
fn the_original_well_typed_transport_passes_declaration_checking() {
    let txn = transaction();
    let proof_type = equality(number(7), number(7));
    let candidate = Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name("goodTransport"),
            level_params: Vec::new(),
            type_: pi(proof_type.clone(), nat()),
        },
        value: lam(
            proof_type,
            transport(number(7), number(7), bvar(0), number(23)),
        ),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![name("goodTransport")],
    });
    assert!(matches!(
        check(&txn.env, &candidate, budget().kernel),
        Outcome::Complete(Verdict::Accepted { .. })
    ));
}

#[test]
fn mixed_queued_transport_obligations_preserve_the_opaque_proof_residual() {
    use fln_elab::constraint::ConstraintKind;
    let mut txn = transaction();
    let out = hole(&mut txn, "out", nat(), MetavarKind::Natural);
    let proof = hole(
        &mut txn,
        "proof",
        equality(number(7), number(7)),
        MetavarKind::SyntheticOpaque,
    );
    let term = transport(
        number(7),
        number(7),
        Expr::mvar(proof.clone()),
        Expr::mvar(out.clone()),
    );
    let typing = txn.postpone(
        ConstraintKind::HasType {
            expr: term.clone(),
            expected_type: nat(),
        },
        0,
    );
    let equation = txn.postpone(
        ConstraintKind::DefEq {
            lhs: term,
            rhs: number(23),
        },
        0,
    );
    let env = txn.env.clone();
    let report = txn
        .solve_constraints_with(&[equation, typing, equation], budget(), &|| false)
        .unwrap();
    assert_eq!(report.solved, vec![typing, equation]);
    assert_eq!(report.unification.expression_assignments, vec![out.clone()]);
    assert_eq!(report.unification.kernel_checks, 2);
    assert_eq!(
        report.unification.residual_metavariables,
        vec![proof.clone()]
    );
    assert_eq!(txn.mvars.get_assigned_expr(&out), Some(&number(23)));
    assert!(!txn.mvars.is_assigned(&proof));
    assert!(txn.constraints.is_empty());
    assert_eq!(txn.env, env);
}

#[test]
fn queued_typing_checks_the_original_proof_even_when_reduction_discards_it() {
    use fln_elab::constraint::{ConstraintKind, ConstraintSolveError};
    let mut txn = transaction();
    let out = hole(&mut txn, "out", nat(), MetavarKind::Natural);
    // The eliminator's proof argument is ill typed. A reduced result alone is
    // not evidence that this original queued term has its claimed type.
    let term = transport(number(7), number(7), number(0), Expr::mvar(out.clone()));
    let typing = txn.postpone(
        ConstraintKind::HasType {
            expr: term.clone(),
            expected_type: nat(),
        },
        0,
    );
    let equation = txn.postpone(
        ConstraintKind::DefEq {
            lhs: term,
            rhs: number(23),
        },
        0,
    );
    let before = txn.clone();
    assert!(matches!(
        txn.solve_constraints_with(&[equation, typing], budget(), &|| false),
        Err(ConstraintSolveError::Unification(
            UnificationError::ConstraintCheck { id, .. }
        )) if id == typing
    ));
    unchanged(&txn, &before);
    // Independent valid work can still succeed, without silently discharging
    // either of the failed rows or overwriting their retained input terms.
    let recovery = txn.postpone(
        ConstraintKind::DefEq {
            lhs: Expr::mvar(out.clone()),
            rhs: number(23),
        },
        0,
    );
    let report = txn
        .solve_constraints_with(&[recovery], budget(), &|| false)
        .unwrap();
    assert_eq!(report.solved, vec![recovery]);
    assert_eq!(txn.mvars.get_assigned_expr(&out), Some(&number(23)));
    let awakened: Vec<_> = report
        .unification
        .awakened
        .iter()
        .map(|row| row.id)
        .collect();
    assert_eq!(awakened, vec![typing, equation]);
}

#[test]
fn queued_transport_reduction_uses_the_saved_dependent_local_context() {
    use fln_elab::constraint::ConstraintKind;
    let mut txn = transaction();
    let out = hole(&mut txn, "out", nat(), MetavarKind::Natural);
    let x = local(&mut txn, "x", nat());
    let proof = local(&mut txn, "proof", equality(x.clone(), x.clone()));
    let term = transport(x.clone(), x, proof, Expr::mvar(out.clone()));
    let typing = txn.postpone(
        ConstraintKind::HasType {
            expr: term.clone(),
            expected_type: nat(),
        },
        0,
    );
    let equation = txn.postpone(
        ConstraintKind::DefEq {
            lhs: term,
            rhs: number(23),
        },
        0,
    );
    txn.lctx.truncate(0);
    let report = txn
        .solve_constraints_with(&[typing, equation], budget(), &|| false)
        .unwrap();
    assert_eq!(report.solved, vec![typing, equation]);
    assert_eq!(report.unification.kernel_checks, 2);
    assert!(report.unification.residual_metavariables.is_empty());
    assert_eq!(txn.mvars.get_assigned_expr(&out), Some(&number(23)));
    assert!(txn.lctx.is_empty());
}
