//! Suspended obligations own their lexical scope, not the resumer's binders.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_elab::constraint::unify::{UnificationBudget, UnificationError};
use fln_elab::constraint::{ConstraintId, ConstraintKind, ConstraintSolveError};
use fln_elab::lctx::LocalContext;
use fln_elab::mvar::{AssignmentJustification, MetavarKind};
use fln_elab::seed::bootstrap_nat_environment;
use fln_elab::txn::ElabTxn;
use fln_kernel::verdict::Budget;
use std::cell::Cell;
use std::collections::HashSet;

fn name(text: &str) -> Name {
    Name::from_components([text])
}
fn nat() -> Expr {
    Expr::const_(name("Nat"), vec![])
}
fn number(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn budget() -> UnificationBudget {
    UnificationBudget::new(Budget::for_stack_bytes(1024 * 1024))
}
fn transaction() -> ElabTxn {
    ElabTxn::new(
        bootstrap_nat_environment(budget().kernel).unwrap(),
        KVMap::new(),
        127,
    )
}
fn local(tx: &mut ElabTxn, text: &str, ty: Expr) -> Expr {
    let id = FVarId(name(text));
    tx.lctx
        .add_param(id.clone(), id.0.clone(), ty, BinderInfo::Default);
    Expr::fvar(id)
}
fn goal(tx: &mut ElabTxn, text: &str, ty: Expr, kind: MetavarKind) -> MVarId {
    let id = MVarId(name(text));
    tx.mvars
        .declare(id.clone(), id.0.clone(), ty, tx.lctx.clone(), kind, 0, None);
    id
}
fn typing(tx: &mut ElabTxn, expr: Expr, expected_type: Expr) -> ConstraintId {
    tx.postpone(
        ConstraintKind::HasType {
            expr,
            expected_type,
        },
        0,
    )
}
fn unchanged(tx: &ElabTxn, before: &ElabTxn) {
    let mut expected = before.clone();
    expected.budget.heartbeats_consumed = tx.budget.heartbeats_consumed;
    assert_eq!(tx, &expected);
}
fn saved_typing() -> (ElabTxn, ConstraintId) {
    let mut tx = transaction();
    let x = local(&mut tx, "x", nat());
    let row = typing(&mut tx, x, nat());
    tx.lctx = LocalContext::new();
    (tx, row)
}

#[test]
fn a_typing_obligation_survives_leaving_its_binder_scope() {
    let (mut tx, row) = saved_typing();
    let ambient = tx.lctx.clone();
    let report = tx
        .solve_constraints_with(&[row], budget(), &|| false)
        .unwrap();
    assert_eq!(report.solved, vec![row]);
    assert_eq!(report.unification.kernel_checks, 1);
    assert_eq!(tx.lctx, ambient);
    assert!(tx.constraints.is_empty());
}

#[test]
fn a_resumer_cannot_reinterpret_a_saved_local_identity() {
    let (mut tx, row) = saved_typing();
    local(&mut tx, "x", Expr::sort(Level::zero()));
    let ambient = tx.lctx.clone();
    tx.solve_constraints_with(&[row], budget(), &|| false)
        .unwrap();
    assert_eq!(tx.lctx, ambient);
}

#[test]
fn captured_empty_context_does_not_gain_later_local_authority() {
    let mut tx = transaction();
    let row = typing(&mut tx, Expr::fvar(FVarId(name("later"))), nat());
    local(&mut tx, "later", nat());
    let before = tx.clone();
    assert!(
        tx.solve_constraints_with(&[row], budget(), &|| false)
            .is_err()
    );
    unchanged(&tx, &before);
}

#[test]
fn equality_reduction_uses_the_saved_let_value() {
    let mut tx = transaction();
    let id = FVarId(name("let_value"));
    tx.lctx.add_let(id.clone(), id.0.clone(), nat(), number(7));
    let row = tx.postpone(
        ConstraintKind::DefEq {
            lhs: Expr::fvar(id.clone()),
            rhs: number(7),
        },
        0,
    );
    tx.lctx = LocalContext::new();
    tx.lctx.add_let(id.clone(), id.0, nat(), number(9));
    let ambient = tx.lctx.clone();
    tx.solve_defeq_constraints_with(&[row], budget(), &|| false)
        .unwrap();
    assert_eq!(tx.lctx, ambient);
}

#[test]
fn a_mixed_batch_restores_each_sibling_scope_independently() {
    for reverse in [false, true] {
        let mut tx = transaction();
        let ty = goal(&mut tx, "T", Expr::sort(Level::one()), MetavarKind::Natural);
        let common = tx.lctx.clone();
        let first = local(&mut tx, "left", Expr::mvar(ty.clone()));
        let left = typing(&mut tx, first, nat());
        tx.lctx = common;
        let p = local(&mut tx, "P", Expr::sort(Level::zero()));
        let proof = local(&mut tx, "right", p.clone());
        let right = typing(&mut tx, proof, p);
        tx.lctx = LocalContext::new();
        let ids = if reverse {
            vec![right, left, right]
        } else {
            vec![left, right]
        };
        let report = tx
            .solve_constraints_with(&ids, budget(), &|| false)
            .unwrap();
        assert_eq!(report.solved, vec![left, right]);
        assert_eq!(tx.mvars.get_assigned_expr(&ty), Some(&nat()));
        assert_eq!(report.unification.kernel_checks, 3);
        assert!(tx.lctx.is_empty());
    }
}

#[test]
fn delayed_abstraction_retains_the_parameters_scope_and_its_type_dependencies() {
    let mut tx = transaction();
    let ty = goal(&mut tx, "T", Expr::sort(Level::one()), MetavarKind::Natural);
    let function = goal(
        &mut tx,
        "f",
        Expr::forall_e(name("n"), nat(), nat(), BinderInfo::Default),
        MetavarKind::Natural,
    );
    let x = local(&mut tx, "x", Expr::mvar(ty.clone()));
    let row = tx.postpone(
        ConstraintKind::DelayedAssign {
            mvar: function.clone(),
            fvars: vec![FVarId(name("x"))],
            val: x,
        },
        0,
    );
    tx.lctx = LocalContext::new();
    tx.solve_constraints_with(&[row], budget(), &|| false)
        .unwrap();
    assert_eq!(tx.mvars.get_assigned_expr(&ty), Some(&nat()));
    let identity = Expr::lam(
        name("n"),
        nat(),
        Expr::bvar(0).unwrap(),
        BinderInfo::Default,
    );
    tx.unify(&Expr::mvar(function), &identity, budget())
        .unwrap();
    assert!(tx.lctx.is_empty());
}

#[test]
fn dependencies_include_captured_local_types_even_when_terms_are_ground() {
    let mut tx = transaction();
    let ty = goal(&mut tx, "T", Expr::sort(Level::one()), MetavarKind::Natural);
    local(&mut tx, "x", Expr::mvar(ty.clone()));
    let row = typing(&mut tx, number(7), nat());
    assert!(tx.constraints.constraints()[&row].reads_mvars.contains(&ty));
    tx.lctx = LocalContext::new();
    let awakened = tx
        .assign_mvar(ty, nat(), AssignmentJustification::DirectDefEq)
        .unwrap();
    assert_eq!(awakened.iter().map(|r| r.id).collect::<Vec<_>>(), vec![row]);
}

#[test]
fn dependencies_include_local_let_values_through_assigned_aliases() {
    let mut tx = transaction();
    let a = goal(&mut tx, "a", nat(), MetavarKind::Natural);
    let b = goal(&mut tx, "b", nat(), MetavarKind::Natural);
    tx.assign_mvar(
        a.clone(),
        Expr::mvar(b.clone()),
        AssignmentJustification::DirectDefEq,
    )
    .unwrap();
    tx.lctx
        .add_let(FVarId(name("z")), name("z"), nat(), Expr::mvar(a));
    let row = tx.postpone(
        ConstraintKind::DefEq {
            lhs: number(7),
            rhs: number(7),
        },
        0,
    );
    assert!(tx.constraints.constraints()[&row].reads_mvars.contains(&b));
    let ready = tx
        .assign_mvar(b, number(7), AssignmentJustification::DirectDefEq)
        .unwrap();
    assert_eq!(ready.iter().map(|r| r.id).collect::<Vec<_>>(), vec![row]);
}

#[test]
fn typed_proof_holes_remain_unresolved_after_their_scope_is_popped() {
    let mut tx = transaction();
    let p = local(&mut tx, "P", Expr::sort(Level::zero()));
    let proof = goal(&mut tx, "proof", p.clone(), MetavarKind::SyntheticOpaque);
    let row = typing(&mut tx, Expr::mvar(proof.clone()), p);
    tx.lctx = LocalContext::new();
    let report = tx
        .solve_constraints_with(&[row], budget(), &|| false)
        .unwrap();
    assert_eq!(
        report.unification.residual_metavariables,
        vec![proof.clone()]
    );
    assert!(!tx.mvars.is_assigned(&proof));
    assert!(tx.lctx.is_empty());
}

#[test]
fn a_later_scope_failure_rolls_back_an_earlier_inferred_assignment() {
    let mut tx = transaction();
    let ty = goal(&mut tx, "T", Expr::sort(Level::one()), MetavarKind::Natural);
    let left = typing(&mut tx, number(7), Expr::mvar(ty.clone()));
    let right = typing(&mut tx, Expr::fvar(FVarId(name("later"))), nat());
    local(&mut tx, "later", nat());
    let before = tx.clone();
    assert!(
        tx.solve_constraints_with(&[left, right], budget(), &|| false)
            .is_err()
    );
    unchanged(&tx, &before);
    tx.solve_constraints_with(&[left], budget(), &|| false)
        .unwrap();
    assert_eq!(tx.mvars.get_assigned_expr(&ty), Some(&nat()));
}

#[test]
fn final_cancellation_does_not_remove_a_scoped_obligation() {
    let (base, row) = saved_typing();
    let polls = Cell::new(0);
    base.clone()
        .solve_constraints_with(&[row], budget(), &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    let total = polls.get();
    for stop in [1, total / 2, total] {
        let mut tx = base.clone();
        polls.set(0);
        assert!(matches!(
            tx.solve_constraints_with(&[row], budget(), &|| {
                polls.set(polls.get() + 1);
                polls.get() >= stop
            }),
            Err(ConstraintSolveError::Unification(
                UnificationError::Cancelled
            ))
        ));
        unchanged(&tx, &base);
    }
}

#[test]
fn explicit_unscoped_queue_rows_still_use_the_callers_context() {
    let mut tx = transaction();
    let x = local(&mut tx, "x", nat());
    let row = tx.constraints.enqueue(
        ConstraintKind::HasType {
            expr: x,
            expected_type: nat(),
        },
        HashSet::new(),
        0,
    );
    tx.solve_constraints_with(&[row], budget(), &|| false)
        .unwrap();
}

#[test]
fn saved_binders_cannot_collide_with_solver_generated_identities() {
    let mut tx = transaction();
    let id = FVarId(Name::from_components(["_fln_unify_local", "0"]));
    tx.lctx.add_let(id.clone(), id.0, nat(), number(7));
    let identity = Expr::lam(
        name("x"),
        nat(),
        Expr::bvar(0).unwrap(),
        BinderInfo::Default,
    );
    let constant = Expr::lam(name("x"), nat(), number(7), BinderInfo::Default);
    let row = tx.postpone(
        ConstraintKind::DefEq {
            lhs: identity,
            rhs: constant,
        },
        0,
    );
    tx.lctx = LocalContext::new();
    let before = tx.clone();
    assert!(
        tx.solve_defeq_constraints_with(&[row], budget(), &|| false)
            .is_err()
    );
    unchanged(&tx, &before);
}

#[test]
fn saved_context_copying_and_execution_share_bounded_failure_atomicity() {
    let mut tx = transaction();
    for index in 0..8 {
        local(&mut tx, &format!("local{index}"), nat());
    }
    let rows: Vec<_> = (0..5).map(|_| typing(&mut tx, number(7), nat())).collect();
    tx.lctx = LocalContext::new();
    let before = tx.clone();
    let mut limited = budget();
    limited.max_visited_nodes = 32; // 40 captured declarations, even with no active locals.
    assert!(matches!(
        tx.solve_constraints_with(&rows, limited, &|| false),
        Err(ConstraintSolveError::Unification(
            UnificationError::NodeLimit { .. }
        ))
    ));
    unchanged(&tx, &before);
    limited = budget();
    limited.max_steps = 1;
    assert!(matches!(
        tx.solve_constraints_with(&rows, limited, &|| false),
        Err(ConstraintSolveError::Unification(
            UnificationError::StepLimit { .. }
        ))
    ));
    unchanged(&tx, &before);
    tx.solve_constraints_with(&rows, budget(), &|| false)
        .unwrap();
}

#[test]
fn malformed_saved_context_is_not_repaired_by_an_innocent_resumer() {
    let mut tx = transaction();
    local(&mut tx, "duplicate", nat());
    local(&mut tx, "duplicate", nat());
    let row = typing(&mut tx, number(7), nat());
    tx.lctx = LocalContext::new();
    let before = tx.clone();
    assert!(
        tx.solve_constraints_with(&[row], budget(), &|| false)
            .is_err()
    );
    unchanged(&tx, &before);
}

fn detached_chain() -> (
    ElabTxn,
    Vec<fln_elab::constraint::Constraint>,
    MVarId,
    ConstraintId,
) {
    let mut tx = transaction();
    let input = goal(&mut tx, "input", nat(), MetavarKind::Natural);
    let output = goal(&mut tx, "output", nat(), MetavarKind::Natural);
    local(&mut tx, "first_scope", nat());
    tx.postpone(
        ConstraintKind::DelayedAssign {
            mvar: output.clone(),
            fvars: vec![],
            val: Expr::mvar(input.clone()),
        },
        0,
    );
    tx.lctx = LocalContext::new();
    local(&mut tx, "second_scope", nat());
    let last = typing(&mut tx, Expr::mvar(output.clone()), nat());
    tx.lctx = LocalContext::new();
    let ready = tx
        .assign_mvar(input, number(7), AssignmentJustification::DirectDefEq)
        .unwrap();
    assert_eq!(ready.len(), 1);
    (tx, ready, output, last)
}

#[test]
fn successive_wakeups_resume_without_reissuing_ids_or_restoring_ambient_binders() {
    let (mut tx, ready, output, last) = detached_chain();
    let first = ready[0].id;
    let report = tx
        .resume_constraints_with(&ready, budget(), &|| false)
        .unwrap();
    assert_eq!(report.solved, vec![first]);
    assert_eq!(tx.mvars.get_assigned_expr(&output), Some(&number(7)));
    assert_eq!(
        report
            .unification
            .awakened
            .iter()
            .map(|r| r.id)
            .collect::<Vec<_>>(),
        vec![last]
    );
    assert_eq!(
        report.unification.awakened[0]
            .local_context
            .as_deref()
            .unwrap()
            .decls()[0]
            .user_name,
        name("second_scope")
    );
    let final_report = tx
        .resume_constraints_with(&report.unification.awakened, budget(), &|| false)
        .unwrap();
    assert_eq!(final_report.solved, vec![last]);
    assert_eq!(final_report.unification.kernel_checks, 1);
    assert!(tx.constraints.is_empty());
    assert!(tx.lctx.is_empty());
    assert_eq!(typing(&mut tx, number(7), nat()), ConstraintId(last.0 + 1));
}

#[test]
fn ready_rows_can_be_resumed_with_their_original_scopes() {
    let (mut tx, row) = saved_typing();
    let ready = tx.constraints.take_ready();
    assert_eq!(ready.len(), 1);
    let report = tx
        .resume_constraints_with(&ready, budget(), &|| false)
        .unwrap();
    assert_eq!(report.solved, vec![row]);
    assert!(tx.constraints.is_empty());
}

#[test]
fn a_resume_failure_keeps_borrowed_rows_retriable_and_assignments_atomic() {
    let (mut tx, mut ready, output, _) = detached_chain();
    let invalid = typing(&mut tx, Expr::sort(Level::zero()), nat());
    ready.push(tx.constraints.remove(&invalid).unwrap());
    let before = tx.clone();
    assert!(
        tx.resume_constraints_with(&ready, budget(), &|| false)
            .is_err()
    );
    unchanged(&tx, &before);
    assert!(!tx.mvars.is_assigned(&output));
    let report = tx
        .resume_constraints_with(&ready[..1], budget(), &|| false)
        .unwrap();
    assert_eq!(report.solved, vec![ready[0].id]);
    assert_eq!(tx.mvars.get_assigned_expr(&output), Some(&number(7)));
}

#[test]
fn resumed_rows_cannot_overwrite_active_rows_or_supply_competing_versions() {
    let (mut tx, row) = saved_typing();
    let still_queued = vec![tx.constraints.constraints()[&row].clone()];
    let before = tx.clone();
    assert!(
        matches!(tx.resume_constraints_with(&still_queued, budget(), &|| false),
        Err(ConstraintSolveError::AlreadyQueued(id)) if id == row)
    );
    unchanged(&tx, &before);
    let detached = tx.constraints.take_ready();
    let duplicates = vec![detached[0].clone(), detached[0].clone()];
    let before = tx.clone();
    assert!(
        matches!(tx.resume_constraints_with(&duplicates, budget(), &|| false),
        Err(ConstraintSolveError::DuplicateResumption(id)) if id == row)
    );
    unchanged(&tx, &before);
    let mut unissued = detached.clone();
    unissued[0].id = ConstraintId(u64::MAX);
    assert!(matches!(
        tx.resume_constraints_with(&unissued, budget(), &|| false),
        Err(ConstraintSolveError::Missing(ConstraintId(u64::MAX)))
    ));
    unchanged(&tx, &before);
    tx.resume_constraints_with(&detached, budget(), &|| false)
        .unwrap();
}

#[test]
fn resumed_selection_is_stable_and_leaves_unselected_queue_rows_alone() {
    for reverse in [false, true] {
        let (mut tx, first) = saved_typing();
        let second = typing(&mut tx, number(3), nat());
        let untouched = typing(&mut tx, number(4), nat());
        let mut rows = vec![
            tx.constraints.remove(&first).unwrap(),
            tx.constraints.remove(&second).unwrap(),
        ];
        if reverse {
            rows.reverse();
        }
        let report = tx
            .resume_constraints_with(&rows, budget(), &|| false)
            .unwrap();
        assert_eq!(report.solved, vec![first, second]);
        assert_eq!(tx.constraints.len(), 1);
        assert!(tx.constraints.constraints().contains_key(&untouched));
    }
}

#[test]
fn resumed_proof_typing_checks_the_obligation_without_solving_the_proof() {
    let mut tx = transaction();
    let p = local(&mut tx, "P", Expr::sort(Level::zero()));
    let proof = goal(&mut tx, "proof", p.clone(), MetavarKind::SyntheticOpaque);
    let id = typing(&mut tx, Expr::mvar(proof.clone()), p);
    let row = tx.constraints.remove(&id).unwrap();
    tx.lctx = LocalContext::new();
    let before = tx.mvars.clone();
    let report = tx
        .resume_constraints_with(&[row], budget(), &|| false)
        .unwrap();
    assert_eq!(report.unification.residual_metavariables, vec![proof]);
    assert_eq!(tx.mvars, before);
}

#[test]
fn resumed_batch_cancellation_cannot_publish_a_successful_inner_transaction() {
    let (base, ready, _, _) = detached_chain();
    let polls = Cell::new(0);
    base.clone()
        .resume_constraints_with(&ready, budget(), &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    let total = polls.get();
    for stop in [1, total / 2, total] {
        let mut tx = base.clone();
        polls.set(0);
        assert!(matches!(
            tx.resume_constraints_with(&ready, budget(), &|| {
                polls.set(polls.get() + 1);
                polls.get() >= stop
            }),
            Err(ConstraintSolveError::Unification(
                UnificationError::Cancelled
            ))
        ));
        unchanged(&tx, &base);
    }
}

#[test]
fn resumed_work_and_assignment_limits_leave_all_state_retriable() {
    let (mut tx, ready, _, _) = detached_chain();
    let before = tx.clone();
    let mut limited = budget();
    limited.max_visited_nodes = 1;
    assert!(matches!(
        tx.resume_constraints_with(&ready, limited, &|| false),
        Err(ConstraintSolveError::Unification(
            UnificationError::NodeLimit { .. }
        ))
    ));
    unchanged(&tx, &before);
    limited = budget();
    limited.max_assignments = 0;
    assert!(matches!(
        tx.resume_constraints_with(&ready, limited, &|| false),
        Err(ConstraintSolveError::Unification(
            UnificationError::AssignmentLimit { .. }
        ))
    ));
    unchanged(&tx, &before);
    tx.resume_constraints_with(&ready, budget(), &|| false)
        .unwrap();
}

#[test]
fn an_instance_request_is_not_disguised_as_a_resumable_equality() {
    let (mut tx, mut ready, output, _) = detached_chain();
    let id = tx.postpone(
        ConstraintKind::SynthInstance {
            class: nat(),
            mvar: output,
        },
        0,
    );
    ready.push(tx.constraints.remove(&id).unwrap());
    let before = tx.clone();
    assert!(
        matches!(tx.resume_constraints_with(&ready, budget(), &|| false),
        Err(ConstraintSolveError::UnsupportedKind(found)) if found == id)
    );
    unchanged(&tx, &before);
}
