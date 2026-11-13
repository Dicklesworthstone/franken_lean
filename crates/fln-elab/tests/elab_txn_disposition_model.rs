//! Property and state-transition model for `TxnDispositionV1`, `ChildTaskDrain`,
//! and outer `Outcome<TxnResolution>` nonpublication invariants
//! (bead `franken_lean-zis`, plan §10.1, FL-INV-01, FL-INV-07).

#![forbid(unsafe_code)]

use fln_core::diag::ResourceReason;
use fln_core::expr::{BinderInfo, Expr, FVarId, MVarId};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::{DataValue, KVMap};
use fln_core::outcome::{
    Authority, CacheAdmission, Inconclusive, InconclusiveCause, InternalFault, Outcome,
    ResourceUsage,
};
use fln_elab::constraint::ConstraintKind;
use fln_elab::decision::DecisionRecord;
use fln_elab::info::Info;
use fln_elab::lctx::LocalContext;
use fln_elab::messages::Message;
use fln_elab::mvar::{AssignmentJustification, MetavarKind};
use fln_elab::seed::bootstrap_nat_environment;
use fln_elab::txn::{
    ChildTaskDrain, ElabTxn, TXN_DISPOSITION_SCHEMA, TXN_DISPOSITION_VERSION, TxnDispositionV1,
    TxnOutcome,
};
use fln_kernel::verdict::Budget;

fn base_txn() -> ElabTxn {
    let env = bootstrap_nat_environment(Budget::for_stack_bytes(1024 * 1024))
        .expect("seed environment must construct");
    ElabTxn::new(env, KVMap::new(), 0x5eed_cafe)
}

fn dirty_child(parent: &ElabTxn, tag: &str, spent_heartbeats: u64) -> (ElabTxn, MVarId) {
    let mut child = parent.child_txn();
    child.budget.heartbeats_consumed = child
        .budget
        .heartbeats_consumed
        .saturating_add(spent_heartbeats);

    let hole = MVarId(Name::from_components([tag, "hole"]));
    child.mvars.declare(
        hole.clone(),
        hole.0.clone(),
        Expr::sort(Level::one()),
        LocalContext::new(),
        MetavarKind::Natural,
        0,
        None,
    );
    child
        .mvars
        .assign(
            hole.clone(),
            Expr::sort(Level::zero()),
            AssignmentJustification::DirectDefEq,
        )
        .expect("fresh child hole assigns");

    let u = LMVarId(Name::from_components([tag, "u"]));
    child.universes.assign(u, Level::one());

    child.lctx.add_param(
        FVarId(Name::from_components([tag, "x"])),
        Name::from_components([tag, "x"]),
        Expr::sort(Level::one()),
        BinderInfo::Default,
    );
    child.postpone(
        ConstraintKind::DefEq {
            lhs: Expr::sort(Level::zero()),
            rhs: Expr::sort(Level::zero()),
        },
        0,
    );
    child.options.insert(
        Name::from_components(["trace", tag]),
        DataValue::OfBool(true),
    );
    child
        .messages
        .add(Message::error(format!("diagnostic:{tag}")));
    child.info_tree.add_leaf(Info::CommandInfo {
        name: Name::from_components(["cmd", tag]),
    });
    (child, hole)
}

#[test]
fn all_five_nested_dispositions_inside_complete_obey_their_publication_contracts() {
    assert_eq!(TXN_DISPOSITION_SCHEMA, "fln.elab.txn_disposition/1");
    let mut parent = base_txn();

    // 1. CommitAll publishes semantic state, diagnostics, options, seed, and revision.
    let cp1 = parent.checkpoint();
    let (child1, hole1) = dirty_child(&parent, "commit_all", 5);
    let expected_seed = child1.seed;
    let res1 = parent
        .resolve_child_outcome(
            &cp1,
            child1,
            Outcome::complete(TxnDispositionV1::CommitAll),
            ChildTaskDrain::new(2, 2, 0),
        )
        .into_complete()
        .expect("CommitAll completes");
    assert_eq!(res1.schema_version, TXN_DISPOSITION_VERSION);
    assert_eq!(res1.disposition_name, "commit_all");
    assert_eq!(res1.heartbeats_charged, 5);
    assert_eq!(res1.parent_revision, 1);
    assert!(parent.mvars.is_assigned(&hole1));
    assert_eq!(parent.mvars.assignment_revision(), 1);
    assert_eq!(parent.seed, expected_seed);
    assert_eq!(parent.messages.len(), 1);
    assert_eq!(parent.info_tree.len(), 1);

    // 2. CommitDiagnosticsOnly retains messages + InfoTree, rolling back semantic state.
    let cp2 = parent.checkpoint();
    let (child2, hole2) = dirty_child(&parent, "diag_only", 3);
    let res2 = parent
        .resolve_child_outcome(
            &cp2,
            child2,
            Outcome::complete(TxnDispositionV1::CommitDiagnosticsOnly),
            ChildTaskDrain::NONE,
        )
        .into_complete()
        .expect("CommitDiagnosticsOnly completes");
    assert_eq!(res2.disposition_name, "commit_diagnostics_only");
    assert_eq!(res2.heartbeats_charged, 3);
    assert_eq!(parent.budget.heartbeats_consumed, 8);
    assert!(!parent.mvars.is_declared(&hole2));
    assert_eq!(parent.mvars.assignment_revision(), 1);
    assert_eq!(parent.messages.len(), 2);
    assert_eq!(parent.info_tree.len(), 2);
    parent.verify_no_term_leaks(&cp2).expect("no semantic leak");

    // 3. Rollback discards both semantic state and diagnostics while charging work.
    let cp3 = parent.checkpoint();
    let (child3, hole3) = dirty_child(&parent, "rollback", 4);
    let res3 = parent
        .resolve_child_outcome(
            &cp3,
            child3,
            Outcome::complete(TxnDispositionV1::rollback("failed_tactic_branch")),
            ChildTaskDrain::new(1, 0, 1),
        )
        .into_complete()
        .expect("Rollback completes");
    assert_eq!(res3.disposition_name, "rollback");
    assert_eq!(res3.heartbeats_charged, 4);
    assert_eq!(parent.budget.heartbeats_consumed, 12);
    assert!(!parent.mvars.is_declared(&hole3));
    assert_eq!(parent.messages.len(), 2);
    assert_eq!(parent.info_tree.len(), 2);
    parent
        .verify_no_state_leaks(&cp3)
        .expect("zero state or diagnostic leak on Rollback");

    // 4. ExposeCandidate retains isolated child context on `exposed_candidate` without publishing.
    let cp4 = parent.checkpoint();
    let (child4, hole4) = dirty_child(&parent, "expose", 2);
    let cand = Expr::mvar(hole4.clone());
    let res4 = parent
        .resolve_child_outcome(
            &cp4,
            child4,
            Outcome::complete(TxnDispositionV1::ExposeCandidate {
                candidate: cand.clone(),
                obligations: vec![hole4.clone()],
            }),
            ChildTaskDrain::NONE,
        )
        .into_complete()
        .expect("ExposeCandidate completes");
    assert_eq!(res4.disposition_name, "expose_candidate");
    assert_eq!(res4.exposed_candidate, Some(cand));
    assert!(!parent.mvars.is_declared(&hole4));
    let exposed = parent
        .take_exposed_candidate()
        .expect("exposed candidate stored");
    assert!(exposed.mvars.is_assigned(&hole4));
    assert_eq!(
        exposed.instantiate_expr().unwrap(),
        Expr::sort(Level::zero())
    );
    parent
        .verify_no_state_leaks(&cp4)
        .expect("taking exposed candidate restores exact parent state");

    // 5. Fork records deterministic fork audit without publishing child state.
    let cp5 = parent.checkpoint();
    let (child5, hole5) = dirty_child(&parent, "fork_marker", 1);
    let res5 = parent
        .resolve_child_outcome(
            &cp5,
            child5,
            Outcome::complete(TxnDispositionV1::from_txn_outcome(TxnOutcome::Fork {
                alternatives_count: 3,
            })),
            ChildTaskDrain::NONE,
        )
        .into_complete()
        .expect("Fork disposition completes");
    assert_eq!(res5.disposition_name, "fork");
    assert!(!parent.mvars.is_declared(&hole5));
    parent
        .verify_no_state_leaks(&cp5)
        .expect("Fork marker publishes no child state");
    assert!(matches!(
        parent.decisions.records().last(),
        Some(DecisionRecord::TransactionFork {
            branch_id: 0,
            num_alternatives: 3
        })
    ));
}

#[test]
fn cancellation_exhaustion_and_internal_fault_never_publish_across_any_child_state() {
    let mut parent = base_txn();
    parent.budget.max_heartbeats = 50;

    let usage = ResourceUsage {
        reason: ResourceReason::Heartbeats {
            consumed: 51,
            limit: 50,
        },
        allowed: 50,
        observed: 51,
    };
    assert!(usage.is_genuine_exhaustion());

    let non_answers: Vec<(&str, Outcome<TxnDispositionV1>)> = vec![
        (
            "cancelled",
            Outcome::Inconclusive(Inconclusive::cancelled("elaboration child cancelled")),
        ),
        (
            "exhausted",
            Outcome::Inconclusive(Inconclusive::resource(usage)),
        ),
        (
            "dep_unavailable",
            Outcome::Inconclusive(Inconclusive::dependency_unavailable("missing import olean")),
        ),
        (
            "internal_fault",
            Outcome::InternalFault(InternalFault::new("FL-INV-07", "simulated child fault")),
        ),
    ];

    let mut expected_heartbeats = 0u64;
    for (tag, child_outcome) in non_answers {
        let cp = parent.checkpoint();
        let (child, hole) = dirty_child(&parent, tag, 6);
        expected_heartbeats += 6;

        let resolved =
            parent.resolve_child_outcome(&cp, child, child_outcome, ChildTaskDrain::new(1, 1, 0));
        assert_eq!(resolved.authority(), Authority::NonAuthoritative);
        assert_eq!(
            resolved.cache_admission(),
            CacheAdmission::Refused {
                authority: Authority::NonAuthoritative
            }
        );
        assert!(!parent.mvars.is_declared(&hole));
        assert_eq!(parent.mvars.assignment_revision(), 0);
        assert_eq!(parent.budget.heartbeats_consumed, expected_heartbeats);
        parent
            .verify_no_state_leaks(&cp)
            .expect("non-authoritative child outcome must never leak state or diagnostics");
    }
}

#[test]
fn budget_overrun_and_undrained_child_tasks_refuse_commit_all_without_publishing() {
    // 1. Undrained child tasks turn an attempted CommitAll into InternalFault with zero publication.
    let mut parent = base_txn();
    let cp_undrained = parent.checkpoint();
    let (child_undrained, hole_undrained) = dirty_child(&parent, "undrained", 4);
    let out_undrained = parent.resolve_child_outcome(
        &cp_undrained,
        child_undrained,
        Outcome::complete(TxnDispositionV1::CommitAll),
        ChildTaskDrain::new(3, 1, 1),
    );
    assert!(matches!(out_undrained, Outcome::InternalFault(_)));
    assert!(!parent.mvars.is_declared(&hole_undrained));
    assert_eq!(parent.budget.heartbeats_consumed, 4);
    parent
        .verify_no_state_leaks(&cp_undrained)
        .expect("undrained child refusal must not publish state");

    // 2. Heartbeat budget overrun converts CommitAll into genuine ResourceExhausted Inconclusive.
    parent.budget.max_heartbeats = 10;
    let cp_overrun = parent.checkpoint();
    let (child_overrun, hole_overrun) = dirty_child(&parent, "overrun", 7);
    let out_overrun = parent.resolve_child_outcome(
        &cp_overrun,
        child_overrun,
        Outcome::complete(TxnDispositionV1::CommitAll),
        ChildTaskDrain::NONE,
    );
    match out_overrun {
        Outcome::Inconclusive(inc) => match inc.cause {
            InconclusiveCause::ResourceExhausted { usage } => {
                assert!(usage.is_genuine_exhaustion());
                assert_eq!(usage.allowed, 10);
                assert_eq!(usage.observed, 11);
            }
            other => panic!("expected ResourceExhausted, got {other:?}"),
        },
        other => panic!("expected Inconclusive on heartbeat overrun, got {other:?}"),
    }
    assert!(!parent.mvars.is_declared(&hole_overrun));
    assert_eq!(parent.budget.heartbeats_consumed, 11);
    parent
        .verify_no_state_leaks(&cp_overrun)
        .expect("heartbeat overrun must charge work and publish nothing");
}

#[test]
fn planted_leaked_assignment_mutant_is_caught_by_audit_and_refused_before_commit() {
    let mut parent = base_txn();
    let pre_hole = MVarId(Name::from_components(["pre_hole"]));
    parent.mvars.declare(
        pre_hole.clone(),
        pre_hole.0.clone(),
        Expr::sort(Level::one()),
        LocalContext::new(),
        MetavarKind::Natural,
        0,
        None,
    );
    let cp = parent.checkpoint();
    let (child, child_hole) = dirty_child(&parent, "after_leak", 2);

    // Planted mutant: an ambient/leaked metavariable assignment mutates `parent` behind the checkpoint.
    parent
        .mvars
        .assign(
            pre_hole.clone(),
            Expr::sort(Level::zero()),
            AssignmentJustification::DirectDefEq,
        )
        .expect("planted leak assigns parent hole");
    assert_eq!(parent.mvars.assignment_revision(), 1);
    assert_eq!(
        parent.verify_no_term_leaks(&cp),
        Err("leak detected: mvar assignments modified after rollback")
    );

    let snapshot_with_leak = parent.clone();
    let resolved = parent.resolve_child_outcome(
        &cp,
        child,
        Outcome::complete(TxnDispositionV1::CommitAll),
        ChildTaskDrain::NONE,
    );
    assert!(
        matches!(resolved, Outcome::InternalFault(_)),
        "leaked parent state must fault rather than commit child on top of corrupted checkpoint"
    );
    assert!(!parent.mvars.is_declared(&child_hole));
    assert_eq!(parent, snapshot_with_leak);
}
