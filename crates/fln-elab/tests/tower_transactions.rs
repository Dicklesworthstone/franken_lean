//! Comprehensive verification tests for the Monadic Tower, ElabTxn, 5 outcomes,
//! audited rollback, and targeted wake-up dependency graph (bead `franken_lean-zis`, plan §10.1).

#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, FVarId, MVarId};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_elab::constraint::{ConstraintKind, ConstraintQueue};
use fln_elab::info::Info;
use fln_elab::lctx::LocalContext;
use fln_elab::messages::Message;
use fln_elab::mvar::{AssignmentJustification, MetavarError, MetavarKind, MetavarStore};
use fln_elab::seed::bootstrap_nat_environment;
use fln_elab::txn::{ElabTxn, TxnOutcome};
use fln_elab::universe::UniverseStore;
use fln_kernel::verdict::Budget;
use std::collections::HashSet;

#[test]
fn test_five_transaction_outcomes_algebra() {
    let budget = Budget::for_stack_bytes(1024 * 1024);
    let env = bootstrap_nat_environment(budget).expect("seed environment must construct");
    let mut root_txn = ElabTxn::new(env, KVMap::new(), 42);

    // 1. Test CommitAll
    let cp1 = root_txn.checkpoint();
    let mut child1 = root_txn.child_txn();
    let mvar1 = MVarId(Name::from_components(["m1"]));
    child1.mvars.declare(
        mvar1.clone(),
        Name::from_components(["_hole1"]),
        Expr::sort(Level::one()),
        LocalContext::new(),
        MetavarKind::Natural,
        0,
        None,
    );
    child1
        .mvars
        .assign(
            mvar1.clone(),
            Expr::sort(Level::zero()),
            AssignmentJustification::DirectDefEq,
        )
        .unwrap();
    child1.messages.add(Message::info("child1 committed"));
    child1.lctx.add_param(
        FVarId(Name::from_components(["x"])),
        Name::from_components(["x"]),
        Expr::sort(Level::one()),
        BinderInfo::Default,
    );

    root_txn
        .commit_outcome(&cp1, child1, TxnOutcome::CommitAll)
        .unwrap();
    assert_eq!(root_txn.mvars.len(), 1);
    assert!(root_txn.mvars.is_assigned(&mvar1));
    assert_eq!(root_txn.messages.len(), 1);
    assert_eq!(root_txn.lctx.len(), 1);

    // 2. Test CommitDiagnosticsOnly
    let cp2 = root_txn.checkpoint();
    let mut child2 = root_txn.child_txn();
    let mvar2 = MVarId(Name::from_components(["m2"]));
    child2.mvars.declare(
        mvar2.clone(),
        Name::from_components(["_hole2"]),
        Expr::sort(Level::one()),
        LocalContext::new(),
        MetavarKind::Natural,
        0,
        None,
    );
    child2
        .mvars
        .assign(
            mvar2.clone(),
            Expr::sort(Level::zero()),
            AssignmentJustification::DirectDefEq,
        )
        .unwrap();
    child2
        .messages
        .add(Message::error("failed alternative in child2"));
    child2.info_tree.add_leaf(Info::CommandInfo {
        name: Name::from_components(["test_cmd"]),
    });
    child2.lctx.add_param(
        FVarId(Name::from_components(["y"])),
        Name::from_components(["y"]),
        Expr::sort(Level::one()),
        BinderInfo::Default,
    );

    root_txn
        .commit_outcome(&cp2, child2, TxnOutcome::CommitDiagnosticsOnly)
        .unwrap();
    // Mvars and local context from child2 must be rolled back
    assert_eq!(root_txn.mvars.len(), 1);
    assert!(!root_txn.mvars.is_declared(&mvar2));
    assert_eq!(root_txn.lctx.len(), 1);
    // Messages and info tree from child2 must be committed into parent
    assert_eq!(root_txn.messages.len(), 2);
    assert!(root_txn.messages.has_errors());
    assert_eq!(root_txn.info_tree.len(), 1);

    // 3. Test Rollback (Zero leaks!)
    let cp3 = root_txn.checkpoint();
    let mut child3 = root_txn.child_txn();
    let mvar3 = MVarId(Name::from_components(["m3"]));
    child3.mvars.declare(
        mvar3.clone(),
        Name::from_components(["_hole3"]),
        Expr::sort(Level::one()),
        LocalContext::new(),
        MetavarKind::Natural,
        0,
        None,
    );
    child3.messages.add(Message::error("should not leak"));
    child3.info_tree.add_leaf(Info::CommandInfo {
        name: Name::from_components(["leaked_cmd"]),
    });
    child3.lctx.add_param(
        FVarId(Name::from_components(["z"])),
        Name::from_components(["z"]),
        Expr::sort(Level::one()),
        BinderInfo::Default,
    );

    root_txn
        .commit_outcome(&cp3, child3, TxnOutcome::Rollback)
        .unwrap();
    // Verify zero state leaks
    assert_eq!(root_txn.mvars.len(), cp3.mvar_decls_count);
    assert_eq!(
        root_txn.mvars.assignments().len(),
        cp3.mvar_assignments_count
    );
    assert_eq!(root_txn.lctx.len(), cp3.lctx_count);
    assert_eq!(root_txn.messages.len(), cp3.messages_count);
    assert_eq!(root_txn.info_tree.len(), cp3.info_tree_count);

    // 4. Test ExposeCandidate
    let cp4 = root_txn.checkpoint();
    let child4 = root_txn.child_txn();
    let candidate_expr = Expr::sort(Level::one());
    let obligations = vec![mvar1.clone()];
    let candidate_res = root_txn
        .commit_outcome(
            &cp4,
            child4,
            TxnOutcome::ExposeCandidate {
                candidate: candidate_expr.clone(),
                obligations,
            },
        )
        .unwrap();
    assert_eq!(candidate_res, Some(candidate_expr));

    // 5. Test Fork
    let forks = root_txn.fork(4);
    assert_eq!(forks.len(), 4);
    // All forks have distinct seeds
    let seeds: HashSet<u64> = forks.iter().map(|f| f.seed).collect();
    assert_eq!(seeds.len(), 4);
}

#[test]
fn test_audited_rollback_catches_planted_leak_mutant() {
    let budget = Budget::for_stack_bytes(1024 * 1024);
    let env = bootstrap_nat_environment(budget).expect("seed environment must construct");
    let mut txn = ElabTxn::new(env, KVMap::new(), 100);
    let cp = txn.checkpoint();

    // Plant mutant 1: dirty mvar leaked
    txn.mvars.declare(
        MVarId(Name::from_components(["leaked_mvar"])),
        Name::from_components(["leak"]),
        Expr::sort(Level::zero()),
        LocalContext::new(),
        MetavarKind::Natural,
        0,
        None,
    );
    assert_eq!(
        txn.verify_no_state_leaks(&cp),
        Err("leak detected: mvar decls modified after rollback")
    );
}

#[test]
fn test_targeted_wake_up_precision_no_spurious_rescheduling() {
    let mut store = MetavarStore::new();
    let mut queue = ConstraintQueue::new();

    let m1 = MVarId(Name::from_components(["m1"]));
    let m2 = MVarId(Name::from_components(["m2"]));
    let m3 = MVarId(Name::from_components(["m3"]));

    store.declare(
        m1.clone(),
        Name::from_components(["m1"]),
        Expr::sort(Level::one()),
        LocalContext::new(),
        MetavarKind::Natural,
        0,
        None,
    );
    store.declare(
        m2.clone(),
        Name::from_components(["m2"]),
        Expr::sort(Level::one()),
        LocalContext::new(),
        MetavarKind::Natural,
        0,
        None,
    );
    store.declare(
        m3.clone(),
        Name::from_components(["m3"]),
        Expr::sort(Level::one()),
        LocalContext::new(),
        MetavarKind::Natural,
        0,
        None,
    );

    // C1 reads {m1}
    let mut reads_c1 = HashSet::new();
    reads_c1.insert(m1.clone());
    let id_c1 = queue.enqueue(
        ConstraintKind::DefEq {
            lhs: Expr::sort(Level::zero()),
            rhs: Expr::sort(Level::zero()),
        },
        reads_c1,
        0,
    );

    // C2 reads {m2}
    let mut reads_c2 = HashSet::new();
    reads_c2.insert(m2.clone());
    let id_c2 = queue.enqueue(
        ConstraintKind::DefEq {
            lhs: Expr::sort(Level::zero()),
            rhs: Expr::sort(Level::zero()),
        },
        reads_c2,
        0,
    );

    // C3 reads {m1, m3}
    let mut reads_c3 = HashSet::new();
    reads_c3.insert(m1.clone());
    reads_c3.insert(m3.clone());
    let id_c3 = queue.enqueue(
        ConstraintKind::DefEq {
            lhs: Expr::sort(Level::zero()),
            rhs: Expr::sort(Level::zero()),
        },
        reads_c3,
        0,
    );

    assert_eq!(queue.len(), 3);

    // Assigning m1 must wake up C1 and C3 ONLY. C2 must NOT be woken up (precision!).
    let woke_up_m1 = queue.wake_up_for_mvar(&m1);
    let woke_up_ids: HashSet<_> = woke_up_m1.iter().map(|c| c.id).collect();
    assert_eq!(woke_up_ids.len(), 2);
    assert!(woke_up_ids.contains(&id_c1));
    assert!(woke_up_ids.contains(&id_c3));
    assert!(!woke_up_ids.contains(&id_c2));

    // C2 remains in the queue
    assert_eq!(queue.len(), 1);

    // Assigning m2 wakes up C2
    let woke_up_m2 = queue.wake_up_for_mvar(&m2);
    assert_eq!(woke_up_m2.len(), 1);
    assert_eq!(woke_up_m2[0].id, id_c2);
    assert_eq!(queue.len(), 0);
}

#[test]
fn test_mvar_occurs_check_refusal() {
    let mut store = MetavarStore::new();
    let m1 = MVarId(Name::from_components(["m1"]));
    store.declare(
        m1.clone(),
        Name::from_components(["m1"]),
        Expr::sort(Level::one()),
        LocalContext::new(),
        MetavarKind::Natural,
        0,
        None,
    );

    // ?m1 := App(Const("f"), ?m1) -> occurs check failure
    let cyclic_val = Expr::app(
        Expr::const_(Name::from_components(["f"]), Vec::new()),
        Expr::mvar(m1.clone()),
    );
    let err = store
        .assign(m1.clone(), cyclic_val, AssignmentJustification::DirectDefEq)
        .unwrap_err();
    assert_eq!(err, MetavarError::OccursCheckFailed { id: m1 });
}

#[test]
fn test_synthetic_opaque_blocked_from_direct_defeq() {
    let mut store = MetavarStore::new();
    let m_opaque = MVarId(Name::from_components(["m_opaque"]));
    store.declare(
        m_opaque.clone(),
        Name::from_components(["m_opaque"]),
        Expr::sort(Level::one()),
        LocalContext::new(),
        MetavarKind::SyntheticOpaque,
        0,
        None,
    );

    let err = store
        .assign(
            m_opaque.clone(),
            Expr::sort(Level::zero()),
            AssignmentJustification::DirectDefEq,
        )
        .unwrap_err();
    assert_eq!(err, MetavarError::SyntheticOpaqueBlocked { id: m_opaque });
}

#[test]
fn test_universe_store_instantiation() {
    let mut universes = UniverseStore::new();
    let u1 = LMVarId(Name::from_components(["u1"]));
    let u2 = LMVarId(Name::from_components(["u2"]));

    universes.assign(u1.clone(), Level::zero());
    universes.assign(u2.clone(), Level::succ(Level::zero()).unwrap());

    let compound_level = Level::max(Level::mvar(u1), Level::mvar(u2)).unwrap();
    let instantiated = universes.instantiate(&compound_level).unwrap();
    let expected = Level::max(Level::zero(), Level::succ(Level::zero()).unwrap()).unwrap();
    assert_eq!(instantiated, expected);
}
