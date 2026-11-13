//! No-mock end-to-end fault recovery, child task drain, Crucible kernel check,
//! and {1, 8, 32}-thread schedule-independence verification for `ElabTxn`
//! (bead `franken_lean-zis`, plan §10.1 & §10.6, FL-INV-01, FL-INV-07).

#![forbid(unsafe_code)]

use fln_core::expr::{Expr, Literal, MVarId, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::{Inconclusive, Outcome};
use fln_elab::dataflow::{CommandId, DataflowGraph, DataflowNode, ElabUnitProduct};
use fln_elab::effects::EffectSummary;
use fln_elab::info::Info;
use fln_elab::lctx::LocalContext;
use fln_elab::messages::Message;
use fln_elab::mvar::{AssignmentJustification, MetavarKind};
use fln_elab::scheduler::{DeterministicScheduler, ExecutionConfig};
use fln_elab::seed::bootstrap_nat_environment;
use fln_elab::txn::{ChildTaskDrain, ElabBudget, ElabTxn, TxnDispositionV1};
use fln_env::constants::{
    ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
};
use fln_env::environment::Environment;
use fln_kernel::verdict::{Budget, Verdict};
use fln_kernel::{Declaration, check};
use std::sync::Arc;

type BranchTask = Box<dyn FnOnce(usize, ElabTxn) -> Outcome<(ElabTxn, TxnDispositionV1)> + Send>;

fn name1(s: impl AsRef<str>) -> Name {
    Name::from_components([s.as_ref()])
}

fn elaborate_command_with_fault_recovery(
    env: &Environment,
    budget: &ElabBudget,
    cmd_idx: usize,
    fork_workers: usize,
) -> Outcome<Result<ElabUnitProduct, String>> {
    let mut root_txn = ElabTxn::new(env.clone(), KVMap::new(), 1_000 + cmd_idx as u64);
    root_txn.budget = budget.clone();
    let cp = root_txn.checkpoint();

    let nat_ty = Expr::const_(Name::from_components(["Nat"]), Vec::new());
    let value = Expr::lit(Literal::Nat(NatLit::from_u64(cmd_idx as u64)));

    // Spawn 4 speculative child branches:
    //   0 -> cooperative cancellation after mutating mvars/messages
    //   1 -> heartbeat exhaustion after mutating mvars/messages
    //   2 -> simulated tactic panic caught at worker boundary as InternalFault
    //   3 -> valid synthesis assigning `?ans := value`, checked via real `fln_kernel::check`!
    let nat_ty_b0 = nat_ty.clone();
    let nat_ty_b1 = nat_ty.clone();
    let nat_ty_b3 = nat_ty.clone();
    let value_b3 = value.clone();

    let tasks: Vec<BranchTask> = vec![
        Box::new(move |_branch_id, mut child| {
            child.budget.check_heartbeat().ok();
            let leaked = MVarId(name1(format!("cancel_m_{cmd_idx}")));
            child.mvars.declare(
                leaked.clone(),
                leaked.0.clone(),
                nat_ty_b0,
                LocalContext::new(),
                MetavarKind::Natural,
                0,
                None,
            );
            child
                .mvars
                .assign(
                    leaked,
                    Expr::sort(Level::zero()),
                    AssignmentJustification::DirectDefEq,
                )
                .unwrap();
            child.messages.add(Message::error("cancelled branch noise"));
            Outcome::Inconclusive(Inconclusive::cancelled(format!("cmd_{cmd_idx}_branch_0")))
        }),
        Box::new(move |_branch_id, mut child| {
            child.budget.max_heartbeats = 2;
            child.budget.heartbeats_consumed = child.budget.heartbeats_consumed.saturating_add(3);
            let leaked = MVarId(name1(format!("exhaust_m_{cmd_idx}")));
            child.mvars.declare(
                leaked,
                Name::from_components(["exhaust"]),
                nat_ty_b1,
                LocalContext::new(),
                MetavarKind::Natural,
                0,
                None,
            );
            Outcome::complete((child, TxnDispositionV1::CommitAll))
        }),
        Box::new(move |_branch_id, _child| {
            panic!("simulated untrusted tactic panic in cmd {cmd_idx} branch 2");
        }),
        Box::new(move |_branch_id, mut child| {
            child
                .budget
                .check_heartbeat()
                .expect("branch 3 within budget");
            let goal = MVarId(name1(format!("goal_{cmd_idx}")));
            child.mvars.declare(
                goal.clone(),
                goal.0.clone(),
                nat_ty_b3,
                LocalContext::new(),
                MetavarKind::Synthetic,
                0,
                None,
            );
            child
                .assign_mvar(
                    goal,
                    value_b3,
                    AssignmentJustification::Tactic {
                        tactic_name: Name::from_components(["exact"]),
                    },
                )
                .expect("goal assigns");
            child
                .messages
                .add(Message::info(format!("elaborated cmd_{cmd_idx}")));
            child.info_tree.add_leaf(Info::CommandInfo {
                name: name1(format!("decl_{cmd_idx}")),
            });
            Outcome::complete((child, TxnDispositionV1::CommitAll))
        }),
    ];

    let (branch_outcomes, drain) = root_txn.run_fork_tasks(fork_workers, tasks, &|| false);
    assert!(drain.is_fully_drained());
    assert_eq!(drain.spawned_tasks, 4);
    assert_eq!(drain.joined_tasks, 4);

    // Branches 0, 1, 2 fail non-authoritatively and MUST NOT publish anything into `root_txn`.
    assert!(matches!(branch_outcomes[0], Outcome::Inconclusive(_)));
    assert!(matches!(branch_outcomes[1], Outcome::Inconclusive(_)));
    assert!(matches!(branch_outcomes[2], Outcome::InternalFault(_)));

    for non_auth in branch_outcomes.iter().take(3) {
        let probe_child = root_txn.child_txn();
        let non_auth_disp = match non_auth {
            Outcome::Inconclusive(inc) => Outcome::Inconclusive(inc.clone()),
            Outcome::InternalFault(flt) => Outcome::InternalFault(flt.clone()),
            Outcome::Complete(_) => unreachable!(),
        };
        let res =
            root_txn.resolve_child_outcome(&cp, probe_child, non_auth_disp, ChildTaskDrain::NONE);
        assert!(!res.authority().as_bool());
        root_txn
            .verify_no_state_leaks(&cp)
            .expect("failed/cancelled/faulted sibling never leaks into parent");
    }

    // Branch 3 commits cleanly.
    let (winner_child, winner_disp) = branch_outcomes
        .into_iter()
        .nth(3)
        .unwrap()
        .into_complete()
        .expect("branch 3 completes");
    let resolution = root_txn
        .resolve_child_outcome(&cp, winner_child, Outcome::complete(winner_disp), drain)
        .into_complete()
        .expect("branch 3 CommitAll resolves");
    assert_eq!(resolution.disposition_name, "commit_all");
    assert_eq!(resolution.parent_revision, 1);

    let goal_id = MVarId(name1(format!("goal_{cmd_idx}")));
    let instantiated = root_txn
        .instantiate_expr(&Expr::mvar(goal_id))
        .expect("universe instantiation");

    let decl_name = name1(format!("recovered_nat_{cmd_idx}"));
    let def_val = DefinitionVal {
        base: ConstantVal {
            name: decl_name.clone(),
            level_params: Vec::new(),
            type_: nat_ty,
        },
        value: instantiated,
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![decl_name.clone()],
    };

    // Pass candidate through real Crucible `fln_kernel::check` (no mocks!).
    let kernel_outcome = check(
        &root_txn.env,
        &Declaration::Defn(def_val.clone()),
        Budget::for_stack_bytes(1024 * 1024),
    );
    match kernel_outcome {
        Outcome::Complete(Verdict::Accepted { .. }) => {}
        Outcome::Complete(Verdict::Rejected { class, message, .. }) => {
            return Outcome::complete(Err(format!(
                "kernel rejected {decl_name:?}: {class:?}: {message}"
            )));
        }
        Outcome::Inconclusive(stop) => return Outcome::Inconclusive(stop),
        Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
    }

    let mut product = ElabUnitProduct::empty();
    product.admitted_decls.push(ConstantInfo::Defn(def_val));
    product.messages = root_txn.messages.messages().to_vec();
    product.info_tree = root_txn.info_tree.trees().first().cloned();
    product.decisions = root_txn.decisions.records().to_vec();
    Outcome::complete(Ok(product))
}

#[test]
fn fault_recovery_and_parallel_elaboration_are_schedule_independent_at_1_8_and_32_threads() {
    let base_env = bootstrap_nat_environment(Budget::for_stack_bytes(1024 * 1024))
        .expect("seed environment must construct");

    let mut snapshots = Vec::new();
    for threads in [1usize, 8, 32] {
        let mut graph = DataflowGraph::new();
        for cmd_idx in 0..12usize {
            let decl_name = name1(format!("recovered_nat_{cmd_idx}"));
            graph.add_node(DataflowNode {
                id: CommandId(cmd_idx),
                name: Some(decl_name.clone()),
                declared_names: vec![decl_name],
                referenced_names: vec![Name::from_components(["Nat"])],
                declared_effects: EffectSummary::new(),
                elab_fn: Arc::new(move |env, budget| {
                    elaborate_command_with_fault_recovery(env, budget, cmd_idx, threads)
                }),
            });
        }

        let config = ExecutionConfig {
            worker_threads: threads,
            enable_speculation: true,
            budget: ElabBudget::new(200_000, 512),
        };
        let out = DeterministicScheduler::execute_parallel(&graph, &base_env, &config)
            .into_complete()
            .expect("parallel fault-recovery run must complete")
            .expect("all 12 commands must elaborate and pass kernel check");

        assert_eq!(out.committed_order.len(), 12);
        assert_eq!(out.messages.len(), 12);
        assert_eq!(out.info_trees.len(), 12);
        for cmd_idx in 0..12usize {
            let decl_name = name1(format!("recovered_nat_{cmd_idx}"));
            assert!(
                out.final_environment.find(&decl_name).is_some(),
                "threads={threads}: missing admitted declaration {decl_name:?}"
            );
        }
        snapshots.push((
            threads,
            out.final_environment.logical_root(&KVMap::new()),
            out.messages,
            out.info_trees,
            out.decisions,
            out.committed_order,
        ));
    }

    let (_, ref root_1, ref msgs_1, ref trees_1, ref decs_1, ref order_1) = snapshots[0];
    for (threads, root_n, msgs_n, trees_n, decs_n, order_n) in &snapshots[1..] {
        assert_eq!(root_n, root_1, "logical root drifted at {threads} threads");
        assert_eq!(msgs_n, msgs_1, "messages drifted at {threads} threads");
        assert_eq!(trees_n, trees_1, "InfoTrees drifted at {threads} threads");
        assert_eq!(
            decs_n, decs_1,
            "DecisionLedger drifted at {threads} threads"
        );
        assert_eq!(
            order_n, order_1,
            "committed_order drifted at {threads} threads"
        );
    }
}
