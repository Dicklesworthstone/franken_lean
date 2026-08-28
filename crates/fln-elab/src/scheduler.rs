//! Deterministic dataflow scheduler (Bet B4, Plan §10.6, FL-INV-01).
//!
//! Declarations execute speculatively in parallel against immutable snapshots.
//! Commits merge in **canonical source order** with commit-time read-set
//! validation and rebase/retry on conflict.
//!
//! Schedule independence: the final environment, diagnostic message stream,
//! InfoTrees, and decision ledgers are bit-for-bit identical at any thread count (1, 8, 32).

use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use fln_core::outcome::Outcome;
use fln_env::environment::{DeclAdmission, Environment};
use fln_env::pmap::CollisionBudget;

use crate::dataflow::{CommandId, DataflowGraph, ElabUnitProduct};
use crate::decision::DecisionRecord;
use crate::effects::EffectSummary;
use crate::info::InfoTree;
use crate::messages::Message;
use crate::txn::ElabBudget;

/// Configuration parameters for the deterministic scheduler.
#[derive(Debug, Clone)]
pub struct ExecutionConfig {
    /// Number of worker threads (e.g., 1, 8, 32).
    pub worker_threads: usize,
    /// Whether speculative parallel execution is enabled.
    pub enable_speculation: bool,
    /// Resource and heartbeat budget for elaboration.
    pub budget: ElabBudget,
}

impl Default for ExecutionConfig {
    fn default() -> Self {
        Self {
            worker_threads: 1,
            enable_speculation: true,
            budget: ElabBudget::default(),
        }
    }
}

/// The deterministic output of executing a module's dataflow graph.
#[derive(Debug, Clone)]
pub struct SchedulerOutput {
    /// The final committed Grimoire environment.
    pub final_environment: Environment,
    /// Canonical diagnostic message stream (ordered by source position).
    pub messages: Vec<Message>,
    /// Canonical InfoTree sequence (ordered by source position).
    pub info_trees: Vec<InfoTree>,
    /// Canonical decision ledger records.
    pub decisions: Vec<DecisionRecord>,
    /// Dynamic effect summaries for each command.
    pub effects: BTreeMap<CommandId, EffectSummary>,
    /// Sequence of committed command IDs.
    pub committed_order: Vec<CommandId>,
    /// Number of speculative re-elaborations / retries performed.
    pub retry_count: usize,
}

/// Deterministic scheduler executing dataflow graphs under `FL-INV-01`.
pub struct DeterministicScheduler;

impl DeterministicScheduler {
    /// Execute a dataflow graph sequentially.
    pub fn execute_sequential(
        graph: &DataflowGraph,
        base_env: &Environment,
        budget: &ElabBudget,
    ) -> Outcome<Result<SchedulerOutput, String>> {
        let mut current_env = base_env.clone();
        let mut all_messages = Vec::new();
        let mut all_info_trees = Vec::new();
        let mut all_decisions = Vec::new();
        let mut all_effects = BTreeMap::new();
        let mut committed_order = Vec::new();

        for node in graph.nodes() {
            let outcome = (node.elab_fn)(&current_env, budget);
            let product = match outcome {
                Outcome::Complete(Ok(p)) => p,
                Outcome::Complete(Err(e)) => return Outcome::complete(Err(e)),
                Outcome::Inconclusive(inc) => return Outcome::Inconclusive(inc),
                Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
            };

            for decl in &product.admitted_decls {
                match current_env.try_add_decl_with_budget(
                    decl.clone(),
                    1,
                    CollisionBudget::UNBOUNDED,
                ) {
                    Outcome::Complete(DeclAdmission::Admitted(new_env)) => {
                        current_env = new_env;
                    }
                    Outcome::Complete(DeclAdmission::Rejected(err)) => {
                        return Outcome::complete(Err(format!(
                            "Failed to admit declaration {:?}: {err:?}",
                            decl.name()
                        )));
                    }
                    Outcome::Inconclusive(inc) => return Outcome::Inconclusive(inc),
                    Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
                }
            }

            all_messages.extend(product.messages);
            if let Some(tree) = product.info_tree {
                all_info_trees.push(tree);
            }
            all_decisions.extend(product.decisions);
            all_effects.insert(node.id, product.effects);
            committed_order.push(node.id);
        }

        Outcome::complete(Ok(SchedulerOutput {
            final_environment: current_env,
            messages: all_messages,
            info_trees: all_info_trees,
            decisions: all_decisions,
            effects: all_effects,
            committed_order,
            retry_count: 0,
        }))
    }

    /// Execute a dataflow graph in parallel with canonical merge and optimistic concurrency.
    pub fn execute_parallel(
        graph: &DataflowGraph,
        base_env: &Environment,
        config: &ExecutionConfig,
    ) -> Outcome<Result<SchedulerOutput, String>> {
        if config.worker_threads <= 1 || !config.enable_speculation || graph.len() <= 1 {
            return Self::execute_sequential(graph, base_env, &config.budget);
        }

        let num_nodes = graph.len();
        let retry_count = Arc::new(AtomicUsize::new(0));

        // Shared speculative results pool: CommandId -> Staged Product
        let staged_results = Arc::new(Mutex::new(HashMap::<CommandId, ElabUnitProduct>::new()));

        // Snapshot of base environment for initial speculative passes
        let base_snapshot = Arc::new(base_env.clone());

        // Launch worker threads to speculatively execute independent/ready nodes
        std::thread::scope(|s| {
            let chunk_size = num_nodes.div_ceil(config.worker_threads);
            for worker_id in 0..config.worker_threads {
                let start_idx = worker_id * chunk_size;
                let end_idx = (start_idx + chunk_size).min(num_nodes);
                if start_idx >= end_idx {
                    continue;
                }

                let nodes_slice: Vec<_> = graph.nodes()[start_idx..end_idx].to_vec();
                let staged_ref = Arc::clone(&staged_results);
                let base_snap = Arc::clone(&base_snapshot);
                let budget = config.budget.clone();

                s.spawn(move || {
                    for node in nodes_slice {
                        // Speculative execution against base snapshot
                        let outcome = (node.elab_fn)(&base_snap, &budget);
                        if let Outcome::Complete(Ok(product)) = outcome {
                            let mut lock = staged_ref.lock().unwrap();
                            lock.insert(node.id, product);
                        }
                    }
                });
            }
        });

        // Canonical Merge Loop (runs in strict source order 0..num_nodes)
        let mut current_env = base_env.clone();
        let mut all_messages = Vec::new();
        let mut all_info_trees = Vec::new();
        let mut all_decisions = Vec::new();
        let mut all_effects = BTreeMap::new();
        let mut committed_order = Vec::new();

        let mut staged_map = match Arc::try_unwrap(staged_results) {
            Ok(mutex) => mutex.into_inner().unwrap(),
            Err(arc) => arc.lock().unwrap().clone(),
        };

        for node in graph.nodes() {
            let mut product_opt = staged_map.remove(&node.id);

            // Read-set validation: check if speculative product is valid over current_env
            let needs_rebase = match &product_opt {
                Some(product) => {
                    let mut invalid = false;
                    for read_decl in product.effects.read_decls() {
                        if !base_snapshot.contains(read_decl) || !current_env.contains(read_decl) {
                            invalid = true;
                            break;
                        }
                    }
                    invalid
                }
                None => true,
            };

            let product = if needs_rebase {
                // Rebase / re-elaborate directly against current committed environment
                retry_count.fetch_add(1, Ordering::Relaxed);
                let outcome = (node.elab_fn)(&current_env, &config.budget);
                match outcome {
                    Outcome::Complete(Ok(p)) => p,
                    Outcome::Complete(Err(e)) => return Outcome::complete(Err(e)),
                    Outcome::Inconclusive(inc) => return Outcome::Inconclusive(inc),
                    Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
                }
            } else {
                product_opt.take().unwrap()
            };

            // Commit declarations into current_env
            for decl in &product.admitted_decls {
                match current_env.try_add_decl_with_budget(
                    decl.clone(),
                    1,
                    CollisionBudget::UNBOUNDED,
                ) {
                    Outcome::Complete(DeclAdmission::Admitted(new_env)) => {
                        current_env = new_env;
                    }
                    Outcome::Complete(DeclAdmission::Rejected(err)) => {
                        return Outcome::complete(Err(format!(
                            "Failed to admit declaration {:?}: {err:?}",
                            decl.name()
                        )));
                    }
                    Outcome::Inconclusive(inc) => return Outcome::Inconclusive(inc),
                    Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
                }
            }

            all_messages.extend(product.messages);
            if let Some(tree) = product.info_tree {
                all_info_trees.push(tree);
            }
            all_decisions.extend(product.decisions);
            all_effects.insert(node.id, product.effects);
            committed_order.push(node.id);
        }

        Outcome::complete(Ok(SchedulerOutput {
            final_environment: current_env,
            messages: all_messages,
            info_trees: all_info_trees,
            decisions: all_decisions,
            effects: all_effects,
            committed_order,
            retry_count: retry_count.load(Ordering::Relaxed),
        }))
    }

    /// Execute a dataflow graph using the provided configuration.
    pub fn execute(
        graph: &DataflowGraph,
        base_env: &Environment,
        config: &ExecutionConfig,
    ) -> Outcome<Result<SchedulerOutput, String>> {
        if config.worker_threads > 1 && config.enable_speculation {
            Self::execute_parallel(graph, base_env, config)
        } else {
            Self::execute_sequential(graph, base_env, &config.budget)
        }
    }
}
