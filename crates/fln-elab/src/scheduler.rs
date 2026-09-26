//! Deterministic dataflow scheduler (Bet B4, Plan §10.6, FL-INV-01).
//!
//! Ready commands execute against a committed immutable snapshot in bounded
//! source-order batches. Dependencies and non-replayable effects split batches.
//! Products merge canonically, with observed-footprint validation against every
//! intervening commit. Stops and faults are never turned into successful retries.
//!
//! Successful products have the same environment, messages, InfoTrees and
//! decisions as sequential execution under the command effect contract.

use std::collections::{BTreeMap, HashSet};
use std::panic::{AssertUnwindSafe, catch_unwind};

use fln_core::outcome::{Inconclusive, InternalFault, Outcome};
use fln_env::environment::{DeclAdmission, Environment};
use fln_env::pmap::CollisionBudget;

use crate::dataflow::{CommandId, DataflowGraph, DataflowNode, ElabUnitProduct};
use crate::decision::DecisionRecord;
use crate::effects::{CommandEffect, EffectSummary};
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

impl SchedulerOutput {
    fn empty(base_env: &Environment) -> Self {
        Self {
            final_environment: base_env.clone(),
            messages: Vec::new(),
            info_trees: Vec::new(),
            decisions: Vec::new(),
            effects: BTreeMap::new(),
            committed_order: Vec::new(),
            retry_count: 0,
        }
    }

    /// No output escapes unless the entire run completes. Declaration admission
    /// still uses the ordinary environment door, including on cache replay.
    fn commit(
        &mut self,
        id: CommandId,
        product: ElabUnitProduct,
    ) -> Outcome<Result<(), String>> {
        for decl in &product.admitted_decls {
            match self.final_environment.try_add_decl_with_budget(
                decl.clone(),
                1,
                CollisionBudget::UNBOUNDED,
            ) {
                Outcome::Complete(DeclAdmission::Admitted(environment)) => {
                    self.final_environment = environment;
                }
                Outcome::Complete(DeclAdmission::Rejected(error)) => {
                    return Outcome::complete(Err(format!(
                        "Failed to admit declaration {:?}: {error:?}",
                        decl.name()
                    )));
                }
                Outcome::Inconclusive(stop) => return Outcome::Inconclusive(stop),
                Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
            }
        }
        self.messages.extend(product.messages);
        if let Some(tree) = product.info_tree {
            self.info_trees.push(tree);
        }
        self.decisions.extend(product.decisions);
        self.effects.insert(id, product.effects);
        self.committed_order.push(id);
        Outcome::complete(Ok(()))
    }
}

type CommandOutcome = Outcome<Result<ElabUnitProduct, String>>;

/// Include actual publications even when a producer omitted WritesDecl from
/// its dynamic effect log. Static pre-scans are conservative and never removed.
fn product_footprint(node: &DataflowNode, product: &ElabUnitProduct) -> EffectSummary {
    let mut effects = node.dependency_effects();
    effects.extend(&product.effects);
    for declaration in &product.admitted_decls {
        effects.record(CommandEffect::WritesDecl {
            name: declaration.name().clone(),
        });
    }
    effects
}

/// A callback panic is an invariant failure, not a rejected source program.
fn invoke(node: &DataflowNode, environment: &Environment, budget: &ElabBudget) -> CommandOutcome {
    match catch_unwind(AssertUnwindSafe(|| (node.elab_fn)(environment, budget))) {
        Ok(outcome) => outcome,
        Err(_) => Outcome::InternalFault(InternalFault::new(
            "FL-INV-01",
            format!("elaboration callback for command {} panicked", node.id),
        )),
    }
}

fn run_batch(
    nodes: &[DataflowNode],
    environment: &Environment,
    budget: &ElabBudget,
) -> Outcome<Vec<CommandOutcome>> {
    if let [node] = nodes {
        return Outcome::complete(vec![invoke(node, environment, budget)]);
    }
    std::thread::scope(|scope| {
        let mut handles = Vec::with_capacity(nodes.len());
        for node in nodes {
            let worker = std::thread::Builder::new()
                .spawn_scoped(scope, move || invoke(node, environment, budget));
            match worker {
                Ok(handle) => handles.push((node.id, handle)),
                Err(error) => {
                    // Scoped workers already started are joined before returning.
                    // No staged success is published from an incomplete batch.
                    return Outcome::Inconclusive(Inconclusive::dependency_unavailable(format!(
                        "elaboration worker for command {}: {error}",
                        node.id
                    )));
                }
            }
        }
        Outcome::complete(
            handles
                .into_iter()
                .map(|(id, handle)| match handle.join() {
                    Ok(outcome) => outcome,
                    Err(_) => Outcome::InternalFault(InternalFault::new(
                        "FL-INV-01",
                        format!("elaboration worker for command {id} panicked"),
                    )),
                })
                .collect(),
        )
    })
}

/// Deterministic scheduler executing dataflow graphs under `FL-INV-01`.
pub struct DeterministicScheduler;

impl DeterministicScheduler {
    /// Execute a dataflow graph sequentially, validating IDs before any callbacks.
    pub fn execute_sequential(
        graph: &DataflowGraph,
        base_env: &Environment,
        budget: &ElabBudget,
    ) -> Outcome<Result<SchedulerOutput, String>> {
        if let Err(error) = graph.validate() {
            return Outcome::complete(Err(error));
        }
        let mut output = SchedulerOutput::empty(base_env);
        for node in graph.nodes() {
            let product = match invoke(node, &output.final_environment, budget) {
                Outcome::Complete(Ok(product)) => product,
                Outcome::Complete(Err(error)) => return Outcome::complete(Err(error)),
                Outcome::Inconclusive(stop) => return Outcome::Inconclusive(stop),
                Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
            };
            match output.commit(node.id, product) {
                Outcome::Complete(Ok(())) => {}
                Outcome::Complete(Err(error)) => return Outcome::complete(Err(error)),
                Outcome::Inconclusive(stop) => return Outcome::Inconclusive(stop),
                Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
            }
        }
        Outcome::complete(Ok(output))
    }

    /// Execute bounded ready prefixes, never speculating across a barrier or
    /// ahead of a declared dependency. Batch width is capped by worker_threads.
    pub fn execute_parallel(
        graph: &DataflowGraph,
        base_env: &Environment,
        config: &ExecutionConfig,
    ) -> Outcome<Result<SchedulerOutput, String>> {
        if config.worker_threads <= 1 || !config.enable_speculation || graph.len() <= 1 {
            return Self::execute_sequential(graph, base_env, &config.budget);
        }
        if let Err(error) = graph.validate() {
            return Outcome::complete(Err(error));
        }
        let mut output = SchedulerOutput::empty(base_env);
        let mut committed = HashSet::new();
        let nodes = graph.nodes();
        let mut next = 0;
        while next < nodes.len() {
            let limit = next.saturating_add(config.worker_threads).min(nodes.len());
            let mut end = next;
            while end < limit {
                let candidate = &nodes[end];
                if !candidate.dependency_effects().is_replay_safe()
                    || !graph.dependencies_of(candidate.id).is_some_and(|dependencies| {
                        dependencies.iter().all(|id| committed.contains(id))
                    })
                {
                    break;
                }
                end += 1;
            }
            if end == next {
                // A non-replayable command runs exactly once at its canonical
                // position, after all earlier commands and before any later ones.
                end += 1;
            }
            let batch = &nodes[next..end];
            let concurrent = batch.len() > 1;
            let outcomes = match run_batch(batch, &output.final_environment, &config.budget) {
                Outcome::Complete(outcomes) => outcomes,
                Outcome::Inconclusive(stop) => return Outcome::Inconclusive(stop),
                Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
            };
            let mut intervening = EffectSummary::new();
            let mut environment_changed = false;
            for (index, (node, outcome)) in batch.iter().zip(outcomes).enumerate() {
                let mut product = match outcome {
                    Outcome::Complete(Ok(product)) => Some(product),
                    // A semantic error may depend on a declaration published
                    // since the snapshot. Resource/cancellation/fault outcomes
                    // are not semantic errors and must NEVER take this retry.
                    Outcome::Complete(Err(_)) if environment_changed => None,
                    Outcome::Complete(Err(error)) => return Outcome::complete(Err(error)),
                    Outcome::Inconclusive(stop) => return Outcome::Inconclusive(stop),
                    Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
                };
                if concurrent
                    && product.as_ref().is_some_and(|product| {
                        !product_footprint(node, product).is_replay_safe()
                    })
                {
                    return undeclared_replay_effect(node.id);
                }
                let needs_rebase = match &product {
                    Some(product) => index > 0
                        && !product_footprint(node, product).commutes_with(&intervening),
                    None => true,
                };
                if needs_rebase {
                    output.retry_count += 1;
                    product = match invoke(node, &output.final_environment, &config.budget) {
                        Outcome::Complete(Ok(product)) => Some(product),
                        Outcome::Complete(Err(error)) => return Outcome::complete(Err(error)),
                        Outcome::Inconclusive(stop) => return Outcome::Inconclusive(stop),
                        Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
                    };
                }
                let Some(product) = product else {
                    return Outcome::InternalFault(InternalFault::new(
                        "FL-INV-01",
                        "successful rebase produced no command product",
                    ));
                };
                let footprint = product_footprint(node, &product);
                if concurrent && !footprint.is_replay_safe() {
                    return undeclared_replay_effect(node.id);
                }
                environment_changed |= !product.admitted_decls.is_empty();
                intervening.extend(&footprint);
                match output.commit(node.id, product) {
                    Outcome::Complete(Ok(())) => {}
                    Outcome::Complete(Err(error)) => return Outcome::complete(Err(error)),
                    Outcome::Inconclusive(stop) => return Outcome::Inconclusive(stop),
                    Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
                }
                committed.insert(node.id);
            }
            next = end;
        }
        Outcome::complete(Ok(output))
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

fn undeclared_replay_effect(id: CommandId) -> Outcome<Result<SchedulerOutput, String>> {
    Outcome::InternalFault(InternalFault::new(
        "FL-INV-01",
        format!("command {id} reported a non-replayable effect after parallel execution; \
                 declare it before scheduling"),
    ))
}
