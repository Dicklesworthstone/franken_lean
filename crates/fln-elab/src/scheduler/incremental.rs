//! Failure-atomic, dependency-directed reuse over a fixed imported environment.
//!
//! Rebuild from the base on every run; replaying on top of the previous final
//! environment would retain deleted declarations and obsolete diagnostics.
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

use fln_core::outcome::{InternalFault, Outcome};
use fln_env::environment::Environment;

use crate::dataflow::{CommandId, DataflowGraph, ElabUnitProduct};
use crate::effects::{CommandEffect, EffectSummary};
use crate::txn::ElabBudget;

use super::{SchedulerOutput, invoke, product_footprint};

/// A complete incremental run and its canonical reuse/execution accounting.
#[derive(Debug, Clone)]
pub struct IncrementalOutput {
    pub output: SchedulerOutput,
    pub executed_commands: Vec<CommandId>,
    pub reused_commands: Vec<CommandId>,
}

#[derive(Debug, Clone)]
struct CachedModule {
    source_graph: DataflowGraph,
    dependencies: DataflowGraph,
    products: BTreeMap<CommandId, ElabUnitProduct>,
    observed: BTreeMap<CommandId, EffectSummary>,
    budget: ElabBudget,
}

/// An in-memory command cache bound to one immutable imported environment.
///
/// Supply changed IDs when source or captured inputs change. New callback Arcs
/// and changed pre-scan metadata are detected automatically. Call
/// `reset_base_environment` when imports/options represented by the base change.
/// Reordering, adding or deleting commands currently causes a conservative cold
/// run; unchanged layouts reuse only outside the old AND new dependency cones.
///
/// Callback effects must obey the same contract as DeterministicScheduler.
/// Ambient/opaque/registry writers are never replayed from a cached product.
/// This is an executable scheduler API, not automatic source-editor wiring.
#[derive(Debug, Clone)]
pub struct IncrementalScheduler {
    base_environment: Environment,
    committed: Option<CachedModule>,
}

impl IncrementalScheduler {
    pub fn new(base_environment: &Environment) -> Self {
        Self {
            base_environment: base_environment.clone(),
            committed: None,
        }
    }

    /// Replace imported authority and discard every product derived from it.
    pub fn reset_base_environment(&mut self, base_environment: &Environment) {
        self.base_environment = base_environment.clone();
        self.committed = None;
    }

    /// Discard reuse state without changing the imported environment.
    pub fn clear(&mut self) {
        self.committed = None;
    }

    /// Execute dirty commands and replay independent authoritative products.
    /// The cache is published only after ALL commands and admissions complete;
    /// a rejection, cancellation, resource stop or fault leaves it unchanged.
    pub fn execute(
        &mut self,
        graph: &DataflowGraph,
        changed: &[CommandId],
        budget: &ElabBudget,
    ) -> Outcome<Result<IncrementalOutput, String>> {
        let dirty = match self.invalidation_plan(graph, changed, budget) {
            Ok(dirty) => dirty,
            Err(error) => return Outcome::complete(Err(error)),
        };
        let mut output = SchedulerOutput::empty(&self.base_environment);
        let mut products = BTreeMap::new();
        let mut observed = BTreeMap::new();
        let mut executed_commands = Vec::new();
        let mut reused_commands = Vec::new();
        let mut changed_effects = EffectSummary::new();
        let previous_nodes: HashMap<_, _> = self
            .committed
            .iter()
            .flat_map(|cache| cache.source_graph.nodes())
            .map(|node| (node.id, node))
            .collect();

        for node in graph.nodes() {
            let cached_product = self
                .committed
                .as_ref()
                .and_then(|cache| cache.products.get(&node.id));
            let reusable = !dirty.contains(&node.id)
                && cached_product.is_some_and(|product| {
                    let effects = product_footprint(node, product);
                    effects.is_replay_safe() && effects.commutes_with(&changed_effects)
                });
            let product = if reusable {
                let Some(product) = cached_product else {
                    return Outcome::InternalFault(InternalFault::new(
                        "FL-INV-01",
                        "incremental reuse selected an absent product",
                    ));
                };
                reused_commands.push(node.id);
                product.clone()
            } else {
                let product = match invoke(node, &output.final_environment, budget) {
                    Outcome::Complete(Ok(product)) => product,
                    Outcome::Complete(Err(error)) => return Outcome::complete(Err(error)),
                    Outcome::Inconclusive(stop) => return Outcome::Inconclusive(stop),
                    Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
                };
                executed_commands.push(node.id);
                // New publications can expose a dependency absent from BOTH
                // previous graphs (e.g. a negative query becomes positive).
                // Old writes matter too: removed outputs must invalidate readers.
                changed_effects.extend(&product_footprint(node, &product));
                if let Some(cache) = &self.committed {
                    if let Some(previous) = cache.observed.get(&node.id) {
                        changed_effects.extend(previous);
                    }
                    if let Some(previous) = previous_nodes.get(&node.id) {
                        changed_effects.extend(&previous.dependency_effects());
                    }
                }
                product
            };
            let mut effects = product.effects.clone();
            for declaration in &product.admitted_decls {
                effects.record(CommandEffect::WritesDecl {
                    name: declaration.name().clone(),
                });
            }
            observed.insert(node.id, effects);
            products.insert(node.id, product.clone());
            match output.commit(node.id, product) {
                Outcome::Complete(Ok(())) => {}
                Outcome::Complete(Err(error)) => return Outcome::complete(Err(error)),
                Outcome::Inconclusive(stop) => return Outcome::Inconclusive(stop),
                Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
            }
        }

        let dependencies = match graph.with_observed_effects(&observed) {
            Ok(dependencies) => dependencies,
            Err(error) => return Outcome::complete(Err(error)),
        };
        self.committed = Some(CachedModule {
            source_graph: graph.clone(),
            dependencies,
            products,
            observed,
            budget: budget.clone(),
        });
        Outcome::complete(Ok(IncrementalOutput {
            output,
            executed_commands,
            reused_commands,
        }))
    }

    fn invalidation_plan(
        &self,
        graph: &DataflowGraph,
        changed: &[CommandId],
        budget: &ElabBudget,
    ) -> Result<HashSet<CommandId>, String> {
        graph.validate()?;
        for &id in changed {
            let current = graph.dependencies_of(id).is_some();
            let previous = self.committed.as_ref().is_some_and(|cache| {
                cache.source_graph.dependencies_of(id).is_some()
            });
            if !current && !previous {
                return Err(format!("unknown changed command ID {id}"));
            }
        }
        let Some(cache) = &self.committed else {
            return Ok(graph.nodes().iter().map(|node| node.id).collect());
        };
        let same_layout = graph.nodes().iter().map(|node| node.id)
            .eq(cache.source_graph.nodes().iter().map(|node| node.id));
        if !same_layout || &cache.budget != budget {
            return Ok(graph.nodes().iter().map(|node| node.id).collect());
        }

        let mut dirty: HashSet<_> = changed.iter().copied().collect();
        for (previous, current) in cache.source_graph.nodes().iter().zip(graph.nodes()) {
            if previous.name != current.name
                || previous.declared_names != current.declared_names
                || previous.referenced_names != current.referenced_names
                || previous.declared_effects != current.declared_effects
                || !Arc::ptr_eq(&previous.elab_fn, &current.elab_fn)
                || !cache.products.get(&current.id).is_some_and(|product| {
                    product_footprint(current, product).is_replay_safe()
                })
            {
                dirty.insert(current.id);
            }
        }
        let current_dependencies = graph.with_observed_effects(&cache.observed)?;
        let mut pending: Vec<_> = dirty.iter().copied().collect();
        // Traverse the UNION graph, not two independent one-shot closures:
        // old A -> B and new B -> C must invalidate C when A changes.
        while let Some(id) = pending.pop() {
            for dependencies in [&cache.dependencies, &current_dependencies] {
                if let Some(dependents) = dependencies.dependents_of(id) {
                    for &dependent in dependents {
                        if dirty.insert(dependent) {
                            pending.push(dependent);
                        }
                    }
                }
            }
        }
        Ok(dirty)
    }
}
