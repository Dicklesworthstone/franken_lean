//! Dataflow node and dependency graph representations (Bet B4, Plan §10.6).
//!
//! In FrankenLean, parsed commands/declarations are dataflow nodes with
//! conservative dependency pre-scans. Elaboration proceeds speculatively
//! in parallel, suspending or aborting only when true dependencies are unready.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_env::constants::ConstantInfo;
use fln_env::environment::Environment;

use crate::decision::DecisionRecord;
use crate::effects::{CommandEffect, DeclAspect, EffectSummary};
use crate::info::InfoTree;
use crate::messages::Message;
use crate::txn::ElabBudget;

/// Source position / sequential index of a command within a module.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CommandId(pub usize);

impl std::fmt::Display for CommandId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.0)
    }
}

/// The result produced by elaborating a single dataflow command node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElabUnitProduct {
    /// Declarations admitted/defined by this command.
    pub admitted_decls: Vec<ConstantInfo>,
    /// Diagnostic messages produced during elaboration.
    pub messages: Vec<Message>,
    /// InfoTree recorded during elaboration.
    pub info_tree: Option<InfoTree>,
    /// Dynamic effect summary captured during elaboration.
    pub effects: EffectSummary,
    /// Decision records recorded for replayable provenance.
    pub decisions: Vec<DecisionRecord>,
}

impl ElabUnitProduct {
    /// Create an empty successful product.
    pub fn empty() -> Self {
        Self {
            admitted_decls: Vec::new(),
            messages: Vec::new(),
            info_tree: None,
            effects: EffectSummary::new(),
            decisions: Vec::new(),
        }
    }
}

/// An executable closure representing the elaboration of one command.
pub type CommandElabFn = Arc<
    dyn Fn(&Environment, &ElabBudget) -> Outcome<Result<ElabUnitProduct, String>> + Send + Sync,
>;

/// A node in the module's elaboration dataflow graph.
#[derive(Clone)]
pub struct DataflowNode {
    /// Sequential source index.
    pub id: CommandId,
    /// Primary name defined by this node, if any.
    pub name: Option<Name>,
    /// All names declared or published by this node.
    pub declared_names: Vec<Name>,
    /// Names referenced or queried by this node (conservative pre-scan).
    pub referenced_names: Vec<Name>,
    /// Static / declared effect summary from parsing.
    pub declared_effects: EffectSummary,
    /// The executable elaboration closure.
    pub elab_fn: CommandElabFn,
}

impl DataflowNode {
    /// Conservative footprint including both typed effects and name pre-scans.
    /// Negative name queries remain reads: a later writer must not change the
    /// snapshot against which an earlier command was elaborated.
    pub fn dependency_effects(&self) -> EffectSummary {
        let mut effects = self.declared_effects.clone();
        for name in self.name.iter().chain(&self.declared_names) {
            effects.record(CommandEffect::WritesDecl { name: name.clone() });
        }
        for name in &self.referenced_names {
            effects.record(CommandEffect::ReadsDecl {
                name: name.clone(),
                aspect: DeclAspect::All,
            });
        }
        effects
    }
}

impl std::fmt::Debug for DataflowNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DataflowNode")
            .field("id", &self.id)
            .field("name", &self.name)
            .field("declared_names", &self.declared_names)
            .field("referenced_names", &self.referenced_names)
            .field("declared_effects", &self.declared_effects)
            .finish()
    }
}

/// Only domains with precise read AND write effects need an access index.
/// Simp/option reads conflict with generic extension writers, handled as global
/// barriers below. Names in different typed domains must not alias.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum DependencyKey {
    Declaration(Name),
    Instances(Name),
    Grammar(Name),
}

#[derive(Debug, Clone, Default)]
struct KeyAccesses {
    readers: HashSet<CommandId>,
    writers: HashSet<CommandId>,
}

fn keyed_access(effect: &CommandEffect) -> Option<(DependencyKey, bool)> {
    match effect {
        CommandEffect::ReadsDecl { name, .. } => {
            Some((DependencyKey::Declaration(name.clone()), false))
        }
        CommandEffect::WritesDecl { name } => {
            Some((DependencyKey::Declaration(name.clone()), true))
        }
        CommandEffect::ReadsInstances { class_head } => {
            Some((DependencyKey::Instances(class_head.clone()), false))
        }
        CommandEffect::WritesInstance { class_head, .. } => {
            Some((DependencyKey::Instances(class_head.clone()), true))
        }
        CommandEffect::ReadsGrammar { category } => {
            Some((DependencyKey::Grammar(category.clone()), false))
        }
        CommandEffect::WritesGrammar { category } => {
            Some((DependencyKey::Grammar(category.clone()), true))
        }
        CommandEffect::ReadsSimpSet { .. }
        | CommandEffect::ReadsOption { .. }
        | CommandEffect::WritesEnvExtension { .. }
        | CommandEffect::UsesCapability { .. }
        | CommandEffect::Opaque { .. } => None,
    }
}

/// A directed acyclic dataflow graph of commands within a module.
#[derive(Debug, Clone, Default)]
pub struct DataflowGraph {
    nodes: Vec<DataflowNode>,
    /// Per-key access history: constructing disjoint nodes does not scan the
    /// entire prefix. Work is proportional to effects and conflicting edges.
    accesses: HashMap<DependencyKey, KeyAccesses>,
    barriers: HashSet<CommandId>,
    /// Predecessors of each node (nodes that must execute/commit before this node).
    dependencies: HashMap<CommandId, HashSet<CommandId>>,
    /// Successors of each node (nodes that depend on this node).
    dependents: HashMap<CommandId, HashSet<CommandId>>,
}

impl DataflowGraph {
    /// Create an empty dataflow graph.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a node to the graph and compute conservative dependency edges.
    pub fn add_node(&mut self, node: DataflowNode) {
        let node_id = node.id;
        let mut deps = HashSet::new();

        let footprint = node.dependency_effects();
        // All edges point backwards in insertion/source order. Both sides of
        // a barrier matter, including successors with completely empty effects.
        if footprint.is_barrier() {
            deps.extend(self.nodes.iter().map(|previous| previous.id));
        } else {
            deps.extend(self.barriers.iter().copied());
        }
        let accesses: Vec<_> = footprint.effects().iter().filter_map(keyed_access).collect();
        for (key, write) in &accesses {
            if let Some(previous) = self.accesses.get(key) {
                deps.extend(previous.writers.iter().copied());
                if *write {
                    deps.extend(previous.readers.iter().copied());
                }
            }
        }
        // Record only AFTER querying all keys, so a command reading and writing
        // the same declaration cannot accidentally depend on itself.
        for (key, write) in accesses {
            let history = self.accesses.entry(key).or_default();
            if write {
                history.writers.insert(node_id);
            } else {
                history.readers.insert(node_id);
            }
        }
        if footprint.is_barrier() {
            self.barriers.insert(node_id);
        }
        // Duplicate identities remain an explicit validate() refusal.
        deps.remove(&node_id);

        // Update dependents
        for &dep in &deps {
            self.dependents.entry(dep).or_default().insert(node_id);
        }

        self.dependencies.insert(node_id, deps);
        self.nodes.push(node);
    }

    /// Validate command identity and the source-order DAG before executing any
    /// callbacks. Legacy `add_node` stays infallible; duplicate IDs are rejected
    /// here rather than letting one staged product stand in for two commands.
    pub fn validate(&self) -> Result<(), String> {
        let mut seen = HashSet::new();
        for node in &self.nodes {
            if !seen.insert(node.id) {
                return Err(format!("duplicate command ID {}", node.id));
            }
        }
        seen.clear();
        for node in &self.nodes {
            let dependencies = self
                .dependencies_of(node.id)
                .ok_or_else(|| format!("missing dependencies for command {}", node.id))?;
            for dependency in dependencies {
                if !seen.contains(dependency) {
                    return Err(format!(
                        "command {} depends on non-preceding command {dependency}",
                        node.id
                    ));
                }
            }
            seen.insert(node.id);
        }
        Ok(())
    }

    /// Commands to re-elaborate after an edit, including the changed commands
    /// and their transitive dependents. Results follow SOURCE order, not hash
    /// iteration or numeric ID order. Unknown change IDs fail closed.
    pub fn affected_commands(&self, changed: &[CommandId]) -> Result<Vec<CommandId>, String> {
        self.validate()?;
        let mut affected = HashSet::new();
        let mut pending = Vec::new();
        for &id in changed {
            if !self.dependencies.contains_key(&id) {
                return Err(format!("unknown changed command ID {id}"));
            }
            if affected.insert(id) {
                pending.push(id);
            }
        }
        while let Some(id) = pending.pop() {
            if let Some(dependents) = self.dependents_of(id) {
                for &dependent in dependents {
                    if affected.insert(dependent) {
                        pending.push(dependent);
                    }
                }
            }
        }
        Ok(self
            .nodes
            .iter()
            .filter(|node| affected.contains(&node.id))
            .map(|node| node.id)
            .collect())
    }

    /// Rebuild dependencies with observed reads/writes, without changing this
    /// graph or dropping conservative pre-scan edges. Dynamic negative queries
    /// and inferred dependencies therefore participate in later invalidation.
    pub fn with_observed_effects(
        &self,
        observed: &BTreeMap<CommandId, EffectSummary>,
    ) -> Result<Self, String> {
        self.validate()?;
        for id in observed.keys() {
            if !self.dependencies.contains_key(id) {
                return Err(format!("effects for unknown command ID {id}"));
            }
        }
        let mut graph = Self::new();
        for original in &self.nodes {
            let mut node = original.clone();
            if let Some(effects) = observed.get(&node.id) {
                node.declared_effects.extend(effects);
            }
            graph.add_node(node);
        }
        Ok(graph)
    }

    /// All nodes in source order.
    pub fn nodes(&self) -> &[DataflowNode] {
        &self.nodes
    }

    /// Number of nodes in the graph.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the graph is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Get direct dependencies of a node.
    pub fn dependencies_of(&self, id: CommandId) -> Option<&HashSet<CommandId>> {
        self.dependencies.get(&id)
    }

    /// Get direct dependents of a node.
    pub fn dependents_of(&self, id: CommandId) -> Option<&HashSet<CommandId>> {
        self.dependents.get(&id)
    }
}
