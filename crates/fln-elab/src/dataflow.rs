//! Dataflow node and dependency graph representations (Bet B4, Plan §10.6).
//!
//! In FrankenLean, parsed commands/declarations are dataflow nodes with
//! conservative dependency pre-scans. Elaboration proceeds speculatively
//! in parallel, suspending or aborting only when true dependencies are unready.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_env::constants::ConstantInfo;
use fln_env::environment::Environment;

use crate::decision::DecisionRecord;
use crate::effects::EffectSummary;
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
#[derive(Debug, Clone)]
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

/// A directed acyclic dataflow graph of commands within a module.
#[derive(Debug, Clone, Default)]
pub struct DataflowGraph {
    nodes: Vec<DataflowNode>,
    /// Mapping from declaration name to the CommandId that declares it.
    name_to_producer: HashMap<Name, CommandId>,
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

        // Check name references against previously declared names
        for ref_name in &node.referenced_names {
            if let Some(&producer_id) = self.name_to_producer.get(ref_name)
                && producer_id != node_id
            {
                deps.insert(producer_id);
            }
        }

        // If the node is an ordering barrier, it depends on all predecessors
        if node.declared_effects.is_barrier() {
            for prev_node in &self.nodes {
                deps.insert(prev_node.id);
            }
        }

        // Register producer names
        for decl_name in &node.declared_names {
            self.name_to_producer.insert(decl_name.clone(), node_id);
        }

        // Update dependents
        for &dep in &deps {
            self.dependents.entry(dep).or_default().insert(node_id);
        }

        self.dependencies.insert(node_id, deps);
        self.nodes.push(node);
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
