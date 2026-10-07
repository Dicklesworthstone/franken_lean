//! The static call graph of a set of decoded `.ir` modules (bead
//! `fln-ir-decoder-call-graph-sjzl`, item 5).
//!
//! The pin's IR is first-order: a full or partial application names its
//! target. So the direct edges are exact, and what the graph cannot see is
//! exactly a call through a closure value (`ap`), which names nothing.
//!
//! Reachability here is a fact about names. It grants no authority and decides
//! nothing about what may be executed.
use super::{IrDecl, IrModule};
use fln_core::name::Name;
use std::collections::BTreeMap;

pub type NodeId = u32;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum IrNodeKind {
    /// A declaration with a body.
    Function,
    /// An `extern` declaration: its code is not IR.
    Extern,
    /// Named as a call target, declared by no module in the set.
    Undeclared,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrGraphError {
    /// More declarations and call targets than a [`NodeId`] can number.
    TooManyNodes,
}

impl std::fmt::Display for IrGraphError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "IR call graph: {self:?}")
    }
}

impl std::error::Error for IrGraphError {}

/// A call graph over the modules added so far. Node numbers follow the order
/// in which names are first met, so the same modules in the same order give
/// the same graph.
#[derive(Debug, Clone, Default)]
pub struct IrCallGraph {
    names: Vec<Name>,
    kinds: Vec<IrNodeKind>,
    /// The module that declares each node, as an index into `labels`.
    modules: Vec<Option<u32>>,
    labels: Vec<String>,
    callees: Vec<Vec<NodeId>>,
    index: BTreeMap<Name, NodeId>,
    duplicates: Vec<(NodeId, u32)>,
}

impl IrCallGraph {
    pub fn new() -> Self {
        Self::default()
    }

    fn intern(&mut self, name: &Name) -> Result<NodeId, IrGraphError> {
        if let Some(id) = self.index.get(name) {
            return Ok(*id);
        }
        let id = NodeId::try_from(self.names.len()).map_err(|_| IrGraphError::TooManyNodes)?;
        self.names.push(name.clone());
        self.kinds.push(IrNodeKind::Undeclared);
        self.modules.push(None);
        self.callees.push(Vec::new());
        self.index.insert(name.clone(), id);
        Ok(id)
    }

    /// Add one module's declarations under `label`. A name an earlier module
    /// already declared keeps its first declaration; the repeat is recorded in
    /// [`Self::duplicates`] and its body contributes no edges.
    pub fn add_module(&mut self, label: &str, module: &IrModule) -> Result<(), IrGraphError> {
        let module_index =
            u32::try_from(self.labels.len()).map_err(|_| IrGraphError::TooManyNodes)?;
        self.labels.push(label.to_owned());
        for decl in &module.decls {
            let id = self.intern(decl.name())?;
            if self.modules[id as usize].is_some() {
                self.duplicates.push((id, module_index));
                continue;
            }
            self.modules[id as usize] = Some(module_index);
            self.kinds[id as usize] = match decl {
                IrDecl::Function { .. } => IrNodeKind::Function,
                IrDecl::Extern { .. } => IrNodeKind::Extern,
            };
            let mut targets = Vec::new();
            for callee in decl.callees() {
                targets.push(self.intern(callee)?);
            }
            targets.sort_unstable();
            targets.dedup();
            self.callees[id as usize] = targets;
        }
        Ok(())
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }

    pub fn edge_count(&self) -> usize {
        self.callees.iter().map(Vec::len).sum()
    }

    pub fn node(&self, name: &Name) -> Option<NodeId> {
        self.index.get(name).copied()
    }

    pub fn name(&self, id: NodeId) -> &Name {
        &self.names[id as usize]
    }

    pub fn kind(&self, id: NodeId) -> IrNodeKind {
        self.kinds[id as usize]
    }

    /// The label of the module that declares `id`; `None` for an undeclared name.
    pub fn module(&self, id: NodeId) -> Option<&str> {
        self.modules[id as usize].map(|index| self.labels[index as usize].as_str())
    }

    /// Direct call targets, ascending, each once.
    pub fn callees(&self, id: NodeId) -> &[NodeId] {
        &self.callees[id as usize]
    }

    /// Later declarations of an already-declared name: the node and the label
    /// of the module whose declaration was not used.
    pub fn duplicates(&self) -> impl Iterator<Item = (NodeId, &str)> {
        self.duplicates
            .iter()
            .map(|(id, module)| (*id, self.labels[*module as usize].as_str()))
    }

    /// Everything `roots` reach. A node is reached when a root is it or a
    /// reached node that `descend` accepted calls it; `descend` is asked once
    /// per reached node, and a node it refuses is reached but not looked
    /// through. The answer is indexed by node. Iterative: depth costs no stack.
    pub fn reach(
        &self,
        roots: impl IntoIterator<Item = NodeId>,
        mut descend: impl FnMut(NodeId) -> bool,
    ) -> Vec<bool> {
        let mut reached = vec![false; self.names.len()];
        let mut pending = Vec::new();
        for root in roots {
            if !std::mem::replace(&mut reached[root as usize], true) {
                pending.push(root);
            }
        }
        while let Some(id) = pending.pop() {
            if !descend(id) {
                continue;
            }
            for callee in &self.callees[id as usize] {
                if !std::mem::replace(&mut reached[*callee as usize], true) {
                    pending.push(*callee);
                }
            }
        }
        reached
    }
}
