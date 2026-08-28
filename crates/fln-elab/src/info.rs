//! InfoTree and structured elaboration tree recording for Athanor (plan §10.1).
//!
//! Provides structured term/tactic/command info nodes for LSP inspection,
//! goal viewing, and semantic navigation.

use fln_core::expr::{Expr, FVarId, MVarId};
use fln_core::name::Name;
use crate::lctx::LocalContext;

/// The semantic payload of an info tree node (Lean.Elab.Info).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Info {
    /// Contextual scope info providing local context.
    ContextInfo {
        lctx: LocalContext,
    },
    /// Elaborated term info associated with a syntax node.
    TermInfo {
        lctx: LocalContext,
        expr: Expr,
        expected_type: Option<Expr>,
        is_binder: bool,
    },
    /// Tactic invocation info before and after step execution.
    TacticInfo {
        tactic_name: Name,
        goals_before: Vec<MVarId>,
        goals_after: Vec<MVarId>,
    },
    /// Command execution info.
    CommandInfo {
        name: Name,
    },
    /// Free variable binding info.
    FVarInfo {
        id: FVarId,
        user_name: Name,
    },
}

/// A node in the InfoTree hierarchy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InfoNode {
    pub info: Info,
    pub children: Vec<InfoNode>,
}

/// An InfoTree representing the structured elaboration trace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InfoTree {
    Context(LocalContext, Box<InfoTree>),
    Node(Info, Vec<InfoTree>),
    Hole(MVarId),
}

/// Builder for recording and constructing InfoTrees.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InfoTreeBuilder {
    trees: Vec<InfoTree>,
    active_stack: Vec<Vec<InfoTree>>,
}

impl InfoTreeBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.trees.is_empty() && self.active_stack.is_empty()
    }

    pub fn len(&self) -> usize {
        self.trees.len()
    }

    pub fn trees(&self) -> &[InfoTree] {
        &self.trees
    }

    pub fn push_scope(&mut self) {
        self.active_stack.push(Vec::new());
    }

    pub fn pop_scope(&mut self, info: Info) {
        let children = self.active_stack.pop().unwrap_or_default();
        let node = InfoTree::Node(info, children);
        if let Some(parent_scope) = self.active_stack.last_mut() {
            parent_scope.push(node);
        } else {
            self.trees.push(node);
        }
    }

    pub fn add_leaf(&mut self, info: Info) {
        let node = InfoTree::Node(info, Vec::new());
        if let Some(parent_scope) = self.active_stack.last_mut() {
            parent_scope.push(node);
        } else {
            self.trees.push(node);
        }
    }

    pub fn add_tree(&mut self, tree: InfoTree) {
        if let Some(parent_scope) = self.active_stack.last_mut() {
            parent_scope.push(tree);
        } else {
            self.trees.push(tree);
        }
    }

    pub fn append(&mut self, other: &mut InfoTreeBuilder) {
        self.trees.append(&mut other.trees);
    }

    pub fn truncate(&mut self, checkpoint: usize) {
        self.trees.truncate(checkpoint);
        self.active_stack.clear();
    }
}
