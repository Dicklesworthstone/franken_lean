//! Root-local instantiation. The surrounding arena is storage, not part of the
//! subject. Keep sparse maps so a small root does not allocate or visit a large
//! unrelated prefix. Traversal and destruction use heap frames, never recursion.
//!
//! As with replacement copying, only reached references are checked here. Wire
//! decoding owns validation of the input representation; this transformation is
//! not an admission shortcut and does not confer authority on any declaration.

mod replacements;

use std::collections::BTreeSet;

use replacements::ReplacementCopies;
use super::*;

fn level_children(node: &LevelNode) -> [Option<LevelId>; 2] {
    match node {
        LevelNode::Succ(child) => [Some(*child), None],
        LevelNode::Max(left, right) | LevelNode::IMax(left, right) => {
            [Some(*left), Some(*right)]
        }
        LevelNode::Zero | LevelNode::Parameter(_) | LevelNode::Meta(_) => [None, None],
    }
}

fn expression_children(node: &ExprNode) -> [Option<ExprId>; 3] {
    match node {
        ExprNode::Apply { function, argument } => [Some(*function), Some(*argument), None],
        ExprNode::Lambda {
            binder_type, body, ..
        }
        | ExprNode::Forall {
            binder_type, body, ..
        } => [Some(*binder_type), Some(*body), None],
        ExprNode::Let {
            type_, value, body, ..
        } => [Some(*type_), Some(*value), Some(*body)],
        ExprNode::Metadata { expression, .. } | ExprNode::Projection { expression, .. } => {
            [Some(*expression), None, None]
        }
        ExprNode::Bound { .. }
        | ExprNode::Free { .. }
        | ExprNode::Meta { .. }
        | ExprNode::Sort { .. }
        | ExprNode::Constant { .. }
        | ExprNode::NatLiteral { .. }
        | ExprNode::StringLiteral(_) => [None, None, None],
    }
}

impl Instantiator<'_, '_> {
    pub(super) fn map_subject_root(
        &mut self,
        source: &[LevelNode],
        root: LevelId,
        mapping: &mut BTreeMap<usize, MappedLevel>,
    ) -> Result<LevelId, Halt> {
        self.map_subject_root_cached(source, root, mapping, &mut ReplacementCopies::default())
    }

    fn map_subject_root_cached(
        &mut self,
        source: &[LevelNode],
        root: LevelId,
        mapping: &mut BTreeMap<usize, MappedLevel>,
        replacements: &mut ReplacementCopies,
    ) -> Result<LevelId, Halt> {
        let input = InstantiationInput::Subject;
        let missing = |index| Halt::Fault(InstantiationFault::MissingLevel { input, index });
        if let Some(mapped) = mapping.get(&root.index()) {
            self.control.poll(root.index())?;
            return Ok(mapped.root);
        }

        let mut needed = BTreeSet::new();
        let mut work = vec![root.index()];
        while let Some(index) = work.pop() {
            if mapping.contains_key(&index) || !needed.insert(index) {
                continue;
            }
            self.control.step(index)?;
            let node = source.get(index).ok_or_else(|| missing(index))?;
            for child in level_children(node).into_iter().flatten() {
                if child.index() >= index {
                    return Err(Halt::Fault(InstantiationFault::NonBackwardLevelReference {
                        input,
                        parent: index,
                        child: child.index(),
                    }));
                }
                work.push(child.index());
            }
        }

        // Backward edges make ascending source IDs a deterministic topological
        // order. Only this root's missing nodes are sorted, not the whole arena.
        for index in needed {
            // Smart constructors can reuse every ancestor without allocating.
            // Those iterations still need a cancellation checkpoint.
            self.control.poll(index)?;
            let node = source.get(index).ok_or_else(|| missing(index))?;
            if let LevelNode::Parameter(name) = node
                && let Some(value_index) = self.parameters.get(name).copied()
            {
                mapping.insert(
                    index,
                    MappedLevel {
                        root: replacements.root(self, value_index)?,
                        // Substitution is simultaneous. The replacement is
                        // copied literally and never enters subject traversal.
                        changed: true,
                    },
                );
                continue;
            }
            let mapped = |child: &LevelId| {
                mapping
                    .get(&child.index())
                    .copied()
                    .ok_or_else(|| missing(child.index()))
            };
            let (node, changed) = match node {
                LevelNode::Succ(child) => {
                    let child = mapped(child)?;
                    (LevelNode::Succ(child.root), child.changed)
                }
                LevelNode::Max(left, right) | LevelNode::IMax(left, right) => {
                    let left = mapped(left)?;
                    let right = mapped(right)?;
                    let copied = if matches!(node, LevelNode::Max(..)) {
                        LevelNode::Max(left.root, right.root)
                    } else {
                        LevelNode::IMax(left.root, right.root)
                    };
                    (copied, left.changed || right.changed)
                }
                node => {
                    // Admit the payload before cloning its owned data.
                    self.control.output(level_owned_units(node), index)?;
                    let root = self.push_level(node.clone(), index)?;
                    mapping.insert(
                        index,
                        MappedLevel {
                            root,
                            changed: false,
                        },
                    );
                    continue;
                }
            };
            let built = if changed {
                self.rebuild(node)?
            } else {
                BuiltLevel::Fresh(node)
            };
            let root = match built {
                BuiltLevel::Existing(root) => root,
                BuiltLevel::Fresh(node) => {
                    self.control.output(level_owned_units(&node), index)?;
                    self.push_level(node, index)?
                }
            };
            mapping.insert(index, MappedLevel { root, changed });
        }
        mapping
            .get(&root.index())
            .map(|mapped| mapped.root)
            .ok_or_else(|| missing(root.index()))
    }

    pub(super) fn copy_subject_root(
        &mut self,
        term: &WireExpr,
    ) -> Result<(Vec<ExprNode>, ExprId), Halt> {
        let missing = |index| Halt::Fault(InstantiationFault::MissingExpression { index });
        let mut needed = BTreeSet::new();
        let mut work = vec![term.root().index()];
        while let Some(index) = work.pop() {
            if !needed.insert(index) {
                continue;
            }
            self.control.step(index)?;
            let node = term.nodes().get(index).ok_or_else(|| missing(index))?;
            Self::validate_expression(index, node)?;
            work.extend(expression_children(node).into_iter().flatten().map(ExprId::index));
        }

        let mut mapping = BTreeMap::<usize, ExprId>::new();
        let mut level_map = BTreeMap::new();
        // One cache spans every universe-bearing expression in this subject,
        // but never outlives the instantiation or crosses source arenas.
        let mut replacements = ReplacementCopies::default();
        let mut nodes = Vec::new();
        for index in needed {
            let source = term.nodes().get(index).ok_or_else(|| missing(index))?;
            self.control.output(expression_owned_units(source), index)?;
            let observed = usize_units(nodes.len()).saturating_add(1);
            self.control.admit_arena_node(observed, index)?;
            let id = ExprId::from_index(nodes.len())
                .ok_or_else(|| self.control.arena_nodes(observed, index))?;
            let mapped = |child: &ExprId| {
                mapping
                    .get(&child.index())
                    .copied()
                    .ok_or_else(|| missing(child.index()))
            };
            let mut node = source.clone();
            match &mut node {
                ExprNode::Apply { function, argument } => {
                    *function = mapped(function)?;
                    *argument = mapped(argument)?;
                }
                ExprNode::Lambda {
                    binder_type, body, ..
                }
                | ExprNode::Forall {
                    binder_type, body, ..
                } => {
                    *binder_type = mapped(binder_type)?;
                    *body = mapped(body)?;
                }
                ExprNode::Let {
                    type_, value, body, ..
                } => {
                    *type_ = mapped(type_)?;
                    *value = mapped(value)?;
                    *body = mapped(body)?;
                }
                ExprNode::Metadata { expression, .. } | ExprNode::Projection { expression, .. } => {
                    *expression = mapped(expression)?;
                }
                ExprNode::Sort { level } => {
                    *level = self.map_subject_root_cached(
                        term.levels(), *level, &mut level_map, &mut replacements,
                    )?;
                }
                ExprNode::Constant { levels, .. } => {
                    for level in levels {
                        *level = self.map_subject_root_cached(
                            term.levels(), *level, &mut level_map, &mut replacements,
                        )?;
                    }
                }
                ExprNode::Bound { .. }
                | ExprNode::Free { .. }
                | ExprNode::Meta { .. }
                | ExprNode::NatLiteral { .. }
                | ExprNode::StringLiteral(_) => {}
            }
            nodes.push(node);
            mapping.insert(index, id);
        }
        let root = mapping
            .get(&term.root().index())
            .copied()
            .ok_or_else(|| missing(term.root().index()))?;
        Ok((nodes, root))
    }
}

#[cfg(test)]
mod tests;
