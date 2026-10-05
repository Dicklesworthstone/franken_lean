//! Distinguish a reused local definition from a cycle in local definitions.
//!
//! A name occurring twice in the reduction trace is not a cycle: with
//! `f := fun x => x`, `f (f a)` must reduce to `a`. On a second unfolding,
//! inspect the binding dependency graph instead. Only a back edge on the
//! current DFS path proves a cycle; completed subgraphs may be shared.
//!
//! The traversal is iterative, charges the reducer's step budget, polls its
//! cancellation callback, and memoizes only completely checked bindings. The
//! memo belongs to this reducer, whose borrowed context cannot change.

use super::{BTreeSet, ExprId, ExprNode, Halt, Reducer, WhnfFault, WhnfRefusal};

#[derive(Clone, Copy)]
enum Frame {
    Enter(usize),
    Node { binding: usize, root: ExprId },
    Leave(usize),
}

impl Reducer<'_, '_> {
    pub(super) fn validate_free_binding_dependencies(
        &mut self,
        binding: usize,
    ) -> Result<(), Halt> {
        if self.acyclic_bindings.contains(&binding) {
            return Ok(());
        }

        let mut active = BTreeSet::new();
        let mut seen = BTreeSet::new();
        let mut pending = vec![Frame::Enter(binding)];
        while let Some(frame) = pending.pop() {
            let at = match frame {
                Frame::Enter(binding) | Frame::Leave(binding) => binding,
                Frame::Node { root, .. } => root.index(),
            };
            self.control.step(at, self.cancelled)?;
            match frame {
                Frame::Enter(binding) => {
                    if self.acyclic_bindings.contains(&binding) {
                        continue;
                    }
                    if !active.insert(binding) {
                        return Err(Halt::Refusal(WhnfRefusal::FreeBindingCycle { binding }));
                    }
                    let value =
                        self.context
                            .source
                            .free_bindings
                            .get(binding)
                            .ok_or(Halt::Fault(WhnfFault::MissingExpression {
                                input: 0,
                                index: binding,
                            }))?;
                    pending.push(Frame::Leave(binding));
                    pending.push(Frame::Node {
                        binding,
                        root: value.value.root(),
                    });
                }
                Frame::Node { binding, root } => {
                    // A flat arena may share subterms. A node is visited once
                    // per binding, not once per incoming edge or unfolding.
                    if !seen.insert((binding, root)) {
                        continue;
                    }
                    let value =
                        self.context
                            .source
                            .free_bindings
                            .get(binding)
                            .ok_or(Halt::Fault(WhnfFault::MissingExpression {
                                input: 0,
                                index: binding,
                            }))?;
                    let node = value.value.node(root).ok_or(Halt::Fault(
                        WhnfFault::MissingExpression {
                            input: 0,
                            index: root.index(),
                        },
                    ))?;
                    if let ExprNode::Free { name } = node {
                        if let Some(&dependency) = self.context.free_bindings.get(name) {
                            pending.push(Frame::Enter(dependency));
                        }
                        continue;
                    }
                    for (child, _) in super::expression_children(node).into_iter().flatten() {
                        Self::validate_child(root, child)?;
                        pending.push(Frame::Node {
                            binding,
                            root: child,
                        });
                    }
                }
                Frame::Leave(binding) => {
                    active.remove(&binding);
                    // Publish only after every dependency has completed. A
                    // failed or cancelled traversal never validates an ancestor.
                    self.acyclic_bindings.insert(binding);
                }
            }
        }
        Ok(())
    }
}
