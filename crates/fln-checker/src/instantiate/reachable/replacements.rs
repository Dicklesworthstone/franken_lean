//! A replacement cache belongs to one instantiation and its one source arena.
//! Equal indexes in separate WireLevels must never alias. In the shared-arena
//! route, however, parameter roots and their descendants really are shared and
//! should be copied only once, including when a later root contains an earlier
//! one. Replacements stay literal: neither substitution nor normalization runs
//! inside them.

use super::*;

#[derive(Default)]
pub(super) struct ReplacementCopies {
    shared: BTreeMap<usize, LevelId>,
}

impl ReplacementCopies {
    pub(super) fn root(
        &mut self,
        instantiator: &mut Instantiator<'_, '_>,
        value_index: usize,
    ) -> Result<LevelId, Halt> {
        // Even a cache hit is cancellable; repeated roots must not hide a long
        // rebuild pass from the caller's cancellation checkpoint.
        instantiator.control.poll(value_index)?;
        let ReplacementValues::ArenaRoots { nodes, roots } = instantiator.values else {
            return instantiator.copy_replacement(value_index);
        };
        let root = roots.get(value_index).copied().ok_or(Halt::Fault(
            InstantiationFault::MissingReplacement { index: value_index },
        ))?;
        let input = InstantiationInput::Replacement { index: value_index };
        let missing = |index| Halt::Fault(InstantiationFault::MissingLevel { input, index });
        let mut work = vec![(root.index(), false)];
        while let Some((index, built)) = work.pop() {
            if self.shared.contains_key(&index) {
                continue;
            }
            let node = nodes.get(index).ok_or_else(|| missing(index))?;
            if !built {
                instantiator.control.step(index)?;
                work.push((index, true));
                for child in level_children(node).into_iter().flatten() {
                    if child.index() >= index {
                        return Err(Halt::Fault(InstantiationFault::NonBackwardLevelReference {
                            input,
                            parent: index,
                            child: child.index(),
                        }));
                    }
                    work.push((child.index(), false));
                }
                continue;
            }
            // Price owned payloads before copying, not after allocating them.
            instantiator
                .control
                .output(level_owned_units(node), index)?;
            let mapped = |child: &LevelId| {
                self.shared
                    .get(&child.index())
                    .copied()
                    .ok_or_else(|| missing(child.index()))
            };
            let copied = match node {
                LevelNode::Zero => LevelNode::Zero,
                LevelNode::Succ(child) => LevelNode::Succ(mapped(child)?),
                LevelNode::Max(left, right) => LevelNode::Max(mapped(left)?, mapped(right)?),
                LevelNode::IMax(left, right) => LevelNode::IMax(mapped(left)?, mapped(right)?),
                LevelNode::Parameter(name) => LevelNode::Parameter(name.clone()),
                LevelNode::Meta(name) => LevelNode::Meta(name.clone()),
            };
            let id = instantiator.push_level(copied, index)?;
            self.shared.insert(index, id);
        }
        self.shared
            .get(&root.index())
            .copied()
            .ok_or_else(|| missing(root.index()))
    }
}

#[cfg(test)]
mod tests;
