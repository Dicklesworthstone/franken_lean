//! Independent universe normalization and equality over checker-owned wire arenas.
//!
//! The implementation follows KR-500/KR-501 but shares no semantic helper with
//! `fln-core`. It uses explicit worklists, a separate structural ordering key, and
//! its own output arena. Equality deliberately compares one-pass forms: the pinned
//! relation is incomplete, and silently taking a fixpoint would be a fidelity change.

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

use crate::wire::{LevelId, LevelNode, WireLevel, WireName};

const MAX_LEVEL_DEPTH: u32 = 16_777_215;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NormalId(u32);

impl NormalId {
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NormalNode {
    Zero,
    Succ(NormalId),
    Max(NormalId, NormalId),
    IMax(NormalId, NormalId),
    Parameter(WireName),
    Meta(WireName),
}

#[derive(Debug, Clone)]
pub struct NormalizedLevel {
    nodes: Vec<NormalNode>,
    root: NormalId,
}

impl NormalizedLevel {
    pub fn nodes(&self) -> &[NormalNode] {
        &self.nodes
    }

    pub const fn root(&self) -> NormalId {
        self.root
    }

    pub fn node(&self, id: NormalId) -> Option<&NormalNode> {
        self.nodes.get(id.index())
    }

    pub fn structurally_equals(&self, other: &NormalizedLevel) -> bool {
        normal_equal(&self.nodes, self.root, &other.nodes, other.root).unwrap_or(false)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UniverseError {
    InvalidArena,
    OffsetOverflow,
    ArenaOverflow,
}

struct Normalizer<'a> {
    input: &'a [LevelNode],
    input_facts: HashMap<LevelId, InputFacts>,
    output: Vec<NormalNode>,
    facts: Vec<NormalFacts>,
    interned: HashMap<NormalNode, NormalId>,
    normalized: HashMap<LevelId, NormalId>,
    successors: HashMap<NormalId, Vec<NormalId>>,
}

#[derive(Clone, Copy)]
struct InputFacts {
    base: LevelId,
    offset: u32,
    never_bottom: bool,
}

#[derive(Clone, Copy)]
struct NormalFacts {
    depth: u32,
    base: NormalId,
    offset: u32,
}

impl<'a> Normalizer<'a> {
    fn new(input: &'a [LevelNode]) -> Normalizer<'a> {
        Normalizer {
            input,
            input_facts: HashMap::new(),
            output: Vec::new(),
            facts: Vec::new(),
            interned: HashMap::new(),
            normalized: HashMap::new(),
            successors: HashMap::new(),
        }
    }

    fn input_node(&self, id: LevelId) -> Result<&LevelNode, UniverseError> {
        checked_level_node(self.input, id)
    }

    fn output_node(&self, id: NormalId) -> Result<&NormalNode, UniverseError> {
        self.output
            .get(id.index())
            .ok_or(UniverseError::InvalidArena)
    }

    fn push(&mut self, node: NormalNode) -> Result<NormalId, UniverseError> {
        // Canonicalize only structural nodes, never universe equivalence. This
        // preserves the pin's deliberately incomplete, one-pass relation.
        if let Some(id) = self.interned.get(&node) {
            return Ok(*id);
        }
        if self.output.len() >= u32::MAX as usize {
            return Err(UniverseError::ArenaOverflow);
        }
        let id = NormalId(self.output.len() as u32);
        let facts = match &node {
            NormalNode::Succ(child) => {
                let child = self.facts(*child)?;
                NormalFacts {
                    depth: child.depth.saturating_add(1),
                    base: child.base,
                    offset: child
                        .offset
                        .checked_add(1)
                        .ok_or(UniverseError::OffsetOverflow)?,
                }
            }
            NormalNode::Max(left, right) | NormalNode::IMax(left, right) => NormalFacts {
                depth: self
                    .facts(*left)?
                    .depth
                    .max(self.facts(*right)?.depth)
                    .saturating_add(1),
                base: id,
                offset: 0,
            },
            _ => NormalFacts {
                depth: 0,
                base: id,
                offset: 0,
            },
        };
        self.interned.insert(node.clone(), id);
        self.output.push(node);
        self.facts.push(facts);
        Ok(id)
    }

    fn shift(&mut self, id: NormalId, offset: u32) -> Result<NormalId, UniverseError> {
        let facts = self.facts(id)?;
        if facts.depth.saturating_add(offset) > MAX_LEVEL_DEPTH {
            return Err(UniverseError::OffsetOverflow);
        }
        if offset == 0 {
            return Ok(id);
        }
        let total = facts
            .offset
            .checked_add(offset)
            .ok_or(UniverseError::OffsetOverflow)? as usize;
        // Interning alone still walks 1 + ... + n successor nodes when n
        // shared prefixes are normalized separately. Extend each base's chain
        // only as far as required, and index already-built offsets directly.
        let (mut last, built) = match self.successors.get(&facts.base) {
            Some(chain) => {
                if let Some(shifted) = chain.get(total - 1) {
                    return Ok(*shifted);
                }
                (chain.last().copied().unwrap_or(facts.base), chain.len())
            }
            None => (facts.base, 0),
        };
        for _ in built..total {
            last = self.push(NormalNode::Succ(last))?;
            self.successors.entry(facts.base).or_default().push(last);
        }
        Ok(last)
    }

    fn facts(&self, id: NormalId) -> Result<NormalFacts, UniverseError> {
        self.facts
            .get(id.index())
            .copied()
            .ok_or(UniverseError::InvalidArena)
    }

    fn input_facts(&mut self, root: LevelId) -> Result<InputFacts, UniverseError> {
        if let Some(facts) = self.input_facts.get(&root) {
            return Ok(*facts);
        }
        // Facts describe the original syntax, not normalized syntax: testing
        // IMax's right side after normalization would change the pin's one-pass
        // relation. Visit only this root's reachable DAG, once per input node.
        let mut pending = vec![(root, false)];
        while let Some((id, built)) = pending.pop() {
            if self.input_facts.contains_key(&id) {
                continue;
            }
            let node = self.input_node(id)?;
            if !built {
                pending.push((id, true));
                match node {
                    LevelNode::Succ(child) => pending.push((*child, false)),
                    LevelNode::Max(left, right) | LevelNode::IMax(left, right) => {
                        pending.push((*right, false));
                        pending.push((*left, false));
                    }
                    _ => {}
                }
                continue;
            }
            let child_facts = |child: &LevelId| {
                self.input_facts
                    .get(child)
                    .copied()
                    .ok_or(UniverseError::InvalidArena)
            };
            let facts = match node {
                LevelNode::Succ(child) => {
                    let child = child_facts(child)?;
                    InputFacts {
                        base: child.base,
                        offset: child
                            .offset
                            .checked_add(1)
                            .ok_or(UniverseError::OffsetOverflow)?,
                        never_bottom: true,
                    }
                }
                _ => InputFacts {
                    base: id,
                    offset: 0,
                    never_bottom: match node {
                        LevelNode::Max(left, right) => {
                            child_facts(left)?.never_bottom || child_facts(right)?.never_bottom
                        }
                        LevelNode::IMax(_, right) => child_facts(right)?.never_bottom,
                        _ => false,
                    },
                },
            };
            self.input_facts.insert(id, facts);
        }
        self.input_facts
            .get(&root)
            .copied()
            .ok_or(UniverseError::InvalidArena)
    }

    fn peel_input(&mut self, id: LevelId) -> Result<(LevelId, u32), UniverseError> {
        let facts = self.input_facts(id)?;
        Ok((facts.base, facts.offset))
    }

    fn peel_output(&self, id: NormalId) -> Result<(NormalId, u32), UniverseError> {
        let facts = self.facts(id)?;
        Ok((facts.base, facts.offset))
    }

    fn input_never_bottom(&mut self, root: LevelId) -> Result<bool, UniverseError> {
        Ok(self.input_facts(root)?.never_bottom)
    }

    fn collect_input_max(&self, root: LevelId) -> Result<Vec<LevelId>, UniverseError> {
        let mut pending = vec![root];
        let mut leaves = Vec::new();
        let mut seen = HashSet::new();
        while let Some(id) = pending.pop() {
            // Max normalization sorts and eliminates repeated arguments. Do
            // not first expand shared max nodes into an exponential leaf list.
            if !seen.insert(id) {
                continue;
            }
            match self.input_node(id)? {
                LevelNode::Max(left, right) => {
                    pending.push(*right);
                    pending.push(*left);
                }
                _ => leaves.push(id),
            }
        }
        Ok(leaves)
    }

    fn collect_output_max(&self, roots: &[NormalId]) -> Result<Vec<NormalId>, UniverseError> {
        let mut pending: Vec<NormalId> = roots.iter().rev().copied().collect();
        let mut leaves = Vec::new();
        let mut seen = HashSet::new();
        while let Some(id) = pending.pop() {
            if !seen.insert(id) {
                continue;
            }
            match self.output_node(id)? {
                NormalNode::Max(left, right) => {
                    pending.push(*right);
                    pending.push(*left);
                }
                _ => leaves.push(id),
            }
        }
        Ok(leaves)
    }

    fn is_bottom(&self, id: NormalId) -> Result<bool, UniverseError> {
        Ok(matches!(self.output_node(id)?, NormalNode::Zero))
    }

    fn is_one(&self, id: NormalId) -> Result<bool, UniverseError> {
        let (base, offset) = self.peel_output(id)?;
        Ok(offset == 1 && self.is_bottom(base)?)
    }

    fn same_output(&self, left: NormalId, right: NormalId) -> Result<bool, UniverseError> {
        self.output_node(left)?;
        self.output_node(right)?;
        Ok(left == right)
    }

    fn order_cmp(
        &self,
        mut left: NormalId,
        mut right: NormalId,
    ) -> Result<Ordering, UniverseError> {
        // The old preorder token key expanded a shared IMax DAG as a tree.
        // Structural interning makes equal subtrees identical, so normLt can
        // descend directly to the first differing child, using constant stack.
        loop {
            let (left_base, left_offset) = self.peel_output(left)?;
            let (right_base, right_offset) = self.peel_output(right)?;
            if left_base == right_base {
                return Ok(left_offset.cmp(&right_offset));
            }
            let left_node = self.output_node(left_base)?;
            let right_node = self.output_node(right_base)?;
            match (left_node, right_node) {
                (NormalNode::Parameter(l), NormalNode::Parameter(r))
                | (NormalNode::Meta(l), NormalNode::Meta(r)) => return Ok(l.cmp(r)),
                (NormalNode::Max(ll, lr), NormalNode::Max(rl, rr))
                | (NormalNode::IMax(ll, lr), NormalNode::IMax(rl, rr)) => {
                    (left, right) = if ll == rl { (*lr, *rr) } else { (*ll, *rl) };
                }
                _ => return Ok(normal_kind(left_node).cmp(&normal_kind(right_node))),
            }
        }
    }

    fn accumulate_max(
        &mut self,
        result: NormalId,
        base: NormalId,
        offset: u32,
    ) -> Result<NormalId, UniverseError> {
        let shifted = self.shift(base, offset)?;
        if self.is_bottom(result)? {
            Ok(shifted)
        } else {
            self.push(NormalNode::Max(result, shifted))
        }
    }

    fn build_max(
        &mut self,
        roots: Vec<NormalId>,
        extra_offset: u32,
    ) -> Result<NormalId, UniverseError> {
        let mut leaves = self.collect_output_max(&roots)?;
        let mut error = None;
        leaves.sort_by(|left, right| match self.order_cmp(*left, *right) {
            Ok(order) => order,
            Err(fault) => {
                error = Some(fault);
                Ordering::Equal
            }
        });
        if let Some(error) = error {
            return Err(error);
        }
        if leaves.is_empty() {
            return Err(UniverseError::InvalidArena);
        }

        let mut first_non_explicit = leaves.len();
        for (index, id) in leaves.iter().enumerate() {
            let (base, _) = self.peel_output(*id)?;
            if !self.is_bottom(base)? {
                first_non_explicit = index;
                break;
            }
        }
        let explicit_subsumed = if first_non_explicit == 0 {
            false
        } else {
            let (_, maximum_explicit) = self.peel_output(leaves[first_non_explicit - 1])?;
            let mut subsumed = false;
            for id in &leaves[first_non_explicit..] {
                let (_, offset) = self.peel_output(*id)?;
                subsumed |= offset >= maximum_explicit;
            }
            subsumed
        };
        let start = if explicit_subsumed {
            first_non_explicit
        } else {
            first_non_explicit.saturating_sub(1)
        };
        if start >= leaves.len() {
            return Err(UniverseError::InvalidArena);
        }

        let (mut previous_base, mut previous_offset) = self.peel_output(leaves[start])?;
        let mut result = self.push(NormalNode::Zero)?;
        for id in leaves.iter().skip(start + 1) {
            let (base, offset) = self.peel_output(*id)?;
            if self.same_output(base, previous_base)? {
                previous_base = base;
                previous_offset = offset;
            } else {
                let combined = extra_offset
                    .checked_add(previous_offset)
                    .ok_or(UniverseError::OffsetOverflow)?;
                result = self.accumulate_max(result, previous_base, combined)?;
                previous_base = base;
                previous_offset = offset;
            }
        }
        let combined = extra_offset
            .checked_add(previous_offset)
            .ok_or(UniverseError::OffsetOverflow)?;
        self.accumulate_max(result, previous_base, combined)
    }

    fn build_imax(
        &mut self,
        left: NormalId,
        right: NormalId,
        offset: u32,
    ) -> Result<NormalId, UniverseError> {
        let result = if self.is_bottom(right)? || self.is_bottom(left)? || self.is_one(left)? {
            right
        } else if self.same_output(left, right)? {
            left
        } else {
            self.push(NormalNode::IMax(left, right))?
        };
        self.shift(result, offset)
    }

    fn run(mut self, root: LevelId) -> Result<NormalizedLevel, UniverseError> {
        enum Task {
            Enter(LevelId),
            Remember(LevelId),
            FinishMax {
                count: usize,
                distributed_offset: u32,
                outer_offset: u32,
            },
            FinishIMax {
                offset: u32,
            },
        }

        let mut tasks = vec![Task::Enter(root)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Enter(id) => {
                    if let Some(normal) = self.normalized.get(&id) {
                        values.push(*normal);
                        continue;
                    }
                    let (base, offset) = self.peel_input(id)?;
                    tasks.push(Task::Remember(id));
                    match self.input_node(base)?.clone() {
                        LevelNode::Zero => {
                            let zero = self.push(NormalNode::Zero)?;
                            values.push(self.shift(zero, offset)?);
                        }
                        LevelNode::Parameter(name) => {
                            let parameter = self.push(NormalNode::Parameter(name))?;
                            values.push(self.shift(parameter, offset)?);
                        }
                        LevelNode::Meta(name) => {
                            let meta = self.push(NormalNode::Meta(name))?;
                            values.push(self.shift(meta, offset)?);
                        }
                        LevelNode::Succ(_) => return Err(UniverseError::InvalidArena),
                        LevelNode::Max(_, _) => {
                            let leaves = self.collect_input_max(base)?;
                            tasks.push(Task::FinishMax {
                                count: leaves.len(),
                                distributed_offset: offset,
                                outer_offset: 0,
                            });
                            for leaf in leaves.into_iter().rev() {
                                tasks.push(Task::Enter(leaf));
                            }
                        }
                        LevelNode::IMax(left, right) if self.input_never_bottom(right)? => {
                            tasks.push(Task::FinishMax {
                                count: 2,
                                distributed_offset: 0,
                                outer_offset: offset,
                            });
                            tasks.push(Task::Enter(right));
                            tasks.push(Task::Enter(left));
                        }
                        LevelNode::IMax(left, right) => {
                            tasks.push(Task::FinishIMax { offset });
                            tasks.push(Task::Enter(right));
                            tasks.push(Task::Enter(left));
                        }
                    }
                }
                Task::Remember(id) => {
                    let normal = *values.last().ok_or(UniverseError::InvalidArena)?;
                    self.normalized.insert(id, normal);
                }
                Task::FinishMax {
                    count,
                    distributed_offset,
                    outer_offset,
                } => {
                    let start = values
                        .len()
                        .checked_sub(count)
                        .ok_or(UniverseError::InvalidArena)?;
                    let roots = values.split_off(start);
                    let normalized = self.build_max(roots, distributed_offset)?;
                    values.push(self.shift(normalized, outer_offset)?);
                }
                Task::FinishIMax { offset } => {
                    let right = values.pop().ok_or(UniverseError::InvalidArena)?;
                    let left = values.pop().ok_or(UniverseError::InvalidArena)?;
                    values.push(self.build_imax(left, right, offset)?);
                }
            }
        }
        if values.len() != 1 {
            return Err(UniverseError::InvalidArena);
        }
        Ok(NormalizedLevel {
            nodes: self.output,
            root: values[0],
        })
    }
}

fn normal_kind(node: &NormalNode) -> u8 {
    match node {
        NormalNode::Zero => 0,
        NormalNode::Parameter(_) => 1,
        NormalNode::Meta(_) => 2,
        NormalNode::Succ(_) => 3,
        NormalNode::Max(_, _) => 4,
        NormalNode::IMax(_, _) => 5,
    }
}

fn normal_equal(
    left_nodes: &[NormalNode],
    left_root: NormalId,
    right_nodes: &[NormalNode],
    right_root: NormalId,
) -> Result<bool, UniverseError> {
    let mut pending = vec![(left_root, right_root)];
    let mut seen = HashSet::new();
    while let Some((left, right)) = pending.pop() {
        if !seen.insert((left, right)) {
            continue;
        }
        let left = left_nodes
            .get(left.index())
            .ok_or(UniverseError::InvalidArena)?;
        let right = right_nodes
            .get(right.index())
            .ok_or(UniverseError::InvalidArena)?;
        match (left, right) {
            (NormalNode::Zero, NormalNode::Zero) => {}
            (NormalNode::Succ(left), NormalNode::Succ(right)) => {
                pending.push((*left, *right));
            }
            (NormalNode::Max(ll, lr), NormalNode::Max(rl, rr))
            | (NormalNode::IMax(ll, lr), NormalNode::IMax(rl, rr)) => {
                pending.push((*lr, *rr));
                pending.push((*ll, *rl));
            }
            (NormalNode::Parameter(left), NormalNode::Parameter(right))
            | (NormalNode::Meta(left), NormalNode::Meta(right))
                if left == right => {}
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn wire_equal(
    left_nodes: &[LevelNode],
    left_root: LevelId,
    right_nodes: &[LevelNode],
    right_root: LevelId,
) -> Result<bool, UniverseError> {
    let mut pending = vec![(left_root, right_root)];
    let mut seen = HashSet::new();
    while let Some((left_id, right_id)) = pending.pop() {
        if !seen.insert((left_id, right_id)) {
            continue;
        }
        let left_node = checked_level_node(left_nodes, left_id)?;
        let right_node = checked_level_node(right_nodes, right_id)?;
        match (left_node, right_node) {
            (LevelNode::Zero, LevelNode::Zero) => {}
            (LevelNode::Succ(left), LevelNode::Succ(right)) => pending.push((*left, *right)),
            (LevelNode::Max(ll, lr), LevelNode::Max(rl, rr))
            | (LevelNode::IMax(ll, lr), LevelNode::IMax(rl, rr)) => {
                pending.push((*lr, *rr));
                pending.push((*ll, *rl));
            }
            (LevelNode::Parameter(left), LevelNode::Parameter(right))
            | (LevelNode::Meta(left), LevelNode::Meta(right))
                if left == right => {}
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn checked_level_node(nodes: &[LevelNode], id: LevelId) -> Result<&LevelNode, UniverseError> {
    let node = nodes.get(id.index()).ok_or(UniverseError::InvalidArena)?;
    let backward = match node {
        LevelNode::Succ(child) => *child < id,
        LevelNode::Max(left, right) | LevelNode::IMax(left, right) => *left < id && *right < id,
        _ => true,
    };
    if !backward {
        return Err(UniverseError::InvalidArena);
    }
    Ok(node)
}

pub(crate) fn level_roots_equal(
    left_nodes: &[LevelNode],
    left_root: LevelId,
    right_nodes: &[LevelNode],
    right_root: LevelId,
) -> Result<bool, UniverseError> {
    if wire_equal(left_nodes, left_root, right_nodes, right_root)? {
        return Ok(true);
    }
    normalized_roots_equal(left_nodes, left_root, right_nodes, right_root)
}

// Do not reserve two normalizers in the structural fast path's stack frame.
// This path is also called from deep conversion on the fixed 64 KiB stack.
#[inline(never)]
fn normalized_roots_equal(
    left_nodes: &[LevelNode],
    left_root: LevelId,
    right_nodes: &[LevelNode],
    right_root: LevelId,
) -> Result<bool, UniverseError> {
    let left = Normalizer::new(left_nodes).run(left_root)?;
    let right = Normalizer::new(right_nodes).run(right_root)?;
    Ok(left.structurally_equals(&right))
}

/// Compute the checker-owned one-pass KR-500 form.
pub fn normalize(level: &WireLevel) -> Result<NormalizedLevel, UniverseError> {
    Normalizer::new(level.nodes()).run(level.root())
}

/// KR-501: structural equality first, then equality of one-pass forms.
pub fn levels_equal(left: &WireLevel, right: &WireLevel) -> Result<bool, UniverseError> {
    level_roots_equal(left.nodes(), left.root(), right.nodes(), right.root())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::defeq::{
        QuickDefEqBudget, QuickDefEqLimit, QuickDefEqOutcome, QuickDefEqStop, quick_def_eq,
        quick_def_eq_with,
    };
    use crate::wire::{ExprId, ExprNode, NamePart, WireExpr};

    fn id(index: usize) -> LevelId {
        LevelId::from_index(index).expect("small test arena")
    }

    fn parameter(name: &str) -> LevelNode {
        LevelNode::Parameter(WireName::from_parts(vec![NamePart::Text(name.to_owned())]))
    }

    // Each layer uses the preceding contingent level twice without introducing
    // a reducible `imax u u`. Tree expansion doubles although the arena grows
    // by two nodes. These are the same backward references as the checker-owned
    // arenas produced by instantiation, not primary heap nodes.
    fn contingent_dag(layers: usize) -> WireLevel {
        let mut nodes = vec![parameter("u"), parameter("v")];
        let mut root = id(0);
        for _ in 0..layers {
            let branch = id(nodes.len());
            nodes.push(LevelNode::IMax(id(1), root));
            let next = id(nodes.len());
            nodes.push(LevelNode::IMax(root, branch));
            root = next;
        }
        WireLevel::from_parts(nodes, root)
    }

    #[test]
    fn normalization_keeps_contingent_universe_sharing() {
        let level = contingent_dag(12);
        let normal = normalize(&level).expect("a well-formed contingent universe");
        assert!(
            normal.nodes().len() <= level.nodes().len() * 2,
            "{} input nodes expanded to {} output nodes",
            level.nodes().len(),
            normal.nodes().len()
        );
    }

    #[test]
    fn deep_contingent_dags_normalize_and_compare_without_tree_expansion() {
        let level = contingent_dag(256);
        let normal = normalize(&level).expect("a shared contingent universe");
        assert_eq!(normal.nodes().len(), level.nodes().len());
        let independently_normalized = normalize(&level.clone()).expect("a separate arena");
        assert!(normal.structurally_equals(&independently_normalized));
        assert_eq!(levels_equal(&level, &level.clone()), Ok(true));

        let mut changed = level.nodes().to_vec();
        changed[0] = parameter("different");
        let changed = WireLevel::from_parts(changed, level.root());
        assert_eq!(levels_equal(&level, &changed), Ok(false));
    }

    #[test]
    fn long_right_imax_chains_keep_each_contingent_suffix() {
        let mut nodes = vec![parameter("u"), parameter("v")];
        let mut root = id(1);
        for _ in 0..4096 {
            let next = id(nodes.len());
            nodes.push(LevelNode::IMax(id(0), root));
            root = next;
        }
        let level = WireLevel::from_parts(nodes, root);
        let normal = normalize(&level).expect("right-nested contingent universes");
        assert_eq!(normal.nodes().len(), level.nodes().len());
    }

    #[test]
    fn shared_successor_prefixes_are_preserved_inside_contingent_imax() {
        let mut nodes = vec![parameter("u")];
        let mut successor = id(0);
        let mut root = id(0);
        for _ in 0..4096 {
            let shifted = id(nodes.len());
            nodes.push(LevelNode::Succ(successor));
            successor = shifted;
            let next = id(nodes.len());
            nodes.push(LevelNode::IMax(successor, root));
            root = next;
        }
        let level = WireLevel::from_parts(nodes, root);
        let normal = normalize(&level).expect("shared successor prefixes");
        assert_eq!(normal.nodes().len(), level.nodes().len());
    }

    #[test]
    fn cached_successor_chains_support_arbitrary_offsets_and_preserve_limits() {
        let mut normalizer = Normalizer::new(&[]);
        let base = normalizer
            .push(NormalNode::Parameter(WireName::from_parts(vec![
                NamePart::Text("u".to_owned()),
            ])))
            .unwrap();
        let longest = normalizer.shift(base, 4096).unwrap();
        for offset in (0..4096).rev() {
            let shifted = normalizer.shift(base, offset).unwrap();
            assert_eq!(normalizer.peel_output(shifted).unwrap(), (base, offset));
            assert_eq!(normalizer.shift(shifted, 4096 - offset), Ok(longest));
        }
        assert_eq!(normalizer.output.len(), 4097);
        assert_eq!(normalizer.successors[&base].len(), 4096);
        assert_eq!(
            normalizer.shift(longest, u32::MAX),
            Err(UniverseError::OffsetOverflow)
        );
        assert_eq!(normalizer.output.len(), 4097);
        assert_eq!(normalizer.shift(base, 4096), Ok(longest));
    }

    #[test]
    fn cached_input_facts_are_root_local_and_keep_imax_right_sided() {
        let nodes = vec![
            parameter("u"),
            LevelNode::Succ(id(0)),
            LevelNode::IMax(id(1), id(0)),
            LevelNode::IMax(id(0), id(1)),
            LevelNode::Max(id(0), id(1)),
            // An unrelated malformed suffix is never borrowed by a valid root.
            LevelNode::Succ(id(5)),
        ];
        let mut normalizer = Normalizer::new(&nodes);
        assert!(!normalizer.input_never_bottom(id(2)).unwrap());
        assert_eq!(normalizer.input_facts.len(), 3);
        assert!(normalizer.input_never_bottom(id(3)).unwrap());
        assert!(normalizer.input_never_bottom(id(4)).unwrap());
        assert_eq!(normalizer.peel_input(id(1)).unwrap(), (id(0), 1));
        assert_eq!(normalizer.input_facts.len(), 5);
        assert_eq!(
            normalizer.input_never_bottom(id(5)),
            Err(UniverseError::InvalidArena)
        );
        assert!(!normalizer.input_never_bottom(id(2)).unwrap());
    }

    fn sort(level: &WireLevel) -> WireExpr {
        WireExpr::from_parts(
            vec![ExprNode::Sort {
                level: level.root(),
            }],
            level.nodes().to_vec(),
            ExprId::from_index(0).unwrap(),
        )
    }

    #[test]
    fn sort_conversion_normalizes_shared_universes_and_detects_unequal_leaves() {
        let level = contingent_dag(512);
        let left = sort(&level);
        // Different raw shapes force the actual conversion path to normalize,
        // rather than return early from structural wire equality.
        let mut nodes = level.nodes().to_vec();
        let root = id(nodes.len());
        nodes.push(LevelNode::Max(level.root(), level.root()));
        let right = sort(&WireLevel::from_parts(nodes.clone(), root));
        let budget = QuickDefEqBudget::new(1, (left.levels().len() + right.levels().len()) as u64);
        assert!(matches!(
            quick_def_eq(&left, &right, budget),
            QuickDefEqOutcome::Equal(_)
        ));
        assert!(matches!(
            quick_def_eq(&right, &left, budget),
            QuickDefEqOutcome::Equal(_)
        ));

        nodes[0] = parameter("different");
        let changed = sort(&WireLevel::from_parts(nodes, root));
        assert!(matches!(
            quick_def_eq(&left, &changed, budget),
            QuickDefEqOutcome::NotEqual { .. }
        ));
        assert!(matches!(
            quick_def_eq(&changed, &left, budget),
            QuickDefEqOutcome::NotEqual { .. }
        ));
    }

    #[test]
    fn shared_sort_conversion_keeps_cancellation_and_arena_limits_as_nonanswers() {
        let level = contingent_dag(512);
        let left = sort(&level);
        let right = sort(&level);
        let observed = (left.levels().len() + right.levels().len()) as u64;
        assert!(matches!(
            quick_def_eq(&left, &right, QuickDefEqBudget::new(1, observed - 1)),
            QuickDefEqOutcome::Inconclusive(QuickDefEqStop::Resource {
                limit: QuickDefEqLimit::LevelArenaNodes,
                completed_comparisons: 0,
                ..
            })
        ));
        let budget = QuickDefEqBudget::new(1, observed);
        assert!(matches!(
            quick_def_eq_with(&left, &right, budget, || true),
            QuickDefEqOutcome::Inconclusive(QuickDefEqStop::Cancelled { .. })
        ));
        assert!(matches!(
            quick_def_eq(&left, &right, budget),
            QuickDefEqOutcome::Equal(_)
        ));
    }

    #[test]
    fn shared_max_flattening_and_never_bottom_preserve_imax_condition() {
        let mut nodes = vec![parameter("u"), parameter("v")];
        let mut root = id(1);
        for _ in 0..128 {
            let next = id(nodes.len());
            nodes.push(LevelNode::Max(root, root));
            root = next;
        }
        let imax = id(nodes.len());
        nodes.push(LevelNode::IMax(id(0), root));
        let level = WireLevel::from_parts(nodes, imax);
        let expected = WireLevel::from_parts(
            vec![
                parameter("u"),
                parameter("v"),
                LevelNode::IMax(id(0), id(1)),
            ],
            id(2),
        );
        let normal = normalize(&level).expect("shared max under contingent imax");
        assert!(normal.nodes().len() <= 4);
        assert_eq!(levels_equal(&level, &expected), Ok(true));
        let unconditional = WireLevel::from_parts(
            vec![parameter("u"), parameter("v"), LevelNode::Max(id(0), id(1))],
            id(2),
        );
        assert_eq!(levels_equal(&level, &unconditional), Ok(false));
    }

    #[test]
    fn max_ordering_does_not_serialize_contingent_dags() {
        let level = contingent_dag(128);
        let mut nodes = level.nodes().to_vec();
        let shifted = id(nodes.len());
        nodes.push(LevelNode::Succ(level.root()));
        let root = id(nodes.len());
        nodes.push(LevelNode::Max(level.root(), shifted));
        let combined = WireLevel::from_parts(nodes.clone(), root);
        let expected = WireLevel::from_parts(nodes, shifted);
        assert_eq!(levels_equal(&combined, &expected), Ok(true));
        assert!(
            normalize(&combined)
                .expect("max of shared terms")
                .nodes()
                .len()
                <= level.nodes().len() + 2
        );
    }

    #[test]
    fn equality_memoizes_pairs_not_individual_nodes() {
        let left = [parameter("u"), LevelNode::Max(id(0), id(0))];
        let right = [parameter("u"), parameter("v"), LevelNode::Max(id(0), id(1))];
        assert_eq!(wire_equal(&left, id(1), &right, id(2)), Ok(false));
        assert_eq!(wire_equal(&right, id(2), &left, id(1)), Ok(false));
        let left = normalize(&WireLevel::from_parts(left.to_vec(), id(1))).unwrap();
        let right = normalize(&WireLevel::from_parts(right.to_vec(), id(2))).unwrap();
        assert!(!left.structurally_equals(&right));
    }

    #[test]
    fn memoization_does_not_accept_broken_private_arenas() {
        for nodes in [
            vec![LevelNode::Succ(id(0))],
            vec![LevelNode::Max(id(0), id(0))],
            vec![LevelNode::IMax(id(1), id(0)), LevelNode::Zero],
        ] {
            let level = WireLevel::from_parts(nodes, id(0));
            assert_eq!(normalize(&level).unwrap_err(), UniverseError::InvalidArena);
            assert_eq!(
                levels_equal(&level, &level),
                Err(UniverseError::InvalidArena)
            );
        }
        let missing = WireLevel::from_parts(vec![LevelNode::Zero], id(1));
        assert_eq!(
            normalize(&missing).unwrap_err(),
            UniverseError::InvalidArena
        );
        assert_eq!(
            levels_equal(&missing, &missing),
            Err(UniverseError::InvalidArena)
        );
    }
}
