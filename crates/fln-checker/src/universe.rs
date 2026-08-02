//! Independent universe normalization and equality over checker-owned wire arenas.
//!
//! The implementation follows KR-500/KR-501 but shares no semantic helper with
//! `fln-core`. It uses explicit worklists, a separate structural ordering key, and
//! its own output arena. Equality deliberately compares one-pass forms: the pinned
//! relation is incomplete, and silently taking a fixpoint would be a fidelity change.

use crate::wire::{LevelId, LevelNode, WireLevel, WireName};

const MAX_LEVEL_DEPTH: u32 = 16_777_215;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NormalId(u32);

impl NormalId {
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
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
    output: Vec<NormalNode>,
}

impl<'a> Normalizer<'a> {
    fn new(input: &'a [LevelNode]) -> Normalizer<'a> {
        Normalizer {
            input,
            output: Vec::new(),
        }
    }

    fn input_node(&self, id: LevelId) -> Result<&LevelNode, UniverseError> {
        self.input
            .get(id.index())
            .ok_or(UniverseError::InvalidArena)
    }

    fn output_node(&self, id: NormalId) -> Result<&NormalNode, UniverseError> {
        self.output
            .get(id.index())
            .ok_or(UniverseError::InvalidArena)
    }

    fn push(&mut self, node: NormalNode) -> Result<NormalId, UniverseError> {
        if self.output.len() >= u32::MAX as usize {
            return Err(UniverseError::ArenaOverflow);
        }
        let id = NormalId(self.output.len() as u32);
        self.output.push(node);
        Ok(id)
    }

    fn shift(&mut self, mut id: NormalId, offset: u32) -> Result<NormalId, UniverseError> {
        if self.depth(id)?.saturating_add(offset) > MAX_LEVEL_DEPTH {
            return Err(UniverseError::OffsetOverflow);
        }
        for _ in 0..offset {
            id = self.push(NormalNode::Succ(id))?;
        }
        Ok(id)
    }

    fn depth(&self, root: NormalId) -> Result<u32, UniverseError> {
        let mut tasks = vec![(root, false)];
        let mut depths: Vec<u32> = Vec::new();
        while let Some((id, built)) = tasks.pop() {
            if built {
                let depth = match self.output_node(id)? {
                    NormalNode::Zero | NormalNode::Parameter(_) | NormalNode::Meta(_) => 0,
                    NormalNode::Succ(_) => depths
                        .pop()
                        .ok_or(UniverseError::InvalidArena)?
                        .saturating_add(1),
                    NormalNode::Max(_, _) | NormalNode::IMax(_, _) => {
                        let right: u32 = depths.pop().ok_or(UniverseError::InvalidArena)?;
                        let left: u32 = depths.pop().ok_or(UniverseError::InvalidArena)?;
                        left.max(right).saturating_add(1)
                    }
                };
                depths.push(depth);
                continue;
            }
            tasks.push((id, true));
            match self.output_node(id)? {
                NormalNode::Succ(child) => tasks.push((*child, false)),
                NormalNode::Max(left, right) | NormalNode::IMax(left, right) => {
                    tasks.push((*right, false));
                    tasks.push((*left, false));
                }
                NormalNode::Zero | NormalNode::Parameter(_) | NormalNode::Meta(_) => {}
            }
        }
        if depths.len() == 1 {
            Ok(depths[0])
        } else {
            Err(UniverseError::InvalidArena)
        }
    }

    fn peel_input(&self, mut id: LevelId) -> Result<(LevelId, u32), UniverseError> {
        let mut offset = 0_u32;
        let mut remaining = self.input.len().saturating_add(1);
        loop {
            if remaining == 0 {
                return Err(UniverseError::InvalidArena);
            }
            remaining -= 1;
            match self.input_node(id)? {
                LevelNode::Succ(child) => {
                    offset = offset.checked_add(1).ok_or(UniverseError::OffsetOverflow)?;
                    id = *child;
                }
                _ => return Ok((id, offset)),
            }
        }
    }

    fn peel_output(&self, mut id: NormalId) -> Result<(NormalId, u32), UniverseError> {
        let mut offset = 0_u32;
        let mut remaining = self.output.len().saturating_add(1);
        loop {
            if remaining == 0 {
                return Err(UniverseError::InvalidArena);
            }
            remaining -= 1;
            match self.output_node(id)? {
                NormalNode::Succ(child) => {
                    offset = offset.checked_add(1).ok_or(UniverseError::OffsetOverflow)?;
                    id = *child;
                }
                _ => return Ok((id, offset)),
            }
        }
    }

    fn input_never_bottom(&self, root: LevelId) -> Result<bool, UniverseError> {
        enum Task {
            Visit(LevelId),
            Or,
        }
        let mut tasks = vec![Task::Visit(root)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(id) => match self.input_node(id)? {
                    LevelNode::Zero | LevelNode::Parameter(_) | LevelNode::Meta(_) => {
                        values.push(false);
                    }
                    LevelNode::Succ(_) => values.push(true),
                    LevelNode::Max(left, right) => {
                        tasks.push(Task::Or);
                        tasks.push(Task::Visit(*right));
                        tasks.push(Task::Visit(*left));
                    }
                    LevelNode::IMax(_, right) => tasks.push(Task::Visit(*right)),
                },
                Task::Or => {
                    let right = values.pop().ok_or(UniverseError::InvalidArena)?;
                    let left = values.pop().ok_or(UniverseError::InvalidArena)?;
                    values.push(left || right);
                }
            }
        }
        if values.len() == 1 {
            Ok(values[0])
        } else {
            Err(UniverseError::InvalidArena)
        }
    }

    fn collect_input_max(&self, root: LevelId) -> Result<Vec<LevelId>, UniverseError> {
        let mut pending = vec![root];
        let mut leaves = Vec::new();
        while let Some(id) = pending.pop() {
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
        while let Some(id) = pending.pop() {
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
        normal_equal(&self.output, left, &self.output, right)
    }

    fn order_key(&self, root: NormalId) -> Result<Vec<OrderToken>, UniverseError> {
        enum Task {
            Visit(NormalId),
            Offset(u32),
        }
        let mut tasks = vec![Task::Visit(root)];
        let mut key = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Offset(offset) => key.push(OrderToken::Offset(offset)),
                Task::Visit(id) => {
                    let (base, offset) = self.peel_output(id)?;
                    match self.output_node(base)? {
                        NormalNode::Zero => {
                            key.push(OrderToken::Constructor(0));
                            key.push(OrderToken::Offset(offset));
                        }
                        NormalNode::Parameter(name) => {
                            key.push(OrderToken::Constructor(1));
                            key.push(OrderToken::Name(name.clone()));
                            key.push(OrderToken::Offset(offset));
                        }
                        NormalNode::Meta(name) => {
                            key.push(OrderToken::Constructor(2));
                            key.push(OrderToken::Name(name.clone()));
                            key.push(OrderToken::Offset(offset));
                        }
                        NormalNode::Succ(_) => return Err(UniverseError::InvalidArena),
                        NormalNode::Max(left, right) => {
                            key.push(OrderToken::Constructor(4));
                            tasks.push(Task::Offset(offset));
                            tasks.push(Task::Visit(*right));
                            tasks.push(Task::Visit(*left));
                        }
                        NormalNode::IMax(left, right) => {
                            key.push(OrderToken::Constructor(5));
                            tasks.push(Task::Offset(offset));
                            tasks.push(Task::Visit(*right));
                            tasks.push(Task::Visit(*left));
                        }
                    }
                }
            }
        }
        Ok(key)
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
        let leaves = self.collect_output_max(&roots)?;
        let mut keyed = Vec::with_capacity(leaves.len());
        for id in leaves {
            keyed.push((self.order_key(id)?, id));
        }
        keyed.sort_by(|left, right| left.0.cmp(&right.0));
        let leaves: Vec<NormalId> = keyed.into_iter().map(|(_, id)| id).collect();
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
            Enter(LevelId, u32),
            FinishMax {
                count: usize,
                distributed_offset: u32,
                outer_offset: u32,
            },
            FinishIMax {
                offset: u32,
            },
        }

        let mut tasks = vec![Task::Enter(root, 0)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Enter(id, inherited_offset) => {
                    let (base, own_offset) = self.peel_input(id)?;
                    let offset = inherited_offset
                        .checked_add(own_offset)
                        .ok_or(UniverseError::OffsetOverflow)?;
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
                                tasks.push(Task::Enter(leaf, 0));
                            }
                        }
                        LevelNode::IMax(left, right) if self.input_never_bottom(right)? => {
                            tasks.push(Task::FinishMax {
                                count: 2,
                                distributed_offset: 0,
                                outer_offset: offset,
                            });
                            tasks.push(Task::Enter(right, 0));
                            tasks.push(Task::Enter(left, 0));
                        }
                        LevelNode::IMax(left, right) => {
                            tasks.push(Task::FinishIMax { offset });
                            tasks.push(Task::Enter(right, 0));
                            tasks.push(Task::Enter(left, 0));
                        }
                    }
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum OrderToken {
    Constructor(u8),
    Name(WireName),
    Offset(u32),
}

fn normal_equal(
    left_nodes: &[NormalNode],
    left_root: NormalId,
    right_nodes: &[NormalNode],
    right_root: NormalId,
) -> Result<bool, UniverseError> {
    let mut pending = vec![(left_root, right_root)];
    while let Some((left, right)) = pending.pop() {
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

fn wire_equal(left: &WireLevel, right: &WireLevel) -> Result<bool, UniverseError> {
    let mut pending = vec![(left.root(), right.root())];
    while let Some((left_id, right_id)) = pending.pop() {
        let left_node = left.node(left_id).ok_or(UniverseError::InvalidArena)?;
        let right_node = right.node(right_id).ok_or(UniverseError::InvalidArena)?;
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

/// Compute the checker-owned one-pass KR-500 form.
pub fn normalize(level: &WireLevel) -> Result<NormalizedLevel, UniverseError> {
    Normalizer::new(level.nodes()).run(level.root())
}

/// KR-501: structural equality first, then equality of one-pass forms.
pub fn levels_equal(left: &WireLevel, right: &WireLevel) -> Result<bool, UniverseError> {
    if wire_equal(left, right)? {
        return Ok(true);
    }
    let left = normalize(left)?;
    let right = normalize(right)?;
    Ok(left.structurally_equals(&right))
}
