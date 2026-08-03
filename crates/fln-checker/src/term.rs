//! Independent term facts and capture-avoiding rewrites over checker-owned arenas.
//!
//! This module deliberately derives scope and traversal facts from the wire nodes
//! themselves. It never consumes the primary expression data word. Rewrites are
//! occurrence walks rather than node-id memoized walks: a future wire schema may
//! share one node beneath different binder depths, and scope is a property of the
//! occurrence, not merely of the arena slot.

use std::collections::BTreeMap;

use crate::wire::{
    ExprId, ExprNode, LevelId, LevelNode, MAX_BVAR_INDEX, MetadataValue, WireExpr, WireName,
    expression_owned_units, level_owned_units, usize_units,
};

/// Exact root facts used by checker traversal and pruning.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct TermFacts {
    /// One more than the largest bound index that remains external at this root.
    pub external_bound_span: u32,
    pub contains_free: bool,
    pub contains_expression_meta: bool,
    pub contains_universe_meta: bool,
    pub contains_universe_parameter: bool,
    /// Constructor depth saturated at 255, matching the shared schema covenant.
    pub approximate_depth: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TermLimit {
    Steps,
    OutputUnits,
    ArenaNodes,
    BoundIndex,
}

/// Work bounds for one facts walk or rewrite.
///
/// Output units count expression and universe nodes, name parts, metadata
/// entries, level references, natural limbs, and owned UTF-8 bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TermBudget {
    pub max_steps: u64,
    pub max_output_units: u64,
    pub max_arena_nodes: u64,
}

impl TermBudget {
    pub const fn new(max_steps: u64, max_output_units: u64) -> TermBudget {
        TermBudget {
            max_steps,
            max_output_units,
            max_arena_nodes: u32::MAX as u64,
        }
    }

    pub const fn with_max_arena_nodes(mut self, max_arena_nodes: u64) -> TermBudget {
        self.max_arena_nodes = max_arena_nodes;
        self
    }

    pub const fn unlimited() -> TermBudget {
        TermBudget::new(u64::MAX, u64::MAX)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TermStop {
    Resource {
        limit: TermLimit,
        allowed: u64,
        observed: u64,
        at: usize,
        completed_steps: u64,
    },
    Cancelled {
        at: usize,
        polls: u64,
        completed_steps: u64,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TermInput {
    Subject,
    Replacement,
}

/// A broken private arena invariant is an internal fault, never a user rejection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TermFault {
    MissingExpression {
        input: TermInput,
        index: usize,
    },
    NonBackwardExpressionReference {
        input: TermInput,
        parent: usize,
        child: usize,
    },
    MissingLevel {
        input: TermInput,
        index: usize,
    },
    NonBackwardLevelReference {
        input: TermInput,
        parent: usize,
        child: usize,
    },
    ValueStack {
        entries: usize,
    },
}

/// Completed value, typed non-answer, or typed implementation fault.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TermOutcome<T> {
    Complete(T),
    Inconclusive(TermStop),
    InternalFault(TermFault),
}

enum Halt {
    Stop(TermStop),
    Fault(TermFault),
}

fn outcome<T>(result: Result<T, Halt>) -> TermOutcome<T> {
    match result {
        Ok(value) => TermOutcome::Complete(value),
        Err(Halt::Stop(stop)) => TermOutcome::Inconclusive(stop),
        Err(Halt::Fault(fault)) => TermOutcome::InternalFault(fault),
    }
}

struct Control<'a> {
    budget: TermBudget,
    steps: u64,
    output_units: u64,
    polls: u64,
    cancelled: &'a mut dyn FnMut() -> bool,
}

impl<'a> Control<'a> {
    fn new(budget: TermBudget, cancelled: &'a mut dyn FnMut() -> bool) -> Control<'a> {
        Control {
            budget,
            steps: 0,
            output_units: 0,
            polls: 0,
            cancelled,
        }
    }

    fn poll(&mut self, at: usize) -> Result<(), Halt> {
        self.polls = self.polls.saturating_add(1);
        if (self.cancelled)() {
            return Err(Halt::Stop(TermStop::Cancelled {
                at,
                polls: self.polls,
                completed_steps: self.steps,
            }));
        }
        Ok(())
    }

    fn step(&mut self, at: usize) -> Result<(), Halt> {
        self.poll(at)?;
        let observed = self.steps.saturating_add(1);
        if observed > self.budget.max_steps {
            return Err(Halt::Stop(TermStop::Resource {
                limit: TermLimit::Steps,
                allowed: self.budget.max_steps,
                observed,
                at,
                completed_steps: self.steps,
            }));
        }
        self.steps = observed;
        Ok(())
    }

    fn output(&mut self, units: u64, at: usize) -> Result<(), Halt> {
        self.poll(at)?;
        let observed = self.output_units.saturating_add(units);
        if observed > self.budget.max_output_units {
            return Err(Halt::Stop(TermStop::Resource {
                limit: TermLimit::OutputUnits,
                allowed: self.budget.max_output_units,
                observed,
                at,
                completed_steps: self.steps,
            }));
        }
        self.output_units = observed;
        Ok(())
    }

    fn bound_index(&self, observed: u64, at: usize) -> Halt {
        Halt::Stop(TermStop::Resource {
            limit: TermLimit::BoundIndex,
            allowed: u64::from(MAX_BVAR_INDEX),
            observed,
            at,
            completed_steps: self.steps,
        })
    }

    fn arena_nodes(&self, observed: u64, at: usize) -> Halt {
        Halt::Stop(TermStop::Resource {
            limit: TermLimit::ArenaNodes,
            allowed: self.budget.max_arena_nodes.min(u64::from(u32::MAX)),
            observed,
            at,
            completed_steps: self.steps,
        })
    }

    fn admit_arena_node(&self, observed: u64, at: usize) -> Result<(), Halt> {
        if observed > self.budget.max_arena_nodes.min(u64::from(u32::MAX)) {
            return Err(self.arena_nodes(observed, at));
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct UniverseMarks {
    meta: bool,
    parameter: bool,
}

impl UniverseMarks {
    fn union(self, other: UniverseMarks) -> UniverseMarks {
        UniverseMarks {
            meta: self.meta || other.meta,
            parameter: self.parameter || other.parameter,
        }
    }
}

impl TermFacts {
    fn union(self, other: TermFacts) -> TermFacts {
        TermFacts {
            external_bound_span: self.external_bound_span.max(other.external_bound_span),
            contains_free: self.contains_free || other.contains_free,
            contains_expression_meta: self.contains_expression_meta
                || other.contains_expression_meta,
            contains_universe_meta: self.contains_universe_meta || other.contains_universe_meta,
            contains_universe_parameter: self.contains_universe_parameter
                || other.contains_universe_parameter,
            approximate_depth: self.approximate_depth.max(other.approximate_depth),
        }
    }

    fn beneath_binder(self) -> TermFacts {
        TermFacts {
            external_bound_span: self.external_bound_span.saturating_sub(1),
            ..self
        }
    }

    fn parent(self) -> TermFacts {
        TermFacts {
            approximate_depth: self.approximate_depth.saturating_add(1),
            ..self
        }
    }

    fn with_universes(mut self, marks: UniverseMarks) -> TermFacts {
        self.contains_universe_meta |= marks.meta;
        self.contains_universe_parameter |= marks.parameter;
        self
    }
}

fn prior_level(marks: &[UniverseMarks], id: LevelId, parent: usize) -> Result<UniverseMarks, Halt> {
    if id.index() >= parent {
        return Err(Halt::Fault(TermFault::NonBackwardLevelReference {
            input: TermInput::Subject,
            parent,
            child: id.index(),
        }));
    }
    marks
        .get(id.index())
        .copied()
        .ok_or(Halt::Fault(TermFault::MissingLevel {
            input: TermInput::Subject,
            index: id.index(),
        }))
}

fn prior_expr(facts: &[TermFacts], id: ExprId, parent: usize) -> Result<TermFacts, Halt> {
    if id.index() >= parent {
        return Err(Halt::Fault(TermFault::NonBackwardExpressionReference {
            input: TermInput::Subject,
            parent,
            child: id.index(),
        }));
    }
    facts
        .get(id.index())
        .copied()
        .ok_or(Halt::Fault(TermFault::MissingExpression {
            input: TermInput::Subject,
            index: id.index(),
        }))
}

fn inspect_inner(term: &WireExpr, control: &mut Control<'_>) -> Result<TermFacts, Halt> {
    let mut universe_marks = Vec::new();
    for (index, node) in term.levels().iter().enumerate() {
        control.step(index)?;
        let marks = match node {
            LevelNode::Zero => UniverseMarks::default(),
            LevelNode::Succ(child) => prior_level(&universe_marks, *child, index)?,
            LevelNode::Max(left, right) | LevelNode::IMax(left, right) => prior_level(
                &universe_marks,
                *left,
                index,
            )?
            .union(prior_level(&universe_marks, *right, index)?),
            LevelNode::Parameter(_) => UniverseMarks {
                parameter: true,
                ..UniverseMarks::default()
            },
            LevelNode::Meta(_) => UniverseMarks {
                meta: true,
                ..UniverseMarks::default()
            },
        };
        universe_marks.push(marks);
    }

    let mut facts = Vec::new();
    for (index, node) in term.nodes().iter().enumerate() {
        control.step(index)?;
        let value = match node {
            ExprNode::Bound { index } => TermFacts {
                external_bound_span: index.saturating_add(1),
                ..TermFacts::default()
            },
            ExprNode::Free { .. } => TermFacts {
                contains_free: true,
                ..TermFacts::default()
            },
            ExprNode::Meta { .. } => TermFacts {
                contains_expression_meta: true,
                ..TermFacts::default()
            },
            ExprNode::Sort { level } => TermFacts::default().with_universes(
                universe_marks
                    .get(level.index())
                    .copied()
                    .ok_or(Halt::Fault(TermFault::MissingLevel {
                        input: TermInput::Subject,
                        index: level.index(),
                    }))?,
            ),
            ExprNode::Constant { levels, .. } => {
                let mut marks = UniverseMarks::default();
                for level in levels {
                    marks = marks.union(universe_marks.get(level.index()).copied().ok_or(
                        Halt::Fault(TermFault::MissingLevel {
                            input: TermInput::Subject,
                            index: level.index(),
                        }),
                    )?);
                }
                TermFacts::default().with_universes(marks)
            }
            ExprNode::Apply { function, argument } => prior_expr(&facts, *function, index)?
                .union(prior_expr(&facts, *argument, index)?)
                .parent(),
            ExprNode::Lambda {
                binder_type, body, ..
            }
            | ExprNode::Forall {
                binder_type, body, ..
            } => prior_expr(&facts, *binder_type, index)?
                .union(prior_expr(&facts, *body, index)?.beneath_binder())
                .parent(),
            ExprNode::Let {
                type_, value, body, ..
            } => prior_expr(&facts, *type_, index)?
                .union(prior_expr(&facts, *value, index)?)
                .union(prior_expr(&facts, *body, index)?.beneath_binder())
                .parent(),
            ExprNode::NatLiteral { .. } | ExprNode::StringLiteral(_) => TermFacts::default(),
            ExprNode::Metadata { expression, .. } | ExprNode::Projection { expression, .. } => {
                prior_expr(&facts, *expression, index)?.parent()
            }
        };
        facts.push(value);
    }

    facts
        .get(term.root().index())
        .copied()
        .ok_or(Halt::Fault(TermFault::MissingExpression {
            input: TermInput::Subject,
            index: term.root().index(),
        }))
}

pub fn inspect(term: &WireExpr, budget: TermBudget) -> TermOutcome<TermFacts> {
    inspect_with(term, budget, || false)
}

pub fn inspect_with(
    term: &WireExpr,
    budget: TermBudget,
    mut cancelled: impl FnMut() -> bool,
) -> TermOutcome<TermFacts> {
    let mut control = Control::new(budget, &mut cancelled);
    outcome(inspect_inner(term, &mut control))
}

#[derive(Debug, Clone, Copy)]
enum Mode {
    Rewrite { scope: u64 },
    Raise { amount: u64, cutoff: u64 },
}

#[derive(Debug, Clone, Copy)]
enum Operation<'a> {
    Raise,
    Bound {
        target: u32,
    },
    Close {
        name: &'a WireName,
    },
    CloseMany {
        ordinals: &'a BTreeMap<WireName, u32>,
        binder_count: u32,
    },
    Free {
        name: &'a WireName,
    },
}

#[derive(Debug, Clone, Copy)]
struct TransformPlan<'a> {
    replacement: Option<(&'a WireExpr, ExprId)>,
    operation: Operation<'a>,
    root_mode: Mode,
    compact_levels: bool,
}

#[derive(Debug, Clone, Copy)]
enum FreeAction {
    Retain,
    Close { index: u64 },
    Replace { scope: u64 },
}

#[derive(Debug, Clone)]
enum Frame {
    Apply,
    Lambda {
        binder_name: WireName,
        style: crate::wire::BinderStyle,
    },
    Forall {
        binder_name: WireName,
        style: crate::wire::BinderStyle,
    },
    Let {
        declaration_name: WireName,
        non_dependent: bool,
    },
    Metadata {
        entries: Vec<(WireName, MetadataValue)>,
    },
    Projection {
        structure_name: WireName,
        index: u64,
    },
}

#[derive(Debug, Clone)]
enum Task {
    Visit {
        input: TermInput,
        id: ExprId,
        mode: Mode,
    },
    Build(Frame),
}

struct Transformer<'a, 'c> {
    subject: &'a WireExpr,
    subject_root: ExprId,
    replacement: Option<(&'a WireExpr, ExprId)>,
    operation: Operation<'a>,
    control: Control<'c>,
    nodes: Vec<ExprNode>,
    levels: Vec<LevelNode>,
    level_maps: [Option<Vec<LevelId>>; 2],
    compact_level_maps: [BTreeMap<usize, LevelId>; 2],
    compact_levels: bool,
    values: Vec<ExprId>,
    tasks: Vec<Task>,
}

impl<'a, 'c> Transformer<'a, 'c> {
    fn input(&self, input: TermInput) -> Result<&'a WireExpr, Halt> {
        match input {
            TermInput::Subject => Ok(self.subject),
            TermInput::Replacement => self.replacement.map(|(term, _)| term).ok_or(Halt::Fault(
                TermFault::MissingExpression { input, index: 0 },
            )),
        }
    }

    fn root(&self, input: TermInput) -> Result<ExprId, Halt> {
        match input {
            TermInput::Subject => Ok(self.subject_root),
            TermInput::Replacement => self.replacement.map(|(_, root)| root).ok_or(Halt::Fault(
                TermFault::MissingExpression { input, index: 0 },
            )),
        }
    }

    fn map_index(input: TermInput) -> usize {
        match input {
            TermInput::Subject => 0,
            TermInput::Replacement => 1,
        }
    }

    fn expression(&self, input: TermInput, id: ExprId) -> Result<&ExprNode, Halt> {
        self.input(input)?
            .node(id)
            .ok_or(Halt::Fault(TermFault::MissingExpression {
                input,
                index: id.index(),
            }))
    }

    fn validate_child(input: TermInput, parent: ExprId, child: ExprId) -> Result<(), Halt> {
        if child.index() >= parent.index() {
            return Err(Halt::Fault(TermFault::NonBackwardExpressionReference {
                input,
                parent: parent.index(),
                child: child.index(),
            }));
        }
        Ok(())
    }

    fn validate_expression(input: TermInput, id: ExprId, node: &ExprNode) -> Result<(), Halt> {
        match node {
            ExprNode::Apply { function, argument } => {
                Self::validate_child(input, id, *function)?;
                Self::validate_child(input, id, *argument)
            }
            ExprNode::Lambda {
                binder_type, body, ..
            }
            | ExprNode::Forall {
                binder_type, body, ..
            } => {
                Self::validate_child(input, id, *binder_type)?;
                Self::validate_child(input, id, *body)
            }
            ExprNode::Let {
                type_, value, body, ..
            } => {
                Self::validate_child(input, id, *type_)?;
                Self::validate_child(input, id, *value)?;
                Self::validate_child(input, id, *body)
            }
            ExprNode::Metadata { expression, .. } | ExprNode::Projection { expression, .. } => {
                Self::validate_child(input, id, *expression)
            }
            ExprNode::Bound { .. }
            | ExprNode::Free { .. }
            | ExprNode::Meta { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Constant { .. }
            | ExprNode::NatLiteral { .. }
            | ExprNode::StringLiteral(_) => Ok(()),
        }
    }

    fn push_reserved(&mut self, node: ExprNode, at: usize) -> Result<ExprId, Halt> {
        let observed = usize_units(self.nodes.len()).saturating_add(1);
        self.control.admit_arena_node(observed, at)?;
        let id = ExprId::from_index(self.nodes.len())
            .ok_or_else(|| self.control.arena_nodes(observed, at))?;
        self.nodes.push(node);
        Ok(id)
    }

    fn emit(&mut self, node: ExprNode, at: usize) -> Result<(), Halt> {
        self.control.output(expression_owned_units(&node), at)?;
        self.retain_reserved(node, at)
    }

    fn retain_reserved(&mut self, node: ExprNode, at: usize) -> Result<(), Halt> {
        let id = self.push_reserved(node, at)?;
        self.values.push(id);
        Ok(())
    }

    fn mapped_level(&mut self, input: TermInput, id: LevelId) -> Result<LevelId, Halt> {
        if self.compact_levels {
            return self.ensure_compact_level(input, id);
        }
        self.ensure_levels(input)?;
        self.level_maps[Self::map_index(input)]
            .as_ref()
            .and_then(|mapping| mapping.get(id.index()))
            .copied()
            .ok_or(Halt::Fault(TermFault::MissingLevel {
                input,
                index: id.index(),
            }))
    }

    fn ensure_levels(&mut self, input: TermInput) -> Result<(), Halt> {
        let map_index = Self::map_index(input);
        if self.level_maps[map_index].is_some() {
            return Ok(());
        }
        let source_len = self.input(input)?.levels().len();
        let mut mapping = Vec::new();
        for index in 0..source_len {
            self.control.step(index)?;
            let node = self
                .input(input)?
                .levels()
                .get(index)
                .ok_or(Halt::Fault(TermFault::MissingLevel { input, index }))?
                .clone();
            self.control.output(level_owned_units(&node), index)?;
            let mapped = match node {
                LevelNode::Zero => LevelNode::Zero,
                LevelNode::Succ(child) => {
                    LevelNode::Succ(Self::mapped_prior_level(&mapping, input, index, child)?)
                }
                LevelNode::Max(left, right) => LevelNode::Max(
                    Self::mapped_prior_level(&mapping, input, index, left)?,
                    Self::mapped_prior_level(&mapping, input, index, right)?,
                ),
                LevelNode::IMax(left, right) => LevelNode::IMax(
                    Self::mapped_prior_level(&mapping, input, index, left)?,
                    Self::mapped_prior_level(&mapping, input, index, right)?,
                ),
                LevelNode::Parameter(name) => LevelNode::Parameter(name),
                LevelNode::Meta(name) => LevelNode::Meta(name),
            };
            let observed = usize_units(self.levels.len()).saturating_add(1);
            self.control.admit_arena_node(observed, index)?;
            let id = LevelId::from_index(self.levels.len())
                .ok_or_else(|| self.control.arena_nodes(observed, index))?;
            self.levels.push(mapped);
            mapping.push(id);
        }
        self.level_maps[map_index] = Some(mapping);
        Ok(())
    }

    fn ensure_compact_level(&mut self, input: TermInput, root: LevelId) -> Result<LevelId, Halt> {
        let map_index = Self::map_index(input);
        if let Some(mapped) = self.compact_level_maps[map_index].get(&root.index()) {
            return Ok(*mapped);
        }
        if self.input(input)?.level(root).is_none() {
            return Err(Halt::Fault(TermFault::MissingLevel {
                input,
                index: root.index(),
            }));
        }

        let mut stack = vec![(root, false)];
        while let Some((id, expanded)) = stack.pop() {
            if self.compact_level_maps[map_index].contains_key(&id.index()) {
                continue;
            }
            let node = self
                .input(input)?
                .level(id)
                .ok_or(Halt::Fault(TermFault::MissingLevel {
                    input,
                    index: id.index(),
                }))?
                .clone();
            let children = match &node {
                LevelNode::Succ(child) => vec![*child],
                LevelNode::Max(left, right) | LevelNode::IMax(left, right) => {
                    vec![*left, *right]
                }
                LevelNode::Zero | LevelNode::Parameter(_) | LevelNode::Meta(_) => Vec::new(),
            };
            for child in &children {
                if child.index() >= id.index() {
                    return Err(Halt::Fault(TermFault::NonBackwardLevelReference {
                        input,
                        parent: id.index(),
                        child: child.index(),
                    }));
                }
                if self.input(input)?.level(*child).is_none() {
                    return Err(Halt::Fault(TermFault::MissingLevel {
                        input,
                        index: child.index(),
                    }));
                }
            }
            if !expanded {
                stack.push((id, true));
                for child in children.into_iter().rev() {
                    if !self.compact_level_maps[map_index].contains_key(&child.index()) {
                        stack.push((child, false));
                    }
                }
                continue;
            }

            self.control.step(id.index())?;
            self.control.output(level_owned_units(&node), id.index())?;
            let mapped_node = match node {
                LevelNode::Zero => LevelNode::Zero,
                LevelNode::Succ(child) => LevelNode::Succ(Self::mapped_compact_level(
                    &self.compact_level_maps[map_index],
                    input,
                    id.index(),
                    child,
                )?),
                LevelNode::Max(left, right) => LevelNode::Max(
                    Self::mapped_compact_level(
                        &self.compact_level_maps[map_index],
                        input,
                        id.index(),
                        left,
                    )?,
                    Self::mapped_compact_level(
                        &self.compact_level_maps[map_index],
                        input,
                        id.index(),
                        right,
                    )?,
                ),
                LevelNode::IMax(left, right) => LevelNode::IMax(
                    Self::mapped_compact_level(
                        &self.compact_level_maps[map_index],
                        input,
                        id.index(),
                        left,
                    )?,
                    Self::mapped_compact_level(
                        &self.compact_level_maps[map_index],
                        input,
                        id.index(),
                        right,
                    )?,
                ),
                LevelNode::Parameter(name) => LevelNode::Parameter(name),
                LevelNode::Meta(name) => LevelNode::Meta(name),
            };
            let observed = usize_units(self.levels.len()).saturating_add(1);
            self.control.admit_arena_node(observed, id.index())?;
            let mapped = LevelId::from_index(self.levels.len())
                .ok_or_else(|| self.control.arena_nodes(observed, id.index()))?;
            self.levels.push(mapped_node);
            self.compact_level_maps[map_index].insert(id.index(), mapped);
        }

        self.compact_level_maps[map_index]
            .get(&root.index())
            .copied()
            .ok_or(Halt::Fault(TermFault::MissingLevel {
                input,
                index: root.index(),
            }))
    }

    fn mapped_prior_level(
        mapping: &[LevelId],
        input: TermInput,
        parent: usize,
        child: LevelId,
    ) -> Result<LevelId, Halt> {
        if child.index() >= parent {
            return Err(Halt::Fault(TermFault::NonBackwardLevelReference {
                input,
                parent,
                child: child.index(),
            }));
        }
        mapping
            .get(child.index())
            .copied()
            .ok_or(Halt::Fault(TermFault::MissingLevel {
                input,
                index: child.index(),
            }))
    }

    fn mapped_compact_level(
        mapping: &BTreeMap<usize, LevelId>,
        input: TermInput,
        parent: usize,
        child: LevelId,
    ) -> Result<LevelId, Halt> {
        if child.index() >= parent {
            return Err(Halt::Fault(TermFault::NonBackwardLevelReference {
                input,
                parent,
                child: child.index(),
            }));
        }
        mapping
            .get(&child.index())
            .copied()
            .ok_or(Halt::Fault(TermFault::MissingLevel {
                input,
                index: child.index(),
            }))
    }

    fn raised(
        index: u32,
        amount: u64,
        cutoff: u64,
        at: usize,
        control: &Control<'_>,
    ) -> Result<u32, Halt> {
        if u64::from(index) < cutoff {
            return Ok(index);
        }
        let observed = u64::from(index).saturating_add(amount);
        if observed > u64::from(MAX_BVAR_INDEX) {
            return Err(control.bound_index(observed, at));
        }
        Ok(observed as u32)
    }

    fn visit_bound(&mut self, index: u32, mode: Mode, at: usize) -> Result<(), Halt> {
        match mode {
            Mode::Raise { amount, cutoff } => {
                let index = Self::raised(index, amount, cutoff, at, &self.control)?;
                self.emit(ExprNode::Bound { index }, at)
            }
            Mode::Rewrite { scope } => match self.operation {
                Operation::Raise => self.emit(ExprNode::Bound { index }, at),
                Operation::Bound { target } => {
                    let sought = u64::from(target).saturating_add(scope);
                    match u64::from(index).cmp(&sought) {
                        std::cmp::Ordering::Equal => {
                            self.tasks.push(Task::Visit {
                                input: TermInput::Replacement,
                                id: self.root(TermInput::Replacement)?,
                                mode: Mode::Raise {
                                    amount: scope,
                                    cutoff: 0,
                                },
                            });
                            Ok(())
                        }
                        std::cmp::Ordering::Greater => {
                            self.emit(ExprNode::Bound { index: index - 1 }, at)
                        }
                        std::cmp::Ordering::Less => self.emit(ExprNode::Bound { index }, at),
                    }
                }
                Operation::Close { .. } => {
                    let index = Self::raised(index, 1, scope, at, &self.control)?;
                    self.emit(ExprNode::Bound { index }, at)
                }
                Operation::CloseMany { binder_count, .. } => {
                    let index =
                        Self::raised(index, u64::from(binder_count), scope, at, &self.control)?;
                    self.emit(ExprNode::Bound { index }, at)
                }
                Operation::Free { .. } => self.emit(ExprNode::Bound { index }, at),
            },
        }
    }

    fn child_modes(mode: Mode) -> (Mode, Mode) {
        match mode {
            Mode::Rewrite { scope } => (
                mode,
                Mode::Rewrite {
                    scope: scope.saturating_add(1),
                },
            ),
            Mode::Raise { amount, cutoff } => (
                mode,
                Mode::Raise {
                    amount,
                    cutoff: cutoff.saturating_add(1),
                },
            ),
        }
    }

    fn visit(&mut self, input: TermInput, id: ExprId, mode: Mode) -> Result<(), Halt> {
        self.control.step(id.index())?;
        let free_action = {
            let node = self.expression(input, id)?;
            Self::validate_expression(input, id, node)?;
            match node {
                ExprNode::Bound { index } => {
                    return self.visit_bound(*index, mode, id.index());
                }
                ExprNode::Free { name } => Some(match mode {
                    Mode::Raise { .. } => FreeAction::Retain,
                    Mode::Rewrite { scope } => match self.operation {
                        Operation::Close { name: target } if name == target => {
                            FreeAction::Close { index: scope }
                        }
                        Operation::CloseMany {
                            ordinals,
                            binder_count,
                        } => match ordinals.get(name) {
                            Some(ordinal) if *ordinal < binder_count => {
                                let index =
                                    u64::from(binder_count - 1 - *ordinal).saturating_add(scope);
                                FreeAction::Close { index }
                            }
                            Some(_) | None => FreeAction::Retain,
                        },
                        Operation::Free { name: target } if name == target => {
                            FreeAction::Replace { scope }
                        }
                        Operation::Raise
                        | Operation::Bound { .. }
                        | Operation::Close { .. }
                        | Operation::Free { .. } => FreeAction::Retain,
                    },
                }),
                ExprNode::Meta { .. }
                | ExprNode::Sort { .. }
                | ExprNode::Constant { .. }
                | ExprNode::Apply { .. }
                | ExprNode::Lambda { .. }
                | ExprNode::Forall { .. }
                | ExprNode::Let { .. }
                | ExprNode::NatLiteral { .. }
                | ExprNode::StringLiteral(_)
                | ExprNode::Metadata { .. }
                | ExprNode::Projection { .. } => None,
            }
        };

        if let Some(action) = free_action {
            match action {
                FreeAction::Retain => {
                    let output_units = expression_owned_units(self.expression(input, id)?);
                    self.control.output(output_units, id.index())?;
                    let ExprNode::Free { name } = self.expression(input, id)? else {
                        return Err(Halt::Fault(TermFault::MissingExpression {
                            input,
                            index: id.index(),
                        }));
                    };
                    return self.retain_reserved(ExprNode::Free { name: name.clone() }, id.index());
                }
                FreeAction::Close { index } => {
                    if index > u64::from(MAX_BVAR_INDEX) {
                        return Err(self.control.bound_index(index, id.index()));
                    }
                    return self.emit(
                        ExprNode::Bound {
                            index: index as u32,
                        },
                        id.index(),
                    );
                }
                FreeAction::Replace { scope } => {
                    self.tasks.push(Task::Visit {
                        input: TermInput::Replacement,
                        id: self.root(TermInput::Replacement)?,
                        mode: Mode::Raise {
                            amount: scope,
                            cutoff: 0,
                        },
                    });
                    return Ok(());
                }
            }
        }

        let output_units = expression_owned_units(self.expression(input, id)?);
        self.control.output(output_units, id.index())?;
        let node = self.expression(input, id)?.clone();
        match node {
            ExprNode::Bound { .. } | ExprNode::Free { .. } => {
                unreachable!("handled before payload reservation")
            }
            ExprNode::Meta { name } => self.retain_reserved(ExprNode::Meta { name }, id.index()),
            ExprNode::Sort { level } => {
                let level = self.mapped_level(input, level)?;
                self.retain_reserved(ExprNode::Sort { level }, id.index())
            }
            ExprNode::Constant { name, levels } => {
                let mut mapped = Vec::new();
                for level in levels {
                    mapped.push(self.mapped_level(input, level)?);
                }
                self.retain_reserved(
                    ExprNode::Constant {
                        name,
                        levels: mapped,
                    },
                    id.index(),
                )
            }
            ExprNode::Apply { function, argument } => {
                self.tasks.push(Task::Build(Frame::Apply));
                self.tasks.push(Task::Visit {
                    input,
                    id: argument,
                    mode,
                });
                self.tasks.push(Task::Visit {
                    input,
                    id: function,
                    mode,
                });
                Ok(())
            }
            ExprNode::Lambda {
                binder_name,
                binder_type,
                body,
                style,
            } => {
                let (ordinary, body_mode) = Self::child_modes(mode);
                self.tasks
                    .push(Task::Build(Frame::Lambda { binder_name, style }));
                self.tasks.push(Task::Visit {
                    input,
                    id: body,
                    mode: body_mode,
                });
                self.tasks.push(Task::Visit {
                    input,
                    id: binder_type,
                    mode: ordinary,
                });
                Ok(())
            }
            ExprNode::Forall {
                binder_name,
                binder_type,
                body,
                style,
            } => {
                let (ordinary, body_mode) = Self::child_modes(mode);
                self.tasks
                    .push(Task::Build(Frame::Forall { binder_name, style }));
                self.tasks.push(Task::Visit {
                    input,
                    id: body,
                    mode: body_mode,
                });
                self.tasks.push(Task::Visit {
                    input,
                    id: binder_type,
                    mode: ordinary,
                });
                Ok(())
            }
            ExprNode::Let {
                declaration_name,
                type_,
                value,
                body,
                non_dependent,
            } => {
                let (ordinary, body_mode) = Self::child_modes(mode);
                self.tasks.push(Task::Build(Frame::Let {
                    declaration_name,
                    non_dependent,
                }));
                self.tasks.push(Task::Visit {
                    input,
                    id: body,
                    mode: body_mode,
                });
                self.tasks.push(Task::Visit {
                    input,
                    id: value,
                    mode: ordinary,
                });
                self.tasks.push(Task::Visit {
                    input,
                    id: type_,
                    mode: ordinary,
                });
                Ok(())
            }
            ExprNode::NatLiteral { limbs_le } => {
                self.retain_reserved(ExprNode::NatLiteral { limbs_le }, id.index())
            }
            ExprNode::StringLiteral(text) => {
                self.retain_reserved(ExprNode::StringLiteral(text), id.index())
            }
            ExprNode::Metadata {
                entries,
                expression,
            } => {
                self.tasks.push(Task::Build(Frame::Metadata { entries }));
                self.tasks.push(Task::Visit {
                    input,
                    id: expression,
                    mode,
                });
                Ok(())
            }
            ExprNode::Projection {
                structure_name,
                index,
                expression,
            } => {
                self.tasks.push(Task::Build(Frame::Projection {
                    structure_name,
                    index,
                }));
                self.tasks.push(Task::Visit {
                    input,
                    id: expression,
                    mode,
                });
                Ok(())
            }
        }
    }

    fn pop_value(&mut self) -> Result<ExprId, Halt> {
        self.values
            .pop()
            .ok_or(Halt::Fault(TermFault::ValueStack { entries: 0 }))
    }

    fn build(&mut self, frame: Frame) -> Result<(), Halt> {
        let node = match frame {
            Frame::Apply => {
                let argument = self.pop_value()?;
                let function = self.pop_value()?;
                ExprNode::Apply { function, argument }
            }
            Frame::Lambda { binder_name, style } => {
                let body = self.pop_value()?;
                let binder_type = self.pop_value()?;
                ExprNode::Lambda {
                    binder_name,
                    binder_type,
                    body,
                    style,
                }
            }
            Frame::Forall { binder_name, style } => {
                let body = self.pop_value()?;
                let binder_type = self.pop_value()?;
                ExprNode::Forall {
                    binder_name,
                    binder_type,
                    body,
                    style,
                }
            }
            Frame::Let {
                declaration_name,
                non_dependent,
            } => {
                let body = self.pop_value()?;
                let value = self.pop_value()?;
                let type_ = self.pop_value()?;
                ExprNode::Let {
                    declaration_name,
                    type_,
                    value,
                    body,
                    non_dependent,
                }
            }
            Frame::Metadata { entries } => {
                let expression = self.pop_value()?;
                ExprNode::Metadata {
                    entries,
                    expression,
                }
            }
            Frame::Projection {
                structure_name,
                index,
            } => {
                let expression = self.pop_value()?;
                ExprNode::Projection {
                    structure_name,
                    index,
                    expression,
                }
            }
        };
        let id = self.push_reserved(node, self.nodes.len())?;
        self.values.push(id);
        Ok(())
    }

    fn run(mut self, root_mode: Mode) -> Result<WireExpr, Halt> {
        self.tasks.push(Task::Visit {
            input: TermInput::Subject,
            id: self.subject_root,
            mode: root_mode,
        });
        while let Some(task) = self.tasks.pop() {
            match task {
                Task::Visit { input, id, mode } => self.visit(input, id, mode)?,
                Task::Build(frame) => self.build(frame)?,
            }
        }
        if self.values.len() != 1 {
            return Err(Halt::Fault(TermFault::ValueStack {
                entries: self.values.len(),
            }));
        }
        let root = self.values.pop().expect("length checked");
        Ok(WireExpr::from_parts(self.nodes, self.levels, root))
    }
}

fn transform_with(
    subject: &WireExpr,
    replacement: Option<&WireExpr>,
    operation: Operation<'_>,
    root_mode: Mode,
    budget: TermBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> TermOutcome<WireExpr> {
    transform_subterms_with(
        subject,
        subject.root(),
        TransformPlan {
            replacement: replacement.map(|term| (term, term.root())),
            operation,
            root_mode,
            compact_levels: false,
        },
        budget,
        cancelled,
    )
}

fn transform_subterms_with(
    subject: &WireExpr,
    subject_root: ExprId,
    plan: TransformPlan<'_>,
    budget: TermBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> TermOutcome<WireExpr> {
    let transformer = Transformer {
        subject,
        subject_root,
        replacement: plan.replacement,
        operation: plan.operation,
        control: Control::new(budget, cancelled),
        nodes: Vec::new(),
        levels: Vec::new(),
        level_maps: [None, None],
        compact_level_maps: [BTreeMap::new(), BTreeMap::new()],
        compact_levels: plan.compact_levels,
        values: Vec::new(),
        tasks: Vec::new(),
    };
    outcome(transformer.run(plan.root_mode))
}

pub(crate) fn copy_subterm_with(
    term: &WireExpr,
    root: ExprId,
    budget: TermBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> TermOutcome<WireExpr> {
    transform_subterms_with(
        term,
        root,
        TransformPlan {
            replacement: None,
            operation: Operation::Raise,
            root_mode: Mode::Rewrite { scope: 0 },
            compact_levels: false,
        },
        budget,
        cancelled,
    )
}

pub(crate) fn copy_compact_subterm_with(
    term: &WireExpr,
    root: ExprId,
    budget: TermBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> TermOutcome<WireExpr> {
    transform_subterms_with(
        term,
        root,
        TransformPlan {
            replacement: None,
            operation: Operation::Raise,
            root_mode: Mode::Rewrite { scope: 0 },
            compact_levels: true,
        },
        budget,
        cancelled,
    )
}

pub(crate) fn substitute_bound_subterms_with(
    term: &WireExpr,
    root: ExprId,
    index: u32,
    replacement: &WireExpr,
    replacement_root: ExprId,
    budget: TermBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> TermOutcome<WireExpr> {
    transform_subterms_with(
        term,
        root,
        TransformPlan {
            replacement: Some((replacement, replacement_root)),
            operation: Operation::Bound { target: index },
            root_mode: Mode::Rewrite { scope: 0 },
            compact_levels: false,
        },
        budget,
        cancelled,
    )
}

/// Raise every external bound index at or above `cutoff` by `amount`.
pub fn raise_external_bounds(
    term: &WireExpr,
    amount: u32,
    cutoff: u32,
    budget: TermBudget,
) -> TermOutcome<WireExpr> {
    raise_external_bounds_with(term, amount, cutoff, budget, || false)
}

pub fn raise_external_bounds_with(
    term: &WireExpr,
    amount: u32,
    cutoff: u32,
    budget: TermBudget,
    mut cancelled: impl FnMut() -> bool,
) -> TermOutcome<WireExpr> {
    transform_with(
        term,
        None,
        Operation::Raise,
        Mode::Raise {
            amount: u64::from(amount),
            cutoff: u64::from(cutoff),
        },
        budget,
        &mut cancelled,
    )
}

/// Consume one bound variable and replace it capture-safely.
///
/// Indices looser than the consumed binder move down by one. If the replacement
/// itself has external bound variables, they are raised beneath nested binders.
pub fn substitute_bound(
    term: &WireExpr,
    index: u32,
    replacement: &WireExpr,
    budget: TermBudget,
) -> TermOutcome<WireExpr> {
    substitute_bound_with(term, index, replacement, budget, || false)
}

pub fn substitute_bound_with(
    term: &WireExpr,
    index: u32,
    replacement: &WireExpr,
    budget: TermBudget,
    mut cancelled: impl FnMut() -> bool,
) -> TermOutcome<WireExpr> {
    transform_with(
        term,
        Some(replacement),
        Operation::Bound { target: index },
        Mode::Rewrite { scope: 0 },
        budget,
        &mut cancelled,
    )
}

/// Close a term over one free name, shifting existing external indices away
/// from the new binder.
pub fn abstract_free(
    term: &WireExpr,
    name: &WireName,
    budget: TermBudget,
) -> TermOutcome<WireExpr> {
    abstract_free_with(term, name, budget, || false)
}

pub fn abstract_free_with(
    term: &WireExpr,
    name: &WireName,
    budget: TermBudget,
    mut cancelled: impl FnMut() -> bool,
) -> TermOutcome<WireExpr> {
    transform_with(
        term,
        None,
        Operation::Close { name },
        Mode::Rewrite { scope: 0 },
        budget,
        &mut cancelled,
    )
}

/// Close a term over an ordered telescope of query-local free names in one
/// occurrence walk.
///
/// `ordinals` records each name's outer-to-inner binder position. A prefix of
/// `binder_count` entries is in scope at the term root, so ordinal `0` becomes
/// bound index `binder_count - 1` and the last active ordinal becomes index
/// zero. Existing external bound variables are raised by the whole prefix at
/// once. Names whose ordinal is outside the active prefix remain free.
pub(crate) fn abstract_free_telescope_with(
    term: &WireExpr,
    ordinals: &BTreeMap<WireName, u32>,
    binder_count: u32,
    budget: TermBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> TermOutcome<WireExpr> {
    transform_with(
        term,
        None,
        Operation::CloseMany {
            ordinals,
            binder_count,
        },
        Mode::Rewrite { scope: 0 },
        budget,
        cancelled,
    )
}

/// Replace one free name capture-safely throughout a term.
pub fn substitute_free(
    term: &WireExpr,
    name: &WireName,
    replacement: &WireExpr,
    budget: TermBudget,
) -> TermOutcome<WireExpr> {
    substitute_free_with(term, name, replacement, budget, || false)
}

pub fn substitute_free_with(
    term: &WireExpr,
    name: &WireName,
    replacement: &WireExpr,
    budget: TermBudget,
    mut cancelled: impl FnMut() -> bool,
) -> TermOutcome<WireExpr> {
    transform_with(
        term,
        Some(replacement),
        Operation::Free { name },
        Mode::Rewrite { scope: 0 },
        budget,
        &mut cancelled,
    )
}
