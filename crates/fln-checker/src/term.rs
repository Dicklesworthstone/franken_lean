//! Independent term facts and capture-avoiding rewrites over checker-owned arenas.
//!
//! This module deliberately derives scope and traversal facts from the wire nodes
//! themselves. It never consumes the primary expression data word. Rewrites are
//! memoized per (node, binder context) when variables can be affected: the shared
//! wire schema meets one node beneath different binder depths. Independently
//! derived input-scope facts prove when a rewrite is a pure copy, allowing those
//! subterms to retain their sharing across depths and substitution input roles.

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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
    let facts = inspect_nodes_inner(term, control)?;
    facts
        .get(term.root().index())
        .copied()
        .ok_or(Halt::Fault(TermFault::MissingExpression {
            input: TermInput::Subject,
            index: term.root().index(),
        }))
}

fn inspect_nodes_inner(term: &WireExpr, control: &mut Control<'_>) -> Result<Vec<TermFacts>, Halt> {
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
    Ok(facts)
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

/// [`inspect`]'s facts for every node of `term`, indexed by [`ExprId`], so a
/// caller asking about many subterms of one arena validates and walks it once.
pub(crate) fn inspect_nodes_with(
    term: &WireExpr,
    budget: TermBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> TermOutcome<Vec<TermFacts>> {
    let mut control = Control::new(budget, cancelled);
    outcome(inspect_nodes_inner(term, &mut control))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Mode {
    /// No variable in this subterm can be affected by the operation. Unlike a
    /// rewrite, this mode is independent of the occurrence's binder depth.
    Copy,
    Rewrite {
        scope: u64,
    },
    Raise {
        amount: u64,
        cutoff: u64,
    },
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
    /// The visit keyed here has just left its one result on the value stack.
    Record(VisitKey),
}

/// What a visit's output depends on besides the fixed operation and
/// replacement: which arena, which node, and the binder context it is met in.
type VisitKey = (TermInput, ExprId, Mode);

/// A deterministic multiplicative hasher for the transform memo, which is only
/// ever looked up, never iterated. `std`'s keyed default costs more than the
/// rewrite it saves on the small keys here.
#[derive(Default, Clone, Copy)]
struct KeyHasher(u64);

impl KeyHasher {
    fn add(&mut self, word: u64) {
        self.0 = (self.0.rotate_left(5) ^ word).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
}

impl std::hash::Hasher for KeyHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.add(u64::from(*byte));
        }
    }

    fn write_u8(&mut self, value: u8) {
        self.add(u64::from(value));
    }

    fn write_u32(&mut self, value: u32) {
        self.add(u64::from(value));
    }

    fn write_u64(&mut self, value: u64) {
        self.add(value);
    }

    fn write_usize(&mut self, value: usize) {
        self.add(value as u64);
    }

    fn write_isize(&mut self, value: isize) {
        self.add(value as u64);
    }
}

type VisitMemo =
    std::collections::HashMap<VisitKey, ExprId, std::hash::BuildHasherDefault<KeyHasher>>;

/// Raw, occurrence-independent scope facts. These describe the INPUT node,
/// not its rewritten result. They are learned on the ordinary postorder walk,
/// so preserving an unaffected DAG needs neither another traversal nor facts
/// imported from the primary checker.
#[derive(Clone, Copy, Default)]
struct RewriteScope {
    external: u64,
    free: bool,
}

impl RewriteScope {
    fn union(self, other: Self) -> Self {
        Self {
            external: self.external.max(other.external),
            free: self.free || other.free,
        }
    }

    fn beneath_binder(self) -> Self {
        Self {
            external: self.external.saturating_sub(1),
            ..self
        }
    }
}

type ScopeMemo = std::collections::HashMap<
    (TermInput, ExprId),
    RewriteScope,
    std::hash::BuildHasherDefault<KeyHasher>,
>;

/// Past this many subject nodes a pure copy keys its visits in the map, so its
/// table never costs more than the arena it indexes could.
const DENSE_COPY_MAX_NODES: usize = 1 << 22;

/// The visits already rewritten, keyed by what their output depends on.
enum Visited {
    /// A pure copy rewrites nothing, so a node's output is the same in every
    /// binder context. One slot per subject node (its output index plus one; 0 is
    /// unvisited) keeps all of the input's sharing and costs no hashing.
    Copy(Vec<u32>),
    Keyed(VisitMemo),
}

impl Visited {
    fn for_plan(plan: &TransformPlan<'_>, subject_root: ExprId) -> Visited {
        let pure_copy = plan.replacement.is_none()
            && matches!(plan.operation, Operation::Raise)
            && matches!(plan.root_mode, Mode::Rewrite { .. });
        let slots = subject_root.index().saturating_add(1);
        if pure_copy && slots <= DENSE_COPY_MAX_NODES {
            Visited::Copy(vec![0; slots])
        } else {
            Visited::Keyed(VisitMemo::default())
        }
    }

    fn get(&self, key: &VisitKey) -> Option<ExprId> {
        match self {
            Visited::Copy(slots) => slots
                .get(key.1.index())
                .and_then(|slot| slot.checked_sub(1))
                .and_then(|index| ExprId::from_index(index as usize)),
            Visited::Keyed(memo) => memo.get(key).copied(),
        }
    }

    fn insert(&mut self, key: VisitKey, done: ExprId) {
        match self {
            Visited::Copy(slots) => {
                if let (Some(slot), Ok(index)) =
                    (slots.get_mut(key.1.index()), u32::try_from(done.index()))
                {
                    *slot = index.saturating_add(1);
                }
            }
            Visited::Keyed(memo) => {
                memo.insert(key, done);
            }
        }
    }
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
    compact_level_maps: [CompactLevelMap; 2],
    compact_levels: bool,
    values: Vec<ExprId>,
    tasks: Vec<Task>,
    /// Each affected (arena, node, binder context) is rewritten once. Proven
    /// copies share one entry across contexts, without reusing a changed result
    /// as the original input node.
    memo: Visited,
    scopes: Option<ScopeMemo>,
}

impl<'a, 'c> Transformer<'a, 'c> {
    fn canonical_input(&self, input: TermInput) -> TermInput {
        if input == TermInput::Replacement
            && self
                .replacement
                .is_some_and(|(term, _)| std::ptr::eq(term, self.subject))
        {
            // A beta/zeta replacement is often a cursor into the subject's
            // own arena. Equal arena addresses, not equal hashes, establish
            // that copying the same raw node can reuse the same output.
            TermInput::Subject
        } else {
            input
        }
    }

    fn canonical_mode(&self, input: TermInput, id: ExprId, mode: Mode) -> Mode {
        match mode {
            Mode::Copy | Mode::Raise { amount: 0, .. } => return Mode::Copy,
            Mode::Rewrite { .. }
                if matches!(
                    self.operation,
                    Operation::Raise
                        | Operation::CloseMany {
                            binder_count: 0,
                            ..
                        }
                ) =>
            {
                return Mode::Copy;
            }
            _ => {}
        }
        let Some(scope) = self.scopes.as_ref().and_then(|memo| memo.get(&(input, id))) else {
            return mode;
        };
        let unchanged = match mode {
            Mode::Copy => true,
            Mode::Raise { cutoff, .. } => scope.external <= cutoff,
            Mode::Rewrite { scope: depth } => match self.operation {
                Operation::Raise => true,
                Operation::Bound { target } => {
                    scope.external <= depth.saturating_add(u64::from(target))
                }
                Operation::Free { .. } => !scope.free,
                Operation::Close { .. } | Operation::CloseMany { .. } => {
                    !scope.free && scope.external <= depth
                }
            },
        };
        if unchanged { Mode::Copy } else { mode }
    }

    fn remember_scope(&mut self, input: TermInput, id: ExprId) -> Result<(), Halt> {
        let Some(scopes) = self.scopes.as_ref() else {
            return Ok(());
        };
        if scopes.contains_key(&(input, id)) {
            return Ok(());
        }
        let child = |id: ExprId| {
            scopes
                .get(&(input, id))
                .copied()
                .ok_or(Halt::Fault(TermFault::MissingExpression {
                    input,
                    index: id.index(),
                }))
        };
        let facts = match self.expression(input, id)? {
            ExprNode::Bound { index } => RewriteScope {
                external: u64::from(*index) + 1,
                free: false,
            },
            ExprNode::Free { .. } => RewriteScope {
                external: 0,
                free: true,
            },
            ExprNode::Apply { function, argument } => child(*function)?.union(child(*argument)?),
            ExprNode::Lambda {
                binder_type, body, ..
            }
            | ExprNode::Forall {
                binder_type, body, ..
            } => child(*binder_type)?.union(child(*body)?.beneath_binder()),
            ExprNode::Let {
                type_, value, body, ..
            } => child(*type_)?
                .union(child(*value)?)
                .union(child(*body)?.beneath_binder()),
            ExprNode::Metadata { expression, .. } | ExprNode::Projection { expression, .. } => {
                child(*expression)?
            }
            ExprNode::Meta { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Constant { .. }
            | ExprNode::NatLiteral { .. }
            | ExprNode::StringLiteral(_) => RewriteScope::default(),
        };
        if let Some(scopes) = self.scopes.as_mut() {
            scopes.insert((input, id), facts);
        }
        Ok(())
    }

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
        if let Some(mapped) = self.compact_level_maps[map_index].get(root.index()) {
            return Ok(mapped);
        }
        if self.input(input)?.level(root).is_none() {
            return Err(Halt::Fault(TermFault::MissingLevel {
                input,
                index: root.index(),
            }));
        }

        let mut stack = vec![(root, false)];
        while let Some((id, expanded)) = stack.pop() {
            if self.compact_level_maps[map_index].contains(id.index()) {
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
                    if !self.compact_level_maps[map_index].contains(child.index()) {
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
            .get(root.index())
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
        mapping: &CompactLevelMap,
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
            Mode::Copy => self.emit(ExprNode::Bound { index }, at),
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
            Mode::Copy => (Mode::Copy, Mode::Copy),
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
                    Mode::Copy => FreeAction::Retain,
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
                Task::Visit { input, id, mode } => {
                    let input = self.canonical_input(input);
                    let mode = self.canonical_mode(input, id, mode);
                    if let Some(done) = self.memo.get(&(input, id, mode)) {
                        self.values.push(done);
                        continue;
                    }
                    self.tasks.push(Task::Record((input, id, mode)));
                    self.visit(input, id, mode)?;
                }
                Task::Build(frame) => self.build(frame)?,
                Task::Record(key) => {
                    let done = *self
                        .values
                        .last()
                        .ok_or(Halt::Fault(TermFault::ValueStack { entries: 0 }))?;
                    self.memo.insert(key, done);
                    self.remember_scope(key.0, key.1)?;
                    if self.canonical_mode(key.0, key.1, key.2) == Mode::Copy {
                        self.memo.insert((key.0, key.1, Mode::Copy), done);
                    }
                }
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

/// Source level index to output level, filled as referenced levels are copied.
/// Indexed directly: compact copies look a level up once per occurrence, and a
/// tree map there was a fifth of the checker's time on WF-recursion lemmas.
#[derive(Default)]
struct CompactLevelMap(Vec<Option<LevelId>>);

impl CompactLevelMap {
    fn get(&self, index: usize) -> Option<LevelId> {
        self.0.get(index).copied().flatten()
    }

    fn contains(&self, index: usize) -> bool {
        self.get(index).is_some()
    }

    fn insert(&mut self, index: usize, level: LevelId) {
        if self.0.len() <= index {
            self.0.resize(index + 1, None);
        }
        if let Some(slot) = self.0.get_mut(index) {
            *slot = Some(level);
        }
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
            compact_levels: true,
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
        compact_level_maps: [CompactLevelMap::default(), CompactLevelMap::default()],
        compact_levels: plan.compact_levels,
        values: Vec::new(),
        tasks: Vec::new(),
        memo: Visited::for_plan(&plan, subject_root),
        scopes: (!(plan.replacement.is_none()
            && matches!(plan.operation, Operation::Raise)
            && matches!(plan.root_mode, Mode::Rewrite { .. })))
        .then(ScopeMemo::default),
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
            compact_levels: true,
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
            compact_levels: true,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::whnf::{WhnfBudget, WhnfContext, WhnfOutcome, whnf};
    use crate::wire::LevelNode;

    const CHAIN: usize = 1000;

    /// `Sort (succ^999 0)` applied to `Sort 0`, over a level arena holding the
    /// whole 1000-node chain. The `Sort 0` subterm references one level.
    fn bloated() -> Option<(WireExpr, ExprId)> {
        let mut levels = vec![LevelNode::Zero];
        for index in 1..CHAIN {
            levels.push(LevelNode::Succ(LevelId::from_index(index - 1)?));
        }
        let nodes = vec![
            ExprNode::Sort {
                level: LevelId::from_index(CHAIN - 1)?,
            },
            ExprNode::Sort {
                level: LevelId::ZERO,
            },
            ExprNode::Apply {
                function: ExprId::from_index(0)?,
                argument: ExprId::from_index(1)?,
            },
        ];
        Some((
            WireExpr::from_parts(nodes, levels, ExprId::from_index(2)?),
            ExprId::from_index(1)?,
        ))
    }

    /// Copying a subterm carries only the levels it references. Before this,
    /// `copy_subterm_with` copied the source's WHOLE level arena into every
    /// output. Level arenas therefore only grew as rewrites composed, until
    /// one Init proof (`Array.binSearchAux._unary._proof_4`) exhausted a
    /// 20 GB cap inside the checker. With compaction it is admitted in 13 s
    /// at about 0.6 GB.
    #[test]
    fn copying_a_subterm_carries_only_its_own_levels() {
        let fixture = bloated();
        assert!(fixture.is_some(), "fixture construction");
        if let Some((term, small)) = fixture {
            assert_eq!(term.levels().len(), CHAIN);
            let copy = copy_subterm_with(&term, small, TermBudget::unlimited(), &mut || false);
            assert!(
                matches!(&copy, TermOutcome::Complete(copied) if copied.levels().len() == 1),
                "{copy:?}"
            );
        }
    }

    fn name(text: &str) -> WireName {
        WireName::from_parts(vec![crate::wire::NamePart::Text(text.to_owned())])
    }

    fn lambda(binder_type: ExprId, body: ExprId) -> ExprNode {
        ExprNode::Lambda {
            binder_name: name("b"),
            binder_type,
            body,
            style: crate::wire::BinderStyle::Default,
        }
    }

    /// `fun (x : T) => fun (y : T) => T`, where `T` is one node met at binder
    /// depths 0, 1 and 2.
    fn shared_across_depths() -> Option<WireExpr> {
        let nodes = vec![
            ExprNode::Sort {
                level: LevelId::ZERO,
            },
            lambda(ExprId::from_index(0)?, ExprId::from_index(0)?),
            lambda(ExprId::from_index(0)?, ExprId::from_index(1)?),
        ];
        Some(WireExpr::from_parts(
            nodes,
            vec![LevelNode::Zero],
            ExprId::from_index(2)?,
        ))
    }

    /// The tree a term denotes, as text, for comparing shapes.
    fn render(term: &WireExpr, id: ExprId) -> String {
        match term.node(id) {
            Some(ExprNode::Bound { index }) => format!("#{index}"),
            Some(ExprNode::Free { .. }) => "x".to_owned(),
            Some(ExprNode::Sort { .. }) => "Sort".to_owned(),
            Some(ExprNode::Lambda {
                binder_type, body, ..
            }) => format!(
                "(fun {} {})",
                render(term, *binder_type),
                render(term, *body)
            ),
            Some(ExprNode::Apply { function, argument }) => {
                format!("({} {})", render(term, *function), render(term, *argument))
            }
            _ => "?".to_owned(),
        }
    }

    /// A pure copy changes nothing, so a node shared across binder depths is
    /// copied once. Keyed by depth, as the other rewrites must be, `T` came out
    /// three times.
    #[test]
    fn a_pure_copy_keeps_sharing_across_binder_depths() {
        let term = shared_across_depths();
        assert!(term.is_some(), "fixture construction");
        if let Some(term) = term {
            let copy =
                copy_subterm_with(&term, term.root(), TermBudget::unlimited(), &mut || false);
            assert!(
                matches!(&copy, TermOutcome::Complete(copied) if copied.nodes().len() == 3),
                "{copy:?}"
            );
        }
    }

    /// `x (fun (y : Sort 0) => x)`, with `x` free and one node. Closing over
    /// `x` depends on binder depth: the outer `x` becomes index 0 and the inner
    /// one index 1, so this rewrite must still key its visits by depth.
    #[test]
    fn closing_over_a_shared_free_name_respects_binder_depth() {
        let term = (|| {
            Some(WireExpr::from_parts(
                vec![
                    ExprNode::Free { name: name("x") },
                    ExprNode::Sort {
                        level: LevelId::ZERO,
                    },
                    lambda(ExprId::from_index(1)?, ExprId::from_index(0)?),
                    ExprNode::Apply {
                        function: ExprId::from_index(0)?,
                        argument: ExprId::from_index(2)?,
                    },
                ],
                vec![LevelNode::Zero],
                ExprId::from_index(3)?,
            ))
        })();
        assert!(term.is_some(), "fixture construction");
        if let Some(term) = term {
            let closed = abstract_free(&term, &name("x"), TermBudget::unlimited());
            assert!(
                matches!(&closed, TermOutcome::Complete(out) if render(out, out.root()) == "(#0 (fun Sort #1))"),
                "{closed:?}"
            );
        }
    }

    /// The rewrites behind `raise_external_bounds`, `substitute_bound` and the
    /// free-variable operations shed unreferenced levels in the same way, so
    /// an input that arrives bloated does not pass its bloat on.
    #[test]
    fn rewriting_a_term_sheds_levels_it_does_not_reference() {
        let fixture = bloated();
        assert!(fixture.is_some(), "fixture construction");
        if let Some((term, _)) = fixture {
            let root = ExprId::from_index(0);
            assert!(root.is_some());
            if let Some(root) = root {
                let only_zero = WireExpr::from_parts(
                    vec![ExprNode::Sort {
                        level: LevelId::ZERO,
                    }],
                    term.levels().to_vec(),
                    root,
                );
                let raised = raise_external_bounds(&only_zero, 1, 0, TermBudget::unlimited());
                assert!(
                    matches!(&raised, TermOutcome::Complete(out) if out.levels().len() == 1),
                    "{raised:?}"
                );
            }
        }
    }

    fn id(index: usize) -> ExprId {
        ExprId::from_index(index).expect("bounded test arena")
    }

    /// One closed DAG is used as every binder domain, and also replaces the
    /// outer variable beneath all the binders. Both cursors belong to one arena.
    fn scoped_diamond(depth: u32, diamonds: usize) -> (WireExpr, ExprId) {
        let mut nodes = vec![ExprNode::Sort {
            level: LevelId::ZERO,
        }];
        for _ in 0..diamonds {
            let child = id(nodes.len() - 1);
            nodes.push(ExprNode::Apply {
                function: child,
                argument: child,
            });
        }
        let replacement = id(nodes.len() - 1);
        nodes.push(ExprNode::Bound { index: depth });
        for _ in 0..depth {
            nodes.push(lambda(replacement, id(nodes.len() - 1)));
        }
        let root = id(nodes.len() - 1);
        (
            WireExpr::from_parts(nodes, vec![LevelNode::Zero], root),
            replacement,
        )
    }

    #[test]
    fn substitution_preserves_an_unaffected_dag_across_scopes_and_input_roles() {
        let (term, replacement) = scoped_diamond(128, 24);
        let count = term.nodes().len() as u64;
        let result = substitute_bound_subterms_with(
            &term,
            term.root(),
            0,
            &term,
            replacement,
            TermBudget::new(count * 3, count * 12).with_max_arena_nodes(count),
            &mut || false,
        );
        let TermOutcome::Complete(result) = result else {
            panic!("{result:?}")
        };
        assert_eq!(result.nodes().len(), term.nodes().len() - 1);
        let mut cursor = result.root();
        let mut shared_domain = None;
        for _ in 0..128 {
            let ExprNode::Lambda {
                binder_type, body, ..
            } = result.node(cursor).unwrap()
            else {
                panic!("lost binder")
            };
            assert_eq!(*shared_domain.get_or_insert(*binder_type), *binder_type);
            cursor = *body;
        }
        assert_eq!(
            Some(cursor),
            shared_domain,
            "replacement shares the original closed DAG"
        );
    }

    #[test]
    fn unchanged_scopes_never_supply_an_active_bound_rewrite() {
        for first_is_bound in [false, true] {
            let term = WireExpr::from_parts(
                vec![
                    ExprNode::Bound { index: 0 },
                    ExprNode::Sort {
                        level: LevelId::ZERO,
                    },
                    lambda(id(1), id(0)),
                    ExprNode::Apply {
                        function: id(if first_is_bound { 0 } else { 2 }),
                        argument: id(if first_is_bound { 2 } else { 0 }),
                    },
                ],
                vec![LevelNode::Zero],
                id(3),
            );
            let replacement = WireExpr::from_parts(
                vec![ExprNode::NatLiteral { limbs_le: vec![7] }],
                vec![],
                id(0),
            );
            let result = substitute_bound(&term, 0, &replacement, TermBudget::unlimited());
            let TermOutcome::Complete(result) = result else {
                panic!("{result:?}")
            };
            let ExprNode::Apply { function, argument } = result.node(result.root()).unwrap() else {
                panic!("lost application")
            };
            let (bound, nested) = if first_is_bound {
                (*function, *argument)
            } else {
                (*argument, *function)
            };
            assert!(
                matches!(result.node(bound), Some(ExprNode::NatLiteral { limbs_le }) if limbs_le == &[7])
            );
            let ExprNode::Lambda { body, .. } = result.node(nested).unwrap() else {
                panic!("lost lambda")
            };
            assert_eq!(result.node(*body), Some(&ExprNode::Bound { index: 0 }));
        }
    }

    #[test]
    fn equal_slot_numbers_in_different_arenas_never_alias() {
        let subject = WireExpr::from_parts(
            vec![
                ExprNode::NatLiteral { limbs_le: vec![7] },
                ExprNode::Bound { index: 0 },
                ExprNode::Apply {
                    function: id(0),
                    argument: id(1),
                },
            ],
            vec![],
            id(2),
        );
        let replacement = WireExpr::from_parts(
            vec![ExprNode::NatLiteral { limbs_le: vec![9] }],
            vec![],
            id(0),
        );
        let result = substitute_bound(&subject, 0, &replacement, TermBudget::unlimited());
        let TermOutcome::Complete(result) = result else {
            panic!("{result:?}")
        };
        let ExprNode::Apply { function, argument } = result.node(result.root()).unwrap() else {
            panic!("lost app")
        };
        assert_ne!(function, argument);
        assert!(
            matches!(result.node(*function), Some(ExprNode::NatLiteral { limbs_le }) if limbs_le == &[7])
        );
        assert!(
            matches!(result.node(*argument), Some(ExprNode::NatLiteral { limbs_le }) if limbs_le == &[9])
        );
    }

    #[test]
    fn shared_scope_rewrites_keep_every_observed_stop_typed_and_recover() {
        let (term, replacement) = scoped_diamond(6, 5);
        let pristine = term.clone();
        let mut polls = 0;
        let success = substitute_bound_subterms_with(
            &term,
            term.root(),
            0,
            &term,
            replacement,
            TermBudget::unlimited(),
            &mut || {
                polls += 1;
                false
            },
        );
        assert!(matches!(success, TermOutcome::Complete(_)));
        for stop in 1..=polls {
            let mut calls = 0;
            let result = substitute_bound_subterms_with(
                &term,
                term.root(),
                0,
                &term,
                replacement,
                TermBudget::unlimited(),
                &mut || {
                    calls += 1;
                    calls == stop
                },
            );
            assert!(
                matches!(
                    result,
                    TermOutcome::Inconclusive(TermStop::Cancelled { .. })
                ),
                "poll {stop}: {result:?}"
            );
            assert_eq!(term, pristine);
        }
        for budget in [
            TermBudget::new(0, u64::MAX),
            TermBudget::new(u64::MAX, 0),
            TermBudget::unlimited().with_max_arena_nodes(1),
        ] {
            assert!(matches!(
                substitute_bound_subterms_with(
                    &term,
                    term.root(),
                    0,
                    &term,
                    replacement,
                    budget,
                    &mut || false,
                ),
                TermOutcome::Inconclusive(TermStop::Resource { .. })
            ));
        }
        assert_eq!(
            substitute_bound_subterms_with(
                &term,
                term.root(),
                0,
                &term,
                replacement,
                TermBudget::unlimited(),
                &mut || false,
            ),
            success
        );
    }

    /// `let x := z; let x := f x x; ...; x`. The binary value is shared
    /// across lexical depths in the input, just as imported let-bound circuits
    /// share syntax. Its normal form denotes an exponential tree but is a DAG
    /// with two application nodes per layer.
    fn circuit_lets(depth: usize) -> (WireExpr, WireExpr) {
        let mut nodes = vec![
            ExprNode::Free { name: name("T") },
            ExprNode::Free { name: name("z") },
            ExprNode::Free { name: name("f") },
            ExprNode::Bound { index: 0 },
            ExprNode::Apply {
                function: id(2),
                argument: id(3),
            },
            ExprNode::Apply {
                function: id(4),
                argument: id(3),
            },
        ];
        let mut body = id(3);
        for _ in 0..depth {
            nodes.push(ExprNode::Let {
                declaration_name: name("x"),
                type_: id(0),
                value: id(5),
                body,
                non_dependent: false,
            });
            body = id(nodes.len() - 1);
        }
        nodes.push(ExprNode::Let {
            declaration_name: name("x"),
            type_: id(0),
            value: id(1),
            body,
            non_dependent: false,
        });
        let root = id(nodes.len() - 1);
        let input = WireExpr::from_parts(nodes, vec![], root);
        let mut nodes = vec![
            ExprNode::Free { name: name("z") },
            ExprNode::Free { name: name("f") },
        ];
        let mut root = id(0);
        for _ in 0..depth {
            let partial = id(nodes.len());
            nodes.push(ExprNode::Apply {
                function: id(1),
                argument: root,
            });
            nodes.push(ExprNode::Apply {
                function: partial,
                argument: root,
            });
            root = id(nodes.len() - 1);
        }
        (input, WireExpr::from_parts(nodes, vec![], root))
    }

    #[test]
    fn zeta_reduction_keeps_a_shared_let_circuit_linear() {
        let depth = 48;
        let (input, expected) = circuit_lets(depth);
        let bound = (4 * depth + 16) as u64;
        let budget = WhnfBudget::new(
            10_000,
            (depth + 1) as u64,
            TermBudget::new(bound * 4, bound * 10).with_max_arena_nodes(bound),
        );
        let result = whnf(&input, &WhnfContext::default(), budget);
        let WhnfOutcome::Complete(result) = result else {
            panic!("{result:?}")
        };
        assert_eq!(result.reductions, (depth + 1) as u64);
        assert_eq!(result.term.nodes().len(), 2 * depth + 2);
        assert!(matches!(
            crate::defeq::def_eq(
                &result.term,
                &expected,
                &WhnfContext::default(),
                crate::defeq::DefEqBudget::unlimited(),
            ),
            crate::defeq::DefEqOutcome::Equal(_)
        ));
        // Inspect the actual DAG, not an expanded rendering of its 2^48 leaves.
        let mut root = result.term.root();
        for _ in 0..depth {
            let ExprNode::Apply { function, argument } = result.term.node(root).unwrap() else {
                panic!("lost application")
            };
            let ExprNode::Apply { argument: left, .. } = result.term.node(*function).unwrap()
            else {
                panic!("lost partial application")
            };
            assert_eq!(left, argument);
            root = *argument;
        }
        assert!(
            matches!(result.term.node(root), Some(ExprNode::Free { name: value }) if value == &name("z"))
        );
    }
}
