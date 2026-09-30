//! Eager weak-head reduction over checker-owned flat arenas.
//!
//! This module deliberately does not share the primary kernel normalizer. It
//! implements the eager checker portion of KR-200 through KR-204 with flat arena
//! cursors and explicit heap frames: safe-definition delta, metadata stripping,
//! beta, let-zeta, supplied let-bound free unfolding, and explicit-constructor
//! projection and registered quotient computation (KR-955) — plus recursor reduction: iota (KR-316) with the K-flagged
//! corner (KR-317, `to_cnstr_when_K`). Unsafe and partial definitions stay
//! stuck. Nat literal majors are exposed one constructor layer at a time;
//! string literal majors and native extensions remain outside this layer.

mod memo;
mod quotient;
mod sharing;

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;
use std::sync::Arc;

use memo::WhnfMemo;

/// Work the KR-317 gate's conversion may spend (see
/// `Reducer::k_constructor_types_convert`): comparisons, normalizations, WHNF
/// steps and reductions each, ten times as many arena nodes and a hundred
/// times as many owned units.
const K_GATE_CONVERSION_WORK: u64 = 100_000;

/// Steps and reductions one side's normalization may spend in the KR-317 gate's
/// structural comparison (`Reducer::k_constructor_types_equal`). Running out is
/// a gate miss that falls through to the gate's conversion, never a stop of the
/// reduction that asked: normalizing an open index such as `n - 57344` unfolds
/// `Nat.sub` into 57,344 levels of recursion, where the conversion compares the
/// two sides lazily, as the pin's `is_def_eq` does.
const K_GATE_NORMALIZATION_WORK: u64 = 10 * K_GATE_CONVERSION_WORK;

thread_local! {
    /// Whether a KR-317 gate's conversion is running on this thread. That
    /// conversion reduces through WHNF, which may meet another K recursor; the
    /// inner gate then uses the structural comparison alone, so conversions
    /// never nest inside WHNF on the host stack.
    static K_GATE_CONVERTING: Cell<bool> = const { Cell::new(false) };
}

use crate::environment::{
    ConstantDeclaration, ConstantEnvironment, DefinitionBody, DefinitionSafety, RecursorDeclaration,
};
use crate::instantiate::{
    InstantiationFault, InstantiationOutcome, InstantiationRefusal,
    instantiate_term_parameters_from_level_roots_with,
};
use crate::nat_reduce::{
    NatReductionBudget, NatReductionFault, NatReductionOutcome, NatReductionProgress,
    NatReductionQuery, NatReductionScope, NatReductionStop, is_potential_nat_reduction,
    reduce_nat_at_with,
};
use crate::numeric::NatBudget;
use crate::string_reduce::{
    StringExpansionBudget, StringExpansionFault, StringExpansionOutcome, StringExpansionProgress,
    StringExpansionStop, expand_string_literal_with,
};
use crate::term::{
    TermBudget, TermFault, TermLimit, TermOutcome, TermStop, copy_subterm_with, inspect_with,
    substitute_bound_subterms_with,
};
use crate::universe::{UniverseError, level_roots_equal};
use crate::wire::{
    ExprId, ExprNode, LevelId, LevelNode, NamePart, WireExpr, WireName, expression_owned_units,
    level_owned_units, usize_units,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FreeBinding {
    name: WireName,
    value: Arc<WireExpr>,
}

impl FreeBinding {
    pub fn new(name: WireName, value: WireExpr) -> FreeBinding {
        FreeBinding {
            name,
            value: Arc::new(value),
        }
    }

    pub(crate) fn from_shared(name: WireName, value: Arc<WireExpr>) -> FreeBinding {
        FreeBinding { name, value }
    }

    pub fn name(&self) -> &WireName {
        &self.name
    }

    pub fn value(&self) -> &WireExpr {
        &self.value
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectionRule {
    structure_name: WireName,
    constructor_name: WireName,
    parameter_count: usize,
}

impl ProjectionRule {
    pub fn new(
        structure_name: WireName,
        constructor_name: WireName,
        parameter_count: usize,
    ) -> ProjectionRule {
        ProjectionRule {
            structure_name,
            constructor_name,
            parameter_count,
        }
    }

    pub fn structure_name(&self) -> &WireName {
        &self.structure_name
    }

    pub fn constructor_name(&self) -> &WireName {
        &self.constructor_name
    }

    pub const fn parameter_count(&self) -> usize {
        self.parameter_count
    }
}

#[derive(Clone, Default, PartialEq, Eq)]
pub struct WhnfContext {
    free_bindings: Vec<FreeBinding>,
    projection_rules: Vec<ProjectionRule>,
    constants: ConstantEnvironment,
    /// The safety of the declaration being checked, which decides which
    /// definitions delta may unfold (`ConstantDeclaration::delta_body_in`).
    scope: DefinitionSafety,
    /// Results already computed under this context; see `memo`.
    memo: WhnfMemo,
}

impl fmt::Debug for WhnfContext {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("WhnfContext")
            .field("free_bindings", &self.free_bindings)
            .field("projection_rules", &self.projection_rules)
            .field("constants", &self.constants)
            .field("scope", &self.scope)
            .finish()
    }
}

impl WhnfContext {
    pub fn new(
        free_bindings: Vec<FreeBinding>,
        projection_rules: Vec<ProjectionRule>,
        constants: ConstantEnvironment,
    ) -> WhnfContext {
        WhnfContext {
            free_bindings,
            projection_rules,
            constants,
            scope: DefinitionSafety::Safe,
            memo: WhnfMemo::default(),
        }
    }

    /// This context for checking a declaration of safety `scope`. A different
    /// scope unfolds different definitions, so it starts its own memo.
    pub fn admitting(&self, scope: DefinitionSafety) -> WhnfContext {
        let mut context = self.clone();
        if scope != self.scope {
            context.scope = scope;
            context.memo = WhnfMemo::default();
        }
        context
    }

    pub fn scope(&self) -> DefinitionSafety {
        self.scope
    }

    /// The body delta may unfold for `constant` in this context.
    pub(crate) fn delta_body<'a>(
        &self,
        constant: &'a ConstantDeclaration,
    ) -> Option<&'a DefinitionBody> {
        constant.delta_body_in(self.scope)
    }

    pub fn free_bindings(&self) -> &[FreeBinding] {
        &self.free_bindings
    }

    /// Inference owns the private overlay and checks local-name freshness before
    /// installing a let. The reducer still validates the complete binding set.
    pub(crate) fn push_scoped_binding(&mut self, binding: FreeBinding) {
        self.free_bindings.push(binding);
    }

    /// Lexical scopes must close in reverse installation order. Never remove
    /// another binding, including an original caller-supplied local definition.
    pub(crate) fn pop_scoped_binding(&mut self, name: &WireName) -> bool {
        if self
            .free_bindings
            .last()
            .is_some_and(|binding| binding.name() == name)
        {
            self.free_bindings.pop();
            true
        } else {
            false
        }
    }

    pub fn projection_rules(&self) -> &[ProjectionRule] {
        &self.projection_rules
    }

    pub fn constants(&self) -> &ConstantEnvironment {
        &self.constants
    }

    /// The memo, while no let-bound local is in scope: only then does reduction
    /// read nothing a context can change.
    fn memo(&self) -> Option<&WhnfMemo> {
        self.free_bindings.is_empty().then_some(&self.memo)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WhnfBudget {
    pub max_steps: u64,
    pub max_reductions: u64,
    pub materialization: TermBudget,
    pub string: StringExpansionBudget,
}

impl WhnfBudget {
    pub const fn new(
        max_steps: u64,
        max_reductions: u64,
        materialization: TermBudget,
    ) -> WhnfBudget {
        WhnfBudget {
            max_steps,
            max_reductions,
            materialization,
            string: StringExpansionBudget::new(
                max_steps,
                materialization.max_steps,
                materialization.max_arena_nodes,
                materialization.max_output_units,
            ),
        }
    }

    pub const fn with_string(mut self, string: StringExpansionBudget) -> WhnfBudget {
        self.string = string;
        self
    }

    pub const fn unlimited() -> WhnfBudget {
        WhnfBudget::new(u64::MAX, u64::MAX, TermBudget::unlimited())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WhnfLimit {
    Steps,
    Reductions,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WhnfPhase {
    Initial,
    FreeBinding { index: usize },
    Beta,
    Zeta,
    Iota,
    RebuildApplication,
    RebuildProjection,
    Final,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WhnfRefusal {
    DuplicateFreeBinding {
        first: usize,
        second: usize,
    },
    DuplicateProjectionRule {
        first: usize,
        second: usize,
    },
    FreeBindingCycle {
        binding: usize,
    },
    ProjectionIndexOverflow {
        rule: usize,
        parameter_count: usize,
        field_index: u64,
    },
    DefinitionInstantiation {
        at: usize,
        refusal: InstantiationRefusal,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WhnfStop {
    NatReduction {
        at: usize,
        stop: Box<NatReductionStop>,
        completed_steps: u64,
        completed_reductions: u64,
    },
    Resource {
        limit: WhnfLimit,
        allowed: u64,
        observed: u64,
        at: usize,
        completed_steps: u64,
        completed_reductions: u64,
    },
    Cancelled {
        at: usize,
        polls: u64,
        completed_steps: u64,
        completed_reductions: u64,
    },
    Materialization {
        phase: WhnfPhase,
        stop: TermStop,
        completed_steps: u64,
        completed_reductions: u64,
    },
    DefinitionInstantiation {
        at: usize,
        stop: TermStop,
        completed_steps: u64,
        completed_reductions: u64,
    },
    StringExpansion {
        at: usize,
        stop: StringExpansionStop,
        completed_steps: u64,
        completed_reductions: u64,
    },
}

impl WhnfStop {
    /// The steps and reductions the stopped run had completed.
    pub(crate) const fn completed_work(&self) -> (u64, u64) {
        match self {
            WhnfStop::NatReduction {
                completed_steps,
                completed_reductions,
                ..
            }
            | WhnfStop::Resource {
                completed_steps,
                completed_reductions,
                ..
            }
            | WhnfStop::Cancelled {
                completed_steps,
                completed_reductions,
                ..
            }
            | WhnfStop::Materialization {
                completed_steps,
                completed_reductions,
                ..
            }
            | WhnfStop::DefinitionInstantiation {
                completed_steps,
                completed_reductions,
                ..
            }
            | WhnfStop::StringExpansion {
                completed_steps,
                completed_reductions,
                ..
            } => (*completed_steps, *completed_reductions),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WhnfFault {
    NatReduction {
        at: usize,
        fault: Box<NatReductionFault>,
    },
    Universe {
        at: usize,
        error: UniverseError,
    },
    Term {
        phase: WhnfPhase,
        fault: TermFault,
    },
    MissingLevel {
        input: usize,
        index: usize,
    },
    NonBackwardLevelReference {
        input: usize,
        parent: usize,
        child: usize,
    },
    MissingExpression {
        input: usize,
        index: usize,
    },
    NonBackwardExpressionReference {
        input: usize,
        parent: usize,
        child: usize,
    },
    DefinitionInstantiation {
        at: usize,
        fault: InstantiationFault,
    },
    StringExpansion {
        at: usize,
        fault: StringExpansionFault,
    },
    NonCanonicalNatLiteral {
        at: usize,
    },
    /// The KR-317 gate's conversion faulted (see
    /// `Reducer::k_constructor_types_convert`). A fault is never read as a
    /// gate miss.
    KGateConversion {
        at: usize,
        fault: Box<crate::defeq::DefEqFault>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WhnfResult {
    pub term: WireExpr,
    pub steps: u64,
    pub reductions: u64,
    pub delta_reductions: u64,
    /// Some reductions were spent checking a K gate rather than rewriting the
    /// returned term. A nonzero reduction count alone then need not mean change.
    pub has_auxiliary_work: bool,
    pub string_progress: StringExpansionProgress,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WhnfOutcome {
    Complete(WhnfResult),
    Refused(WhnfRefusal),
    Inconclusive(WhnfStop),
    InternalFault(WhnfFault),
}

enum Halt {
    Refusal(WhnfRefusal),
    // Keep progress-rich stop payloads off the successful reduction stack:
    // every fallible arena operation otherwise reserves their full size.
    Stop(Box<WhnfStop>),
    Fault(WhnfFault),
}

fn outcome(result: Result<WhnfResult, Halt>) -> WhnfOutcome {
    match result {
        Ok(result) => WhnfOutcome::Complete(result),
        Err(Halt::Refusal(refusal)) => WhnfOutcome::Refused(refusal),
        Err(Halt::Stop(stop)) => WhnfOutcome::Inconclusive(*stop),
        Err(Halt::Fault(fault)) => WhnfOutcome::InternalFault(fault),
    }
}

struct Control {
    budget: WhnfBudget,
    steps: u64,
    reductions: u64,
    polls: u64,
}

impl Control {
    fn new(budget: WhnfBudget) -> Control {
        Control {
            budget,
            steps: 0,
            reductions: 0,
            polls: 0,
        }
    }

    fn poll(&mut self, at: usize, cancelled: &mut dyn FnMut() -> bool) -> Result<(), Halt> {
        self.polls = self.polls.saturating_add(1);
        if cancelled() {
            return Err(Halt::Stop(Box::new(WhnfStop::Cancelled {
                at,
                polls: self.polls,
                completed_steps: self.steps,
                completed_reductions: self.reductions,
            })));
        }
        Ok(())
    }

    fn step(&mut self, at: usize, cancelled: &mut dyn FnMut() -> bool) -> Result<(), Halt> {
        self.poll(at, cancelled)?;
        let observed = self.steps.saturating_add(1);
        if observed > self.budget.max_steps {
            return Err(Halt::Stop(Box::new(WhnfStop::Resource {
                limit: WhnfLimit::Steps,
                allowed: self.budget.max_steps,
                observed,
                at,
                completed_steps: self.steps,
                completed_reductions: self.reductions,
            })));
        }
        self.steps = observed;
        Ok(())
    }

    fn reduction(&mut self, at: usize, cancelled: &mut dyn FnMut() -> bool) -> Result<(), Halt> {
        self.poll(at, cancelled)?;
        let observed = self.reductions.saturating_add(1);
        if observed > self.budget.max_reductions {
            return Err(Halt::Stop(Box::new(WhnfStop::Resource {
                limit: WhnfLimit::Reductions,
                allowed: self.budget.max_reductions,
                observed,
                at,
                completed_steps: self.steps,
                completed_reductions: self.reductions,
            })));
        }
        self.reductions = observed;
        Ok(())
    }

    fn term_halt<T>(&self, phase: WhnfPhase, outcome: TermOutcome<T>) -> Result<T, Halt> {
        match outcome {
            TermOutcome::Complete(value) => Ok(value),
            TermOutcome::Inconclusive(stop) => {
                Err(Halt::Stop(Box::new(WhnfStop::Materialization {
                    phase,
                    stop,
                    completed_steps: self.steps,
                    completed_reductions: self.reductions,
                })))
            }
            TermOutcome::InternalFault(fault) => Err(Halt::Fault(WhnfFault::Term { phase, fault })),
        }
    }
}

struct PreparedContext<'a> {
    source: &'a WhnfContext,
    free_bindings: BTreeMap<&'a WireName, usize>,
    projection_rules: BTreeMap<&'a WireName, usize>,
}

impl<'a> PreparedContext<'a> {
    fn prepare(
        source: &'a WhnfContext,
        control: &mut Control,
        cancelled: &mut dyn FnMut() -> bool,
    ) -> Result<PreparedContext<'a>, Halt> {
        let mut free_bindings = BTreeMap::new();
        for (index, binding) in source.free_bindings.iter().enumerate() {
            control.step(index, cancelled)?;
            if let Some(first) = free_bindings.insert(&binding.name, index) {
                return Err(Halt::Refusal(WhnfRefusal::DuplicateFreeBinding {
                    first,
                    second: index,
                }));
            }
        }

        let mut projection_rules = BTreeMap::new();
        for (index, rule) in source.projection_rules.iter().enumerate() {
            control.step(index, cancelled)?;
            if let Some(first) = projection_rules.insert(&rule.structure_name, index) {
                return Err(Halt::Refusal(WhnfRefusal::DuplicateProjectionRule {
                    first,
                    second: index,
                }));
            }
        }

        Ok(PreparedContext {
            source,
            free_bindings,
            projection_rules,
        })
    }
}

/// A term under reduction: `root` in `arena`, whose loose bound variables
/// `0..env.len()` stand for the environment's values, innermost first; a loose
/// index at or past `env.len()` is the run's own loose variable `index -
/// env.len()`. Beta and zeta extend the environment instead of rewriting the
/// body, so a step costs what it changes, not the size of the term. A term is
/// rebuilt only where it leaves the reducer (`Composer::copy_cursor`).
///
/// Cursors are made resolved (`Cursor::resolved`): a root is never a bound
/// variable its own environment binds, so reading the root node is enough to
/// classify the term.
///
/// A cursor that is an argument or a bound value may carry a `Thunk`, shared by
/// every copy of it: the first eager evaluation records its weak head normal
/// form there and every later one resumes from it, as the pin's whnf cache
/// shares the result for a term that `instantiate` shared by pointer. Only the
/// evaluation reads it: a term is always rebuilt as written.
#[derive(Clone)]
struct Cursor {
    arena: Arc<WireExpr>,
    root: ExprId,
    env: Env,
    thunk: Option<Arc<Thunk>>,
}

impl Cursor {
    /// A term with no environment: every loose index is the run's own.
    fn closed(arena: Arc<WireExpr>, root: ExprId) -> Cursor {
        Cursor {
            arena,
            root,
            env: Env::default(),
            thunk: None,
        }
    }

    /// `root` in `arena` under `env`, with a root bound by `env` replaced by its
    /// value. Values are stored resolved, so one lookup suffices.
    fn resolved(arena: Arc<WireExpr>, root: ExprId, env: Env) -> Cursor {
        if let Some(ExprNode::Bound { index }) = arena.node(root)
            && let Some(value) = env.get(*index)
        {
            return value.clone();
        }
        Cursor {
            arena,
            root,
            env,
            thunk: None,
        }
    }

    /// A subterm of this cursor's term, in the same environment.
    fn child(&self, root: ExprId) -> Cursor {
        Cursor::resolved(Arc::clone(&self.arena), root, self.env.clone())
    }

    /// This cursor, sharing one evaluation among its copies when it is a
    /// computation rather than already a head form.
    fn shared(mut self) -> Cursor {
        if self.thunk.is_none()
            && matches!(
                self.arena.node(self.root),
                Some(
                    ExprNode::Apply { .. }
                        | ExprNode::Let { .. }
                        | ExprNode::Projection { .. }
                        | ExprNode::Metadata { .. }
                        | ExprNode::Constant { .. }
                )
            )
        {
            self.thunk = Some(Arc::new(Thunk::default()));
        }
        self
    }
}

/// A term by pointer structure: a node of an arena, with the identity of each
/// environment value its loose indices refer to. Two cursors with one key denote
/// the same term, so they share one evaluation.
#[derive(Clone, PartialEq, Eq, Hash)]
struct WhnfKey {
    arena: usize,
    node: usize,
    values: Vec<ValueIdentity>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum ValueIdentity {
    /// A shared value: its thunk.
    Thunk(usize),
    /// A value with no environment: its node.
    Closed(usize, usize),
}

/// A canonical spelling of universe values: equal levels spell the same.
/// `None` for a spelling too long to be worth a cache key.
fn level_key(nodes: &[LevelNode], roots: &[LevelId]) -> Option<String> {
    let mut key = String::new();
    for root in roots {
        let mut pending = vec![*root];
        while let Some(id) = pending.pop() {
            if key.len() > 1024 {
                return None;
            }
            match nodes.get(id.index())? {
                LevelNode::Zero => key.push('Z'),
                LevelNode::Succ(child) => {
                    key.push('S');
                    pending.push(*child);
                }
                LevelNode::Max(left, right) => {
                    key.push('M');
                    pending.push(*right);
                    pending.push(*left);
                }
                LevelNode::IMax(left, right) => {
                    key.push('I');
                    pending.push(*right);
                    pending.push(*left);
                }
                node @ (LevelNode::Parameter(name) | LevelNode::Meta(name)) => {
                    key.push(if matches!(node, LevelNode::Meta(_)) {
                        '?'
                    } else {
                        'P'
                    });
                    for part in name.parts() {
                        match part {
                            NamePart::Text(text) => {
                                key.push('"');
                                key.push_str(&text.len().to_string());
                                key.push(':');
                                key.push_str(text);
                            }
                            NamePart::Numeric { .. } => key.push_str(&format!("#{part:?}")),
                        }
                    }
                    key.push(';');
                }
            }
        }
        key.push('|');
    }
    Some(key)
}

/// The weak head normal form of a shared cursor, once evaluated eagerly.
#[derive(Default)]
struct Thunk {
    result: std::sync::OnceLock<Spine>,
}

impl Drop for Thunk {
    fn drop(&mut self) {
        if let Some(spine) = self.result.take() {
            let mut cells = Vec::new();
            let mut thunks = Vec::new();
            spine.release_into(&mut cells, &mut thunks);
            release(cells, thunks);
        }
    }
}

/// An application kept unbuilt: `head` applied to `args`. Reduction results
/// stay spines until something needs one term, so a constructor's fields are
/// never copied just to be taken apart again by the recursor that demanded it.
#[derive(Clone)]
struct Spine {
    head: Cursor,
    args: VecDeque<Cursor>,
}

impl Spine {
    /// Hand this spine's environments and thunks to an iterative release.
    fn release_into(self, cells: &mut Vec<Arc<EnvCell>>, thunks: &mut Vec<Arc<Thunk>>) {
        for mut cursor in std::iter::once(self.head).chain(self.args) {
            cells.extend(cursor.env.0.take());
            thunks.extend(cursor.thunk.take());
        }
    }
}

/// Release environments and thunks on a heap stack: they nest through each
/// other as deeply as a computation ran, too deep for the recursive default
/// drop.
fn release(mut cells: Vec<Arc<EnvCell>>, mut thunks: Vec<Arc<Thunk>>) {
    loop {
        if let Some(cell) = cells.pop() {
            if let Some(mut cell) = Arc::into_inner(cell) {
                cells.extend(cell.next.0.take());
                cells.extend(cell.value.env.0.take());
                thunks.extend(cell.value.thunk.take());
            }
        } else if let Some(thunk) = thunks.pop() {
            if let Some(mut thunk) = Arc::into_inner(thunk)
                && let Some(spine) = thunk.result.take()
            {
                spine.release_into(&mut cells, &mut thunks);
            }
        } else {
            return;
        }
    }
}

/// A persistent list of the values bound around a cursor's term.
#[derive(Clone, Default)]
struct Env(Option<Arc<EnvCell>>);

struct EnvCell {
    value: Cursor,
    next: Env,
    len: u32,
}

impl Env {
    fn len(&self) -> u32 {
        self.0.as_ref().map_or(0, |cell| cell.len)
    }

    fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    /// This environment with `value` bound as index 0.
    fn push(&self, value: Cursor) -> Env {
        Env(Some(Arc::new(EnvCell {
            value,
            next: self.clone(),
            len: self.len().saturating_add(1),
        })))
    }

    fn get(&self, index: u32) -> Option<&Cursor> {
        let mut cell = self.0.as_deref()?;
        for _ in 0..index {
            cell = cell.next.0.as_deref()?;
        }
        Some(&cell.value)
    }

    /// An identity for memo keys, valid while this environment is alive.
    fn identity(&self) -> usize {
        self.0.as_ref().map_or(0, |cell| Arc::as_ptr(cell).addr())
    }
}

impl Drop for Env {
    fn drop(&mut self) {
        release(self.0.take().into_iter().collect(), Vec::new());
    }
}

enum ReductionFrame {
    Projection(ProjectionFrame),
    Quotient(quotient::QuotientFrame),
    Recursor(Box<RecursorFrame>),
    Nat(Box<NatFrame>),
    /// Record a shared cursor's weak head normal form. It was evaluated with no
    /// pending arguments, so the result is the whole term.
    Update {
        thunk: Arc<Thunk>,
        /// The evaluation registered under the same key, if another one.
        keyed: Option<Arc<Thunk>>,
    },
}

/// KR-313 at a WHNF head, evaluated in this loop: each operand is normalized
/// here in turn, as the pin's `reduce_nat` calls `whnf` on it, and the
/// operation computes once all are naturals. An operand that is not a natural
/// declines the operation, which then unfolds (`skip_nat`).
struct NatFrame {
    operation: crate::nat_reduce::NatReductionOperation,
    head: Cursor,
    /// Every argument the operation was applied to; the first `arity` are its
    /// operands.
    arguments: VecDeque<Cursor>,
    values: Vec<crate::numeric::NatValue>,
    delta_mode: DeltaMode,
    unfolded_bindings: BTreeSet<usize>,
    force_string_delta: bool,
}

/// Per-node facts of one arena, each computed at most once per run and only for
/// the subterms a check reaches: the loose bound-variable range, the loose
/// indices below 64 as a mask, and whether a free variable occurs.
struct ArenaFacts {
    arena: Arc<WireExpr>,
    known: Vec<bool>,
    loose: Vec<u32>,
    mask: Vec<u64>,
    free: Vec<bool>,
}

impl ArenaFacts {
    fn new(arena: Arc<WireExpr>) -> ArenaFacts {
        let len = arena.nodes().len();
        ArenaFacts {
            arena,
            known: vec![false; len],
            loose: vec![0; len],
            mask: vec![0; len],
            free: vec![false; len],
        }
    }

    /// The facts of `root`, computing those of its subterms not yet known; each
    /// node computed is one step.
    fn at(
        &mut self,
        root: ExprId,
        control: &mut Control,
        cancelled: &mut dyn FnMut() -> bool,
    ) -> Result<(u32, u64, bool), Halt> {
        let missing = |index| Halt::Fault(WhnfFault::MissingExpression { input: 0, index });
        let mut work = vec![(root.index(), false)];
        while let Some((index, built)) = work.pop() {
            if *self.known.get(index).ok_or_else(|| missing(index))? {
                continue;
            }
            let node = self
                .arena
                .nodes()
                .get(index)
                .ok_or_else(|| missing(index))?;
            let children = expression_children(node);
            if !built {
                control.step(index, cancelled)?;
                work.push((index, true));
                for (child, _) in children.into_iter().flatten() {
                    if child.index() >= index {
                        return Err(Halt::Fault(WhnfFault::NonBackwardExpressionReference {
                            input: 0,
                            parent: index,
                            child: child.index(),
                        }));
                    }
                    work.push((child.index(), false));
                }
                continue;
            }
            let (mut loose, mut mask, mut free) = match node {
                ExprNode::Bound { index } => (
                    index.saturating_add(1),
                    1u64.checked_shl(*index).unwrap_or(0),
                    false,
                ),
                ExprNode::Free { .. } => (0, 0, true),
                _ => (0, 0, false),
            };
            for (child, binders) in children.into_iter().flatten() {
                let child = child.index();
                loose = loose.max(self.loose[child].saturating_sub(binders));
                mask |= self.mask[child].checked_shr(binders).unwrap_or(0);
                free |= self.free[child];
            }
            self.loose[index] = loose;
            self.mask[index] = mask;
            self.free[index] = free;
            self.known[index] = true;
        }
        let index = root.index();
        Ok((self.loose[index], self.mask[index], self.free[index]))
    }
}

struct RecursorFrame {
    head: Cursor,
    metadata: RecursorDeclaration,
    level_parameters: Vec<WireName>,
    recursor_type: WireExpr,
    levels: Vec<LevelId>,
    arguments: VecDeque<Cursor>,
    major_index: usize,
    parameter_count: usize,
    prefix: usize,
    delta_mode: DeltaMode,
    unfolded_bindings: BTreeSet<usize>,
    force_string_delta: bool,
    progress: ProgressMark,
}

enum RecursorStep {
    Reduced(Spine),
    NormalizeMajor {
        frame: Box<RecursorFrame>,
        major: Cursor,
    },
}

struct ProjectionFrame {
    projection: Cursor,
    outer_arguments: VecDeque<Cursor>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum DeltaMode {
    Eager,
    Disabled,
    Once,
}

enum HeadAction {
    Metadata(ExprId),
    Let { value: ExprId, body: ExprId },
    Free(Option<usize>),
    Constant,
    Apply,
    Projection { expression: ExprId },
    Stuck,
}

struct Reducer<'a, 'c> {
    context: PreparedContext<'a>,
    control: Control,
    cancelled: &'c mut dyn FnMut() -> bool,
    unfolded_bindings: BTreeSet<usize>,
    delta_mode: DeltaMode,
    /// Which open operands a Nat operation at the head may normalize.
    head_nat: NatReductionScope,
    delta_reductions: u64,
    /// Reductions spent normalizing the major of a recursor that then stayed
    /// stuck. Its application is returned with the major it had, so this work
    /// changed nothing in the result and is not reported as progress. The
    /// budget still counts it.
    discarded_reductions: u64,
    discarded_delta_reductions: u64,
    has_auxiliary_work: bool,
    string_progress: StringExpansionProgress,
    force_string_delta: bool,
    /// A Nat operation at the head just declined: unfold it this once instead
    /// of offering it again.
    skip_nat: bool,
    /// `ArenaFacts` by arena address; each entry holds its arena.
    facts: std::collections::HashMap<usize, ArenaFacts>,
    /// Each String literal's shared expansion (`expand_string`).
    string_expansions: std::collections::HashMap<String, Cursor>,
    /// Instantiated definition bodies and recursor rules by subject address and
    /// universe values (`Reducer::instantiated`).
    bodies: std::collections::HashMap<(usize, String), Arc<WireExpr>>,
    /// Shared evaluations by pointer structure (`Reducer::keyed`). Each entry
    /// holds the cursor its key was taken from, which keeps every address in the
    /// key alive, so an address can never be reused for another term while it
    /// is a key.
    keyed_thunks: std::collections::HashMap<WhnfKey, (Cursor, Arc<Thunk>)>,
}

/// The reported-progress counters when a recursor frame starts normalizing
/// its major.
#[derive(Clone, Copy)]
struct ProgressMark {
    reductions: u64,
    delta_reductions: u64,
    discarded_reductions: u64,
    discarded_delta_reductions: u64,
}

impl<'a, 'c> Reducer<'a, 'c> {
    fn node<'t>(&self, cursor: &'t Cursor) -> Result<&'t ExprNode, Halt> {
        cursor
            .arena
            .node(cursor.root)
            .ok_or(Halt::Fault(WhnfFault::MissingExpression {
                input: 0,
                index: cursor.root.index(),
            }))
    }

    fn validate_child(parent: ExprId, child: ExprId) -> Result<(), Halt> {
        if child.index() >= parent.index() {
            return Err(Halt::Fault(WhnfFault::NonBackwardExpressionReference {
                input: 0,
                parent: parent.index(),
                child: child.index(),
            }));
        }
        Ok(())
    }

    fn remaining_string_budget(&self) -> StringExpansionBudget {
        let mut budget = self.control.budget.string;
        budget.max_steps = budget.max_steps.saturating_sub(self.string_progress.steps);
        budget.max_code_points = budget
            .max_code_points
            .saturating_sub(self.string_progress.code_points);
        budget.max_arena_nodes = budget
            .max_arena_nodes
            .saturating_sub(self.string_progress.arena_nodes);
        budget.max_owned_units = budget
            .max_owned_units
            .saturating_sub(self.string_progress.owned_units);
        budget
    }

    fn absorb_string(&mut self, progress: StringExpansionProgress) {
        self.string_progress.steps = self.string_progress.steps.saturating_add(progress.steps);
        self.string_progress.code_points = self
            .string_progress
            .code_points
            .saturating_add(progress.code_points);
        self.string_progress.generated_arenas = self
            .string_progress
            .generated_arenas
            .saturating_add(progress.generated_arenas);
        self.string_progress.arena_nodes = self
            .string_progress
            .arena_nodes
            .saturating_add(progress.arena_nodes);
        self.string_progress.owned_units = self
            .string_progress
            .owned_units
            .saturating_add(progress.owned_units);
    }

    /// The constructor form of a String literal. One shared expansion per
    /// literal and run: every projection of the literal then reads the same
    /// evaluated fields, where the pin's whnf cache finds the structurally equal
    /// expansion.
    fn expand_string(&mut self, value: &str, at: usize) -> Result<Cursor, Halt> {
        if let Some(expanded) = self.string_expansions.get(value) {
            return Ok(expanded.clone());
        }
        let budget = self.remaining_string_budget();
        match expand_string_literal_with(value, budget, &mut self.cancelled) {
            StringExpansionOutcome::Expanded(result) => {
                self.absorb_string(result.progress);
                let root = result.term.root();
                let expanded = Cursor::closed(Arc::new(result.term), root).shared();
                self.string_expansions
                    .insert(value.to_owned(), expanded.clone());
                Ok(expanded)
            }
            StringExpansionOutcome::Inconclusive(stop) => {
                self.absorb_string(stop.progress());
                Err(Halt::Stop(Box::new(WhnfStop::StringExpansion {
                    at,
                    stop,
                    completed_steps: self.control.steps,
                    completed_reductions: self.control.reductions,
                })))
            }
            StringExpansionOutcome::InternalFault { fault, progress } => {
                self.absorb_string(progress);
                Err(Halt::Fault(WhnfFault::StringExpansion { at, fault }))
            }
        }
    }

    fn projection_requests_string(&self, frame: &ProjectionFrame) -> Result<bool, Halt> {
        let ExprNode::Projection { structure_name, .. } = self.node(&frame.projection)? else {
            return Err(Halt::Fault(WhnfFault::MissingExpression {
                input: 0,
                index: frame.projection.root.index(),
            }));
        };
        Ok(matches!(
            structure_name.parts(),
            [NamePart::Text(name)] if name == "String"
        ))
    }

    fn materialize_wire(
        &mut self,
        term: &WireExpr,
        root: ExprId,
        phase: WhnfPhase,
    ) -> Result<WireExpr, Halt> {
        self.control.step(root.index(), self.cancelled)?;
        let result = copy_subterm_with(
            term,
            root,
            self.control.budget.materialization,
            self.cancelled,
        );
        self.control.term_halt(phase, result)
    }

    fn materialize_term(
        &mut self,
        term: &WireExpr,
        root: ExprId,
        phase: WhnfPhase,
    ) -> Result<Cursor, Halt> {
        let term = self.materialize_wire(term, root, phase)?;
        let root = term.root();
        Ok(Cursor::closed(Arc::new(term), root))
    }

    /// The head and arguments of an application spine. A function position
    /// bound by the environment continues the spine in its value, which may
    /// live in another arena.
    fn peel_application(&mut self, cursor: &Cursor) -> Result<(Cursor, VecDeque<Cursor>), Halt> {
        let mut head = cursor.clone();
        let mut arguments = VecDeque::new();
        loop {
            self.control.step(head.root.index(), self.cancelled)?;
            let node =
                head.arena
                    .node(head.root)
                    .ok_or(Halt::Fault(WhnfFault::MissingExpression {
                        input: 0,
                        index: head.root.index(),
                    }))?;
            let ExprNode::Apply { function, argument } = node else {
                break;
            };
            Self::validate_child(head.root, *function)?;
            Self::validate_child(head.root, *argument)?;
            arguments.push_front(head.child(*argument).shared());
            head = head.child(*function);
        }
        Ok((head, arguments))
    }

    fn compose_application<'b, I>(
        &mut self,
        function: &Cursor,
        arguments: I,
    ) -> Result<Cursor, Halt>
    where
        I: IntoIterator<Item = &'b Cursor>,
    {
        self.control.step(function.root.index(), self.cancelled)?;
        let mut composer = Composer::new(
            self.control.budget.materialization,
            WhnfPhase::RebuildApplication,
            self.control.steps,
            self.control.reductions,
            self.cancelled,
        );
        let mut root = composer.copy_cursor(function, 0)?;
        for (index, argument) in arguments.into_iter().enumerate() {
            let argument = composer.copy_cursor(argument, index.saturating_add(1))?;
            root = composer.push_expression(
                ExprNode::Apply {
                    function: root,
                    argument,
                },
                1,
                index,
            )?;
        }
        Ok(composer.finish_cursor(root))
    }

    fn compose_projection(
        &mut self,
        projection: &Cursor,
        expression: &Cursor,
    ) -> Result<Cursor, Halt> {
        self.control.step(projection.root.index(), self.cancelled)?;
        let projection_node = self.node(projection)?;
        let ExprNode::Projection {
            structure_name,
            index,
            ..
        } = projection_node
        else {
            return Err(Halt::Fault(WhnfFault::MissingExpression {
                input: 0,
                index: projection.root.index(),
            }));
        };
        let units = expression_owned_units(projection_node);
        let mut composer = Composer::new(
            self.control.budget.materialization,
            WhnfPhase::RebuildProjection,
            self.control.steps,
            self.control.reductions,
            self.cancelled,
        );
        let expression = composer.copy_cursor(expression, 0)?;
        composer
            .control
            .output(units, projection.root.index())
            .map_err(|halt| composer.map_halt(halt))?;
        let root = composer.push_expression(
            ExprNode::Projection {
                structure_name: structure_name.clone(),
                index: *index,
                expression,
            },
            0,
            projection.root.index(),
        )?;
        Ok(composer.finish_cursor(root))
    }

    fn projection_field(
        &mut self,
        frame: &ProjectionFrame,
        scrutinee: &Spine,
    ) -> Result<Option<Cursor>, Halt> {
        let (rule, rule_index, field_index) = {
            let node = self.node(&frame.projection)?;
            let ExprNode::Projection {
                structure_name,
                index,
                ..
            } = node
            else {
                return Err(Halt::Fault(WhnfFault::MissingExpression {
                    input: 0,
                    index: frame.projection.root.index(),
                }));
            };
            // The caller's registry stays the untrusted-input surface; on a
            // miss, KR-112's condition is derivable from the environment for
            // a single-constructor inductive (`derive_projection_rule`).
            let (rule, rule_index) =
                match self.context.projection_rules.get(structure_name).copied() {
                    Some(rule_index) => {
                        let rule = self.context.source.projection_rules.get(rule_index).ok_or(
                            Halt::Fault(WhnfFault::MissingExpression {
                                input: 0,
                                index: rule_index,
                            }),
                        )?;
                        (rule.clone(), rule_index)
                    }
                    None => {
                        let Some(rule) =
                            derive_projection_rule(self.context.source.constants(), structure_name)
                        else {
                            return Ok(None);
                        };
                        // No registry row exists for a derived rule; the overflow
                        // refusal's row field reports usize::MAX there.
                        (rule, usize::MAX)
                    }
                };
            (rule, rule_index, *index)
        };

        let arguments = &scrutinee.args;
        let constructor_matches = matches!(
            self.node(&scrutinee.head)?,
            ExprNode::Constant { name, .. } if name == &rule.constructor_name
        );
        if !constructor_matches {
            return Ok(None);
        }

        let field = usize::try_from(field_index).map_err(|_| {
            Halt::Refusal(WhnfRefusal::ProjectionIndexOverflow {
                rule: rule_index,
                parameter_count: rule.parameter_count,
                field_index,
            })
        })?;
        let target = rule.parameter_count.checked_add(field).ok_or({
            Halt::Refusal(WhnfRefusal::ProjectionIndexOverflow {
                rule: rule_index,
                parameter_count: rule.parameter_count,
                field_index,
            })
        })?;
        Ok(arguments.get(target).cloned())
    }

    fn unfold_definition(&mut self, current: &Cursor) -> Result<Option<Cursor>, Halt> {
        let (name, levels) = match self.node(current)? {
            ExprNode::Constant { name, levels } => (name, levels),
            _ => {
                return Err(Halt::Fault(WhnfFault::MissingExpression {
                    input: 0,
                    index: current.root.index(),
                }));
            }
        };
        let Some(constant) = self.context.source.constants().find(name) else {
            return Ok(None);
        };
        let Some(definition) = self.context.source.delta_body(constant) else {
            return Ok(None);
        };
        if constant.level_parameters().len() != levels.len() {
            return Err(Halt::Refusal(WhnfRefusal::DefinitionInstantiation {
                at: current.root.index(),
                refusal: InstantiationRefusal::ArityMismatch {
                    parameters: constant.level_parameters().len(),
                    values: levels.len(),
                },
            }));
        }

        self.control
            .reduction(current.root.index(), self.cancelled)?;
        let body = self.instantiated(
            definition.value(),
            constant.level_parameters(),
            &current.arena,
            levels,
            current.root.index(),
            true,
        )?;
        let root = body.root();
        Ok(Some(Cursor::closed(body, root)))
    }

    /// `subject`, an environment-owned term, with its universe `parameters`
    /// instantiated to the level roots `levels` of `source`. One arena per
    /// subject and universe values in a run: a definition unfolded again
    /// yields the same arena, so the shared-evaluation keys (`Reducer::keyed`)
    /// recognize its subterms. Only a `cacheable` subject is shared: one the
    /// environment owns, which outlives the run, so its address stays its own.
    fn instantiated(
        &mut self,
        subject: &WireExpr,
        parameters: &[WireName],
        source: &WireExpr,
        levels: &[LevelId],
        at: usize,
        cacheable: bool,
    ) -> Result<Arc<WireExpr>, Halt> {
        let key = level_key(source.levels(), levels)
            .filter(|_| cacheable)
            .map(|spelled| (std::ptr::from_ref(subject).addr(), spelled));
        if let Some(key) = &key
            && let Some(term) = self.bodies.get(key)
        {
            return Ok(Arc::clone(term));
        }
        match instantiate_term_parameters_from_level_roots_with(
            subject,
            parameters,
            source.levels(),
            levels,
            self.control.budget.materialization,
            &mut *self.cancelled,
        ) {
            InstantiationOutcome::Complete(term) => {
                let term = Arc::new(term);
                if let Some(key) = key {
                    if self.bodies.len() >= 1 << 16 {
                        self.bodies.clear();
                    }
                    self.bodies.insert(key, Arc::clone(&term));
                }
                Ok(term)
            }
            InstantiationOutcome::Refused(refusal) => {
                Err(Halt::Refusal(WhnfRefusal::DefinitionInstantiation {
                    at,
                    refusal,
                }))
            }
            InstantiationOutcome::Inconclusive(stop) => {
                Err(Halt::Stop(Box::new(WhnfStop::DefinitionInstantiation {
                    at,
                    stop,
                    completed_steps: self.control.steps,
                    completed_reductions: self.control.reductions,
                })))
            }
            InstantiationOutcome::InternalFault(fault) => {
                Err(Halt::Fault(WhnfFault::DefinitionInstantiation {
                    at,
                    fault,
                }))
            }
        }
    }

    /// The shared evaluation for `cursor`'s key (`WhnfKey`), about to evaluate
    /// with `thunk`: a whnf cache by pointer structure, as the pin's whnf cache
    /// finds a term that `instantiate` shared by pointer. A new key registers
    /// `thunk`. `None` when an environment value the term refers to cannot be
    /// identified. Keys are taken only for terms being evaluated, so a spine's
    /// arguments that never are cost nothing here.
    fn keyed_thunk(
        &mut self,
        cursor: &Cursor,
        thunk: &Arc<Thunk>,
    ) -> Result<Option<Arc<Thunk>>, Halt> {
        let (loose, mask, _) = self.fact(&cursor.arena, cursor.root)?;
        let mut values = Vec::new();
        for slot in 0..loose {
            if slot < 64 && mask & (1 << slot) == 0 {
                continue;
            }
            let Some(value) = cursor.env.get(slot) else {
                return Ok(None);
            };
            values.push(match &value.thunk {
                Some(thunk) => ValueIdentity::Thunk(Arc::as_ptr(thunk).addr()),
                None if value.env.is_empty() => {
                    ValueIdentity::Closed(Arc::as_ptr(&value.arena).addr(), value.root.index())
                }
                None => return Ok(None),
            });
        }
        let key = WhnfKey {
            arena: Arc::as_ptr(&cursor.arena).addr(),
            node: cursor.root.index(),
            values,
        };
        if let Some((_, existing)) = self.keyed_thunks.get(&key) {
            return Ok(Some(Arc::clone(existing)));
        }
        if self.keyed_thunks.len() >= 1 << 20 {
            self.keyed_thunks.clear();
        }
        self.keyed_thunks
            .insert(key, (cursor.clone(), Arc::clone(thunk)));
        Ok(Some(Arc::clone(thunk)))
    }

    /// Whether the major premise already reduces to a constructor
    /// application — the shape the pin converts before the K corner
    /// (`inductive.h:91-95`), which the ordinary fire path owns. Literal
    /// majors are NOT constructor applications here: Nat/String
    /// literal-to-constructor conversion is outside this layer for now.
    fn major_is_constructor_application(&mut self, major: &Cursor) -> Result<bool, Halt> {
        let (head, _) = self.peel_application(major)?;
        match self.node(&head)? {
            ExprNode::Constant { name, .. } => {
                let name = name.clone();
                Ok(self
                    .context
                    .source
                    .constants()
                    .find(&name)
                    .is_some_and(|entry| entry.constructor_metadata().is_some()))
            }
            _ => Ok(false),
        }
    }

    /// Normalize one side of the KR-317 gate's structural comparison, including
    /// its definitions even when outer conversion delays delta reduction.
    /// Absorb the sub-run's work into the remaining budget. `None` when it runs
    /// out of `K_GATE_NORMALIZATION_WORK`: the caller takes that as a gate miss,
    /// and a cancellation still stops this reduction.
    fn whnf_recursor_major(&mut self, cursor: &Cursor) -> Result<Option<Cursor>, Halt> {
        if !cursor.env.is_empty() {
            let term = self.close(cursor, WhnfPhase::Iota)?;
            let root = term.root();
            return self.whnf_recursor_major(&Cursor::closed(Arc::new(term), root));
        }
        let context = self.context.source;
        let budget = WhnfBudget::new(
            self.control
                .budget
                .max_steps
                .saturating_sub(self.control.steps)
                .min(K_GATE_NORMALIZATION_WORK),
            self.control
                .budget
                .max_reductions
                .saturating_sub(self.control.reductions)
                .min(K_GATE_NORMALIZATION_WORK),
            self.control.budget.materialization,
        )
        .with_string(self.remaining_string_budget());
        // Its caller compares the result, as the pin's `to_cnstr_when_K`
        // compares types with `is_def_eq`: see `whnf_comparand_with`.
        match whnf_at_mode_with(
            &cursor.arena,
            cursor.root,
            context,
            budget,
            DeltaMode::Eager,
            NatReductionScope::ClosedPair,
            &mut *self.cancelled,
        ) {
            WhnfOutcome::Complete(result) => {
                self.control.steps = self.control.steps.saturating_add(result.steps);
                self.control.reductions = self.control.reductions.saturating_add(result.reductions);
                self.delta_reductions = self
                    .delta_reductions
                    .saturating_add(result.delta_reductions);
                self.has_auxiliary_work |= result.has_auxiliary_work;
                self.absorb_string(result.string_progress);
                self.reduce_demanded_nat(result.term).map(Some)
            }
            WhnfOutcome::Refused(refusal) => Err(Halt::Refusal(refusal)),
            WhnfOutcome::Inconclusive(stop @ WhnfStop::Cancelled { .. }) => {
                Err(Halt::Stop(Box::new(stop)))
            }
            WhnfOutcome::Inconclusive(stop) => {
                // The work is spent all the same; charging it here stops this
                // reduction when its own budget, not the gate's, ran out.
                let (steps, reductions) = stop.completed_work();
                self.control.steps = self.control.steps.saturating_add(steps);
                self.control.reductions = self.control.reductions.saturating_add(reductions);
                self.control.step(cursor.root.index(), self.cancelled)?;
                self.has_auxiliary_work = true;
                Ok(None)
            }
            WhnfOutcome::InternalFault(fault) => Err(Halt::Fault(fault)),
        }
    }

    /// KR-313 must also execute when a recursor demands a major such as
    /// Nat.beq (Nat.add 2 3) 5. Reuse the checker-owned arithmetic evaluator,
    /// never the primary kernel or an unchecked host Boolean decision. Ordinary
    /// core WHNF stays unchanged: this is the explicitly demanded-major lane.
    fn reduce_demanded_nat(&mut self, term: WireExpr) -> Result<Cursor, Halt> {
        let at = term.root().index();
        if !is_potential_nat_reduction(&term, term.root()) {
            let root = term.root();
            return Ok(Cursor::closed(Arc::new(term), root));
        }
        let steps = self
            .control
            .budget
            .max_steps
            .saturating_sub(self.control.steps);
        let reductions = self
            .control
            .budget
            .max_reductions
            .saturating_sub(self.control.reductions);
        let materialization = self.control.budget.materialization;
        let budget = NatReductionBudget::new(
            steps,
            steps,
            reductions,
            materialization.max_arena_nodes,
            materialization.max_output_units,
            materialization.max_output_units,
            WhnfBudget::new(steps, reductions, materialization)
                .with_string(self.remaining_string_budget()),
            NatBudget::new(steps, materialization.max_output_units),
        );
        let result = reduce_nat_at_with(
            NatReductionQuery::new(&term, term.root(), &term, term.root(), self.context.source),
            budget,
            NatReductionScope::DemandedMajor,
            &mut *self.cancelled,
        );
        match result {
            NatReductionOutcome::Reduced(result) => {
                self.absorb_demanded_nat(result.progress, at)?;
                let root = result.term.root();
                Ok(Cursor::closed(Arc::new(result.term), root))
            }
            NatReductionOutcome::NotReduced { progress, .. } => {
                // Work in a failed arithmetic demand is not a changed outer term.
                self.has_auxiliary_work = true;
                self.absorb_demanded_nat(progress, at)?;
                let root = term.root();
                Ok(Cursor::closed(Arc::new(term), root))
            }
            NatReductionOutcome::Refused {
                refusal: crate::nat_reduce::NatReductionRefusal::Whnf { refusal, .. },
                progress,
            } => {
                self.absorb_demanded_nat(progress, at)?;
                Err(Halt::Refusal(refusal))
            }
            NatReductionOutcome::Inconclusive(stop) => {
                // Preserve the complete nested reason, including cancellation.
                let progress = stop.progress();
                self.control.steps = self
                    .control
                    .steps
                    .saturating_add(progress.steps)
                    .saturating_add(progress.whnf_steps)
                    .saturating_add(progress.numeric_steps);
                self.control.reductions = self
                    .control
                    .reductions
                    .saturating_add(progress.whnf_reductions)
                    .saturating_add(progress.numeric_reductions);
                Err(Halt::Stop(Box::new(WhnfStop::NatReduction {
                    at,
                    stop: Box::new(stop),
                    completed_steps: self.control.steps,
                    completed_reductions: self.control.reductions,
                })))
            }
            NatReductionOutcome::InternalFault(fault) => {
                Err(Halt::Fault(WhnfFault::NatReduction {
                    at,
                    fault: Box::new(fault),
                }))
            }
        }
    }

    /// A demanded major that is an arithmetic form is computed by the demanded-major
    /// lane (`reduce_demanded_nat`); any other spine is returned as it is.
    fn reduce_demanded_nat_spine(&mut self, spine: Spine) -> Result<Spine, Halt> {
        let potential = match self.node(&spine.head)? {
            ExprNode::Constant { name, levels } => {
                levels.is_empty()
                    && crate::nat_reduce::operation_for_name(name)
                        .is_some_and(|operation| spine.args.len() == usize::from(operation.arity()))
            }
            _ => false,
        };
        if !potential {
            return Ok(spine);
        }
        let cursor = self.build_spine(spine)?;
        let term = if cursor.env.is_empty() {
            self.materialize_wire(&cursor.arena, cursor.root, WhnfPhase::Iota)?
        } else {
            self.close(&cursor, WhnfPhase::Iota)?
        };
        let reduced = self.reduce_demanded_nat(term)?;
        let (head, args) = self.peel_application(&reduced)?;
        Ok(Spine { head, args })
    }

    /// One term for a spine: its head, or the head applied to its arguments.
    fn build_spine(&mut self, spine: Spine) -> Result<Cursor, Halt> {
        if spine.args.is_empty() {
            return Ok(spine.head);
        }
        self.compose_application(&spine.head, &spine.args)
    }

    /// A cursor's term with its environment substituted, as one arena.
    fn close(&mut self, cursor: &Cursor, phase: WhnfPhase) -> Result<WireExpr, Halt> {
        self.control.step(cursor.root.index(), self.cancelled)?;
        let mut composer = Composer::new(
            self.control.budget.materialization,
            phase,
            self.control.steps,
            self.control.reductions,
            self.cancelled,
        );
        let root = composer.copy_cursor(cursor, 0)?;
        Ok(composer.finish(root))
    }

    fn absorb_demanded_nat(
        &mut self,
        progress: NatReductionProgress,
        at: usize,
    ) -> Result<(), Halt> {
        self.control.steps = self
            .control
            .steps
            .saturating_add(progress.steps)
            .saturating_add(progress.whnf_steps)
            .saturating_add(progress.numeric_steps);
        self.control.reductions = self
            .control
            .reductions
            .saturating_add(progress.whnf_reductions)
            .saturating_add(progress.numeric_reductions);
        self.delta_reductions = self.delta_reductions.saturating_add(progress.delta_unfolds);
        self.control.poll(at, self.cancelled)?;
        for (limit, observed, allowed) in [
            (
                WhnfLimit::Steps,
                self.control.steps,
                self.control.budget.max_steps,
            ),
            (
                WhnfLimit::Reductions,
                self.control.reductions,
                self.control.budget.max_reductions,
            ),
        ] {
            if observed > allowed {
                return Err(Halt::Stop(Box::new(WhnfStop::Resource {
                    limit,
                    allowed,
                    observed,
                    at,
                    completed_steps: self.control.steps,
                    completed_reductions: self.control.reductions,
                })));
            }
        }
        Ok(())
    }

    /// Structural equality of two cursor roots across arenas, budgeted by the
    /// control: the checker-local equivalent of the gate the pin runs with
    /// `is_def_eq` in `to_cnstr_when_K`. Arenas are acyclic with
    /// backward-only references, so the walk terminates.
    fn structural_cursors_equal(&mut self, left: &Cursor, right: &Cursor) -> Result<bool, Halt> {
        // The walk reads bound indices as written, so it compares closed terms.
        if !left.env.is_empty() || !right.env.is_empty() {
            let mut closed = [left, right].map(|cursor| (cursor.env.is_empty(), cursor.clone()));
            for (is_closed, cursor) in &mut closed {
                if !*is_closed {
                    let term = self.close(cursor, WhnfPhase::Iota)?;
                    let root = term.root();
                    *cursor = Cursor::closed(Arc::new(term), root);
                }
            }
            let [(_, left), (_, right)] = closed;
            return self.structural_cursors_equal(&left, &right);
        }
        let mut pending = vec![(left.root, right.root)];
        let mut seen = BTreeSet::new();
        while let Some((left_id, right_id)) = pending.pop() {
            if !seen.insert((left_id, right_id)) {
                continue;
            }
            self.control
                .step(left_id.index().max(right_id.index()), self.cancelled)?;
            let left_node =
                left.arena
                    .node(left_id)
                    .ok_or(Halt::Fault(WhnfFault::MissingExpression {
                        input: 0,
                        index: left_id.index(),
                    }))?;
            let right_node =
                right
                    .arena
                    .node(right_id)
                    .ok_or(Halt::Fault(WhnfFault::MissingExpression {
                        input: 0,
                        index: right_id.index(),
                    }))?;
            let mut push = |left_child: ExprId, right_child: ExprId| -> Result<(), Halt> {
                Self::validate_child(left_id, left_child)?;
                Self::validate_child(right_id, right_child)?;
                pending.push((left_child, right_child));
                Ok(())
            };
            match (left_node, right_node) {
                (ExprNode::NatLiteral { limbs_le: a }, ExprNode::NatLiteral { limbs_le: b }) => {
                    if a.last() == Some(&0) || b.last() == Some(&0) {
                        return Err(Halt::Fault(WhnfFault::NonCanonicalNatLiteral {
                            at: left_id.index(),
                        }));
                    }
                    if a.len() != b.len() {
                        return Ok(false);
                    }
                    for (a, b) in a.iter().zip(b) {
                        self.control.step(left_id.index(), self.cancelled)?;
                        if a != b {
                            return Ok(false);
                        }
                    }
                }
                (ExprNode::Bound { index: left }, ExprNode::Bound { index: right })
                    if left == right => {}
                (ExprNode::Free { name: left }, ExprNode::Free { name: right })
                    if left == right => {}
                (ExprNode::Sort { level: left_level }, ExprNode::Sort { level: right_level }) => {
                    if !level_roots_equal(
                        left.arena.levels(),
                        *left_level,
                        right.arena.levels(),
                        *right_level,
                    )
                    .map_err(|error| {
                        Halt::Fault(WhnfFault::Universe {
                            at: left_id.index(),
                            error,
                        })
                    })? {
                        return Ok(false);
                    }
                }
                (
                    ExprNode::Constant {
                        name: left_name,
                        levels: left_levels,
                    },
                    ExprNode::Constant {
                        name: right_name,
                        levels: right_levels,
                    },
                ) if left_name == right_name && left_levels.len() == right_levels.len() => {
                    for (left_level, right_level) in left_levels.iter().zip(right_levels) {
                        if !level_roots_equal(
                            left.arena.levels(),
                            *left_level,
                            right.arena.levels(),
                            *right_level,
                        )
                        .map_err(|error| {
                            Halt::Fault(WhnfFault::Universe {
                                at: left_id.index(),
                                error,
                            })
                        })? {
                            return Ok(false);
                        }
                    }
                }
                (
                    ExprNode::Apply {
                        function: left_function,
                        argument: left_argument,
                    },
                    ExprNode::Apply {
                        function: right_function,
                        argument: right_argument,
                    },
                ) => {
                    push(*left_argument, *right_argument)?;
                    push(*left_function, *right_function)?;
                }
                (
                    ExprNode::Lambda {
                        binder_type: left_type,
                        body: left_body,
                        style: left_style,
                        ..
                    },
                    ExprNode::Lambda {
                        binder_type: right_type,
                        body: right_body,
                        style: right_style,
                        ..
                    },
                )
                | (
                    ExprNode::Forall {
                        binder_type: left_type,
                        body: left_body,
                        style: left_style,
                        ..
                    },
                    ExprNode::Forall {
                        binder_type: right_type,
                        body: right_body,
                        style: right_style,
                        ..
                    },
                ) if left_style == right_style => {
                    push(*left_body, *right_body)?;
                    push(*left_type, *right_type)?;
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    /// The KR-317 gate by the checker's own conversion, for what the structural
    /// comparison cannot tell. The pin gates K on full `is_def_eq`
    /// (`to_cnstr_when_K`, inductive.h:31). A cast along `hcast : w * (idx + 1)
    /// = w * idx + w` (Std.Tactic.BVDecide ... Operations.Cpop) has indices that
    /// are equal only by unfolding `Nat.mul` on a successor. Missing the gate
    /// there sent WHNF to normalize the proof `hcast` itself, which spent the
    /// whole budget of `blastExtractAndExtend.go._unary.eq_def`.
    ///
    /// Only `Equal` passes the gate: any other outcome, including a stop within
    /// `K_GATE_CONVERSION_WORK`, leaves the major as it is, as a structural
    /// miss does. The work is charged to this reduction, and a cancellation
    /// observed during it stops this reduction too.
    fn k_constructor_types_convert(
        &mut self,
        domain: &Arc<WireExpr>,
        result: &Arc<WireExpr>,
        at: usize,
    ) -> Result<bool, Halt> {
        if K_GATE_CONVERTING.with(Cell::get) {
            return Ok(false);
        }
        let memo = self.context.source.memo().cloned();
        if let Some(equal) = memo
            .as_ref()
            .and_then(|memo| memo.recall_k_gate(domain, result))
        {
            self.control.step(at, self.cancelled)?;
            return Ok(equal);
        }
        let work = K_GATE_CONVERSION_WORK;
        let budget = crate::defeq::DefEqBudget::new(
            crate::defeq::QuickDefEqBudget::new(work, work),
            work,
            work,
            work.saturating_mul(10),
            work.saturating_mul(100),
            WhnfBudget::new(work, work, self.control.budget.materialization),
        );
        let context = self.context.source;
        let cancelled = &mut *self.cancelled;
        let mut saw_cancellation = false;
        K_GATE_CONVERTING.with(|converting| converting.set(true));
        let outcome = crate::defeq::def_eq_with(domain, result, context, budget, || {
            let stop = cancelled();
            saw_cancellation |= stop;
            stop
        });
        K_GATE_CONVERTING.with(|converting| converting.set(false));
        let (equal, progress) = match &outcome {
            crate::defeq::DefEqOutcome::Equal(progress) => (true, *progress),
            crate::defeq::DefEqOutcome::NotEqual { progress, .. }
            | crate::defeq::DefEqOutcome::Deferred { progress, .. }
            | crate::defeq::DefEqOutcome::Refused { progress, .. } => (false, *progress),
            crate::defeq::DefEqOutcome::Inconclusive(stop) => {
                (false, crate::defeq::stop_progress(stop))
            }
            crate::defeq::DefEqOutcome::InternalFault(fault) => {
                return Err(Halt::Fault(WhnfFault::KGateConversion {
                    at,
                    fault: Box::new(fault.clone()),
                }));
            }
        };
        if saw_cancellation {
            return Err(Halt::Stop(Box::new(WhnfStop::Cancelled {
                at,
                polls: self.control.polls,
                completed_steps: self.control.steps,
                completed_reductions: self.control.reductions,
            })));
        }
        self.control.steps = self
            .control
            .steps
            .saturating_add(progress.whnf_steps)
            .saturating_add(progress.slow_comparisons);
        self.control.reductions = self
            .control
            .reductions
            .saturating_add(progress.whnf_reductions);
        if let Some(memo) = memo {
            memo.remember_k_gate(Arc::clone(domain), Arc::clone(result), equal);
        }
        self.control.step(at, self.cancelled)?;
        Ok(equal)
    }

    /// A sufficient conversion gate for KR-317. Compare demanded application
    /// arguments after checker-owned WHNF instead of requiring identical syntax.
    /// This permits equal types computed by recursors/projections without making
    /// a cast across distinct types disappear. No proof irrelevance is assumed.
    /// Binder bodies stay on the structural path: reducing them here would need
    /// a shifted local context which this cursor-only reducer does not carry.
    fn k_constructor_types_equal(&mut self, left: &Cursor, right: &Cursor) -> Result<bool, Halt> {
        let mut pending = vec![(left.clone(), right.clone())];
        let mut seen = BTreeSet::new();
        // Keep arenas behind request-local address keys alive until the walk ends.
        let mut roots = Vec::new();
        while let Some((left, right)) = pending.pop() {
            let key = (
                Arc::as_ptr(&left.arena),
                left.root,
                Arc::as_ptr(&right.arena),
                right.root,
            );
            if !seen.insert(key) {
                continue;
            }
            roots.push((left.arena.clone(), right.arena.clone()));
            if self.structural_cursors_equal(&left, &right)? {
                continue;
            }
            self.has_auxiliary_work = true;
            let Some(left) = self.whnf_recursor_major(&left)? else {
                return Ok(false);
            };
            let Some(right) = self.whnf_recursor_major(&right)? else {
                return Ok(false);
            };
            if self.structural_cursors_equal(&left, &right)? {
                continue;
            }
            let literal_fields = match self.k_literal_constructor_pair(&left, &right)? {
                Some(fields) => Some(fields),
                None => self.k_literal_constructor_pair(&right, &left)?,
            };
            if let Some(fields) = literal_fields {
                pending.extend(fields);
                continue;
            }
            match (self.node(&left)?, self.node(&right)?) {
                (
                    ExprNode::Apply {
                        function: lf,
                        argument: la,
                    },
                    ExprNode::Apply {
                        function: rf,
                        argument: ra,
                    },
                ) => {
                    for (l, r) in [(*lf, *rf), (*la, *ra)] {
                        Self::validate_child(left.root, l)?;
                        Self::validate_child(right.root, r)?;
                        pending.push((left.child(l), right.child(r)));
                    }
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    /// Compare one compact literal layer with an explicitly written Nat
    /// constructor. Reuse the ordinary admitted-family gate and predecessor
    /// builder; never unfold a numeral into a complete unary constructor tree.
    fn k_literal_constructor_pair(
        &mut self,
        literal: &Cursor,
        constructor: &Cursor,
    ) -> Result<Option<Vec<(Cursor, Cursor)>>, Halt> {
        if !matches!(self.node(literal)?, ExprNode::NatLiteral { .. }) {
            return Ok(None);
        }
        let (head, arguments) = self.peel_application(constructor)?;
        let ExprNode::Constant { name, levels } = self.node(&head)? else {
            return Ok(None);
        };
        if !levels.is_empty() {
            return Ok(None);
        }
        let name = name.clone();
        let rec = WireName::from_parts(vec![
            NamePart::Text("Nat".into()),
            NamePart::Text("rec".into()),
        ]);
        let Some(entry) = self.context.source.constants().find(&rec) else {
            return Ok(None);
        };
        if entry.safety() != crate::environment::ConstantSafety::Safe {
            return Ok(None);
        }
        let Some(metadata) = entry.recursor_metadata().cloned() else {
            return Ok(None);
        };
        let Some((expected, fields)) = self.nat_literal_constructor(&metadata, literal)? else {
            return Ok(None);
        };
        if name != expected || fields.len() != arguments.len() {
            return Ok(None);
        }
        Ok(Some(fields.into_iter().zip(arguments).collect()))
    }

    /// Consume a peeled telescope from the inside out. Each replacement lives
    /// outside all remaining slots, so lift its external indices before insertion.
    /// Without that lift a later substitution rewrites the replacement's own
    /// outer locals, silently changing the type used to decide K reduction.
    fn instantiate_k_slots(
        &mut self,
        mut term: WireExpr,
        arguments: &VecDeque<Cursor>,
        end: usize,
    ) -> Result<Option<WireExpr>, Halt> {
        let facts = self.control.term_halt(
            WhnfPhase::Iota,
            inspect_with(
                &term,
                self.control.budget.materialization,
                &mut *self.cancelled,
            ),
        )?;
        let needed = usize::try_from(facts.external_bound_span).unwrap_or(usize::MAX);
        if needed > end || end > arguments.len() {
            return Ok(None);
        }
        for (position, replacement) in arguments.range(end - needed..end).rev().enumerate() {
            self.control.step(term.root().index(), self.cancelled)?;
            // Substituting an index that does not occur only renumbers the others,
            // so any closed value gives the same term. The motive and minor
            // premises before a structure's major are often large, and the
            // major's type rarely mentions them.
            if !loose_bound_occurs(&term, 0) {
                term = self.control.term_halt(
                    WhnfPhase::Iota,
                    substitute_bound_subterms_with(
                        &term,
                        term.root(),
                        0,
                        &absent_value(),
                        ExprId::ZERO,
                        self.control.budget.materialization,
                        &mut *self.cancelled,
                    ),
                )?;
                continue;
            }
            let replacement = if replacement.env.is_empty() {
                self.materialize_wire(&replacement.arena, replacement.root, WhnfPhase::Iota)?
            } else {
                self.close(replacement, WhnfPhase::Iota)?
            };
            // `needed` originated in a u32, and position is strictly below it.
            let amount = u32::try_from(needed - position - 1).unwrap_or(u32::MAX);
            let replacement = self.control.term_halt(
                WhnfPhase::Iota,
                crate::term::raise_external_bounds_with(
                    &replacement,
                    amount,
                    0,
                    self.control.budget.materialization,
                    &mut *self.cancelled,
                ),
            )?;
            term = self.control.term_halt(
                WhnfPhase::Iota,
                substitute_bound_subterms_with(
                    &term,
                    term.root(),
                    0,
                    &replacement,
                    replacement.root(),
                    self.control.budget.materialization,
                    &mut *self.cancelled,
                ),
            )?;
        }
        Ok(Some(term))
    }

    /// KR-317 (`to_cnstr_when_K`, inductive.h:31): a K-flagged recursor
    /// replaces a stuck major premise with the inductive's nullary
    /// constructor so the ordinary iota rule can fire. The pin gates the
    /// replacement on `is_def_eq` between the major's INFERRED type and the
    /// constructed constructor's type; this layer has no term inference, so
    /// the gate derives the major's domain from the recursor's own telescope
    /// instantiated by the spine (the same place K1's `recursor_major_induct`
    /// reads, tc.rs:3409) and requires the constructor's result type to match
    /// it by budgeted structural/applicative WHNF conversion. A gate miss leaves
    /// the major stuck, never produces a wrong reduction. This is what closes
    /// `cast h a ≡ a` with the proof h a variable (fln-51y8 item 126).
    #[allow(clippy::too_many_arguments)]
    fn recursor_major_to_nullary_constructor(
        &mut self,
        level_parameters: &[WireName],
        recursor_type: &WireExpr,
        current: &Cursor,
        levels: &[LevelId],
        arguments: &VecDeque<Cursor>,
        major_index: usize,
        parameter_count: usize,
    ) -> Result<Option<Cursor>, Halt> {
        if self.major_is_constructor_application(&arguments[major_index])? {
            return Ok(None);
        }
        // derived domain is concrete.
        let instantiated_type = match instantiate_term_parameters_from_level_roots_with(
            recursor_type,
            level_parameters,
            current.arena.levels(),
            levels,
            self.control.budget.materialization,
            &mut *self.cancelled,
        ) {
            InstantiationOutcome::Complete(term) => term,
            InstantiationOutcome::Refused(refusal) => {
                return Err(Halt::Refusal(WhnfRefusal::DefinitionInstantiation {
                    at: current.root.index(),
                    refusal,
                }));
            }
            InstantiationOutcome::Inconclusive(stop) => {
                return Err(Halt::Stop(Box::new(WhnfStop::DefinitionInstantiation {
                    at: current.root.index(),
                    stop,
                    completed_steps: self.control.steps,
                    completed_reductions: self.control.reductions,
                })));
            }
            InstantiationOutcome::InternalFault(fault) => {
                return Err(Halt::Fault(WhnfFault::DefinitionInstantiation {
                    at: current.root.index(),
                    fault,
                }));
            }
        };
        // Walk `major_index` binders of the recursor's type; the next binder's
        // domain is the major premise's expected type.
        let mut root = instantiated_type.root();
        for _ in 0..major_index {
            self.control.step(root.index(), self.cancelled)?;
            let Some(ExprNode::Forall { body, .. }) = instantiated_type.node(root) else {
                return Ok(None);
            };
            Self::validate_child(root, *body)?;
            root = *body;
        }
        self.control.step(root.index(), self.cancelled)?;
        let Some(ExprNode::Forall { binder_type, .. }) = instantiated_type.node(root) else {
            return Ok(None);
        };
        Self::validate_child(root, *binder_type)?;
        let domain = self.materialize_wire(&instantiated_type, *binder_type, WhnfPhase::Iota)?;
        let Some(domain) = self.instantiate_k_slots(domain, arguments, major_index)? else {
            return Ok(None);
        };
        let domain = Arc::new(domain);
        let domain_cursor = Cursor::closed(Arc::clone(&domain), domain.root());
        let (domain_head, domain_args) = self.peel_application(&domain_cursor)?;
        let (inductive_name, inductive_levels) = match self.node(&domain_head)? {
            ExprNode::Constant { name, levels } => (name.clone(), levels.clone()),
            _ => return Ok(None),
        };
        let Some(inductive_entry) = self.context.source.constants().find(&inductive_name) else {
            return Ok(None);
        };
        let Some(inductive_metadata) = inductive_entry.inductive_metadata() else {
            return Ok(None);
        };
        let Some(constructor_name) = inductive_metadata.constructors().first().cloned() else {
            return Ok(None);
        };
        let Some(constructor_entry) = self.context.source.constants().find(&constructor_name)
        else {
            return Ok(None);
        };
        let constructor_type = constructor_entry.type_().clone();
        let constructor_levels = constructor_entry.level_parameters().to_vec();
        // The constructor's result type with the domain's parameters applied:
        // peel the parameter binders and substitute the domain's parameter
        // arguments. K-flagged families are nullary, so no field binders
        // remain at that point by construction.
        let mut constructor_result = match instantiate_term_parameters_from_level_roots_with(
            &constructor_type,
            &constructor_levels,
            domain.levels(),
            &inductive_levels,
            self.control.budget.materialization,
            &mut *self.cancelled,
        ) {
            InstantiationOutcome::Complete(term) => term,
            InstantiationOutcome::Refused(refusal) => {
                return Err(Halt::Refusal(WhnfRefusal::DefinitionInstantiation {
                    at: current.root.index(),
                    refusal,
                }));
            }
            InstantiationOutcome::Inconclusive(stop) => {
                return Err(Halt::Stop(Box::new(WhnfStop::DefinitionInstantiation {
                    at: current.root.index(),
                    stop,
                    completed_steps: self.control.steps,
                    completed_reductions: self.control.reductions,
                })));
            }
            InstantiationOutcome::InternalFault(fault) => {
                return Err(Halt::Fault(WhnfFault::DefinitionInstantiation {
                    at: current.root.index(),
                    fault,
                }));
            }
        };
        let mut result_root = constructor_result.root();
        for _ in 0..parameter_count {
            self.control.step(result_root.index(), self.cancelled)?;
            let Some(ExprNode::Forall { body, .. }) = constructor_result.node(result_root) else {
                return Ok(None);
            };
            Self::validate_child(result_root, *body)?;
            result_root = *body;
        }
        constructor_result =
            self.materialize_wire(&constructor_result, result_root, WhnfPhase::Iota)?;
        let Some(constructor_result) =
            self.instantiate_k_slots(constructor_result, &domain_args, parameter_count)?
        else {
            return Ok(None);
        };
        let result_root = constructor_result.root();
        let result_cursor = Cursor::closed(Arc::new(constructor_result), result_root);
        // The pin's gate: the constructed constructor's type must be defeq to
        // the major's type. Here: the reconstructed result type must match
        // the spine-derived domain by a sufficient checker-owned conversion,
        // structural first and the full conversion when that cannot tell.
        if !self.k_constructor_types_equal(&domain_cursor, &result_cursor)?
            && !self.k_constructor_types_convert(
                &domain_cursor.arena,
                &result_cursor.arena,
                current.root.index(),
            )?
        {
            return Ok(None);
        }
        // Build the nullary constructor applied to the domain's parameters.
        let mut composer = Composer::new(
            self.control.budget.materialization,
            WhnfPhase::Iota,
            self.control.steps,
            self.control.reductions,
            &mut *self.cancelled,
        );
        let domain_source = composer.source_index(&domain);
        let mut level_ids = Vec::with_capacity(inductive_levels.len());
        for level in &inductive_levels {
            level_ids.push(composer.copy_level_root(domain_source, *level, 0)?);
        }
        let mut root = composer.push_expression(
            ExprNode::Constant {
                name: constructor_name,
                levels: level_ids,
            },
            1,
            0,
        )?;
        for (index, argument) in domain_args.iter().take(parameter_count).enumerate() {
            let argument = composer.copy_cursor(argument, index.saturating_add(1))?;
            root = composer.push_expression(
                ExprNode::Apply {
                    function: root,
                    argument,
                },
                1,
                index,
            )?;
        }
        Ok(Some(composer.finish_cursor(root)))
    }

    /// KR-316 structure-eta coercion (`to_cnstr_when_structure`): a major of a
    /// one-constructor, index-free, non-recursive, non-Prop structure type that
    /// is not already a constructor application becomes
    /// `mk params (proj 0 major) … (proj n-1 major)`. When the structure has zero
    /// fields (like PUnit), it simplifies directly to `mk params`. Any gate
    /// failure returns `Ok(None)` leaving the recursor major unchanged.
    #[allow(clippy::too_many_arguments)]
    fn recursor_major_to_structure_constructor(
        &mut self,
        level_parameters: &[WireName],
        recursor_type: &WireExpr,
        current: &Cursor,
        levels: &[LevelId],
        arguments: &VecDeque<Cursor>,
        major_index: usize,
    ) -> Result<Option<Cursor>, Halt> {
        if self.major_is_constructor_application(&arguments[major_index])? {
            return Ok(None);
        }
        let instantiated_type = match instantiate_term_parameters_from_level_roots_with(
            recursor_type,
            level_parameters,
            current.arena.levels(),
            levels,
            self.control.budget.materialization,
            &mut *self.cancelled,
        ) {
            InstantiationOutcome::Complete(term) => term,
            InstantiationOutcome::Refused(refusal) => {
                return Err(Halt::Refusal(WhnfRefusal::DefinitionInstantiation {
                    at: current.root.index(),
                    refusal,
                }));
            }
            InstantiationOutcome::Inconclusive(stop) => {
                return Err(Halt::Stop(Box::new(WhnfStop::DefinitionInstantiation {
                    at: current.root.index(),
                    stop,
                    completed_steps: self.control.steps,
                    completed_reductions: self.control.reductions,
                })));
            }
            InstantiationOutcome::InternalFault(fault) => {
                return Err(Halt::Fault(WhnfFault::DefinitionInstantiation {
                    at: current.root.index(),
                    fault,
                }));
            }
        };
        let mut root = instantiated_type.root();
        for _ in 0..major_index {
            self.control.step(root.index(), self.cancelled)?;
            let Some(ExprNode::Forall { body, .. }) = instantiated_type.node(root) else {
                return Ok(None);
            };
            Self::validate_child(root, *body)?;
            root = *body;
        }
        self.control.step(root.index(), self.cancelled)?;
        let Some(ExprNode::Forall { binder_type, .. }) = instantiated_type.node(root) else {
            return Ok(None);
        };
        Self::validate_child(root, *binder_type)?;
        let domain = self.materialize_wire(&instantiated_type, *binder_type, WhnfPhase::Iota)?;
        let Some(domain) = self.instantiate_k_slots(domain, arguments, major_index)? else {
            return Ok(None);
        };
        let domain = Arc::new(domain);
        let domain_cursor = Cursor::closed(Arc::clone(&domain), domain.root());
        let (domain_head, domain_args) = self.peel_application(&domain_cursor)?;
        let (inductive_name, inductive_levels) = match self.node(&domain_head)? {
            ExprNode::Constant { name, levels } => (name.clone(), levels.clone()),
            _ => return Ok(None),
        };
        let Some(inductive_entry) = self.context.source.constants().find(&inductive_name) else {
            return Ok(None);
        };
        let Some(inductive_metadata) = inductive_entry.inductive_metadata() else {
            return Ok(None);
        };
        // Must be a non-recursive, index-free structure with exactly 1 constructor.
        if inductive_metadata.constructors().len() != 1
            || inductive_metadata.num_indices() != 0
            || inductive_metadata.is_recursive()
        {
            return Ok(None);
        }
        let Some(constructor_name) = inductive_metadata.constructors().first().cloned() else {
            return Ok(None);
        };
        let Some(constructor_entry) = self.context.source.constants().find(&constructor_name)
        else {
            return Ok(None);
        };
        let Some(constructor_meta) = constructor_entry.constructor_metadata() else {
            return Ok(None);
        };
        let num_fields = usize::try_from(constructor_meta.num_fields()).unwrap_or(usize::MAX);
        let ctor_params = usize::try_from(constructor_meta.num_parameters()).unwrap_or(usize::MAX);

        // Prop-valued structures are excluded (proof irrelevance covers them).
        let mut ind_type_root = inductive_entry.type_().root();
        for _ in 0..inductive_metadata.num_parameters() {
            let Some(ExprNode::Forall { body, .. }) = inductive_entry.type_().node(ind_type_root)
            else {
                break;
            };
            ind_type_root = *body;
        }
        if let Some(ExprNode::Sort { level }) = inductive_entry.type_().node(ind_type_root)
            && matches!(inductive_entry.type_().level(*level), Some(LevelNode::Zero))
        {
            return Ok(None);
        }

        // Build the constructor application:
        // Ctor.{inductive_levels} domain_args[0..ctor_params] (proj 0 major) … (proj (n-1) major)
        let mut composer = Composer::new(
            self.control.budget.materialization,
            WhnfPhase::Iota,
            self.control.steps,
            self.control.reductions,
            &mut *self.cancelled,
        );
        let domain_source = composer.source_index(&domain);
        let mut level_ids = Vec::with_capacity(inductive_levels.len());
        for level in &inductive_levels {
            level_ids.push(composer.copy_level_root(domain_source, *level, 0)?);
        }
        let mut root = composer.push_expression(
            ExprNode::Constant {
                name: constructor_name,
                levels: level_ids,
            },
            1,
            0,
        )?;
        for (index, argument) in domain_args.iter().take(ctor_params).enumerate() {
            let argument = composer.copy_cursor(argument, index.saturating_add(1))?;
            root = composer.push_expression(
                ExprNode::Apply {
                    function: root,
                    argument,
                },
                1,
                index,
            )?;
        }
        if num_fields > 0 {
            let major_cursor =
                composer.copy_cursor(&arguments[major_index], ctor_params.saturating_add(1))?;
            for i in 0..num_fields {
                let proj = composer.push_expression(
                    ExprNode::Projection {
                        structure_name: inductive_name.clone(),
                        index: i as u64,
                        expression: major_cursor,
                    },
                    1,
                    ctor_params.saturating_add(i),
                )?;
                root = composer.push_expression(
                    ExprNode::Apply {
                        function: root,
                        argument: proj,
                    },
                    1,
                    ctor_params.saturating_add(i),
                )?;
            }
        }
        Ok(Some(composer.finish_cursor(root)))
    }

    /// Expose one layer of an admitted Nat constructor for a literal major.
    /// Never build a unary numeral: successor fields remain compact literals.
    /// The family and constructors must be present with the expected metadata;
    /// a same-shaped recursor for another family cannot consume a Nat literal.
    fn nat_literal_constructor(
        &mut self,
        metadata: &RecursorDeclaration,
        major: &Cursor,
    ) -> Result<Option<(WireName, VecDeque<Cursor>)>, Halt> {
        let ExprNode::NatLiteral { limbs_le } = self.node(major)? else {
            return Ok(None);
        };
        let nat = WireName::from_parts(vec![NamePart::Text("Nat".to_owned())]);
        let zero = WireName::from_parts(vec![
            NamePart::Text("Nat".to_owned()),
            NamePart::Text("zero".to_owned()),
        ]);
        let succ = WireName::from_parts(vec![
            NamePart::Text("Nat".to_owned()),
            NamePart::Text("succ".to_owned()),
        ]);
        if metadata.mutual() != std::slice::from_ref(&nat)
            || metadata.num_parameters() != 0
            || metadata.num_indices() != 0
            || metadata.num_motives() != 1
            || metadata.num_minors() != 2
            || metadata.k()
        {
            return Ok(None);
        }
        let constants = self.context.source.constants();
        let Some(entry) = constants.find(&nat) else {
            return Ok(None);
        };
        let Some(family) = entry.inductive_metadata() else {
            return Ok(None);
        };
        if entry.safety() != crate::environment::ConstantSafety::Safe
            || !entry.level_parameters().is_empty()
            || family.num_parameters() != 0
            || family.num_indices() != 0
            || family.constructors() != [zero.clone(), succ.clone()]
            || family.mutual() != std::slice::from_ref(&nat)
        {
            return Ok(None);
        }
        for (index, name) in [&zero, &succ].into_iter().enumerate() {
            let Some(entry) = constants.find(name) else {
                return Ok(None);
            };
            let Some(constructor) = entry.constructor_metadata() else {
                return Ok(None);
            };
            if entry.safety() != crate::environment::ConstantSafety::Safe
                || !entry.level_parameters().is_empty()
                || constructor.inductive() != &nat
                || constructor.index() != index as u32
                || constructor.num_parameters() != 0
                || constructor.num_fields() != index as u32
            {
                return Ok(None);
            }
        }
        if limbs_le.last() == Some(&0) {
            return Err(Halt::Fault(WhnfFault::NonCanonicalNatLiteral {
                at: major.root.index(),
            }));
        }
        if limbs_le.is_empty() {
            return Ok(Some((zero, VecDeque::new())));
        }
        let mut composer = Composer::new(
            self.control.budget.materialization,
            WhnfPhase::Iota,
            self.control.steps,
            self.control.reductions,
            &mut *self.cancelled,
        );
        // Admit the largest output before allocating its limb storage.
        composer
            .control
            .output(
                1_u64.saturating_add(usize_units(limbs_le.len())),
                major.root.index(),
            )
            .map_err(|halt| composer.map_halt(halt))?;
        composer
            .control
            .admit_arena_node(1, major.root.index())
            .map_err(|halt| composer.map_halt(halt))?;
        let mut predecessor = Vec::with_capacity(limbs_le.len());
        let mut borrow = true;
        for limb in limbs_le {
            composer
                .control
                .step(major.root.index())
                .map_err(|halt| composer.map_halt(halt))?;
            let (value, next) = limb.overflowing_sub(u64::from(borrow));
            predecessor.push(value);
            borrow = next;
        }
        if predecessor.last() == Some(&0) {
            predecessor.pop();
        }
        let root = composer
            .push_expression_charged(
                ExprNode::NatLiteral {
                    limbs_le: predecessor,
                },
                major.root.index(),
                None,
            )
            .map_err(|halt| composer.map_halt(halt))?;
        let term = composer.finish(root);
        Ok(Some((
            succ,
            VecDeque::from([Cursor::closed(Arc::new(term), root)]),
        )))
    }

    /// KR-316 (`inductive_reduce_rec`, inductive.h:76): a recursor application
    /// KR-316 (`inductive_reduce_rec`, inductive.h:76): a recursor application
    /// fires when its major premise reduces to a constructor of the recursor's
    /// inductive. The matching rule's right-hand side is instantiated with the
    /// recursor's levels and applied to the spine's parameters, motives, and
    /// minor premises (the indices are consumed by the motive, never applied
    /// to the rule), then the constructor's fields, then the trailing
    /// arguments. Nat literal majors expose one compact constructor layer;
    /// structure-eta coercion reduces non-Prop structures; String literal
    /// majors remain unsupported.
    #[inline(never)]
    #[allow(clippy::too_many_arguments)]
    fn apply_recursor_rule(
        &mut self,
        metadata: &RecursorDeclaration,
        level_parameters: &[WireName],
        head: &Cursor,
        levels: &[LevelId],
        arguments: &VecDeque<Cursor>,
        major_index: usize,
        major: &Spine,
        prefix: usize,
    ) -> Result<Option<Spine>, Halt> {
        let literal = if major.args.is_empty() {
            self.nat_literal_constructor(metadata, &major.head)?
        } else {
            None
        };
        let (constructor_name, major_args) = if let Some(parts) = literal {
            parts
        } else {
            let ExprNode::Constant { name, .. } = self.node(&major.head)? else {
                return Ok(None);
            };
            (name.clone(), major.args.clone())
        };
        let Some(rule) = metadata
            .rules()
            .iter()
            .find(|rule| rule.constructor() == &constructor_name)
        else {
            return Ok(None);
        };
        let field_count = usize::try_from(rule.num_fields()).unwrap_or(usize::MAX);
        if field_count > major_args.len() {
            return Ok(None);
        }
        if levels.len() != level_parameters.len() {
            return Ok(None);
        }
        self.control.reduction(head.root.index(), self.cancelled)?;
        // The environment's own rule, whose address is stable for the run, so
        // its instantiation is shared (`Reducer::instantiated`). `metadata` may
        // be a frame's copy of it.
        let source = self.context.source;
        let stable = match self.node(head)? {
            ExprNode::Constant { name, .. } => source
                .constants()
                .find(name)
                .and_then(|entry| entry.recursor_metadata())
                .and_then(|metadata| {
                    metadata
                        .rules()
                        .iter()
                        .find(|stable| stable.constructor() == &constructor_name)
                })
                .map(|stable| stable.rhs()),
            _ => None,
        };
        let instantiated_rhs = self.instantiated(
            stable.unwrap_or(rule.rhs()),
            level_parameters,
            &head.arena,
            levels,
            head.root.index(),
            stable.is_some(),
        )?;
        let rhs_root = instantiated_rhs.root();
        // The rule's right-hand side is applied to the spine's parameters,
        // motives and minors, the constructor's fields and the trailing
        // arguments, as pending arguments of the reduction: nothing is copied.
        let mut pending = VecDeque::new();
        let spine_arguments = arguments
            .iter()
            .take(prefix)
            .chain(major_args.iter().skip(major_args.len() - field_count))
            .chain(arguments.iter().skip(major_index.saturating_add(1)));
        for argument in spine_arguments {
            self.control.step(argument.root.index(), self.cancelled)?;
            pending.push_back(argument.clone());
        }
        Ok(Some(Spine {
            head: Cursor::closed(instantiated_rhs, rhs_root),
            args: pending,
        }))
    }

    /// Step recursor reduction: if the major premise is already a constructor,
    /// fire the rule immediately. Otherwise, package the state into a heap-allocated
    /// `RecursorFrame` to evaluate the major premise without native Rust recursion.
    #[inline(never)]
    fn step_recursor_reduction(
        &mut self,
        current: &Cursor,
        arguments: &mut VecDeque<Cursor>,
    ) -> Result<Option<RecursorStep>, Halt> {
        let (name, levels) = match self.node(current)? {
            ExprNode::Constant { name, levels } => (name.clone(), levels.clone()),
            _ => return Ok(None),
        };
        let Some(entry) = self.context.source.constants().find(&name) else {
            return Ok(None);
        };
        let Some(metadata) = entry.recursor_metadata().cloned() else {
            return Ok(None);
        };
        let level_parameters = entry.level_parameters().to_vec();
        let recursor_type = entry.type_().clone();
        let parameter_count = usize::try_from(metadata.num_parameters()).unwrap_or(usize::MAX);
        let Some(major_index) = parameter_count
            .checked_add(usize::try_from(metadata.num_motives()).unwrap_or(usize::MAX))
            .and_then(|value| {
                value.checked_add(usize::try_from(metadata.num_minors()).unwrap_or(usize::MAX))
            })
            .and_then(|value| {
                value.checked_add(usize::try_from(metadata.num_indices()).unwrap_or(usize::MAX))
            })
        else {
            return Ok(None);
        };
        if arguments.len() <= major_index {
            return Ok(None);
        }
        let mut major = arguments[major_index].clone();
        if metadata.k()
            && let Some(replacement) = self.recursor_major_to_nullary_constructor(
                &level_parameters,
                &recursor_type,
                current,
                &levels,
                arguments,
                major_index,
                parameter_count,
            )?
        {
            major = replacement;
        } else if let Some(replacement) = self.recursor_major_to_structure_constructor(
            &level_parameters,
            &recursor_type,
            current,
            &levels,
            arguments,
            major_index,
        )? {
            major = replacement;
        }
        let prefix = parameter_count
            .saturating_add(usize::try_from(metadata.num_motives()).unwrap_or(usize::MAX))
            .saturating_add(usize::try_from(metadata.num_minors()).unwrap_or(usize::MAX));

        let (major_head, major_args) = self.peel_application(&major)?;
        let major_spine = Spine {
            head: major_head,
            args: major_args,
        };
        if let Some(reduced) = self.apply_recursor_rule(
            &metadata,
            &level_parameters,
            current,
            &levels,
            arguments,
            major_index,
            &major_spine,
            prefix,
        )? {
            arguments.clear();
            return Ok(Some(RecursorStep::Reduced(reduced)));
        }

        let frame = Box::new(RecursorFrame {
            head: current.clone(),
            metadata,
            level_parameters,
            recursor_type,
            levels,
            arguments: std::mem::take(arguments),
            major_index,
            parameter_count,
            prefix,
            delta_mode: self.delta_mode,
            unfolded_bindings: self.unfolded_bindings.clone(),
            force_string_delta: self.force_string_delta,
            progress: ProgressMark {
                reductions: self.control.reductions,
                delta_reductions: self.delta_reductions,
                discarded_reductions: self.discarded_reductions,
                discarded_delta_reductions: self.discarded_delta_reductions,
            },
        });
        Ok(Some(RecursorStep::NormalizeMajor { frame, major }))
    }

    /// KR-313 natural literal acceleration in the WHNF loop (type_checker.cpp:689).
    /// If the head constant is in the pinned Nat operation table, enough
    /// pending arguments are present and the scope admits the form, its
    /// operands are normalized in this loop (`NatFrame`) before any delta
    /// unfolding; the first operand to normalize is returned. Every operation is
    /// offered, as the pin's `whnf` offers it to `reduce_nat`; `self.head_nat`
    /// decides which open forms may be. Declined, an operation unfolds into its
    /// definition's recursion.
    fn begin_nat(
        &mut self,
        current: &Cursor,
        pending_arguments: &mut VecDeque<Cursor>,
        frames: &mut Vec<ReductionFrame>,
    ) -> Result<Option<Cursor>, Halt> {
        let (name, levels) = match self.node(current)? {
            ExprNode::Constant { name, levels } => (name, levels),
            _ => return Ok(None),
        };
        if !levels.is_empty() {
            return Ok(None);
        }
        let Some(operation) = crate::nat_reduce::operation_for_name(name) else {
            return Ok(None);
        };
        let arity = usize::from(operation.arity());
        if pending_arguments.len() < arity {
            return Ok(None);
        }
        if !self.nat_form_closed(current, pending_arguments, arity)? {
            self.has_auxiliary_work = true;
            return Ok(None);
        }
        let arguments = std::mem::take(pending_arguments);
        let first = arguments[0].clone();
        frames.push(ReductionFrame::Nat(Box::new(NatFrame {
            operation,
            head: current.clone(),
            arguments,
            values: Vec::new(),
            delta_mode: self.delta_mode,
            unfolded_bindings: self.unfolded_bindings.clone(),
            force_string_delta: self.force_string_delta,
        })));
        self.delta_mode = DeltaMode::Eager;
        self.force_string_delta = false;
        Ok(Some(first))
    }

    /// Whether the operation with its first `arity` arguments may be reduced in
    /// `self.head_nat`'s scope: no loose bound variable, and no free variable,
    /// or for `WhnfHead` only free variables let-bound to closed values
    /// (nat_reduce's `is_closed_in`). Each subterm is checked once, from cached
    /// per-arena facts, through the environment values it refers to.
    fn nat_form_closed(
        &mut self,
        head: &Cursor,
        arguments: &VecDeque<Cursor>,
        arity: usize,
    ) -> Result<bool, Halt> {
        let lets_allowed = match self.head_nat {
            NatReductionScope::EagerOpenPair => return Ok(true),
            NatReductionScope::WhnfHead => true,
            NatReductionScope::ClosedPair | NatReductionScope::DemandedMajor => false,
        };
        let mut pending: Vec<Cursor> = std::iter::once(head.clone())
            .chain(arguments.iter().take(arity).cloned())
            .collect();
        let mut seen = std::collections::HashSet::new();
        // Environments stay alive while their identities key `seen`.
        let mut held = Vec::new();
        while let Some(cursor) = pending.pop() {
            let key = (
                Arc::as_ptr(&cursor.arena).addr(),
                cursor.root.index(),
                cursor.env.identity(),
            );
            if !seen.insert(key) {
                continue;
            }
            self.control.step(cursor.root.index(), self.cancelled)?;
            let (loose, mask, free) = self.fact(&cursor.arena, cursor.root)?;
            if loose > cursor.env.len() {
                return Ok(false);
            }
            if free && !(lets_allowed && self.frees_let_bound_closed(&cursor)?) {
                return Ok(false);
            }
            for slot in 0..loose {
                if slot < 64 && mask & (1 << slot) == 0 {
                    continue;
                }
                if let Some(value) = cursor.env.get(slot) {
                    pending.push(value.clone());
                }
            }
            held.push(cursor);
        }
        Ok(true)
    }

    /// Whether every free variable of a cursor's own arena subterm is let-bound
    /// in the context to a closed value. Each binding is followed once.
    fn frees_let_bound_closed(&mut self, cursor: &Cursor) -> Result<bool, Halt> {
        let mut followed = BTreeSet::new();
        let mut seen = std::collections::HashSet::new();
        let mut pending = vec![(Arc::clone(&cursor.arena), cursor.root)];
        while let Some((arena, root)) = pending.pop() {
            if !self.fact(&arena, root)?.2 {
                continue;
            }
            if !seen.insert((Arc::as_ptr(&arena).addr(), root.index())) {
                continue;
            }
            self.control.step(root.index(), self.cancelled)?;
            let node = arena
                .node(root)
                .ok_or(Halt::Fault(WhnfFault::MissingExpression {
                    input: 0,
                    index: root.index(),
                }))?;
            if let ExprNode::Free { name } = node {
                let Some(&binding) = self.context.free_bindings.get(name) else {
                    return Ok(false);
                };
                if followed.insert(binding) {
                    let value = self
                        .context
                        .source
                        .free_bindings
                        .get(binding)
                        .map(|binding| Arc::clone(&binding.value))
                        .ok_or(Halt::Fault(WhnfFault::MissingExpression {
                            input: 0,
                            index: binding,
                        }))?;
                    let value_root = value.root();
                    if self.fact(&value, value_root)?.0 != 0 {
                        return Ok(false);
                    }
                    pending.push((value, value_root));
                }
                continue;
            }
            for (child, _) in expression_children(node).into_iter().flatten() {
                pending.push((Arc::clone(&arena), child));
            }
        }
        Ok(true)
    }

    /// The loose range, loose mask and free-variable flag of `root` in `arena`.
    fn fact(&mut self, arena: &Arc<WireExpr>, root: ExprId) -> Result<(u32, u64, bool), Halt> {
        // A pure cache that keeps its arenas alive: bounded, so a long run does
        // not retain every arena it ever checked.
        if self.facts.len() >= 4096 && !self.facts.contains_key(&Arc::as_ptr(arena).addr()) {
            self.facts.clear();
        }
        let facts = self
            .facts
            .entry(Arc::as_ptr(arena).addr())
            .or_insert_with(|| ArenaFacts::new(Arc::clone(arena)));
        facts.at(root, &mut self.control, &mut *self.cancelled)
    }

    /// Compute a Nat frame's operation on its natural operands: the result, or
    /// `None` when the operation declines (`Nat.pow` above the pin's cap).
    fn execute_nat(&mut self, frame: &NatFrame) -> Result<Option<Cursor>, Halt> {
        let at = frame.head.root.index();
        let steps = self
            .control
            .budget
            .max_steps
            .saturating_sub(self.control.steps);
        let reductions = self
            .control
            .budget
            .max_reductions
            .saturating_sub(self.control.reductions);
        let materialization = self.control.budget.materialization;
        let budget = NatReductionBudget::new(
            steps,
            steps,
            reductions,
            materialization.max_arena_nodes,
            materialization.max_output_units,
            materialization.max_output_units,
            WhnfBudget::new(steps, reductions, materialization)
                .with_string(self.remaining_string_budget()),
            NatBudget::new(steps, materialization.max_output_units),
        );
        let result = crate::nat_reduce::execute_operation(
            frame.operation,
            &frame.values,
            budget,
            &mut *self.cancelled,
        );
        match result {
            NatReductionOutcome::Reduced(result) => {
                self.absorb_demanded_nat(result.progress, at)?;
                self.control.reduction(at, self.cancelled)?;
                let root = result.term.root();
                Ok(Some(Cursor::closed(Arc::new(result.term), root)))
            }
            NatReductionOutcome::NotReduced { progress, .. } => {
                self.absorb_demanded_nat(progress, at)?;
                Ok(None)
            }
            NatReductionOutcome::Refused {
                refusal: crate::nat_reduce::NatReductionRefusal::Whnf { refusal, .. },
                progress,
            } => {
                self.absorb_demanded_nat(progress, at)?;
                Err(Halt::Refusal(refusal))
            }
            NatReductionOutcome::Inconclusive(stop) => {
                let progress = stop.progress();
                self.control.steps = self
                    .control
                    .steps
                    .saturating_add(progress.steps)
                    .saturating_add(progress.whnf_steps)
                    .saturating_add(progress.numeric_steps);
                self.control.reductions = self
                    .control
                    .reductions
                    .saturating_add(progress.whnf_reductions)
                    .saturating_add(progress.numeric_reductions);
                Err(Halt::Stop(Box::new(WhnfStop::NatReduction {
                    at,
                    stop: Box::new(stop),
                    completed_steps: self.control.steps,
                    completed_reductions: self.control.reductions,
                })))
            }
            NatReductionOutcome::InternalFault(fault) => {
                Err(Halt::Fault(WhnfFault::NatReduction {
                    at,
                    fault: Box::new(fault),
                }))
            }
        }
    }

    fn head_action(&self, current: &Cursor) -> Result<HeadAction, Halt> {
        let node = self.node(current)?;
        match node {
            ExprNode::Metadata { expression, .. } => {
                Self::validate_child(current.root, *expression)?;
                Ok(HeadAction::Metadata(*expression))
            }
            ExprNode::Let { value, body, .. } => {
                Self::validate_child(current.root, *value)?;
                Self::validate_child(current.root, *body)?;
                Ok(HeadAction::Let {
                    value: *value,
                    body: *body,
                })
            }
            ExprNode::Free { name } => Ok(HeadAction::Free(
                self.context.free_bindings.get(name).copied(),
            )),
            ExprNode::Constant { .. } => Ok(HeadAction::Constant),
            ExprNode::Apply { .. } => Ok(HeadAction::Apply),
            ExprNode::Projection { expression, .. } => {
                Self::validate_child(current.root, *expression)?;
                Ok(HeadAction::Projection {
                    expression: *expression,
                })
            }
            ExprNode::Bound { .. }
            | ExprNode::Meta { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Lambda { .. }
            | ExprNode::Forall { .. }
            | ExprNode::NatLiteral { .. }
            | ExprNode::StringLiteral(_) => Ok(HeadAction::Stuck),
        }
    }

    fn run(mut self, input: &WireExpr, root: ExprId) -> Result<WhnfResult, Halt> {
        let current = self.materialize_term(input, root, WhnfPhase::Initial)?;
        let Some(memo) = self.context.source.memo() else {
            return self.normalize(current);
        };
        let (delta_mode, budget) = (self.delta_mode, self.control.budget);
        if let Some(result) = memo.recall(&current.arena, delta_mode, &budget) {
            return Ok(result);
        }
        let input = Arc::clone(&current.arena);
        let result = self.normalize(current)?;
        memo.remember(input, delta_mode, budget.materialization, &result);
        Ok(result)
    }

    /// The reduction loop. Out of line so the initial materialization in `run`
    /// executes on a small frame: unoptimized, this loop's frame is about 11 KiB,
    /// and the 64 KiB stack tests reach materialization from inside inference.
    #[inline(never)]
    fn normalize(mut self, mut current: Cursor) -> Result<WhnfResult, Halt> {
        let mut pending_arguments = VecDeque::<Cursor>::new();
        let mut frames = Vec::new();

        'normalize: loop {
            self.control.step(current.root.index(), self.cancelled)?;
            // A shared cursor evaluated eagerly before resumes from its result;
            // evaluated now, its result is recorded (`ReductionFrame::Update`).
            // Other modes stop short of a weak head normal form, so they
            // neither read nor record one. An eager run unfolds whether or not
            // a String expansion forced it, so a recorded result also discharges
            // that force. Only a term with no pending arguments is evaluated
            // on its own: a function position is reduced within its
            // application, as the pin's `whnf_core` reduces a head without
            // delta. Evaluated alone, `Nat.mod` unfolds to its recursion, and
            // `Nat.mod a b` then never reaches the arithmetic its application
            // is offered.
            if let Some(thunk) = current.thunk.take()
                && matches!(self.delta_mode, DeltaMode::Eager)
                && pending_arguments.is_empty()
            {
                // Another term of the same key may already have been evaluated.
                let keyed = match thunk.result.get() {
                    Some(_) => None,
                    None => self
                        .keyed_thunk(&current, &thunk)?
                        .filter(|keyed| !Arc::ptr_eq(keyed, &thunk)),
                };
                let evaluated = thunk
                    .result
                    .get()
                    .or_else(|| keyed.as_ref().and_then(|keyed| keyed.result.get()))
                    .cloned();
                if let Some(value) = evaluated {
                    let _ = thunk.result.set(value.clone());
                    self.force_string_delta = false;
                    let mut arguments = value.args;
                    arguments.append(&mut pending_arguments);
                    pending_arguments = arguments;
                    current = value.head;
                    continue;
                }
                frames.push(ReductionFrame::Update { thunk, keyed });
            }
            match self.head_action(&current)? {
                HeadAction::Metadata(expression) => {
                    self.control
                        .reduction(current.root.index(), self.cancelled)?;
                    current = current.child(expression);
                    continue;
                }
                HeadAction::Let { value, body } => {
                    self.control
                        .reduction(current.root.index(), self.cancelled)?;
                    self.control.step(body.index(), self.cancelled)?;
                    let env = current.env.push(current.child(value).shared());
                    current = Cursor::resolved(Arc::clone(&current.arena), body, env);
                    continue;
                }
                HeadAction::Free(Some(binding)) => {
                    if !self.unfolded_bindings.insert(binding) {
                        return Err(Halt::Refusal(WhnfRefusal::FreeBindingCycle { binding }));
                    }
                    self.control
                        .reduction(current.root.index(), self.cancelled)?;
                    let value =
                        self.context
                            .source
                            .free_bindings
                            .get(binding)
                            .ok_or(Halt::Fault(WhnfFault::MissingExpression {
                                input: 0,
                                index: binding,
                            }))?;
                    self.control
                        .step(value.value.root().index(), self.cancelled)?;
                    let result = copy_subterm_with(
                        &value.value,
                        value.value.root(),
                        self.control.budget.materialization,
                        self.cancelled,
                    );
                    let term = self
                        .control
                        .term_halt(WhnfPhase::FreeBinding { index: binding }, result)?;
                    let root = term.root();
                    current = Cursor::closed(Arc::new(term), root);
                    continue;
                }
                HeadAction::Constant => {
                    let forced = self.force_string_delta;
                    let may_unfold = forced
                        || match self.delta_mode {
                            DeltaMode::Eager => true,
                            DeltaMode::Disabled => false,
                            DeltaMode::Once => self.delta_reductions == 0,
                        };
                    if matches!(self.delta_mode, DeltaMode::Eager)
                        && !std::mem::take(&mut self.skip_nat)
                        && let Some(first) =
                            self.begin_nat(&current, &mut pending_arguments, &mut frames)?
                    {
                        current = first;
                        continue;
                    }
                    if may_unfold && let Some(unfolded) = self.unfold_definition(&current)? {
                        if forced {
                            self.force_string_delta = false;
                        }
                        self.delta_reductions = self.delta_reductions.saturating_add(1);
                        current = unfolded;
                        continue;
                    }
                    // A constant with a collected spine that did not delta-unfold
                    // may be a recursor: iota (KR-316) and the K corner
                    // (KR-317) fire regardless of delta mode — a recursor has
                    // no definition body.
                    if let Some(major) = self.quotient_major(&current, pending_arguments.len())? {
                        let next = pending_arguments[major].clone();
                        frames.push(ReductionFrame::Quotient(quotient::QuotientFrame {
                            head: current,
                            arguments: std::mem::take(&mut pending_arguments),
                            major,
                            delta_mode: self.delta_mode,
                            unfolded_bindings: self.unfolded_bindings.clone(),
                            force_string_delta: self.force_string_delta,
                        }));
                        self.delta_mode = DeltaMode::Eager;
                        self.force_string_delta = false;
                        current = next;
                        continue;
                    }
                    if !pending_arguments.is_empty()
                        && let Some(step) =
                            self.step_recursor_reduction(&current, &mut pending_arguments)?
                    {
                        match step {
                            RecursorStep::Reduced(reduced) => {
                                current = reduced.head;
                                pending_arguments = reduced.args;
                                continue;
                            }
                            RecursorStep::NormalizeMajor { frame, major } => {
                                frames.push(ReductionFrame::Recursor(frame));
                                self.delta_mode = DeltaMode::Eager;
                                self.force_string_delta = false;
                                current = major;
                                continue;
                            }
                        }
                    }
                }
                HeadAction::Apply => {
                    let (head, mut arguments) = self.peel_application(&current)?;
                    arguments.append(&mut pending_arguments);
                    pending_arguments = arguments;
                    current = head;
                    continue;
                }
                HeadAction::Projection { expression } => {
                    frames.push(ReductionFrame::Projection(ProjectionFrame {
                        projection: current.clone(),
                        outer_arguments: std::mem::take(&mut pending_arguments),
                    }));
                    current = current.child(expression).shared();
                    continue;
                }
                HeadAction::Stuck => {
                    let expanded = {
                        let value = match self.node(&current)? {
                            ExprNode::StringLiteral(value) => Some(value.as_str()),
                            _ => None,
                        };
                        match (value, frames.last()) {
                            (Some(value), Some(ReductionFrame::Projection(frame)))
                                if self.projection_requests_string(frame)? =>
                            {
                                Some(self.expand_string(value, current.root.index())?)
                            }
                            _ => None,
                        }
                    };
                    if let Some(expanded) = expanded {
                        current = expanded;
                        self.force_string_delta = true;
                        continue;
                    }
                }
                HeadAction::Free(None) => {}
            }

            if !pending_arguments.is_empty()
                && matches!(self.node(&current)?, ExprNode::Lambda { .. })
            {
                self.control
                    .reduction(current.root.index(), self.cancelled)?;
                while let Some(argument) = pending_arguments.pop_front() {
                    let body = match self.node(&current)? {
                        ExprNode::Lambda { body, .. } => *body,
                        _ => {
                            pending_arguments.push_front(argument);
                            break;
                        }
                    };
                    Self::validate_child(current.root, body)?;
                    self.control.step(body.index(), self.cancelled)?;
                    let env = current.env.push(argument);
                    current = Cursor::resolved(Arc::clone(&current.arena), body, env);
                }
                continue 'normalize;
            }

            // `current` applied to the pending arguments is stuck. It stays a
            // spine for the frame that demanded it; only a term that cannot be
            // taken apart is built.
            let stuck = Spine {
                head: current,
                args: std::mem::take(&mut pending_arguments),
            };
            match self.resume(stuck, &mut frames)? {
                Resumed::Continue(next) => {
                    current = next.head;
                    pending_arguments = next.args;
                }
                Resumed::Stuck(stuck) => return self.finish(stuck),
            }
        }
    }

    /// Hand a stuck term to the frames that demanded it, innermost first. A
    /// frame that reduces continues normalization; otherwise the term is stuck
    /// for good. Out of line, as `normalize` is, to keep that loop's frame small.
    #[inline(never)]
    fn resume(
        &mut self,
        mut stuck: Spine,
        frames: &mut Vec<ReductionFrame>,
    ) -> Result<Resumed, Halt> {
        while let Some(frame) = frames.pop() {
            let frame = match frame {
                ReductionFrame::Update { thunk, keyed } => {
                    let _ = thunk.result.set(stuck.clone());
                    if let Some(keyed) = keyed {
                        let _ = keyed.result.set(stuck.clone());
                    }
                    continue;
                }
                ReductionFrame::Nat(mut frame) => {
                    self.delta_mode = frame.delta_mode;
                    self.unfolded_bindings = frame.unfolded_bindings.clone();
                    self.force_string_delta = frame.force_string_delta;
                    let value = if stuck.args.is_empty() {
                        crate::nat_reduce::natural_of(self.node(&stuck.head)?).map_err(|()| {
                            Halt::Fault(WhnfFault::NonCanonicalNatLiteral {
                                at: stuck.head.root.index(),
                            })
                        })?
                    } else {
                        None
                    };
                    if let Some(value) = value {
                        frame.values.push(value);
                        let arity = usize::from(frame.operation.arity());
                        if frame.values.len() < arity {
                            let next = frame.arguments[frame.values.len()].clone();
                            self.delta_mode = DeltaMode::Eager;
                            self.force_string_delta = false;
                            frames.push(ReductionFrame::Nat(frame));
                            return Ok(Resumed::Continue(Spine {
                                head: next,
                                args: VecDeque::new(),
                            }));
                        }
                        if let Some(result) = self.execute_nat(&frame)? {
                            self.force_string_delta = false;
                            self.delta_reductions = self.delta_reductions.saturating_add(1);
                            let args = frame.arguments.split_off(arity);
                            return Ok(Resumed::Continue(Spine { head: result, args }));
                        }
                    }
                    // Declined, as when the pin's `reduce_nat` returns none:
                    // the operation unfolds, on the arguments it was given.
                    self.skip_nat = true;
                    self.has_auxiliary_work = true;
                    return Ok(Resumed::Continue(Spine {
                        head: frame.head,
                        args: frame.arguments,
                    }));
                }
                ReductionFrame::Projection(frame) => frame,
                ReductionFrame::Quotient(mut frame) => {
                    self.delta_mode = frame.delta_mode;
                    self.unfolded_bindings = frame.unfolded_bindings;
                    self.force_string_delta = frame.force_string_delta;
                    let major = self.build_spine(stuck)?;
                    if let Some(representative) =
                        self.quotient_representative(&frame.head, &major)?
                    {
                        self.control
                            .reduction(frame.head.root.index(), self.cancelled)?;
                        let function = frame.arguments[3].clone();
                        let mut args = frame.arguments.split_off(frame.major + 1);
                        args.push_front(representative);
                        return Ok(Resumed::Continue(Spine {
                            head: function,
                            args,
                        }));
                    }
                    // Preserve progress within a blocked major, but do not
                    // re-enter the same unchanged eliminator in a loop.
                    frame.arguments[frame.major] = major;
                    stuck = Spine {
                        head: frame.head,
                        args: frame.arguments,
                    };
                    continue;
                }
                ReductionFrame::Recursor(mut frame) => {
                    self.delta_mode = frame.delta_mode;
                    self.unfolded_bindings = frame.unfolded_bindings;
                    self.force_string_delta = frame.force_string_delta;

                    let reduced_major = self.reduce_demanded_nat_spine(stuck)?;
                    if let Some(reduced) = self.apply_recursor_rule(
                        &frame.metadata,
                        &frame.level_parameters,
                        &frame.head,
                        &frame.levels,
                        &frame.arguments,
                        frame.major_index,
                        &reduced_major,
                        frame.prefix,
                    )? {
                        return Ok(Resumed::Continue(reduced));
                    }
                    // The K and structure-eta conversions read the major as
                    // one term, from the spine.
                    let reduced_major = self.build_spine(reduced_major)?;
                    let original_major =
                        std::mem::replace(&mut frame.arguments[frame.major_index], reduced_major);

                    let mut alt_major = None;
                    if frame.metadata.k() {
                        if let Some(replacement) = self.recursor_major_to_nullary_constructor(
                            &frame.level_parameters,
                            &frame.recursor_type,
                            &frame.head,
                            &frame.levels,
                            &frame.arguments,
                            frame.major_index,
                            frame.parameter_count,
                        )? {
                            alt_major = Some(replacement);
                        }
                    } else if let Some(replacement) = self.recursor_major_to_structure_constructor(
                        &frame.level_parameters,
                        &frame.recursor_type,
                        &frame.head,
                        &frame.levels,
                        &frame.arguments,
                        frame.major_index,
                    )? {
                        alt_major = Some(replacement);
                    }

                    if let Some(alt_major) = alt_major {
                        let (head, args) = self.peel_application(&alt_major)?;
                        if let Some(reduced) = self.apply_recursor_rule(
                            &frame.metadata,
                            &frame.level_parameters,
                            &frame.head,
                            &frame.levels,
                            &frame.arguments,
                            frame.major_index,
                            &Spine { head, args },
                            frame.prefix,
                        )? {
                            return Ok(Resumed::Continue(reduced));
                        }
                    }

                    // No rule fires: the application is stuck, and it is
                    // returned with the major it had, as the pin's
                    // `whnf_core` returns `e` when `reduce_recursor`
                    // fails. The normalized major is not kept in the
                    // result: it can be far larger than the major it came
                    // from (`Int32.toBitVec_div` grew 179 nodes into
                    // 74,901 in one whnf), and every later comparison paid
                    // for it. Work that needs the major normalizes it
                    // again, as at the pin. The reductions spent on the
                    // major changed nothing in the result, so they are not
                    // reported as progress (the budget still counts them):
                    // callers read a nonzero count as change, and would
                    // resubmit the same term forever.
                    frame.arguments[frame.major_index] = original_major;
                    let mark = frame.progress;
                    self.discarded_reductions = mark
                        .discarded_reductions
                        .saturating_add(self.control.reductions.saturating_sub(mark.reductions));
                    self.discarded_delta_reductions =
                        mark.discarded_delta_reductions.saturating_add(
                            self.delta_reductions.saturating_sub(mark.delta_reductions),
                        );
                    stuck = Spine {
                        head: frame.head,
                        args: frame.arguments,
                    };
                    continue;
                }
            };
            if let Some(field) = self.projection_field(&frame, &stuck)? {
                self.control
                    .reduction(frame.projection.root.index(), self.cancelled)?;
                return Ok(Resumed::Continue(Spine {
                    head: field,
                    args: frame.outer_arguments,
                }));
            }
            let expression = self.build_spine(stuck)?;
            stuck = Spine {
                head: self.compose_projection(&frame.projection, &expression)?,
                args: frame.outer_arguments,
            };
        }
        Ok(Resumed::Stuck(stuck))
    }

    /// The weak head normal form, built as one arena.
    #[inline(never)]
    fn finish(&mut self, stuck: Spine) -> Result<WhnfResult, Halt> {
        let current = self.build_spine(stuck)?;
        let term = if current.env.is_empty() {
            self.materialize_wire(&current.arena, current.root, WhnfPhase::Final)?
        } else {
            self.close(&current, WhnfPhase::Final)?
        };
        Ok(WhnfResult {
            term,
            steps: self.control.steps,
            reductions: self
                .control
                .reductions
                .saturating_sub(self.discarded_reductions),
            delta_reductions: self
                .delta_reductions
                .saturating_sub(self.discarded_delta_reductions),
            has_auxiliary_work: self.has_auxiliary_work,
            string_progress: self.string_progress,
        })
    }
}

/// What the frames make of a stuck term.
enum Resumed {
    /// A frame reduced: normalize this next.
    Continue(Spine),
    /// Every frame is done and the term is stuck.
    Stuck(Spine),
}

enum ComposeHalt {
    Stop(TermStop),
    Fault(WhnfFault),
}

struct Materialization<'c> {
    budget: TermBudget,
    steps: u64,
    output_units: u64,
    polls: u64,
    cancelled: &'c mut dyn FnMut() -> bool,
}

impl<'c> Materialization<'c> {
    fn new(budget: TermBudget, cancelled: &'c mut dyn FnMut() -> bool) -> Materialization<'c> {
        Materialization {
            budget,
            steps: 0,
            output_units: 0,
            polls: 0,
            cancelled,
        }
    }

    fn poll(&mut self, at: usize) -> Result<(), ComposeHalt> {
        self.polls = self.polls.saturating_add(1);
        if (self.cancelled)() {
            return Err(ComposeHalt::Stop(TermStop::Cancelled {
                at,
                polls: self.polls,
                completed_steps: self.steps,
            }));
        }
        Ok(())
    }

    fn step(&mut self, at: usize) -> Result<(), ComposeHalt> {
        self.poll(at)?;
        let observed = self.steps.saturating_add(1);
        if observed > self.budget.max_steps {
            return Err(ComposeHalt::Stop(TermStop::Resource {
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

    fn output(&mut self, units: u64, at: usize) -> Result<(), ComposeHalt> {
        self.poll(at)?;
        let observed = self.output_units.saturating_add(units);
        if observed > self.budget.max_output_units {
            return Err(ComposeHalt::Stop(TermStop::Resource {
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

    fn admit_arena_node(&self, observed: u64, at: usize) -> Result<(), ComposeHalt> {
        let allowed = self.budget.max_arena_nodes.min(u64::from(u32::MAX));
        if observed > allowed {
            return Err(ComposeHalt::Stop(TermStop::Resource {
                limit: TermLimit::ArenaNodes,
                allowed,
                observed,
                at,
                completed_steps: self.steps,
            }));
        }
        Ok(())
    }
}

struct Composer<'c> {
    control: Materialization<'c>,
    phase: WhnfPhase,
    outer_steps: u64,
    outer_reductions: u64,
    levels: Vec<LevelNode>,
    expressions: Vec<ExprNode>,
    sources: Vec<SourceCopy>,
    /// `sources` by arena address.
    source_lookup: std::collections::HashMap<usize, usize>,
    /// Environment copies, shared by every cursor this composer copies: one
    /// closure reached from two arguments is copied once.
    open_contexts: OpenContexts,
    open_memo: std::collections::HashMap<OpenKey, ExprId>,
    shared_levels: sharing::Interned,
    shared_expressions: sharing::Interned,
}

struct SourceCopy {
    arena: Arc<WireExpr>,
    levels: Vec<Option<LevelId>>,
    expressions: Vec<Option<ExprId>>,
    /// Loose bound-variable range of each node reached by an environment copy:
    /// a node below that many binders is closed there, so its copy is the plain
    /// one whatever the environment.
    loose: std::collections::HashMap<usize, u32>,
}

/// One node of an environment copy: `node` of `context`'s arena, at `depth`
/// binders inside the copied term, which sits under `shift` further binders.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct OpenKey {
    context: usize,
    node: usize,
    depth: u32,
    shift: u32,
}

enum OpenWork {
    Visit(OpenKey),
    Build(OpenKey),
    /// `key` is a bound variable whose value's copy is `value`.
    Alias {
        key: OpenKey,
        value: OpenKey,
    },
}

/// The (source, environment) pairs an environment copy has met. Each entry
/// holds its environment, so an environment's identity stays unique while the
/// copy runs.
#[derive(Default)]
struct OpenContexts {
    list: Vec<(usize, Env)>,
    lookup: std::collections::HashMap<(usize, usize), usize>,
}

impl OpenContexts {
    fn of(&mut self, source: usize, env: &Env) -> usize {
        let list = &mut self.list;
        *self
            .lookup
            .entry((source, env.identity()))
            .or_insert_with(|| {
                list.push((source, env.clone()));
                list.len() - 1
            })
    }
}

/// The children of a node, each with the binders it sits under.
fn expression_children(node: &ExprNode) -> [Option<(ExprId, u32)>; 3] {
    match node {
        ExprNode::Apply { function, argument } => {
            [Some((*function, 0)), Some((*argument, 0)), None]
        }
        ExprNode::Lambda {
            binder_type, body, ..
        }
        | ExprNode::Forall {
            binder_type, body, ..
        } => [Some((*binder_type, 0)), Some((*body, 1)), None],
        ExprNode::Let {
            type_, value, body, ..
        } => [Some((*type_, 0)), Some((*value, 0)), Some((*body, 1))],
        ExprNode::Metadata { expression, .. } | ExprNode::Projection { expression, .. } => {
            [Some((*expression, 0)), None, None]
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

impl<'c> Composer<'c> {
    fn new(
        budget: TermBudget,
        phase: WhnfPhase,
        outer_steps: u64,
        outer_reductions: u64,
        cancelled: &'c mut dyn FnMut() -> bool,
    ) -> Composer<'c> {
        Composer {
            control: Materialization::new(budget, cancelled),
            phase,
            outer_steps,
            outer_reductions,
            levels: Vec::new(),
            expressions: Vec::new(),
            sources: Vec::new(),
            source_lookup: std::collections::HashMap::new(),
            open_contexts: OpenContexts::default(),
            open_memo: std::collections::HashMap::new(),
            shared_levels: sharing::Interned::default(),
            shared_expressions: sharing::Interned::default(),
        }
    }

    fn prior_level(
        mapping: &[Option<LevelId>],
        input: usize,
        parent: usize,
        child: LevelId,
    ) -> Result<LevelId, ComposeHalt> {
        if child.index() >= parent {
            return Err(ComposeHalt::Fault(WhnfFault::NonBackwardLevelReference {
                input,
                parent,
                child: child.index(),
            }));
        }
        mapping
            .get(child.index())
            .copied()
            .flatten()
            .ok_or(ComposeHalt::Fault(WhnfFault::MissingLevel {
                input,
                index: child.index(),
            }))
    }

    fn prior_expression(
        mapping: &[Option<ExprId>],
        input: usize,
        parent: usize,
        child: ExprId,
    ) -> Result<ExprId, ComposeHalt> {
        if child.index() >= parent {
            return Err(ComposeHalt::Fault(
                WhnfFault::NonBackwardExpressionReference {
                    input,
                    parent,
                    child: child.index(),
                },
            ));
        }
        mapping
            .get(child.index())
            .copied()
            .flatten()
            .ok_or(ComposeHalt::Fault(WhnfFault::MissingExpression {
                input,
                index: child.index(),
            }))
    }

    fn push_level(
        &mut self,
        node: LevelNode,
        at: usize,
        source: usize,
    ) -> Result<LevelId, ComposeHalt> {
        let hash = sharing::fingerprint(&node);
        if let Some(id) = self
            .shared_levels
            .find(hash, &node, &self.levels, source)
            .and_then(LevelId::from_index)
        {
            return Ok(id);
        }
        let observed = usize_units(self.levels.len()).saturating_add(1);
        self.control.admit_arena_node(observed, at)?;
        let id = LevelId::from_index(self.levels.len()).ok_or(ComposeHalt::Stop(
            TermStop::Resource {
                limit: TermLimit::ArenaNodes,
                allowed: u64::from(u32::MAX),
                observed,
                at,
                completed_steps: self.control.steps,
            },
        ))?;
        self.levels.push(node);
        self.shared_levels.record(hash, id.index(), source);
        Ok(id)
    }

    fn push_expression(&mut self, node: ExprNode, units: u64, at: usize) -> Result<ExprId, Halt> {
        self.control.step(at).map_err(|halt| self.map_halt(halt))?;
        self.control
            .output(units, at)
            .map_err(|halt| self.map_halt(halt))?;
        self.push_expression_charged(node, at, None)
            .map_err(|halt| self.map_halt(halt))
    }

    fn push_expression_charged(
        &mut self,
        node: ExprNode,
        at: usize,
        source: Option<usize>,
    ) -> Result<ExprId, ComposeHalt> {
        // Child IDs and universe IDs have already been mapped into this output
        // arena. Equality here is exact syntax equality, including every name,
        // binder style and metadata value; it is not a conversion judgment.
        // The payload was charged before cloning, even on a sharing hit.
        let hash = sharing::fingerprint(&node);
        if let Some(id) = source
            .and_then(|source| {
                self.shared_expressions
                    .find(hash, &node, &self.expressions, source)
            })
            .and_then(ExprId::from_index)
        {
            return Ok(id);
        }
        let observed = usize_units(self.expressions.len()).saturating_add(1);
        self.control.admit_arena_node(observed, at)?;
        let id = ExprId::from_index(self.expressions.len()).ok_or(ComposeHalt::Stop(
            TermStop::Resource {
                limit: TermLimit::ArenaNodes,
                allowed: u64::from(u32::MAX),
                observed,
                at,
                completed_steps: self.control.steps,
            },
        ))?;
        self.expressions.push(node);
        if let Some(source) = source {
            self.shared_expressions.record(hash, id.index(), source);
        }
        Ok(id)
    }

    fn source_index(&mut self, arena: &Arc<WireExpr>) -> usize {
        // Every source is held in `sources`, so its address stays unique here.
        let address = Arc::as_ptr(arena).addr();
        if let Some(index) = self.source_lookup.get(&address) {
            return *index;
        }
        let index = self.sources.len();
        self.sources.push(SourceCopy {
            arena: Arc::clone(arena),
            levels: vec![None; arena.levels().len()],
            expressions: vec![None; arena.nodes().len()],
            loose: std::collections::HashMap::new(),
        });
        self.source_lookup.insert(address, index);
        index
    }

    /// The loose bound-variable range of `root` in `source`: the least number
    /// of binders under which it is closed.
    fn loose_range(&mut self, source: usize, root: ExprId, input: usize) -> Result<u32, Halt> {
        if let Some(range) = self.sources[source].loose.get(&root.index()) {
            return Ok(*range);
        }
        let arena = Arc::clone(&self.sources[source].arena);
        let mut work = vec![(root, false)];
        while let Some((id, built)) = work.pop() {
            let index = id.index();
            if self.sources[source].loose.contains_key(&index) {
                continue;
            }
            let node = arena
                .node(id)
                .ok_or(Halt::Fault(WhnfFault::MissingExpression { input, index }))?;
            let children = expression_children(node);
            if !built {
                self.control
                    .step(index)
                    .map_err(|halt| self.map_halt(halt))?;
                work.push((id, true));
                for (child, _) in children.into_iter().flatten() {
                    if child.index() >= index {
                        return Err(Halt::Fault(WhnfFault::NonBackwardExpressionReference {
                            input,
                            parent: index,
                            child: child.index(),
                        }));
                    }
                    work.push((child, false));
                }
                continue;
            }
            let loose = &self.sources[source].loose;
            let mut range = match node {
                ExprNode::Bound { index } => index.saturating_add(1),
                _ => 0,
            };
            for (child, binders) in children.into_iter().flatten() {
                let child_range = loose.get(&child.index()).copied().unwrap_or(0);
                range = range.max(child_range.saturating_sub(binders));
            }
            self.sources[source].loose.insert(index, range);
        }
        Ok(self.sources[source]
            .loose
            .get(&root.index())
            .copied()
            .unwrap_or(0))
    }

    /// Copy a cursor's term with its environment substituted. A loose index
    /// bound by the environment becomes a copy of its value, lifted over the
    /// binders it now sits under; a loose index past the environment becomes
    /// the run's own index, below the environment. Work is iterative: values
    /// nest through their own environments as deeply as a computation ran.
    fn copy_open(&mut self, cursor: &Cursor, input: usize) -> Result<ExprId, Halt> {
        let mut contexts = std::mem::take(&mut self.open_contexts);
        let mut memo = std::mem::take(&mut self.open_memo);
        let copied = self.copy_open_with(cursor, input, &mut contexts, &mut memo);
        self.open_contexts = contexts;
        self.open_memo = memo;
        copied
    }

    fn copy_open_with(
        &mut self,
        cursor: &Cursor,
        input: usize,
        contexts: &mut OpenContexts,
        memo: &mut std::collections::HashMap<OpenKey, ExprId>,
    ) -> Result<ExprId, Halt> {
        let root = OpenKey {
            context: contexts.of(self.source_index(&cursor.arena), &cursor.env),
            node: cursor.root.index(),
            depth: 0,
            shift: 0,
        };
        let mut work = vec![OpenWork::Visit(root)];
        while let Some(item) = work.pop() {
            match item {
                OpenWork::Visit(key) => {
                    if memo.contains_key(&key) {
                        continue;
                    }
                    let (source, env) = contexts.list[key.context].clone();
                    let id = ExprId::from_index(key.node).ok_or(Halt::Fault(
                        WhnfFault::MissingExpression {
                            input,
                            index: key.node,
                        },
                    ))?;
                    if self.loose_range(source, id, input)? <= key.depth {
                        // Closed where it sits: the plain copy, shared by every
                        // environment and depth that reaches it.
                        let arena = Arc::clone(&self.sources[source].arena);
                        let copied = self.copy_plain(&Cursor::closed(arena, id), input)?;
                        memo.insert(key, copied);
                        continue;
                    }
                    self.control
                        .step(key.node)
                        .map_err(|halt| self.map_halt(halt))?;
                    let arena = Arc::clone(&self.sources[source].arena);
                    let node = arena
                        .node(id)
                        .ok_or(Halt::Fault(WhnfFault::MissingExpression {
                            input,
                            index: key.node,
                        }))?;
                    if let ExprNode::Bound { index } = node {
                        // Not closed here, so the index reaches past `depth`.
                        let outer = index.saturating_sub(key.depth);
                        if let Some(value) = env.get(outer) {
                            let value = OpenKey {
                                context: contexts.of(self.source_index(&value.arena), &value.env),
                                node: value.root.index(),
                                depth: 0,
                                shift: key.shift.saturating_add(key.depth),
                            };
                            work.push(OpenWork::Alias { key, value });
                            work.push(OpenWork::Visit(value));
                            continue;
                        }
                        let lowered = u64::from(outer) - u64::from(env.len())
                            + u64::from(key.depth)
                            + u64::from(key.shift);
                        let index = u32::try_from(lowered).map_err(|_| {
                            self.map_halt(ComposeHalt::Stop(TermStop::Resource {
                                limit: TermLimit::BoundIndex,
                                allowed: u64::from(u32::MAX),
                                observed: lowered,
                                at: key.node,
                                completed_steps: self.control.steps,
                            }))
                        })?;
                        self.control
                            .output(1, key.node)
                            .map_err(|halt| self.map_halt(halt))?;
                        let copied = self
                            .push_expression_charged(ExprNode::Bound { index }, key.node, None)
                            .map_err(|halt| self.map_halt(halt))?;
                        memo.insert(key, copied);
                        continue;
                    }
                    work.push(OpenWork::Build(key));
                    for (child, binders) in expression_children(node).into_iter().flatten() {
                        if child.index() >= key.node {
                            return Err(Halt::Fault(WhnfFault::NonBackwardExpressionReference {
                                input,
                                parent: key.node,
                                child: child.index(),
                            }));
                        }
                        work.push(OpenWork::Visit(OpenKey {
                            node: child.index(),
                            depth: key.depth.saturating_add(binders),
                            ..key
                        }));
                    }
                }
                OpenWork::Alias { key, value } => {
                    let copied =
                        *memo
                            .get(&value)
                            .ok_or(Halt::Fault(WhnfFault::MissingExpression {
                                input,
                                index: value.node,
                            }))?;
                    memo.insert(key, copied);
                }
                OpenWork::Build(key) => {
                    let source = contexts.list[key.context].0;
                    let arena = Arc::clone(&self.sources[source].arena);
                    let node = ExprId::from_index(key.node)
                        .and_then(|id| arena.node(id))
                        .ok_or(Halt::Fault(WhnfFault::MissingExpression {
                            input,
                            index: key.node,
                        }))?;
                    self.control
                        .output(expression_owned_units(node), key.node)
                        .map_err(|halt| self.map_halt(halt))?;
                    let child = |child: &ExprId, binders: u32| -> Result<ExprId, Halt> {
                        memo.get(&OpenKey {
                            node: child.index(),
                            depth: key.depth.saturating_add(binders),
                            ..key
                        })
                        .copied()
                        .ok_or(Halt::Fault(
                            WhnfFault::MissingExpression {
                                input,
                                index: child.index(),
                            },
                        ))
                    };
                    let mapped = match node {
                        ExprNode::Apply { function, argument } => ExprNode::Apply {
                            function: child(function, 0)?,
                            argument: child(argument, 0)?,
                        },
                        ExprNode::Lambda {
                            binder_name,
                            binder_type,
                            body,
                            style,
                        } => ExprNode::Lambda {
                            binder_name: binder_name.clone(),
                            binder_type: child(binder_type, 0)?,
                            body: child(body, 1)?,
                            style: *style,
                        },
                        ExprNode::Forall {
                            binder_name,
                            binder_type,
                            body,
                            style,
                        } => ExprNode::Forall {
                            binder_name: binder_name.clone(),
                            binder_type: child(binder_type, 0)?,
                            body: child(body, 1)?,
                            style: *style,
                        },
                        ExprNode::Let {
                            declaration_name,
                            type_,
                            value,
                            body,
                            non_dependent,
                        } => ExprNode::Let {
                            declaration_name: declaration_name.clone(),
                            type_: child(type_, 0)?,
                            value: child(value, 0)?,
                            body: child(body, 1)?,
                            non_dependent: *non_dependent,
                        },
                        ExprNode::Metadata {
                            entries,
                            expression,
                        } => ExprNode::Metadata {
                            entries: entries.clone(),
                            expression: child(expression, 0)?,
                        },
                        ExprNode::Projection {
                            structure_name,
                            index,
                            expression,
                        } => ExprNode::Projection {
                            structure_name: structure_name.clone(),
                            index: *index,
                            expression: child(expression, 0)?,
                        },
                        // Leaves have no loose index, so they took the plain copy.
                        _ => {
                            return Err(Halt::Fault(WhnfFault::MissingExpression {
                                input,
                                index: key.node,
                            }));
                        }
                    };
                    let copied = self
                        .push_expression_charged(mapped, key.node, None)
                        .map_err(|halt| self.map_halt(halt))?;
                    memo.insert(key, copied);
                }
            }
        }
        memo.get(&root)
            .copied()
            .ok_or(Halt::Fault(WhnfFault::MissingExpression {
                input,
                index: cursor.root.index(),
            }))
    }

    fn copy_level_root(
        &mut self,
        source_index: usize,
        root: LevelId,
        input: usize,
    ) -> Result<LevelId, Halt> {
        let source = Arc::clone(&self.sources[source_index].arena);
        let mut work = vec![(root, false)];
        while let Some((level_id, built)) = work.pop() {
            let index = level_id.index();
            if self.sources[source_index]
                .levels
                .get(index)
                .copied()
                .flatten()
                .is_some()
            {
                continue;
            }
            let node = source
                .levels()
                .get(index)
                .ok_or(Halt::Fault(WhnfFault::MissingLevel { input, index }))?;
            if !built {
                self.control
                    .step(index)
                    .map_err(|halt| self.map_halt(halt))?;
                work.push((level_id, true));
                match node {
                    LevelNode::Succ(child) => {
                        if child.index() >= index {
                            return Err(Halt::Fault(WhnfFault::NonBackwardLevelReference {
                                input,
                                parent: index,
                                child: child.index(),
                            }));
                        }
                        work.push((*child, false));
                    }
                    LevelNode::Max(left, right) | LevelNode::IMax(left, right) => {
                        for child in [right, left] {
                            if child.index() >= index {
                                return Err(Halt::Fault(WhnfFault::NonBackwardLevelReference {
                                    input,
                                    parent: index,
                                    child: child.index(),
                                }));
                            }
                            work.push((*child, false));
                        }
                    }
                    LevelNode::Zero | LevelNode::Parameter(_) | LevelNode::Meta(_) => {}
                }
                continue;
            }
            self.control
                .output(level_owned_units(node), index)
                .map_err(|halt| self.map_halt(halt))?;
            let mapping = &self.sources[source_index].levels;
            let mapped = match node {
                LevelNode::Zero => LevelNode::Zero,
                LevelNode::Succ(child) => LevelNode::Succ(
                    Self::prior_level(mapping, input, index, *child)
                        .map_err(|halt| self.map_halt(halt))?,
                ),
                LevelNode::Max(left, right) => LevelNode::Max(
                    Self::prior_level(mapping, input, index, *left)
                        .map_err(|halt| self.map_halt(halt))?,
                    Self::prior_level(mapping, input, index, *right)
                        .map_err(|halt| self.map_halt(halt))?,
                ),
                LevelNode::IMax(left, right) => LevelNode::IMax(
                    Self::prior_level(mapping, input, index, *left)
                        .map_err(|halt| self.map_halt(halt))?,
                    Self::prior_level(mapping, input, index, *right)
                        .map_err(|halt| self.map_halt(halt))?,
                ),
                LevelNode::Parameter(name) => LevelNode::Parameter(name.clone()),
                LevelNode::Meta(name) => LevelNode::Meta(name.clone()),
            };
            let copied = self
                .push_level(mapped, index, source_index)
                .map_err(|halt| self.map_halt(halt))?;
            self.sources[source_index].levels[index] = Some(copied);
        }
        self.sources[source_index]
            .levels
            .get(root.index())
            .copied()
            .flatten()
            .ok_or(Halt::Fault(WhnfFault::MissingLevel {
                input,
                index: root.index(),
            }))
    }

    /// Copy a cursor's term into this arena with its environment substituted.
    fn copy_cursor(&mut self, cursor: &Cursor, input: usize) -> Result<ExprId, Halt> {
        if cursor.env.is_empty() {
            return self.copy_plain(cursor, input);
        }
        self.copy_open(cursor, input)
    }

    /// Copy a subterm as written: loose indices stay as they are.
    fn copy_plain(&mut self, cursor: &Cursor, input: usize) -> Result<ExprId, Halt> {
        let source_index = self.source_index(&cursor.arena);
        let source = Arc::clone(&self.sources[source_index].arena);
        let mut work = vec![(cursor.root, false)];
        while let Some((expression_id, built)) = work.pop() {
            let index = expression_id.index();
            if self.sources[source_index]
                .expressions
                .get(index)
                .copied()
                .flatten()
                .is_some()
            {
                continue;
            }
            let node = source
                .node(expression_id)
                .ok_or(Halt::Fault(WhnfFault::MissingExpression { input, index }))?;
            if !built {
                self.control
                    .step(index)
                    .map_err(|halt| self.map_halt(halt))?;
                work.push((expression_id, true));
                let mut push_child = |child: ExprId| -> Result<(), Halt> {
                    if child.index() >= index {
                        return Err(Halt::Fault(WhnfFault::NonBackwardExpressionReference {
                            input,
                            parent: index,
                            child: child.index(),
                        }));
                    }
                    work.push((child, false));
                    Ok(())
                };
                match node {
                    ExprNode::Apply { function, argument } => {
                        push_child(*argument)?;
                        push_child(*function)?;
                    }
                    ExprNode::Lambda {
                        binder_type, body, ..
                    }
                    | ExprNode::Forall {
                        binder_type, body, ..
                    } => {
                        push_child(*body)?;
                        push_child(*binder_type)?;
                    }
                    ExprNode::Let {
                        type_, value, body, ..
                    } => {
                        push_child(*body)?;
                        push_child(*value)?;
                        push_child(*type_)?;
                    }
                    ExprNode::Metadata { expression, .. }
                    | ExprNode::Projection { expression, .. } => {
                        push_child(*expression)?;
                    }
                    ExprNode::Bound { .. }
                    | ExprNode::Free { .. }
                    | ExprNode::Meta { .. }
                    | ExprNode::Sort { .. }
                    | ExprNode::Constant { .. }
                    | ExprNode::NatLiteral { .. }
                    | ExprNode::StringLiteral(_) => {}
                }
                continue;
            }
            self.control
                .output(expression_owned_units(node), index)
                .map_err(|halt| self.map_halt(halt))?;
            let expression_mapping = &self.sources[source_index].expressions;
            let map_expr = |child| Self::prior_expression(expression_mapping, input, index, child);
            let mapped = match node {
                ExprNode::Bound { index } => ExprNode::Bound { index: *index },
                ExprNode::Free { name } => ExprNode::Free { name: name.clone() },
                ExprNode::Meta { name } => ExprNode::Meta { name: name.clone() },
                ExprNode::Sort { level } => ExprNode::Sort {
                    level: self.copy_level_root(source_index, *level, input)?,
                },
                ExprNode::Constant { name, levels } => {
                    let mut mapped_levels = Vec::new();
                    for level in levels {
                        mapped_levels.push(self.copy_level_root(source_index, *level, input)?);
                    }
                    ExprNode::Constant {
                        name: name.clone(),
                        levels: mapped_levels,
                    }
                }
                ExprNode::Apply { function, argument } => ExprNode::Apply {
                    function: map_expr(*function).map_err(|halt| self.map_halt(halt))?,
                    argument: map_expr(*argument).map_err(|halt| self.map_halt(halt))?,
                },
                ExprNode::Lambda {
                    binder_name,
                    binder_type,
                    body,
                    style,
                } => ExprNode::Lambda {
                    binder_name: binder_name.clone(),
                    binder_type: map_expr(*binder_type).map_err(|halt| self.map_halt(halt))?,
                    body: map_expr(*body).map_err(|halt| self.map_halt(halt))?,
                    style: *style,
                },
                ExprNode::Forall {
                    binder_name,
                    binder_type,
                    body,
                    style,
                } => ExprNode::Forall {
                    binder_name: binder_name.clone(),
                    binder_type: map_expr(*binder_type).map_err(|halt| self.map_halt(halt))?,
                    body: map_expr(*body).map_err(|halt| self.map_halt(halt))?,
                    style: *style,
                },
                ExprNode::Let {
                    declaration_name,
                    type_,
                    value,
                    body,
                    non_dependent,
                } => ExprNode::Let {
                    declaration_name: declaration_name.clone(),
                    type_: map_expr(*type_).map_err(|halt| self.map_halt(halt))?,
                    value: map_expr(*value).map_err(|halt| self.map_halt(halt))?,
                    body: map_expr(*body).map_err(|halt| self.map_halt(halt))?,
                    non_dependent: *non_dependent,
                },
                ExprNode::NatLiteral { limbs_le } => ExprNode::NatLiteral {
                    limbs_le: limbs_le.clone(),
                },
                ExprNode::StringLiteral(value) => ExprNode::StringLiteral(value.clone()),
                ExprNode::Metadata {
                    entries,
                    expression,
                } => ExprNode::Metadata {
                    entries: entries.clone(),
                    expression: map_expr(*expression).map_err(|halt| self.map_halt(halt))?,
                },
                ExprNode::Projection {
                    structure_name,
                    index,
                    expression,
                } => ExprNode::Projection {
                    structure_name: structure_name.clone(),
                    index: *index,
                    expression: map_expr(*expression).map_err(|halt| self.map_halt(halt))?,
                },
            };
            let id = self
                .push_expression_charged(mapped, index, Some(source_index))
                .map_err(|halt| self.map_halt(halt))?;
            self.sources[source_index].expressions[index] = Some(id);
        }

        self.sources[source_index]
            .expressions
            .get(cursor.root.index())
            .copied()
            .flatten()
            .ok_or(Halt::Fault(WhnfFault::MissingExpression {
                input,
                index: cursor.root.index(),
            }))
    }

    fn map_halt(&self, halt: ComposeHalt) -> Halt {
        match halt {
            ComposeHalt::Stop(stop) => Halt::Stop(Box::new(WhnfStop::Materialization {
                phase: self.phase,
                stop,
                completed_steps: self.outer_steps,
                completed_reductions: self.outer_reductions,
            })),
            ComposeHalt::Fault(fault) => Halt::Fault(fault),
        }
    }

    fn finish(self, root: ExprId) -> WireExpr {
        WireExpr::from_parts(self.expressions, self.levels, root)
    }

    fn finish_cursor(self, root: ExprId) -> Cursor {
        let term = self.finish(root);
        let root = term.root();
        Cursor::closed(Arc::new(term), root)
    }
}

/// Derive a projection rule from the environment when the caller's registry
/// does not carry one. KR-112's condition: a single-constructor inductive —
/// the rule names the staged inductive's own constructor, so it is well-formed
/// by construction, unlike a caller-supplied rule (which stays the
/// untrusted-input surface and is still refused downstream when it names a
/// non-constructor). Indexed structures derive with the inductive's parameter
/// count: the arity walk treats the index arguments exactly as the pin's
/// `|As| = nparams + nindices` spine does.
pub fn derive_projection_rule(
    constants: &ConstantEnvironment,
    structure: &WireName,
) -> Option<ProjectionRule> {
    let entry = constants.find(structure)?;
    let metadata = entry.inductive_metadata()?;
    let [constructor] = metadata.constructors() else {
        return None;
    };
    Some(ProjectionRule::new(
        structure.clone(),
        constructor.clone(),
        usize::try_from(metadata.num_parameters()).ok()?,
    ))
}

pub fn whnf(term: &WireExpr, context: &WhnfContext, budget: WhnfBudget) -> WhnfOutcome {
    whnf_with(term, context, budget, || false)
}

pub fn whnf_with(
    term: &WireExpr,
    context: &WhnfContext,
    budget: WhnfBudget,
    mut cancelled: impl FnMut() -> bool,
) -> WhnfOutcome {
    whnf_at_with(term, term.root(), context, budget, &mut cancelled)
}

pub(crate) fn whnf_at_with(
    term: &WireExpr,
    root: ExprId,
    context: &WhnfContext,
    budget: WhnfBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> WhnfOutcome {
    whnf_at_mode_with(
        term,
        root,
        context,
        budget,
        DeltaMode::Eager,
        NatReductionScope::WhnfHead,
        cancelled,
    )
}

/// WHNF of a term being compared, as opposed to a type or a recursor major.
/// The pin's conversion never takes the WHNF of a comparand: it reduces a Nat
/// operation only in lazy delta, and only when neither side has a free
/// variable (`type_checker.cpp:1007` of the vendored source). A caller that
/// normalizes comparands to widen conversion must therefore not reduce an
/// open operation, whatever its free variables are bound to.
pub(crate) fn whnf_comparand_with(
    term: &WireExpr,
    context: &WhnfContext,
    budget: WhnfBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> WhnfOutcome {
    whnf_at_mode_with(
        term,
        term.root(),
        context,
        budget,
        DeltaMode::Eager,
        NatReductionScope::ClosedPair,
        cancelled,
    )
}

pub(crate) fn whnf_core_at_with(
    term: &WireExpr,
    root: ExprId,
    context: &WhnfContext,
    budget: WhnfBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> WhnfOutcome {
    whnf_at_mode_with(
        term,
        root,
        context,
        budget,
        DeltaMode::Disabled,
        NatReductionScope::WhnfHead,
        cancelled,
    )
}

pub(crate) fn whnf_delta_step_at_with(
    term: &WireExpr,
    root: ExprId,
    context: &WhnfContext,
    budget: WhnfBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> WhnfOutcome {
    whnf_at_mode_with(
        term,
        root,
        context,
        budget,
        DeltaMode::Once,
        NatReductionScope::WhnfHead,
        cancelled,
    )
}

/// Whether the loose index `target` occurs in `term`, counting it at every
/// binder depth.
fn loose_bound_occurs(term: &WireExpr, target: u32) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![(term.root(), 0u32)];
    while let Some((id, depth)) = stack.pop() {
        if !seen.insert((id, depth)) {
            continue;
        }
        let Some(node) = term.node(id) else {
            // A malformed arena is refused where it is read; say it may occur.
            return true;
        };
        match node {
            ExprNode::Bound { index } => {
                if index.checked_sub(depth) == Some(target) {
                    return true;
                }
            }
            ExprNode::Apply { function, argument } => {
                stack.push((*function, depth));
                stack.push((*argument, depth));
            }
            ExprNode::Lambda {
                binder_type, body, ..
            }
            | ExprNode::Forall {
                binder_type, body, ..
            } => {
                stack.push((*binder_type, depth));
                stack.push((*body, depth.saturating_add(1)));
            }
            ExprNode::Let {
                type_, value, body, ..
            } => {
                stack.push((*type_, depth));
                stack.push((*value, depth));
                stack.push((*body, depth.saturating_add(1)));
            }
            ExprNode::Metadata { expression, .. } | ExprNode::Projection { expression, .. } => {
                stack.push((*expression, depth));
            }
            ExprNode::Free { .. }
            | ExprNode::Meta { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Constant { .. }
            | ExprNode::NatLiteral { .. }
            | ExprNode::StringLiteral(_) => {}
        }
    }
    false
}

/// A closed value for an index that does not occur.
fn absent_value() -> WireExpr {
    WireExpr::from_parts(
        vec![ExprNode::Sort {
            level: LevelId::ZERO,
        }],
        vec![LevelNode::Zero],
        ExprId::ZERO,
    )
}

fn whnf_at_mode_with(
    term: &WireExpr,
    root: ExprId,
    context: &WhnfContext,
    budget: WhnfBudget,
    delta_mode: DeltaMode,
    head_nat: NatReductionScope,
    cancelled: &mut dyn FnMut() -> bool,
) -> WhnfOutcome {
    let mut control = Control::new(budget);
    let prepared = match PreparedContext::prepare(context, &mut control, cancelled) {
        Ok(prepared) => prepared,
        Err(halt) => {
            return outcome(Err(halt));
        }
    };
    let reducer = Reducer {
        context: prepared,
        control,
        cancelled,
        unfolded_bindings: BTreeSet::new(),
        delta_mode,
        head_nat,
        delta_reductions: 0,
        discarded_reductions: 0,
        discarded_delta_reductions: 0,
        has_auxiliary_work: false,
        string_progress: StringExpansionProgress::default(),
        force_string_delta: false,
        skip_nat: false,
        facts: std::collections::HashMap::new(),
        string_expansions: std::collections::HashMap::new(),
        bodies: std::collections::HashMap::new(),
        keyed_thunks: std::collections::HashMap::new(),
    };
    outcome(reducer.run(term, root))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn private_arena_corruption_is_an_internal_fault() {
        let root = ExprId::from_index(0).expect("zero is a valid expression index");
        let term = WireExpr::from_parts(
            vec![ExprNode::Apply {
                function: root,
                argument: root,
            }],
            Vec::new(),
            root,
        );
        assert_eq!(
            whnf(&term, &WhnfContext::default(), WhnfBudget::unlimited()),
            WhnfOutcome::InternalFault(WhnfFault::Term {
                phase: WhnfPhase::Initial,
                fault: TermFault::NonBackwardExpressionReference {
                    input: crate::term::TermInput::Subject,
                    parent: 0,
                    child: 0,
                },
            })
        );
    }
}
