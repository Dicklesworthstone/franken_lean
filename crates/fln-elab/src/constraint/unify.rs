//! Native, transactional pattern unification (Athanor, plan §10.2).
//!
//! This is an equation solver, not a declaration-admission authority. It owns
//! beta/zeta reduction, first-order congruence and distinct-local Miller patterns.
//! Each new expression assignment must additionally pass K1 at its declared
//! type, closed over its local context and any typed residual metavariables.
//! Residuals remain unassigned: a conditional typing check is not a completed
//! proof. Unsupported equations and unresolved typing requirements defer.
//! There is no Reference fallback and no unchecked assignment publication.
//!
//! The public methods are inherent methods on `ElabTxn`. A request commits only
//! its metavariables, universes and constraint queue, atomically on success.
//! Failures retain spent work but no speculative assignments or wake-ups.

mod residual;

use crate::constraint::Constraint;
use crate::lctx::LocalContext;
use crate::mvar::{AssignmentJustification, MetavarError, MetavarKind};
use crate::txn::ElabTxn;
use crate::universe::UniverseInstantiationError;
use fln_core::expr::{Expr, ExprNode, FVarId, MVarId};
use fln_core::level::{LMVarId, Level, LevelView};
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_env::constants::{
    ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
};
use fln_kernel::verdict::{Budget, Verdict};
use fln_kernel::{Declaration, check};
use std::collections::{HashSet, VecDeque};

/// Native delta policy. Opaque declarations, unsafe definitions and partial
/// definitions never unfold. Polymorphic delta is outside this bounded lane.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnificationTransparency {
    None,
    Abbreviations,
    SafeDefinitions,
}

#[derive(Debug, Clone, Copy)]
pub struct UnificationBudget {
    pub max_steps: u64,
    pub max_visited_nodes: usize,
    pub max_assignments: usize,
    pub max_metavar_depth: u32,
    pub transparency: UnificationTransparency,
    /// Unfold local let declarations. This is independent of global delta
    /// transparency; automatic `simp` closure leaves these names closed.
    pub zeta_delta: bool,
    /// A separate, caller-calibrated bound for each assignment's K1 check.
    pub kernel: Budget,
}

impl UnificationBudget {
    pub fn new(kernel: Budget) -> Self {
        Self {
            max_steps: 100_000,
            max_visited_nodes: 1_000_000,
            max_assignments: 256,
            max_metavar_depth: 0,
            transparency: UnificationTransparency::Abbreviations,
            zeta_delta: true,
            kernel,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnificationDeferred {
    UnsupportedEquation,
    NotAPattern,
    UnknownMetavariable(MVarId),
    OpaqueMetavariable(MVarId),
    MetavariableDepth(MVarId),
    EscapingLocal(MVarId),
    UnresolvedAssignmentType(MVarId),
    CyclicUniverse(LMVarId),
    InvalidLocalContext,
}

/// Nonanswers are not flattened into a Boolean or a kernel rejection. In
/// particular, `AssignmentCheck` preserves the complete kernel outcome.
#[derive(Debug, Clone, PartialEq)]
pub enum UnificationError {
    Deferred(UnificationDeferred),
    Cancelled,
    StepLimit {
        limit: u64,
    },
    NodeLimit {
        limit: usize,
    },
    AssignmentLimit {
        limit: usize,
    },
    HeartbeatLimit,
    LooseBoundVariable,
    ExpressionScope,
    Metavariable(MetavarError),
    Universe(UniverseInstantiationError),
    AssignmentCheck {
        id: MVarId,
        outcome: Box<Outcome<Verdict>>,
    },
}

impl std::fmt::Display for UnificationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Deferred(reason) => write!(f, "unification deferred: {reason:?}"),
            Self::Cancelled => write!(f, "unification cancelled"),
            Self::StepLimit { limit } => write!(f, "unification step limit {limit} reached"),
            Self::NodeLimit { limit } => write!(f, "unification node limit {limit} reached"),
            Self::AssignmentLimit { limit } => {
                write!(f, "unification assignment limit {limit} reached")
            }
            Self::HeartbeatLimit => write!(f, "elaboration heartbeat limit reached"),
            Self::LooseBoundVariable => write!(f, "unification input has a loose bound variable"),
            Self::ExpressionScope => {
                write!(f, "unification substitution exceeded expression scope")
            }
            Self::Metavariable(error) => write!(f, "{error}"),
            Self::Universe(error) => write!(f, "{error}"),
            Self::AssignmentCheck { id, .. } => write!(
                f,
                "kernel did not validate assignment to ?{}",
                id.0.to_display_string()
            ),
        }
    }
}

impl std::error::Error for UnificationError {}

/// Successful equation solving is not an environment publication. Awakened
/// constraints still need processing; residual metavariables are not solved.
#[derive(Debug)]
pub struct UnificationReport {
    pub expression_assignments: Vec<MVarId>,
    pub universe_assignments: Vec<LMVarId>,
    /// Unassigned metavariables quantified by conditional assignment checks,
    /// deduplicated in deterministic first-use dependency order.
    pub residual_metavariables: Vec<MVarId>,
    pub awakened: Vec<Constraint>,
    pub unifier_steps: u64,
    pub visited_nodes: usize,
    pub kernel_checks: usize,
}

struct Meter<'a> {
    steps: u64,
    nodes: usize,
    max_steps: u64,
    max_nodes: usize,
    heartbeat_bound: bool,
    cancelled: &'a dyn Fn() -> bool,
}

impl Meter<'_> {
    fn tick(&mut self) -> Result<(), UnificationError> {
        if (self.cancelled)() {
            return Err(UnificationError::Cancelled);
        }
        if self.steps >= self.max_steps {
            return Err(if self.heartbeat_bound {
                UnificationError::HeartbeatLimit
            } else {
                UnificationError::StepLimit {
                    limit: self.max_steps,
                }
            });
        }
        self.steps += 1;
        Ok(())
    }

    fn node(&mut self) -> Result<(), UnificationError> {
        self.tick()?;
        if self.nodes >= self.max_nodes {
            return Err(UnificationError::NodeLimit {
                limit: self.max_nodes,
            });
        }
        self.nodes += 1;
        Ok(())
    }
}

fn children(expr: &Expr) -> [Option<&Expr>; 3] {
    match expr.node() {
        ExprNode::App { f, a } => [Some(f), Some(a), None],
        ExprNode::Lam {
            binder_type, body, ..
        }
        | ExprNode::ForallE {
            binder_type, body, ..
        } => [Some(binder_type), Some(body), None],
        ExprNode::LetE {
            type_, value, body, ..
        } => [Some(type_), Some(value), Some(body)],
        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => [Some(expr), None, None],
        _ => [None, None, None],
    }
}

#[derive(Default)]
struct Facts {
    fvars: HashSet<FVarId>,
    params: Vec<Name>,
}

/// Explicit DAG walks precede core substitution and kernel submission. Keys
/// live only while the borrowed roots are pinned; no address is persisted.
fn facts(expr: &Expr, meter: &mut Meter<'_>) -> Result<Facts, UnificationError> {
    let mut result = Facts::default();
    let mut seen = HashSet::new();
    let mut seen_levels = HashSet::new();
    let mut params = HashSet::new();
    let mut pending = vec![expr];
    let mut levels = Vec::new();
    while let Some(current) = pending.pop() {
        if !seen.insert(std::ptr::from_ref(current.node())) {
            continue;
        }
        meter.node()?;
        match current.node() {
            ExprNode::FVar { id } => {
                result.fvars.insert(id.clone());
            }
            ExprNode::Sort { level } => levels.push(level),
            ExprNode::Const {
                levels: arguments, ..
            } => levels.extend(arguments.iter().rev()),
            _ => {}
        }
        pending.extend(children(current).into_iter().rev().flatten());
    }
    while let Some(level) = levels.pop() {
        if !seen_levels.insert(std::ptr::from_ref(level)) {
            continue;
        }
        meter.node()?;
        match level.view() {
            LevelView::Param(name) if params.insert(name.clone()) => {
                result.params.push(name.clone())
            }
            LevelView::Succ(inner) => levels.push(inner),
            LevelView::Max(a, b) | LevelView::IMax(a, b) => {
                levels.push(b);
                levels.push(a);
            }
            _ => {}
        }
    }
    Ok(result)
}

fn same_levels(
    left: &Level,
    right: &Level,
    meter: &mut Meter<'_>,
) -> Result<bool, UnificationError> {
    let mut pending = vec![(left, right)];
    let mut seen = HashSet::new();
    while let Some((left, right)) = pending.pop() {
        if !seen.insert((std::ptr::from_ref(left), std::ptr::from_ref(right))) {
            continue;
        }
        meter.node()?;
        match (left.view(), right.view()) {
            (LevelView::Zero, LevelView::Zero) => {}
            (LevelView::Param(a), LevelView::Param(b)) if a == b => {}
            (LevelView::MVar(a), LevelView::MVar(b)) if a == b => {}
            (LevelView::Succ(a), LevelView::Succ(b)) => pending.push((a, b)),
            (LevelView::Max(a, b), LevelView::Max(c, d))
            | (LevelView::IMax(a, b), LevelView::IMax(c, d)) => {
                pending.push((b, d));
                pending.push((a, c));
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

/// A sufficient reflexivity test, not a negative definitional-equality verdict.
/// Binder names/styles and metadata do not affect this equality. Pair memoization
/// prevents exponentially shared terms from becoming exponentially many tasks.
fn same_terms(left: &Expr, right: &Expr, meter: &mut Meter<'_>) -> Result<bool, UnificationError> {
    let mut pending = vec![(left, right)];
    let mut seen = HashSet::new();
    while let Some((left, right)) = pending.pop() {
        if !seen.insert((
            std::ptr::from_ref(left.node()),
            std::ptr::from_ref(right.node()),
        )) {
            continue;
        }
        meter.node()?;
        if std::ptr::eq(left.node(), right.node()) {
            continue;
        }
        match (left.node(), right.node()) {
            (ExprNode::MData { expr, .. }, _) => pending.push((expr, right)),
            (_, ExprNode::MData { expr, .. }) => pending.push((left, expr)),
            (ExprNode::BVar { idx: a }, ExprNode::BVar { idx: b }) if a == b => {}
            (ExprNode::FVar { id: a }, ExprNode::FVar { id: b }) if a == b => {}
            (ExprNode::MVar { id: a }, ExprNode::MVar { id: b }) if a == b => {}
            (ExprNode::Lit { literal: a }, ExprNode::Lit { literal: b }) if a == b => {}
            (ExprNode::Sort { level: a }, ExprNode::Sort { level: b }) => {
                if !same_levels(a, b, meter)? {
                    return Ok(false);
                }
            }
            (
                ExprNode::Const {
                    name: a,
                    levels: ua,
                },
                ExprNode::Const {
                    name: b,
                    levels: ub,
                },
            ) if a == b && ua.len() == ub.len() => {
                for (a, b) in ua.iter().zip(ub) {
                    if !same_levels(a, b, meter)? {
                        return Ok(false);
                    }
                }
            }
            (ExprNode::App { f: a, a: b }, ExprNode::App { f: c, a: d }) => {
                pending.push((b, d));
                pending.push((a, c));
            }
            (
                ExprNode::Lam {
                    binder_type: a,
                    body: b,
                    ..
                },
                ExprNode::Lam {
                    binder_type: c,
                    body: d,
                    ..
                },
            )
            | (
                ExprNode::ForallE {
                    binder_type: a,
                    body: b,
                    ..
                },
                ExprNode::ForallE {
                    binder_type: c,
                    body: d,
                    ..
                },
            ) => {
                pending.push((b, d));
                pending.push((a, c));
            }
            (
                ExprNode::LetE {
                    type_: a,
                    value: b,
                    body: c,
                    ..
                },
                ExprNode::LetE {
                    type_: d,
                    value: e,
                    body: f,
                    ..
                },
            ) => {
                pending.push((c, f));
                pending.push((b, e));
                pending.push((a, d));
            }
            (
                ExprNode::Proj {
                    struct_name: a,
                    idx: i,
                    expr: x,
                },
                ExprNode::Proj {
                    struct_name: b,
                    idx: j,
                    expr: y,
                },
            ) if a == b && i == j => pending.push((x, y)),
            _ => return Ok(false),
        }
    }
    Ok(true)
}

type Equation = (Expr, Expr, LocalContext);

struct Engine<'a> {
    work: ElabTxn,
    budget: UnificationBudget,
    meter: Meter<'a>,
    reserved: HashSet<FVarId>,
    next_local: u64,
    assigned: Vec<MVarId>,
    assigned_levels: Vec<LMVarId>,
    residuals: Vec<MVarId>,
    awakened: Vec<Constraint>,
    kernel_checks: usize,
}

impl Engine<'_> {
    fn generation(&self) -> usize {
        self.assigned
            .len()
            .saturating_add(self.assigned_levels.len())
    }

    fn scan(&mut self, expr: &Expr) -> Result<Facts, UnificationError> {
        let found = facts(expr, &mut self.meter)?;
        self.reserved.extend(found.fvars.iter().cloned());
        Ok(found)
    }

    fn instantiate(&mut self, expr: &Expr) -> Result<Expr, UnificationError> {
        self.scan(expr)?;
        let expanded = self.work.mvars.instantiate(expr);
        self.scan(&expanded)?;
        let remaining = self
            .budget
            .max_visited_nodes
            .saturating_sub(self.meter.nodes);
        let expanded = self
            .work
            .universes
            .instantiate_expr_with_limit(&expanded, remaining)
            .map_err(UnificationError::Universe)?;
        self.scan(&expanded)?;
        Ok(expanded)
    }

    fn fresh(&mut self) -> Result<FVarId, UnificationError> {
        loop {
            self.meter.tick()?;
            let suffix = self.next_local.to_string();
            self.next_local = self
                .next_local
                .checked_add(1)
                .ok_or(UnificationError::ExpressionScope)?;
            let id = FVarId(Name::from_components(["_fln_unify_local", suffix.as_str()]));
            if self.reserved.insert(id.clone()) {
                return Ok(id);
            }
        }
    }

    fn substitute(&mut self, body: &Expr, value: &Expr) -> Result<Expr, UnificationError> {
        self.scan(body)?;
        self.scan(value)?;
        let result = body
            .subst_loose(0, std::slice::from_ref(value))
            .map_err(|_| UnificationError::ExpressionScope)?;
        self.scan(&result)?;
        Ok(result)
    }

    fn whnf(&mut self, expr: &Expr, locals: &LocalContext) -> Result<Expr, UnificationError> {
        let mut head = expr.clone();
        let mut args = Vec::new();
        loop {
            self.meter.tick()?;
            match head.node() {
                ExprNode::MData { expr, .. } => head = expr.clone(),
                ExprNode::LetE { value, body, .. } => head = self.substitute(body, value)?,
                ExprNode::App { f, a } => {
                    args.push(a.clone());
                    head = f.clone();
                }
                ExprNode::MVar { id } => {
                    if let Some(value) = self.work.mvars.get_assigned_expr(id) {
                        head = value.clone();
                    } else {
                        break;
                    }
                }
                ExprNode::FVar { id } if self.budget.zeta_delta => {
                    if let Some(value) = locals.find(id).and_then(|local| local.value.as_ref()) {
                        head = value.clone();
                    } else {
                        break;
                    }
                }
                ExprNode::Lam { body, .. } if !args.is_empty() => {
                    let argument = args.pop().expect("nonempty application spine");
                    head = self.substitute(body, &argument)?;
                }
                ExprNode::Const { name, levels } if levels.is_empty() => {
                    let definition = match self.work.env.find(name) {
                        Some(ConstantInfo::Defn(definition))
                            if definition.safety == DefinitionSafety::Safe
                                && definition.base.level_params.is_empty()
                                && match self.budget.transparency {
                                    UnificationTransparency::None => false,
                                    UnificationTransparency::Abbreviations => {
                                        definition.hints == ReducibilityHints::Abbrev
                                    }
                                    UnificationTransparency::SafeDefinitions => true,
                                } =>
                        {
                            Some(definition.value.clone())
                        }
                        _ => None,
                    };
                    if let Some(value) = definition {
                        self.scan(&value)?;
                        head = value;
                    } else {
                        break;
                    }
                }
                _ => break,
            }
        }
        for argument in args.into_iter().rev() {
            self.meter.tick()?;
            head = Expr::app(head, argument);
        }
        Ok(head)
    }

    fn assignment_slot(&self) -> Result<(), UnificationError> {
        if self.generation() >= self.budget.max_assignments {
            Err(UnificationError::AssignmentLimit {
                limit: self.budget.max_assignments,
            })
        } else {
            Ok(())
        }
    }

    /// A candidate is scope-checked now and type-checked after the whole batch.
    /// Every refusal precedes assignment mutation, allowing reverse orientation.
    fn pattern(
        &mut self,
        lhs: &Expr,
        rhs: &Expr,
        locals: &LocalContext,
    ) -> Result<bool, UnificationError> {
        let mut head = lhs;
        let mut arguments = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.meter.tick()?;
            arguments.push(a.clone());
            head = f;
        }
        let ExprNode::MVar { id } = head.node() else {
            return Ok(false);
        };
        let declaration = self.work.mvars.get_decl(id).cloned().ok_or_else(|| {
            UnificationError::Deferred(UnificationDeferred::UnknownMetavariable(id.clone()))
        })?;
        if declaration.kind == MetavarKind::SyntheticOpaque {
            return Err(UnificationError::Deferred(
                UnificationDeferred::OpaqueMetavariable(id.clone()),
            ));
        }
        if declaration.depth > self.budget.max_metavar_depth {
            return Err(UnificationError::Deferred(
                UnificationDeferred::MetavariableDepth(id.clone()),
            ));
        }
        arguments.reverse();
        let mut distinct = HashSet::new();
        let mut binders = Vec::new();
        let mut function_type = declaration.type_.clone();
        for argument in &arguments {
            let ExprNode::FVar { id: local_id } = argument.node() else {
                return Err(UnificationError::Deferred(UnificationDeferred::NotAPattern));
            };
            if !distinct.insert(local_id.clone()) || !locals.contains(local_id) {
                return Err(UnificationError::Deferred(UnificationDeferred::NotAPattern));
            }
            function_type = self.whnf(&function_type, locals)?;
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = function_type.node()
            else {
                return Err(UnificationError::Deferred(UnificationDeferred::NotAPattern));
            };
            binders.push((local_id.clone(), binder_type.clone(), *binder_info));
            function_type = self.substitute(body, argument)?;
        }
        let mut value = self.instantiate(rhs)?;
        for (local, domain, style) in binders.into_iter().rev() {
            self.scan(&value)?;
            value = value
                .abstract_fvar(&local, 0)
                .map_err(|_| UnificationError::ExpressionScope)?;
            value = Expr::lam(local.0.clone(), domain, value, style);
        }
        if value.has_loose_bvars() {
            return Err(UnificationError::LooseBoundVariable);
        }
        let free = self.scan(&value)?.fvars;
        if free.iter().any(|id| !declaration.lctx.contains(id)) {
            return Err(UnificationError::Deferred(
                UnificationDeferred::EscapingLocal(id.clone()),
            ));
        }
        self.assignment_slot()?;
        let awakened = self
            .work
            .assign_mvar(id.clone(), value, AssignmentJustification::DirectDefEq)
            .map_err(UnificationError::Metavariable)?;
        self.awakened.extend(awakened);
        self.assigned.push(id.clone());
        Ok(true)
    }

    fn levels(&mut self, left: &Level, right: &Level) -> Result<(), UnificationError> {
        let mut pending = vec![(left.clone(), right.clone())];
        while let Some((left, right)) = pending.pop() {
            self.meter.tick()?;
            let remaining = self
                .budget
                .max_visited_nodes
                .saturating_sub(self.meter.nodes);
            let left = self
                .work
                .universes
                .instantiate_with_limit(&left, remaining)
                .map_err(UnificationError::Universe)?;
            let right = self
                .work
                .universes
                .instantiate_with_limit(&right, remaining)
                .map_err(UnificationError::Universe)?;
            self.scan(&Expr::sort(left.clone()))?;
            self.scan(&Expr::sort(right.clone()))?;
            if same_levels(&left, &right, &mut self.meter)? {
                continue;
            }
            match (left.view(), right.view()) {
                (LevelView::MVar(id), _) | (_, LevelView::MVar(id)) => {
                    let value = if matches!(left.view(), LevelView::MVar(found) if found == id) {
                        &right
                    } else {
                        &left
                    };
                    let mut todo = vec![value];
                    let mut visited = HashSet::new();
                    while let Some(level) = todo.pop() {
                        if !visited.insert(std::ptr::from_ref(level)) {
                            continue;
                        }
                        self.meter.node()?;
                        match level.view() {
                            LevelView::MVar(found) if found == id => {
                                return Err(UnificationError::Deferred(
                                    UnificationDeferred::CyclicUniverse(id.clone()),
                                ));
                            }
                            LevelView::Succ(inner) => todo.push(inner),
                            LevelView::Max(a, b) | LevelView::IMax(a, b) => {
                                todo.push(b);
                                todo.push(a);
                            }
                            _ => {}
                        }
                    }
                    self.assignment_slot()?;
                    self.work.universes.assign(id.clone(), value.clone());
                    self.assigned_levels.push(id.clone());
                }
                (LevelView::Succ(a), LevelView::Succ(b)) => pending.push((a.clone(), b.clone())),
                (LevelView::Max(a, b), LevelView::Max(c, d))
                | (LevelView::IMax(a, b), LevelView::IMax(c, d)) => {
                    pending.push((b.clone(), d.clone()));
                    pending.push((a.clone(), c.clone()));
                }
                _ => {
                    return Err(UnificationError::Deferred(
                        UnificationDeferred::UnsupportedEquation,
                    ));
                }
            }
        }
        Ok(())
    }

    fn compare(
        &mut self,
        equation: &Equation,
        pending: &mut VecDeque<Equation>,
    ) -> Result<(), UnificationError> {
        let (left, right, locals) = equation;
        self.meter.tick()?;
        if same_terms(left, right, &mut self.meter)? {
            return Ok(());
        }
        let left = self.whnf(left, locals)?;
        let right = self.whnf(right, locals)?;
        if same_terms(&left, &right, &mut self.meter)? {
            return Ok(());
        }
        let mut reason = UnificationDeferred::UnsupportedEquation;
        match self.pattern(&left, &right, locals) {
            Ok(true) => return Ok(()),
            Err(UnificationError::Deferred(found)) => reason = found,
            Ok(false) => {}
            Err(error) => return Err(error),
        }
        match self.pattern(&right, &left, locals) {
            Ok(true) => return Ok(()),
            Err(UnificationError::Deferred(found))
                if reason == UnificationDeferred::UnsupportedEquation =>
            {
                reason = found
            }
            Err(UnificationError::Deferred(_)) | Ok(false) => {}
            Err(error) => return Err(error),
        }
        match (left.node(), right.node()) {
            (ExprNode::Sort { level: a }, ExprNode::Sort { level: b }) => self.levels(a, b)?,
            (
                ExprNode::Const {
                    name: a,
                    levels: ua,
                },
                ExprNode::Const {
                    name: b,
                    levels: ub,
                },
            ) if a == b && ua.len() == ub.len() => {
                for (a, b) in ua.iter().zip(ub) {
                    self.levels(a, b)?;
                }
            }
            (ExprNode::App { f: a, a: b }, ExprNode::App { f: c, a: d }) => {
                pending.push_front((b.clone(), d.clone(), locals.clone()));
                pending.push_front((a.clone(), c.clone(), locals.clone()));
            }
            (
                ExprNode::Lam {
                    binder_type: a,
                    body: b,
                    binder_info,
                    ..
                },
                ExprNode::Lam {
                    binder_type: c,
                    body: d,
                    ..
                },
            )
            | (
                ExprNode::ForallE {
                    binder_type: a,
                    body: b,
                    binder_info,
                    ..
                },
                ExprNode::ForallE {
                    binder_type: c,
                    body: d,
                    ..
                },
            ) => {
                let fresh = self.fresh()?;
                let argument = Expr::fvar(fresh.clone());
                let left_body = self.substitute(b, &argument)?;
                let right_body = self.substitute(d, &argument)?;
                let mut body_locals = locals.clone();
                body_locals.add_param(fresh.clone(), fresh.0, a.clone(), *binder_info);
                pending.push_front((left_body, right_body, body_locals));
                pending.push_front((a.clone(), c.clone(), locals.clone()));
            }
            (
                ExprNode::Proj {
                    struct_name: a,
                    idx: i,
                    expr: x,
                },
                ExprNode::Proj {
                    struct_name: b,
                    idx: j,
                    expr: y,
                },
            ) if a == b && i == j => pending.push_front((x.clone(), y.clone(), locals.clone())),
            _ => return Err(UnificationError::Deferred(reason)),
        }
        Ok(())
    }

    fn solve(&mut self, equations: &[(Expr, Expr)]) -> Result<(), UnificationError> {
        let mut pending = VecDeque::new();
        for (left, right) in equations {
            if left.has_loose_bvars() || right.has_loose_bvars() {
                return Err(UnificationError::LooseBoundVariable);
            }
            self.scan(left)?;
            self.scan(right)?;
            pending.push_back((left.clone(), right.clone(), self.work.lctx.clone()));
        }
        // Reserve all pre-existing identities before opening binders. Map
        // iteration changes neither the resulting set nor the generated names.
        let mut roots = Vec::new();
        for declaration in self.work.mvars.decls().values() {
            roots.push(declaration.type_.clone());
            for local in declaration.lctx.decls() {
                self.reserved.insert(local.id.clone());
                roots.push(local.type_.clone());
                roots.extend(local.value.iter().cloned());
            }
        }
        for assignment in self.work.mvars.assignments().values() {
            roots.push(assignment.expr.clone());
        }
        for local in self.work.lctx.decls() {
            self.reserved.insert(local.id.clone());
            roots.push(local.type_.clone());
            roots.extend(local.value.iter().cloned());
        }
        for root in roots {
            self.scan(&root)?;
        }
        loop {
            let generation = self.generation();
            let mut postponed = VecDeque::new();
            let mut first_reason = None;
            while let Some(equation) = pending.pop_front() {
                match self.compare(&equation, &mut pending) {
                    Ok(()) => {}
                    Err(UnificationError::Deferred(reason)) => {
                        first_reason.get_or_insert(reason);
                        postponed.push_back(equation);
                    }
                    Err(error) => return Err(error),
                }
            }
            if postponed.is_empty() {
                break;
            }
            if self.generation() == generation {
                return Err(UnificationError::Deferred(
                    first_reason.expect("a postponed equation has a reason"),
                ));
            }
            pending = postponed;
        }
        for id in self.assigned.clone() {
            self.check_assignment(&id)?;
        }
        Ok(())
    }

    fn check_assignment(&mut self, id: &MVarId) -> Result<(), UnificationError> {
        let (value, type_, residuals) = self.prepare_assignment_check(id)?;
        if value.has_expr_mvar()
            || type_.has_expr_mvar()
            || value.has_level_mvar()
            || type_.has_level_mvar()
        {
            return Err(UnificationError::Deferred(
                UnificationDeferred::UnresolvedAssignmentType(id.clone()),
            ));
        }
        let value_facts = self.scan(&value)?;
        let type_facts = self.scan(&type_)?;
        if !value_facts.fvars.is_empty() || !type_facts.fvars.is_empty() {
            return Err(UnificationError::Deferred(
                UnificationDeferred::EscapingLocal(id.clone()),
            ));
        }
        let mut params = type_facts.params;
        for name in value_facts.params {
            if !params.contains(&name) {
                params.push(name);
            }
        }
        let mut ordinal = 0_u64;
        let name = loop {
            self.meter.tick()?;
            let suffix = ordinal.to_string();
            let name = Name::from_components(["_fln_unify_check", suffix.as_str()]);
            if !self.work.env.contains(&name) {
                break name;
            }
            ordinal = ordinal
                .checked_add(1)
                .ok_or(UnificationError::ExpressionScope)?;
        };
        let candidate = Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: params,
                type_,
            },
            value,
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![name],
        });
        self.meter.tick()?;
        self.kernel_checks += 1;
        let outcome = check(&self.work.env, &candidate, self.budget.kernel);
        match &outcome {
            Outcome::Complete(Verdict::Accepted { .. }) => {
                for residual in residuals {
                    if !self.residuals.contains(&residual) {
                        self.residuals.push(residual);
                    }
                }
                Ok(())
            }
            Outcome::Complete(Verdict::Rejected { .. }) if !residuals.is_empty() => {
                // Failure of the universally quantified obligation need not be
                // failure after the remaining holes acquire concrete values.
                Err(UnificationError::Deferred(
                    UnificationDeferred::UnresolvedAssignmentType(id.clone()),
                ))
            }
            _ => Err(UnificationError::AssignmentCheck {
                id: id.clone(),
                outcome: Box::new(outcome),
            }),
        }
    }
}

impl ElabTxn {
    pub fn unify(
        &mut self,
        lhs: &Expr,
        rhs: &Expr,
        budget: UnificationBudget,
    ) -> Result<UnificationReport, UnificationError> {
        self.unify_many_with(&[(lhs.clone(), rhs.clone())], budget, &|| false)
    }

    /// Solve the entire equation batch or publish none of it. Later equations
    /// may unblock earlier non-pattern equations and assignment-type checks.
    pub fn unify_many_with(
        &mut self,
        equations: &[(Expr, Expr)],
        budget: UnificationBudget,
        cancelled: &dyn Fn() -> bool,
    ) -> Result<UnificationReport, UnificationError> {
        if cancelled() {
            return Err(UnificationError::Cancelled);
        }
        if equations
            .len()
            .saturating_add(self.mvars.len())
            .saturating_add(self.universes.len())
            > budget.max_visited_nodes
        {
            return Err(UnificationError::NodeLimit {
                limit: budget.max_visited_nodes,
            });
        }
        let remaining = if self.budget.max_heartbeats == 0 {
            u64::MAX
        } else {
            self.budget
                .max_heartbeats
                .saturating_sub(self.budget.heartbeats_consumed)
        };
        let mut engine = Engine {
            work: self.clone(),
            budget,
            meter: Meter {
                steps: 0,
                nodes: 0,
                max_steps: budget.max_steps.min(remaining),
                max_nodes: budget.max_visited_nodes,
                heartbeat_bound: remaining <= budget.max_steps,
                cancelled,
            },
            reserved: HashSet::new(),
            next_local: 0,
            assigned: Vec::new(),
            assigned_levels: Vec::new(),
            residuals: Vec::new(),
            awakened: Vec::new(),
            kernel_checks: 0,
        };
        let result = engine.solve(equations);
        self.budget.heartbeats_consumed = self
            .budget
            .heartbeats_consumed
            .checked_add(engine.meter.steps)
            .ok_or(UnificationError::HeartbeatLimit)?;
        result?;
        if cancelled() {
            return Err(UnificationError::Cancelled);
        }
        self.mvars = engine.work.mvars;
        self.universes = engine.work.universes;
        self.constraints = engine.work.constraints;
        engine.awakened.sort_by_key(|constraint| constraint.id);
        Ok(UnificationReport {
            expression_assignments: engine.assigned,
            universe_assignments: engine.assigned_levels,
            residual_metavariables: engine.residuals,
            awakened: engine.awakened,
            unifier_steps: engine.meter.steps,
            visited_nodes: engine.meter.nodes,
            kernel_checks: engine.kernel_checks,
        })
    }
}
