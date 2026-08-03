//! Resource-counted leaf inference over checker-owned terms.
//!
//! This is the independent checker's first typing dispatcher. It implements the
//! closed-term precondition and the leaf rules KR-100 through KR-105, together
//! with iterative KR-111 metadata transparency. Later rule families are named by
//! [`InferenceDeferred`] instead of being misreported as rejection.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::environment::{ConstantEnvironment, ConstantSafety, DefinitionSafety};
use crate::instantiate::{
    InstantiationFault, InstantiationOutcome, InstantiationRefusal,
    instantiate_term_parameters_from_level_roots_with,
};
use crate::term::{
    TermBudget, TermFault, TermInput, TermLimit, TermOutcome, TermStop, copy_subterm_with,
    inspect_with,
};
use crate::wire::{
    ExprId, ExprNode, LevelId, LevelNode, WireExpr, WireName, expression_owned_units,
    level_owned_units, usize_units,
};

/// One checker-owned local declaration.
///
/// Assumptions have no value. Let declarations retain a value for the later
/// KR-109 and zeta paths, while KR-102 reads only the common type field.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalDeclaration {
    name: WireName,
    type_: WireExpr,
    value: Option<WireExpr>,
}

impl LocalDeclaration {
    pub fn assumption(name: WireName, type_: WireExpr) -> LocalDeclaration {
        LocalDeclaration {
            name,
            type_,
            value: None,
        }
    }

    pub fn definition(name: WireName, type_: WireExpr, value: WireExpr) -> LocalDeclaration {
        LocalDeclaration {
            name,
            type_,
            value: Some(value),
        }
    }

    pub fn name(&self) -> &WireName {
        &self.name
    }

    pub fn type_(&self) -> &WireExpr {
        &self.type_
    }

    pub fn value(&self) -> Option<&WireExpr> {
        self.value.as_ref()
    }
}

/// Context construction is failure-atomic and never silently overwrites a row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InferenceContextRefusal {
    DuplicateLocal {
        name: WireName,
        first: usize,
        second: usize,
    },
    DuplicateLevelParameter {
        name: WireName,
        first: usize,
        second: usize,
    },
}

/// Immutable local and constant lookup state for independent inference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InferenceContext {
    locals: Arc<Vec<LocalDeclaration>>,
    local_indexes: Arc<BTreeMap<WireName, usize>>,
    level_parameters: Arc<Vec<WireName>>,
    level_parameter_set: Arc<BTreeSet<WireName>>,
    constants: ConstantEnvironment,
}

impl InferenceContext {
    pub fn new(
        locals: Vec<LocalDeclaration>,
        level_parameters: Vec<WireName>,
        constants: ConstantEnvironment,
    ) -> Result<InferenceContext, InferenceContextRefusal> {
        let mut local_indexes = BTreeMap::new();
        for (index, local) in locals.iter().enumerate() {
            if let Some(first) = local_indexes.insert(local.name().clone(), index) {
                return Err(InferenceContextRefusal::DuplicateLocal {
                    name: local.name().clone(),
                    first,
                    second: index,
                });
            }
        }

        let mut level_parameter_indexes = BTreeMap::new();
        let mut level_parameter_set = BTreeSet::new();
        for (index, parameter) in level_parameters.iter().enumerate() {
            if let Some(first) = level_parameter_indexes.insert(parameter.clone(), index) {
                return Err(InferenceContextRefusal::DuplicateLevelParameter {
                    name: parameter.clone(),
                    first,
                    second: index,
                });
            }
            level_parameter_set.insert(parameter.clone());
        }

        Ok(InferenceContext {
            locals: Arc::new(locals),
            local_indexes: Arc::new(local_indexes),
            level_parameters: Arc::new(level_parameters),
            level_parameter_set: Arc::new(level_parameter_set),
            constants,
        })
    }

    pub fn empty(constants: ConstantEnvironment) -> InferenceContext {
        InferenceContext {
            locals: Arc::new(Vec::new()),
            local_indexes: Arc::new(BTreeMap::new()),
            level_parameters: Arc::new(Vec::new()),
            level_parameter_set: Arc::new(BTreeSet::new()),
            constants,
        }
    }

    pub fn locals(&self) -> &[LocalDeclaration] {
        &self.locals
    }

    pub fn level_parameters(&self) -> &[WireName] {
        &self.level_parameters
    }

    pub fn constants(&self) -> &ConstantEnvironment {
        &self.constants
    }

    fn local(&self, name: &WireName) -> Option<&LocalDeclaration> {
        self.local_indexes
            .get(name)
            .and_then(|index| self.locals.get(*index))
    }

    fn declares_level_parameter(&self, name: &WireName) -> bool {
        self.level_parameter_set.contains(name)
    }
}

/// `InferOnly` omits admission-only quarantine checks. Constant arity remains
/// exact in both modes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InferenceMode {
    InferOnly,
    Checking { declaration_safety: ConstantSafety },
}

impl InferenceMode {
    const fn is_checking(self) -> bool {
        matches!(self, InferenceMode::Checking { .. })
    }

    const fn checks_safe_declaration(self) -> bool {
        matches!(
            self,
            InferenceMode::Checking {
                declaration_safety: ConstantSafety::Safe
            }
        )
    }
}

/// Outer dispatcher bounds plus separately accounted term walks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InferenceBudget {
    pub max_steps: u64,
    pub max_level_nodes: u64,
    pub inspection: TermBudget,
    pub materialization: TermBudget,
}

impl InferenceBudget {
    pub const fn new(
        max_steps: u64,
        max_level_nodes: u64,
        inspection: TermBudget,
        materialization: TermBudget,
    ) -> InferenceBudget {
        InferenceBudget {
            max_steps,
            max_level_nodes,
            inspection,
            materialization,
        }
    }

    pub const fn unlimited() -> InferenceBudget {
        InferenceBudget::new(
            u64::MAX,
            u64::MAX,
            TermBudget::unlimited(),
            TermBudget::unlimited(),
        )
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct InferenceProgress {
    pub steps: u64,
    pub level_nodes: u64,
    pub metadata_layers: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InferenceLimit {
    Steps,
    LevelNodes,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InferencePhase {
    Precondition,
    Metadata,
    Dispatch,
    UniverseValidation,
    LocalType,
    SortType,
    ConstantType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InferenceStop {
    Resource {
        limit: InferenceLimit,
        allowed: u64,
        observed: u64,
        phase: InferencePhase,
        at: usize,
        progress: InferenceProgress,
    },
    Cancelled {
        phase: InferencePhase,
        at: usize,
        polls: u64,
        progress: InferenceProgress,
    },
    Inspection {
        stop: TermStop,
        progress: InferenceProgress,
    },
    Materialization {
        phase: InferencePhase,
        stop: TermStop,
        progress: InferenceProgress,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InferenceRefusal {
    ExpressionMetavariable,
    UnknownFreeVariable {
        name: WireName,
    },
    UnknownConstant {
        name: WireName,
    },
    ConstantUniverseArity {
        name: WireName,
        expected: usize,
        actual: usize,
    },
    UndeclaredUniverseParameter {
        name: WireName,
    },
    UniverseMetavariable {
        name: WireName,
    },
    UnsafeConstant {
        name: WireName,
    },
    PartialConstant {
        name: WireName,
    },
}

/// Rule families deliberately outside this child.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InferenceDeferred {
    Application,
    Lambda,
    Forall,
    Let,
    NatLiteral,
    StringLiteral,
    Projection,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InferenceFault {
    LooseBoundVariables {
        external_bound_span: u32,
    },
    MissingExpression {
        index: usize,
    },
    MissingLevel {
        index: usize,
    },
    ResidualMetadata {
        index: usize,
    },
    Inspection(TermFault),
    Materialization {
        phase: InferencePhase,
        fault: TermFault,
    },
    ConstantInstantiation {
        name: WireName,
        fault: InstantiationFault,
    },
    ConstantInstantiationRefusal {
        name: WireName,
        refusal: InstantiationRefusal,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InferenceResult {
    pub type_: WireExpr,
    pub progress: InferenceProgress,
}

/// A semantic refusal, a not-yet-implemented rule, and a resource stop are three
/// different outcomes. None is promoted to the other.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InferenceOutcome {
    Complete(InferenceResult),
    Refused {
        refusal: InferenceRefusal,
        progress: InferenceProgress,
    },
    Deferred {
        requirement: InferenceDeferred,
        progress: InferenceProgress,
    },
    Inconclusive(InferenceStop),
    InternalFault {
        fault: InferenceFault,
        progress: InferenceProgress,
    },
}

struct Control {
    budget: InferenceBudget,
    progress: InferenceProgress,
    polls: u64,
}

impl Control {
    fn new(budget: InferenceBudget) -> Control {
        Control {
            budget,
            progress: InferenceProgress::default(),
            polls: 0,
        }
    }

    fn poll(
        &mut self,
        cancelled: &mut dyn FnMut() -> bool,
        phase: InferencePhase,
        at: usize,
    ) -> Result<(), InferenceStop> {
        self.polls = self.polls.saturating_add(1);
        if cancelled() {
            return Err(InferenceStop::Cancelled {
                phase,
                at,
                polls: self.polls,
                progress: self.progress,
            });
        }
        Ok(())
    }

    fn step(
        &mut self,
        cancelled: &mut dyn FnMut() -> bool,
        phase: InferencePhase,
        at: usize,
    ) -> Result<(), InferenceStop> {
        self.poll(cancelled, phase, at)?;
        let observed = self.progress.steps.saturating_add(1);
        if observed > self.budget.max_steps {
            return Err(InferenceStop::Resource {
                limit: InferenceLimit::Steps,
                allowed: self.budget.max_steps,
                observed,
                phase,
                at,
                progress: self.progress,
            });
        }
        self.progress.steps = observed;
        Ok(())
    }

    fn level_node(&mut self, at: usize) -> Result<(), InferenceStop> {
        let observed = self.progress.level_nodes.saturating_add(1);
        if observed > self.budget.max_level_nodes {
            return Err(InferenceStop::Resource {
                limit: InferenceLimit::LevelNodes,
                allowed: self.budget.max_level_nodes,
                observed,
                phase: InferencePhase::UniverseValidation,
                at,
                progress: self.progress,
            });
        }
        self.progress.level_nodes = observed;
        Ok(())
    }
}

enum LeafHalt {
    Refused(InferenceRefusal),
    Deferred(InferenceDeferred),
    Stop(InferenceStop),
    Fault(InferenceFault),
}

fn finish(result: Result<WireExpr, LeafHalt>, progress: InferenceProgress) -> InferenceOutcome {
    match result {
        Ok(type_) => InferenceOutcome::Complete(InferenceResult { type_, progress }),
        Err(LeafHalt::Refused(refusal)) => InferenceOutcome::Refused { refusal, progress },
        Err(LeafHalt::Deferred(requirement)) => InferenceOutcome::Deferred {
            requirement,
            progress,
        },
        Err(LeafHalt::Stop(stop)) => InferenceOutcome::Inconclusive(stop),
        Err(LeafHalt::Fault(fault)) => InferenceOutcome::InternalFault { fault, progress },
    }
}

fn validate_level_roots(
    term: &WireExpr,
    roots: &[LevelId],
    context: &InferenceContext,
    control: &mut Control,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<(), LeafHalt> {
    let mut visited = BTreeSet::new();
    for root in roots {
        let mut stack = vec![*root];
        while let Some(id) = stack.pop() {
            if visited.contains(&id.index()) {
                continue;
            }
            control
                .step(cancelled, InferencePhase::UniverseValidation, id.index())
                .map_err(LeafHalt::Stop)?;
            control.level_node(id.index()).map_err(LeafHalt::Stop)?;
            visited.insert(id.index());
            let node = term
                .level(id)
                .ok_or(LeafHalt::Fault(InferenceFault::MissingLevel {
                    index: id.index(),
                }))?;
            match node {
                LevelNode::Zero => {}
                LevelNode::Succ(child) => stack.push(*child),
                LevelNode::Max(left, right) | LevelNode::IMax(left, right) => {
                    stack.push(*right);
                    stack.push(*left);
                }
                LevelNode::Parameter(name) => {
                    if !context.declares_level_parameter(name) {
                        return Err(LeafHalt::Refused(
                            InferenceRefusal::UndeclaredUniverseParameter { name: name.clone() },
                        ));
                    }
                }
                LevelNode::Meta(name) => {
                    return Err(LeafHalt::Refused(InferenceRefusal::UniverseMetavariable {
                        name: name.clone(),
                    }));
                }
            }
        }
    }
    Ok(())
}

enum MaterializeHalt {
    Stop(TermStop),
    Fault(TermFault),
}

struct MaterializationControl<'a> {
    budget: TermBudget,
    steps: u64,
    output_units: u64,
    polls: u64,
    cancelled: &'a mut dyn FnMut() -> bool,
}

impl<'a> MaterializationControl<'a> {
    fn new(
        budget: TermBudget,
        cancelled: &'a mut dyn FnMut() -> bool,
    ) -> MaterializationControl<'a> {
        MaterializationControl {
            budget,
            steps: 0,
            output_units: 0,
            polls: 0,
            cancelled,
        }
    }

    fn poll(&mut self, at: usize) -> Result<(), MaterializeHalt> {
        self.polls = self.polls.saturating_add(1);
        if (self.cancelled)() {
            return Err(MaterializeHalt::Stop(TermStop::Cancelled {
                at,
                polls: self.polls,
                completed_steps: self.steps,
            }));
        }
        Ok(())
    }

    fn step(&mut self, at: usize) -> Result<(), MaterializeHalt> {
        self.poll(at)?;
        let observed = self.steps.saturating_add(1);
        if observed > self.budget.max_steps {
            return Err(MaterializeHalt::Stop(TermStop::Resource {
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

    fn output(&mut self, units: u64, at: usize) -> Result<(), MaterializeHalt> {
        self.poll(at)?;
        let observed = self.output_units.saturating_add(units);
        if observed > self.budget.max_output_units {
            return Err(MaterializeHalt::Stop(TermStop::Resource {
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

    fn arena_node(&self, observed: u64, at: usize) -> Result<(), MaterializeHalt> {
        let allowed = self.budget.max_arena_nodes.min(u64::from(u32::MAX));
        if observed > allowed {
            return Err(MaterializeHalt::Stop(TermStop::Resource {
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

fn validate_materialized_level_child(
    levels: &[LevelNode],
    parent: usize,
    child: LevelId,
) -> Result<(), MaterializeHalt> {
    if child.index() >= parent {
        return Err(MaterializeHalt::Fault(
            TermFault::NonBackwardLevelReference {
                input: TermInput::Subject,
                parent,
                child: child.index(),
            },
        ));
    }
    if levels.get(child.index()).is_none() {
        return Err(MaterializeHalt::Fault(TermFault::MissingLevel {
            input: TermInput::Subject,
            index: child.index(),
        }));
    }
    Ok(())
}

fn materialize_sort_successor(
    term: &WireExpr,
    source: LevelId,
    budget: TermBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> TermOutcome<WireExpr> {
    let mut control = MaterializationControl::new(budget, cancelled);
    if term.level(source).is_none() {
        return TermOutcome::InternalFault(TermFault::MissingLevel {
            input: TermInput::Subject,
            index: source.index(),
        });
    }

    let mut levels = Vec::new();
    for (index, node) in term.levels().iter().enumerate() {
        if let Err(halt) = control.step(index) {
            return materialize_halted(halt);
        }
        let children = match node {
            LevelNode::Succ(child) => [Some(*child), None],
            LevelNode::Max(left, right) | LevelNode::IMax(left, right) => {
                [Some(*left), Some(*right)]
            }
            LevelNode::Zero | LevelNode::Parameter(_) | LevelNode::Meta(_) => [None, None],
        };
        for child in children.into_iter().flatten() {
            if let Err(halt) = validate_materialized_level_child(term.levels(), index, child) {
                return materialize_halted(halt);
            }
        }
        if let Err(halt) = control.output(level_owned_units(node), index) {
            return materialize_halted(halt);
        }
        let observed = usize_units(levels.len()).saturating_add(1);
        if let Err(halt) = control.arena_node(observed, index) {
            return materialize_halted(halt);
        }
        levels.push(node.clone());
    }

    let successor_at = levels.len();
    if let Err(halt) = control.step(successor_at) {
        return materialize_halted(halt);
    }
    let successor_node = LevelNode::Succ(source);
    if let Err(halt) = control.output(level_owned_units(&successor_node), successor_at) {
        return materialize_halted(halt);
    }
    let level_observed = usize_units(levels.len()).saturating_add(1);
    if let Err(halt) = control.arena_node(level_observed, successor_at) {
        return materialize_halted(halt);
    }
    let Some(successor) = LevelId::from_index(levels.len()) else {
        return TermOutcome::Inconclusive(TermStop::Resource {
            limit: TermLimit::ArenaNodes,
            allowed: u64::from(u32::MAX),
            observed: level_observed,
            at: successor_at,
            completed_steps: control.steps,
        });
    };
    levels.push(successor_node);

    let expression_at = levels.len();
    if let Err(halt) = control.step(expression_at) {
        return materialize_halted(halt);
    }
    let root_node = ExprNode::Sort { level: successor };
    if let Err(halt) = control.output(expression_owned_units(&root_node), expression_at) {
        return materialize_halted(halt);
    }
    let expression_observed = usize_units(levels.len()).saturating_add(1);
    if let Err(halt) = control.arena_node(expression_observed, expression_at) {
        return materialize_halted(halt);
    }
    let Some(root) = ExprId::from_index(0) else {
        return TermOutcome::Inconclusive(TermStop::Resource {
            limit: TermLimit::ArenaNodes,
            allowed: u64::from(u32::MAX),
            observed: 1,
            at: expression_at,
            completed_steps: control.steps,
        });
    };
    TermOutcome::Complete(WireExpr::from_parts(vec![root_node], levels, root))
}

fn materialize_halted(halt: MaterializeHalt) -> TermOutcome<WireExpr> {
    match halt {
        MaterializeHalt::Stop(stop) => TermOutcome::Inconclusive(stop),
        MaterializeHalt::Fault(fault) => TermOutcome::InternalFault(fault),
    }
}

fn map_materialization(
    outcome: TermOutcome<WireExpr>,
    phase: InferencePhase,
    progress: InferenceProgress,
) -> Result<WireExpr, LeafHalt> {
    match outcome {
        TermOutcome::Complete(term) => Ok(term),
        TermOutcome::Inconclusive(stop) => Err(LeafHalt::Stop(InferenceStop::Materialization {
            phase,
            stop,
            progress,
        })),
        TermOutcome::InternalFault(fault) => {
            Err(LeafHalt::Fault(InferenceFault::Materialization {
                phase,
                fault,
            }))
        }
    }
}

fn infer_inner(
    term: &WireExpr,
    context: &InferenceContext,
    mode: InferenceMode,
    control: &mut Control,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<WireExpr, LeafHalt> {
    control
        .step(cancelled, InferencePhase::Precondition, term.root().index())
        .map_err(LeafHalt::Stop)?;

    let facts = match inspect_with(term, control.budget.inspection, &mut *cancelled) {
        TermOutcome::Complete(facts) => facts,
        TermOutcome::Inconclusive(stop) => {
            return Err(LeafHalt::Stop(InferenceStop::Inspection {
                stop,
                progress: control.progress,
            }));
        }
        TermOutcome::InternalFault(fault) => {
            return Err(LeafHalt::Fault(InferenceFault::Inspection(fault)));
        }
    };
    if facts.external_bound_span != 0 {
        return Err(LeafHalt::Fault(InferenceFault::LooseBoundVariables {
            external_bound_span: facts.external_bound_span,
        }));
    }
    if facts.contains_expression_meta {
        return Err(LeafHalt::Refused(InferenceRefusal::ExpressionMetavariable));
    }

    let mut root = term.root();
    loop {
        let node = term
            .node(root)
            .ok_or(LeafHalt::Fault(InferenceFault::MissingExpression {
                index: root.index(),
            }))?;
        let ExprNode::Metadata { expression, .. } = node else {
            break;
        };
        control
            .step(cancelled, InferencePhase::Metadata, root.index())
            .map_err(LeafHalt::Stop)?;
        control.progress.metadata_layers = control.progress.metadata_layers.saturating_add(1);
        root = *expression;
    }

    control
        .step(cancelled, InferencePhase::Dispatch, root.index())
        .map_err(LeafHalt::Stop)?;
    let node = term
        .node(root)
        .ok_or(LeafHalt::Fault(InferenceFault::MissingExpression {
            index: root.index(),
        }))?;
    match node {
        ExprNode::Bound { index } => Err(LeafHalt::Fault(InferenceFault::LooseBoundVariables {
            external_bound_span: index.saturating_add(1),
        })),
        ExprNode::Free { name } => {
            let local = context.local(name).ok_or_else(|| {
                LeafHalt::Refused(InferenceRefusal::UnknownFreeVariable { name: name.clone() })
            })?;
            map_materialization(
                copy_subterm_with(
                    local.type_(),
                    local.type_().root(),
                    control.budget.materialization,
                    cancelled,
                ),
                InferencePhase::LocalType,
                control.progress,
            )
        }
        ExprNode::Meta { .. } => Err(LeafHalt::Refused(InferenceRefusal::ExpressionMetavariable)),
        ExprNode::Sort { level } => {
            if mode.is_checking() {
                validate_level_roots(term, &[*level], context, control, cancelled)?;
            }
            map_materialization(
                materialize_sort_successor(term, *level, control.budget.materialization, cancelled),
                InferencePhase::SortType,
                control.progress,
            )
        }
        ExprNode::Constant { name, levels } => {
            let declaration = context.constants().find(name).ok_or_else(|| {
                LeafHalt::Refused(InferenceRefusal::UnknownConstant { name: name.clone() })
            })?;
            let expected = declaration.level_parameters().len();
            if levels.len() != expected {
                return Err(LeafHalt::Refused(InferenceRefusal::ConstantUniverseArity {
                    name: name.clone(),
                    expected,
                    actual: levels.len(),
                }));
            }
            if mode.is_checking() {
                validate_level_roots(term, levels, context, control, cancelled)?;
            }
            if mode.checks_safe_declaration() {
                let definition_safety = declaration
                    .definition_body()
                    .map(|definition| definition.safety());
                if declaration.safety() == ConstantSafety::Unsafe
                    || definition_safety == Some(DefinitionSafety::Unsafe)
                {
                    return Err(LeafHalt::Refused(InferenceRefusal::UnsafeConstant {
                        name: name.clone(),
                    }));
                }
                if definition_safety == Some(DefinitionSafety::Partial) {
                    return Err(LeafHalt::Refused(InferenceRefusal::PartialConstant {
                        name: name.clone(),
                    }));
                }
            }

            match instantiate_term_parameters_from_level_roots_with(
                declaration.type_(),
                declaration.level_parameters(),
                term.levels(),
                levels,
                control.budget.materialization,
                cancelled,
            ) {
                InstantiationOutcome::Complete(type_) => Ok(type_),
                InstantiationOutcome::Refused(refusal) => Err(LeafHalt::Fault(
                    InferenceFault::ConstantInstantiationRefusal {
                        name: name.clone(),
                        refusal,
                    },
                )),
                InstantiationOutcome::Inconclusive(stop) => {
                    Err(LeafHalt::Stop(InferenceStop::Materialization {
                        phase: InferencePhase::ConstantType,
                        stop,
                        progress: control.progress,
                    }))
                }
                InstantiationOutcome::InternalFault(fault) => {
                    Err(LeafHalt::Fault(InferenceFault::ConstantInstantiation {
                        name: name.clone(),
                        fault,
                    }))
                }
            }
        }
        ExprNode::Apply { .. } => Err(LeafHalt::Deferred(InferenceDeferred::Application)),
        ExprNode::Lambda { .. } => Err(LeafHalt::Deferred(InferenceDeferred::Lambda)),
        ExprNode::Forall { .. } => Err(LeafHalt::Deferred(InferenceDeferred::Forall)),
        ExprNode::Let { .. } => Err(LeafHalt::Deferred(InferenceDeferred::Let)),
        ExprNode::NatLiteral { .. } => Err(LeafHalt::Deferred(InferenceDeferred::NatLiteral)),
        ExprNode::StringLiteral(_) => Err(LeafHalt::Deferred(InferenceDeferred::StringLiteral)),
        ExprNode::Projection { .. } => Err(LeafHalt::Deferred(InferenceDeferred::Projection)),
        ExprNode::Metadata { .. } => Err(LeafHalt::Fault(InferenceFault::ResidualMetadata {
            index: root.index(),
        })),
    }
}

pub fn infer(
    term: &WireExpr,
    context: &InferenceContext,
    mode: InferenceMode,
    budget: InferenceBudget,
) -> InferenceOutcome {
    infer_with(term, context, mode, budget, || false)
}

pub fn infer_with(
    term: &WireExpr,
    context: &InferenceContext,
    mode: InferenceMode,
    budget: InferenceBudget,
    mut cancelled: impl FnMut() -> bool,
) -> InferenceOutcome {
    let mut control = Control::new(budget);
    let result = infer_inner(term, context, mode, &mut control, &mut cancelled);
    finish(result, control.progress)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn private_missing_root_is_an_internal_fault() {
        let root = ExprId::from_index(0).expect("zero expression index exists");
        let broken = WireExpr::from_parts(Vec::new(), Vec::new(), root);
        assert!(matches!(
            infer(
                &broken,
                &InferenceContext::empty(ConstantEnvironment::empty()),
                InferenceMode::InferOnly,
                InferenceBudget::unlimited(),
            ),
            InferenceOutcome::InternalFault {
                fault: InferenceFault::Inspection(TermFault::MissingExpression {
                    input: TermInput::Subject,
                    index: 0,
                }),
                ..
            }
        ));
    }
}
