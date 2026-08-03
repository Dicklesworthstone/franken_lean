//! Resource-counted inference over checker-owned terms.
//!
//! This is the independent checker's typing dispatcher. It implements the
//! closed-term precondition, the leaf rules KR-100 through KR-105, iterative
//! KR-111 metadata transparency, and worklist-driven KR-106 application
//! inference. Later rule families are named by [`InferenceDeferred`] instead of
//! being misreported as rejection.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::defeq::{
    DefEqBudget, DefEqDeferred, DefEqFault, DefEqMismatch, DefEqOutcome, DefEqSide, DefEqStop,
    QuickDefEqBudget, def_eq_with,
};
use crate::environment::{ConstantEnvironment, ConstantSafety, DefinitionSafety};
use crate::instantiate::{
    InstantiationFault, InstantiationOutcome, InstantiationRefusal,
    instantiate_term_parameters_from_level_roots_with,
};
use crate::term::{
    TermBudget, TermFault, TermInput, TermLimit, TermOutcome, TermStop, copy_subterm_with,
    inspect_with, substitute_bound_subterms_with,
};
use crate::whnf::{
    FreeBinding, ProjectionRule, WhnfBudget, WhnfContext, WhnfFault, WhnfOutcome, WhnfRefusal,
    WhnfStop, whnf_with,
};
use crate::wire::{
    ExprId, ExprNode, LevelId, LevelNode, NamePart, WireExpr, WireName, expression_owned_units,
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
    value: Option<Arc<WireExpr>>,
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
            value: Some(Arc::new(value)),
        }
    }

    pub fn name(&self) -> &WireName {
        &self.name
    }

    pub fn type_(&self) -> &WireExpr {
        &self.type_
    }

    pub fn value(&self) -> Option<&WireExpr> {
        self.value.as_deref()
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
    DuplicateProjectionRule {
        structure_name: WireName,
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
    reduction: Arc<WhnfContext>,
}

impl InferenceContext {
    pub fn new(
        locals: Vec<LocalDeclaration>,
        level_parameters: Vec<WireName>,
        constants: ConstantEnvironment,
    ) -> Result<InferenceContext, InferenceContextRefusal> {
        Self::new_with_projection_rules(locals, level_parameters, Vec::new(), constants)
    }

    pub fn new_with_projection_rules(
        locals: Vec<LocalDeclaration>,
        level_parameters: Vec<WireName>,
        projection_rules: Vec<ProjectionRule>,
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

        let mut projection_indexes = BTreeMap::new();
        for (index, rule) in projection_rules.iter().enumerate() {
            if let Some(first) = projection_indexes.insert(rule.structure_name().clone(), index) {
                return Err(InferenceContextRefusal::DuplicateProjectionRule {
                    structure_name: rule.structure_name().clone(),
                    first,
                    second: index,
                });
            }
        }

        let free_bindings = locals
            .iter()
            .filter_map(|local| {
                local
                    .value
                    .as_ref()
                    .map(|value| FreeBinding::from_shared(local.name().clone(), Arc::clone(value)))
            })
            .collect();
        let reduction = Arc::new(WhnfContext::new(free_bindings, projection_rules, constants));

        Ok(InferenceContext {
            locals: Arc::new(locals),
            local_indexes: Arc::new(local_indexes),
            level_parameters: Arc::new(level_parameters),
            level_parameter_set: Arc::new(level_parameter_set),
            reduction,
        })
    }

    pub fn empty(constants: ConstantEnvironment) -> InferenceContext {
        InferenceContext {
            locals: Arc::new(Vec::new()),
            local_indexes: Arc::new(BTreeMap::new()),
            level_parameters: Arc::new(Vec::new()),
            level_parameter_set: Arc::new(BTreeSet::new()),
            reduction: Arc::new(WhnfContext::new(Vec::new(), Vec::new(), constants)),
        }
    }

    pub fn locals(&self) -> &[LocalDeclaration] {
        &self.locals
    }

    pub fn level_parameters(&self) -> &[WireName] {
        &self.level_parameters
    }

    pub fn constants(&self) -> &ConstantEnvironment {
        self.reduction.constants()
    }

    pub fn projection_rules(&self) -> &[ProjectionRule] {
        self.reduction.projection_rules()
    }

    fn local(&self, name: &WireName) -> Option<&LocalDeclaration> {
        self.local_indexes
            .get(name)
            .and_then(|index| self.locals.get(*index))
    }

    fn declares_level_parameter(&self, name: &WireName) -> bool {
        self.level_parameter_set.contains(name)
    }

    fn reduction(&self) -> &WhnfContext {
        &self.reduction
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
    pub whnf: WhnfBudget,
    pub defeq: DefEqBudget,
}

impl InferenceBudget {
    pub const fn new(
        max_steps: u64,
        max_level_nodes: u64,
        inspection: TermBudget,
        materialization: TermBudget,
    ) -> InferenceBudget {
        let whnf = WhnfBudget::new(max_steps, max_steps, materialization);
        InferenceBudget {
            max_steps,
            max_level_nodes,
            inspection,
            materialization,
            whnf,
            defeq: DefEqBudget::new(
                QuickDefEqBudget::new(max_steps, max_level_nodes),
                max_steps,
                max_steps,
                materialization.max_arena_nodes,
                materialization.max_output_units,
                whnf,
            ),
        }
    }

    pub const fn with_whnf(mut self, whnf: WhnfBudget) -> InferenceBudget {
        self.whnf = whnf;
        self
    }

    pub const fn with_defeq(mut self, defeq: DefEqBudget) -> InferenceBudget {
        self.defeq = defeq;
        self
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
    pub application_spine_nodes: u64,
    pub application_arguments: u64,
    pub whnf_queries: u64,
    pub defeq_queries: u64,
    pub eager_argument_checks: u64,
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
    ApplicationTerm,
    ApplicationSpine,
    FunctionType,
    ApplicationDomain,
    ArgumentType,
    DomainComparison,
    Codomain,
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
    Whnf {
        argument: usize,
        stop: Box<WhnfStop>,
        progress: InferenceProgress,
    },
    DefEq {
        argument: usize,
        stop: Box<DefEqStop>,
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
    FunctionExpected {
        argument: usize,
    },
    ApplicationTypeMismatch {
        argument: usize,
        mismatch: DefEqMismatch,
    },
    ReductionRefusal {
        argument: usize,
        refusal: WhnfRefusal,
    },
    ConversionRefusal {
        argument: usize,
        side: DefEqSide,
        refusal: WhnfRefusal,
    },
}

/// Rule families deliberately outside this child.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InferenceDeferred {
    ApplicationConversion {
        argument: usize,
        need: DefEqDeferred,
    },
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
    Whnf {
        argument: usize,
        fault: WhnfFault,
    },
    DefEq {
        argument: usize,
        fault: DefEqFault,
    },
    MissingGeneratedArena {
        generation: usize,
    },
    EmptyWorklist,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ArenaSource {
    Input,
    Generated(usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct TermReference {
    source: ArenaSource,
    root: ExprId,
}

enum Dispatch {
    Type(WireExpr),
    Application {
        head: TermReference,
        arguments: Vec<TermReference>,
    },
}

enum Continuation {
    ApplicationHead {
        arguments: Vec<TermReference>,
    },
    ApplicationArgument {
        arguments: Vec<TermReference>,
        index: usize,
        function: FunctionState,
        domain: WireExpr,
        argument: TermReference,
        conversion: ConversionMode,
    },
}

struct FunctionState {
    term: WireExpr,
    root: ExprId,
    instantiations: Vec<TermReference>,
}

impl FunctionState {
    fn new(term: WireExpr) -> FunctionState {
        let root = term.root();
        FunctionState {
            term,
            root,
            instantiations: Vec::new(),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ConversionMode {
    Ordinary,
    EagerReduce,
}

fn inference_arena<'a>(
    input: &'a WireExpr,
    generated: &'a [WireExpr],
    source: ArenaSource,
) -> Result<&'a WireExpr, LeafHalt> {
    match source {
        ArenaSource::Input => Ok(input),
        ArenaSource::Generated(generation) => generated.get(generation).ok_or(LeafHalt::Fault(
            InferenceFault::MissingGeneratedArena { generation },
        )),
    }
}

fn dispatch_reference(
    input: &WireExpr,
    generated: &[WireExpr],
    reference: TermReference,
    context: &InferenceContext,
    mode: InferenceMode,
    control: &mut Control,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<Dispatch, LeafHalt> {
    let term = inference_arena(input, generated, reference.source)?;
    control
        .step(
            cancelled,
            InferencePhase::Precondition,
            reference.root.index(),
        )
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

    let mut root = reference.root;
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
            .map(Dispatch::Type)
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
            .map(Dispatch::Type)
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
                InstantiationOutcome::Complete(type_) => Ok(Dispatch::Type(type_)),
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
        ExprNode::Apply { .. } => {
            let mut cursor = root;
            let mut arguments = Vec::new();
            loop {
                let current = term.node(cursor).ok_or(LeafHalt::Fault(
                    InferenceFault::MissingExpression {
                        index: cursor.index(),
                    },
                ))?;
                let ExprNode::Apply { function, argument } = current else {
                    break;
                };
                control
                    .step(cancelled, InferencePhase::ApplicationSpine, cursor.index())
                    .map_err(LeafHalt::Stop)?;
                control.progress.application_spine_nodes =
                    control.progress.application_spine_nodes.saturating_add(1);
                arguments.push(TermReference {
                    source: reference.source,
                    root: *argument,
                });
                cursor = *function;
            }
            arguments.reverse();
            Ok(Dispatch::Application {
                head: TermReference {
                    source: reference.source,
                    root: cursor,
                },
                arguments,
            })
        }
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

struct InferenceEngine<'a> {
    input: &'a WireExpr,
    context: &'a InferenceContext,
    mode: InferenceMode,
    control: &'a mut Control,
    cancelled: &'a mut dyn FnMut() -> bool,
    generated: Vec<WireExpr>,
    continuations: Vec<Continuation>,
}

impl<'a> InferenceEngine<'a> {
    fn materialize_reference(
        &mut self,
        reference: TermReference,
    ) -> Result<TermReference, LeafHalt> {
        let already_root = {
            let arena = inference_arena(self.input, &self.generated, reference.source)?;
            arena.root() == reference.root
        };
        if already_root {
            return Ok(reference);
        }

        self.control
            .step(
                self.cancelled,
                InferencePhase::ApplicationTerm,
                reference.root.index(),
            )
            .map_err(LeafHalt::Stop)?;
        let result = {
            let arena = inference_arena(self.input, &self.generated, reference.source)?;
            copy_subterm_with(
                arena,
                reference.root,
                self.control.budget.materialization,
                self.cancelled,
            )
        };
        let term = map_materialization(
            result,
            InferencePhase::ApplicationTerm,
            self.control.progress,
        )?;
        let generation = self.generated.len();
        let root = term.root();
        self.generated.push(term);
        Ok(TermReference {
            source: ArenaSource::Generated(generation),
            root,
        })
    }

    fn materialize_function_subterm(
        &mut self,
        function: &FunctionState,
        root: ExprId,
        phase: InferencePhase,
    ) -> Result<WireExpr, LeafHalt> {
        let mut result = map_materialization(
            copy_subterm_with(
                &function.term,
                root,
                self.control.budget.materialization,
                self.cancelled,
            ),
            phase,
            self.control.progress,
        )?;
        let external_bound_span = match inspect_with(
            &result,
            self.control.budget.inspection,
            &mut *self.cancelled,
        ) {
            TermOutcome::Complete(facts) => facts.external_bound_span,
            TermOutcome::Inconclusive(stop) => {
                return Err(LeafHalt::Stop(InferenceStop::Inspection {
                    stop,
                    progress: self.control.progress,
                }));
            }
            TermOutcome::InternalFault(fault) => {
                return Err(LeafHalt::Fault(InferenceFault::Inspection(fault)));
            }
        };
        let needed = usize::try_from(external_bound_span).map_err(|_| {
            LeafHalt::Fault(InferenceFault::LooseBoundVariables {
                external_bound_span,
            })
        })?;
        if needed > function.instantiations.len() {
            return Err(LeafHalt::Fault(InferenceFault::LooseBoundVariables {
                external_bound_span,
            }));
        }

        let first = function.instantiations.len() - needed;
        for replacement in function.instantiations[first..].iter().rev() {
            let replacement_term =
                inference_arena(self.input, &self.generated, replacement.source)?;
            let result_root = result.root();
            result = map_materialization(
                substitute_bound_subterms_with(
                    &result,
                    result_root,
                    0,
                    replacement_term,
                    replacement.root,
                    self.control.budget.materialization,
                    self.cancelled,
                ),
                phase,
                self.control.progress,
            )?;
        }
        Ok(result)
    }

    fn ensure_pi(
        &mut self,
        mut function: FunctionState,
        argument: usize,
    ) -> Result<FunctionState, LeafHalt> {
        self.control
            .step(
                self.cancelled,
                InferencePhase::FunctionType,
                function.root.index(),
            )
            .map_err(LeafHalt::Stop)?;
        if !matches!(
            function.term.node(function.root),
            Some(ExprNode::Forall { .. })
        ) {
            self.control.progress.whnf_queries =
                self.control.progress.whnf_queries.saturating_add(1);
            let instantiated = self.materialize_function_subterm(
                &function,
                function.root,
                InferencePhase::FunctionType,
            )?;
            let function_type = match whnf_with(
                &instantiated,
                self.context.reduction(),
                self.control.budget.whnf,
                &mut *self.cancelled,
            ) {
                WhnfOutcome::Complete(result) => result.term,
                WhnfOutcome::Refused(refusal) => {
                    return Err(LeafHalt::Refused(InferenceRefusal::ReductionRefusal {
                        argument,
                        refusal,
                    }));
                }
                WhnfOutcome::Inconclusive(stop) => {
                    return Err(LeafHalt::Stop(InferenceStop::Whnf {
                        argument,
                        stop: Box::new(stop),
                        progress: self.control.progress,
                    }));
                }
                WhnfOutcome::InternalFault(fault) => {
                    return Err(LeafHalt::Fault(InferenceFault::Whnf { argument, fault }));
                }
            };
            function = FunctionState::new(function_type);
        }
        if matches!(
            function.term.node(function.root),
            Some(ExprNode::Forall { .. })
        ) {
            Ok(function)
        } else {
            Err(LeafHalt::Refused(InferenceRefusal::FunctionExpected {
                argument,
            }))
        }
    }

    fn pi_parts(function: &FunctionState) -> Result<(ExprId, ExprId), LeafHalt> {
        match function.term.node(function.root) {
            Some(ExprNode::Forall {
                binder_type, body, ..
            }) => Ok((*binder_type, *body)),
            Some(_) => Err(LeafHalt::Fault(InferenceFault::EmptyWorklist)),
            None => Err(LeafHalt::Fault(InferenceFault::MissingExpression {
                index: function.root.index(),
            })),
        }
    }

    fn copy_domain(
        &mut self,
        function: &FunctionState,
        domain: ExprId,
    ) -> Result<WireExpr, LeafHalt> {
        self.materialize_function_subterm(function, domain, InferencePhase::ApplicationDomain)
    }

    fn conversion_mode(&mut self, argument: TermReference) -> Result<ConversionMode, LeafHalt> {
        let term = inference_arena(self.input, &self.generated, argument.source)?;
        let mut cursor = argument.root;
        let mut arity = 0usize;
        loop {
            let node =
                term.node(cursor)
                    .ok_or(LeafHalt::Fault(InferenceFault::MissingExpression {
                        index: cursor.index(),
                    }))?;
            let ExprNode::Apply { function, .. } = node else {
                break;
            };
            self.control
                .step(
                    self.cancelled,
                    InferencePhase::DomainComparison,
                    cursor.index(),
                )
                .map_err(LeafHalt::Stop)?;
            arity = arity.saturating_add(1);
            if arity > 2 {
                return Ok(ConversionMode::Ordinary);
            }
            cursor = *function;
        }
        let eager = arity == 2
            && matches!(
                term.node(cursor),
                Some(ExprNode::Constant { name, .. })
                    if matches!(
                        name.parts(),
                        [NamePart::Text(component)] if component == "eagerReduce"
                    )
            );
        Ok(if eager {
            ConversionMode::EagerReduce
        } else {
            ConversionMode::Ordinary
        })
    }

    fn infer_only_application(
        &mut self,
        function_type: WireExpr,
        arguments: &[TermReference],
    ) -> Result<WireExpr, LeafHalt> {
        let mut function = FunctionState::new(function_type);
        for (index, argument) in arguments.iter().copied().enumerate() {
            self.control
                .step(
                    self.cancelled,
                    InferencePhase::ApplicationSpine,
                    argument.root.index(),
                )
                .map_err(LeafHalt::Stop)?;
            self.control.progress.application_arguments = self
                .control
                .progress
                .application_arguments
                .saturating_add(1);
            function = self.ensure_pi(function, index)?;
            let (_, body) = Self::pi_parts(&function)?;
            function.root = body;
            function.instantiations.push(argument);
        }
        self.materialize_function_subterm(&function, function.root, InferencePhase::Codomain)
    }

    fn schedule_checking_argument(
        &mut self,
        function: FunctionState,
        arguments: Vec<TermReference>,
        index: usize,
    ) -> Result<(Continuation, TermReference), LeafHalt> {
        let argument = arguments
            .get(index)
            .copied()
            .ok_or(LeafHalt::Fault(InferenceFault::EmptyWorklist))?;
        self.control
            .step(
                self.cancelled,
                InferencePhase::ArgumentType,
                argument.root.index(),
            )
            .map_err(LeafHalt::Stop)?;
        self.control.progress.application_arguments = self
            .control
            .progress
            .application_arguments
            .saturating_add(1);
        let function = self.ensure_pi(function, index)?;
        let (domain_root, _) = Self::pi_parts(&function)?;
        let domain = self.copy_domain(&function, domain_root)?;
        let conversion = self.conversion_mode(argument)?;
        if conversion == ConversionMode::EagerReduce {
            self.control.progress.eager_argument_checks = self
                .control
                .progress
                .eager_argument_checks
                .saturating_add(1);
        }
        Ok((
            Continuation::ApplicationArgument {
                arguments,
                index,
                function,
                domain,
                argument,
                conversion,
            },
            argument,
        ))
    }

    fn compare_domain(
        &mut self,
        argument: usize,
        conversion: ConversionMode,
        actual: &WireExpr,
        expected: &WireExpr,
    ) -> Result<(), LeafHalt> {
        self.control
            .step(self.cancelled, InferencePhase::DomainComparison, argument)
            .map_err(LeafHalt::Stop)?;
        self.control.progress.defeq_queries = self.control.progress.defeq_queries.saturating_add(1);
        // The current independent conversion engine has no eager-sensitive
        // native or open-pair reduction rule. Carry the marker as query-local
        // state so adding such a rule cannot require mutable context state or
        // leak into the next conversion query.
        let outcome = match conversion {
            ConversionMode::Ordinary | ConversionMode::EagerReduce => def_eq_with(
                actual,
                expected,
                self.context.reduction(),
                self.control.budget.defeq,
                &mut *self.cancelled,
            ),
        };
        match outcome {
            DefEqOutcome::Equal(_) => Ok(()),
            DefEqOutcome::NotEqual { mismatch, .. } => Err(LeafHalt::Refused(
                InferenceRefusal::ApplicationTypeMismatch { argument, mismatch },
            )),
            DefEqOutcome::Deferred { need, .. } => Err(LeafHalt::Deferred(
                InferenceDeferred::ApplicationConversion { argument, need },
            )),
            DefEqOutcome::Refused { side, refusal, .. } => {
                Err(LeafHalt::Refused(InferenceRefusal::ConversionRefusal {
                    argument,
                    side,
                    refusal,
                }))
            }
            DefEqOutcome::Inconclusive(stop) => Err(LeafHalt::Stop(InferenceStop::DefEq {
                argument,
                stop: Box::new(stop),
                progress: self.control.progress,
            })),
            DefEqOutcome::InternalFault(fault) => {
                Err(LeafHalt::Fault(InferenceFault::DefEq { argument, fault }))
            }
        }
    }

    fn run(&mut self) -> Result<WireExpr, LeafHalt> {
        let mut current = Some(TermReference {
            source: ArenaSource::Input,
            root: self.input.root(),
        });
        let mut inferred = None;

        loop {
            if let Some(reference) = current.take() {
                let reference = self.materialize_reference(reference)?;
                match dispatch_reference(
                    self.input,
                    &self.generated,
                    reference,
                    self.context,
                    self.mode,
                    self.control,
                    self.cancelled,
                )? {
                    Dispatch::Type(type_) => inferred = Some(type_),
                    Dispatch::Application { head, arguments } => {
                        self.continuations
                            .push(Continuation::ApplicationHead { arguments });
                        current = Some(head);
                    }
                }
                continue;
            }

            let value = inferred
                .take()
                .ok_or(LeafHalt::Fault(InferenceFault::EmptyWorklist))?;
            let Some(continuation) = self.continuations.pop() else {
                return Ok(value);
            };
            match continuation {
                Continuation::ApplicationHead { arguments } => {
                    if self.mode == InferenceMode::InferOnly {
                        inferred = Some(self.infer_only_application(value, &arguments)?);
                    } else {
                        let (continuation, argument) = self.schedule_checking_argument(
                            FunctionState::new(value),
                            arguments,
                            0,
                        )?;
                        self.continuations.push(continuation);
                        current = Some(argument);
                    }
                }
                Continuation::ApplicationArgument {
                    arguments,
                    index,
                    mut function,
                    domain,
                    argument,
                    conversion,
                } => {
                    self.compare_domain(index, conversion, &value, &domain)?;
                    let (_, body) = Self::pi_parts(&function)?;
                    function.root = body;
                    function.instantiations.push(argument);
                    let next = index.saturating_add(1);
                    if next == arguments.len() {
                        inferred = Some(self.materialize_function_subterm(
                            &function,
                            function.root,
                            InferencePhase::Codomain,
                        )?);
                    } else {
                        let (continuation, argument) =
                            self.schedule_checking_argument(function, arguments, next)?;
                        self.continuations.push(continuation);
                        current = Some(argument);
                    }
                }
            }
        }
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
    let result = InferenceEngine {
        input: term,
        context,
        mode,
        control: &mut control,
        cancelled: &mut cancelled,
        generated: Vec::new(),
        continuations: Vec::new(),
    }
    .run();
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
