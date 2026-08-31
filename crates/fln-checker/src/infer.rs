//! Resource-counted inference over checker-owned terms.
//!
//! This is the independent checker's typing dispatcher. It implements the
//! closed-term precondition, the leaf rules KR-100 through KR-105, iterative
//! KR-111 metadata transparency, worklist-driven KR-106 application inference,
//! stack-safe KR-107 lambda-telescope inference, and stack-safe KR-108 Forall
//! inference with checker-owned right-associated `imax`. Later rule families
//! are named by [`InferenceDeferred`] instead of being misreported as rejection.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::defeq::{
    DefEqBudget, DefEqDeferred, DefEqFault, DefEqMismatch, DefEqOutcome, DefEqSide, DefEqStop,
    QuickDefEqBudget, def_eq_eager_with, def_eq_with,
};
use crate::environment::{ConstantEnvironment, ConstantKind, ConstantSafety, DefinitionSafety};
use crate::instantiate::{
    InstantiationFault, InstantiationOutcome, InstantiationRefusal,
    instantiate_term_parameters_from_level_roots_with,
};
use crate::term::{
    TermBudget, TermFault, TermInput, TermLimit, TermOutcome, TermStop,
    abstract_free_telescope_with, copy_compact_subterm_with, copy_subterm_with, inspect_with,
    substitute_bound_subterms_with, substitute_free_with,
};
use crate::whnf::{
    FreeBinding, ProjectionRule, WhnfBudget, WhnfContext, WhnfFault, WhnfOutcome, WhnfRefusal,
    WhnfStop, whnf_with,
};
use crate::wire::{
    BinderStyle, ExprId, ExprNode, LevelId, LevelNode, MAX_BVAR_INDEX, NamePart, WireExpr,
    WireName, expression_owned_units, level_owned_units, name_owned_units, usize_units,
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

    /// The reduction context this inference context reduces in.
    ///
    /// Public so that `admit`'s KR-972 sort check reduces in the **same** context
    /// the declared type was inferred in. The alternative — rebuilding a
    /// `WhnfContext` from the same inputs at the call site — is a second copy of
    /// this construction, free to drift from it the moment either grows a field.
    pub fn reduction(&self) -> &WhnfContext {
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
    pub reserved_free_names: u64,
    pub local_identity_candidates: u64,
    pub lambda_telescope_nodes: u64,
    pub lambda_binders: u64,
    pub lambda_domain_queries: u64,
    pub lambda_body_queries: u64,
    pub binder_sort_checks: u64,
    pub cheap_beta_steps: u64,
    pub forall_telescope_nodes: u64,
    pub forall_binders: u64,
    pub forall_domain_queries: u64,
    pub forall_body_queries: u64,
    pub forall_sort_checks: u64,
    pub forall_imax_nodes: u64,
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
    LocalIdentity,
    LambdaTelescope,
    LambdaDomain,
    BinderSort,
    LambdaBody,
    CheapBeta,
    PiAbstraction,
    ForallTelescope,
    ForallDomain,
    ForallDomainSort,
    ForallBody,
    ForallCodomainSort,
    ForallUniverse,
    LetTelescope,
    LetDeclaredType,
    LetDeclaredTypeSort,
    LetValue,
    LetValueComparison,
    LetBody,
    LetZeta,
    LiteralType,
    ProjectionScrutinee,
    ProjectionWhnf,
    ProjectionField,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InferenceSortSite {
    LambdaBinder { binder: usize },
    ForallBinder { binder: usize },
    ForallCodomain { binders: usize },
    LetBinder { binder: usize },
}

impl InferenceSortSite {
    const fn phase(self) -> InferencePhase {
        match self {
            InferenceSortSite::LambdaBinder { .. } => InferencePhase::BinderSort,
            InferenceSortSite::ForallBinder { .. } => InferencePhase::ForallDomainSort,
            InferenceSortSite::ForallCodomain { .. } => InferencePhase::ForallCodomainSort,
            InferenceSortSite::LetBinder { .. } => InferencePhase::LetDeclaredTypeSort,
        }
    }

    const fn at(self) -> usize {
        match self {
            InferenceSortSite::LambdaBinder { binder }
            | InferenceSortSite::ForallBinder { binder }
            | InferenceSortSite::LetBinder { binder } => binder,
            InferenceSortSite::ForallCodomain { binders } => binders,
        }
    }

    const fn is_forall(self) -> bool {
        matches!(
            self,
            InferenceSortSite::ForallBinder { .. } | InferenceSortSite::ForallCodomain { .. }
        )
    }

    const fn is_let(self) -> bool {
        matches!(self, InferenceSortSite::LetBinder { .. })
    }
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
    SortWhnf {
        site: InferenceSortSite,
        stop: Box<WhnfStop>,
        progress: InferenceProgress,
    },
    /// KR-109: the let value / declared type conversion exhausted its budget or
    /// was cancelled. Separate from [`InferenceStop::DefEq`] because that one is
    /// keyed by an application argument ordinal, which a let has none of.
    LetValueDefEq {
        binder: usize,
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
    SortExpected {
        site: InferenceSortSite,
    },
    SortReductionRefusal {
        site: InferenceSortSite,
        refusal: WhnfRefusal,
    },
    /// KR-112: no projection rule is registered for the named structure. The
    /// rules are CALLER-SUPPLIED through the reduction context, so their absence
    /// is untrusted input rather than an internal inconsistency.
    ProjectionRuleMissing {
        structure: WireName,
    },
    /// KR-112: the scrutinee's type did not reduce to an application of the
    /// structure the projection names.
    ProjectionStructureMismatch {
        expected: WireName,
    },
    /// KR-112: the projection rule names a constant that is not declared as a
    /// constructor. Caller-supplied metadata, so this is untrusted input.
    ProjectionConstructorKind {
        constructor: WireName,
    },
    /// KR-112: the rule's parameter_count exceeds the arguments the scrutinee's
    /// type actually supplies, or the constructor telescope is shorter than the
    /// parameters plus the requested field.
    ProjectionArityExceeded {
        structure: WireName,
        needed: usize,
        available: usize,
    },
    /// KR-109: the let value's inferred type is not definitionally equal to the
    /// declared type. The binder ordinal is retained because a let telescope is
    /// flattened, so "which let" is not recoverable from the term root.
    LetValueTypeMismatch {
        binder: usize,
        mismatch: DefEqMismatch,
    },
    /// KR-109: reduction refused while comparing a let value against its
    /// declared type. Distinct from the mismatch above: nothing was decided.
    LetValueConversionRefusal {
        binder: usize,
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
    /// KR-109: the let value / declared type conversion could not be decided
    /// within the definitional-equality budget. Never a rejection.
    LetValueConversion { binder: usize, need: DefEqDeferred },
    // NatLiteral, StringLiteral and Projection were REMOVED here, not merely left
    // unconstructed. KR-110 and KR-112 implemented those rules and stopped
    // building the variants, but the enum went on advertising three rule families
    // as unimplemented -- a declared set that had quietly become a lie.
    // `no_rule_family_deferral_remains_reachable` matches this enum EXHAUSTIVELY,
    // so it failed to COMPILE until they were gone, and a future rule family
    // added as a deferral fails the same way rather than slipping in unnoticed.
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
    /// KR-110: the one-node arena for a literal's type constant could not be
    /// allocated, or its root index did not construct. A unit variant so the
    /// fault costs no width in a type returned by value on the hot path.
    LiteralTypeAllocation,
    /// KR-109: an internal fault raised while comparing a let value against its
    /// declared type. Keyed by binder ordinal, not by argument ordinal.
    LetValueDefEq {
        binder: usize,
        fault: DefEqFault,
    },
    DefEq {
        argument: usize,
        fault: DefEqFault,
    },
    SortWhnf {
        site: InferenceSortSite,
        fault: WhnfFault,
    },
    FreshLocalIdentityExhausted,
    ScopedLocalCollision {
        name: WireName,
    },
    MissingScopedLocal {
        name: WireName,
    },
    MissingGeneratedArena {
        generation: usize,
    },
    RetainedSortExpected {
        position: usize,
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
    ) -> Result<(), Box<InferenceStop>> {
        self.polls = self.polls.saturating_add(1);
        if cancelled() {
            return Err(Box::new(InferenceStop::Cancelled {
                phase,
                at,
                polls: self.polls,
                progress: self.progress,
            }));
        }
        Ok(())
    }

    fn step(
        &mut self,
        cancelled: &mut dyn FnMut() -> bool,
        phase: InferencePhase,
        at: usize,
    ) -> Result<(), Box<InferenceStop>> {
        self.poll(cancelled, phase, at)?;
        let observed = self.progress.steps.saturating_add(1);
        if observed > self.budget.max_steps {
            return Err(Box::new(InferenceStop::Resource {
                limit: InferenceLimit::Steps,
                allowed: self.budget.max_steps,
                observed,
                phase,
                at,
                progress: self.progress,
            }));
        }
        self.progress.steps = observed;
        Ok(())
    }

    fn level_node(&mut self, at: usize) -> Result<(), Box<InferenceStop>> {
        let observed = self.progress.level_nodes.saturating_add(1);
        if observed > self.budget.max_level_nodes {
            return Err(Box::new(InferenceStop::Resource {
                limit: InferenceLimit::LevelNodes,
                allowed: self.budget.max_level_nodes,
                observed,
                phase: InferencePhase::UniverseValidation,
                at,
                progress: self.progress,
            }));
        }
        self.progress.level_nodes = observed;
        Ok(())
    }
}

enum LeafHalt {
    Refused(InferenceRefusal),
    Deferred(InferenceDeferred),
    Stop(Box<InferenceStop>),
    Fault(InferenceFault),
}

impl LeafHalt {
    fn stop(stop: impl Into<Box<InferenceStop>>) -> LeafHalt {
        LeafHalt::Stop(stop.into())
    }
}

fn finish(result: Result<WireExpr, LeafHalt>, progress: InferenceProgress) -> InferenceOutcome {
    match result {
        Ok(type_) => InferenceOutcome::Complete(InferenceResult { type_, progress }),
        Err(LeafHalt::Refused(refusal)) => InferenceOutcome::Refused { refusal, progress },
        Err(LeafHalt::Deferred(requirement)) => InferenceOutcome::Deferred {
            requirement,
            progress,
        },
        Err(LeafHalt::Stop(stop)) => InferenceOutcome::Inconclusive(*stop),
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
                .map_err(LeafHalt::stop)?;
            control.level_node(id.index()).map_err(LeafHalt::stop)?;
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
        TermOutcome::Inconclusive(stop) => Err(LeafHalt::stop(InferenceStop::Materialization {
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

fn map_assembly<T>(
    result: Result<T, MaterializeHalt>,
    phase: InferencePhase,
    progress: InferenceProgress,
) -> Result<T, LeafHalt> {
    match result {
        Ok(value) => Ok(value),
        Err(MaterializeHalt::Stop(stop)) => Err(LeafHalt::stop(InferenceStop::Materialization {
            phase,
            stop,
            progress,
        })),
        Err(MaterializeHalt::Fault(fault)) => {
            Err(LeafHalt::Fault(InferenceFault::Materialization {
                phase,
                fault,
            }))
        }
    }
}

fn materialize_free(
    name: &WireName,
    budget: TermBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> TermOutcome<WireExpr> {
    let mut control = MaterializationControl::new(budget, cancelled);
    if let Err(halt) = control.step(0) {
        return materialize_halted(halt);
    }
    let output_units = 1u64.saturating_add(name_owned_units(name));
    if let Err(halt) = control.output(output_units, 0) {
        return materialize_halted(halt);
    }
    if let Err(halt) = control.arena_node(1, 0) {
        return materialize_halted(halt);
    }
    let Some(root) = ExprId::from_index(0) else {
        return TermOutcome::Inconclusive(TermStop::Resource {
            limit: TermLimit::ArenaNodes,
            allowed: budget.max_arena_nodes.min(u64::from(u32::MAX)),
            observed: 1,
            at: 0,
            completed_steps: control.steps,
        });
    };
    TermOutcome::Complete(WireExpr::from_parts(
        vec![ExprNode::Free { name: name.clone() }],
        Vec::new(),
        root,
    ))
}

struct ArenaAssembler<'a> {
    control: MaterializationControl<'a>,
    nodes: Vec<ExprNode>,
    levels: Vec<LevelNode>,
}

impl<'a> ArenaAssembler<'a> {
    fn new(budget: TermBudget, cancelled: &'a mut dyn FnMut() -> bool) -> ArenaAssembler<'a> {
        ArenaAssembler {
            control: MaterializationControl::new(budget, cancelled),
            nodes: Vec::new(),
            levels: Vec::new(),
        }
    }

    fn total_nodes(&self, additional: u64) -> u64 {
        usize_units(self.levels.len())
            .saturating_add(usize_units(self.nodes.len()))
            .saturating_add(additional)
    }

    fn mapped_level(
        source: &WireExpr,
        parent: usize,
        child: LevelId,
        offset: usize,
        at: usize,
        control: &MaterializationControl<'_>,
    ) -> Result<LevelId, MaterializeHalt> {
        if child.index() >= parent {
            return Err(MaterializeHalt::Fault(
                TermFault::NonBackwardLevelReference {
                    input: TermInput::Subject,
                    parent,
                    child: child.index(),
                },
            ));
        }
        if source.level(child).is_none() {
            return Err(MaterializeHalt::Fault(TermFault::MissingLevel {
                input: TermInput::Subject,
                index: child.index(),
            }));
        }
        let mapped = offset.saturating_add(child.index());
        LevelId::from_index(mapped).ok_or_else(|| {
            MaterializeHalt::Stop(TermStop::Resource {
                limit: TermLimit::ArenaNodes,
                allowed: control.budget.max_arena_nodes.min(u64::from(u32::MAX)),
                observed: usize_units(mapped).saturating_add(1),
                at,
                completed_steps: control.steps,
            })
        })
    }

    fn mapped_level_root(
        source: &WireExpr,
        child: LevelId,
        offset: usize,
        at: usize,
        control: &MaterializationControl<'_>,
    ) -> Result<LevelId, MaterializeHalt> {
        if source.level(child).is_none() {
            return Err(MaterializeHalt::Fault(TermFault::MissingLevel {
                input: TermInput::Subject,
                index: child.index(),
            }));
        }
        let mapped = offset.saturating_add(child.index());
        LevelId::from_index(mapped).ok_or_else(|| {
            MaterializeHalt::Stop(TermStop::Resource {
                limit: TermLimit::ArenaNodes,
                allowed: control.budget.max_arena_nodes.min(u64::from(u32::MAX)),
                observed: usize_units(mapped).saturating_add(1),
                at,
                completed_steps: control.steps,
            })
        })
    }

    fn mapped_expression(
        source: &WireExpr,
        parent: usize,
        child: ExprId,
        offset: usize,
        at: usize,
        control: &MaterializationControl<'_>,
    ) -> Result<ExprId, MaterializeHalt> {
        if child.index() >= parent {
            return Err(MaterializeHalt::Fault(
                TermFault::NonBackwardExpressionReference {
                    input: TermInput::Subject,
                    parent,
                    child: child.index(),
                },
            ));
        }
        if source.node(child).is_none() {
            return Err(MaterializeHalt::Fault(TermFault::MissingExpression {
                input: TermInput::Subject,
                index: child.index(),
            }));
        }
        let mapped = offset.saturating_add(child.index());
        ExprId::from_index(mapped).ok_or_else(|| {
            MaterializeHalt::Stop(TermStop::Resource {
                limit: TermLimit::ArenaNodes,
                allowed: control.budget.max_arena_nodes.min(u64::from(u32::MAX)),
                observed: usize_units(mapped).saturating_add(1),
                at,
                completed_steps: control.steps,
            })
        })
    }

    fn append_levels(&mut self, source: &WireExpr) -> Result<usize, MaterializeHalt> {
        let level_offset = self.levels.len();
        for (index, node) in source.levels().iter().enumerate() {
            let at = self.levels.len();
            self.control.step(at)?;
            self.control.output(level_owned_units(node), at)?;
            let mapped = match node {
                LevelNode::Zero => LevelNode::Zero,
                LevelNode::Succ(child) => LevelNode::Succ(Self::mapped_level(
                    source,
                    index,
                    *child,
                    level_offset,
                    at,
                    &self.control,
                )?),
                LevelNode::Max(left, right) => LevelNode::Max(
                    Self::mapped_level(source, index, *left, level_offset, at, &self.control)?,
                    Self::mapped_level(source, index, *right, level_offset, at, &self.control)?,
                ),
                LevelNode::IMax(left, right) => LevelNode::IMax(
                    Self::mapped_level(source, index, *left, level_offset, at, &self.control)?,
                    Self::mapped_level(source, index, *right, level_offset, at, &self.control)?,
                ),
                LevelNode::Parameter(name) => LevelNode::Parameter(name.clone()),
                LevelNode::Meta(name) => LevelNode::Meta(name.clone()),
            };
            self.control.arena_node(self.total_nodes(1), at)?;
            if LevelId::from_index(self.levels.len()).is_none() {
                return Err(MaterializeHalt::Stop(TermStop::Resource {
                    limit: TermLimit::ArenaNodes,
                    allowed: self.control.budget.max_arena_nodes.min(u64::from(u32::MAX)),
                    observed: self.total_nodes(1),
                    at,
                    completed_steps: self.control.steps,
                }));
            }
            self.levels.push(mapped);
        }
        Ok(level_offset)
    }

    fn append_level_root(
        &mut self,
        source: &WireExpr,
        root: LevelId,
    ) -> Result<LevelId, MaterializeHalt> {
        let level_offset = self.append_levels(source)?;
        Self::mapped_level_root(source, root, level_offset, self.levels.len(), &self.control)
    }

    fn append(&mut self, source: &WireExpr) -> Result<ExprId, MaterializeHalt> {
        let level_offset = self.append_levels(source)?;
        let expression_offset = self.nodes.len();
        for (index, node) in source.nodes().iter().enumerate() {
            let at = self.nodes.len();
            self.control.step(at)?;
            self.control.output(expression_owned_units(node), at)?;
            let map_expression = |child| {
                Self::mapped_expression(source, index, child, expression_offset, at, &self.control)
            };
            let map_level =
                |level| Self::mapped_level_root(source, level, level_offset, at, &self.control);
            let mapped = match node {
                ExprNode::Bound { index } => ExprNode::Bound { index: *index },
                ExprNode::Free { name } => ExprNode::Free { name: name.clone() },
                ExprNode::Meta { name } => ExprNode::Meta { name: name.clone() },
                ExprNode::Sort { level } => ExprNode::Sort {
                    level: map_level(*level)?,
                },
                ExprNode::Constant { name, levels } => ExprNode::Constant {
                    name: name.clone(),
                    levels: levels
                        .iter()
                        .map(|level| map_level(*level))
                        .collect::<Result<Vec<_>, _>>()?,
                },
                ExprNode::Apply { function, argument } => ExprNode::Apply {
                    function: map_expression(*function)?,
                    argument: map_expression(*argument)?,
                },
                ExprNode::Lambda {
                    binder_name,
                    binder_type,
                    body,
                    style,
                } => ExprNode::Lambda {
                    binder_name: binder_name.clone(),
                    binder_type: map_expression(*binder_type)?,
                    body: map_expression(*body)?,
                    style: *style,
                },
                ExprNode::Forall {
                    binder_name,
                    binder_type,
                    body,
                    style,
                } => ExprNode::Forall {
                    binder_name: binder_name.clone(),
                    binder_type: map_expression(*binder_type)?,
                    body: map_expression(*body)?,
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
                    type_: map_expression(*type_)?,
                    value: map_expression(*value)?,
                    body: map_expression(*body)?,
                    non_dependent: *non_dependent,
                },
                ExprNode::NatLiteral { limbs_le } => ExprNode::NatLiteral {
                    limbs_le: limbs_le.clone(),
                },
                ExprNode::StringLiteral(text) => ExprNode::StringLiteral(text.clone()),
                ExprNode::Metadata {
                    entries,
                    expression,
                } => ExprNode::Metadata {
                    entries: entries.clone(),
                    expression: map_expression(*expression)?,
                },
                ExprNode::Projection {
                    structure_name,
                    index,
                    expression,
                } => ExprNode::Projection {
                    structure_name: structure_name.clone(),
                    index: *index,
                    expression: map_expression(*expression)?,
                },
            };
            self.control.arena_node(self.total_nodes(1), at)?;
            if ExprId::from_index(self.nodes.len()).is_none() {
                return Err(MaterializeHalt::Stop(TermStop::Resource {
                    limit: TermLimit::ArenaNodes,
                    allowed: self.control.budget.max_arena_nodes.min(u64::from(u32::MAX)),
                    observed: self.total_nodes(1),
                    at,
                    completed_steps: self.control.steps,
                }));
            }
            self.nodes.push(mapped);
        }

        if source.node(source.root()).is_none() {
            return Err(MaterializeHalt::Fault(TermFault::MissingExpression {
                input: TermInput::Subject,
                index: source.root().index(),
            }));
        }
        let mapped_root = expression_offset.saturating_add(source.root().index());
        ExprId::from_index(mapped_root).ok_or_else(|| {
            MaterializeHalt::Stop(TermStop::Resource {
                limit: TermLimit::ArenaNodes,
                allowed: self.control.budget.max_arena_nodes.min(u64::from(u32::MAX)),
                observed: usize_units(mapped_root).saturating_add(1),
                at: mapped_root,
                completed_steps: self.control.steps,
            })
        })
    }

    fn push_level(&mut self, node: LevelNode) -> Result<LevelId, MaterializeHalt> {
        let at = self.levels.len();
        self.control.step(at)?;
        self.control.output(level_owned_units(&node), at)?;
        let children = match &node {
            LevelNode::Succ(child) => [Some(*child), None],
            LevelNode::Max(left, right) | LevelNode::IMax(left, right) => {
                [Some(*left), Some(*right)]
            }
            LevelNode::Zero | LevelNode::Parameter(_) | LevelNode::Meta(_) => [None, None],
        };
        for child in children.into_iter().flatten() {
            validate_materialized_level_child(&self.levels, at, child)?;
        }
        self.control.arena_node(self.total_nodes(1), at)?;
        let id = LevelId::from_index(self.levels.len()).ok_or_else(|| {
            MaterializeHalt::Stop(TermStop::Resource {
                limit: TermLimit::ArenaNodes,
                allowed: self.control.budget.max_arena_nodes.min(u64::from(u32::MAX)),
                observed: self.total_nodes(1),
                at,
                completed_steps: self.control.steps,
            })
        })?;
        self.levels.push(node);
        Ok(id)
    }

    fn push_sort(&mut self, level: LevelId) -> Result<ExprId, MaterializeHalt> {
        if self.levels.get(level.index()).is_none() {
            return Err(MaterializeHalt::Fault(TermFault::MissingLevel {
                input: TermInput::Subject,
                index: level.index(),
            }));
        }
        let at = self.nodes.len();
        let node = ExprNode::Sort { level };
        self.control.step(at)?;
        self.control.output(expression_owned_units(&node), at)?;
        self.control.arena_node(self.total_nodes(1), at)?;
        let id = ExprId::from_index(self.nodes.len()).ok_or_else(|| {
            MaterializeHalt::Stop(TermStop::Resource {
                limit: TermLimit::ArenaNodes,
                allowed: self.control.budget.max_arena_nodes.min(u64::from(u32::MAX)),
                observed: self.total_nodes(1),
                at,
                completed_steps: self.control.steps,
            })
        })?;
        self.nodes.push(node);
        Ok(id)
    }

    fn push_apply(
        &mut self,
        function: ExprId,
        argument: ExprId,
    ) -> Result<ExprId, MaterializeHalt> {
        let at = self.nodes.len();
        self.control.step(at)?;
        self.control.output(1, at)?;
        self.control.arena_node(self.total_nodes(1), at)?;
        let id = ExprId::from_index(self.nodes.len()).ok_or_else(|| {
            MaterializeHalt::Stop(TermStop::Resource {
                limit: TermLimit::ArenaNodes,
                allowed: self.control.budget.max_arena_nodes.min(u64::from(u32::MAX)),
                observed: self.total_nodes(1),
                at,
                completed_steps: self.control.steps,
            })
        })?;
        self.nodes.push(ExprNode::Apply { function, argument });
        Ok(id)
    }

    /// KR-112: the assembler had no projection constructor; this is its only
    /// caller. Added rather than open-coding an arena, so the node-budget
    /// accounting stays in one place.
    fn push_projection(
        &mut self,
        structure_name: &WireName,
        index: u64,
        expression: ExprId,
    ) -> Result<ExprId, MaterializeHalt> {
        let at = self.nodes.len();
        self.control.step(at)?;
        self.control
            .output(1u64.saturating_add(name_owned_units(structure_name)), at)?;
        self.control.arena_node(self.total_nodes(1), at)?;
        let id = ExprId::from_index(self.nodes.len()).ok_or_else(|| {
            MaterializeHalt::Stop(TermStop::Resource {
                limit: TermLimit::ArenaNodes,
                allowed: self.control.budget.max_arena_nodes.min(u64::from(u32::MAX)),
                observed: self.total_nodes(1),
                at,
                completed_steps: self.control.steps,
            })
        })?;
        self.nodes.push(ExprNode::Projection {
            structure_name: structure_name.clone(),
            index,
            expression,
        });
        Ok(id)
    }

    fn push_forall(
        &mut self,
        binder_name: &WireName,
        style: BinderStyle,
        binder_type: ExprId,
        body: ExprId,
    ) -> Result<ExprId, MaterializeHalt> {
        let at = self.nodes.len();
        self.control.step(at)?;
        self.control
            .output(1u64.saturating_add(name_owned_units(binder_name)), at)?;
        self.control.arena_node(self.total_nodes(1), at)?;
        let id = ExprId::from_index(self.nodes.len()).ok_or_else(|| {
            MaterializeHalt::Stop(TermStop::Resource {
                limit: TermLimit::ArenaNodes,
                allowed: self.control.budget.max_arena_nodes.min(u64::from(u32::MAX)),
                observed: self.total_nodes(1),
                at,
                completed_steps: self.control.steps,
            })
        })?;
        self.nodes.push(ExprNode::Forall {
            binder_name: binder_name.clone(),
            binder_type,
            body,
            style,
        });
        Ok(id)
    }

    fn finish(self, root: ExprId) -> WireExpr {
        WireExpr::from_parts(self.nodes, self.levels, root)
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

struct TelescopeBinderSource {
    display_name: WireName,
    style: BinderStyle,
    domain: TermReference,
}

struct TelescopeBinder {
    display_name: WireName,
    style: BinderStyle,
    local_name: WireName,
    local_reference: TermReference,
    domain: Arc<WireExpr>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TelescopeKind {
    Lambda,
    Forall,
}

/// KR-109: one `let` binder as it appears in the source term.
///
/// The source's display name is deliberately NOT retained. A let is transparent
/// to typing, so the completed type mentions the VALUE and never a binder, and a
/// field nothing reads is a place for a future reader to assume a guarantee that
/// is not made.
struct LetBinderSource {
    declared_type: TermReference,
    value: TermReference,
}

/// KR-109: one `let` binder after its declared type and value have been
/// materialized under the binders to its left.
///
/// `value` is the zeta replacement: the completed body type has this term
/// substituted for `local_name`, which is what makes a let transparent to
/// typing rather than abstracted over like a lambda.
struct LetBinder {
    local_name: WireName,
    local_reference: TermReference,
    declared_type: Arc<WireExpr>,
    value: Arc<WireExpr>,
}

/// KR-109: the flattened let telescope.
///
/// **This rule deliberately adds NO `InferenceProgress` counters**, unlike
/// KR-107 and KR-108 which each carry several. `InferenceProgress` is returned
/// by value through the whole inference path, and eight KR-109 counters took it
/// from 176 to 240 bytes and overflowed the 64 KiB stack the deep-telescope
/// cells run on — in a *forall* test this rule does not touch. The KR-109 cells
/// assert the SEMANTICS instead (the value reaching the type, the internal local
/// not surviving, each nonanswer in its own class), which is what the rule
/// actually claims. `crates/fln-checker/tests/size_probe.rs` holds the ceiling
/// so the next counter fails there rather than in an unrelated rule.
///
/// Nested and sequential lets are collected onto the heap exactly as the lambda
/// and forall telescopes are, because let depth is attacker-controlled and a
/// recursive host traversal over it is the defect the covenant forbids.
struct LetState {
    sources: Vec<LetBinderSource>,
    body: TermReference,
    binders: Vec<LetBinder>,
    next: usize,
    /// The binder currently being checked.
    ///
    /// This lives INSIDE the boxed state rather than in the continuation on
    /// purpose. Carrying it in the `Continuation` variants grew that enum enough
    /// to push `fifty_thousand_binder_forall_telescope_fits_a_64k_stack` — a rule
    /// this slice does not touch — into a stack overflow, because the covenant's
    /// 64 KiB budget leaves no headroom for a wider frame in the dispatch path.
    /// Measured: that test passes at HEAD and overflowed with the payload inline.
    pending: Option<LetPending>,
}

/// KR-112: a projection awaiting its scrutinee's inferred type.
///
/// Boxed in the continuation for the reason `LetState` records: `run` is one
/// frame on a 64 KiB budget shared by every rule.
struct ProjectionState {
    structure_name: WireName,
    index: u64,
    scrutinee: TermReference,
}

/// KR-109: the in-flight binder's materialized parts.
struct LetPending {
    declared_type: Arc<WireExpr>,
    value: Arc<WireExpr>,
    local_name: WireName,
    local_reference: TermReference,
}

struct TelescopeState {
    kind: TelescopeKind,
    sources: Vec<TelescopeBinderSource>,
    body: TermReference,
    binders: Vec<TelescopeBinder>,
    domain_sorts: Vec<WireExpr>,
    next: usize,
}

enum Dispatch {
    Type(WireExpr),
    Application {
        head: TermReference,
        arguments: Vec<TermReference>,
    },
    Lambda {
        binders: Vec<TelescopeBinderSource>,
        body: TermReference,
    },
    Forall {
        binders: Vec<TelescopeBinderSource>,
        body: TermReference,
    },
    Let {
        binders: Vec<LetBinderSource>,
        body: TermReference,
    },
    Projection {
        state: Box<ProjectionState>,
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
    TelescopeDomain {
        state: Box<TelescopeState>,
        domain: Arc<WireExpr>,
        local_name: WireName,
        local_reference: TermReference,
    },
    TelescopeBody {
        state: Box<TelescopeState>,
    },
    /// KR-109: the declared type of `state.next` is being inferred; its own
    /// inferred type must reduce to a Sort. The materialized parts ride in
    /// `state.pending`, so this variant stays one pointer wide.
    LetDeclaredType {
        state: Box<LetState>,
    },
    /// KR-109: the value of `state.next` is being inferred; its inferred type
    /// must be definitionally equal to the declared type.
    LetValue {
        state: Box<LetState>,
    },
    /// KR-109: the let body is being inferred; the result is its type with every
    /// bound value zeta-substituted back in.
    LetBody {
        state: Box<LetState>,
    },
    /// KR-112: the projection's scrutinee is being inferred; its type decides the
    /// structure, its parameters, and therefore the field type.
    ProjectionScrutinee {
        state: Box<ProjectionState>,
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
    generated: &'a [Arc<WireExpr>],
    source: ArenaSource,
) -> Result<&'a WireExpr, LeafHalt> {
    match source {
        ArenaSource::Input => Ok(input),
        ArenaSource::Generated(generation) => {
            generated
                .get(generation)
                .map(Arc::as_ref)
                .ok_or(LeafHalt::Fault(InferenceFault::MissingGeneratedArena {
                    generation,
                }))
        }
    }
}

struct DispatchScope<'a> {
    context: &'a InferenceContext,
    scoped_locals: &'a BTreeMap<WireName, Arc<WireExpr>>,
    mode: InferenceMode,
}

impl TelescopeKind {
    const fn telescope_phase(self) -> InferencePhase {
        match self {
            TelescopeKind::Lambda => InferencePhase::LambdaTelescope,
            TelescopeKind::Forall => InferencePhase::ForallTelescope,
        }
    }

    fn record_binder(self, progress: &mut InferenceProgress) {
        match self {
            TelescopeKind::Lambda => {
                progress.lambda_telescope_nodes = progress.lambda_telescope_nodes.saturating_add(1);
                progress.lambda_binders = progress.lambda_binders.saturating_add(1);
            }
            TelescopeKind::Forall => {
                progress.forall_telescope_nodes = progress.forall_telescope_nodes.saturating_add(1);
                progress.forall_binders = progress.forall_binders.saturating_add(1);
            }
        }
    }

    const fn domain_phase(self) -> InferencePhase {
        match self {
            TelescopeKind::Lambda => InferencePhase::LambdaDomain,
            TelescopeKind::Forall => InferencePhase::ForallDomain,
        }
    }

    const fn body_phase(self) -> InferencePhase {
        match self {
            TelescopeKind::Lambda => InferencePhase::LambdaBody,
            TelescopeKind::Forall => InferencePhase::ForallBody,
        }
    }

    fn record_domain_query(self, progress: &mut InferenceProgress) {
        match self {
            TelescopeKind::Lambda => {
                progress.lambda_domain_queries = progress.lambda_domain_queries.saturating_add(1);
            }
            TelescopeKind::Forall => {
                progress.forall_domain_queries = progress.forall_domain_queries.saturating_add(1);
            }
        }
    }

    fn record_body_query(self, progress: &mut InferenceProgress) {
        match self {
            TelescopeKind::Lambda => {
                progress.lambda_body_queries = progress.lambda_body_queries.saturating_add(1);
            }
            TelescopeKind::Forall => {
                progress.forall_body_queries = progress.forall_body_queries.saturating_add(1);
            }
        }
    }
}

fn telescope_node(
    node: &ExprNode,
    kind: TelescopeKind,
) -> Option<(WireName, BinderStyle, ExprId, ExprId)> {
    match (kind, node) {
        (
            TelescopeKind::Lambda,
            ExprNode::Lambda {
                binder_name,
                binder_type,
                body,
                style,
            },
        )
        | (
            TelescopeKind::Forall,
            ExprNode::Forall {
                binder_name,
                binder_type,
                body,
                style,
            },
        ) => Some((binder_name.clone(), *style, *binder_type, *body)),
        _ => None,
    }
}

fn collect_telescope(
    term: &WireExpr,
    source: ArenaSource,
    root: ExprId,
    kind: TelescopeKind,
    control: &mut Control,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<(Vec<TelescopeBinderSource>, TermReference), LeafHalt> {
    let mut cursor = root;
    let mut binders = Vec::new();
    loop {
        let current =
            term.node(cursor)
                .ok_or(LeafHalt::Fault(InferenceFault::MissingExpression {
                    index: cursor.index(),
                }))?;
        let Some((display_name, style, binder_type, body)) = telescope_node(current, kind) else {
            break;
        };
        control
            .step(cancelled, kind.telescope_phase(), cursor.index())
            .map_err(LeafHalt::stop)?;
        kind.record_binder(&mut control.progress);
        binders.push(TelescopeBinderSource {
            display_name,
            style,
            domain: TermReference {
                source,
                root: binder_type,
            },
        });
        cursor = body;
    }
    if binders.len() > MAX_BVAR_INDEX as usize + 1 {
        return Err(LeafHalt::stop(InferenceStop::Materialization {
            phase: kind.telescope_phase(),
            stop: TermStop::Resource {
                limit: TermLimit::BoundIndex,
                allowed: u64::from(MAX_BVAR_INDEX).saturating_add(1),
                observed: usize_units(binders.len()),
                at: cursor.index(),
                completed_steps: control.progress.steps,
            },
            progress: control.progress,
        }));
    }
    Ok((
        binders,
        TermReference {
            source,
            root: cursor,
        },
    ))
}

/// KR-109: flatten a chain of `let` binders onto the heap.
///
/// Mirrors [`collect_telescope`]; kept separate rather than folded into
/// [`TelescopeKind`] because a let binder carries a third component — the value —
/// that neither a lambda nor a forall binder has, and a shared shape would have
/// to carry a dead field for two of the three kinds.
fn collect_let_telescope(
    term: &WireExpr,
    source: ArenaSource,
    root: ExprId,
    control: &mut Control,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<(Vec<LetBinderSource>, TermReference), LeafHalt> {
    let mut cursor = root;
    let mut binders = Vec::new();
    loop {
        let current =
            term.node(cursor)
                .ok_or(LeafHalt::Fault(InferenceFault::MissingExpression {
                    index: cursor.index(),
                }))?;
        let ExprNode::Let {
            type_, value, body, ..
        } = current
        else {
            break;
        };
        control
            .step(cancelled, InferencePhase::LetTelescope, cursor.index())
            .map_err(LeafHalt::stop)?;
        binders.push(LetBinderSource {
            declared_type: TermReference {
                source,
                root: *type_,
            },
            value: TermReference {
                source,
                root: *value,
            },
        });
        cursor = *body;
    }
    if binders.len() > MAX_BVAR_INDEX as usize + 1 {
        return Err(LeafHalt::stop(InferenceStop::Materialization {
            phase: InferencePhase::LetTelescope,
            stop: TermStop::Resource {
                limit: TermLimit::BoundIndex,
                allowed: u64::from(MAX_BVAR_INDEX).saturating_add(1),
                observed: usize_units(binders.len()),
                at: cursor.index(),
                completed_steps: control.progress.steps,
            },
            progress: control.progress,
        }));
    }
    Ok((
        binders,
        TermReference {
            source,
            root: cursor,
        },
    ))
}

/// KR-110: the constant a `Nat` literal is typed by.
const LITERAL_NAT: &str = "Nat";
/// KR-110: the constant a `String` literal is typed by.
const LITERAL_STRING: &str = "String";

/// KR-110: the type of a literal is a CONSTANT the term does not contain.
///
/// Every other leaf rule copies a type out of an arena it was handed; this one
/// has to build one, because a literal node carries no type subterm. Two things
/// about that are load-bearing.
///
/// The environment is consulted rather than trusted. A literal whose type
/// constant is not declared is a typed [`InferenceRefusal::UnknownConstant`] —
/// not a deferral, because the question is answered rather than open, and not a
/// panic. The universe arity is checked even though it is always zero here: an
/// environment declaring `Nat` with level parameters is malformed input and must
/// refuse rather than silently instantiate nothing.
///
/// The constant's own declared type is deliberately NOT re-checked. KR-105 does
/// not re-check a constant's type either; doing it here would smuggle KR-972's
/// preamble law into this rule.
///
/// `#[inline(never)]`, and the arms above call it rather than inlining their
/// bodies, for the reason `LetState` records: `run` and `dispatch_reference` sit
/// on a 64 KiB budget shared by every rule, and KR-109 overran it by growing one
/// frame with match-arm locals.
#[inline(never)]
fn literal_type(
    constant: &str,
    context: &InferenceContext,
    control: &mut Control,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<Dispatch, LeafHalt> {
    let name = WireName::from_parts(vec![NamePart::Text(constant.to_owned())]);
    control
        .step(cancelled, InferencePhase::LiteralType, 0)
        .map_err(LeafHalt::stop)?;
    let declaration = context.constants().find(&name).ok_or(LeafHalt::Refused(
        InferenceRefusal::UnknownConstant { name: name.clone() },
    ))?;
    let expected = declaration.level_parameters().len();
    if expected != 0 {
        return Err(LeafHalt::Refused(InferenceRefusal::ConstantUniverseArity {
            name,
            expected,
            actual: 0,
        }));
    }
    let mut nodes = Vec::new();
    nodes
        .try_reserve_exact(1)
        .map_err(|_| LeafHalt::Fault(InferenceFault::LiteralTypeAllocation))?;
    nodes.push(ExprNode::Constant {
        name,
        levels: Vec::new(),
    });
    let root =
        ExprId::from_index(0).ok_or(LeafHalt::Fault(InferenceFault::LiteralTypeAllocation))?;
    Ok(Dispatch::Type(WireExpr::from_parts(
        nodes,
        Vec::new(),
        root,
    )))
}

fn dispatch_reference(
    input: &WireExpr,
    generated: &[Arc<WireExpr>],
    reference: TermReference,
    scope: DispatchScope<'_>,
    control: &mut Control,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<Dispatch, LeafHalt> {
    let context = scope.context;
    let scoped_locals = scope.scoped_locals;
    let mode = scope.mode;
    let term = inference_arena(input, generated, reference.source)?;
    control
        .step(
            cancelled,
            InferencePhase::Precondition,
            reference.root.index(),
        )
        .map_err(LeafHalt::stop)?;

    let facts = match inspect_with(term, control.budget.inspection, &mut *cancelled) {
        TermOutcome::Complete(facts) => facts,
        TermOutcome::Inconclusive(stop) => {
            return Err(LeafHalt::stop(InferenceStop::Inspection {
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
            .map_err(LeafHalt::stop)?;
        control.progress.metadata_layers = control.progress.metadata_layers.saturating_add(1);
        root = *expression;
    }

    control
        .step(cancelled, InferencePhase::Dispatch, root.index())
        .map_err(LeafHalt::stop)?;
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
            let local_type = scoped_locals
                .get(name)
                .map(Arc::as_ref)
                .or_else(|| context.local(name).map(LocalDeclaration::type_))
                .ok_or_else(|| {
                    LeafHalt::Refused(InferenceRefusal::UnknownFreeVariable { name: name.clone() })
                })?;
            map_materialization(
                copy_subterm_with(
                    local_type,
                    local_type.root(),
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
                    Err(LeafHalt::stop(InferenceStop::Materialization {
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
                    .map_err(LeafHalt::stop)?;
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
        ExprNode::Lambda { .. } => {
            let (binders, body) = collect_telescope(
                term,
                reference.source,
                root,
                TelescopeKind::Lambda,
                control,
                cancelled,
            )?;
            Ok(Dispatch::Lambda { binders, body })
        }
        ExprNode::Forall { .. } => {
            let (binders, body) = collect_telescope(
                term,
                reference.source,
                root,
                TelescopeKind::Forall,
                control,
                cancelled,
            )?;
            Ok(Dispatch::Forall { binders, body })
        }
        ExprNode::Let { .. } => {
            let (binders, body) =
                collect_let_telescope(term, reference.source, root, control, cancelled)?;
            Ok(Dispatch::Let { binders, body })
        }
        ExprNode::NatLiteral { .. } => literal_type(LITERAL_NAT, context, control, cancelled),
        ExprNode::StringLiteral(_) => literal_type(LITERAL_STRING, context, control, cancelled),
        ExprNode::Projection {
            structure_name,
            index,
            expression,
        } => Ok(Dispatch::Projection {
            state: Box::new(ProjectionState {
                structure_name: structure_name.clone(),
                index: *index,
                scrutinee: TermReference {
                    source: reference.source,
                    root: *expression,
                },
            }),
        }),
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
    generated: Vec<Arc<WireExpr>>,
    scoped_locals: BTreeMap<WireName, Arc<WireExpr>>,
    reserved_names: Option<BTreeSet<WireName>>,
    next_local_identity: u64,
    continuations: Vec<Continuation>,
}

enum TelescopeSchedule {
    Query {
        continuation: Continuation,
        reference: TermReference,
    },
}

fn reserve_free_names_in_term(
    term: &WireExpr,
    names: &mut BTreeSet<WireName>,
    control: &mut Control,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<(), LeafHalt> {
    for (index, node) in term.nodes().iter().enumerate() {
        control
            .step(cancelled, InferencePhase::LocalIdentity, index)
            .map_err(LeafHalt::stop)?;
        let ExprNode::Free { name } = node else {
            continue;
        };
        if names.insert(name.clone()) {
            control.progress.reserved_free_names =
                control.progress.reserved_free_names.saturating_add(1);
        }
    }
    Ok(())
}

impl<'a> InferenceEngine<'a> {
    fn initialize_reserved_names(&mut self) -> Result<(), LeafHalt> {
        if self.reserved_names.is_some() {
            return Ok(());
        }

        let mut names = BTreeSet::new();
        reserve_free_names_in_term(self.input, &mut names, self.control, self.cancelled)?;
        for local in self.context.locals() {
            self.control
                .step(self.cancelled, InferencePhase::LocalIdentity, names.len())
                .map_err(LeafHalt::stop)?;
            if names.insert(local.name().clone()) {
                self.control.progress.reserved_free_names =
                    self.control.progress.reserved_free_names.saturating_add(1);
            }
            reserve_free_names_in_term(local.type_(), &mut names, self.control, self.cancelled)?;
            if let Some(value) = local.value() {
                reserve_free_names_in_term(value, &mut names, self.control, self.cancelled)?;
            }
        }
        for (name, declaration) in self.context.constants().constants() {
            self.control
                .step(self.cancelled, InferencePhase::LocalIdentity, names.len())
                .map_err(LeafHalt::stop)?;
            if names.insert(name.clone()) {
                self.control.progress.reserved_free_names =
                    self.control.progress.reserved_free_names.saturating_add(1);
            }
            reserve_free_names_in_term(
                declaration.type_(),
                &mut names,
                self.control,
                self.cancelled,
            )?;
            if let Some(body) = declaration.body_value() {
                reserve_free_names_in_term(body, &mut names, self.control, self.cancelled)?;
            }
        }
        self.reserved_names = Some(names);
        Ok(())
    }

    fn fresh_local_name(&mut self) -> Result<WireName, LeafHalt> {
        self.initialize_reserved_names()?;
        loop {
            self.control
                .step(
                    self.cancelled,
                    InferencePhase::LocalIdentity,
                    usize::try_from(self.next_local_identity).unwrap_or(usize::MAX),
                )
                .map_err(LeafHalt::stop)?;
            self.control.progress.local_identity_candidates = self
                .control
                .progress
                .local_identity_candidates
                .saturating_add(1);
            let candidate = WireName::from_parts(vec![
                NamePart::Text("_fln_checker_local".to_owned()),
                NamePart::Numeric {
                    value: self.next_local_identity,
                    overflowed: false,
                },
            ]);
            self.next_local_identity = self
                .next_local_identity
                .checked_add(1)
                .ok_or(LeafHalt::Fault(InferenceFault::FreshLocalIdentityExhausted))?;
            let names = self
                .reserved_names
                .as_mut()
                .ok_or(LeafHalt::Fault(InferenceFault::FreshLocalIdentityExhausted))?;
            if names.insert(candidate.clone()) {
                self.control.progress.reserved_free_names =
                    self.control.progress.reserved_free_names.saturating_add(1);
                return Ok(candidate);
            }
        }
    }

    fn store_generated(&mut self, term: Arc<WireExpr>) -> TermReference {
        let generation = self.generated.len();
        let root = term.root();
        self.generated.push(term);
        TermReference {
            source: ArenaSource::Generated(generation),
            root,
        }
    }

    fn materialize_free_reference(&mut self, name: &WireName) -> Result<TermReference, LeafHalt> {
        let term = map_materialization(
            materialize_free(name, self.control.budget.materialization, self.cancelled),
            InferencePhase::LocalIdentity,
            self.control.progress,
        )?;
        Ok(self.store_generated(Arc::new(term)))
    }

    fn materialize_telescope_subterm(
        &mut self,
        reference: TermReference,
        binders: &[TelescopeBinder],
        phase: InferencePhase,
    ) -> Result<WireExpr, LeafHalt> {
        let source = inference_arena(self.input, &self.generated, reference.source)?;
        let mut result = map_materialization(
            copy_compact_subterm_with(
                source,
                reference.root,
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
                return Err(LeafHalt::stop(InferenceStop::Inspection {
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
        if needed > binders.len() {
            return Err(LeafHalt::Fault(InferenceFault::LooseBoundVariables {
                external_bound_span,
            }));
        }

        let first = binders.len() - needed;
        for binder in binders[first..].iter().rev() {
            let replacement =
                inference_arena(self.input, &self.generated, binder.local_reference.source)?;
            let root = result.root();
            result = map_materialization(
                substitute_bound_subterms_with(
                    &result,
                    root,
                    0,
                    replacement,
                    binder.local_reference.root,
                    self.control.budget.materialization,
                    self.cancelled,
                ),
                phase,
                self.control.progress,
            )?;
        }
        Ok(result)
    }

    fn install_telescope_binder(
        &mut self,
        state: &mut TelescopeState,
        domain: Arc<WireExpr>,
        local_name: WireName,
        local_reference: TermReference,
    ) -> Result<(), LeafHalt> {
        let source = state
            .sources
            .get(state.next)
            .ok_or(LeafHalt::Fault(InferenceFault::EmptyWorklist))?;
        // Resolve the materialized domain to its TYPE (via materialize_reference,
        // which already recursively resolves every Free local to its registered
        // type and walks App/Forall/Lambda subterms). Storing the raw Free
        // form made compare_domain compare concrete inferred types against Free
        // locals — the quick def-eq has no rule for that pair, and the
        // Init.Prelude item 15 [HEq] member preamble defers on exactly this
        // comparison. Storing the inferred TYPE gives every consumer of
        // scoped_locals a canonical concrete form.
        let domain_ref = self.store_generated(Arc::clone(&domain));
        let type_ref = self.materialize_reference(domain_ref)?;
        let stored_type = Arc::new(
            inference_arena(self.input, &self.generated, type_ref.source)?.clone(),
        );
        if self
            .scoped_locals
            .insert(local_name.clone(), stored_type)
            .is_some()
        {
            return Err(LeafHalt::Fault(InferenceFault::ScopedLocalCollision {
                name: local_name,
            }));
        }
        state.binders.push(TelescopeBinder {
            display_name: source.display_name.clone(),
            style: source.style,
            local_name,
            local_reference,
            domain,
        });
        state.next = state.next.saturating_add(1);
        Ok(())
    }

    fn schedule_telescope(
        &mut self,
        mut state: Box<TelescopeState>,
    ) -> Result<TelescopeSchedule, LeafHalt> {
        while state.next < state.sources.len() {
            let source = state
                .sources
                .get(state.next)
                .ok_or(LeafHalt::Fault(InferenceFault::EmptyWorklist))?;
            let phase = state.kind.domain_phase();
            self.control
                .step(self.cancelled, phase, source.domain.root.index())
                .map_err(LeafHalt::stop)?;
            let domain = Arc::new(self.materialize_telescope_subterm(
                source.domain,
                &state.binders,
                phase,
            )?);
            let domain_reference = self.store_generated(Arc::clone(&domain));
            let local_name = self.fresh_local_name()?;
            let local_reference = self.materialize_free_reference(&local_name)?;

            if state.kind == TelescopeKind::Forall || self.mode.is_checking() {
                state.kind.record_domain_query(&mut self.control.progress);
                return Ok(TelescopeSchedule::Query {
                    continuation: Continuation::TelescopeDomain {
                        state,
                        domain,
                        local_name,
                        local_reference,
                    },
                    reference: domain_reference,
                });
            }

            self.install_telescope_binder(&mut state, domain, local_name, local_reference)?;
        }

        let phase = state.kind.body_phase();
        self.control
            .step(self.cancelled, phase, state.body.root.index())
            .map_err(LeafHalt::stop)?;
        let body =
            Arc::new(self.materialize_telescope_subterm(state.body, &state.binders, phase)?);
        let reference = self.store_generated(body);
        state.kind.record_body_query(&mut self.control.progress);
        Ok(TelescopeSchedule::Query {
            continuation: Continuation::TelescopeBody { state },
            reference,
        })
    }

    /// KR-109: materialize the let subterm at `reference` under the locals
    /// already installed.
    ///
    /// A let binder's declared type and value are both open in the binders to
    /// their left, exactly as a telescope domain is, so the substitution walk is
    /// the same one — reused rather than re-implemented, since a second copy of
    /// the loose-bvar accounting is a place for the two to disagree.
    fn materialize_let_subterm(
        &mut self,
        reference: TermReference,
        binders: &[LetBinder],
        phase: InferencePhase,
    ) -> Result<WireExpr, LeafHalt> {
        let carriers: Vec<TelescopeBinder> = binders
            .iter()
            .map(|binder| TelescopeBinder {
                display_name: binder.local_name.clone(),
                style: BinderStyle::Default,
                local_name: binder.local_name.clone(),
                local_reference: binder.local_reference,
                domain: Arc::clone(&binder.declared_type),
            })
            .collect();
        self.materialize_telescope_subterm(reference, &carriers, phase)
    }

    /// KR-109: bind the let local to its DECLARED type.
    ///
    /// The local carries the declared type and not the value's inferred type,
    /// because the two are only definitionally equal and KR-102 must read back
    /// the type the term declared.
    fn install_let_binder(&mut self, state: &mut LetState) -> Result<(), LeafHalt> {
        let pending = state
            .pending
            .take()
            .ok_or(LeafHalt::Fault(InferenceFault::EmptyWorklist))?;
        if self
            .scoped_locals
            .insert(
                pending.local_name.clone(),
                Arc::clone(&pending.declared_type),
            )
            .is_some()
        {
            return Err(LeafHalt::Fault(InferenceFault::ScopedLocalCollision {
                name: pending.local_name,
            }));
        }
        state.binders.push(LetBinder {
            local_name: pending.local_name,
            local_reference: pending.local_reference,
            declared_type: pending.declared_type,
            value: pending.value,
        });
        state.next = state.next.saturating_add(1);
        Ok(())
    }

    /// KR-109: schedule the next outstanding query for a let telescope.
    ///
    /// Per binder this is two queries in order — the declared type, then the
    /// value — and after the last binder, the body.
    #[inline(never)]
    fn schedule_let(&mut self, mut state: Box<LetState>) -> Result<TelescopeSchedule, LeafHalt> {
        if state.next < state.sources.len() {
            let source = state
                .sources
                .get(state.next)
                .ok_or(LeafHalt::Fault(InferenceFault::EmptyWorklist))?;
            let declared_reference = source.declared_type;
            let value_reference = source.value;
            self.control
                .step(
                    self.cancelled,
                    InferencePhase::LetDeclaredType,
                    declared_reference.root.index(),
                )
                .map_err(LeafHalt::stop)?;
            let declared_type = Arc::new(self.materialize_let_subterm(
                declared_reference,
                &state.binders,
                InferencePhase::LetDeclaredType,
            )?);
            let value = Arc::new(self.materialize_let_subterm(
                value_reference,
                &state.binders,
                InferencePhase::LetValue,
            )?);
            let query = self.store_generated(Arc::clone(&declared_type));
            let local_name = self.fresh_local_name()?;
            let local_reference = self.materialize_free_reference(&local_name)?;
            if state.pending.is_some() {
                return Err(LeafHalt::Fault(InferenceFault::EmptyWorklist));
            }
            state.pending = Some(LetPending {
                declared_type,
                value,
                local_name,
                local_reference,
            });
            return Ok(TelescopeSchedule::Query {
                continuation: Continuation::LetDeclaredType { state },
                reference: query,
            });
        }

        self.control
            .step(
                self.cancelled,
                InferencePhase::LetBody,
                state.body.root.index(),
            )
            .map_err(LeafHalt::stop)?;
        let body = Arc::new(self.materialize_let_subterm(
            state.body,
            &state.binders,
            InferencePhase::LetBody,
        )?);
        let reference = self.store_generated(body);
        Ok(TelescopeSchedule::Query {
            continuation: Continuation::LetBody { state },
            reference,
        })
    }

    /// KR-109: enter a let telescope.
    ///
    /// `#[inline(never)]` and split out of `run` deliberately. `run` is ONE
    /// frame on a 64 KiB budget shared with every rule, and inlining these arms
    /// grew that frame enough to overflow
    /// `fifty_thousand_binder_forall_telescope_fits_a_64k_stack` — a forall test
    /// this slice does not otherwise touch. Measured at HEAD and after.
    #[inline(never)]
    fn begin_let(
        &mut self,
        binders: Vec<LetBinderSource>,
        body: TermReference,
    ) -> Result<TermReference, LeafHalt> {
        let state = Box::new(LetState {
            sources: binders,
            body,
            binders: Vec::new(),
            next: 0,
            pending: None,
        });
        let TelescopeSchedule::Query {
            continuation,
            reference,
        } = self.schedule_let(state)?;
        self.continuations.push(continuation);
        Ok(reference)
    }

    /// KR-109: the declared type's own type must reduce to a Sort.
    ///
    /// Runs in BOTH modes: the value is substituted into the result, so an
    /// annotation that is not a type would put an ill-typed term into a type
    /// even when only inferring.
    #[inline(never)]
    fn after_let_declared_type(
        &mut self,
        state: Box<LetState>,
        declared_type_type: &WireExpr,
    ) -> Result<TermReference, LeafHalt> {
        self.ensure_sort(
            InferenceSortSite::LetBinder { binder: state.next },
            declared_type_type,
            false,
        )?;
        let pending = state
            .pending
            .as_ref()
            .ok_or(LeafHalt::Fault(InferenceFault::EmptyWorklist))?;
        let query = self.store_generated(Arc::clone(&pending.value));
        self.continuations.push(Continuation::LetValue { state });
        Ok(query)
    }

    /// KR-109: the value's inferred type must be defeq to the declared type;
    /// then the binder is installed and the next query scheduled.
    #[inline(never)]
    fn after_let_value(
        &mut self,
        mut state: Box<LetState>,
        value_type: &WireExpr,
    ) -> Result<TermReference, LeafHalt> {
        let declared = {
            let pending = state
                .pending
                .as_ref()
                .ok_or(LeafHalt::Fault(InferenceFault::EmptyWorklist))?;
            Arc::clone(&pending.declared_type)
        };
        self.compare_let_value(state.next, value_type, &declared)?;
        self.install_let_binder(&mut state)?;
        let TelescopeSchedule::Query {
            continuation,
            reference,
        } = self.schedule_let(state)?;
        self.continuations.push(continuation);
        Ok(reference)
    }

    /// KR-109: the value's inferred type must be definitionally equal to the
    /// declared type. Every outcome stays in its own class.
    #[inline(never)]
    fn compare_let_value(
        &mut self,
        binder: usize,
        actual: &WireExpr,
        declared: &WireExpr,
    ) -> Result<(), LeafHalt> {
        self.control
            .step(self.cancelled, InferencePhase::LetValueComparison, binder)
            .map_err(LeafHalt::stop)?;
        self.control.progress.defeq_queries = self.control.progress.defeq_queries.saturating_add(1);
        match def_eq_with(
            actual,
            declared,
            self.context.reduction(),
            self.control.budget.defeq,
            &mut *self.cancelled,
        ) {
            DefEqOutcome::Equal(_) => Ok(()),
            DefEqOutcome::NotEqual { mismatch, .. } => {
                Err(LeafHalt::Refused(InferenceRefusal::LetValueTypeMismatch {
                    binder,
                    mismatch,
                }))
            }
            DefEqOutcome::Deferred { need, .. } => {
                Err(LeafHalt::Deferred(InferenceDeferred::LetValueConversion {
                    binder,
                    need,
                }))
            }
            DefEqOutcome::Refused { side, refusal, .. } => Err(LeafHalt::Refused(
                InferenceRefusal::LetValueConversionRefusal {
                    binder,
                    side,
                    refusal,
                },
            )),
            DefEqOutcome::Inconclusive(stop) => Err(LeafHalt::stop(InferenceStop::LetValueDefEq {
                binder,
                stop: Box::new(stop),
                progress: self.control.progress,
            })),
            DefEqOutcome::InternalFault(fault) => {
                Err(LeafHalt::Fault(InferenceFault::LetValueDefEq {
                    binder,
                    fault,
                }))
            }
        }
    }

    /// KR-109: complete the let by ZETA-SUBSTITUTING each bound value into the
    /// body's inferred type, innermost binder first.
    ///
    /// This is the whole difference between KR-109 and KR-107: a lambda
    /// ABSTRACTS its binder into a Pi, while a let is transparent to typing, so
    /// the value flows into the type and the internal local must not survive.
    #[inline(never)]
    fn complete_let(&mut self, state: LetState, body_type: WireExpr) -> Result<WireExpr, LeafHalt> {
        let mut result = self.cheap_beta_reduce(body_type)?;
        for binder in state.binders.iter().rev() {
            self.control
                .step(self.cancelled, InferencePhase::LetZeta, state.binders.len())
                .map_err(LeafHalt::stop)?;
            result = map_materialization(
                substitute_free_with(
                    &result,
                    &binder.local_name,
                    &binder.value,
                    self.control.budget.materialization,
                    &mut *self.cancelled,
                ),
                InferencePhase::LetZeta,
                self.control.progress,
            )?;
        }
        self.remove_let_locals(&state.binders)?;
        Ok(result)
    }

    /// KR-112: reduce the scrutinee's inferred type so the structure is visible.
    #[inline(never)]
    fn projection_whnf(&mut self, type_: &WireExpr) -> Result<WireExpr, LeafHalt> {
        self.control
            .step(self.cancelled, InferencePhase::ProjectionWhnf, 0)
            .map_err(LeafHalt::stop)?;
        self.control.progress.whnf_queries = self.control.progress.whnf_queries.saturating_add(1);
        match whnf_with(
            type_,
            self.context.reduction(),
            self.control.budget.whnf,
            &mut *self.cancelled,
        ) {
            WhnfOutcome::Complete(result) => Ok(result.term),
            WhnfOutcome::Refused(refusal) => {
                Err(LeafHalt::Refused(InferenceRefusal::ReductionRefusal {
                    argument: 0,
                    refusal,
                }))
            }
            WhnfOutcome::Inconclusive(stop) => Err(LeafHalt::stop(InferenceStop::Whnf {
                argument: 0,
                stop: Box::new(stop),
                progress: self.control.progress,
            })),
            WhnfOutcome::InternalFault(fault) => {
                Err(LeafHalt::Fault(InferenceFault::Whnf { argument: 0, fault }))
            }
        }
    }

    /// KR-112: the field type of a projection.
    ///
    /// The structure metadata is CALLER-SUPPLIED through the reduction context's
    /// projection rules -- not derived from the environment and not validated by
    /// it -- so every field of a rule is untrusted input here, and each way it can
    /// be wrong gets its own typed outcome rather than a shared generic rejection.
    ///
    /// Reduce the scrutinee's type to an application of the named structure; take
    /// the rule's constructor and parameter count; instantiate the constructor's
    /// telescope with the structure's own arguments for the parameters, then with
    /// a projection of the SAME scrutinee for each earlier field, because a later
    /// field's type may mention an earlier one. The requested field's domain is
    /// the answer.
    ///
    /// The rule's constructor must be declared with `ConstantKind::Constructor`.
    ///
    /// **KR-112 originally disclosed this as unenforceable, and that disclosure was
    /// FALSE.** `ConstantDeclaration::kind` exists (`environment.rs:161`) and always
    /// did; the search that "established" its absence was `pub fn kind`, which
    /// cannot match a `pub const fn`. A scan that could not find the thing was read
    /// as proof the thing was missing, and the wrong conclusion travelled into a
    /// code comment, a bead, a coverage row and a routed message. The check is
    /// implemented below rather than merely un-disclosed: the honest repair for an
    /// excuse that was never true is the work it excused.
    #[inline(never)]
    fn complete_projection(
        &mut self,
        state: ProjectionState,
        scrutinee_type: &WireExpr,
    ) -> Result<WireExpr, LeafHalt> {
        let reduced = self.projection_whnf(scrutinee_type)?;

        let mut cursor = reduced.root();
        let mut arguments: Vec<ExprId> = Vec::new();
        while let Some(ExprNode::Apply { function, argument }) = reduced.node(cursor) {
            arguments.push(*argument);
            cursor = *function;
        }
        arguments.reverse();
        let levels: Vec<LevelId> = match reduced.node(cursor) {
            Some(ExprNode::Constant { name, levels }) if *name == state.structure_name => {
                levels.clone()
            }
            _ => {
                return Err(LeafHalt::Refused(
                    InferenceRefusal::ProjectionStructureMismatch {
                        expected: state.structure_name,
                    },
                ));
            }
        };

        let rule = self
            .context
            .reduction()
            .projection_rules()
            .iter()
            .find(|candidate| *candidate.structure_name() == state.structure_name)
            .ok_or(LeafHalt::Refused(InferenceRefusal::ProjectionRuleMissing {
                structure: state.structure_name.clone(),
            }))?;
        let parameters = rule.parameter_count();
        let constructor_name = rule.constructor_name().clone();
        if parameters > arguments.len() {
            return Err(LeafHalt::Refused(
                InferenceRefusal::ProjectionArityExceeded {
                    structure: state.structure_name,
                    needed: parameters,
                    available: arguments.len(),
                },
            ));
        }

        let declaration =
            self.context
                .constants()
                .find(&constructor_name)
                .ok_or(LeafHalt::Refused(InferenceRefusal::UnknownConstant {
                    name: constructor_name.clone(),
                }))?;
        // KR-112: the projection rule is CALLER-SUPPLIED, so a rule naming a
        // constant that is not a constructor is untrusted input rather than an
        // internal inconsistency. Refuse it in its own right.
        if declaration.kind() != ConstantKind::Constructor {
            return Err(LeafHalt::Refused(
                InferenceRefusal::ProjectionConstructorKind {
                    constructor: constructor_name,
                },
            ));
        }
        if declaration.level_parameters().len() != levels.len() {
            return Err(LeafHalt::Refused(InferenceRefusal::ConstantUniverseArity {
                name: constructor_name,
                expected: declaration.level_parameters().len(),
                actual: levels.len(),
            }));
        }
        let constructor_type = match instantiate_term_parameters_from_level_roots_with(
            declaration.type_(),
            declaration.level_parameters(),
            reduced.levels(),
            &levels,
            self.control.budget.materialization,
            self.cancelled,
        ) {
            InstantiationOutcome::Complete(type_) => type_,
            InstantiationOutcome::Refused(refusal) => {
                return Err(LeafHalt::Fault(
                    InferenceFault::ConstantInstantiationRefusal {
                        name: constructor_name,
                        refusal,
                    },
                ));
            }
            InstantiationOutcome::Inconclusive(stop) => {
                return Err(LeafHalt::stop(InferenceStop::Materialization {
                    phase: InferencePhase::ProjectionField,
                    stop,
                    progress: self.control.progress,
                }));
            }
            InstantiationOutcome::InternalFault(fault) => {
                return Err(LeafHalt::Fault(InferenceFault::ConstantInstantiation {
                    name: constructor_name,
                    fault,
                }));
            }
        };

        let reduced_reference = self.store_generated(Arc::new(reduced));
        let mut function = FunctionState::new(constructor_type);
        let requested = usize::try_from(state.index)
            .map_err(|_| LeafHalt::Fault(InferenceFault::EmptyWorklist))?;
        let total = parameters
            .checked_add(requested)
            .ok_or(LeafHalt::Fault(InferenceFault::EmptyWorklist))?;
        for step in 0..total {
            self.control
                .step(self.cancelled, InferencePhase::ProjectionField, step)
                .map_err(LeafHalt::stop)?;
            let rest = match Self::pi_parts(&function) {
                Ok((_, rest)) => rest,
                Err(_) => {
                    return Err(LeafHalt::Refused(
                        InferenceRefusal::ProjectionArityExceeded {
                            structure: state.structure_name,
                            needed: total.saturating_add(1),
                            available: step,
                        },
                    ));
                }
            };
            let instantiation = if step < parameters {
                // `.get` rather than `[step]`: the index is derived from a
                // CALLER-SUPPLIED parameter_count, so a direct index would be a
                // panic path on untrusted input even though the bound was checked
                // above. Clippy's needless_range_loop pointed here; the honest
                // repair removes the panic, not just the lint.
                let argument = *arguments.get(step).ok_or(LeafHalt::Refused(
                    InferenceRefusal::ProjectionArityExceeded {
                        structure: state.structure_name.clone(),
                        needed: parameters,
                        available: arguments.len(),
                    },
                ))?;
                TermReference {
                    source: reduced_reference.source,
                    root: argument,
                }
            } else {
                let earlier = u64::try_from(step - parameters)
                    .map_err(|_| LeafHalt::Fault(InferenceFault::EmptyWorklist))?;
                self.projection_of(&state.structure_name, earlier, state.scrutinee)?
            };
            function.root = rest;
            function.instantiations.push(instantiation);
        }

        let domain = match Self::pi_parts(&function) {
            Ok((domain, _)) => domain,
            Err(_) => {
                return Err(LeafHalt::Refused(
                    InferenceRefusal::ProjectionArityExceeded {
                        structure: state.structure_name,
                        needed: total.saturating_add(1),
                        available: total,
                    },
                ));
            }
        };
        self.materialize_function_subterm(&function, domain, InferencePhase::ProjectionField)
    }

    /// KR-112: build `<scrutinee>.<field>`, the term substituted for an earlier
    /// field when a later field's type mentions it.
    #[inline(never)]
    fn projection_of(
        &mut self,
        structure_name: &WireName,
        index: u64,
        scrutinee: TermReference,
    ) -> Result<TermReference, LeafHalt> {
        let source = inference_arena(self.input, &self.generated, scrutinee.source)?;
        let inner = map_materialization(
            copy_compact_subterm_with(
                source,
                scrutinee.root,
                self.control.budget.materialization,
                self.cancelled,
            ),
            InferencePhase::ProjectionField,
            self.control.progress,
        )?;
        let progress = self.control.progress;
        let mut assembler =
            ArenaAssembler::new(self.control.budget.materialization, &mut *self.cancelled);
        let inner_root = map_assembly(
            assembler.append(&inner),
            InferencePhase::ProjectionField,
            progress,
        )?;
        let root = map_assembly(
            assembler.push_projection(structure_name, index, inner_root),
            InferencePhase::ProjectionField,
            progress,
        )?;
        let term = assembler.finish(root);
        Ok(self.store_generated(Arc::new(term)))
    }

    /// KR-109: drop the query-local let bindings.
    ///
    /// Separate from [`Self::remove_telescope_locals`] only because the binder
    /// shapes differ; the law it enforces is the same one — a local that was
    /// never installed, or was removed twice, is an internal fault rather than a
    /// silently tolerated state.
    fn remove_let_locals(&mut self, binders: &[LetBinder]) -> Result<(), LeafHalt> {
        for binder in binders.iter().rev() {
            if self.scoped_locals.remove(&binder.local_name).is_none() {
                return Err(LeafHalt::Fault(InferenceFault::MissingScopedLocal {
                    name: binder.local_name.clone(),
                }));
            }
        }
        Ok(())
    }

    fn ensure_sort(
        &mut self,
        site: InferenceSortSite,
        inferred_type: &WireExpr,
        retain_sort: bool,
    ) -> Result<Option<WireExpr>, LeafHalt> {
        let phase = site.phase();
        self.control
            .step(self.cancelled, phase, site.at())
            .map_err(LeafHalt::stop)?;
        if site.is_forall() {
            self.control.progress.forall_sort_checks =
                self.control.progress.forall_sort_checks.saturating_add(1);
        } else if site.is_let() {
        } else {
            self.control.progress.binder_sort_checks =
                self.control.progress.binder_sort_checks.saturating_add(1);
        }
        self.control.progress.whnf_queries = self.control.progress.whnf_queries.saturating_add(1);
        let reduced = match whnf_with(
            inferred_type,
            self.context.reduction(),
            self.control.budget.whnf,
            &mut *self.cancelled,
        ) {
            WhnfOutcome::Complete(result) => result.term,
            WhnfOutcome::Refused(refusal) => {
                return Err(LeafHalt::Refused(InferenceRefusal::SortReductionRefusal {
                    site,
                    refusal,
                }));
            }
            WhnfOutcome::Inconclusive(stop) => {
                return Err(LeafHalt::stop(InferenceStop::SortWhnf {
                    site,
                    stop: Box::new(stop),
                    progress: self.control.progress,
                }));
            }
            WhnfOutcome::InternalFault(fault) => {
                return Err(LeafHalt::Fault(InferenceFault::SortWhnf { site, fault }));
            }
        };
        match reduced.node(reduced.root()) {
            Some(ExprNode::Sort { .. }) => {}
            Some(_) => return Err(LeafHalt::Refused(InferenceRefusal::SortExpected { site })),
            None => {
                return Err(LeafHalt::Fault(InferenceFault::MissingExpression {
                    index: reduced.root().index(),
                }));
            }
        }
        if !retain_sort {
            return Ok(None);
        }
        map_materialization(
            copy_compact_subterm_with(
                &reduced,
                reduced.root(),
                self.control.budget.materialization,
                self.cancelled,
            ),
            phase,
            self.control.progress,
        )
        .map(Some)
    }

    fn copy_cheap_beta_subterm(
        &mut self,
        term: &WireExpr,
        root: ExprId,
    ) -> Result<WireExpr, LeafHalt> {
        map_materialization(
            copy_compact_subterm_with(
                term,
                root,
                self.control.budget.materialization,
                self.cancelled,
            ),
            InferencePhase::CheapBeta,
            self.control.progress,
        )
    }

    fn cheap_beta_reduce(&mut self, term: WireExpr) -> Result<WireExpr, LeafHalt> {
        if !matches!(term.node(term.root()), Some(ExprNode::Apply { .. })) {
            return Ok(term);
        }

        let mut head = term.root();
        let mut arguments = Vec::new();
        loop {
            let node =
                term.node(head)
                    .ok_or(LeafHalt::Fault(InferenceFault::MissingExpression {
                        index: head.index(),
                    }))?;
            let ExprNode::Apply { function, argument } = node else {
                break;
            };
            self.control
                .step(self.cancelled, InferencePhase::CheapBeta, head.index())
                .map_err(LeafHalt::stop)?;
            self.control.progress.cheap_beta_steps =
                self.control.progress.cheap_beta_steps.saturating_add(1);
            arguments.push(*argument);
            head = *function;
        }
        arguments.reverse();

        let mut consumed = 0usize;
        while consumed < arguments.len() {
            let node =
                term.node(head)
                    .ok_or(LeafHalt::Fault(InferenceFault::MissingExpression {
                        index: head.index(),
                    }))?;
            let ExprNode::Lambda { body, .. } = node else {
                break;
            };
            self.control
                .step(self.cancelled, InferencePhase::CheapBeta, head.index())
                .map_err(LeafHalt::stop)?;
            self.control.progress.cheap_beta_steps =
                self.control.progress.cheap_beta_steps.saturating_add(1);
            head = *body;
            consumed = consumed.saturating_add(1);
        }
        if consumed == 0 {
            return Ok(term);
        }

        let selected = match term.node(head) {
            Some(ExprNode::Bound { index })
                if usize::try_from(*index)
                    .ok()
                    .is_some_and(|index| index < consumed) =>
            {
                let index = usize::try_from(*index).map_err(|_| {
                    LeafHalt::Fault(InferenceFault::LooseBoundVariables {
                        external_bound_span: index.saturating_add(1),
                    })
                })?;
                let argument = consumed - 1 - index;
                self.copy_cheap_beta_subterm(
                    &term,
                    *arguments
                        .get(argument)
                        .ok_or(LeafHalt::Fault(InferenceFault::EmptyWorklist))?,
                )?
            }
            Some(ExprNode::Bound { .. }) => return Ok(term),
            Some(_) => {
                let candidate = self.copy_cheap_beta_subterm(&term, head)?;
                let facts = match inspect_with(
                    &candidate,
                    self.control.budget.inspection,
                    &mut *self.cancelled,
                ) {
                    TermOutcome::Complete(facts) => facts,
                    TermOutcome::Inconclusive(stop) => {
                        return Err(LeafHalt::stop(InferenceStop::Inspection {
                            stop,
                            progress: self.control.progress,
                        }));
                    }
                    TermOutcome::InternalFault(fault) => {
                        return Err(LeafHalt::Fault(InferenceFault::Inspection(fault)));
                    }
                };
                if facts.external_bound_span != 0 {
                    return Ok(term);
                }
                candidate
            }
            None => {
                return Err(LeafHalt::Fault(InferenceFault::MissingExpression {
                    index: head.index(),
                }));
            }
        };

        if consumed == arguments.len() {
            return Ok(selected);
        }
        let mut residual_arguments = Vec::with_capacity(arguments.len() - consumed);
        for argument in &arguments[consumed..] {
            residual_arguments.push(self.copy_cheap_beta_subterm(&term, *argument)?);
        }
        let progress = self.control.progress;
        let mut assembler =
            ArenaAssembler::new(self.control.budget.materialization, &mut *self.cancelled);
        let mut root = map_assembly(
            assembler.append(&selected),
            InferencePhase::CheapBeta,
            progress,
        )?;
        for compact in &residual_arguments {
            let argument_root = map_assembly(
                assembler.append(compact),
                InferencePhase::CheapBeta,
                progress,
            )?;
            root = map_assembly(
                assembler.push_apply(root, argument_root),
                InferencePhase::CheapBeta,
                progress,
            )?;
        }
        Ok(assembler.finish(root))
    }

    fn remove_telescope_locals(&mut self, binders: &[TelescopeBinder]) -> Result<(), LeafHalt> {
        for binder in binders.iter().rev() {
            if self.scoped_locals.remove(&binder.local_name).is_none() {
                return Err(LeafHalt::Fault(InferenceFault::MissingScopedLocal {
                    name: binder.local_name.clone(),
                }));
            }
        }
        Ok(())
    }

    fn complete_lambda(
        &mut self,
        state: TelescopeState,
        body_type: WireExpr,
    ) -> Result<WireExpr, LeafHalt> {
        let body_type = self.cheap_beta_reduce(body_type)?;
        self.remove_telescope_locals(&state.binders)?;

        let binder_count = u32::try_from(state.binders.len()).map_err(|_| {
            LeafHalt::stop(InferenceStop::Materialization {
                phase: InferencePhase::PiAbstraction,
                stop: TermStop::Resource {
                    limit: TermLimit::BoundIndex,
                    allowed: u64::from(MAX_BVAR_INDEX).saturating_add(1),
                    observed: usize_units(state.binders.len()),
                    at: state.binders.len(),
                    completed_steps: self.control.progress.steps,
                },
                progress: self.control.progress,
            })
        })?;
        let mut ordinals = BTreeMap::new();
        for (index, binder) in state.binders.iter().enumerate() {
            let ordinal = u32::try_from(index)
                .map_err(|_| LeafHalt::Fault(InferenceFault::FreshLocalIdentityExhausted))?;
            if ordinals
                .insert(binder.local_name.clone(), ordinal)
                .is_some()
            {
                return Err(LeafHalt::Fault(InferenceFault::ScopedLocalCollision {
                    name: binder.local_name.clone(),
                }));
            }
        }

        let body = map_materialization(
            abstract_free_telescope_with(
                &body_type,
                &ordinals,
                binder_count,
                self.control.budget.materialization,
                self.cancelled,
            ),
            InferencePhase::PiAbstraction,
            self.control.progress,
        )?;
        let mut domains = Vec::with_capacity(state.binders.len());
        for (index, binder) in state.binders.iter().enumerate() {
            let active = u32::try_from(index)
                .map_err(|_| LeafHalt::Fault(InferenceFault::FreshLocalIdentityExhausted))?;
            domains.push(map_materialization(
                abstract_free_telescope_with(
                    &binder.domain,
                    &ordinals,
                    active,
                    self.control.budget.materialization,
                    self.cancelled,
                ),
                InferencePhase::PiAbstraction,
                self.control.progress,
            )?);
        }

        let progress = self.control.progress;
        let mut assembler =
            ArenaAssembler::new(self.control.budget.materialization, &mut *self.cancelled);
        let mut domain_roots = Vec::with_capacity(domains.len());
        for domain in &domains {
            domain_roots.push(map_assembly(
                assembler.append(domain),
                InferencePhase::PiAbstraction,
                progress,
            )?);
        }
        let mut root = map_assembly(
            assembler.append(&body),
            InferencePhase::PiAbstraction,
            progress,
        )?;
        for (binder, domain_root) in state.binders.iter().zip(domain_roots).rev() {
            root = map_assembly(
                assembler.push_forall(&binder.display_name, binder.style, domain_root, root),
                InferencePhase::PiAbstraction,
                progress,
            )?;
        }
        Ok(assembler.finish(root))
    }

    fn complete_forall(
        &mut self,
        mut state: TelescopeState,
        body_type: &WireExpr,
    ) -> Result<WireExpr, LeafHalt> {
        let codomain = self
            .ensure_sort(
                InferenceSortSite::ForallCodomain {
                    binders: state.binders.len(),
                },
                body_type,
                true,
            )?
            .ok_or(LeafHalt::Fault(InferenceFault::EmptyWorklist))?;
        state.domain_sorts.push(codomain);
        let expected = state.binders.len().saturating_add(1);
        if state.domain_sorts.len() != expected {
            return Err(LeafHalt::Fault(InferenceFault::EmptyWorklist));
        }
        self.remove_telescope_locals(&state.binders)?;

        for index in 0..state.binders.len() {
            self.control
                .step(self.cancelled, InferencePhase::ForallUniverse, index)
                .map_err(LeafHalt::stop)?;
            self.control.progress.forall_imax_nodes =
                self.control.progress.forall_imax_nodes.saturating_add(1);
        }

        let progress = self.control.progress;
        let mut assembler =
            ArenaAssembler::new(self.control.budget.materialization, &mut *self.cancelled);
        let mut levels = Vec::with_capacity(state.domain_sorts.len());
        for (position, sort) in state.domain_sorts.iter().enumerate() {
            let level = match sort.node(sort.root()) {
                Some(ExprNode::Sort { level }) => *level,
                Some(_) => {
                    return Err(LeafHalt::Fault(InferenceFault::RetainedSortExpected {
                        position,
                    }));
                }
                None => {
                    return Err(LeafHalt::Fault(InferenceFault::MissingExpression {
                        index: sort.root().index(),
                    }));
                }
            };
            levels.push(map_assembly(
                assembler.append_level_root(sort, level),
                InferencePhase::ForallUniverse,
                progress,
            )?);
        }
        let mut level = levels
            .pop()
            .ok_or(LeafHalt::Fault(InferenceFault::EmptyWorklist))?;
        for domain in levels.into_iter().rev() {
            level = map_assembly(
                assembler.push_level(LevelNode::IMax(domain, level)),
                InferencePhase::ForallUniverse,
                progress,
            )?;
        }
        let root = map_assembly(
            assembler.push_sort(level),
            InferencePhase::ForallUniverse,
            progress,
        )?;
        Ok(assembler.finish(root))
    }

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
            .map_err(LeafHalt::stop)?;
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
        self.generated.push(Arc::new(term));
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
                return Err(LeafHalt::stop(InferenceStop::Inspection {
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
            .map_err(LeafHalt::stop)?;
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
                    return Err(LeafHalt::stop(InferenceStop::Whnf {
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
                .map_err(LeafHalt::stop)?;
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
                .map_err(LeafHalt::stop)?;
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
            .map_err(LeafHalt::stop)?;
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
            .map_err(LeafHalt::stop)?;
        self.control.progress.defeq_queries = self.control.progress.defeq_queries.saturating_add(1);
        let outcome = match conversion {
            ConversionMode::Ordinary => def_eq_with(
                actual,
                expected,
                self.context.reduction(),
                self.control.budget.defeq,
                &mut *self.cancelled,
            ),
            ConversionMode::EagerReduce => def_eq_eager_with(
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
            DefEqOutcome::Deferred { need, .. } => {
                if std::env::var_os("FLN_CHECKER_TRACE").is_some() {
                    eprintln!(
                        "INFER_DOMAIN_DEFER arg={argument} actual={:?} expected={:?}",
                        actual.nodes(),
                        expected.nodes()
                    );
                }
                Err(LeafHalt::Deferred(
                    InferenceDeferred::ApplicationConversion { argument, need },
                ))
            }
            DefEqOutcome::Refused { side, refusal, .. } => {
                Err(LeafHalt::Refused(InferenceRefusal::ConversionRefusal {
                    argument,
                    side,
                    refusal,
                }))
            }
            DefEqOutcome::Inconclusive(stop) => Err(LeafHalt::stop(InferenceStop::DefEq {
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
                    DispatchScope {
                        context: self.context,
                        scoped_locals: &self.scoped_locals,
                        mode: self.mode,
                    },
                    self.control,
                    self.cancelled,
                )? {
                    Dispatch::Type(type_) => inferred = Some(type_),
                    Dispatch::Application { head, arguments } => {
                        self.continuations
                            .push(Continuation::ApplicationHead { arguments });
                        current = Some(head);
                    }
                    Dispatch::Lambda { binders, body } => {
                        let state = Box::new(TelescopeState {
                            kind: TelescopeKind::Lambda,
                            sources: binders,
                            body,
                            binders: Vec::new(),
                            domain_sorts: Vec::new(),
                            next: 0,
                        });
                        let TelescopeSchedule::Query {
                            continuation,
                            reference,
                        } = self.schedule_telescope(state)?;
                        self.continuations.push(continuation);
                        current = Some(reference);
                    }
                    Dispatch::Forall { binders, body } => {
                        let state = Box::new(TelescopeState {
                            kind: TelescopeKind::Forall,
                            sources: binders,
                            body,
                            binders: Vec::new(),
                            domain_sorts: Vec::new(),
                            next: 0,
                        });
                        let TelescopeSchedule::Query {
                            continuation,
                            reference,
                        } = self.schedule_telescope(state)?;
                        self.continuations.push(continuation);
                        current = Some(reference);
                    }
                    Dispatch::Let { binders, body } => {
                        current = Some(self.begin_let(binders, body)?);
                    }
                    Dispatch::Projection { state } => {
                        let scrutinee = state.scrutinee;
                        self.continuations
                            .push(Continuation::ProjectionScrutinee { state });
                        current = Some(scrutinee);
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
                Continuation::TelescopeDomain {
                    mut state,
                    domain,
                    local_name,
                    local_reference,
                } => {
                    match state.kind {
                        TelescopeKind::Lambda => {
                            self.ensure_sort(
                                InferenceSortSite::LambdaBinder { binder: state.next },
                                &value,
                                false,
                            )?;
                        }
                        TelescopeKind::Forall => {
                            let sort = self
                                .ensure_sort(
                                    InferenceSortSite::ForallBinder { binder: state.next },
                                    &value,
                                    true,
                                )?
                                .ok_or(LeafHalt::Fault(InferenceFault::EmptyWorklist))?;
                            state.domain_sorts.push(sort);
                        }
                    }
                    self.install_telescope_binder(&mut state, domain, local_name, local_reference)?;
                    let TelescopeSchedule::Query {
                        continuation,
                        reference,
                    } = self.schedule_telescope(state)?;
                    self.continuations.push(continuation);
                    current = Some(reference);
                }
                Continuation::TelescopeBody { state } => {
                    inferred = Some(match state.kind {
                        TelescopeKind::Lambda => self.complete_lambda(*state, value)?,
                        TelescopeKind::Forall => self.complete_forall(*state, &value)?,
                    });
                }
                Continuation::LetDeclaredType { state } => {
                    current = Some(self.after_let_declared_type(state, &value)?);
                }
                Continuation::LetValue { state } => {
                    current = Some(self.after_let_value(state, &value)?);
                }
                Continuation::LetBody { state } => {
                    inferred = Some(self.complete_let(*state, value)?);
                }
                Continuation::ProjectionScrutinee { state } => {
                    inferred = Some(self.complete_projection(*state, &value)?);
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
        scoped_locals: BTreeMap::new(),
        reserved_names: None,
        next_local_identity: 0,
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

    #[test]
    fn private_malformed_lambda_child_is_an_internal_fault_and_recovery_is_clean() {
        let domain = ExprId::from_index(0).expect("zero expression index exists");
        let body = ExprId::from_index(7).expect("small expression index exists");
        let root = ExprId::from_index(1).expect("one expression index exists");
        let broken = WireExpr::from_parts(
            vec![
                ExprNode::NatLiteral {
                    limbs_le: Vec::new(),
                },
                ExprNode::Lambda {
                    binder_name: WireName::default(),
                    binder_type: domain,
                    body,
                    style: BinderStyle::Default,
                },
            ],
            Vec::new(),
            root,
        );
        let context = InferenceContext::empty(ConstantEnvironment::empty());
        assert!(matches!(
            infer(
                &broken,
                &context,
                InferenceMode::InferOnly,
                InferenceBudget::unlimited(),
            ),
            InferenceOutcome::InternalFault {
                fault: InferenceFault::Inspection(TermFault::NonBackwardExpressionReference {
                    input: TermInput::Subject,
                    parent: 1,
                    child: 7,
                }),
                ..
            }
        ));

        let zero = LevelId::from_index(0).expect("zero level index exists");
        let healthy_root = ExprId::from_index(0).expect("zero expression index exists");
        let healthy = WireExpr::from_parts(
            vec![ExprNode::Sort { level: zero }],
            vec![LevelNode::Zero],
            healthy_root,
        );
        assert!(matches!(
            infer(
                &healthy,
                &context,
                InferenceMode::InferOnly,
                InferenceBudget::unlimited(),
            ),
            InferenceOutcome::Complete(_)
        ));
    }

    #[test]
    fn private_malformed_forall_child_is_an_internal_fault_and_recovery_is_clean() {
        let zero = LevelId::from_index(0).expect("zero level index exists");
        let domain = ExprId::from_index(0).expect("zero expression index exists");
        let body = ExprId::from_index(7).expect("small expression index exists");
        let root = ExprId::from_index(1).expect("one expression index exists");
        let broken = WireExpr::from_parts(
            vec![
                ExprNode::Sort { level: zero },
                ExprNode::Forall {
                    binder_name: WireName::default(),
                    binder_type: domain,
                    body,
                    style: BinderStyle::Default,
                },
            ],
            vec![LevelNode::Zero],
            root,
        );
        let context = InferenceContext::empty(ConstantEnvironment::empty());
        assert!(matches!(
            infer(
                &broken,
                &context,
                InferenceMode::InferOnly,
                InferenceBudget::unlimited(),
            ),
            InferenceOutcome::InternalFault {
                fault: InferenceFault::Inspection(TermFault::NonBackwardExpressionReference {
                    input: TermInput::Subject,
                    parent: 1,
                    child: 7,
                }),
                ..
            }
        ));

        let healthy_root = ExprId::from_index(0).expect("zero expression index exists");
        let healthy = WireExpr::from_parts(
            vec![ExprNode::Sort { level: zero }],
            vec![LevelNode::Zero],
            healthy_root,
        );
        assert!(matches!(
            infer(
                &healthy,
                &context,
                InferenceMode::InferOnly,
                InferenceBudget::unlimited(),
            ),
            InferenceOutcome::Complete(_)
        ));
    }

    #[test]
    fn private_lambda_compacts_shared_level_dependencies_in_dependency_order() {
        let zero = LevelId::from_index(0).expect("zero level index exists");
        let one = LevelId::from_index(1).expect("one level index exists");
        let two = LevelId::from_index(2).expect("two level index exists");
        let maximum = LevelId::from_index(3).expect("three level index exists");
        let domain = ExprId::from_index(0).expect("zero expression index exists");
        let body = ExprId::from_index(1).expect("one expression index exists");
        let root = ExprId::from_index(2).expect("two expression index exists");
        let lambda = WireExpr::from_parts(
            vec![
                ExprNode::Sort { level: maximum },
                ExprNode::Bound { index: 0 },
                ExprNode::Lambda {
                    binder_name: WireName::default(),
                    binder_type: domain,
                    body,
                    style: BinderStyle::Default,
                },
            ],
            vec![
                LevelNode::Zero,
                LevelNode::Succ(zero),
                LevelNode::Succ(one),
                LevelNode::Max(two, one),
            ],
            root,
        );
        assert!(matches!(
            infer(
                &lambda,
                &InferenceContext::empty(ConstantEnvironment::empty()),
                InferenceMode::InferOnly,
                InferenceBudget::unlimited(),
            ),
            InferenceOutcome::Complete(InferenceResult {
                progress: InferenceProgress {
                    lambda_binders: 1,
                    ..
                },
                ..
            })
        ));
    }
}
