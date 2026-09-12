//! Eager weak-head reduction over checker-owned flat arenas.
//!
//! This module deliberately does not share the primary kernel normalizer. It
//! implements the eager checker portion of KR-200 through KR-204 with flat arena
//! cursors and explicit heap frames: safe-definition delta, metadata stripping,
//! beta, let-zeta, supplied let-bound free unfolding, and explicit-constructor
//! projection — plus recursor reduction: iota (KR-316) with the K-flagged
//! corner (KR-317, `to_cnstr_when_K`). Unsafe and partial definitions stay
//! stuck. Nat literal majors are exposed one constructor layer at a time;
//! string literal majors and native extensions remain outside this layer.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::Arc;

use crate::environment::{ConstantEnvironment, RecursorDeclaration};
use crate::instantiate::{
    InstantiationFault, InstantiationOutcome, InstantiationRefusal,
    instantiate_term_parameters_from_level_roots_with,
};
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

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct WhnfContext {
    free_bindings: Vec<FreeBinding>,
    projection_rules: Vec<ProjectionRule>,
    constants: ConstantEnvironment,
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
        }
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WhnfFault {
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

#[derive(Clone)]
struct Cursor {
    arena: Arc<WireExpr>,
    root: ExprId,
}

struct ProjectionFrame {
    projection: Cursor,
    outer_arguments: VecDeque<Cursor>,
}

#[derive(Clone, Copy)]
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
    delta_reductions: u64,
    has_auxiliary_work: bool,
    string_progress: StringExpansionProgress,
    force_string_delta: bool,
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

    fn expand_string(&mut self, value: &str, at: usize) -> Result<Cursor, Halt> {
        let budget = self.remaining_string_budget();
        match expand_string_literal_with(value, budget, &mut self.cancelled) {
            StringExpansionOutcome::Expanded(result) => {
                self.absorb_string(result.progress);
                let root = result.term.root();
                Ok(Cursor {
                    arena: Arc::new(result.term),
                    root,
                })
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
        Ok(Cursor {
            arena: Arc::new(term),
            root,
        })
    }

    fn substitute(
        &mut self,
        subject: &Cursor,
        body: ExprId,
        replacement: &Cursor,
        phase: WhnfPhase,
    ) -> Result<Cursor, Halt> {
        self.control.step(body.index(), self.cancelled)?;
        let result = substitute_bound_subterms_with(
            &subject.arena,
            body,
            0,
            &replacement.arena,
            replacement.root,
            self.control.budget.materialization,
            self.cancelled,
        );
        let term = self.control.term_halt(phase, result)?;
        let root = term.root();
        Ok(Cursor {
            arena: Arc::new(term),
            root,
        })
    }

    fn peel_application(&mut self, cursor: &Cursor) -> Result<(Cursor, VecDeque<Cursor>), Halt> {
        let mut root = cursor.root;
        let mut arguments = VecDeque::new();
        loop {
            self.control.step(root.index(), self.cancelled)?;
            let node =
                cursor
                    .arena
                    .node(root)
                    .ok_or(Halt::Fault(WhnfFault::MissingExpression {
                        input: 0,
                        index: root.index(),
                    }))?;
            let ExprNode::Apply { function, argument } = node else {
                break;
            };
            Self::validate_child(root, *function)?;
            Self::validate_child(root, *argument)?;
            arguments.push_front(Cursor {
                arena: Arc::clone(&cursor.arena),
                root: *argument,
            });
            root = *function;
        }
        Ok((
            Cursor {
                arena: Arc::clone(&cursor.arena),
                root,
            },
            arguments,
        ))
    }

    fn compose_application(
        &mut self,
        function: &Cursor,
        arguments: &VecDeque<Cursor>,
    ) -> Result<Cursor, Halt> {
        self.control.step(function.root.index(), self.cancelled)?;
        let mut composer = Composer::new(
            self.control.budget.materialization,
            WhnfPhase::RebuildApplication,
            self.control.steps,
            self.control.reductions,
            self.cancelled,
        );
        let mut root = composer.copy_cursor(function, 0)?;
        for (index, argument) in arguments.iter().enumerate() {
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
        let term = composer.finish(root);
        Ok(Cursor {
            root: term.root(),
            arena: Arc::new(term),
        })
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
        let term = composer.finish(root);
        Ok(Cursor {
            root: term.root(),
            arena: Arc::new(term),
        })
    }

    fn projection_field(
        &mut self,
        frame: &ProjectionFrame,
        scrutinee: &Cursor,
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

        let (head, arguments) = self.peel_application(scrutinee)?;
        let constructor_matches = matches!(
            self.node(&head)?,
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
        let Some(definition) = constant.delta_body() else {
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
        let result = instantiate_term_parameters_from_level_roots_with(
            definition.value(),
            constant.level_parameters(),
            current.arena.levels(),
            levels,
            self.control.budget.materialization,
            self.cancelled,
        );
        match result {
            InstantiationOutcome::Complete(term) => Ok(Some(Cursor {
                root: term.root(),
                arena: Arc::new(term),
            })),
            InstantiationOutcome::Refused(refusal) => {
                Err(Halt::Refusal(WhnfRefusal::DefinitionInstantiation {
                    at: current.root.index(),
                    refusal,
                }))
            }
            InstantiationOutcome::Inconclusive(stop) => {
                Err(Halt::Stop(Box::new(WhnfStop::DefinitionInstantiation {
                    at: current.root.index(),
                    stop,
                    completed_steps: self.control.steps,
                    completed_reductions: self.control.reductions,
                })))
            }
            InstantiationOutcome::InternalFault(fault) => {
                Err(Halt::Fault(WhnfFault::DefinitionInstantiation {
                    at: current.root.index(),
                    fault,
                }))
            }
        }
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

    /// Normalize the demanded recursor major, including its definitions even
    /// when outer conversion delays delta reduction. The pin likewise uses
    /// full WHNF for ordinary recursor majors (`type_checker.cpp`,
    /// `reduce_recursor`). Absorb the sub-run's work into the remaining budget.
    fn whnf_recursor_major(&mut self, cursor: &Cursor) -> Result<Cursor, Halt> {
        let context = self.context.source;
        let budget = WhnfBudget::new(
            self.control
                .budget
                .max_steps
                .saturating_sub(self.control.steps),
            self.control
                .budget
                .max_reductions
                .saturating_sub(self.control.reductions),
            self.control.budget.materialization,
        )
        .with_string(self.remaining_string_budget());
        match whnf_at_mode_with(
            &cursor.arena,
            cursor.root,
            context,
            budget,
            DeltaMode::Eager,
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
                let root = result.term.root();
                Ok(Cursor {
                    arena: Arc::new(result.term),
                    root,
                })
            }
            WhnfOutcome::Refused(refusal) => Err(Halt::Refusal(refusal)),
            WhnfOutcome::Inconclusive(stop) => Err(Halt::Stop(Box::new(stop))),
            WhnfOutcome::InternalFault(fault) => Err(Halt::Fault(fault)),
        }
    }

    /// Structural equality of two cursor roots across arenas, budgeted by the
    /// control: the checker-local equivalent of the gate the pin runs with
    /// `is_def_eq` in `to_cnstr_when_K`. Arenas are acyclic with
    /// backward-only references, so the walk terminates.
    fn structural_cursors_equal(&mut self, left: &Cursor, right: &Cursor) -> Result<bool, Halt> {
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
            let left = self.whnf_recursor_major(&left)?;
            let right = self.whnf_recursor_major(&right)?;
            if self.structural_cursors_equal(&left, &right)? {
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
                        pending.push((
                            Cursor {
                                arena: left.arena.clone(),
                                root: l,
                            },
                            Cursor {
                                arena: right.arena.clone(),
                                root: r,
                            },
                        ));
                    }
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
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
            let replacement =
                self.materialize_wire(&replacement.arena, replacement.root, WhnfPhase::Iota)?;
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
        let domain_cursor = Cursor {
            root: domain.root(),
            arena: Arc::clone(&domain),
        };
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
        let result_cursor = Cursor {
            root: constructor_result.root(),
            arena: Arc::new(constructor_result),
        };
        // The pin's gate: the constructed constructor's type must be defeq to
        // the major's type. Here: the reconstructed result type must match
        // the spine-derived domain by a sufficient checker-owned conversion.
        if !self.k_constructor_types_equal(&domain_cursor, &result_cursor)? {
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
        let term = composer.finish(root);
        Ok(Some(Cursor {
            root: term.root(),
            arena: Arc::new(term),
        }))
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
            )
            .map_err(|halt| composer.map_halt(halt))?;
        let term = composer.finish(root);
        Ok(Some((
            succ,
            VecDeque::from([Cursor {
                root,
                arena: Arc::new(term),
            }]),
        )))
    }

    /// KR-316 (`inductive_reduce_rec`, inductive.h:76): a recursor application
    /// fires when its major premise reduces to a constructor of the recursor's
    /// inductive. The matching rule's right-hand side is instantiated with the
    /// recursor's levels and applied to the spine's parameters, motives, and
    /// minor premises (the indices are consumed by the motive, never applied
    /// to the rule), then the constructor's fields, then the trailing
    /// arguments. Nat literal majors expose one compact constructor layer;
    /// String literal majors and structure-eta coercion remain unsupported.
    #[allow(clippy::too_many_arguments)]
    fn finish_recursor_reduction(
        &mut self,
        metadata: &RecursorDeclaration,
        level_parameters: &[WireName],
        current: &Cursor,
        levels: &[LevelId],
        arguments: &mut VecDeque<Cursor>,
        major_index: usize,
        major: &Cursor,
        prefix: usize,
    ) -> Result<Option<Cursor>, Halt> {
        let reduced_major = self.whnf_recursor_major(major)?;
        // Even when iota stays stuck, retain reductions performed inside the
        // major premise. Dropping them would report progress while returning
        // the original recursor, causing defeq to unfold the same definition
        // forever instead of reaching a stable stuck spine.
        arguments[major_index] = reduced_major.clone();
        let (constructor_name, major_args) =
            if let Some(parts) = self.nat_literal_constructor(metadata, &reduced_major)? {
                parts
            } else {
                let (major_head, major_args) = self.peel_application(&reduced_major)?;
                let ExprNode::Constant { name, .. } = self.node(&major_head)? else {
                    return Ok(None);
                };
                (name.clone(), major_args)
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
        self.control
            .reduction(current.root.index(), self.cancelled)?;
        let instantiated_rhs = match instantiate_term_parameters_from_level_roots_with(
            rule.rhs(),
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
        let rhs = Cursor {
            root: instantiated_rhs.root(),
            arena: Arc::new(instantiated_rhs),
        };
        let mut composer = Composer::new(
            self.control.budget.materialization,
            WhnfPhase::Iota,
            self.control.steps,
            self.control.reductions,
            &mut *self.cancelled,
        );
        let mut root = composer.copy_cursor(&rhs, 0)?;
        for (index, argument) in arguments.iter().take(prefix).enumerate() {
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
        for field in major_args.iter().skip(major_args.len() - field_count) {
            let field = composer.copy_cursor(field, 0)?;
            root = composer.push_expression(
                ExprNode::Apply {
                    function: root,
                    argument: field,
                },
                1,
                0,
            )?;
        }
        for extra in arguments.iter().skip(major_index.saturating_add(1)) {
            let extra = composer.copy_cursor(extra, 0)?;
            root = composer.push_expression(
                ExprNode::Apply {
                    function: root,
                    argument: extra,
                },
                1,
                0,
            )?;
        }
        let term = composer.finish(root);
        Ok(Some(Cursor {
            root: term.root(),
            arena: Arc::new(term),
        }))
    }

    /// Try to reduce a recursor application sitting at a constant head with a
    /// collected spine: the K corner first for a K-flagged recursor with a
    /// stuck major, then the ordinary constructor fire. On a fire the whole
    /// spine is consumed into the composed result and `arguments` is drained.
    fn try_recursor_reduction(
        &mut self,
        current: &Cursor,
        arguments: &mut VecDeque<Cursor>,
    ) -> Result<Option<Cursor>, Halt> {
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
        }
        let prefix = parameter_count
            .saturating_add(usize::try_from(metadata.num_motives()).unwrap_or(usize::MAX))
            .saturating_add(usize::try_from(metadata.num_minors()).unwrap_or(usize::MAX));
        let Some(reduced) = self.finish_recursor_reduction(
            &metadata,
            &level_parameters,
            current,
            &levels,
            arguments,
            major_index,
            &major,
            prefix,
        )?
        else {
            return Ok(None);
        };
        arguments.clear();
        Ok(Some(reduced))
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
        let mut current = self.materialize_term(input, root, WhnfPhase::Initial)?;
        let mut pending_arguments = VecDeque::new();
        let mut projections = Vec::new();

        'normalize: loop {
            self.control.step(current.root.index(), self.cancelled)?;
            match self.head_action(&current)? {
                HeadAction::Metadata(expression) => {
                    self.control
                        .reduction(current.root.index(), self.cancelled)?;
                    current.root = expression;
                    continue;
                }
                HeadAction::Let { value, body } => {
                    self.control
                        .reduction(current.root.index(), self.cancelled)?;
                    let replacement = Cursor {
                        arena: Arc::clone(&current.arena),
                        root: value,
                    };
                    current = self.substitute(&current, body, &replacement, WhnfPhase::Zeta)?;
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
                    current = Cursor {
                        root: term.root(),
                        arena: Arc::new(term),
                    };
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
                    if !pending_arguments.is_empty()
                        && let Some(reduced) =
                            self.try_recursor_reduction(&current, &mut pending_arguments)?
                    {
                        current = reduced;
                        continue;
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
                    projections.push(ProjectionFrame {
                        projection: current.clone(),
                        outer_arguments: std::mem::take(&mut pending_arguments),
                    });
                    current = Cursor {
                        arena: Arc::clone(&current.arena),
                        root: expression,
                    };
                    continue;
                }
                HeadAction::Stuck => {
                    let expanded = {
                        let value = match self.node(&current)? {
                            ExprNode::StringLiteral(value) => Some(value.as_str()),
                            _ => None,
                        };
                        match (value, projections.last()) {
                            (Some(value), Some(frame))
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
                    current = self.substitute(&current, body, &argument, WhnfPhase::Beta)?;
                }
                continue 'normalize;
            }

            if !pending_arguments.is_empty() {
                current = self.compose_application(&current, &pending_arguments)?;
                pending_arguments.clear();
            }

            while let Some(frame) = projections.pop() {
                if let Some(field) = self.projection_field(&frame, &current)? {
                    self.control
                        .reduction(frame.projection.root.index(), self.cancelled)?;
                    current = field;
                    pending_arguments = frame.outer_arguments;
                    continue 'normalize;
                }
                current = self.compose_projection(&frame.projection, &current)?;
                pending_arguments = frame.outer_arguments;
                if !pending_arguments.is_empty() {
                    current = self.compose_application(&current, &pending_arguments)?;
                    pending_arguments.clear();
                }
            }

            let term = self.materialize_wire(&current.arena, current.root, WhnfPhase::Final)?;
            return Ok(WhnfResult {
                term,
                steps: self.control.steps,
                reductions: self.control.reductions,
                delta_reductions: self.delta_reductions,
                has_auxiliary_work: self.has_auxiliary_work,
                string_progress: self.string_progress,
            });
        }
    }
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
}

struct SourceCopy {
    arena: Arc<WireExpr>,
    levels: Vec<Option<LevelId>>,
    expressions: Vec<Option<ExprId>>,
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

    fn push_level(&mut self, node: LevelNode, at: usize) -> Result<LevelId, ComposeHalt> {
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
        Ok(id)
    }

    fn push_expression(&mut self, node: ExprNode, units: u64, at: usize) -> Result<ExprId, Halt> {
        self.control.step(at).map_err(|halt| self.map_halt(halt))?;
        self.control
            .output(units, at)
            .map_err(|halt| self.map_halt(halt))?;
        self.push_expression_charged(node, at)
            .map_err(|halt| self.map_halt(halt))
    }

    fn push_expression_charged(
        &mut self,
        node: ExprNode,
        at: usize,
    ) -> Result<ExprId, ComposeHalt> {
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
        Ok(id)
    }

    fn source_index(&mut self, arena: &Arc<WireExpr>) -> usize {
        if let Some(index) = self
            .sources
            .iter()
            .position(|source| Arc::ptr_eq(&source.arena, arena))
        {
            return index;
        }
        let index = self.sources.len();
        self.sources.push(SourceCopy {
            arena: Arc::clone(arena),
            levels: vec![None; arena.levels().len()],
            expressions: vec![None; arena.nodes().len()],
        });
        index
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
                .push_level(mapped, index)
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

    fn copy_cursor(&mut self, cursor: &Cursor, input: usize) -> Result<ExprId, Halt> {
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
                .push_expression_charged(mapped, index)
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
    whnf_at_mode_with(term, root, context, budget, DeltaMode::Eager, cancelled)
}

pub(crate) fn whnf_core_at_with(
    term: &WireExpr,
    root: ExprId,
    context: &WhnfContext,
    budget: WhnfBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> WhnfOutcome {
    whnf_at_mode_with(term, root, context, budget, DeltaMode::Disabled, cancelled)
}

pub(crate) fn whnf_delta_step_at_with(
    term: &WireExpr,
    root: ExprId,
    context: &WhnfContext,
    budget: WhnfBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> WhnfOutcome {
    whnf_at_mode_with(term, root, context, budget, DeltaMode::Once, cancelled)
}

fn whnf_at_mode_with(
    term: &WireExpr,
    root: ExprId,
    context: &WhnfContext,
    budget: WhnfBudget,
    delta_mode: DeltaMode,
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
        delta_reductions: 0,
        has_auxiliary_work: false,
        string_progress: StringExpansionProgress::default(),
        force_string_delta: false,
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
