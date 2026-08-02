//! Eager weak-head reduction over checker-owned flat arenas.
//!
//! This module deliberately does not share the primary kernel normalizer. It
//! implements the eager checker portion of KR-200 through KR-204 with flat arena
//! cursors and explicit heap frames: safe-definition delta, metadata stripping,
//! beta, let-zeta, supplied let-bound free unfolding, and explicit-constructor
//! projection. Unsafe and partial definitions stay stuck. Recursors, native
//! extensions, and numeric/string acceleration remain outside this layer.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::Arc;

use crate::environment::DefinitionEnvironment;
use crate::instantiate::{
    InstantiationFault, InstantiationOutcome, InstantiationRefusal,
    instantiate_term_parameters_from_level_roots_with,
};
use crate::term::{
    TermBudget, TermFault, TermLimit, TermOutcome, TermStop, copy_subterm_with,
    substitute_bound_subterms_with,
};
use crate::wire::{
    ExprId, ExprNode, LevelId, LevelNode, WireExpr, WireName, expression_owned_units,
    level_owned_units, usize_units,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FreeBinding {
    name: WireName,
    value: WireExpr,
}

impl FreeBinding {
    pub fn new(name: WireName, value: WireExpr) -> FreeBinding {
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
    definitions: DefinitionEnvironment,
}

impl WhnfContext {
    pub fn new(
        free_bindings: Vec<FreeBinding>,
        projection_rules: Vec<ProjectionRule>,
        definitions: DefinitionEnvironment,
    ) -> WhnfContext {
        WhnfContext {
            free_bindings,
            projection_rules,
            definitions,
        }
    }

    pub fn free_bindings(&self) -> &[FreeBinding] {
        &self.free_bindings
    }

    pub fn projection_rules(&self) -> &[ProjectionRule] {
        &self.projection_rules
    }

    pub fn definitions(&self) -> &DefinitionEnvironment {
        &self.definitions
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WhnfBudget {
    pub max_steps: u64,
    pub max_reductions: u64,
    pub materialization: TermBudget,
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
        }
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WhnfFault {
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WhnfResult {
    pub term: WireExpr,
    pub steps: u64,
    pub reductions: u64,
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
    Stop(WhnfStop),
    Fault(WhnfFault),
}

fn outcome(result: Result<WhnfResult, Halt>) -> WhnfOutcome {
    match result {
        Ok(result) => WhnfOutcome::Complete(result),
        Err(Halt::Refusal(refusal)) => WhnfOutcome::Refused(refusal),
        Err(Halt::Stop(stop)) => WhnfOutcome::Inconclusive(stop),
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
            return Err(Halt::Stop(WhnfStop::Cancelled {
                at,
                polls: self.polls,
                completed_steps: self.steps,
                completed_reductions: self.reductions,
            }));
        }
        Ok(())
    }

    fn step(&mut self, at: usize, cancelled: &mut dyn FnMut() -> bool) -> Result<(), Halt> {
        self.poll(at, cancelled)?;
        let observed = self.steps.saturating_add(1);
        if observed > self.budget.max_steps {
            return Err(Halt::Stop(WhnfStop::Resource {
                limit: WhnfLimit::Steps,
                allowed: self.budget.max_steps,
                observed,
                at,
                completed_steps: self.steps,
                completed_reductions: self.reductions,
            }));
        }
        self.steps = observed;
        Ok(())
    }

    fn reduction(&mut self, at: usize, cancelled: &mut dyn FnMut() -> bool) -> Result<(), Halt> {
        self.poll(at, cancelled)?;
        let observed = self.reductions.saturating_add(1);
        if observed > self.budget.max_reductions {
            return Err(Halt::Stop(WhnfStop::Resource {
                limit: WhnfLimit::Reductions,
                allowed: self.budget.max_reductions,
                observed,
                at,
                completed_steps: self.steps,
                completed_reductions: self.reductions,
            }));
        }
        self.reductions = observed;
        Ok(())
    }

    fn term_halt<T>(&self, phase: WhnfPhase, outcome: TermOutcome<T>) -> Result<T, Halt> {
        match outcome {
            TermOutcome::Complete(value) => Ok(value),
            TermOutcome::Inconclusive(stop) => Err(Halt::Stop(WhnfStop::Materialization {
                phase,
                stop,
                completed_steps: self.steps,
                completed_reductions: self.reductions,
            })),
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
        let (rule_index, field_index) = {
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
            let Some(rule_index) = self.context.projection_rules.get(structure_name).copied()
            else {
                return Ok(None);
            };
            (rule_index, *index)
        };

        let (head, arguments) = self.peel_application(scrutinee)?;
        let constructor_matches = {
            let rule = self
                .context
                .source
                .projection_rules
                .get(rule_index)
                .ok_or(Halt::Fault(WhnfFault::MissingExpression {
                    input: 0,
                    index: rule_index,
                }))?;
            matches!(
                self.node(&head)?,
                ExprNode::Constant { name, .. } if name == &rule.constructor_name
            )
        };
        if !constructor_matches {
            return Ok(None);
        }

        let rule = self
            .context
            .source
            .projection_rules
            .get(rule_index)
            .ok_or(Halt::Fault(WhnfFault::MissingExpression {
                input: 0,
                index: rule_index,
            }))?;
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
        let Some(definition) = self.context.source.definitions().find(name) else {
            return Ok(None);
        };
        if !definition.is_delta_unfoldable() {
            return Ok(None);
        }
        if definition.level_parameters().len() != levels.len() {
            return Err(Halt::Refusal(WhnfRefusal::DefinitionInstantiation {
                at: current.root.index(),
                refusal: InstantiationRefusal::ArityMismatch {
                    parameters: definition.level_parameters().len(),
                    values: levels.len(),
                },
            }));
        }

        self.control
            .reduction(current.root.index(), self.cancelled)?;
        let result = instantiate_term_parameters_from_level_roots_with(
            definition.value(),
            definition.level_parameters(),
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
                Err(Halt::Stop(WhnfStop::DefinitionInstantiation {
                    at: current.root.index(),
                    stop,
                    completed_steps: self.control.steps,
                    completed_reductions: self.control.reductions,
                }))
            }
            InstantiationOutcome::InternalFault(fault) => {
                Err(Halt::Fault(WhnfFault::DefinitionInstantiation {
                    at: current.root.index(),
                    fault,
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
                    if let Some(unfolded) = self.unfold_definition(&current)? {
                        current = unfolded;
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
                HeadAction::Free(None) | HeadAction::Stuck => {}
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
            ComposeHalt::Stop(stop) => Halt::Stop(WhnfStop::Materialization {
                phase: self.phase,
                stop,
                completed_steps: self.outer_steps,
                completed_reductions: self.outer_reductions,
            }),
            ComposeHalt::Fault(fault) => Halt::Fault(fault),
        }
    }

    fn finish(self, root: ExprId) -> WireExpr {
        WireExpr::from_parts(self.expressions, self.levels, root)
    }
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
