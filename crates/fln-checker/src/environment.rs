//! Immutable constant environment for the independent checker.
//!
//! This is intentionally not an adapter over `fln-env`. It preserves the
//! common declaration header needed by checker-owned typing and the optional
//! definition body needed by delta reduction while using a separate immutable
//! map, separate validation, and separate resource taxonomy. Construction is
//! failure-atomic: only a completely validated environment is published.

use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::wire::{
    ExprId, ExprNode, LevelId, LevelNode, NamePart, WireExpr, WireName, expression_owned_units,
    level_owned_units,
};

/// The three reducibility-hint shapes carried by a Lean definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReducibilityHint {
    Opaque,
    Abbrev,
    Regular(u32),
}

impl ReducibilityHint {
    /// Height used by KR-309. Abbreviations are selected eagerly; opaque hints
    /// remain ordinary safe definitions with the minimum height.
    pub const fn delta_height(self) -> u32 {
        match self {
            ReducibilityHint::Opaque => 0,
            ReducibilityHint::Abbrev => u32::MAX,
            ReducibilityHint::Regular(height) => height,
        }
    }
}

/// The declaration family carried by one constant header.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstantKind {
    Axiom,
    Theorem,
    Opaque,
    Definition,
    Inductive,
    Constructor,
    Recursor,
    Quotient,
}

/// Unsafe quarantine is common declaration metadata, independent of whether a
/// constant has a definition body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstantSafety {
    Safe,
    Unsafe,
}

/// Definition safety is schema, not an admission decision. Delta reduction may
/// unfold only `Safe` bodies belonging to a safe constant; retaining all three
/// forms prevents the environment boundary from erasing that distinction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefinitionSafety {
    Unsafe,
    Safe,
    Partial,
}

/// Optional definition-specific payload stored behind the common header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefinitionBody {
    value: WireExpr,
    hint: ReducibilityHint,
    safety: DefinitionSafety,
    mutual: Vec<WireName>,
}

impl DefinitionBody {
    pub fn new(
        value: WireExpr,
        hint: ReducibilityHint,
        safety: DefinitionSafety,
        mutual: Vec<WireName>,
    ) -> DefinitionBody {
        DefinitionBody {
            value,
            hint,
            safety,
            mutual,
        }
    }

    pub fn value(&self) -> &WireExpr {
        &self.value
    }

    pub const fn hint(&self) -> ReducibilityHint {
        self.hint
    }

    pub const fn safety(&self) -> DefinitionSafety {
        self.safety
    }

    pub fn mutual(&self) -> &[WireName] {
        &self.mutual
    }
}

/// One constant declaration. Typing and reduction share this header; only a
/// definition may carry a body, and header-only declarations never receive a
/// fabricated value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstantDeclaration {
    level_parameters: Vec<WireName>,
    type_: WireExpr,
    kind: ConstantKind,
    safety: ConstantSafety,
    definition: Option<DefinitionBody>,
}

impl ConstantDeclaration {
    pub fn header(
        level_parameters: Vec<WireName>,
        type_: WireExpr,
        kind: ConstantKind,
        safety: ConstantSafety,
    ) -> ConstantDeclaration {
        ConstantDeclaration {
            level_parameters,
            type_,
            kind,
            safety,
            definition: None,
        }
    }

    pub fn definition(
        level_parameters: Vec<WireName>,
        type_: WireExpr,
        safety: ConstantSafety,
        definition: DefinitionBody,
    ) -> ConstantDeclaration {
        ConstantDeclaration {
            level_parameters,
            type_,
            kind: ConstantKind::Definition,
            safety,
            definition: Some(definition),
        }
    }

    pub fn level_parameters(&self) -> &[WireName] {
        &self.level_parameters
    }

    pub fn type_(&self) -> &WireExpr {
        &self.type_
    }

    pub const fn kind(&self) -> ConstantKind {
        self.kind
    }

    pub const fn safety(&self) -> ConstantSafety {
        self.safety
    }

    pub fn definition_body(&self) -> Option<&DefinitionBody> {
        self.definition.as_ref()
    }

    /// Return the body only when every schema dimension permits delta
    /// reduction. This keeps callers from forgetting the common unsafe flag.
    pub fn delta_body(&self) -> Option<&DefinitionBody> {
        if self.kind == ConstantKind::Definition
            && self.safety == ConstantSafety::Safe
            && matches!(
                self.definition.as_ref().map(DefinitionBody::safety),
                Some(DefinitionSafety::Safe)
            )
        {
            self.definition.as_ref()
        } else {
            None
        }
    }

    pub fn is_delta_unfoldable(&self) -> bool {
        self.delta_body().is_some()
    }
}

/// One input row. The name becomes the immutable map key on successful build.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstantEntry {
    name: WireName,
    declaration: ConstantDeclaration,
}

impl ConstantEntry {
    pub fn new(name: WireName, declaration: ConstantDeclaration) -> ConstantEntry {
        ConstantEntry { name, declaration }
    }

    pub fn name(&self) -> &WireName {
        &self.name
    }

    pub fn declaration(&self) -> &ConstantDeclaration {
        &self.declaration
    }

    fn into_parts(self) -> (WireName, ConstantDeclaration) {
        (self.name, self.declaration)
    }
}

/// Persistent, deterministic name resolution for checker-owned constants.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ConstantEnvironment {
    constants: Arc<BTreeMap<WireName, ConstantDeclaration>>,
}

impl ConstantEnvironment {
    pub fn empty() -> ConstantEnvironment {
        ConstantEnvironment::default()
    }

    pub fn len(&self) -> usize {
        self.constants.len()
    }

    pub fn is_empty(&self) -> bool {
        self.constants.is_empty()
    }

    pub fn find(&self, name: &WireName) -> Option<&ConstantDeclaration> {
        self.constants.get(name)
    }

    pub fn constants(
        &self,
    ) -> impl ExactSizeIterator<Item = (&WireName, &ConstantDeclaration)> + DoubleEndedIterator
    {
        self.constants.iter()
    }

    pub fn build(entries: Vec<ConstantEntry>, budget: EnvironmentBudget) -> EnvironmentOutcome {
        Self::build_with(entries, budget, || false)
    }

    pub fn build_with(
        entries: Vec<ConstantEntry>,
        budget: EnvironmentBudget,
        mut cancelled: impl FnMut() -> bool,
    ) -> EnvironmentOutcome {
        build_environment(entries, budget, &mut cancelled)
    }
}

/// Aggregate limits for one environment build.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EnvironmentBudget {
    pub max_steps: u64,
    pub max_constants: u64,
    pub max_level_parameters: u64,
    pub max_mutual_members: u64,
    pub max_arena_nodes: u64,
    pub max_owned_units: u64,
}

impl EnvironmentBudget {
    pub const fn new(
        max_steps: u64,
        max_constants: u64,
        max_level_parameters: u64,
        max_mutual_members: u64,
        max_arena_nodes: u64,
        max_owned_units: u64,
    ) -> EnvironmentBudget {
        EnvironmentBudget {
            max_steps,
            max_constants,
            max_level_parameters,
            max_mutual_members,
            max_arena_nodes,
            max_owned_units,
        }
    }

    pub const fn unlimited() -> EnvironmentBudget {
        EnvironmentBudget::new(u64::MAX, u64::MAX, u64::MAX, u64::MAX, u64::MAX, u64::MAX)
    }
}

/// Exact completed work. Stops report this without promoting a partial map.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct EnvironmentProgress {
    pub steps: u64,
    pub constants: u64,
    pub level_parameters: u64,
    pub mutual_members: u64,
    pub arena_nodes: u64,
    pub owned_units: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnvironmentLimit {
    Steps,
    Constants,
    LevelParameters,
    MutualMembers,
    ArenaNodes,
    OwnedUnits,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnvironmentField {
    Name,
    LevelParameter,
    MutualMember,
    TypeLevel,
    TypeExpression,
    ValueLevel,
    ValueExpression,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EnvironmentPosition {
    pub constant: usize,
    pub field: EnvironmentField,
    pub index: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvironmentStop {
    Resource {
        limit: EnvironmentLimit,
        allowed: u64,
        observed: u64,
        at: EnvironmentPosition,
        progress: EnvironmentProgress,
    },
    Cancelled {
        at: EnvironmentPosition,
        polls: u64,
        progress: EnvironmentProgress,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvironmentRefusal {
    DuplicateConstant {
        name: WireName,
    },
    DuplicateLevelParameter {
        constant: usize,
        first: usize,
        second: usize,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnvironmentTerm {
    Type,
    Value,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvironmentFault {
    MissingExpression {
        constant: usize,
        term: EnvironmentTerm,
        index: usize,
    },
    NonBackwardExpressionReference {
        constant: usize,
        term: EnvironmentTerm,
        parent: usize,
        child: usize,
    },
    MissingLevel {
        constant: usize,
        term: EnvironmentTerm,
        index: usize,
    },
    NonBackwardLevelReference {
        constant: usize,
        term: EnvironmentTerm,
        parent: usize,
        child: usize,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvironmentOutcome {
    Complete {
        environment: ConstantEnvironment,
        progress: EnvironmentProgress,
    },
    Refused {
        refusal: EnvironmentRefusal,
        progress: EnvironmentProgress,
    },
    Inconclusive(EnvironmentStop),
    InternalFault {
        fault: EnvironmentFault,
        progress: EnvironmentProgress,
    },
}

enum Halt {
    Stop(EnvironmentStop),
    Fault(EnvironmentFault),
}

struct Control<'a> {
    budget: EnvironmentBudget,
    progress: EnvironmentProgress,
    polls: u64,
    cancelled: &'a mut dyn FnMut() -> bool,
}

impl<'a> Control<'a> {
    fn new(budget: EnvironmentBudget, cancelled: &'a mut dyn FnMut() -> bool) -> Control<'a> {
        Control {
            budget,
            progress: EnvironmentProgress::default(),
            polls: 0,
            cancelled,
        }
    }

    fn poll(&mut self, at: EnvironmentPosition) -> Result<(), EnvironmentStop> {
        self.polls = self.polls.saturating_add(1);
        if (self.cancelled)() {
            return Err(EnvironmentStop::Cancelled {
                at,
                polls: self.polls,
                progress: self.progress,
            });
        }
        Ok(())
    }

    fn admit(
        &mut self,
        limit: EnvironmentLimit,
        allowed: u64,
        completed: u64,
        at: EnvironmentPosition,
    ) -> Result<u64, EnvironmentStop> {
        let observed = completed.saturating_add(1);
        if observed > allowed {
            return Err(EnvironmentStop::Resource {
                limit,
                allowed,
                observed,
                at,
                progress: self.progress,
            });
        }
        Ok(observed)
    }

    fn step(&mut self, at: EnvironmentPosition) -> Result<(), EnvironmentStop> {
        self.poll(at)?;
        self.progress.steps = self.admit(
            EnvironmentLimit::Steps,
            self.budget.max_steps,
            self.progress.steps,
            at,
        )?;
        Ok(())
    }

    fn constant(&mut self, at: EnvironmentPosition) -> Result<(), EnvironmentStop> {
        self.progress.constants = self.admit(
            EnvironmentLimit::Constants,
            self.budget.max_constants,
            self.progress.constants,
            at,
        )?;
        Ok(())
    }

    fn level_parameter(&mut self, at: EnvironmentPosition) -> Result<(), EnvironmentStop> {
        self.progress.level_parameters = self.admit(
            EnvironmentLimit::LevelParameters,
            self.budget.max_level_parameters,
            self.progress.level_parameters,
            at,
        )?;
        Ok(())
    }

    fn mutual_member(&mut self, at: EnvironmentPosition) -> Result<(), EnvironmentStop> {
        self.progress.mutual_members = self.admit(
            EnvironmentLimit::MutualMembers,
            self.budget.max_mutual_members,
            self.progress.mutual_members,
            at,
        )?;
        Ok(())
    }

    fn arena_node(&mut self, at: EnvironmentPosition) -> Result<(), EnvironmentStop> {
        self.progress.arena_nodes = self.admit(
            EnvironmentLimit::ArenaNodes,
            self.budget.max_arena_nodes,
            self.progress.arena_nodes,
            at,
        )?;
        Ok(())
    }

    fn owned_units(&mut self, units: u64, at: EnvironmentPosition) -> Result<(), EnvironmentStop> {
        let observed = self.progress.owned_units.saturating_add(units);
        if observed > self.budget.max_owned_units {
            return Err(EnvironmentStop::Resource {
                limit: EnvironmentLimit::OwnedUnits,
                allowed: self.budget.max_owned_units,
                observed,
                at,
                progress: self.progress,
            });
        }
        self.progress.owned_units = observed;
        Ok(())
    }
}

fn name_owned_units(name: &WireName) -> u64 {
    name.parts().iter().fold(0u64, |units, part| {
        let payload = match part {
            NamePart::Numeric { .. } => 0,
            NamePart::Text(text) => u64::try_from(text.len()).unwrap_or(u64::MAX),
        };
        units.saturating_add(1).saturating_add(payload)
    })
}

fn expression_children(node: &ExprNode) -> impl Iterator<Item = ExprId> {
    let children = match node {
        ExprNode::Apply { function, argument } => [Some(*function), Some(*argument), None],
        ExprNode::Lambda {
            binder_type, body, ..
        }
        | ExprNode::Forall {
            binder_type, body, ..
        } => [Some(*binder_type), Some(*body), None],
        ExprNode::Let {
            type_, value, body, ..
        } => [Some(*type_), Some(*value), Some(*body)],
        ExprNode::Metadata { expression, .. } | ExprNode::Projection { expression, .. } => {
            [Some(*expression), None, None]
        }
        ExprNode::Bound { .. }
        | ExprNode::Free { .. }
        | ExprNode::Meta { .. }
        | ExprNode::Sort { .. }
        | ExprNode::Constant { .. }
        | ExprNode::NatLiteral { .. }
        | ExprNode::StringLiteral(_) => [None, None, None],
    };
    children.into_iter().flatten()
}

fn level_children(node: &LevelNode) -> impl Iterator<Item = LevelId> {
    let children = match node {
        LevelNode::Succ(child) => [Some(*child), None],
        LevelNode::Max(left, right) | LevelNode::IMax(left, right) => [Some(*left), Some(*right)],
        LevelNode::Zero | LevelNode::Parameter(_) | LevelNode::Meta(_) => [None, None],
    };
    children.into_iter().flatten()
}

fn field(term: EnvironmentTerm, levels: bool) -> EnvironmentField {
    match (term, levels) {
        (EnvironmentTerm::Type, true) => EnvironmentField::TypeLevel,
        (EnvironmentTerm::Type, false) => EnvironmentField::TypeExpression,
        (EnvironmentTerm::Value, true) => EnvironmentField::ValueLevel,
        (EnvironmentTerm::Value, false) => EnvironmentField::ValueExpression,
    }
}

fn missing_level(constant: usize, term: EnvironmentTerm, index: usize) -> Halt {
    Halt::Fault(EnvironmentFault::MissingLevel {
        constant,
        term,
        index,
    })
}

fn validate_level_child(
    levels: &[LevelNode],
    constant: usize,
    term: EnvironmentTerm,
    parent: usize,
    child: LevelId,
) -> Result<(), Halt> {
    if child.index() >= parent {
        return Err(Halt::Fault(EnvironmentFault::NonBackwardLevelReference {
            constant,
            term,
            parent,
            child: child.index(),
        }));
    }
    if levels.get(child.index()).is_none() {
        return Err(missing_level(constant, term, child.index()));
    }
    Ok(())
}

fn validate_expression_child(
    nodes: &[ExprNode],
    constant: usize,
    term: EnvironmentTerm,
    parent: usize,
    child: ExprId,
) -> Result<(), Halt> {
    if child.index() >= parent {
        return Err(Halt::Fault(
            EnvironmentFault::NonBackwardExpressionReference {
                constant,
                term,
                parent,
                child: child.index(),
            },
        ));
    }
    if nodes.get(child.index()).is_none() {
        return Err(Halt::Fault(EnvironmentFault::MissingExpression {
            constant,
            term,
            index: child.index(),
        }));
    }
    Ok(())
}

fn validate_term(
    control: &mut Control<'_>,
    constant: usize,
    term_kind: EnvironmentTerm,
    term: &WireExpr,
) -> Result<(), Halt> {
    if term.node(term.root()).is_none() {
        return Err(Halt::Fault(EnvironmentFault::MissingExpression {
            constant,
            term: term_kind,
            index: term.root().index(),
        }));
    }

    for (index, node) in term.levels().iter().enumerate() {
        let at = EnvironmentPosition {
            constant,
            field: field(term_kind, true),
            index,
        };
        control.step(at).map_err(Halt::Stop)?;
        control.arena_node(at).map_err(Halt::Stop)?;
        control
            .owned_units(level_owned_units(node), at)
            .map_err(Halt::Stop)?;
        for child in level_children(node) {
            validate_level_child(term.levels(), constant, term_kind, index, child)?;
        }
    }

    for (index, node) in term.nodes().iter().enumerate() {
        let at = EnvironmentPosition {
            constant,
            field: field(term_kind, false),
            index,
        };
        control.step(at).map_err(Halt::Stop)?;
        control.arena_node(at).map_err(Halt::Stop)?;
        control
            .owned_units(expression_owned_units(node), at)
            .map_err(Halt::Stop)?;
        for child in expression_children(node) {
            validate_expression_child(term.nodes(), constant, term_kind, index, child)?;
        }
        match node {
            ExprNode::Sort { level } => {
                if term.level(*level).is_none() {
                    return Err(missing_level(constant, term_kind, level.index()));
                }
            }
            ExprNode::Constant { levels, .. } => {
                for level in levels {
                    if term.level(*level).is_none() {
                        return Err(missing_level(constant, term_kind, level.index()));
                    }
                }
            }
            ExprNode::Bound { .. }
            | ExprNode::Free { .. }
            | ExprNode::Meta { .. }
            | ExprNode::Apply { .. }
            | ExprNode::Lambda { .. }
            | ExprNode::Forall { .. }
            | ExprNode::Let { .. }
            | ExprNode::NatLiteral { .. }
            | ExprNode::StringLiteral(_)
            | ExprNode::Metadata { .. }
            | ExprNode::Projection { .. } => {}
        }
    }
    Ok(())
}

fn build_environment(
    entries: Vec<ConstantEntry>,
    budget: EnvironmentBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> EnvironmentOutcome {
    let mut control = Control::new(budget, cancelled);
    let mut constants = BTreeMap::new();
    let mut duplicates = BTreeSet::new();

    for (input, entry) in entries.into_iter().enumerate() {
        let at = EnvironmentPosition {
            constant: input,
            field: EnvironmentField::Name,
            index: 0,
        };
        if let Err(stop) = control.step(at) {
            return EnvironmentOutcome::Inconclusive(stop);
        }
        if let Err(stop) = control.constant(at) {
            return EnvironmentOutcome::Inconclusive(stop);
        }
        let (name, declaration) = entry.into_parts();
        if let Err(stop) = control.owned_units(name_owned_units(&name), at) {
            return EnvironmentOutcome::Inconclusive(stop);
        }
        match constants.entry(name) {
            Entry::Vacant(entry) => {
                entry.insert(declaration);
            }
            Entry::Occupied(entry) => {
                duplicates.insert(entry.key().clone());
            }
        }
    }

    if let Some(name) = duplicates.into_iter().next() {
        return EnvironmentOutcome::Refused {
            refusal: EnvironmentRefusal::DuplicateConstant { name },
            progress: control.progress,
        };
    }

    for (constant_index, declaration) in constants.values().enumerate() {
        let mut parameters = BTreeMap::new();
        for (parameter_index, parameter) in declaration.level_parameters.iter().enumerate() {
            let at = EnvironmentPosition {
                constant: constant_index,
                field: EnvironmentField::LevelParameter,
                index: parameter_index,
            };
            if let Err(stop) = control.step(at) {
                return EnvironmentOutcome::Inconclusive(stop);
            }
            if let Err(stop) = control.level_parameter(at) {
                return EnvironmentOutcome::Inconclusive(stop);
            }
            if let Err(stop) = control.owned_units(name_owned_units(parameter), at) {
                return EnvironmentOutcome::Inconclusive(stop);
            }
            if let Some(first) = parameters.insert(parameter, parameter_index) {
                return EnvironmentOutcome::Refused {
                    refusal: EnvironmentRefusal::DuplicateLevelParameter {
                        constant: constant_index,
                        first,
                        second: parameter_index,
                    },
                    progress: control.progress,
                };
            }
        }

        if let Err(halt) = validate_term(
            &mut control,
            constant_index,
            EnvironmentTerm::Type,
            &declaration.type_,
        ) {
            return match halt {
                Halt::Stop(stop) => EnvironmentOutcome::Inconclusive(stop),
                Halt::Fault(fault) => EnvironmentOutcome::InternalFault {
                    fault,
                    progress: control.progress,
                },
            };
        }

        if let Some(definition) = declaration.definition.as_ref() {
            for (member_index, member) in definition.mutual.iter().enumerate() {
                let at = EnvironmentPosition {
                    constant: constant_index,
                    field: EnvironmentField::MutualMember,
                    index: member_index,
                };
                if let Err(stop) = control.step(at) {
                    return EnvironmentOutcome::Inconclusive(stop);
                }
                if let Err(stop) = control.mutual_member(at) {
                    return EnvironmentOutcome::Inconclusive(stop);
                }
                if let Err(stop) = control.owned_units(name_owned_units(member), at) {
                    return EnvironmentOutcome::Inconclusive(stop);
                }
            }

            if let Err(halt) = validate_term(
                &mut control,
                constant_index,
                EnvironmentTerm::Value,
                &definition.value,
            ) {
                return match halt {
                    Halt::Stop(stop) => EnvironmentOutcome::Inconclusive(stop),
                    Halt::Fault(fault) => EnvironmentOutcome::InternalFault {
                        fault,
                        progress: control.progress,
                    },
                };
            }
        }
    }

    EnvironmentOutcome::Complete {
        environment: ConstantEnvironment {
            constants: Arc::new(constants),
        },
        progress: control.progress,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf() -> WireExpr {
        let root = ExprId::from_index(0).expect("zero is a valid expression index");
        WireExpr::from_parts(
            vec![ExprNode::NatLiteral { limbs_le: vec![0] }],
            Vec::new(),
            root,
        )
    }

    fn entry(value: WireExpr) -> ConstantEntry {
        ConstantEntry::new(
            WireName::default(),
            ConstantDeclaration::definition(
                Vec::new(),
                leaf(),
                ConstantSafety::Safe,
                DefinitionBody::new(
                    value,
                    ReducibilityHint::Regular(0),
                    DefinitionSafety::Safe,
                    Vec::new(),
                ),
            ),
        )
    }

    #[test]
    fn private_type_and_value_corruption_are_distinct_faults_and_recovery_is_exact() {
        let root = ExprId::from_index(0).expect("zero is a valid expression index");
        let broken = WireExpr::from_parts(
            vec![ExprNode::Apply {
                function: root,
                argument: root,
            }],
            Vec::new(),
            root,
        );
        let broken_type = ConstantEntry::new(
            WireName::default(),
            ConstantDeclaration::header(
                Vec::new(),
                broken.clone(),
                ConstantKind::Axiom,
                ConstantSafety::Safe,
            ),
        );
        assert!(matches!(
            ConstantEnvironment::build(vec![broken_type], EnvironmentBudget::unlimited()),
            EnvironmentOutcome::InternalFault {
                fault: EnvironmentFault::NonBackwardExpressionReference {
                    constant: 0,
                    term: EnvironmentTerm::Type,
                    parent: 0,
                    child: 0,
                },
                ..
            }
        ));
        assert!(matches!(
            ConstantEnvironment::build(vec![entry(broken)], EnvironmentBudget::unlimited()),
            EnvironmentOutcome::InternalFault {
                fault: EnvironmentFault::NonBackwardExpressionReference {
                    constant: 0,
                    term: EnvironmentTerm::Value,
                    parent: 0,
                    child: 0,
                },
                ..
            }
        ));
        assert!(matches!(
            ConstantEnvironment::build(vec![entry(leaf())], EnvironmentBudget::unlimited()),
            EnvironmentOutcome::Complete { .. }
        ));
    }
}
