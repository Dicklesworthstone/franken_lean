//! Immutable definition environment for the independent checker.
//!
//! This is intentionally not an adapter over `fln-env`. It preserves the
//! definition fields needed by later checker-owned delta reduction while using a
//! separate immutable map, separate validation, and separate resource taxonomy.
//! Construction is failure-atomic: only a completely validated environment is
//! published.

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

/// Safety is schema, not an admission decision. Later reduction may unfold only
/// `Safe` definitions; retaining all three forms here prevents the environment
/// boundary from erasing that distinction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefinitionSafety {
    Unsafe,
    Safe,
    Partial,
}

/// Definition payload stored under one canonical name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Definition {
    level_parameters: Vec<WireName>,
    type_: WireExpr,
    value: WireExpr,
    hint: ReducibilityHint,
    safety: DefinitionSafety,
    mutual: Vec<WireName>,
}

impl Definition {
    pub fn new(
        level_parameters: Vec<WireName>,
        type_: WireExpr,
        value: WireExpr,
        hint: ReducibilityHint,
        safety: DefinitionSafety,
        mutual: Vec<WireName>,
    ) -> Definition {
        Definition {
            level_parameters,
            type_,
            value,
            hint,
            safety,
            mutual,
        }
    }

    pub fn level_parameters(&self) -> &[WireName] {
        &self.level_parameters
    }

    pub fn type_(&self) -> &WireExpr {
        &self.type_
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

    pub const fn is_delta_unfoldable(&self) -> bool {
        matches!(self.safety, DefinitionSafety::Safe)
    }
}

/// One input row. The name becomes the immutable map key on successful build.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefinitionEntry {
    name: WireName,
    definition: Definition,
}

impl DefinitionEntry {
    pub fn new(name: WireName, definition: Definition) -> DefinitionEntry {
        DefinitionEntry { name, definition }
    }

    pub fn name(&self) -> &WireName {
        &self.name
    }

    pub fn definition(&self) -> &Definition {
        &self.definition
    }

    fn into_parts(self) -> (WireName, Definition) {
        (self.name, self.definition)
    }
}

/// Persistent, deterministic name resolution for checker-owned definitions.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DefinitionEnvironment {
    definitions: Arc<BTreeMap<WireName, Definition>>,
}

impl DefinitionEnvironment {
    pub fn empty() -> DefinitionEnvironment {
        DefinitionEnvironment::default()
    }

    pub fn len(&self) -> usize {
        self.definitions.len()
    }

    pub fn is_empty(&self) -> bool {
        self.definitions.is_empty()
    }

    pub fn find(&self, name: &WireName) -> Option<&Definition> {
        self.definitions.get(name)
    }

    pub fn definitions(
        &self,
    ) -> impl ExactSizeIterator<Item = (&WireName, &Definition)> + DoubleEndedIterator {
        self.definitions.iter()
    }

    pub fn build(entries: Vec<DefinitionEntry>, budget: EnvironmentBudget) -> EnvironmentOutcome {
        Self::build_with(entries, budget, || false)
    }

    pub fn build_with(
        entries: Vec<DefinitionEntry>,
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
    pub max_definitions: u64,
    pub max_level_parameters: u64,
    pub max_mutual_members: u64,
    pub max_arena_nodes: u64,
    pub max_owned_units: u64,
}

impl EnvironmentBudget {
    pub const fn new(
        max_steps: u64,
        max_definitions: u64,
        max_level_parameters: u64,
        max_mutual_members: u64,
        max_arena_nodes: u64,
        max_owned_units: u64,
    ) -> EnvironmentBudget {
        EnvironmentBudget {
            max_steps,
            max_definitions,
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
    pub definitions: u64,
    pub level_parameters: u64,
    pub mutual_members: u64,
    pub arena_nodes: u64,
    pub owned_units: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnvironmentLimit {
    Steps,
    Definitions,
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
    pub definition: usize,
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
    DuplicateDefinition {
        name: WireName,
    },
    DuplicateLevelParameter {
        definition: usize,
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
        definition: usize,
        term: EnvironmentTerm,
        index: usize,
    },
    NonBackwardExpressionReference {
        definition: usize,
        term: EnvironmentTerm,
        parent: usize,
        child: usize,
    },
    MissingLevel {
        definition: usize,
        term: EnvironmentTerm,
        index: usize,
    },
    NonBackwardLevelReference {
        definition: usize,
        term: EnvironmentTerm,
        parent: usize,
        child: usize,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvironmentOutcome {
    Complete {
        environment: DefinitionEnvironment,
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

    fn definition(&mut self, at: EnvironmentPosition) -> Result<(), EnvironmentStop> {
        self.progress.definitions = self.admit(
            EnvironmentLimit::Definitions,
            self.budget.max_definitions,
            self.progress.definitions,
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

fn missing_level(definition: usize, term: EnvironmentTerm, index: usize) -> Halt {
    Halt::Fault(EnvironmentFault::MissingLevel {
        definition,
        term,
        index,
    })
}

fn validate_level_child(
    levels: &[LevelNode],
    definition: usize,
    term: EnvironmentTerm,
    parent: usize,
    child: LevelId,
) -> Result<(), Halt> {
    if child.index() >= parent {
        return Err(Halt::Fault(EnvironmentFault::NonBackwardLevelReference {
            definition,
            term,
            parent,
            child: child.index(),
        }));
    }
    if levels.get(child.index()).is_none() {
        return Err(missing_level(definition, term, child.index()));
    }
    Ok(())
}

fn validate_expression_child(
    nodes: &[ExprNode],
    definition: usize,
    term: EnvironmentTerm,
    parent: usize,
    child: ExprId,
) -> Result<(), Halt> {
    if child.index() >= parent {
        return Err(Halt::Fault(
            EnvironmentFault::NonBackwardExpressionReference {
                definition,
                term,
                parent,
                child: child.index(),
            },
        ));
    }
    if nodes.get(child.index()).is_none() {
        return Err(Halt::Fault(EnvironmentFault::MissingExpression {
            definition,
            term,
            index: child.index(),
        }));
    }
    Ok(())
}

fn validate_term(
    control: &mut Control<'_>,
    definition: usize,
    term_kind: EnvironmentTerm,
    term: &WireExpr,
) -> Result<(), Halt> {
    if term.node(term.root()).is_none() {
        return Err(Halt::Fault(EnvironmentFault::MissingExpression {
            definition,
            term: term_kind,
            index: term.root().index(),
        }));
    }

    for (index, node) in term.levels().iter().enumerate() {
        let at = EnvironmentPosition {
            definition,
            field: field(term_kind, true),
            index,
        };
        control.step(at).map_err(Halt::Stop)?;
        control.arena_node(at).map_err(Halt::Stop)?;
        control
            .owned_units(level_owned_units(node), at)
            .map_err(Halt::Stop)?;
        for child in level_children(node) {
            validate_level_child(term.levels(), definition, term_kind, index, child)?;
        }
    }

    for (index, node) in term.nodes().iter().enumerate() {
        let at = EnvironmentPosition {
            definition,
            field: field(term_kind, false),
            index,
        };
        control.step(at).map_err(Halt::Stop)?;
        control.arena_node(at).map_err(Halt::Stop)?;
        control
            .owned_units(expression_owned_units(node), at)
            .map_err(Halt::Stop)?;
        for child in expression_children(node) {
            validate_expression_child(term.nodes(), definition, term_kind, index, child)?;
        }
        match node {
            ExprNode::Sort { level } => {
                if term.level(*level).is_none() {
                    return Err(missing_level(definition, term_kind, level.index()));
                }
            }
            ExprNode::Constant { levels, .. } => {
                for level in levels {
                    if term.level(*level).is_none() {
                        return Err(missing_level(definition, term_kind, level.index()));
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
    entries: Vec<DefinitionEntry>,
    budget: EnvironmentBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> EnvironmentOutcome {
    let mut control = Control::new(budget, cancelled);
    let mut definitions = BTreeMap::new();
    let mut duplicates = BTreeSet::new();

    for (input, entry) in entries.into_iter().enumerate() {
        let at = EnvironmentPosition {
            definition: input,
            field: EnvironmentField::Name,
            index: 0,
        };
        if let Err(stop) = control.step(at) {
            return EnvironmentOutcome::Inconclusive(stop);
        }
        if let Err(stop) = control.definition(at) {
            return EnvironmentOutcome::Inconclusive(stop);
        }
        let (name, definition) = entry.into_parts();
        if let Err(stop) = control.owned_units(name_owned_units(&name), at) {
            return EnvironmentOutcome::Inconclusive(stop);
        }
        match definitions.entry(name) {
            Entry::Vacant(entry) => {
                entry.insert(definition);
            }
            Entry::Occupied(entry) => {
                duplicates.insert(entry.key().clone());
            }
        }
    }

    if let Some(name) = duplicates.into_iter().next() {
        return EnvironmentOutcome::Refused {
            refusal: EnvironmentRefusal::DuplicateDefinition { name },
            progress: control.progress,
        };
    }

    for (definition_index, definition) in definitions.values().enumerate() {
        let mut parameters = BTreeMap::new();
        for (parameter_index, parameter) in definition.level_parameters.iter().enumerate() {
            let at = EnvironmentPosition {
                definition: definition_index,
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
                        definition: definition_index,
                        first,
                        second: parameter_index,
                    },
                    progress: control.progress,
                };
            }
        }

        for (member_index, member) in definition.mutual.iter().enumerate() {
            let at = EnvironmentPosition {
                definition: definition_index,
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

        for (term_kind, term) in [
            (EnvironmentTerm::Type, &definition.type_),
            (EnvironmentTerm::Value, &definition.value),
        ] {
            if let Err(halt) = validate_term(&mut control, definition_index, term_kind, term) {
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
        environment: DefinitionEnvironment {
            definitions: Arc::new(definitions),
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

    fn entry(value: WireExpr) -> DefinitionEntry {
        DefinitionEntry::new(
            WireName::default(),
            Definition::new(
                Vec::new(),
                leaf(),
                value,
                ReducibilityHint::Regular(0),
                DefinitionSafety::Safe,
                Vec::new(),
            ),
        )
    }

    #[test]
    fn private_arena_corruption_is_an_internal_fault_and_recovery_is_exact() {
        let root = ExprId::from_index(0).expect("zero is a valid expression index");
        let broken = WireExpr::from_parts(
            vec![ExprNode::Apply {
                function: root,
                argument: root,
            }],
            Vec::new(),
            root,
        );
        assert!(matches!(
            DefinitionEnvironment::build(vec![entry(broken)], EnvironmentBudget::unlimited()),
            EnvironmentOutcome::InternalFault {
                fault: EnvironmentFault::NonBackwardExpressionReference {
                    definition: 0,
                    term: EnvironmentTerm::Value,
                    parent: 0,
                    child: 0,
                },
                ..
            }
        ));
        assert!(matches!(
            DefinitionEnvironment::build(vec![entry(leaf())], EnvironmentBudget::unlimited()),
            EnvironmentOutcome::Complete { .. }
        ));
    }
}
