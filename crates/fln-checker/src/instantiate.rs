//! Independent universe-parameter instantiation over checker-owned flat arenas.
//!
//! Substitution is simultaneous: a parameter found in the subject is replaced by
//! the corresponding value, but parameters inside replacement values are copied
//! verbatim. Changed maximum ancestors use the pin's smart constructors; the
//! untouched subject is not normalized. That is the KR-105 operation needed
//! before unfolding without borrowing K1's nodes or substitution implementation.

use std::collections::{BTreeMap, HashMap};

use crate::term::{TermBudget, TermLimit, TermStop};
use crate::wire::{
    ExprId, ExprNode, LevelId, LevelNode, WireExpr, WireLevel, WireName, expression_owned_units,
    level_owned_units, usize_units,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstantiationRefusal {
    ArityMismatch { parameters: usize, values: usize },
    DuplicateParameter { first: usize, second: usize },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstantiationInput {
    Subject,
    Replacement { index: usize },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstantiationFault {
    MissingReplacement {
        index: usize,
    },
    MissingLevel {
        input: InstantiationInput,
        index: usize,
    },
    NonBackwardLevelReference {
        input: InstantiationInput,
        parent: usize,
        child: usize,
    },
    MissingExpression {
        index: usize,
    },
    NonBackwardExpressionReference {
        parent: usize,
        child: usize,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstantiationOutcome<T> {
    Complete(T),
    Refused(InstantiationRefusal),
    Inconclusive(TermStop),
    InternalFault(InstantiationFault),
}

enum Halt {
    Stop(TermStop),
    Fault(InstantiationFault),
}

fn halted<T>(halt: Halt) -> InstantiationOutcome<T> {
    match halt {
        Halt::Stop(stop) => InstantiationOutcome::Inconclusive(stop),
        Halt::Fault(fault) => InstantiationOutcome::InternalFault(fault),
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

#[derive(Clone, Copy)]
struct MappedLevel {
    root: LevelId,
    changed: bool,
}

enum BuiltLevel {
    Existing(LevelId),
    Fresh(LevelNode),
}

#[derive(Clone, Copy)]
struct LevelFacts {
    /// Identity of the literal structure, never of a normalized/equivalent level.
    identity: LevelId,
    base: LevelId,
    offset: u32,
    nonzero: bool,
}

#[derive(Clone, Copy)]
enum ReplacementValues<'a> {
    Separate(&'a [WireLevel]),
    ArenaRoots {
        nodes: &'a [LevelNode],
        roots: &'a [LevelId],
    },
}

impl<'a> ReplacementValues<'a> {
    fn len(self) -> usize {
        match self {
            ReplacementValues::Separate(values) => values.len(),
            ReplacementValues::ArenaRoots { roots, .. } => roots.len(),
        }
    }

    fn root(self, index: usize) -> Option<LevelId> {
        match self {
            ReplacementValues::Separate(values) => values.get(index).map(WireLevel::root),
            ReplacementValues::ArenaRoots { roots, .. } => roots.get(index).copied(),
        }
    }

    fn nodes(self, index: usize) -> Option<&'a [LevelNode]> {
        match self {
            ReplacementValues::Separate(values) => values.get(index).map(|value| value.nodes()),
            ReplacementValues::ArenaRoots { nodes, roots } => roots.get(index).map(|_| nodes),
        }
    }
}

struct Instantiator<'a, 'c> {
    parameters: BTreeMap<&'a WireName, usize>,
    values: ReplacementValues<'a>,
    control: Control<'c>,
    levels: Vec<LevelNode>,
    level_facts: Vec<LevelFacts>,
    level_identities: HashMap<LevelNode, LevelId>,
    /// Each replacement's copied root, once copied.
    replacement_maps: Vec<Option<LevelId>>,
}

impl<'a, 'c> Instantiator<'a, 'c> {
    fn prepare(
        parameters: &'a [WireName],
        values: ReplacementValues<'a>,
        budget: TermBudget,
        cancelled: &'c mut dyn FnMut() -> bool,
    ) -> Result<Result<Instantiator<'a, 'c>, InstantiationRefusal>, Halt> {
        if parameters.len() != values.len() {
            return Ok(Err(InstantiationRefusal::ArityMismatch {
                parameters: parameters.len(),
                values: values.len(),
            }));
        }

        let mut control = Control::new(budget, cancelled);
        let mut lookup = BTreeMap::new();
        for (index, parameter) in parameters.iter().enumerate() {
            control.step(index)?;
            if let Some(first) = lookup.insert(parameter, index) {
                return Ok(Err(InstantiationRefusal::DuplicateParameter {
                    first,
                    second: index,
                }));
            }
        }

        let mut replacement_maps = Vec::new();
        replacement_maps.resize_with(values.len(), || None);
        Ok(Ok(Instantiator {
            parameters: lookup,
            values,
            control,
            levels: Vec::new(),
            level_facts: Vec::new(),
            level_identities: HashMap::new(),
            replacement_maps,
        }))
    }

    fn prior_level(
        mapping: &[MappedLevel],
        input: InstantiationInput,
        parent: usize,
        child: LevelId,
    ) -> Result<MappedLevel, Halt> {
        if child.index() >= parent {
            return Err(Halt::Fault(InstantiationFault::NonBackwardLevelReference {
                input,
                parent,
                child: child.index(),
            }));
        }
        mapping
            .get(child.index())
            .copied()
            .ok_or(Halt::Fault(InstantiationFault::MissingLevel {
                input,
                index: child.index(),
            }))
    }

    fn push_level(&mut self, node: LevelNode, at: usize) -> Result<LevelId, Halt> {
        let observed = usize_units(self.levels.len()).saturating_add(1);
        self.control.admit_arena_node(observed, at)?;
        let id = LevelId::from_index(self.levels.len())
            .ok_or_else(|| self.control.arena_nodes(observed, at))?;
        // The output stays a literal arena. These auxiliary identities make
        // structural comparisons and successor/nonzero queries constant-time
        // without repeatedly traversing shared or deep universe subterms.
        let (key, successor, nonzero) = match &node {
            LevelNode::Succ(child) => {
                let facts = self.facts(*child)?;
                (
                    LevelNode::Succ(facts.identity),
                    // The u32 arena ceiling bounds every successor chain.
                    Some((facts.base, facts.offset.saturating_add(1))),
                    true,
                )
            }
            LevelNode::Max(left, right) => {
                let left = self.facts(*left)?;
                let right = self.facts(*right)?;
                (
                    LevelNode::Max(left.identity, right.identity),
                    None,
                    left.nonzero || right.nonzero,
                )
            }
            LevelNode::IMax(left, right) => {
                let left = self.facts(*left)?;
                let right = self.facts(*right)?;
                (
                    LevelNode::IMax(left.identity, right.identity),
                    None,
                    right.nonzero,
                )
            }
            _ => (node.clone(), None, false),
        };
        let identity = *self.level_identities.entry(key).or_insert(id);
        let (base, offset) = successor.unwrap_or((identity, 0));
        self.levels.push(node);
        self.level_facts.push(LevelFacts {
            identity,
            base,
            offset,
            nonzero,
        });
        Ok(id)
    }

    fn facts(&self, id: LevelId) -> Result<LevelFacts, Halt> {
        self.level_facts.get(id.index()).copied().ok_or(Halt::Fault(
            InstantiationFault::MissingLevel {
                input: InstantiationInput::Subject,
                index: id.index(),
            },
        ))
    }

    fn node(&self, id: LevelId) -> Result<&LevelNode, Halt> {
        self.levels
            .get(id.index())
            .ok_or(Halt::Fault(InstantiationFault::MissingLevel {
                input: InstantiationInput::Subject,
                index: id.index(),
            }))
    }

    fn is_zero(&self, id: LevelId) -> Result<bool, Halt> {
        Ok(matches!(self.node(id)?, LevelNode::Zero))
    }

    /// The pin's mk_max, not its universe normalizer. In particular, absorption
    /// inspects only immediate Max children and equality is purely structural.
    fn rebuild_max(&self, left: LevelId, right: LevelId) -> Result<BuiltLevel, Halt> {
        let l = self.facts(left)?;
        let r = self.facts(right)?;
        if self.is_zero(l.base)? && self.is_zero(r.base)? {
            return Ok(BuiltLevel::Existing(if l.offset >= r.offset {
                left
            } else {
                right
            }));
        }
        if l.identity == r.identity || self.is_zero(right)? {
            return Ok(BuiltLevel::Existing(left));
        }
        if self.is_zero(left)? {
            return Ok(BuiltLevel::Existing(right));
        }
        if let LevelNode::Max(a, b) = self.node(right)?
            && (self.facts(*a)?.identity == l.identity || self.facts(*b)?.identity == l.identity)
        {
            return Ok(BuiltLevel::Existing(right));
        }
        if let LevelNode::Max(a, b) = self.node(left)?
            && (self.facts(*a)?.identity == r.identity || self.facts(*b)?.identity == r.identity)
        {
            return Ok(BuiltLevel::Existing(left));
        }
        if l.base == r.base {
            return Ok(BuiltLevel::Existing(if l.offset > r.offset {
                left
            } else {
                right
            }));
        }
        Ok(BuiltLevel::Fresh(LevelNode::Max(left, right)))
    }

    /// update_max invokes these constructors only after a child changes.
    /// Replacement levels are already values and must not enter this route.
    /// Authority: vendor/lean4-src/src/kernel/level.cpp, mk_max/mk_imax and
    /// update_max/instantiate. No implementation is shared with the primary.
    fn rebuild(&self, node: LevelNode) -> Result<BuiltLevel, Halt> {
        match node {
            LevelNode::Max(left, right) => self.rebuild_max(left, right),
            LevelNode::IMax(left, right) => {
                let l = self.facts(left)?;
                let r = self.facts(right)?;
                if r.nonzero {
                    self.rebuild_max(left, right)
                } else if self.is_zero(right)?
                    || self.is_zero(left)?
                    || (l.offset == 1 && self.is_zero(l.base)?)
                {
                    Ok(BuiltLevel::Existing(right))
                } else if l.identity == r.identity {
                    Ok(BuiltLevel::Existing(left))
                } else {
                    Ok(BuiltLevel::Fresh(LevelNode::IMax(left, right)))
                }
            }
            _ => Ok(BuiltLevel::Fresh(node)),
        }
    }

    fn replacement_root(&self, index: usize) -> Result<LevelId, Halt> {
        self.values
            .root(index)
            .ok_or(Halt::Fault(InstantiationFault::MissingReplacement {
                index,
            }))
    }

    fn replacement_nodes(&self, index: usize) -> Result<&'a [LevelNode], Halt> {
        self.values
            .nodes(index)
            .ok_or(Halt::Fault(InstantiationFault::MissingReplacement {
                index,
            }))
    }

    /// Copy the level a replacement's root denotes into the output, once per
    /// replacement. Only the root's own subtree is walked: the arena it lives in
    /// may hold many other levels (a WHNF cursor's shared arena does), and
    /// copying them all made every instantiation cost that whole arena.
    fn copy_replacement(&mut self, value_index: usize) -> Result<LevelId, Halt> {
        if let Some(mapped) = self.replacement_maps.get(value_index).copied().flatten() {
            return Ok(mapped);
        }
        let root = self.replacement_root(value_index)?;
        let nodes = self.replacement_nodes(value_index)?;
        let input = InstantiationInput::Replacement { index: value_index };
        let missing = |index| Halt::Fault(InstantiationFault::MissingLevel { input, index });
        let mut mapping: BTreeMap<usize, LevelId> = BTreeMap::new();
        let mut work = vec![(root.index(), false)];
        while let Some((index, built)) = work.pop() {
            if mapping.contains_key(&index) {
                continue;
            }
            let node = nodes.get(index).ok_or_else(|| missing(index))?;
            let children = match node {
                LevelNode::Succ(child) => [Some(*child), None],
                LevelNode::Max(left, right) | LevelNode::IMax(left, right) => {
                    [Some(*left), Some(*right)]
                }
                LevelNode::Zero | LevelNode::Parameter(_) | LevelNode::Meta(_) => [None, None],
            };
            if !built {
                self.control.step(index)?;
                work.push((index, true));
                for child in children.into_iter().flatten() {
                    if child.index() >= index {
                        return Err(Halt::Fault(InstantiationFault::NonBackwardLevelReference {
                            input,
                            parent: index,
                            child: child.index(),
                        }));
                    }
                    work.push((child.index(), false));
                }
                continue;
            }
            let mapped = |child: &LevelId| {
                mapping
                    .get(&child.index())
                    .copied()
                    .ok_or_else(|| missing(child.index()))
            };
            let copied = match node {
                LevelNode::Zero => LevelNode::Zero,
                LevelNode::Succ(child) => LevelNode::Succ(mapped(child)?),
                LevelNode::Max(left, right) => LevelNode::Max(mapped(left)?, mapped(right)?),
                LevelNode::IMax(left, right) => LevelNode::IMax(mapped(left)?, mapped(right)?),
                LevelNode::Parameter(name) => LevelNode::Parameter(name.clone()),
                LevelNode::Meta(name) => LevelNode::Meta(name.clone()),
            };
            self.control.output(level_owned_units(node), index)?;
            let id = self.push_level(copied, index)?;
            mapping.insert(index, id);
        }

        let mapped_root = mapping
            .get(&root.index())
            .copied()
            .ok_or_else(|| missing(root.index()))?;
        let Some(slot) = self.replacement_maps.get_mut(value_index) else {
            return Err(Halt::Fault(InstantiationFault::MissingReplacement {
                index: value_index,
            }));
        };
        *slot = Some(mapped_root);
        Ok(mapped_root)
    }

    fn map_subject_levels(&mut self, source: &[LevelNode]) -> Result<Vec<LevelId>, Halt> {
        let input = InstantiationInput::Subject;
        let mut mapping = Vec::new();
        for index in 0..source.len() {
            self.control.step(index)?;
            let node = source
                .get(index)
                .ok_or(Halt::Fault(InstantiationFault::MissingLevel {
                    input,
                    index,
                }))?;
            if let LevelNode::Parameter(name) = node
                && let Some(value_index) = self.parameters.get(name).copied()
            {
                mapping.push(MappedLevel {
                    root: self.copy_replacement(value_index)?,
                    // This API carries replacement values, not the pin's
                    // cross-input allocation identity. Selecting a binding
                    // rebuilds its ancestor path even for an equal structure.
                    changed: true,
                });
                continue;
            }
            let (mapped, changed) = match node {
                LevelNode::Succ(child) => {
                    let child = Self::prior_level(&mapping, input, index, *child)?;
                    (LevelNode::Succ(child.root), child.changed)
                }
                LevelNode::Max(left, right) | LevelNode::IMax(left, right) => {
                    let left = Self::prior_level(&mapping, input, index, *left)?;
                    let right = Self::prior_level(&mapping, input, index, *right)?;
                    let mapped = if matches!(node, LevelNode::Max(..)) {
                        LevelNode::Max(left.root, right.root)
                    } else {
                        LevelNode::IMax(left.root, right.root)
                    };
                    (mapped, left.changed || right.changed)
                }
                _ => {
                    self.control.output(level_owned_units(node), index)?;
                    mapping.push(MappedLevel {
                        root: self.push_level(node.clone(), index)?,
                        changed: false,
                    });
                    continue;
                }
            };
            let built = if changed {
                self.rebuild(mapped)?
            } else {
                BuiltLevel::Fresh(mapped)
            };
            let root = match built {
                BuiltLevel::Existing(root) => root,
                BuiltLevel::Fresh(mapped) => {
                    self.control.output(level_owned_units(node), index)?;
                    self.push_level(mapped, index)?
                }
            };
            mapping.push(MappedLevel { root, changed });
        }
        Ok(mapping.into_iter().map(|mapped| mapped.root).collect())
    }

    fn validate_child(parent: usize, child: ExprId) -> Result<(), Halt> {
        if child.index() >= parent {
            return Err(Halt::Fault(
                InstantiationFault::NonBackwardExpressionReference {
                    parent,
                    child: child.index(),
                },
            ));
        }
        Ok(())
    }

    fn validate_expression(parent: usize, node: &ExprNode) -> Result<(), Halt> {
        match node {
            ExprNode::Apply { function, argument } => {
                Self::validate_child(parent, *function)?;
                Self::validate_child(parent, *argument)
            }
            ExprNode::Lambda {
                binder_type, body, ..
            }
            | ExprNode::Forall {
                binder_type, body, ..
            } => {
                Self::validate_child(parent, *binder_type)?;
                Self::validate_child(parent, *body)
            }
            ExprNode::Let {
                type_, value, body, ..
            } => {
                Self::validate_child(parent, *type_)?;
                Self::validate_child(parent, *value)?;
                Self::validate_child(parent, *body)
            }
            ExprNode::Metadata { expression, .. } | ExprNode::Projection { expression, .. } => {
                Self::validate_child(parent, *expression)
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

    fn copy_expressions(
        &mut self,
        term: &WireExpr,
        level_map: &[LevelId],
    ) -> Result<Vec<ExprNode>, Halt> {
        let mut nodes = Vec::new();
        for index in 0..term.nodes().len() {
            self.control.step(index)?;
            let units = {
                let node = term
                    .nodes()
                    .get(index)
                    .ok_or(Halt::Fault(InstantiationFault::MissingExpression { index }))?;
                Self::validate_expression(index, node)?;
                expression_owned_units(node)
            };
            self.control.output(units, index)?;

            let source = term
                .nodes()
                .get(index)
                .cloned()
                .ok_or(Halt::Fault(InstantiationFault::MissingExpression { index }))?;
            let node = match source {
                ExprNode::Sort { level } => ExprNode::Sort {
                    level: level_map.get(level.index()).copied().ok_or(Halt::Fault(
                        InstantiationFault::MissingLevel {
                            input: InstantiationInput::Subject,
                            index: level.index(),
                        },
                    ))?,
                },
                ExprNode::Constant { name, levels } => {
                    let mut mapped = Vec::new();
                    for level in levels {
                        mapped.push(level_map.get(level.index()).copied().ok_or(Halt::Fault(
                            InstantiationFault::MissingLevel {
                                input: InstantiationInput::Subject,
                                index: level.index(),
                            },
                        ))?);
                    }
                    ExprNode::Constant {
                        name,
                        levels: mapped,
                    }
                }
                node => node,
            };

            let observed = usize_units(nodes.len()).saturating_add(1);
            self.control.admit_arena_node(observed, index)?;
            ExprId::from_index(nodes.len())
                .ok_or_else(|| self.control.arena_nodes(observed, index))?;
            nodes.push(node);
        }
        Ok(nodes)
    }
}

pub fn instantiate_level_parameters(
    level: &WireLevel,
    parameters: &[WireName],
    values: &[WireLevel],
    budget: TermBudget,
) -> InstantiationOutcome<WireLevel> {
    instantiate_level_parameters_with(level, parameters, values, budget, || false)
}

pub fn instantiate_level_parameters_with(
    level: &WireLevel,
    parameters: &[WireName],
    values: &[WireLevel],
    budget: TermBudget,
    mut cancelled: impl FnMut() -> bool,
) -> InstantiationOutcome<WireLevel> {
    let mut instantiator = match Instantiator::prepare(
        parameters,
        ReplacementValues::Separate(values),
        budget,
        &mut cancelled,
    ) {
        Ok(Ok(instantiator)) => instantiator,
        Ok(Err(refusal)) => return InstantiationOutcome::Refused(refusal),
        Err(halt) => return halted(halt),
    };
    let mapping = match instantiator.map_subject_levels(level.nodes()) {
        Ok(mapping) => mapping,
        Err(halt) => return halted(halt),
    };
    let root = match mapping.get(level.root().index()).copied() {
        Some(root) => root,
        None => {
            return InstantiationOutcome::InternalFault(InstantiationFault::MissingLevel {
                input: InstantiationInput::Subject,
                index: level.root().index(),
            });
        }
    };
    InstantiationOutcome::Complete(WireLevel::from_parts(instantiator.levels, root))
}

pub fn instantiate_term_parameters(
    term: &WireExpr,
    parameters: &[WireName],
    values: &[WireLevel],
    budget: TermBudget,
) -> InstantiationOutcome<WireExpr> {
    instantiate_term_parameters_with(term, parameters, values, budget, || false)
}

pub fn instantiate_term_parameters_with(
    term: &WireExpr,
    parameters: &[WireName],
    values: &[WireLevel],
    budget: TermBudget,
    mut cancelled: impl FnMut() -> bool,
) -> InstantiationOutcome<WireExpr> {
    instantiate_term_from_values_with(
        term,
        parameters,
        ReplacementValues::Separate(values),
        budget,
        &mut cancelled,
    )
}

pub(crate) fn instantiate_term_parameters_from_level_roots_with(
    term: &WireExpr,
    parameters: &[WireName],
    source_levels: &[LevelNode],
    roots: &[LevelId],
    budget: TermBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> InstantiationOutcome<WireExpr> {
    instantiate_term_from_values_with(
        term,
        parameters,
        ReplacementValues::ArenaRoots {
            nodes: source_levels,
            roots,
        },
        budget,
        cancelled,
    )
}

fn instantiate_term_from_values_with(
    term: &WireExpr,
    parameters: &[WireName],
    values: ReplacementValues<'_>,
    budget: TermBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> InstantiationOutcome<WireExpr> {
    let mut instantiator = match Instantiator::prepare(parameters, values, budget, cancelled) {
        Ok(Ok(instantiator)) => instantiator,
        Ok(Err(refusal)) => return InstantiationOutcome::Refused(refusal),
        Err(halt) => return halted(halt),
    };
    let level_map = match instantiator.map_subject_levels(term.levels()) {
        Ok(mapping) => mapping,
        Err(halt) => return halted(halt),
    };
    let nodes = match instantiator.copy_expressions(term, &level_map) {
        Ok(nodes) => nodes,
        Err(halt) => return halted(halt),
    };
    let root = match ExprId::from_index(term.root().index())
        .filter(|root| nodes.get(root.index()).is_some())
    {
        Some(root) => root,
        None => {
            return InstantiationOutcome::InternalFault(InstantiationFault::MissingExpression {
                index: term.root().index(),
            });
        }
    };
    InstantiationOutcome::Complete(WireExpr::from_parts(nodes, instantiator.levels, root))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn private_arena_corruption_is_an_internal_fault() {
        let level_root = LevelId::from_index(0).expect("zero is a valid level arena index");
        let broken_level = WireLevel::from_parts(vec![LevelNode::Succ(level_root)], level_root);
        assert_eq!(
            instantiate_level_parameters(&broken_level, &[], &[], TermBudget::unlimited(),),
            InstantiationOutcome::InternalFault(InstantiationFault::NonBackwardLevelReference {
                input: InstantiationInput::Subject,
                parent: 0,
                child: 0,
            },)
        );

        let expression_root =
            ExprId::from_index(0).expect("zero is a valid expression arena index");
        let broken_term = WireExpr::from_parts(
            vec![ExprNode::Apply {
                function: expression_root,
                argument: expression_root,
            }],
            Vec::new(),
            expression_root,
        );
        assert_eq!(
            instantiate_term_parameters(&broken_term, &[], &[], TermBudget::unlimited()),
            InstantiationOutcome::InternalFault(
                InstantiationFault::NonBackwardExpressionReference {
                    parent: 0,
                    child: 0,
                },
            )
        );
    }
}
