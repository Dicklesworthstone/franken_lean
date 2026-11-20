//! Reconstruct declaration units from the independent `.olean` reading.
//!
//! Lean's `mkModuleData` exports a persistent-map traversal (private) or name
//! order (public/server), neither of which is dependency order. Metadata names
//! identify atomic admission units; storage adjacency carries no authority.
//! This planner uses only checker-owned values and never decides admission.

use std::collections::{BTreeMap, BTreeSet};

use fln_checker::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantKind, DefinitionBody,
    DefinitionSafety,
};
use fln_checker::wire::{ExprNode, NamePart, WireName};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum UnitKind {
    Single,
    Mutual,
    Inductive,
    Quotient,
}

pub(super) struct DeclarationUnit {
    pub kind: UnitKind,
    pub members: Vec<usize>,
}

pub(super) struct DeclarationPlan {
    pub units: Vec<DeclarationUnit>,
    pub order: Vec<usize>,
    pub already_present: u32,
    pub repeats: Vec<usize>,
}

pub(super) enum PlanError {
    Rejected(WireName),
    Inconclusive(&'static str),
}

type PlanResult<T> = Result<T, PlanError>;

struct Work {
    remaining: u64,
}

impl Work {
    fn charge(&mut self, count: usize) -> PlanResult<()> {
        self.remaining = self
            .remaining
            .checked_sub(u64::try_from(count).unwrap_or(u64::MAX))
            .ok_or(PlanError::Inconclusive(
                "declaration planning budget exhausted",
            ))?;
        Ok(())
    }
}

fn reserved<T>(count: usize) -> PlanResult<Vec<T>> {
    let mut values = Vec::new();
    values
        .try_reserve_exact(count)
        .map_err(|_| PlanError::Inconclusive("declaration planning allocation failed"))?;
    Ok(values)
}

fn push<T>(values: &mut Vec<T>, value: T) -> PlanResult<()> {
    values
        .try_reserve(1)
        .map_err(|_| PlanError::Inconclusive("declaration planning allocation failed"))?;
    values.push(value);
    Ok(())
}

fn rejected(entry: &ConstantEntry) -> PlanError {
    PlanError::Rejected(entry.name().clone())
}

fn charge_reading(declaration: &ConstantDeclaration, work: &mut Work) -> PlanResult<()> {
    work.charge(declaration.level_parameters().len())?;
    for expression in std::iter::once(declaration.type_()).chain(declaration.body_value()) {
        work.charge(expression.nodes().len())?;
        work.charge(expression.levels().len())?;
    }
    if let Some(body) = declaration.definition_body() {
        work.charge(body.mutual().len())?;
    }
    if let Some(metadata) = declaration.inductive_metadata() {
        work.charge(metadata.mutual().len())?;
        work.charge(metadata.constructors().len())?;
    }
    if let Some(metadata) = declaration.recursor_metadata() {
        work.charge(metadata.mutual().len())?;
        work.charge(metadata.rules().len())?;
        for rule in metadata.rules() {
            work.charge(rule.rhs().nodes().len())?;
            work.charge(rule.rhs().levels().len())?;
        }
    }
    Ok(())
}

fn single_definition(body: &DefinitionBody) -> bool {
    body.safety() == DefinitionSafety::Safe
        || body.mutual().is_empty()
        || (body.mutual().len() == 1 && body.safety() != DefinitionSafety::Partial)
}

fn safety_key(safety: DefinitionSafety) -> u8 {
    match safety {
        DefinitionSafety::Safe => 0,
        DefinitionSafety::Unsafe => 1,
        DefinitionSafety::Partial => 2,
    }
}

fn quotient_slot(name: &WireName) -> Option<usize> {
    match name.parts() {
        [NamePart::Text(root)] if root == "Quot" => Some(0),
        [NamePart::Text(root), NamePart::Text(child)] if root == "Quot" => match child.as_str() {
            "mk" => Some(1),
            "lift" => Some(2),
            "ind" => Some(3),
            _ => None,
        },
        _ => None,
    }
}

fn add_unit(
    kind: UnitKind,
    members: Vec<usize>,
    entries: &[ConstantEntry],
    owners: &mut [usize],
    units: &mut Vec<DeclarationUnit>,
    work: &mut Work,
) -> PlanResult<()> {
    work.charge(members.len())?;
    for &member in &members {
        if owners[member] != usize::MAX {
            return Err(rejected(&entries[member]));
        }
        owners[member] = units.len();
    }
    units.push(DeclarationUnit { kind, members });
    Ok(())
}

fn inductive_members(
    entry: &ConstantEntry,
    entries: &[ConstantEntry],
    by_name: &BTreeMap<&WireName, usize>,
    recursors: &BTreeMap<&WireName, Vec<usize>>,
    work: &mut Work,
) -> PlanResult<Vec<usize>> {
    let metadata = entry
        .declaration()
        .inductive_metadata()
        .ok_or_else(|| rejected(entry))?;
    let mut members = Vec::new();
    work.charge(metadata.mutual().len())?;
    for name in metadata.mutual() {
        let &index = by_name.get(name).ok_or_else(|| rejected(entry))?;
        let member = entries[index]
            .declaration()
            .inductive_metadata()
            .ok_or_else(|| rejected(entry))?;
        work.charge(member.mutual().len())?;
        if member.mutual() != metadata.mutual() {
            return Err(rejected(entry));
        }
        push(&mut members, index)?;
    }
    // Types precede their constructors within a unit, in the metadata's mutual
    // order. Every supplied row still goes through inductive reconstruction.
    for name in metadata.mutual() {
        let member = entries[by_name[name]]
            .declaration()
            .inductive_metadata()
            .ok_or_else(|| rejected(entry))?;
        work.charge(member.constructors().len())?;
        for (position, constructor) in member.constructors().iter().enumerate() {
            let &index = by_name.get(constructor).ok_or_else(|| rejected(entry))?;
            let constructor = entries[index]
                .declaration()
                .constructor_metadata()
                .ok_or_else(|| rejected(entry))?;
            if constructor.inductive() != name
                || usize::try_from(constructor.index()).ok() != Some(position)
            {
                return Err(rejected(entry));
            }
            push(&mut members, index)?;
        }
    }
    if let Some(rows) = recursors.get(entry.name()) {
        work.charge(rows.len())?;
        for &index in rows {
            push(&mut members, index)?;
        }
    }
    Ok(members)
}

/// Plan one module against exactly its already checked import environment.
/// Work counts metadata entries, reachable expression nodes, and graph edges;
/// shared expression DAGs are never expanded into trees.
pub(super) fn plan_declarations(
    entries: &[ConstantEntry],
    environment: &ConstantEnvironment,
    maximum_work: u64,
) -> PlanResult<DeclarationPlan> {
    let mut work = Work {
        remaining: maximum_work,
    };
    work.charge(entries.len())?;
    let mut seen = BTreeSet::new();
    let mut by_name = BTreeMap::new();
    let mut already_present = 0u32;
    let mut repeats = Vec::new();
    let mut recursors: BTreeMap<&WireName, Vec<usize>> = BTreeMap::new();
    let mut compiled: BTreeMap<(u8, &[WireName]), Vec<usize>> = BTreeMap::new();
    let mut quotients = [None; 4];
    for (index, entry) in entries.iter().enumerate() {
        if !seen.insert(entry.name()) {
            return Err(rejected(entry));
        }
        let declaration = entry.declaration();
        if let Some(existing) = environment.find(entry.name()) {
            // Imported rows already passed admission in this module's actual
            // closure. Identical readings reuse that authority. Compatible
            // nonidentical theorem rows keep their original imported binding
            // and recheck their own proof after all ordinary declarations.
            charge_reading(declaration, &mut work)?;
            charge_reading(existing, &mut work)?;
            let previous = ConstantEntry::new(entry.name().clone(), existing.clone());
            if previous.reading_digest() != entry.reading_digest() {
                if !super::import_repeats::compatible(&previous, entry, &mut work.remaining)
                    .map_err(PlanError::Inconclusive)?
                {
                    return Err(rejected(entry));
                }
                push(&mut repeats, index)?;
                continue;
            }
            already_present = already_present
                .checked_add(1)
                .ok_or(PlanError::Inconclusive(
                    "declaration presentation count overflowed",
                ))?;
            continue;
        }
        by_name.insert(entry.name(), index);
        if let Some(metadata) = declaration.recursor_metadata()
            && let Some(anchor) = metadata.mutual().first()
        {
            push(recursors.entry(anchor).or_default(), index)?;
        }
        if let Some(body) = declaration.definition_body()
            && !single_definition(body)
        {
            work.charge(body.mutual().len())?;
            if !body.mutual().contains(entry.name()) {
                // Mathlib's compiled recursors retain the inductive block's
                // `all`, not their own names. Lean's add_mutual ignores `all`;
                // native replay groups these by shared metadata and safety.
                push(
                    compiled
                        .entry((safety_key(body.safety()), body.mutual()))
                        .or_default(),
                    index,
                )?;
            }
        }
        if declaration.kind() == ConstantKind::Quotient {
            let slot = quotient_slot(entry.name()).ok_or_else(|| rejected(entry))?;
            if quotients[slot].replace(index).is_some() {
                return Err(rejected(entry));
            }
        }
    }

    let mut units = reserved(entries.len())?;
    let mut constant_units = reserved(entries.len())?;
    constant_units.resize(entries.len(), usize::MAX);
    // Names make both envelope failures and the later topological tie-break
    // independent of the artifact's declaration-array permutation.
    for &index in by_name.values() {
        if constant_units[index] != usize::MAX {
            continue;
        }
        let entry = &entries[index];
        let declaration = entry.declaration();
        let (kind, members) = match declaration.kind() {
            ConstantKind::Inductive => {
                let metadata = declaration
                    .inductive_metadata()
                    .ok_or_else(|| rejected(entry))?;
                if metadata.mutual().first() != Some(entry.name()) {
                    continue;
                }
                (
                    UnitKind::Inductive,
                    inductive_members(entry, entries, &by_name, &recursors, &mut work)?,
                )
            }
            ConstantKind::Constructor | ConstantKind::Recursor => continue,
            ConstantKind::Quotient => {
                let mut members = reserved(4)?;
                for member in quotients {
                    members.push(member.ok_or_else(|| rejected(entry))?);
                }
                (UnitKind::Quotient, members)
            }
            ConstantKind::Definition => {
                let body = declaration
                    .definition_body()
                    .ok_or_else(|| rejected(entry))?;
                if single_definition(body) {
                    (UnitKind::Single, vec![index])
                } else {
                    work.charge(body.mutual().len())?;
                    if !body.mutual().contains(entry.name()) {
                        let mut members = compiled
                            .remove(&(safety_key(body.safety()), body.mutual()))
                            .ok_or_else(|| rejected(entry))?;
                        members.sort_by(|&a, &b| entries[a].name().cmp(entries[b].name()));
                        (UnitKind::Mutual, members)
                    } else {
                        let mut members = reserved(body.mutual().len())?;
                        for name in body.mutual() {
                            let &member = by_name.get(name).ok_or_else(|| rejected(entry))?;
                            let member_body = entries[member]
                                .declaration()
                                .definition_body()
                                .ok_or_else(|| rejected(entry))?;
                            work.charge(member_body.mutual().len())?;
                            if member_body.safety() != body.safety()
                                || member_body.mutual() != body.mutual()
                            {
                                return Err(rejected(entry));
                            }
                            members.push(member);
                        }
                        (UnitKind::Mutual, members)
                    }
                }
            }
            ConstantKind::Axiom | ConstantKind::Theorem | ConstantKind::Opaque => {
                (UnitKind::Single, vec![index])
            }
        };
        add_unit(
            kind,
            members,
            entries,
            &mut constant_units,
            &mut units,
            &mut work,
        )?;
    }
    for &index in by_name.values() {
        if constant_units[index] == usize::MAX {
            return Err(rejected(&entries[index]));
        }
    }

    let mut pending = reserved(units.len())?;
    let mut dependants = reserved(units.len())?;
    dependants.resize_with(units.len(), Vec::new);
    let mut keys = reserved(units.len())?;
    for (unit_index, unit) in units.iter().enumerate() {
        let first = &entries[unit.members[0]];
        let key = unit
            .members
            .iter()
            .map(|&index| entries[index].name())
            .min()
            .ok_or(PlanError::Inconclusive(
                "internal fault: empty declaration unit",
            ))?;
        keys.push(key);
        let mut dependencies = BTreeSet::new();
        for &index in &unit.members {
            let declaration = entries[index].declaration();
            for expression in std::iter::once(declaration.type_()).chain(declaration.body_value()) {
                // OleanReader's per-expression arena contains only nodes
                // reachable from its root, each retained once by address.
                work.charge(expression.nodes().len())?;
                for node in expression.nodes() {
                    let name = match node {
                        ExprNode::Constant { name, .. } => name,
                        ExprNode::Projection { structure_name, .. } => structure_name,
                        _ => continue,
                    };
                    match by_name.get(name) {
                        Some(&owner) => {
                            let dependency = constant_units[owner];
                            if dependency != unit_index {
                                dependencies.insert(dependency);
                            }
                        }
                        None if environment.find(name).is_some() => {}
                        None => return Err(rejected(first)),
                    }
                }
            }
        }
        work.charge(dependencies.len())?;
        pending.push(dependencies.len());
        for dependency in dependencies {
            push(&mut dependants[dependency], unit_index)?;
        }
    }

    let mut ready = BTreeSet::new();
    for (index, &count) in pending.iter().enumerate() {
        if count == 0 {
            ready.insert((keys[index], index));
        }
    }
    let mut order = reserved(units.len())?;
    while let Some((_, index)) = ready.pop_first() {
        work.charge(1)?;
        order.push(index);
        work.charge(dependants[index].len())?;
        for &dependant in &dependants[index] {
            pending[dependant] -= 1;
            if pending[dependant] == 0 {
                ready.insert((keys[dependant], dependant));
            }
        }
    }
    if order.len() != units.len() {
        let name = pending
            .iter()
            .enumerate()
            .filter(|(_, count)| **count != 0)
            .map(|(index, _)| keys[index])
            .min()
            .ok_or(PlanError::Inconclusive(
                "internal fault: incomplete declaration order",
            ))?;
        return Err(PlanError::Rejected(name.clone()));
    }
    repeats.sort_by(|&a, &b| entries[a].name().cmp(entries[b].name()));
    Ok(DeclarationPlan {
        units,
        order,
        already_present,
        repeats,
    })
}
