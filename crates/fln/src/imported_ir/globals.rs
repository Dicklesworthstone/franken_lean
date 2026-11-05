//! Preparation and result handling for explicitly authorized initialization.
//!
//! Selected globals use a closed executable dependency graph. Full journal
//! replay instead preserves the supplied import and declaration order. Every
//! initializer is selected and checked by the ordinary imported-code policy.
//! Dependency discovery includes all branches and partial applications, so a
//! callback cannot hide a forward global read. Cycles remain typed refusals.

use super::*;
use fln_core::outcome::InternalFault;
use fln_vm::interpreter::VmRefusal;

#[derive(Clone, Debug)]
pub(super) struct InitializedGlobal {
    pub declaration: Name,
    pub initializer: Name,
}

#[derive(Clone, Debug)]
pub(super) struct InitializationStep {
    pub declaration: Name,
    pub initializer: Name,
    pub global_slot: Option<usize>,
}

#[derive(Clone, Debug, Default)]
pub(super) struct InitializationPlan {
    pub globals: Vec<InitializedGlobal>,
    pub steps: Vec<InitializationStep>,
}

impl InitializationPlan {
    fn push_global(&mut self, global: InitializedGlobal) {
        self.steps.push(InitializationStep {
            declaration: global.declaration.clone(),
            initializer: global.initializer.clone(),
            global_slot: Some(self.globals.len()),
        });
        self.globals.push(global);
    }
}

pub(super) struct InitializerIndex {
    pub named: BTreeMap<Name, Name>,
    pub journal: Vec<(Name, Option<Name>)>,
    order: BTreeMap<Name, usize>,
    has_standalone_actions: bool,
}

pub(super) fn contract(declaration: &Name, detail: &'static str) -> IrExecutionError {
    IrExecutionError::InitializerContract {
        declaration: declaration.clone(),
        detail,
    }
}

pub(super) fn index(
    modules: &[IrModule],
    limits: IrExecutionLimits,
) -> Result<InitializerIndex, IrExecutionError> {
    let mut named = BTreeMap::new();
    let mut order = BTreeMap::new();
    let mut seen = BTreeSet::new();
    let mut journal = Vec::new();
    let mut has_standalone_actions = false;
    for module in modules {
        has_standalone_actions |= module
            .initializers
            .iter()
            .any(|entry| entry.initializer.is_none());
        for entry in &module.initializers {
            if seen.len() >= limits.ir.max_declarations {
                return Err(IrExecutionError::Limit("initializer entries"));
            }
            if entry.declaration.is_anonymous() || !seen.insert(entry.declaration.clone()) {
                return Err(contract(
                    &entry.declaration,
                    "anonymous or repeated initialized declaration",
                ));
            }
            journal.push((entry.declaration.clone(), entry.initializer.clone()));
            if let Some(initializer) = &entry.initializer {
                if initializer.is_anonymous() {
                    return Err(contract(&entry.declaration, "anonymous named initializer"));
                }
                order.insert(entry.declaration.clone(), order.len());
                named.insert(entry.declaration.clone(), initializer.clone());
            }
        }
    }
    Ok(InitializerIndex {
        named,
        journal,
        order,
        has_standalone_actions,
    })
}

pub(super) fn validate_global(
    name: &Name,
    declaration: &IrDecl,
    initializer: &Name,
    declarations: &BTreeMap<Name, &IrDecl>,
    index: &InitializerIndex,
    full_journal: bool,
) -> Result<(), IrExecutionError> {
    // A standalone action in another supplied module can mutate this global
    // even when no function from that module is in the static call closure.
    // Without the full-journal capability, never silently omit that action.
    if index.has_standalone_actions && !full_journal {
        return Err(contract(
            name,
            "supplied modules also require standalone initialization actions",
        ));
    }
    let IrDecl::Function { params, result, .. } = declaration else {
        return Err(contract(name, "initialized global has no IR declaration"));
    };
    if !params.is_empty() {
        return Err(contract(
            name,
            "initialized global is not a zero-argument declaration",
        ));
    }
    check_type(name, result)?;
    validate_initializer(name, initializer, declarations)
}

pub(super) fn validate_actions(
    index: &InitializerIndex,
    declarations: &BTreeMap<Name, &IrDecl>,
) -> Result<(), IrExecutionError> {
    for (name, initializer) in &index.journal {
        if initializer.is_none() {
            validate_initializer(name, name, declarations)?;
        }
    }
    Ok(())
}

fn validate_initializer(
    name: &Name,
    initializer: &Name,
    declarations: &BTreeMap<Name, &IrDecl>,
) -> Result<(), IrExecutionError> {
    if native_row(initializer).is_some()
        || native_signature::boxed_row(initializer).is_some()
        || fln_vm::macro_native::row_for_name(initializer).is_some()
    {
        return Err(contract(
            name,
            "initializer must have an interpreted IO body",
        ));
    }
    let declaration = declarations
        .get(initializer)
        .ok_or_else(|| IrExecutionError::MissingDeclaration(initializer.clone()))?;
    let IrDecl::Function { params, result, .. } = declaration else {
        return Err(contract(
            name,
            "initializer must have an interpreted IO body",
        ));
    };
    if params.len() != 1
        || params[0].ty != IrType::Void
        || !matches!(result, IrType::Object | IrType::TObject)
    {
        return Err(contract(
            name,
            "initializer must return IO.Result with one erased world parameter",
        ));
    }
    Ok(())
}

pub(super) fn plan(
    index: &InitializerIndex,
    selected: &BTreeMap<Name, &IrDecl>,
    limits: IrExecutionLimits,
) -> Result<InitializationPlan, IrExecutionError> {
    let globals: BTreeMap<_, _> = index
        .named
        .iter()
        .filter(|(name, _)| selected.contains_key(*name))
        .map(|(name, initializer)| (name.clone(), initializer.clone()))
        .collect();
    let reads = initializer_reads(index, selected, limits)?;
    let mut dependencies = BTreeMap::new();
    let mut dependents: BTreeMap<Name, BTreeSet<Name>> = BTreeMap::new();
    for global in globals.keys() {
        let reads = &reads[global];
        for dependency in reads {
            dependents
                .entry(dependency.clone())
                .or_default()
                .insert(global.clone());
        }
        dependencies.insert(global.clone(), reads.len());
    }
    // Preserve journal order where dependency order leaves a choice. Callers
    // supplying raw modules define their order; this never pretends to replay
    // every action in a transitive import graph.
    let mut ready: BTreeSet<_> = dependencies
        .iter()
        .filter(|(_, count)| **count == 0)
        .map(|(name, _)| (index.order[name], name.clone()))
        .collect();
    let mut result = InitializationPlan::default();
    while let Some((_, name)) = ready.pop_first() {
        result.push_global(InitializedGlobal {
            declaration: name.clone(),
            initializer: globals[&name].clone(),
        });
        if let Some(next) = dependents.get(&name) {
            for dependent in next {
                let remaining = dependencies
                    .get_mut(dependent)
                    .expect("known dependency vertex");
                *remaining -= 1;
                if *remaining == 0 {
                    ready.insert((index.order[dependent], dependent.clone()));
                }
            }
        }
    }
    if result.globals.len() != globals.len() {
        let name = dependencies
            .iter()
            .find(|(_, count)| **count != 0)
            .unwrap()
            .0;
        return Err(contract(name, "cyclic initialized-global dependency"));
    }
    Ok(result)
}

/// Full startup cannot reorder effects to satisfy a forward read. Unlike the
/// selected-global capability, it retains every journal member and validates
/// its reads against the already initialized prefix, including captured code.
pub(super) fn plan_journals(
    index: &InitializerIndex,
    selected: &BTreeMap<Name, &IrDecl>,
    limits: IrExecutionLimits,
) -> Result<InitializationPlan, IrExecutionError> {
    let reads = initializer_reads(index, selected, limits)?;
    let mut ready = BTreeSet::new();
    let mut result = InitializationPlan::default();
    for (name, initializer) in &index.journal {
        let dependencies = reads
            .get(name)
            .ok_or_else(|| IrExecutionError::MissingDeclaration(name.clone()))?;
        if !dependencies.is_subset(&ready) {
            return Err(contract(
                name,
                "module initializer reads a global before its journal entry",
            ));
        }
        if let Some(initializer) = initializer {
            result.push_global(InitializedGlobal {
                declaration: name.clone(),
                initializer: initializer.clone(),
            });
            ready.insert(name.clone());
        } else {
            result.steps.push(InitializationStep {
                declaration: name.clone(),
                initializer: name.clone(),
                global_slot: None,
            });
        }
    }
    Ok(result)
}

fn initializer_reads(
    index: &InitializerIndex,
    selected: &BTreeMap<Name, &IrDecl>,
    limits: IrExecutionLimits,
) -> Result<BTreeMap<Name, BTreeSet<Name>>, IrExecutionError> {
    let mut work = 0u64;
    let edges: BTreeMap<_, Vec<_>> = selected
        .iter()
        // Global declarations are replaced by generated getters. Their
        // placeholder bodies are neither executed nor dependency sources.
        .filter(|(name, _)| !index.named.contains_key(*name))
        .map(|(name, declaration)| {
            (
                name.clone(),
                declaration.callees().into_iter().cloned().collect(),
            )
        })
        .collect();
    let mut result = BTreeMap::new();
    for (name, initializer) in &index.journal {
        if !selected.contains_key(name) {
            continue;
        }
        let mut pending = vec![initializer.as_ref().unwrap_or(name).clone()];
        let mut seen = BTreeSet::new();
        let mut reads = BTreeSet::new();
        while let Some(name) = pending.pop() {
            work = work.saturating_add(1);
            if work > limits.ir.max_work {
                return Err(IrExecutionError::Limit("initializer dependency graph"));
            }
            if !seen.insert(name.clone()) {
                continue;
            }
            if index.named.contains_key(&name) {
                reads.insert(name);
                continue;
            }
            if let Some(callees) = edges.get(&name) {
                work = work.saturating_add(callees.len() as u64);
                if work > limits.ir.max_work {
                    return Err(IrExecutionError::Limit("initializer dependency graph"));
                }
                for callee in callees {
                    pending.push(callee.clone());
                }
            }
        }
        result.insert(name.clone(), reads);
    }
    Ok(result)
}

/// The generated wrapper owns this envelope. User values occupy its children
/// and can never impersonate an outer success or failure tag.
pub(super) fn finish(
    outcome: Outcome<VmExit>,
    plan: &InitializationPlan,
) -> (Outcome<VmExit>, Option<IrInitializationFailure>) {
    let Outcome::Complete(VmExit::Returned(mut completed)) = outcome else {
        return (outcome, None);
    };
    let bad_envelope = || {
        (
            Outcome::InternalFault(InternalFault::new(
                "IMPORTED-IR-INITIALIZATION-ENVELOPE",
                "generated initializer wrapper returned an invalid private envelope",
            )),
            None,
        )
    };
    let value = &completed.value;
    if value.is_scalar() {
        return bad_envelope();
    }
    let tag = value.header().tag;
    if tag == 0 && value.header().other == 1 {
        let Some(result) = value.try_ctor_child(0) else {
            return bad_envelope();
        };
        completed.value = result;
        return (Outcome::Complete(VmExit::Returned(completed)), None);
    }
    if !matches!(tag, 1 | 2) || value.header().other != 2 {
        return bad_envelope();
    }
    let Some(slot) = value
        .try_ctor_child(0)
        .and_then(|slot| crate::nat_decimal(&slot))
        .and_then(|slot| slot.parse::<usize>().ok())
    else {
        return bad_envelope();
    };
    let Some(global) = plan.steps.get(slot) else {
        return bad_envelope();
    };
    let Some(result) = value.try_ctor_child(1) else {
        return bad_envelope();
    };
    let malformed = tag == 2;
    let failure = IrInitializationFailure {
        declaration: global.declaration.clone(),
        initializer: global.initializer.clone(),
        result,
        malformed,
    };
    let refusal = VmRefusal::Initialization {
        initializer: global.initializer.to_display_string(),
        malformed_result: malformed,
    };
    (
        Outcome::Complete(VmExit::Refused {
            refusal,
            usage: completed.usage,
        }),
        Some(failure),
    )
}

#[cfg(test)]
mod tests;
