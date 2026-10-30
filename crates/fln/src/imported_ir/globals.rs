//! Preparation and result handling for explicitly selected initialized globals.
//!
//! This is a closed executable dependency graph, not module startup. Every
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

#[derive(Clone, Debug, Default)]
pub(super) struct InitializationPlan {
    pub globals: Vec<InitializedGlobal>,
}

pub(super) struct InitializerIndex {
    pub named: BTreeMap<Name, Name>,
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
) -> Result<(), IrExecutionError> {
    // A standalone action in another supplied module can mutate this global
    // even when no function from that module is in the static call closure.
    // Without a complete startup interpreter, never silently omit that action.
    if index.has_standalone_actions {
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
    if native_row(initializer).is_some()
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
    let mut work = 0u64;
    let edges: BTreeMap<_, Vec<_>> = selected
        .iter()
        // Global declarations are replaced by generated getters. Their
        // placeholder bodies are neither executed nor dependency sources.
        .filter(|(name, _)| !globals.contains_key(*name))
        .map(|(name, declaration)| {
            (
                name.clone(),
                declaration.callees().into_iter().cloned().collect(),
            )
        })
        .collect();
    let mut dependencies = BTreeMap::new();
    let mut dependents: BTreeMap<Name, BTreeSet<Name>> = BTreeMap::new();
    for (global, initializer) in &globals {
        let mut pending = vec![initializer.clone()];
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
            if globals.contains_key(&name) {
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
        for dependency in &reads {
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
        result.globals.push(InitializedGlobal {
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
    let Some(global) = plan.globals.get(slot) else {
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
