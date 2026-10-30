//! Registered imported macros over caller-supplied native Syntax.
//!
//! Registration order comes from the caller's checked import replay, never a
//! sorted module inventory. This bounded embedding door does not install parser
//! descriptions, activate scoped namespaces, or execute module initializers.
use super::{
    CompiledMacro, MacroContext, MacroExecutionError, MacroLimits, MacroResult, MacroState,
    StateBudget, compile, conversion_outcome, inject_state,
};
use crate::imported_ir::{IrExecutionLimits, ReferenceFunction, VerifiedPartition};
use crate::{CheckedOleanModule, Environment};
use fln_core::diag::{ResourceReason, StructuralUnit};
use fln_core::expr::ExprNode;
use fln_core::name::Name;
use fln_core::outcome::{Inconclusive, Outcome, ResourceUsage};
use fln_env::constants::ConstantInfo;
use fln_olean::ir::IrModule;
use fln_olean::region::OpaqueExtensionBlock;
use fln_olean::source_extensions::{DecodeError, DecodeLimits, macros};
use fln_syntax::source::SourceText;
use fln_syntax::tree::Syntax;
use fln_vm::interpreter::{CancellationProbe, ExecutionUsage};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

/// A checked module and its complete captured extension journal. For a
/// module-system artifact, capture the final private part with its public and
/// server dependencies, rather than concatenating cumulative companion rows.
///
/// The caller supplies the same artifacts it checked. Every selected owner is
/// additionally compared with its exact declaration in `admitted`; a matching
/// display name or ambient declaration alone is insufficient.
pub struct MacroRegistrationModule<'a> {
    pub checked: &'a CheckedOleanModule,
    pub extensions: &'a [OpaqueExtensionBlock],
}

#[derive(Debug, Clone, Copy)]
pub struct MacroRegistryLimits {
    pub max_modules: usize,
    pub max_declarations: usize,
    pub max_macros: usize,
    pub metadata: DecodeLimits,
    pub compilation: IrExecutionLimits,
}

impl Default for MacroRegistryLimits {
    fn default() -> Self {
        Self {
            max_modules: 4096,
            max_declarations: 1 << 20,
            max_macros: 256,
            metadata: DecodeLimits::default(),
            compilation: IrExecutionLimits::default(),
        }
    }
}

#[derive(Debug)]
pub enum MacroRegistrationError {
    Limit(&'static str),
    DuplicateModule(Name),
    ImportOrder {
        module: Name,
        dependency: Name,
    },
    MissingPrivateJournal(Name),
    Decode {
        module: Name,
        error: DecodeError,
    },
    Owner {
        module: Name,
        declaration: Name,
        reason: &'static str,
    },
    Scoped {
        module: Name,
        declaration: Name,
        namespace: Name,
    },
    Compile {
        module: Name,
        declaration: Name,
        error: MacroExecutionError,
    },
}

impl MacroRegistrationError {
    pub fn is_resource(&self) -> bool {
        match self {
            Self::Limit(_) => true,
            Self::Decode { error, .. } => error.is_resource(),
            Self::Compile {
                error: MacroExecutionError::Compile(error),
                ..
            } => error.is_resource(),
            _ => false,
        }
    }
}

impl fmt::Display for MacroRegistrationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Limit(resource) => write!(f, "registered macro preparation exhausted {resource}"),
            Self::DuplicateModule(module) => {
                write!(f, "duplicate macro module {}", module.to_display_string())
            }
            Self::ImportOrder { module, dependency } => write!(
                f,
                "macro module {} precedes dependency {}",
                module.to_display_string(),
                dependency.to_display_string()
            ),
            Self::MissingPrivateJournal(module) => write!(
                f,
                "macro module {} requires its complete private journal",
                module.to_display_string()
            ),
            Self::Decode { module, error } => write!(
                f,
                "macro metadata in {}: {error}",
                module.to_display_string()
            ),
            Self::Owner {
                module,
                declaration,
                reason,
            } => write!(
                f,
                "macro owner {} in {}: {reason}",
                declaration.to_display_string(),
                module.to_display_string()
            ),
            Self::Scoped {
                module,
                declaration,
                namespace,
            } => write!(
                f,
                "macro {} in {} requires unsupported scope activation {}",
                declaration.to_display_string(),
                module.to_display_string(),
                namespace.to_display_string()
            ),
            Self::Compile {
                module,
                declaration,
                error,
            } => write!(
                f,
                "registered macro {} in {}: {error}",
                declaration.to_display_string(),
                module.to_display_string()
            ),
        }
    }
}

impl std::error::Error for MacroRegistrationError {}

#[derive(Debug)]
struct RegisteredMacro {
    module: Name,
    declaration: Name,
    compiled: Arc<CompiledMacro>,
}

/// Prepared global registrations. Every candidate has passed both exact owner
/// validation and the ordinary census-authorized imported-IR compiler.
#[derive(Debug)]
pub struct RegisteredMacros {
    candidates: BTreeMap<Name, Vec<RegisteredMacro>>,
}

impl RegisteredMacros {
    /// Prepare a supplied registration subset in actual dependency-first import
    /// order. Dependencies absent from this subset contribute no registrations;
    /// dependencies present in it must precede their consumers. This does not
    /// claim that the supplied subset is the complete environment macro table.
    ///
    /// Entries within a module retain the pin's stored order, with later
    /// registrations tried first. Unknown extension families remain uninterpreted.
    /// Scoped entries are a typed refusal until an explicit activation API exists.
    pub fn prepare(
        ordered_modules: &[MacroRegistrationModule<'_>],
        admitted: &Environment,
        code: &[IrModule],
        partition: &VerifiedPartition,
        user_declarations: &BTreeSet<Name>,
        limits: MacroRegistryLimits,
    ) -> Result<Self, MacroRegistrationError> {
        if ordered_modules.len() > limits.max_modules {
            return Err(MacroRegistrationError::Limit("modules"));
        }
        let mut positions = BTreeMap::new();
        let mut declaration_count = 0usize;
        for (index, input) in ordered_modules.iter().enumerate() {
            let checked = input.checked;
            if positions.insert(&checked.name, index).is_some() {
                return Err(MacroRegistrationError::DuplicateModule(
                    checked.name.clone(),
                ));
            }
            declaration_count = declaration_count
                .checked_add(checked.decoded.constants.len())
                .filter(|count| *count <= limits.max_declarations)
                .ok_or(MacroRegistrationError::Limit("owner declarations"))?;
            if checked.decoded.module.is_module && !checked.decoded.companion_parts_loaded {
                return Err(MacroRegistrationError::MissingPrivateJournal(
                    checked.name.clone(),
                ));
            }
        }
        for (index, input) in ordered_modules.iter().enumerate() {
            for dependency in &input.checked.decoded.module.imports {
                if positions
                    .get(&dependency.module)
                    .is_some_and(|position| *position >= index)
                {
                    return Err(MacroRegistrationError::ImportOrder {
                        module: input.checked.name.clone(),
                        dependency: dependency.module.clone(),
                    });
                }
            }
        }
        let mut decoder = macros::Decoder::new(limits.metadata);
        let mut candidates: BTreeMap<Name, Vec<RegisteredMacro>> = BTreeMap::new();
        let mut compiled: BTreeMap<Name, (Name, Arc<CompiledMacro>)> = BTreeMap::new();
        for input in ordered_modules {
            let module = &input.checked.name;
            let rows = decoder.decode(input.extensions).map_err(|error| {
                MacroRegistrationError::Decode {
                    module: module.clone(),
                    error,
                }
            })?;
            let mut owners = BTreeMap::new();
            for declaration in &input.checked.decoded.constants {
                if owners.insert(declaration.name(), declaration).is_some() {
                    return Err(MacroRegistrationError::Owner {
                        module: module.clone(),
                        declaration: declaration.name().clone(),
                        reason: "checked module repeats a declaration owner",
                    });
                }
            }
            for row in rows {
                if let Some(namespace) = row.scope {
                    return Err(MacroRegistrationError::Scoped {
                        module: module.clone(),
                        declaration: row.declaration,
                        namespace,
                    });
                }
                let error = |reason| MacroRegistrationError::Owner {
                    module: module.clone(),
                    declaration: row.declaration.clone(),
                    reason,
                };
                let owner = owners
                    .get(&row.declaration)
                    .ok_or_else(|| error("registration is not owned by this checked module"))?;
                if admitted.find(&row.declaration) != Some(*owner) {
                    return Err(error(
                        "active admitted declaration differs from checked owner",
                    ));
                }
                if !matches!(owner, ConstantInfo::Defn(_) | ConstantInfo::Opaque(_))
                    || !matches!(owner.constant_val().type_.node(), ExprNode::Const { name, levels }
                        if *name == Name::from_components(["Lean", "Macro"]) && levels.is_empty())
                {
                    return Err(error(
                        "registered owner is not an executable declaration of exact type Lean.Macro",
                    ));
                }
                let callable =
                    if let Some((previous_module, callable)) = compiled.get(&row.declaration) {
                        if previous_module != module {
                            return Err(error("registration has multiple checked module owners"));
                        }
                        Arc::clone(callable)
                    } else {
                        if compiled.len() >= limits.max_macros {
                            return Err(MacroRegistrationError::Limit("compiled macros"));
                        }
                        let callable = Arc::new(
                            compile(
                                code,
                                &row.declaration,
                                partition,
                                user_declarations,
                                limits.compilation,
                            )
                            .map_err(|error| {
                                MacroRegistrationError::Compile {
                                    module: module.clone(),
                                    declaration: row.declaration.clone(),
                                    error,
                                }
                            })?,
                        );
                        compiled.insert(
                            row.declaration.clone(),
                            (module.clone(), Arc::clone(&callable)),
                        );
                        callable
                    };
                let chain = candidates.entry(row.key).or_default();
                chain
                    .try_reserve(1)
                    .map_err(|_| MacroRegistrationError::Limit("candidate allocation"))?;
                chain.push(RegisteredMacro {
                    module: module.clone(),
                    declaration: row.declaration,
                    compiled: callable,
                });
            }
        }
        for chain in candidates.values_mut() {
            chain.reverse();
        }
        Ok(Self { candidates })
    }

    /// Registered declarations in the exact order this syntax kind will try.
    pub fn declarations(&self, kind: &Name) -> impl Iterator<Item = &Name> {
        self.candidates
            .get(kind)
            .into_iter()
            .flatten()
            .map(|entry| &entry.declaration)
    }

    /// Expand one root, without recursively expanding its children or result.
    /// Every attempt gets a fresh scope; unsupported syntax retains the returned
    /// state and tries the next registration. A diagnostic stops the chain.
    ///
    /// `max_steps` is one cumulative allowance across candidates. Stack and
    /// arithmetic-result ceilings remain per invocation. Incomplete execution
    /// publishes no syntax or successor state, and never falls back to an older
    /// registration. All state is invocation-local, so the registry is reusable.
    pub fn expand_root(
        &self,
        input: &Syntax,
        source: &SourceText,
        context: &MacroContext,
        state: MacroState,
        limits: MacroDispatchLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> MacroDispatch {
        let mut report = MacroDispatch {
            outcome: Outcome::Complete(Ok(RegisteredExpansion::Unsupported {
                state: MacroState::default(),
            })),
            attempts: Vec::new(),
            completed_vm_usage: ExecutionUsage {
                steps: 0,
                system_polls: 0,
                peak_stack_depth: 0,
            },
        };
        report.outcome = self.expand(
            input,
            source,
            context,
            state,
            limits,
            cancellation,
            &mut report,
        );
        report
    }

    fn expand(
        &self,
        input: &Syntax,
        source: &SourceText,
        context: &MacroContext,
        mut state: MacroState,
        limits: MacroDispatchLimits,
        cancellation: Option<&dyn CancellationProbe>,
        report: &mut MacroDispatch,
    ) -> Outcome<Result<RegisteredExpansion, MacroExecutionError>> {
        let kind = match input {
            Syntax::Node { kind, .. } => kind.clone(),
            Syntax::Ident { .. } => Name::from_components(["ident"]),
            Syntax::Missing => Name::from_components(["missing"]),
            Syntax::Atom { val, .. } => {
                let allowed = limits.execution.syntax.max_bytes as u64;
                if val.len() as u64 > allowed {
                    return Outcome::Inconclusive(
                        Inconclusive::resource(ResourceUsage {
                            reason: ResourceReason::Memory {
                                limit_bytes: allowed,
                            },
                            allowed,
                            observed: val.len() as u64,
                        })
                        .with_progress("registered macro atom kind"),
                    );
                }
                Name::str(Name::anonymous(), val)
            }
        };
        for candidate in self.candidates.get(&kind).into_iter().flatten() {
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Outcome::Inconclusive(Inconclusive::cancelled(
                    "registered macro before candidate",
                ));
            }
            if report.attempts.len() as u64 >= limits.max_attempts {
                return stopped(
                    "registered macro attempts",
                    limits.max_attempts,
                    (report.attempts.len() as u64).saturating_add(1),
                );
            }
            if report.attempts.try_reserve(1).is_err() {
                return Outcome::Inconclusive(Inconclusive::dependency_unavailable(
                    "host allocation for macro attempts",
                ));
            }
            let fresh_scope = state.macro_scope;
            let Some(next_scope) = fresh_scope.checked_add(1) else {
                return stopped("registered macro scope counter", u64::MAX - 1, u64::MAX);
            };
            state.macro_scope = next_scope;
            let mut current = context.clone();
            current.current_macro_scope = fresh_scope;
            let mut execution = limits.execution;
            execution.vm.max_steps -= report.completed_vm_usage.steps;
            let result = candidate.compiled.execute(
                input,
                source,
                &current,
                &state,
                execution,
                cancellation,
            );
            if let Some(usage) = result.vm_usage {
                report.completed_vm_usage.steps += usage.steps;
                report.completed_vm_usage.system_polls += usage.system_polls;
                report.completed_vm_usage.peak_stack_depth = report
                    .completed_vm_usage
                    .peak_stack_depth
                    .max(usage.peak_stack_depth);
            }
            report.attempts.push(MacroAttempt {
                module: candidate.module.clone(),
                declaration: candidate.declaration.clone(),
                vm_usage: result.vm_usage,
                reference_functions: result.reference_functions,
                native_functions: result.native_functions,
            });
            match result.outcome {
                Outcome::Complete(Ok(MacroResult::Unsupported { state: next })) => state = next,
                Outcome::Complete(Ok(MacroResult::Expanded {
                    syntax,
                    state: mut next,
                })) => {
                    if next.expanded_macro_declarations.try_reserve(1).is_err() {
                        return Outcome::Inconclusive(Inconclusive::dependency_unavailable(
                            "host allocation for expanded macro declarations",
                        ));
                    }
                    next.expanded_macro_declarations
                        .insert(0, candidate.declaration.clone());
                    if let Err(error) =
                        inject_state(&next, &mut StateBudget::new(limits.execution.syntax))
                    {
                        return conversion_outcome(error).map_complete(|result| {
                            result.map(|_| unreachable!("conversion failure cannot expand syntax"))
                        });
                    }
                    return Outcome::Complete(Ok(RegisteredExpansion::Expanded {
                        module: candidate.module.clone(),
                        declaration: candidate.declaration.clone(),
                        syntax,
                        state: next,
                    }));
                }
                Outcome::Complete(Ok(MacroResult::Error {
                    reference,
                    message,
                    state,
                })) => {
                    return Outcome::Complete(Ok(RegisteredExpansion::Error {
                        module: candidate.module.clone(),
                        declaration: candidate.declaration.clone(),
                        reference,
                        message,
                        state,
                    }));
                }
                Outcome::Complete(Err(error)) => return Outcome::Complete(Err(error)),
                Outcome::Inconclusive(reason) => return Outcome::Inconclusive(reason),
                Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
            }
        }
        Outcome::Complete(Ok(RegisteredExpansion::Unsupported { state }))
    }
}

#[derive(Debug, Clone, Copy)]
pub struct MacroDispatchLimits {
    pub max_attempts: u64,
    pub execution: MacroLimits,
}

impl Default for MacroDispatchLimits {
    fn default() -> Self {
        Self {
            max_attempts: 4096,
            execution: MacroLimits::default(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RegisteredExpansion {
    Expanded {
        module: Name,
        declaration: Name,
        syntax: Syntax,
        state: MacroState,
    },
    Unsupported {
        state: MacroState,
    },
    Error {
        module: Name,
        declaration: Name,
        reference: Syntax,
        message: String,
        state: MacroState,
    },
}

#[derive(Debug)]
pub struct MacroAttempt {
    pub module: Name,
    pub declaration: Name,
    pub vm_usage: Option<ExecutionUsage>,
    /// The conservative linked closure, not a claim that every function ran.
    pub reference_functions: Vec<ReferenceFunction>,
    pub native_functions: Vec<String>,
}

#[derive(Debug)]
pub struct MacroDispatch {
    pub outcome: Outcome<Result<RegisteredExpansion, MacroExecutionError>>,
    pub attempts: Vec<MacroAttempt>,
    /// Sum/max over terminal invocations. An inconclusive invocation reports
    /// its stop usage in `outcome` and ends dispatch immediately.
    pub completed_vm_usage: ExecutionUsage,
}

fn stopped<T>(what: &'static str, allowed: u64, observed: u64) -> Outcome<T> {
    Outcome::Inconclusive(
        Inconclusive::resource(ResourceUsage {
            reason: ResourceReason::StructuralBudget {
                unit: StructuralUnit::ProducedNodes,
            },
            allowed,
            observed,
        })
        .with_progress(what),
    )
}

#[cfg(test)]
#[path = "registrations/tests.rs"]
mod tests;
