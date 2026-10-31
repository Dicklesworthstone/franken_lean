//! Registered imported macros over caller-supplied native Syntax.
//!
//! Registration order comes from the caller's checked import replay, never a
//! sorted module inventory. Scoped registrations remain inactive until an
//! explicit activation produces an immutable successor. This bounded embedding
//! door does not install parser descriptions or execute module initializers.
use super::{
    CompiledMacro, MacroContext, MacroExecutionError, MacroInvocation, MacroLimits, MacroResult,
    MacroState, StateBudget, compile, conversion_outcome, inject_state,
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
use fln_vm::macro_native::MacroLookup;
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
    Compile {
        module: Name,
        declaration: Name,
        error: Box<MacroExecutionError>,
    },
}

impl MacroRegistrationError {
    pub fn is_resource(&self) -> bool {
        match self {
            Self::Limit(_) => true,
            Self::Decode { error, .. } => error.is_resource(),
            Self::Compile { error, .. } => {
                matches!(error.as_ref(), MacroExecutionError::Compile(error) if error.is_resource())
            }
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

#[derive(Debug, Clone)]
struct RegisteredMacro {
    module: Name,
    declaration: Name,
    compiled: Arc<CompiledMacro>,
}

type CandidateTable = BTreeMap<Name, Arc<[RegisteredMacro]>>;

/// Prepared global and scoped registrations. Every candidate, including inactive
/// scoped candidates, has passed exact owner validation and the ordinary
/// census-authorized imported-IR compiler. Clones share code and candidate chains.
#[derive(Debug, Clone)]
pub struct RegisteredMacros {
    candidates: Arc<CandidateTable>,
    scoped: Arc<BTreeMap<Name, CandidateTable>>,
    active_scopes: BTreeSet<Name>,
    /// Exact checked owners retained for binding an embedding registry to a
    /// later source-checking engine. Scope activation shares this provenance.
    owners: Arc<BTreeMap<Name, (Name, ConstantInfo)>>,
}

fn dispatch_order(table: BTreeMap<Name, Vec<RegisteredMacro>>) -> CandidateTable {
    table
        .into_iter()
        .map(|(kind, mut entries)| {
            entries.reverse();
            (kind, Arc::from(entries))
        })
        .collect()
}

/// Owned invocation state and borrowed inputs for one registered expansion.
///
/// Lookup authority is supplied for this invocation only. Registries and their
/// scoped successors retain no provider; legacy entry points supply `None`.
pub struct MacroDispatchInvocation<'a> {
    pub source: &'a SourceText,
    pub context: &'a MacroContext,
    pub state: MacroState,
    pub lookup: Option<&'a dyn MacroLookup>,
}

struct ExpansionContext<'a> {
    source: &'a SourceText,
    context: &'a MacroContext,
    lookup: Option<&'a dyn MacroLookup>,
    cancellation: Option<&'a dyn CancellationProbe>,
}

impl RegisteredMacros {
    /// Prepare a supplied registration subset in actual dependency-first import
    /// order. Dependencies absent from this subset contribute no registrations;
    /// dependencies present in it must precede their consumers. This does not
    /// claim that the supplied subset is the complete environment macro table.
    ///
    /// Entries within a module retain the pin's stored order, with later
    /// registrations tried first. Unknown extension families remain uninterpreted.
    /// Scoped entries are checked and compiled too, but remain inactive until
    /// [`Self::activate_scoped`] is called with their exact namespace.
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
        let mut scoped: BTreeMap<Name, BTreeMap<Name, Vec<RegisteredMacro>>> = BTreeMap::new();
        let mut compiled: BTreeMap<Name, (Name, ConstantInfo, Arc<CompiledMacro>)> =
            BTreeMap::new();
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
                    if let Some((previous_module, _, callable)) = compiled.get(&row.declaration) {
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
                                    error: Box::new(error),
                                }
                            })?,
                        );
                        compiled.insert(
                            row.declaration.clone(),
                            (module.clone(), (**owner).clone(), Arc::clone(&callable)),
                        );
                        callable
                    };
                let table = match row.scope {
                    Some(namespace) => scoped.entry(namespace).or_default(),
                    None => &mut candidates,
                };
                let chain = table.entry(row.key).or_default();
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
        Ok(Self {
            candidates: Arc::new(dispatch_order(candidates)),
            scoped: Arc::new(
                scoped
                    .into_iter()
                    .map(|(namespace, entries)| (namespace, dispatch_order(entries)))
                    .collect(),
            ),
            active_scopes: BTreeSet::new(),
            owners: Arc::new(
                compiled
                    .into_iter()
                    .map(|(declaration, (module, owner, _))| (declaration, (module, owner)))
                    .collect(),
            ),
        })
    }

    /// A prepared registry is not transferable authority. An Engine source
    /// invocation must still have imported each owner module and retain its
    /// exact checked declaration, including inactive scoped registrations.
    pub(crate) fn validate_source_engine(
        &self,
        engine: &crate::Engine,
    ) -> Result<(), MacroRegistrationError> {
        for (declaration, (module, owner)) in self.owners.iter() {
            let reason = if !engine.imported_modules().contains(module) {
                Some("macro module is not an admitted import of the source engine")
            } else if engine.environment().find(declaration) != Some(owner) {
                Some("source engine declaration differs from the checked macro owner")
            } else {
                None
            };
            if let Some(reason) = reason {
                return Err(MacroRegistrationError::Owner {
                    module: module.clone(),
                    declaration: declaration.clone(),
                    reason,
                });
            }
        }
        Ok(())
    }

    /// Activate exactly one namespace in an immutable successor, following
    /// `ScopedEnvExtension.activateScoped` at the pin. Later activations take
    /// precedence over earlier ones; each namespace retains its reverse import
    /// and entry order. Reopening an active namespace does not reorder it.
    ///
    /// Retain the original registry to leave a lexical scope or roll back an
    /// alternative. Neither a successful activation nor an allocation refusal
    /// changes it. Unknown namespaces are no-ops: this prepared registry cannot
    /// acquire additional registrations after activation.
    pub fn activate_scoped(&self, namespace: &Name) -> Result<Self, MacroRegistrationError> {
        if self.active_scopes.contains(namespace) {
            return Ok(self.clone());
        }
        let Some(entries) = self.scoped.get(namespace) else {
            return Ok(self.clone());
        };
        let mut candidates = self.candidates.as_ref().clone();
        for (kind, additions) in entries {
            let previous = self.candidates.get(kind);
            let count = additions
                .len()
                .checked_add(previous.map_or(0, |chain| chain.len()))
                .ok_or(MacroRegistrationError::Limit("scoped candidates"))?;
            let mut chain = Vec::new();
            chain
                .try_reserve_exact(count)
                .map_err(|_| MacroRegistrationError::Limit("scoped candidate allocation"))?;
            chain.extend(additions.iter().cloned());
            if let Some(previous) = previous {
                chain.extend(previous.iter().cloned());
            }
            candidates.insert(kind.clone(), Arc::from(chain));
        }
        let mut active_scopes = self.active_scopes.clone();
        active_scopes.insert(namespace.clone());
        Ok(Self {
            candidates: Arc::new(candidates),
            scoped: Arc::clone(&self.scoped),
            active_scopes,
            owners: Arc::clone(&self.owners),
        })
    }

    /// Registered declarations in the exact order this syntax kind will try.
    pub fn declarations(&self, kind: &Name) -> impl Iterator<Item = &Name> {
        self.candidates
            .get(kind)
            .into_iter()
            .flat_map(|chain| chain.iter())
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
        self.expand_root_with_context(
            input,
            MacroDispatchInvocation {
                source,
                context,
                state,
                lookup: None,
            },
            limits,
            cancellation,
        )
    }

    /// Expand one root with optional invocation-local native lookup authority.
    /// The same provider is available to every candidate in the chain; state
    /// and the cumulative work allowance follow the ordinary dispatch rules.
    pub fn expand_root_with_context(
        &self,
        input: &Syntax,
        invocation: MacroDispatchInvocation<'_>,
        limits: MacroDispatchLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> MacroDispatch {
        let MacroDispatchInvocation {
            source,
            context,
            state,
            lookup,
        } = invocation;
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
            ExpansionContext {
                source,
                context,
                lookup,
                cancellation,
            },
            state,
            limits,
            &mut report,
        );
        report
    }

    /// The pin's default `Init.Meta.Defs.expandMacros` traversal: expand a node
    /// at its root first, revisit a successful result, otherwise visit children
    /// left to right. Leaves and `Lean.Parser.Term.byTactic` are left alone.
    /// Tactic alternatives require the tactic evaluator's backtracking semantics.
    ///
    /// This expands only this registry's supplied registration subset. It does
    /// not install parsers or claim that every macro in an environment is known.
    /// Attempts and VM steps are shared across the whole tree. Recursion depth
    /// comes from `context`; `max_visits` additionally bounds repeated results
    /// and macro-free trees. Stops publish neither a partial tree nor state.
    /// `generation` bounds the sum of converted macro results, including results
    /// later discarded, so expanding wide sibling trees cannot retain an
    /// unbounded collection of individually bounded results.
    pub fn expand_tree(
        &self,
        input: &Syntax,
        source: &SourceText,
        context: &MacroContext,
        state: MacroState,
        limits: MacroTreeLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> MacroTreeDispatch {
        self.expand_tree_with_context(
            input,
            MacroDispatchInvocation {
                source,
                context,
                state,
                lookup: None,
            },
            limits,
            cancellation,
        )
    }

    /// Expand a complete tree using one explicit native lookup snapshot.
    /// Authority follows every candidate and revisited result without being
    /// installed in the registry or copied into a Syntax or Macro.Context value.
    pub fn expand_tree_with_context(
        &self,
        input: &Syntax,
        invocation: MacroDispatchInvocation<'_>,
        limits: MacroTreeLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> MacroTreeDispatch {
        let MacroDispatchInvocation {
            source,
            context,
            state,
            lookup,
        } = invocation;
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
        let outcome = self.expand_tree_impl(
            input,
            ExpansionContext {
                source,
                context,
                lookup,
                cancellation,
            },
            state,
            limits,
            &mut report,
        );
        MacroTreeDispatch {
            outcome,
            attempts: report.attempts,
            completed_vm_usage: report.completed_vm_usage,
        }
    }

    fn expand_tree_impl(
        &self,
        input: &Syntax,
        invocation: ExpansionContext<'_>,
        mut state: MacroState,
        limits: MacroTreeLimits,
        report: &mut MacroDispatch,
    ) -> Outcome<Result<MacroTreeResult, MacroExecutionError>> {
        let ExpansionContext {
            source,
            context,
            lookup,
            cancellation,
        } = invocation;
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Outcome::Inconclusive(Inconclusive::cancelled("before macro tree conversion"));
        }
        // Validate and bound the complete input before cloning it, including a
        // macro-free tree. A root-only invocation would never inspect its leaves.
        if let Err(error) = super::syntax::inject(input, source, limits.dispatch.execution.syntax) {
            return conversion_outcome(error).map_complete(|result| {
                result.map(|_| unreachable!("failed input conversion cannot produce a tree"))
            });
        }
        enum Task {
            Visit(Syntax, u64),
            Finish(Syntax, usize),
        }
        let mut tasks = vec![Task::Visit(input.clone(), context.current_recursion_depth)];
        let mut built = Vec::new();
        let mut visits = 0u64;
        let mut generated_nodes = 0usize;
        let mut generated_bytes = 0usize;
        let tactic = Name::from_components(["Lean", "Parser", "Term", "byTactic"]);
        while let Some(task) = tasks.pop() {
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Outcome::Inconclusive(Inconclusive::cancelled("macro tree traversal"));
            }
            match task {
                Task::Finish(mut parent, start) => {
                    let Syntax::Node { args, .. } = &mut parent else {
                        unreachable!("only nodes have a finish task")
                    };
                    *args = built.split_off(start);
                    built.push(parent);
                }
                Task::Visit(mut syntax, depth) => {
                    if visits >= limits.max_visits {
                        return stopped(
                            "macro tree visits",
                            limits.max_visits,
                            visits.saturating_add(1),
                        );
                    }
                    visits += 1;
                    let Some(kind) = syntax.kind() else {
                        built.push(syntax);
                        continue;
                    };
                    if *kind == tactic {
                        built.push(syntax);
                        continue;
                    }
                    let mut current = context.clone();
                    current.current_recursion_depth = depth;
                    match self.expand(
                        &syntax,
                        ExpansionContext {
                            source,
                            context: &current,
                            lookup,
                            cancellation,
                        },
                        state,
                        limits.dispatch,
                        report,
                    ) {
                        Outcome::Complete(Ok(RegisteredExpansion::Expanded {
                            syntax: next,
                            state: successor,
                            ..
                        })) => {
                            let usage = match super::syntax::inject_counted(
                                &next,
                                source,
                                limits.dispatch.execution.syntax,
                            ) {
                                Ok((_, usage)) => usage,
                                Err(error) => {
                                    return conversion_outcome(error).map_complete(|result| {
                                        result.map(|_| {
                                            unreachable!(
                                                "failed generated conversion cannot produce a tree"
                                            )
                                        })
                                    });
                                }
                            };
                            generated_nodes = generated_nodes.saturating_add(usage.max_nodes);
                            generated_bytes = generated_bytes.saturating_add(usage.max_bytes);
                            if generated_nodes > limits.generation.max_nodes {
                                return stopped(
                                    "macro tree generated nodes",
                                    limits.generation.max_nodes as u64,
                                    generated_nodes as u64,
                                );
                            }
                            if generated_bytes > limits.generation.max_bytes {
                                return Outcome::Inconclusive(
                                    Inconclusive::resource(ResourceUsage {
                                        reason: ResourceReason::Memory {
                                            limit_bytes: limits.generation.max_bytes as u64,
                                        },
                                        allowed: limits.generation.max_bytes as u64,
                                        observed: generated_bytes as u64,
                                    })
                                    .with_progress("macro tree generated bytes"),
                                );
                            }
                            state = successor;
                            tasks.push(Task::Visit(next, depth));
                            continue;
                        }
                        Outcome::Complete(Ok(RegisteredExpansion::Unsupported {
                            state: successor,
                        })) => {
                            state = successor;
                        }
                        Outcome::Complete(Ok(RegisteredExpansion::Error {
                            module,
                            declaration,
                            reference,
                            message,
                            state,
                        })) => {
                            return Outcome::Complete(Ok(MacroTreeResult::Error {
                                module,
                                declaration,
                                reference,
                                message,
                                state,
                            }));
                        }
                        Outcome::Complete(Err(error)) => return Outcome::Complete(Err(error)),
                        Outcome::Inconclusive(reason) => return Outcome::Inconclusive(reason),
                        Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
                    }
                    if depth >= context.max_recursion_depth {
                        return Outcome::Inconclusive(
                            Inconclusive::resource(ResourceUsage {
                                reason: ResourceReason::RecursionDepth {
                                    limit: context.max_recursion_depth,
                                },
                                allowed: context.max_recursion_depth,
                                observed: depth.saturating_add(1),
                            })
                            .with_progress("macro tree children"),
                        );
                    }
                    let Syntax::Node { args, .. } = &mut syntax else {
                        unreachable!("Syntax::kind is present only on nodes")
                    };
                    if tasks.try_reserve(args.len().saturating_add(1)).is_err()
                        || built.try_reserve(args.len().saturating_add(1)).is_err()
                    {
                        return Outcome::Inconclusive(Inconclusive::dependency_unavailable(
                            "host allocation for macro tree traversal",
                        ));
                    }
                    let children = std::mem::take(args);
                    tasks.push(Task::Finish(syntax, built.len()));
                    tasks.extend(
                        children
                            .into_iter()
                            .rev()
                            .map(|child| Task::Visit(child, depth + 1)),
                    );
                }
            }
        }
        let syntax = built.pop().expect("one completed root");
        // Individual VM results are bounded already, but siblings together can
        // exceed that ceiling. Validate the assembled result before publishing.
        if let Err(error) = super::syntax::inject(&syntax, source, limits.dispatch.execution.syntax)
        {
            return conversion_outcome(error).map_complete(|result| {
                result.map(|_| unreachable!("failed output conversion cannot produce a tree"))
            });
        }
        Outcome::Complete(Ok(MacroTreeResult::Expanded { syntax, state }))
    }

    fn expand(
        &self,
        input: &Syntax,
        invocation: ExpansionContext<'_>,
        mut state: MacroState,
        limits: MacroDispatchLimits,
        report: &mut MacroDispatch,
    ) -> Outcome<Result<RegisteredExpansion, MacroExecutionError>> {
        let ExpansionContext {
            source,
            context,
            lookup,
            cancellation,
        } = invocation;
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
        for candidate in self
            .candidates
            .get(&kind)
            .into_iter()
            .flat_map(|chain| chain.iter())
        {
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
            let result = candidate.compiled.execute_with_context(
                input,
                MacroInvocation {
                    source,
                    context: &current,
                    state: &state,
                    lookup,
                },
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

#[derive(Debug, Clone, Copy)]
pub struct MacroTreeLimits {
    pub dispatch: MacroDispatchLimits,
    pub max_visits: u64,
    pub generation: super::SyntaxLimits,
}

impl Default for MacroTreeLimits {
    fn default() -> Self {
        Self {
            dispatch: MacroDispatchLimits::default(),
            max_visits: 1_000_000,
            generation: super::SyntaxLimits::default(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MacroTreeResult {
    Expanded {
        syntax: Syntax,
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
pub struct MacroTreeDispatch {
    pub outcome: Outcome<Result<MacroTreeResult, MacroExecutionError>>,
    pub attempts: Vec<MacroAttempt>,
    pub completed_vm_usage: ExecutionUsage,
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
