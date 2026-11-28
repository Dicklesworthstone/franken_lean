//! Native executable companions from a module's exact checked implementation.
//! This facet never interprets emitted `.olean` bytes as admission authority.
use super::*;
use crate::EngineExecutionLimits;
use crate::ir::{CompileError, CompileLimits, DefinitionCompileError};
use fln_olean::ir::IrModule;
use fln_olean::ir::write::{IrWriteError, IrWriteInput, IrWriteLimits, encode_ir};

#[derive(Debug)]
pub(super) struct CompilerInput {
    pub engine: Engine,
    pub options: KVMap,
    pub name: Name,
    pub is_module: bool,
    /// A checked native cache-bearing family owned by this implementation
    /// world. Inherited families are guarded by each definition's actual ABI
    /// and complete runtime preparation, rather than blocking unrelated code.
    pub owned_computed_family: Option<Name>,
    pub imports: Vec<OleanModuleImport>,
    pub constants: Vec<ConstantInfo>,
    pub public: Arc<ArtifactData>,
    pub private: Option<Arc<ArtifactData>>,
}

/// Each definition uses independent compiler/preparation bounds. The writer's
/// entry and node limits bound the complete IR, including helpers. Its container
/// budget covers IR plus all refreshed logical companions and compiler metadata.
#[derive(Debug, Clone, Copy)]
pub struct SourceModuleIrLimits {
    pub execution: EngineExecutionLimits,
    pub compiler: CompileLimits,
    pub writer: IrWriteLimits,
}

impl SourceModuleIrLimits {
    pub fn new(execution: EngineExecutionLimits) -> Self {
        Self {
            execution,
            compiler: CompileLimits::default(),
            writer: IrWriteLimits::default(),
        }
    }
}

#[derive(Debug)]
pub enum SourceModuleIrError {
    Limit {
        module: Name,
        resource: &'static str,
    },
    Unsupported {
        module: Name,
        declaration: Name,
        reason: &'static str,
    },
    Compile {
        module: Name,
        declaration: Name,
        error: Box<DefinitionCompileError>,
    },
    Encode {
        module: Name,
        error: IrWriteError,
    },
    Logical(SourceModuleBuildError),
}

impl std::fmt::Display for SourceModuleIrError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Limit { module, resource } => write!(
                f,
                "compiling module `{}` exhausted {resource}",
                module.to_display_string()
            ),
            Self::Unsupported {
                module,
                declaration,
                reason,
            } => write!(
                f,
                "compiling `{}` in module `{}`: {reason}",
                declaration.to_display_string(),
                module.to_display_string()
            ),
            Self::Compile {
                module,
                declaration,
                error,
            } => write!(
                f,
                "compiling `{}` in module `{}`: {error}",
                declaration.to_display_string(),
                module.to_display_string()
            ),
            Self::Encode { module, error } => write!(
                f,
                "encoding executable module `{}`: {error}",
                module.to_display_string()
            ),
            Self::Logical(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for SourceModuleIrError {}

impl SourceModuleIrError {
    pub fn disposition(&self) -> (&'static str, bool, u8) {
        match self {
            Self::Limit { .. } => ("resource", false, 3),
            Self::Unsupported { .. } => ("unsupported", false, 1),
            Self::Compile { error, .. } => match error.as_ref() {
                DefinitionCompileError::Engine(error) => crate::source_check::classify(error),
                DefinitionCompileError::Ir(error) => match error {
                    CompileError::Unsupported { .. } => ("unsupported", false, 1),
                    CompileError::Limit | CompileError::Allocation => ("resource", false, 3),
                    CompileError::Lowering(error) if error.is_resource_exhaustion() => {
                        ("resource", false, 3)
                    }
                    CompileError::Lowering(error) if error.is_internal_fault() => {
                        ("internal-fault", false, 4)
                    }
                    CompileError::Lowering(_) => ("unsupported", false, 1),
                    CompileError::Validation(error) if error.is_resource() => {
                        ("resource", false, 3)
                    }
                    CompileError::Invariant { .. } | CompileError::Validation(_) => {
                        ("internal-fault", false, 4)
                    }
                },
            },
            Self::Encode { error, .. } => match error {
                IrWriteError::Limit { .. }
                | IrWriteError::Write(OleanWriteError::Budget { .. }) => ("resource", false, 3),
                IrWriteError::Write(OleanWriteError::Unsupported { .. }) => {
                    ("unsupported", false, 1)
                }
                _ => ("internal-fault", false, 4),
            },
            Self::Logical(error) => error.disposition(),
        }
    }
}

/// The pin adds these logical constructions after scheduling an inductive's
/// executable declarations. Unlike recOn/casesOn, not all carry the auxiliary
/// recursor tag. A name, reducibility hint or eliminator tag cannot establish
/// that origin: reconstruct the complete definition from its checked family.
fn logical_inductive_auxiliary(
    input: &CompilerInput,
    constant: &ConstantInfo,
    limits: CompileLimits,
) -> Result<bool, CompileError> {
    use fln_core::name::LeafView;
    use fln_elab::inductive::auxiliaries::{
        AuxiliaryError, below_declaration, brec_on_declarations, cases_on_declaration,
        ctor_elim_declarations, no_confusion_declarations,
    };
    use fln_elab::records::RecordBudget;
    use fln_env::constants::{DefinitionSafety, ReducibilityHints};

    let ConstantInfo::Defn(definition) = constant else {
        return Ok(false);
    };
    let (family, kind) = match definition.base.name.leaf_view() {
        LeafView::Str(kind @ ("noConfusion" | "noConfusionType" | "ctorElimType")) => {
            (definition.base.name.parent(), kind)
        }
        LeafView::Str("go")
            if definition.base.name.parent().leaf_view() == LeafView::Str("brecOn") =>
        {
            (definition.base.name.parent().parent(), "brecOn.go")
        }
        _ => return Ok(false),
    };
    if definition.safety != DefinitionSafety::Safe || definition.hints != ReducibilityHints::Abbrev
    {
        return Ok(false);
    }
    let environment = input.engine.environment();
    let Some(ConstantInfo::Induct(inductive)) = environment.find(&family) else {
        return Ok(false);
    };
    let mut remaining = limits.max_work;
    let charge = |remaining: &mut u64, amount: usize| {
        *remaining = remaining
            .checked_sub(u64::try_from(amount).map_err(|_| CompileError::Limit)?)
            .ok_or(CompileError::Limit)?;
        Ok::<(), CompileError>(())
    };
    // Keep this omission profile aligned with the data layouts the standalone
    // compiler actually exports. Mutual, indexed and nested families retain
    // the ordinary compiler's explicit refusal until their ABI is supported.
    if CompilerData::from_inductive(
        inductive,
        |name| environment.find(name),
        |amount| charge(&mut remaining, amount),
    )?
    .is_none()
    {
        return Ok(false);
    }
    let Some(ConstantInfo::Rec(recursor)) = environment.find(&Name::str(family.clone(), "rec"))
    else {
        return Ok(false);
    };
    let Some(ConstantInfo::Defn(cases_on)) =
        environment.find(&Name::str(family.clone(), "casesOn"))
    else {
        return Ok(false);
    };
    // Reserve bounded work before each native construction and its comparison.
    // The generator's own node/binder counters remain active as usual.
    let reserve = |remaining: &mut u64| {
        let defaults = RecordBudget::default();
        let max_nodes = defaults
            .max_nodes
            .min(usize::try_from(*remaining / 2).unwrap_or(usize::MAX));
        if max_nodes == 0 {
            return Err(CompileError::Limit);
        }
        charge(remaining, max_nodes)?;
        charge(remaining, max_nodes)?;
        Ok(RecordBudget {
            max_nodes,
            max_binders: defaults.max_binders.min(max_nodes),
        })
    };
    fn candidate<T>(generated: Result<T, AuxiliaryError>) -> Result<Option<T>, CompileError> {
        match generated {
            Ok(value) => Ok(Some(value)),
            Err(AuxiliaryError::ResourceLimit) => Err(CompileError::Limit),
            Err(_) => Ok(None),
        }
    }
    let families = std::slice::from_ref(inductive);
    let Some(canonical_cases) = candidate(cases_on_declaration(
        inductive,
        recursor,
        families,
        reserve(&mut remaining)?,
    ))?
    else {
        return Ok(false);
    };
    if &canonical_cases != cases_on {
        return Ok(false);
    }
    let constructors: Vec<_> = inductive
        .ctors
        .iter()
        .filter_map(|name| match environment.find(name) {
            Some(ConstantInfo::Ctor(constructor)) => Some(constructor.clone()),
            _ => None,
        })
        .collect();
    let matches = match kind {
        "noConfusion" | "noConfusionType" => {
            let mut matches = false;
            let enum_helper_available = constructors
                .iter()
                .all(|constructor| constructor.num_fields == 0)
                && [
                    "noConfusionEnum",
                    "noConfusionTypeEnum",
                    "Nat",
                    "instDecidableEqNat",
                ]
                .into_iter()
                .all(|name| environment.contains(&Name::from_components([name])));
            // Early bootstrap families precede the enum helper. Either native
            // construction must still match the admitted definition exactly.
            // Prefer the available compact enum form before constructing its
            // potentially much larger ordinary case-analysis alternative.
            for use_enum_helper in [enum_helper_available, !enum_helper_available] {
                if use_enum_helper && !enum_helper_available {
                    continue;
                }
                let Some(Some(generated)) = candidate(no_confusion_declarations(
                    inductive,
                    &constructors,
                    cases_on,
                    use_enum_helper,
                    reserve(&mut remaining)?,
                    |name| environment.find(name),
                ))?
                else {
                    continue;
                };
                let canonical = if kind == "noConfusion" {
                    generated.no_confusion
                } else {
                    generated.no_confusion_type
                };
                if &canonical == definition {
                    matches = true;
                    break;
                }
            }
            matches
        }
        "ctorElimType" => candidate(ctor_elim_declarations(
            inductive,
            &constructors,
            cases_on,
            reserve(&mut remaining)?,
            |name| environment.find(name),
        ))?
        .flatten()
        .is_some_and(|generated| &generated.ctor_elim_type == definition),
        "brecOn.go" if inductive.is_rec => {
            let Some(ConstantInfo::Defn(below)) = environment.find(&Name::str(family, "below"))
            else {
                return Ok(false);
            };
            let Some(canonical_below) = candidate(below_declaration(
                recursor,
                families,
                reserve(&mut remaining)?,
            ))?
            else {
                return Ok(false);
            };
            &canonical_below == below
                && candidate(brec_on_declarations(
                    recursor,
                    families,
                    reserve(&mut remaining)?,
                ))?
                .is_some_and(|[go, _]| &go == definition)
        }
        _ => false,
    };
    if !matches {
        return Ok(false);
    }
    // A later explicit executable replacement is not a logical construction.
    let externs = fln_elab::externs::ExternTable::read_metered(environment, |amount| {
        charge(&mut remaining, amount)
    })
    .map_err(|error| match error {
        fln_elab::externs::ExternReadError::Budget(error) => error,
        fln_elab::externs::ExternReadError::Registry(fln_elab::externs::ExternError::Limit) => {
            CompileError::Limit
        }
        _ => CompileError::Unsupported {
            what: "invalid source extern metadata",
        },
    })?;
    let replacements =
        fln_elab::implemented_by::ImplementedByTable::read_metered(environment, |amount| {
            charge(&mut remaining, amount)
        })
        .map_err(|error| match error {
            fln_elab::implemented_by::ImplementedByReadError::Budget(error) => error,
            fln_elab::implemented_by::ImplementedByReadError::Registry(
                fln_elab::implemented_by::ImplementedByError::Limit,
            ) => CompileError::Limit,
            _ => CompileError::Unsupported {
                what: "invalid source executable replacement metadata",
            },
        })?;
    Ok(externs.get(&definition.base.name).is_none()
        && replacements.get(&definition.base.name).is_none())
}

impl SourceModuleArtifact {
    /// Compile every computable definition owned by this module and encode the
    /// pinned `.ir` companion. The compiler sees the exact checked implementation
    /// world, including private definitions, on cold, reused and persisted builds.
    /// On success, refresh all logical companions with the exact compiler
    /// signatures needed by downstream Lean compilation. Both code and logical
    /// products come from the saved checked snapshots, never caller-edited bytes.
    /// No runtime evaluation occurs, no partially compiled module is returned,
    /// and failure leaves every member of this artifact unchanged.
    ///
    /// This supports module-system files with checked scalar, enum and boxed-data
    /// signatures. Legacy files require IR embedded in their `.olean`, so a
    /// standalone companion is refused. Unsupported executable definitions refuse
    /// the entire facet. Safe opaque bodies use their checked implementation
    /// without changing the logical declaration. Proofs, type formers,
    /// declaration-only constants, tagged auxiliary recursors and exactly
    /// reconstructed logical inductive auxiliaries need no standalone
    /// executable entries; explicit
    /// `noncomputable` definitions are omitted as at the pin.
    /// Ordinary `.olean` compilation does not require this facet.
    pub fn compile_ir(
        &mut self,
        limits: SourceModuleIrLimits,
    ) -> Result<Outcome<fln_olean::write::EncodedModule>, SourceModuleIrError> {
        let input = &self.compiler;
        let refuse = |declaration: &Name, reason| SourceModuleIrError::Unsupported {
            module: input.name.clone(),
            declaration: declaration.clone(),
            reason,
        };
        let limit = |resource| SourceModuleIrError::Limit {
            module: input.name.clone(),
            resource,
        };
        if self.name != input.name {
            return Err(refuse(
                &self.name,
                "artifact name differs from its checked compiler input",
            ));
        }
        if !input.is_module {
            return Err(refuse(
                &input.name,
                "standalone IR requires a module-system file; legacy modules require executable entries embedded in their .olean",
            ));
        }
        if let Some(family) = &input.owned_computed_family {
            return Err(refuse(
                family,
                "computed-field source IR requires cached constructor and replacement ABI lowering",
            ));
        }
        if input.constants.len() > limits.writer.max_entries {
            return Err(limit("source declaration count"));
        }
        let noncomputable =
            fln_elab::noncomputable::read(input.engine.environment()).map_err(|error| {
                if matches!(error, fln_elab::noncomputable::NoncomputableError::Limit) {
                    limit("noncomputable metadata")
                } else {
                    refuse(&input.name, "invalid noncomputable metadata")
                }
            })?;
        let auxiliary_recursors = fln_elab::aux_recursors::AuxRecursors::read(
            input.engine.environment(),
        )
        .map_err(|error| {
            if matches!(error, fln_elab::aux_recursors::AuxRecursorError::Limit) {
                limit("auxiliary-recursor metadata")
            } else {
                refuse(&input.name, "invalid auxiliary-recursor metadata")
            }
        })?;
        let mut module = IrModule::default();
        let mut names = std::collections::BTreeSet::new();
        let public_names: BTreeSet<_> = input
            .public
            .constants
            .iter()
            .map(ConstantInfo::name)
            .collect();
        let local_names: BTreeSet<_> = input.constants.iter().map(ConstantInfo::name).collect();
        let mut public_signatures = Vec::new();
        for constant in &input.constants {
            let mut compiler_limits = limits.compiler;
            // The pin's generated auxiliary recursors are logical definitions
            // unfolded into callers, not separately scheduled source exports.
            // Only validated generator/importer tags grant this exemption; a
            // user function named recOn or casesOn still requires executable IR.
            if noncomputable.contains(constant.name())
                || auxiliary_recursors.contains(constant.name())
            {
                continue;
            }
            if matches!(constant, ConstantInfo::Defn(_) | ConstantInfo::Opaque(_)) {
                let mut ingress = limits.execution.ingress;
                ingress.max_nodes = ingress
                    .max_nodes
                    .min(usize::try_from(compiler_limits.max_work).unwrap_or(usize::MAX));
                let (irrelevant, work) =
                    crate::runtime::Preparation::computationally_irrelevant_header(
                        input.engine.environment(),
                        &constant.constant_val().type_,
                        ingress,
                    )
                    .map_err(|error| SourceModuleIrError::Compile {
                        module: input.name.clone(),
                        declaration: constant.name().clone(),
                        error: Box::new(DefinitionCompileError::Engine(
                            crate::EngineExecutionError::Ingress(error),
                        )),
                    })?;
                compiler_limits.max_work = compiler_limits
                    .max_work
                    .checked_sub(u64::try_from(work).unwrap_or(u64::MAX))
                    .ok_or_else(|| limit("source header classification"))?;
                // LCNF.shouldGenerateCode omits proof-valued definitions and
                // type formers, including opaque declarations. Their original
                // checked declarations stay in every logical companion; only
                // executable scheduling is affected by this type-only query.
                if irrelevant {
                    continue;
                }
            }
            if logical_inductive_auxiliary(input, constant, compiler_limits).map_err(|error| {
                SourceModuleIrError::Compile {
                    module: input.name.clone(),
                    declaration: constant.name().clone(),
                    error: Box::new(DefinitionCompileError::Ir(error)),
                }
            })? {
                continue;
            }
            if matches!(constant,
                ConstantInfo::Defn(definition)
                    if definition.safety == fln_env::constants::DefinitionSafety::Partial)
                && local_names.contains(&constant.name().parent())
                && !noncomputable.contains(&constant.name().parent())
                && crate::ir::is_checked_recursive_companion(
                    &input.engine,
                    constant.name(),
                    limits.execution,
                    compiler_limits,
                )
                .map_err(|error| SourceModuleIrError::Compile {
                    module: input.name.clone(),
                    declaration: constant.name().clone(),
                    error: Box::new(error),
                })?
            {
                // The owned logical declaration is compiled separately under
                // its source ABI. Its exact executable companion is selected
                // by runtime preparation, not emitted as an unsafe source API.
                continue;
            }
            match constant {
                ConstantInfo::Defn(_) | ConstantInfo::Opaque(_) => {}
                ConstantInfo::Thm(_)
                | ConstantInfo::Axiom(_)
                | ConstantInfo::Quot(_)
                | ConstantInfo::Induct(_)
                | ConstantInfo::Ctor(_)
                | ConstantInfo::Rec(_) => continue,
            }
            let compiled = crate::ir::compile_checked_source_definition(
                &input.engine,
                constant.name(),
                &input.options,
                limits.execution,
                compiler_limits,
            )
            .map_err(|error| SourceModuleIrError::Compile {
                module: input.name.clone(),
                declaration: constant.name().clone(),
                error: Box::new(error),
            })?;
            let compiled = match compiled {
                Outcome::Complete(compiled) => compiled,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            if !compiled.initializers.is_empty() || !compiled.uninterpreted.is_empty() {
                return Err(refuse(
                    constant.name(),
                    "definition compiler returned unbound module effects",
                ));
            }
            for declaration in compiled.decls {
                if names.len() >= limits.writer.max_entries {
                    return Err(limit("compiled declaration count"));
                }
                if !names.insert(declaration.name().clone()) {
                    return Err(refuse(
                        declaration.name(),
                        "compiled declarations have colliding names",
                    ));
                }
                // A generated helper may not replace an unrelated admitted
                // declaration, even when no body for that declaration is emitted.
                if declaration.name() != constant.name()
                    && input.engine.environment().contains(declaration.name())
                {
                    return Err(refuse(
                        declaration.name(),
                        "compiler helper collides with an admitted declaration",
                    ));
                }
                // Export the source-facing ABI and its own generated adapters,
                // without publishing private source declarations as metadata.
                if public_names.contains(constant.name()) {
                    public_signatures.push(CompilerSignature::from_ir(&declaration, false));
                }
                module.decls.push(declaration);
            }
        }
        module.decls.sort_by(|a, b| a.name().quick_cmp(b.name()));
        let extra_names: Vec<_> = module
            .decls
            .iter()
            .map(|declaration| declaration.name().clone())
            .collect();
        let encoded = encode_ir(
            IrWriteInput {
                module: OleanModuleWriteInput {
                    is_module: input.is_module,
                    imports: &input.imports,
                    constants: &[],
                    extra_const_names: &extra_names,
                },
                declarations: &module.decls,
                initializers: &[],
                additional_extensions: &[],
            },
            OleanWriteHeader {
                version: OLEAN_ACCEPTED_VERSIONS[0],
                flags: 1,
                lean_version: OLEAN_PIN_TAG.strip_prefix('v').unwrap_or(OLEAN_PIN_TAG),
                githash: OLEAN_PIN_COMMIT,
                base_addr: (OLEAN_REGION_ALIGN as u64) * 2,
            },
            limits.writer,
        )
        .map_err(|error| SourceModuleIrError::Encode {
            module: input.name.clone(),
            error,
        })?;
        let signatures: Vec<_> = module
            .decls
            .iter()
            .map(|declaration| CompilerSignature::from_ir(declaration, false))
            .collect();
        let mut budget = limits.writer.container;
        budget.max_bytes = budget
            .max_bytes
            .checked_sub(encoded.report.file_bytes)
            .ok_or_else(|| limit("executable artifact bytes"))?;
        budget.max_objects = budget
            .max_objects
            .checked_sub(encoded.report.runtime_objects)
            .ok_or_else(|| limit("executable artifact objects"))?;
        let pending = PendingArtifact {
            public: Arc::clone(&input.public),
            private: input.private.as_ref().map(Arc::clone),
            compiler: Arc::clone(&self.compiler),
        };
        let rebuilt = pending
            .encode_with_compiler_signatures(budget, &public_signatures, &signatures)
            .map_err(SourceModuleIrError::Logical)?;
        *self = rebuilt;
        Ok(Outcome::Complete(encoded))
    }
}
