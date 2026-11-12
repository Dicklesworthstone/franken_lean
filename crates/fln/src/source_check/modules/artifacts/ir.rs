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
    /// This currently supports module-system files and the native compiler's
    /// closed Nat/String/Bool signatures. Legacy files require IR embedded in
    /// their `.olean`, so a standalone companion is refused. Unsupported
    /// executable definitions refuse the entire facet. Safe opaque bodies use
    /// their checked implementation without changing the logical declaration. Theorems and declaration-only constants need no
    /// executable bodies; explicit `noncomputable` definitions are omitted as at
    /// the pin. Ordinary `.olean` compilation does not require this facet.
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
        let mut module = IrModule::default();
        let mut names = std::collections::BTreeSet::new();
        let public_names: BTreeSet<_> = input
            .public
            .constants
            .iter()
            .map(ConstantInfo::name)
            .collect();
        let mut public_signatures = Vec::new();
        for constant in &input.constants {
            if noncomputable.contains(constant.name()) {
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
                limits.compiler,
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
