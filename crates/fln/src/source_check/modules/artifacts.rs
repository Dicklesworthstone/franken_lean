//! Per-module, checked declaration products for the native Lake `.olean` facet.
use super::*;
use fln_olean::write::source::{
    CompilerData, CompilerSignature, SourceMetadata, encode_module_with_source_metadata,
};
use std::sync::Arc;

mod ir;
pub use ir::{SourceModuleIrError, SourceModuleIrLimits};

fn artifact_discrimination_key(
    key: fln_elab::instances::discr_tree::Key,
) -> fln_olean::source_extensions::DiscrTreeKey {
    use fln_elab::instances::discr_tree::Key;
    use fln_olean::source_extensions::DiscrTreeKey;
    match key {
        Key::Star => DiscrTreeKey::Star,
        Key::Other => DiscrTreeKey::Other,
        Key::Lit(value) => DiscrTreeKey::Lit(value),
        Key::FVar(id, arity) => DiscrTreeKey::FVar(id.0, arity),
        Key::Const(name, arity) => DiscrTreeKey::Const(name, arity),
        Key::Arrow => DiscrTreeKey::Arrow,
        Key::Proj(name, index, arity) => DiscrTreeKey::Proj(name, index, arity),
    }
}

/// One module's checked `.olean` facet, containing only its own constants.
#[derive(Debug)]
pub struct SourceModuleArtifact {
    pub name: Name,
    pub bytes: Vec<u8>,
    pub report: OleanModuleWriteReport,
    /// Module-system companion regions, present together. The public region
    /// exports interfaces; the private region retains checked implementations.
    /// These are source artifacts; executable IR is a separate compiler facet.
    pub companions: Option<SourceModuleCompanions>,
    /// The compiler consumes this private checked snapshot, never the caller-
    /// editable artifact bytes or the final environment of a sibling module.
    compiler: Arc<ir::CompilerInput>,
}

/// The source metadata and implementation companions of one module-system image.
#[derive(Debug)]
pub struct SourceModuleCompanions {
    pub server: Vec<u8>,
    pub private: Vec<u8>,
    pub server_report: OleanModuleWriteReport,
    pub private_report: OleanModuleWriteReport,
}

/// All products of a successfully checked import closure. No filesystem writes
/// occur here, and no partial products escape a failed check or encoding.
#[derive(Debug)]
pub struct SourceModuleBuild {
    pub checked: SourceModuleCheck,
    pub artifacts: Vec<SourceModuleArtifact>,
    /// Module snapshots reused from this process's checked build session.
    /// Every returned artifact is still encoded under this call's writer budget.
    pub reused_modules: usize,
    pub elaborated_modules: usize,
    /// Modules re-admitted from persisted records rather than elaborated.
    pub persisted_modules: usize,
    /// Each module of the closure, in build order, and how it was obtained.
    pub modules: Vec<super::persisted::ModuleProvenance>,
}

#[derive(Debug)]
pub enum SourceModuleBuildError {
    /// An ambient seed or caller-created environment has no import identity.
    UnboundBase,
    Check(SourceModuleCheckError),
    Encode {
        module: Name,
        error: OleanWriteError,
    },
}

impl std::fmt::Display for SourceModuleBuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnboundBase => f.write_str(
                "module artifacts require an empty base or rechecked .olean imports; an ambient source seed cannot be exported as a library",
            ),
            Self::Check(error) => error.fmt(f),
            Self::Encode { module, error } => write!(
                f,
                "encoding module `{}`: {error}",
                module.to_display_string()
            ),
        }
    }
}
impl std::error::Error for SourceModuleBuildError {}
impl SourceModuleBuildError {
    pub fn disposition(&self) -> (&'static str, bool, u8) {
        match self {
            Self::UnboundBase => ("input", false, 1),
            Self::Check(error) => error.disposition(),
            Self::Encode { error, .. } => match error {
                OleanWriteError::Budget { .. } => ("resource", false, 3),
                OleanWriteError::Unsupported { .. } => ("unsupported", false, 3),
                OleanWriteError::Contract { .. } | OleanWriteError::Region(_) => {
                    ("internal-fault", false, 4)
                }
            },
        }
    }
}

pub(super) struct PendingArtifact {
    public: Arc<ArtifactData>,
    private: Option<Arc<ArtifactData>>,
    compiler: Arc<ir::CompilerInput>,
}

#[derive(Debug)]
struct ArtifactData {
    name: Name,
    imports: Vec<OleanModuleImport>,
    constants: Vec<ConstantInfo>,
    metadata: SourceMetadata,
}

/// Every artifact must name its entire external base, directly or through local
/// dependencies. Import receipts project that base per module; legacy explicit
/// Engine callers must supply the exact world themselves. Neither path may
/// let an unrelated external sibling leak names into a module's declarations.
pub(super) fn validate_import_scope(
    base: &Engine,
    index: usize,
    dependencies: &[usize],
    plan: &graph::Plan,
    modules: &[SourceModuleInput<'_>],
    meter: &mut Meter,
) -> Result<(), SourceModuleCheckError> {
    meter.work(modules.len())?;
    let local: BTreeSet<_> = modules.iter().map(|module| module.name).collect();
    let mut work = Vec::new();
    for source in dependencies.iter().copied().chain(std::iter::once(index)) {
        for import in &plan.headers[source].imports {
            meter.work(1)?;
            if !local.contains(import) {
                work.push(import.clone());
            }
        }
    }
    let mut visible = BTreeSet::new();
    while let Some(import) = work.pop() {
        meter.work(1)?;
        if visible.insert(import.clone())
            && let Some(dependencies) = base.imported_module_dependencies.get(&import)
        {
            meter.work(dependencies.len())?;
            work.extend(dependencies.iter().cloned());
        }
    }
    for import in base.imported_modules() {
        meter.work(1)?;
        if !visible.contains(import) {
            return Err(SourceModuleCheckError::AmbientImport {
                module: modules[index].name.clone(),
                import: import.clone(),
            });
        }
    }
    Ok(())
}

impl ArtifactData {
    fn capture(
        name: &Name,
        header: &SourceHeader,
        base: &Environment,
        checked: &Environment,
        meter: &mut Meter,
    ) -> Result<Self, SourceModuleCheckError> {
        // Computed fields require `_impl` compiler layouts and the generated
        // replacement/attribute inventory as one package. Until this writer
        // emits that complete package, refuse new provenance before projecting
        // ordinary inductive caches; a successful artifact must never silently
        // lose its cache-bearing runtime representation.
        if let Some(journal) = checked.extension(&fln_elab::computed_fields::journal_name()) {
            let inherited = base.extension(&fln_elab::computed_fields::journal_name());
            let mut unchanged = inherited.is_some_and(|previous| previous.len() == journal.len());
            let mut prior = inherited
                .into_iter()
                .flat_map(|previous| previous.entries());
            for entry in journal.entries() {
                meter.work(1)?;
                meter.bytes(entry.payload.len())?;
                unchanged &= prior.next() == Some(entry);
            }
            if !unchanged {
                let remaining = meter.limits.max_work.saturating_sub(meter.work);
                let allowance = (remaining / 2).min(100_000);
                meter.work(allowance)?;
                let families = fln_elab::computed_fields::families(
                    checked,
                    fln_elab::records::RecordBudget {
                        max_binders: allowance,
                        max_nodes: allowance,
                    },
                )
                .map_err(|error| match error {
                    fln_elab::computed_fields::ComputedFieldError::ResourceLimit => {
                        SourceModuleCheckError::Limit {
                            resource: "module work",
                            limit: meter.limits.max_work,
                        }
                    }
                    _ => SourceModuleCheckError::Extension {
                        module: name.clone(),
                        extension: fln_elab::computed_fields::journal_name(),
                        reason: "invalid computed-field generation provenance",
                    },
                })?;
                for family in families {
                    meter.work(1)?;
                    if !base.contains(&family) || !base.contains(&Name::str(family, "_impl")) {
                        return Err(SourceModuleCheckError::Extension {
                            module: name.clone(),
                            extension: fln_elab::computed_fields::journal_name(),
                            reason: "computed-field artifacts require generated implementation compiler layouts and attribute metadata",
                        });
                    }
                }
            }
        }
        // Default equation policies and realization provenance are local
        // compilation facts: the pin reconstructs their result from the actual
        // checked equation declarations. Nondefault definition-time options
        // require its persistent eqnOptionsExt and cannot be silently dropped.
        if let Some(journal) =
            checked.extension(&fln_elab::source::scope::simp::equations::journal_name())
        {
            for entry in journal.entries() {
                meter.bytes(entry.payload.len())?;
            }
        }
        let remaining = meter.limits.max_work.saturating_sub(meter.work);
        let work =
            fln_elab::source::scope::simp::equations::validate_export(checked, remaining)
                .map_err(|error| match error {
                    fln_elab::source::scope::simp::SimpSetError::Limit => {
                        SourceModuleCheckError::Limit {
                            resource: "module work",
                            limit: meter.limits.max_work,
                        }
                    }
                    fln_elab::source::scope::simp::SimpSetError::UnsupportedDeclaration(_) => {
                        SourceModuleCheckError::Extension {
                            module: name.clone(),
                            extension: fln_elab::source::scope::simp::equations::journal_name(),
                            reason: "nondefault equation-generation options require pinned persistent metadata that the writer cannot yet serialize",
                        }
                    }
                    _ => SourceModuleCheckError::Extension {
                        module: name.clone(),
                        extension: fln_elab::source::scope::simp::equations::journal_name(),
                        reason: "invalid equation-generation provenance",
                    },
                })?;
        meter.work(work)?;
        let mut constants = Vec::new();
        for (name, constant) in checked.constants() {
            meter.work(1)?;
            if !base.contains(name) {
                constants.push(constant.clone());
            }
        }
        // Lean.Elab.HeaderSyntax.imports adds two Init imports (ordinary and
        // meta) unless `prelude` is present. Graph planning inserts the first
        // name, and retains every explicit import row after it.
        let mut imports = Vec::new();
        for (index, module) in header.imports.iter().enumerate() {
            let (is_exported, import_all) =
                if header.module_system && (header.prelude || index != 0) {
                    let explicit = index - usize::from(!header.prelude);
                    let spec = header
                        .import_specs
                        .get(explicit)
                        .filter(|spec| spec.module == *module)
                        .ok_or_else(|| SourceModuleCheckError::ImportContext {
                            module: name.clone(),
                            reason: "module artifact imports differ from their checked header",
                        })?;
                    (spec.public_at.is_some(), spec.all_at.is_some())
                } else {
                    (true, false)
                };
            imports.push(OleanModuleImport {
                module: module.clone(),
                import_all,
                is_exported,
                is_meta: false,
            });
            if index == 0 && !header.prelude {
                imports.push(OleanModuleImport {
                    module: module.clone(),
                    import_all: false,
                    is_exported: true,
                    is_meta: true,
                });
            }
        }
        let remaining = meter.limits.max_work.saturating_sub(meter.work);
        let exported = fln_elab::instances::export::registrations(base, checked, remaining)
            .map_err(|error| match error {
                fln_elab::instances::InstanceRegistryError::Limit => {
                    SourceModuleCheckError::Limit {
                        resource: "module work",
                        limit: meter.limits.max_work,
                    }
                }
                _ => SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::instances::export::journal_name(),
                    reason: "invalid class or instance metadata export",
                },
            })?;
        let (registrations, work) = exported.ok_or_else(|| SourceModuleCheckError::Extension {
            module: name.clone(),
            extension: fln_elab::instances::export::journal_name(),
            reason: "instance registration ownership, scope, or exact indexing is unsupported",
        })?;
        meter.work(work)?;
        meter.bytes(registrations.bytes_examined)?;
        let mut metadata = SourceMetadata::default();
        for class in registrations.classes {
            meter.bytes(
                4 * (class.parameters.out_params.len() + class.parameters.out_level_params.len()),
            )?;
            metadata
                .classes
                .push(fln_olean::source_extensions::ClassEntry {
                    name: class.name,
                    out_params: class.parameters.out_params,
                    out_level_params: class.parameters.out_level_params,
                });
        }
        for instance in registrations.instances {
            use fln_olean::source_extensions::{DiscrTreeKey, InstanceEntry};
            meter.work(1)?;
            meter.bytes(instance.synth_order.len().saturating_mul(4))?;
            meter.bytes(
                instance
                    .keys
                    .len()
                    .saturating_mul(std::mem::size_of::<DiscrTreeKey>()),
            )?;
            let keys = instance
                .keys
                .into_iter()
                .map(artifact_discrimination_key)
                .collect();
            metadata.instances.push(InstanceEntry {
                declaration: instance.declaration,
                value: instance.value,
                priority: instance.priority,
                synth_order: instance.synth_order,
                scope: instance.scope,
                keys,
            });
        }
        let remaining = meter.limits.max_work.saturating_sub(meter.work);
        let simps = fln_elab::source::scope::simp::export::registrations(base, checked, remaining)
            .map_err(|error| match error {
                fln_elab::source::scope::simp::SimpSetError::Limit => {
                    SourceModuleCheckError::Limit {
                        resource: "module work",
                        limit: meter.limits.max_work,
                    }
                }
                fln_elab::source::scope::simp::SimpSetError::UnsupportedDeclaration(_) => {
                    SourceModuleCheckError::Extension {
                        module: name.clone(),
                        extension: fln_elab::source::scope::simp::export::journal_name(),
                        reason: "simp export requires supported equality proofs, checked equation theorems, or reducible definitions; unsupported equation generation and imported proof re-registration cannot be serialized",
                    }
                }
                _ => SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::source::scope::simp::export::journal_name(),
                    reason: "invalid simp metadata export",
                },
            })?;
        meter.work(simps.work)?;
        meter.bytes(simps.bytes_examined)?;
        for row in simps.entries {
            use fln_elab::source::scope::simp::export::Kind;
            use fln_olean::source_extensions::{DiscrTreeKey, SimpEntry, SimpKind, SimpTheorem};
            meter.work(1)?;
            let kind = match row {
                Kind::Unfold(declaration) => SimpKind::Unfold(declaration),
                Kind::UnfoldTheorems {
                    declaration,
                    theorems,
                } => {
                    meter.work(theorems.len())?;
                    for theorem in &theorems {
                        meter.bytes(theorem.to_canonical_bytes().len())?;
                    }
                    SimpKind::UnfoldTheorems {
                        declaration,
                        theorems,
                    }
                }
                Kind::Theorem(theorem) => {
                    meter.work(
                        theorem
                            .keys
                            .len()
                            .saturating_add(theorem.level_params.len()),
                    )?;
                    meter.bytes(
                        theorem
                            .keys
                            .len()
                            .saturating_mul(std::mem::size_of::<DiscrTreeKey>()),
                    )?;
                    SimpKind::Theorem(SimpTheorem {
                        proof: theorem.proof,
                        level_params: theorem.level_params,
                        origin: theorem.origin,
                        origin_reverse: theorem.origin_reverse,
                        priority: theorem.priority,
                        post: theorem.post,
                        permutation: theorem.permutation,
                        reflexive: theorem.reflexive,
                        backward_reflexive: theorem.backward_reflexive,
                        keys: theorem
                            .keys
                            .into_iter()
                            .map(artifact_discrimination_key)
                            .collect(),
                    })
                }
            };
            metadata.simp.push(SimpEntry { scope: None, kind });
        }
        let remaining = meter.limits.max_work.saturating_sub(meter.work);
        let defaults = fln_elab::instances::defaults::registrations(base, checked, remaining)
            .map_err(|error| match error {
                fln_elab::instances::InstanceRegistryError::Limit => {
                    SourceModuleCheckError::Limit {
                        resource: "module work",
                        limit: meter.limits.max_work,
                    }
                }
                _ => SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::instances::defaults::journal_name(),
                    reason: "invalid default instance metadata export",
                },
            })?;
        meter.work(defaults.work)?;
        meter.bytes(defaults.bytes_examined)?;
        for row in defaults.entries {
            meter.work(1)?;
            metadata
                .defaults
                .push(fln_olean::source_extensions::DefaultEntry {
                    class: row.class,
                    declaration: row.candidate.declaration,
                    priority: row.candidate.priority,
                });
        }
        let remaining = meter.limits.max_work.saturating_sub(meter.work);
        let exported = fln_elab::implemented_by::export::registrations(base, checked, remaining)
            .map_err(|error| match error {
                fln_elab::implemented_by::ImplementedByError::Limit => {
                    SourceModuleCheckError::Limit {
                        resource: "module work",
                        limit: meter.limits.max_work,
                    }
                }
                _ => SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::implemented_by::journal_name(),
                    reason: "invalid executable attribute metadata export",
                },
            })?;
        let rows = exported.ok_or_else(|| SourceModuleCheckError::Extension {
            module: name.clone(),
            extension: fln_elab::implemented_by::journal_name(),
            reason: "executable attributes must belong to declarations defined in this module",
        })?;
        meter.work(rows.work)?;
        meter.bytes(rows.bytes_examined)?;
        for (declaration, implementation) in rows.entries {
            meter.work(1)?;
            metadata
                .implemented_by
                .push(fln_olean::source_extensions::ImplementedByEntry {
                    declaration,
                    implementation,
                });
        }
        let remaining = meter.limits.max_work.saturating_sub(meter.work);
        let exported = fln_elab::externs::export::registrations(base, checked, remaining).map_err(
            |error| match error {
                fln_elab::externs::ExternError::Limit => SourceModuleCheckError::Limit {
                    resource: "module work",
                    limit: meter.limits.max_work,
                },
                _ => SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::externs::journal_name(),
                    reason: "invalid executable attribute metadata export",
                },
            },
        )?;
        let rows = exported.ok_or_else(|| SourceModuleCheckError::Extension {
            module: name.clone(),
            extension: fln_elab::externs::journal_name(),
            reason: "executable attributes must belong to declarations defined in this module",
        })?;
        meter.work(rows.work)?;
        meter.bytes(rows.bytes_examined)?;
        for (declaration, entries) in rows.entries {
            use fln_elab::externs::ExternEntry as Native;
            use fln_olean::source_extensions::{ExternAttribute, ExternEntry as Wire};
            meter.work(entries.len().saturating_add(1))?;
            metadata.externs.push(ExternAttribute {
                declaration,
                entries: entries
                    .into_iter()
                    .map(|entry| match entry {
                        Native::Adhoc { backend } => Wire::Adhoc { backend },
                        Native::Inline { backend, pattern } => Wire::Inline { backend, pattern },
                        Native::Standard { backend, symbol } => Wire::Standard { backend, symbol },
                        Native::Opaque => Wire::Opaque,
                    })
                    .collect(),
            });
        }
        let remaining = meter.limits.max_work.saturating_sub(meter.work);
        let exported = fln_elab::macro_inline::export::registrations(base, checked, remaining)
            .map_err(|error| match error {
                fln_elab::macro_inline::MacroInlineError::Limit => SourceModuleCheckError::Limit {
                    resource: "module work",
                    limit: meter.limits.max_work,
                },
                _ => SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::macro_inline::journal_name(),
                    reason: "invalid macro-inline metadata export",
                },
            })?;
        let inline = exported.ok_or_else(|| SourceModuleCheckError::Extension {
            module: name.clone(),
            extension: fln_elab::macro_inline::journal_name(),
            reason: "inlining attributes must belong to declarations defined in this module",
        })?;
        meter.work(inline.work)?;
        meter.bytes(inline.bytes_examined)?;
        for declaration in inline.declarations {
            meter.work(1)?;
            metadata
                .inline
                .push(fln_olean::source_extensions::InlineEntry {
                    declaration,
                    kind: fln_olean::source_extensions::InlineKind::MacroInline,
                });
        }
        let remaining = meter.limits.max_work.saturating_sub(meter.work);
        let exported = fln_elab::reducibility::export::statuses(base, checked, remaining).map_err(
            |error| match error {
                fln_elab::reducibility::ReducibilityError::Limit => SourceModuleCheckError::Limit {
                    resource: "module work",
                    limit: meter.limits.max_work,
                },
                _ => SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::reducibility::export::journal_name(),
                    reason: "invalid reducibility metadata export",
                },
            },
        )?;
        meter.work(exported.work)?;
        let status = |status| {
            use fln_elab::reducibility::Reducibility;
            use fln_olean::source_extensions::ReducibilityStatus;
            match status {
                Reducibility::Reducible => ReducibilityStatus::Reducible,
                Reducibility::Semireducible => ReducibilityStatus::Semireducible,
                Reducibility::Irreducible => ReducibilityStatus::Irreducible,
                Reducibility::ImplicitReducible => ReducibilityStatus::ImplicitReducible,
            }
        };
        let mut explicit_statuses = std::collections::BTreeSet::new();
        for declaration in exported.default_semireducible {
            meter.work(1)?;
            explicit_statuses.insert(declaration);
        }
        for row in exported.owned {
            use fln_olean::source_extensions::ReducibilityEntry;
            meter.work(1)?;
            explicit_statuses.insert(row.declaration.clone());
            metadata.reducibility.push(ReducibilityEntry {
                declaration: row.declaration,
                status: status(row.status),
            });
        }
        for row in exported.imported {
            meter.work(1)?;
            metadata.reducibility_extra.push(
                fln_olean::source_extensions::ReducibilityExtraEntry {
                    scope: None,
                    declaration: row.declaration,
                    status: status(row.status),
                },
            );
        }
        // Native instances have this default in ReducibilityTable::effective.
        // Once imported, their status must come from reducibilityCore instead;
        // An explicit owned status always wins, including later overrides.
        // Known semireducible defaults (such as proof instances) deliberately
        // have no wire row and must not acquire this data-instance fallback.
        // Retagging an imported declaration preserves its original policy;
        // imported overrides belong only to reducibilityExtra above.
        for instance in &metadata.instances {
            meter.work(1)?;
            if !base.contains(&instance.declaration)
                && explicit_statuses.insert(instance.declaration.clone())
            {
                metadata
                    .reducibility
                    .push(fln_olean::source_extensions::ReducibilityEntry {
                        declaration: instance.declaration.clone(),
                        status: fln_olean::source_extensions::ReducibilityStatus::ImplicitReducible,
                    });
            }
        }
        // The module's own `protected` tags: those the checked environment
        // records beyond its import base. The pin tags a declaration only in the
        // module that declares it, and writes them into that module's olean.
        let protected = |env: &Environment| {
            fln_elab::protected_names::ProtectedNames::read(env).map_err(|_| {
                SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::protected_names::journal_name(),
                    reason: "invalid protected-declaration journal",
                }
            })
        };
        let inherited = protected(base)?;
        for tagged in protected(checked)?.iter() {
            meter.work(1)?;
            if !inherited.contains(tagged) {
                metadata.protected.push(tagged.clone());
            }
        }
        // Deprecation parameters belong to the declaration's defining module.
        // Generated enum aliases use the same native journal as source attributes.
        let deprecations = |env: &Environment, meter: &mut Meter| {
            if let Some(journal) = env.extension(&fln_elab::deprecations::journal_name()) {
                for entry in journal.entries() {
                    meter.work(1)?;
                    meter.bytes(entry.payload.len())?;
                }
            }
            fln_elab::deprecations::Deprecations::read(env).map_err(|error| match error {
                fln_elab::deprecations::DeprecationError::Limit => SourceModuleCheckError::Limit {
                    resource: "module work",
                    limit: meter.limits.max_work,
                },
                _ => SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::deprecations::journal_name(),
                    reason: "invalid deprecation journal",
                },
            })
        };
        let inherited = deprecations(base, meter)?;
        for row in deprecations(checked, meter)?.iter() {
            meter.work(1)?;
            if let Some(previous) = inherited.get(&row.declaration) {
                if previous != row {
                    return Err(SourceModuleCheckError::Extension {
                        module: name.clone(),
                        extension: fln_elab::deprecations::journal_name(),
                        reason: "a module cannot change an imported deprecation parameter",
                    });
                }
                continue;
            }
            if base.contains(&row.declaration) {
                return Err(SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::deprecations::journal_name(),
                    reason: "a module cannot deprecate an imported declaration",
                });
            }
            metadata
                .deprecations
                .push(fln_olean::source_extensions::DeprecationEntry {
                    declaration: row.declaration.clone(),
                    new_name: row.new_name.clone(),
                    text: row.text.clone(),
                    since: row.since.clone(),
                });
        }
        // Auxiliary tags belong to the module that generated the definition;
        // dependencies' tags stay in their own artifacts, including diamonds.
        let auxiliaries = |env: &Environment| {
            fln_elab::aux_recursors::AuxRecursors::read(env).map_err(|_| {
                SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::aux_recursors::journal_name(),
                    reason: "invalid auxiliary-recursor journal",
                }
            })
        };
        let inherited = auxiliaries(base)?;
        for tagged in auxiliaries(checked)?.iter() {
            meter.work(1)?;
            if !inherited.contains(tagged) {
                if base.contains(tagged) {
                    return Err(SourceModuleCheckError::Extension {
                        module: name.clone(),
                        extension: fln_elab::aux_recursors::journal_name(),
                        reason: "a module cannot tag an imported auxiliary recursor",
                    });
                }
                metadata.aux_recursors.push(tagged.clone());
            }
        }
        // Compilation effects belong only to their declaring module. Preserve
        // explicit tags and generated partial-companion tags without copying
        // dependencies' journals or changing their executable interpretation.
        let noncomputable = |env: &Environment, meter: &mut Meter| {
            if let Some(journal) = env.extension(&fln_elab::noncomputable::journal_name()) {
                for entry in journal.entries() {
                    meter.work(1)?;
                    meter.bytes(entry.payload.len())?;
                }
            }
            fln_elab::noncomputable::read(env).map_err(|error| match error {
                fln_elab::noncomputable::NoncomputableError::Limit => {
                    SourceModuleCheckError::Limit {
                        resource: "native noncomputable tags",
                        limit: fln_elab::noncomputable::MAX_ROWS,
                    }
                }
                _ => SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::noncomputable::journal_name(),
                    reason: "invalid noncomputable-declaration journal",
                },
            })
        };
        let inherited = noncomputable(base, meter)?;
        for tagged in noncomputable(checked, meter)? {
            meter.work(1)?;
            if !inherited.contains(&tagged) {
                if base.contains(&tagged) {
                    return Err(SourceModuleCheckError::Extension {
                        module: name.clone(),
                        extension: fln_elab::noncomputable::journal_name(),
                        reason: "a module cannot tag an imported noncomputable declaration",
                    });
                }
                metadata.noncomputable.push(tagged);
            }
        }
        let unbox = |env: &Environment, meter: &mut Meter| {
            if let Some(journal) = env.extension(&fln_elab::unbox::journal_name()) {
                for entry in journal.entries() {
                    meter.work(1)?;
                    meter.bytes(entry.payload.len())?;
                }
            }
            fln_elab::unbox::read(env).map_err(|error| match error {
                fln_elab::unbox::UnboxError::Limit => SourceModuleCheckError::Limit {
                    resource: "native unbox tags",
                    limit: fln_elab::unbox::MAX_ROWS,
                },
                _ => SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::unbox::journal_name(),
                    reason: "invalid unbox journal",
                },
            })
        };
        let inherited = unbox(base, meter)?;
        for tagged in unbox(checked, meter)? {
            meter.work(1)?;
            if !inherited.contains(&tagged) {
                if base.contains(&tagged) {
                    return Err(SourceModuleCheckError::Extension {
                        module: name.clone(),
                        extension: fln_elab::unbox::journal_name(),
                        reason: "a module cannot tag an imported unbox declaration",
                    });
                }
                metadata.unbox.push(tagged);
            }
        }
        let never_extract = |env: &Environment, meter: &mut Meter| {
            if let Some(journal) = env.extension(&fln_elab::never_extract::journal_name()) {
                for entry in journal.entries() {
                    meter.work(1)?;
                    meter.bytes(entry.payload.len())?;
                }
            }
            fln_elab::never_extract::read(env).map_err(|error| match error {
                fln_elab::never_extract::NeverExtractError::Limit => {
                    SourceModuleCheckError::Limit {
                        resource: "native never_extract tags",
                        limit: fln_elab::never_extract::MAX_ROWS,
                    }
                }
                _ => SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::never_extract::journal_name(),
                    reason: "invalid never_extract journal",
                },
            })
        };
        let inherited = never_extract(base, meter)?;
        for tagged in never_extract(checked, meter)? {
            meter.work(1)?;
            if !inherited.contains(&tagged) {
                if base.contains(&tagged) {
                    return Err(SourceModuleCheckError::Extension {
                        module: name.clone(),
                        extension: fln_elab::never_extract::journal_name(),
                        reason: "a module cannot tag an imported never_extract declaration",
                    });
                }
                metadata.never_extract.push(tagged);
            }
        }
        let match_patterns = |env: &Environment, meter: &mut Meter| {
            if let Some(journal) = env.extension(&fln_elab::match_pattern::journal_name()) {
                for entry in journal.entries() {
                    meter.work(1)?;
                    meter.bytes(entry.payload.len())?;
                }
            }
            fln_elab::match_pattern::read(env).map_err(|error| match error {
                fln_elab::match_pattern::MatchPatternError::Limit => {
                    SourceModuleCheckError::Limit {
                        resource: "native match-pattern tags",
                        limit: fln_elab::match_pattern::MAX_ROWS,
                    }
                }
                _ => SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::match_pattern::journal_name(),
                    reason: "invalid match-pattern journal",
                },
            })
        };
        let inherited = match_patterns(base, meter)?;
        for tagged in match_patterns(checked, meter)? {
            meter.work(1)?;
            if !inherited.contains(&tagged) {
                if base.contains(&tagged) {
                    return Err(SourceModuleCheckError::Extension {
                        module: name.clone(),
                        extension: fln_elab::match_pattern::journal_name(),
                        reason: "a module cannot tag an imported match-pattern definition",
                    });
                }
                metadata.match_patterns.push(tagged);
            }
        }
        let symms = |env: &Environment, meter: &mut Meter| {
            if let Some(journal) = env.extension(&fln_elab::symm::journal_name()) {
                for entry in journal.entries() {
                    meter.work(1)?;
                    meter.bytes(entry.payload.len())?;
                }
            }
            fln_elab::symm::read(env).map_err(|error| match error {
                fln_elab::symm::SymmRegistryError::Limit => SourceModuleCheckError::Limit {
                    resource: "native symmetry registrations",
                    limit: fln_elab::symm::MAX_ROWS,
                },
                _ => SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::symm::journal_name(),
                    reason: "invalid symmetry journal",
                },
            })
        };
        let inherited = symms(base, meter)?;
        let current = symms(checked, meter)?;
        if !current.starts_with(&inherited) {
            return Err(SourceModuleCheckError::Extension {
                module: name.clone(),
                extension: fln_elab::symm::journal_name(),
                reason: "symmetry registrations do not extend the checked predecessor journal",
            });
        }
        for entry in current.into_iter().skip(inherited.len()) {
            meter.work(1)?;
            if !checked.contains(&entry.lemma.declaration) {
                return Err(SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::symm::journal_name(),
                    reason: "a symmetry registration names a hidden declaration",
                });
            }
            metadata
                .symms
                .push(fln_olean::source_extensions::SymmEntry {
                    declaration: entry.lemma.declaration,
                    keys: entry
                        .lemma
                        .keys
                        .into_iter()
                        .map(artifact_discrimination_key)
                        .collect(),
                    scope: entry.namespace,
                });
        }
        let grind_patterns = |env: &Environment, meter: &mut Meter| {
            use fln_elab::grind_patterns::{self, GrindPatternError};
            if let Some(journal) = env.extension(&grind_patterns::journal_name()) {
                for entry in journal.entries() {
                    meter.work(1)?;
                    meter.bytes(entry.payload.len())?;
                }
            }
            grind_patterns::read(env).map_err(|error| match error {
                GrindPatternError::Limit => SourceModuleCheckError::Limit {
                    resource: "native grind-pattern registrations",
                    limit: grind_patterns::MAX_ROWS,
                },
                _ => SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: grind_patterns::journal_name(),
                    reason: "invalid grind-pattern journal",
                },
            })
        };
        let inherited = grind_patterns(base, meter)?;
        let current = grind_patterns(checked, meter)?;
        if !current.starts_with(&inherited) {
            return Err(SourceModuleCheckError::Extension {
                module: name.clone(),
                extension: fln_elab::grind_patterns::journal_name(),
                reason: "grind patterns do not extend the checked predecessor journal",
            });
        }
        for entry in current.into_iter().skip(inherited.len()) {
            meter.work(1)?;
            let captured = entry.captured.ok_or_else(|| SourceModuleCheckError::Extension {
                module: name.clone(),
                extension: fln_elab::grind_patterns::journal_name(),
                reason: "a legacy grind pattern has no registration-time normalization snapshot",
            })?;
            let declaration = checked.find(&entry.declaration).ok_or_else(|| {
                SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::grind_patterns::journal_name(),
                    reason: "a grind-pattern registration names a hidden declaration",
                }
            })?;
            let levels = declaration
                .constant_val()
                .level_params
                .iter()
                .cloned()
                .map(fln_core::level::Level::param)
                .collect();
            metadata
                .grind_patterns
                .push(fln_olean::source_extensions::GrindPatternEntry {
                    proof: Expr::const_(entry.declaration.clone(), levels),
                    declaration: entry.declaration,
                    num_params: entry.num_params,
                    patterns: captured.patterns,
                    symbols: captured.symbols,
                });
        }
        let eliminator_tags = |env: &Environment, kind, meter: &mut Meter| {
            let extension = fln_elab::eliminator_tags::journal_name(kind);
            if let Some(journal) = env.extension(&extension) {
                for entry in journal.entries() {
                    meter.work(1)?;
                    meter.bytes(entry.payload.len())?;
                }
            }
            fln_elab::eliminator_tags::read(env, kind).map_err(|error| match error {
                fln_elab::eliminator_tags::EliminatorTagError::Limit => {
                    SourceModuleCheckError::Limit {
                        resource: "native eliminator tag journal",
                        limit: fln_elab::eliminator_tags::MAX_ROWS,
                    }
                }
                _ => SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension,
                    reason: "invalid or unsupported eliminator tag journal",
                },
            })
        };
        for (kind, tags) in [
            (
                fln_elab::eliminator_tags::TagKind::ElabAsElim,
                &mut metadata.elab_as_elim,
            ),
            (
                fln_elab::eliminator_tags::TagKind::SparseCasesOn,
                &mut metadata.sparse_cases_on,
            ),
        ] {
            let inherited = eliminator_tags(base, kind, meter)?;
            for tagged in eliminator_tags(checked, kind, meter)? {
                meter.work(1)?;
                if !inherited.contains(&tagged) {
                    if base.contains(&tagged) {
                        return Err(SourceModuleCheckError::Extension {
                            module: name.clone(),
                            extension: fln_elab::eliminator_tags::journal_name(kind),
                            reason: "a module cannot tag an imported eliminator declaration",
                        });
                    }
                    tags.push(tagged);
                }
            }
        }
        let anonymous_constructors = |env: &Environment, meter: &mut Meter| {
            use fln_elab::delaborator_tags;
            if let Some(journal) = env.extension(&delaborator_tags::source_journal_name()) {
                for entry in journal.entries() {
                    meter.work(1)?;
                    meter.bytes(entry.payload.len())?;
                }
            }
            delaborator_tags::source_anonymous_constructors(env).map_err(|error| match error {
                delaborator_tags::DelaboratorTagError::Limit => SourceModuleCheckError::Limit {
                    resource: "native anonymous-constructor tags",
                    limit: delaborator_tags::MAX_SOURCE_ROWS,
                },
                _ => SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: delaborator_tags::source_journal_name(),
                    reason: "invalid anonymous-constructor tag journal",
                },
            })
        };
        let inherited = anonymous_constructors(base, meter)?;
        for tagged in anonymous_constructors(checked, meter)? {
            meter.work(1)?;
            if !inherited.contains(&tagged) {
                if base.contains(&tagged) {
                    return Err(SourceModuleCheckError::Extension {
                        module: name.clone(),
                        extension: fln_elab::delaborator_tags::source_journal_name(),
                        reason: "a module cannot tag an imported anonymous-constructor declaration",
                    });
                }
                metadata.pp_anonymous_constructor.push(tagged);
            }
        }
        let coercions = |env: &Environment, meter: &mut Meter| {
            use fln_elab::delaborator_tags::{DelaboratorTagError, coercions};
            if let Some(journal) = env.extension(&coercions::journal_name()) {
                for entry in journal.entries() {
                    meter.work(1)?;
                    meter.bytes(entry.payload.len())?;
                }
            }
            coercions::read(env).map_err(|error| match error {
                DelaboratorTagError::Limit => SourceModuleCheckError::Limit {
                    resource: "native coercion registrations",
                    limit: coercions::MAX_ROWS,
                },
                _ => SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: coercions::journal_name(),
                    reason: "invalid coercion journal",
                },
            })
        };
        let inherited = coercions(base, meter)?;
        let current = coercions(checked, meter)?;
        if !current.starts_with(&inherited) {
            return Err(SourceModuleCheckError::Extension {
                module: name.clone(),
                extension: fln_elab::delaborator_tags::coercions::journal_name(),
                reason: "coercion registrations do not extend the checked predecessor journal",
            });
        }
        for (declaration, info) in current.into_iter().skip(inherited.len()) {
            meter.work(1)?;
            use fln_elab::delaborator_tags::CoeFnKind;
            use fln_olean::source_extensions as metadata_types;
            metadata.coercions.push(metadata_types::CoeEntry {
                declaration,
                num_args: info.num_args,
                coercee: info.coercee,
                kind: match info.kind {
                    CoeFnKind::Coe => metadata_types::CoeFnKind::Coe,
                    CoeFnKind::CoeFun => metadata_types::CoeFnKind::CoeFun,
                    CoeFnKind::CoeSort => metadata_types::CoeFnKind::CoeSort,
                },
            });
        }
        // Reflexivity tags are selection metadata owned by the module that
        // declared the theorem. The codec already emits both pinned tag sets;
        // export the journal delta rather than silently losing it at this edge.
        let defeq = |env: &Environment, meter: &mut Meter| {
            use fln_elab::source::scope::simp::{SimpSetError, defeq};
            if let Some(journal) = env.extension(&defeq::journal_name()) {
                for entry in journal.entries() {
                    meter.work(2 * (1 + entry.payload.len().div_ceil(64)))?;
                    meter.bytes(entry.payload.len())?;
                }
            }
            defeq::read(env, || Ok(()))
                .and_then(|strict| {
                    defeq::read_backward(env, || Ok(())).map(|backward| (strict, backward))
                })
                .map_err(|error| match error {
                    fln_elab::NatDefinitionElabError::Inference(
                        fln_elab::source::SourceInferenceError::SimpSet(SimpSetError::Limit),
                    ) => SourceModuleCheckError::Limit {
                        resource: "native reflexivity tags",
                        limit: defeq::MAX_ROWS,
                    },
                    _ => SourceModuleCheckError::Extension {
                        module: name.clone(),
                        extension: defeq::journal_name(),
                        reason: "invalid reflexivity-declaration journal",
                    },
                })
        };
        let (inherited, inherited_backward) = defeq(base, meter)?;
        let (strict, backward) = defeq(checked, meter)?;
        for tagged in &strict {
            meter.work(1)?;
            if !inherited.contains(tagged) {
                if base.contains(tagged) {
                    return Err(SourceModuleCheckError::Extension {
                        module: name.clone(),
                        extension: fln_elab::source::scope::simp::defeq::journal_name(),
                        reason: "a module cannot tag an imported reflexivity theorem",
                    });
                }
                metadata.defeq.push(tagged.clone());
            }
        }
        for tagged in backward.difference(&strict) {
            meter.work(1)?;
            if !inherited_backward.contains(tagged) {
                if base.contains(tagged) {
                    return Err(SourceModuleCheckError::Extension {
                        module: name.clone(),
                        extension: fln_elab::source::scope::simp::defeq::journal_name(),
                        reason: "a module cannot tag an imported backward-reflexivity theorem",
                    });
                }
                metadata.backward_defeq.push(tagged.clone());
            }
        }
        let remaining = meter.limits.max_work.saturating_sub(meter.work);
        let aliases = fln_elab::aliases::export::registrations(base, checked, remaining).map_err(
            |error| match error {
                fln_elab::aliases::AliasError::Limit => SourceModuleCheckError::Limit {
                    resource: "module work",
                    limit: meter.limits.max_work,
                },
                _ => SourceModuleCheckError::Extension {
                    module: name.clone(),
                    extension: fln_elab::aliases::export::journal_name(),
                    reason: "invalid alias metadata export",
                },
            },
        )?;
        meter.work(aliases.work)?;
        meter.bytes(aliases.bytes_examined)?;
        metadata
            .aliases
            .extend(aliases.entries.into_iter().map(|(alias, declaration)| {
                fln_olean::source_extensions::AliasEntry { alias, declaration }
            }));
        let remaining = meter.limits.max_work.saturating_sub(meter.work);
        let namespaces =
            fln_elab::namespaces::registrations(base, checked, remaining).map_err(|error| {
                match error {
                    fln_elab::instances::InstanceRegistryError::Limit => {
                        SourceModuleCheckError::Limit {
                            resource: "module work",
                            limit: meter.limits.max_work,
                        }
                    }
                    _ => SourceModuleCheckError::Extension {
                        module: name.clone(),
                        extension: fln_elab::namespaces::journal_name(),
                        reason: "invalid namespace metadata export",
                    },
                }
            })?;
        meter.work(namespaces.work)?;
        meter.bytes(namespaces.bytes_examined)?;
        metadata.namespaces.extend(namespaces.names);
        let remaining = meter.limits.max_work.saturating_sub(meter.work);
        let structures = fln_elab::records::imported::export::registrations(
            base, checked, remaining,
        )
        .map_err(|error| match error {
            fln_elab::records::RecordError::ResourceLimit => SourceModuleCheckError::Limit {
                resource: "module work",
                limit: meter.limits.max_work,
            },
            _ => SourceModuleCheckError::Extension {
                module: name.clone(),
                extension: fln_elab::records::imported::export::journal_name(),
                reason: "invalid structure interface metadata export",
            },
        })?;
        meter.work(structures.work)?;
        meter.bytes(structures.bytes_examined)?;
        for row in structures.structures {
            meter.work(1 + row.fields.len() + row.parents.len())?;
            metadata
                .structures
                .push(fln_olean::source_extensions::StructureEntry {
                    name: row.name,
                    fields: row
                        .fields
                        .into_iter()
                        .map(|field| fln_olean::source_extensions::StructureField {
                            name: field.name,
                            projection: field.projection,
                            subobject: field.subobject,
                            binder_info: field.binder_info,
                            auto_param: None,
                        })
                        .collect(),
                    parents: row
                        .parents
                        .into_iter()
                        .map(|parent| fln_olean::source_extensions::StructureParent {
                            name: parent.name,
                            subobject: parent.subobject,
                            projection: parent.projection,
                        })
                        .collect(),
                });
        }
        // Compiler data caches belong to the declaration's defining module,
        // just like the pin's compileInductives entries. Project only constants
        // in this independently checked public/private view; imported or sibling
        // declarations never acquire local layout ownership here.
        for constant in &constants {
            if let ConstantInfo::Induct(inductive) = constant
                && let Some(data) = CompilerData::from_inductive(
                    inductive,
                    |name| checked.find(name),
                    |work| meter.work(work),
                )?
            {
                metadata.compiler_data.push(data);
            }
        }
        Ok(Self {
            name: name.clone(),
            imports,
            constants,
            metadata,
        })
    }

    fn encode(
        &self,
        is_module: bool,
        base_addr: u64,
        budget: OleanWriteBudget,
        compiler_signatures: &[CompilerSignature],
    ) -> Result<fln_olean::write::EncodedModule, SourceModuleBuildError> {
        let metadata = if compiler_signatures.is_empty() {
            None
        } else {
            let mut metadata = self.metadata.clone();
            metadata.compiler_signatures = compiler_signatures.to_vec();
            Some(metadata)
        };
        let extra_names: Vec<_> = if compiler_signatures.is_empty() {
            Vec::new()
        } else {
            let declared: BTreeSet<_> = self.constants.iter().map(ConstantInfo::name).collect();
            compiler_signatures
                .iter()
                .filter(|signature| !declared.contains(&signature.name))
                .map(|signature| signature.name.clone())
                .collect()
        };
        let encoded = encode_module_with_source_metadata(
            OleanModuleWriteInput {
                is_module,
                imports: &self.imports,
                constants: &self.constants,
                extra_const_names: &extra_names,
            },
            metadata.as_ref().unwrap_or(&self.metadata),
            OleanWriteHeader {
                version: OLEAN_ACCEPTED_VERSIONS[0],
                flags: 1,
                lean_version: OLEAN_PIN_TAG.strip_prefix('v').unwrap_or(OLEAN_PIN_TAG),
                githash: OLEAN_PIN_COMMIT,
                base_addr,
            },
            budget,
        )
        .map_err(|error| SourceModuleBuildError::Encode {
            module: self.name.clone(),
            error,
        })?;
        Ok(encoded)
    }
}

impl PendingArtifact {
    pub(super) fn capture(
        name: &Name,
        header: &SourceHeader,
        base: &Environment,
        checked: &Engine,
        public: Option<(&Environment, &Environment)>,
        options: &KVMap,
        meter: &mut Meter,
    ) -> Result<Self, SourceModuleCheckError> {
        let (public, private) = match (header.module_system, public) {
            (false, None) => (
                ArtifactData::capture(name, header, base, checked.environment(), meter)?,
                None,
            ),
            (true, Some((public_base, public_checked))) => (
                ArtifactData::capture(name, header, public_base, public_checked, meter)?,
                Some(ArtifactData::capture(
                    name,
                    header,
                    base,
                    checked.environment(),
                    meter,
                )?),
            ),
            _ => {
                return Err(SourceModuleCheckError::ImportContext {
                    module: name.clone(),
                    reason: "module artifact capture has no matching checked public world",
                });
            }
        };
        let public = Arc::new(public);
        let private = private.map(Arc::new);
        let implementation = private.as_ref().unwrap_or(&public);
        let compiler = Arc::new(ir::CompilerInput {
            engine: checked.clone(),
            options: options.clone(),
            name: name.clone(),
            is_module: header.module_system,
            imports: implementation.imports.clone(),
            constants: implementation.constants.clone(),
            public: Arc::clone(&public),
            private: private.as_ref().map(Arc::clone),
        });
        Ok(Self {
            public,
            private,
            compiler,
        })
    }

    pub(super) fn encode(
        &self,
        budget: OleanWriteBudget,
    ) -> Result<SourceModuleArtifact, SourceModuleBuildError> {
        self.encode_with_compiler_signatures(budget, &[], &[])
    }

    pub(super) fn encode_with_compiler_signatures(
        &self,
        mut budget: OleanWriteBudget,
        public_signatures: &[CompilerSignature],
        private_signatures: &[CompilerSignature],
    ) -> Result<SourceModuleArtifact, SourceModuleBuildError> {
        let is_module = self.private.is_some();
        // Native placement policy for self-contained companion regions. Keep
        // their compacted addresses above local file offsets and disjoint.
        // This chooses valid regions; it does not claim the pin's byte layout.
        let mut base = if is_module {
            1u64 << 40
        } else {
            (OLEAN_REGION_ALIGN as u64) * 2
        };
        let public = self
            .public
            .encode(is_module, base, budget, public_signatures)?;
        let companions = if let Some(private) = &self.private {
            let spend = |budget: &mut OleanWriteBudget,
                         base: &mut u64,
                         report: OleanModuleWriteReport|
             -> Result<(), SourceModuleBuildError> {
                budget.max_bytes -= report.file_bytes;
                budget.max_objects -= report.runtime_objects;
                *base = base
                    .checked_add(report.file_bytes)
                    .and_then(|end| end.checked_add(OLEAN_REGION_ALIGN as u64 - 1))
                    .map(|end| end & !(OLEAN_REGION_ALIGN as u64 - 1))
                    .ok_or_else(|| SourceModuleBuildError::Encode {
                        module: self.public.name.clone(),
                        error: OleanWriteError::Contract {
                            what: "module companion address space overflows",
                        },
                    })?;
                Ok(())
            };
            spend(&mut budget, &mut base, public.report)?;
            let server = self.public.encode(true, base, budget, public_signatures)?;
            spend(&mut budget, &mut base, server.report)?;
            let private = private.encode(true, base, budget, private_signatures)?;
            Some(SourceModuleCompanions {
                server: server.bytes,
                private: private.bytes,
                server_report: server.report,
                private_report: private.report,
            })
        } else {
            None
        };
        Ok(SourceModuleArtifact {
            name: self.public.name.clone(),
            bytes: public.bytes,
            report: public.report,
            companions,
            compiler: Arc::clone(&self.compiler),
        })
    }
}

impl Engine {
    /// Check and encode an ordinary source module closure as separate `.olean`
    /// products. The caller supplies an empty engine or the exact independently
    /// rechecked external import closure; no source seed is silently installed.
    /// Unlike the explicit-environment check API, this applies Lean's implicit
    /// `Init` dependency to every header without `prelude`.
    ///
    /// Both kernel engines must accept the complete graph before any encoded
    /// products are returned. Native extension effects are refused until their
    /// pinned serialization exists; they are never silently dropped.
    /// Module-system headers retain their separate public/server/private regions.
    /// Runtime/native code artifacts and filesystem publication are separate
    /// facets. Writer limits cover every companion, supporting object and header.
    pub fn compile_source_modules(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceModuleCheckLimits,
        write_budget: OleanWriteBudget,
    ) -> Result<Outcome<SourceModuleBuild>, SourceModuleBuildError> {
        validate_base(self, modules)?;
        let run = match cache::run_collecting(
            self,
            modules,
            entry,
            options,
            limits,
            None,
            cache::RunOptions {
                cache: None,
                collect_artifacts: true,
                implicit_init: true,
                contexts: None,
                records: None,
                macros: None,
            },
        )
        .map_err(SourceModuleBuildError::Check)?
        {
            Outcome::Complete(run) => run,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        finish(run, write_budget).map(Outcome::Complete)
    }
}

pub(super) fn finish(
    run: cache::Run,
    write_budget: OleanWriteBudget,
) -> Result<SourceModuleBuild, SourceModuleBuildError> {
    let mut remaining = write_budget;
    let mut artifacts = Vec::new();
    for pending in run.artifacts {
        let artifact = pending.encode(remaining)?;
        remaining.max_bytes -= artifact.report.file_bytes;
        remaining.max_objects -= artifact.report.runtime_objects;
        if let Some(companions) = &artifact.companions {
            remaining.max_bytes -=
                companions.server_report.file_bytes + companions.private_report.file_bytes;
            remaining.max_objects -= companions.server_report.runtime_objects
                + companions.private_report.runtime_objects;
        }
        artifacts.push(artifact);
    }
    Ok(SourceModuleBuild {
        checked: run.result.checked,
        artifacts,
        reused_modules: run.result.reused_modules,
        elaborated_modules: run.result.elaborated_modules,
        persisted_modules: run.persisted_modules,
        modules: run.provenance,
    })
}

/// The same authority boundary applies to cold and cached artifact builds.
pub(super) fn validate_base(
    base: &Engine,
    modules: &[SourceModuleInput<'_>],
) -> Result<(), SourceModuleBuildError> {
    if base.environment() != &Environment::new()
        && base.imported_environment.as_ref() != Some(base.environment())
    {
        return Err(SourceModuleBuildError::UnboundBase);
    }
    for module in modules {
        if base.imported_modules().contains(module.name) {
            return Err(SourceModuleBuildError::Check(
                SourceModuleCheckError::DuplicateModule(module.name.clone()),
            ));
        }
    }
    Ok(())
}

/// Encoding never imports persisted cache bytes. Reused, privately captured
/// declaration products obey fresh aggregate writer limits and cancellation.
/// The caller publishes its new cache only after this complete batch succeeds.
pub(super) fn encode_pending(
    pending: &[Arc<PendingArtifact>],
    mut remaining: OleanWriteBudget,
    cancellation: Option<&dyn CancellationProbe>,
) -> Result<Outcome<Vec<SourceModuleArtifact>>, SourceModuleBuildError> {
    let mut artifacts = Vec::new();
    for product in pending {
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "source-modules/before-encoding",
            )));
        }
        let artifact = product.encode(remaining)?;
        remaining.max_bytes -= artifact.report.file_bytes;
        remaining.max_objects -= artifact.report.runtime_objects;
        if let Some(companions) = &artifact.companions {
            remaining.max_bytes -=
                companions.server_report.file_bytes + companions.private_report.file_bytes;
            remaining.max_objects -= companions.server_report.runtime_objects
                + companions.private_report.runtime_objects;
        }
        artifacts.push(artifact);
    }
    if cancellation.is_some_and(CancellationProbe::is_cancelled) {
        return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
            "source-modules/before-build-publication",
        )));
    }
    Ok(Outcome::Complete(artifacts))
}

/// Extract normalized declaration-attribute tags introduced between `base` and
/// `checked` from the exact native journals used by `.olean` export.
///
/// This is read-only inspection metadata for differential comparison (bead
/// `fln-file-scale-t2-differential-5f1b`); it grants no kernel authority.
pub fn extract_native_module_attributes(
    base: &Environment,
    checked: &Environment,
) -> std::collections::BTreeMap<Name, std::collections::BTreeSet<String>> {
    use std::collections::{BTreeMap, BTreeSet};

    let mut attrs: BTreeMap<Name, BTreeSet<String>> = BTreeMap::new();
    let mut tag = |decl: Name, label: String| {
        attrs.entry(decl).or_default().insert(label);
    };
    let work = 1_000_000usize;

    if let Ok(Some((registrations, _))) =
        fln_elab::instances::export::registrations(base, checked, work)
    {
        for class in registrations.classes {
            tag(class.name.clone(), "class".to_owned());
            if !class.parameters.out_params.is_empty() {
                tag(
                    class.name.clone(),
                    format!("class:out_params={:?}", class.parameters.out_params),
                );
            }
            if !class.parameters.out_level_params.is_empty() {
                tag(
                    class.name,
                    format!(
                        "class:out_level_params={:?}",
                        class.parameters.out_level_params
                    ),
                );
            }
        }
        for instance in registrations.instances {
            tag(
                instance.declaration.clone(),
                format!("instance:priority={}", instance.priority),
            );
            if let Some(scope) = instance.scope {
                tag(
                    instance.declaration,
                    format!("instance:scope={}", scope.to_display_string()),
                );
            }
        }
    }

    if let Ok(defaults) = fln_elab::instances::defaults::registrations(base, checked, work) {
        for row in defaults.entries {
            tag(
                row.candidate.declaration,
                format!(
                    "default_instance:class={},priority={}",
                    row.class.to_display_string(),
                    row.candidate.priority
                ),
            );
        }
    }

    if let Ok(simps) = fln_elab::source::scope::simp::export::registrations(base, checked, work) {
        use fln_elab::source::scope::simp::export::Kind;
        for row in simps.entries {
            match row {
                Kind::Unfold(decl) => tag(decl, "simp:unfold".to_owned()),
                Kind::UnfoldTheorems { declaration, .. } => {
                    tag(declaration, "simp:unfold_theorems".to_owned());
                }
                Kind::Theorem(theorem) => {
                    tag(
                        theorem.origin,
                        format!("simp:theorem:priority={}", theorem.priority),
                    );
                }
            }
        }
    }

    if let Ok(exported) = fln_elab::reducibility::export::statuses(base, checked, work) {
        let status_label = |status: fln_elab::reducibility::Reducibility| match status {
            fln_elab::reducibility::Reducibility::Reducible => "reducibility:reducible",
            fln_elab::reducibility::Reducibility::Semireducible => "reducibility:semireducible",
            fln_elab::reducibility::Reducibility::Irreducible => "reducibility:irreducible",
            fln_elab::reducibility::Reducibility::ImplicitReducible => {
                "reducibility:implicit_reducible"
            }
        };
        let mut explicit = BTreeSet::new();
        for declaration in exported.default_semireducible {
            explicit.insert(declaration);
        }
        for row in exported.owned {
            explicit.insert(row.declaration.clone());
            tag(row.declaration, status_label(row.status).to_owned());
        }
        for row in exported.imported {
            tag(
                row.declaration,
                format!("extra:{}", status_label(row.status)),
            );
        }
        if let Ok(Some((registrations, _))) =
            fln_elab::instances::export::registrations(base, checked, work)
        {
            for instance in registrations.instances {
                if !base.contains(&instance.declaration)
                    && explicit.insert(instance.declaration.clone())
                {
                    tag(
                        instance.declaration,
                        "reducibility:implicit_reducible".to_owned(),
                    );
                }
            }
        }
    }

    if let (Ok(inherited), Ok(current)) = (
        fln_elab::protected_names::ProtectedNames::read(base),
        fln_elab::protected_names::ProtectedNames::read(checked),
    ) {
        for name in current.iter() {
            if !inherited.contains(name) {
                tag(name.clone(), "protected".to_owned());
            }
        }
    }

    if let (Ok(inherited), Ok(current)) = (
        fln_elab::deprecations::Deprecations::read(base),
        fln_elab::deprecations::Deprecations::read(checked),
    ) {
        for row in current.iter() {
            if inherited.get(&row.declaration).is_none() {
                tag(row.declaration.clone(), "deprecated".to_owned());
            }
        }
    }

    if let (Ok(inherited), Ok(current)) = (
        fln_elab::aux_recursors::AuxRecursors::read(base),
        fln_elab::aux_recursors::AuxRecursors::read(checked),
    ) {
        for name in current.iter() {
            if !inherited.contains(name) {
                tag(name.clone(), "aux_recursor".to_owned());
            }
        }
    }

    if let (Ok(inherited), Ok(current)) = (
        fln_elab::noncomputable::read(base),
        fln_elab::noncomputable::read(checked),
    ) {
        for name in current {
            if !inherited.contains(&name) {
                tag(name, "noncomputable".to_owned());
            }
        }
    }

    if let (Ok(inherited), Ok(current)) =
        (fln_elab::unbox::read(base), fln_elab::unbox::read(checked))
    {
        for name in current {
            if !inherited.contains(&name) {
                tag(name, "unbox".to_owned());
            }
        }
    }

    if let (Ok(inherited), Ok(current)) = (
        fln_elab::never_extract::read(base),
        fln_elab::never_extract::read(checked),
    ) {
        for name in current {
            if !inherited.contains(&name) {
                tag(name, "never_extract".to_owned());
            }
        }
    }

    if let (Ok(inherited), Ok(current)) = (
        fln_elab::match_pattern::read(base),
        fln_elab::match_pattern::read(checked),
    ) {
        for name in current {
            if !inherited.contains(&name) {
                tag(name, "match_pattern".to_owned());
            }
        }
    }

    if let (Ok(inherited), Ok(current)) =
        (fln_elab::symm::read(base), fln_elab::symm::read(checked))
        && current.starts_with(&inherited)
    {
        for entry in current.into_iter().skip(inherited.len()) {
            tag(entry.lemma.declaration, "symm".to_owned());
        }
    }

    if let (Ok(inherited), Ok(current)) = (
        fln_elab::delaborator_tags::coercions::read(base),
        fln_elab::delaborator_tags::coercions::read(checked),
    ) && current.starts_with(&inherited)
    {
        use fln_elab::delaborator_tags::CoeFnKind;
        for (decl, info) in current.into_iter().skip(inherited.len()) {
            let kind = match info.kind {
                CoeFnKind::Coe => "coe",
                CoeFnKind::CoeFun => "coe_fun",
                CoeFnKind::CoeSort => "coe_sort",
            };
            tag(
                decl,
                format!("coe:{kind}:{}:{}", info.num_args, info.coercee),
            );
        }
    }

    if let Ok(Some(inline)) = fln_elab::macro_inline::export::registrations(base, checked, work) {
        for decl in inline.declarations {
            tag(decl, "inline:macro_inline".to_owned());
        }
    }

    if let Ok(structures) = fln_elab::records::imported::export::registrations(base, checked, work)
    {
        for row in structures.structures {
            tag(row.name, "structure".to_owned());
        }
    }

    attrs
}
