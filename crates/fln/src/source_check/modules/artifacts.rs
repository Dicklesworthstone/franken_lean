//! Per-module, checked declaration products for the native Lake `.olean` facet.
use super::*;
use fln_olean::write::source::{SourceMetadata, encode_module_with_source_metadata};
use std::sync::Arc;

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

/// One basic (pre-module-system) `.olean`, containing only its own constants.
#[derive(Debug)]
pub struct SourceModuleArtifact {
    pub name: Name,
    pub bytes: Vec<u8>,
    pub report: OleanModuleWriteReport,
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

impl PendingArtifact {
    pub(super) fn capture(
        name: &Name,
        header: &SourceHeader,
        base: &Environment,
        checked: &Environment,
        meter: &mut Meter,
    ) -> Result<Self, SourceModuleCheckError> {
        if header.module_system {
            return Err(SourceModuleCheckError::ImportContext {
                module: name.clone(),
                reason: "module-system .olean emission requires public/private split artifacts",
            });
        }
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
            imports.push(OleanModuleImport {
                module: module.clone(),
                import_all: false,
                is_exported: true,
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
                        reason: "simp export requires supported equality proofs or reducible definitions; equation theorem generation, erasures and imported proof re-registration are unsupported",
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
        let (statuses, work) = exported.ok_or_else(|| SourceModuleCheckError::Extension {
            module: name.clone(),
            extension: fln_elab::reducibility::export::journal_name(),
            reason: "imported-declaration reducibility overrides require a reducibilityExtra serializer",
        })?;
        meter.work(work)?;
        let mut explicit_statuses = std::collections::BTreeSet::new();
        for row in statuses {
            use fln_elab::reducibility::Reducibility;
            use fln_olean::source_extensions::{ReducibilityEntry, ReducibilityStatus};
            meter.work(1)?;
            explicit_statuses.insert(row.declaration.clone());
            metadata.reducibility.push(ReducibilityEntry {
                declaration: row.declaration,
                status: match row.status {
                    Reducibility::Reducible => ReducibilityStatus::Reducible,
                    Reducibility::Semireducible => ReducibilityStatus::Semireducible,
                    Reducibility::Irreducible => ReducibilityStatus::Irreducible,
                    Reducibility::ImplicitReducible => ReducibilityStatus::ImplicitReducible,
                },
            });
        }
        // Native instances have this default in ReducibilityTable::effective.
        // Once imported, their status must come from reducibilityCore instead;
        // an explicit owned status always wins, including later overrides.
        for instance in &metadata.instances {
            meter.work(1)?;
            if explicit_statuses.insert(instance.declaration.clone()) {
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
        // Reflexivity tags are selection metadata owned by the module that
        // declared the theorem. The codec already emits both pinned tag sets;
        // export the journal delta rather than silently losing it at this edge.
        let defeq = |env: &Environment, meter: &mut Meter| {
            use fln_elab::source::scope::simp::{SimpSetError, defeq};
            if let Some(journal) = env.extension(&defeq::journal_name()) {
                for entry in journal.entries() {
                    meter.work(1 + entry.payload.len().div_ceil(64))?;
                    meter.bytes(entry.payload.len())?;
                }
            }
            defeq::read(env, || Ok(())).map_err(|error| match error {
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
        let inherited = defeq(base, meter)?;
        for tagged in defeq(checked, meter)? {
            meter.work(1)?;
            if !inherited.contains(&tagged) {
                if base.contains(&tagged) {
                    return Err(SourceModuleCheckError::Extension {
                        module: name.clone(),
                        extension: fln_elab::source::scope::simp::defeq::journal_name(),
                        reason: "a module cannot tag an imported reflexivity theorem",
                    });
                }
                metadata.defeq.push(tagged);
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
        Ok(Self {
            name: name.clone(),
            imports,
            constants,
            metadata,
        })
    }

    pub(super) fn encode(
        &self,
        budget: OleanWriteBudget,
    ) -> Result<SourceModuleArtifact, SourceModuleBuildError> {
        let encoded = encode_module_with_source_metadata(
            OleanModuleWriteInput {
                is_module: false,
                imports: &self.imports,
                constants: &self.constants,
                extra_const_names: &[],
            },
            &self.metadata,
            OleanWriteHeader {
                version: OLEAN_ACCEPTED_VERSIONS[0],
                flags: 1,
                lean_version: OLEAN_PIN_TAG.strip_prefix('v').unwrap_or(OLEAN_PIN_TAG),
                githash: OLEAN_PIN_COMMIT,
                base_addr: (OLEAN_REGION_ALIGN as u64) * 2,
            },
            budget,
        )
        .map_err(|error| SourceModuleBuildError::Encode {
            module: self.name.clone(),
            error,
        })?;
        Ok(SourceModuleArtifact {
            name: self.name.clone(),
            bytes: encoded.bytes,
            report: encoded.report,
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
    /// pinned serialization exists; they are never silently dropped. New
    /// `module` headers, runtime/native code artifacts and filesystem publication
    /// are outside this basic `.olean` facet. Writer limits are aggregate across
    /// the closure, including supporting objects and file headers.
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
                contexts: None,
                records: None,
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
        artifacts.push(artifact);
    }
    if cancellation.is_some_and(CancellationProbe::is_cancelled) {
        return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
            "source-modules/before-build-publication",
        )));
    }
    Ok(Outcome::Complete(artifacts))
}
