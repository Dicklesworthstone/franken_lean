//! Import the supported source-language metadata from the very artifacts whose
//! declarations passed the ordinary council. No Reference initializer executes.
//!
//! Checking order and extension replay order are distinct: equal-priority
//! instances must follow the roots' declared import order, not a sorted file
//! inventory. Companion journals are cumulative; only the final private part is
//! replayed. Unknown extensions are reported, not treated as understood.
use crate::*;
use fln_elab::instances::{self, InstanceRegistryError};
use fln_olean::region::{OleanView, OpaqueExtensionBlock};
use fln_olean::source_extensions::{self as metadata, DecodeLimits};
use std::collections::{BTreeMap, BTreeSet, HashSet};
#[path = "imported/implemented_by.rs"]
mod implemented_by;
mod simp;
#[path = "imported/structures.rs"]
mod structures;

#[derive(Default)]
struct ReflexivityTags {
    payloads: BTreeMap<Vec<u8>, Name>,
    names: BTreeSet<Name>,
    declarations: Vec<Name>,
}

impl ReflexivityTags {
    fn capture(
        &mut self,
        module: &Name,
        extension: &Name,
        entries: Vec<Vec<u8>>,
        remaining: &mut DecodeLimits,
    ) -> Result<usize> {
        let before = self.declarations.len();
        let mut local = BTreeSet::new();
        for payload in entries {
            let declaration = if let Some(declaration) = self.payloads.get(&payload) {
                declaration.clone()
            } else {
                let mut block = OpaqueExtensionBlock {
                    name: extension.clone(),
                    entries: vec![payload],
                };
                let (decoded, rest) = metadata::decode_with_remaining_limits(
                    std::slice::from_ref(&block),
                    *remaining,
                )
                .map_err(SourceOleanImportError::Decode)?;
                let mut names = decoded.defeq.into_iter().chain(decoded.backward_defeq);
                let declaration = names.next().ok_or(SourceOleanImportError::Internal(
                    "a reflexivity entry did not decode to a name",
                ))?;
                if names.next().is_some() {
                    return Err(SourceOleanImportError::Internal(
                        "a reflexivity entry decoded to several names",
                    ));
                }
                *remaining = rest;
                let payload = block.entries.pop().ok_or(SourceOleanImportError::Internal(
                    "a decoded reflexivity payload disappeared",
                ))?;
                self.payloads.insert(payload, declaration.clone());
                declaration
            };
            if !local.insert(declaration.clone()) {
                return Err(SourceOleanImportError::Metadata {
                    module: module.clone(),
                    declaration,
                    reason: "duplicate reflexivity tag in one module",
                });
            }
            if self.names.insert(declaration.clone()) {
                self.declarations.push(declaration);
            }
        }
        Ok(self.declarations.len() - before)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct SourceOleanImportLimits {
    pub check: OleanCheckLimits,
    /// Aggregate selected metadata bytes, objects, entries and indices.
    pub metadata: DecodeLimits,
    /// Object traversal bound for each module's extension capture.
    pub capture: OleanWalkBudget,
    /// Aggregate captured bytes, including uninterpreted extensions.
    pub max_capture_bytes: usize,
    pub max_roots: usize,
    /// How many closure modules the council checks at once. The import is the
    /// same at every count ([`Engine::check_olean_modules_scheduled`]); only its
    /// wall time depends on it.
    pub jobs: OleanFrontierJobs,
    /// How many threads run the import's work that is not a council: decoding
    /// the closure and measuring its declarations when a `reuse-verified` record
    /// is re-proved, and capturing each module's extension payloads. Each piece
    /// reads only bytes the caller supplied, and the import is the same at every
    /// count, so a caller may allow more here than council workers.
    pub read_jobs: OleanFrontierJobs,
}
impl SourceOleanImportLimits {
    /// Capture may use as many bytes as the caller allows the artifacts
    /// themselves, never fewer than 64 MiB. The pinned `Init` closure (601
    /// modules, 350 MiB of `.olean` parts) captures 300 MiB of extension
    /// payloads, so a fixed 64 MiB made `import Init` a resource refusal.
    /// Modules are checked one at a time on the calling thread unless the
    /// caller sets `jobs`.
    pub fn new(check: OleanCheckLimits) -> Self {
        Self {
            check,
            // Restore the allowance for the selected simp index cells, as in
            // fln-simp-default-set-a4nb's pinned Init measurement (96,786 cells).
            // Byte, object, entry and instance-key limits remain independent.
            metadata: DecodeLimits {
                max_indices: 1 << 17,
                ..DecodeLimits::default()
            },
            capture: OleanWalkBudget::default(),
            max_capture_bytes: check.max_total_bytes.max(64 * 1024 * 1024),
            max_roots: 256,
            jobs: OleanFrontierJobs::SERIAL,
            read_jobs: OleanFrontierJobs::SERIAL,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceMetadataReport {
    pub module: Name,
    pub classes: usize,
    pub instances: usize,
    pub defaults: usize,
    pub scoped_instances: usize,
    /// `export` aliases (the pin's `aliasExtension`), activated for name resolution.
    pub aliases: usize,
    /// Explicit namespace registrations, independent of aliases.
    pub namespaces: usize,
    /// `protected` declarations (the pin's `protectedExt`), activated so that an
    /// atomic identifier does not resolve to one.
    pub protected: usize,
    /// Internal auxiliary-recursion tags (the pin's `auxRecExt`), activated
    /// only for this module's own admitted definitions.
    pub aux_recursors: usize,
    /// Compilation restrictions owned by this module, including partial companions.
    pub noncomputable: usize,
    /// `@[defeq]` tags (the pin's `Lean.defeqAttr`), which select `dsimp`'s rfl lemmas.
    pub defeq: usize,
    /// Backward-definitional tags, retained independently so an imported
    /// semireducible equation lemma never becomes a strict `dsimp` rule.
    pub backward_defeq: usize,
    /// Original structure fields and direct-parent metadata, validated against
    /// this module's checked constructor and projection interfaces.
    pub structures: usize,
    /// Reducibility statuses (the pin's `reducibilityCore`), activated for the
    /// `instances` transparency instance selection runs at.
    pub reducibility: usize,
    /// Explicit native-call intentions (the pin's `Lean.externAttr`), retained
    /// only for this module's own admitted declarations.
    pub externs: usize,
    /// Compatible executable replacements, bound to this module's own checked
    /// declarations and to targets in its actual import closure.
    pub implemented_by: usize,
    /// Inlining attributes (the pin's `inlineAttrs`). Only the `macro_inline` ones,
    /// which change what code computes, are recorded, for this module's own definitions.
    pub inline: usize,
    /// Ordered initialization entries retained for executable-body classification.
    /// No initialization action is executed by importing metadata.
    pub regular_initializers: usize,
    pub builtin_initializers: usize,
    /// Decoded default simp entries, including explicitly deferred forms.
    pub simps: usize,
    /// Supported global forward post-phase entries replayed natively.
    pub activated_simps: usize,
    /// The pin's delaborator tags on this module's own declarations
    /// (`pp_using_anonymous_constructor`, `pp_nodot`), and its `app_unexpander`
    /// registrations, which the printer reads.
    pub pp_anonymous_constructor: usize,
    pub pp_nodot: usize,
    pub app_unexpanders: usize,
    /// `@[deprecated]` entries on this module's own declarations (the pin's `deprecatedAttr`),
    /// which name resolution reports from.
    pub deprecations: usize,
    /// Unsupported scope, phase or proof forms; also named in `uninterpreted`.
    pub deferred_simps: usize,
    pub uninterpreted: Vec<Name>,
}

#[derive(Debug)]
pub struct SourceOleanImport {
    pub(super) contexts: super::contexts::ImportContexts,
    /// The metadata-enabled successor. Both checker projections and import
    /// identities are retained; metadata itself grants no declaration authority.
    pub engine: Engine,
    /// Unmodified declaration-checking records and their original roots.
    pub checked: CheckedOleanSet,
    /// Root after native metadata replay, distinct from the checking-only root.
    pub result_logical_root: LogicalRoot,
    /// Actual dependency-first metadata replay order.
    pub modules: Vec<SourceMetadataReport>,
}

#[derive(Debug)]
pub enum SourceOleanImportError {
    Check(Box<OleanCheckError>),
    EmptyRoots,
    MissingRoot(Name),
    UnreachableModule(Name),
    Limit(&'static str),
    Capture {
        module: Name,
        error: OleanRegionError,
    },
    Decode(metadata::DecodeError),
    Registry {
        module: Name,
        declaration: Name,
        error: InstanceRegistryError,
    },
    Metadata {
        module: Name,
        declaration: Name,
        reason: &'static str,
    },
    Internal(&'static str),
}
impl std::fmt::Display for SourceOleanImportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Check(error) => error.fmt(f),
            Self::EmptyRoots => f.write_str("source import requires at least one root module"),
            Self::MissingRoot(name) => {
                write!(f, "missing source import root {}", name.to_display_string())
            }
            Self::UnreachableModule(name) => write!(
                f,
                "module {} is outside the source import closure",
                name.to_display_string()
            ),
            Self::Limit(resource) => write!(f, "source import exceeded {resource}"),
            Self::Capture { module, error } => write!(
                f,
                "module {} metadata capture: {error}",
                module.to_display_string()
            ),
            Self::Decode(error) => error.fmt(f),
            Self::Registry {
                module,
                declaration,
                error,
            } => write!(
                f,
                "module {} metadata for {}: {error}",
                module.to_display_string(),
                declaration.to_display_string()
            ),
            Self::Metadata {
                module,
                declaration,
                reason,
            } => write!(
                f,
                "module {} metadata for {}: {reason}",
                module.to_display_string(),
                declaration.to_display_string()
            ),
            Self::Internal(reason) => write!(f, "source import invariant: {reason}"),
        }
    }
}
impl std::error::Error for SourceOleanImportError {}
impl SourceOleanImportError {
    /// Metadata resource stops are nonanswers, not evidence of malformed input.
    /// `Check` retains its own declaration-checking disposition separately.
    pub fn metadata_resource_exhausted(&self) -> bool {
        match self {
            Self::Limit(_)
            | Self::Registry {
                error: InstanceRegistryError::Limit,
                ..
            }
            | Self::Capture {
                error:
                    OleanRegionError::BudgetExhausted { .. }
                    | OleanRegionError::PayloadBudgetExhausted { .. },
                ..
            } => true,
            Self::Decode(error) => error.is_resource(),
            _ => false,
        }
    }
}

type Result<T> = std::result::Result<T, SourceOleanImportError>;

impl Engine {
    /// Recheck a complete artifact closure, then activate its native class,
    /// instance and default-instance journals. Roots are in source import order.
    /// No partially checked or partially activated successor is ever returned.
    ///
    /// This is the supported metadata subset, not general Lean import parity:
    /// unrecognized nonempty extensions are named in `modules[].uninterpreted`.
    /// Scoped registrations are retained but remain inactive, as on import.
    pub fn import_olean_modules_for_source(
        &self,
        modules: &[OleanModuleInput<'_>],
        roots: &[Name],
        options: &KVMap,
        limits: SourceOleanImportLimits,
    ) -> Result<Outcome<SourceOleanImport>> {
        self.import_olean_modules_for_source_with_cancel(modules, roots, options, limits, None)
    }

    /// Checks cancellation before the council, between capture/replay steps and
    /// before publication, and, when [`Engine::check_olean_modules_scheduled`]
    /// schedules the council (`limits.jobs` above one, empty base), also as each
    /// closure module is decided. A module's council is not interrupted mid-call.
    pub fn import_olean_modules_for_source_with_cancel(
        &self,
        modules: &[OleanModuleInput<'_>],
        roots: &[Name],
        options: &KVMap,
        limits: SourceOleanImportLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<SourceOleanImport>> {
        if roots.is_empty() {
            return Err(SourceOleanImportError::EmptyRoots);
        }
        if roots.len() > limits.max_roots {
            return Err(SourceOleanImportError::Limit("import roots"));
        }
        macro_rules! cancelled {
            ($at:literal) => {
                if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                    return Ok(Outcome::Inconclusive(Inconclusive::cancelled($at)));
                }
            };
        }
        cancelled!("source-olean/before-council");
        let checked = match self
            .check_olean_modules_scheduled(
                modules,
                options,
                limits.check,
                limits.jobs,
                cancellation,
            )
            .map_err(|e| SourceOleanImportError::Check(Box::new(e)))?
        {
            Outcome::Complete(checked) => checked,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        self.activate_source_metadata(checked, modules, roots, options, limits, cancellation)
    }

    /// Activate the native class, instance and default-instance journals of a
    /// checked closure, in the roots' import order. Both import postures end
    /// here: `recheck` with the set the council just admitted, `reuse-verified`
    /// ([`super::reuse`]) with the set it rebuilt and proved identical by root.
    /// Metadata grants no declaration authority either way.
    pub(super) fn activate_source_metadata(
        &self,
        checked: CheckedOleanSet,
        modules: &[OleanModuleInput<'_>],
        roots: &[Name],
        options: &KVMap,
        limits: SourceOleanImportLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<SourceOleanImport>> {
        self.activate_source_metadata_with::<instances::imported::ImportActivation>(
            checked,
            modules,
            roots,
            options,
            limits,
            cancellation,
        )
    }

    /// [`Self::activate_source_metadata`] with the registrations made by `R`.
    fn activate_source_metadata_with<R: Registrar>(
        &self,
        checked: CheckedOleanSet,
        modules: &[OleanModuleInput<'_>],
        roots: &[Name],
        options: &KVMap,
        limits: SourceOleanImportLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<SourceOleanImport>> {
        macro_rules! cancelled {
            ($at:literal) => {
                if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                    return Ok(Outcome::Inconclusive(Inconclusive::cancelled($at)));
                }
            };
        }
        let order = replay_order(&checked, roots)?;
        let inputs: BTreeMap<_, _> = modules.iter().map(|m| (m.name, m)).collect();
        let selected = [
            metadata::CLASS_EXTENSION,
            metadata::INSTANCE_EXTENSION,
            metadata::DEFAULT_EXTENSION,
            metadata::ALIAS_EXTENSION,
            metadata::PROTECTED_EXTENSION,
            metadata::REDUCIBILITY_EXTENSION,
            metadata::EXTERN_EXTENSION,
            metadata::IMPLEMENTED_BY_EXTENSION,
            metadata::AUX_RECURSOR_EXTENSION,
            fln_olean::initializers::REGULAR_INIT_EXTENSION,
            fln_olean::initializers::BUILTIN_INIT_EXTENSION,
        ]
        .map(|name| Name::from_components(name.split('.')));
        let selected: Vec<_> = selected
            .into_iter()
            .chain([
                metadata::structure_extension_name(),
                Name::from_components(metadata::NONCOMPUTABLE_EXTENSION.split('.')),
                Name::from_components(metadata::SIMP_EXTENSION.split('.')),
                Name::from_components(metadata::DEFEQ_EXTENSION.split('.')),
                Name::from_components(metadata::PP_ANONYMOUS_CONSTRUCTOR_EXTENSION.split('.')),
                Name::from_components(metadata::PP_NODOT_EXTENSION.split('.')),
                Name::from_components(metadata::APP_UNEXPANDER_EXTENSION.split('.')),
                Name::from_components(metadata::INLINE_EXTENSION.split('.')),
                metadata::namespace_extension_name(),
                Name::from_components(metadata::DEPRECATED_EXTENSION.split('.')),
                Name::from_components(metadata::BACKWARD_DEFEQ_EXTENSION.split('.')),
            ])
            .collect();
        let mut blocks: Vec<_> = selected
            .iter()
            .map(|name| OpaqueExtensionBlock {
                name: name.clone(),
                entries: Vec::new(),
            })
            .collect();
        let mut reports = Vec::new();
        let mut capture_left = limits.max_capture_bytes;
        let mut entries_left = limits.metadata.max_entries;
        let mut defeq_tags = ReflexivityTags::default();
        let mut backward_defeq_tags = ReflexivityTags::default();
        let mut metadata_remaining = limits.metadata;
        // Each module's capture reads only its own parts, so the walks run
        // `limits.read_jobs` at once; the cumulative byte allowance is charged below
        // in replay order, exactly as when one walk followed another.
        cancelled!("source-olean/capture");
        let mut captures = capture_modules(&checked, &order, &inputs, &limits).into_iter();
        for &index in &order {
            cancelled!("source-olean/capture");
            let module = &checked.modules[index];
            let captured = captures.next().ok_or(SourceOleanImportError::Internal(
                "a replayed module has no capture",
            ))??;
            let mut report = SourceMetadataReport {
                module: module.name.clone(),
                classes: 0,
                instances: 0,
                defaults: 0,
                scoped_instances: 0,
                aliases: 0,
                namespaces: 0,
                protected: 0,
                aux_recursors: 0,
                noncomputable: 0,
                defeq: 0,
                backward_defeq: 0,
                structures: 0,
                reducibility: 0,
                externs: 0,
                implemented_by: 0,
                inline: 0,
                regular_initializers: 0,
                builtin_initializers: 0,
                simps: 0,
                activated_simps: 0,
                deferred_simps: 0,
                pp_anonymous_constructor: 0,
                pp_nodot: 0,
                app_unexpanders: 0,
                deprecations: 0,
                uninterpreted: Vec::new(),
            };
            let mut seen = BTreeSet::new();
            for block in captured {
                if !seen.insert(block.name.clone()) {
                    return Err(SourceOleanImportError::Metadata {
                        module: module.name.clone(),
                        declaration: block.name,
                        reason: "duplicate extension block",
                    });
                }
                for payload in &block.entries {
                    capture_left = capture_left
                        .checked_sub(payload.len())
                        .ok_or(SourceOleanImportError::Limit("captured extension bytes"))?;
                }
                if let Some(kind) = selected.iter().position(|name| name == &block.name) {
                    let entries = block.entries;
                    if kind == 14 || kind == 21 {
                        // A realized equation can carry the same tag in several
                        // modules with different compacted object layouts. Compare
                        // decoded names, retaining the first module's registration.
                        // Cached byte-identical entries keep their old zero decode
                        // cost; a same-module name repeat still refuses.
                        let tags = if kind == 14 {
                            &mut defeq_tags
                        } else {
                            &mut backward_defeq_tags
                        };
                        let before = metadata_remaining.max_entries;
                        let count = tags.capture(
                            &module.name,
                            &block.name,
                            entries,
                            &mut metadata_remaining,
                        )?;
                        entries_left = entries_left
                            .checked_sub(before - metadata_remaining.max_entries)
                            .ok_or(SourceOleanImportError::Limit("metadata entries"))?;
                        if kind == 14 {
                            report.defeq = count;
                        } else {
                            report.backward_defeq = count;
                        }
                        continue;
                    }
                    entries_left = entries_left
                        .checked_sub(entries.len())
                        .ok_or(SourceOleanImportError::Limit("metadata entries"))?;
                    match kind {
                        0 => report.classes = entries.len(),
                        1 => report.instances = entries.len(),
                        2 => report.defaults = entries.len(),
                        3 => report.aliases = entries.len(),
                        4 => report.protected = entries.len(),
                        5 => report.reducibility = entries.len(),
                        6 => report.externs = entries.len(),
                        7 => report.implemented_by = entries.len(),
                        8 => report.aux_recursors = entries.len(),
                        9 => report.regular_initializers = entries.len(),
                        10 => report.builtin_initializers = entries.len(),
                        11 => report.structures = entries.len(),
                        12 => report.noncomputable = entries.len(),
                        13 => report.simps = entries.len(),
                        14 => report.defeq = entries.len(),
                        15 => report.pp_anonymous_constructor = entries.len(),
                        16 => report.pp_nodot = entries.len(),
                        17 => report.app_unexpanders = entries.len(),
                        18 => report.inline = entries.len(),
                        19 => report.namespaces = entries.len(),
                        20 => report.deprecations = entries.len(),
                        21 => report.backward_defeq = entries.len(),
                        _ => {
                            return Err(SourceOleanImportError::Internal(
                                "unknown selected metadata kind",
                            ));
                        }
                    }
                    // Move payloads, not copies. The remaining allowances include
                    // every tag already decoded across the module boundaries.
                    blocks[kind].entries.extend(entries);
                } else if !block.entries.is_empty() {
                    report.uninterpreted.push(block.name);
                }
            }
            reports.push(report);
        }
        cancelled!("source-olean/before-metadata-decode");
        let mut decoded = metadata::decode(&blocks, metadata_remaining)
            .map_err(SourceOleanImportError::Decode)?;
        decoded.defeq = defeq_tags.declarations;
        decoded.backward_defeq = backward_defeq_tags.declarations;
        let mut implementation_scopes = implemented_by::Scopes::new(
            &checked,
            &decoded.implemented_by,
            limits.metadata.max_objects,
        )?;
        let mut structure_scopes =
            structures::Scopes::new(&checked, &decoded.structures, limits.metadata.max_objects)?;
        let simp_rows = decoded.simps;
        let mut structure_rows = decoded.structures.into_iter();
        let mut classes = decoded.classes.into_iter();
        let mut instances = decoded.instances.into_iter();
        let mut defaults = decoded.defaults.into_iter();
        let mut aliases = decoded.aliases.into_iter();
        let mut namespaces = decoded.namespaces.into_iter();
        let mut protected = decoded.protected.into_iter();
        let mut aux_recursors = decoded.aux_recursors.into_iter();
        let mut noncomputable = decoded.noncomputable.into_iter();
        let mut defeq = decoded.defeq.into_iter();
        let mut backward_defeq = decoded.backward_defeq.into_iter();
        let mut pp_anonymous_constructor = decoded.pp_anonymous_constructor.into_iter();
        let mut pp_nodot = decoded.pp_nodot.into_iter();
        let mut app_unexpanders = decoded.app_unexpanders.into_iter();
        let mut deprecations = decoded.deprecations.into_iter();
        let mut reducibility = decoded.reducibility.into_iter();
        let mut externs = decoded.externs.into_iter();
        let mut implementations = decoded.implemented_by.into_iter();
        let mut inline = decoded.inline.into_iter();
        let mut regular_initializers = decoded.initializers.regular.into_iter();
        let mut builtin_initializers = decoded.initializers.builtin.into_iter();
        let mut engine = checked.engine.clone();
        let mut executable_opaques = (*engine.executable_opaques).clone();
        let mut runtime_initializers = (*engine.runtime_initializers).clone();
        let bound = engine.imported_environment.as_ref() == Some(&engine.environment);
        let mut journals = BTreeMap::new();
        // One activation for the whole closure: the registries are read once and
        // kept current, rather than re-read and re-validated before every row.
        let mut activation = R::new(engine.environment.clone());
        use fln_elab::source::scope::simp::defeq as reflexivity;
        let tag_module = roots.first().cloned().unwrap_or_default();
        let mut tag_work = limits.metadata.max_objects;
        let mut tick_tags = || {
            tag_work =
                tag_work
                    .checked_sub(1)
                    .ok_or(fln_elab::NatDefinitionElabError::Inference(
                        fln_elab::source::SourceInferenceError::SimpSet(
                            fln_elab::source::scope::simp::SimpSetError::Limit,
                        ),
                    ))?;
            Ok(())
        };
        let mut strict_tags = reflexivity::read(activation.environment(), &mut tick_tags)
            .map_err(|error| defeq_error(&tag_module, &reflexivity::journal_name(), error))?;
        let mut backward_tags =
            reflexivity::read_backward(activation.environment(), &mut tick_tags)
                .map_err(|error| defeq_error(&tag_module, &reflexivity::journal_name(), error))?;
        for (&index, report) in order.iter().zip(&mut reports) {
            let before = activation.environment().clone();
            if report.structures != 0 {
                cancelled!("source-olean/structure");
                let rows = match structures::module(
                    &checked,
                    &self.environment,
                    activation.environment(),
                    index,
                    report.structures,
                    &mut structure_rows,
                    &mut structure_scopes,
                    &limits,
                    cancellation,
                )? {
                    Outcome::Complete(rows) => rows,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
                activation = activation.register_structures(&rows).map_err(|problem| {
                    structures::error(&report.module, &report.module, problem)
                })?;
            }
            for _ in 0..report.classes {
                cancelled!("source-olean/class");
                let row = classes.next().ok_or(SourceOleanImportError::Internal(
                    "class count changed during decode",
                ))?;
                activation = activation
                    .register_class(
                        &row.name,
                        &instances::imported::ClassParameters {
                            out_params: row.out_params,
                            out_level_params: row.out_level_params,
                        },
                    )
                    .map_err(|error| registry_error(&report.module, &row.name, error))?;
            }
            for _ in 0..report.instances {
                cancelled!("source-olean/instance");
                let row = instances.next().ok_or(SourceOleanImportError::Internal(
                    "instance count changed during decode",
                ))?;
                let info = activation
                    .environment()
                    .find(&row.declaration)
                    .ok_or_else(|| {
                        registry_error(
                            &report.module,
                            &row.declaration,
                            InstanceRegistryError::UnknownDeclaration(row.declaration.clone()),
                        )
                    })?;
                let expected = Expr::const_(
                    row.declaration.clone(),
                    info.constant_val()
                        .level_params
                        .iter()
                        .cloned()
                        .map(Level::param)
                        .collect(),
                );
                // The native registry instantiates a declaration at fresh levels.
                // It cannot faithfully replace a specialized/reordered expression.
                if row.value != expected {
                    return Err(SourceOleanImportError::Metadata {
                        module: report.module.clone(),
                        declaration: row.declaration,
                        reason: "instance value is not its generic declaration",
                    });
                }
                report.scoped_instances += usize::from(row.scope.is_some());
                activation = activation
                    .register_instance(
                        &row.declaration,
                        &instances::imported::InstanceParameters {
                            priority: row.priority,
                            synth_order: row.synth_order,
                            scope: row.scope,
                            keys: row.keys.into_iter().map(instance_key).collect(),
                        },
                    )
                    .map_err(|error| registry_error(&report.module, &row.declaration, error))?;
            }
            for _ in 0..report.defaults {
                cancelled!("source-olean/default");
                let row = defaults.next().ok_or(SourceOleanImportError::Internal(
                    "default count changed during decode",
                ))?;
                let actual = activation
                    .environment()
                    .find(&row.declaration)
                    .and_then(|info| {
                        instances::instance_telescope(
                            activation.environment(),
                            &info.constant_val().type_,
                        )
                    })
                    .map(|(_, class)| class);
                if actual.as_ref() != Some(&row.class) {
                    return Err(SourceOleanImportError::Metadata {
                        module: report.module.clone(),
                        declaration: row.declaration,
                        reason: "default instance class does not match its checked type",
                    });
                }
                activation = activation
                    .register_default(&row.declaration, row.priority)
                    .map_err(|error| registry_error(&report.module, &row.declaration, error))?;
            }
            for _ in 0..report.aliases {
                cancelled!("source-olean/alias");
                let row = aliases.next().ok_or(SourceOleanImportError::Internal(
                    "alias count changed during decode",
                ))?;
                activation = activation
                    .register_alias(&row.alias, &row.declaration)
                    .map_err(|error| SourceOleanImportError::Metadata {
                        module: report.module.clone(),
                        declaration: row.declaration.clone(),
                        reason: match error {
                            fln_elab::aliases::AliasError::UnknownDeclaration(_) => {
                                "an export alias names no admitted declaration"
                            }
                            fln_elab::aliases::AliasError::Limit => "export alias journal limit",
                            fln_elab::aliases::AliasError::Malformed => "malformed export alias",
                        },
                    })?;
            }
            cancelled!("source-olean/namespaces");
            let names: Vec<Name> = namespaces.by_ref().take(report.namespaces).collect();
            if names.len() != report.namespaces {
                return Err(SourceOleanImportError::Internal(
                    "namespace count changed during decode",
                ));
            }
            activation = activation.register_namespaces(&names).map_err(|error| {
                registry_error(&report.module, &metadata::namespace_extension_name(), error)
            })?;
            // One module's tags, recorded together inside its own journal window.
            cancelled!("source-olean/protected");
            let tagged: Vec<Name> = protected.by_ref().take(report.protected).collect();
            if tagged.len() != report.protected {
                return Err(SourceOleanImportError::Internal(
                    "protected count changed during decode",
                ));
            }
            activation = activation.register_protected(&tagged).map_err(|error| {
                let (declaration, reason) = match error {
                    fln_elab::protected_names::ProtectedError::UnknownDeclaration(name) => {
                        (name, "a protected tag names no admitted declaration")
                    }
                    fln_elab::protected_names::ProtectedError::Duplicate(name) => {
                        (name, "a declaration is tagged protected twice")
                    }
                    fln_elab::protected_names::ProtectedError::Limit => {
                        (report.module.clone(), "protected-declaration journal limit")
                    }
                    fln_elab::protected_names::ProtectedError::Malformed => {
                        (report.module.clone(), "malformed protected declaration")
                    }
                };
                SourceOleanImportError::Metadata {
                    module: report.module.clone(),
                    declaration,
                    reason,
                }
            })?;
            if report.aux_recursors != 0 {
                cancelled!("source-olean/auxiliary-recursor");
                let tagged: Vec<Name> = aux_recursors.by_ref().take(report.aux_recursors).collect();
                if tagged.len() != report.aux_recursors {
                    return Err(SourceOleanImportError::Internal(
                        "auxiliary-recursor count changed during decode",
                    ));
                }
                let mut owners = AttributeOwners::new(
                    &checked.modules[index].decoded.constants,
                    report.aux_recursors,
                    limits.check.max_declarations,
                    limits.metadata.max_entries,
                )?;
                for declaration in &tagged {
                    cancelled!("source-olean/auxiliary-recursor-owner");
                    owners.validate(activation.environment(), &report.module, declaration)?;
                }
                activation = activation
                    .register_aux_recursors(&tagged)
                    .map_err(|error| auxiliary_error(&report.module, error))?;
            }
            if report.pp_anonymous_constructor + report.pp_nodot + report.app_unexpanders != 0 {
                cancelled!("source-olean/delaborator-tags");
                let anonymous: Vec<Name> = pp_anonymous_constructor
                    .by_ref()
                    .take(report.pp_anonymous_constructor)
                    .collect();
                let nodot: Vec<Name> = pp_nodot.by_ref().take(report.pp_nodot).collect();
                let unexpanders: Vec<_> = app_unexpanders
                    .by_ref()
                    .take(report.app_unexpanders)
                    .collect();
                if anonymous.len() != report.pp_anonymous_constructor
                    || nodot.len() != report.pp_nodot
                    || unexpanders.len() != report.app_unexpanders
                {
                    return Err(SourceOleanImportError::Internal(
                        "delaborator tag count changed during decode",
                    ));
                }
                // A tag attribute names this module's own declaration; an unexpander's key
                // may be any admitted constant.
                for tagged in [&anonymous, &nodot] {
                    let mut owners = AttributeOwners::new(
                        &checked.modules[index].decoded.constants,
                        tagged.len(),
                        limits.check.max_declarations,
                        limits.metadata.max_entries,
                    )?;
                    for declaration in tagged {
                        cancelled!("source-olean/delaborator-tag-owner");
                        owners.validate(activation.environment(), &report.module, declaration)?;
                    }
                }
                use fln_elab::delaborator_tags::DelaboratorTag;
                let tags: Vec<DelaboratorTag> = anonymous
                    .into_iter()
                    .map(DelaboratorTag::AnonymousConstructor)
                    .chain(nodot.into_iter().map(DelaboratorTag::NoDot))
                    .chain(
                        unexpanders
                            .into_iter()
                            .map(|entry| DelaboratorTag::Unexpander {
                                key: entry.key,
                                scope: entry.scope,
                            }),
                    )
                    .collect();
                activation =
                    activation
                        .register_delaborator_tags(&tags)
                        .map_err(|error| {
                            let declaration = match &error {
                        fln_elab::delaborator_tags::DelaboratorTagError::UnknownDeclaration(name)
                        | fln_elab::delaborator_tags::DelaboratorTagError::NotInductive(name)
                        | fln_elab::delaborator_tags::DelaboratorTagError::Duplicate(name) => {
                            name.clone()
                        }
                        _ => report.module.clone(),
                    };
                            SourceOleanImportError::Metadata {
                                module: report.module.clone(),
                                declaration,
                                reason: "a delaborator tag cannot be recorded",
                            }
                        })?;
            }
            if report.deprecations != 0 {
                cancelled!("source-olean/deprecations");
                let entries: Vec<_> = deprecations
                    .by_ref()
                    .take(report.deprecations)
                    .map(|entry| fln_elab::deprecations::Deprecation {
                        declaration: entry.declaration,
                        new_name: entry.new_name,
                        text: entry.text,
                        since: entry.since,
                    })
                    .collect();
                if entries.len() != report.deprecations {
                    return Err(SourceOleanImportError::Internal(
                        "deprecation count changed during decode",
                    ));
                }
                // `ParametricAttribute.setParam` sets a parameter only on the module's own
                // declaration.
                let mut owners = AttributeOwners::new(
                    &checked.modules[index].decoded.constants,
                    entries.len(),
                    limits.check.max_declarations,
                    limits.metadata.max_entries,
                )?;
                for entry in &entries {
                    cancelled!("source-olean/deprecation-owner");
                    owners.validate(
                        activation.environment(),
                        &report.module,
                        &entry.declaration,
                    )?;
                }
                activation = activation
                    .register_deprecations(&entries)
                    .map_err(|error| {
                        let declaration = match &error {
                            fln_elab::deprecations::DeprecationError::UnknownDeclaration(name)
                            | fln_elab::deprecations::DeprecationError::Duplicate(name) => {
                                name.clone()
                            }
                            _ => report.module.clone(),
                        };
                        SourceOleanImportError::Metadata {
                            module: report.module.clone(),
                            declaration,
                            reason: "a deprecation cannot be recorded",
                        }
                    })?;
            }
            if report.noncomputable != 0 {
                let mut owners = AttributeOwners::new(
                    &checked.modules[index].decoded.constants,
                    report.noncomputable,
                    limits.check.max_declarations,
                    limits.metadata.max_entries,
                )?;
                for _ in 0..report.noncomputable {
                    cancelled!("source-olean/noncomputable");
                    let declaration =
                        noncomputable
                            .next()
                            .ok_or(SourceOleanImportError::Internal(
                                "noncomputable count changed during decode",
                            ))?;
                    owners.validate(activation.environment(), &report.module, &declaration)?;
                    activation = activation
                        .register_noncomputable(&declaration)
                        .map_err(|error| noncomputable_error(&report.module, error))?;
                }
            }
            if report.defeq != 0 {
                let mut owners = AttributeOwners::new(
                    &checked.modules[index].decoded.constants,
                    report.defeq,
                    limits.check.max_declarations,
                    limits.metadata.max_entries,
                )?;
                for _ in 0..report.defeq {
                    cancelled!("source-olean/defeq");
                    let declaration = defeq.next().ok_or(SourceOleanImportError::Internal(
                        "defeq count changed during decode",
                    ))?;
                    owners.validate(activation.environment(), &report.module, &declaration)?;
                    if strict_tags.insert(declaration.clone()) {
                        activation = activation
                            .register_defeq(&declaration)
                            .map_err(|error| defeq_error(&report.module, &declaration, error))?;
                        backward_tags.insert(declaration);
                    }
                }
            }
            if report.backward_defeq != 0 {
                let mut owners = AttributeOwners::new(
                    &checked.modules[index].decoded.constants,
                    report.backward_defeq,
                    limits.check.max_declarations,
                    limits.metadata.max_entries,
                )?;
                for _ in 0..report.backward_defeq {
                    cancelled!("source-olean/backward-defeq");
                    let declaration =
                        backward_defeq
                            .next()
                            .ok_or(SourceOleanImportError::Internal(
                                "backward-defeq count changed during decode",
                            ))?;
                    owners.validate(activation.environment(), &report.module, &declaration)?;
                    if backward_tags.insert(declaration.clone()) {
                        activation = activation
                            .register_backward_defeq(&declaration)
                            .map_err(|error| defeq_error(&report.module, &declaration, error))?;
                    }
                }
            }
            for _ in 0..report.reducibility {
                cancelled!("source-olean/reducibility");
                let row = reducibility.next().ok_or(SourceOleanImportError::Internal(
                    "reducibility count changed during decode",
                ))?;
                activation = activation
                    .register_reducibility(&row.declaration, reducibility_status(row.status))
                    .map_err(|error| SourceOleanImportError::Metadata {
                        module: report.module.clone(),
                        declaration: row.declaration.clone(),
                        reason: match error {
                            fln_elab::reducibility::ReducibilityError::UnknownDeclaration(_) => {
                                "a reducibility status names no admitted declaration"
                            }
                            fln_elab::reducibility::ReducibilityError::Limit => {
                                "reducibility journal limit"
                            }
                            fln_elab::reducibility::ReducibilityError::Malformed
                            | fln_elab::reducibility::ReducibilityError::Instances(_) => {
                                "malformed reducibility status"
                            }
                        },
                    })?;
            }
            if report.externs != 0 {
                cancelled!("source-olean/extern-owner-index");
                let mut owners = AttributeOwners::new(
                    &checked.modules[index].decoded.constants,
                    report.externs,
                    limits.check.max_declarations,
                    limits.metadata.max_entries,
                )?;
                for _ in 0..report.externs {
                    cancelled!("source-olean/extern");
                    let row = externs.next().ok_or(SourceOleanImportError::Internal(
                        "extern count changed during decode",
                    ))?;
                    owners.validate(activation.environment(), &report.module, &row.declaration)?;
                    activation = activation
                        .register_extern(
                            &row.declaration,
                            row.entries.into_iter().map(extern_entry).collect(),
                        )
                        .map_err(|error| extern_error(&report.module, &row.declaration, error))?;
                }
            }
            if report.implemented_by != 0 {
                cancelled!("source-olean/implemented-by-owner-index");
                let mut owners = AttributeOwners::new(
                    &checked.modules[index].decoded.constants,
                    report.implemented_by,
                    limits.check.max_declarations,
                    limits.metadata.max_entries,
                )?;
                for _ in 0..report.implemented_by {
                    cancelled!("source-olean/implemented-by");
                    let row = implementations
                        .next()
                        .ok_or(SourceOleanImportError::Internal(
                            "implemented_by count changed during decode",
                        ))?;
                    owners.validate(activation.environment(), &report.module, &row.declaration)?;
                    implementation_scopes.validate(
                        &checked,
                        &self.environment,
                        activation.environment(),
                        index,
                        &row,
                    )?;
                    activation = activation
                        .register_implemented_by(&row.declaration, &row.implementation)
                        .map_err(|error| {
                            implemented_by::error(&report.module, &row.declaration, error)
                        })?;
                }
            }
            // Enumeration attributes, like parametric ones, can be set only in the
            // declaring module (Lean/Attributes.lean, registerEnumAttributes), so each
            // `macro_inline` row must name this module's own checked declaration.
            if report.inline != 0 {
                cancelled!("source-olean/inline-owner-index");
                let mut owners = AttributeOwners::new(
                    &checked.modules[index].decoded.constants,
                    report.inline,
                    limits.check.max_declarations,
                    limits.metadata.max_entries,
                )?;
                for _ in 0..report.inline {
                    cancelled!("source-olean/inline");
                    let row = inline.next().ok_or(SourceOleanImportError::Internal(
                        "inline attribute count changed during decode",
                    ))?;
                    if row.kind != metadata::InlineKind::MacroInline {
                        continue;
                    }
                    owners.validate(activation.environment(), &report.module, &row.declaration)?;
                    use fln_elab::macro_inline::MacroInlineError;
                    let reason = |error| match error {
                        MacroInlineError::Limit => "macro_inline journal limit",
                        MacroInlineError::NotADefinition(_) => {
                            "a macro_inline tag names no non-mutual definition"
                        }
                        _ => "a macro_inline tag cannot be recorded",
                    };
                    activation =
                        activation
                            .register_macro_inline(&row.declaration)
                            .map_err(|error| SourceOleanImportError::Metadata {
                                module: report.module.clone(),
                                declaration: row.declaration.clone(),
                                reason: reason(error),
                            })?;
                }
            }
            // Parametric attributes export their complete journal in the private
            // part (Lean/Attributes.lean, registerParametricAttribute). Capture
            // required that part for a module-system artifact, so absence here
            // means no initializer, not a filtered public view. Each entry must
            // belong to this module; a sibling cannot change another global's
            // executable interpretation through forged initialization metadata.
            for (count, rows) in [
                (report.regular_initializers, &mut regular_initializers),
                (report.builtin_initializers, &mut builtin_initializers),
            ] {
                if count == 0 {
                    continue;
                }
                let mut owners = AttributeOwners::new(
                    &checked.modules[index].decoded.constants,
                    count,
                    limits.check.max_declarations,
                    limits.metadata.max_entries,
                )?;
                for _ in 0..count {
                    cancelled!("source-olean/initializer");
                    let row = rows.next().ok_or(SourceOleanImportError::Internal(
                        "initializer count changed during decode",
                    ))?;
                    owners.validate(activation.environment(), &report.module, &row.declaration)?;
                    validate_initializer(activation.environment(), &report.module, &row)?;
                    if row.initializer.is_some() {
                        runtime_initializers.insert(row.declaration);
                    }
                }
            }
            for constant in &checked.modules[index].decoded.constants {
                cancelled!("source-olean/opaque-value");
                if let ConstantInfo::Opaque(opaque) = constant
                    && !opaque.is_unsafe
                    && !runtime_initializers.contains(&opaque.base.name)
                    && activation.environment().find(&opaque.base.name) == Some(constant)
                {
                    executable_opaques.insert(opaque.base.name.clone());
                }
            }
            journals.insert(
                report.module.clone(),
                (before, activation.environment().clone()),
            );
        }
        engine.environment = activation.finish().map_err(|problem| {
            if problem == InstanceRegistryError::Limit {
                SourceOleanImportError::Limit("activated registry readback")
            } else {
                SourceOleanImportError::Internal(
                    "the activated registries disagree with their kept state",
                )
            }
        })?;
        // Validate the complete graph once. A later registration can introduce
        // a cycle through an earlier module; no partial activation escapes it.
        implemented_by::validate_journal(&engine.environment)?;
        fln_elab::aux_recursors::AuxRecursors::read(&engine.environment)
            .map_err(|error| auxiliary_error(&roots.first().cloned().unwrap_or_default(), error))?;
        fln_elab::noncomputable::read(&engine.environment).map_err(|error| {
            noncomputable_error(&roots.first().cloned().unwrap_or_default(), error)
        })?;
        fln_elab::macro_inline::read(&engine.environment).map_err(|_| {
            SourceOleanImportError::Metadata {
                module: roots.first().cloned().unwrap_or_default(),
                declaration: roots.first().cloned().unwrap_or_default(),
                reason: "the macro_inline journal cannot be read back",
            }
        })?;
        fln_elab::delaborator_tags::DelaboratorTags::read(&engine.environment).map_err(|_| {
            SourceOleanImportError::Metadata {
                module: roots.first().cloned().unwrap_or_default(),
                declaration: roots.first().cloned().unwrap_or_default(),
                reason: "the delaborator tag journal cannot be read back",
            }
        })?;
        fln_elab::namespaces::read(&engine.environment).map_err(|error| {
            registry_error(
                &roots.first().cloned().unwrap_or_default(),
                &metadata::namespace_extension_name(),
                error,
            )
        })?;
        fln_elab::records::imported::ImportedStructures::read(&engine.environment).map_err(
            |problem| {
                structures::error(
                    &roots.first().cloned().unwrap_or_default(),
                    &roots.first().cloned().unwrap_or_default(),
                    problem,
                )
            },
        )?;
        if structure_rows.next().is_some()
            || classes.next().is_some()
            || instances.next().is_some()
            || defaults.next().is_some()
            || aliases.next().is_some()
            || namespaces.next().is_some()
            || protected.next().is_some()
            || aux_recursors.next().is_some()
            || noncomputable.next().is_some()
            || defeq.next().is_some()
            || backward_defeq.next().is_some()
            || pp_anonymous_constructor.next().is_some()
            || pp_nodot.next().is_some()
            || app_unexpanders.next().is_some()
            || deprecations.next().is_some()
            || reducibility.next().is_some()
            || externs.next().is_some()
            || implementations.next().is_some()
            || inline.next().is_some()
            || regular_initializers.next().is_some()
            || builtin_initializers.next().is_some()
        {
            return Err(SourceOleanImportError::Internal(
                "decoded metadata escaped its module inventory",
            ));
        }
        // Simp is an independent journal. Preserve the kept registrar and add
        // each module's ordered simp suffix to its retained replay snapshots.
        engine.environment = match (simp::Replay {
            checked: &checked,
            origin: &self.environment,
            order: &order,
            limits: &limits,
            cancellation,
        })
        .activate(&engine.environment, simp_rows, &mut reports, &mut journals)?
        {
            Outcome::Complete(environment) => environment,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        cancelled!("source-olean/before-publication");
        engine.executable_opaques = std::sync::Arc::new(executable_opaques);
        engine.runtime_initializers = std::sync::Arc::new(runtime_initializers);
        // Adding metadata changes the logical root, but not the declarations
        // represented by the retained independent-checker projection.
        if bound {
            engine.imported_environment = Some(engine.environment.clone());
        }
        let result_logical_root = engine.logical_root(options);
        let contexts = super::contexts::ImportContexts::capture(self, &engine, &checked, journals);
        cancelled!("source-olean/after-context-capture");
        Ok(Outcome::Complete(SourceOleanImport {
            engine,
            checked,
            result_logical_root,
            modules: reports,
            contexts,
        }))
    }
}

/// Every module's extension payloads, in replay `order`, `limits.read_jobs` modules
/// at once. Each walk may use the whole capture allowance; the caller charges the
/// cumulative allowance in order, so a closure over it is still refused.
fn capture_modules(
    checked: &CheckedOleanSet,
    order: &[usize],
    inputs: &BTreeMap<&Name, &OleanModuleInput<'_>>,
    limits: &SourceOleanImportLimits,
) -> Vec<Result<Vec<OpaqueExtensionBlock>>> {
    let capture = |index: usize| -> Result<Vec<OpaqueExtensionBlock>> {
        let module = &checked.modules[index];
        let input = inputs
            .get(&module.name)
            .ok_or(SourceOleanImportError::Internal(
                "checked module lost its artifact",
            ))?;
        let view = if module.decoded.module.is_module {
            let (Some(server), Some(private)) = (input.server_artifact, input.private_artifact)
            else {
                return Err(SourceOleanImportError::Internal(
                    "checked module lost its companions",
                ));
            };
            OleanView::parse_with_dependencies(private, &[input.artifact, server])
        } else {
            OleanView::parse(input.artifact)
        }
        .map_err(|error| SourceOleanImportError::Capture {
            module: module.name.clone(),
            error,
        })?;
        view.extension_payloads(limits.capture, limits.max_capture_bytes)
            .map_err(|error| SourceOleanImportError::Capture {
                module: module.name.clone(),
                error,
            })
    };
    let threads = limits.read_jobs.threads.get().min(order.len());
    if threads <= 1 {
        return order.iter().map(|&index| capture(index)).collect();
    }
    let next = std::sync::atomic::AtomicUsize::new(0);
    let slots: Vec<std::sync::OnceLock<Result<Vec<OpaqueExtensionBlock>>>> =
        order.iter().map(|_| std::sync::OnceLock::new()).collect();
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                loop {
                    let at = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    let (Some(slot), Some(&index)) = (slots.get(at), order.get(at)) else {
                        return;
                    };
                    let _ = slot.set(capture(index));
                }
            });
        }
    });
    slots
        .into_iter()
        .zip(order)
        .map(|(slot, &index)| slot.into_inner().unwrap_or_else(|| capture(index)))
        .collect()
}

/// Who makes a closure's metadata registrations. Production makes them through one
/// [`instances::imported::ImportActivation`]; the tests also make them one call at a
/// time through the per-call functions, and require the same environment.
trait Registrar: Sized {
    fn new(env: Environment) -> Self;
    fn environment(&self) -> &Environment;
    fn register_class(
        self,
        class: &Name,
        parameters: &instances::imported::ClassParameters,
    ) -> std::result::Result<Self, InstanceRegistryError>;
    fn register_instance(
        self,
        declaration: &Name,
        parameters: &instances::imported::InstanceParameters,
    ) -> std::result::Result<Self, InstanceRegistryError>;
    fn register_default(
        self,
        declaration: &Name,
        priority: u32,
    ) -> std::result::Result<Self, InstanceRegistryError>;
    fn register_alias(
        self,
        alias: &Name,
        declaration: &Name,
    ) -> std::result::Result<Self, fln_elab::aliases::AliasError>;
    fn register_namespaces(
        self,
        names: &[Name],
    ) -> std::result::Result<Self, InstanceRegistryError>;
    fn register_protected(
        self,
        declarations: &[Name],
    ) -> std::result::Result<Self, fln_elab::protected_names::ProtectedError>;
    fn register_aux_recursors(
        self,
        declarations: &[Name],
    ) -> std::result::Result<Self, fln_elab::aux_recursors::AuxRecursorError>;
    fn register_delaborator_tags(
        self,
        tags: &[fln_elab::delaborator_tags::DelaboratorTag],
    ) -> std::result::Result<Self, fln_elab::delaborator_tags::DelaboratorTagError>;
    fn register_deprecations(
        self,
        entries: &[fln_elab::deprecations::Deprecation],
    ) -> std::result::Result<Self, fln_elab::deprecations::DeprecationError>;
    fn register_noncomputable(
        self,
        declaration: &Name,
    ) -> std::result::Result<Self, fln_elab::noncomputable::NoncomputableError>;
    fn register_defeq(
        self,
        declaration: &Name,
    ) -> std::result::Result<Self, fln_elab::NatDefinitionElabError>;
    fn register_backward_defeq(
        self,
        declaration: &Name,
    ) -> std::result::Result<Self, fln_elab::NatDefinitionElabError>;
    fn register_reducibility(
        self,
        declaration: &Name,
        status: fln_elab::reducibility::Reducibility,
    ) -> std::result::Result<Self, fln_elab::reducibility::ReducibilityError>;
    fn register_extern(
        self,
        declaration: &Name,
        entries: Vec<fln_elab::externs::ExternEntry>,
    ) -> std::result::Result<Self, fln_elab::externs::ExternError>;
    fn register_implemented_by(
        self,
        declaration: &Name,
        implementation: &Name,
    ) -> std::result::Result<Self, fln_elab::implemented_by::ImplementedByError>;
    fn register_macro_inline(
        self,
        declaration: &Name,
    ) -> std::result::Result<Self, fln_elab::macro_inline::MacroInlineError>;
    fn register_structures(
        self,
        rows: &[fln_elab::records::imported::StructureEntry],
    ) -> std::result::Result<Self, fln_elab::records::RecordError>;
    fn finish(self) -> std::result::Result<Environment, InstanceRegistryError>;
}

impl Registrar for instances::imported::ImportActivation {
    fn new(env: Environment) -> Self {
        Self::new(env)
    }
    fn environment(&self) -> &Environment {
        self.environment()
    }
    fn register_class(
        self,
        class: &Name,
        parameters: &instances::imported::ClassParameters,
    ) -> std::result::Result<Self, InstanceRegistryError> {
        self.register_class(class, parameters)
    }
    fn register_instance(
        self,
        declaration: &Name,
        parameters: &instances::imported::InstanceParameters,
    ) -> std::result::Result<Self, InstanceRegistryError> {
        self.register_instance(declaration, parameters)
    }
    fn register_default(
        self,
        declaration: &Name,
        priority: u32,
    ) -> std::result::Result<Self, InstanceRegistryError> {
        self.register_default(declaration, priority)
    }
    fn register_alias(
        self,
        alias: &Name,
        declaration: &Name,
    ) -> std::result::Result<Self, fln_elab::aliases::AliasError> {
        self.register_alias(alias, declaration)
    }
    fn register_protected(
        self,
        declarations: &[Name],
    ) -> std::result::Result<Self, fln_elab::protected_names::ProtectedError> {
        self.register_protected(declarations)
    }
    fn register_namespaces(
        self,
        names: &[Name],
    ) -> std::result::Result<Self, InstanceRegistryError> {
        self.register_namespaces(names)
    }
    fn register_aux_recursors(
        self,
        declarations: &[Name],
    ) -> std::result::Result<Self, fln_elab::aux_recursors::AuxRecursorError> {
        self.register_aux_recursors(declarations)
    }
    fn register_delaborator_tags(
        self,
        tags: &[fln_elab::delaborator_tags::DelaboratorTag],
    ) -> std::result::Result<Self, fln_elab::delaborator_tags::DelaboratorTagError> {
        self.register_delaborator_tags(tags)
    }
    fn register_deprecations(
        self,
        entries: &[fln_elab::deprecations::Deprecation],
    ) -> std::result::Result<Self, fln_elab::deprecations::DeprecationError> {
        self.register_deprecations(entries)
    }
    fn register_noncomputable(
        self,
        declaration: &Name,
    ) -> std::result::Result<Self, fln_elab::noncomputable::NoncomputableError> {
        self.register_noncomputable(declaration)
    }
    fn register_defeq(
        self,
        declaration: &Name,
    ) -> std::result::Result<Self, fln_elab::NatDefinitionElabError> {
        self.register_defeq(declaration)
    }
    fn register_backward_defeq(
        self,
        declaration: &Name,
    ) -> std::result::Result<Self, fln_elab::NatDefinitionElabError> {
        self.register_backward_defeq(declaration)
    }
    fn register_reducibility(
        self,
        declaration: &Name,
        status: fln_elab::reducibility::Reducibility,
    ) -> std::result::Result<Self, fln_elab::reducibility::ReducibilityError> {
        self.register_reducibility(declaration, status)
    }
    fn register_extern(
        self,
        declaration: &Name,
        entries: Vec<fln_elab::externs::ExternEntry>,
    ) -> std::result::Result<Self, fln_elab::externs::ExternError> {
        self.register_extern(declaration, entries)
    }
    fn register_implemented_by(
        self,
        declaration: &Name,
        implementation: &Name,
    ) -> std::result::Result<Self, fln_elab::implemented_by::ImplementedByError> {
        self.register_implemented_by(declaration, implementation)
    }
    fn register_macro_inline(
        self,
        declaration: &Name,
    ) -> std::result::Result<Self, fln_elab::macro_inline::MacroInlineError> {
        self.register_macro_inline(declaration)
    }
    fn register_structures(
        self,
        rows: &[fln_elab::records::imported::StructureEntry],
    ) -> std::result::Result<Self, fln_elab::records::RecordError> {
        self.register_structures(rows)
    }
    fn finish(self) -> std::result::Result<Environment, InstanceRegistryError> {
        self.finish()
    }
}

/// A decoded stored `DiscrTree.Key` as the native instance index holds it.
fn instance_key(key: metadata::DiscrTreeKey) -> instances::discr_tree::Key {
    use instances::discr_tree::Key;
    use metadata::DiscrTreeKey;
    match key {
        DiscrTreeKey::Star => Key::Star,
        DiscrTreeKey::Other => Key::Other,
        DiscrTreeKey::Lit(literal) => Key::Lit(literal),
        DiscrTreeKey::FVar(name, arity) => Key::FVar(fln_core::expr::FVarId(name), arity),
        DiscrTreeKey::Const(name, arity) => Key::Const(name, arity),
        DiscrTreeKey::Arrow => Key::Arrow,
        DiscrTreeKey::Proj(name, field, arity) => Key::Proj(name, field, arity),
    }
}

/// The decoded olean status as the elaborator's.
fn reducibility_status(
    status: metadata::ReducibilityStatus,
) -> fln_elab::reducibility::Reducibility {
    use fln_elab::reducibility::Reducibility;
    match status {
        metadata::ReducibilityStatus::Reducible => Reducibility::Reducible,
        metadata::ReducibilityStatus::Semireducible => Reducibility::Semireducible,
        metadata::ReducibilityStatus::Irreducible => Reducibility::Irreducible,
        metadata::ReducibilityStatus::ImplicitReducible => Reducibility::ImplicitReducible,
    }
}

fn defeq_error(
    module: &Name,
    declaration: &Name,
    error: fln_elab::NatDefinitionElabError,
) -> SourceOleanImportError {
    if matches!(
        error,
        fln_elab::NatDefinitionElabError::Inference(
            fln_elab::source::SourceInferenceError::SimpSet(
                fln_elab::source::scope::simp::SimpSetError::Limit
            ) | fln_elab::source::SourceInferenceError::ResourceLimit
        )
    ) {
        return SourceOleanImportError::Limit("native reflexivity journal");
    }
    SourceOleanImportError::Metadata {
        module: module.clone(),
        declaration: declaration.clone(),
        reason: "reflexivity tag cannot be recorded",
    }
}

/// Parametric attributes cannot be applied to an imported declaration at the pin.
/// Retain the exact checked owner, rather than accepting any ambient name that
/// happens to have the expected spelling. Both allocations are bounded before
/// construction; the index exists only for a module with selected attribute rows.
struct AttributeOwners<'a> {
    declarations: Vec<&'a ConstantInfo>,
    seen: HashSet<Name>,
}

impl<'a> AttributeOwners<'a> {
    fn new(
        constants: &'a [ConstantInfo],
        rows: usize,
        max_declarations: usize,
        max_entries: usize,
    ) -> Result<Self> {
        if constants.len() > max_declarations {
            return Err(SourceOleanImportError::Limit(
                "attribute declaration ownership index",
            ));
        }
        if rows > max_entries {
            return Err(SourceOleanImportError::Limit("attribute ownership rows"));
        }
        let mut declarations = Vec::new();
        declarations
            .try_reserve_exact(constants.len())
            .map_err(|_| {
                SourceOleanImportError::Limit("attribute declaration ownership allocation")
            })?;
        declarations.extend(constants.iter());
        declarations.sort_unstable_by(|left, right| {
            left.constant_val().name.cmp(&right.constant_val().name)
        });
        if declarations
            .windows(2)
            .any(|pair| pair[0].constant_val().name == pair[1].constant_val().name)
        {
            return Err(SourceOleanImportError::Internal(
                "checked module repeats an attribute owner declaration",
            ));
        }
        let mut seen = HashSet::new();
        seen.try_reserve(rows)
            .map_err(|_| SourceOleanImportError::Limit("attribute ownership allocation"))?;
        Ok(Self { declarations, seen })
    }

    fn validate(&mut self, env: &Environment, module: &Name, declaration: &Name) -> Result<()> {
        let error = |reason| SourceOleanImportError::Metadata {
            module: module.clone(),
            declaration: declaration.clone(),
            reason,
        };
        let position = self
            .declarations
            .binary_search_by(|info| info.constant_val().name.cmp(declaration))
            .map_err(|_| {
                error("an attribute does not belong to this module's checked declarations")
            })?;
        if env.find(declaration) != Some(self.declarations[position]) {
            return Err(error(
                "an attribute owner differs from its active admitted declaration",
            ));
        }
        if !self.seen.insert(declaration.clone()) {
            return Err(error("duplicate attribute for one module declaration"));
        }
        Ok(())
    }
}

/// Match the pin's exact `IO T` / `IO Unit` attribute contract without reducing
/// any body or running an action (Lean/Compiler/InitAttr.lean, getParam).
fn validate_initializer(
    env: &Environment,
    module: &Name,
    row: &fln_olean::initializers::InitEntry,
) -> Result<()> {
    fn io_argument(type_: &Expr) -> Option<&Expr> {
        if let ExprNode::App { f, a } = type_.node()
            && let ExprNode::Const { name, .. } = f.node()
            && *name == Name::from_components(["IO"])
        {
            Some(a)
        } else {
            None
        }
    }
    let error = |reason| SourceOleanImportError::Metadata {
        module: module.clone(),
        declaration: row.declaration.clone(),
        reason,
    };
    let owner = env
        .find(&row.declaration)
        .ok_or_else(|| error("an initialized declaration is not admitted"))?;
    if let Some(initializer) = &row.initializer {
        let action = env.find(initializer).ok_or_else(|| {
            error("an initializer names no admitted declaration")
        })?;
        if io_argument(&action.constant_val().type_) != Some(&owner.constant_val().type_) {
            return Err(error("an initializer must have type IO of its declaration's exact type"));
        }
    } else if !io_argument(&owner.constant_val().type_).is_some_and(|type_| {
        matches!(type_.node(), ExprNode::Const { name, .. } if *name == Name::from_components(["Unit"]))
    }) {
        return Err(error("an anonymous initialization action must have type IO Unit"));
    }
    Ok(())
}

fn extern_entry(entry: metadata::ExternEntry) -> fln_elab::externs::ExternEntry {
    use fln_elab::externs::ExternEntry;
    match entry {
        metadata::ExternEntry::Adhoc { backend } => ExternEntry::Adhoc { backend },
        metadata::ExternEntry::Inline { backend, pattern } => {
            ExternEntry::Inline { backend, pattern }
        }
        metadata::ExternEntry::Standard { backend, symbol } => {
            ExternEntry::Standard { backend, symbol }
        }
        metadata::ExternEntry::Opaque => ExternEntry::Opaque,
    }
}

fn extern_error(
    module: &Name,
    declaration: &Name,
    error: fln_elab::externs::ExternError,
) -> SourceOleanImportError {
    use fln_elab::externs::ExternError;
    let reason = match error {
        ExternError::Limit => return SourceOleanImportError::Limit("extern attribute journal"),
        ExternError::UnknownDeclaration(_) => "an extern attribute names no admitted declaration",
        ExternError::Malformed => "malformed extern attribute journal",
    };
    SourceOleanImportError::Metadata {
        module: module.clone(),
        declaration: declaration.clone(),
        reason,
    }
}

fn auxiliary_error(
    module: &Name,
    error: fln_elab::aux_recursors::AuxRecursorError,
) -> SourceOleanImportError {
    use fln_elab::aux_recursors::AuxRecursorError;
    let (declaration, reason) = match error {
        AuxRecursorError::Limit => {
            return SourceOleanImportError::Limit("auxiliary-recursor journal");
        }
        AuxRecursorError::UnknownDeclaration(name) => {
            (name, "an auxiliary tag names no admitted declaration")
        }
        AuxRecursorError::NotDefinition(name) => (name, "an auxiliary tag names a non-definition"),
        AuxRecursorError::Duplicate(name) => (
            name,
            "a definition is tagged as an auxiliary recursor twice",
        ),
        AuxRecursorError::Malformed => (module.clone(), "malformed auxiliary-recursor journal"),
    };
    SourceOleanImportError::Metadata {
        module: module.clone(),
        declaration,
        reason,
    }
}

fn noncomputable_error(
    module: &Name,
    error: fln_elab::noncomputable::NoncomputableError,
) -> SourceOleanImportError {
    use fln_elab::noncomputable::NoncomputableError;
    let (declaration, reason) = match error {
        NoncomputableError::Limit => return SourceOleanImportError::Limit("noncomputable journal"),
        NoncomputableError::UnknownDeclaration(name) => {
            (name, "a noncomputable tag names no admitted declaration")
        }
        NoncomputableError::Duplicate(name) => {
            (name, "a declaration is tagged noncomputable twice")
        }
        NoncomputableError::Malformed => (module.clone(), "malformed noncomputable journal"),
        NoncomputableError::CompilerEquation { theorem, reason } => (theorem, reason),
    };
    SourceOleanImportError::Metadata {
        module: module.clone(),
        declaration,
        reason,
    }
}

fn registry_error(
    module: &Name,
    declaration: &Name,
    error: InstanceRegistryError,
) -> SourceOleanImportError {
    SourceOleanImportError::Registry {
        module: module.clone(),
        declaration: declaration.clone(),
        error,
    }
}

/// Import-order postorder, with each shared dependency replayed once. A caller
/// cannot smuggle unrelated module metadata in through an oversized input set.
fn replay_order(checked: &CheckedOleanSet, roots: &[Name]) -> Result<Vec<usize>> {
    let indices: BTreeMap<_, _> = checked
        .modules
        .iter()
        .enumerate()
        .map(|(i, m)| (&m.name, i))
        .collect();
    let mut colors = vec![0u8; checked.modules.len()];
    let mut order = Vec::new();
    for root in roots {
        let &index = indices
            .get(root)
            .ok_or_else(|| SourceOleanImportError::MissingRoot(root.clone()))?;
        if colors[index] == 2 {
            continue;
        }
        colors[index] = 1;
        let mut stack = vec![(index, 0usize)];
        while let Some((index, next)) = stack.last_mut() {
            if let Some(import) = checked.modules[*index].decoded.module.imports.get(*next) {
                *next += 1;
                let &dependency =
                    indices
                        .get(&import.module)
                        .ok_or(SourceOleanImportError::Internal(
                            "checked import closure is incomplete",
                        ))?;
                match colors[dependency] {
                    0 => {
                        colors[dependency] = 1;
                        stack.push((dependency, 0));
                    }
                    1 => {
                        return Err(SourceOleanImportError::Internal(
                            "checked import graph has a cycle",
                        ));
                    }
                    _ => {}
                }
            } else {
                colors[*index] = 2;
                order.push(*index);
                stack.pop();
            }
        }
    }
    if order.len() != checked.modules.len() {
        let index =
            colors
                .iter()
                .position(|color| *color != 2)
                .ok_or(SourceOleanImportError::Internal(
                    "module order count mismatch",
                ))?;
        return Err(SourceOleanImportError::UnreachableModule(
            checked.modules[index].name.clone(),
        ));
    }
    Ok(order)
}

#[cfg(test)]
#[path = "imported/extern_tests.rs"]
mod extern_tests;

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use std::num::NonZeroUsize;

    /// The `.olean` kernel depth budget's stack, as `check-source` gives it.
    const STACK: usize = 64 * 1024 * 1024;

    pub(in crate::source_check::modules) fn n(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    pub(in crate::source_check::modules) fn pinned_lib() -> Option<std::path::PathBuf> {
        let lib = std::env::var_os("FLN_REFERENCE_LIB")
            .map(std::path::PathBuf::from)
            .or_else(|| {
                std::env::var_os("HOME").map(|home| {
                    std::path::PathBuf::from(home)
                        .join(".elan/toolchains")
                        .join(format!("leanprover--lean4---{OLEAN_PIN_TAG}"))
                        .join("lib/lean")
                })
            })
            .filter(|lib| lib.join("Init/Prelude.olean").is_file());
        assert!(
            lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "FLN_REQUIRE_REFERENCE is set but the pinned Reference lib/lean is absent"
        );
        lib
    }

    /// Each module of `roots`' closure with its exported, server and private
    /// parts, in discovery order, read as data from the pinned toolchain.
    pub(in crate::source_check::modules) fn closure(
        lib: &std::path::Path,
        roots: &[&str],
    ) -> Vec<(Name, [Vec<u8>; 3])> {
        let mut pending: Vec<Name> = roots.iter().map(|root| n(root)).collect();
        let mut seen = BTreeSet::new();
        let mut loaded = Vec::new();
        while let Some(name) = pending.pop() {
            if !seen.insert(name.clone()) {
                continue;
            }
            let base = lib.join(name.to_display_string().replace('.', "/"));
            let parts = ["olean", "olean.server", "olean.private"]
                .map(|extension| std::fs::read(base.with_extension(extension)).unwrap_or_default());
            assert!(!parts[0].is_empty(), "{} has no .olean", base.display());
            let imports = olean_module_imports(&parts[0], OleanDecodeLimits::new(parts[0].len()))
                .expect("a pinned module's imports decode");
            pending.extend(imports);
            loaded.push((name, parts));
        }
        loaded
    }

    pub(in crate::source_check::modules) fn inputs(
        closure: &[(Name, [Vec<u8>; 3])],
    ) -> Vec<OleanModuleInput<'_>> {
        closure
            .iter()
            .map(|(name, [exported, server, private])| OleanModuleInput {
                name,
                artifact: exported,
                server_artifact: (!server.is_empty()).then_some(server.as_slice()),
                private_artifact: (!private.is_empty()).then_some(private.as_slice()),
            })
            .collect()
    }

    pub(in crate::source_check::modules) fn limits(threads: usize) -> SourceOleanImportLimits {
        let jobs = OleanFrontierJobs {
            threads: NonZeroUsize::new(threads).expect("a positive thread count"),
            worker_stack_bytes: STACK,
        };
        SourceOleanImportLimits {
            jobs,
            read_jobs: jobs,
            ..SourceOleanImportLimits::new(OleanCheckLimits::new(
                1 << 30,
                Budget::for_stack_bytes(STACK),
            ))
        }
    }

    fn import(
        inputs: &[OleanModuleInput<'_>],
        roots: &[Name],
        limits: SourceOleanImportLimits,
    ) -> Result<Outcome<SourceOleanImport>> {
        Engine::from_environment(Environment::new()).import_olean_modules_for_source(
            inputs,
            roots,
            &KVMap::new(),
            limits,
        )
    }

    /// Run on a stack the `.olean` kernel budget is calibrated for, as the
    /// front doors do.
    pub(in crate::source_check::modules) fn on_import_stack<T: Send>(
        body: impl FnOnce() -> T + Send,
    ) -> T {
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(STACK)
                .spawn_scoped(scope, body)
                .expect("spawn the import thread")
                .join()
                .expect("the import thread does not panic")
        })
    }

    /// The receipt the parallel council produces is the serial one: the same
    /// checked set (engine, roots, module rows with their artifacts and per-module
    /// roots), the same metadata reports and replayed engine, the same retained
    /// import contexts, and the same answer when source is checked against it.
    /// Equality on this closure is evidence for this closure, not a proof of
    /// schedule independence in general.
    #[test]
    fn a_real_closure_imports_identically_at_one_and_several_jobs() {
        let Some(lib) = pinned_lib() else {
            eprintln!("SKIP: pinned Reference lib/lean absent");
            return;
        };
        // Siblings `Init.Data.Cast` and `Init.Data.Option.Coe` import only
        // `Init.Coe`, so two modules are checked side by side.
        let roots = ["Init.Data.Cast", "Init.Data.Option.Coe", "Init.Data.Zero"];
        let closure = closure(&lib, &roots);
        assert_eq!(closure.len(), 7, "the closure this test was sized for");
        let inputs = inputs(&closure);
        let roots: Vec<Name> = roots.iter().map(|root| n(root)).collect();
        on_import_stack(|| {
            let serial = import(&inputs, &roots, limits(1))
                .expect("the pinned closure imports")
                .into_complete()
                .expect("the pinned closure imports completely");
            let parallel = import(&inputs, &roots, limits(3))
                .expect("the pinned closure imports")
                .into_complete()
                .expect("the pinned closure imports completely");
            crate::assert_checked_sets_identical(&serial.checked, &parallel.checked, "checked set");
            crate::assert_engines_identical(&serial.engine, &parallel.engine, "metadata engine");
            assert_eq!(serial.result_logical_root, parallel.result_logical_root);
            assert_eq!(serial.modules, parallel.modules, "metadata reports");
            serial
                .contexts
                .assert_identical(&parallel.contexts, "import contexts");
            assert!(
                serial.modules.iter().any(|report| report.instances > 0),
                "the closure carries instance metadata"
            );

            let main = n("Main");
            let source =
                b"prelude\nimport Init.Data.Cast\ntheorem keep (P : Prop) (h : P) : P := h\n";
            let check = |receipt: &SourceOleanImport| {
                receipt
                    .check_source_modules(
                        &[SourceModuleInput {
                            name: &main,
                            source,
                        }],
                        &main,
                        &KVMap::new(),
                        super::super::SourceModuleCheckLimits::new(SourceCheckLimits::new(
                            EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
                        )),
                        None,
                    )
                    .expect("source checks against the receipt")
                    .into_complete()
                    .expect("source checks completely")
            };
            let (serial, parallel) = (check(&serial), check(&parallel));
            assert_eq!(
                serial.checked.base_logical_root,
                parallel.checked.base_logical_root
            );
            assert_eq!(
                serial.checked.result_logical_root,
                parallel.checked.result_logical_root
            );
            crate::assert_engines_identical(
                &serial.checked.engine,
                &parallel.checked.engine,
                "source result",
            );
        });
    }

    #[test]
    fn reflexivity_tags_merge_by_name_across_modules_but_not_within_one() {
        use fln_env::constants::{ConstantVal, DefinitionVal, ReducibilityHints};
        use fln_olean::extension_write::{ModuleExtensionInput, encode_module_with_extensions};
        use fln_rt::convert::inject_name;
        use fln_rt::obj::Obj;
        use fln_rt::region::compact;

        on_import_stack(|| {
            let declaration = n("tag.tag");
            let unshared = inject_name(&declaration);
            let prefix = unshared.try_ctor_child(0).unwrap();
            // Both Name components have the same string. Sharing that string
            // changes compacted bytes without changing a component or its hash.
            let shared = Obj::mk_ctor(
                u8::try_from(unshared.obj_tag()).unwrap(),
                vec![prefix.clone_ref(), prefix.try_ctor_child(1).unwrap()],
                &declaration.hash().to_le_bytes(),
            );
            assert_ne!(compact(&unshared, 0).unwrap(), compact(&shared, 0).unwrap());
            let constants = [ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: declaration.clone(),
                    level_params: vec![],
                    type_: Expr::forall_e(
                        n("A"),
                        Expr::sort(Level::one()),
                        Expr::forall_e(
                            n("x"),
                            Expr::bvar(0).unwrap(),
                            Expr::bvar(1).unwrap(),
                            BinderInfo::Default,
                        ),
                        BinderInfo::Default,
                    ),
                },
                value: Expr::lam(
                    n("A"),
                    Expr::sort(Level::one()),
                    Expr::lam(
                        n("x"),
                        Expr::bvar(0).unwrap(),
                        Expr::bvar(0).unwrap(),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![declaration.clone()],
            })];
            let base = n("Base");
            let main = n("Main");
            let imports = [OleanModuleImport {
                module: base.clone(),
                import_all: false,
                is_exported: false,
                is_meta: false,
            }];
            for extension in [
                metadata::DEFEQ_EXTENSION,
                metadata::BACKWARD_DEFEQ_EXTENSION,
            ] {
                let extension = n(extension);
                let encode =
                    |imports: &[OleanModuleImport], constants: &[ConstantInfo], entries: &[Obj]| {
                        encode_module_with_extensions(
                            OleanModuleWriteInput {
                                is_module: false,
                                imports,
                                constants,
                                extra_const_names: &[],
                            },
                            &[ModuleExtensionInput {
                                name: &extension,
                                entries,
                            }],
                            OleanWriteHeader {
                                version: OLEAN_ACCEPTED_VERSIONS[0],
                                flags: 1,
                                lean_version: OLEAN_PIN_TAG.strip_prefix('v').unwrap(),
                                githash: OLEAN_PIN_COMMIT,
                                base_addr: (OLEAN_REGION_ALIGN as u64) * 2,
                            },
                            OleanWriteBudget::default(),
                        )
                        .unwrap()
                    };
                let first = encode(&[], &constants, std::slice::from_ref(&unshared));
                let run = |entries: &[Obj], limits: SourceOleanImportLimits| {
                    let second = encode(&imports, &[], entries);
                    let inputs = [
                        OleanModuleInput {
                            name: &base,
                            artifact: &first.bytes,
                            server_artifact: None,
                            private_artifact: None,
                        },
                        OleanModuleInput {
                            name: &main,
                            artifact: &second.bytes,
                            server_artifact: None,
                            private_artifact: None,
                        },
                    ];
                    import(&inputs, std::slice::from_ref(&main), limits)
                };
                for second in [&shared, &unshared] {
                    let imported = run(std::slice::from_ref(second), limits(1))
                        .unwrap()
                        .into_complete()
                        .unwrap();
                    let counts: Vec<_> = imported
                        .modules
                        .iter()
                        .map(|report| report.defeq + report.backward_defeq)
                        .collect();
                    assert_eq!(counts, [1, 0]);
                    use fln_elab::source::scope::simp::defeq;
                    assert_eq!(
                        defeq::read_backward(imported.engine.environment(), || Ok(())).unwrap(),
                        BTreeSet::from([declaration.clone()]),
                    );
                }
                for entries in [
                    vec![shared.clone_ref(), unshared.clone_ref()],
                    vec![shared.clone_ref(), shared.clone_ref()],
                ] {
                    assert!(matches!(
                        run(&entries, limits(1)),
                        Err(SourceOleanImportError::Metadata { module, declaration: repeated, reason: "duplicate reflexivity tag in one module" })
                            if module == main && repeated == declaration
                    ));
                }
                let mut bounded = limits(1);
                bounded.metadata.max_entries = 1;
                assert!(
                    run(std::slice::from_ref(&unshared), bounded)
                        .unwrap()
                        .into_complete()
                        .is_some(),
                    "byte-identical cross-module tags retain their original cached decode cost"
                );
                assert!(matches!(
                    run(std::slice::from_ref(&shared), bounded),
                    Err(SourceOleanImportError::Decode(
                        metadata::DecodeError::Limit {
                            resource: "entries"
                        }
                    ))
                ));
            }
        });
    }

    #[test]
    fn imported_backward_only_tags_are_distinct_from_strict_reflexivity() {
        use fln_env::constants::{ConstantVal, TheoremVal};
        use fln_olean::write::source::{SourceMetadata, encode_module_with_source_metadata};

        on_import_stack(|| {
            let base = Engine::from_environment(Environment::new())
                .admit_declarations(
                    &[fln_elab::seed::eq_seed_declaration()],
                    &KVMap::new(),
                    EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)),
                )
                .unwrap()
                .into_complete()
                .unwrap()
                .engine;
            let a = Expr::bvar(1).unwrap();
            let x = Expr::bvar(0).unwrap();
            let equality = Expr::app(
                Expr::app(
                    Expr::app(Expr::const_(n("Eq"), vec![Level::one()]), a.clone()),
                    x.clone(),
                ),
                x.clone(),
            );
            let proof = Expr::app(
                Expr::app(Expr::const_(n("Eq.refl"), vec![Level::one()]), a),
                x,
            );
            let type_ = Expr::forall_e(
                n("A"),
                Expr::sort(Level::one()),
                Expr::forall_e(
                    n("x"),
                    Expr::bvar(0).unwrap(),
                    equality,
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            );
            let value = Expr::lam(
                n("A"),
                Expr::sort(Level::one()),
                Expr::lam(n("x"), Expr::bvar(0).unwrap(), proof, BinderInfo::Default),
                BinderInfo::Default,
            );
            let constants: Vec<_> = [n("strict"), n("backward")]
                .into_iter()
                .map(|name| {
                    ConstantInfo::Thm(TheoremVal {
                        base: ConstantVal {
                            name: name.clone(),
                            level_params: vec![],
                            type_: type_.clone(),
                        },
                        value: value.clone(),
                        all: vec![name],
                    })
                })
                .collect();
            let encoded = encode_module_with_source_metadata(
                OleanModuleWriteInput {
                    is_module: false,
                    imports: &[],
                    constants: &constants,
                    extra_const_names: &[],
                },
                &SourceMetadata {
                    defeq: vec![n("strict")],
                    backward_defeq: vec![n("backward")],
                    ..Default::default()
                },
                OleanWriteHeader {
                    version: OLEAN_ACCEPTED_VERSIONS[0],
                    flags: 1,
                    lean_version: OLEAN_PIN_TAG.strip_prefix('v').unwrap(),
                    githash: OLEAN_PIN_COMMIT,
                    base_addr: (OLEAN_REGION_ALIGN as u64) * 2,
                },
                OleanWriteBudget::default(),
            )
            .unwrap();
            let root = n("Tags");
            let inputs = [OleanModuleInput {
                name: &root,
                artifact: &encoded.bytes,
                server_artifact: None,
                private_artifact: None,
            }];
            let imported = base
                .import_olean_modules_for_source(
                    &inputs,
                    std::slice::from_ref(&root),
                    &KVMap::new(),
                    limits(1),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            assert_eq!(imported.modules[0].defeq, 1);
            assert_eq!(imported.modules[0].backward_defeq, 2);
            assert!(imported.modules[0].uninterpreted.is_empty());
            use fln_elab::source::scope::simp::defeq;
            let env = imported.engine.environment().clone();
            assert_eq!(
                defeq::read(&env, || Ok(())).unwrap(),
                BTreeSet::from([n("strict")])
            );
            assert_eq!(
                defeq::read_backward(&env, || Ok(())).unwrap(),
                BTreeSet::from([n("strict"), n("backward")])
            );
            // The strict tag already implies its backward flag, so the native
            // journal holds two events instead of three duplicated selections.
            assert_eq!(env.extension(&defeq::journal_name()).unwrap().len(), 2);
            let sequential = base
                .activate_source_metadata_with::<Sequential>(
                    imported.checked,
                    &inputs,
                    std::slice::from_ref(&root),
                    &KVMap::new(),
                    limits(1),
                    None,
                )
                .unwrap()
                .into_complete()
                .unwrap();
            assert_eq!(&env, sequential.engine.environment());
        });
    }

    /// The pin's `@[defeq]` tags (`Lean.defeqAttr`) are activated with each module's
    /// other metadata, so `dsimp` reads an imported rfl lemma as reflexive. None was
    /// imported before: `dsimp` on `P (id x)` made no progress, where the pinned lean
    /// (`prelude`, `import Init.Tactics`) rewrites it with `id_eq` and accepts the proof.
    #[test]
    fn imported_defeq_tags_make_dsimp_use_imported_rfl_lemmas() {
        let Some(lib) = pinned_lib() else {
            eprintln!("SKIP: pinned Reference lib/lean absent");
            return;
        };
        let roots = ["Init.Tactics"];
        let closure = closure(&lib, &roots);
        let inputs = inputs(&closure);
        let roots: Vec<Name> = roots.iter().map(|root| n(root)).collect();
        on_import_stack(|| {
            let imported = import(&inputs, &roots, limits(1))
                .expect("the pinned closure imports")
                .into_complete()
                .expect("the pinned closure imports completely");
            let prelude = imported
                .modules
                .iter()
                .find(|report| report.module == n("Init.Prelude"))
                .expect("the closure contains Init.Prelude");
            assert!(prelude.defeq > 0, "Init.Prelude carries defeq tags");
            let main = n("Main");
            let source = b"prelude\nimport Init.Tactics\ntheorem viaIdEq (x : Nat) (P : Nat \xe2\x86\x92 Prop) (h : P x) : P (id x) := by\n  dsimp\n  exact h\n";
            imported
                .check_source_modules(
                    &[SourceModuleInput {
                        name: &main,
                        source,
                    }],
                    &main,
                    &KVMap::new(),
                    super::super::SourceModuleCheckLimits::new(SourceCheckLimits::new(
                        EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
                    )),
                    None,
                )
                .expect("dsimp rewrites `id x` with the imported rfl lemma")
                .into_complete()
                .expect("source checks completely");
        });
    }

    #[test]
    fn pinned_opaque_identity_runs_after_complete_private_metadata() {
        let Some(lib) = pinned_lib() else {
            eprintln!("SKIP: pinned Reference lib/lean absent");
            return;
        };
        let closure = closure(&lib, &["Init.Core"]);
        let all = inputs(&closure);
        let roots = [n("Init.Core")];
        on_import_stack(|| {
            let imported = import(&all, &roots, limits(1))
                .unwrap()
                .into_complete()
                .unwrap();
            assert!(matches!(
                imported.engine.environment().find(&n("Lean.opaqueId")),
                Some(ConstantInfo::Opaque(_))
            ));
            let run = imported
                .engine
                .execute_source_commands_with_checks(
                    b"#eval Lean.opaqueId 42",
                    &KVMap::new(),
                    EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            let evaluation = run.batch.executions.last().unwrap();
            assert_eq!(
                closed_vm_value(&evaluation.exit).unwrap(),
                Some(ClosedVmValue::Scalar(42))
            );
            let replay =
                execute_flbc_artifact(&evaluation.flbc_artifact, &KVMap::new(), Default::default())
                    .unwrap()
                    .into_complete()
                    .unwrap();
            assert_eq!(
                closed_vm_value(&replay).unwrap(),
                Some(ClosedVmValue::Scalar(42))
            );
            // A public journal can omit initialized globals. Missing private
            // metadata must fail before any opaque's value becomes executable.
            let mut incomplete = all.clone();
            let owner = incomplete
                .iter_mut()
                .find(|module| module.name == &roots[0])
                .unwrap();
            owner.private_artifact = None;
            assert!(import(&incomplete, &roots, limits(1)).is_err());
        });
    }

    /// The per-call registration functions, one row at a time: the semantics a
    /// batched [`instances::imported::ImportActivation`] must equal.
    pub(super) struct Sequential(Environment);
    impl Registrar for Sequential {
        fn new(env: Environment) -> Self {
            Sequential(env)
        }
        fn environment(&self) -> &Environment {
            &self.0
        }
        fn register_class(
            self,
            class: &Name,
            parameters: &instances::imported::ClassParameters,
        ) -> std::result::Result<Self, InstanceRegistryError> {
            instances::imported::register_class(&self.0, class, parameters).map(Sequential)
        }
        fn register_instance(
            self,
            declaration: &Name,
            parameters: &instances::imported::InstanceParameters,
        ) -> std::result::Result<Self, InstanceRegistryError> {
            instances::imported::register_instance(&self.0, declaration, parameters).map(Sequential)
        }
        fn register_default(
            self,
            declaration: &Name,
            priority: u32,
        ) -> std::result::Result<Self, InstanceRegistryError> {
            instances::defaults::register(&self.0, declaration, priority).map(Sequential)
        }
        fn register_alias(
            self,
            alias: &Name,
            declaration: &Name,
        ) -> std::result::Result<Self, fln_elab::aliases::AliasError> {
            fln_elab::aliases::register(&self.0, alias, declaration).map(Sequential)
        }
        fn register_protected(
            self,
            declarations: &[Name],
        ) -> std::result::Result<Self, fln_elab::protected_names::ProtectedError> {
            fln_elab::protected_names::register_module(&self.0, declarations).map(Sequential)
        }
        fn register_namespaces(
            self,
            names: &[Name],
        ) -> std::result::Result<Self, InstanceRegistryError> {
            fln_elab::namespaces::register_module(&self.0, names).map(Sequential)
        }
        fn register_aux_recursors(
            self,
            declarations: &[Name],
        ) -> std::result::Result<Self, fln_elab::aux_recursors::AuxRecursorError> {
            fln_elab::aux_recursors::register_module(&self.0, declarations).map(Sequential)
        }
        fn register_delaborator_tags(
            self,
            tags: &[fln_elab::delaborator_tags::DelaboratorTag],
        ) -> std::result::Result<Self, fln_elab::delaborator_tags::DelaboratorTagError> {
            fln_elab::delaborator_tags::register_module(&self.0, tags).map(Sequential)
        }
        fn register_deprecations(
            self,
            entries: &[fln_elab::deprecations::Deprecation],
        ) -> std::result::Result<Self, fln_elab::deprecations::DeprecationError> {
            fln_elab::deprecations::register_module(&self.0, entries).map(Sequential)
        }
        fn register_noncomputable(
            self,
            declaration: &Name,
        ) -> std::result::Result<Self, fln_elab::noncomputable::NoncomputableError> {
            fln_elab::noncomputable::register(&self.0, declaration).map(Sequential)
        }
        fn register_defeq(
            self,
            declaration: &Name,
        ) -> std::result::Result<Self, fln_elab::NatDefinitionElabError> {
            fln_elab::source::scope::simp::defeq::register_imported(&self.0, declaration)
                .map(Sequential)
        }
        fn register_backward_defeq(
            self,
            declaration: &Name,
        ) -> std::result::Result<Self, fln_elab::NatDefinitionElabError> {
            fln_elab::source::scope::simp::defeq::register_backward(&self.0, declaration)
                .map(Sequential)
        }
        fn register_reducibility(
            self,
            declaration: &Name,
            status: fln_elab::reducibility::Reducibility,
        ) -> std::result::Result<Self, fln_elab::reducibility::ReducibilityError> {
            fln_elab::reducibility::register(&self.0, declaration, status).map(Sequential)
        }
        fn register_extern(
            self,
            declaration: &Name,
            entries: Vec<fln_elab::externs::ExternEntry>,
        ) -> std::result::Result<Self, fln_elab::externs::ExternError> {
            fln_elab::externs::register(&self.0, declaration, entries).map(Sequential)
        }
        fn register_implemented_by(
            self,
            declaration: &Name,
            implementation: &Name,
        ) -> std::result::Result<Self, fln_elab::implemented_by::ImplementedByError> {
            fln_elab::implemented_by::register(&self.0, declaration, implementation).map(Sequential)
        }
        fn register_macro_inline(
            self,
            declaration: &Name,
        ) -> std::result::Result<Self, fln_elab::macro_inline::MacroInlineError> {
            fln_elab::macro_inline::register(&self.0, declaration).map(Sequential)
        }
        fn register_structures(
            self,
            rows: &[fln_elab::records::imported::StructureEntry],
        ) -> std::result::Result<Self, fln_elab::records::RecordError> {
            fln_elab::records::imported::register(&self.0, rows).map(Sequential)
        }
        fn finish(self) -> std::result::Result<Environment, InstanceRegistryError> {
            Ok(self.0)
        }
    }

    /// Activating a real closure's metadata through one batched activation gives the
    /// environment, metadata reports, roots and per-module journals that registering
    /// each row through the per-call functions gives (bead `fln-uyuz`). The closure's
    /// declarations are admitted once by the council; the second, identical checked
    /// set comes from the reuse rebuild, which re-proves it by root.
    #[test]
    fn batched_metadata_activation_equals_one_registration_at_a_time() {
        let Some(lib) = pinned_lib() else {
            eprintln!("SKIP: pinned Reference lib/lean absent");
            return;
        };
        let roots = ["Init.Data.Cast", "Init.Data.Option.Coe", "Init.Data.Zero"];
        let closure = closure(&lib, &roots);
        let inputs = inputs(&closure);
        let roots: Vec<Name> = roots.iter().map(|root| n(root)).collect();
        on_import_stack(|| {
            let base = Engine::from_environment(Environment::new());
            let batched = import(&inputs, &roots, limits(1))
                .expect("the pinned closure imports")
                .into_complete()
                .expect("the pinned closure imports completely");
            assert!(
                batched.modules.iter().any(|report| report.instances > 0)
                    && batched.modules.iter().any(|report| report.classes > 0),
                "the closure carries class and instance metadata"
            );
            let checker = super::super::reuse::CheckerIdentity::of_executable(b"sequential");
            let key = super::super::reuse::ImportClosureKey::compute(
                &inputs,
                &roots,
                &KVMap::new(),
                checker,
            );
            let record = super::super::reuse::ImportReuseRecord::from_admission(
                key,
                checker,
                &KVMap::new(),
                &batched,
            )
            .expect("the admission is recordable");
            let rebuilt = base
                .rebuild_for_test(&inputs, &record)
                .expect("the council's closure re-proves");
            let sequential = base
                .activate_source_metadata_with::<Sequential>(
                    rebuilt,
                    &inputs,
                    &roots,
                    &KVMap::new(),
                    limits(1),
                    None,
                )
                .expect("one registration at a time activates")
                .into_complete()
                .expect("one registration at a time activates completely");
            assert!(
                batched.engine.environment == sequential.engine.environment,
                "the batched and per-call environments differ"
            );
            assert_eq!(batched.result_logical_root, sequential.result_logical_root);
            assert_eq!(batched.modules, sequential.modules);
            assert_eq!(
                batched.contexts.complete.environment, sequential.contexts.complete.environment,
                "complete contexts"
            );

            // A skipped check is invisible on valid metadata, so plant invalid rows
            // over the activated environment: both registrars must refuse each one
            // the same way, and accept the valid control the same way.
            fn outcome<R: Registrar>(
                env: &Environment,
                step: impl Fn(R) -> std::result::Result<R, InstanceRegistryError>,
            ) -> std::result::Result<Environment, InstanceRegistryError> {
                step(R::new(env.clone())).and_then(R::finish)
            }
            let activated = &batched.engine.environment;
            let global = instances::imported::InstanceParameters {
                priority: 1000,
                synth_order: Vec::new(),
                scope: None,
                keys: Vec::new(),
            };
            let scoped = instances::imported::InstanceParameters {
                scope: Some(n("Planted.Scope")),
                ..global.clone()
            };
            type Answer = std::result::Result<Environment, InstanceRegistryError>;
            type Case<'a> = Box<dyn Fn(&Environment) -> (Answer, Answer) + 'a>;
            let cases: Vec<(&str, Case<'_>)> = vec![
                (
                    "a global instance re-registered as scoped",
                    Box::new(|env: &Environment| {
                        let declaration = n("instInhabitedNat");
                        (
                            outcome::<instances::imported::ImportActivation>(env, |r| {
                                r.register_instance(&declaration, &scoped)
                            }),
                            outcome::<Sequential>(env, |r| {
                                r.register_instance(&declaration, &scoped)
                            }),
                        )
                    }),
                ),
                (
                    "a declaration that is not an instance",
                    Box::new(|env: &Environment| {
                        let declaration = n("Nat.add");
                        (
                            outcome::<instances::imported::ImportActivation>(env, |r| {
                                r.register_instance(&declaration, &global)
                            }),
                            outcome::<Sequential>(env, |r| {
                                r.register_instance(&declaration, &global)
                            }),
                        )
                    }),
                ),
                (
                    "a non-instance declaration registered as a default",
                    Box::new(|env: &Environment| {
                        let declaration = n("Nat.add");
                        (
                            outcome::<instances::imported::ImportActivation>(env, |r| {
                                r.register_default(&declaration, 100)
                            }),
                            outcome::<Sequential>(env, |r| r.register_default(&declaration, 100)),
                        )
                    }),
                ),
                (
                    "a default candidate registered twice is preserved",
                    Box::new(|env: &Environment| {
                        let declaration = n("instInhabitedNat");
                        (
                            outcome::<instances::imported::ImportActivation>(env, |r| {
                                r.register_default(&declaration, 100)?
                                    .register_default(&declaration, 100)
                            }),
                            outcome::<Sequential>(env, |r| {
                                r.register_default(&declaration, 100)?
                                    .register_default(&declaration, 100)
                            }),
                        )
                    }),
                ),
                (
                    "the valid control: a global upsert of a registered instance",
                    Box::new(|env: &Environment| {
                        let declaration = n("instInhabitedNat");
                        (
                            outcome::<instances::imported::ImportActivation>(env, |r| {
                                r.register_instance(&declaration, &global)
                            }),
                            outcome::<Sequential>(env, |r| {
                                r.register_instance(&declaration, &global)
                            }),
                        )
                    }),
                ),
            ];
            let mut refused = 0;
            for (case, run) in &cases {
                let (batched, sequential) = run(activated);
                assert!(
                    batched == sequential,
                    "{case}: batched {:?}, per-call {:?}",
                    batched.as_ref().err(),
                    sequential.as_ref().err()
                );
                refused += usize::from(batched.is_err());
            }
            assert_eq!(
                refused, 3,
                "three invalid rows are refused; ordinary upserts and repeated defaults succeed"
            );
        });
    }

    /// A refused or exhausted closure is refused the same way at any job count.
    #[test]
    fn a_broken_real_closure_is_refused_identically_at_one_and_several_jobs() {
        let Some(lib) = pinned_lib() else {
            eprintln!("SKIP: pinned Reference lib/lean absent");
            return;
        };
        let roots = ["Init.Data.Cast", "Init.Data.Option.Coe", "Init.Data.Zero"];
        let mut closure = closure(&lib, &roots);
        let roots: Vec<Name> = roots.iter().map(|root| n(root)).collect();
        let roots = roots.as_slice();
        let refusal = |inputs: &[OleanModuleInput<'_>],
                       limits: &dyn Fn(usize) -> SourceOleanImportLimits| {
            let answers: Vec<OleanCheckError> = [1, 3]
                .into_iter()
                .map(|threads| {
                    let limits = limits(threads);
                    match on_import_stack(move || import(inputs, roots, limits)) {
                        Err(SourceOleanImportError::Check(error)) => *error,
                        other => {
                            panic!("{threads} threads: expected a council refusal, got {other:?}")
                        }
                    }
                })
                .collect();
            assert_eq!(answers[0], answers[1]);
            answers[0].clone()
        };

        // A member missing from the set.
        let without_coe: Vec<_> = inputs(&closure)
            .into_iter()
            .filter(|input| *input.name != n("Init.Coe"))
            .collect();
        assert!(matches!(
            refusal(&without_coe, &limits),
            OleanCheckError::MissingModuleImports { .. }
        ));

        // A planning budget the first module exceeds: the serial door's error,
        // which the frontier would report as a resource non-answer instead.
        let tight = |threads: usize| {
            let mut tight = limits(threads);
            tight.check.max_declarations = 100;
            tight
        };
        assert!(matches!(
            refusal(&inputs(&closure), &tight),
            OleanCheckError::DeclarationLimit { limit: 100, .. }
        ));

        // A corrupted member.
        let coe = closure
            .iter()
            .position(|(name, _)| *name == n("Init.Coe"))
            .expect("Init.Coe is in the closure");
        closure[coe].1[0][0] ^= u8::MAX;
        assert!(matches!(
            refusal(&inputs(&closure), &limits),
            OleanCheckError::ModuleDecode { .. }
        ));
    }
}
