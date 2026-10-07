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
            metadata: DecodeLimits::default(),
            capture: OleanWalkBudget::default(),
            max_capture_bytes: check.max_total_bytes.max(64 * 1024 * 1024),
            max_roots: 256,
            jobs: OleanFrontierJobs::SERIAL,
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
    /// `protected` declarations (the pin's `protectedExt`), activated so that an
    /// atomic identifier does not resolve to one.
    pub protected: usize,
    /// Reducibility statuses (the pin's `reducibilityCore`), activated for the
    /// `instances` transparency instance selection runs at.
    pub reducibility: usize,
    /// Explicit native-call intentions (the pin's `Lean.externAttr`), retained
    /// only for this module's own admitted declarations.
    pub externs: usize,
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
        ]
        .map(|name| Name::from_components(name.split('.')));
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
        // Each module's capture reads only its own parts, so the walks run
        // `limits.jobs` at once; the cumulative byte allowance is charged below in
        // replay order, exactly as when one walk followed another.
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
                protected: 0,
                reducibility: 0,
                externs: 0,
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
                    entries_left = entries_left
                        .checked_sub(block.entries.len())
                        .ok_or(SourceOleanImportError::Limit("metadata entries"))?;
                    match kind {
                        0 => report.classes = block.entries.len(),
                        1 => report.instances = block.entries.len(),
                        2 => report.defaults = block.entries.len(),
                        3 => report.aliases = block.entries.len(),
                        4 => report.protected = block.entries.len(),
                        5 => report.reducibility = block.entries.len(),
                        6 => report.externs = block.entries.len(),
                        _ => {
                            return Err(SourceOleanImportError::Internal(
                                "unknown selected metadata kind",
                            ));
                        }
                    }
                    // Move payloads, not copies. Decoding once gives all modules
                    // one cumulative byte/object/index allowance.
                    blocks[kind].entries.extend(block.entries);
                } else if !block.entries.is_empty() {
                    report.uninterpreted.push(block.name);
                }
            }
            reports.push(report);
        }
        cancelled!("source-olean/before-metadata-decode");
        let decoded =
            metadata::decode(&blocks, limits.metadata).map_err(SourceOleanImportError::Decode)?;
        let mut classes = decoded.classes.into_iter();
        let mut instances = decoded.instances.into_iter();
        let mut defaults = decoded.defaults.into_iter();
        let mut aliases = decoded.aliases.into_iter();
        let mut protected = decoded.protected.into_iter();
        let mut reducibility = decoded.reducibility.into_iter();
        let mut externs = decoded.externs.into_iter();
        let mut engine = checked.engine.clone();
        let bound = engine.imported_environment.as_ref() == Some(&engine.environment);
        let mut journals = BTreeMap::new();
        // One activation for the whole closure: the registries are read once and
        // kept current, rather than re-read and re-validated before every row.
        let mut activation = R::new(engine.environment.clone());
        for (&index, report) in order.iter().zip(&mut reports) {
            let before = activation.environment().clone();
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
                let mut owners = ExternOwners::new(
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
            journals.insert(
                report.module.clone(),
                (before, activation.environment().clone()),
            );
        }
        engine.environment = activation.finish().map_err(|_| {
            SourceOleanImportError::Internal(
                "the activated registries disagree with their kept state",
            )
        })?;
        if classes.next().is_some()
            || instances.next().is_some()
            || defaults.next().is_some()
            || aliases.next().is_some()
            || protected.next().is_some()
            || reducibility.next().is_some()
            || externs.next().is_some()
        {
            return Err(SourceOleanImportError::Internal(
                "decoded metadata escaped its module inventory",
            ));
        }
        cancelled!("source-olean/before-publication");
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

/// Every module's extension payloads, in replay `order`, `limits.jobs` modules at
/// once. Each walk may use the whole capture allowance; the caller charges the
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
    let threads = limits.jobs.threads.get().min(order.len());
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
    fn register_protected(
        self,
        declarations: &[Name],
    ) -> std::result::Result<Self, fln_elab::protected_names::ProtectedError>;
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
    fn finish(self) -> std::result::Result<Environment, InstanceRegistryError> {
        self.finish()
    }
}

/// A decoded stored `DiscrTree.Key` as the native instance index holds it.
fn instance_key(key: metadata::InstanceKey) -> instances::discr_tree::Key {
    use instances::discr_tree::Key;
    use metadata::InstanceKey;
    match key {
        InstanceKey::Star => Key::Star,
        InstanceKey::Other => Key::Other,
        InstanceKey::Lit(literal) => Key::Lit(literal),
        InstanceKey::FVar(name, arity) => Key::FVar(fln_core::expr::FVarId(name), arity),
        InstanceKey::Const(name, arity) => Key::Const(name, arity),
        InstanceKey::Arrow => Key::Arrow,
        InstanceKey::Proj(name, field, arity) => Key::Proj(name, field, arity),
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

/// Extern attributes cannot be applied to an imported declaration at the pin.
/// Retain the exact checked owner, rather than accepting any ambient name that
/// happens to have the expected spelling. Both allocations are bounded before
/// construction; the index exists only for a module with extern rows.
struct ExternOwners<'a> {
    declarations: Vec<&'a ConstantInfo>,
    seen: HashSet<Name>,
}

impl<'a> ExternOwners<'a> {
    fn new(
        constants: &'a [ConstantInfo],
        rows: usize,
        max_declarations: usize,
        max_entries: usize,
    ) -> Result<Self> {
        if constants.len() > max_declarations {
            return Err(SourceOleanImportError::Limit(
                "extern declaration ownership index",
            ));
        }
        if rows > max_entries {
            return Err(SourceOleanImportError::Limit(
                "extern attribute ownership rows",
            ));
        }
        let mut declarations = Vec::new();
        declarations
            .try_reserve_exact(constants.len())
            .map_err(|_| {
                SourceOleanImportError::Limit("extern declaration ownership allocation")
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
                "checked module repeats an extern owner declaration",
            ));
        }
        let mut seen = HashSet::new();
        seen.try_reserve(rows)
            .map_err(|_| SourceOleanImportError::Limit("extern attribute ownership allocation"))?;
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
                error("an extern attribute does not belong to this module's checked declarations")
            })?;
        if env.find(declaration) != Some(self.declarations[position]) {
            return Err(error(
                "an extern owner differs from its active admitted declaration",
            ));
        }
        if !self.seen.insert(declaration.clone()) {
            return Err(error(
                "duplicate extern attribute for one module declaration",
            ));
        }
        Ok(())
    }
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
        let lib = std::env::var_os("HOME")
            .map(std::path::PathBuf::from)
            .map(|home| {
                home.join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{OLEAN_PIN_TAG}"))
                    .join("lib/lean")
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
        SourceOleanImportLimits {
            jobs: OleanFrontierJobs {
                threads: NonZeroUsize::new(threads).expect("a positive thread count"),
                worker_stack_bytes: STACK,
            },
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
                    "a default candidate registered twice",
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
                "three planted rows are refused, the control is not"
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
