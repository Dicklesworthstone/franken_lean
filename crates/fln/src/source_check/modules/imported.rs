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
use std::collections::{BTreeMap, BTreeSet};

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
}
impl SourceOleanImportLimits {
    pub fn new(check: OleanCheckLimits) -> Self {
        Self {
            check,
            metadata: DecodeLimits::default(),
            capture: OleanWalkBudget::default(),
            max_capture_bytes: 64 * 1024 * 1024,
            max_roots: 256,
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
    pub uninterpreted: Vec<Name>,
}

#[derive(Debug)]
pub struct SourceOleanImport {
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
    Capture { module: Name, error: OleanRegionError },
    Decode(metadata::DecodeError),
    Registry { module: Name, declaration: Name, error: InstanceRegistryError },
    Metadata { module: Name, declaration: Name, reason: &'static str },
    Internal(&'static str),
}
impl std::fmt::Display for SourceOleanImportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Check(error) => error.fmt(f),
            Self::EmptyRoots => f.write_str("source import requires at least one root module"),
            Self::MissingRoot(name) => write!(f, "missing source import root {}", name.to_display_string()),
            Self::UnreachableModule(name) => write!(f, "module {} is outside the source import closure", name.to_display_string()),
            Self::Limit(resource) => write!(f, "source import exceeded {resource}"),
            Self::Capture { module, error } => write!(f, "module {} metadata capture: {error}", module.to_display_string()),
            Self::Decode(error) => error.fmt(f),
            Self::Registry { module, declaration, error } => write!(f, "module {} metadata for {}: {error}", module.to_display_string(), declaration.to_display_string()),
            Self::Metadata { module, declaration, reason } => write!(f, "module {} metadata for {}: {reason}", module.to_display_string(), declaration.to_display_string()),
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
    /// before publication. The existing bounded council is not interrupted mid-call.
    pub fn import_olean_modules_for_source_with_cancel(
        &self,
        modules: &[OleanModuleInput<'_>],
        roots: &[Name],
        options: &KVMap,
        limits: SourceOleanImportLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<SourceOleanImport>> {
        if roots.is_empty() { return Err(SourceOleanImportError::EmptyRoots); }
        if roots.len() > limits.max_roots { return Err(SourceOleanImportError::Limit("import roots")); }
        macro_rules! cancelled {
            ($at:literal) => {
                if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                    return Ok(Outcome::Inconclusive(Inconclusive::cancelled($at)));
                }
            };
        }
        cancelled!("source-olean/before-council");
        let checked = match self.check_olean_modules(modules, options, limits.check)
            .map_err(|e| SourceOleanImportError::Check(Box::new(e)))? {
            Outcome::Complete(checked) => checked,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let order = replay_order(&checked, roots)?;
        let inputs: BTreeMap<_, _> = modules.iter().map(|m| (m.name, m)).collect();
        let selected = [metadata::CLASS_EXTENSION, metadata::INSTANCE_EXTENSION, metadata::DEFAULT_EXTENSION]
            .map(|name| Name::from_components(name.split('.')));
        let mut blocks: Vec<_> = selected.iter().map(|name| OpaqueExtensionBlock {
            name: name.clone(), entries: Vec::new(),
        }).collect();
        let mut reports = Vec::new();
        let mut capture_left = limits.max_capture_bytes;
        let mut entries_left = limits.metadata.max_entries;
        for &index in &order {
            cancelled!("source-olean/capture");
            let module = &checked.modules[index];
            let input = inputs.get(&module.name).ok_or(SourceOleanImportError::Internal("checked module lost its artifact"))?;
            let view = if module.decoded.module.is_module {
                let (Some(server), Some(private)) = (input.server_artifact, input.private_artifact) else {
                    return Err(SourceOleanImportError::Internal("checked module lost its companions"));
                };
                OleanView::parse_with_dependencies(private, &[input.artifact, server])
            } else {
                OleanView::parse(input.artifact)
            }.map_err(|error| SourceOleanImportError::Capture { module: module.name.clone(), error })?;
            let captured = view.extension_payloads(limits.capture, capture_left)
                .map_err(|error| SourceOleanImportError::Capture { module: module.name.clone(), error })?;
            let mut report = SourceMetadataReport {
                module: module.name.clone(), classes: 0, instances: 0, defaults: 0,
                scoped_instances: 0, uninterpreted: Vec::new(),
            };
            let mut seen = BTreeSet::new();
            for block in captured {
                if !seen.insert(block.name.clone()) {
                    return Err(SourceOleanImportError::Metadata { module: module.name.clone(), declaration: block.name, reason: "duplicate extension block" });
                }
                for payload in &block.entries {
                    capture_left = capture_left.checked_sub(payload.len())
                        .ok_or(SourceOleanImportError::Limit("captured extension bytes"))?;
                }
                if let Some(kind) = selected.iter().position(|name| name == &block.name) {
                    entries_left = entries_left.checked_sub(block.entries.len())
                        .ok_or(SourceOleanImportError::Limit("metadata entries"))?;
                    match kind {
                        0 => report.classes = block.entries.len(),
                        1 => report.instances = block.entries.len(),
                        _ => report.defaults = block.entries.len(),
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
        let decoded = metadata::decode(&blocks, limits.metadata).map_err(SourceOleanImportError::Decode)?;
        let mut classes = decoded.classes.into_iter();
        let mut instances = decoded.instances.into_iter();
        let mut defaults = decoded.defaults.into_iter();
        let mut engine = checked.engine.clone();
        let bound = engine.imported_environment.as_ref() == Some(&engine.environment);
        for report in &mut reports {
            for _ in 0..report.classes {
                cancelled!("source-olean/class");
                let row = classes.next().ok_or(SourceOleanImportError::Internal("class count changed during decode"))?;
                engine.environment = instances::imported::register_class(
                    &engine.environment, &row.name,
                    &instances::imported::ClassParameters { out_params: row.out_params, out_level_params: row.out_level_params },
                ).map_err(|error| registry_error(&report.module, &row.name, error))?;
            }
            for _ in 0..report.instances {
                cancelled!("source-olean/instance");
                let row = instances.next().ok_or(SourceOleanImportError::Internal("instance count changed during decode"))?;
                let info = engine.environment.find(&row.declaration).ok_or_else(|| registry_error(
                    &report.module, &row.declaration, InstanceRegistryError::UnknownDeclaration(row.declaration.clone()),
                ))?;
                let expected = Expr::const_(row.declaration.clone(), info.constant_val().level_params.iter().cloned().map(Level::param).collect());
                // The native registry instantiates a declaration at fresh levels.
                // It cannot faithfully replace a specialized/reordered expression.
                if row.value != expected {
                    return Err(SourceOleanImportError::Metadata { module: report.module.clone(), declaration: row.declaration, reason: "instance value is not its generic declaration" });
                }
                report.scoped_instances += usize::from(row.scope.is_some());
                engine.environment = instances::imported::register_instance(
                    &engine.environment, &row.declaration,
                    &instances::imported::InstanceParameters { priority: row.priority, synth_order: row.synth_order, scope: row.scope },
                ).map_err(|error| registry_error(&report.module, &row.declaration, error))?;
            }
            for _ in 0..report.defaults {
                cancelled!("source-olean/default");
                let row = defaults.next().ok_or(SourceOleanImportError::Internal("default count changed during decode"))?;
                let actual = engine.environment.find(&row.declaration)
                    .and_then(|info| instances::instance_telescope(&engine.environment, &info.constant_val().type_))
                    .map(|(_, class)| class);
                if actual.as_ref() != Some(&row.class) {
                    return Err(SourceOleanImportError::Metadata { module: report.module.clone(), declaration: row.declaration, reason: "default instance class does not match its checked type" });
                }
                engine.environment = instances::defaults::register(&engine.environment, &row.declaration, row.priority)
                    .map_err(|error| registry_error(&report.module, &row.declaration, error))?;
            }
        }
        if classes.next().is_some() || instances.next().is_some() || defaults.next().is_some() {
            return Err(SourceOleanImportError::Internal("decoded metadata escaped its module inventory"));
        }
        cancelled!("source-olean/before-publication");
        // Adding metadata changes the logical root, but not the declarations
        // represented by the retained independent-checker projection.
        if bound { engine.imported_environment = Some(engine.environment.clone()); }
        let result_logical_root = engine.logical_root(options);
        Ok(Outcome::Complete(SourceOleanImport { engine, checked, result_logical_root, modules: reports }))
    }
}

fn registry_error(module: &Name, declaration: &Name, error: InstanceRegistryError) -> SourceOleanImportError {
    SourceOleanImportError::Registry { module: module.clone(), declaration: declaration.clone(), error }
}

/// Import-order postorder, with each shared dependency replayed once. A caller
/// cannot smuggle unrelated module metadata in through an oversized input set.
fn replay_order(checked: &CheckedOleanSet, roots: &[Name]) -> Result<Vec<usize>> {
    let indices: BTreeMap<_, _> = checked.modules.iter().enumerate().map(|(i, m)| (&m.name, i)).collect();
    let mut colors = vec![0u8; checked.modules.len()];
    let mut order = Vec::new();
    for root in roots {
        let &index = indices.get(root).ok_or_else(|| SourceOleanImportError::MissingRoot(root.clone()))?;
        if colors[index] == 2 { continue; }
        colors[index] = 1;
        let mut stack = vec![(index, 0usize)];
        while let Some((index, next)) = stack.last_mut() {
            if let Some(import) = checked.modules[*index].decoded.module.imports.get(*next) {
                *next += 1;
                let &dependency = indices.get(&import.module).ok_or(SourceOleanImportError::Internal("checked import closure is incomplete"))?;
                match colors[dependency] {
                    0 => { colors[dependency] = 1; stack.push((dependency, 0)); }
                    1 => return Err(SourceOleanImportError::Internal("checked import graph has a cycle")),
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
        let index = colors.iter().position(|color| *color != 2)
            .ok_or(SourceOleanImportError::Internal("module order count mismatch"))?;
        return Err(SourceOleanImportError::UnreachableModule(checked.modules[index].name.clone()));
    }
    Ok(order)
}
