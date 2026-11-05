//! Per-module external worlds assembled only from retained council-checked entries.
//! Native metadata is replayed in the same mixed source/artifact postorder as
//! declarations. A sibling's imports are never an ambient source environment.
use super::*;
use fln_env::environment::EnvironmentEntry;
use std::sync::Arc;

#[derive(Debug)]
struct PublicModule {
    decoded: Arc<DecodedOlean>,
    before: Environment,
    after: Environment,
    same_syntax: bool,
}

#[derive(Debug)]
struct ExternalModule {
    imports: Vec<Name>,
    import_specs: Vec<OleanModuleImport>,
    is_module: bool,
    companion_parts_loaded: bool,
    entries: Vec<EnvironmentEntry>,
    unavailable: bool,
    before: Environment,
    after: Environment,
    public: Option<PublicModule>,
}

/// Private provenance, independent of the public, caller-editable import report.
#[derive(Debug)]
pub(super) struct ImportContexts {
    origin: Engine,
    declarations: Engine,
    pub(super) complete: Engine,
    modules: BTreeMap<Name, ExternalModule>,
    declaration_order: Vec<Name>,
    check_limits: Option<OleanCheckLimits>,
}

#[derive(Debug, Clone)]
pub(super) enum Step {
    Source(usize, bool),
    External(Name, bool),
}

/// The data part of the pin's import lattice. A later edge can upgrade a
/// module's visibility without moving its first-discovery journal position.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
struct ImportFlags {
    all: bool,
    exported: bool,
    data: bool,
}

impl ImportFlags {
    fn child(self, edge: &OleanModuleImport, legacy: bool) -> Self {
        Self {
            all: legacy || self.all && edge.import_all,
            exported: self.exported && edge.is_exported,
            data: self.data && (edge.is_exported || self.all),
        }
    }

    fn join(self, other: Self) -> Self {
        Self {
            all: self.all || other.all,
            exported: self.exported || other.exported,
            data: self.data || other.data,
        }
    }
}

fn source_imports(header: &SourceHeader) -> Vec<OleanModuleImport> {
    let implicit = header.imports.len() - header.import_specs.len();
    header.imports[..implicit]
        .iter()
        .map(|module| OleanModuleImport {
            module: module.clone(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        })
        .chain(header.import_specs.iter().map(|import| OleanModuleImport {
            module: import.module.clone(),
            import_all: import.all_at.is_some(),
            is_exported: !header.module_system || import.public_at.is_some(),
            is_meta: import.meta_at.is_some(),
        }))
        .collect()
}

#[derive(Clone, Copy)]
enum Projection {
    Local,
    Exported,
    Runtime { exported_roots: bool },
}

/// Source-only checking uses the same flag joins and journal order as mixed
/// source/artifact checking; source bytes and private cache stamps own its data.
pub(super) fn source_order(
    index: usize,
    plan: &graph::Plan,
    modules: &[SourceModuleInput<'_>],
    meter: &mut Meter,
    public_root: bool,
) -> Result<Vec<Step>, SourceModuleCheckError> {
    order_in(
        None,
        index,
        plan,
        modules,
        meter,
        if public_root {
            Projection::Exported
        } else {
            Projection::Local
        },
    )
}

fn order_in(
    contexts: Option<&ImportContexts>,
    index: usize,
    plan: &graph::Plan,
    modules: &[SourceModuleInput<'_>],
    meter: &mut Meter,
    projection: Projection,
) -> Result<Vec<Step>, SourceModuleCheckError> {
    enum Visit {
        Enter(Name, ImportFlags),
        Finish(Name),
    }
    meter.work(modules.len())?;
    let local: BTreeMap<_, _> = modules
        .iter()
        .enumerate()
        .map(|(i, module)| (module.name, i))
        .collect();
    if let Some(contexts) = contexts {
        for module in modules {
            if contexts.modules.contains_key(module.name)
                || contexts.origin.imported_modules().contains(module.name)
            {
                return Err(SourceModuleCheckError::DuplicateModule(module.name.clone()));
            }
        }
    }
    let public_root = matches!(projection, Projection::Exported);
    let legacy =
        matches!(projection, Projection::Runtime { .. }) || !plan.headers[index].module_system;
    let root = ImportFlags {
        all: true,
        exported: true,
        data: true,
    };
    let mut imports = source_imports(&plan.headers[index]);
    if matches!(
        projection,
        Projection::Runtime {
            exported_roots: true
        }
    ) {
        imports.retain(|edge| edge.is_exported);
    }
    meter.work(imports.len())?;
    let mut pending: Vec<_> = imports
        .iter()
        .rev()
        .map(|edge| Visit::Enter(edge.module.clone(), root.child(edge, legacy)))
        .collect();
    let mut flags = BTreeMap::<Name, ImportFlags>::new();
    let mut order = Vec::new();
    while let Some(visit) = pending.pop() {
        meter.work(1)?;
        let (name, incoming) = match visit {
            Visit::Enter(name, incoming) => (name, incoming),
            Visit::Finish(name) => {
                order.push(name);
                continue;
            }
        };
        if !incoming.data {
            continue;
        }
        let old = flags.get(&name).copied();
        let merged = old.unwrap_or_default().join(incoming);
        if old == Some(merged) {
            continue;
        }
        let imports = if let Some(&source) = local.get(&name) {
            source_imports(&plan.headers[source])
        } else if let Some(contexts) = contexts {
            if let Some(module) = contexts.modules.get(&name) {
                module.import_specs.clone()
            } else if contexts.origin.imported_modules().contains(&name) {
                continue;
            } else {
                return Err(SourceModuleCheckError::MissingModule {
                    importer: modules[index].name.clone(),
                    module: name,
                });
            }
        } else {
            // Plan::new already checked that this is a named import admitted
            // by the immutable base. Modern use requires a retained receipt.
            continue;
        };
        flags.insert(name.clone(), merged);
        if old.is_none() {
            pending.push(Visit::Finish(name));
        }
        meter.work(imports.len())?;
        pending.extend(
            imports
                .iter()
                .rev()
                .map(|edge| Visit::Enter(edge.module.clone(), merged.child(edge, legacy))),
        );
    }
    let mut selected = Vec::new();
    for name in order {
        let flags = flags[&name];
        if public_root && !flags.exported {
            continue;
        }
        let private = !public_root && flags.all;
        if let Some(&source) = local.get(&name) {
            if source != index {
                selected.push(Step::Source(source, private));
            }
        } else {
            selected.push(Step::External(name, private));
        }
    }
    Ok(selected)
}

/// Inputs already validated by the source graph. The implementation closure
/// is separate from logical visibility and never contributes lookup constants.
pub(super) struct ImportReplay<'a> {
    pub(super) base: &'a Engine,
    pub(super) contexts: Option<&'a ImportContexts>,
    pub(super) index: usize,
    pub(super) plan: &'a graph::Plan,
    pub(super) modules: &'a [SourceModuleInput<'a>],
    pub(super) options: &'a KVMap,
    pub(super) cancellation: Option<&'a dyn CancellationProbe>,
    pub(super) exported_roots: bool,
}

/// Retain the checked implementation and metadata-validation contexts after
/// exact logical import replay. Both use the same selected source root, never
/// the unrelated union of roots present in an artifact receipt.
pub(super) fn finish_imports<'e>(
    mut logical: Engine,
    request: ImportReplay<'_>,
    export: impl Fn(usize) -> &'e replay::Export,
    meter: &mut Meter,
) -> Result<Outcome<Engine>, SourceModuleCheckError> {
    if !request.plan.headers[request.index].module_system {
        return Ok(Outcome::Complete(logical));
    }
    let steps = order_in(
        request.contexts,
        request.index,
        request.plan,
        request.modules,
        meter,
        Projection::Runtime {
            exported_roots: request.exported_roots,
        },
    )?;
    if steps.is_empty() {
        return Ok(Outcome::Complete(logical));
    }
    let mut private = match request.contexts {
        Some(contexts) => {
            match contexts.project(&steps, request.options, meter, request.cancellation)? {
                Outcome::Complete(engine) => engine,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            }
        }
        None => request.base.clone(),
    };
    let sources: BTreeSet<_> = steps
        .iter()
        .filter_map(|step| match step {
            Step::Source(dependency, _) => Some(*dependency),
            Step::External(_, _) => None,
        })
        .collect();
    for &dependency in &request.plan.order {
        if !sources.contains(&dependency) {
            continue;
        }
        private = match export(dependency).for_import(true).replay_declarations(
            private,
            request.modules[dependency].name,
            request.options,
            meter,
            request.cancellation,
        )? {
            Outcome::Complete(engine) => engine,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
    }
    for step in &steps {
        let replayed = match step {
            Step::Source(dependency, _) => export(*dependency).for_import(true).replay_metadata(
                private,
                request.modules[*dependency].name,
                meter,
                request.cancellation,
            )?,
            Step::External(name, _) => request
                .contexts
                .expect("external runtime imports have checked provenance")
                .replay_metadata(name, true, private, meter, request.cancellation)?,
        };
        private = match replayed {
            Outcome::Complete(engine) => engine,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
    }
    logical.environment = logical
        .environment
        .with_imported_metadata_validation(private.environment());
    let public_base = logical.environment.clone();
    Ok(Outcome::Complete(
        logical.with_checked_runtime_imports(public_base, &private),
    ))
}

fn exported_header_agrees(exported: &ConstantInfo, private: &ConstantInfo) -> bool {
    if exported == private {
        return true;
    }
    let ConstantInfo::Axiom(header) = exported else {
        return false;
    };
    if &header.base != private.constant_val() {
        return false;
    }
    let unsafe_body = match private {
        ConstantInfo::Defn(value) => value.safety == DefinitionSafety::Unsafe,
        ConstantInfo::Thm(_) => false,
        ConstantInfo::Opaque(value) => value.is_unsafe,
        _ => return false,
    };
    header.is_unsafe == unsafe_body
}

fn unavailable(module: &Name, reason: &'static str) -> SourceModuleCheckError {
    SourceModuleCheckError::ImportContext {
        module: module.clone(),
        reason,
    }
}

impl ImportContexts {
    pub(super) fn has_inherited_imports(&self) -> bool {
        !self.origin.imported_modules().is_empty() || self.origin.has_checked_runtime_imports()
    }

    /// Public checking reports are observations, not editable provenance.
    /// Parser preparation must still match the private declarations and import
    /// graph captured at admission, before consulting any report fields.
    pub(super) fn retains_checked_module(&self, checked: &CheckedOleanModule) -> bool {
        self.modules.get(&checked.name).is_some_and(|module| {
            !module.unavailable
                && module.is_module == checked.decoded.module.is_module
                && module.companion_parts_loaded == checked.decoded.companion_parts_loaded
                && module.import_specs == checked.decoded.module.imports
                && module.entries.len() == checked.decoded.constants.len()
                && module
                    .entries
                    .iter()
                    .zip(&checked.decoded.constants)
                    .all(|(entry, constant)| entry.declaration() == constant)
        })
    }

    pub(super) fn capture(
        origin: &Engine,
        complete: &Engine,
        checked: &CheckedOleanSet,
        mut journals: BTreeMap<Name, (Environment, Environment)>,
    ) -> Self {
        let modules = checked
            .modules
            .iter()
            .map(|module| {
                let mut entries = Vec::new();
                let mut unavailable = false;
                for constant in &module.decoded.constants {
                    match checked.engine.environment.entry(constant.name()) {
                        Some(entry) if entry.declaration() == constant => entries.push(entry),
                        // A subsuming repeat can have a different proof. Never take
                        // an unrelated module's proof just because its name agrees.
                        _ => unavailable = true,
                    }
                }
                let (before, after) = journals
                    .remove(&module.name)
                    .expect("each replayed module has one metadata snapshot");
                (
                    module.name.clone(),
                    ExternalModule {
                        imports: module
                            .decoded
                            .module
                            .imports
                            .iter()
                            .map(|i| i.module.clone())
                            .collect(),
                        import_specs: module.decoded.module.imports.clone(),
                        is_module: module.decoded.module.is_module,
                        companion_parts_loaded: module.decoded.companion_parts_loaded,
                        entries,
                        unavailable,
                        before,
                        after,
                        public: None,
                    },
                )
            })
            .collect();
        Self {
            origin: origin.clone(),
            declarations: checked.engine.clone(),
            complete: complete.clone(),
            modules,
            declaration_order: checked
                .modules
                .iter()
                .map(|module| module.name.clone())
                .collect(),
            check_limits: None,
        }
    }

    /// Pair actual primary-part declarations and journals with the complete
    /// artifact receipt. A public header is never synthesized from a body.
    pub(super) fn retain_public(
        &mut self,
        mut exported: BTreeMap<Name, DecodedOlean>,
        public: Option<(Self, BTreeSet<Name>)>,
        checked: &CheckedOleanSet,
        limits: OleanCheckLimits,
    ) -> Result<(), imported::SourceOleanImportError> {
        if exported.is_empty() && public.is_none() {
            return Ok(());
        }
        let (mut public, same_syntax) =
            public.ok_or(imported::SourceOleanImportError::Internal(
                "exported artifacts have no matching metadata capture",
            ))?;
        let checked_modules: BTreeMap<_, _> = checked
            .modules
            .iter()
            .map(|module| (&module.name, &module.decoded))
            .collect();
        for (name, module) in &mut self.modules {
            let decoded =
                exported
                    .remove(name)
                    .ok_or(imported::SourceOleanImportError::Internal(
                        "missing exported declaration snapshot",
                    ))?;
            let journals =
                public
                    .modules
                    .remove(name)
                    .ok_or(imported::SourceOleanImportError::Internal(
                        "missing exported metadata snapshot",
                    ))?;
            if decoded.module.imports != module.import_specs
                || decoded.module.is_module != module.is_module
                || journals.import_specs != module.import_specs
                || journals.is_module != module.is_module
            {
                return Err(imported::SourceOleanImportError::Internal(
                    "exported and private module headers disagree",
                ));
            }
            // A repeated theorem can have another checked proof representative
            // in the aggregate environment. Compare the exact private artifact
            // that the council checked, not an unrelated representative entry.
            let private =
                checked_modules
                    .get(name)
                    .ok_or(imported::SourceOleanImportError::Internal(
                        "exported snapshot has no completed private artifact check",
                    ))?;
            let implementations: BTreeMap<_, _> = private
                .constants
                .iter()
                .map(|constant| (constant.name(), constant))
                .collect();
            for constant in &decoded.constants {
                let private = implementations.get(constant.name());
                if !private.is_some_and(|private| exported_header_agrees(constant, private)) {
                    return Err(imported::SourceOleanImportError::Metadata {
                        module: name.clone(),
                        declaration: constant.name().clone(),
                        reason: "exported declaration does not match its checked private implementation",
                    });
                }
            }
            module.public = Some(PublicModule {
                decoded: Arc::new(decoded),
                before: journals.before,
                after: journals.after,
                same_syntax: same_syntax.contains(name),
            });
        }
        if !exported.is_empty() || !public.modules.is_empty() {
            return Err(imported::SourceOleanImportError::Internal(
                "exported snapshots escaped the checked module set",
            ));
        }
        self.check_limits = Some(limits);
        Ok(())
    }

    /// Two captures, field by field: each retained engine and, per module, its
    /// imports, exact checked entries, availability and metadata snapshots.
    #[cfg(test)]
    pub(super) fn assert_identical(&self, other: &Self, what: &str) {
        crate::assert_engines_identical(&self.origin, &other.origin, &format!("{what}: origin"));
        crate::assert_engines_identical(
            &self.declarations,
            &other.declarations,
            &format!("{what}: declarations"),
        );
        crate::assert_engines_identical(
            &self.complete,
            &other.complete,
            &format!("{what}: complete"),
        );
        assert_eq!(
            self.modules.keys().collect::<Vec<_>>(),
            other.modules.keys().collect::<Vec<_>>(),
            "{what}: modules"
        );
        assert_eq!(
            self.declaration_order, other.declaration_order,
            "{what}: declaration order"
        );
        assert_eq!(
            self.check_limits.is_some(),
            other.check_limits.is_some(),
            "{what}: checked view limits"
        );
        for ((name, left), right) in self.modules.iter().zip(other.modules.values()) {
            let module = name.to_display_string();
            assert_eq!(left.imports, right.imports, "{what}: {module}: imports");
            assert_eq!(
                left.import_specs, right.import_specs,
                "{what}: {module}: import specifications"
            );
            assert_eq!(
                left.is_module, right.is_module,
                "{what}: {module}: module system"
            );
            assert_eq!(
                left.companion_parts_loaded, right.companion_parts_loaded,
                "{what}: {module}: companions"
            );
            assert!(left.entries == right.entries, "{what}: {module}: entries");
            assert_eq!(
                left.unavailable, right.unavailable,
                "{what}: {module}: availability"
            );
            assert!(left.before == right.before, "{what}: {module}: before");
            assert!(left.after == right.after, "{what}: {module}: after");
            match (&left.public, &right.public) {
                (Some(left), Some(right)) => {
                    assert_eq!(
                        left.same_syntax, right.same_syntax,
                        "{what}: {module}: syntax projection"
                    );
                    assert_eq!(
                        left.decoded, right.decoded,
                        "{what}: {module}: exported declarations"
                    );
                    assert!(
                        left.before == right.before,
                        "{what}: {module}: exported before"
                    );
                    assert!(
                        left.after == right.after,
                        "{what}: {module}: exported after"
                    );
                }
                (None, None) => {}
                _ => panic!("{what}: {module}: different exported snapshot availability"),
            }
        }
    }

    pub(super) fn order(
        &self,
        index: usize,
        plan: &graph::Plan,
        modules: &[SourceModuleInput<'_>],
        meter: &mut Meter,
    ) -> Result<Vec<Step>, SourceModuleCheckError> {
        order_in(Some(self), index, plan, modules, meter, Projection::Local)
    }

    pub(super) fn public_order(
        &self,
        index: usize,
        plan: &graph::Plan,
        modules: &[SourceModuleInput<'_>],
        meter: &mut Meter,
    ) -> Result<Vec<Step>, SourceModuleCheckError> {
        order_in(
            Some(self),
            index,
            plan,
            modules,
            meter,
            Projection::Exported,
        )
    }

    /// The optional macro/parser product currently binds one journal per
    /// module. Reuse it for an exported view only when that exact journal is
    /// unchanged; a distinct private grammar needs its own checked product.
    pub(super) fn require_syntax_views(
        &self,
        steps: &[Step],
    ) -> Result<(), SourceModuleCheckError> {
        for step in steps {
            let Step::External(name, false) = step else {
                continue;
            };
            let module = &self.modules[name];
            if module.is_module
                && !module
                    .public
                    .as_ref()
                    .is_some_and(|public| public.same_syntax)
            {
                return Err(unavailable(
                    name,
                    "distinct exported and private macro/parser journals require separate checked syntax products",
                ));
            }
        }
        Ok(())
    }

    pub(super) fn project(
        &self,
        steps: &[Step],
        options: &KVMap,
        meter: &mut Meter,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<Engine>, SourceModuleCheckError> {
        meter.work(steps.len())?;
        let selected: BTreeMap<_, _> = steps
            .iter()
            .filter_map(|step| match step {
                Step::External(name, private) => Some((name, *private)),
                Step::Source(_, _) => None,
            })
            .collect();
        // Preserve the complete council projection, including subsumed proof
        // representatives, only for the exact full private declaration set.
        if selected.len() == self.modules.len()
            && selected
                .iter()
                .all(|(name, private)| *private || !self.modules[*name].is_module)
        {
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                    "source-modules/project-import",
                )));
            }
            return Ok(Outcome::Complete(self.declarations.clone()));
        }
        let mut engine = self.origin.clone();
        let bound = engine.environment == Environment::new()
            || engine.imported_environment.as_ref() == Some(&engine.environment);
        let mut imported = (*engine.imported_modules).clone();
        let mut dependencies = (*engine.imported_module_dependencies).clone();
        // Declaration readiness follows the checked dependency order. Journal
        // replay separately retains first discovery even after an all-upgrade.
        for name in &self.declaration_order {
            let Some(&private) = selected.get(name) else {
                continue;
            };
            let module = &self.modules[name];
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                    "source-modules/project-import",
                )));
            }
            if module.is_module && !private {
                let public = module.public.as_ref().ok_or_else(|| {
                    unavailable(
                        name,
                        "the retained import has no checked exported-file provenance",
                    )
                })?;
                meter.work(public.decoded.constants.len())?;
                let mut limits = self.check_limits.ok_or_else(|| {
                    unavailable(
                        name,
                        "the retained import has no exported-file admission limits",
                    )
                })?;
                limits.admission = meter.limits.source.admission;
                engine =
                    match engine.check_decoded_olean((*public.decoded).clone(), options, limits) {
                        Ok(Outcome::Complete(checked)) => checked.engine,
                        Ok(Outcome::Inconclusive(reason)) => {
                            return Ok(Outcome::Inconclusive(reason));
                        }
                        Ok(Outcome::InternalFault(fault)) => {
                            return Ok(Outcome::InternalFault(fault));
                        }
                        Err(error) => match fln_admission::frontier_error_verdict(error) {
                            fln_admission::OleanModuleVerdict::Inconclusive(reason) => {
                                return Ok(Outcome::Inconclusive(reason));
                            }
                            fln_admission::OleanModuleVerdict::InternalFault(fault) => {
                                return Ok(Outcome::InternalFault(fault));
                            }
                            fln_admission::OleanModuleVerdict::Failed(error) => {
                                return Err(SourceModuleCheckError::ImportDeclarations {
                                    module: name.clone(),
                                    error: Box::new(error),
                                });
                            }
                            _ => {
                                return Err(unavailable(
                                    name,
                                    "an exported declaration check returned no verdict",
                                ));
                            }
                        },
                    };
            } else {
                if module.unavailable {
                    return Err(unavailable(
                        name,
                        "an exact checked declaration snapshot for this import is unavailable",
                    ));
                }
                for entry in &module.entries {
                    meter.work(1)?;
                    if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                        return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                            "source-modules/project-import",
                        )));
                    }
                    engine.environment = crate::merge_frontier_entry(engine.environment, entry)
                        .map_err(|_| {
                            unavailable(name, "conflicting checked import declarations")
                        })?;
                }
                // A projection of a strict subset has no inherited independent
                // checker map; ordinary admission reconstructs its exact map.
                engine.checker_environment = None;
            }
            imported.insert(name.clone());
            dependencies.insert(name.clone(), module.imports.clone());
        }
        engine.imported_modules = Arc::new(imported);
        engine.imported_module_dependencies = Arc::new(dependencies);
        engine.imported_environment = bound.then(|| engine.environment.clone());
        Ok(Outcome::Complete(engine))
    }

    pub(super) fn replay_metadata(
        &self,
        name: &Name,
        private: bool,
        engine: Engine,
        meter: &mut Meter,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<Engine>, SourceModuleCheckError> {
        let module = &self.modules[name];
        let (before, after) = if module.is_module && !private {
            let public = module.public.as_ref().ok_or_else(|| {
                unavailable(
                    name,
                    "the retained import has no exported metadata provenance",
                )
            })?;
            (&public.before, &public.after)
        } else {
            (&module.before, &module.after)
        };
        let export = replay::Export::capture(name, before, after, Vec::new(), meter)?;
        let mut engine = match export.replay_metadata(engine, name, meter, cancellation)? {
            Outcome::Complete(engine) => engine,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        for entry in &module.entries {
            meter.work(1)?;
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                    "source-modules/replay-executable-metadata",
                )));
            }
            let declaration = entry.declaration().name();
            if !engine.environment.contains(declaration) {
                continue;
            }
            if self.complete.executable_opaques.contains(declaration) {
                Arc::make_mut(&mut engine.executable_opaques).insert(declaration.clone());
            }
            if self.complete.runtime_initializers.contains(declaration) {
                Arc::make_mut(&mut engine.runtime_initializers).insert(declaration.clone());
            }
        }
        Ok(Outcome::Complete(engine))
    }
}

impl imported::SourceOleanImport {
    /// Check each source module in its own declared import world. The retained
    /// import receipt, not caller-mutated public report fields, owns the bases.
    /// Modern modules require a receipt whose origin has no inherited imports
    /// or earlier runtime import binding; a raw/incremental Engine lacks the
    /// exported-file provenance needed to reconstruct those views faithfully.
    pub fn check_source_modules(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceModuleCheckLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
        cache::run_collecting(
            &self.contexts.complete,
            modules,
            entry,
            options,
            limits,
            cancellation,
            cache::RunOptions {
                cache: None,
                collect_artifacts: false,
                contexts: Some(&self.contexts),
                records: None,
                macros: None,
            },
        )
        .map(|outcome| outcome.map_complete(|run| run.result.checked))
    }

    /// Encode only after the whole source graph has passed both checkers in
    /// exact import contexts. Unsupported source metadata still fails closed.
    pub fn compile_source_modules(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceModuleCheckLimits,
        write_budget: OleanWriteBudget,
    ) -> Result<Outcome<SourceModuleBuild>, SourceModuleBuildError> {
        let base = &self.contexts.complete;
        if base.imported_environment.as_ref() != Some(base.environment()) {
            return Err(SourceModuleBuildError::UnboundBase);
        }
        let run = cache::run_collecting(
            base,
            modules,
            entry,
            options,
            limits,
            None,
            cache::RunOptions {
                cache: None,
                collect_artifacts: true,
                contexts: Some(&self.contexts),
                records: None,
                macros: None,
            },
        )
        .map_err(SourceModuleBuildError::Check)?;
        match run {
            Outcome::Complete(run) => artifacts::finish(run, write_budget).map(Outcome::Complete),
            Outcome::Inconclusive(reason) => Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => Ok(Outcome::InternalFault(fault)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::imported_parsers::{ParserRegistrationError, ParserRegistryLimits};
    use crate::source_check::modules::imported::{SourceOleanImport, SourceOleanImportLimits};
    use fln_core::expr::{Expr, Literal, NatLit};
    use fln_env::constants::{
        ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
    };
    use fln_olean::format;
    use fln_olean::write::{ModuleWriteInput, OleanWriteHeader, WriteBudget, encode_module};

    fn name(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    fn definition(label: &str, value: Expr) -> ConstantInfo {
        ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: name(label),
                level_params: Vec::new(),
                type_: Expr::const_(name("Nat"), Vec::new()),
            },
            value,
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![name(label)],
        })
    }

    fn natural(value: u64) -> Expr {
        Expr::lit(Literal::Nat(NatLit::from_u64(value)))
    }

    fn import(module: &str) -> OleanModuleImport {
        OleanModuleImport {
            module: name(module),
            import_all: false,
            is_exported: false,
            is_meta: false,
        }
    }

    /// Real codec and council admission retain three distinct artifact owners.
    /// Consumer imports Original; Sibling is a separate root and cannot supply
    /// parser helpers to Consumer merely because both appear in the receipt.
    fn receipt() -> SourceOleanImport {
        let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
        let seed = Engine::with_source_seed(admission)
            .unwrap()
            .into_complete()
            .unwrap();
        let specs = [
            (
                name("Original"),
                Vec::new(),
                vec![
                    definition("Original.helper", natural(1)),
                    definition("Original.other", natural(2)),
                ],
            ),
            (
                name("Consumer"),
                vec![import("Original")],
                vec![definition(
                    "Consumer.owner",
                    Expr::const_(name("Original.helper"), Vec::new()),
                )],
            ),
            (
                name("Sibling"),
                Vec::new(),
                vec![definition("Sibling.helper", natural(3))],
            ),
        ];
        let bytes: Vec<_> = specs
            .iter()
            .map(|(_, imports, constants)| {
                encode_module(
                    ModuleWriteInput {
                        is_module: false,
                        imports,
                        constants,
                        extra_const_names: &[],
                    },
                    OleanWriteHeader {
                        version: format::OLEAN_ACCEPTED_VERSIONS[0],
                        flags: 1,
                        lean_version: format::PIN_TAG.strip_prefix('v').unwrap(),
                        githash: format::PIN_COMMIT,
                        base_addr: (format::REGION_ALIGN * 2) as u64,
                    },
                    WriteBudget::default(),
                )
                .unwrap()
                .bytes
            })
            .collect();
        let inputs: Vec<_> = specs
            .iter()
            .zip(&bytes)
            .map(|((name, _, _), artifact)| OleanModuleInput {
                name,
                artifact,
                server_artifact: None,
                private_artifact: None,
            })
            .collect();
        seed.import_olean_modules_for_source(
            &inputs,
            &[name("Consumer"), name("Sibling")],
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                bytes.iter().map(Vec::len).sum(),
                admission.kernel,
            )),
        )
        .unwrap()
        .into_complete()
        .unwrap()
    }

    fn assert_original(receipt: &SourceOleanImport) {
        let parsers = receipt
            .prepare_imported_parsers(ParserRegistryLimits::default())
            .unwrap();
        let product = parsers
            .project_imports(
                &[name("Original"), name("Consumer"), name("Sibling")],
                &receipt.engine,
            )
            .unwrap();
        assert!(product.is_empty());
        for module in &receipt.checked.modules {
            assert!(receipt.contexts.retains_checked_module(module));
        }
    }

    fn assert_owner_refusal(receipt: &SourceOleanImport, module: &str) {
        let error = receipt
            .prepare_imported_parsers(ParserRegistryLimits::default())
            .unwrap_err();
        assert!(!error.is_resource(), "{error:?}");
        assert!(
            matches!(&error, ParserRegistrationError::Owner { module: owner, reason, .. }
                if *owner == name(module)
                    && *reason == "public checking report differs from retained parser ownership"),
            "{error:?}"
        );
    }

    #[test]
    fn parser_receipts_bind_original_imports_and_module_parts() {
        let mut receipt = receipt();
        assert_original(&receipt);
        let index = receipt
            .checked
            .modules
            .iter()
            .position(|module| module.name == name("Consumer"))
            .unwrap();
        let original = receipt.checked.modules[index].decoded.clone();
        let base = receipt.engine.logical_root(&KVMap::new());
        for mutation in 0..7 {
            receipt.checked.modules[index].decoded = original.clone();
            let decoded = &mut receipt.checked.modules[index].decoded;
            match mutation {
                0 => decoded.module.imports.push(import("Sibling")),
                1 => decoded.module.imports[0].module = name("Sibling"),
                2 => decoded.module.imports[0].import_all = true,
                3 => decoded.module.imports[0].is_exported = true,
                4 => decoded.module.imports[0].is_meta = true,
                5 => decoded.module.is_module = !decoded.module.is_module,
                6 => decoded.companion_parts_loaded = !decoded.companion_parts_loaded,
                _ => unreachable!(),
            }
            assert_owner_refusal(&receipt, "Consumer");
            assert_eq!(receipt.engine.logical_root(&KVMap::new()), base);
        }
        receipt.checked.modules[index].decoded = original;
        assert_original(&receipt);
    }

    #[test]
    fn parser_receipts_bind_owner_values_and_original_module_assignment() {
        let mut receipt = receipt();
        assert_original(&receipt);
        let index = receipt
            .checked
            .modules
            .iter()
            .position(|module| module.name == name("Original"))
            .unwrap();
        let original = receipt.checked.modules[index].decoded.clone();
        let sibling = receipt
            .engine
            .environment()
            .find(&name("Sibling.helper"))
            .unwrap()
            .clone();
        for mutation in 0..5 {
            receipt.checked.modules[index].decoded = original.clone();
            let constants = &mut receipt.checked.modules[index].decoded.constants;
            match mutation {
                0 => constants.push(sibling.clone()),
                1 => constants[0] = sibling.clone(),
                2 => constants[0] = definition("Original.helper", natural(99)),
                3 => constants.swap(0, 1),
                4 => constants.truncate(1),
                _ => unreachable!(),
            }
            assert_owner_refusal(&receipt, "Original");
            assert_eq!(
                receipt.engine.environment().find(sibling.name()),
                Some(&sibling)
            );
        }
        receipt.checked.modules[index].decoded = original;
        assert_original(&receipt);
    }

    #[test]
    fn parser_receipts_bound_public_reports_before_owner_comparison() {
        let mut receipt = receipt();
        let original = receipt.checked.modules[0].decoded.clone();
        let first = &receipt.checked.modules[0];
        receipt.checked.modules.push(CheckedOleanModule {
            name: name("Forged"),
            decoded: first.decoded.clone(),
            base_logical_root: first.base_logical_root,
            result_logical_root: first.result_logical_root,
            declarations: Vec::new(),
        });
        let limits = ParserRegistryLimits {
            max_modules: 3,
            ..ParserRegistryLimits::default()
        };
        assert!(matches!(
            receipt.prepare_imported_parsers(limits),
            Err(ParserRegistrationError::Limit("modules"))
        ));
        receipt.checked.modules.pop();
        receipt.checked.modules[0].decoded.constants[0] = definition("Forged.owner", natural(0));
        let limits = ParserRegistryLimits {
            max_declarations: 0,
            ..ParserRegistryLimits::default()
        };
        assert!(matches!(
            receipt.prepare_imported_parsers(limits),
            Err(ParserRegistrationError::Limit("owner declarations"))
        ));
        receipt.checked.modules[0].decoded = original;
        assert_original(&receipt);
    }
}
