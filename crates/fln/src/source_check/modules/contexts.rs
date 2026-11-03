//! Per-module external worlds assembled only from retained council-checked entries.
//! Native metadata is replayed in the same mixed source/artifact postorder as
//! declarations. A sibling's imports are never an ambient source environment.
use super::*;
use fln_env::environment::EnvironmentEntry;
use std::sync::Arc;

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
}

/// Private provenance, independent of the public, caller-editable import report.
#[derive(Debug)]
pub(super) struct ImportContexts {
    origin: Engine,
    declarations: Engine,
    pub(super) complete: Engine,
    modules: BTreeMap<Name, ExternalModule>,
}

pub(super) enum Step {
    Source(usize),
    External(Name),
}

fn unavailable(module: &Name, reason: &'static str) -> SourceModuleCheckError {
    SourceModuleCheckError::ImportContext {
        module: module.clone(),
        reason,
    }
}

impl ImportContexts {
    pub(super) fn has_inherited_imports(&self) -> bool {
        !self.origin.imported_modules().is_empty()
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
                    },
                )
            })
            .collect();
        Self {
            origin: origin.clone(),
            declarations: checked.engine.clone(),
            complete: complete.clone(),
            modules,
        }
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
        }
    }

    /// One heap DFS handles both kinds of import, so a local registration
    /// between two external imports stays between them. Shared imports run once.
    pub(super) fn order(
        &self,
        index: usize,
        plan: &graph::Plan,
        modules: &[SourceModuleInput<'_>],
        meter: &mut Meter,
    ) -> Result<Vec<Step>, SourceModuleCheckError> {
        self.order_in(index, plan, modules, meter, false)
    }

    pub(super) fn public_order(
        &self,
        index: usize,
        plan: &graph::Plan,
        modules: &[SourceModuleInput<'_>],
        meter: &mut Meter,
    ) -> Result<Vec<Step>, SourceModuleCheckError> {
        self.order_in(index, plan, modules, meter, true)
    }

    fn order_in(
        &self,
        index: usize,
        plan: &graph::Plan,
        modules: &[SourceModuleInput<'_>],
        meter: &mut Meter,
        public_root: bool,
    ) -> Result<Vec<Step>, SourceModuleCheckError> {
        meter.work(modules.len())?;
        let local: BTreeMap<_, _> = modules
            .iter()
            .enumerate()
            .map(|(i, m)| (m.name, i))
            .collect();
        for module in modules {
            if self.modules.contains_key(module.name)
                || self.origin.imported_modules().contains(module.name)
            {
                return Err(SourceModuleCheckError::DuplicateModule(module.name.clone()));
            }
        }
        let mut seen = BTreeSet::new();
        let mut pending = vec![(modules[index].name.clone(), false)];
        let mut order = Vec::new();
        while let Some((name, finish)) = pending.pop() {
            meter.work(1)?;
            if finish {
                if let Some(&source) = local.get(&name) {
                    if source != index {
                        order.push(Step::Source(source));
                    }
                } else if self.modules.contains_key(&name) {
                    order.push(Step::External(name));
                }
                continue;
            }
            if !seen.insert(name.clone()) {
                continue;
            }
            let imports = if let Some(&source) = local.get(&name) {
                if source != index || public_root {
                    plan.visible_imports(source)
                } else {
                    &plan.headers[source].imports
                }
            } else if let Some(module) = self.modules.get(&name) {
                &module.imports
            } else if self.origin.imported_modules().contains(&name) {
                continue;
            } else {
                return Err(SourceModuleCheckError::MissingModule {
                    importer: modules[index].name.clone(),
                    module: name,
                });
            };
            meter.work(imports.len())?;
            pending.push((name, true));
            pending.extend(imports.iter().rev().cloned().map(|name| (name, false)));
        }
        Ok(order)
    }

    pub(super) fn project(
        &self,
        steps: &[Step],
        meter: &mut Meter,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<Engine>, SourceModuleCheckError> {
        meter.work(steps.len())?;
        // The private planner emits each external module once. When the whole
        // set is present, retain its original council projection, including the
        // chosen representative of subsumed repeated proofs. This is not a
        // subset reconstruction and must not require identical raw copies.
        if steps
            .iter()
            .filter(|step| matches!(step, Step::External(_)))
            .count()
            == self.modules.len()
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
        for step in steps {
            let Step::External(name) = step else { continue };
            let module = &self.modules[name];
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
                    .map_err(|_| unavailable(name, "conflicting checked import declarations"))?;
            }
            imported.insert(name.clone());
            dependencies.insert(name.clone(), module.imports.clone());
        }
        // The full closure's checker projection is not valid for a subset. The
        // ordinary admission path constructs a checker for the projected world.
        engine.checker_environment = None;
        engine.imported_modules = Arc::new(imported);
        engine.imported_module_dependencies = Arc::new(dependencies);
        engine.imported_environment = bound.then(|| engine.environment.clone());
        Ok(Outcome::Complete(engine))
    }

    pub(super) fn replay_metadata(
        &self,
        name: &Name,
        engine: Engine,
        options: &KVMap,
        meter: &mut Meter,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<Engine>, SourceModuleCheckError> {
        let module = &self.modules[name];
        let export =
            replay::Export::capture(name, &module.before, &module.after, Vec::new(), meter)?;
        let mut engine = match export.replay(engine, name, options, meter, cancellation)? {
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
