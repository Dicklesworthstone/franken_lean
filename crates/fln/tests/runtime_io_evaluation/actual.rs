//! Actual IO artifact metadata for diagnostics only; no module admission.
//! This fixture never creates import receipts or verified reuse entries.
use super::*;
use fln_core::level::Level;
use fln_elab::instances::{self, imported::ImportActivation};
use fln_olean::region::{OleanView, OpaqueExtensionBlock};
use fln_olean::source_extensions as metadata;
use std::collections::BTreeSet;

struct Module {
    imports: Vec<Name>,
    constants: BTreeMap<Name, ConstantInfo>,
    blocks: Vec<OpaqueExtensionBlock>,
}

pub(super) struct SourceFixture {
    pub(super) engine: Engine,
    pub(super) owners: BTreeMap<Name, BTreeSet<Name>>,
}

fn replay_order(modules: &BTreeMap<Name, Module>, root: &Name) -> Vec<Name> {
    let mut colors = BTreeMap::new();
    colors.insert(root.clone(), 1u8);
    let mut pending = vec![(root.clone(), 0usize)];
    let mut order = Vec::new();
    while let Some((module, next)) = pending.last_mut() {
        let current = modules.get(module).expect("complete actual import closure");
        if let Some(import) = current.imports.get(*next) {
            *next += 1;
            match colors.get(import).copied().unwrap_or_default() {
                0 => {
                    colors.insert(import.clone(), 1);
                    pending.push((import.clone(), 0));
                }
                1 => panic!("cycle in pinned artifact imports: {import:?}"),
                _ => {}
            }
        } else {
            colors.insert(module.clone(), 2);
            order.push(module.clone());
            pending.pop();
        }
    }
    assert_eq!(order.len(), modules.len(), "no unrelated ambient modules");
    order
}

fn retain_actual_constant(constants: &mut BTreeMap<Name, ConstantInfo>, info: &ConstantInfo) {
    let replace = match constants.get(info.name()) {
        None => true,
        Some(previous) if previous == info => false,
        Some(previous) => {
            // The actual pin repeats theorem statements, sometimes first as a
            // safe axiom. Retain a serialized proof only for the same statement
            // and mutual-name envelope. This is not declaration admission.
            assert_eq!(previous.constant_val(), info.constant_val());
            match (previous, info) {
                (ConstantInfo::Thm(first), ConstantInfo::Thm(second)) => {
                    assert_eq!(first.all, second.all);
                    false
                }
                (ConstantInfo::Axiom(first), ConstantInfo::Thm(second))
                    if !first.is_unsafe
                        && second.all.as_slice() == std::slice::from_ref(&second.base.name) =>
                {
                    true
                }
                (ConstantInfo::Thm(first), ConstantInfo::Axiom(second))
                    if !second.is_unsafe
                        && first.all.as_slice() == std::slice::from_ref(&first.base.name) =>
                {
                    false
                }
                _ => panic!("unsupported raw-fixture duplicate: {:?}", info.name()),
            }
        }
    };
    if replace {
        constants.insert(info.name().clone(), info.clone());
    }
}

fn instance_key(key: metadata::InstanceKey) -> instances::discr_tree::Key {
    use instances::discr_tree::Key;
    match key {
        metadata::InstanceKey::Star => Key::Star,
        metadata::InstanceKey::Other => Key::Other,
        metadata::InstanceKey::Lit(literal) => Key::Lit(literal),
        metadata::InstanceKey::FVar(name, arity) => Key::FVar(fln_core::expr::FVarId(name), arity),
        metadata::InstanceKey::Const(name, arity) => Key::Const(name, arity),
        metadata::InstanceKey::Arrow => Key::Arrow,
        metadata::InstanceKey::Proj(name, field, arity) => Key::Proj(name, field, arity),
    }
}

fn reducibility(status: metadata::ReducibilityStatus) -> fln_elab::reducibility::Reducibility {
    use fln_elab::reducibility::Reducibility;
    match status {
        metadata::ReducibilityStatus::Reducible => Reducibility::Reducible,
        metadata::ReducibilityStatus::Semireducible => Reducibility::Semireducible,
        metadata::ReducibilityStatus::Irreducible => Reducibility::Irreducible,
        metadata::ReducibilityStatus::ImplicitReducible => Reducibility::ImplicitReducible,
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

pub(super) fn decoded_io_with_source_metadata(library: &Path) -> SourceFixture {
    let root = name("Init.System.IO");
    let artifacts = artifacts(library, &root);
    eprintln!(
        "Actual pinned IO artifact closure: {} modules",
        artifacts.len()
    );
    let limits =
        SourceOleanImportLimits::new(OleanCheckLimits::new(BYTES, Budget::for_stack_bytes(STACK)));
    let mut modules = BTreeMap::new();
    let mut constants = BTreeMap::new();
    for (module, (public, server, private)) in &artifacts {
        let decoded = fln::decode_olean_module_artifacts(
            public,
            server.as_deref().unwrap_or_default(),
            private.as_deref().unwrap_or_default(),
            OleanDecodeLimits::new(BYTES),
        )
        .unwrap();
        let view = if decoded.module.is_module {
            OleanView::parse_with_dependencies(
                private.as_deref().expect("module private part"),
                &[
                    public.as_slice(),
                    server.as_deref().expect("module server part"),
                ],
            )
        } else {
            OleanView::parse(public)
        }
        .unwrap();
        // Split artifacts contain cumulative journals; only the final private
        // part is replayed, exactly as in production metadata activation.
        let blocks = view
            .extension_payloads(limits.capture, limits.max_capture_bytes)
            .unwrap();
        let mut owners = BTreeMap::new();
        for info in decoded.constants {
            assert!(owners.insert(info.name().clone(), info.clone()).is_none());
            retain_actual_constant(&mut constants, &info);
        }
        modules.insert(
            module.clone(),
            Module {
                imports: decoded
                    .module
                    .imports
                    .into_iter()
                    .map(|import| import.module)
                    .collect(),
                constants: owners,
                blocks,
            },
        );
    }
    drop(artifacts);
    let constant_count = constants.len();
    let mut environment = Environment::new();
    for info in constants.into_values() {
        environment = environment.add_decl(info).unwrap();
    }
    let order = replay_order(&modules, &root);
    let selected = [
        metadata::CLASS_EXTENSION,
        metadata::INSTANCE_EXTENSION,
        metadata::DEFAULT_EXTENSION,
        metadata::ALIAS_EXTENSION,
        metadata::PROTECTED_EXTENSION,
        metadata::REDUCIBILITY_EXTENSION,
        metadata::EXTERN_EXTENSION,
    ]
    .map(name);
    let mut blocks: Vec<_> = selected
        .iter()
        .map(|name| OpaqueExtensionBlock {
            name: name.clone(),
            entries: Vec::new(),
        })
        .collect();
    let mut counts = Vec::new();
    let mut capture_left = limits.max_capture_bytes;
    let mut entries_left = limits.metadata.max_entries;
    for module in &order {
        let mut seen = BTreeSet::new();
        let mut count = [0usize; 7];
        for block in std::mem::take(&mut modules.get_mut(module).unwrap().blocks) {
            assert!(seen.insert(block.name.clone()), "duplicate extension block");
            for payload in &block.entries {
                capture_left = capture_left
                    .checked_sub(payload.len())
                    .expect("capture budget");
            }
            if let Some(kind) = selected.iter().position(|name| name == &block.name) {
                count[kind] = block.entries.len();
                entries_left = entries_left
                    .checked_sub(count[kind])
                    .expect("metadata entry budget");
                blocks[kind].entries.extend(block.entries);
            }
        }
        counts.push(count);
    }
    let decoded = metadata::decode(&blocks, limits.metadata).unwrap();
    let mut classes = decoded.classes.into_iter();
    let mut instances = decoded.instances.into_iter();
    let mut defaults = decoded.defaults.into_iter();
    let mut aliases = decoded.aliases.into_iter();
    let mut protected = decoded.protected.into_iter();
    let mut reductions = decoded.reducibility.into_iter();
    let mut externs = decoded.externs.into_iter();
    let mut activation = ImportActivation::new(environment);
    for (module, count) in order.iter().zip(&counts) {
        for _ in 0..count[0] {
            let row = classes.next().unwrap();
            activation = activation
                .register_class(
                    &row.name,
                    &instances::imported::ClassParameters {
                        out_params: row.out_params,
                        out_level_params: row.out_level_params,
                    },
                )
                .unwrap();
        }
        for _ in 0..count[1] {
            let row = instances.next().unwrap();
            let info = activation.environment().find(&row.declaration).unwrap();
            let expected = Expr::const_(
                row.declaration.clone(),
                info.constant_val()
                    .level_params
                    .iter()
                    .cloned()
                    .map(Level::param)
                    .collect(),
            );
            assert_eq!(row.value, expected, "actual generic instance declaration");
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
                .unwrap();
        }
        for _ in 0..count[2] {
            let row = defaults.next().unwrap();
            let info = activation.environment().find(&row.declaration).unwrap();
            let (_, class) =
                instances::instance_telescope(activation.environment(), &info.constant_val().type_)
                    .unwrap();
            assert_eq!(class, row.class, "actual default instance class");
            activation = activation
                .register_default(&row.declaration, row.priority)
                .unwrap();
        }
        for _ in 0..count[3] {
            let row = aliases.next().unwrap();
            activation = activation
                .register_alias(&row.alias, &row.declaration)
                .unwrap();
        }
        let tags: Vec<_> = protected.by_ref().take(count[4]).collect();
        assert_eq!(tags.len(), count[4]);
        activation = activation.register_protected(&tags).unwrap();
        for _ in 0..count[5] {
            let row = reductions.next().unwrap();
            activation = activation
                .register_reducibility(&row.declaration, reducibility(row.status))
                .unwrap();
        }
        let mut seen_externs = BTreeSet::new();
        for _ in 0..count[6] {
            let row = externs.next().unwrap();
            let owned = modules[module]
                .constants
                .get(&row.declaration)
                .expect("extern belongs to its actual artifact module");
            assert_eq!(
                activation.environment().find(&row.declaration),
                Some(owned),
                "actual active extern owner"
            );
            assert!(
                seen_externs.insert(row.declaration.clone()),
                "duplicate module extern"
            );
            activation = activation
                .register_extern(
                    &row.declaration,
                    row.entries.into_iter().map(extern_entry).collect(),
                )
                .unwrap();
        }
    }
    assert!(
        classes.next().is_none()
            && instances.next().is_none()
            && defaults.next().is_none()
            && aliases.next().is_none()
            && protected.next().is_none()
            && reductions.next().is_none()
            && externs.next().is_none()
    );
    let environment = activation.finish().unwrap();
    let totals = counts.iter().fold([0usize; 7], |mut totals, count| {
        for (total, count) in totals.iter_mut().zip(count) {
            *total += count;
        }
        totals
    });
    assert!(totals[0] > 0 && totals[1] > 0 && totals[5] > 0 && totals[6] > 0);
    eprintln!(
        "RAW DECODED IO WITH ACTUAL SOURCE METADATA, NOT MODULE ADMISSION: {} modules, {constant_count} declarations; class/instance/default/alias/protected/reducibility/extern rows {totals:?}",
        order.len()
    );
    SourceFixture {
        engine: Engine::from_environment(environment),
        owners: modules
            .into_iter()
            .map(|(module, data)| (module, data.constants.into_keys().collect()))
            .collect(),
    }
}
