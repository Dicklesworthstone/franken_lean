//! Actual Hashable/UInt64 declarations, independently admitted from an empty Engine.
//! This is a selected-declaration fixture, not complete library admission.
//! No raw decoded constant or manufactured scalar declaration enters the Engine.
use super::*;
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{IndependentReading, OleanCheckLimits, OleanDecodeLimits};
use fln_elab::instances::{self, imported::ImportActivation};
use fln_olean::region::OleanView;
use fln_olean::source_extensions as metadata;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::path::Path;

fn references(expression: &Expr, names: &mut BTreeSet<Name>) {
    let mut pending = vec![expression];
    let mut seen = HashSet::new();
    while let Some(expression) = pending.pop() {
        if !seen.insert(expression.allocation_identity()) {
            continue;
        }
        assert!(seen.len() <= 1_000_000, "bounded actual fixture walk");
        match expression.node() {
            ExprNode::Const { name, .. } => {
                names.insert(name.clone());
            }
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } => pending.push(expr),
            ExprNode::Proj {
                struct_name, expr, ..
            } => {
                names.insert(struct_name.clone());
                pending.push(expr);
            }
            _ => {}
        }
    }
}

fn dependencies(info: &ConstantInfo, recursors: &BTreeMap<Vec<Name>, Vec<Name>>) -> BTreeSet<Name> {
    let mut names = BTreeSet::new();
    references(&info.constant_val().type_, &mut names);
    match info {
        ConstantInfo::Defn(value) => {
            references(&value.value, &mut names);
            names.extend(value.all.iter().cloned());
        }
        ConstantInfo::Thm(value) => {
            references(&value.value, &mut names);
            names.extend(value.all.iter().cloned());
        }
        ConstantInfo::Opaque(value) => {
            references(&value.value, &mut names);
            names.extend(value.all.iter().cloned());
        }
        ConstantInfo::Induct(value) => {
            names.extend(value.all.iter().cloned());
            names.extend(value.ctors.iter().cloned());
            names.extend(recursors.get(&value.all).into_iter().flatten().cloned());
        }
        ConstantInfo::Ctor(value) => {
            names.insert(value.induct.clone());
        }
        ConstantInfo::Rec(value) => {
            names.extend(value.all.iter().cloned());
            for rule in &value.rules {
                names.insert(rule.ctor.clone());
                references(&rule.rhs, &mut names);
            }
        }
        ConstantInfo::Axiom(_) | ConstantInfo::Quot(_) => {}
    }
    names
}

fn key(key: metadata::DiscrTreeKey) -> instances::discr_tree::Key {
    use instances::discr_tree::Key;
    match key {
        metadata::DiscrTreeKey::Star => Key::Star,
        metadata::DiscrTreeKey::Other => Key::Other,
        metadata::DiscrTreeKey::Lit(value) => Key::Lit(value),
        metadata::DiscrTreeKey::FVar(value, arity) => {
            Key::FVar(fln_core::expr::FVarId(value), arity)
        }
        metadata::DiscrTreeKey::Const(value, arity) => Key::Const(value, arity),
        metadata::DiscrTreeKey::Arrow => Key::Arrow,
        metadata::DiscrTreeKey::Proj(value, field, arity) => Key::Proj(value, field, arity),
    }
}

fn activate(
    mut activation: ImportActivation,
    data: metadata::SourceExtensions,
    selected: &BTreeSet<Name>,
) -> ImportActivation {
    for row in data
        .classes
        .into_iter()
        .filter(|row| selected.contains(&row.name))
    {
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
    for row in data
        .instances
        .into_iter()
        .filter(|row| selected.contains(&row.declaration))
    {
        let info = activation.environment().find(&row.declaration).unwrap();
        assert_eq!(
            row.value,
            Expr::const_(
                row.declaration.clone(),
                info.constant_val()
                    .level_params
                    .iter()
                    .cloned()
                    .map(fln_core::level::Level::param)
                    .collect(),
            )
        );
        activation = activation
            .register_instance(
                &row.declaration,
                &instances::imported::InstanceParameters {
                    priority: row.priority,
                    synth_order: row.synth_order,
                    scope: row.scope,
                    keys: row.keys.into_iter().map(key).collect(),
                },
            )
            .unwrap();
    }
    for row in data
        .aliases
        .into_iter()
        .filter(|row| selected.contains(&row.declaration))
    {
        activation = activation
            .register_alias(&row.alias, &row.declaration)
            .unwrap();
    }
    for row in data
        .reducibility
        .into_iter()
        .filter(|row| selected.contains(&row.declaration))
    {
        activation = activation
            .register_reducibility(
                &row.declaration,
                match row.status {
                    metadata::ReducibilityStatus::Reducible => Reducibility::Reducible,
                    metadata::ReducibilityStatus::Semireducible => Reducibility::Semireducible,
                    metadata::ReducibilityStatus::Irreducible => Reducibility::Irreducible,
                    metadata::ReducibilityStatus::ImplicitReducible => {
                        Reducibility::ImplicitReducible
                    }
                },
            )
            .unwrap();
    }
    activation
}

pub(super) fn admitted(library: &Path) -> Engine {
    let limits = SourceOleanImportLimits::new(OleanCheckLimits::new(BYTES, admission().kernel));
    let mut modules = Vec::new();
    let mut journals = Vec::new();
    // Every dependency of these selected declarations is in these two genuine
    // artifacts. Starting empty also checks the original Nat arithmetic used
    // by imported proofs; source seed arithmetic axioms cannot replace it.
    // Missing dependencies fail the closure walk. Raw decoding never admits.
    for module in ["Init/Prelude", "Init/Data/UInt/BasicAux"] {
        let path = library.join(module).with_extension("olean");
        let public = std::fs::read(&path).unwrap();
        let server = std::fs::read(path.with_extension("olean.server")).unwrap();
        let private = std::fs::read(path.with_extension("olean.private")).unwrap();
        let decoded = fln::decode_olean_module_artifacts(
            &public,
            &server,
            &private,
            OleanDecodeLimits::new(BYTES),
        )
        .expect("both readers decode the actual pinned artifacts");
        assert!(matches!(decoded.independent, IndependentReading::Read(_)));
        let view = OleanView::parse_with_dependencies(&private, &[&public, &server]).unwrap();
        let mut blocks = view
            .extension_payloads(limits.capture, limits.max_capture_bytes)
            .unwrap();
        let wanted = [
            metadata::CLASS_EXTENSION,
            metadata::INSTANCE_EXTENSION,
            metadata::ALIAS_EXTENSION,
            metadata::REDUCIBILITY_EXTENSION,
        ]
        .map(name);
        blocks.retain(|block| wanted.contains(&block.name));
        journals.push(metadata::decode(&blocks, limits.metadata).unwrap());
        modules.push(decoded);
    }
    let mut engine = Engine::builder().build_empty();
    let constants: BTreeMap<_, _> = modules
        .iter()
        .flat_map(|module| &module.constants)
        .map(|info| (info.name().clone(), info))
        .collect();
    let mut recursors = BTreeMap::<Vec<Name>, Vec<Name>>::new();
    for info in constants.values() {
        if let ConstantInfo::Rec(value) = info {
            recursors
                .entry(value.all.clone())
                .or_default()
                .push(value.base.name.clone());
        }
    }
    // The final roots supply the source frontend's projections and equality
    // vocabulary. They are original declarations with their entire checked
    // dependency closure, not substitutes installed by fixture code.
    let mut pending: BTreeSet<_> = [
        "Hashable",
        "Hashable.hash",
        "mixHash",
        "UInt64.instOfNat",
        "OfNat.ofNat",
        "Inhabited.default",
        "Eq",
    ]
    .map(name)
    .into_iter()
    .collect();
    let mut selected = BTreeSet::new();
    while let Some(label) = pending.pop_first() {
        if engine.environment().contains(&label) || !selected.insert(label.clone()) {
            continue;
        }
        let info = constants
            .get(&label)
            .unwrap_or_else(|| panic!("missing actual Hashable dependency {label:?}"));
        pending.extend(dependencies(info, &recursors));
    }
    assert!(
        selected.len() <= 512,
        "bounded selected Hashable dependency closure"
    );
    drop(constants);
    let mut admitted = BTreeSet::new();
    for mut module in modules {
        module
            .constants
            .retain(|info| selected.contains(info.name()));
        if module.constants.is_empty() {
            continue;
        }
        let checked = engine
            .check_decoded_olean(
                module,
                &KVMap::new(),
                OleanCheckLimits::new(BYTES, admission().kernel),
            )
            .expect("both checkers admit the selected actual declarations")
            .into_complete()
            .expect("selected Hashable declaration admission completes");
        assert_eq!(checked.declarations.len(), checked.decoded.constants.len());
        for row in &checked.declarations {
            assert_eq!(row.checker.schema, "fln.checker-admission/1");
            assert!(admitted.insert(row.name.clone()));
        }
        engine = checked.engine;
    }
    assert_eq!(admitted, selected);
    for label in &selected {
        assert!(
            !matches!(
                engine.environment().find(label),
                Some(ConstantInfo::Axiom(_))
            ),
            "the actual Hashable slice introduces no new axiom: {label:?}"
        );
    }
    let mut activation = ImportActivation::new(engine.environment().clone());
    for journal in journals {
        activation = activate(activation, journal, &selected);
    }
    Engine::from_environment(activation.finish().unwrap())
}
