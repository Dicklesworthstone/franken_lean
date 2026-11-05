//! A small real Prelude slice, independently read and checked over SourceSeed.
//! This is not complete module admission. No raw decoded declaration enters
//! the returned Engine, and the choice axiom is the original pinned artifact.
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

pub(super) fn admitted(library: &Path) -> Engine {
    let path = library.join("Init/Prelude.olean");
    let public = std::fs::read(&path).unwrap();
    let server = std::fs::read(path.with_extension("olean.server")).unwrap();
    let private = std::fs::read(path.with_extension("olean.private")).unwrap();
    let mut decoded = fln::decode_olean_module_artifacts(
        &public,
        &server,
        &private,
        OleanDecodeLimits::new(BYTES),
    )
    .expect("decode actual pinned Prelude through both artifact readers");
    assert!(matches!(decoded.independent, IndependentReading::Read(_)));
    let seed = Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .expect("the ordinary source seed passes both checkers");
    let constants: BTreeMap<_, _> = decoded
        .constants
        .iter()
        .map(|info| (info.name().clone(), info))
        .collect();
    let mut recursors = BTreeMap::<Vec<Name>, Vec<Name>>::new();
    for info in &decoded.constants {
        if let ConstantInfo::Rec(value) = info {
            recursors
                .entry(value.all.clone())
                .or_default()
                .push(value.base.name.clone());
        }
    }
    let mut pending: BTreeSet<_> = [
        "Nonempty",
        "Nonempty.elim",
        "Classical.choice",
        "Classical.ofNonempty",
        "instNonemptyOfInhabited",
        "Pi.instNonempty",
        // The genuine private-constructor Provider's generated noConfusion
        // definitions require this original equality eliminator wrapper.
        "Eq.ndrec",
    ]
    .map(name)
    .into_iter()
    .collect();
    let mut selected = BTreeSet::new();
    while let Some(label) = pending.pop_first() {
        if seed.environment().contains(&label) || !selected.insert(label.clone()) {
            continue;
        }
        let info = constants
            .get(&label)
            .unwrap_or_else(|| panic!("missing original Prelude dependency {label:?}"));
        pending.extend(dependencies(info, &recursors));
    }
    assert!(
        selected.len() < 64,
        "this is a small actual declaration slice"
    );
    drop(constants);
    decoded
        .constants
        .retain(|info| selected.contains(info.name()));
    let checked = seed
        .check_decoded_olean(
            decoded,
            &KVMap::new(),
            OleanCheckLimits::new(BYTES, admission().kernel),
        )
        .expect("both checkers compare and admit each selected actual declaration")
        .into_complete()
        .expect("the small selected Prelude slice completes");
    assert_eq!(checked.declarations.len(), selected.len());
    for row in &checked.declarations {
        assert_eq!(row.checker.schema, "fln.checker-admission/1");
    }
    let new_axioms: Vec<_> = selected
        .iter()
        .filter(|label| {
            matches!(
                checked.engine.environment().find(label),
                Some(ConstantInfo::Axiom(_))
            )
        })
        .cloned()
        .collect();
    assert_eq!(new_axioms, vec![name("Classical.choice")]);

    // Activate only original class/instance/status rows for those declarations,
    // after admission. The expected discrimination keys are not synthesized.
    let view = OleanView::parse_with_dependencies(&private, &[&public, &server]).unwrap();
    let limits = SourceOleanImportLimits::new(OleanCheckLimits::new(BYTES, admission().kernel));
    let mut blocks = view
        .extension_payloads(limits.capture, limits.max_capture_bytes)
        .unwrap();
    let wanted = [
        metadata::CLASS_EXTENSION,
        metadata::INSTANCE_EXTENSION,
        metadata::REDUCIBILITY_EXTENSION,
    ]
    .map(name);
    blocks.retain(|block| wanted.contains(&block.name));
    let data = metadata::decode(&blocks, limits.metadata).unwrap();
    let mut activation = ImportActivation::new(checked.engine.environment().clone());
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
                    .collect()
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
        .reducibility
        .into_iter()
        .filter(|row| selected.contains(&row.declaration))
    {
        use fln_elab::reducibility::Reducibility;
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
    Engine::from_environment(activation.finish().unwrap())
}
