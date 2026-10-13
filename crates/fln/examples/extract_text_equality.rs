//! Extract post-admission text-decision comparison data from the retained pinned Prelude.
//! Run with `cargo run -p fln --example extract_text_equality -- String` (or Char).
//! Writes only the requested inventory to stdout; never changes a logical declaration.
#![forbid(unsafe_code)]
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{Budget, Engine, Environment, ExprNode, KVMap, Name, OleanCheckLimits, OleanModuleInput};
use fln_core::name::LeafView;
use fln_env::constants::ConstantInfo;
use std::collections::{BTreeSet, HashSet};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn dependencies(environment: &Environment, root: &str) -> BTreeSet<Name> {
    let mut pending = vec![n("Decidable.decide"), n(root), n("Bool"), n("Nat.beq")];
    let mut found = BTreeSet::new();
    while let Some(label) = pending.pop() {
        if !found.insert(label.clone()) {
            continue;
        }
        let info = environment
            .find(&label)
            .unwrap_or_else(|| panic!("missing {}", label.to_display_string()));
        let mut expressions = vec![&info.constant_val().type_];
        match info {
            ConstantInfo::Defn(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Opaque(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Thm(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Induct(value) => {
                pending.extend(value.all.iter().cloned());
                pending.extend(value.ctors.iter().cloned());
            }
            ConstantInfo::Ctor(value) => pending.push(value.induct.clone()),
            ConstantInfo::Rec(value) => {
                pending.extend(value.all.iter().cloned());
                pending.extend(value.rules.iter().map(|rule| rule.ctor.clone()));
                expressions.extend(value.rules.iter().map(|rule| &rule.rhs));
            }
            ConstantInfo::Axiom(_) | ConstantInfo::Quot(_) => {}
        }
        let mut visited = HashSet::new();
        while let Some(expression) = expressions.pop() {
            if !visited.insert(expression.allocation_identity()) {
                continue;
            }
            match expression.node() {
                ExprNode::Const { name, .. } => pending.push(name.clone()),
                ExprNode::App { f, a } => expressions.extend([f, a]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => expressions.extend([binder_type, body]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => expressions.extend([type_, value, body]),
                ExprNode::Proj {
                    struct_name, expr, ..
                } => {
                    pending.push(struct_name.clone());
                    expressions.push(expr);
                }
                ExprNode::MData { expr, .. } => expressions.push(expr),
                _ => {}
            }
        }
    }
    found
}

fn encoded(label: &Name) -> String {
    let mut name = label.clone();
    let mut parts = Vec::new();
    while !name.is_anonymous() {
        assert!(!name.component_overflowed(), "overflowed name component");
        parts.push(match name.leaf_view() {
            LeafView::Str(part) => {
                assert!(!part.contains(['/', '\t', '\n']));
                format!("s:{part}")
            }
            LeafView::Num(part) => format!("n:{part}"),
            LeafView::Anonymous => unreachable!(),
        });
        name = name.parent();
    }
    parts.reverse();
    parts.join("/")
}

fn main() {
    let carrier = std::env::args().nth(1).expect("expected String or Char");
    assert!(matches!(carrier.as_str(), "String" | "Char"));
    std::thread::Builder::new()
        .stack_size(128 << 20)
        .spawn(move || {
            let module = n("Init.Prelude");
            let imported = Engine::builder()
                .build_empty()
                .import_olean_modules_for_source(
                    &[OleanModuleInput {
                        name: &module,
                        artifact: include_bytes!(
                            "../../fln-conformance/fixtures/tag_attributes/prelude.olean"
                        ),
                        server_artifact: Some(include_bytes!(
                            "../../fln-conformance/fixtures/tag_attributes/prelude.olean.server"
                        )),
                        private_artifact: Some(include_bytes!(
                            "../../fln-conformance/fixtures/tag_attributes/prelude.olean.private"
                        )),
                    }],
                    std::slice::from_ref(&module),
                    &KVMap::new(),
                    SourceOleanImportLimits::new(OleanCheckLimits::new(
                        16 << 20,
                        Budget::for_stack_bytes(128 << 20),
                    )),
                )
                .unwrap()
                .into_complete()
                .expect("the actual Prelude must be council-admitted");
            let environment = imported.engine.environment();
            let root = format!("instDecidableEq{carrier}");
            let found = dependencies(environment, &root);
            eprintln!(
                "{}: {} complete type/body/structural dependencies",
                carrier,
                found.len()
            );
            for label in found {
                println!(
                    "{}\t{}",
                    encoded(&label),
                    environment.entry(&label).unwrap().digest().to_hex()
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
