//! Omitted opaque witnesses retain checked private bodies and public headers
//! across authenticated modern module imports of the exact Prelude.
#![forbid(unsafe_code)]
use fln::source_check::modules::SourceModuleCheckLimits;
use fln::source_check::modules::imported::{SourceOleanImport, SourceOleanImportLimits};
use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, Expr, KVMap, Name, OleanCheckLimits,
    OleanModuleInput, SourceCheckLimits, SourceModuleInput,
};
use fln_core::expr::ExprNode;
use std::collections::HashSet;
use std::sync::OnceLock;

const STACK: usize = 128 << 20;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))
}

fn on_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(body)
        .unwrap()
        .join()
        .unwrap();
}

fn imports() -> &'static SourceOleanImport {
    static PRELUDE: OnceLock<SourceOleanImport> = OnceLock::new();
    PRELUDE.get_or_init(|| {
        let module = n("Init.Prelude");
        Engine::builder()
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
                SourceOleanImportLimits::new(OleanCheckLimits::new(16 << 20, limits().kernel)),
            )
            .unwrap()
            .into_complete()
            .unwrap()
    })
}

fn references(expression: &Expr, name: &Name) -> bool {
    let mut pending = vec![expression];
    let mut seen = HashSet::new();
    while let Some(expression) = pending.pop() {
        if !seen.insert(expression.allocation_identity()) {
            continue;
        }
        assert!(seen.len() < 10_000);
        match expression.node() {
            ExprNode::Const { name: found, .. } if found == name => return true,
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
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    false
}

#[test]
fn bodyless_public_opaques_keep_checked_choice_bodies_behind_public_headers() {
    on_stack(|| {
        let module = n("OpaqueDefaults");
        let source = b"module\nprelude\npublic import Init.Prelude\nuniverse u\npublic noncomputable opaque chosen {A : Sort u} [Nonempty A] : A\npublic opaque preferred {A : Sort u} [Inhabited A] : A\n";
        let provider = SourceModuleInput {
            name: &module,
            source,
        };
        let checked = imports()
            .check_source_modules(
                std::slice::from_ref(&provider),
                &module,
                &KVMap::new(),
                SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
                None,
            )
            .unwrap()
            .into_complete()
            .expect("paired opaque admission");
        let Some(ConstantInfo::Opaque(chosen)) =
            checked.checked.engine.environment().find(&n("chosen"))
        else {
            panic!("the full implementation retains its normally checked opaque value");
        };
        assert!(references(&chosen.value, &n("Classical.ofNonempty")));
        let consumer = n("Consumer");
        let imported = imports()
            .check_source_modules(
                &[
                    SourceModuleInput {
                        name: &consumer,
                        source: b"module\nprelude\npublic import OpaqueDefaults\n",
                    },
                    provider,
                ],
                &consumer,
                &KVMap::new(),
                SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
                None,
            )
            .unwrap()
            .into_complete()
            .expect("modern imports expose the checked logical interface");
        let public = imported.checked.engine.environment();
        for name in ["chosen", "preferred"] {
            assert!(matches!(
                public.find(&n(name)),
                Some(ConstantInfo::Axiom(_))
            ));
        }
    });
}
