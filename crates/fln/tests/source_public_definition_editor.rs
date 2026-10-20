//! Hidden module implementations use private editor contexts, never private signatures.
#![forbid(unsafe_code)]

use fln::source_check::inspect::{ObservationKind, SourceObservation};
use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, Expr, ExprNode, KVMap, Name, SourceCheckLimits,
    SourceModuleInput,
};

fn n(name: &str) -> Name {
    Name::from_components(name.split('.'))
}
fn private(name: &str) -> Name {
    Name::num(n("_private.Api"), 0).append_core(&n(name))
}
fn session() -> SourceModuleSession {
    SourceModuleSession::new(
        Engine::builder().build_empty(),
        KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
            Budget::for_stack_bytes(2 * 1024 * 1024),
        ))),
        SourceModuleCacheLimits::default(),
    )
}
fn references(expr: &Expr, target: &Name) -> bool {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        match expr.node() {
            ExprNode::Const { name, .. } if name == target => return true,
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
const BASE: &str = "prelude\ninductive Bit where\n| off\n| on\nclass Pick where\n  value : Bit";
const SECRET: &str =
    "prelude\nimport Base\ndef hiddenValue : Bit := Bit.on\ndef Hidden : Type := Bit";
const PREFIX: &str = "module\nprelude\npublic import Base\nimport Secret\nprivate def hiddenLocal : Bit := hiddenValue\n";
fn inputs<'a>(names: &'a [Name; 3], source: &'a str) -> [SourceModuleInput<'a>; 3] {
    [
        SourceModuleInput {
            name: &names[0],
            source: source.as_bytes(),
        },
        SourceModuleInput {
            name: &names[1],
            source: SECRET.as_bytes(),
        },
        SourceModuleInput {
            name: &names[2],
            source: BASE.as_bytes(),
        },
    ]
}

#[test]
fn goals_and_hover_enter_hidden_definition_bodies_without_publishing_them() {
    let names = [n("Api"), n("Secret"), n("Base")];
    let mut session = session();
    for head in [
        "public def pending : Bit",
        "public opaque pending : Bit",
        "@[no_expose] public abbrev pending : Bit",
        "@[expose, no_expose] public def pending : Bit",
    ] {
        // Byte offsets must survive both Unicode trivia and CRLF normalization.
        let source = format!("{PREFIX}/-- λ implementation -/\n{head} := by\n  exact hiddenLocal")
            .replace('\n', "\r\n");
        let inputs = inputs(&names, &source);
        for _ in 0..2 {
            let observed = session
                .inspect(&inputs, &names[0], source.len(), ObservationKind::Goals)
                .unwrap_or_else(|error| panic!("{head}: {error:?}"))
                .into_complete()
                .unwrap();
            assert!(
                matches!(observed.observation,
                Some(SourceObservation::Goals { goals, .. }) if goals.is_empty()),
                "{head}"
            );
            assert!(
                !observed
                    .prefix
                    .checked
                    .checked
                    .engine
                    .environment()
                    .contains(&n("pending"))
            );
        }
        let start = source.rfind("hiddenLocal").unwrap();
        let observed = session
            .inspect(&inputs, &names[0], start + 2, ObservationKind::Term)
            .unwrap()
            .into_complete()
            .unwrap();
        let Some(SourceObservation::Term {
            range,
            expression,
            type_,
            ..
        }) = observed.observation
        else {
            panic!("expected the actual private helper in {head}");
        };
        assert_eq!(range, start..start + "hiddenLocal".len());
        assert!(references(&expression, &private("hiddenLocal")));
        assert!(references(&type_, &n("Bit")));
    }
}

#[test]
fn inferred_definition_and_hidden_data_instance_terms_have_private_observations() {
    let names = [n("Api"), n("Secret"), n("Base")];
    let mut session = session();
    for declaration in [
        "public def pending := hiddenLocal",
        "@[no_expose] public instance pending : Pick := Pick.mk hiddenLocal",
    ] {
        let source = format!("{PREFIX}{declaration}");
        let observed = session
            .inspect(
                &inputs(&names, &source),
                &names[0],
                source.rfind("hiddenLocal").unwrap() + 2,
                ObservationKind::Term,
            )
            .unwrap_or_else(|error| panic!("{declaration}: {error:?}"))
            .into_complete()
            .unwrap();
        let Some(SourceObservation::Term { expression, .. }) = observed.observation else {
            panic!("expected private implementation observation");
        };
        assert!(references(&expression, &private("hiddenLocal")));
        assert!(
            !observed
                .prefix
                .checked
                .checked
                .engine
                .environment()
                .contains(&n("pending"))
        );
    }
}

#[test]
fn completion_uses_header_checked_declaration_specific_exposure() {
    let names = [n("Api"), n("Secret"), n("Base")];
    let mut session = session();
    for (declaration, hidden) in [
        ("public def pending : hid", false),
        ("public def pending (x : hid", false),
        ("public def pending : Bit := hid", true),
        ("public def pending := hid", true),
        ("@[expose] public def pending : Bit := hid", false),
        ("@[expose, no_expose] public def pending : Bit := hid", true),
        ("public abbrev pending : Bit := hid", false),
        ("@[no_expose] public abbrev pending : Bit := hid", true),
        ("@[expose] public section\ndef pending : Bit := hid", false),
        (
            "@[expose] public section\n@[no_expose] def pending : Bit := hid",
            true,
        ),
        (
            "@[expose] public section\nopaque pending : Bit := hid",
            true,
        ),
        ("@[expose] public opaque pending : Bit := hid", false),
        ("public opaque pending : Bit := hid", true),
        (
            "@[no_expose] public instance pending : Pick := Pick.mk hid",
            true,
        ),
        ("public instance pending : Pick := Pick.mk hid", false),
        ("private def pending : hid", true),
        (
            "set_option maxRecDepth 2048 in public def pending : Bit := hid",
            true,
        ),
        (
            "set_option maxRecDepth 2048 in @[expose] public def pending : Bit := hid",
            false,
        ),
    ] {
        let source = format!("{PREFIX}{declaration}");
        let result = session
            .complete(&inputs(&names, &source), &names[0], source.len())
            .unwrap_or_else(|error| panic!("{declaration}: {error:?}"))
            .into_complete()
            .unwrap()
            .unwrap();
        for label in ["hiddenValue", "hiddenLocal"] {
            assert_eq!(
                result.items.iter().any(|item| item.label == label),
                hidden,
                "{declaration}: {result:?}"
            );
        }
    }
}

#[test]
fn private_header_dependencies_and_exposed_bodies_cannot_be_rescued_by_inspection() {
    let names = [n("Api"), n("Secret"), n("Base")];
    let mut session = session();
    for declaration in [
        "public def pending : Hidden := by exact hiddenLocal",
        "public def pending (x : Hidden) : Bit := by exact hiddenLocal",
        "@[expose] public def pending : Bit := by exact hiddenLocal",
        "public abbrev pending : Bit := by exact hiddenLocal",
        "@[expose] public opaque pending : Bit := by exact hiddenLocal",
    ] {
        let source = format!("{PREFIX}{declaration}");
        assert!(
            session
                .inspect(
                    &inputs(&names, &source),
                    &names[0],
                    source.len(),
                    ObservationKind::Goals
                )
                .is_err(),
            "{declaration}"
        );
    }
    for declaration in [
        "public def pending : Hidden := hid",
        "public def pending (x : Hidden) : Bit := hid",
        "public opaque pending : Hidden := hid",
        "@[no_expose] public abbrev pending : Hidden := hid",
    ] {
        let source = format!("{PREFIX}{declaration}");
        assert!(
            session
                .complete(&inputs(&names, &source), &names[0], source.len())
                .is_err(),
            "{declaration}"
        );
    }
    let source = format!("{PREFIX}public def pending : Bit := by exact hiddenLocal");
    let recovered = session
        .inspect(
            &inputs(&names, &source),
            &names[0],
            source.len(),
            ObservationKind::Goals,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(matches!(recovered.observation,
        Some(SourceObservation::Goals { goals, .. }) if goals.is_empty()));
    assert!(
        !recovered
            .prefix
            .checked
            .checked
            .engine
            .environment()
            .contains(&n("pending"))
    );
}
