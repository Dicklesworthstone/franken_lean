//! Fixed Init/System/IO declarations at the pinned epoch. Binder labels and
//! transparent metadata are omitted; their complete logical structure remains.

use super::*;

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn constant(label: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(name(label), levels)
}

fn c(label: &str) -> Expr {
    constant(label, vec![])
}

fn apply(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

fn type_() -> Expr {
    Expr::sort(Level::one())
}

fn parameter(body: Expr, lambda: bool) -> Expr {
    if lambda {
        Expr::lam(Name::anonymous(), type_(), body, BinderInfo::Default)
    } else {
        Expr::forall_e(Name::anonymous(), type_(), body, BinderInfo::Default)
    }
}

fn base(label: &str, type_: Expr) -> ConstantVal {
    ConstantVal {
        name: name(label),
        level_params: vec![],
        type_,
    }
}

fn definition(label: &str, type_: Expr, value: Expr, hints: ReducibilityHints) -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: base(label, type_),
        value,
        hints,
        safety: DefinitionSafety::Safe,
        all: vec![name(label)],
    })
}

pub(super) fn declarations() -> [ConstantInfo; 5] {
    let b = |index| Expr::bvar(index).expect("fixed IO model binder");
    let carrier = "IO.RealWorld.nonemptyType";
    [
        ConstantInfo::Opaque(OpaqueVal {
            base: base(carrier, constant("NonemptyType", vec![Level::zero()])),
            value: apply(
                constant(
                    "Inhabited.default",
                    vec![Level::one().succ().expect("fixed IO universe")],
                ),
                [
                    constant("NonemptyType", vec![Level::zero()]),
                    constant("instInhabitedNonemptyType", vec![Level::zero()]),
                ],
            ),
            is_unsafe: false,
            all: vec![name(carrier)],
        }),
        definition(
            "IO.RealWorld",
            type_(),
            Expr::app(
                constant("NonemptyType.type", vec![Level::zero()]),
                c(carrier),
            ),
            ReducibilityHints::Regular(1),
        ),
        definition(
            "BaseIO",
            parameter(type_(), false),
            parameter(apply(c("ST"), [c("IO.RealWorld"), b(0)]), true),
            ReducibilityHints::Regular(3),
        ),
        definition(
            "EIO",
            parameter(parameter(type_(), false), false),
            parameter(
                parameter(apply(c("EST"), [b(1), c("IO.RealWorld"), b(0)]), true),
                true,
            ),
            ReducibilityHints::Regular(3),
        ),
        definition(
            "IO",
            parameter(type_(), false),
            Expr::app(c("EIO"), c("IO.Error")),
            ReducibilityHints::Abbrev,
        ),
    ]
}
