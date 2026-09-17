//! Universe-polymorphic decision interfaces, as ordinary checked definitions.
//!
//! The aliases preserve the caller's dictionary, including its proof fields.
//! There is no built-in equality guess for an unknown carrier.
use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_kernel::Declaration;

fn name(s: &str) -> Name {
    Name::from_components([s])
}
fn bound(index: u32) -> Expr {
    Expr::bvar(index).expect("fixed decision-interface telescope")
}
fn app(function: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(function, Expr::app)
}
fn decision(proposition: Expr) -> Expr {
    Expr::app(Expr::const_(name("Decidable"), vec![]), proposition)
}
fn definition(s: &str, universe: Name, type_: Expr, value: Expr) -> Declaration {
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name(s),
            level_params: vec![universe],
            type_,
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name(s)],
    })
}

fn equality_type_declaration() -> Declaration {
    let u = name("u");
    let level = Level::param(u.clone());
    // Inside the two element binders the context is [alpha, a, b].
    let proposition = app(
        Expr::const_(name("Eq"), vec![level.clone()]),
        [bound(2), bound(1), bound(0)],
    );
    let body = Expr::forall_e(
        name("a"),
        bound(0),
        Expr::forall_e(name("b"), bound(1), decision(proposition), BinderInfo::Default),
        BinderInfo::Default,
    );
    definition(
        "DecidableEq",
        u,
        Expr::forall_e(
            name("alpha"),
            Expr::sort(level.clone()),
            Expr::sort(Level::max(level.clone(), Level::one()).expect("fixed decision universe")),
            BinderInfo::Default,
        ),
        Expr::lam(name("alpha"), Expr::sort(level), body, BinderInfo::Default),
    )
}

fn generic_dec_eq_declaration() -> Declaration {
    let u = name("u");
    let level = Level::param(u.clone());
    // Inner context is [alpha, inst, a, b]; each binder domain is written in
    // its preceding context, not the full inner context.
    let proposition = app(
        Expr::const_(name("Eq"), vec![level.clone()]),
        [bound(3), bound(1), bound(0)],
    );
    let mut type_ = decision(proposition);
    let mut value = app(bound(2), [bound(1), bound(0)]);
    for (label, domain, info) in [
        ("b", bound(2), BinderInfo::Default),
        ("a", bound(1), BinderInfo::Default),
        (
            "inst",
            Expr::app(
                Expr::const_(name("DecidableEq"), vec![level.clone()]),
                bound(0),
            ),
            BinderInfo::InstImplicit,
        ),
        ("alpha", Expr::sort(level), BinderInfo::Implicit),
    ] {
        type_ = Expr::forall_e(name(label), domain.clone(), type_, info);
        value = Expr::lam(name(label), domain, value, info);
    }
    definition("decEq", u, type_, value)
}

/// Admit these in order, after the Eq and Decidable inductive declarations.
/// Instance synthesis remains the native registry's responsibility.
pub fn generic_equality_decision_seed_declarations() -> [Declaration; 2] {
    [equality_type_declaration(), generic_dec_eq_declaration()]
}
