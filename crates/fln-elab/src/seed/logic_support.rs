//! Ordinary polymorphic definitions for negated equality and false elimination.
//! These candidates must pass the same two admission seats as all other seeds.
use super::*;

fn name(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn bound(index: u32) -> Expr {
    Expr::bvar(index).expect("fixed logical binder index")
}
fn binder(label: &str, domain: Expr, body: Expr, implicit: bool, lambda: bool) -> Expr {
    let info = if implicit {
        BinderInfo::Implicit
    } else {
        BinderInfo::Default
    };
    if lambda {
        Expr::lam(name(label), domain, body, info)
    } else {
        Expr::forall_e(name(label), domain, body, info)
    }
}
fn definition(label: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name(label),
            level_params: vec![name("u")],
            type_,
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name(label)],
    })
}

/// `False.elim.{u} {C : Sort u} (h : False) : C` is a checked use of
/// `False.rec`, not a trusted host-side instruction for discarding goals.
fn false_elimination() -> Declaration {
    let u = Level::param(name("u"));
    let false_ = Expr::const_(name("False"), vec![]);
    let type_ = binder(
        "C",
        Expr::sort(u.clone()),
        binder("h", false_.clone(), bound(1), false, false),
        true,
        false,
    );
    let motive = binder("impossible", false_.clone(), bound(2), false, true);
    let body = Expr::app(
        Expr::app(Expr::const_(name("False.rec"), vec![u.clone()]), motive),
        bound(0),
    );
    let value = binder(
        "C",
        Expr::sort(u),
        binder("h", false_, body, false, true),
        true,
        true,
    );
    definition("False.elim", type_, value)
}

/// Inequality preserves the carrier's full `Sort u`, including Prop.
fn not_equal() -> Declaration {
    let u = Level::param(name("u"));
    let telescope = |body, lambda| {
        binder(
            "A",
            Expr::sort(u.clone()),
            binder(
                "a",
                bound(0),
                binder("b", bound(1), body, false, lambda),
                false,
                lambda,
            ),
            true,
            lambda,
        )
    };
    let equality = [bound(2), bound(1), bound(0)]
        .into_iter()
        .fold(Expr::const_(name("Eq"), vec![u.clone()]), Expr::app);
    definition(
        "Ne",
        telescope(Expr::sort(Level::zero()), false),
        telescope(Expr::app(Expr::const_(name("Not"), vec![]), equality), true),
    )
}

pub fn logical_support_seed_declarations() -> [Declaration; 2] {
    [false_elimination(), not_equal()]
}
