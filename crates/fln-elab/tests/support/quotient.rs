//! Test candidate for the kernel's four-primitive quotient initialization.
//! It has no admission authority. Tests send it through the ordinary K1 block
//! admission and publication path, including the Eq prerequisite.
use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_env::constants::{ConstantVal, QuotKind, QuotVal};
use fln_kernel::Declaration;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn bv(index: u32) -> Expr {
    Expr::bvar(index).expect("fixed quotient telescope indices fit")
}
fn pi(name: &str, style: BinderInfo, domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(n(name), domain, body, style)
}
fn arrow(domain: Expr, body: Expr) -> Expr {
    pi("a", BinderInfo::Default, domain, body)
}
fn app(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}

/// Pin-shaped types, constructed as closed de Bruijn telescopes rather than
/// installed via raw environment mutation. The level order of lift is [u, v].
pub fn quotient_declaration() -> Declaration {
    use BinderInfo::{Default as D, Implicit as I};
    let u = Level::param(n("u"));
    let v = Level::param(n("v"));
    let prop = || Expr::sort(Level::zero());
    let quot = |alpha, relation| {
        app(Expr::const_(n("Quot"), vec![u.clone()]), [alpha, relation])
    };
    let family = pi(
        "α", I, Expr::sort(u.clone()),
        arrow(arrow(bv(0), arrow(bv(1), prop())), Expr::sort(u.clone())),
    );
    let constructor = pi(
        "α", I, Expr::sort(u.clone()),
        pi("r", D, arrow(bv(0), arrow(bv(1), prop())),
            pi("a", D, bv(1), quot(bv(2), bv(1)))),
    );
    // Inside α,r,β,f,a,b: r a b is the arrow domain. Its codomain is
    // under the additional relation proof, so β,f,a,b shift by one.
    let respects = pi(
        "a", D, bv(3),
        pi("b", D, bv(4),
            arrow(app(bv(4), [bv(1), bv(0)]),
                app(Expr::const_(n("Eq"), vec![v.clone()]), [
                    bv(4), Expr::app(bv(3), bv(2)), Expr::app(bv(3), bv(1)),
                ]))),
    );
    let lift = pi(
        "α", I, Expr::sort(u.clone()),
        pi("r", I, arrow(bv(0), arrow(bv(1), prop())),
            pi("β", I, Expr::sort(v.clone()),
                pi("f", D, arrow(bv(2), bv(1)),
                    arrow(respects, arrow(quot(bv(4), bv(3)), bv(3)))))),
    );
    let induction = pi(
        "α", I, Expr::sort(u.clone()),
        pi("r", I, arrow(bv(0), arrow(bv(1), prop())),
            pi("β", I, arrow(quot(bv(1), bv(0)), prop()),
                pi("mk", D,
                    pi("a", D, bv(2), Expr::app(bv(1),
                        app(Expr::const_(n("Quot.mk"), vec![u.clone()]),
                            [bv(3), bv(2), bv(0)]))),
                    pi("q", D, quot(bv(3), bv(2)), Expr::app(bv(2), bv(0)))))),
    );
    Declaration::Quotient([
        ("Quot", vec![n("u")], family, QuotKind::Type),
        ("Quot.mk", vec![n("u")], constructor, QuotKind::Ctor),
        ("Quot.lift", vec![n("u"), n("v")], lift, QuotKind::Lift),
        ("Quot.ind", vec![n("u")], induction, QuotKind::Ind),
    ].into_iter().map(|(name, level_params, type_, kind)| QuotVal {
        base: ConstantVal { name: n(name), level_params, type_ }, kind,
    }).collect())
}
