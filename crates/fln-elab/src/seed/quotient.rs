//! Candidates for the kernel's quotient quartet and the explicit quotient axiom.
//!
//! The primitive types follow the pinned KR-950..954 initialization contract.
//! They must pass ordinary block admission after Eq; constructing them grants
//! no environment or runtime authority. `Quot.sound` is the named quotient
//! axiom from the pin's Init/Core.lean, not an invented proof or a new axiom.
//! This module does not implement Setoid/Quotient or a complete Prelude.
use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_env::constants::{AxiomVal, ConstantVal, QuotKind, QuotVal};
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
pub fn quotient_seed_declaration() -> Declaration {
    use BinderInfo::{Default as D, Implicit as I};
    let u = Level::param(n("u"));
    let v = Level::param(n("v"));
    let prop = || Expr::sort(Level::zero());
    let quot = |alpha, relation| app(Expr::const_(n("Quot"), vec![u.clone()]), [alpha, relation]);
    let family = pi(
        "α",
        I,
        Expr::sort(u.clone()),
        arrow(arrow(bv(0), arrow(bv(1), prop())), Expr::sort(u.clone())),
    );
    let constructor = pi(
        "α",
        I,
        Expr::sort(u.clone()),
        pi(
            "r",
            D,
            arrow(bv(0), arrow(bv(1), prop())),
            pi("a", D, bv(1), quot(bv(2), bv(1))),
        ),
    );
    // Inside α,r,β,f,a,b: r a b is the arrow domain. Its codomain is
    // under the additional relation proof, so β,f,a,b shift by one.
    let respects = pi(
        "a",
        D,
        bv(3),
        pi(
            "b",
            D,
            bv(4),
            arrow(
                app(bv(4), [bv(1), bv(0)]),
                app(
                    Expr::const_(n("Eq"), vec![v.clone()]),
                    [bv(4), Expr::app(bv(3), bv(2)), Expr::app(bv(3), bv(1))],
                ),
            ),
        ),
    );
    let lift = pi(
        "α",
        I,
        Expr::sort(u.clone()),
        pi(
            "r",
            I,
            arrow(bv(0), arrow(bv(1), prop())),
            pi(
                "β",
                I,
                Expr::sort(v.clone()),
                pi(
                    "f",
                    D,
                    arrow(bv(2), bv(1)),
                    arrow(respects, arrow(quot(bv(4), bv(3)), bv(3))),
                ),
            ),
        ),
    );
    let induction = pi(
        "α",
        I,
        Expr::sort(u.clone()),
        pi(
            "r",
            I,
            arrow(bv(0), arrow(bv(1), prop())),
            pi(
                "β",
                I,
                arrow(quot(bv(1), bv(0)), prop()),
                pi(
                    "mk",
                    D,
                    pi(
                        "a",
                        D,
                        bv(2),
                        Expr::app(
                            bv(1),
                            app(
                                Expr::const_(n("Quot.mk"), vec![u.clone()]),
                                [bv(3), bv(2), bv(0)],
                            ),
                        ),
                    ),
                    pi("q", D, quot(bv(3), bv(2)), Expr::app(bv(2), bv(0))),
                ),
            ),
        ),
    );
    Declaration::Quotient(
        [
            ("Quot", vec![n("u")], family, QuotKind::Type),
            ("Quot.mk", vec![n("u")], constructor, QuotKind::Ctor),
            ("Quot.lift", vec![n("u"), n("v")], lift, QuotKind::Lift),
            ("Quot.ind", vec![n("u")], induction, QuotKind::Ind),
        ]
        .into_iter()
        .map(|(name, level_params, type_, kind)| QuotVal {
            base: ConstantVal {
                name: n(name),
                level_params,
                type_,
            },
            kind,
        })
        .collect(),
    )
}

/// The explicit quotient axiom, admitted after the primitive quartet:
/// `{α : Sort u} {r : α → α → Prop} {a b : α} → r a b → Quot.mk r a = Quot.mk r b`.
/// This candidate remains visibly an axiom in the environment and receipts.
pub fn quotient_sound_seed_declaration() -> Declaration {
    use BinderInfo::{Default as D, Implicit as I};
    let u = Level::param(n("u"));
    let quot = app(Expr::const_(n("Quot"), vec![u.clone()]), [bv(4), bv(3)]);
    let constructor = Expr::const_(n("Quot.mk"), vec![u.clone()]);
    let equation = app(
        Expr::const_(n("Eq"), vec![u.clone()]),
        [
            quot,
            app(constructor.clone(), [bv(4), bv(3), bv(2)]),
            app(constructor, [bv(4), bv(3), bv(1)]),
        ],
    );
    Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: n("Quot.sound"),
            level_params: vec![n("u")],
            type_: pi(
                "α",
                I,
                Expr::sort(u),
                pi(
                    "r",
                    I,
                    arrow(bv(0), arrow(bv(1), Expr::sort(Level::zero()))),
                    pi(
                        "a",
                        I,
                        bv(1),
                        pi(
                            "b",
                            I,
                            bv(2),
                            pi("h", D, app(bv(2), [bv(1), bv(0)]), equation),
                        ),
                    ),
                ),
            ),
        },
        is_unsafe: false,
    })
}
