//! Ordinary checked bridges for heterogeneous equality. These are proof terms
//! built from the admitted Eq/HEq recursors, not primitive conversion rules.
use super::*;
use fln_core::expr::FVarId;
use fln_env::constants::TheoremVal;

struct Builder {
    next: u64,
    universe: Level,
}
struct Local {
    id: FVarId,
    name: Name,
    domain: Expr,
    style: BinderInfo,
}
impl Local {
    fn expr(&self) -> Expr {
        Expr::fvar(self.id.clone())
    }
}
fn apply(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}
fn constant(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_components(name.split('.')), levels)
}
fn close(locals: &[&Local], mut body: Expr, lambda: bool) -> Expr {
    for local in locals.iter().rev() {
        body = body
            .abstract_fvar(&local.id, 0)
            .expect("fixed proof telescope");
        body = if lambda {
            Expr::lam(local.name.clone(), local.domain.clone(), body, local.style)
        } else {
            Expr::forall_e(local.name.clone(), local.domain.clone(), body, local.style)
        };
    }
    body
}
impl Builder {
    fn new() -> Self {
        Self {
            next: 0,
            universe: Level::param(Name::from_components(["u"])),
        }
    }
    fn local(&mut self, name: &str, domain: Expr, implicit: bool) -> Local {
        let id = FVarId(Name::num(
            Name::from_components(["_fln_heq_bridge"]),
            self.next,
        ));
        self.next += 1;
        Local {
            id,
            name: Name::from_components([name]),
            domain,
            style: if implicit {
                BinderInfo::Implicit
            } else {
                BinderInfo::Default
            },
        }
    }
    fn heq(&self, a: &Expr, x: &Expr, b: &Expr, y: &Expr) -> Expr {
        apply(
            constant("HEq", vec![self.universe.clone()]),
            [a.clone(), x.clone(), b.clone(), y.clone()],
        )
    }
    fn eq(&self, alpha: Expr, x: Expr, y: Expr) -> Expr {
        apply(constant("Eq", vec![self.universe.clone()]), [alpha, x, y])
    }
    fn type_eq(&self, a: Expr, b: Expr) -> Expr {
        apply(
            constant(
                "Eq",
                vec![self.universe.clone().succ().expect("one successor")],
            ),
            [Expr::sort(self.universe.clone()), a, b],
        )
    }
    fn refl(&self, alpha: Expr, value: Expr, heterogeneous: bool) -> Expr {
        apply(
            constant(
                if heterogeneous { "HEq.refl" } else { "Eq.refl" },
                vec![self.universe.clone()],
            ),
            [alpha, value],
        )
    }
    fn cast(&mut self, a: Expr, b: Expr, evidence: Expr, value: Expr) -> Expr {
        let ty = self.local("T", Expr::sort(self.universe.clone()), false);
        let h = self.local("e", self.type_eq(a.clone(), ty.expr()), false);
        let motive = close(&[&ty, &h], ty.expr(), true);
        apply(
            constant(
                "Eq.rec",
                vec![
                    self.universe.clone(),
                    self.universe.clone().succ().expect("one successor"),
                ],
            ),
            [
                Expr::sort(self.universe.clone()),
                a,
                motive,
                value,
                b,
                evidence,
            ],
        )
    }
    fn theorem(&self, name: &str, locals: &[&Local], type_: Expr, value: Expr) -> Declaration {
        Declaration::Thm(TheoremVal {
            base: ConstantVal {
                name: Name::from_components(name.split('.')),
                level_params: vec![Name::from_components(["u"])],
                type_: close(locals, type_, false),
            },
            value: close(locals, value, true),
            all: vec![Name::from_components(name.split('.'))],
        })
    }
}

/// HEq retains the equality of the endpoint types, even when they differ.
pub fn type_eq_seed_declaration() -> Declaration {
    let mut b = Builder::new();
    let a = b.local("A", Expr::sort(b.universe.clone()), true);
    let x = b.local("a", a.expr(), true);
    let beta = b.local("B", Expr::sort(b.universe.clone()), true);
    let y = b.local("b", beta.expr(), true);
    let h = b.local(
        "h",
        b.heq(&a.expr(), &x.expr(), &beta.expr(), &y.expr()),
        false,
    );
    let generic = b.local("e", h.domain.clone(), false);
    let result = b.type_eq(a.expr(), beta.expr());
    let motive = close(&[&beta, &y, &generic], result.clone(), true);
    let base = apply(
        constant(
            "Eq.refl",
            vec![b.universe.clone().succ().expect("one successor")],
        ),
        [Expr::sort(b.universe.clone()), a.expr()],
    );
    let value = apply(
        constant("HEq.rec", vec![Level::zero(), b.universe.clone()]),
        [
            a.expr(),
            x.expr(),
            motive,
            base,
            beta.expr(),
            y.expr(),
            h.expr(),
        ],
    );
    b.theorem("type_eq_of_heq", &[&a, &x, &beta, &y, &h], result, value)
}

pub fn heq_of_eq_seed_declaration() -> Declaration {
    let mut b = Builder::new();
    let a = b.local("A", Expr::sort(b.universe.clone()), true);
    let x = b.local("a", a.expr(), true);
    let y = b.local("b", a.expr(), true);
    let h = b.local("h", b.eq(a.expr(), x.expr(), y.expr()), false);
    let generic = b.local("e", h.domain.clone(), false);
    let result = b.heq(&a.expr(), &x.expr(), &a.expr(), &y.expr());
    let motive = close(&[&y, &generic], result.clone(), true);
    let value = apply(
        constant("Eq.rec", vec![Level::zero(), b.universe.clone()]),
        [
            a.expr(),
            x.expr(),
            motive,
            b.refl(a.expr(), x.expr(), true),
            y.expr(),
            h.expr(),
        ],
    );
    b.theorem("heq_of_eq", &[&a, &x, &y, &h], result, value)
}

/// A fixed-type HEq becomes Eq by transporting a type-equality-indexed motive.
/// The cast stays in the proof. Only the already admitted equality K rule can
/// reduce it when its endpoint types coincide; no witness is retyped by fiat.
pub fn eq_of_heq_seed_declaration() -> Declaration {
    let mut b = Builder::new();
    let a = b.local("A", Expr::sort(b.universe.clone()), true);
    let x = b.local("a", a.expr(), true);
    let y = b.local("b", a.expr(), true);
    let h = b.local(
        "h",
        b.heq(&a.expr(), &x.expr(), &a.expr(), &y.expr()),
        false,
    );
    let beta = b.local("B", Expr::sort(b.universe.clone()), false);
    let z = b.local("z", beta.expr(), false);
    let generic = b.local(
        "e",
        b.heq(&a.expr(), &x.expr(), &beta.expr(), &z.expr()),
        false,
    );
    let types = b.local("types", b.type_eq(a.expr(), beta.expr()), false);
    let transported = b.cast(a.expr(), beta.expr(), types.expr(), x.expr());
    let relation = b.eq(beta.expr(), transported, z.expr());
    let motive = close(
        &[&beta, &z, &generic],
        close(&[&types], relation, false),
        true,
    );
    let same_types = b.local("types", b.type_eq(a.expr(), a.expr()), false);
    let minor = close(&[&same_types], b.refl(a.expr(), x.expr(), false), true);
    let proof = apply(
        constant("HEq.rec", vec![Level::zero(), b.universe.clone()]),
        [
            a.expr(),
            x.expr(),
            motive,
            minor,
            a.expr(),
            y.expr(),
            h.expr(),
        ],
    );
    let type_refl = apply(
        constant(
            "Eq.refl",
            vec![b.universe.clone().succ().expect("one successor")],
        ),
        [Expr::sort(b.universe.clone()), a.expr()],
    );
    let result = b.eq(a.expr(), x.expr(), y.expr());
    b.theorem(
        "eq_of_heq",
        &[&a, &x, &y, &h],
        result,
        Expr::app(proof, type_refl),
    )
}

pub fn symmetry_seed_declaration() -> Declaration {
    let mut b = Builder::new();
    let a = b.local("A", Expr::sort(b.universe.clone()), true);
    let x = b.local("a", a.expr(), true);
    let beta = b.local("B", Expr::sort(b.universe.clone()), true);
    let y = b.local("b", beta.expr(), true);
    let h = b.local(
        "h",
        b.heq(&a.expr(), &x.expr(), &beta.expr(), &y.expr()),
        false,
    );
    let generic = b.local("e", h.domain.clone(), false);
    let result = b.heq(&beta.expr(), &y.expr(), &a.expr(), &x.expr());
    let motive = close(&[&beta, &y, &generic], result.clone(), true);
    let value = apply(
        constant("HEq.rec", vec![Level::zero(), b.universe.clone()]),
        [
            a.expr(),
            x.expr(),
            motive,
            b.refl(a.expr(), x.expr(), true),
            beta.expr(),
            y.expr(),
            h.expr(),
        ],
    );
    b.theorem("HEq.symm", &[&a, &x, &beta, &y, &h], result, value)
}

pub fn transitivity_seed_declaration() -> Declaration {
    let mut b = Builder::new();
    let a = b.local("A", Expr::sort(b.universe.clone()), true);
    let x = b.local("a", a.expr(), true);
    let beta = b.local("B", Expr::sort(b.universe.clone()), true);
    let y = b.local("b", beta.expr(), true);
    let gamma = b.local("C", Expr::sort(b.universe.clone()), true);
    let z = b.local("c", gamma.expr(), true);
    let h = b.local(
        "h",
        b.heq(&a.expr(), &x.expr(), &beta.expr(), &y.expr()),
        false,
    );
    let k = b.local(
        "k",
        b.heq(&beta.expr(), &y.expr(), &gamma.expr(), &z.expr()),
        false,
    );
    let generic = b.local("e", k.domain.clone(), false);
    let result = b.heq(&a.expr(), &x.expr(), &gamma.expr(), &z.expr());
    let motive = close(&[&gamma, &z, &generic], result.clone(), true);
    let value = apply(
        constant("HEq.rec", vec![Level::zero(), b.universe.clone()]),
        [
            beta.expr(),
            y.expr(),
            motive,
            h.expr(),
            gamma.expr(),
            z.expr(),
            k.expr(),
        ],
    );
    b.theorem(
        "HEq.trans",
        &[&a, &x, &beta, &y, &gamma, &z, &h, &k],
        result,
        value,
    )
}
