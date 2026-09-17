//! Constructive equality decisions for the bounded source prelude.
//!
//! These are untrusted core-term candidates. Nat and Bool elimination computes
//! each decision, and Eq.rec constructs every positive or negative proof field.
//! There is no host comparison, new axiom, or special admission rule.
use crate::lctx::LocalDecl;
use fln_core::expr::{BinderInfo, Expr, FVarId};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_kernel::Declaration;

fn name(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn constant(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}
fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}
fn fv(l: &LocalDecl) -> Expr {
    Expr::fvar(l.id.clone())
}
fn close(locals: &[&LocalDecl], mut body: Expr, lambda: bool) -> Expr {
    for local in locals.iter().rev() {
        body = body
            .abstract_fvar(&local.id, 0)
            .expect("fixed equality-decision telescope");
        body = if lambda {
            Expr::lam(
                local.user_name.clone(),
                local.type_.clone(),
                body,
                local.binder_info,
            )
        } else {
            Expr::forall_e(
                local.user_name.clone(),
                local.type_.clone(),
                body,
                local.binder_info,
            )
        };
    }
    body
}
fn eq(alpha: Expr, universe: Level, left: Expr, right: Expr) -> Expr {
    app(
        Expr::const_(name("Eq"), vec![universe]),
        [alpha, left, right],
    )
}
fn nat_eq(left: Expr, right: Expr) -> Expr {
    eq(constant("Nat"), Level::one(), left, right)
}
fn bool_eq(left: Expr, right: Expr) -> Expr {
    eq(constant("Bool"), Level::one(), left, right)
}
fn refl(alpha: Expr, universe: Level, value: Expr) -> Expr {
    app(
        Expr::const_(name("Eq.refl"), vec![universe]),
        [alpha, value],
    )
}
fn decision(proposition: Expr) -> Expr {
    Expr::app(constant("Decidable"), proposition)
}
fn neg(proposition: Expr) -> Expr {
    Expr::app(constant("Not"), proposition)
}
fn positive(proposition: Expr, proof: Expr) -> Expr {
    app(constant("Decidable.isTrue"), [proposition, proof])
}
fn negative(proposition: Expr, proof: Expr) -> Expr {
    app(constant("Decidable.isFalse"), [proposition, proof])
}
fn succ(value: Expr) -> Expr {
    Expr::app(constant("Nat.succ"), value)
}
fn nat_rec(motive: Expr, zero: Expr, step: Expr, major: Expr) -> Expr {
    app(
        Expr::const_(name("Nat.rec"), vec![Level::one()]),
        [motive, zero, step, major],
    )
}
fn bool_rec(motive: Expr, no: Expr, yes: Expr, major: Expr) -> Expr {
    app(
        Expr::const_(name("Bool.rec"), vec![Level::one()]),
        [motive, no, yes, major],
    )
}
fn defined(
    s: &str,
    levels: Vec<Name>,
    locals: &[&LocalDecl],
    result: Expr,
    value: Expr,
) -> Declaration {
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name(s),
            level_params: levels,
            type_: close(locals, result, false),
        },
        value: close(locals, value, true),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name(s)],
    })
}

#[derive(Default)]
struct Terms {
    next: usize,
}
impl Terms {
    fn local(&mut self, label: &str, type_: Expr, binder_info: BinderInfo) -> LocalDecl {
        let id = FVarId(name(&format!("_fln_dec_eq_seed.{label}_{}", self.next)));
        self.next += 1;
        LocalDecl {
            id,
            user_name: name(label),
            type_,
            value: None,
            binder_info,
            index: 0,
        }
    }
    fn explicit(&mut self, label: &str, type_: Expr) -> LocalDecl {
        self.local(label, type_, BinderInfo::Default)
    }
    /// Transport a proposition-valued family along an explicit equality. The
    /// supplied endpoint is scoped only over the motive, never over the proof.
    fn transport(
        &mut self,
        endpoint: &LocalDecl,
        left: Expr,
        right: Expr,
        evidence: Expr,
        result: Expr,
        proof: Expr,
    ) -> Expr {
        let equality = self.explicit(
            "transport_equality",
            eq(
                endpoint.type_.clone(),
                Level::one(),
                left.clone(),
                fv(endpoint),
            ),
        );
        app(
            Expr::const_(name("Eq.rec"), vec![Level::zero(), Level::one()]),
            [
                endpoint.type_.clone(),
                left,
                close(&[endpoint, &equality], result, true),
                proof,
                right,
                evidence,
            ],
        )
    }
    fn nat_discriminator(&mut self, value: Expr, zero_case: bool) -> Expr {
        let n = self.explicit("discriminator_argument", constant("Nat"));
        let k = self.explicit("discriminator_predecessor", constant("Nat"));
        let ih = self.explicit("discriminator_induction", Expr::sort(Level::zero()));
        let (zero, step) = if zero_case {
            (constant("True"), constant("False"))
        } else {
            (constant("False"), constant("True"))
        };
        nat_rec(
            close(&[&n], Expr::sort(Level::zero()), true),
            zero,
            close(&[&k, &ih], step, true),
            value,
        )
    }
    fn nat_mismatch(&mut self, predecessor: Expr, zero_left: bool) -> Expr {
        let (left, right) = if zero_left {
            (constant("Nat.zero"), succ(predecessor))
        } else {
            (succ(predecessor), constant("Nat.zero"))
        };
        let hypothesis = self.explicit(
            "impossible_nat_equality",
            nat_eq(left.clone(), right.clone()),
        );
        let endpoint = self.explicit("nat_endpoint", constant("Nat"));
        let predicate = self.nat_discriminator(fv(&endpoint), zero_left);
        let contradiction = self.transport(
            &endpoint,
            left,
            right,
            fv(&hypothesis),
            predicate,
            constant("True.intro"),
        );
        close(&[&hypothesis], contradiction, true)
    }
    fn predecessor(&mut self, value: Expr) -> Expr {
        let n = self.explicit("predecessor_argument", constant("Nat"));
        let k = self.explicit("predecessor_value", constant("Nat"));
        let ih = self.explicit("predecessor_induction", constant("Nat"));
        nat_rec(
            close(&[&n], constant("Nat"), true),
            constant("Nat.zero"),
            close(&[&k, &ih], fv(&k), true),
            value,
        )
    }
    fn succ_injective(&mut self, left: Expr, right: Expr, evidence: Expr) -> Expr {
        let endpoint = self.explicit("successor_endpoint", constant("Nat"));
        let predecessor = self.predecessor(fv(&endpoint));
        let predicate = nat_eq(left.clone(), predecessor);
        let reflexive = refl(constant("Nat"), Level::one(), left.clone());
        self.transport(
            &endpoint,
            succ(left),
            succ(right),
            evidence,
            predicate,
            reflexive,
        )
    }
    fn succ_congruent(&mut self, left: Expr, right: Expr, evidence: Expr) -> Expr {
        let endpoint = self.explicit("congruence_endpoint", constant("Nat"));
        let predicate = nat_eq(succ(left.clone()), succ(fv(&endpoint)));
        let reflexive = refl(constant("Nat"), Level::one(), succ(left.clone()));
        self.transport(&endpoint, left, right, evidence, predicate, reflexive)
    }
    fn bool_mismatch(&mut self, left_true: bool) -> Expr {
        let (left, right) = if left_true {
            (constant("Bool.true"), constant("Bool.false"))
        } else {
            (constant("Bool.false"), constant("Bool.true"))
        };
        let hypothesis = self.explicit(
            "impossible_bool_equality",
            bool_eq(left.clone(), right.clone()),
        );
        let endpoint = self.explicit("bool_endpoint", constant("Bool"));
        let b = self.explicit("bool_discriminator", constant("Bool"));
        let (no, yes) = if left_true {
            (constant("False"), constant("True"))
        } else {
            (constant("True"), constant("False"))
        };
        let predicate = bool_rec(
            close(&[&b], Expr::sort(Level::zero()), true),
            no,
            yes,
            fv(&endpoint),
        );
        let contradiction = self.transport(
            &endpoint,
            left,
            right,
            fv(&hypothesis),
            predicate,
            constant("True.intro"),
        );
        close(&[&hypothesis], contradiction, true)
    }
}

fn bool_declaration() -> Declaration {
    let mut terms = Terms::default();
    let a = terms.explicit("a", constant("Bool"));
    let b = terms.explicit("b", constant("Bool"));
    let x = terms.explicit("x", constant("Bool"));
    let y = terms.explicit("y", constant("Bool"));
    let mut branches = Vec::new();
    for left_true in [false, true] {
        let left = constant(if left_true { "Bool.true" } else { "Bool.false" });
        let same = positive(
            bool_eq(left.clone(), left.clone()),
            refl(constant("Bool"), Level::one(), left.clone()),
        );
        let different = constant(if left_true { "Bool.false" } else { "Bool.true" });
        let other = negative(
            bool_eq(left.clone(), different),
            terms.bool_mismatch(left_true),
        );
        let (no, yes) = if left_true {
            (other, same)
        } else {
            (same, other)
        };
        branches.push(close(
            &[&b],
            bool_rec(
                close(&[&y], decision(bool_eq(left, fv(&y))), true),
                no,
                yes,
                fv(&b),
            ),
            true,
        ));
    }
    let motive = close(
        &[&x],
        close(&[&b], decision(bool_eq(fv(&x), fv(&b))), false),
        true,
    );
    let value = Expr::app(
        bool_rec(motive, branches[0].clone(), branches[1].clone(), fv(&a)),
        fv(&b),
    );
    defined(
        "Bool.decEq",
        vec![],
        &[&a, &b],
        decision(bool_eq(fv(&a), fv(&b))),
        value,
    )
}

fn nat_declaration() -> Declaration {
    let mut terms = Terms::default();
    let a = terms.explicit("a", constant("Nat"));
    let b = terms.explicit("b", constant("Nat"));
    let x = terms.explicit("x", constant("Nat"));
    let y = terms.explicit("y", constant("Nat"));
    let zero = constant("Nat.zero");
    let k = terms.explicit("zero_predecessor", constant("Nat"));
    let ih_zero = terms.explicit("zero_induction", decision(nat_eq(zero.clone(), fv(&k))));
    let zero_step = close(
        &[&k, &ih_zero],
        negative(
            nat_eq(zero.clone(), succ(fv(&k))),
            terms.nat_mismatch(fv(&k), true),
        ),
        true,
    );
    let zero_case = close(
        &[&b],
        nat_rec(
            close(&[&y], decision(nat_eq(zero.clone(), fv(&y))), true),
            positive(
                nat_eq(zero.clone(), zero.clone()),
                refl(constant("Nat"), Level::one(), zero.clone()),
            ),
            zero_step,
            fv(&b),
        ),
        true,
    );

    let n = terms.explicit("left_predecessor", constant("Nat"));
    let ih = terms.explicit(
        "left_induction",
        close(&[&b], decision(nat_eq(fv(&n), fv(&b))), false),
    );
    let m = terms.explicit("right_predecessor", constant("Nat"));
    let ignored = terms.explicit("right_induction", decision(nat_eq(succ(fv(&n)), fv(&m))));
    let smaller = nat_eq(fv(&n), fv(&m));
    let larger = nat_eq(succ(fv(&n)), succ(fv(&m)));
    let d = terms.explicit("smaller_decision", decision(smaller.clone()));
    let hp = terms.explicit("smaller_equality", smaller.clone());
    let hn = terms.explicit("smaller_inequality", neg(smaller.clone()));
    let h = terms.explicit("successor_equality", larger.clone());
    let injection = terms.succ_injective(fv(&n), fv(&m), fv(&h));
    let no = close(
        &[&hn],
        negative(
            larger.clone(),
            close(&[&h], Expr::app(fv(&hn), injection), true),
        ),
        true,
    );
    let congruence = terms.succ_congruent(fv(&n), fv(&m), fv(&hp));
    let yes = close(&[&hp], positive(larger.clone(), congruence), true);
    let step = app(
        Expr::const_(name("Decidable.rec"), vec![Level::one()]),
        [
            smaller,
            close(&[&d], decision(larger), true),
            no,
            yes,
            Expr::app(fv(&ih), fv(&m)),
        ],
    );
    let succ_case = close(
        &[&n, &ih, &b],
        nat_rec(
            close(&[&y], decision(nat_eq(succ(fv(&n)), fv(&y))), true),
            negative(
                nat_eq(succ(fv(&n)), zero),
                terms.nat_mismatch(fv(&n), false),
            ),
            close(&[&m, &ignored], step, true),
            fv(&b),
        ),
        true,
    );
    let motive = close(
        &[&x],
        close(&[&b], decision(nat_eq(fv(&x), fv(&b))), false),
        true,
    );
    let value = Expr::app(nat_rec(motive, zero_case, succ_case, fv(&a)), fv(&b));
    defined(
        "Nat.decEq",
        vec![],
        &[&a, &b],
        decision(nat_eq(fv(&a), fv(&b))),
        value,
    )
}

fn instance_declaration(carrier: &str) -> Declaration {
    let mut terms = Terms::default();
    let a = terms.explicit("a", constant(carrier));
    let b = terms.explicit("b", constant(carrier));
    defined(
        &format!("instDecidableEq{carrier}"),
        vec![],
        &[&a, &b],
        decision(eq(constant(carrier), Level::one(), fv(&a), fv(&b))),
        app(constant(&format!("{carrier}.decEq")), [fv(&a), fv(&b)]),
    )
}

/// Pure candidate constructors; publication and instance registration remain
/// the caller's ordinary kernel-plus-independent-checker responsibility.
pub fn equality_decision_seed_declarations() -> [Declaration; 4] {
    [
        bool_declaration(),
        nat_declaration(),
        instance_declaration("Bool"),
        instance_declaration("Nat"),
    ]
}
