//! Regression guard for the large-elimination defect of bead `franken_lean-d17i`
//! (kernel repair landed at `bbb464f1`).
//!
//! `elim_only_at_universe_zero` decided whether a constructor field was a Prop
//! with the purely-STRUCTURAL `Level::is_zero()`, on a sort `whnf` had reduced as
//! an expression without normalising the level inside it. A field of sort
//! `Sort (imax u 0)` is semantically a Prop but is not `Node::Zero`, so it was
//! misread as data, found absent from the constructor's result, and the whole
//! inductive was restricted to Prop-only elimination — the regenerated recursor
//! carried NO motive universe and its level-parameter list came out one shorter
//! than the pin's, rejecting every declaration in the block (228 corpus rows
//! across 76 subsingleton types, `Acc` among them).
//!
//! This admits, THROUGH THE PUBLIC AUTHORITY, the minimal subsingleton that
//! reproduces the defect: `T (α : Sort u) (p : Prop) : Prop` with the single
//! constructor `T.mk : (α → p) → T α p`, whose one field has sort exactly
//! `imax u 0`. A large-eliminating recursor is admitted with it, so the block is
//! accepted ONLY when the field is recognised as a Prop and the motive universe
//! is regenerated. Under the pre-`bbb464f1` code the regenerated recursor is one
//! level-parameter short and the block is a `BlockMismatch`.
//!
//! These are also the only fast unit tests that admit an `InductiveBlock` through
//! the public authority at all (the admission engine is otherwise exercised only by
//! the Reference differential / corpus lane), so this file additionally guards the
//! recursor-regeneration paths those cases reach: single-type non-recursive (`T`),
//! single-type recursive/reflexive (`W`, Acc-shaped), and a two-type MUTUAL block
//! (`P`/`Q`) whose recursors each carry every block motive.

#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_env::constants::{ConstantVal, ConstructorVal, InductiveVal, RecursorRule, RecursorVal};
use fln_env::environment::Environment;
use fln_kernel::verdict::{Budget, Verdict};
use fln_kernel::{Declaration, InductiveBlock, check};

fn n(s: &str) -> Name {
    Name::str(Name::anonymous(), s)
}

fn nn(outer: &str, inner: &str) -> Name {
    Name::str(n(outer), inner)
}

fn bvar(i: u32) -> Expr {
    Expr::bvar(i).expect("packs")
}

fn app2(f: Expr, a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(f, a), b)
}

/// `T` referenced at universe `u` (level index 1 in the recursor, the sole level
/// in `T`/`T.mk`).
fn t_const(u: &Name) -> Expr {
    Expr::const_(n("T"), vec![Level::param(u.clone())])
}

fn mk_const(u: &Name) -> Expr {
    Expr::const_(nn("T", "mk"), vec![Level::param(u.clone())])
}

fn forall(name: &str, ty: Expr, body: Expr) -> Expr {
    Expr::forall_e(n(name), ty, body, BinderInfo::Default)
}

fn forall_impl(name: &str, ty: Expr, body: Expr) -> Expr {
    Expr::forall_e(n(name), ty, body, BinderInfo::Implicit)
}

fn lam(name: &str, ty: Expr, body: Expr) -> Expr {
    Expr::lam(n(name), ty, body, BinderInfo::Default)
}

fn sort(l: Level) -> Expr {
    Expr::sort(l)
}

fn prop() -> Expr {
    Expr::sort(Level::zero())
}

/// The block for `T (α : Sort u) (p : Prop) : Prop` with `T.mk : (α → p) → T α p`
/// and a large-eliminating recursor at a fresh motive universe `mu`.
fn t_block(u: &Name, mu: &Name) -> InductiveBlock {
    // T : ∀ (α : Sort u) (p : Prop), Prop
    let t_type = forall(
        "α",
        sort(Level::param(u.clone())),
        forall("p", prop(), prop()),
    );

    // T.mk : ∀ (α : Sort u) (p : Prop) (f : α → p), T α p
    //   at f's binder: α = bvar 1, p = bvar 0; f = α → p = ∀ (_ : α), p
    //   under the `_` binder p becomes bvar 1.
    let field_ty = forall("_x", bvar(1), bvar(1)); // α → p
    // body T α p under (α=2, p=1, f=0)
    let mk_result = app2(t_const(u), bvar(2), bvar(1));
    let mk_type = forall(
        "α",
        sort(Level::param(u.clone())),
        forall("p", prop(), forall("f", field_ty, mk_result)),
    );

    // T.rec.{mu,u} : ∀ (α : Sort u) (p : Prop)
    //   (motive : T α p → Sort mu)
    //   (mk : ∀ (f : α → p), motive (T.mk α p f))
    //   (t : T α p), motive t
    //
    // Indices below are relative to each binder position; converged against the
    // engine's own regeneration (the reject message pinpoints any drift).
    let motive_ty = forall(
        "t",
        app2(t_const(u), bvar(1), bvar(0)),
        sort(Level::param(mu.clone())),
    );
    // minor `mk`: ∀ (f : α → p), motive (T.mk α p f)
    //   scope entering the minor: α=2, p=1, motive=0
    //   f's type α → p: α=bvar 2, p=bvar 1 → ∀(_:α), p  ⇒ ∀(_: bvar2), bvar2
    let minor_field_ty = forall("_x", bvar(2), bvar(2));
    // body motive (T.mk α p f): scope α=3,p=2,motive=1,f=0
    let mk_applied = Expr::app(Expr::app(Expr::app(mk_const(u), bvar(3)), bvar(2)), bvar(0));
    let minor_body = Expr::app(bvar(1), mk_applied);
    let minor_ty = forall("f", minor_field_ty, minor_body);
    // major t : T α p ; scope α=3,p=2,motive=1,mk=0
    let major_ty = app2(t_const(u), bvar(3), bvar(2));
    // result motive t ; scope α=4,p=3,motive=2,mk=1,t=0
    let rec_result = Expr::app(bvar(2), bvar(0));
    // `infer_implicit_strict`: a binder is Implicit iff its variable occurs in a
    // later binder's type. α, p, motive each do; mk and t do not.
    let rec_type = forall_impl(
        "α",
        sort(Level::param(u.clone())),
        forall_impl(
            "p",
            prop(),
            forall_impl(
                "motive",
                motive_ty,
                forall("mk", minor_ty, forall("t", major_ty, rec_result)),
            ),
        ),
    );

    // iota rhs: fun (α) (p) (motive) (mk) (f) => mk f
    //   scope inside: α=4,p=3,motive=2,mk=1,f=0
    let rhs = lam(
        "α",
        sort(Level::param(u.clone())),
        lam(
            "p",
            prop(),
            lam(
                "motive",
                // motive : T α p → Sort mu, α=1,p=0 here
                forall(
                    "t",
                    app2(t_const(u), bvar(1), bvar(0)),
                    sort(Level::param(mu.clone())),
                ),
                lam(
                    "mk",
                    // mk minor type, α=2,p=1,motive=0
                    forall(
                        "f",
                        forall("_x", bvar(2), bvar(2)),
                        Expr::app(
                            bvar(1),
                            Expr::app(Expr::app(Expr::app(mk_const(u), bvar(3)), bvar(2)), bvar(0)),
                        ),
                    ),
                    lam(
                        "f",
                        forall("_x", bvar(3), bvar(3)),
                        Expr::app(bvar(1), bvar(0)),
                    ),
                ),
            ),
        ),
    );

    let recursor = RecursorVal {
        base: ConstantVal {
            name: nn("T", "rec"),
            level_params: vec![mu.clone(), u.clone()],
            type_: rec_type,
        },
        all: vec![n("T")],
        num_params: 2,
        num_indices: 0,
        num_motives: 1,
        num_minors: 1,
        rules: vec![RecursorRule {
            ctor: nn("T", "mk"),
            nfields: 1,
            rhs,
        }],
        k: false,
        is_unsafe: false,
    };

    InductiveBlock {
        types: vec![InductiveVal {
            base: ConstantVal {
                name: n("T"),
                level_params: vec![u.clone()],
                type_: t_type,
            },
            num_params: 2,
            num_indices: 0,
            all: vec![n("T")],
            ctors: vec![nn("T", "mk")],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }],
        ctors: vec![ConstructorVal {
            base: ConstantVal {
                name: nn("T", "mk"),
                level_params: vec![u.clone()],
                type_: mk_type,
            },
            induct: n("T"),
            cidx: 0,
            num_params: 2,
            num_fields: 1,
            is_unsafe: false,
        }],
        recursors: vec![recursor],
    }
}

#[test]
fn imax_field_permits_large_elimination() {
    let u = n("u");
    let mu = n("u_1");
    let block = t_block(&u, &mu);
    let verdict = check(
        &Environment::new(),
        &Declaration::Inductive(block),
        Budget::DEFAULT,
    );
    assert!(
        matches!(
            verdict,
            fln_core::outcome::Outcome::Complete(Verdict::Accepted { .. })
        ),
        "T's `imax u 0` field must be recognised as a Prop so the recursor keeps \
         its motive universe (bead franken_lean-d17i); got {verdict:?}"
    );
}

/// The `Acc`-shaped RECURSIVE reproducer: `W (α : Sort u) : Prop` with
/// `W.sup : (α → W α) → W α`. The field `α → W α` has sort `imax u 0` AND is a
/// reflexive recursive occurrence, so admission exercises the induction-hypothesis
/// generation and the recursive iota right-hand side (`mk_rec_rules`) that the
/// non-recursive `T` never reaches — the path the real `Acc`/`WellFounded` block
/// takes. Same defect: pre-`bbb464f1`, the `imax u 0` field reads as data and the
/// recursor loses its motive universe.
fn w_block(u: &Name, mu: &Name) -> InductiveBlock {
    let w = || Expr::const_(n("W"), vec![Level::param(u.clone())]);
    let wsup = || Expr::const_(nn("W", "sup"), vec![Level::param(u.clone())]);
    let wrec = || {
        Expr::const_(
            nn("W", "rec"),
            vec![Level::param(mu.clone()), Level::param(u.clone())],
        )
    };

    // W : ∀ (α : Sort u), Prop
    let w_type = forall("α", sort(Level::param(u.clone())), prop());

    // W.sup : ∀ (α : Sort u) (f : α → W α), W α
    //   f's type at α=bvar0: ∀ (_ : α[bvar0]), W α[bvar1]
    let sup_field = forall("_a", bvar(0), Expr::app(w(), bvar(1)));
    let sup_type = forall(
        "α",
        sort(Level::param(u.clone())),
        forall("f", sup_field, Expr::app(w(), bvar(1))), // result W α, α=bvar1
    );

    // W.rec.{mu,u} : {α} {motive : W α → Sort mu}
    //   (sup : ∀ (f : α → W α) (ih : ∀ a, motive (f a)), motive (W.sup α f)) {t : W α}, motive t
    let motive_ty = forall("t", Expr::app(w(), bvar(0)), sort(Level::param(mu.clone()))); // α=bvar0
    // minor sup, scope α=bvar1 motive=bvar0
    let sup_f_ty = forall("_a", bvar(1), Expr::app(w(), bvar(2)));
    // ih : ∀ (a : α), motive (f a); scope α=2 motive=1 f=0, under a: motive=2 f=1 a=0
    let sup_ih_ty = forall(
        "_a",
        bvar(2),
        Expr::app(bvar(2), Expr::app(bvar(1), bvar(0))),
    );
    // result motive (W.sup α f); scope α=3 motive=2 f=1 ih=0
    let sup_result = Expr::app(bvar(2), Expr::app(Expr::app(wsup(), bvar(3)), bvar(1)));
    let sup_minor_ty = forall("f", sup_f_ty, forall("f_ih", sup_ih_ty, sup_result));
    let major_ty = Expr::app(w(), bvar(2)); // t : W α; scope α=2 motive=1 sup=0
    let rec_result = Expr::app(bvar(2), bvar(0)); // motive t; scope α=3 motive=2 sup=1 t=0
    let rec_type = forall_impl(
        "α",
        sort(Level::param(u.clone())),
        forall_impl(
            "motive",
            motive_ty,
            forall("sup", sup_minor_ty, forall("t", major_ty, rec_result)),
        ),
    );

    // iota rhs: fun α motive sup f => sup f (fun a => W.rec α motive sup (f a))
    let rhs_motive_ty = forall("t", Expr::app(w(), bvar(0)), sort(Level::param(mu.clone())));
    let rhs_sup_f_ty = forall("_a", bvar(1), Expr::app(w(), bvar(2)));
    let rhs_sup_ih_ty = forall(
        "_a",
        bvar(2),
        Expr::app(bvar(2), Expr::app(bvar(1), bvar(0))),
    );
    let rhs_sup_result = Expr::app(bvar(2), Expr::app(Expr::app(wsup(), bvar(3)), bvar(1)));
    let rhs_sup_ty = forall(
        "f",
        rhs_sup_f_ty,
        forall("f_ih", rhs_sup_ih_ty, rhs_sup_result),
    );
    // f's type at scope α=2 motive=1 sup=0: ∀(_:α[bvar2]), W α[bvar3]
    let rhs_f_ty = forall("_a", bvar(2), Expr::app(w(), bvar(3)));
    // ih_value = fun (a : α) => W.rec α motive sup (f a); a:α=bvar3, under a shift +1
    let ih_value = lam(
        "_a",
        bvar(3),
        Expr::app(
            Expr::app(Expr::app(Expr::app(wrec(), bvar(4)), bvar(3)), bvar(2)),
            Expr::app(bvar(1), bvar(0)),
        ),
    );
    // body: sup f ih_value; sup=bvar1 f=bvar0
    let rhs_body = Expr::app(Expr::app(bvar(1), bvar(0)), ih_value);
    let rhs = lam(
        "α",
        sort(Level::param(u.clone())),
        lam(
            "motive",
            rhs_motive_ty,
            lam("sup", rhs_sup_ty, lam("f", rhs_f_ty, rhs_body)),
        ),
    );

    let recursor = RecursorVal {
        base: ConstantVal {
            name: nn("W", "rec"),
            level_params: vec![mu.clone(), u.clone()],
            type_: rec_type,
        },
        all: vec![n("W")],
        num_params: 1,
        num_indices: 0,
        num_motives: 1,
        num_minors: 1,
        rules: vec![RecursorRule {
            ctor: nn("W", "sup"),
            nfields: 1,
            rhs,
        }],
        k: false,
        is_unsafe: false,
    };

    InductiveBlock {
        types: vec![InductiveVal {
            base: ConstantVal {
                name: n("W"),
                level_params: vec![u.clone()],
                type_: w_type,
            },
            num_params: 1,
            num_indices: 0,
            all: vec![n("W")],
            ctors: vec![nn("W", "sup")],
            num_nested: 0,
            is_rec: true,
            is_unsafe: false,
            is_reflexive: true,
        }],
        ctors: vec![ConstructorVal {
            base: ConstantVal {
                name: nn("W", "sup"),
                level_params: vec![u.clone()],
                type_: sup_type,
            },
            induct: n("W"),
            cidx: 0,
            num_params: 1,
            num_fields: 1,
            is_unsafe: false,
        }],
        recursors: vec![recursor],
    }
}

#[test]
fn recursive_imax_field_permits_large_elimination() {
    let u = n("u");
    let mu = n("u_1");
    let block = w_block(&u, &mu);
    let verdict = check(
        &Environment::new(),
        &Declaration::Inductive(block),
        Budget::DEFAULT,
    );
    assert!(
        matches!(
            verdict,
            fln_core::outcome::Outcome::Complete(Verdict::Accepted { .. })
        ),
        "W (Acc-shaped recursive Prop) with an `imax u 0` recursive field must permit \
         large elimination via the recursive recursor path (bead franken_lean-d17i); \
         got {verdict:?}"
    );
}

/// A minimal MUTUAL inductive block `{P, Q}` — both `Type`, nullary constructors,
/// no cross-reference — admitted through the public authority. This is a genuinely
/// distinct admission path from the single-type cases above: `generate_recursors`
/// emits EACH recursor carrying ALL block motives (`motive_1`, `motive_2`) and ALL
/// minors (`p`, `q`), the mutual recursor regeneration that otherwise only the
/// Reference differential / corpus lane exercises. A fast per-commit guard for it.
fn pq_block(u: &Name) -> InductiveBlock {
    let p = || Expr::const_(n("P"), vec![]);
    let q = || Expr::const_(n("Q"), vec![]);
    let pp = || Expr::const_(nn("P", "p"), vec![]);
    let qq = || Expr::const_(nn("Q", "q"), vec![]);
    let sort_u = || sort(Level::param(u.clone()));
    let type1 = || sort(Level::one());

    // motive_1 : P → Sort u ; motive_2 : Q → Sort u  (closed, no bvars)
    let motive1_ty = || forall("t", p(), sort_u());
    let motive2_ty = || forall("t", q(), sort_u());
    // minor types: `p : motive_1 P.p` (scope m1=1,m2=0), `q : motive_2 Q.q` (scope m1=2,m2=1,p=0)
    let minor_p_ty = || Expr::app(bvar(1), pp());
    let minor_q_ty = || Expr::app(bvar(1), qq());

    // {motive_1}{motive_2}(p)(q)(t : major), motive_{result} t
    //   scope at result: m1=4,m2=3,p=2,q=1,t=0
    let rec_type = |major: Expr, result_motive: u32| {
        forall_impl(
            "motive_1",
            motive1_ty(),
            forall_impl(
                "motive_2",
                motive2_ty(),
                forall(
                    "p",
                    minor_p_ty(),
                    forall(
                        "q",
                        minor_q_ty(),
                        forall("t", major, Expr::app(bvar(result_motive), bvar(0))),
                    ),
                ),
            ),
        )
    };
    // rhs: fun motive_1 motive_2 p q => <minor>  (no fields/ihs); scope m1=3,m2=2,p=1,q=0
    let rec_rhs = |minor: u32| {
        lam(
            "motive_1",
            motive1_ty(),
            lam(
                "motive_2",
                motive2_ty(),
                lam("p", minor_p_ty(), lam("q", minor_q_ty(), bvar(minor))),
            ),
        )
    };

    let recursor = |name: Name, ctor: Name, ty: Expr, rhs: Expr| RecursorVal {
        base: ConstantVal {
            name,
            level_params: vec![u.clone()],
            type_: ty,
        },
        all: vec![n("P"), n("Q")],
        num_params: 0,
        num_indices: 0,
        num_motives: 2,
        num_minors: 2,
        rules: vec![RecursorRule {
            ctor,
            nfields: 0,
            rhs,
        }],
        k: false,
        is_unsafe: false,
    };

    let inductive = |name: Name, ctor: Name| InductiveVal {
        base: ConstantVal {
            name,
            level_params: vec![],
            type_: type1(),
        },
        num_params: 0,
        num_indices: 0,
        all: vec![n("P"), n("Q")],
        ctors: vec![ctor],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    };
    let ctor = |name: Name, induct: Name, ty: Expr| ConstructorVal {
        base: ConstantVal {
            name,
            level_params: vec![],
            type_: ty,
        },
        induct,
        cidx: 0,
        num_params: 0,
        num_fields: 0,
        is_unsafe: false,
    };

    InductiveBlock {
        types: vec![
            inductive(n("P"), nn("P", "p")),
            inductive(n("Q"), nn("Q", "q")),
        ],
        ctors: vec![
            ctor(nn("P", "p"), n("P"), p()),
            ctor(nn("Q", "q"), n("Q"), q()),
        ],
        // P.rec result is motive_1 (bvar 4); Q.rec result is motive_2 (bvar 3).
        // P.rec.(P.p) ↦ p (minor bvar 1); Q.rec.(Q.q) ↦ q (minor bvar 0).
        recursors: vec![
            recursor(nn("P", "rec"), nn("P", "p"), rec_type(p(), 4), rec_rhs(1)),
            recursor(nn("Q", "rec"), nn("Q", "q"), rec_type(q(), 3), rec_rhs(0)),
        ],
    }
}

#[test]
fn mutual_inductive_block_admits() {
    let u = n("u");
    let block = pq_block(&u);
    let verdict = check(
        &Environment::new(),
        &Declaration::Inductive(block),
        Budget::DEFAULT,
    );
    assert!(
        matches!(
            verdict,
            fln_core::outcome::Outcome::Complete(Verdict::Accepted { .. })
        ),
        "a two-type mutual inductive block must admit, exercising cross-motive \
         recursor regeneration (both `motive_1` and `motive_2` in each recursor); \
         got {verdict:?}"
    );
}
