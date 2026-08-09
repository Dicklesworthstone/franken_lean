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
