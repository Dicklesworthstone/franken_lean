//! Nested-family admission through the independent checker. Every declared
//! recursor below is written out by hand in the form the pin's
//! `elim_nested_inductive` and restoration produce; none is derived from the
//! checker's own reconstruction.
#![forbid(unsafe_code)]
use fln_checker::admit::{AdmissionBudget, InductiveRejection, InductiveVerdict, admit_inductive};
use fln_checker::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantSafety,
    ConstructorDeclaration, EnvironmentBudget, EnvironmentOutcome, InductiveDeclaration,
    RecursorDeclaration, RecursorRule,
};
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, WireExpr, WireName, decode_expr, decode_name,
};
use fln_core::expr::{BinderInfo, Expr, FVarId};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_hash::canon::Canonical;

fn name(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn wn(s: &str) -> WireName {
    match decode_name(&name(s).to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("name decode {other:?}"),
    }
}
fn we(expr: &Expr) -> WireExpr {
    match decode_expr(&expr.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("term decode {other:?}"),
    }
}
fn param(s: &str) -> Level {
    Level::param(name(s))
}
fn max(a: Level, b: Level) -> Level {
    Level::max(a, b).expect("level fits")
}
fn ty(level: Level) -> Expr {
    Expr::sort(Level::succ(level).expect("level fits"))
}
fn c(n: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(name(n), levels)
}
fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}

#[derive(Clone)]
struct Local {
    id: FVarId,
    ty: Expr,
}
fn local(label: &str, ty: Expr) -> Local {
    Local {
        id: FVarId(name(&format!("fixture_local.{label}"))),
        ty,
    }
}
impl Local {
    fn e(&self) -> Expr {
        Expr::fvar(self.id.clone())
    }
}
fn close(locals: &[&Local], mut body: Expr, lambda: bool) -> Expr {
    for l in locals.iter().rev() {
        body = body.abstract_fvar(&l.id, 0).expect("abstract");
        body = if lambda {
            Expr::lam(name("x"), l.ty.clone(), body, BinderInfo::Default)
        } else {
            Expr::forall_e(name("x"), l.ty.clone(), body, BinderInfo::Default)
        };
    }
    body
}
fn pi(locals: &[&Local], body: Expr) -> Expr {
    close(locals, body, false)
}
fn lam(locals: &[&Local], body: Expr) -> Expr {
    close(locals, body, true)
}

#[allow(clippy::too_many_arguments)]
fn inductive(
    n: &str,
    levels: &[&str],
    ty: Expr,
    parameters: u32,
    all: &[&str],
    ctors: &[&str],
    nested: u32,
    recursive: bool,
) -> ConstantEntry {
    ConstantEntry::new(
        wn(n),
        ConstantDeclaration::inductive(
            levels.iter().map(|l| wn(l)).collect(),
            we(&ty),
            ConstantSafety::Safe,
            InductiveDeclaration::new(
                parameters,
                0,
                all.iter().map(|a| wn(a)).collect(),
                ctors.iter().map(|c| wn(c)).collect(),
                nested,
                recursive,
                false,
            ),
        ),
    )
}
fn constructor(
    n: &str,
    levels: &[&str],
    ty: Expr,
    family: &str,
    index: u32,
    parameters: u32,
    fields: u32,
) -> ConstantEntry {
    ConstantEntry::new(
        wn(n),
        ConstantDeclaration::constructor(
            levels.iter().map(|l| wn(l)).collect(),
            we(&ty),
            ConstantSafety::Safe,
            ConstructorDeclaration::new(wn(family), index, parameters, fields),
        ),
    )
}
#[allow(clippy::too_many_arguments)]
fn recursor(
    n: &str,
    levels: &[&str],
    ty: Expr,
    all: &[&str],
    parameters: u32,
    motives: u32,
    minors: u32,
    rules: Vec<(&str, u32, Expr)>,
) -> ConstantEntry {
    ConstantEntry::new(
        wn(n),
        ConstantDeclaration::recursor(
            levels.iter().map(|l| wn(l)).collect(),
            we(&ty),
            ConstantSafety::Safe,
            RecursorDeclaration::new(
                all.iter().map(|a| wn(a)).collect(),
                parameters,
                0,
                motives,
                minors,
                rules
                    .into_iter()
                    .map(|(ctor, fields, rhs)| RecursorRule::new(wn(ctor), fields, we(&rhs)))
                    .collect(),
                false,
            ),
        ),
    )
}
fn environment(entries: Vec<ConstantEntry>) -> ConstantEnvironment {
    match ConstantEnvironment::build(entries, EnvironmentBudget::unlimited()) {
        EnvironmentOutcome::Complete { environment, .. } => environment,
        other => panic!("environment {other:?}"),
    }
}
fn verdict(environment: &ConstantEnvironment, rows: &[ConstantEntry]) -> InductiveVerdict {
    admit_inductive(
        environment,
        rows,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    )
}

/// `Box.{u} (α : Type u) : Type u` with `Box.mk : {α} → α → Box α`.
fn box_entries() -> Vec<ConstantEntry> {
    let alpha = local("box.alpha", ty(param("u")));
    let x = local("box.x", alpha.e());
    let box_alpha = app(c("Box", vec![param("u")]), [alpha.e()]);
    vec![
        inductive(
            "Box",
            &["u"],
            pi(&[&alpha], ty(param("u"))),
            1,
            &["Box"],
            &["Box.mk"],
            0,
            false,
        ),
        constructor(
            "Box.mk",
            &["u"],
            pi(&[&alpha, &x], box_alpha),
            "Box",
            0,
            1,
            1,
        ),
    ]
}

/// F1: `T (α β : Type) | leaf (a : α) (b : β) | node (c : Box (T α β))`, one
/// auxiliary family for `Box (T α β)`. Two parameters, so the parameters must
/// be closed back in their own order.
fn f1(mutation: &str) -> (ConstantEnvironment, Vec<ConstantEntry>) {
    let zero = || Level::zero();
    let alpha = local("alpha", ty(zero()));
    let beta = local("beta", ty(zero()));
    let t = |a: Expr, b: Expr| app(c("T", vec![]), [a, b]);
    let t_ab = t(alpha.e(), beta.e());
    let box_t = app(c("Box", vec![zero()]), [t_ab.clone()]);
    let a = local("a", alpha.e());
    let b = local("b", beta.e());
    let child = local("child", box_t.clone());
    let x = local("x", t_ab.clone());
    let w = param("w");
    let m1 = local(
        "m1",
        pi(&[&local("t1", t_ab.clone())], Expr::sort(w.clone())),
    );
    let m2 = local(
        "m2",
        pi(&[&local("t2", box_t.clone())], Expr::sort(w.clone())),
    );
    let leaf_value = app(c("T.leaf", vec![]), [alpha.e(), beta.e(), a.e(), b.e()]);
    let node_value = app(c("T.node", vec![]), [alpha.e(), beta.e(), child.e()]);
    let mk_value = app(c("Box.mk", vec![zero()]), [t_ab.clone(), x.e()]);
    let ih_child = local("ih_child", app(m2.e(), [child.e()]));
    let ih_x = local("ih_x", app(m1.e(), [x.e()]));
    let leaf = local("leaf", pi(&[&a, &b], app(m1.e(), [leaf_value])));
    let node = local("node", pi(&[&child, &ih_child], app(m1.e(), [node_value])));
    let mk = local("mk", pi(&[&x, &ih_x], app(m2.e(), [mk_value])));
    let prefix = [&alpha, &beta, &m1, &m2, &leaf, &node, &mk];
    let head = |n: &str| app(c(n, vec![w.clone()]), prefix.iter().map(|l| l.e()));
    let major_t = local("major_t", t_ab.clone());
    let major_box = local("major_box", box_t.clone());
    let rec_type = pi(
        &[&alpha, &beta, &m1, &m2, &leaf, &node, &mk, &major_t],
        app(m1.e(), [major_t.e()]),
    );
    let rec1_type = pi(
        &[&alpha, &beta, &m1, &m2, &leaf, &node, &mk, &major_box],
        app(m2.e(), [major_box.e()]),
    );
    let leaf_rule = lam(
        &[&alpha, &beta, &m1, &m2, &leaf, &node, &mk, &a, &b],
        app(leaf.e(), [a.e(), b.e()]),
    );
    let node_rule = lam(
        &[&alpha, &beta, &m1, &m2, &leaf, &node, &mk, &child],
        app(node.e(), [child.e(), app(head("T.rec_1"), [child.e()])]),
    );
    // The induction hypothesis for `Box.mk`'s field calls `T.rec`; the mutation
    // calls the auxiliary recursor instead.
    let mk_minor_ih = if mutation == "swapped_ih" {
        app(head("T.rec_1"), [x.e()])
    } else {
        app(head("T.rec"), [x.e()])
    };
    let mk_rule = lam(
        &[&alpha, &beta, &m1, &m2, &leaf, &node, &mk, &x],
        app(mk.e(), [x.e(), mk_minor_ih]),
    );
    let leaf_rule = if mutation == "private_name" {
        lam(
            &[&alpha, &beta, &m1, &m2, &leaf, &node, &mk, &a, &b],
            app(leaf.e(), [a.e(), app(c("_fln_nested.1", vec![]), [b.e()])]),
        )
    } else {
        leaf_rule
    };
    let nested = if mutation == "nested_count" { 2 } else { 1 };
    let t_type = pi(&[&alpha, &beta], ty(zero()));
    let rows = vec![
        inductive(
            "T",
            &[],
            t_type,
            2,
            &["T"],
            &["T.leaf", "T.node"],
            nested,
            true,
        ),
        constructor(
            "T.leaf",
            &[],
            pi(&[&alpha, &beta, &a, &b], t_ab.clone()),
            "T",
            0,
            2,
            2,
        ),
        constructor(
            "T.node",
            &[],
            pi(&[&alpha, &beta, &child], t_ab.clone()),
            "T",
            1,
            2,
            1,
        ),
        recursor(
            "T.rec",
            &["w"],
            rec_type,
            &["T"],
            2,
            2,
            3,
            vec![("T.leaf", 2, leaf_rule), ("T.node", 1, node_rule)],
        ),
        recursor(
            "T.rec_1",
            &["w"],
            rec1_type,
            &["T"],
            2,
            2,
            3,
            vec![("Box.mk", 1, mk_rule)],
        ),
    ];
    (environment(box_entries()), rows)
}

/// `Wrap.{u} (α : Type u) : Type u` with `Wrap.mk : {α} → Box.{max u u} α →
/// Wrap α`. At `u := 0` the pin's `mk_max` writes the field as `Box.{0} α`.
fn wrap_entries() -> Vec<ConstantEntry> {
    let alpha = local("wrap.alpha", ty(param("u")));
    let inner = local(
        "wrap.inner",
        app(c("Box", vec![max(param("u"), param("u"))]), [alpha.e()]),
    );
    let mut entries = box_entries();
    entries.push(inductive(
        "Wrap",
        &["u"],
        pi(&[&alpha], ty(param("u"))),
        1,
        &["Wrap"],
        &["Wrap.mk"],
        0,
        false,
    ));
    entries.push(constructor(
        "Wrap.mk",
        &["u"],
        pi(
            &[&alpha, &inner],
            app(c("Wrap", vec![param("u")]), [alpha.e()]),
        ),
        "Wrap",
        0,
        1,
        1,
    ));
    entries
}

/// F2: `S | leaf | node (w : Wrap S)`. Two auxiliary families, `Wrap S` and then
/// `Box.{0} S` from `Wrap.mk`'s field, written as the pin's `mk_max` leaves it.
fn f2() -> (ConstantEnvironment, Vec<ConstantEntry>) {
    let zero = || Level::zero();
    let s = c("S", vec![]);
    let wrap_s = app(c("Wrap", vec![zero()]), [s.clone()]);
    let box_s = app(c("Box", vec![zero()]), [s.clone()]);
    let w = param("w");
    let m1 = local("m1", pi(&[&local("t1", s.clone())], Expr::sort(w.clone())));
    let m2 = local(
        "m2",
        pi(&[&local("t2", wrap_s.clone())], Expr::sort(w.clone())),
    );
    let m3 = local(
        "m3",
        pi(&[&local("t3", box_s.clone())], Expr::sort(w.clone())),
    );
    let child = local("child", wrap_s.clone());
    let inner = local("inner", box_s.clone());
    let x = local("x", s.clone());
    let ih_child = local("ih_child", app(m2.e(), [child.e()]));
    let ih_inner = local("ih_inner", app(m3.e(), [inner.e()]));
    let ih_x = local("ih_x", app(m1.e(), [x.e()]));
    let leaf = local("leaf", app(m1.e(), [c("S.leaf", vec![])]));
    let node = local(
        "node",
        pi(
            &[&child, &ih_child],
            app(m1.e(), [app(c("S.node", vec![]), [child.e()])]),
        ),
    );
    let wrap_mk = local(
        "wrap_mk",
        pi(
            &[&inner, &ih_inner],
            app(
                m2.e(),
                [app(c("Wrap.mk", vec![zero()]), [s.clone(), inner.e()])],
            ),
        ),
    );
    let box_mk = local(
        "box_mk",
        pi(
            &[&x, &ih_x],
            app(m3.e(), [app(c("Box.mk", vec![zero()]), [s.clone(), x.e()])]),
        ),
    );
    let prefix = [&m1, &m2, &m3, &leaf, &node, &wrap_mk, &box_mk];
    let head = |n: &str| app(c(n, vec![w.clone()]), prefix.iter().map(|l| l.e()));
    let rec_type = |major: &Local, motive: &Local| {
        let mut all: Vec<&Local> = prefix.to_vec();
        all.push(major);
        pi(&all, app(motive.e(), [major.e()]))
    };
    let rule = |fields: &[&Local], body: Expr| {
        let mut all: Vec<&Local> = prefix.to_vec();
        all.extend_from_slice(fields);
        lam(&all, body)
    };
    let major_s = local("major_s", s.clone());
    let major_wrap = local("major_wrap", wrap_s.clone());
    let major_box = local("major_box", box_s.clone());
    let rows = vec![
        inductive(
            "S",
            &[],
            ty(zero()),
            0,
            &["S"],
            &["S.leaf", "S.node"],
            2,
            true,
        ),
        constructor("S.leaf", &[], s.clone(), "S", 0, 0, 0),
        constructor("S.node", &[], pi(&[&child], s.clone()), "S", 1, 0, 1),
        recursor(
            "S.rec",
            &["w"],
            rec_type(&major_s, &m1),
            &["S"],
            0,
            3,
            4,
            vec![
                ("S.leaf", 0, rule(&[], leaf.e())),
                (
                    "S.node",
                    1,
                    rule(
                        &[&child],
                        app(node.e(), [child.e(), app(head("S.rec_1"), [child.e()])]),
                    ),
                ),
            ],
        ),
        recursor(
            "S.rec_1",
            &["w"],
            rec_type(&major_wrap, &m2),
            &["S"],
            0,
            3,
            4,
            vec![(
                "Wrap.mk",
                1,
                rule(
                    &[&inner],
                    app(wrap_mk.e(), [inner.e(), app(head("S.rec_2"), [inner.e()])]),
                ),
            )],
        ),
        recursor(
            "S.rec_2",
            &["w"],
            rec_type(&major_box, &m3),
            &["S"],
            0,
            3,
            4,
            vec![(
                "Box.mk",
                1,
                rule(&[&x], app(box_mk.e(), [x.e(), app(head("S.rec"), [x.e()])])),
            )],
        ),
    ];
    (environment(wrap_entries()), rows)
}

/// F3: `R.{u,v} : Type (max u v) | leaf | node (j : J.{u,v} R)`, where
/// `J.{a,b} (γ : Type (max a b)) : Type (max b a)`. The auxiliary family's
/// sort, `Type (max v u)`, is the block's only up to level equivalence, which is
/// how the pin compares them.
fn f3() -> (ConstantEnvironment, Vec<ConstantEntry>) {
    let (u, v) = (param("u"), param("v"));
    let gamma = local("j.gamma", ty(max(param("a"), param("b"))));
    let y = local("j.y", gamma.e());
    let env = environment(vec![
        inductive(
            "J",
            &["a", "b"],
            pi(&[&gamma], ty(max(param("b"), param("a")))),
            1,
            &["J"],
            &["J.mk"],
            0,
            false,
        ),
        constructor(
            "J.mk",
            &["a", "b"],
            pi(
                &[&gamma, &y],
                app(c("J", vec![param("a"), param("b")]), [gamma.e()]),
            ),
            "J",
            0,
            1,
            1,
        ),
    ]);
    let r = c("R", vec![u.clone(), v.clone()]);
    let j_r = app(c("J", vec![u.clone(), v.clone()]), [r.clone()]);
    let w = param("w");
    let m1 = local("m1", pi(&[&local("t1", r.clone())], Expr::sort(w.clone())));
    let m2 = local(
        "m2",
        pi(&[&local("t2", j_r.clone())], Expr::sort(w.clone())),
    );
    let child = local("child", j_r.clone());
    let x = local("x", r.clone());
    let ih_child = local("ih_child", app(m2.e(), [child.e()]));
    let ih_x = local("ih_x", app(m1.e(), [x.e()]));
    let leaf = local(
        "leaf",
        app(m1.e(), [c("R.leaf", vec![u.clone(), v.clone()])]),
    );
    let node = local(
        "node",
        pi(
            &[&child, &ih_child],
            app(
                m1.e(),
                [app(c("R.node", vec![u.clone(), v.clone()]), [child.e()])],
            ),
        ),
    );
    let mk = local(
        "mk",
        pi(
            &[&x, &ih_x],
            app(
                m2.e(),
                [app(
                    c("J.mk", vec![u.clone(), v.clone()]),
                    [r.clone(), x.e()],
                )],
            ),
        ),
    );
    let prefix = [&m1, &m2, &leaf, &node, &mk];
    let head = |n: &str| {
        app(
            c(n, vec![w.clone(), u.clone(), v.clone()]),
            prefix.iter().map(|l| l.e()),
        )
    };
    let major_r = local("major_r", r.clone());
    let major_j = local("major_j", j_r.clone());
    let rows = vec![
        inductive(
            "R",
            &["u", "v"],
            ty(max(u.clone(), v.clone())),
            0,
            &["R"],
            &["R.leaf", "R.node"],
            1,
            true,
        ),
        constructor("R.leaf", &["u", "v"], r.clone(), "R", 0, 0, 0),
        constructor(
            "R.node",
            &["u", "v"],
            pi(&[&child], r.clone()),
            "R",
            1,
            0,
            1,
        ),
        recursor(
            "R.rec",
            &["w", "u", "v"],
            pi(&joined(&prefix, &[&major_r]), app(m1.e(), [major_r.e()])),
            &["R"],
            0,
            2,
            3,
            vec![
                ("R.leaf", 0, lam(&joined(&prefix, &[]), leaf.e())),
                (
                    "R.node",
                    1,
                    lam(
                        &joined(&prefix, &[&child]),
                        app(node.e(), [child.e(), app(head("R.rec_1"), [child.e()])]),
                    ),
                ),
            ],
        ),
        recursor(
            "R.rec_1",
            &["w", "u", "v"],
            pi(&joined(&prefix, &[&major_j]), app(m2.e(), [major_j.e()])),
            &["R"],
            0,
            2,
            3,
            vec![(
                "J.mk",
                1,
                lam(
                    &joined(&prefix, &[&x]),
                    app(mk.e(), [x.e(), app(head("R.rec"), [x.e()])]),
                ),
            )],
        ),
    ];
    (env, rows)
}

/// F4: `K | node (f : Fam K (fun _ => K))`, where `Fam.{u} (α : Type u)
/// (β : α → Type u)` has `Fam.mk : (a : α) → β a → Fam α β`. The auxiliary
/// constructor's second field is `(fun _ => K) a`, a head redex that the pin
/// recognizes as recursive only after whnf. Its binder keeps the written type;
/// its induction hypothesis reads the reduced one.
fn f4() -> (ConstantEnvironment, Vec<ConstantEntry>) {
    let zero = || Level::zero();
    let alpha = local("fam.alpha", ty(param("u")));
    let beta = local(
        "fam.beta",
        pi(&[&local("fam.x", alpha.e())], ty(param("u"))),
    );
    let fa = local("fam.a", alpha.e());
    let fb = local("fam.b", app(beta.e(), [fa.e()]));
    let env = environment(vec![
        inductive(
            "Fam",
            &["u"],
            pi(&[&alpha, &beta], ty(param("u"))),
            2,
            &["Fam"],
            &["Fam.mk"],
            0,
            false,
        ),
        constructor(
            "Fam.mk",
            &["u"],
            pi(
                &[&alpha, &beta, &fa, &fb],
                app(c("Fam", vec![param("u")]), [alpha.e(), beta.e()]),
            ),
            "Fam",
            0,
            2,
            2,
        ),
    ]);
    let k = c("K", vec![]);
    let family = Expr::lam(name("x"), k.clone(), k.clone(), BinderInfo::Default);
    let fam_k = app(c("Fam", vec![zero()]), [k.clone(), family.clone()]);
    let w = param("w");
    let m1 = local("m1", pi(&[&local("t1", k.clone())], Expr::sort(w.clone())));
    let m2 = local(
        "m2",
        pi(&[&local("t2", fam_k.clone())], Expr::sort(w.clone())),
    );
    let child = local("child", fam_k.clone());
    let a = local("a", k.clone());
    let b = local("b", app(family.clone(), [a.e()]));
    let ih_child = local("ih_child", app(m2.e(), [child.e()]));
    let ih_a = local("ih_a", app(m1.e(), [a.e()]));
    let ih_b = local("ih_b", app(m1.e(), [b.e()]));
    let node = local(
        "node",
        pi(
            &[&child, &ih_child],
            app(m1.e(), [app(c("K.node", vec![]), [child.e()])]),
        ),
    );
    let mk = local(
        "mk",
        pi(
            &[&a, &b, &ih_a, &ih_b],
            app(
                m2.e(),
                [app(
                    c("Fam.mk", vec![zero()]),
                    [k.clone(), family.clone(), a.e(), b.e()],
                )],
            ),
        ),
    );
    let prefix = [&m1, &m2, &node, &mk];
    let head = |n: &str| app(c(n, vec![w.clone()]), prefix.iter().map(|l| l.e()));
    let major_k = local("major_k", k.clone());
    let major_fam = local("major_fam", fam_k.clone());
    let rows = vec![
        inductive("K", &[], ty(zero()), 0, &["K"], &["K.node"], 1, true),
        constructor("K.node", &[], pi(&[&child], k.clone()), "K", 0, 0, 1),
        recursor(
            "K.rec",
            &["w"],
            pi(&joined(&prefix, &[&major_k]), app(m1.e(), [major_k.e()])),
            &["K"],
            0,
            2,
            2,
            vec![(
                "K.node",
                1,
                lam(
                    &joined(&prefix, &[&child]),
                    app(node.e(), [child.e(), app(head("K.rec_1"), [child.e()])]),
                ),
            )],
        ),
        recursor(
            "K.rec_1",
            &["w"],
            pi(
                &joined(&prefix, &[&major_fam]),
                app(m2.e(), [major_fam.e()]),
            ),
            &["K"],
            0,
            2,
            2,
            vec![(
                "Fam.mk",
                2,
                lam(
                    &joined(&prefix, &[&a, &b]),
                    app(
                        mk.e(),
                        [
                            a.e(),
                            b.e(),
                            app(head("K.rec"), [a.e()]),
                            app(head("K.rec"), [b.e()]),
                        ],
                    ),
                ),
            )],
        ),
    ];
    (env, rows)
}

fn joined<'a>(prefix: &[&'a Local], extra: &[&'a Local]) -> Vec<&'a Local> {
    prefix.iter().chain(extra).copied().collect()
}

fn admitted(verdict: &InductiveVerdict) -> bool {
    matches!(verdict, InductiveVerdict::Admitted(_))
}

#[test]
fn a_nested_family_with_parameters_is_admitted_as_its_auxiliary_mutual_block() {
    let (env, rows) = f1("");
    let verdict = verdict(&env, &rows);
    assert!(admitted(&verdict), "{verdict:?}");
}

#[test]
fn nested_levels_are_instantiated_as_the_pins_mk_max_writes_them() {
    let (env, rows) = f2();
    let verdict = verdict(&env, &rows);
    assert!(admitted(&verdict), "{verdict:?}");
}

#[test]
fn an_auxiliary_family_in_an_equivalent_universe_joins_the_block() {
    let (env, rows) = f3();
    let verdict = verdict(&env, &rows);
    assert!(admitted(&verdict), "{verdict:?}");
}

#[test]
fn a_wrong_nested_recursor_rule_is_rejected() {
    let (env, rows) = f1("swapped_ih");
    let verdict = verdict(&env, &rows);
    assert!(
        matches!(
            verdict,
            InductiveVerdict::Rejected(InductiveRejection::RecursorShape { .. })
        ),
        "{verdict:?}"
    );
}

#[test]
fn a_declared_term_naming_a_private_auxiliary_is_refused() {
    let (env, rows) = f1("private_name");
    let verdict = verdict(&env, &rows);
    assert!(
        matches!(
            verdict,
            InductiveVerdict::Rejected(InductiveRejection::ConstructorShape { .. })
        ),
        "{verdict:?}"
    );
}

#[test]
fn a_declared_nested_count_must_match_the_translation() {
    let (env, rows) = f1("nested_count");
    let verdict = verdict(&env, &rows);
    assert!(
        matches!(
            verdict,
            InductiveVerdict::Rejected(InductiveRejection::ConstructorShape { .. })
        ),
        "{verdict:?}"
    );
}

#[test]
fn a_field_whose_type_reduces_to_the_family_is_recursive() {
    let (env, rows) = f4();
    let verdict = verdict(&env, &rows);
    assert!(admitted(&verdict), "{verdict:?}");
}
