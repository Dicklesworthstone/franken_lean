//! Fixed arithmetic dependencies of the native UInt32 logical bound.
//!
//! These are pin metadata comparisons, never declarations installed or bodies
//! executed as a fallback. Binder labels and transparent metadata are omitted
//! exactly as in Comparison. Nat.pow's full existing model supplies OfNat and
//! the underlying arithmetic; these dictionaries connect that model to BitVec.

use super::*;

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}
fn constant(label: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(name(label), levels)
}
fn b(index: u32) -> Expr {
    Expr::bvar(index).expect("fixed word-bound binder")
}
fn pi(domain: Expr, body: Expr, info: BinderInfo) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, info)
}
fn lam(domain: Expr, body: Expr, info: BinderInfo) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, info)
}
fn base(label: &str, levels: Vec<&str>, type_: Expr) -> ConstantVal {
    ConstantVal {
        name: name(label),
        level_params: levels.into_iter().map(name).collect(),
        type_,
    }
}
fn definition(
    label: &str,
    levels: Vec<&str>,
    hints: ReducibilityHints,
    type_: Expr,
    value: Expr,
    all: Vec<Name>,
) -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: base(label, levels, type_),
        value,
        hints,
        safety: DefinitionSafety::Safe,
        all,
    })
}
fn inductive(
    label: &str,
    levels: Vec<&str>,
    metadata: (u32, u32, u32, bool, bool, bool),
    type_: Expr,
    all: Vec<Name>,
    ctors: Vec<Name>,
) -> ConstantInfo {
    let (num_params, num_indices, num_nested, is_rec, is_unsafe, is_reflexive) = metadata;
    ConstantInfo::Induct(InductiveVal {
        base: base(label, levels, type_),
        num_params,
        num_indices,
        num_nested,
        is_rec,
        is_unsafe,
        is_reflexive,
        all,
        ctors,
    })
}
fn constructor(
    label: &str,
    levels: Vec<&str>,
    metadata: (&str, u32, u32, u32, bool),
    type_: Expr,
) -> ConstantInfo {
    let (family, cidx, num_params, num_fields, is_unsafe) = metadata;
    ConstantInfo::Ctor(ConstructorVal {
        base: base(label, levels, type_),
        induct: name(family),
        cidx,
        num_params,
        num_fields,
        is_unsafe,
    })
}

pub(super) fn declarations() -> Vec<ConstantInfo> {
    vec![
        inductive(
            "NatPow",
            vec!["u"],
            (1, 0, 0, false, false, false),
            pi(
                Expr::sort(Level::succ(Level::param(name("u"))).expect("fixed word-bound level")),
                Expr::sort(Level::succ(Level::param(name("u"))).expect("fixed word-bound level")),
                BinderInfo::Default,
            ),
            vec![name("NatPow")],
            vec![name("NatPow.mk")],
        ),
        constructor(
            "NatPow.mk",
            vec!["u"],
            ("NatPow", 0, 1, 1, false),
            pi(
                Expr::sort(Level::succ(Level::param(name("u"))).expect("fixed word-bound level")),
                pi(
                    pi(
                        b(0),
                        pi(constant("Nat", vec![]), b(2), BinderInfo::Default),
                        BinderInfo::Default,
                    ),
                    Expr::app(constant("NatPow", vec![Level::param(name("u"))]), b(1)),
                    BinderInfo::Default,
                ),
                BinderInfo::Implicit,
            ),
        ),
        definition(
            "NatPow.pow",
            vec!["u"],
            ReducibilityHints::Abbrev,
            pi(
                Expr::sort(Level::succ(Level::param(name("u"))).expect("fixed word-bound level")),
                pi(
                    Expr::app(constant("NatPow", vec![Level::param(name("u"))]), b(0)),
                    pi(
                        b(1),
                        pi(constant("Nat", vec![]), b(3), BinderInfo::Default),
                        BinderInfo::Default,
                    ),
                    BinderInfo::InstImplicit,
                ),
                BinderInfo::Implicit,
            ),
            lam(
                Expr::sort(Level::succ(Level::param(name("u"))).expect("fixed word-bound level")),
                lam(
                    Expr::app(constant("NatPow", vec![Level::param(name("u"))]), b(0)),
                    Expr::proj(name("NatPow"), 0, b(0)),
                    BinderInfo::InstImplicit,
                ),
                BinderInfo::Default,
            ),
            vec![name("NatPow.pow")],
        ),
        inductive(
            "Pow",
            vec!["u", "v"],
            (2, 0, 0, false, false, false),
            pi(
                Expr::sort(Level::succ(Level::param(name("u"))).expect("fixed word-bound level")),
                pi(
                    Expr::sort(
                        Level::succ(Level::param(name("v"))).expect("fixed word-bound level"),
                    ),
                    Expr::sort(
                        Level::max(
                            Level::succ(Level::param(name("u"))).expect("fixed word-bound level"),
                            Level::succ(Level::param(name("v"))).expect("fixed word-bound level"),
                        )
                        .expect("fixed word-bound level"),
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            vec![name("Pow")],
            vec![name("Pow.mk")],
        ),
        constructor(
            "Pow.mk",
            vec!["u", "v"],
            ("Pow", 0, 2, 1, false),
            pi(
                Expr::sort(Level::succ(Level::param(name("u"))).expect("fixed word-bound level")),
                pi(
                    Expr::sort(
                        Level::succ(Level::param(name("v"))).expect("fixed word-bound level"),
                    ),
                    pi(
                        pi(
                            b(1),
                            pi(b(1), b(3), BinderInfo::Default),
                            BinderInfo::Default,
                        ),
                        Expr::app(
                            Expr::app(
                                constant(
                                    "Pow",
                                    vec![Level::param(name("u")), Level::param(name("v"))],
                                ),
                                b(2),
                            ),
                            b(1),
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Implicit,
                ),
                BinderInfo::Implicit,
            ),
        ),
        definition(
            "Pow.pow",
            vec!["u", "v"],
            ReducibilityHints::Abbrev,
            pi(
                Expr::sort(Level::succ(Level::param(name("u"))).expect("fixed word-bound level")),
                pi(
                    Expr::sort(
                        Level::succ(Level::param(name("v"))).expect("fixed word-bound level"),
                    ),
                    pi(
                        Expr::app(
                            Expr::app(
                                constant(
                                    "Pow",
                                    vec![Level::param(name("u")), Level::param(name("v"))],
                                ),
                                b(1),
                            ),
                            b(0),
                        ),
                        pi(
                            b(2),
                            pi(b(2), b(4), BinderInfo::Default),
                            BinderInfo::Default,
                        ),
                        BinderInfo::InstImplicit,
                    ),
                    BinderInfo::Implicit,
                ),
                BinderInfo::Implicit,
            ),
            lam(
                Expr::sort(Level::succ(Level::param(name("u"))).expect("fixed word-bound level")),
                lam(
                    Expr::sort(
                        Level::succ(Level::param(name("v"))).expect("fixed word-bound level"),
                    ),
                    lam(
                        Expr::app(
                            Expr::app(
                                constant(
                                    "Pow",
                                    vec![Level::param(name("u")), Level::param(name("v"))],
                                ),
                                b(1),
                            ),
                            b(0),
                        ),
                        Expr::proj(name("Pow"), 0, b(0)),
                        BinderInfo::InstImplicit,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            vec![name("Pow.pow")],
        ),
        inductive(
            "HPow",
            vec!["u", "v", "w"],
            (3, 0, 0, false, false, false),
            pi(
                Expr::sort(Level::succ(Level::param(name("u"))).expect("fixed word-bound level")),
                pi(
                    Expr::sort(
                        Level::succ(Level::param(name("v"))).expect("fixed word-bound level"),
                    ),
                    pi(
                        Expr::app(
                            constant(
                                "outParam",
                                vec![
                                    Level::succ(
                                        Level::succ(Level::param(name("w")))
                                            .expect("fixed word-bound level"),
                                    )
                                    .expect("fixed word-bound level"),
                                ],
                            ),
                            Expr::sort(
                                Level::succ(Level::param(name("w")))
                                    .expect("fixed word-bound level"),
                            ),
                        ),
                        Expr::sort(
                            Level::max(
                                Level::max(
                                    Level::succ(Level::param(name("u")))
                                        .expect("fixed word-bound level"),
                                    Level::succ(Level::param(name("v")))
                                        .expect("fixed word-bound level"),
                                )
                                .expect("fixed word-bound level"),
                                Level::succ(Level::param(name("w")))
                                    .expect("fixed word-bound level"),
                            )
                            .expect("fixed word-bound level"),
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            vec![name("HPow")],
            vec![name("HPow.mk")],
        ),
        constructor(
            "HPow.mk",
            vec!["u", "v", "w"],
            ("HPow", 0, 3, 1, false),
            pi(
                Expr::sort(Level::succ(Level::param(name("u"))).expect("fixed word-bound level")),
                pi(
                    Expr::sort(
                        Level::succ(Level::param(name("v"))).expect("fixed word-bound level"),
                    ),
                    pi(
                        Expr::app(
                            constant(
                                "outParam",
                                vec![
                                    Level::succ(
                                        Level::succ(Level::param(name("w")))
                                            .expect("fixed word-bound level"),
                                    )
                                    .expect("fixed word-bound level"),
                                ],
                            ),
                            Expr::sort(
                                Level::succ(Level::param(name("w")))
                                    .expect("fixed word-bound level"),
                            ),
                        ),
                        pi(
                            pi(
                                b(2),
                                pi(b(2), b(2), BinderInfo::Default),
                                BinderInfo::Default,
                            ),
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        constant(
                                            "HPow",
                                            vec![
                                                Level::param(name("u")),
                                                Level::param(name("v")),
                                                Level::param(name("w")),
                                            ],
                                        ),
                                        b(3),
                                    ),
                                    b(2),
                                ),
                                b(1),
                            ),
                            BinderInfo::Default,
                        ),
                        BinderInfo::Implicit,
                    ),
                    BinderInfo::Implicit,
                ),
                BinderInfo::Implicit,
            ),
        ),
        definition(
            "HPow.hPow",
            vec!["u", "v", "w"],
            ReducibilityHints::Abbrev,
            pi(
                Expr::sort(Level::succ(Level::param(name("u"))).expect("fixed word-bound level")),
                pi(
                    Expr::sort(
                        Level::succ(Level::param(name("v"))).expect("fixed word-bound level"),
                    ),
                    pi(
                        Expr::app(
                            constant(
                                "outParam",
                                vec![
                                    Level::succ(
                                        Level::succ(Level::param(name("w")))
                                            .expect("fixed word-bound level"),
                                    )
                                    .expect("fixed word-bound level"),
                                ],
                            ),
                            Expr::sort(
                                Level::succ(Level::param(name("w")))
                                    .expect("fixed word-bound level"),
                            ),
                        ),
                        pi(
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        constant(
                                            "HPow",
                                            vec![
                                                Level::param(name("u")),
                                                Level::param(name("v")),
                                                Level::param(name("w")),
                                            ],
                                        ),
                                        b(2),
                                    ),
                                    b(1),
                                ),
                                b(0),
                            ),
                            pi(
                                b(3),
                                pi(b(3), b(3), BinderInfo::Default),
                                BinderInfo::Default,
                            ),
                            BinderInfo::InstImplicit,
                        ),
                        BinderInfo::Implicit,
                    ),
                    BinderInfo::Implicit,
                ),
                BinderInfo::Implicit,
            ),
            lam(
                Expr::sort(Level::succ(Level::param(name("u"))).expect("fixed word-bound level")),
                lam(
                    Expr::sort(
                        Level::succ(Level::param(name("v"))).expect("fixed word-bound level"),
                    ),
                    lam(
                        Expr::app(
                            constant(
                                "outParam",
                                vec![
                                    Level::succ(
                                        Level::succ(Level::param(name("w")))
                                            .expect("fixed word-bound level"),
                                    )
                                    .expect("fixed word-bound level"),
                                ],
                            ),
                            Expr::sort(
                                Level::succ(Level::param(name("w")))
                                    .expect("fixed word-bound level"),
                            ),
                        ),
                        lam(
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        constant(
                                            "HPow",
                                            vec![
                                                Level::param(name("u")),
                                                Level::param(name("v")),
                                                Level::param(name("w")),
                                            ],
                                        ),
                                        b(2),
                                    ),
                                    b(1),
                                ),
                                b(0),
                            ),
                            Expr::proj(name("HPow"), 0, b(0)),
                            BinderInfo::InstImplicit,
                        ),
                        BinderInfo::Implicit,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            vec![name("HPow.hPow")],
        ),
        definition(
            "instNatPowNat",
            vec![],
            ReducibilityHints::Regular(4),
            Expr::app(
                constant("NatPow", vec![Level::zero()]),
                constant("Nat", vec![]),
            ),
            Expr::app(
                Expr::app(
                    constant("NatPow.mk", vec![Level::zero()]),
                    constant("Nat", vec![]),
                ),
                constant("Nat.pow", vec![]),
            ),
            vec![name("instNatPowNat")],
        ),
        definition(
            "instPowNat",
            vec!["u_1"],
            ReducibilityHints::Regular(1),
            pi(
                Expr::sort(Level::succ(Level::param(name("u_1"))).expect("fixed word-bound level")),
                pi(
                    Expr::app(constant("NatPow", vec![Level::param(name("u_1"))]), b(0)),
                    Expr::app(
                        Expr::app(
                            constant("Pow", vec![Level::param(name("u_1")), Level::zero()]),
                            b(1),
                        ),
                        constant("Nat", vec![]),
                    ),
                    BinderInfo::InstImplicit,
                ),
                BinderInfo::Implicit,
            ),
            lam(
                Expr::sort(Level::succ(Level::param(name("u_1"))).expect("fixed word-bound level")),
                lam(
                    Expr::app(constant("NatPow", vec![Level::param(name("u_1"))]), b(0)),
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                constant("Pow.mk", vec![Level::param(name("u_1")), Level::zero()]),
                                b(1),
                            ),
                            constant("Nat", vec![]),
                        ),
                        lam(
                            b(1),
                            lam(
                                constant("Nat", vec![]),
                                Expr::app(
                                    Expr::app(
                                        Expr::app(
                                            Expr::app(
                                                constant(
                                                    "NatPow.pow",
                                                    vec![Level::param(name("u_1"))],
                                                ),
                                                b(3),
                                            ),
                                            b(2),
                                        ),
                                        b(1),
                                    ),
                                    b(0),
                                ),
                                BinderInfo::Default,
                            ),
                            BinderInfo::Default,
                        ),
                    ),
                    BinderInfo::InstImplicit,
                ),
                BinderInfo::Implicit,
            ),
            vec![name("instPowNat")],
        ),
        definition(
            "instHPow",
            vec!["u_1", "u_2"],
            ReducibilityHints::Regular(1),
            pi(
                Expr::sort(Level::succ(Level::param(name("u_1"))).expect("fixed word-bound level")),
                pi(
                    Expr::sort(
                        Level::succ(Level::param(name("u_2"))).expect("fixed word-bound level"),
                    ),
                    pi(
                        Expr::app(
                            Expr::app(
                                constant(
                                    "Pow",
                                    vec![Level::param(name("u_1")), Level::param(name("u_2"))],
                                ),
                                b(1),
                            ),
                            b(0),
                        ),
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    constant(
                                        "HPow",
                                        vec![
                                            Level::param(name("u_1")),
                                            Level::param(name("u_2")),
                                            Level::param(name("u_1")),
                                        ],
                                    ),
                                    b(2),
                                ),
                                b(1),
                            ),
                            b(2),
                        ),
                        BinderInfo::InstImplicit,
                    ),
                    BinderInfo::Implicit,
                ),
                BinderInfo::Implicit,
            ),
            lam(
                Expr::sort(Level::succ(Level::param(name("u_1"))).expect("fixed word-bound level")),
                lam(
                    Expr::sort(
                        Level::succ(Level::param(name("u_2"))).expect("fixed word-bound level"),
                    ),
                    lam(
                        Expr::app(
                            Expr::app(
                                constant(
                                    "Pow",
                                    vec![Level::param(name("u_1")), Level::param(name("u_2"))],
                                ),
                                b(1),
                            ),
                            b(0),
                        ),
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        constant(
                                            "HPow.mk",
                                            vec![
                                                Level::param(name("u_1")),
                                                Level::param(name("u_2")),
                                                Level::param(name("u_1")),
                                            ],
                                        ),
                                        b(2),
                                    ),
                                    b(1),
                                ),
                                b(2),
                            ),
                            lam(
                                b(2),
                                lam(
                                    b(2),
                                    Expr::app(
                                        Expr::app(
                                            Expr::app(
                                                Expr::app(
                                                    Expr::app(
                                                        constant(
                                                            "Pow.pow",
                                                            vec![
                                                                Level::param(name("u_1")),
                                                                Level::param(name("u_2")),
                                                            ],
                                                        ),
                                                        b(4),
                                                    ),
                                                    b(3),
                                                ),
                                                b(2),
                                            ),
                                            b(1),
                                        ),
                                        b(0),
                                    ),
                                    BinderInfo::Default,
                                ),
                                BinderInfo::Default,
                            ),
                        ),
                        BinderInfo::InstImplicit,
                    ),
                    BinderInfo::Implicit,
                ),
                BinderInfo::Implicit,
            ),
            vec![name("instHPow")],
        ),
        inductive(
            "LT",
            vec!["u"],
            (1, 0, 0, false, false, false),
            pi(
                Expr::sort(Level::succ(Level::param(name("u"))).expect("fixed word-bound level")),
                Expr::sort(Level::succ(Level::param(name("u"))).expect("fixed word-bound level")),
                BinderInfo::Default,
            ),
            vec![name("LT")],
            vec![name("LT.mk")],
        ),
        constructor(
            "LT.mk",
            vec!["u"],
            ("LT", 0, 1, 1, false),
            pi(
                Expr::sort(Level::succ(Level::param(name("u"))).expect("fixed word-bound level")),
                pi(
                    pi(
                        b(0),
                        pi(b(1), Expr::sort(Level::zero()), BinderInfo::Default),
                        BinderInfo::Default,
                    ),
                    Expr::app(constant("LT", vec![Level::param(name("u"))]), b(1)),
                    BinderInfo::Default,
                ),
                BinderInfo::Implicit,
            ),
        ),
        definition(
            "LT.lt",
            vec!["u"],
            ReducibilityHints::Abbrev,
            pi(
                Expr::sort(Level::succ(Level::param(name("u"))).expect("fixed word-bound level")),
                pi(
                    Expr::app(constant("LT", vec![Level::param(name("u"))]), b(0)),
                    pi(
                        b(1),
                        pi(b(2), Expr::sort(Level::zero()), BinderInfo::Default),
                        BinderInfo::Default,
                    ),
                    BinderInfo::InstImplicit,
                ),
                BinderInfo::Implicit,
            ),
            lam(
                Expr::sort(Level::succ(Level::param(name("u"))).expect("fixed word-bound level")),
                lam(
                    Expr::app(constant("LT", vec![Level::param(name("u"))]), b(0)),
                    Expr::proj(name("LT"), 0, b(0)),
                    BinderInfo::InstImplicit,
                ),
                BinderInfo::Default,
            ),
            vec![name("LT.lt")],
        ),
        definition(
            "instLTNat",
            vec![],
            ReducibilityHints::Regular(2),
            Expr::app(constant("LT", vec![Level::zero()]), constant("Nat", vec![])),
            Expr::app(
                Expr::app(
                    constant("LT.mk", vec![Level::zero()]),
                    constant("Nat", vec![]),
                ),
                constant("Nat.lt", vec![]),
            ),
            vec![name("instLTNat")],
        ),
        definition(
            "Nat.lt",
            vec![],
            ReducibilityHints::Regular(1),
            pi(
                constant("Nat", vec![]),
                pi(
                    constant("Nat", vec![]),
                    Expr::sort(Level::zero()),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            lam(
                constant("Nat", vec![]),
                lam(
                    constant("Nat", vec![]),
                    Expr::app(
                        Expr::app(
                            constant("Nat.le", vec![]),
                            Expr::app(constant("Nat.succ", vec![]), b(1)),
                        ),
                        b(0),
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            vec![name("Nat.lt")],
        ),
        inductive(
            "Nat.le",
            vec![],
            (1, 1, 0, true, false, false),
            pi(
                constant("Nat", vec![]),
                pi(
                    constant("Nat", vec![]),
                    Expr::sort(Level::zero()),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            vec![name("Nat.le")],
            vec![name("Nat.le.refl"), name("Nat.le.step")],
        ),
        constructor(
            "Nat.le.refl",
            vec![],
            ("Nat.le", 0, 1, 0, false),
            pi(
                constant("Nat", vec![]),
                Expr::app(Expr::app(constant("Nat.le", vec![]), b(0)), b(0)),
                BinderInfo::Implicit,
            ),
        ),
        constructor(
            "Nat.le.step",
            vec![],
            ("Nat.le", 1, 1, 2, false),
            pi(
                constant("Nat", vec![]),
                pi(
                    constant("Nat", vec![]),
                    pi(
                        Expr::app(Expr::app(constant("Nat.le", vec![]), b(1)), b(0)),
                        Expr::app(
                            Expr::app(constant("Nat.le", vec![]), b(2)),
                            Expr::app(constant("Nat.succ", vec![]), b(1)),
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Implicit,
                ),
                BinderInfo::Implicit,
            ),
        ),
    ]
}
