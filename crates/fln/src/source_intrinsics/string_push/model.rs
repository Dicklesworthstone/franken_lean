//! Exact pinned implementation, matcher, character views and Unicode predicate.
//!
//! These fixed terms are comparison data only. They are never declarations to
//! install or an implementation to execute. The matcher includes its complete
//! String eliminator; logical character projections keep the ordinary admitted
//! UInt32/BitVec/Fin object layers and the original proof fields.

use super::*;

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}
fn constant(label: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(name(label), levels)
}
fn b(index: u32) -> Expr {
    Expr::bvar(index).expect("fixed string-push model binder")
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

fn recursor(
    label: &str,
    levels: Vec<&str>,
    metadata: (u32, u32, u32, u32, bool, bool),
    type_: Expr,
    all: Vec<Name>,
    rules: Vec<RecursorRule>,
) -> ConstantInfo {
    let (num_params, num_indices, num_motives, num_minors, k, is_unsafe) = metadata;
    ConstantInfo::Rec(RecursorVal {
        base: base(label, levels, type_),
        all,
        num_params,
        num_indices,
        num_motives,
        num_minors,
        rules,
        k,
        is_unsafe,
    })
}

pub(super) fn declarations() -> Vec<ConstantInfo> {
    vec![
        definition(
            "String.push",
            vec![],
            ReducibilityHints::Regular(14),
            pi(
                constant("String", vec![]),
                pi(
                    constant("Char", vec![]),
                    constant("String", vec![]),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            lam(
                constant("String", vec![]),
                lam(
                    constant("Char", vec![]),
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    constant(
                                        "String.push.match_1",
                                        vec![
                                            Level::succ(Level::zero())
                                                .expect("fixed string-push model level"),
                                        ],
                                    ),
                                    lam(
                                        constant("String", vec![]),
                                        lam(
                                            constant("Char", vec![]),
                                            constant("String", vec![]),
                                            BinderInfo::Default,
                                        ),
                                        BinderInfo::Default,
                                    ),
                                ),
                                b(1),
                            ),
                            b(0),
                        ),
                        lam(
                            constant("ByteArray", vec![]),
                            lam(
                                Expr::app(constant("ByteArray.IsValidUTF8", vec![]), b(0)),
                                lam(
                                    constant("Char", vec![]),
                                    Expr::app(
                                        Expr::app(
                                            constant("String.ofByteArray", vec![]),
                                            Expr::app(
                                                Expr::app(
                                                    constant("ByteArray.append", vec![]),
                                                    b(2),
                                                ),
                                                Expr::app(
                                                    constant("List.utf8Encode", vec![]),
                                                    Expr::app(
                                                        Expr::app(
                                                            Expr::app(
                                                                constant(
                                                                    "List.cons",
                                                                    vec![Level::zero()],
                                                                ),
                                                                constant("Char", vec![]),
                                                            ),
                                                            b(0),
                                                        ),
                                                        Expr::app(
                                                            constant(
                                                                "List.nil",
                                                                vec![Level::zero()],
                                                            ),
                                                            constant("Char", vec![]),
                                                        ),
                                                    ),
                                                ),
                                            ),
                                        ),
                                        Expr::app(
                                            Expr::app(
                                                Expr::app(
                                                    constant("String.push._proof_5", vec![]),
                                                    b(2),
                                                ),
                                                b(1),
                                            ),
                                            b(0),
                                        ),
                                    ),
                                    BinderInfo::Default,
                                ),
                                BinderInfo::Default,
                            ),
                            BinderInfo::Default,
                        ),
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            vec![name("String.push")],
        ),
        definition(
            "String.push.match_1",
            vec!["u_1"],
            ReducibilityHints::Abbrev,
            pi(
                pi(
                    constant("String", vec![]),
                    pi(
                        constant("Char", vec![]),
                        Expr::sort(Level::param(name("u_1"))),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                pi(
                    constant("String", vec![]),
                    pi(
                        constant("Char", vec![]),
                        pi(
                            pi(
                                constant("ByteArray", vec![]),
                                pi(
                                    Expr::app(constant("ByteArray.IsValidUTF8", vec![]), b(0)),
                                    pi(
                                        constant("Char", vec![]),
                                        Expr::app(
                                            Expr::app(
                                                b(5),
                                                Expr::app(
                                                    Expr::app(
                                                        constant("String.ofByteArray", vec![]),
                                                        b(2),
                                                    ),
                                                    b(1),
                                                ),
                                            ),
                                            b(0),
                                        ),
                                        BinderInfo::Default,
                                    ),
                                    BinderInfo::Default,
                                ),
                                BinderInfo::Default,
                            ),
                            Expr::app(Expr::app(b(3), b(2)), b(1)),
                            BinderInfo::Default,
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            lam(
                pi(
                    constant("String", vec![]),
                    pi(
                        constant("Char", vec![]),
                        Expr::sort(Level::param(name("u_1"))),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                lam(
                    constant("String", vec![]),
                    lam(
                        constant("Char", vec![]),
                        lam(
                            pi(
                                constant("ByteArray", vec![]),
                                pi(
                                    Expr::app(constant("ByteArray.IsValidUTF8", vec![]), b(0)),
                                    pi(
                                        constant("Char", vec![]),
                                        Expr::app(
                                            Expr::app(
                                                b(5),
                                                Expr::app(
                                                    Expr::app(
                                                        constant("String.ofByteArray", vec![]),
                                                        b(2),
                                                    ),
                                                    b(1),
                                                ),
                                            ),
                                            b(0),
                                        ),
                                        BinderInfo::Default,
                                    ),
                                    BinderInfo::Default,
                                ),
                                BinderInfo::Default,
                            ),
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        constant("String.casesOn", vec![Level::param(name("u_1"))]),
                                        lam(
                                            constant("String", vec![]),
                                            Expr::app(Expr::app(b(4), b(0)), b(2)),
                                            BinderInfo::Default,
                                        ),
                                    ),
                                    b(2),
                                ),
                                lam(
                                    constant("ByteArray", vec![]),
                                    lam(
                                        Expr::app(constant("ByteArray.IsValidUTF8", vec![]), b(0)),
                                        Expr::app(Expr::app(Expr::app(b(2), b(1)), b(0)), b(3)),
                                        BinderInfo::Default,
                                    ),
                                    BinderInfo::Default,
                                ),
                            ),
                            BinderInfo::Default,
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            vec![name("String.push.match_1")],
        ),
        inductive(
            "BitVec",
            vec![],
            (1, 0, 0, false, false, false),
            pi(
                constant("Nat", vec![]),
                Expr::sort(Level::succ(Level::zero()).expect("fixed string-push model level")),
                BinderInfo::Default,
            ),
            vec![name("BitVec")],
            vec![name("BitVec.ofFin")],
        ),
        constructor(
            "BitVec.ofFin",
            vec![],
            ("BitVec", 0, 1, 1, false),
            pi(
                constant("Nat", vec![]),
                pi(
                    Expr::app(
                        constant("Fin", vec![]),
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::app(
                                            Expr::app(
                                                constant(
                                                    "HPow.hPow",
                                                    vec![
                                                        Level::zero(),
                                                        Level::zero(),
                                                        Level::zero(),
                                                    ],
                                                ),
                                                constant("Nat", vec![]),
                                            ),
                                            constant("Nat", vec![]),
                                        ),
                                        constant("Nat", vec![]),
                                    ),
                                    Expr::app(
                                        Expr::app(
                                            Expr::app(
                                                constant(
                                                    "instHPow",
                                                    vec![Level::zero(), Level::zero()],
                                                ),
                                                constant("Nat", vec![]),
                                            ),
                                            constant("Nat", vec![]),
                                        ),
                                        Expr::app(
                                            Expr::app(
                                                constant("instPowNat", vec![Level::zero()]),
                                                constant("Nat", vec![]),
                                            ),
                                            constant("instNatPowNat", vec![]),
                                        ),
                                    ),
                                ),
                                Expr::app(
                                    Expr::app(
                                        Expr::app(
                                            constant("OfNat.ofNat", vec![Level::zero()]),
                                            constant("Nat", vec![]),
                                        ),
                                        Expr::lit(Literal::Nat(NatLit::from_u64(2))),
                                    ),
                                    Expr::app(
                                        constant("instOfNatNat", vec![]),
                                        Expr::lit(Literal::Nat(NatLit::from_u64(2))),
                                    ),
                                ),
                            ),
                            b(0),
                        ),
                    ),
                    Expr::app(constant("BitVec", vec![]), b(1)),
                    BinderInfo::Default,
                ),
                BinderInfo::Implicit,
            ),
        ),
        inductive(
            "Fin",
            vec![],
            (1, 0, 0, false, false, false),
            pi(
                constant("Nat", vec![]),
                Expr::sort(Level::succ(Level::zero()).expect("fixed string-push model level")),
                BinderInfo::Default,
            ),
            vec![name("Fin")],
            vec![name("Fin.mk")],
        ),
        constructor(
            "Fin.mk",
            vec![],
            ("Fin", 0, 1, 2, false),
            pi(
                constant("Nat", vec![]),
                pi(
                    constant("Nat", vec![]),
                    pi(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        constant("LT.lt", vec![Level::zero()]),
                                        constant("Nat", vec![]),
                                    ),
                                    constant("instLTNat", vec![]),
                                ),
                                b(0),
                            ),
                            b(1),
                        ),
                        Expr::app(constant("Fin", vec![]), b(2)),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Implicit,
            ),
        ),
        definition(
            "Char.val",
            vec![],
            ReducibilityHints::Abbrev,
            pi(
                constant("Char", vec![]),
                constant("UInt32", vec![]),
                BinderInfo::Default,
            ),
            lam(
                constant("Char", vec![]),
                Expr::proj(name("Char"), 0, b(0)),
                BinderInfo::Default,
            ),
            vec![name("Char.val")],
        ),
        definition(
            "UInt32.toBitVec",
            vec![],
            ReducibilityHints::Abbrev,
            pi(
                constant("UInt32", vec![]),
                Expr::app(
                    constant("BitVec", vec![]),
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                constant("OfNat.ofNat", vec![Level::zero()]),
                                constant("Nat", vec![]),
                            ),
                            Expr::lit(Literal::Nat(NatLit::from_u64(32))),
                        ),
                        Expr::app(
                            constant("instOfNatNat", vec![]),
                            Expr::lit(Literal::Nat(NatLit::from_u64(32))),
                        ),
                    ),
                ),
                BinderInfo::Default,
            ),
            lam(
                constant("UInt32", vec![]),
                Expr::proj(name("UInt32"), 0, b(0)),
                BinderInfo::Default,
            ),
            vec![name("UInt32.toBitVec")],
        ),
        definition(
            "BitVec.toFin",
            vec![],
            ReducibilityHints::Abbrev,
            pi(
                constant("Nat", vec![]),
                pi(
                    Expr::app(constant("BitVec", vec![]), b(0)),
                    Expr::app(
                        constant("Fin", vec![]),
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::app(
                                            Expr::app(
                                                constant(
                                                    "HPow.hPow",
                                                    vec![
                                                        Level::zero(),
                                                        Level::zero(),
                                                        Level::zero(),
                                                    ],
                                                ),
                                                constant("Nat", vec![]),
                                            ),
                                            constant("Nat", vec![]),
                                        ),
                                        constant("Nat", vec![]),
                                    ),
                                    Expr::app(
                                        Expr::app(
                                            Expr::app(
                                                constant(
                                                    "instHPow",
                                                    vec![Level::zero(), Level::zero()],
                                                ),
                                                constant("Nat", vec![]),
                                            ),
                                            constant("Nat", vec![]),
                                        ),
                                        Expr::app(
                                            Expr::app(
                                                constant("instPowNat", vec![Level::zero()]),
                                                constant("Nat", vec![]),
                                            ),
                                            constant("instNatPowNat", vec![]),
                                        ),
                                    ),
                                ),
                                Expr::app(
                                    Expr::app(
                                        Expr::app(
                                            constant("OfNat.ofNat", vec![Level::zero()]),
                                            constant("Nat", vec![]),
                                        ),
                                        Expr::lit(Literal::Nat(NatLit::from_u64(2))),
                                    ),
                                    Expr::app(
                                        constant("instOfNatNat", vec![]),
                                        Expr::lit(Literal::Nat(NatLit::from_u64(2))),
                                    ),
                                ),
                            ),
                            b(1),
                        ),
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Implicit,
            ),
            lam(
                constant("Nat", vec![]),
                lam(
                    Expr::app(constant("BitVec", vec![]), b(0)),
                    Expr::proj(name("BitVec"), 0, b(0)),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            vec![name("BitVec.toFin")],
        ),
        definition(
            "Fin.val",
            vec![],
            ReducibilityHints::Abbrev,
            pi(
                constant("Nat", vec![]),
                pi(
                    Expr::app(constant("Fin", vec![]), b(0)),
                    constant("Nat", vec![]),
                    BinderInfo::Default,
                ),
                BinderInfo::Implicit,
            ),
            lam(
                constant("Nat", vec![]),
                lam(
                    Expr::app(constant("Fin", vec![]), b(0)),
                    Expr::proj(name("Fin"), 0, b(0)),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            vec![name("Fin.val")],
        ),
        definition(
            "UInt32.toNat",
            vec![],
            ReducibilityHints::Regular(6),
            pi(
                constant("UInt32", vec![]),
                constant("Nat", vec![]),
                BinderInfo::Default,
            ),
            lam(
                constant("UInt32", vec![]),
                Expr::app(
                    Expr::app(
                        constant("BitVec.toNat", vec![]),
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    constant("OfNat.ofNat", vec![Level::zero()]),
                                    constant("Nat", vec![]),
                                ),
                                Expr::lit(Literal::Nat(NatLit::from_u64(32))),
                            ),
                            Expr::app(
                                constant("instOfNatNat", vec![]),
                                Expr::lit(Literal::Nat(NatLit::from_u64(32))),
                            ),
                        ),
                    ),
                    Expr::app(constant("UInt32.toBitVec", vec![]), b(0)),
                ),
                BinderInfo::Default,
            ),
            vec![name("UInt32.toNat")],
        ),
        definition(
            "BitVec.toNat",
            vec![],
            ReducibilityHints::Regular(5),
            pi(
                constant("Nat", vec![]),
                pi(
                    Expr::app(constant("BitVec", vec![]), b(0)),
                    constant("Nat", vec![]),
                    BinderInfo::Default,
                ),
                BinderInfo::Implicit,
            ),
            lam(
                constant("Nat", vec![]),
                lam(
                    Expr::app(constant("BitVec", vec![]), b(0)),
                    Expr::app(
                        Expr::app(
                            constant("Fin.val", vec![]),
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::app(
                                            Expr::app(
                                                Expr::app(
                                                    constant(
                                                        "HPow.hPow",
                                                        vec![
                                                            Level::zero(),
                                                            Level::zero(),
                                                            Level::zero(),
                                                        ],
                                                    ),
                                                    constant("Nat", vec![]),
                                                ),
                                                constant("Nat", vec![]),
                                            ),
                                            constant("Nat", vec![]),
                                        ),
                                        Expr::app(
                                            Expr::app(
                                                Expr::app(
                                                    constant(
                                                        "instHPow",
                                                        vec![Level::zero(), Level::zero()],
                                                    ),
                                                    constant("Nat", vec![]),
                                                ),
                                                constant("Nat", vec![]),
                                            ),
                                            Expr::app(
                                                Expr::app(
                                                    constant("instPowNat", vec![Level::zero()]),
                                                    constant("Nat", vec![]),
                                                ),
                                                constant("instNatPowNat", vec![]),
                                            ),
                                        ),
                                    ),
                                    Expr::app(
                                        Expr::app(
                                            Expr::app(
                                                constant("OfNat.ofNat", vec![Level::zero()]),
                                                constant("Nat", vec![]),
                                            ),
                                            Expr::lit(Literal::Nat(NatLit::from_u64(2))),
                                        ),
                                        Expr::app(
                                            constant("instOfNatNat", vec![]),
                                            Expr::lit(Literal::Nat(NatLit::from_u64(2))),
                                        ),
                                    ),
                                ),
                                b(1),
                            ),
                        ),
                        Expr::app(Expr::app(constant("BitVec.toFin", vec![]), b(1)), b(0)),
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Implicit,
            ),
            vec![name("BitVec.toNat")],
        ),
        definition(
            "Nat.isValidChar",
            vec![],
            ReducibilityHints::Abbrev,
            pi(
                constant("Nat", vec![]),
                Expr::sort(Level::zero()),
                BinderInfo::Default,
            ),
            lam(
                constant("Nat", vec![]),
                Expr::app(
                    Expr::app(
                        constant("Or", vec![]),
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        constant("LT.lt", vec![Level::zero()]),
                                        constant("Nat", vec![]),
                                    ),
                                    constant("instLTNat", vec![]),
                                ),
                                b(0),
                            ),
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        constant("OfNat.ofNat", vec![Level::zero()]),
                                        constant("Nat", vec![]),
                                    ),
                                    Expr::lit(Literal::Nat(NatLit::from_u64(55296))),
                                ),
                                Expr::app(
                                    constant("instOfNatNat", vec![]),
                                    Expr::lit(Literal::Nat(NatLit::from_u64(55296))),
                                ),
                            ),
                        ),
                    ),
                    Expr::app(
                        Expr::app(
                            constant("And", vec![]),
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::app(
                                            constant("LT.lt", vec![Level::zero()]),
                                            constant("Nat", vec![]),
                                        ),
                                        constant("instLTNat", vec![]),
                                    ),
                                    Expr::app(
                                        Expr::app(
                                            Expr::app(
                                                constant("OfNat.ofNat", vec![Level::zero()]),
                                                constant("Nat", vec![]),
                                            ),
                                            Expr::lit(Literal::Nat(NatLit::from_u64(57343))),
                                        ),
                                        Expr::app(
                                            constant("instOfNatNat", vec![]),
                                            Expr::lit(Literal::Nat(NatLit::from_u64(57343))),
                                        ),
                                    ),
                                ),
                                b(0),
                            ),
                        ),
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        constant("LT.lt", vec![Level::zero()]),
                                        constant("Nat", vec![]),
                                    ),
                                    constant("instLTNat", vec![]),
                                ),
                                b(0),
                            ),
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        constant("OfNat.ofNat", vec![Level::zero()]),
                                        constant("Nat", vec![]),
                                    ),
                                    Expr::lit(Literal::Nat(NatLit::from_u64(1114112))),
                                ),
                                Expr::app(
                                    constant("instOfNatNat", vec![]),
                                    Expr::lit(Literal::Nat(NatLit::from_u64(1114112))),
                                ),
                            ),
                        ),
                    ),
                ),
                BinderInfo::Default,
            ),
            vec![name("Nat.isValidChar")],
        ),
        definition(
            "UInt32.isValidChar",
            vec![],
            ReducibilityHints::Abbrev,
            pi(
                constant("UInt32", vec![]),
                Expr::sort(Level::zero()),
                BinderInfo::Default,
            ),
            lam(
                constant("UInt32", vec![]),
                Expr::app(
                    constant("Nat.isValidChar", vec![]),
                    Expr::app(constant("UInt32.toNat", vec![]), b(0)),
                ),
                BinderInfo::Default,
            ),
            vec![name("UInt32.isValidChar")],
        ),
        inductive(
            "Or",
            vec![],
            (2, 0, 0, false, false, false),
            pi(
                Expr::sort(Level::zero()),
                pi(
                    Expr::sort(Level::zero()),
                    Expr::sort(Level::zero()),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            vec![name("Or")],
            vec![name("Or.inl"), name("Or.inr")],
        ),
        constructor(
            "Or.inl",
            vec![],
            ("Or", 0, 2, 1, false),
            pi(
                Expr::sort(Level::zero()),
                pi(
                    Expr::sort(Level::zero()),
                    pi(
                        b(1),
                        Expr::app(Expr::app(constant("Or", vec![]), b(2)), b(1)),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Implicit,
                ),
                BinderInfo::Implicit,
            ),
        ),
        constructor(
            "Or.inr",
            vec![],
            ("Or", 1, 2, 1, false),
            pi(
                Expr::sort(Level::zero()),
                pi(
                    Expr::sort(Level::zero()),
                    pi(
                        b(0),
                        Expr::app(Expr::app(constant("Or", vec![]), b(2)), b(1)),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Implicit,
                ),
                BinderInfo::Implicit,
            ),
        ),
        inductive(
            "And",
            vec![],
            (2, 0, 0, false, false, false),
            pi(
                Expr::sort(Level::zero()),
                pi(
                    Expr::sort(Level::zero()),
                    Expr::sort(Level::zero()),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            vec![name("And")],
            vec![name("And.intro")],
        ),
        constructor(
            "And.intro",
            vec![],
            ("And", 0, 2, 2, false),
            pi(
                Expr::sort(Level::zero()),
                pi(
                    Expr::sort(Level::zero()),
                    pi(
                        b(1),
                        pi(
                            b(1),
                            Expr::app(Expr::app(constant("And", vec![]), b(3)), b(2)),
                            BinderInfo::Default,
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Implicit,
                ),
                BinderInfo::Implicit,
            ),
        ),
        definition(
            "String.casesOn",
            vec!["u"],
            ReducibilityHints::Abbrev,
            pi(
                pi(
                    constant("String", vec![]),
                    Expr::sort(Level::param(name("u"))),
                    BinderInfo::Default,
                ),
                pi(
                    constant("String", vec![]),
                    pi(
                        pi(
                            constant("ByteArray", vec![]),
                            pi(
                                Expr::app(constant("ByteArray.IsValidUTF8", vec![]), b(0)),
                                Expr::app(
                                    b(3),
                                    Expr::app(
                                        Expr::app(constant("String.ofByteArray", vec![]), b(1)),
                                        b(0),
                                    ),
                                ),
                                BinderInfo::Default,
                            ),
                            BinderInfo::Default,
                        ),
                        Expr::app(b(2), b(1)),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Implicit,
            ),
            lam(
                pi(
                    constant("String", vec![]),
                    Expr::sort(Level::param(name("u"))),
                    BinderInfo::Default,
                ),
                lam(
                    constant("String", vec![]),
                    lam(
                        pi(
                            constant("ByteArray", vec![]),
                            pi(
                                Expr::app(constant("ByteArray.IsValidUTF8", vec![]), b(0)),
                                Expr::app(
                                    b(3),
                                    Expr::app(
                                        Expr::app(constant("String.ofByteArray", vec![]), b(1)),
                                        b(0),
                                    ),
                                ),
                                BinderInfo::Default,
                            ),
                            BinderInfo::Default,
                        ),
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    constant("String.rec", vec![Level::param(name("u"))]),
                                    b(2),
                                ),
                                lam(
                                    constant("ByteArray", vec![]),
                                    lam(
                                        Expr::app(constant("ByteArray.IsValidUTF8", vec![]), b(0)),
                                        Expr::app(Expr::app(b(2), b(1)), b(0)),
                                        BinderInfo::Default,
                                    ),
                                    BinderInfo::Default,
                                ),
                            ),
                            b(1),
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Implicit,
            ),
            vec![name("String.casesOn")],
        ),
        recursor(
            "String.rec",
            vec!["u"],
            (0, 0, 1, 1, false, false),
            pi(
                pi(
                    constant("String", vec![]),
                    Expr::sort(Level::param(name("u"))),
                    BinderInfo::Default,
                ),
                pi(
                    pi(
                        constant("ByteArray", vec![]),
                        pi(
                            Expr::app(constant("ByteArray.IsValidUTF8", vec![]), b(0)),
                            Expr::app(
                                b(2),
                                Expr::app(
                                    Expr::app(constant("String.ofByteArray", vec![]), b(1)),
                                    b(0),
                                ),
                            ),
                            BinderInfo::Default,
                        ),
                        BinderInfo::Default,
                    ),
                    pi(
                        constant("String", vec![]),
                        Expr::app(b(2), b(0)),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Implicit,
            ),
            vec![name("String")],
            vec![RecursorRule {
                ctor: name("String.ofByteArray"),
                nfields: 2,
                rhs: lam(
                    pi(
                        constant("String", vec![]),
                        Expr::sort(Level::param(name("u"))),
                        BinderInfo::Default,
                    ),
                    lam(
                        pi(
                            constant("ByteArray", vec![]),
                            pi(
                                Expr::app(constant("ByteArray.IsValidUTF8", vec![]), b(0)),
                                Expr::app(
                                    b(2),
                                    Expr::app(
                                        Expr::app(constant("String.ofByteArray", vec![]), b(1)),
                                        b(0),
                                    ),
                                ),
                                BinderInfo::Default,
                            ),
                            BinderInfo::Default,
                        ),
                        lam(
                            constant("ByteArray", vec![]),
                            lam(
                                Expr::app(constant("ByteArray.IsValidUTF8", vec![]), b(0)),
                                Expr::app(Expr::app(b(2), b(1)), b(0)),
                                BinderInfo::Default,
                            ),
                            BinderInfo::Default,
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
            }],
        ),
    ]
}
