//! Fixed declaration models from Init/Prelude and Init/System/ST at the pin.
//! Binder labels and transparent metadata are intentionally absent. Comparison
//! still checks every binder kind, universe, body, constructor, and recursor rule.

use super::*;
use fln_env::constants::{RecursorRule, RecursorVal};

pub(super) const PRIMITIVES: [&str; 5] = [
    "Void.mk",
    "ST.Prim.mkRef",
    "ST.Prim.Ref.get",
    "ST.Prim.Ref.set",
    "ST.Prim.Ref.swap",
];

pub(super) fn name(label: &str) -> Name {
    if let Some(tail) = label.strip_prefix("_private.Init.System.ST.0.") {
        tail.split('.').fold(
            Name::num(
                Name::from_components(["_private", "Init", "System", "ST"]),
                0,
            ),
            Name::str,
        )
    } else {
        Name::from_components(label.split('.'))
    }
}

fn c(label: &str) -> Expr {
    constant(label, vec![])
}
fn constant(label: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(name(label), levels)
}
fn app(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}
fn b(index: u32) -> Expr {
    Expr::bvar(index).expect("fixed ST model index")
}
fn ty() -> Expr {
    Expr::sort(Level::one())
}
fn pi(domain: Expr, body: Expr, info: BinderInfo) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, info)
}
fn p(domain: Expr, body: Expr) -> Expr {
    pi(domain, body, BinderInfo::Default)
}
fn l(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}
fn parameters(count: usize, mut body: Expr, info: BinderInfo, lambda: bool) -> Expr {
    for _ in 0..count {
        body = if lambda {
            Expr::lam(Name::anonymous(), ty(), body, info)
        } else {
            pi(ty(), body, info)
        };
    }
    body
}
fn base(label: &str, levels: &[&str], type_: Expr) -> ConstantVal {
    ConstantVal {
        name: name(label),
        level_params: levels.iter().map(|n| name(n)).collect(),
        type_,
    }
}
fn definition(
    label: &str,
    levels: &[&str],
    type_: Expr,
    value: Expr,
    hints: ReducibilityHints,
) -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: base(label, levels, type_),
        value,
        hints,
        safety: DefinitionSafety::Safe,
        all: vec![name(label)],
    })
}
fn opaque(label: &str, type_: Expr, value: Expr) -> OpaqueVal {
    OpaqueVal {
        base: base(label, &[], type_),
        value,
        is_unsafe: false,
        all: vec![name(label)],
    }
}
fn void(state: Expr) -> Expr {
    Expr::app(c("Void"), state)
}
fn reference(state: Expr, value: Expr) -> Expr {
    app(c("ST.Ref"), [state, value])
}
fn state_action(state: Expr, value: Expr) -> Expr {
    app(c("ST"), [state, value])
}
fn nonempty(type_: Expr) -> Expr {
    Expr::app(constant("Nonempty", vec![Level::one()]), type_)
}
fn pointed() -> Expr {
    Expr::app(
        constant("NonemptyType.type", vec![Level::zero()]),
        c("ST.RefPointed"),
    )
}
fn default_nonempty() -> Expr {
    app(
        constant(
            "Inhabited.default",
            vec![Level::one().succ().expect("fixed universe")],
        ),
        [
            constant("NonemptyType", vec![Level::zero()]),
            constant("instInhabitedNonemptyType", vec![Level::zero()]),
        ],
    )
}

fn result_family(label: &str, count: u32, constructors: &[(&str, Expr)]) -> Vec<ConstantInfo> {
    let names: Vec<_> = constructors.iter().map(|(n, _)| name(n)).collect();
    let mut model = vec![ConstantInfo::Induct(InductiveVal {
        base: base(
            label,
            &[],
            parameters(count as usize, ty(), BinderInfo::Default, false),
        ),
        num_params: count,
        num_indices: 0,
        all: vec![name(label)],
        ctors: names,
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    })];
    for (index, (constructor, type_)) in constructors.iter().enumerate() {
        model.push(ConstantInfo::Ctor(ConstructorVal {
            base: base(
                constructor,
                &[],
                parameters(count as usize, type_.clone(), BinderInfo::Implicit, false),
            ),
            induct: name(label),
            cidx: index as u32,
            num_params: count,
            num_fields: 2,
            is_unsafe: false,
        }));
    }
    model
}

fn record_recursor(label: &str, is_reference: bool) -> ConstantInfo {
    let constructor = format!("{label}.mk");
    let motive = p(
        app(c(label), [b(1), b(0)]),
        Expr::sort(Level::param(name("u"))),
    );
    let minor = p(
        if is_reference { pointed() } else { b(1) },
        p(
            if is_reference {
                nonempty(b(2))
            } else {
                void(b(3))
            },
            Expr::app(b(2), app(c(&constructor), [b(4), b(3), b(1), b(0)])),
        ),
    );
    let type_ = parameters(
        2,
        pi(
            motive.clone(),
            p(
                minor.clone(),
                p(app(c(label), [b(3), b(2)]), Expr::app(b(2), b(0))),
            ),
            BinderInfo::Implicit,
        ),
        BinderInfo::Implicit,
        false,
    );
    let rhs = parameters(
        2,
        l(
            motive,
            l(
                minor,
                l(
                    if is_reference { pointed() } else { b(2) },
                    l(
                        if is_reference {
                            nonempty(b(3))
                        } else {
                            void(b(4))
                        },
                        app(b(2), [b(1), b(0)]),
                    ),
                ),
            ),
        ),
        BinderInfo::Default,
        true,
    );
    ConstantInfo::Rec(RecursorVal {
        base: base(&format!("{label}.rec"), &["u"], type_),
        all: vec![name(label)],
        num_params: 2,
        num_indices: 0,
        num_motives: 1,
        num_minors: 1,
        rules: vec![RecursorRule {
            ctor: name(&constructor),
            nfields: 2,
            rhs,
        }],
        k: false,
        is_unsafe: false,
    })
}

fn exception_recursor() -> ConstantInfo {
    let motive = p(
        app(c("EST.Out"), [b(2), b(1), b(0)]),
        Expr::sort(Level::param(name("u"))),
    );
    let ok = p(
        b(1),
        p(
            void(b(3)),
            Expr::app(b(2), app(c("EST.Out.ok"), [b(5), b(4), b(3), b(1), b(0)])),
        ),
    );
    let error = p(
        b(4),
        p(
            void(b(4)),
            Expr::app(
                b(3),
                app(c("EST.Out.error"), [b(6), b(5), b(4), b(1), b(0)]),
            ),
        ),
    );
    let type_ = parameters(
        3,
        pi(
            motive.clone(),
            p(
                ok.clone(),
                p(
                    error.clone(),
                    p(app(c("EST.Out"), [b(5), b(4), b(3)]), Expr::app(b(3), b(0))),
                ),
            ),
            BinderInfo::Implicit,
        ),
        BinderInfo::Implicit,
        false,
    );
    let rules = [("EST.Out.ok", 3, 3), ("EST.Out.error", 5, 2)].map(|(ctor, field, branch)| {
        let rhs = parameters(
            3,
            l(
                motive.clone(),
                l(
                    ok.clone(),
                    l(
                        error.clone(),
                        l(b(field), l(void(b(5)), app(b(branch), [b(1), b(0)]))),
                    ),
                ),
            ),
            BinderInfo::Default,
            true,
        );
        RecursorRule {
            ctor: name(ctor),
            nfields: 2,
            rhs,
        }
    });
    ConstantInfo::Rec(RecursorVal {
        base: base("EST.Out.rec", &["u"], type_),
        all: vec![name("EST.Out")],
        num_params: 3,
        num_indices: 0,
        num_motives: 1,
        num_minors: 2,
        rules: rules.into(),
        k: false,
        is_unsafe: false,
    })
}

fn unit() -> Vec<ConstantInfo> {
    let u = Level::param(name("u"));
    let motive = p(
        constant("PUnit", vec![u.clone()]),
        Expr::sort(Level::param(name("u_1"))),
    );
    let minor = Expr::app(b(0), constant("PUnit.unit", vec![u.clone()]));
    vec![
        ConstantInfo::Induct(InductiveVal {
            base: base("PUnit", &["u"], Expr::sort(u.clone())),
            num_params: 0,
            num_indices: 0,
            all: vec![name("PUnit")],
            ctors: vec![name("PUnit.unit")],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }),
        ConstantInfo::Ctor(ConstructorVal {
            base: base("PUnit.unit", &["u"], constant("PUnit", vec![u.clone()])),
            induct: name("PUnit"),
            cidx: 0,
            num_params: 0,
            num_fields: 0,
            is_unsafe: false,
        }),
        ConstantInfo::Rec(RecursorVal {
            base: base(
                "PUnit.rec",
                &["u_1", "u"],
                pi(
                    motive.clone(),
                    p(
                        minor.clone(),
                        p(constant("PUnit", vec![u]), Expr::app(b(2), b(0))),
                    ),
                    BinderInfo::Implicit,
                ),
            ),
            all: vec![name("PUnit")],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 1,
            rules: vec![RecursorRule {
                ctor: name("PUnit.unit"),
                nfields: 0,
                rhs: l(motive, l(minor, b(0))),
            }],
            k: false,
            is_unsafe: false,
        }),
        definition(
            "Unit",
            &[],
            ty(),
            constant("PUnit", vec![Level::one()]),
            ReducibilityHints::Abbrev,
        ),
        definition(
            "Unit.unit",
            &[],
            c("Unit"),
            constant("PUnit.unit", vec![Level::one()]),
            ReducibilityHints::Abbrev,
        ),
    ]
}

pub(super) fn world() -> Vec<ConstantInfo> {
    let u = Level::param(name("u"));
    let u1 = u.clone().succ().expect("fixed universe");
    let u2 = u1.clone().succ().expect("fixed universe");
    let property = l(
        Expr::sort(u1.clone()),
        Expr::app(constant("Nonempty", vec![u1.clone()]), b(0)),
    );
    let subtype = app(
        constant("Subtype", vec![u2.clone()]),
        [Expr::sort(u1.clone()), property.clone()],
    );
    let mut model = vec![
        definition(
            "NonemptyType",
            &["u"],
            Expr::sort(Level::max(Level::one(), u2.clone()).expect("fixed universe")),
            subtype,
            ReducibilityHints::Regular(1),
        ),
        definition(
            "NonemptyType.type",
            &["u"],
            p(
                constant("NonemptyType", vec![u.clone()]),
                Expr::sort(u1.clone()),
            ),
            l(
                constant("NonemptyType", vec![u.clone()]),
                app(
                    constant("Subtype.val", vec![u2.clone()]),
                    [Expr::sort(u1.clone()), property.clone(), b(0)],
                ),
            ),
            ReducibilityHints::Abbrev,
        ),
        definition(
            "instInhabitedNonemptyType",
            &["u"],
            Expr::app(
                constant("Inhabited", vec![u2.clone()]),
                constant("NonemptyType", vec![u.clone()]),
            ),
            app(
                constant("Inhabited.mk", vec![u2.clone()]),
                [
                    constant("NonemptyType", vec![u]),
                    app(
                        constant("Subtype.mk", vec![u2]),
                        [
                            Expr::sort(u1.clone()),
                            property,
                            constant("PUnit", vec![u1.clone()]),
                            app(
                                constant("Nonempty.intro", vec![u1.clone()]),
                                [
                                    constant("PUnit", vec![u1.clone()]),
                                    constant("PUnit.unit", vec![u1]),
                                ],
                            ),
                        ],
                    ),
                ],
            ),
            ReducibilityHints::Regular(2),
        ),
        ConstantInfo::Opaque(opaque(
            "Void.nonemptyType",
            p(ty(), constant("NonemptyType", vec![Level::zero()])),
            l(ty(), default_nonempty()),
        )),
        definition(
            "Void",
            &[],
            p(ty(), ty()),
            l(
                ty(),
                Expr::app(
                    constant("NonemptyType.type", vec![Level::zero()]),
                    Expr::app(c("Void.nonemptyType"), b(0)),
                ),
            ),
            ReducibilityHints::Regular(1),
        ),
        definition(
            "ST",
            &[],
            parameters(2, ty(), BinderInfo::Default, false),
            parameters(
                2,
                p(void(b(1)), app(c("ST.Out"), [b(2), b(1)])),
                BinderInfo::Default,
                true,
            ),
            ReducibilityHints::Regular(2),
        ),
        definition(
            "EST",
            &[],
            parameters(3, ty(), BinderInfo::Default, false),
            parameters(
                3,
                p(void(b(1)), app(c("EST.Out"), [b(3), b(2), b(1)])),
                BinderInfo::Default,
                true,
            ),
            ReducibilityHints::Regular(2),
        ),
    ];
    model.extend(unit());
    model.extend(result_family(
        "ST.Out",
        2,
        &[(
            "ST.Out.mk",
            p(b(0), p(void(b(2)), app(c("ST.Out"), [b(3), b(2)]))),
        )],
    ));
    model.push(record_recursor("ST.Out", false));
    model.extend(result_family(
        "EST.Out",
        3,
        &[
            (
                "EST.Out.ok",
                p(b(0), p(void(b(2)), app(c("EST.Out"), [b(4), b(3), b(2)]))),
            ),
            (
                "EST.Out.error",
                p(b(2), p(void(b(2)), app(c("EST.Out"), [b(4), b(3), b(2)]))),
            ),
        ],
    ));
    model.push(exception_recursor());
    model
}

pub(super) fn references() -> Vec<ConstantInfo> {
    let mut model = vec![ConstantInfo::Opaque(opaque(
        "ST.RefPointed",
        constant("NonemptyType", vec![Level::zero()]),
        default_nonempty(),
    ))];
    model.extend(result_family(
        "ST.Ref",
        2,
        &[(
            "ST.Ref.mk",
            p(pointed(), p(nonempty(b(1)), reference(b(3), b(2)))),
        )],
    ));
    model.push(record_recursor("ST.Ref", true));
    model
}

fn pure_dictionary(state: Expr) -> Expr {
    let monad = Expr::app(c("ST"), state.clone());
    app(
        constant("Applicative.toPure", vec![Level::zero(); 2]),
        [
            monad.clone(),
            app(
                constant("Monad.toApplicative", vec![Level::zero(); 2]),
                [monad, Expr::app(c("instMonadST"), state)],
            ),
        ],
    )
}

pub(super) fn primitive(label: &str) -> OpaqueVal {
    if label == "Void.mk" {
        let value = l(
            b(0),
            app(
                constant("Classical.ofNonempty", vec![Level::one()]),
                [void(b(1)), Expr::app(c("Void.instNonempty"), b(1))],
            ),
        );
        return opaque(
            label,
            parameters(1, p(b(0), void(b(1))), BinderInfo::Implicit, false),
            parameters(1, value, BinderInfo::Implicit, true),
        );
    }
    let (type_, value) = match label {
        "ST.Prim.mkRef" => {
            let ref_type = reference(b(2), b(1));
            let cell = app(
                c("ST.Ref.mk"),
                [
                    b(2),
                    b(1),
                    app(
                        constant("Classical.choice", vec![Level::one()]),
                        [
                            pointed(),
                            c("_private.Init.System.ST.0.ST.Prim.mkRef._proof_1"),
                        ],
                    ),
                    app(constant("Nonempty.intro", vec![Level::one()]), [b(1), b(0)]),
                ],
            );
            (
                p(b(0), state_action(b(2), ref_type.clone())),
                l(
                    b(0),
                    app(
                        constant("Pure.pure", vec![Level::zero(); 2]),
                        [
                            Expr::app(c("ST"), b(2)),
                            pure_dictionary(b(2)),
                            ref_type,
                            cell,
                        ],
                    ),
                ),
            )
        }
        "ST.Prim.Ref.get" => (
            p(reference(b(1), b(0)), state_action(b(2), b(1))),
            l(
                reference(b(1), b(0)),
                app(
                    c("_private.Init.System.ST.0.ST.Prim.inhabitedFromRef"),
                    [b(2), b(1), b(0)],
                ),
            ),
        ),
        "ST.Prim.Ref.swap" => (
            p(reference(b(1), b(0)), p(b(1), state_action(b(3), b(2)))),
            l(
                reference(b(1), b(0)),
                l(
                    b(1),
                    app(
                        c("_private.Init.System.ST.0.ST.Prim.inhabitedFromRef"),
                        [b(3), b(2), b(1)],
                    ),
                ),
            ),
        ),
        "ST.Prim.Ref.set" => (
            p(
                reference(b(1), b(0)),
                p(b(1), state_action(b(3), c("Unit"))),
            ),
            l(
                reference(b(1), b(0)),
                l(
                    b(1),
                    app(
                        constant("Inhabited.default", vec![Level::one()]),
                        [
                            state_action(b(3), c("Unit")),
                            app(
                                c("instInhabitedST"),
                                [
                                    b(3),
                                    c("Unit"),
                                    constant("instInhabitedPUnit", vec![Level::one()]),
                                ],
                            ),
                        ],
                    ),
                ),
            ),
        ),
        _ => unreachable!("fixed safe ST primitive"),
    };
    opaque(
        label,
        parameters(2, type_, BinderInfo::Implicit, false),
        parameters(2, value, BinderInfo::Implicit, true),
    )
}

pub(super) fn runner(requested: &Name) -> Option<ConstantInfo> {
    let initial_world = app(c("Void.mk"), [c("Unit"), c("Unit.unit")]);
    let action = app(b(0), [c("Unit"), initial_world]);
    if requested == &name("runST") {
        let callback = p(ty(), state_action(b(0), b(1)));
        let type_ = parameters(1, p(callback.clone(), b(1)), BinderInfo::Implicit, false);
        let body = app(
            constant(
                "_private.Init.System.ST.0.runST.match_1",
                vec![Level::one()],
            ),
            [
                b(1),
                l(app(c("ST.Out"), [c("Unit"), b(1)]), b(2)),
                action,
                l(b(1), l(void(c("Unit")), b(1))),
            ],
        );
        Some(definition(
            "runST",
            &[],
            type_,
            parameters(1, l(callback, body), BinderInfo::Implicit, true),
            ReducibilityHints::Regular(3),
        ))
    } else if requested == &name("runEST") {
        let callback = p(ty(), app(c("EST"), [b(2), b(0), b(1)]));
        let result = app(constant("Except", vec![Level::zero(); 2]), [b(2), b(1)]);
        let type_ = parameters(2, p(callback.clone(), result), BinderInfo::Implicit, false);
        let body = app(
            constant(
                "_private.Init.System.ST.0.runEST.match_1",
                vec![Level::one()],
            ),
            [
                b(2),
                b(1),
                l(
                    app(c("EST.Out"), [b(2), c("Unit"), b(1)]),
                    app(constant("Except", vec![Level::zero(); 2]), [b(3), b(2)]),
                ),
                action,
                l(
                    b(1),
                    l(
                        void(c("Unit")),
                        app(
                            constant("Except.ok", vec![Level::zero(); 2]),
                            [b(4), b(3), b(1)],
                        ),
                    ),
                ),
                l(
                    b(2),
                    l(
                        void(c("Unit")),
                        app(
                            constant("Except.error", vec![Level::zero(); 2]),
                            [b(4), b(3), b(1)],
                        ),
                    ),
                ),
            ],
        );
        Some(definition(
            "runEST",
            &[],
            type_,
            parameters(2, l(callback, body), BinderInfo::Implicit, true),
            ReducibilityHints::Regular(3),
        ))
    } else {
        None
    }
}
