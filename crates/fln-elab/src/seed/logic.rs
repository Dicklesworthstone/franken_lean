//! Constructive propositional connectives and compositional decisions.
//!
//! Every result is an ordinary declaration candidate. The production seed
//! admits it through K1 and the independent checker, like user declarations.
//! Negative decisions retain explicit refutations, not host truth values.
use crate::inductive::{ConstructorSpec, InductiveSpec, inductive_with_field_universes};
use crate::lctx::LocalDecl;
use crate::records::RecordBudget;
use fln_core::expr::{BinderInfo, Expr, FVarId};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_env::constants::{
    ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints, TheoremVal,
};
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
fn local(s: &str, type_: Expr, binder_info: BinderInfo) -> LocalDecl {
    LocalDecl {
        id: FVarId(Name::str(name("_fln_logic_seed"), s)),
        user_name: name(s),
        type_,
        value: None,
        binder_info,
        index: 0,
    }
}
fn fv(local: &LocalDecl) -> Expr {
    Expr::fvar(local.id.clone())
}
fn close(locals: &[&LocalDecl], mut body: Expr, lambda: bool) -> Expr {
    for local in locals.iter().rev() {
        body = body
            .abstract_fvar(&local.id, 0)
            .expect("fixed logical telescope");
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
fn arrow(domain: Expr, codomain: Expr) -> Expr {
    let premise = local("arrow_premise", domain, BinderInfo::Default);
    close(&[&premise], codomain, false)
}
fn neg(p: Expr) -> Expr {
    Expr::app(constant("Not"), p)
}
fn decision(p: Expr) -> Expr {
    Expr::app(constant("Decidable"), p)
}
fn positive(p: Expr, proof: Expr) -> Expr {
    app(constant("Decidable.isTrue"), [p, proof])
}
fn negative(p: Expr, proof: Expr) -> Expr {
    app(constant("Decidable.isFalse"), [p, proof])
}
fn defined(s: &str, locals: &[&LocalDecl], result: Expr, value: Expr) -> Declaration {
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name(s),
            level_params: vec![],
            type_: close(locals, result, false),
        },
        value: close(locals, value, true),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name(s)],
    })
}
fn binary_parameters(info: BinderInfo) -> (LocalDecl, LocalDecl) {
    (
        local("a", Expr::sort(Level::zero()), info),
        local("b", Expr::sort(Level::zero()), info),
    )
}
fn connective(s: &str) -> Declaration {
    let (a, b) = binary_parameters(BinderInfo::Default);
    let fields = match s {
        "And" => vec![vec![
            local("left", fv(&a), BinderInfo::Default),
            local("right", fv(&b), BinderInfo::Default),
        ]],
        "Or" => vec![
            vec![local("left", fv(&a), BinderInfo::Default)],
            vec![local("right", fv(&b), BinderInfo::Default)],
        ],
        "Iff" => vec![vec![
            local("mp", arrow(fv(&a), fv(&b)), BinderInfo::Default),
            local("mpr", arrow(fv(&b), fv(&a)), BinderInfo::Default),
        ]],
        _ => unreachable!("fixed logical connective"),
    };
    let universes = fields
        .iter()
        .map(|fs| vec![Level::zero(); fs.len()])
        .collect::<Vec<_>>();
    let constructors = fields
        .into_iter()
        .enumerate()
        .map(|(i, fields)| ConstructorSpec {
            name: name(if s == "Or" {
                if i == 0 { "inl" } else { "inr" }
            } else {
                "intro"
            }),
            fields,
            result_indices: vec![],
        })
        .collect();
    inductive_with_field_universes(
        &InductiveSpec {
            name: name(s),
            level_params: vec![],
            parameters: vec![a, b],
            indices: vec![],
            constructors,
            result_level: Level::zero(),
        },
        RecordBudget::default(),
        &universes,
    )
    .expect("fixed proof-only connective telescope")
}
fn projection(s: &str, field: &str, index: u64) -> Declaration {
    let (a, b) = binary_parameters(BinderInfo::Implicit);
    let h = local(
        "self",
        app(constant(s), [fv(&a), fv(&b)]),
        BinderInfo::Default,
    );
    let result = match (s, index) {
        ("And", 0) => fv(&a),
        ("And", _) => fv(&b),
        ("Iff", 0) => arrow(fv(&a), fv(&b)),
        ("Iff", _) => arrow(fv(&b), fv(&a)),
        _ => unreachable!("fixed logical projection"),
    };
    defined(
        &format!("{s}.{field}"),
        &[&a, &b, &h],
        result,
        Expr::proj(name(s), index, fv(&h)),
    )
}
fn or_elim() -> Declaration {
    let (a, b) = binary_parameters(BinderInfo::Implicit);
    let c = local("c", Expr::sort(Level::zero()), BinderInfo::Implicit);
    let domain = app(constant("Or"), [fv(&a), fv(&b)]);
    let h = local("h", domain.clone(), BinderInfo::Default);
    let left = local("left", arrow(fv(&a), fv(&c)), BinderInfo::Default);
    let right = local("right", arrow(fv(&b), fv(&c)), BinderInfo::Default);
    let witness = local("witness", domain, BinderInfo::Default);
    // Or has two constructors in Prop: its recursor eliminates only to Prop
    // and has no universe parameter. No proof-to-data escape is introduced.
    let value = app(
        constant("Or.rec"),
        [
            fv(&a),
            fv(&b),
            close(&[&witness], fv(&c), true),
            fv(&left),
            fv(&right),
            fv(&h),
        ],
    );
    Declaration::Thm(TheoremVal {
        base: ConstantVal {
            name: name("Or.elim"),
            level_params: vec![],
            type_: close(&[&a, &b, &c, &h, &left, &right], fv(&c), false),
        },
        value: close(&[&a, &b, &c, &h, &left, &right], value, true),
        all: vec![name("Or.elim")],
    })
}
fn eliminate(p: Expr, d: Expr, result: Expr, no: Expr, yes: Expr) -> Expr {
    let witness = local("decision_witness", decision(p.clone()), BinderInfo::Default);
    app(
        Expr::const_(name("Decidable.rec"), vec![Level::one()]),
        [p, close(&[&witness], result, true), no, yes, d],
    )
}
fn absurd(p: Expr, false_proof: Expr) -> Expr {
    let witness = local("false_witness", constant("False"), BinderInfo::Default);
    app(
        Expr::const_(name("False.rec"), vec![Level::zero()]),
        [close(&[&witness], p, true), false_proof],
    )
}

/// Reference branch order is retained: inspect the left dictionary first,
/// then inspect the right dictionary only where its proof is needed.
fn composite_instance(s: &str, instance_name: &str) -> Declaration {
    let (a, b) = binary_parameters(BinderInfo::Implicit);
    let da = local("da", decision(fv(&a)), BinderInfo::InstImplicit);
    let db = local("db", decision(fv(&b)), BinderInfo::InstImplicit);
    let ha = local("ha", fv(&a), BinderInfo::Default);
    let hb = local("hb", fv(&b), BinderInfo::Default);
    let na = local("na", neg(fv(&a)), BinderInfo::Default);
    let nb = local("nb", neg(fv(&b)), BinderInfo::Default);
    let target = if s == "Implies" {
        arrow(fv(&a), fv(&b))
    } else {
        app(constant(s), [fv(&a), fv(&b)])
    };
    let h = local("h", target.clone(), BinderInfo::Default);
    let result = decision(target.clone());
    let pos = |proof| positive(target.clone(), proof);
    let nope = |proof| negative(target.clone(), proof);
    let field = |index| Expr::proj(name(s), index, fv(&h));
    let (no, yes) = match s {
        "And" => {
            let no = close(
                &[&na],
                nope(close(&[&h], Expr::app(fv(&na), field(0)), true)),
                true,
            );
            let yes = eliminate(
                fv(&b),
                fv(&db),
                result.clone(),
                close(
                    &[&nb],
                    nope(close(&[&h], Expr::app(fv(&nb), field(1)), true)),
                    true,
                ),
                close(
                    &[&hb],
                    pos(app(
                        constant("And.intro"),
                        [fv(&a), fv(&b), fv(&ha), fv(&hb)],
                    )),
                    true,
                ),
            );
            (no, close(&[&ha], yes, true))
        }
        "Or" => {
            let witness = local("or_witness", target.clone(), BinderInfo::Default);
            let contradiction = app(
                constant("Or.rec"),
                [
                    fv(&a),
                    fv(&b),
                    close(&[&witness], constant("False"), true),
                    fv(&na),
                    fv(&nb),
                    fv(&h),
                ],
            );
            let no = eliminate(
                fv(&b),
                fv(&db),
                result.clone(),
                close(&[&nb], nope(close(&[&h], contradiction, true)), true),
                close(
                    &[&hb],
                    pos(app(constant("Or.inr"), [fv(&a), fv(&b), fv(&hb)])),
                    true,
                ),
            );
            let yes = pos(app(constant("Or.inl"), [fv(&a), fv(&b), fv(&ha)]));
            (close(&[&na], no, true), close(&[&ha], yes, true))
        }
        "Implies" => {
            let no = pos(close(
                &[&ha],
                absurd(fv(&b), Expr::app(fv(&na), fv(&ha))),
                true,
            ));
            let yes = eliminate(
                fv(&b),
                fv(&db),
                result.clone(),
                close(
                    &[&nb],
                    nope(close(
                        &[&h],
                        Expr::app(fv(&nb), Expr::app(fv(&h), fv(&ha))),
                        true,
                    )),
                    true,
                ),
                close(&[&hb], pos(close(&[&ha], fv(&hb), true)), true),
            );
            (close(&[&na], no, true), close(&[&ha], yes, true))
        }
        "Iff" => {
            let intro = |mp, mpr| app(constant("Iff.intro"), [fv(&a), fv(&b), mp, mpr]);
            let yes = eliminate(
                fv(&b),
                fv(&db),
                result.clone(),
                close(
                    &[&nb],
                    nope(close(
                        &[&h],
                        Expr::app(fv(&nb), Expr::app(field(0), fv(&ha))),
                        true,
                    )),
                    true,
                ),
                close(
                    &[&hb],
                    pos(intro(
                        close(&[&ha], fv(&hb), true),
                        close(&[&hb], fv(&ha), true),
                    )),
                    true,
                ),
            );
            let no = eliminate(
                fv(&b),
                fv(&db),
                result.clone(),
                close(
                    &[&nb],
                    pos(intro(
                        close(&[&ha], absurd(fv(&b), Expr::app(fv(&na), fv(&ha))), true),
                        close(&[&hb], absurd(fv(&a), Expr::app(fv(&nb), fv(&hb))), true),
                    )),
                    true,
                ),
                close(
                    &[&hb],
                    nope(close(
                        &[&h],
                        Expr::app(fv(&na), Expr::app(field(1), fv(&hb))),
                        true,
                    )),
                    true,
                ),
            );
            (close(&[&na], no, true), close(&[&ha], yes, true))
        }
        _ => unreachable!("fixed composite decision"),
    };
    let value = eliminate(fv(&a), fv(&da), result.clone(), no, yes);
    defined(instance_name, &[&a, &b, &da, &db], result, value)
}

/// Order is deterministic and dependencies precede their consumers. These
/// candidates introduce neither classical axioms nor trusted evaluator cases.
pub fn logical_seed_declarations() -> [Declaration; 12] {
    [
        connective("And"),
        projection("And", "left", 0),
        projection("And", "right", 1),
        connective("Or"),
        or_elim(),
        connective("Iff"),
        projection("Iff", "mp", 0),
        projection("Iff", "mpr", 1),
        composite_instance("And", "instDecidableAnd"),
        composite_instance("Or", "instDecidableOr"),
        composite_instance("Implies", "instDecidableImplies"),
        composite_instance("Iff", "instDecidableIff"),
    ]
}
