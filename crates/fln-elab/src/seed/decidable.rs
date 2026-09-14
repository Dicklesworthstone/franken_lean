//! Checked logical decisions. A decision carries a proof or a refutation;
//! no host Boolean or new axiom can stand in for either constructor argument.
use super::*;
use crate::inductive::{ConstructorSpec, InductiveSpec, inductive_declaration};
use crate::lctx::LocalDecl;
use crate::records::RecordBudget;
use fln_core::expr::FVarId;
use fln_env::constants::{DefinitionSafety, DefinitionVal, ReducibilityHints};

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
        id: FVarId(Name::str(name("_fln_decidable_seed"), s)),
        user_name: name(s),
        type_,
        value: None,
        binder_info,
        index: 0,
    }
}
fn fv(l: &LocalDecl) -> Expr {
    Expr::fvar(l.id.clone())
}
fn close(locals: &[&LocalDecl], mut body: Expr, lambda: bool) -> Expr {
    for l in locals.iter().rev() {
        body = body
            .abstract_fvar(&l.id, 0)
            .expect("fixed decision telescope");
        body = if lambda {
            Expr::lam(l.user_name.clone(), l.type_.clone(), body, l.binder_info)
        } else {
            Expr::forall_e(l.user_name.clone(), l.type_.clone(), body, l.binder_info)
        };
    }
    body
}
fn neg(p: Expr) -> Expr {
    Expr::app(constant("Not"), p)
}
fn decision(p: Expr) -> Expr {
    Expr::app(constant("Decidable"), p)
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
fn family(
    s: &str,
    parameters: Vec<LocalDecl>,
    constructors: Vec<ConstructorSpec>,
    level: Level,
) -> Declaration {
    inductive_declaration(
        &InductiveSpec {
            name: name(s),
            level_params: vec![],
            parameters,
            indices: vec![],
            constructors,
            result_level: level,
        },
        RecordBudget::default(),
    )
    .expect("fixed logical family has a valid telescope")
}
pub fn false_declaration() -> Declaration {
    family("False", vec![], vec![], Level::zero())
}
pub fn true_declaration() -> Declaration {
    family(
        "True",
        vec![],
        vec![ConstructorSpec {
            name: name("intro"),
            fields: vec![],
            result_indices: vec![],
        }],
        Level::zero(),
    )
}
pub fn not_declaration() -> Declaration {
    let p = local("p", Expr::sort(Level::zero()), BinderInfo::Default);
    let h = local("h", fv(&p), BinderInfo::Default);
    defined(
        "Not",
        vec![],
        &[&p],
        Expr::sort(Level::zero()),
        close(&[&h], constant("False"), false),
    )
}
pub fn decidable_declaration() -> Declaration {
    let p = local("p", Expr::sort(Level::zero()), BinderInfo::Default);
    family(
        "Decidable",
        vec![p.clone()],
        vec![
            ConstructorSpec {
                name: name("isFalse"),
                fields: vec![local("h", neg(fv(&p)), BinderInfo::Default)],
                result_indices: vec![],
            },
            ConstructorSpec {
                name: name("isTrue"),
                fields: vec![local("h", fv(&p), BinderInfo::Default)],
                result_indices: vec![],
            },
        ],
        Level::one(),
    )
}
fn eliminate(p: Expr, d: Expr, result: Expr, level: Level, no: Expr, yes: Expr) -> Expr {
    let witness = local("witness", decision(p.clone()), BinderInfo::Default);
    app(
        Expr::const_(name("Decidable.rec"), vec![level]),
        [p, close(&[&witness], result, true), no, yes, d],
    )
}
pub fn conditional_declaration(dependent: bool) -> Declaration {
    let u = name("u");
    let alpha = local(
        "alpha",
        Expr::sort(Level::param(u.clone())),
        BinderInfo::Implicit,
    );
    let p = local("p", Expr::sort(Level::zero()), BinderInfo::Default);
    let d = local("d", decision(fv(&p)), BinderInfo::InstImplicit);
    let hp = local("hp", fv(&p), BinderInfo::Default);
    let hn = local("hn", neg(fv(&p)), BinderInfo::Default);
    let yes = local(
        "yes",
        if dependent {
            close(&[&hp], fv(&alpha), false)
        } else {
            fv(&alpha)
        },
        BinderInfo::Default,
    );
    let no = local(
        "no",
        if dependent {
            close(&[&hn], fv(&alpha), false)
        } else {
            fv(&alpha)
        },
        BinderInfo::Default,
    );
    let value = eliminate(
        fv(&p),
        fv(&d),
        fv(&alpha),
        Level::param(u.clone()),
        if dependent {
            fv(&no)
        } else {
            close(&[&hn], fv(&no), true)
        },
        if dependent {
            fv(&yes)
        } else {
            close(&[&hp], fv(&yes), true)
        },
    );
    defined(
        if dependent { "dite" } else { "ite" },
        vec![u],
        &[&alpha, &p, &d, &yes, &no],
        fv(&alpha),
        value,
    )
}
pub fn decide_declaration() -> Declaration {
    let p = local("p", Expr::sort(Level::zero()), BinderInfo::Default);
    let d = local("d", decision(fv(&p)), BinderInfo::InstImplicit);
    let hp = local("hp", fv(&p), BinderInfo::Default);
    let hn = local("hn", neg(fv(&p)), BinderInfo::Default);
    let value = eliminate(
        fv(&p),
        fv(&d),
        constant("Bool"),
        Level::one(),
        close(&[&hn], constant("Bool.false"), true),
        close(&[&hp], constant("Bool.true"), true),
    );
    defined("decide", vec![], &[&p, &d], constant("Bool"), value)
}
pub fn true_instance() -> Declaration {
    defined(
        "instDecidableTrue",
        vec![],
        &[],
        decision(constant("True")),
        app(
            constant("Decidable.isTrue"),
            [constant("True"), constant("True.intro")],
        ),
    )
}
pub fn false_instance() -> Declaration {
    let h = local("h", constant("False"), BinderInfo::Default);
    defined(
        "instDecidableFalse",
        vec![],
        &[],
        decision(constant("False")),
        app(
            constant("Decidable.isFalse"),
            [constant("False"), close(&[&h], fv(&h), true)],
        ),
    )
}
pub fn not_instance() -> Declaration {
    let p = local("p", Expr::sort(Level::zero()), BinderInfo::Implicit);
    let d = local("d", decision(fv(&p)), BinderInfo::InstImplicit);
    let hp = local("hp", fv(&p), BinderInfo::Default);
    let hn = local("hn", neg(fv(&p)), BinderInfo::Default);
    let negative = close(
        &[&hn],
        app(constant("Decidable.isTrue"), [neg(fv(&p)), fv(&hn)]),
        true,
    );
    let refutation = close(&[&hn], Expr::app(fv(&hn), fv(&hp)), true);
    let positive = close(
        &[&hp],
        app(constant("Decidable.isFalse"), [neg(fv(&p)), refutation]),
        true,
    );
    let result = decision(neg(fv(&p)));
    let value = eliminate(
        fv(&p),
        fv(&d),
        result.clone(),
        Level::one(),
        negative,
        positive,
    );
    defined("instDecidableNot", vec![], &[&p, &d], result, value)
}
