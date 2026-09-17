//! Native existential candidates with the ordinary Prop-only elimination rule.
//! Witnesses are never extracted as data by a trusted shortcut.
use crate::inductive::{ConstructorSpec, InductiveSpec, inductive_with_field_universes};
use crate::lctx::LocalDecl;
use crate::records::RecordBudget;
use fln_core::{
    expr::{BinderInfo, Expr, FVarId},
    level::Level,
    name::Name,
};
use fln_env::constants::{ConstantVal, TheoremVal};
use fln_kernel::Declaration;

fn name(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn fv(local: &LocalDecl) -> Expr {
    Expr::fvar(local.id.clone())
}
fn local(s: &str, type_: Expr, info: BinderInfo) -> LocalDecl {
    LocalDecl {
        id: FVarId(Name::str(name("_fln_exists_seed"), s)),
        user_name: name(s),
        type_,
        value: None,
        binder_info: info,
        index: 0,
    }
}
fn close(locals: &[&LocalDecl], mut body: Expr, lambda: bool) -> Expr {
    for local in locals.iter().rev() {
        body = body
            .abstract_fvar(&local.id, 0)
            .expect("fixed existential telescope");
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
fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}

pub fn existential_seed_declarations() -> [Declaration; 2] {
    let u_name = name("u");
    let u = Level::param(u_name.clone());
    let implicit = BinderInfo::Implicit;
    let explicit = BinderInfo::Default;
    let alpha = local("A", Expr::sort(u.clone()), implicit);
    let witness = local("w", fv(&alpha), explicit);
    let predicate = local(
        "p",
        close(&[&witness], Expr::sort(Level::zero()), false),
        explicit,
    );
    let evidence = local("h", Expr::app(fv(&predicate), fv(&witness)), explicit);
    let family = inductive_with_field_universes(
        &InductiveSpec {
            name: name("Exists"),
            level_params: vec![u_name.clone()],
            parameters: vec![alpha.clone(), predicate.clone()],
            indices: vec![],
            constructors: vec![ConstructorSpec {
                name: name("intro"),
                fields: vec![witness.clone(), evidence.clone()],
                result_indices: vec![],
            }],
            result_level: Level::zero(),
        },
        RecordBudget::default(),
        &[vec![u.clone(), Level::zero()]],
    )
    .expect("fixed dependent existential family");

    let mut predicate = predicate;
    predicate.binder_info = implicit;
    let result = local("b", Expr::sort(Level::zero()), implicit);
    let exists = app(
        Expr::const_(name("Exists"), vec![u.clone()]),
        [fv(&alpha), fv(&predicate)],
    );
    let major = local("major", exists, explicit);
    let minor = local(
        "minor",
        close(&[&witness, &evidence], fv(&result), false),
        explicit,
    );
    let motive = close(&[&major], fv(&result), true);
    let proof = app(
        Expr::const_(name("Exists.rec"), vec![u]),
        [fv(&alpha), fv(&predicate), motive, fv(&minor), fv(&major)],
    );
    let binders = [&alpha, &predicate, &result, &major, &minor];
    let eliminator = Declaration::Thm(TheoremVal {
        base: ConstantVal {
            name: name("Exists.elim"),
            level_params: vec![u_name],
            type_: close(&binders, fv(&result), false),
        },
        value: close(&binders, proof, true),
        all: vec![name("Exists.elim")],
    });
    [family, eliminator]
}
