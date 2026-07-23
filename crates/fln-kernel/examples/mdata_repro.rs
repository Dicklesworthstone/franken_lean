#![forbid(unsafe_code)]

use fln_core::expr::Expr;
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};
use fln_env::environment::Environment;
use fln_kernel::check_def_eq;
use fln_kernel::verdict::Budget;

fn n(s: &str) -> Name {
    Name::str(Name::anonymous(), s)
}

fn main() {
    let env = Environment::new();
    let ax = |name: &str, ty: Expr| {
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n(name),
                level_params: vec![],
                type_: ty,
            },
            is_unsafe: false,
        })
    };
    let sort1 = Expr::sort(Level::one());
    let a_ty = Expr::const_(n("A"), vec![]);
    let arrow = Expr::forall_e(
        n("_x"),
        a_ty.clone(),
        a_ty.clone(),
        fln_core::expr::BinderInfo::Default,
    );
    let env = env.add_decl(ax("A", sort1)).unwrap();
    let env = env.add_decl(ax("c", arrow.clone())).unwrap();
    let env = env.add_decl(ax("x", a_ty.clone())).unwrap();
    let x = Expr::const_(n("x"), vec![]);
    let c = Expr::const_(n("c"), vec![]);
    let mx = Expr::mdata(KVMap::default(), x.clone());
    let t1 = Expr::app(c.clone(), x.clone());
    let s1 = Expr::app(c.clone(), mx.clone());
    println!(
        "c x =?= c (mdata x): {:?}",
        check_def_eq(&env, &[], &t1, &s1, Budget::DEFAULT)
    );
    let t2 = Expr::app(c.clone(), Expr::app(c.clone(), x.clone()));
    let s2 = Expr::app(c.clone(), Expr::app(c.clone(), mx.clone()));
    println!(
        "c (c x) =?= c (c (mdata x)): {:?}",
        check_def_eq(&env, &[], &t2, &s2, Budget::DEFAULT)
    );
}
