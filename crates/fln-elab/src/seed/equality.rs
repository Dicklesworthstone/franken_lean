//! Equality for the source prelude. This is the ordinary indexed inductive
//! block, not an axiom asserting equality or an alternate admission path.
//!
//! Shapes follow the pinned Init.Eq block also exercised by the independent
//! checker. K1 regenerates and checks the eliminator before publication.

use super::*;

pub fn eq_seed_declaration() -> Declaration {
    let name = |s: &str| Name::from_components(s.split('.'));
    let eq = name("Eq");
    let refl = name("Eq.refl");
    let rec = name("Eq.rec");
    let u_name = name("u");
    let v_name = name("u_1");
    let u = Level::param(u_name.clone());
    let v = Level::param(v_name.clone());
    let bv = |i| Expr::bvar(i).expect("fixed equality telescope index");
    let pi = |s: &str, style, domain, body| Expr::forall_e(name(s), domain, body, style);
    let eq_at = |a, x, y| Expr::app(Expr::app(Expr::app(Expr::const_(eq.clone(), vec![v.clone()]), a), x), y);
    let refl_at = |a, x| Expr::app(Expr::app(Expr::const_(refl.clone(), vec![v.clone()]), a), x);
    let implicit = BinderInfo::Implicit;
    let explicit = BinderInfo::Default;
    let type_ = pi("α", implicit, Expr::sort(v.clone()),
        pi("a", explicit, bv(0), pi("b", explicit, bv(1), Expr::sort(Level::zero()))));
    let refl_type = pi("α", implicit, Expr::sort(v.clone()),
        pi("a", explicit, bv(0), eq_at(bv(1), bv(0), bv(0))));
    let motive_type = pi("b", explicit, bv(1),
        pi("t", explicit, eq_at(bv(2), bv(1), bv(0)), Expr::sort(u.clone())));
    let minor_type = Expr::app(Expr::app(bv(0), bv(1)), refl_at(bv(2), bv(1)));
    let result = Expr::app(Expr::app(bv(3), bv(1)), bv(0));
    let rec_type = pi("α", implicit, Expr::sort(v.clone()),
        pi("a", implicit, bv(0),
            pi("motive", implicit, motive_type.clone(),
                pi("refl", explicit, minor_type.clone(),
                    pi("b", implicit, bv(3),
                        pi("t", explicit, eq_at(bv(4), bv(3), bv(0)), result))))));
    let rhs = Expr::lam(name("α"), Expr::sort(v),
        Expr::lam(name("a"), bv(0),
            Expr::lam(name("motive"), motive_type,
                Expr::lam(name("refl"), minor_type, bv(0), explicit), explicit), explicit), implicit);
    Declaration::Inductive(InductiveBlock {
        types: vec![InductiveVal {
            base: ConstantVal { name: eq.clone(), level_params: vec![v_name.clone()], type_ },
            num_params: 2, num_indices: 1, all: vec![eq.clone()], ctors: vec![refl.clone()],
            num_nested: 0, is_rec: false, is_unsafe: false, is_reflexive: false,
        }],
        ctors: vec![ConstructorVal {
            base: ConstantVal { name: refl.clone(), level_params: vec![v_name.clone()], type_: refl_type },
            induct: eq.clone(), cidx: 0, num_params: 2, num_fields: 0, is_unsafe: false,
        }],
        recursors: vec![RecursorVal {
            base: ConstantVal { name: rec, level_params: vec![u_name, v_name], type_: rec_type },
            all: vec![eq], num_params: 2, num_indices: 1, num_motives: 1, num_minors: 1,
            rules: vec![RecursorRule { ctor: refl, nfields: 0, rhs }], k: true, is_unsafe: false,
        }],
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_kernel::{check, verdict::Verdict};

    #[test]
    fn equality_is_an_ordinary_kernel_checked_indexed_inductive() {
        let budget = Budget::for_stack_bytes(1024 * 1024);
        let declaration = eq_seed_declaration();
        let result = check(&Environment::new(), &declaration, budget);
        assert!(matches!(result, Outcome::Complete(Verdict::Accepted { .. })), "{result:?}");
        let Declaration::Inductive(block) = declaration else { panic!("equality must not be axiomatic"); };
        assert_eq!(block.types[0].num_indices, 1);
        assert_eq!(block.types[0].num_params, 2);
        assert_eq!(block.ctors[0].num_fields, 0);
        assert!(block.recursors[0].k);
    }

    #[test]
    fn forged_equality_eliminator_is_rejected_by_regeneration() {
        let Declaration::Inductive(mut block) = eq_seed_declaration() else { unreachable!() };
        block.recursors[0].rules[0].rhs = Expr::sort(Level::zero());
        let result = check(&Environment::new(), &Declaration::Inductive(block), Budget::for_stack_bytes(1024 * 1024));
        assert!(matches!(result, Outcome::Complete(Verdict::Rejected { .. })), "{result:?}");
    }
}
