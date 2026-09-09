//! The ordinary one-field Inhabited class used by native instance elaboration.
//! Every row remains a candidate for K1 and the independent checker.
use super::*;
use fln_core::expr::{FVarId, Literal, NatLit};
use fln_env::constants::{DefinitionSafety, DefinitionVal, ReducibilityHints};

fn name(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn local(s: &str) -> Expr {
    Expr::fvar(FVarId(name(s)))
}
fn apply(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}
fn bind(s: &str, domain: Expr, body: Expr, style: BinderInfo, lambda: bool) -> Expr {
    let body = body
        .abstract_fvar(&FVarId(name(s)), 0)
        .expect("fixed Inhabited telescope");
    if lambda {
        Expr::lam(name(s), domain, body, style)
    } else {
        Expr::forall_e(name(s), domain, body, style)
    }
}

pub fn inhabited_seed_declaration() -> Declaration {
    let u_name = name("u");
    let v_name = name("u_1");
    let u = Level::param(u_name.clone());
    let v = Level::param(v_name.clone());
    let alpha = local("α");
    let field = local("default");
    let motive = local("motive");
    let minor = local("mk");
    let major = local("t");
    let inhabited = |a| Expr::app(Expr::const_(name("Inhabited"), vec![u.clone()]), a);
    let constructor = |a, x| apply(Expr::const_(name("Inhabited.mk"), vec![u.clone()]), [a, x]);
    let explicit = BinderInfo::Default;
    let implicit = BinderInfo::Implicit;
    let motive_type = bind(
        "t",
        inhabited(alpha.clone()),
        Expr::sort(v.clone()),
        explicit,
        false,
    );
    let minor_type = bind(
        "default",
        alpha.clone(),
        Expr::app(motive.clone(), constructor(alpha.clone(), field.clone())),
        explicit,
        false,
    );
    let rec_type = bind(
        "α",
        Expr::sort(u.clone()),
        bind(
            "motive",
            motive_type.clone(),
            bind(
                "mk",
                minor_type.clone(),
                bind(
                    "t",
                    inhabited(alpha.clone()),
                    Expr::app(motive.clone(), major),
                    explicit,
                    false,
                ),
                explicit,
                false,
            ),
            implicit,
            false,
        ),
        implicit,
        false,
    );
    let rhs = bind(
        "α",
        Expr::sort(u.clone()),
        bind(
            "motive",
            motive_type,
            bind(
                "mk",
                minor_type,
                bind(
                    "default",
                    alpha.clone(),
                    Expr::app(minor, field.clone()),
                    explicit,
                    true,
                ),
                explicit,
                true,
            ),
            explicit,
            true,
        ),
        explicit,
        true,
    );
    Declaration::Inductive(InductiveBlock {
        types: vec![InductiveVal {
            base: ConstantVal {
                name: name("Inhabited"),
                level_params: vec![u_name.clone()],
                type_: bind(
                    "α",
                    Expr::sort(u.clone()),
                    Expr::sort(Level::max(Level::one(), u.clone()).expect("fixed max")),
                    explicit,
                    false,
                ),
            },
            num_params: 1,
            num_indices: 0,
            all: vec![name("Inhabited")],
            ctors: vec![name("Inhabited.mk")],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }],
        ctors: vec![ConstructorVal {
            base: ConstantVal {
                name: name("Inhabited.mk"),
                level_params: vec![u_name.clone()],
                type_: bind(
                    "α",
                    Expr::sort(u.clone()),
                    bind(
                        "default",
                        alpha.clone(),
                        inhabited(alpha.clone()),
                        explicit,
                        false,
                    ),
                    implicit,
                    false,
                ),
            },
            induct: name("Inhabited"),
            cidx: 0,
            num_params: 1,
            num_fields: 1,
            is_unsafe: false,
        }],
        recursors: vec![RecursorVal {
            base: ConstantVal {
                name: name("Inhabited.rec"),
                level_params: vec![v_name, u_name],
                type_: rec_type,
            },
            all: vec![name("Inhabited")],
            num_params: 1,
            num_indices: 0,
            num_motives: 1,
            num_minors: 1,
            rules: vec![RecursorRule {
                ctor: name("Inhabited.mk"),
                nfields: 1,
                rhs,
            }],
            k: false,
            is_unsafe: false,
        }],
    })
}

pub fn default_seed_declaration(qualified: bool) -> Declaration {
    let u_name = name("u");
    let u = Level::param(u_name.clone());
    let alpha = local("α");
    let domain = Expr::app(
        Expr::const_(name("Inhabited"), vec![u.clone()]),
        alpha.clone(),
    );
    let n = name(if qualified {
        "Inhabited.default"
    } else {
        "default"
    });
    let type_ = bind(
        "α",
        Expr::sort(u.clone()),
        bind(
            "self",
            domain.clone(),
            alpha.clone(),
            BinderInfo::InstImplicit,
            false,
        ),
        BinderInfo::Implicit,
        false,
    );
    let projected = if qualified {
        Expr::proj(name("Inhabited"), 0, local("self"))
    } else {
        apply(
            Expr::const_(name("Inhabited.default"), vec![u.clone()]),
            [alpha, local("self")],
        )
    };
    let value = bind(
        "α",
        Expr::sort(u),
        bind("self", domain, projected, BinderInfo::InstImplicit, true),
        BinderInfo::Implicit,
        true,
    );
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: n.clone(),
            level_params: vec![u_name],
            type_,
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![n],
    })
}

pub fn scalar_inhabited_seed_declaration(scalar: &str) -> Declaration {
    let (n, value) = match scalar {
        "Nat" => (
            "instInhabitedNat",
            Expr::lit(Literal::Nat(NatLit::from_u64(0))),
        ),
        "String" => (
            "instInhabitedString",
            Expr::lit(Literal::Str(String::new())),
        ),
        "Bool" => (
            "instInhabitedBool",
            Expr::const_(name("Bool.false"), vec![]),
        ),
        _ => unreachable!("fixed source seed inventory"),
    };
    let alpha = Expr::const_(name(scalar), vec![]);
    let type_ = Expr::app(
        Expr::const_(name("Inhabited"), vec![Level::one()]),
        alpha.clone(),
    );
    let value = apply(
        Expr::const_(name("Inhabited.mk"), vec![Level::one()]),
        [alpha, value],
    );
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name(n),
            level_params: vec![],
            type_,
        },
        value,
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![name(n)],
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn inhabited_eliminator_is_regenerated_not_trusted() {
        let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
        let mut candidate = inhabited_seed_declaration();
        let result = fln_kernel::check(&Environment::new(), &candidate, budget);
        assert!(
            matches!(
                result,
                Outcome::Complete(fln_kernel::verdict::Verdict::Accepted { .. })
            ),
            "{result:?}"
        );
        let Declaration::Inductive(block) = &mut candidate else {
            unreachable!()
        };
        block.recursors[0].rules[0].rhs = Expr::sort(Level::zero());
        assert!(matches!(
            fln_kernel::check(&Environment::new(), &candidate, budget),
            Outcome::Complete(fln_kernel::verdict::Verdict::Rejected { .. })
        ));
    }
}
