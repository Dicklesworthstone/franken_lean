use super::*;
use fln_core::level::Level;
use fln_core::options::KVMap;
use fln_env::constants::{AxiomVal, ConstantVal, DefinitionVal};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn c(text: &str) -> Expr {
    Expr::const_(n(text), vec![])
}

fn ty() -> Expr {
    Expr::sort(Level::one())
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn axiom(env: &Environment, name: &str, type_: Expr) -> Environment {
    env.add_decl(ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_,
        },
        is_unsafe: false,
    }))
    .unwrap()
}

fn abbrev(env: &Environment, name: &str, type_: Expr, value: Expr) -> Environment {
    env.add_decl(ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_,
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    }))
    .unwrap()
}

fn fixture() -> Environment {
    let env = axiom(&Environment::new(), "C", ty());
    let env = register_class(&env, &n("C")).unwrap();
    axiom(&axiom(&env, "first", c("C")), "second", c("C"))
}

#[test]
fn suffix_ownership_preserves_repeated_imported_candidates_and_exact_work() {
    let empty = fixture();
    let base = super::super::register(&empty, &n("first"), 2000).unwrap();
    let env = super::super::register(&base, &n("first"), 100).unwrap();
    let env = super::super::register(&env, &n("second"), 1000).unwrap();
    let env = super::super::register(&env, &n("second"), 1000).unwrap();
    let root = env.logical_root(&KVMap::new());
    let rows = registrations(&base, &env, usize::MAX).unwrap();
    assert_eq!(
        rows.entries
            .iter()
            .map(|row| (
                row.candidate.declaration.clone(),
                row.candidate.priority,
                row.candidate.order,
            ))
            .collect::<Vec<_>>(),
        [
            (n("first"), 100, 1),
            (n("second"), 1000, 2),
            (n("second"), 1000, 3),
        ]
    );
    assert!(rows.bytes_examined > 0);
    assert_eq!(registrations(&base, &env, rows.work).unwrap(), rows);
    assert_eq!(
        registrations(&base, &env, rows.work - 1),
        Err(InstanceRegistryError::Limit)
    );
    assert_eq!(
        registrations(&env, &env, 0).unwrap(),
        Registrations::default()
    );
    assert_eq!(
        registrations(&env, &base, usize::MAX),
        Err(InstanceRegistryError::Malformed)
    );
    let changed = super::super::append(&empty, &n("first"), 1999).unwrap();
    let changed = super::super::append(&changed, &n("second"), 1000).unwrap();
    assert_eq!(
        registrations(&base, &changed, usize::MAX),
        Err(InstanceRegistryError::Malformed)
    );
    assert_eq!(env.logical_root(&KVMap::new()), root);
}

#[test]
fn metered_heads_reduce_class_abbreviations_and_beta_under_forall_binders() {
    let env = fixture();
    let env = axiom(&env, "A", ty());
    // Keep R ignored := R exercises a nonzero de Bruijn lookup. The
    // telescope inside ForallAlias exercises suspended substitution under Pi.
    let two_types = Expr::forall_e(
        n("R"),
        ty(),
        Expr::forall_e(n("ignored"), ty(), ty(), BinderInfo::Default),
        BinderInfo::Default,
    );
    let keep = Expr::lam(
        n("R"),
        ty(),
        Expr::lam(n("ignored"), ty(), b(1), BinderInfo::Default),
        BinderInfo::Default,
    );
    let env = abbrev(&env, "Keep", two_types, keep);
    let env = abbrev(
        &env,
        "ForallAlias",
        Expr::forall_e(n("R"), ty(), ty(), BinderInfo::Default),
        Expr::lam(
            n("R"),
            ty(),
            Expr::forall_e(n("x"), c("A"), b(1), BinderInfo::Default),
            BinderInfo::Default,
        ),
    );
    let keep_c = Expr::app(Expr::app(c("Keep"), c("C")), b(0));
    let candidate = Expr::forall_e(
        n("X"),
        ty(),
        Expr::app(c("ForallAlias"), keep_c),
        BinderInfo::Implicit,
    );
    let env = axiom(&env, "throughAliases", candidate);
    assert_eq!(
        validate_instance(&env, &n("throughAliases")).unwrap(),
        n("C")
    );
    let result = super::super::append(&env, &n("throughAliases"), 1000).unwrap();
    let rows = registrations(&env, &result, 10_000).unwrap();
    assert_eq!(rows.entries[0].class, n("C"));
    assert_eq!(
        registrations(&env, &result, rows.work - 1),
        Err(InstanceRegistryError::Limit)
    );
}

#[test]
fn candidate_reduction_is_metered_and_unrelated_instance_types_are_not_normalized() {
    let env = fixture();
    // Adversarial raw environment metadata: a cyclic abbreviation must spend
    // caller work, including when its journal payload is only a short name.
    let env = abbrev(&env, "Loop", ty(), c("Loop"));
    let env = axiom(&env, "looping", c("Loop"));
    let row = instances::instance_payload(1, &n("C"), &n("looping"), 1000, None).unwrap();
    let env = instances::append(&env, row).unwrap();
    let result = super::super::append(&env, &n("first"), 1000).unwrap();
    let rows = registrations(&env, &result, 1000).unwrap();
    assert_eq!(rows.entries[0].class, n("C"));
    let result = super::super::append(&env, &n("looping"), 1000).unwrap();
    assert_eq!(
        registrations(&env, &result, 1000),
        Err(InstanceRegistryError::Limit)
    );

    let mut telescope = c("C");
    for _ in 0..2000 {
        telescope = Expr::forall_e(n("x"), ty(), telescope, BinderInfo::Default);
    }
    let env = axiom(&fixture(), "long", telescope);
    let result = super::super::append(&env, &n("long"), 1000).unwrap();
    assert_eq!(
        registrations(&env, &result, 1000),
        Err(InstanceRegistryError::Limit)
    );
    assert_eq!(
        registrations(&env, &result, 5000).unwrap().entries[0].class,
        n("C")
    );
}
