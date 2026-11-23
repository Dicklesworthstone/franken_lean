use super::*;
use fln_core::expr::{BinderInfo, ExprNode};
use fln_core::level::Level;
use fln_env::constants::{
    AxiomVal, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn c(text: &str) -> Expr {
    Expr::const_(n(text), Vec::new())
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn axiom(env: &Environment, name: &str, type_: Expr) -> Environment {
    env.add_decl(ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: Vec::new(),
            type_,
        },
        is_unsafe: false,
    }))
    .unwrap()
}

fn definition(env: &Environment, name: &str, type_: Expr, value: Expr) -> Environment {
    env.add_decl(ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: Vec::new(),
            type_,
        },
        value,
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    }))
    .unwrap()
}

fn wrap(lambda: bool, name: &str, domain: Expr, body: Expr, style: BinderInfo) -> Expr {
    if lambda {
        Expr::lam(n(name), domain, body, style)
    } else {
        Expr::forall_e(n(name), domain, body, style)
    }
}

fn eliminator(lambda: bool) -> Expr {
    let motive = Expr::forall_e(
        n("x"),
        c("A"),
        Expr::sort(Level::zero()),
        BinderInfo::Default,
    );
    wrap(
        lambda,
        "m",
        motive,
        wrap(
            lambda,
            "a",
            c("A"),
            wrap(
                lambda,
                "h",
                Expr::app(b(1), b(0)),
                if lambda { b(0) } else { Expr::app(b(2), b(1)) },
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    )
}

fn fixture() -> Environment {
    let env = axiom(&Environment::new(), "A", Expr::sort(Level::one()));
    let env = definition(&env, "ordinary", eliminator(false), eliminator(true));
    axiom(&env, "other", eliminator(false))
}

fn forged(env: &Environment, kind: TagKind, names: &[Name]) -> Environment {
    let mut payload = kind.magic().to_vec();
    payload.extend((names.len() as u32).to_le_bytes());
    for name in names {
        write_name(name, &mut payload).unwrap();
    }
    let env = if env.extension(&journal_name(kind)).is_some() {
        env.clone()
    } else {
        env.register_extension(descriptor(kind)).unwrap()
    };
    env.push_extension_entry(&journal_name(kind), payload)
        .unwrap()
}

#[test]
fn generated_tags_are_distinct_from_auxiliary_membership_and_atomic() {
    let env = fixture();
    let tagged = register_generated(&env, &[n("ordinary")]).unwrap();
    for kind in [TagKind::ElabAsElim, TagKind::SparseCasesOn] {
        assert_eq!(
            read(&tagged, kind).unwrap(),
            BTreeSet::from([n("ordinary")])
        );
        assert!(read(&env, kind).unwrap().is_empty());
    }
    assert!(
        crate::aux_recursors::AuxRecursors::read(&tagged)
            .unwrap()
            .is_empty()
    );
    // A user axiom may have the dependent telescope for elab_as_elim, but
    // the generator API cannot mark it as a sparse generated definition.
    let other = register_module(&env, TagKind::ElabAsElim, &[n("other")]).unwrap();
    assert!(
        read(&other, TagKind::ElabAsElim)
            .unwrap()
            .contains(&n("other"))
    );
    assert_eq!(
        register_generated(&env, &[n("other")]),
        Err(EliminatorTagError::NotDefinition(n("other")))
    );
    let env = definition(&env, "bad", Expr::sort(Level::one()), c("A"));
    assert_eq!(
        register_generated(&env, &[n("ordinary"), n("bad")]),
        Err(EliminatorTagError::InvalidEliminator(n("bad")))
    );
    assert!(
        env.extension(&journal_name(TagKind::SparseCasesOn))
            .is_none()
    );
    assert!(env.extension(&journal_name(TagKind::ElabAsElim)).is_none());
    assert_eq!(
        register_module(&env, TagKind::ElabAsElim, &[n("ordinary"), n("ordinary")]),
        Err(EliminatorTagError::Duplicate(n("ordinary")))
    );
    assert_eq!(
        read(
            &forged(&other, TagKind::ElabAsElim, &[n("other")]),
            TagKind::ElabAsElim
        ),
        Err(EliminatorTagError::Duplicate(n("other")))
    );
}

#[test]
fn header_validation_rejects_invalid_motives_and_optional_parameters() {
    let env = fixture();
    let zero_arity = Expr::forall_e(
        n("p"),
        Expr::sort(Level::zero()),
        Expr::forall_e(n("h"), b(0), b(1), BinderInfo::Default),
        BinderInfo::Default,
    );
    let optional = Expr::forall_e(
        n("m"),
        Expr::forall_e(
            n("a"),
            c("A"),
            Expr::sort(Level::zero()),
            BinderInfo::Default,
        ),
        Expr::forall_e(
            n("a"),
            Expr::app(Expr::app(c("optParam"), c("A")), c("a")),
            Expr::app(b(1), b(0)),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    let env = axiom(&env, "a", c("A"));
    let env = axiom(&env, "zeroArity", zero_arity);
    let env = axiom(&env, "optional", optional);
    let env = axiom(&env, "notEliminator", Expr::sort(Level::one()));
    for name in ["zeroArity", "optional", "notEliminator"] {
        assert_eq!(
            register_module(&env, TagKind::ElabAsElim, &[n(name)]),
            Err(EliminatorTagError::InvalidEliminator(n(name)))
        );
        assert_eq!(
            read(
                &forged(&env, TagKind::ElabAsElim, &[n(name)]),
                TagKind::ElabAsElim
            ),
            Err(EliminatorTagError::InvalidEliminator(n(name)))
        );
    }
    let mut no_work = 0;
    assert_eq!(
        validation::eliminator_type(&env, env.find(&n("ordinary")).unwrap(), &mut no_work),
        Err(EliminatorTagError::Limit)
    );
}

#[test]
fn telescope_aliases_are_normalized_and_later_opacity_is_unsupported() {
    let env = fixture();
    let env = definition(&env, "Header", Expr::sort(Level::one()), eliminator(false));
    let env = axiom(&env, "aliasElim", c("Header"));
    let env = register_module(&env, TagKind::ElabAsElim, &[n("aliasElim")]).unwrap();
    let cache = ElabAsElimCache::default();
    let type_ = cache.declared_type(&env, &n("aliasElim")).unwrap().unwrap();
    assert!(matches!(type_.node(), ExprNode::ForallE { .. }));
    assert_eq!(type_, eliminator(false));
    let opaque = crate::reducibility::register(
        &env,
        &n("Header"),
        crate::reducibility::Reducibility::Irreducible,
    )
    .unwrap();
    assert_eq!(
        cache.declared_type(&opaque, &n("aliasElim")),
        Err(EliminatorTagError::UnsupportedEliminator(n("aliasElim")))
    );
    // A failed read does not poison the earlier valid snapshot.
    assert!(
        cache
            .declared_type(&env, &n("aliasElim"))
            .unwrap()
            .is_some()
    );
    // Reducing the FINAL non-forall type does not replace it. Even a
    // reducible alias whose value is `m a` cannot pass as that motive head.
    let motive = Expr::forall_e(
        n("a"),
        c("A"),
        Expr::sort(Level::zero()),
        BinderInfo::Default,
    );
    let result_type = Expr::forall_e(
        n("m"),
        motive.clone(),
        Expr::forall_e(
            n("a"),
            c("A"),
            Expr::sort(Level::zero()),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let result_value = Expr::lam(
        n("m"),
        motive.clone(),
        Expr::lam(n("a"), c("A"), Expr::app(b(1), b(0)), BinderInfo::Default),
        BinderInfo::Default,
    );
    let env = definition(&env, "Result", result_type, result_value);
    let alias_result_type = Expr::forall_e(
        n("m"),
        motive,
        Expr::forall_e(
            n("a"),
            c("A"),
            Expr::forall_e(
                n("h"),
                Expr::app(b(1), b(0)),
                Expr::app(Expr::app(c("Result"), b(2)), b(1)),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    let env = axiom(&env, "aliasResult", alias_result_type);
    assert_eq!(
        register_module(&env, TagKind::ElabAsElim, &[n("aliasResult")]),
        Err(EliminatorTagError::InvalidEliminator(n("aliasResult")))
    );
}

#[test]
fn cached_tags_do_not_cross_equal_size_sibling_declarations_or_hidden_worlds() {
    let env = fixture();
    let tagged = register_module(&env, TagKind::ElabAsElim, &[n("ordinary")]).unwrap();
    let cache = ElabAsElimCache::default();
    assert!(
        cache
            .declared_type(&tagged, &n("ordinary"))
            .unwrap()
            .is_some()
    );
    let sibling = axiom(&Environment::new(), "A", Expr::sort(Level::one()));
    let sibling = axiom(&sibling, "ordinary", Expr::sort(Level::one()));
    let sibling = axiom(&sibling, "other", eliminator(false));
    let sibling = forged(&sibling, TagKind::ElabAsElim, &[n("ordinary")]);
    assert_eq!(sibling.len(), tagged.len());
    assert_eq!(
        cache.declared_type(&sibling, &n("ordinary")),
        Err(EliminatorTagError::InvalidEliminator(n("ordinary")))
    );
    let hidden = forged(&Environment::new(), TagKind::ElabAsElim, &[n("ordinary")]);
    assert_eq!(
        read(&hidden, TagKind::ElabAsElim),
        Err(EliminatorTagError::UnknownDeclaration(n("ordinary")))
    );
    let hidden = hidden.with_imported_metadata_validation(&tagged);
    assert!(read(&hidden, TagKind::ElabAsElim).unwrap().is_empty());
    assert!(
        cache
            .declared_type(&hidden, &n("ordinary"))
            .unwrap()
            .is_none()
    );
    let new_row = forged(&hidden, TagKind::ElabAsElim, &[n("other")]);
    assert_eq!(
        read(&new_row, TagKind::ElabAsElim),
        Err(EliminatorTagError::UnknownDeclaration(n("other")))
    );
}

#[test]
fn malformed_and_foreign_journals_never_become_empty_membership() {
    let env = fixture();
    for kind in [TagKind::ElabAsElim, TagKind::SparseCasesOn] {
        let malformed = env
            .register_extension(descriptor(kind))
            .unwrap()
            .push_extension_entry(&journal_name(kind), vec![0, 1, 2])
            .unwrap();
        assert_eq!(read(&malformed, kind), Err(EliminatorTagError::Malformed));
        let unknown = forged(&env, kind, &[n("missing")]);
        assert_eq!(
            read(&unknown, kind),
            Err(EliminatorTagError::UnknownDeclaration(n("missing")))
        );
        let other = if kind == TagKind::ElabAsElim {
            TagKind::SparseCasesOn
        } else {
            TagKind::ElabAsElim
        };
        assert!(!supports(kind, &descriptor(other)));
    }
}

#[test]
fn visible_elaboration_cannot_recover_an_unexposed_header_body_from_metadata() {
    let env = fixture();
    let env = definition(&env, "Header", Expr::sort(Level::one()), eliminator(false));
    let env = axiom(&env, "aliasElim", c("Header"));
    let complete = register_module(&env, TagKind::ElabAsElim, &[n("aliasElim")]).unwrap();
    let public = axiom(&Environment::new(), "A", Expr::sort(Level::one()));
    let public = axiom(&public, "Header", Expr::sort(Level::one()));
    let public = axiom(&public, "aliasElim", c("Header"));
    let public = forged(&public, TagKind::ElabAsElim, &[n("aliasElim")]);
    let public = public.with_imported_metadata_validation(&complete);
    assert!(
        read(&public, TagKind::ElabAsElim)
            .unwrap()
            .contains(&n("aliasElim"))
    );
    let cache = ElabAsElimCache::default();
    assert!(
        cache
            .declared_type(&complete, &n("aliasElim"))
            .unwrap()
            .is_some()
    );
    assert_eq!(
        cache.declared_type(&public, &n("aliasElim")),
        Err(EliminatorTagError::UnsupportedEliminator(n("aliasElim")))
    );
}
