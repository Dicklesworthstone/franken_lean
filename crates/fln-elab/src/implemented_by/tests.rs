use super::*;
use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_core::options::KVMap;
use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};

fn n(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn axiom(name: Name, params: Vec<Name>, type_: Expr) -> ConstantInfo {
    ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name,
            level_params: params,
            type_,
        },
        is_unsafe: false,
    })
}

fn simple() -> Environment {
    ["a", "b", "c"]
        .into_iter()
        .fold(Environment::new(), |env, label| {
            env.add_decl(axiom(n(label), vec![], Expr::sort(Level::one())))
                .unwrap()
        })
}

fn polymorphic(universe: &str, binder: &str, info: BinderInfo) -> Expr {
    Expr::forall_e(
        n(binder),
        Expr::sort(Level::param(n(universe))),
        Expr::forall_e(n("x"), Expr::bvar(0).unwrap(), Expr::bvar(1).unwrap(), info),
        info,
    )
}

#[test]
fn signature_validation_renames_universes_and_ignores_only_binder_annotations() {
    let source = polymorphic("u", "A", BinderInfo::Implicit);
    let target = polymorphic("v", "B", BinderInfo::Default);
    assert_ne!(source, target);
    let base = Environment::new()
        .add_decl(axiom(n("source"), vec![n("u")], source))
        .unwrap()
        .add_decl(axiom(n("target"), vec![n("v")], target))
        .unwrap();
    let env = register(&base, &n("source"), &n("target")).unwrap();
    assert_eq!(
        ImplementedByTable::read(&env)
            .unwrap()
            .implementation(&n("source")),
        Some(&n("target"))
    );
    for (name, info) in base.constants() {
        assert_eq!(
            env.find(name),
            Some(info),
            "metadata cannot change a logical type or body"
        );
    }
    assert_eq!(env.len(), base.len());
    assert_ne!(
        env.logical_root(&KVMap::new()),
        base.logical_root(&KVMap::new())
    );
}

#[test]
fn incompatible_types_universe_counts_and_self_replacements_refuse_without_a_successor() {
    let base = simple()
        .add_decl(axiom(n("different"), vec![], Expr::sort(Level::zero())))
        .unwrap()
        .add_decl(axiom(
            n("universes"),
            vec![n("u")],
            Expr::sort(Level::one()),
        ))
        .unwrap();
    for target in ["different", "universes"] {
        assert!(matches!(
            register(&base, &n("a"), &n(target)),
            Err(ImplementedByError::InvalidSignature { .. })
        ));
    }
    for (source, target, missing) in [("a", "missing", "missing"), ("missing", "a", "missing")] {
        assert_eq!(
            register(&base, &n(source), &n(target)),
            Err(ImplementedByError::UnknownDeclaration(n(missing)))
        );
    }
    assert_eq!(
        register(&base, &n("a"), &n("a")),
        Err(ImplementedByError::SelfImplementation(n("a")))
    );
    assert!(base.extension(&journal_name()).is_none());
}

#[test]
fn signature_comparison_does_not_reduce_lets_or_drop_metadata() {
    let type_ = Expr::sort(Level::one());
    let with_let = Expr::let_e(
        n("unused"),
        Expr::sort(Level::one()),
        Expr::sort(Level::zero()),
        type_.clone(),
        true,
    );
    let base = simple()
        .add_decl(axiom(n("letType"), vec![], with_let))
        .unwrap()
        .add_decl(axiom(
            n("markedType"),
            vec![],
            Expr::mdata(KVMap::new(), type_),
        ))
        .unwrap();
    for target in ["letType", "markedType"] {
        assert!(matches!(
            register(&base, &n("a"), &n(target)),
            Err(ImplementedByError::InvalidSignature { .. })
        ));
    }
}

#[test]
fn chains_resolve_deterministically_and_cycles_never_expose_a_partial_table() {
    let base = simple();
    let env = register(
        &register(&base, &n("a"), &n("b")).unwrap(),
        &n("b"),
        &n("c"),
    )
    .unwrap();
    let table = ImplementedByTable::read(&env).unwrap();
    assert_eq!(table.get(&n("a")), Some(&n("b")));
    assert_eq!(table.implementation(&n("a")), Some(&n("c")));
    assert_eq!(table.implementation(&n("b")), Some(&n("c")));
    assert_eq!(table.implementation(&n("c")), None);
    let cycle = register(&env, &n("c"), &n("a")).unwrap();
    assert_eq!(
        ImplementedByTable::read(&cycle),
        Err(ImplementedByError::Cycle(n("a")))
    );
    let replaced = register(&env, &n("a"), &n("c")).unwrap();
    assert_eq!(
        ImplementedByTable::read(&replaced).unwrap().get(&n("a")),
        Some(&n("c"))
    );
    assert_eq!(ImplementedByTable::read(&env).unwrap(), table);
}

#[test]
fn malformed_unknown_and_overwritten_rows_are_all_checked() {
    let base = simple();
    let good = register(&base, &n("a"), &n("b")).unwrap();
    let payload = encode_entry(&n("a"), &n("b")).unwrap();
    for end in 0..payload.len() {
        assert!(decode_entry(&payload[..end]).is_err());
    }
    let mut trailing = payload;
    trailing.push(0);
    assert_eq!(decode_entry(&trailing), Err(ImplementedByError::Malformed));
    let bad = good.push_extension_entry(&journal_name(), vec![0]).unwrap();
    let hidden = register(&bad, &n("a"), &n("c")).unwrap();
    assert_eq!(
        ImplementedByTable::read(&hidden),
        Err(ImplementedByError::Malformed)
    );
    let absent = good
        .push_extension_entry(
            &journal_name(),
            encode_entry(&n("a"), &n("absent")).unwrap(),
        )
        .unwrap();
    assert_eq!(
        ImplementedByTable::read(&absent),
        Err(ImplementedByError::UnknownDeclaration(n("absent")))
    );
    let mut foreign = descriptor();
    foreign.provenance = PayloadProvenance::Opaque;
    assert_eq!(
        ImplementedByTable::read(&base.register_extension(foreign).unwrap()),
        Err(ImplementedByError::Malformed)
    );
}

#[test]
fn exact_name_components_and_caller_budgets_survive_native_journal_replay() {
    let numeric = Name::num(n("part"), 7);
    let string = Name::str(n("part"), "7");
    let dotted = Name::str(Name::anonymous(), "part.7");
    let base = [numeric.clone(), string.clone(), dotted.clone()]
        .into_iter()
        .fold(Environment::new(), |env, name| {
            env.add_decl(axiom(name, vec![], Expr::sort(Level::one())))
                .unwrap()
        });
    let env = register(&base, &numeric, &string).unwrap();
    let env = register(&env, &string, &dotted).unwrap();
    let table = ImplementedByTable::read(&env).unwrap();
    assert_eq!(table.len(), 2);
    assert_eq!(table.implementation(&numeric), Some(&dotted));
    assert_eq!(
        ImplementedByTable::read_metered(&env, |_| Err("caller stopped")),
        Err(ImplementedByReadError::Budget("caller stopped"))
    );
    let mut calls = 0;
    let stopped = ImplementedByTable::read_metered(&env, |_| {
        calls += 1;
        if calls > 4 {
            Err("during validation")
        } else {
            Ok(())
        }
    });
    assert_eq!(
        stopped,
        Err(ImplementedByReadError::Budget("during validation"))
    );
    assert!(ImplementedByTable::read(&base).unwrap().is_empty());
}
