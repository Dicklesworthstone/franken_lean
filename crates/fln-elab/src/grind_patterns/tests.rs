use super::*;
use fln_core::expr::{BinderInfo, FVarId, Literal, NatLit};
use fln_env::constants::{AxiomVal, ConstantVal};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn c(text: &str) -> Expr {
    Expr::const_(n(text), Vec::new())
}

fn fixture() -> (Environment, GrindPattern) {
    let forall = |label: &str, domain: Expr, body: Expr| {
        Expr::forall_e(n(label), domain, body, BinderInfo::Default)
    };
    let mut env = Environment::new();
    for (label, type_) in [
        ("A", Expr::sort(Level::one())),
        ("P", Expr::sort(Level::zero())),
        ("f", forall("x", c("A"), forall("y", c("A"), c("A")))),
        ("g", forall("x", c("A"), forall("y", c("A"), c("A")))),
        (
            "rule",
            forall(
                "x",
                c("A"),
                forall("y", c("A"), forall("h", c("P"), c("P"))),
            ),
        ),
    ] {
        env = env
            .add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: n(label),
                    level_params: vec![],
                    type_,
                },
                is_unsafe: false,
            }))
            .unwrap();
    }
    let row = GrindPattern {
        declaration: n("rule"),
        num_params: 3,
        data_params: 2,
        patterns: vec![Expr::app(
            Expr::app(c("f"), Expr::bvar(2).unwrap()),
            Expr::bvar(1).unwrap(),
        )],
    };
    (env, row)
}

#[test]
fn rows_remain_ordered_and_a_failed_batch_publishes_nothing() {
    let (env, first) = fixture();
    let second = GrindPattern {
        patterns: vec![Expr::app(
            Expr::app(c("g"), Expr::bvar(2).unwrap()),
            Expr::bvar(1).unwrap(),
        )],
        ..first.clone()
    };
    let registered = register(&env, &[first.clone(), second.clone(), first.clone()]).unwrap();
    assert_eq!(
        read(&registered).unwrap(),
        [first.clone(), second.clone(), first.clone()]
    );
    assert!(read(&env).unwrap().is_empty());
    let invalid = GrindPattern {
        declaration: n("missing"),
        ..second.clone()
    };
    assert_eq!(
        register(&registered, &[second, invalid]).err(),
        Some(Error::UnknownDeclaration(n("missing")))
    );
    assert_eq!(read(&registered).unwrap().len(), 3);
}

#[test]
fn full_telescope_indices_open_in_original_order_and_proof_indices_refuse() {
    let (env, row) = fixture();
    let registered = register(&env, std::slice::from_ref(&row)).unwrap();
    let rows = read(&registered).unwrap();
    let read = &rows[0];
    let x = Expr::fvar(FVarId(n("left")));
    let y = Expr::fvar(FVarId(n("right")));
    assert_eq!(
        read.patterns[0]
            .subst_loose(read.num_params - read.data_params, &[x.clone(), y.clone()])
            .unwrap(),
        Expr::app(Expr::app(c("f"), x), y)
    );
    let proof = GrindPattern {
        patterns: vec![Expr::app(
            Expr::app(c("f"), Expr::bvar(2).unwrap()),
            Expr::bvar(0).unwrap(),
        )],
        ..row.clone()
    };
    assert!(matches!(
        register(&env, &[proof]),
        Err(Error::Unsupported(_))
    ));
    let uncovered = GrindPattern {
        patterns: vec![Expr::app(
            Expr::app(c("f"), Expr::bvar(2).unwrap()),
            Expr::bvar(2).unwrap(),
        )],
        ..row
    };
    assert!(matches!(
        register(&env, &[uncovered]),
        Err(Error::Unsupported(_))
    ));
}

#[test]
fn unresolved_and_unavailable_pattern_references_cannot_be_hidden() {
    let (env, row) = fixture();
    for argument in [
        Expr::fvar(FVarId(n("unclosed"))),
        Expr::bvar(row.num_params).unwrap(),
        Expr::sort(Level::param(n("undeclaredUniverse"))),
    ] {
        let invalid = GrindPattern {
            patterns: vec![Expr::app(
                Expr::app(c("f"), argument),
                Expr::bvar(1).unwrap(),
            )],
            ..row.clone()
        };
        assert!(register(&env, &[invalid]).is_err());
    }
    let invalid = GrindPattern {
        patterns: vec![Expr::app(
            Expr::app(c("privateOrUnknown"), Expr::bvar(2).unwrap()),
            Expr::bvar(1).unwrap(),
        )],
        ..row
    };
    assert_eq!(
        register(&env, &[invalid]).err(),
        Some(Error::UnknownDeclaration(n("privateOrUnknown")))
    );
}

#[test]
fn malformed_journal_prefix_cannot_be_overwritten_by_a_valid_row() {
    let (env, row) = fixture();
    let bytes = codec::encode(&row).unwrap();
    for end in 0..bytes.len() {
        assert!(codec::decode(&bytes[..end]).is_err(), "truncated at {end}");
    }
    let mut suffix = bytes.clone();
    suffix.push(0);
    assert_eq!(codec::decode(&suffix), Err(Error::Malformed));
    let corrupted = env
        .register_extension(descriptor())
        .unwrap()
        .push_extension_entry(&journal_name(), suffix)
        .unwrap();
    assert_eq!(read(&corrupted), Err(Error::Malformed));
    assert_eq!(
        register(&corrupted, std::slice::from_ref(&row)).err(),
        Some(Error::Malformed)
    );
    assert!(read(&env).unwrap().is_empty());

    let mut forward_edge = MAGIC.to_vec();
    crate::instances::write_name(&row.declaration, &mut forward_edge).unwrap();
    for value in [row.num_params, row.data_params, 1, 1] {
        forward_edge.extend(value.to_le_bytes());
    }
    forward_edge.push(3); // The only expression node is an application.
    forward_edge.extend(0u32.to_le_bytes());
    forward_edge.extend(0u32.to_le_bytes()); // Both children refer to itself.
    assert_eq!(codec::decode(&forward_edge), Err(Error::Malformed));
}

#[test]
fn codec_round_trips_shared_nodes_literals_and_named_universes() {
    let (_, mut row) = fixture();
    let universe = Level::max(Level::one(), Level::param(n("u"))).unwrap();
    let shared = Expr::app(
        Expr::const_(n("polymorphic"), vec![universe.clone()]),
        Expr::sort(universe),
    );
    row.patterns = vec![
        Expr::app(shared.clone(), shared),
        Expr::app(
            c("natural"),
            Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![]))),
        ),
        Expr::app(
            c("natural"),
            Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![1, 2]))),
        ),
        Expr::app(c("string"), Expr::lit(Literal::Str("λ\n\0".to_owned()))),
    ];
    let encoded = codec::encode(&row).unwrap();
    assert_eq!(codec::decode(&encoded).unwrap(), row);
    assert_eq!(
        codec::encode(&codec::decode(&encoded).unwrap()).unwrap(),
        encoded
    );
}

#[test]
fn explicit_resource_bounds_remain_typed_and_do_not_publish() {
    let (env, row) = fixture();
    let too_many_parameters = GrindPattern {
        num_params: MAX_PARAMETERS + 1,
        ..row.clone()
    };
    assert_eq!(
        register(&env, &[too_many_parameters]).err(),
        Some(Error::Limit)
    );
    let too_many_patterns = GrindPattern {
        patterns: vec![row.patterns[0].clone(); MAX_PATTERNS + 1],
        ..row
    };
    assert_eq!(
        register(&env, &[too_many_patterns]).err(),
        Some(Error::Limit)
    );
    let oversized = env
        .register_extension(descriptor())
        .unwrap()
        .push_extension_entry(&journal_name(), vec![0; MAX_ENTRY_BYTES + 1])
        .unwrap();
    assert_eq!(read(&oversized), Err(Error::Limit));
    assert!(read(&env).unwrap().is_empty());
}

#[test]
fn constant_universe_argument_limit_is_symmetric() {
    let (_, mut row) = fixture();
    row.patterns = vec![Expr::const_(
        n("polymorphic"),
        vec![Level::zero(); codec::MAX_LEVEL_ARGUMENTS],
    )];
    let bytes = codec::encode(&row).unwrap();
    assert_eq!(codec::decode(&bytes).unwrap(), row);
    row.patterns = vec![Expr::const_(
        n("polymorphic"),
        vec![Level::zero(); codec::MAX_LEVEL_ARGUMENTS + 1],
    )];
    assert_eq!(codec::encode(&row), Err(Error::Limit));
}

#[test]
fn cumulative_registration_never_publishes_an_unreadable_journal() {
    let (env, row) = fixture();
    // Repeated expression handles share work during pre-encoding validation;
    // decoding reconstructs each pattern and must validate the full journal.
    let dense = GrindPattern {
        patterns: vec![row.patterns[0].clone(); MAX_PATTERNS],
        ..row
    };
    let admitted = register(&env, &vec![dense.clone(); 64]).unwrap();
    assert_eq!(read(&admitted).unwrap().len(), 64);
    assert_eq!(
        register(&env, &vec![dense; MAX_ROWS / 2]).err(),
        Some(Error::Limit)
    );
    assert!(read(&env).unwrap().is_empty());
}
