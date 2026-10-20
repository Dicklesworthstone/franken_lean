use super::*;
use fln_core::level::Level;

#[test]
fn equality_transport_requires_every_canonical_family_object() {
    for mutation in 0..8 {
        let Declaration::Inductive(mut block) = fln_elab::seed::eq_seed_declaration() else {
            panic!("equality block");
        };
        match mutation {
            0 => {}
            1 => block.types[0].num_indices += 1,
            2 => block.ctors[0].num_fields += 1,
            3 => block.recursors[0].rules[0].rhs = nat::literal(0),
            4 => block.recursors[0].k = false,
            5 => block.recursors[0].base.level_params.swap(0, 1),
            6 => block.recursors[0].base.type_ = Expr::sort(Level::zero()),
            _ => block.types[0].is_unsafe = true,
        }
        let mut environment = Environment::new();
        for value in block.types {
            environment = environment.add_decl(ConstantInfo::Induct(value)).unwrap();
        }
        for value in block.ctors {
            environment = environment.add_decl(ConstantInfo::Ctor(value)).unwrap();
        }
        for value in block.recursors {
            environment = environment.add_decl(ConstantInfo::Rec(value)).unwrap();
        }
        let mut prep = Preparation::new(&environment, IngressLimits::default());
        assert_eq!(prep.check_equality_family().is_ok(), mutation == 0);
        assert_eq!(prep.equality_family_checked, mutation == 0);
        assert!(prep.lambdas.is_empty());
        assert!(prep.constructors.is_empty());
        if mutation == 0 {
            let mut bounded = Preparation::new(
                &environment,
                IngressLimits {
                    max_nodes: 1,
                    ..IngressLimits::default()
                },
            );
            assert!(matches!(
                bounded.check_equality_family(),
                Err(IngressError::ResourceLimit { .. })
            ));
            assert!(!bounded.equality_family_checked);
        }
    }
    assert!(
        Preparation::new(&Environment::new(), IngressLimits::default())
            .check_equality_family()
            .is_err()
    );
}

#[test]
fn equal_machine_categories_do_not_authorize_a_representation_changing_cast() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[b"structure Left where value : Nat\nstructure Right where value : String"],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
    let left = Expr::const_(name("Left"), vec![]);
    let right = Expr::const_(name("Right"), vec![]);
    // Both are FIR Constructor, but their field layouts and types differ.
    assert_eq!(
        prep.value_type(&left).unwrap(),
        Some(ValueType::Constructor)
    );
    assert_eq!(
        prep.value_type(&right).unwrap(),
        Some(ValueType::Constructor)
    );
    let motive = Expr::lam(
        Name::anonymous(),
        Expr::sort(Level::one()),
        Expr::lam(
            Name::anonymous(),
            Expr::sort(Level::zero()),
            Expr::bvar(1).unwrap(),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let args = [
        Expr::sort(Level::one()),
        left,
        motive,
        Expr::app(Expr::const_(name("Left.mk"), vec![]), nat::literal(42)),
        right,
        Expr::const_(name("Bool.false"), vec![]),
    ];
    // Deliberately exercise the erasure guard with fabricated post-admission
    // evidence; public checking must reject such evidence before this point.
    assert!(
        prep.equality_transport(
            &Expr::const_(
                name("Eq.rec"),
                vec![Level::one(), Level::succ(Level::one()).unwrap()]
            ),
            &args
        )
        .is_err()
    );
}

#[test]
fn boxed_type_refinements_keep_the_payload_interface_and_typed_result_boundary() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
    let boxed = prep.enable_boxed_type().unwrap();
    let nat = Expr::const_(name("Nat"), vec![]);
    let callback = Expr::forall_e(name("n"), nat.clone(), nat.clone(), BinderInfo::Default);
    let lambda = Expr::lam(
        name("n"),
        nat.clone(),
        Expr::bvar(0).unwrap(),
        BinderInfo::Default,
    );
    let recursor = Expr::const_(
        name("Eq.rec"),
        vec![Level::one(), Level::succ(Level::one()).unwrap()],
    );
    let motive = Expr::lam(
        name("A"),
        Expr::sort(Level::one()),
        Expr::lam(
            name("proof"),
            Expr::sort(Level::zero()),
            Expr::bvar(1).unwrap(),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let arguments = |before: Expr, after: Expr, value: Expr| {
        [
            Expr::sort(Level::one()),
            before,
            motive.clone(),
            value,
            after,
            Expr::const_(name("Bool.false"), vec![]),
        ]
    };

    // These private-ingress probes inspect the representation boundary with
    // synthetic proof metadata. The source integration tests establish that
    // real checked Type refinements reach it; no public checker accepts this
    // deliberately fabricated proof.
    let boxed_lambda = prep
        .equality_transport(
            &recursor,
            &arguments(callback.clone(), boxed.clone(), lambda.clone()),
        )
        .unwrap()
        .unwrap();
    let ExprNode::LetE { type_, value, .. } = boxed_lambda.node() else {
        panic!("boxing keeps a typed value binding")
    };
    assert_eq!(*type_, boxed);
    let ExprNode::LetE { type_, value, .. } = value.node() else {
        panic!("a literal callback must retain its concrete interface")
    };
    assert_eq!(*type_, callback);
    assert_eq!(*value, lambda);

    for concrete in [nat, callback] {
        let unboxed = prep
            .equality_transport(
                &recursor,
                &arguments(boxed.clone(), concrete.clone(), Expr::bvar(0).unwrap()),
            )
            .unwrap()
            .unwrap();
        let ExprNode::LetE { type_, value, .. } = unboxed.node() else {
            panic!("unboxing keeps a typed result binding")
        };
        assert_eq!(*type_, concrete);
        assert_eq!(*value, Expr::bvar(0).unwrap());
    }

    // Enabling the boxed carrier does not authorize two concrete layouts,
    // an unsupported payload type, or value-level endpoint erasure.
    for (before, after, carrier) in [
        (
            Expr::const_(name("Nat"), vec![]),
            Expr::const_(name("String"), vec![]),
            Expr::sort(Level::one()),
        ),
        (
            indexed::pending_parameter(),
            boxed.clone(),
            Expr::sort(Level::one()),
        ),
        (
            Expr::const_(name("Nat"), vec![]),
            boxed.clone(),
            Expr::const_(name("Nat"), vec![]),
        ),
    ] {
        let mut args = arguments(before, after, nat::literal(42));
        args[0] = carrier;
        assert!(prep.equality_transport(&recursor, &args).is_err());
    }

    let mut unregistered = Preparation::new(&engine.environment, IngressLimits::default());
    assert!(
        unregistered
            .equality_transport(
                &recursor,
                &arguments(Expr::const_(name("Nat"), vec![]), boxed, nat::literal(42)),
            )
            .is_err(),
        "a private name alone is not permission to box a value"
    );
}
