use super::*;
use fln_core::level::Level;

#[test]
fn equality_transport_requires_every_canonical_family_object() {
    for mutation in 0..4 {
        let Declaration::Inductive(mut block) = fln_elab::seed::eq_seed_declaration() else {
            panic!("equality block");
        };
        match mutation {
            0 => {}
            1 => block.types[0].num_indices += 1,
            2 => block.ctors[0].num_fields += 1,
            _ => block.recursors[0].rules[0].rhs = nat::literal(0),
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
