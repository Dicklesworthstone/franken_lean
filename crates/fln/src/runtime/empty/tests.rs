use super::*;
use fln_core::level::Level;

#[test]
fn false_elimination_requires_the_complete_canonical_family() {
    for mutation in 0..5 {
        let Declaration::Inductive(mut block) = fln_elab::seed::false_seed_declaration() else {
            panic!("False seed block");
        };
        match mutation {
            0 => {}
            1 => block.types[0].num_indices += 1,
            2 => block.types[0].is_unsafe = true,
            3 => block.recursors[0].base.type_ = Expr::const_(name("Nat"), vec![]),
            _ => block.recursors[0].k = true,
        }
        let mut environment = Environment::new();
        for value in block.types {
            environment = environment.add_decl(ConstantInfo::Induct(value)).unwrap();
        }
        for value in block.recursors {
            environment = environment.add_decl(ConstantInfo::Rec(value)).unwrap();
        }
        let mut prep = Preparation::new(&environment, IngressLimits::default());
        assert_eq!(prep.check_false_family().is_ok(), mutation == 0);
        assert_eq!(prep.false_family_checked, mutation == 0);
        assert!(prep.empty_cases.is_empty());
        assert!(prep.constructors.is_empty());
    }
    assert!(
        Preparation::new(&Environment::new(), IngressLimits::default())
            .check_false_family()
            .is_err()
    );
}

fn checked(source: &[u8]) -> Engine {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(&[source], &KVMap::new(), SourceCheckLimits::new(limits))
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

#[test]
fn empty_recursors_keep_value_parameters_and_major_in_strict_source_order() {
    let engine = checked(b"inductive Never (n : Nat) : Prop where");
    let head = Expr::const_(name("Never.rec"), vec![Level::one()]);
    let motive = Expr::lam(
        Name::anonymous(),
        Expr::app(Expr::const_(name("Never"), vec![]), nat::literal(7)),
        Expr::const_(name("Nat"), vec![]),
        BinderInfo::Default,
    );
    // This is deliberately post-admission, erased input; it is not proof of
    // Never 7. The lowering must retain a non-returning call, not produce Nat.
    let args = [
        nat::literal(7),
        motive,
        Expr::const_(name("Bool.false"), vec![]),
    ];
    let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
    assert!(prep.empty_recursor(&head, &args[..2]).unwrap().is_none());
    let lowered = prep.empty_recursor(&head, &args).unwrap().unwrap();
    let ExprNode::LetE {
        value: parameter,
        body,
        ..
    } = lowered.node()
    else {
        panic!("strict parameter")
    };
    assert_eq!(parameter, &args[0]);
    let ExprNode::LetE {
        value: major, body, ..
    } = body.node()
    else {
        panic!("strict major")
    };
    assert_eq!(major, &args[2]);
    let (callee, call_args) = prep.spine(body).unwrap();
    assert_eq!(
        callee,
        Expr::const_(prep.empty_cases[0].name.clone(), vec![])
    );
    assert_eq!(call_args, vec![Expr::bvar(0).unwrap()]);
    assert_eq!(prep.empty_recursor(&head, &args).unwrap(), Some(lowered));
    assert_eq!(prep.empty_cases.len(), 1);
    assert!(prep.constructors.is_empty(), "no inhabitant was fabricated");
}

#[test]
fn inhabited_families_collisions_and_budget_stops_cannot_register_empty_cases() {
    let engine = checked(b"");
    let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
    for callee in ["Bool.rec", "True.rec", "Nat.rec", "Eq.rec", "Unknown.rec"] {
        assert!(
            prep.empty_recursor(&Expr::const_(name(callee), vec![Level::one()]), &[])
                .unwrap()
                .is_none()
        );
    }
    assert!(prep.empty_cases.is_empty());
    let mut limits = IngressLimits::default();
    limits.fir.max_functions = 0;
    let mut limited = Preparation::new(&engine.environment, limits);
    assert!(limited.empty_name(ValueType::Bool, ValueType::Nat).is_err());
    assert!(limited.empty_cases.is_empty());
    limits = IngressLimits::default();
    limits.max_nodes = 0;
    let mut limited = Preparation::new(&engine.environment, limits);
    assert!(limited.check_false_family().is_err());
    assert!(!limited.false_family_checked);
    // Private lowering names never shadow an admitted declaration.
    let collision = name("_fln_runtime_empty_case");
    let mut declaration = match fln_elab::seed::source_seed_declarations()
        .into_iter()
        .find(|d| matches!(d, Declaration::Defn(_)))
        .unwrap()
    {
        Declaration::Defn(d) => d,
        _ => unreachable!(),
    };
    declaration.base.name = Name::num(collision, 0);
    let environment = engine
        .environment
        .add_decl(ConstantInfo::Defn(declaration))
        .unwrap();
    let mut prep = Preparation::new(&environment, IngressLimits::default());
    assert!(prep.empty_name(ValueType::Bool, ValueType::Nat).is_err());
    assert!(prep.empty_cases.is_empty());
}
