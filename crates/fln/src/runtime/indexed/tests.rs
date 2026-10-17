use super::*;

fn environment() -> Environment {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap().into_complete().unwrap()
        .check_source_files(&[b"inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)"],
            &KVMap::new(), SourceCheckLimits::new(limits))
        .unwrap().into_complete().unwrap().engine.environment().clone()
}
fn vector(element: &str, index: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(name("Vec"), vec![]),
            Expr::const_(name(element), vec![]),
        ),
        index,
    )
}
#[test]
fn indices_share_layouts_without_conflating_element_types() {
    let env = environment();
    let mut prep = Preparation::new(&env, IngressLimits::default());
    assert_eq!(
        prep.value_type(&vector("Nat", nat::literal(0))).unwrap(),
        Some(ValueType::Constructor)
    );
    let first = prep.constructors.clone();
    assert_eq!(first.len(), 2);
    assert_eq!(
        prep.value_type(&vector("Nat", nat::literal(9999))).unwrap(),
        Some(ValueType::Constructor)
    );
    assert_eq!(prep.constructors, first);
    assert_eq!(
        prep.value_type(&vector("String", nat::literal(0))).unwrap(),
        Some(ValueType::Constructor)
    );
    assert_eq!(prep.constructors.len(), 4);
    assert_ne!(prep.constructors[0].name, prep.constructors[2].name);
}
#[test]
fn index_type_erasure_uses_a_bounded_heap_worklist_on_a_small_stack() {
    let env = environment();
    let mut type_ = vector("Nat", Expr::bvar(0).unwrap());
    for _ in 0..2000 {
        type_ = Expr::forall_e(
            Name::anonymous(),
            Expr::const_(name("Nat"), vec![]),
            type_,
            BinderInfo::Default,
        );
    }
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(move || {
            let mut prep = Preparation::new(&env, IngressLimits::default());
            let erased = prep.erase_data_indices(&type_).unwrap();
            assert!(!erased.has_loose_bvars());
            let mut result = &erased;
            for _ in 0..2000 {
                let ExprNode::ForallE { body, .. } = result.node() else {
                    panic!("preserved binder")
                };
                result = body;
            }
            assert_eq!(
                *result,
                Expr::app(
                    Expr::const_(name("Vec"), vec![]),
                    Expr::const_(name("Nat"), vec![])
                )
            );
            let limits = IngressLimits {
                max_nodes: 4,
                ..IngressLimits::default()
            };
            assert!(matches!(
                Preparation::new(&env, limits).erase_data_indices(&type_),
                Err(IngressError::ResourceLimit { .. })
            ));
        })
        .unwrap()
        .join()
        .unwrap();
}

fn proof_parameter_engine() -> &'static Engine {
    static ENGINE: std::sync::OnceLock<Engine> = std::sync::OnceLock::new();
    ENGINE.get_or_init(|| {
        let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
        Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap()
            .check_source_files(
                &[br#"
structure PropPacket (A : Type) (P : Prop) where
  payload : A
  witness : P
structure PredicatePacket (A : Type) (P : A -> Prop) where
  payload : A
  witness : P payload
structure TypePacket (A : Type) (B : A -> Type) where
  payload : A
  extra : B payload
"#],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine
    })
}

fn constant(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}

fn packet(family: &str, carrier: &str, parameter: Expr) -> Expr {
    Expr::app(Expr::app(constant(family), constant(carrier)), parameter)
}

#[test]
fn proof_parameters_share_layouts_and_preserve_exact_motive_carriers() {
    let engine = proof_parameter_engine();
    let root = engine.logical_root(&KVMap::new());
    let equality = |value: Expr| {
        [constant("Nat"), value.clone(), value]
            .into_iter()
            .fold(Expr::const_(name("Eq"), vec![Level::one()]), Expr::app)
    };
    let predicate = Expr::lam(
        name("payload"),
        constant("Nat"),
        equality(Expr::bvar(0).unwrap()),
        BinderInfo::Default,
    );
    let other_predicate = Expr::lam(
        name("other"),
        constant("Nat"),
        constant("True"),
        BinderInfo::Default,
    );
    for (family, original, other) in [
        ("PropPacket", equality(nat::literal(42)), constant("True")),
        ("PredicatePacket", predicate, other_predicate),
    ] {
        let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
        let original = packet(family, "Nat", original);
        let other = packet(family, "Nat", other);
        assert_eq!(
            prep.value_type(&original).unwrap(),
            Some(ValueType::Constructor)
        );
        let first = prep.record_shape(&original).unwrap().unwrap();
        assert_eq!(
            first.constructors[0].fields,
            [constant("Nat"), constant("Bool")]
        );
        let constructors = prep.constructors.clone();
        for source in [&other, &first.source] {
            assert_eq!(
                prep.value_type(source).unwrap(),
                Some(ValueType::Constructor)
            );
            assert_eq!(
                prep.record_shape(source).unwrap().unwrap().source,
                first.source
            );
            assert_eq!(prep.constructors, constructors);
        }
        // The motive retains its original admitted predicate while a helper
        // specialization supplies the canonical carrier. Their erased types
        // must agree before the recursor's existing exact check can succeed.
        let motive = Expr::lam(
            Name::anonymous(),
            original,
            constant("Nat"),
            BinderInfo::Default,
        );
        let motive = prep.erase_type_argument(&motive, &[]).unwrap();
        assert_eq!(
            prep.indexed_motive(&motive, &[], &first.source).unwrap(),
            Some(constant("Nat")),
        );
        let wrong_motive = Expr::lam(
            Name::anonymous(),
            constant("Nat"),
            constant("Nat"),
            BinderInfo::Default,
        );
        assert_eq!(
            prep.indexed_motive(&wrong_motive, &[], &first.source)
                .unwrap(),
            None,
        );
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn predicate_canonicalization_keeps_data_families_and_checked_decision_carriers() {
    let engine = proof_parameter_engine();
    let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
    let type_family = |result| {
        Expr::lam(
            Name::anonymous(),
            constant("Nat"),
            constant(result),
            BinderInfo::Default,
        )
    };
    let nat_packet = packet("TypePacket", "Nat", type_family("Nat"));
    let string_packet = packet("TypePacket", "Nat", type_family("String"));
    assert_eq!(
        prep.value_type(&nat_packet).unwrap(),
        Some(ValueType::Constructor)
    );
    assert_eq!(
        prep.value_type(&string_packet).unwrap(),
        Some(ValueType::Constructor)
    );
    let nat_shape = prep.record_shape(&nat_packet).unwrap().unwrap();
    let string_shape = prep.record_shape(&string_packet).unwrap().unwrap();
    assert_ne!(nat_shape.name, string_shape.name);
    assert_eq!(
        nat_shape.constructors[0].fields,
        [constant("Nat"), constant("Nat")]
    );
    assert_eq!(
        string_shape.constructors[0].fields,
        [constant("Nat"), constant("String")]
    );

    // Decidable already has a checked representative and its native branch
    // adapters use that carrier. Generic proof-parameter erasure must leave
    // this existing choice intact, including on a second preparation pass.
    let decision = |proposition| Expr::app(constant("Decidable"), proposition);
    let expected = decision(constant("True"));
    for proposition in [constant("True"), constant("False"), Expr::bvar(0).unwrap()] {
        let erased = prep.erase_data_indices(&decision(proposition)).unwrap();
        assert_eq!(erased, expected);
        assert_eq!(prep.erase_data_indices(&erased).unwrap(), expected);
        assert_eq!(
            prep.value_type(&erased).unwrap(),
            Some(ValueType::Constructor)
        );
    }
}
