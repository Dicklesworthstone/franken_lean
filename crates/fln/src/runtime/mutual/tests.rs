use super::*;

fn environment() -> Environment {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits).unwrap().into_complete().unwrap()
        .check_source_files(&[b"mutual\ninductive T (A : Type) : Nat -> Type where | leaf (n : Nat) (x : A) : T A n | node (b : Bool) (s : String) (f : F A b s) : T A 0\ninductive F (A : Type) : Bool -> String -> Type where | nil (b : Bool) (s : String) : F A b s | cons (n : Nat) (b : Bool) (s : String) (t : T A n) : F A b s\nend"],
            &KVMap::new(), SourceCheckLimits::new(limits))
        .unwrap().into_complete().unwrap().engine.environment().clone()
}
fn family(name_: &str, element: &str, args: &[Expr]) -> Expr {
    args.iter().cloned().fold(
        Expr::app(
            Expr::const_(name(name_), vec![]),
            Expr::const_(name(element), vec![]),
        ),
        Expr::app,
    )
}
#[test]
fn index_erasure_reuses_group_layouts_but_keeps_element_specializations_separate() {
    let env = environment();
    let mut prep = Preparation::new(&env, IngressLimits::default());
    for index in [0, 42, u64::MAX] {
        assert_eq!(
            prep.value_type(&family("T", "Nat", &[nat::literal(index)]))
                .unwrap(),
            Some(ValueType::Constructor)
        );
        assert_eq!(prep.constructors.len(), 4);
    }
    let original = prep.constructors.clone();
    for b in ["Bool.false", "Bool.true"] {
        assert_eq!(
            prep.value_type(&family(
                "F",
                "Nat",
                &[
                    Expr::const_(Name::from_components(b.split('.')), vec![]),
                    Expr::lit(fln_core::expr::Literal::Str("index".into()))
                ]
            ))
            .unwrap(),
            Some(ValueType::Constructor)
        );
        assert_eq!(prep.constructors, original);
    }
    assert_eq!(
        prep.value_type(&family("T", "String", &[nat::literal(0)]))
            .unwrap(),
        Some(ValueType::Constructor)
    );
    assert_eq!(prep.constructors.len(), 8);
    assert_ne!(prep.constructors[0].name, prep.constructors[4].name);
    assert_ne!(prep.constructors[0].fields, prep.constructors[4].fields);
}
#[test]
fn inconsistent_recursor_index_metadata_is_not_a_new_admission_path() {
    let env = environment();
    let Some(ConstantInfo::Rec(actual)) = env.find(&name("T.rec")) else {
        panic!("admitted recursor")
    };
    let levels = [fln_core::level::Level::one()];
    let args = [Expr::const_(name("Nat"), vec![])];
    assert!(
        Preparation::new(&env, IngressLimits::default())
            .mutual_group(actual, &levels, &args)
            .unwrap()
            .is_some()
    );
    let mut bad = actual.clone();
    bad.num_indices += 1;
    let mut prep = Preparation::new(&env, IngressLimits::default());
    assert!(prep.mutual_group(&bad, &levels, &args).unwrap().is_none());
    assert!(prep.constructors.is_empty());
}

#[test]
fn function_child_discovery_rolls_back_every_peer_on_interface_exhaustion() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let env = Engine::with_source_seed(limits).unwrap().into_complete().unwrap()
        .check_source_files(&[b"mutual\ninductive T : Nat -> Type where | leaf (n : Nat) : T n | node (f : (i : Nat) -> F i) : T 0\ninductive F : Nat -> Type where | node (f : (i : Nat) -> T i) : F 0\nend"],
            &KVMap::new(), SourceCheckLimits::new(limits))
        .unwrap().into_complete().unwrap().engine.environment().clone();
    let source = Expr::app(Expr::const_(name("T"), vec![]), nat::literal(0));
    let mut bounded = IngressLimits::default();
    bounded.fir.max_closure_types = 0;
    let mut prep = Preparation::new(&env, bounded);
    assert!(matches!(
        prep.value_type(&source),
        Err(IngressError::ResourceLimit { .. })
    ));
    assert!(prep.value_types.records.is_empty());
    assert!(prep.value_types.closures.is_empty());
    assert!(prep.interfaces.is_empty());
    assert!(prep.constructors.is_empty());
    // Descriptive shape caches are not executable anchors. Reusing them on a
    // retry must produce exactly the same bindings as clean discovery.
    prep.limits = IngressLimits::default();
    assert_eq!(
        prep.value_type(&source).unwrap(),
        Some(ValueType::Constructor)
    );
    let mut clean = Preparation::new(&env, IngressLimits::default());
    assert_eq!(
        clean.value_type(&source).unwrap(),
        Some(ValueType::Constructor)
    );
    assert_eq!(prep.constructors, clean.constructors);
    assert_eq!(prep.interfaces, clean.interfaces);
}

#[test]
fn polymorphic_child_argument_layouts_remain_a_precise_refusal() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let env = Engine::with_source_seed(limits).unwrap().into_complete().unwrap()
        .check_source_files(&[b"mutual\ninductive T : Type 1 where | node (f : (A : Type) -> A -> F)\ninductive F : Type 1 where | leaf | node (t : T)\nend"],
            &KVMap::new(), SourceCheckLimits::new(limits))
        .unwrap().into_complete().unwrap().engine.environment().clone();
    let mut prep = Preparation::new(&env, IngressLimits::default());
    assert_eq!(
        prep.value_type(&Expr::const_(name("T"), vec![])).unwrap(),
        None
    );
    assert!(prep.value_types.records.is_empty());
    assert!(prep.value_types.closures.is_empty());
    assert!(prep.interfaces.is_empty());
    assert!(prep.constructors.is_empty());
}
