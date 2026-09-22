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
