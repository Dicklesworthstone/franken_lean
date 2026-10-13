use super::*;
use fln_env::constants::ReducibilityHints;

fn c(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}

fn arrow(domain: Expr, result: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, result, BinderInfo::Default)
}

fn engine() -> Engine {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[br#"
def memoKeep (A : Type) (h : 0 = 0) (value : A) : A := value
def memoPlain (A : Type) (value : A) : A := value
structure MemoBox (A : Type) where
  value : A
structure MemoPayload where
  flag : Bool
  value : if flag then Nat else String
inductive MemoBad where
  | mk (callback : Nat -> MemoBad) (payload : MemoPayload)
"#],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

fn specialization(preparation: &mut Preparation<'_>, label: &str, argument: Expr) -> DefinitionVal {
    let value = preparation
        .specialize_call(&c(label), &[argument])
        .unwrap()
        .unwrap();
    let ExprNode::Const { name, levels } = value.node() else {
        panic!("static arguments leave a canonical function constant")
    };
    assert!(levels.is_empty());
    preparation.specialized_definition(name).unwrap()
}

fn with_result(definition: &DefinitionVal, result: Expr) -> DefinitionVal {
    let mut body = definition.value.clone();
    let mut binders = Vec::new();
    while let ExprNode::Lam {
        binder_name,
        binder_type,
        body: next,
        binder_info,
    } = body.node()
    {
        binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
        body = next.clone();
    }
    let mut changed = definition.clone();
    changed.value = binders
        .into_iter()
        .rev()
        .fold(result, |body, (name, type_, info)| {
            Expr::lam(name, type_, body, info)
        });
    changed
}

#[test]
fn completed_canonical_normalization_reuses_work_without_changing_logical_syntax() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let original = specialization(&mut preparation, "memoKeep", c("Nat"));
    let before = preparation.visited;
    let normalized = preparation
        .normalize_definition_signature(&original)
        .unwrap();
    assert!(preparation.visited > before + 1);
    // The proof binder is represented by an inert scalar only in the result.
    assert_ne!(normalized.base.type_, original.base.type_);
    assert_eq!(
        preparation.specialized_definition(&original.base.name),
        Some(original.clone())
    );
    assert_eq!(preparation.specializations.normalized_definitions.len(), 1);

    // Growing the canonical registry must not require the earlier source body
    // to be erased again, or confuse two concrete carrier specializations.
    let other = specialization(&mut preparation, "memoKeep", c("Bool"));
    let other_normalized = preparation.normalize_definition_signature(&other).unwrap();
    assert_ne!(normalized.base.type_, other_normalized.base.type_);
    assert_eq!(preparation.specializations.normalized_definitions.len(), 2);
    let before = preparation.visited;
    preparation.limits.max_nodes = before + 1;
    assert_eq!(
        preparation
            .normalize_definition_signature(&original)
            .unwrap(),
        normalized
    );
    assert_eq!(preparation.visited, before + 1);
    assert!(matches!(
        preparation.normalize_definition_signature(&original),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit,
            observed,
        }) if limit == before + 1 && observed == before + 2
    ));
    assert_eq!(
        preparation.specialized_definition(&original.base.name),
        Some(original)
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn same_name_modified_body_type_or_metadata_does_not_receive_a_cached_result() {
    let engine = engine();
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let original = specialization(&mut preparation, "memoKeep", c("Nat"));
    let normalized = preparation
        .normalize_definition_signature(&original)
        .unwrap();
    let body_changed = with_result(&original, nat::literal(42));
    let mut type_changed = specialization(&mut preparation, "memoPlain", c("Nat"));
    type_changed.base.name = original.base.name.clone();
    let mut metadata_changed = original.clone();
    metadata_changed.hints = if original.hints == ReducibilityHints::Opaque {
        ReducibilityHints::Abbrev
    } else {
        ReducibilityHints::Opaque
    };
    for changed in [&body_changed, &type_changed, &metadata_changed] {
        let mut fresh = Preparation::new(&engine.environment, IngressLimits::default());
        let expected = fresh.normalize_definition_signature(changed).unwrap();
        assert_ne!(expected, normalized);
        assert_eq!(
            preparation.normalize_definition_signature(changed).unwrap(),
            expected
        );
        let retained = &preparation.specializations.normalized_definitions[&original.base.name];
        assert_eq!(retained.original, original);
        assert_eq!(retained.normalized, normalized);
        assert_eq!(preparation.specializations.normalized_definitions.len(), 1);
        assert_eq!(
            preparation.specialized_definition(&original.base.name),
            Some(original.clone())
        );
    }

    // Production canonical entries are immutable. Retaining the exact original
    // also protects reuse if a future implementation replaces one deliberately.
    preparation
        .specializations
        .definitions
        .insert(original.base.name.clone(), body_changed.clone());
    let refreshed = preparation
        .normalize_definition_signature(&body_changed)
        .unwrap();
    assert_ne!(refreshed.value, normalized.value);
    assert_eq!(
        preparation.specializations.normalized_definitions[&original.base.name].original,
        body_changed
    );
    assert_eq!(preparation.specializations.normalized_definitions.len(), 1);
}

#[test]
fn exhausted_normalization_never_publishes_a_result_and_retry_matches_a_fresh_preparation() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let original = specialization(&mut preparation, "memoKeep", c("Nat"));
    let before = preparation.visited;
    preparation.limits.max_nodes = before + 2;
    assert!(matches!(
        preparation.normalize_definition_signature(&original),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit,
            observed,
        }) if limit == before + 2 && observed == before + 3
    ));
    assert!(
        preparation
            .specializations
            .normalized_definitions
            .is_empty()
    );
    assert_eq!(
        preparation.specialized_definition(&original.base.name),
        Some(original.clone())
    );
    preparation.limits = IngressLimits::default();
    let normalized = preparation
        .normalize_definition_signature(&original)
        .unwrap();
    assert!(preparation.visited > before + 3);
    let mut fresh = Preparation::new(&engine.environment, IngressLimits::default());
    let fresh_original = specialization(&mut fresh, "memoKeep", c("Nat"));
    assert_eq!(fresh_original, original);
    assert_eq!(
        fresh
            .normalize_definition_signature(&fresh_original)
            .unwrap(),
        normalized
    );
    assert_eq!(preparation.specializations.normalized_definitions.len(), 1);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn completed_normalization_entries_obey_the_program_table_budget() {
    let engine = engine();
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let first = specialization(&mut preparation, "memoKeep", c("Nat"));
    let second = specialization(&mut preparation, "memoKeep", c("Bool"));
    // Both canonical sources already exist. This limit exercises the completed
    // normalization table, not the independent specialization creation gate.
    preparation.limits.fir.max_functions = 1;
    let first_normalized = preparation.normalize_definition_signature(&first).unwrap();
    assert!(matches!(
        preparation.normalize_definition_signature(&second),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ProgramTables,
            limit: 1,
            observed: 2,
        })
    ));
    assert_eq!(preparation.specializations.normalized_definitions.len(), 1);
    assert!(
        !preparation
            .specializations
            .normalized_definitions
            .contains_key(&second.base.name)
    );
    assert_eq!(
        preparation.normalize_definition_signature(&first).unwrap(),
        first_normalized
    );
    preparation.limits = IngressLimits::default();
    preparation.normalize_definition_signature(&second).unwrap();
    assert_eq!(preparation.specializations.normalized_definitions.len(), 2);
}

#[test]
fn cached_closure_and_projection_normalization_survives_later_layout_rollback() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let callback = arrow(c("Nat"), c("Nat"));
    let original = specialization(&mut preparation, "MemoBox.value", callback);
    let normalized = preparation
        .normalize_definition_signature(&original)
        .unwrap();
    let before_signature = preparation
        .prepared_signature(&normalized, false)
        .unwrap()
        .unwrap();
    assert!(matches!(before_signature.result, ValueType::Closure(_)));
    assert!(!preparation.interfaces.is_empty());
    assert!(!preparation.constructors.is_empty());
    let ExprNode::Lam { body, .. } = normalized.value.node() else {
        panic!("project retains its real receiver lambda")
    };
    let ExprNode::Proj { struct_name, .. } = body.node() else {
        panic!("project retains a checked primitive field selection")
    };
    assert_ne!(struct_name, &name("MemoBox"));

    // Register another independent layout and callback after the cached result.
    let unrelated = Expr::app(c("MemoBox"), arrow(c("Bool"), c("Bool")));
    assert_eq!(
        preparation.value_type(&unrelated).unwrap(),
        Some(ValueType::Constructor)
    );
    let constructors = preparation.constructors.clone();
    let interfaces = preparation.interfaces.clone();
    assert_eq!(preparation.value_type(&c("MemoBad")).unwrap(), None);
    assert_eq!(preparation.constructors, constructors);
    assert_eq!(preparation.interfaces, interfaces);
    assert!(!preparation.value_types.records.contains(&c("MemoBad")));

    let before = preparation.visited;
    preparation.limits.max_nodes = before + 1;
    assert_eq!(
        preparation
            .normalize_definition_signature(&original)
            .unwrap(),
        normalized
    );
    assert_eq!(preparation.visited, before + 1);
    preparation.limits = IngressLimits::default();
    let after_signature = preparation
        .prepared_signature(&normalized, false)
        .unwrap()
        .unwrap();
    assert_eq!(after_signature.parameters, before_signature.parameters);
    assert_eq!(after_signature.result, before_signature.result);
    assert_eq!(
        after_signature.result_ownership,
        before_signature.result_ownership
    );
    assert_eq!(after_signature.body, before_signature.body);
    assert_eq!(
        preparation.specialized_definition(&original.base.name),
        Some(original)
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}
