use super::*;
use fln_env::constants::{ConstantVal, ReducibilityHints};

fn c(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}

fn call(label: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(c(label), Expr::app)
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
structure CacheBox (A : Type) where
  value : A
structure CacheOther where
  value : Nat
structure CachePair where
  first : Nat
  second : Nat
structure CacheMethod where
  select : CacheBox (Nat -> Nat) -> Nat -> Nat
structure CachePayload where
  flag : Bool
  value : if flag then Nat else String
inductive CacheBad where
  | mk (callback : Nat -> CacheBad) (payload : CachePayload)
def cacheRuntimeWork (n : Nat) : Nat := n + 1
"#],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

#[test]
fn completed_projection_reuse_retains_registered_layouts_after_unrelated_rollback() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let Some(ConstantInfo::Defn(projection)) = engine.environment.find(&name("CacheBox.value"))
    else {
        panic!("admitted generated projection")
    };
    let ExprNode::Lam { body, .. } = projection.value.node() else {
        panic!("generated projection has its type parameter")
    };
    let field = preparation
        .substitution(body, &arrow(c("Nat"), c("Nat")))
        .unwrap();
    let receiver = call("CacheMethod.mk", [field.clone()]);
    let selected = preparation
        .executable_projection(&name("CacheMethod"), 0, &receiver)
        .unwrap()
        .unwrap();
    let ExprNode::Lam { body, .. } = selected.node() else {
        panic!("selected field retains its receiver lambda")
    };
    let ExprNode::Proj { struct_name, .. } = body.node() else {
        panic!("selected field retains its primitive projection")
    };
    assert_ne!(struct_name, &name("CacheBox"));
    assert!(!preparation.constructors.is_empty());
    assert!(!preparation.interfaces.is_empty());
    assert_eq!(preparation.specializations.executable_projections.len(), 1);

    let unrelated = call("CacheBox", [arrow(c("Bool"), c("Bool"))]);
    assert_eq!(
        preparation.value_type(&unrelated).unwrap(),
        Some(ValueType::Constructor)
    );
    let constructors = preparation.constructors.clone();
    let interfaces = preparation.interfaces.clone();
    assert_eq!(preparation.value_type(&c("CacheBad")).unwrap(), None);
    assert_eq!(preparation.constructors, constructors);
    assert_eq!(preparation.interfaces, interfaces);
    let work = preparation.visited;
    preparation.limits.max_nodes = work + 1;
    assert_eq!(
        preparation
            .executable_projection(&name("CacheMethod"), 0, &call("CacheMethod.mk", [field]))
            .unwrap(),
        Some(selected)
    );
    assert_eq!(preparation.visited, work + 1);
    assert!(matches!(
        preparation.executable_projection(&name("CacheMethod"), 0, &receiver),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit,
            observed,
        }) if limit == work + 1 && observed == work + 2
    ));
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn projection_cache_keys_include_family_index_and_every_receiver_field() {
    let engine = engine();
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let receiver = call("CachePair.mk", [nat::literal(42), nat::literal(7)]);
    assert_eq!(
        preparation
            .executable_projection(&name("CachePair"), 0, &receiver)
            .unwrap(),
        Some(nat::literal(42))
    );
    assert_eq!(
        preparation
            .executable_projection(&name("CachePair"), 1, &receiver)
            .unwrap(),
        Some(nat::literal(7))
    );
    let entries = preparation.specializations.executable_projections.len();
    let changed = call(
        "CachePair.mk",
        [
            nat::literal(42),
            call("cacheRuntimeWork", [nat::literal(7)]),
        ],
    );
    for (family, index, input) in [
        ("CachePair", 0, changed),
        ("CacheOther", 0, receiver.clone()),
        ("CachePair", 2, receiver.clone()),
        ("CachePair", 0, Expr::bvar(0).unwrap()),
    ] {
        assert!(
            preparation
                .executable_projection(&name(family), index, &input)
                .unwrap()
                .is_none()
        );
        assert!(
            !preparation
                .specializations
                .executable_projections
                .contains_key(&(name(family), index, input,))
        );
    }
    assert_eq!(
        preparation.specializations.executable_projections.len(),
        entries
    );
    assert_eq!(
        preparation
            .executable_projection(
                &name("CachePair"),
                0,
                &call("CachePair.mk", [nat::literal(42), nat::literal(9)]),
            )
            .unwrap(),
        Some(nat::literal(42))
    );
    assert_eq!(
        preparation.specializations.executable_projections.len(),
        entries + 1
    );
}

#[test]
fn unfinished_projection_preparation_does_not_publish_and_can_retry() {
    let engine = engine();
    let receiver = call("CachePair.mk", [nat::literal(42), nat::literal(7)]);
    let mut fresh = Preparation::new(&engine.environment, IngressLimits::default());
    let expected = fresh
        .executable_projection(&name("CachePair"), 0, &receiver)
        .unwrap();
    let complete_work = fresh.visited;
    assert!(complete_work > 1);
    let mut limited = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_nodes: complete_work - 1,
            ..IngressLimits::default()
        },
    );
    assert!(matches!(
        limited.executable_projection(&name("CachePair"), 0, &receiver),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit,
            observed,
        }) if limit == complete_work - 1 && observed == complete_work
    ));
    assert!(limited.specializations.executable_projections.is_empty());
    limited.limits = IngressLimits::default();
    assert_eq!(
        limited
            .executable_projection(&name("CachePair"), 0, &receiver)
            .unwrap(),
        expected
    );
    assert_eq!(limited.specializations.executable_projections.len(), 1);
}

#[test]
fn reused_single_field_code_keeps_a_nonreturning_runtime_computation() {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let options = KVMap::new();
    let mut engine = engine();
    let logical = DefinitionVal {
        base: ConstantVal {
            name: name("cacheSpin"),
            level_params: Vec::new(),
            type_: arrow(c("Nat"), c("Nat")),
        },
        value: Expr::lam(
            Name::anonymous(),
            c("Nat"),
            nat::literal(0),
            BinderInfo::Default,
        ),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name("cacheSpin")],
    };
    let executable = DefinitionVal {
        base: ConstantVal {
            name: name("cacheSpin._unsafe_rec"),
            level_params: Vec::new(),
            type_: logical.base.type_.clone(),
        },
        value: Expr::lam(
            Name::anonymous(),
            c("Nat"),
            call("cacheSpin._unsafe_rec", [Expr::bvar(0).unwrap()]),
            BinderInfo::Default,
        ),
        hints: ReducibilityHints::Opaque,
        safety: DefinitionSafety::Partial,
        all: vec![name("cacheSpin._unsafe_rec")],
    };
    for declaration in [
        Declaration::Defn(logical),
        Declaration::Mutual(vec![executable]),
    ] {
        engine = engine
            .admit_declaration(declaration, &options, limits.admission())
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
    }
    engine = engine
        .check_source_files(
            &[b"def cachedStrictBox : CacheBox Nat := CacheBox.mk (cacheSpin 0)"],
            &options,
            SourceCheckLimits::new(limits.admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = engine.logical_root(&options);
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let selected = preparation
        .executable_projection(&name("CacheBox"), 0, &c("cachedStrictBox"))
        .unwrap()
        .unwrap();
    let Some(ConstantInfo::Defn(strict_box)) = engine.environment.find(&name("cachedStrictBox"))
    else {
        panic!("admitted source box")
    };
    let (constructor, fields) = preparation.spine(&strict_box.value).unwrap();
    assert_eq!(constructor, c("CacheBox.mk"));
    let (original_head, original_arguments) = preparation
        .spine(fields.last().expect("source field"))
        .unwrap();
    assert_eq!(original_head, c("cacheSpin"));
    let (selected_head, selected_arguments) = preparation.spine(&selected).unwrap();
    assert_eq!(selected_head, c("cacheSpin._unsafe_rec"));
    assert_eq!(selected_arguments, original_arguments);
    assert_eq!(
        preparation
            .executable_projection(&name("CacheBox"), 0, &c("cachedStrictBox"),)
            .unwrap(),
        Some(selected)
    );
    let mut bounded = limits;
    bounded.vm.max_steps = 200;
    let outcome = engine.execute_source_definitions(
            &[b"#eval let ignored : Nat := cachedStrictBox.value; let alsoIgnored : Nat := cachedStrictBox.value; 42"],
            &options, bounded,
        ).unwrap();
    let Outcome::Inconclusive(stopped) = outcome else {
        panic!("the selected runtime field must execute before the unused binding is discarded")
    };
    assert!(matches!(
        stopped.cause,
        fln_core::outcome::InconclusiveCause::ResourceExhausted { usage }
            if usage.reason == fln_core::diag::ResourceReason::ExecutionSteps
                && usage.allowed == 200 && usage.observed == 201
    ));
    assert_eq!(engine.logical_root(&options), root);
    let retry = engine
        .execute_source_definitions(&[b"#eval 42"], &options, limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &retry.executions[0].exit else {
        panic!("clean retry must return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
}
