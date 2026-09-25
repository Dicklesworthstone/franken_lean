//! Structural producer tests; actual source admission/execution is covered by
//! runtime_interleaved_specialization. No synthetic declaration here is a proof.
use super::*;
use fln_env::constants::{ConstantVal, ReducibilityHints};

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}
fn ty(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}
fn telescope(binders: &[(Expr, BinderInfo)], mut body: Expr, lambda: bool) -> Expr {
    for (domain, info) in binders.iter().rev() {
        body = if lambda {
            Expr::lam(Name::anonymous(), domain.clone(), body, *info)
        } else {
            Expr::forall_e(Name::anonymous(), domain.clone(), body, *info)
        };
    }
    body
}
fn generic() -> (Expr, Expr) {
    // (n : Nat) {A : Type} (x : A) : A := x
    let binders = [
        (ty("Nat"), BinderInfo::Default),
        (Expr::sort(Level::one()), BinderInfo::Implicit),
        (b(0), BinderInfo::Default),
    ];
    (telescope(&binders, b(1), false), telescope(&binders, b(0), true))
}

#[test]
fn type_arguments_after_runtime_parameters_are_erased_without_substituting_values() {
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let (type_, value) = generic();
    let runtime = b(0);
    let result = preparation
        .specialize_arguments(type_, value, &[runtime.clone(), ty("Nat"), nat::literal(42)])
        .unwrap();
    let retained = [
        (ty("Nat"), BinderInfo::Default),
        (ty("Nat"), BinderInfo::Default),
    ];
    assert_eq!(result.type_, telescope(&retained, ty("Nat"), false));
    assert_eq!(result.value, telescope(&retained, b(0), true));
    assert_eq!(result.static_arguments, vec![(1, ty("Nat"))]);
    assert_eq!(result.runtime_arguments, vec![runtime, nat::literal(42)]);
    assert!(!result.value.has_loose_bvars());
}

#[test]
fn multiple_interleaved_types_rebase_later_domains_and_earlier_runtime_references() {
    let binders = [
        (ty("Nat"), BinderInfo::Default),
        (Expr::sort(Level::one()), BinderInfo::Implicit),
        (b(0), BinderInfo::Default),
        (Expr::sort(Level::one()), BinderInfo::Implicit),
        (b(0), BinderInfo::Default),
    ];
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let result = preparation
        .specialize_arguments(
            telescope(&binders, b(3), false),
            telescope(&binders, b(2), true),
            &[nat::literal(7), ty("Nat"), b(0), ty("String"), ty("runtimeText")],
        )
        .unwrap();
    let retained = [
        (ty("Nat"), BinderInfo::Default),
        (ty("Nat"), BinderInfo::Default),
        (ty("String"), BinderInfo::Default),
    ];
    assert_eq!(result.type_, telescope(&retained, ty("Nat"), false));
    assert_eq!(result.value, telescope(&retained, b(1), true));
    assert_eq!(result.static_arguments, vec![(1, ty("Nat")), (3, ty("String"))]);
    assert_eq!(result.runtime_arguments, vec![nat::literal(7), b(0), ty("runtimeText")]);
}

#[test]
fn independent_inert_dictionary_arguments_can_follow_dynamic_arguments() {
    let callable = telescope(&[(ty("Nat"), BinderInfo::Default)], ty("Nat"), false);
    let dictionary = telescope(&[(ty("Nat"), BinderInfo::Default)], b(0), true);
    // A direct inert function is a structural stand-in for a dictionary field;
    // registered class dictionaries are exercised by the source integration.
    let binders = [
        (ty("Nat"), BinderInfo::Default),
        (callable, BinderInfo::InstImplicit),
    ];
    let environment = Environment::new();
    let result = Preparation::new(&environment, IngressLimits::default())
        .specialize_arguments(
            telescope(&binders, ty("Nat"), false),
            telescope(&binders, Expr::app(b(0), b(1)), true),
            &[b(0), dictionary.clone()],
        )
        .unwrap();
    assert_eq!(result.static_arguments, vec![(1, dictionary.clone())]);
    assert_eq!(result.runtime_arguments, vec![b(0)]);
    assert_eq!(
        result.value,
        telescope(
            &[(ty("Nat"), BinderInfo::Default)],
            Expr::app(dictionary, b(0)),
            true
        )
    );
}

#[test]
fn value_dependent_and_computed_dictionaries_are_not_erased() {
    let dictionary = telescope(&[(ty("Nat"), BinderInfo::Default)], b(0), true);
    let dependent = [
        (ty("Nat"), BinderInfo::Default),
        (Expr::app(ty("IndexedClass"), b(0)), BinderInfo::InstImplicit),
    ];
    let environment = Environment::new();
    let type_ = telescope(&dependent, ty("Nat"), false);
    let value = telescope(&dependent, b(1), true);
    let result = Preparation::new(&environment, IngressLimits::default())
        .specialize_arguments(type_.clone(), value.clone(), &[nat::literal(0), dictionary])
        .unwrap();
    assert!(result.static_arguments.is_empty());
    assert_eq!(result.type_, type_);
    assert_eq!(result.value, value);

    let independent = [
        (ty("Nat"), BinderInfo::Default),
        (ty("Class"), BinderInfo::InstImplicit),
    ];
    let computed = Expr::app(ty("computeDictionary"), nat::literal(0));
    let result = Preparation::new(&environment, IngressLimits::default())
        .specialize_arguments(
            telescope(&independent, ty("Nat"), false),
            telescope(&independent, b(1), true),
            &[nat::literal(1), computed.clone()],
        )
        .unwrap();
    assert!(result.static_arguments.is_empty());
    assert_eq!(result.runtime_arguments, vec![nat::literal(1), computed]);
}

#[test]
fn specialization_does_not_cross_a_strict_function_return_stage() {
    let (type_, value) = generic();
    let ExprNode::Lam { body, .. } = value.node() else {
        panic!("runtime prefix");
    };
    let value = telescope(
        &[(ty("Nat"), BinderInfo::Default)],
        Expr::let_e(
            name("paid"),
            ty("Nat"),
            Expr::app(ty("observableInitializer"), b(0)),
            body.lift_loose(0, 1).unwrap(),
            false,
        ),
        true,
    );
    let environment = Environment::new();
    let result = Preparation::new(&environment, IngressLimits::default())
        .specialize_arguments(type_.clone(), value.clone(), &[nat::literal(1), ty("Nat")])
        .unwrap();
    assert!(result.static_arguments.is_empty());
    assert_eq!(result.type_, type_);
    assert_eq!(result.value, value);
}

fn environment() -> Environment {
    let (type_, value) = generic();
    Environment::new()
        .add_decl(ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: name("generic"),
                level_params: Vec::new(),
                type_,
            },
            value,
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: Vec::new(),
        }))
        .unwrap()
}

#[test]
fn partial_and_saturated_calls_share_keys_but_distinct_static_types_do_not() {
    let environment = environment();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let head = ty("generic");
    let partial = preparation
        .specialize_call(&head, &[nat::literal(1), ty("Nat")])
        .unwrap()
        .unwrap();
    let full = preparation
        .specialize_call(&head, &[nat::literal(2), ty("Nat"), nat::literal(42)])
        .unwrap()
        .unwrap();
    let (partial_head, partial_args) = preparation.spine(&partial).unwrap();
    let (full_head, full_args) = preparation.spine(&full).unwrap();
    assert_eq!(partial_head, full_head);
    assert_eq!(partial_args, vec![nat::literal(1)]);
    assert_eq!(full_args, vec![nat::literal(2), nat::literal(42)]);
    assert_eq!(preparation.specializations.definitions.len(), 1);
    let other = preparation
        .specialize_call(&head, &[nat::literal(2), ty("String"), ty("runtimeText")])
        .unwrap()
        .unwrap();
    assert_ne!(preparation.spine(&other).unwrap().0, full_head);
    assert_eq!(preparation.specializations.definitions.len(), 2);
    let ExprNode::Const { name: generated, .. } = full_head.node() else {
        panic!("private specialization head");
    };
    assert!(!environment.contains(generated));
    assert!(preparation.specialize_call(&full_head, &full_args).unwrap().is_none());
}

#[test]
fn resource_refusals_do_not_publish_partial_specializations() {
    let environment = environment();
    for limits in [
        IngressLimits { max_nodes: 1, ..IngressLimits::default() },
        IngressLimits { max_application_args: 1, ..IngressLimits::default() },
        IngressLimits { max_context_depth: 0, ..IngressLimits::default() },
        IngressLimits {
            fir: fln_comp::fir::ValidationLimits {
                max_functions: 0,
                ..IngressLimits::default().fir
            },
            ..IngressLimits::default()
        },
    ] {
        let mut preparation = Preparation::new(&environment, limits);
        assert!(matches!(
            preparation.specialize_call(&ty("generic"), &[nat::literal(1), ty("Nat"), nat::literal(42)]),
            Err(IngressError::ResourceLimit { .. })
        ));
        assert!(preparation.specializations.definitions.is_empty());
        assert!(preparation.specializations.instances.is_empty());
    }
}

#[test]
fn late_static_arguments_use_a_bounded_heap_telescope() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut binders = vec![(ty("Nat"), BinderInfo::Default); 2000];
            binders.push((Expr::sort(Level::one()), BinderInfo::Implicit));
            binders.push((b(0), BinderInfo::Default));
            let type_ = telescope(&binders, b(1), false);
            let value = telescope(&binders, b(0), true);
            let mut args = vec![nat::literal(0); 2000];
            args.push(ty("Nat"));
            args.push(nat::literal(42));
            let environment = Environment::new();
            let result = Preparation::new(&environment, IngressLimits::default())
                .specialize_arguments(type_, value, &args)
                .unwrap();
            assert_eq!(result.static_arguments, vec![(2000, ty("Nat"))]);
            assert_eq!(result.runtime_arguments.len(), 2001);
            assert!(!result.type_.has_loose_bvars());
            assert!(!result.value.has_loose_bvars());
        })
        .unwrap()
        .join()
        .unwrap();
}
