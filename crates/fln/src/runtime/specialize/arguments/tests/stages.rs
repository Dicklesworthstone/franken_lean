//! Static arguments following strict callback-producing stages.
use super::*;

fn strict(name_: &str, init: Expr, body: Expr) -> Expr {
    Expr::let_e(name(name_), ty("Nat"), init, body, false)
}
fn call(label: &str, arg: Expr) -> Expr {
    Expr::app(ty(label), arg)
}

#[test]
fn nested_value_only_binders_do_not_enter_the_type_telescope() {
    // n; let first := observe n; A; x; let second := observe first; B; y.
    // The result x is #3 in the original value but #2 after A and B are erased.
    let type_ = telescope(
        &[
            (ty("Nat"), BinderInfo::Default),
            (Expr::sort(Level::one()), BinderInfo::Implicit),
            (b(0), BinderInfo::Default),
            (Expr::sort(Level::one()), BinderInfo::Implicit),
            (b(0), BinderInfo::Default),
        ],
        b(3),
        false,
    );
    let value = telescope(
        &[(ty("Nat"), BinderInfo::Default)],
        strict(
            "first",
            call("observe", b(0)),
            telescope(
                &[
                    (Expr::sort(Level::one()), BinderInfo::Implicit),
                    (b(0), BinderInfo::Default),
                ],
                strict(
                    "second",
                    call("observe", b(2)),
                    telescope(
                        &[
                            (Expr::sort(Level::one()), BinderInfo::Implicit),
                            (b(0), BinderInfo::Default),
                        ],
                        b(3),
                        true,
                    ),
                ),
                true,
            ),
        ),
        true,
    );
    let environment = Environment::new();
    let result = Preparation::new(&environment, IngressLimits::default())
        .specialize_arguments(
            type_,
            value,
            &[b(0), ty("Nat"), nat::literal(42), ty("String"), ty("text")],
        )
        .unwrap();
    assert_eq!(
        result.type_,
        telescope(
            &[
                (ty("Nat"), BinderInfo::Default),
                (ty("Nat"), BinderInfo::Default),
                (ty("String"), BinderInfo::Default),
            ],
            ty("Nat"),
            false,
        )
    );
    assert_eq!(
        result.value,
        telescope(
            &[(ty("Nat"), BinderInfo::Default)],
            strict(
                "first",
                call("observe", b(0)),
                telescope(
                    &[(ty("Nat"), BinderInfo::Default)],
                    strict(
                        "second",
                        call("observe", b(1)),
                        telescope(&[(ty("String"), BinderInfo::Default)], b(2), true),
                    ),
                    true,
                ),
            ),
            true,
        )
    );
    assert_eq!(
        result.static_arguments,
        vec![(1, ty("Nat")), (3, ty("String"))]
    );
    assert_eq!(
        result.runtime_arguments,
        vec![b(0), nat::literal(42), ty("text")]
    );
    assert!(!result.type_.has_loose_bvars());
    assert!(!result.value.has_loose_bvars());
}

#[test]
fn zero_argument_producers_preserve_all_initialization_before_the_static_binder() {
    let binders = [
        (Expr::sort(Level::one()), BinderInfo::Implicit),
        (b(0), BinderInfo::Default),
    ];
    let type_ = telescope(&binders, b(1), false);
    let value = strict(
        "first",
        call("observe", nat::literal(0)),
        strict("second", call("observe", b(0)), telescope(&binders, b(0), true)),
    );
    let environment = Environment::new();
    let result = Preparation::new(&environment, IngressLimits::default())
        .specialize_arguments(type_, value, &[ty("Nat")])
        .unwrap();
    assert_eq!(
        result.type_,
        telescope(&[(ty("Nat"), BinderInfo::Default)], ty("Nat"), false)
    );
    assert_eq!(
        result.value,
        strict(
            "first",
            call("observe", nat::literal(0)),
            strict(
                "second",
                call("observe", b(0)),
                telescope(&[(ty("Nat"), BinderInfo::Default)], b(0), true),
            ),
        )
    );
    assert!(result.runtime_arguments.is_empty());
    assert!(!result.value.has_loose_bvars());
}

#[test]
fn computed_callback_results_are_not_executed_to_find_a_static_telescope() {
    let (type_, _) = generic();
    let value = telescope(
        &[(ty("Nat"), BinderInfo::Default)],
        strict("paid", call("observe", b(0)), call("computeCallback", b(0))),
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

#[test]
fn trailing_runtime_arguments_cannot_change_a_cached_strict_stage() {
    let (type_, value) = generic();
    let ExprNode::Lam { body, .. } = value.node() else {
        panic!("prefix");
    };
    let value = telescope(
        &[(ty("Nat"), BinderInfo::Default)],
        strict("paid", call("observe", b(0)), body.lift_loose(0, 1).unwrap()),
        true,
    );
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let partial = preparation
        .specialize_arguments(type_.clone(), value.clone(), &[nat::literal(1), ty("Nat")])
        .unwrap();
    let saturated = preparation
        .specialize_arguments(type_, value, &[nat::literal(99), ty("Nat"), nat::literal(42)])
        .unwrap();
    assert_eq!(partial.type_, saturated.type_);
    assert_eq!(partial.value, saturated.value);
    assert_eq!(partial.static_arguments, saturated.static_arguments);
    assert_ne!(partial.runtime_arguments, saturated.runtime_arguments);
}

#[test]
fn strict_stage_depth_is_bounded_before_publication() {
    let (type_, value) = generic();
    let value = strict("paid", call("observe", nat::literal(0)), value);
    let environment = Environment::new()
        .add_decl(ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: name("staged"),
                level_params: Vec::new(),
                type_,
            },
            value,
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: Vec::new(),
        }))
        .unwrap();
    let limits = IngressLimits {
        max_context_depth: 1,
        ..IngressLimits::default()
    };
    let mut preparation = Preparation::new(&environment, limits);
    assert!(matches!(
        preparation.specialize_call(&ty("staged"), &[nat::literal(1), ty("Nat")]),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ProgramTables,
            ..
        })
    ));
    assert!(preparation.specializations.definitions.is_empty());
    assert!(preparation.specializations.instances.is_empty());
}

#[test]
fn deep_strict_telescope_uses_a_heap_worklist_and_preserves_scope() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let binders = [
                (Expr::sort(Level::one()), BinderInfo::Implicit),
                (b(0), BinderInfo::Default),
            ];
            let type_ = telescope(&binders, b(1), false);
            let mut value = telescope(&binders, b(0), true);
            for _ in 0..2000 {
                value = strict("paid", call("observe", nat::literal(0)), value);
            }
            let environment = Environment::new();
            let result = Preparation::new(&environment, IngressLimits::default())
                .specialize_arguments(type_, value, &[ty("Nat"), nat::literal(42)])
                .unwrap();
            assert_eq!(result.static_arguments, vec![(0, ty("Nat"))]);
            assert_eq!(result.runtime_arguments, vec![nat::literal(42)]);
            assert!(!result.value.has_loose_bvars());
            let mut value = result.value;
            let mut count = 0;
            while let ExprNode::LetE { body, .. } = value.node() {
                count += 1;
                value = body.clone();
            }
            assert_eq!(count, 2000);
            assert!(matches!(value.node(), ExprNode::Lam { .. }));
        })
        .unwrap()
        .join()
        .unwrap();
}
