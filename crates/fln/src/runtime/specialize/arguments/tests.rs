//! Structural producer tests; actual source admission/execution is covered by
//! runtime_interleaved_specialization. No synthetic declaration here is a proof.
use super::*;
use fln_env::constants::{ConstantVal, ReducibilityHints};

// These worlds exercise post-admission compiler mechanics, not admission itself.
// The integration tests admit the corresponding declarations through both seats.
fn bare_universe_definition(label: &str, value: Expr) -> DefinitionVal {
    let declaration_name = name(label);
    DefinitionVal {
        base: ConstantVal {
            name: declaration_name.clone(),
            level_params: vec![name("u")],
            type_: ty("Nat"),
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![declaration_name],
    }
}

#[test]
fn bare_universe_values_receive_private_ground_definitions() {
    let definition = bare_universe_definition("bareAnswer", nat::literal(42));
    let environment = Environment::new()
        .add_decl(ConstantInfo::Defn(definition.clone()))
        .unwrap();
    let input = Expr::const_(definition.base.name.clone(), vec![Level::one()]);
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let prepared = preparation.expression(&input).unwrap();
    let ExprNode::Const { name, levels } = prepared.node() else {
        panic!("a nullary value must remain a constant, not execute during preparation");
    };
    assert_ne!(name, &definition.base.name);
    assert!(levels.is_empty());
    let specialized = preparation.specialized_definition(name).unwrap();
    assert!(specialized.base.level_params.is_empty());
    assert_eq!(specialized.base.type_, definition.base.type_);
    assert_eq!(specialized.value, definition.value);
    assert!(!environment.contains(name));
    assert_eq!(
        environment.find(&definition.base.name),
        Some(&ConstantInfo::Defn(definition.clone()))
    );
}

#[test]
fn bare_universe_cache_keys_distinguish_universes_and_reuse_repeated_values() {
    let definition = bare_universe_definition("bareAnswer", nat::literal(42));
    let environment = Environment::new()
        .add_decl(ConstantInfo::Defn(definition))
        .unwrap();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let zero = Expr::const_(name("bareAnswer"), vec![Level::zero()]);
    let one = Expr::const_(name("bareAnswer"), vec![Level::one()]);
    let first = preparation.expression(&zero).unwrap();
    let second = preparation.expression(&one).unwrap();
    assert_ne!(first, second);
    assert_eq!(preparation.expression(&zero).unwrap(), first);
    assert_eq!(preparation.expression(&one).unwrap(), second);
    assert_eq!(preparation.specializations.definitions.len(), 2);
}

#[test]
fn bare_universe_alias_dependencies_reach_the_executable_catalog() {
    let inner = bare_universe_definition("bareInner", nat::literal(42));
    let outer = bare_universe_definition(
        "bareOuter",
        Expr::const_(inner.base.name.clone(), vec![Level::param(name("u"))]),
    );
    let environment = Environment::new()
        .add_decl(ConstantInfo::Defn(inner))
        .unwrap()
        .add_decl(ConstantInfo::Defn(outer))
        .unwrap();
    let limits = IngressLimits::default();
    let mut preparation = Preparation::new(&environment, limits);
    let prepared = preparation
        .expression(&Expr::const_(name("bareOuter"), vec![Level::one()]))
        .unwrap();
    let catalog =
        executable_dependencies(&environment, &prepared, limits, &mut preparation).unwrap();
    assert_eq!(catalog.functions.len(), 2);
    assert_eq!(preparation.specializations.definitions.len(), 2);
    for function in &catalog.functions {
        assert_eq!(function.universe_arity, 0);
        assert!(function.parameters.is_empty());
        assert!(!environment.contains(&function.name));
    }
    assert!(
        catalog
            .functions
            .iter()
            .any(|function| function.body == nat::literal(42))
    );
    let mut referenced = std::collections::BTreeSet::new();
    let mut visited = 0;
    for function in &catalog.functions {
        collect_executable_constants(&function.body, &mut referenced, &mut visited, limits)
            .unwrap();
    }
    assert_eq!(referenced.len(), 1);
    assert!(
        referenced
            .iter()
            .all(|name| catalog.functions.iter().any(|f| &f.name == name))
    );
}

#[test]
fn bare_universe_path_leaves_monomorphic_constants_unchanged() {
    let mut definition = bare_universe_definition("monoAnswer", nat::literal(42));
    definition.base.level_params.clear();
    let environment = Environment::new()
        .add_decl(ConstantInfo::Defn(definition))
        .unwrap();
    let input = ty("monoAnswer");
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    assert_eq!(preparation.expression(&input).unwrap(), input);
    assert!(preparation.specializations.definitions.is_empty());
}

#[test]
fn bare_universe_specialization_never_guesses_open_or_mismatched_levels() {
    let definition = bare_universe_definition("bareAnswer", nat::literal(42));
    let environment = Environment::new()
        .add_decl(ConstantInfo::Defn(definition))
        .unwrap();
    for levels in [
        vec![],
        vec![Level::zero(), Level::one()],
        vec![Level::param(name("unresolved"))],
    ] {
        let mut preparation = Preparation::new(&environment, IngressLimits::default());
        let input = Expr::const_(name("bareAnswer"), levels);
        assert!(preparation.specialize_call(&input, &[]).unwrap().is_none());
        assert!(preparation.specializations.definitions.is_empty());
    }
}

#[test]
fn bare_universe_specialization_refuses_reserved_name_collisions() {
    let definition = bare_universe_definition("bareAnswer", nat::literal(42));
    let mut collision = bare_universe_definition("collision", nat::literal(0));
    collision.base.name = Name::num(name("_fln_runtime_specialization"), 0);
    collision.base.level_params.clear();
    collision.all = vec![collision.base.name.clone()];
    let environment = Environment::new()
        .add_decl(ConstantInfo::Defn(definition))
        .unwrap()
        .add_decl(ConstantInfo::Defn(collision.clone()))
        .unwrap();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let input = Expr::const_(name("bareAnswer"), vec![Level::one()]);
    assert!(matches!(
        preparation.expression(&input),
        Err(IngressError::UnsupportedNode {
            kind: "runtime specialization name collision"
        })
    ));
    assert!(preparation.specializations.definitions.is_empty());
    assert_eq!(
        environment.find(&collision.base.name),
        Some(&ConstantInfo::Defn(collision.clone()))
    );
}

#[test]
fn bare_universe_specialization_obeys_table_limits_and_allows_a_clean_retry() {
    let definition = bare_universe_definition("bareAnswer", nat::literal(42));
    let environment = Environment::new()
        .add_decl(ConstantInfo::Defn(definition))
        .unwrap();
    let input = Expr::const_(name("bareAnswer"), vec![Level::one()]);
    let mut limits = IngressLimits::default();
    limits.fir.max_functions = 0;
    let mut preparation = Preparation::new(&environment, limits);
    assert!(matches!(
        preparation.expression(&input),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ProgramTables,
            limit: 0,
            observed: 1,
        })
    ));
    assert!(preparation.specializations.definitions.is_empty());
    let first = Preparation::new(&environment, IngressLimits::default())
        .expression(&input)
        .unwrap();
    let retry = Preparation::new(&environment, IngressLimits::default())
        .expression(&input)
        .unwrap();
    assert_eq!(first, retry);
}

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
    (
        telescope(&binders, b(1), false),
        telescope(&binders, b(0), true),
    )
}

#[test]
fn type_arguments_after_runtime_parameters_are_erased_without_substituting_values() {
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let (type_, value) = generic();
    let runtime = b(0);
    let result = preparation
        .specialize_arguments(
            type_,
            value,
            &[runtime.clone(), ty("Nat"), nat::literal(42)],
        )
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
fn open_propositions_do_not_capture_runtime_locals_in_specialization_keys() {
    let environment = Environment::new();
    let binders = [
        (ty("Nat"), BinderInfo::Default),
        (Expr::sort(Level::zero()), BinderInfo::Implicit),
        (Expr::app(ty("Decidable"), b(0)), BinderInfo::InstImplicit),
        (ty("Nat"), BinderInfo::Default),
    ];
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    for proposition in [b(0), b(3), ty("someClosedProposition")] {
        let result = preparation
            .specialize_arguments(
                telescope(&binders, ty("Nat"), false),
                telescope(&binders, b(0), true),
                &[b(0), proposition, b(1), nat::literal(42)],
            )
            .unwrap();
        assert_eq!(result.static_arguments, vec![(1, erased_proposition())]);
        assert_eq!(result.runtime_arguments, vec![b(0), b(1), nat::literal(42)]);
        let retained = [
            (ty("Nat"), BinderInfo::Default),
            (
                Expr::app(ty("Decidable"), erased_proposition()),
                BinderInfo::InstImplicit,
            ),
            (ty("Nat"), BinderInfo::Default),
        ];
        assert_eq!(result.type_, telescope(&retained, ty("Nat"), false));
        assert_eq!(result.value, telescope(&retained, b(0), true));
        assert!(!result.type_.has_loose_bvars());
        assert!(!result.value.has_loose_bvars());
    }
}

#[test]
fn erased_propositions_are_closed_propositions_not_a_fabricated_sort_or_proof() {
    use fln_core::outcome::Outcome;
    use fln_kernel::verdict::{Budget, Verdict};
    let proposition = erased_proposition();
    assert!(!proposition.has_loose_bvars());
    assert!(!proposition.has_fvar());
    assert!(!proposition.has_expr_mvar());
    assert!(!proposition.has_level_mvar());
    let candidate = Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name("proposition"),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        },
        value: proposition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Abbrev,
        all: vec![name("proposition")],
    });
    assert!(matches!(
        fln_kernel::check(
            &Environment::new(),
            &candidate,
            Budget::for_stack_bytes(2 * 1024 * 1024)
        ),
        Outcome::Complete(Verdict::Accepted { .. })
    ));
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    for level in [Level::one(), Level::param(name("u"))] {
        assert!(
            !preparation
                .proposition_parameter(&Expr::sort(level))
                .unwrap()
        );
    }
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
            &[
                nat::literal(7),
                ty("Nat"),
                b(0),
                ty("String"),
                ty("runtimeText"),
            ],
        )
        .unwrap();
    let retained = [
        (ty("Nat"), BinderInfo::Default),
        (ty("Nat"), BinderInfo::Default),
        (ty("String"), BinderInfo::Default),
    ];
    assert_eq!(result.type_, telescope(&retained, ty("Nat"), false));
    assert_eq!(result.value, telescope(&retained, b(1), true));
    assert_eq!(
        result.static_arguments,
        vec![(1, ty("Nat")), (3, ty("String"))]
    );
    assert_eq!(
        result.runtime_arguments,
        vec![nat::literal(7), b(0), ty("runtimeText")]
    );
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
        (
            Expr::app(ty("IndexedClass"), b(0)),
            BinderInfo::InstImplicit,
        ),
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
fn specialization_preserves_a_strict_function_return_stage() {
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
    assert_eq!(result.static_arguments, vec![(1, ty("Nat"))]);
    assert_eq!(result.runtime_arguments, vec![nat::literal(1)]);
    assert_eq!(
        result.type_,
        telescope(
            &[
                (ty("Nat"), BinderInfo::Default),
                (ty("Nat"), BinderInfo::Default),
            ],
            ty("Nat"),
            false,
        )
    );
    assert_eq!(
        result.value,
        telescope(
            &[(ty("Nat"), BinderInfo::Default)],
            Expr::let_e(
                name("paid"),
                ty("Nat"),
                Expr::app(ty("observableInitializer"), b(0)),
                telescope(&[(ty("Nat"), BinderInfo::Default)], b(0), true),
                false,
            ),
            true,
        )
    );
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
    let ExprNode::Const {
        name: generated, ..
    } = full_head.node()
    else {
        panic!("private specialization head");
    };
    assert!(!environment.contains(generated));
    assert!(
        preparation
            .specialize_call(&full_head, &full_args)
            .unwrap()
            .is_none()
    );
}

#[test]
fn resource_refusals_do_not_publish_partial_specializations() {
    let environment = environment();
    for limits in [
        IngressLimits {
            max_nodes: 1,
            ..IngressLimits::default()
        },
        IngressLimits {
            max_application_args: 1,
            ..IngressLimits::default()
        },
        IngressLimits {
            max_context_depth: 0,
            ..IngressLimits::default()
        },
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
            preparation.specialize_call(
                &ty("generic"),
                &[nat::literal(1), ty("Nat"), nat::literal(42)]
            ),
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

#[cfg(test)]
mod stages;
