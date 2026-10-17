//! Private selector probes over the actual decoded pinned declarations. This
//! small raw fixture is not admission, and altered models are never executed.
//! source_well_founded separately imports the full closure through both seats.
use super::*;
use fln_elab::{externs, implemented_by};
use fln_env::constants::{AxiomVal, TheoremVal};
use std::path::PathBuf;
use std::sync::OnceLock;

const STACK: usize = 256 * 1024 * 1024;

fn fixture() -> Option<&'static Environment> {
    static FIXTURE: OnceLock<Option<Environment>> = OnceLock::new();
    FIXTURE
        .get_or_init(|| {
            let library = std::env::var_os("FLN_REFERENCE_LIB")
                .map(PathBuf::from)
                .or_else(|| {
                    std::env::var_os("HOME").map(|home| {
                        PathBuf::from(home)
                            .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
                    })
                })
                .filter(|path| path.is_dir());
            let Some(library) = library else {
                assert!(
                    std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                    "the pinned Reference library is required"
                );
                eprintln!("SKIP: set FLN_REFERENCE_LIB to the pinned lib/lean");
                return None;
            };
            let mut environment = Environment::new();
            for module in ["Init/Prelude", "Init/WF", "Init/WFComputable"] {
                let path = library.join(module).with_extension("olean");
                let parts = [
                    std::fs::read(&path).expect("actual exported WF artifact"),
                    std::fs::read(path.with_extension("olean.server"))
                        .expect("actual server WF artifact"),
                    std::fs::read(path.with_extension("olean.private"))
                        .expect("actual private WF artifact"),
                ];
                let decoded = decode_olean_module_artifacts(
                    &parts[0],
                    &parts[1],
                    &parts[2],
                    OleanDecodeLimits::new(STACK),
                )
                .expect("decode the actual pinned WF declarations");
                for constant in decoded.constants {
                    if !environment.contains(constant.name()) {
                        environment = environment.add_decl(constant).unwrap();
                    }
                }
            }
            for label in [
                source_name(),
                target_name(),
                equation_name(),
                name("WellFounded.fixC._unsafe_rec"),
            ] {
                assert!(
                    environment.contains(&label),
                    "{}",
                    label.to_display_string()
                );
            }
            Some(environment)
        })
        .as_ref()
}

fn with_fixture(test: impl FnOnce(&Environment) + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            if let Some(environment) = fixture() {
                test(environment);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

fn change(
    environment: &Environment,
    label: &Name,
    replacement: Option<ConstantInfo>,
) -> Environment {
    let mut altered = Environment::new();
    for (candidate, _) in environment.constants() {
        if candidate != label {
            altered = altered
                .with_entry(environment.entry(candidate).unwrap())
                .unwrap();
        }
    }
    for (journal, state) in environment.extensions() {
        altered = altered
            .register_extension(state.descriptor.clone())
            .unwrap();
        for entry in state.entries() {
            altered = altered
                .push_extension_entry(journal, entry.payload.clone())
                .unwrap();
        }
    }
    if let Some(replacement) = replacement {
        assert_eq!(replacement.name(), label);
        altered = altered.add_decl(replacement).unwrap();
    }
    altered
}

fn theorem(environment: &Environment) -> TheoremVal {
    let ConstantInfo::Thm(theorem) = environment.find(&equation_name()).unwrap() else {
        panic!("the actual equation is an imported theorem")
    };
    theorem.clone()
}

fn definition(environment: &Environment, label: &Name) -> DefinitionVal {
    let ConstantInfo::Defn(definition) = environment.find(label).unwrap() else {
        panic!("the actual endpoint is an imported definition")
    };
    definition.clone()
}

fn refused(environment: &Environment, label: &str) {
    let original = environment.logical_root(&KVMap::new());
    let mut preparation = Preparation::new(environment, IngressLimits::default());
    let error = preparation
        .well_founded_fix_target(&source_name())
        .expect_err(label);
    assert!(
        matches!(error, IngressError::UnsupportedNode { .. }),
        "{label}: {error:?}"
    );
    assert!(!preparation.well_founded_fix_checked, "{label}");
    assert_eq!(environment.logical_root(&KVMap::new()), original);
}

#[test]
fn actual_equation_preserves_every_universe_and_argument_position() {
    with_fixture(|environment| {
        let original = environment.logical_root(&KVMap::new());
        let logical = definition(environment, &source_name());
        let target = definition(environment, &target_name());
        let executable = definition(environment, &name("WellFounded.fixC._unsafe_rec"));
        let mut preparation = Preparation::new(environment, IngressLimits::default());
        assert!(preparation.has_implementation(&source_name()).unwrap());
        assert_eq!(
            preparation.well_founded_fix_target(&source_name()).unwrap(),
            Some(target_name())
        );
        assert!(preparation.well_founded_fix_checked);
        assert_eq!(
            preparation.executable_definition(&target_name()).unwrap(),
            Some(executable.clone())
        );
        assert_eq!(
            preparation.executable_definition(&source_name()).unwrap(),
            Some(executable.clone())
        );
        assert_eq!(executable.base.type_, target.base.type_);
        assert_eq!(executable.base.level_params, target.base.level_params);

        // These are the argument variables under fix's own six-binder
        // telescope, not synthesized proof constants or executable test input.
        let mut telescope = logical.base.type_.clone();
        let mut count = 0;
        while let ExprNode::ForallE { body, .. } = telescope.node() {
            count += 1;
            telescope = body.clone();
        }
        assert_eq!(count, 6);
        for levels in [
            vec![Level::zero(), Level::one()],
            vec![Level::one(), Level::zero()],
            vec![Level::one(), Level::one().succ().unwrap()],
        ] {
            let logical_type = preparation
                .universe_instance(&logical.base.type_, &logical.base.level_params, &levels)
                .unwrap();
            let executable_type = preparation
                .universe_instance(
                    &executable.base.type_,
                    &executable.base.level_params,
                    &levels,
                )
                .unwrap();
            assert_eq!(logical_type, executable_type);
            for arity in 0..=count {
                let args: Vec<_> = (0..arity)
                    .map(|index| Expr::bvar(count - index - 1).unwrap())
                    .collect();
                let head = Expr::const_(source_name(), levels.clone());
                let expected = args
                    .iter()
                    .cloned()
                    .fold(Expr::const_(target_name(), levels.clone()), Expr::app);
                assert_eq!(
                    preparation.implemented_by_call(&head, &args).unwrap(),
                    Some(expected)
                );
            }
        }
        assert_eq!(
            environment.find(&source_name()),
            Some(&ConstantInfo::Defn(logical))
        );
        assert_eq!(environment.logical_root(&KVMap::new()), original);
    });
}

#[test]
fn absent_equation_and_unrelated_names_gain_no_executable_replacement() {
    with_fixture(|environment| {
        let missing = change(environment, &equation_name(), None);
        let mut preparation = Preparation::new(&missing, IngressLimits::default());
        assert!(!preparation.has_implementation(&source_name()).unwrap());
        assert_eq!(
            preparation.well_founded_fix_target(&source_name()).unwrap(),
            None
        );
        assert!(!preparation.well_founded_fix_checked);
        let visited = preparation.visited;
        assert_eq!(
            preparation
                .well_founded_fix_target(&name("someOtherFix"))
                .unwrap(),
            None
        );
        assert_eq!(preparation.visited, visited);
    });
}

#[test]
fn theorem_spelling_never_authorizes_an_axiom_or_malformed_equation() {
    with_fixture(|environment| {
        let original = theorem(environment);
        let axiom = ConstantInfo::Axiom(AxiomVal {
            base: original.base.clone(),
            is_unsafe: false,
        });
        refused(
            &change(environment, &equation_name(), Some(axiom)),
            "same-name axiom",
        );
        let (head, arguments) = Preparation::new(environment, IngressLimits::default())
            .spine(&original.base.type_)
            .unwrap();
        assert_eq!(arguments.len(), 3);
        for mutation in 0..8 {
            let mut altered = original.clone();
            let mut head = head.clone();
            let mut arguments = arguments.clone();
            match mutation {
                0 => head = Expr::const_(name("HEq"), vec![Level::one()]),
                1 => {
                    arguments.pop();
                }
                2 => arguments[2] = Expr::const_(name("WellFounded.fixF"), vec![]),
                3 => arguments.swap(1, 2),
                4 => arguments[2] = Expr::app(arguments[2].clone(), nat::literal(0)),
                5 => {
                    let ExprNode::Const { name, .. } = arguments[2].node() else {
                        unreachable!()
                    };
                    arguments[2] = Expr::const_(name.clone(), vec![Level::zero(); 2]);
                }
                6 => arguments[0] = Expr::const_(name("Nat"), vec![]),
                7 => head = Expr::const_(name("Eq"), vec![]),
                _ => unreachable!(),
            }
            altered.base.type_ = arguments.into_iter().fold(head, Expr::app);
            // Retaining the original proof makes these intentionally invalid
            // matcher inputs. They never enter admission or an Engine result.
            refused(
                &change(
                    environment,
                    &equation_name(),
                    Some(ConstantInfo::Thm(altered)),
                ),
                &format!("malformed equation {mutation}"),
            );
        }
    });
}

#[test]
fn equations_cannot_specialize_or_repeat_universe_parameters() {
    with_fixture(|environment| {
        let original = theorem(environment);
        let (head, arguments) = Preparation::new(environment, IngressLimits::default())
            .spine(&original.base.type_)
            .unwrap();
        assert_eq!(original.base.level_params.len(), 2);
        for mutation in 0..4 {
            let mut altered = original.clone();
            let mut arguments = arguments.clone();
            match mutation {
                0 => altered.base.level_params[1] = altered.base.level_params[0].clone(),
                1 | 2 => {
                    let levels = if mutation == 1 {
                        vec![Level::zero(); 2]
                    } else {
                        vec![Level::param(altered.base.level_params[0].clone()); 2]
                    };
                    arguments[1] = Expr::const_(source_name(), levels.clone());
                    arguments[2] = Expr::const_(target_name(), levels);
                }
                3 => {
                    altered.base.level_params.clear();
                    arguments[1] = Expr::const_(source_name(), vec![]);
                    arguments[2] = Expr::const_(target_name(), vec![]);
                }
                _ => unreachable!(),
            }
            altered.base.type_ = arguments.into_iter().fold(head.clone(), Expr::app);
            refused(
                &change(
                    environment,
                    &equation_name(),
                    Some(ConstantInfo::Thm(altered)),
                ),
                &format!("invalid universe mapping {mutation}"),
            );
        }
    });
}

#[test]
fn endpoint_safety_types_and_the_complete_equality_family_are_required() {
    with_fixture(|environment| {
        for endpoint in [source_name(), target_name()] {
            let original = definition(environment, &endpoint);
            for mutation in 0..4 {
                let mut altered = original.clone();
                match mutation {
                    0 => altered.safety = DefinitionSafety::Unsafe,
                    1 => altered.safety = DefinitionSafety::Partial,
                    2 => altered.base.type_ = Expr::const_(name("Nat"), vec![]),
                    3 => {
                        altered.base.level_params.pop();
                    }
                    _ => unreachable!(),
                }
                refused(
                    &change(environment, &endpoint, Some(ConstantInfo::Defn(altered))),
                    &format!("{} endpoint {mutation}", endpoint.to_display_string()),
                );
            }
        }
        for label in [name("Eq"), name("Eq.refl"), name("Eq.rec")] {
            let mut altered = environment.find(&label).unwrap().clone();
            match &mut altered {
                ConstantInfo::Induct(value) => value.num_indices += 1,
                ConstantInfo::Ctor(value) => value.num_fields += 1,
                ConstantInfo::Rec(value) => value.rules[0].rhs = nat::literal(0),
                _ => unreachable!("canonical equality family member"),
            }
            refused(
                &change(environment, &label, Some(altered)),
                "corrupt equality family",
            );
        }
    });
}

#[test]
fn source_metadata_and_companions_keep_precedence_over_the_fix_equation() {
    with_fixture(|environment| {
        let source = definition(environment, &source_name());
        let levels: Vec<_> = source
            .base
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect();
        let head = Expr::const_(source_name(), levels.clone());
        let mut alias = source.clone();
        alias.base.name = name("WellFounded.fixtureImplementation");
        alias.all = vec![alias.base.name.clone()];
        let with_alias = environment
            .add_decl(ConstantInfo::Defn(alias.clone()))
            .unwrap();
        let overridden =
            implemented_by::register(&with_alias, &source_name(), &alias.base.name).unwrap();
        let mut preparation = Preparation::new(&overridden, IngressLimits::default());
        assert_eq!(
            preparation.implemented_by_call(&head, &[]).unwrap(),
            Some(Expr::const_(alias.base.name.clone(), levels.clone()))
        );
        assert_eq!(
            preparation.executable_definition(&source_name()).unwrap(),
            Some(alias.clone())
        );
        assert!(!preparation.well_founded_fix_checked);

        // The equality changes the head to fixC, which keeps its own ordinary
        // implementation attributes before choosing its recursive companion.
        let target_override =
            implemented_by::register(&with_alias, &target_name(), &alias.base.name).unwrap();
        let mut preparation = Preparation::new(&target_override, IngressLimits::default());
        assert_eq!(
            preparation.executable_definition(&source_name()).unwrap(),
            Some(alias)
        );
        assert!(preparation.well_founded_fix_checked);

        // Copying the actual logical body under its permitted Partial sibling
        // tests selection precedence; this raw model is never executed.
        let mut companion = source.clone();
        companion.base.name = Name::str(source_name(), "_unsafe_rec");
        companion.all = vec![companion.base.name.clone()];
        companion.safety = DefinitionSafety::Partial;
        let paired = environment
            .add_decl(ConstantInfo::Defn(companion.clone()))
            .unwrap();
        let mut preparation = Preparation::new(&paired, IngressLimits::default());
        assert_eq!(
            preparation.implemented_by_call(&head, &[]).unwrap(),
            Some(Expr::const_(companion.base.name.clone(), levels))
        );
        assert_eq!(
            preparation.executable_definition(&source_name()).unwrap(),
            Some(companion)
        );
        assert!(!preparation.well_founded_fix_checked);

        let mut invalid = definition(&paired, &Name::str(source_name(), "_unsafe_rec"));
        invalid.safety = DefinitionSafety::Safe;
        let malformed = change(
            &paired,
            &invalid.base.name.clone(),
            Some(ConstantInfo::Defn(invalid)),
        );
        let mut preparation = Preparation::new(&malformed, IngressLimits::default());
        assert_eq!(
            preparation.well_founded_fix_target(&source_name()).unwrap(),
            None,
            "a malformed source companion cannot fall back to the fix equation"
        );
        assert!(matches!(
            preparation.implemented_by_call(&head, &[]),
            Err(IngressError::UnsupportedNode { .. })
        ));
        assert!(!preparation.well_founded_fix_checked);

        let foreign = externs::register(
            environment,
            &source_name(),
            vec![externs::ExternEntry::Opaque],
        )
        .unwrap();
        let mut preparation = Preparation::new(&foreign, IngressLimits::default());
        assert!(matches!(
            preparation.well_founded_fix_target(&source_name()),
            Err(IngressError::UnsupportedNode { .. })
        ));
        assert!(!preparation.well_founded_fix_checked);
        let initializers = BTreeSet::from([source_name()]);
        let mut preparation = Preparation::new(environment, IngressLimits::default())
            .with_runtime_initializers(&initializers);
        assert!(matches!(
            preparation.well_founded_fix_target(&source_name()),
            Err(IngressError::UnsupportedNode { .. })
        ));
        assert!(!preparation.well_founded_fix_checked);
    });
}

#[test]
fn target_metadata_is_preserved_without_a_recursive_companion() {
    with_fixture(|environment| {
        let target = target_name();
        let without_companion =
            change(environment, &Name::str(target.clone(), "_unsafe_rec"), None);
        let original = without_companion.logical_root(&KVMap::new());
        let foreign = externs::register(
            &without_companion,
            &target,
            vec![externs::ExternEntry::Opaque],
        )
        .unwrap();
        refused(&foreign, "target extern without a recursive companion");

        let initializers = BTreeSet::from([target.clone()]);
        let mut preparation = Preparation::new(&without_companion, IngressLimits::default())
            .with_runtime_initializers(&initializers);
        assert!(matches!(
            preparation.well_founded_fix_target(&source_name()),
            Err(IngressError::UnsupportedNode { .. })
        ));
        assert!(!preparation.well_founded_fix_checked);
        assert_eq!(without_companion.logical_root(&KVMap::new()), original);

        // Explicit replacement keeps its existing priority over both target
        // metadata contracts. This raw selector fixture is never executed.
        let mut alias = definition(environment, &source_name());
        alias.base.name = name("WellFounded.fixtureTargetImplementation");
        alias.all = vec![alias.base.name.clone()];
        let with_alias = foreign.add_decl(ConstantInfo::Defn(alias.clone())).unwrap();
        let overridden = implemented_by::register(&with_alias, &target, &alias.base.name).unwrap();
        let original = overridden.logical_root(&KVMap::new());
        let mut preparation = Preparation::new(&overridden, IngressLimits::default())
            .with_runtime_initializers(&initializers);
        assert_eq!(
            preparation.well_founded_fix_target(&source_name()).unwrap(),
            Some(alias.base.name.clone())
        );
        assert!(preparation.well_founded_fix_checked);
        assert_eq!(
            preparation.executable_definition(&source_name()).unwrap(),
            Some(alias)
        );
        assert_eq!(overridden.logical_root(&KVMap::new()), original);
    });
}

#[test]
fn implementation_cycles_cannot_hide_behind_the_fix_equation() {
    with_fixture(|environment| {
        let cycle = implemented_by::register(environment, &target_name(), &source_name()).unwrap();
        refused(&cycle, "fixC implementation points back to fix");
    });
}

#[test]
fn resource_stops_never_cache_an_unfinished_fix_equation() {
    with_fixture(|environment| {
        let original = environment.logical_root(&KVMap::new());
        let mut complete = Preparation::new(environment, IngressLimits::default());
        assert_eq!(
            complete.well_founded_fix_target(&source_name()).unwrap(),
            Some(target_name())
        );
        let required = complete.visited;
        assert!(required > 2);
        for max_nodes in [0, required / 2, required - 1] {
            let mut bounded = Preparation::new(
                environment,
                IngressLimits {
                    max_nodes,
                    ..IngressLimits::default()
                },
            );
            assert!(matches!(
                bounded.well_founded_fix_target(&source_name()),
                Err(IngressError::ResourceLimit { resource: IngressResource::Nodes, limit, observed })
                    if limit == max_nodes && observed > limit
            ));
            assert!(!bounded.well_founded_fix_checked);
        }
        let mut recovered = Preparation::new(environment, IngressLimits::default());
        assert_eq!(
            recovered.well_founded_fix_target(&source_name()).unwrap(),
            Some(target_name())
        );
        assert!(recovered.well_founded_fix_checked);
        assert_eq!(recovered.visited, required);
        assert_eq!(environment.logical_root(&KVMap::new()), original);
    });
}
