//! Selector tests use the real decoded pinned declarations, not recreated WF
//! types. Mutated fixtures test refusal only; they are never executed. The
//! independent mixed-chain test below instead uses source-admitted equations.
use super::*;
use fln_elab::{externs, implemented_by};
use std::path::PathBuf;
use std::sync::OnceLock;

const STACK: usize = 256 * 1024 * 1024;
const PAIRS: [(&str, &str, &str); 5] = [
    ("WellFounded.fix", "WellFounded.fixC", "WellFounded.fix_eq_fixC"),
    ("Acc.rec", "Acc.recC", "Acc.rec_eq_recC"),
    ("Acc.ndrec", "Acc.ndrecC", "Acc.ndrec_eq_ndrecC"),
    ("Acc.ndrecOn", "Acc.ndrecOnC", "Acc.ndrecOn_eq_ndrecOnC"),
    ("WellFounded.fixF", "WellFounded.fixFC", "WellFounded.fixF_eq_fixFC"),
];

fn fixture() -> Option<&'static Environment> {
    static FIXTURE: OnceLock<Option<Environment>> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let library = std::env::var_os("FLN_REFERENCE_LIB")
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            }))
            .filter(|path| path.is_dir());
        let Some(library) = library else {
            assert!(std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "the pinned Reference library is required");
            eprintln!("SKIP: set FLN_REFERENCE_LIB to the pinned lib/lean");
            return None;
        };
        let mut environment = Environment::new();
        for module in ["Init/Prelude", "Init/WF", "Init/WFComputable"] {
            let path = library.join(module).with_extension("olean");
            let parts = [
                std::fs::read(&path).expect("actual exported WF artifact"),
                std::fs::read(path.with_extension("olean.server")).expect("actual server WF artifact"),
                std::fs::read(path.with_extension("olean.private")).expect("actual private WF artifact"),
            ];
            let decoded = decode_olean_module_artifacts(
                &parts[0], &parts[1], &parts[2], OleanDecodeLimits::new(STACK),
            ).expect("decode the actual pinned WF declarations");
            for constant in decoded.constants {
                if !environment.contains(constant.name()) {
                    environment = environment.add_decl(constant).unwrap();
                }
            }
        }
        for (source, target, equation) in PAIRS {
            for label in [source, target, equation] {
                assert!(environment.contains(&name(label)), "{label}");
            }
        }
        Some(environment)
    }).as_ref()
}

fn with_fixture(test: impl FnOnce(&Environment) + Send + 'static) {
    std::thread::Builder::new().stack_size(STACK).spawn(move || {
        if let Some(environment) = fixture() {
            test(environment);
        }
    }).unwrap().join().unwrap();
}

fn change(environment: &Environment, label: &Name, replacement: Option<ConstantInfo>) -> Environment {
    let mut altered = Environment::new();
    for (candidate, _) in environment.constants() {
        if candidate != label {
            altered = altered.with_entry(environment.entry(candidate).unwrap()).unwrap();
        }
    }
    for (journal, state) in environment.extensions() {
        altered = altered.register_extension(state.descriptor.clone()).unwrap();
        for entry in state.entries() {
            altered = altered.push_extension_entry(journal, entry.payload.clone()).unwrap();
        }
    }
    if let Some(replacement) = replacement {
        assert_eq!(replacement.name(), label);
        altered = altered.add_decl(replacement).unwrap();
    }
    altered
}

#[test]
fn all_five_actual_equations_preserve_universes_and_partial_application_spines() {
    with_fixture(|environment| {
        let root = environment.logical_root(&KVMap::new());
        for (source, target, _) in PAIRS {
            let original = environment.find(&name(source)).unwrap().constant_val();
            let mut preparation = Preparation::new(environment, IngressLimits::default());
            assert!(preparation.has_implementation(&name(source)).unwrap(), "{source}");
            assert_eq!(preparation.well_founded_fix_target(&name(source)).unwrap(), Some(name(target)));
            let mut arity = 0;
            let mut telescope = &original.type_;
            while let ExprNode::ForallE { body, .. } = telescope.node() {
                arity += 1;
                telescope = body;
            }
            assert!(arity > 0);
            for level in [Level::one(), Level::one().succ().unwrap()] {
                let levels = vec![level; original.level_params.len()];
                for supplied in 0..=arity + 1 {
                    // Transformation-only inputs, including one overapplication.
                    // They verify that the selector never drops an argument.
                    let args: Vec<_> = (0..supplied).map(|i| nat::literal(i as u64)).collect();
                    let head = Expr::const_(name(source), levels.clone());
                    let expected = args.iter().cloned()
                        .fold(Expr::const_(name(target), levels.clone()), Expr::app);
                    assert_eq!(preparation.implemented_by_call(&head, &args).unwrap(), Some(expected),
                        "{source}, {supplied} arguments");
                }
            }
        }
        assert_eq!(environment.logical_root(&KVMap::new()), root);
    });
}

#[test]
fn cached_fix_equation_does_not_authorize_missing_or_malformed_sibling_equations() {
    with_fixture(|environment| {
        for (source, _, equation) in PAIRS.into_iter().skip(1) {
            let label = name(equation);
            let missing = change(environment, &label, None);
            let mut preparation = Preparation::new(&missing, IngressLimits::default());
            assert_eq!(preparation.well_founded_fix_target(&source_name()).unwrap(), Some(target_name()));
            assert!(preparation.well_founded_fix_checked);
            assert_eq!(preparation.well_founded_fix_target(&name(source)).unwrap(), None);
            let ConstantInfo::Thm(original) = environment.find(&label).unwrap() else { panic!("actual theorem"); };
            let (head, args) = Preparation::new(environment, IngressLimits::default())
                .spine(&original.base.type_).unwrap();
            for mutation in 0..3 {
                let mut changed = original.clone();
                let mut args = args.clone();
                match mutation {
                    0 => args.swap(1, 2),
                    1 => args[0] = Expr::const_(name("Nat"), vec![]),
                    _ => { args.pop(); }
                }
                changed.base.type_ = args.into_iter().fold(head.clone(), Expr::app);
                let damaged = change(environment, &label, Some(ConstantInfo::Thm(changed)));
                let mut preparation = Preparation::new(&damaged, IngressLimits::default());
                preparation.well_founded_fix_target(&source_name()).unwrap();
                assert!(matches!(preparation.well_founded_fix_target(&name(source)),
                    Err(IngressError::UnsupportedNode { .. })), "{equation}, mutation {mutation}");
            }
        }
    });
}

#[test]
fn each_equation_requires_a_theorem_and_safe_executable_target() {
    with_fixture(|environment| {
        for (source, target, equation) in PAIRS {
            let equation = name(equation);
            let base = environment.find(&equation).unwrap().constant_val().clone();
            let counterfeit = change(environment, &equation, Some(ConstantInfo::Axiom(AxiomVal {
                base, is_unsafe: false,
            })));
            assert!(Preparation::new(&counterfeit, IngressLimits::default())
                .well_founded_fix_target(&name(source)).is_err());
            let target = name(target);
            let ConstantInfo::Defn(original) = environment.find(&target).unwrap() else { panic!("actual target"); };
            for safety in [DefinitionSafety::Unsafe, DefinitionSafety::Partial] {
                let mut changed = original.clone();
                changed.safety = safety;
                let damaged = change(environment, &target, Some(ConstantInfo::Defn(changed)));
                assert!(Preparation::new(&damaged, IngressLimits::default())
                    .well_founded_fix_target(&name(source)).is_err());
            }
        }
        let source = name("Acc.rec");
        let ConstantInfo::Rec(original) = environment.find(&source).unwrap() else { panic!("actual primitive recursor"); };
        let mut changed = original.clone();
        changed.is_unsafe = true;
        let damaged = change(environment, &source, Some(ConstantInfo::Rec(changed)));
        assert!(Preparation::new(&damaged, IngressLimits::default())
            .well_founded_fix_target(&source).is_err());
    });
}

#[test]
fn all_equations_preserve_runtime_initializers_and_explicit_extern_authority() {
    with_fixture(|environment| {
        for (source, target, _) in PAIRS {
            for label in [name(source), name(target)] {
                let initialized = BTreeSet::from([label.clone()]);
                let mut preparation = Preparation::new(environment, IngressLimits::default())
                    .with_runtime_initializers(&initialized);
                assert!(preparation.well_founded_fix_target(&name(source)).is_err(), "{label:?}");
                if matches!(environment.find(&label), Some(ConstantInfo::Defn(_))) {
                    let foreign = externs::register(
                        environment, &label, vec![externs::ExternEntry::Opaque],
                    ).unwrap();
                    assert!(Preparation::new(&foreign, IngressLimits::default())
                        .well_founded_fix_target(&name(source)).is_err(), "{label:?}");
                }
            }
        }
    });
}

#[test]
fn each_equation_is_metered_and_failed_work_does_not_publish_a_fix_cache() {
    with_fixture(|environment| {
        for (source, target, _) in PAIRS {
            let mut full = Preparation::new(environment, IngressLimits::default());
            assert_eq!(full.well_founded_fix_target(&name(source)).unwrap(), Some(name(target)));
            let required = full.visited;
            assert!(required > 1);
            for allowed in [0, required / 2, required - 1] {
                let mut limited = Preparation::new(environment, IngressLimits {
                    max_nodes: allowed, ..IngressLimits::default()
                });
                assert!(matches!(limited.well_founded_fix_target(&name(source)),
                    Err(IngressError::ResourceLimit { .. })), "{source}, limit {allowed}");
                assert!(!limited.well_founded_fix_checked);
            }
            let mut retry = Preparation::new(environment, IngressLimits::default());
            assert_eq!(retry.well_founded_fix_target(&name(source)).unwrap(), Some(name(target)));
            assert_eq!(retry.visited, required);
        }
    });
}

#[test]
fn mixed_equation_attribute_cycles_are_detected_after_source_admission() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits).unwrap().into_complete().unwrap()
        .check_source_files(&[br#"
namespace WellFounded
noncomputable def fix : Nat := 7
def fixC : Nat := 7
theorem fix_eq_fixC : fix = fixC := rfl
noncomputable def fixF : Nat := 7
def fixFC : Nat := 7
theorem fixF_eq_fixFC : fixF = fixFC := rfl
end WellFounded
"#], &KVMap::new(), SourceCheckLimits::new(limits))
        .unwrap().into_complete().unwrap().engine;
    let root = engine.logical_root(&KVMap::new());
    let first = implemented_by::register(&engine.environment, &target_name(), &name("WellFounded.fixF")).unwrap();
    let mut valid = Preparation::new(&first, IngressLimits::default());
    assert_eq!(valid.well_founded_fix_target(&source_name()).unwrap(), Some(name("WellFounded.fixFC")));
    assert!(valid.well_founded_fix_checked);
    let cyclic = implemented_by::register(&first, &name("WellFounded.fixFC"), &source_name()).unwrap();
    let mut rejected = Preparation::new(&cyclic, IngressLimits::default());
    assert!(matches!(rejected.well_founded_fix_target(&source_name()),
        Err(IngressError::UnsupportedNode { kind: "well-founded executable replacement cycle" })));
    assert!(!rejected.well_founded_fix_checked);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn interface_comparison_ignores_labels_but_not_domains_or_binder_conventions() {
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let nat = Expr::const_(name("Nat"), vec![]);
    let interface = |label, domain, info| Expr::forall_e(name(label), domain, nat.clone(), info);
    let left = interface("original", nat.clone(), BinderInfo::Default);
    let right = interface("generated", nat.clone(), BinderInfo::Default);
    assert!(preparation.well_founded_interface_matches(&left, &right).unwrap());
    let wrong_domain = interface("original", Expr::const_(name("String"), vec![]), BinderInfo::Default);
    assert!(!preparation.well_founded_interface_matches(&left, &wrong_domain).unwrap());
    let wrong_info = interface("original", nat.clone(), BinderInfo::Implicit);
    assert!(!preparation.well_founded_interface_matches(&left, &wrong_info).unwrap());
    let mut stopped = Preparation::new(&environment, IngressLimits { max_nodes: 0, ..IngressLimits::default() });
    assert!(matches!(stopped.well_founded_interface_matches(&left, &right), Err(IngressError::ResourceLimit { .. })));
}
