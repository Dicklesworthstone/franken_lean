//! Source behavior through the real Engine elaborator and dual-check path.
//! Ownership fixtures below are synthetic caller inputs, as in the parent
//! registration tests. The live cell additionally compiles actual Lean macros;
//! neither fixture substitutes for production artifact admission.
use super::*;
use crate::imported_macros::source::{SourceMacroCheck, SourceMacroError, SourceMacroInvocation};
use crate::{Engine, EngineAdmissionLimits};
use std::sync::Arc;

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(crate::Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn bound_engine(module: &CheckedOleanModule) -> Engine {
    let seed = Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .unwrap();
    let environment = module
        .decoded
        .constants
        .iter()
        .fold(seed.environment().clone(), |environment, owner| {
            environment.add_decl(owner.clone()).unwrap()
        });
    // Only test fixtures can supply this ownership marker directly. The public
    // Engine adapter requires the production artifact import path to supply it.
    let mut engine = Engine::from_environment(environment);
    engine.imported_modules = Arc::new(BTreeSet::from([module.name.clone()]));
    engine
}

fn fixture() -> (Engine, RegisteredMacros, CheckedOleanModule) {
    let module = checked(
        "SourceLibrary",
        &[
            owner("SourceLibrary.right"),
            owner("SourceLibrary.skip"),
            owner("SourceLibrary.diagnostic"),
            owner("SourceLibrary.left"),
        ],
        &[],
    );
    let rows = journal(&[
        ("term_+_", "SourceLibrary.right", None),
        ("term_+_", "SourceLibrary.skip", None),
        ("term_-_", "SourceLibrary.diagnostic", None),
        ("term_+_", "SourceLibrary.left", Some("SourceScoped")),
    ]);
    let code = code(vec![
        selecting_function("SourceLibrary.right", 2),
        function("SourceLibrary.skip", Behavior::Unsupported),
        function("SourceLibrary.diagnostic", Behavior::Diagnostic),
        selecting_function("SourceLibrary.left", 0),
    ]);
    let registry = prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code,
    );
    (bound_engine(&module), registry, module)
}

fn run(
    engine: &Engine,
    registry: &RegisteredMacros,
    source: &[u8],
    limits: MacroTreeLimits,
    cancellation: Option<&dyn CancellationProbe>,
) -> SourceMacroCheck {
    engine.check_source_command_with_imported_macros(
        source,
        &KVMap::new(),
        admission(),
        SourceMacroInvocation {
            registry,
            context: &context(),
            state: MacroState {
                macro_scope: 17,
                ..MacroState::default()
            },
            lookup: None,
            limits,
            cancellation,
        },
    )
}

fn checked_constant<'a>(report: &'a SourceMacroCheck, expected: &str) -> &'a crate::SourceCheck {
    let Outcome::Complete(Ok(checked)) = &report.outcome else {
        panic!("{report:?}")
    };
    assert_eq!(
        checked.checker.ground,
        crate::CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
    );
    assert!(
        matches!(checked.checked_type.node(), ExprNode::Sort { level }
        if level.to_nat() == Some(1))
    );
    let crate::Declaration::Defn(declaration) = &checked.declaration else {
        panic!("a source check must validate a scratch definition")
    };
    assert!(
        matches!(declaration.value.node(), ExprNode::Const { name: value, .. }
        if value == &name(expected))
    );
    checked
}

#[test]
fn imported_ir_changes_a_real_source_query_and_preserves_original_coordinates() {
    let (engine, registry, _) = fixture();
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let source = b"\xef\xbb\xbf#check (Nat + Bool)\r\n";
    assert!(
        engine
            .check_source_command(source, &options, admission())
            .is_err(),
        "the unchanged standalone path cannot add two types"
    );
    let report = run(&engine, &registry, source, MacroTreeLimits::default(), None);
    let checked = checked_constant(&report, "Bool");
    assert_eq!(checked.environment_root, before);
    assert_eq!(checked.parsed.reconstruct_original(), source);
    assert_eq!(checked.parsed.query_term_normalized(), Some("(Nat + Bool)"));
    assert!(!checked.parsed.query_is_identifier());
    assert_eq!(report.attempts.len(), 2);
    assert_eq!(report.attempts[0].declaration, name("SourceLibrary.skip"));
    assert_eq!(report.attempts[1].declaration, name("SourceLibrary.right"));
    let state = report.state.as_ref().unwrap();
    assert_eq!(state.macro_scope, 19);
    assert_eq!(
        state.expanded_macro_declarations,
        [name("SourceLibrary.right")]
    );
    assert!(report.completed_vm_usage.steps > 0);
    assert_eq!(engine.logical_root(&options), before);

    let scoped = registry.activate_scoped(&name("SourceScoped")).unwrap();
    let scoped_report = run(
        &engine,
        &scoped,
        b"#check Nat + Bool",
        MacroTreeLimits::default(),
        None,
    );
    checked_constant(&scoped_report, "Nat");
    assert_eq!(scoped_report.attempts.len(), 1);
    assert_eq!(
        scoped_report.attempts[0].declaration,
        name("SourceLibrary.left")
    );
    checked_constant(
        &run(
            &engine,
            &registry,
            b"#check Nat + Bool",
            MacroTreeLimits::default(),
            None,
        ),
        "Bool",
    );
    assert_eq!(engine.logical_root(&options), before);
}

#[test]
fn source_binding_rejects_ambient_foreign_and_changed_owners_before_execution() {
    let (engine, registry, module) = fixture();
    let mut foreign = engine.clone();
    foreign.imported_modules = Arc::new(BTreeSet::from([name("OtherLibrary")]));
    let ambient = Engine::from_environment(engine.environment().clone());
    let mut changed = module.decoded.constants.clone();
    let ConstantInfo::Defn(owner) = &mut changed[0] else {
        unreachable!()
    };
    owner.value = Expr::lit(Literal::Nat(NatLit::from_u64(99)));
    let changed = checked("SourceLibrary", &changed, &[]);
    let changed = bound_engine(&changed);
    let inactive = registry.activate_scoped(&name("UnusedNamespace")).unwrap();
    for engine in [&foreign, &ambient, &changed] {
        for registry in [&registry, &inactive] {
            let before = engine.logical_root(&KVMap::new());
            let report = run(
                engine,
                registry,
                b"#check Nat + Bool",
                MacroTreeLimits::default(),
                None,
            );
            assert!(matches!(
                report.outcome,
                Outcome::Complete(Err(SourceMacroError::Binding(_)))
            ));
            assert!(report.attempts.is_empty());
            assert!(report.state.is_none());
            assert_eq!(report.completed_vm_usage.steps, 0);
            assert_eq!(engine.logical_root(&KVMap::new()), before);
        }
    }
}

#[test]
fn source_diagnostics_and_budgets_publish_neither_checks_nor_partial_state() {
    let (engine, registry, _) = fixture();
    let before = engine.logical_root(&KVMap::new());
    let diagnostic = run(
        &engine,
        &registry,
        b"#check Nat - Bool",
        MacroTreeLimits::default(),
        None,
    );
    assert!(matches!(
        &diagnostic.outcome,
        Outcome::Complete(Err(SourceMacroError::Diagnostic {
            declaration, reference, message, ..
        })) if declaration == &name("SourceLibrary.diagnostic")
            && reference.kind() == Some(&name("term_-_"))
            && message == "λ\0diagnostic"
    ));
    assert_eq!(diagnostic.attempts.len(), 1);
    assert!(diagnostic.state.is_none());

    let baseline = run(
        &engine,
        &registry,
        b"#check Nat + Bool",
        MacroTreeLimits::default(),
        None,
    );
    checked_constant(&baseline, "Bool");
    let mut exact = MacroTreeLimits::default();
    exact.dispatch.execution.vm.max_steps = baseline.completed_vm_usage.steps;
    checked_constant(
        &run(&engine, &registry, b"#check Nat + Bool", exact, None),
        "Bool",
    );
    let mut short_steps = exact;
    short_steps.dispatch.execution.vm.max_steps -= 1;
    let mut short_attempts = MacroTreeLimits::default();
    short_attempts.dispatch.max_attempts = 1;
    let mut short_visits = MacroTreeLimits::default();
    short_visits.max_visits = 0;
    let mut short_source = MacroTreeLimits::default();
    short_source.dispatch.execution.syntax.max_bytes = 1;
    for limits in [short_steps, short_attempts, short_visits, short_source] {
        let report = run(&engine, &registry, b"#check Nat + Bool", limits, None);
        assert!(
            matches!(report.outcome, Outcome::Inconclusive(_)),
            "{report:?}"
        );
        assert!(report.state.is_none());
        assert_eq!(engine.logical_root(&KVMap::new()), before);
    }
    struct Cancelled;
    impl CancellationProbe for Cancelled {
        fn is_cancelled(&self) -> bool {
            true
        }
    }
    let cancelled = run(
        &engine,
        &registry,
        b"#check Nat + Bool",
        MacroTreeLimits::default(),
        Some(&Cancelled),
    );
    assert!(matches!(cancelled.outcome, Outcome::Inconclusive(_)));
    assert!(cancelled.attempts.is_empty());
    assert!(cancelled.state.is_none());
    checked_constant(
        &run(
            &engine,
            &registry,
            b"#check Nat + Bool",
            MacroTreeLimits::default(),
            None,
        ),
        "Bool",
    );
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn source_shortcut_preserves_global_queries_and_refuses_unhandled_atomic_macros() {
    let module = checked("AtomicLibrary", &[owner("AtomicLibrary.fail")], &[]);
    let rows = journal(&[("ident", "AtomicLibrary.fail", None)]);
    let code = code(vec![function("AtomicLibrary.fail", Behavior::Diagnostic)]);
    let registry = prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code,
    );
    let engine = bound_engine(&module);
    let mut no_execution = MacroTreeLimits::default();
    no_execution.dispatch.max_attempts = 0;
    no_execution.dispatch.execution.vm.max_steps = 0;
    let global = run(&engine, &registry, b"#check Nat", no_execution, None);
    assert!(
        checked_constant(&global, "Nat")
            .parsed
            .query_is_identifier()
    );
    assert!(global.attempts.is_empty());
    assert_eq!(global.state.unwrap().macro_scope, 17);
    let unknown = run(
        &engine,
        &registry,
        b"#check Missing",
        MacroTreeLimits::default(),
        None,
    );
    assert!(matches!(
        unknown.outcome,
        Outcome::Complete(Err(SourceMacroError::AtomicExpansion { kind }))
            if kind == name("ident")
    ));
    assert!(unknown.state.is_none());

    for source in [b"#eval 1".as_slice(), b"#synth Nat".as_slice()] {
        let wrong_command = run(&engine, &registry, source, MacroTreeLimits::default(), None);
        assert!(matches!(
            wrong_command.outcome,
            Outcome::Complete(Err(SourceMacroError::Frontend(error)))
                if matches!(*error, crate::EngineExecutionError::StandaloneCheckRequired)
        ));
        assert!(wrong_command.attempts.is_empty());
    }
}

#[test]
fn source_refuses_imported_tactics_left_for_the_tactic_evaluator() {
    let module = checked("TacticLibrary", &[owner("TacticLibrary.fail")], &[]);
    let rows = journal(&[("Lean.Parser.Tactic.tacticRfl", "TacticLibrary.fail", None)]);
    let code = code(vec![function("TacticLibrary.fail", Behavior::Diagnostic)]);
    let registry = prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code,
    );
    let engine = bound_engine(&module);
    let report = run(
        &engine,
        &registry,
        b"#check (by rfl : Nat = Nat)",
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(
            &report.outcome,
            Outcome::Complete(Err(SourceMacroError::TacticExpansion { kind }))
                if kind == &name("Lean.Parser.Tactic.tacticRfl")
        ),
        "{report:?}"
    );
    assert!(report.attempts.is_empty());
    assert!(report.state.is_none());
}

#[test]
fn source_lookup_capability_changes_expansion_using_the_admitted_snapshot() {
    use crate::imported_macros::lookup::EnvironmentMacroLookup;

    let module = checked(
        "SourceCapability",
        &[
            owner("SourceCapability.choose"),
            owner("SourceCapability.skip"),
        ],
        &[],
    );
    let rows = journal(&[
        ("term_+_", "SourceCapability.choose", None),
        ("term_+_", "SourceCapability.skip", None),
    ]);
    let code = code(vec![
        super::lookup::has_decl_selector("SourceCapability.choose"),
        function("SourceCapability.skip", Behavior::Unsupported),
    ]);
    let registry = prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code,
    );
    let engine = bound_engine(&module);
    let before = engine.logical_root(&KVMap::new());
    let source = b"#check Nat + (Nat + Bool)";
    let absent = run(&engine, &registry, source, MacroTreeLimits::default(), None);
    assert!(matches!(
        absent.outcome,
        Outcome::Complete(Err(SourceMacroError::Execution(_)))
    ));
    assert!(absent.state.is_none());

    let module_name = name("SourceQuery");
    let namespace = Name::anonymous();
    let old_lookup = EnvironmentMacroLookup::new(engine.environment(), &module_name, &namespace);
    let invoke = |engine: &Engine, lookup: &dyn fln_vm::macro_native::MacroLookup| {
        engine.check_source_command_with_imported_macros(
            source,
            &KVMap::new(),
            admission(),
            SourceMacroInvocation {
                registry: &registry,
                context: &context(),
                state: MacroState::default(),
                lookup: Some(lookup),
                limits: MacroTreeLimits::default(),
                cancellation: None,
            },
        )
    };
    let missing = invoke(&engine, &old_lookup);
    checked_constant(&missing, "Bool");
    assert_eq!(missing.attempts.len(), 4);
    assert!(missing.attempts.iter().any(|attempt| {
        attempt
            .native_functions
            .iter()
            .any(|id| id == "mirror:Lean.Macro.hasDecl")
    }));

    let successor = engine
        .admit_source_declaration(b"def available : Nat := 0", &KVMap::new(), admission())
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let after = successor.logical_root(&KVMap::new());
    let new_lookup = EnvironmentMacroLookup::new(successor.environment(), &module_name, &namespace);
    let available = invoke(&successor, &new_lookup);
    checked_constant(&available, "Nat");
    assert_eq!(available.attempts.len(), 2);
    checked_constant(&invoke(&engine, &old_lookup), "Bool");
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    assert_eq!(successor.logical_root(&KVMap::new()), after);
}

#[test]
fn source_expansion_does_not_bypass_the_independent_checker() {
    let (engine, registry, _) = fixture();
    let before = engine.logical_root(&KVMap::new());
    let term = fln_checker::term::TermBudget::new(0, 0).with_max_arena_nodes(0);
    let whnf = fln_checker::whnf::WhnfBudget::new(0, 0, term);
    let inference = fln_checker::infer::InferenceBudget::new(0, 0, term, term).with_whnf(whnf);
    let mut constrained = admission();
    constrained.checker.admission =
        crate::CheckerAdmissionBudget::new(inference, whnf, inference.defeq);
    let report = engine.check_source_command_with_imported_macros(
        b"#check Nat + Bool",
        &KVMap::new(),
        constrained,
        SourceMacroInvocation {
            registry: &registry,
            context: &context(),
            state: MacroState::default(),
            lookup: None,
            limits: MacroTreeLimits::default(),
            cancellation: None,
        },
    );
    assert!(
        matches!(
            &report.outcome,
            Outcome::Complete(Err(SourceMacroError::Frontend(error)))
                if matches!(error.as_ref(), crate::EngineExecutionError::CouncilNoAnswer { summary }
                    if summary.contains("fln-checker"))
        ),
        "{report:?}"
    );
    assert_eq!(report.attempts.len(), 2);
    assert!(report.state.is_none());
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[path = "source/reference.rs"]
mod reference;
