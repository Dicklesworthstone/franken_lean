//! Tests for the embeddable EngineBuilder facade and ModuleApplyState integration.
//! (Plan §17.2; bead `franken_lean-7kc`).

#![forbid(unsafe_code)]

use fln::{
    DataValue, Declaration, Engine, EngineAdmissionLimits, EngineBuilder, EngineExecutionLimits,
    Environment, KVMap, Mode, ModuleApplyState, ModuleEpoch, Name, Outcome, ReproducibilityProfile,
};

#[test]
fn engine_builder_defaults() {
    let builder = Engine::builder();
    assert_eq!(builder.epoch(), &Engine::pinned_epoch());
    assert_eq!(builder.get_mode(), Mode::DEFAULT);
    assert_eq!(
        builder.get_reproducibility(),
        ReproducibilityProfile::Standard
    );
    assert!(builder.get_options().is_empty());
    assert!(builder.get_admission_limits().is_none());
    assert!(builder.get_execution_limits().is_none());

    let default_builder = EngineBuilder::default();
    assert_eq!(builder, default_builder);

    let empty_engine = builder.build_empty();
    assert_eq!(empty_engine.toolchain_epoch(), &Engine::pinned_epoch());
    assert_eq!(empty_engine.mode(), Mode::DEFAULT);
    assert_eq!(
        empty_engine.reproducibility(),
        ReproducibilityProfile::Standard
    );
    assert!(empty_engine.options().is_empty());
    assert!(empty_engine.environment().is_empty());
}

#[test]
fn engine_builder_custom_configuration() {
    let custom_epoch = ModuleEpoch::new("v4.32.0", "8c9756b28d64dab099da31a4c09229a9e6a2ef35");
    let mut options = KVMap::new();
    options.insert(
        Name::from_components(["pp", "all"]),
        DataValue::OfBool(true),
    );

    let limits = EngineAdmissionLimits::for_stack_bytes(4 * 1024 * 1024);
    let exec_limits = EngineExecutionLimits::for_stack_bytes(4 * 1024 * 1024);

    let builder = Engine::builder()
        .toolchain_epoch(custom_epoch.clone())
        .mode(Mode::Faithful)
        .reproducibility(ReproducibilityProfile::Certified)
        .options(options.clone())
        .admission_limits(limits)
        .execution_limits(exec_limits);

    assert_eq!(builder.epoch(), &custom_epoch);
    assert_eq!(builder.get_mode(), Mode::Faithful);
    assert_eq!(
        builder.get_reproducibility(),
        ReproducibilityProfile::Certified
    );
    assert_eq!(builder.get_options(), &options);
    assert_eq!(builder.get_admission_limits(), Some(limits));
    assert_eq!(builder.get_execution_limits(), Some(exec_limits));

    let engine = builder.build_empty();
    assert_eq!(engine.toolchain_epoch(), &custom_epoch);
    assert_eq!(engine.mode(), Mode::Faithful);
    assert_eq!(engine.reproducibility(), ReproducibilityProfile::Certified);
    assert_eq!(engine.options(), &options);
}

#[test]
fn engine_builder_build_from_environment() {
    let env = Environment::new();
    let custom_epoch = ModuleEpoch::new("v4.32.0", "8c9756b28d64dab099da31a4c09229a9e6a2ef35");
    let builder = Engine::builder()
        .toolchain_epoch(custom_epoch.clone())
        .mode(Mode::Frontier);

    let engine = builder.build_from_environment(env);
    assert_eq!(engine.toolchain_epoch(), &custom_epoch);
    assert_eq!(engine.mode(), Mode::Frontier);
    assert!(engine.environment().is_empty());
}

#[test]
fn engine_builder_seeded_nat_and_admission_continuity() {
    let limits = EngineAdmissionLimits::for_stack_bytes(2 * 1024 * 1024);
    let mut options = KVMap::new();
    options.insert(Name::from_components(["test", "key"]), DataValue::OfNat(42));

    let builder = Engine::builder()
        .mode(Mode::Sound)
        .options(options.clone())
        .admission_limits(limits);

    let outcome = builder.build_nat_seed().expect("seeded nat must succeed");
    let engine = match outcome {
        Outcome::Complete(engine) => engine,
        other => panic!("expected complete engine, got {:?}", other),
    };

    assert_eq!(engine.mode(), Mode::Sound);
    assert_eq!(engine.toolchain_epoch(), &Engine::pinned_epoch());
    assert_eq!(engine.options(), &options);
    assert!(
        engine
            .environment()
            .contains(&Name::from_components(["Nat"]))
    );

    // Verify admit_decl preserves configuration and advances the environment
    let axiom = Declaration::Axiom(fln::AxiomVal {
        base: fln::ConstantVal {
            name: Name::from_components(["postulate_foo"]),
            level_params: vec![],
            type_: fln::Expr::const_(Name::from_components(["Nat"]), vec![]),
        },
        is_unsafe: false,
    });
    let admission = engine
        .admit_decl(axiom, limits)
        .expect("admission should succeed");
    let successor = match admission {
        Outcome::Complete(admission) => admission.engine,
        other => panic!("expected complete admission, got {:?}", other),
    };

    assert_eq!(successor.mode(), Mode::Sound);
    assert_eq!(successor.toolchain_epoch(), &Engine::pinned_epoch());
    assert_eq!(successor.options(), &options);
    assert!(
        successor
            .environment()
            .contains(&Name::from_components(["postulate_foo"]))
    );
}

#[test]
fn engine_module_apply_state_integration() {
    let epoch = ModuleEpoch::new("v4.32.0", "8c9756b28d64dab099da31a4c09229a9e6a2ef35");
    let state = ModuleApplyState::from_epoch(epoch.clone())
        .expect("empty module apply state must construct cleanly");

    // Engine::from_module_apply_state
    let engine = Engine::from_module_apply_state(&state);
    assert_eq!(engine.toolchain_epoch(), &epoch);
    assert_eq!(engine.mode(), Mode::DEFAULT);
    assert_eq!(engine.reproducibility(), ReproducibilityProfile::Standard);
    assert_eq!(engine.environment().len(), state.environment().len());

    // builder.build_from_module_state with custom mode and options
    let mut extra_options = KVMap::new();
    extra_options.insert(
        Name::from_components(["extra", "opt"]),
        DataValue::OfBool(true),
    );
    let custom_engine = Engine::builder()
        .mode(Mode::Faithful)
        .reproducibility(ReproducibilityProfile::Certified)
        .options(extra_options.clone())
        .build_from_module_state(&state);

    assert_eq!(custom_engine.toolchain_epoch(), &epoch);
    assert_eq!(custom_engine.mode(), Mode::Faithful);
    assert_eq!(
        custom_engine.reproducibility(),
        ReproducibilityProfile::Certified
    );
    assert!(
        custom_engine
            .options()
            .contains(&Name::from_components(["extra", "opt"]))
    );

    // engine.apply_module_state
    let advanced = custom_engine.apply_module_state(&state);
    assert_eq!(advanced.toolchain_epoch(), &epoch);
    assert_eq!(advanced.mode(), Mode::Faithful);
    assert_eq!(
        advanced.reproducibility(),
        ReproducibilityProfile::Certified
    );
}
