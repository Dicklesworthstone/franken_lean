use super::*;

fn model() -> Vec<ConstantInfo> {
    let mut values = scalar_records();
    for declaration in support() {
        match declaration {
            Declaration::Defn(value) => values.push(ConstantInfo::Defn(value)),
            Declaration::Inductive(block) => {
                values.extend(block.types.into_iter().map(ConstantInfo::Induct));
                values.extend(block.ctors.into_iter().map(ConstantInfo::Ctor));
                values.extend(block.recursors.into_iter().map(ConstantInfo::Rec));
            }
            _ => unreachable!("fixed contract support"),
        }
    }
    values.extend(
        ["String.Internal.append", "String.Internal.length"]
            .map(|label| ConstantInfo::Opaque(opaque(label))),
    );
    values
}

fn bare_environment(change: impl Fn(&mut ConstantInfo)) -> Environment {
    model()
        .into_iter()
        .fold(Environment::new(), |env, mut value| {
            change(&mut value);
            env.add_decl(value).unwrap()
        })
}

fn canonical_entry(label: &str) -> fln_elab::externs::ExternEntry {
    let row = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .find(|row| row.name == label)
        .unwrap();
    fln_elab::externs::ExternEntry::Standard {
        backend: name("all"),
        symbol: row.symbol.to_owned(),
    }
}

fn environment(change: impl Fn(&mut ConstantInfo)) -> Environment {
    ["String.Internal.append", "String.Internal.length"]
        .into_iter()
        .fold(bare_environment(change), |env, label| {
            fln_elab::externs::register(&env, &name(label), vec![canonical_entry(label)]).unwrap()
        })
}

#[test]
fn complete_opaque_contract_selects_existing_pure_rows_and_meters_every_comparison() {
    let env = environment(|_| {});
    for label in ["String.Internal.append", "String.Internal.length"] {
        let mut work = 0;
        assert!(
            imported_string_internal_matches(
                &env,
                &name(label),
                &mut None,
                &mut work,
                IngressLimits::default()
            )
            .unwrap()
        );
        assert!(work > 100, "both opaque and support contracts are visited");
        let binding =
            executable_intrinsic_binding(&env, &name(label), &mut 0, IngressLimits::default())
                .unwrap()
                .unwrap();
        assert_eq!(binding.row, format!("extern:{label}"));
        assert_eq!(binding.effect, fln_comp::fir::EffectClass::Pure);
        assert_eq!(
            binding.result_ownership,
            fln_comp::flbc::ResultOwnership::Owned
        );
        assert!(matches!(
            imported_string_internal_matches(
                &env,
                &name(label),
                &mut None,
                &mut 0,
                IngressLimits {
                    max_nodes: 1,
                    ..IngressLimits::default()
                }
            ),
            Err(IngressError::ResourceLimit { .. })
        ));
    }
}

#[test]
fn changed_opaque_metadata_values_and_support_never_acquire_native_authority() {
    for target in ["String.Internal.append", "String.Internal.length"] {
        for mutation in 0..9 {
            let env = environment(|info| {
                if info.name() == &name(target) {
                    let ConstantInfo::Opaque(value) = info else {
                        unreachable!()
                    };
                    match mutation {
                        0 => {
                            value.value = lambda(
                                constant("String"),
                                Expr::lit(Literal::Str("counterfeit".to_owned())),
                            )
                        }
                        1 => value.base.type_ = arrow(constant("Nat"), constant("Nat")),
                        2 => value.is_unsafe = true,
                        3 => value.all = vec![name(target), name("counterfeitPeer")],
                        4 => value.base.level_params = vec![name("u")],
                        5 => {
                            *info = ConstantInfo::Defn(DefinitionVal {
                                base: value.base.clone(),
                                value: value.value.clone(),
                                hints: ReducibilityHints::Regular(1),
                                safety: DefinitionSafety::Safe,
                                all: value.all.clone(),
                            })
                        }
                        _ => {}
                    }
                } else if mutation == 6 && info.name() == &name("String.instInhabited") {
                    let ConstantInfo::Defn(value) = info else {
                        unreachable!()
                    };
                    value.value = apply(
                        Expr::const_(name("Inhabited.mk"), vec![Level::one()]),
                        [
                            constant("String"),
                            Expr::lit(Literal::Str("counterfeit".to_owned())),
                        ],
                    );
                } else if mutation == 7 && info.name() == &name("Pi.instInhabited") {
                    let ConstantInfo::Defn(value) = info else {
                        unreachable!()
                    };
                    value.safety = DefinitionSafety::Unsafe;
                } else if mutation == 8 && info.name() == &name("String.ofByteArray") {
                    let ConstantInfo::Ctor(value) = info else {
                        unreachable!()
                    };
                    value.num_fields = 1;
                }
            });
            assert!(
                matches!(
                    imported_string_internal_matches(
                        &env,
                        &name(target),
                        &mut None,
                        &mut 0,
                        IngressLimits::default()
                    ),
                    Err(IngressError::UnsupportedNode { .. })
                ),
                "{target} mutation {mutation}"
            );
            assert!(
                matches!(
                    executable_intrinsic_binding(
                        &env,
                        &name(target),
                        &mut 0,
                        IngressLimits::default()
                    ),
                    Err(IngressError::UnsupportedNode { .. })
                ),
                "{target} mutation {mutation}"
            );
        }
    }
}

#[test]
fn exact_bootstrap_opaque_and_prelude_dependencies_match_the_pin() {
    let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(std::path::PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference is required"
        );
        eprintln!("SKIP: FLN_REFERENCE_LIB absent");
        return;
    };
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let expected = model();
            let names: std::collections::BTreeSet<_> =
                expected.iter().map(|info| info.name().clone()).collect();
            let mut environment = Environment::new();
            for module in ["Init/Prelude", "Init/Data/String/Bootstrap"] {
                let path = library.join(module).with_extension("olean");
                let parts = [
                    std::fs::read(&path).unwrap(),
                    std::fs::read(path.with_extension("olean.server")).unwrap(),
                    std::fs::read(path.with_extension("olean.private")).unwrap(),
                ];
                let decoded = decode_olean_module_artifacts(
                    &parts[0],
                    &parts[1],
                    &parts[2],
                    OleanDecodeLimits::new(256 * 1024 * 1024),
                )
                .unwrap();
                for info in decoded
                    .constants
                    .into_iter()
                    .filter(|info| names.contains(info.name()))
                {
                    environment = environment.add_decl(info).unwrap();
                }
            }
            for expected in expected {
                let mut comparison = Comparison {
                    visited: &mut 0,
                    limits: IngressLimits::default(),
                };
                assert!(
                    comparison.constant(&environment, expected.clone()).unwrap(),
                    "pinned contract mismatch: {}",
                    expected.name().to_display_string()
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn opaque_models_need_exact_extern_entries_not_just_matching_constants() {
    use fln_elab::externs::{self, ExternEntry};
    for label in ["String.Internal.append", "String.Internal.length"] {
        let bare = bare_environment(|_| {});
        assert!(
            !imported_string_internal_matches(
                &bare,
                &name(label),
                &mut None,
                &mut 0,
                IngressLimits::default()
            )
            .unwrap()
        );
        let canonical = canonical_entry(label);
        for entries in [
            vec![],
            vec![ExternEntry::Opaque],
            vec![ExternEntry::Adhoc {
                backend: name("all"),
            }],
            vec![ExternEntry::Inline {
                backend: name("all"),
                pattern: "wrong".to_owned(),
            }],
            vec![ExternEntry::Standard {
                backend: name("c"),
                symbol: match &canonical {
                    ExternEntry::Standard { symbol, .. } => symbol.clone(),
                    _ => unreachable!(),
                },
            }],
            vec![ExternEntry::Standard {
                backend: name("all"),
                symbol: "counterfeit".to_owned(),
            }],
            vec![canonical.clone(), ExternEntry::Opaque],
            vec![ExternEntry::Opaque, canonical],
        ] {
            let env = externs::register(&bare, &name(label), entries).unwrap();
            assert!(matches!(
                executable_intrinsic_binding(&env, &name(label), &mut 0, IngressLimits::default()),
                Err(IngressError::UnsupportedNode { .. })
            ));
        }
    }
}

#[test]
fn explicit_extern_cannot_override_a_selected_logical_nat_model() {
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        16 * 1024 * 1024,
    )))
    .unwrap()
    .into_complete()
    .unwrap();
    let target = name("Nat.add");
    assert!(
        executable_intrinsic_binding(
            engine.environment(),
            &target,
            &mut 0,
            IngressLimits::default()
        )
        .unwrap()
        .is_some()
    );
    let original = canonical_entry("Nat.add");
    let exact = fln_elab::externs::register(engine.environment(), &target, vec![original]).unwrap();
    assert!(
        executable_intrinsic_binding(&exact, &target, &mut 0, IngressLimits::default())
            .unwrap()
            .is_some()
    );
    let changed = fln_elab::externs::register(
        &exact,
        &target,
        vec![fln_elab::externs::ExternEntry::Opaque],
    )
    .unwrap();
    assert!(matches!(
        executable_intrinsic_binding(&changed, &target, &mut 0, IngressLimits::default()),
        Err(IngressError::UnsupportedNode { .. })
    ));
}

#[test]
fn extern_table_is_metered_once_per_preparation_and_failures_are_retryable() {
    let env = environment(|_| {});
    let mut cache = None;
    let target = name("String.Internal.length");
    assert!(matches!(
        executable_intrinsic_binding_cached(
            &env,
            &target,
            &mut 0,
            IngressLimits {
                max_nodes: 2,
                ..IngressLimits::default()
            },
            &mut cache
        ),
        Err(IngressError::ResourceLimit { .. })
    ));
    assert!(
        cache.is_none(),
        "budget failures cannot populate the table cache"
    );
    let mut first = 0;
    assert!(
        executable_intrinsic_binding_cached(
            &env,
            &target,
            &mut first,
            IngressLimits::default(),
            &mut cache
        )
        .unwrap()
        .is_some()
    );
    let mut next = 0;
    assert!(
        executable_intrinsic_binding_cached(
            &env,
            &target,
            &mut next,
            IngressLimits::default(),
            &mut cache
        )
        .unwrap()
        .is_some()
    );
    let journal = env.extension(&fln_elab::externs::journal_name()).unwrap();
    let bytes: usize = journal.entries().map(|entry| entry.payload.len()).sum();
    assert_eq!(
        first - next,
        1 + journal.len() + bytes,
        "only repeated journal parsing is omitted; model checks and every lookup are still charged"
    );
    assert!(matches!(
        executable_intrinsic_binding_cached(
            &env,
            &target,
            &mut 0,
            IngressLimits {
                max_nodes: 0,
                ..IngressLimits::default()
            },
            &mut cache
        ),
        Err(IngressError::ResourceLimit { .. })
    ));
}

#[test]
fn explicit_externs_cannot_disappear_through_canonical_float_folds() {
    let budget = Budget::for_stack_bytes(16 * 1024 * 1024);
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(budget))
        .unwrap()
        .into_complete()
        .unwrap();
    for (label, arguments) in [
        ("Float.ofScientific", "15 Bool.false 1"),
        ("Float32.ofScientific", "15 Bool.false 1"),
        ("Float.ofNat", "42"),
        ("Float32.ofNat", "42"),
        ("Nat.toFloat", "42"),
        ("Nat.toFloat32", "42"),
    ] {
        let source = format!("def floatResult := {label} {arguments}");
        engine
            .execute_source_definition(
                source.as_bytes(),
                &KVMap::new(),
                EngineExecutionLimits::new(budget),
            )
            .unwrap_or_else(|error| panic!("canonical {label}: {error:?}"))
            .into_complete()
            .unwrap();
        let changed = Engine::from_environment(
            fln_elab::externs::register(
                engine.environment(),
                &name(label),
                vec![fln_elab::externs::ExternEntry::Opaque],
            )
            .unwrap(),
        );
        let root = changed.logical_root(&KVMap::new());
        let failure = changed
            .execute_source_definition(
                source.as_bytes(),
                &KVMap::new(),
                EngineExecutionLimits::new(budget),
            )
            .expect_err("constant folding must not discard an explicit runtime implementation");
        assert!(
            matches!(
                failure,
                EngineExecutionError::Ingress(IngressError::UnsupportedNode { .. })
            ),
            "{label}: {failure:?}"
        );
        assert_eq!(changed.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn oversized_extern_journal_is_a_resource_nonanswer_without_poisoning_retry() {
    let env = environment(|_| {});
    let oversized = env
        .push_extension_entry(&fln_elab::externs::journal_name(), vec![0; 65_537])
        .unwrap();
    let mut cache = None;
    let error = executable_intrinsic_binding_cached(
        &oversized,
        &name("String.Internal.length"),
        &mut 0,
        IngressLimits::default(),
        &mut cache,
    )
    .expect_err("an oversized native metadata row cannot be decoded");
    assert!(matches!(
        error,
        IngressError::MetadataResourceExhausted { .. }
    ));
    assert!(error.is_resource_exhaustion());
    assert!(cache.is_none());
    assert!(
        executable_intrinsic_binding_cached(
            &env,
            &name("String.Internal.length"),
            &mut 0,
            IngressLimits::default(),
            &mut cache
        )
        .unwrap()
        .is_some()
    );
}
