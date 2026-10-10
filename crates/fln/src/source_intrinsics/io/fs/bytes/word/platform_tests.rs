//! The platform producer uses actual Prelude declarations, with neither an
//! admitted IO closure nor a manufactured platform-width definition.
use super::*;

fn platform_environment(fixture: &Fixture) -> Environment {
    let needed = super::super::super::actual_dependencies(
        &fixture.environment,
        &[
            "System.Platform.getNumBits",
            "System.Platform.numBits",
            "Unit.unit",
            // The compiler's inert proof slot is the checked Bool.false
            // scalar. Keep its real model even though it is not a logical
            // dependency of the platform producer's subtype.
            "Bool.false",
            "Nat.rec",
            "Nat.pred",
        ],
    );
    let mut environment = Environment::new();
    for label in &needed {
        environment = environment
            .with_entry(fixture.environment.entry(label).unwrap())
            .unwrap();
    }
    for (label, entries) in &fixture.externs {
        if needed.contains(label) {
            environment = externs::register(&environment, label, entries.clone()).unwrap();
        }
    }
    assert!(!environment.contains(&name("USize")));
    assert!(!environment.contains(&name("IO.Error")));
    environment
}

fn evaluation_steps(engine: &Engine, expression: &str, expected: Option<&str>) -> u64 {
    let source = format!("#eval {expression}");
    let result = engine
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_complete()
        .unwrap();
    let execution = &result.batch.executions[result.batch.source_evaluation_indices[0]];
    let VmExit::Returned(value) = &execution.exit else {
        panic!("completed platform source: {:?}", execution.exit);
    };
    if let Some(expected) = expected {
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
    value.usage.steps
}

#[test]
fn actual_platform_width_rebuilds_its_subtype_and_retains_strict_unit_work() {
    with_fixture(|fixture| {
        let rows = inventory(PLATFORM_DEPENDENCIES);
        assert_eq!(rows.len(), 20);
        assert_eq!(
            rows.keys().cloned().collect::<BTreeSet<_>>(),
            super::super::super::actual_dependencies(
                &fixture.environment,
                &["System.Platform.getNumBits"],
            )
        );
        let environment = platform_environment(fixture);
        for (label, digest) in rows {
            assert_eq!(environment.entry(&label).unwrap().digest().to_hex(), digest);
        }
        assert!(matches_word(&environment, "System.Platform.getNumBits").unwrap());
        assert_eq!(std::mem::size_of::<usize>(), 8);
        let engine = Engine::from_environment(environment);
        execute_and_replay(
            &engine,
            "#eval System.Platform.numBits\n#eval Subtype.val (System.Platform.getNumBits ())\n#eval (let f := System.Platform.getNumBits; Subtype.val (f ()))",
            &[
                Expected::Nat("64"),
                Expected::Nat("64"),
                Expected::Nat("64"),
            ],
        );
        let engine = checked_source(
            engine.environment().clone(),
            // Ignoring the IH erases recursive work. This strict
            // initializer actually follows the IH before producing Unit.
            b"def unitWork (n : Nat) : Unit := let spent := Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => ih) n; ()",
        );
        let work = evaluation_steps(&engine, "unitWork 20", None)
            - evaluation_steps(&engine, "unitWork 0", None);
        assert!(work > 0, "the strictness witness performs real VM work");
        assert_eq!(
            evaluation_steps(
                &engine,
                "Subtype.val (System.Platform.getNumBits (unitWork 20))",
                Some("64"),
            ) - evaluation_steps(
                &engine,
                "Subtype.val (System.Platform.getNumBits (unitWork 0))",
                Some("64"),
            ),
            work,
            "the ignored native Unit receiver is evaluated exactly once"
        );
    });
}

#[test]
fn platform_models_metadata_cache_and_budget_never_fall_back_to_an_inhabitant() {
    with_fixture(|fixture| {
        let root = name("System.Platform.getNumBits");
        let without_extern = rebuild(fixture, None, Some(&root));
        assert!(!matches_word(&without_extern, "System.Platform.getNumBits").unwrap());
        // The ordinary word contract permits absent metadata on an indirect
        // model dependency. That warmed cache cannot authorize its native call.
        assert!(matches_word(&without_extern, "USize.ofNat").unwrap());
        let checked = checked_source(
            without_extern,
            b"def warmPlatformWord : USize := USize.ofNat 7\ndef unavailablePlatform := System.Platform.getNumBits",
        );
        let body = |label| match checked.environment().find(&name(label)).unwrap() {
            ConstantInfo::Defn(value) => value.value.clone(),
            _ => panic!("checked platform cache control"),
        };
        let mut preparation =
            crate::runtime::Preparation::new(checked.environment(), IngressLimits::default());
        preparation.expression(&body("warmPlatformWord")).unwrap();
        assert_eq!(
            preparation
                .expression(&body("unavailablePlatform"))
                .unwrap(),
            c("System.Platform.getNumBits"),
            "a warm word cache cannot synthesize a native platform wrapper"
        );
        assert!(matches!(
            checked.execute_source_definition(
                b"def unavailablePlatformWidth : Nat := System.Platform.numBits",
                &KVMap::new(),
                EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
            ),
            Err(EngineExecutionError::Ingress(IngressError::UnknownConstant { name: missing, .. }))
                if missing == root
        ));

        for entry in [
            ExternEntry::Opaque,
            ExternEntry::Standard {
                backend: name("all"),
                symbol: "foreign_platform_width".to_owned(),
            },
        ] {
            let changed = externs::register(&fixture.environment, &root, vec![entry]).unwrap();
            assert!(matches!(
                matches_word(&changed, "System.Platform.getNumBits"),
                Err(IngressError::UnsupportedNode { .. })
            ));
        }
        for missing in ["Unit", "Subtype.mk", "Or.inr"] {
            assert!(matches!(
                matches_word(
                    &rebuild(fixture, Some(&name(missing)), None),
                    "System.Platform.getNumBits",
                ),
                Err(IngressError::UnsupportedNode { .. })
            ));
        }

        let Some(ConstantInfo::Opaque(original)) = fixture.environment.find(&root) else {
            panic!("actual opaque platform producer");
        };
        let ExprNode::Lam {
            binder_name,
            binder_type,
            binder_info,
            body,
        } = original.value.node()
        else {
            panic!("actual platform inhabitant lambda");
        };
        let mut head = body.clone();
        let mut args = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            args.push(a.clone());
            head = f.clone();
        }
        args.reverse();
        assert_eq!(args.len(), 4);
        let natural = |value| {
            Expr::lit(fln_core::expr::Literal::Nat(
                fln_core::expr::NatLit::from_u64(value),
            ))
        };
        let equality = |right| {
            apply(
                Expr::const_(name("Eq"), vec![Level::one()]),
                [c("Nat"), natural(32), natural(right)],
            )
        };
        args[2] = natural(32);
        args[3] = apply(
            c("Or.inl"),
            [
                equality(32),
                equality(64),
                apply(
                    Expr::const_(name("Eq.refl"), vec![Level::one()]),
                    [c("Nat"), natural(32)],
                ),
            ],
        );
        let mut changed = original.clone();
        changed.value = Expr::lam(
            binder_name.clone(),
            binder_type.clone(),
            apply(head, args),
            *binder_info,
        );
        let admitted = Engine::from_environment(rebuild(fixture, Some(&root), None))
            .admit_declaration(
                Declaration::Opaque(changed),
                &KVMap::new(),
                EngineAdmissionLimits::for_stack_bytes(STACK),
            )
            .expect("32 is an independently checked inhabitant of the actual subtype")
            .into_complete()
            .unwrap();
        let changed = externs::register(
            admitted.engine.environment(),
            &root,
            fixture.externs[&root].clone(),
        )
        .unwrap();
        assert!(matches!(
            matches_word(&changed, "System.Platform.getNumBits"),
            Err(IngressError::UnsupportedNode { .. })
        ));
        let engine = Engine::from_environment(changed);
        assert!(matches!(
            engine.execute_source_definition(
                b"def alteredPlatformWidth : Nat := System.Platform.numBits",
                &KVMap::new(),
                EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
            ),
            Err(EngineExecutionError::Ingress(
                IngressError::UnsupportedNode { .. }
            ))
        ));

        let environment = platform_environment(fixture);
        let mut work = 0;
        assert!(
            word_matches(
                &environment,
                &root,
                &mut None,
                &mut work,
                IngressLimits::default()
            )
            .unwrap()
        );
        assert!(matches!(
            word_matches(
                &environment,
                &root,
                &mut None,
                &mut 0,
                IngressLimits {
                    max_nodes: work - 1,
                    ..IngressLimits::default()
                }
            ),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                ..
            })
        ));
    });
}
