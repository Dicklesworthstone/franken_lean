//! Checked course-of-values callbacks and the actual imported arithmetic path.
use super::*;

type Local = (FVarId, Expr);
fn local(label: &str, type_: Expr) -> Local {
    (FVarId(named(label)), type_)
}
fn value(local: &Local) -> Expr {
    Expr::fvar(local.0.clone())
}
fn bind(locals: &[Local], mut body: Expr, lambda: bool) -> Expr {
    for (id, type_) in locals.iter().rev() {
        body = body.lift_loose(0, 1).unwrap().abstract_fvar(id, 0).unwrap();
        body = if lambda {
            Expr::lam(id.0.clone(), type_.clone(), body, BinderInfo::Default)
        } else {
            Expr::forall_e(id.0.clone(), type_.clone(), body, BinderInfo::Default)
        };
    }
    body
}
fn natural() -> Expr {
    constant("Nat", vec![])
}
fn nat(n: u64) -> Expr {
    super::super::super::nat::literal(n)
}
fn motive() -> Expr {
    Expr::lam(Name::anonymous(), natural(), natural(), BinderInfo::Default)
}
fn history(major: Expr) -> Expr {
    application(constant("Nat.below", vec![Level::one()]), [motive(), major])
}
fn declaration(label: &str, type_: Expr, body: Expr) -> Declaration {
    let name = named(label);
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name.clone(),
            level_params: vec![],
            type_,
        },
        value: body,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name],
    })
}
fn admitted_scaffold(altered: Option<&str>) -> Engine {
    let mut engine = Engine::from_environment(Environment::new());
    for mut declaration in crate::source_intrinsics::imported_nat_recursion_model_declarations()
        .into_iter()
        .chain(
            fln_elab::seed::nat_add_support_seed_declarations()
                .into_iter()
                .skip(6),
        )
        .chain([
            fln_elab::seed::nat_add_seed_declaration(),
            fln_elab::seed::bool_seed_declaration(),
            fln_elab::seed::nat_pred_seed_declaration(),
            fln_elab::seed::nat_beq_seed_declaration(),
        ])
    {
        if let Some(altered) = altered
            && let Declaration::Defn(definition) = &mut declaration
            && definition.base.name == named(altered)
        {
            definition.value = Expr::app(
                Expr::lam(
                    Name::anonymous(),
                    definition.base.type_.clone(),
                    Expr::bvar(0).unwrap(),
                    BinderInfo::Default,
                ),
                definition.value.clone(),
            );
        }
        engine = engine
            .admit_declaration(
                declaration,
                &KVMap::new(),
                EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
    }
    engine
}
fn successor_functional(initial: u64) -> Expr {
    let major = local("major", natural());
    let previous = local("previous", history(value(&major)));
    let case_motive = bind(
        std::slice::from_ref(&major),
        bind(std::slice::from_ref(&previous), natural(), false),
        true,
    );
    let first_history = local("first_history", history(constant("Nat.zero", vec![])));
    let first = bind(&[first_history], nat(initial), true);
    let pred = local("pred", natural());
    let unused = local("unused", Expr::app(case_motive.clone(), value(&pred)));
    let succ_history = local(
        "succ_history",
        history(Expr::app(constant("Nat.succ", vec![]), value(&pred))),
    );
    let step = bind(
        &[pred, unused, succ_history.clone()],
        application(
            constant("Nat.add", vec![]),
            [Expr::proj(named("PProd"), 0, value(&succ_history)), nat(1)],
        ),
        true,
    );
    let result = application(
        constant("Nat.rec", vec![Level::one()]),
        [case_motive, first, step, value(&major), value(&previous)],
    );
    bind(&[major, previous], result, true)
}
fn brec(major: Expr, functional: Expr) -> Expr {
    application(
        constant("Nat.brecOn", vec![Level::one()]),
        [motive(), major, functional],
    )
}

#[test]
fn checked_nat_history_executes_actual_functionals_and_checks_every_dependency() {
    let engine = admitted_scaffold(None);
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for (initial, count, expected) in [(7, 0, 7), (7, 5, 12), (40, 2, 42)] {
        let result = engine
            .execute_definition(
                declaration(
                    "answer",
                    natural(),
                    brec(nat(count), successor_functional(initial)),
                ),
                &options,
                EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(
            closed_vm_value(&result.exit).unwrap(),
            Some(ClosedVmValue::Scalar(expected))
        );
        assert_eq!(root, engine.logical_root(&options));
    }
    for changed in ["Nat.below", "Nat.brecOn.go", "Nat.brecOn", "Nat.casesOn"] {
        let altered = admitted_scaffold(Some(changed));
        assert!(
            !crate::source_intrinsics::imported_nat_recursion_matches(
                altered.environment(),
                &mut 0,
                IngressLimits::default()
            )
            .unwrap()
        );
    }
    assert!(matches!(
        crate::source_intrinsics::imported_nat_recursion_matches(
            engine.environment(),
            &mut 0,
            IngressLimits {
                max_nodes: 1,
                ..IngressLimits::default()
            }
        ),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            ..
        })
    ));
}

#[test]
fn nat_history_refuses_opaque_consumers_and_preserves_strict_work() {
    let engine = admitted_scaffold(None);
    let major = local("major", natural());
    let previous = local("previous", history(value(&major)));
    let callback_type = bind(&[major, previous], natural(), false);
    let body = Expr::lam(
        Name::anonymous(),
        callback_type.clone(),
        brec(nat(2), Expr::bvar(0).unwrap()),
        BinderInfo::Default,
    );
    engine
        .admit_declaration(
            declaration(
                "opaque",
                Expr::forall_e(
                    Name::anonymous(),
                    callback_type,
                    natural(),
                    BinderInfo::Default,
                ),
                body,
            ),
            &KVMap::new(),
            EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let head = constant("Nat.brecOn", vec![Level::one()]);
    let mut prep = Preparation::new(engine.environment(), IngressLimits::default());
    assert!(matches!(
        prep.imported_nat_recursion(&head, &[motive(), nat(2), Expr::bvar(0).unwrap()]),
        Err(IngressError::UnsupportedNode {
            kind: "Nat course-of-values history escapes"
        })
    ));
    // An ordinary runtime call producing a value may not disappear from a let
    // or from a beta operand, even when the result does not use that value.
    let engine = engine
        .admit_declaration(
            declaration(
                "work",
                Expr::forall_e(Name::anonymous(), natural(), natural(), BinderInfo::Default),
                Expr::lam(
                    Name::anonymous(),
                    natural(),
                    Expr::bvar(0).unwrap(),
                    BinderInfo::Default,
                ),
            ),
            &KVMap::new(),
            EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let call = Expr::app(constant("work", vec![]), nat(42));
    let minor = Expr::lam(
        Name::anonymous(),
        natural(),
        Expr::lam(
            Name::anonymous(),
            natural(),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let paid_minor = Expr::let_e(
        Name::anonymous(),
        natural(),
        call.clone(),
        minor.clone(),
        false,
    );
    let discarded_minor = application(
        constant("Nat.rec", vec![Level::one()]),
        [motive(), nat(7), paid_minor, constant("Nat.zero", vec![])],
    );
    engine
        .admit_declaration(
            declaration("strictMinor", natural(), discarded_minor.clone()),
            &KVMap::new(),
            EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let marker = FVarId(named("history_marker"));
    for source in [
        discarded_minor,
        Expr::let_e(Name::anonymous(), natural(), call.clone(), nat(7), false),
        Expr::app(
            Expr::lam(Name::anonymous(), natural(), nat(7), BinderInfo::Default),
            call,
        ),
    ] {
        assert_eq!(
            Preparation::new(engine.environment(), IngressLimits::default())
                .nat_history_reduce(&source, &marker)
                .unwrap(),
            source
        );
    }
}

#[test]
fn actual_prelude_modulo_and_bitvector_words_execute_at_default_budgets() {
    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(std::path::PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                std::path::PathBuf::from(home)
                    .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|path| path.is_dir());
    let Some(library) = library else {
        assert!(std::env::var_os("FLN_REQUIRE_REFERENCE").is_none());
        eprintln!("SKIP: pinned Reference lib/lean absent");
        return;
    };
    const STACK: usize = 256 * 1024 * 1024;
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let path = library.join("Init/Prelude.olean");
            let parts = [
                std::fs::read(&path).unwrap(),
                std::fs::read(path.with_extension("olean.server")).unwrap(),
                std::fs::read(path.with_extension("olean.private")).unwrap(),
            ];
            let module = named("Init.Prelude");
            let inputs = [OleanModuleInput {
                name: &module,
                artifact: &parts[0],
                server_artifact: Some(&parts[1]),
                private_artifact: Some(&parts[2]),
            }];
            let options = KVMap::new();
            let imported = Engine::from_environment(Environment::new())
                .import_olean_modules_for_source(
                    &inputs,
                    std::slice::from_ref(&module),
                    &options,
                    crate::source_check::modules::imported::SourceOleanImportLimits::new(
                        OleanCheckLimits::new(256 * 1024 * 1024, Budget::for_stack_bytes(STACK)),
                    ),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            assert!(
                crate::source_intrinsics::imported_nat_recursion_matches(
                    imported.engine.environment(),
                    &mut 0,
                    IngressLimits::default()
                )
                .unwrap()
            );
            let mut cases = vec![];
            for (x, y, expected) in [(43, 5, 3), (42, 0, 42), (0, 5, 0), (6, 7, 6), (14, 7, 0)] {
                cases.push((
                    format!("Nat.mod {x} {y}"),
                    application(constant("Nat.mod", vec![]), [nat(x), nat(y)]),
                    expected,
                ));
            }
            for (width, label) in [(32, "UInt32"), (64, "UInt64")] {
                let bitvector =
                    application(constant("BitVec.ofNat", vec![]), [nat(width), nat(42)]);
                let word = Expr::app(constant(&format!("{label}.ofBitVec"), vec![]), bitvector);
                let result = if width == 32 {
                    Expr::app(constant("UInt32.toNat", vec![]), word)
                } else {
                    // UInt64.toNat lives beyond Prelude; its admitted bitvector
                    // projection already exposes the same natural payload.
                    let bits = Expr::app(constant("UInt64.toBitVec", vec![]), word);
                    application(constant("BitVec.toNat", vec![]), [nat(width), bits])
                };
                cases.push((format!("{label} modulo constructor"), result, 42));
            }
            for (x, y, expected) in [(43, 5, 8), (42, 0, 0), (0, 5, 0), (6, 7, 0), (14, 7, 2)] {
                cases.push((
                    format!("Nat.div {x} {y}"),
                    application(constant("Nat.div", vec![]), [nat(x), nat(y)]),
                    expected,
                ));
            }
            for (label, body, expected) in cases {
                let result = imported
                    .engine
                    .execute_definition(
                        declaration("importedAnswer", natural(), body),
                        &options,
                        EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
                    )
                    .unwrap_or_else(|error| panic!("{label}: {error:?}"))
                    .into_complete()
                    .unwrap();
                assert_eq!(
                    closed_vm_value(&result.exit).unwrap(),
                    Some(ClosedVmValue::Scalar(expected)),
                    "{label}"
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
