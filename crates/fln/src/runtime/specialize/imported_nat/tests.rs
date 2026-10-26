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

    // Selecting a known zero must not let its enclosing projection erase a
    // different field's strict work before the record is constructed.
    let pair_type = application(
        constant("PProd", vec![Level::one(); 2]),
        [natural(), natural()],
    );
    let pair = application(
        constant("PProd.mk", vec![Level::one(); 2]),
        [
            natural(),
            natural(),
            nat(7),
            Expr::app(constant("work", vec![]), nat(42)),
        ],
    );
    let zero_pair = application(
        constant("Nat.rec", vec![Level::one()]),
        [
            Expr::lam(
                Name::anonymous(),
                natural(),
                pair_type.clone(),
                BinderInfo::Default,
            ),
            pair,
            Expr::lam(
                Name::anonymous(),
                natural(),
                Expr::lam(
                    Name::anonymous(),
                    pair_type,
                    Expr::bvar(0).unwrap(),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            nat(0),
        ],
    );
    assert!(
        Preparation::new(engine.environment(), IngressLimits::default())
            .executable_projection(&named("PProd"), 0, &zero_pair)
            .unwrap()
            .is_none()
    );
}

#[test]
fn history_reduction_keeps_explicit_implementations_and_extern_contracts() {
    let engine = admitted_scaffold(None);
    let source = named("Nat.add._f");
    let Some(ConstantInfo::Defn(original)) = engine.environment().find(&source) else {
        panic!("the actual checked arithmetic functional is present");
    };
    let mut replacement = original.clone();
    replacement.base.name = named("replacementHistory");
    replacement.all = vec![replacement.base.name.clone()];
    let target = replacement.base.name.clone();
    let engine = engine
        .admit_declaration(
            Declaration::Defn(replacement),
            &KVMap::new(),
            EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let environment =
        fln_elab::implemented_by::register(engine.environment(), &source, &target).unwrap();
    let helper = constant("Nat.add._f", vec![]);
    let marker = FVarId(named("history_marker"));
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    assert!(!preparation.nat_history_inert(&helper).unwrap());
    assert!(
        preparation
            .nat_history_step(&helper, &marker)
            .unwrap()
            .is_none()
    );

    for label in ["Nat.add._f", "Nat.brecOn", "Nat.rec"] {
        let environment = fln_elab::externs::register(
            engine.environment(),
            &named(label),
            vec![fln_elab::externs::ExternEntry::Opaque],
        )
        .unwrap();
        let helper = constant(
            label,
            if label == "Nat.add._f" {
                vec![]
            } else {
                vec![Level::one()]
            },
        );
        let mut preparation = Preparation::new(&environment, IngressLimits::default());
        assert!(matches!(
            preparation.nat_history_step(&helper, &marker),
            Err(IngressError::UnsupportedNode {
                kind: "native extern attribute does not match the supported ABI"
            })
        ));
        assert!(preparation.nat_history_inert(&helper).is_err());
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
            // The arithmetic history exposed by source index refinement must
            // also disappear with the pin's actual imported declarations and
            // executable metadata, not only with the small source seed.
            let indexed = imported
                .engine
                .execute_source_definitions(
                    &[b"inductive Vec (A : Type) : Nat -> Type\n\
                       | nil : Vec A 0\n\
                       | cons : A -> {n : Nat} -> Vec A n -> Vec A (n+1)\n\
                       open Vec\n\
                       def head : Vec Nat (n+1) -> Nat\n\
                       | cons b bv => b\n\
                       #eval head (cons 42 nil)"],
                    &options,
                    EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            assert_eq!(
                closed_vm_value(&indexed.executions.last().unwrap().exit).unwrap(),
                Some(ClosedVmValue::Scalar(42))
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

/// `(Nat.brecOn.go M t F).1` with the definition already unfolded, as plain
/// delta reduction of a structural definition leaves it in an elaborated term.
fn unfolded_history(engine: &Engine, major: Expr, functional: Expr) -> Expr {
    let body = Preparation::new(engine.environment(), IngressLimits::default())
        .nat_history_body(
            "Nat.brecOn.go",
            &[Level::one()],
            &[motive(), major, functional],
        )
        .unwrap()
        .unwrap();
    Expr::proj(named("PProd"), 0, body)
}

#[test]
fn an_unfolded_history_scaffold_refolds_only_to_its_own_admitted_definition() {
    let engine = admitted_scaffold(None);
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    // The receiver's motive is a type computed from the index: Nat.rec alone
    // has no uniform layout for it, so this used to be a refusal.
    for (initial, count, expected) in [(7, 0, 7), (7, 5, 12), (40, 2, 42)] {
        let unfolded = unfolded_history(&engine, nat(count), successor_functional(initial));
        let result = engine
            .execute_definition(
                declaration("answer", natural(), unfolded),
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
    let functional = successor_functional(7);
    let unfolded = unfolded_history(&engine, nat(3), functional.clone());
    let ExprNode::Proj { expr: receiver, .. } = unfolded.node() else {
        unreachable!()
    };
    let mut prep = Preparation::new(engine.environment(), IngressLimits::default());
    assert_eq!(
        prep.nat_history_refold(0, receiver).unwrap(),
        Some(brec(nat(3), functional))
    );
    // The history component is no observable value of the fold.
    assert_eq!(prep.nat_history_refold(1, receiver).unwrap(), None);
    // Any change to the scaffold is not one delta step from Nat.brecOn.
    let (head, mut args) = prep.spine(receiver).unwrap();
    let ExprNode::Lam {
        binder_name,
        binder_type,
        body,
        binder_info,
    } = args[2].node()
    else {
        unreachable!()
    };
    let ExprNode::Lam { body: step, .. } = body.node() else {
        unreachable!()
    };
    let (mk, mut fields) = prep.spine(step).unwrap();
    fields[3] = application(
        constant("PProd.mk", vec![Level::one(), Level::one()]),
        [natural(), natural(), nat(0), nat(0)],
    );
    let ExprNode::Lam {
        binder_name: inner_name,
        binder_type: inner_type,
        binder_info: inner_info,
        ..
    } = body.node()
    else {
        unreachable!()
    };
    args[2] = Expr::lam(
        binder_name.clone(),
        binder_type.clone(),
        Expr::lam(
            inner_name.clone(),
            inner_type.clone(),
            application(mk, fields),
            *inner_info,
        ),
        *binder_info,
    );
    let altered = application(head, args);
    assert_eq!(prep.nat_history_refold(0, &altered).unwrap(), None);
    // A scaffold whose admitted definitions are not the pinned model is
    // never refolded, even when the receiver is its own unfolding.
    let other = admitted_scaffold(Some("Nat.brecOn"));
    let unfolded = unfolded_history(&other, nat(3), successor_functional(7));
    let ExprNode::Proj { expr: receiver, .. } = unfolded.node() else {
        unreachable!()
    };
    assert_eq!(
        Preparation::new(other.environment(), IngressLimits::default())
            .nat_history_refold(0, receiver)
            .unwrap(),
        None
    );
}

#[test]
fn history_refolding_never_selects_a_replaced_or_extern_brec_on() {
    let engine = admitted_scaffold(None);
    let unfolded = unfolded_history(&engine, nat(3), successor_functional(7));
    let ExprNode::Proj { expr: receiver, .. } = unfolded.node() else {
        unreachable!()
    };
    // Control: the pinned scaffold refolds in this environment.
    assert!(
        Preparation::new(engine.environment(), IngressLimits::default())
            .nat_history_refold(0, receiver)
            .unwrap()
            .is_some()
    );
    // The original term never calls Nat.brecOn, so refolding must not hand
    // it to an executable replacement or a native extern of that name.
    let source = named("Nat.brecOn");
    let Some(ConstantInfo::Defn(original)) = engine.environment().find(&source) else {
        panic!("the admitted course-of-values definition is present");
    };
    let mut replacement = original.clone();
    replacement.base.name = named("replacementBrecOn");
    replacement.all = vec![replacement.base.name.clone()];
    let target = replacement.base.name.clone();
    let replaced = engine
        .admit_declaration(
            Declaration::Defn(replacement),
            &KVMap::new(),
            EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let environment =
        fln_elab::implemented_by::register(replaced.environment(), &source, &target).unwrap();
    assert_eq!(
        Preparation::new(&environment, IngressLimits::default())
            .nat_history_refold(0, receiver)
            .unwrap(),
        None
    );
    let environment = fln_elab::externs::register(
        engine.environment(),
        &source,
        vec![fln_elab::externs::ExternEntry::Opaque],
    )
    .unwrap();
    assert!(matches!(
        Preparation::new(&environment, IngressLimits::default()).nat_history_refold(0, receiver),
        Err(IngressError::UnsupportedNode {
            kind: "native extern attribute does not match the supported ABI"
        })
    ));
}
