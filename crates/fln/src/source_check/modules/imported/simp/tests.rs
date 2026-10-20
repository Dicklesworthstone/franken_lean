use super::super::tests::{closure, inputs, limits, n, on_import_stack, pinned_lib};
use super::*;
use fln_env::constants::{
    AxiomVal, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
};

fn model() -> Environment {
    // The minimal opaque-Nat seed contains neither Nat.zero nor Eq. Use
    // admitted declarations so the proposition classifier sees the actual
    // generic Eq telescope instead of a dangling constant in a fake proof type.
    let mut env = Engine::from_environment(Environment::new())
        .admit_declarations(
            &[
                fln_elab::seed::nat_inductive_seed_declaration(),
                fln_elab::seed::eq_seed_declaration(),
            ],
            &KVMap::new(),
            EngineAdmissionLimits::new(Budget::DEFAULT),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
        .environment()
        .clone();
    let nat = Expr::const_(n("Nat"), vec![]);
    let zero = Expr::const_(n("Nat.zero"), vec![]);
    let equality = Expr::app(
        Expr::app(
            Expr::app(Expr::const_(n("Eq"), vec![Level::one()]), nat.clone()),
            zero.clone(),
        ),
        zero.clone(),
    );
    for name in [n("origin"), n("proof"), Name::num(n("internal"), 7)] {
        env = env
            .add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name,
                    level_params: vec![n("u")],
                    type_: equality.clone(),
                },
                is_unsafe: false,
            }))
            .unwrap();
    }
    env.add_decl(ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: n("data"),
            level_params: vec![],
            type_: nat,
        },
        value: zero,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![n("data")],
    }))
    .unwrap()
}

fn theorem() -> metadata::SimpEntry {
    metadata::SimpEntry {
        scope: None,
        kind: metadata::SimpKind::Theorem(metadata::SimpTheorem {
            origin: n("origin"),
            proof: Expr::const_(n("proof"), vec![]),
            level_params: vec![],
            origin_reverse: false,
            priority: 900,
            post: true,
            permutation: false,
            reflexive: false,
            backward_reflexive: false,
            key_count: 1,
        }),
    }
}

#[test]
fn generic_proofs_retain_distinct_origins_and_numeric_names() {
    let env = model();
    for proof in [n("proof"), Name::num(n("internal"), 7)] {
        let mut row = theorem();
        let metadata::SimpKind::Theorem(t) = &mut row.kind else {
            unreachable!()
        };
        t.proof = Expr::const_(proof.clone(), vec![]);
        let (Some(operation), false) = select(&env, &n("Module"), &row).unwrap() else {
            panic!("a compact generic proof must activate")
        };
        assert_eq!(
            operation,
            ImportedSimpRule::Proof {
                origin: n("origin"),
                proof: proof.clone(),
                priority: 900,
            }
        );
        let next = native::import_rules(&env, &[operation]).unwrap();
        let active = native::read(&next).unwrap();
        assert_eq!(active.len(), 1);
        assert_eq!(active[0].declaration, n("origin"));
        assert_eq!(active[0].proof, Some(proof));
        assert_eq!(active[0].priority, 900);
        assert!(!active[0].reverse);
        assert!(native::read(&env).unwrap().is_empty());
    }
}

#[test]
fn a_missing_equality_declaration_does_not_become_proof_evidence() {
    let complete = model();
    let incomplete = fln_elab::seed::bootstrap_nat_environment(Budget::DEFAULT)
        .unwrap()
        .add_decl(complete.find(&n("proof")).unwrap().clone())
        .unwrap();
    assert!(matches!(
        native::register_imported_proof(&incomplete, &n("proof"), &n("proof"), 900),
        Err(SimpSetError::UnsupportedDeclaration(name)) if name == n("proof")
    ));
    assert!(native::read(&incomplete).unwrap().is_empty());
}

#[test]
fn explicit_universes_must_be_generic_not_specialized() {
    let env = model();
    let mut row = theorem();
    let metadata::SimpKind::Theorem(t) = &mut row.kind else {
        unreachable!()
    };
    t.level_params = vec![n("renamed")];
    t.proof = Expr::const_(n("proof"), vec![Level::param(n("renamed"))]);
    assert!(candidate(&env, &row).is_some());
    for levels in [vec![Level::one()], vec![Level::param(n("other"))], vec![]] {
        let mut specialized = row.clone();
        let metadata::SimpKind::Theorem(t) = &mut specialized.kind else {
            unreachable!()
        };
        t.proof = Expr::const_(n("proof"), levels);
        assert!(candidate(&env, &specialized).is_none());
        assert!(select(&env, &n("Module"), &specialized).unwrap().1);
    }
}

#[test]
fn scoped_rules_are_dormant_and_deferred_globals_withdraw_stale_rules() {
    let env = model();
    let row = theorem();
    let operation = select(&env, &n("Module"), &row).unwrap().0.unwrap();
    let active = native::import_rules(&env, &[operation]).unwrap();
    for variant in 0..4 {
        let mut deferred = row.clone();
        let metadata::SimpKind::Theorem(t) = &mut deferred.kind else {
            unreachable!()
        };
        match variant {
            0 => deferred.scope = Some(n("Scope")),
            1 => t.post = false,
            2 => t.permutation = true,
            3 => t.origin_reverse = true,
            _ => unreachable!(),
        }
        let (operation, is_deferred) = select(&active, &n("Module"), &deferred).unwrap();
        assert!(is_deferred);
        let next =
            native::import_rules(&active, &operation.into_iter().collect::<Vec<_>>()).unwrap();
        assert_eq!(
            native::read(&next).unwrap().len(),
            usize::from(variant == 0)
        );
        assert_eq!(native::read(&active).unwrap().len(), 1);
    }
}

#[test]
fn data_proofs_are_not_activated_but_safe_unfolding_is() {
    let env = model();
    let mut row = theorem();
    let metadata::SimpKind::Theorem(t) = &mut row.kind else {
        unreachable!()
    };
    t.proof = Expr::const_(n("data"), vec![]);
    assert!(select(&env, &n("Module"), &row).unwrap().1);
    let unfolding = metadata::SimpEntry {
        scope: None,
        kind: metadata::SimpKind::Unfold(n("data")),
    };
    let (Some(operation), false) = select(&env, &n("Module"), &unfolding).unwrap() else {
        panic!("a checked safe definition must be unfoldable")
    };
    assert!(matches!(operation, ImportedSimpRule::Unfold { .. }));
    let next = native::import_rules(&env, &[operation]).unwrap();
    let rows = native::read(&next).unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].declaration, n("data"));
    assert_eq!(rows[0].proof, None);
}

#[test]
fn missing_names_are_errors_not_deferred_rules() {
    let env = model();
    for change_origin in [false, true] {
        let mut row = theorem();
        let metadata::SimpKind::Theorem(t) = &mut row.kind else {
            unreachable!()
        };
        if change_origin {
            t.origin = n("missing");
        } else {
            t.proof = Expr::const_(n("missing"), vec![]);
        }
        assert!(matches!(
            select(&env, &n("Module"), &row),
            Err(SourceOleanImportError::Metadata { declaration, .. })
                if declaration == n("missing")
        ));
    }
    assert!(native::read(&env).unwrap().is_empty());
}

#[test]
fn malformed_existing_journals_cannot_be_hidden_by_per_rule_validation() {
    let env = model();
    let operation = select(&env, &n("Module"), &theorem()).unwrap().0.unwrap();
    let valid = native::import_rules(&env, std::slice::from_ref(&operation)).unwrap();
    let mut added = None;
    for (name, _) in valid.extensions() {
        if env.extension(name).is_none() {
            added = Some(name.clone());
            break;
        }
    }
    let journal = added.expect("registration adds the simp journal");
    let broken = valid
        .push_extension_entry(&journal, b"broken".to_vec())
        .unwrap();
    operation.validate(&broken).unwrap();
    assert!(matches!(
        native::import_rules(&broken, &[operation]),
        Err(SimpSetError::Malformed)
    ));
    assert!(matches!(
        native::import_rules(&broken, &[]),
        Err(SimpSetError::Malformed)
    ));
    assert_eq!(native::read(&valid).unwrap().len(), 1);
}

fn graph() -> ScopeIndex {
    ScopeIndex {
        parents: vec![vec![], vec![0], vec![0]],
        owners: BTreeMap::from([(n("origin"), vec![0]), (n("proof"), vec![2])]),
        work_left: 100,
    }
}

#[test]
fn imported_siblings_cannot_supply_proofs_but_real_dependencies_can() {
    let env = model();
    let mut graph = graph();
    let left = graph.closure(1).unwrap();
    assert_eq!(left, BTreeSet::from([0, 1]));
    graph
        .authorize(&Environment::new(), &env, &left, &n("Left"), &n("origin"))
        .unwrap();
    assert!(matches!(
        graph.authorize(&Environment::new(), &env, &left, &n("Left"), &n("proof")),
        Err(SourceOleanImportError::Metadata { .. })
    ));
    let right = graph.closure(2).unwrap();
    graph
        .authorize(&Environment::new(), &env, &right, &n("Right"), &n("proof"))
        .unwrap();
    graph
        .authorize(&env, &env, &left, &n("Left"), &n("proof"))
        .unwrap();
}

#[test]
fn import_scope_budget_stops_are_typed_resource_errors() {
    let mut graph = graph();
    graph.work_left = 0;
    let error = graph.closure(1).unwrap_err();
    assert!(error.metadata_resource_exhausted());
    assert!(matches!(error, SourceOleanImportError::Limit(_)));
}

#[test]
fn retained_simp_suffixes_preserve_source_order_and_redundant_events() {
    use crate::source_check::modules::{Meter, SourceModuleCheckLimits, replay::Export};
    let before = model();
    let proof = select(&before, &n("Module"), &theorem())
        .unwrap()
        .0
        .unwrap();
    let erase = ImportedSimpRule::Erase {
        declaration: n("origin"),
    };
    let options = KVMap::new();
    let source_limits = SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::DEFAULT));
    let mut meter = Meter {
        work: 0,
        bytes: 0,
        limits: SourceModuleCheckLimits::new(source_limits),
    };
    // An erasure captured when no rule is active must still remove a rule
    // registered by a source module that precedes it at replay time.
    let erased = native::import_rules(&before, std::slice::from_ref(&erase)).unwrap();
    let module = n("ExternalErase");
    let suffix = Export::capture(&module, &before, &erased, vec![], &mut meter).unwrap();
    let source = native::import_rules(&before, std::slice::from_ref(&proof)).unwrap();
    let replayed = suffix
        .replay(
            Engine::from_environment(source),
            &module,
            &options,
            &mut meter,
            None,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(native::read(replayed.environment()).unwrap().is_empty());
    // Every operation in an external suffix retains its original position.
    // A final re-registration after an erasure must remain effective.
    let operations = [proof.clone(), erase, proof];
    let after = native::import_rules(&before, &operations).unwrap();
    let module = n("ExternalReadd");
    let suffix = Export::capture(&module, &before, &after, vec![], &mut meter).unwrap();
    let replayed = suffix
        .replay(
            Engine::from_environment(before),
            &module,
            &options,
            &mut meter,
            None,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        native::read(replayed.environment()).unwrap(),
        native::read(&after).unwrap()
    );
    let rows = native::read(replayed.environment()).unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].proof, Some(n("proof")));
    assert_eq!(rows[0].order, 2);
}

#[test]
fn pinned_prelude_defaults_reach_source_simp_and_keep_negative_controls() {
    let root = n("Init.Prelude");
    let input = OleanModuleInput {
        name: &root,
        artifact: include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../fln-conformance/fixtures/tag_attributes/prelude.olean"
        )),
        server_artifact: Some(include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../fln-conformance/fixtures/tag_attributes/prelude.olean.server"
        ))),
        private_artifact: Some(include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../fln-conformance/fixtures/tag_attributes/prelude.olean.private"
        ))),
    };
    on_import_stack(|| {
        let receipt = Engine::from_environment(Environment::new())
            .import_olean_modules_for_source(
                &[input],
                std::slice::from_ref(&root),
                &KVMap::new(),
                limits(1),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(receipt.modules.len(), 1);
        let report = &receipt.modules[0];
        assert_eq!(
            (report.simps, report.activated_simps, report.deferred_simps),
            (3, 3, 0)
        );
        let before = receipt.engine.logical_root(&KVMap::new());
        let check = |body: &str| {
            let main = n("Main");
            let source = format!("prelude\nimport Init.Prelude\n{body}\n");
            receipt.check_source_modules(
                &[SourceModuleInput {
                    name: &main,
                    source: source.as_bytes(),
                }],
                &main,
                &KVMap::new(),
                crate::source_check::modules::SourceModuleCheckLimits::new(SourceCheckLimits::new(
                    EngineAdmissionLimits::new(Budget::for_stack_bytes(64 * 1024 * 1024)),
                )),
                None,
            )
        };
        for body in [
            "theorem imported_default (n : Nat) : id n = n := by simp",
            "theorem explicit_default (n : Nat) : id n = n := by simp only [id_eq]",
        ] {
            let result = check(body).unwrap().into_complete().unwrap();
            assert_eq!(result.checked.theorems, 1);
        }
        for (body, message) in [
            (
                "theorem no_default (n : Nat) : id n = n := by simp only",
                "made no progress",
            ),
            (
                "theorem excluded (n : Nat) : id n = n := by simp [-id_eq]",
                "made no progress",
            ),
            (
                "attribute [-simp] id_eq\ntheorem erased (n : Nat) : id n = n := by simp",
                "made no progress",
            ),
            // No default rule here reduces `0 = 1`. The pin's simp would, through a
            // built-in literal simproc this engine lacks (under `import Init.Tactics` it
            // then fails on `Unknown constant eq_false'`). "unsolved goals" was once read
            // here because unfolding the absent `Eq.ndrec` normalized the `let` kept for
            // the ascription `(0 : Nat)`; that is not progress (b59e8668).
            (
                "theorem false_goal : (0 : Nat) = 1 := by simp",
                "made no progress",
            ),
        ] {
            let Err(crate::source_check::modules::SourceModuleCheckError::Source { error, .. }) =
                check(body)
            else {
                panic!("expected source refusal, not an import failure or resource stop: {body}")
            };
            assert!(error.to_string().contains(message), "{body}: {error}");
            assert_eq!(receipt.engine.logical_root(&KVMap::new()), before);
        }
    });
}

#[test]
fn pinned_init_restores_the_reported_list_and_nat_default_simp_goals() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent");
        return;
    };
    let closure = closure(&lib, &["Init"]);
    let inputs = inputs(&closure);
    on_import_stack(|| {
        let receipt = Engine::from_environment(Environment::new())
            .import_olean_modules_for_source(&inputs, &[n("Init")], &KVMap::new(), limits(4))
            .unwrap()
            .into_complete()
            .unwrap();
        let journal = receipt
            .engine
            .environment()
            .extension(&n("FrankenLean.sourceSimp.v1"))
            .expect("Init must retain its native default-simp journal");
        // This is the historical failing population boundary, not a new
        // capacity setting. Exercise it with the pin's real admitted rules.
        assert!(
            journal.len() > 4096,
            "Init must exercise the old row ceiling"
        );
        eprintln!(
            "Init native simp journal: {} events, {} retained payload bytes",
            journal.len(),
            journal.payload_bytes()
        );
        let main = n("Main");
        let source = b"import Init\ntheorem imported_append (xs : List Nat) : (xs ++ []).length = xs.length := by simp\ntheorem imported_add (n : Nat) : n + 0 = n := by simp\n";
        let result = receipt
            .check_source_modules(
                &[SourceModuleInput {
                    name: &main,
                    source,
                }],
                &main,
                &KVMap::new(),
                crate::source_check::modules::SourceModuleCheckLimits::new(SourceCheckLimits::new(
                    EngineAdmissionLimits::new(Budget::for_stack_bytes(64 * 1024 * 1024)),
                )),
                None,
            )
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(result.checked.theorems, 2);
    });
}
