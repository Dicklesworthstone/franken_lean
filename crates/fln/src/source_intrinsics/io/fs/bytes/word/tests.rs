//! Actual pinned comparison data, not admission of an imported module closure.
//!
//! The fixture retains decoded constants, externs, and the LT instance journal.
//! Every source
//! example and every changed definition below still crosses both ordinary
//! declaration checkers before compiler ingress. No Reference code executes.
#![cfg(test)]

use super::*;
use fln_elab::externs::{self, ExternEntry};
use fln_olean::source_extensions as metadata;
use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::sync::OnceLock;

const STACK: usize = 64 * 1024 * 1024;
const BYTES: usize = 256 * 1024 * 1024;
const MODULES: [&str; 12] = [
    "Init/Prelude",
    "Init/Core",
    "Init/Data/List/Basic",
    "Init/Data/UInt/BasicAux",
    "Init/GetElem",
    "Init/Data/ByteArray/Bootstrap",
    "Init/Data/ByteArray/Basic",
    "Init/Data/String/Defs",
    "Init/SimpLemmas",
    "Init/Data/ByteArray/Lemmas",
    "Init/Data/Char/Basic",
    "Init/Data/Repr",
];

struct Fixture {
    environment: Environment,
    externs: BTreeMap<Name, Vec<ExternEntry>>,
}

fn inventory(text: &'static str) -> BTreeMap<Name, &'static str> {
    let mut rows = BTreeMap::new();
    for line in text.lines() {
        let (encoded, digest) = line.split_once('\t').unwrap();
        let label = dependency_name(encoded, &mut 0, IngressLimits::default()).unwrap();
        assert!(
            rows.insert(label, digest).is_none(),
            "duplicate inventory row"
        );
    }
    rows
}

fn fixture() -> Option<&'static Fixture> {
    static FIXTURE: OnceLock<Option<Fixture>> = OnceLock::new();
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
                .filter(|library| library.is_dir());
            let Some(library) = library else {
                assert!(
                    std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                    "the actual pinned Reference library is required"
                );
                eprintln!("SKIP: pinned Reference lib/lean absent");
                return None;
            };
            let mut needed = inventory(DEPENDENCIES);
            for (label, digest) in inventory(REPR_DEPENDENCIES) {
                assert!(needed.insert(label, digest).is_none());
            }
            for line in BOUNDED_DEPENDENCIES.lines() {
                let columns: Vec<_> = line.split('\t').collect();
                assert_eq!(columns.len(), 5);
                let label = dependency_name(columns[0], &mut 0, IngressLimits::default()).unwrap();
                if let Some(previous) = needed.insert(label, columns[1]) {
                    assert_eq!(previous, columns[1], "shared actual model identity");
                }
            }
            let mut constants = BTreeMap::new();
            let mut actual_externs = BTreeMap::new();
            let mut classes = Vec::new();
            let mut instances = Vec::new();
            for module in MODULES {
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
                    OleanDecodeLimits::new(BYTES),
                )
                .unwrap();
                let view = if decoded.module.is_module {
                    fln_olean::region::OleanView::parse_with_dependencies(
                        &parts[2],
                        &[parts[0].as_slice(), parts[1].as_slice()],
                    )
                } else {
                    fln_olean::region::OleanView::parse(&parts[0])
                }
                .unwrap();
                let blocks = view
                    .extension_payloads(OleanWalkBudget::default(), BYTES)
                    .unwrap();
                let extensions =
                    metadata::decode(&blocks, metadata::DecodeLimits::default()).unwrap();
                classes.extend(
                    extensions
                        .classes
                        .into_iter()
                        .filter(|row| row.name == name("LT")),
                );
                instances.extend(
                    extensions
                        .instances
                        .into_iter()
                        .filter(|row| row.declaration == name("instLTNat")),
                );
                for row in extensions.externs {
                    if !needed.contains_key(&row.declaration) {
                        continue;
                    }
                    let entries: Vec<_> = row
                        .entries
                        .into_iter()
                        .map(|entry| match entry {
                            metadata::ExternEntry::Adhoc { backend } => {
                                ExternEntry::Adhoc { backend }
                            }
                            metadata::ExternEntry::Inline { backend, pattern } => {
                                ExternEntry::Inline { backend, pattern }
                            }
                            metadata::ExternEntry::Standard { backend, symbol } => {
                                ExternEntry::Standard { backend, symbol }
                            }
                            metadata::ExternEntry::Opaque => ExternEntry::Opaque,
                        })
                        .collect();
                    if let Some(previous) = actual_externs.insert(row.declaration, entries.clone())
                    {
                        assert_eq!(previous, entries, "conflicting actual helper externs");
                    }
                }
                for info in decoded.constants {
                    // Keep the first actual declaration in the extraction's
                    // module order. The source probes additionally use proof
                    // projections outside the executable word model itself.
                    constants.entry(info.name().clone()).or_insert(info);
                }
            }
            let mut decoded = Environment::new();
            for info in constants.into_values() {
                decoded = decoded.add_decl(info).unwrap();
            }
            let mut retained = super::super::actual_dependencies(
                &decoded,
                &["Fin.isLt", "BitVec.toFin", "USize.size_pos"],
            );
            for (label, digest) in &needed {
                assert_eq!(
                    decoded.entry(label).unwrap().digest().to_hex(),
                    *digest,
                    "every original model entry retains its actual identity"
                );
                retained.insert(label.clone());
            }
            let mut environment = Environment::new();
            for label in &retained {
                environment = environment
                    .with_entry(decoded.entry(label).unwrap())
                    .unwrap();
            }
            assert_eq!(environment.constants().count(), retained.len());
            assert!(actual_externs.contains_key(&name("USize.repr")));
            assert!(actual_externs.contains_key(&name("USize.ofNat")));
            assert!(actual_externs.contains_key(&name("USize.ofBitVec")));
            assert!(
                actual_externs.len() > 1,
                "helper metadata was not discarded"
            );
            for (label, entries) in &actual_externs {
                environment = externs::register(&environment, label, entries.clone()).unwrap();
            }
            // Raw constant decoding does not activate class metadata. Without
            // this actual journal, `<` takes the bounded Nat decision bridge,
            // whose Decidable result cannot be used as a binder proposition.
            use fln_elab::instances::imported;
            assert_eq!(classes.len(), 1, "the actual LT class journal");
            assert_eq!(instances.len(), 1, "the actual Nat LT instance journal");
            let mut activation = imported::ImportActivation::new(environment);
            for row in classes {
                activation = activation
                    .register_class(
                        &row.name,
                        &imported::ClassParameters {
                            out_params: row.out_params,
                            out_level_params: row.out_level_params,
                        },
                    )
                    .unwrap();
            }
            for row in instances {
                assert_eq!(row.value, c("instLTNat"));
                activation = activation
                    .register_instance(
                        &row.declaration,
                        &imported::InstanceParameters {
                            priority: row.priority,
                            synth_order: row.synth_order,
                            scope: row.scope,
                            keys: row.keys.into_iter().map(instance_key).collect(),
                        },
                    )
                    .unwrap();
            }
            let environment = activation.finish().unwrap();
            Some(Fixture {
                environment,
                externs: actual_externs,
            })
        })
        .as_ref()
}

fn instance_key(key: metadata::DiscrTreeKey) -> fln_elab::instances::discr_tree::Key {
    use fln_elab::instances::discr_tree::Key;
    match key {
        metadata::DiscrTreeKey::Star => Key::Star,
        metadata::DiscrTreeKey::Other => Key::Other,
        metadata::DiscrTreeKey::Lit(literal) => Key::Lit(literal),
        metadata::DiscrTreeKey::FVar(name, arity) => Key::FVar(fln_core::expr::FVarId(name), arity),
        metadata::DiscrTreeKey::Const(name, arity) => Key::Const(name, arity),
        metadata::DiscrTreeKey::Arrow => Key::Arrow,
        metadata::DiscrTreeKey::Proj(name, field, arity) => Key::Proj(name, field, arity),
    }
}

fn with_fixture(test: impl FnOnce(&Fixture) + Send + 'static) {
    std::thread::Builder::new()
        .name("fln-pure-word-fixture".to_owned())
        .stack_size(STACK)
        .spawn(move || {
            if let Some(fixture) = fixture() {
                test(fixture);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

fn matches_word(environment: &Environment, label: &str) -> Result<bool, IngressError> {
    word_matches(
        environment,
        &name(label),
        &mut None,
        &mut 0,
        IngressLimits::default(),
    )
}

fn rebuild(fixture: &Fixture, missing: Option<&Name>, omit_extern: Option<&Name>) -> Environment {
    let mut environment = Environment::new();
    for (label, _) in fixture.environment.constants() {
        if missing != Some(label) {
            environment = environment
                .with_entry(fixture.environment.entry(label).unwrap())
                .unwrap();
        }
    }
    for (label, entries) in &fixture.externs {
        if missing != Some(label) && omit_extern != Some(label) {
            environment = externs::register(&environment, label, entries.clone()).unwrap();
        }
    }
    environment
}

#[derive(Debug)]
enum Expected {
    Nat(&'static str),
    String(&'static str),
}

fn assert_value(exit: &VmExit, expected: &Expected) {
    match expected {
        Expected::Nat(expected) => {
            let VmExit::Returned(returned) = exit else {
                panic!("expected Nat {expected}, got {exit:?}");
            };
            assert_eq!(
                fln_vm::interpreter::nat_decimal(&returned.value).as_deref(),
                Some(*expected)
            );
        }
        Expected::String(expected) => assert_eq!(
            closed_vm_value(exit).unwrap(),
            Some(ClosedVmValue::String((*expected).to_owned()))
        ),
    }
}

fn execute_and_replay(engine: &Engine, source: &str, expected: &[Expected]) {
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let completed = engine
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &options,
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .unwrap_or_else(|error| panic!("checked pure word source {source}: {error:?}"))
        .into_complete()
        .unwrap();
    let indices = &completed.batch.source_evaluation_indices;
    assert_eq!(indices.len(), expected.len());
    for (&index, expected) in indices.iter().zip(expected) {
        let execution = &completed.batch.executions[index];
        // #eval's auxiliary is unsafe at the pin (BuiltinEvalCommand.lean:92).
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::UnsafeQuarantine
        );
        assert_value(&execution.exit, expected);
        let replay = execute_flbc_artifact(
            &execution.flbc_artifact,
            &options,
            FlbcExecutionLimits::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
        assert_value(&replay, expected);
    }
    assert_eq!(engine.logical_root(&options), before);
}

fn checked_source(environment: Environment, source: &[u8]) -> Engine {
    Engine::from_environment(environment)
        .check_source_files(
            &[source],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::for_stack_bytes(STACK)),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

fn unary_body(type_: &Expr, body: Expr) -> Expr {
    let mut current = type_;
    while let ExprNode::MData { expr, .. } = current.node() {
        current = expr;
    }
    let ExprNode::ForallE {
        binder_name,
        binder_type,
        binder_info,
        body: result_type,
    } = current.node()
    else {
        panic!("one actual word argument");
    };
    assert!(!matches!(result_type.node(), ExprNode::ForallE { .. }));
    Expr::lam(binder_name.clone(), binder_type.clone(), body, *binder_info)
}

/// Change only the body of an actual one-argument definition, then obtain
/// ordinary agreement from both checker seats before restoring its real extern.
fn changed_body(fixture: &Fixture, label: &str, body: Expr) -> Engine {
    let target = name(label);
    let Some(ConstantInfo::Defn(original)) = fixture.environment.find(&target) else {
        panic!("actual safe word definition {label}");
    };
    let mut changed = original.clone();
    changed.value = unary_body(&original.base.type_, body);
    let admitted = Engine::from_environment(rebuild(fixture, Some(&target), None))
        .admit_declaration(
            Declaration::Defn(changed),
            &KVMap::new(),
            EngineAdmissionLimits::for_stack_bytes(STACK),
        )
        .expect("the changed body has the actual declared type under both checkers")
        .into_complete()
        .unwrap();
    assert_eq!(
        admitted.checker.ground,
        CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
    );
    Engine::from_environment(
        externs::register(
            admitted.engine.environment(),
            &target,
            fixture.externs.get(&target).unwrap().clone(),
        )
        .unwrap(),
    )
}

fn declared_printer(environment: &Environment, label: &str, text: &str) -> Engine {
    let Some(ConstantInfo::Defn(actual)) = environment.find(&name("USize.repr")) else {
        panic!("actual word printer signature");
    };
    // The native signature contains borrowed (@&) binder metadata. Reuse
    // that exact telescope, rather than weakening implemented_by's checked
    // signature relation to accept an ordinary owned source argument.
    let mut definition = actual.clone();
    definition.base.name = name(label);
    definition.all = vec![name(label)];
    definition.value = unary_body(
        &actual.base.type_,
        Expr::lit(fln_core::expr::Literal::Str(text.to_owned())),
    );
    let admitted = Engine::from_environment(environment.clone())
        .admit_declaration(
            Declaration::Defn(definition),
            &KVMap::new(),
            EngineAdmissionLimits::for_stack_bytes(STACK),
        )
        .expect("safe replacement body is ordinarily checked at the exact borrowed type")
        .into_complete()
        .unwrap();
    assert_eq!(
        admitted.checker.ground,
        CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
    );
    admitted.engine
}

#[test]
fn actual_pure_words_close_their_model_and_execute_without_io_contracts() {
    with_fixture(|fixture| {
        let base = inventory(DEPENDENCIES);
        let printing = inventory(REPR_DEPENDENCIES);
        assert_eq!(base.len(), 261);
        assert_eq!(printing.len(), 111);
        let base_names: BTreeSet<_> = base.keys().cloned().collect();
        assert_eq!(
            super::super::actual_dependencies(&fixture.environment, &WORD_HELPERS),
            base_names
        );
        let actual_printing =
            super::super::actual_dependencies(&fixture.environment, &["USize.repr"]);
        assert_eq!(actual_printing.len(), 371);
        assert_eq!(
            actual_printing
                .difference(&base_names)
                .cloned()
                .collect::<BTreeSet<_>>(),
            printing.keys().cloned().collect()
        );
        for (label, digest) in base.into_iter().chain(printing) {
            assert_eq!(
                fixture.environment.entry(&label).unwrap().digest().to_hex(),
                digest
            );
        }
        assert!(!fixture.environment.contains(&name("IO.Error")));
        assert!(!fixture.environment.contains(&name("IO.RealWorld")));
        for helper in ["USize.ofNat", "USize.toNat", "USize.repr"] {
            assert!(
                matches_word(&fixture.environment, helper).unwrap(),
                "{helper}"
            );
        }
        // The pinned artifact and ABI target use 64-bit words. Values above
        // that boundary must wrap before either logical projection or printing.
        assert_eq!(std::mem::size_of::<usize>(), 8);
        execute_and_replay(
            &Engine::from_environment(fixture.environment.clone()),
            r#"
#eval USize.toNat (USize.ofNat 0)
#eval USize.toNat (USize.ofNat 18446744073709551615)
#eval USize.toNat (USize.ofNat 18446744073709551616)
#eval USize.toNat (USize.ofNat 18446744073709551621)
#eval USize.repr (USize.ofNat 0)
#eval USize.repr (USize.ofNat 18446744073709551615)
#eval USize.repr (USize.ofNat 18446744073709551621)
#eval (let convert := USize.ofNat; USize.toNat (convert 42))
#eval (let project := USize.toNat; project (USize.ofNat 42))
#eval (let f := USize.repr; f (USize.ofNat 42))
"#,
            &[
                Expected::Nat("0"),
                Expected::Nat("18446744073709551615"),
                Expected::Nat("0"),
                Expected::Nat("5"),
                Expected::String("0"),
                Expected::String("18446744073709551615"),
                Expected::String("5"),
                Expected::Nat("42"),
                Expected::Nat("42"),
                Expected::String("42"),
            ],
        );
    });
}

#[test]
fn typed_word_changes_warm_caches_and_executable_aliases_keep_their_contracts() {
    with_fixture(|fixture| {
        for (label, body) in [
            (
                "USize.toNat",
                Expr::lit(fln_core::expr::Literal::Nat(
                    fln_core::expr::NatLit::from_u64(0),
                )),
            ),
            (
                "USize.repr",
                Expr::lit(fln_core::expr::Literal::Str("counterfeit".to_owned())),
            ),
        ] {
            let changed = changed_body(fixture, label, body);
            assert!(matches!(
                matches_word(changed.environment(), "USize.repr"),
                Err(IngressError::UnsupportedNode { .. })
            ));
            assert!(matches!(
                changed.execute_source_definition(
                    b"def changedWordOutput : String := USize.repr (USize.ofNat 7)",
                    &KVMap::new(),
                    EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
                ),
                Err(EngineExecutionError::Ingress(
                    IngressError::UnsupportedNode { .. }
                ))
            ));

            if label == "USize.repr" {
                // Both expressions are ordinarily checked first. A successful
                // conversion in this very same Preparation must not authorize
                // a different, unvalidated decimal-printer body afterward.
                let checked = checked_source(
                    changed.environment().clone(),
                    b"def warmWord : USize := USize.ofNat 7\ndef coldPrinter : String := USize.repr warmWord",
                );
                let value = |label| match checked.environment().find(&name(label)).unwrap() {
                    ConstantInfo::Defn(value) => value.value.clone(),
                    _ => panic!("checked source definition"),
                };
                let mut preparation = crate::runtime::Preparation::new(
                    checked.environment(),
                    IngressLimits::default(),
                );
                preparation.expression(&value("warmWord")).unwrap();
                assert!(matches!(
                    preparation.expression(&value("coldPrinter")),
                    Err(IngressError::UnsupportedNode { .. })
                ));
            }
        }

        let alternate =
            declared_printer(&fixture.environment, "alternateWordPrinter", "replacement");
        let ordinary = declared_printer(alternate.environment(), "ordinaryWordPrinter", "logical");
        let checked = checked_source(
            ordinary.environment().clone(),
            b"def bareWordAlias := USize.repr\ndef ordinaryWordAlias := ordinaryWordPrinter",
        );
        let replacement = fln_elab::implemented_by::register(
            checked.environment(),
            &name("USize.repr"),
            &name("alternateWordPrinter"),
        )
        .unwrap();
        execute_and_replay(
            &Engine::from_environment(replacement),
            "#eval (let f := USize.repr; f (USize.ofNat 7))\n#eval bareWordAlias (USize.ofNat 7)",
            &[
                Expected::String("replacement"),
                Expected::String("replacement"),
            ],
        );
        let native_endpoint = fln_elab::implemented_by::register(
            checked.environment(),
            &name("ordinaryWordPrinter"),
            &name("USize.repr"),
        )
        .unwrap();
        let logical = checked_source(
            native_endpoint,
            b"theorem originalWordBody : ordinaryWordPrinter (USize.ofNat 7) = \"logical\" := by rfl",
        );
        execute_and_replay(
            &logical,
            "#eval ordinaryWordAlias (USize.ofNat 7)\n#eval (let f := ordinaryWordPrinter; f (USize.ofNat 7))",
            &[Expected::String("7"), Expected::String("7")],
        );
    });
}

#[test]
fn incomplete_word_models_foreign_externs_and_exhaustion_never_authorize_native_calls() {
    with_fixture(|fixture| {
        for helper in ["USize.ofNat", "USize.toNat", "USize.repr"] {
            assert!(!matches_word(&rebuild(fixture, None, Some(&name(helper))), helper).unwrap());
        }
        for helper in WORD_HELPERS {
            assert!(matches!(
                matches_word(&rebuild(fixture, None, Some(&name(helper))), "USize.repr"),
                Err(IngressError::UnsupportedNode { .. })
            ));
        }
        for helper in [
            "System.Platform.numBits",
            "Nat.mod",
            "String.ofList",
            "Nat.toDigits",
        ] {
            assert!(fixture.environment.contains(&name(helper)), "{helper}");
            assert!(matches!(
                matches_word(&rebuild(fixture, Some(&name(helper)), None), "USize.repr"),
                Err(IngressError::UnsupportedNode { .. })
            ));
        }
        for helper in ["USize.repr", "USize.ofBitVec", "USize.toNat"] {
            for entry in [
                ExternEntry::Opaque,
                ExternEntry::Standard {
                    backend: name("all"),
                    symbol: "foreign_word_contract".to_owned(),
                },
            ] {
                let changed =
                    externs::register(&fixture.environment, &name(helper), vec![entry]).unwrap();
                assert!(matches!(
                    matches_word(&changed, "USize.repr"),
                    Err(IngressError::UnsupportedNode { .. })
                ));
            }
        }
        let mut measured = 0;
        assert!(
            word_matches(
                &fixture.environment,
                &name("USize.repr"),
                &mut None,
                &mut measured,
                IngressLimits::default(),
            )
            .unwrap()
        );
        assert!(measured > inventory(DEPENDENCIES).len() + inventory(REPR_DEPENDENCIES).len());
        let error = word_matches(
            &fixture.environment,
            &name("USize.repr"),
            &mut None,
            &mut 0,
            IngressLimits {
                max_nodes: measured - 1,
                ..IngressLimits::default()
            },
        )
        .unwrap_err();
        assert!(matches!(
            error,
            IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                ..
            }
        ));
        assert!(error.is_resource_exhaustion());
        assert!(matches_word(&fixture.environment, "USize.repr").unwrap());
    });
}

#[path = "platform_tests.rs"]
mod platform;

#[test]
fn bounded_words_preserve_proofs_partial_calls_and_native_rows() {
    with_fixture(|fixture| {
        let engine = Engine::from_environment(fixture.environment.clone());
        execute_and_replay(
            &engine,
            include_str!("../../../../../../tests/source_imported_arrays/bounded_words.lean")
                .strip_prefix(
                    "prelude\nimport Init.Data.Array.Basic\nimport Init.Data.List.Control\n\n",
                )
                .unwrap(),
            &[
                Expected::Nat("0"),
                Expected::Nat("42"),
                Expected::Nat("18446744073709551615"),
                Expected::Nat("0"),
                Expected::Nat("5"),
                Expected::Nat("0"),
                Expected::Nat("0"),
                Expected::Nat("0"),
            ],
        );
        let completed = engine
            .execute_source_commands_with_checks(
                b"#eval USize.toNat (USize.ofNatLT 0 USize.size_pos)",
                &KVMap::new(),
                EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        let index = completed.batch.source_evaluation_indices[0];
        let execution = &completed.batch.executions[index];
        let decoded = fln_comp::flbc::decode_canonical(
            &execution.flbc_artifact,
            fln_comp::flbc::CodecLimits::default(),
        )
        .unwrap();
        assert!(decoded.functions().iter().flat_map(|f| &f.code).any(|instruction| matches!(
            instruction, fln_comp::flbc::Instruction::Intrinsic { row, argument_ownership, .. }
            if row == "extern:USize.ofNatLT" && argument_ownership == &[fln_comp::flbc::ArgumentOwnership::Borrowed]
        )), "the proof-bearing call must use its actual native row");
    });
}

#[test]
fn bounded_words_refuse_changed_metadata_initializers_models_and_resource_exhaustion() {
    with_fixture(|fixture| {
        let requested = name("USize.ofNatLT");
        let check = |environment: &Environment| {
            let implementations =
                fln_elab::implemented_by::ImplementedByTable::read(environment).unwrap();
            assert!(
                bounded_word_matches(
                    environment,
                    &implementations,
                    None,
                    &mut None,
                    &mut 0,
                    IngressLimits::default()
                )
                .is_err()
            );
        };
        check(&rebuild(fixture, Some(&requested), None));
        let ConstantInfo::Defn(mut changed) = fixture.environment.find(&requested).unwrap().clone()
        else {
            unreachable!()
        };
        changed.value = Expr::app(
            Expr::lam(
                Name::anonymous(),
                changed.base.type_.clone(),
                Expr::bvar(0).unwrap(),
                BinderInfo::Default,
            ),
            changed.value.clone(),
        );
        check(
            &rebuild(fixture, Some(&requested), None)
                .add_decl(ConstantInfo::Defn(changed))
                .unwrap(),
        );
        for label in ["USize.ofNatLT", "USize.toNat", "USize.ofNat"] {
            check(
                &externs::register(
                    &fixture.environment,
                    &name(label),
                    vec![ExternEntry::Standard {
                        backend: name("all"),
                        symbol: "foreign_bounded_word".to_owned(),
                    }],
                )
                .unwrap(),
            );
            let initializers = BTreeSet::from([name(label)]);
            let implementations =
                fln_elab::implemented_by::ImplementedByTable::read(&fixture.environment).unwrap();
            assert!(
                bounded_word_matches(
                    &fixture.environment,
                    &implementations,
                    Some(&initializers),
                    &mut None,
                    &mut 0,
                    IngressLimits::default()
                )
                .is_err()
            );
        }
        let implementations =
            fln_elab::implemented_by::ImplementedByTable::read(&fixture.environment).unwrap();
        let mut cost = 0;
        bounded_word_matches(
            &fixture.environment,
            &implementations,
            None,
            &mut None,
            &mut cost,
            IngressLimits::default(),
        )
        .unwrap();
        assert!(cost > 1);
        assert!(matches!(
            bounded_word_matches(
                &fixture.environment,
                &implementations,
                None,
                &mut None,
                &mut 0,
                IngressLimits {
                    max_nodes: cost - 1,
                    ..IngressLimits::default()
                }
            ),
            Err(IngressError::ResourceLimit { .. })
        ));
        assert!(
            matches_word(&fixture.environment, "USize.ofNat").unwrap(),
            "a failed probe cannot poison a fresh word call"
        );
    });
}
