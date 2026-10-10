//! Actual pinned comparison data, not admission of an imported module closure.
//!
//! The fixture retains decoded constants and extern entries only. Every source
//! example and every changed definition below still crosses both ordinary
//! declaration checkers before compiler ingress. No Reference code executes.

use super::*;
use fln_elab::externs::{self, ExternEntry};
use fln_olean::source_extensions as metadata;
use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::sync::OnceLock;

const STACK: usize = 64 * 1024 * 1024;
const BYTES: usize = 256 * 1024 * 1024;
const MODULES: [&str; 10] = [
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
];

struct Fixture {
    environment: Environment,
    externs: BTreeMap<Name, Vec<ExternEntry>>,
}

fn inventory() -> BTreeMap<Name, &'static str> {
    let mut rows = BTreeMap::new();
    for line in DEPENDENCIES.lines() {
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
            let needed = inventory();
            let mut constants = BTreeMap::new();
            let mut actual_externs = BTreeMap::new();
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
                    if needed.contains_key(info.name()) {
                        // The inventory was extracted in this module order. Keep the
                        // first actual declaration, including its actual theorem body;
                        // never select or manufacture a body to match an expected hash.
                        constants.entry(info.name().clone()).or_insert(info);
                    }
                }
            }
            assert_eq!(
                constants.len(),
                needed.len(),
                "all actual dependencies are present"
            );
            let mut environment = Environment::new();
            for info in constants.into_values() {
                environment = environment.add_decl(info).unwrap();
            }
            assert!(actual_externs.contains_key(&name("String.append")));
            assert!(actual_externs.contains_key(&name("String.toByteArray")));
            assert!(actual_externs.contains_key(&name("Array.toList")));
            assert!(
                actual_externs.len() > 1,
                "helper metadata was not discarded"
            );
            for (label, entries) in &actual_externs {
                environment = externs::register(&environment, label, entries.clone()).unwrap();
            }
            Some(Fixture {
                environment,
                externs: actual_externs,
            })
        })
        .as_ref()
}

fn with_fixture(test: impl FnOnce(&Fixture) + Send + 'static) {
    std::thread::Builder::new()
        .name("fln-string-append-fixture".to_owned())
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

fn matches(environment: &Environment) -> Result<bool, IngressError> {
    imported_string_append_matches(
        environment,
        &name("String.append"),
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

/// Recompute reachability from decoded declarations independently of the fixed
/// inventory. The graph includes erased proof bodies as well as data bodies.
fn actual_dependencies(environment: &Environment) -> BTreeSet<Name> {
    let mut pending = vec![name("String.append")];
    let mut found = BTreeSet::new();
    while let Some(label) = pending.pop() {
        if !found.insert(label.clone()) {
            continue;
        }
        let info = environment
            .find(&label)
            .unwrap_or_else(|| panic!("omitted actual dependency {}", label.to_display_string()));
        let mut expressions = vec![&info.constant_val().type_];
        match info {
            ConstantInfo::Defn(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Opaque(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Thm(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Induct(value) => {
                pending.extend(value.all.iter().cloned());
                pending.extend(value.ctors.iter().cloned());
            }
            ConstantInfo::Ctor(value) => pending.push(value.induct.clone()),
            ConstantInfo::Rec(value) => {
                pending.extend(value.all.iter().cloned());
                pending.extend(value.rules.iter().map(|rule| rule.ctor.clone()));
                expressions.extend(value.rules.iter().map(|rule| &rule.rhs));
            }
            ConstantInfo::Axiom(_) | ConstantInfo::Quot(_) => {}
        }
        while let Some(expression) = expressions.pop() {
            match expression.node() {
                ExprNode::Const { name, .. } => pending.push(name.clone()),
                ExprNode::App { f, a } => expressions.extend([f, a]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    expressions.extend([binder_type, body]);
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    expressions.extend([type_, value, body]);
                }
                ExprNode::Proj {
                    struct_name, expr, ..
                } => {
                    pending.push(struct_name.clone());
                    expressions.push(expr);
                }
                ExprNode::MData { expr, .. } => expressions.push(expr),
                _ => {}
            }
        }
    }
    found
}

#[test]
fn actual_append_inventory_closes_every_dependency_and_selects_the_native_row() {
    with_fixture(|fixture| {
        let rows = inventory();
        assert_eq!(rows.len(), 376);
        assert_eq!(
            actual_dependencies(&fixture.environment),
            rows.keys().cloned().collect()
        );
        for (label, digest) in rows {
            assert_eq!(
                fixture.environment.entry(&label).unwrap().digest().to_hex(),
                digest
            );
        }
        assert!(matches(&fixture.environment).unwrap());
        let binding = executable_intrinsic_binding(
            &fixture.environment,
            &name("String.append"),
            &mut 0,
            IngressLimits::default(),
        )
        .unwrap()
        .unwrap();
        assert_eq!(binding.row, "extern:String.append");
        assert_eq!(binding.arguments, [ValueType::String, ValueType::String]);
        assert_eq!(binding.result, ValueType::String);
        assert_eq!(binding.effect, fln_comp::fir::EffectClass::Pure);
        assert_eq!(
            binding.argument_ownership,
            [
                fln_comp::flbc::ArgumentOwnership::Owned,
                fln_comp::flbc::ArgumentOwnership::Borrowed,
            ]
        );
    });
}

#[test]
fn actual_public_append_executes_checked_unicode_empty_partial_and_repeated_calls() {
    with_fixture(|fixture| {
        let engine = Engine::from_environment(fixture.environment.clone());
        let options = KVMap::new();
        let before = engine.logical_root(&options);
        let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
        let source = "def twice (s : String) : String := String.append s s\n#eval String.append \"\" \"\"\n#eval String.append \"λ\\x00\" \"é😀\"\n#eval (let pfx := String.append \"λ\"; pfx \"🙂\")\n#eval twice \"é\"\n#eval String.append \"left\" \"\"\n";
        let run = || {
            engine
                .execute_source_commands_with_checks(source.as_bytes(), &options, limits)
                .unwrap_or_else(|error| panic!("checked append source: {error:?}"))
                .into_complete()
                .unwrap()
        };
        let first = run();
        let indices = &first.batch.source_evaluation_indices;
        assert_eq!(indices.len(), 5);
        for (&index, expected) in indices.iter().zip(["", "λ\0é😀", "λ🙂", "éé", "left"]) {
            let execution = &first.batch.executions[index];
            assert_eq!(
                execution.checker.ground,
                CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
            );
            assert_eq!(
                closed_vm_value(&execution.exit).unwrap(),
                Some(ClosedVmValue::String(expected.to_owned()))
            );
            let row = b"extern:String.append";
            assert!(
                execution
                    .flbc_artifact
                    .windows(row.len())
                    .any(|bytes| bytes == row)
            );
            let replay =
                execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
                    .unwrap()
                    .into_complete()
                    .unwrap();
            assert_eq!(
                closed_vm_value(&replay).unwrap(),
                Some(ClosedVmValue::String(expected.to_owned()))
            );
        }
        let repeated = run();
        assert_eq!(indices, &repeated.batch.source_evaluation_indices);
        for &index in indices {
            assert_eq!(
                first.batch.executions[index].flbc_artifact,
                repeated.batch.executions[index].flbc_artifact
            );
        }
        assert_eq!(engine.logical_root(&options), before);
    });
}

#[test]
fn well_typed_changed_append_bodies_do_not_acquire_the_original_native_semantics() {
    with_fixture(|fixture| {
        let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
        for (label, result) in [("String.append", 1), ("ByteArray.append", 0)] {
            let target = name(label);
            let Some(ConstantInfo::Defn(original)) = fixture.environment.find(&target) else {
                panic!("actual safe append definition {label}");
            };
            let mut changed = original.clone();
            let mut binders = Vec::new();
            let mut current = &original.value;
            loop {
                match current.node() {
                    ExprNode::MData { expr, .. } => current = expr,
                    ExprNode::Lam {
                        binder_name,
                        binder_type,
                        body,
                        binder_info,
                    } => {
                        binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
                        current = body;
                    }
                    _ => break,
                }
            }
            assert_eq!(binders.len(), 2);
            let mut body = Expr::bvar(result).unwrap();
            for (binder, type_, info) in binders.into_iter().rev() {
                body = Expr::lam(binder, type_, body, info);
            }
            changed.value = body;
            let changed = Engine::from_environment(rebuild(fixture, Some(&target), None))
                .admit_declaration(
                    Declaration::Defn(changed),
                    &KVMap::new(),
                    limits.admission(),
                )
                .expect("the changed definition has the original type under both checkers")
                .into_complete()
                .unwrap()
                .engine;
            // Restore the unchanged *actual* extern row after ordinary admission.
            let environment = fixture.externs.get(&target).map_or_else(
                || changed.environment().clone(),
                |entries| {
                    externs::register(changed.environment(), &target, entries.clone()).unwrap()
                },
            );
            let changed = Engine::from_environment(environment);
            assert!(
                matches!(
                    matches(changed.environment()),
                    Err(IngressError::UnsupportedNode { .. })
                ),
                "{label}"
            );
            let options = KVMap::new();
            let before = changed.logical_root(&options);
            let error = changed
                .execute_source_definition(
                    b"def alteredAppend : String := String.append \"left\" \"right\"",
                    &options,
                    limits,
                )
                .expect_err("a typed mutation must not inherit the native result");
            assert!(
                matches!(
                    error,
                    EngineExecutionError::Ingress(IngressError::UnsupportedNode { .. })
                ),
                "{label}: {error:?}"
            );
            assert_eq!(changed.logical_root(&options), before);
        }
    });
}

#[test]
fn missing_contracts_conflicting_externs_and_budget_exhaustion_never_authorize_append() {
    with_fixture(|fixture| {
        let root = name("String.append");
        assert!(!matches(&rebuild(fixture, None, Some(&root))).unwrap());
        for label in [
            "String.toByteArray",
            "ByteArray.append",
            "List.rec",
            "ByteArray.IsValidUTF8",
        ] {
            assert!(
                matches!(
                    matches(&rebuild(fixture, Some(&name(label)), None)),
                    Err(IngressError::UnsupportedNode { .. })
                ),
                "{label}"
            );
        }
        for label in ["String.append", "String.toByteArray"] {
            for entry in [
                ExternEntry::Opaque,
                ExternEntry::Standard {
                    backend: name("all"),
                    symbol: "foreign_append_contract".to_owned(),
                },
            ] {
                let changed =
                    externs::register(&fixture.environment, &name(label), vec![entry]).unwrap();
                assert!(
                    matches!(matches(&changed), Err(IngressError::UnsupportedNode { .. })),
                    "{label}"
                );
            }
        }
        let mut measured = 0;
        assert!(
            imported_string_append_matches(
                &fixture.environment,
                &root,
                &mut None,
                &mut measured,
                IngressLimits::default()
            )
            .unwrap()
        );
        assert!(measured > inventory().len());
        let error = imported_string_append_matches(
            &fixture.environment,
            &root,
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
        assert!(
            matches(&fixture.environment).unwrap(),
            "budget refusal does not poison a retry"
        );
    });
}
