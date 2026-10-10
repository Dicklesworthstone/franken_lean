//! Actual Prelude comparison data, never admission of an imported module.
//! Every executed source candidate and changed definition is still admitted
//! through both ordinary checker seats. No Reference executable runs here.

use super::*;
use fln_elab::externs::{self, ExternEntry};
use fln_olean::source_extensions as metadata;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::path::PathBuf;
use std::sync::OnceLock;

const STACK: usize = 64 * 1024 * 1024;
const BYTES: usize = 256 * 1024 * 1024;

struct Fixture {
    environment: Environment,
    externs: BTreeMap<Name, Vec<ExternEntry>>,
}

fn rows(operation: &str) -> BTreeMap<Name, &'static str> {
    let mut rows = BTreeMap::new();
    for line in inventory(&name(operation)).unwrap().lines() {
        let (encoded, digest) = line.split_once('\t').unwrap();
        let label = dependency_name(encoded, &mut 0, IngressLimits::default()).unwrap();
        assert!(
            rows.insert(label, digest).is_none(),
            "duplicate inventory name"
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
            let mut needed = rows("Nat.div");
            needed.extend(rows("Nat.mod"));
            let path = library.join("Init/Prelude.olean");
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
            let extensions = metadata::decode(&blocks, metadata::DecodeLimits::default()).unwrap();
            let mut actual_externs = BTreeMap::new();
            for row in extensions.externs {
                if !needed.contains_key(&row.declaration) {
                    continue;
                }
                let entries = row
                    .entries
                    .into_iter()
                    .map(|entry| match entry {
                        metadata::ExternEntry::Adhoc { backend } => ExternEntry::Adhoc { backend },
                        metadata::ExternEntry::Inline { backend, pattern } => {
                            ExternEntry::Inline { backend, pattern }
                        }
                        metadata::ExternEntry::Standard { backend, symbol } => {
                            ExternEntry::Standard { backend, symbol }
                        }
                        metadata::ExternEntry::Opaque => ExternEntry::Opaque,
                    })
                    .collect::<Vec<_>>();
                if let Some(previous) = actual_externs.insert(row.declaration, entries.clone()) {
                    assert_eq!(previous, entries, "conflicting actual extern metadata");
                }
            }
            let mut constants = BTreeMap::new();
            for info in decoded.constants {
                if needed.contains_key(info.name()) {
                    // Keep the actual decoded declaration, never a declaration
                    // selected or manufactured to match an expected digest.
                    constants.entry(info.name().clone()).or_insert(info);
                }
            }
            assert_eq!(constants.len(), needed.len());
            let mut environment = Environment::new();
            for info in constants.into_values() {
                environment = environment.add_decl(info).unwrap();
            }
            for (label, entries) in &actual_externs {
                environment = externs::register(&environment, label, entries.clone()).unwrap();
            }
            for label in ["Nat.div", "Nat.mod", "Nat.modCore", "Nat.sub", "Nat.ble"] {
                assert!(
                    actual_externs.contains_key(&name(label)),
                    "actual extern {label}"
                );
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
        .name("fln-nat-div-mod-fixture".to_owned())
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

fn selected(environment: &Environment, operation: &str) -> Result<bool, IngressError> {
    matches(
        environment,
        &name(operation),
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

/// Compute the complete graph from actual declarations independently of the
/// inventory, including erased proofs and all constructor/recursor metadata.
fn actual_dependencies(environment: &Environment, root: &str) -> BTreeSet<Name> {
    let mut pending = vec![name(root)];
    let mut found = BTreeSet::new();
    while let Some(label) = pending.pop() {
        if !found.insert(label.clone()) {
            continue;
        }
        let info = environment
            .find(&label)
            .unwrap_or_else(|| panic!("missing actual dependency {}", label.to_display_string()));
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
        let mut visited = HashSet::new();
        while let Some(expression) = expressions.pop() {
            if !visited.insert(expression) {
                continue;
            }
            match expression.node() {
                ExprNode::Const { name, .. } => pending.push(name.clone()),
                ExprNode::App { f, a } => expressions.extend([f, a]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => expressions.extend([binder_type, body]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => expressions.extend([type_, value, body]),
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

fn execute_and_replay(environment: &Environment, source: &str, expected: &[(&str, Option<&str>)]) {
    let engine = Engine::from_environment(environment.clone());
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let completed = engine
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &options,
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .unwrap_or_else(|error| panic!("checked Nat division source {source}: {error:?}"))
        .into_complete()
        .unwrap();
    let indices = &completed.batch.source_evaluation_indices;
    assert_eq!(indices.len(), expected.len());
    for (&index, (expected, row)) in indices.iter().zip(expected) {
        let execution = &completed.batch.executions[index];
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        let program = fln_comp::flbc::decode_canonical(
            &execution.flbc_artifact,
            fln_comp::flbc::CodecLimits::default(),
        )
        .unwrap();
        assert_eq!(
            fln_comp::flbc::encode_canonical(&program, Default::default()).unwrap(),
            execution.flbc_artifact
        );
        for candidate in ["extern:Nat.div", "extern:Nat.mod"] {
            assert_eq!(
                execution
                    .flbc_artifact
                    .windows(candidate.len())
                    .any(|bytes| bytes == candidate.as_bytes()),
                *row == Some(candidate)
            );
        }
        let replay = execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
            .unwrap()
            .into_complete()
            .unwrap();
        for exit in [&execution.exit, &replay] {
            let VmExit::Returned(value) = exit else {
                panic!("Nat operation did not return: {exit:?}");
            };
            assert_eq!(
                fln_vm::interpreter::nat_decimal(&value.value).unwrap(),
                *expected
            );
        }
    }
    assert_eq!(engine.logical_root(&options), before);
}

fn constant_body(type_: &Expr, result: u64) -> Expr {
    let mut type_ = type_;
    let mut binders = Vec::new();
    loop {
        match type_.node() {
            ExprNode::MData { expr, .. } => type_ = expr,
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
                type_ = body;
            }
            _ => break,
        }
    }
    assert_eq!(type_, &Expr::const_(name("Nat"), Vec::new()));
    binders.into_iter().rev().fold(
        Expr::lit(fln_core::expr::Literal::Nat(
            fln_core::expr::NatLit::from_u64(result),
        )),
        |body, (label, domain, info)| Expr::lam(label, domain, body, info),
    )
}

fn admit_constant(
    environment: Environment,
    original: &fln_env::constants::DefinitionVal,
    label: &str,
    result: u64,
) -> Engine {
    let mut definition = original.clone();
    definition.base.name = name(label);
    definition.all = vec![name(label)];
    definition.value = constant_body(&original.base.type_, result);
    let admitted = Engine::from_environment(environment)
        .admit_declaration(
            Declaration::Defn(definition),
            &KVMap::new(),
            EngineAdmissionLimits::for_stack_bytes(STACK),
        )
        .expect("constant replacement checks at the exact actual borrowed telescope")
        .into_complete()
        .unwrap();
    assert_eq!(
        admitted.checker.ground,
        CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
    );
    admitted.engine
}

#[test]
fn actual_division_models_execute_large_zero_and_partial_calls_with_canonical_replay() {
    with_fixture(|fixture| {
        for (operation, count) in [("Nat.div", 167), ("Nat.mod", 171)] {
            let rows = rows(operation);
            assert_eq!(rows.len(), count);
            assert_eq!(
                actual_dependencies(&fixture.environment, operation),
                rows.keys().cloned().collect()
            );
            for (label, digest) in rows {
                assert_eq!(
                    fixture.environment.entry(&label).unwrap().digest().to_hex(),
                    digest
                );
            }
            assert!(selected(&fixture.environment, operation).unwrap());
            let binding = executable_intrinsic_binding(
                &fixture.environment,
                &name(operation),
                &mut 0,
                IngressLimits::default(),
            )
            .unwrap()
            .unwrap();
            assert_eq!(binding.row, format!("extern:{operation}"));
            assert_eq!(binding.arguments, [ValueType::Nat, ValueType::Nat]);
            assert_eq!(binding.result, ValueType::Nat);
            assert_eq!(
                binding.argument_ownership,
                [fln_comp::flbc::ArgumentOwnership::Borrowed; 2]
            );
            assert_eq!(
                binding.result_ownership,
                fln_comp::flbc::ResultOwnership::Owned
            );
            assert_eq!(binding.effect, fln_comp::fir::EffectClass::Pure);
        }
        assert!(!fixture.environment.contains(&name("IO.RealWorld")));
        execute_and_replay(
            &fixture.environment,
            r#"
#eval Nat.div 128512 64
#eval Nat.mod 128513 64
#eval Nat.div 340282366920938463463374607431768211507 97
#eval Nat.mod 340282366920938463463374607431768211507 97
#eval Nat.div 340282366920938463463374607431768211507 0
#eval Nat.mod 340282366920938463463374607431768211507 0
#eval Nat.div 0 3
#eval Nat.mod 0 7
#eval (let divide := Nat.div; divide 43 10)
#eval (let remainder := Nat.mod 43; remainder 10)
"#,
            &[
                ("2008", Some("extern:Nat.div")),
                ("1", Some("extern:Nat.mod")),
                (
                    "3508065638360190344983243375585239293",
                    Some("extern:Nat.div"),
                ),
                ("86", Some("extern:Nat.mod")),
                ("0", Some("extern:Nat.div")),
                (
                    "340282366920938463463374607431768211507",
                    Some("extern:Nat.mod"),
                ),
                ("0", Some("extern:Nat.div")),
                ("0", Some("extern:Nat.mod")),
                ("4", Some("extern:Nat.div")),
                ("3", Some("extern:Nat.mod")),
            ],
        );
    });
}

#[test]
fn admitted_changes_and_executable_replacements_preserve_logical_and_runtime_authority() {
    with_fixture(|fixture| {
        for (operation, changed) in [
            ("Nat.div", "Nat.div"),
            ("Nat.div", "Nat.div.go"),
            ("Nat.mod", "Nat.mod"),
            ("Nat.mod", "Nat.modCore"),
        ] {
            let ConstantInfo::Defn(original) = fixture.environment.find(&name(changed)).unwrap()
            else {
                panic!("actual safe definition");
            };
            let admitted = admit_constant(
                rebuild(fixture, Some(&name(changed)), None),
                original,
                changed,
                7,
            );
            let environment = fixture.externs.get(&name(changed)).map_or_else(
                || admitted.environment().clone(),
                |entries| {
                    externs::register(admitted.environment(), &name(changed), entries.clone())
                        .unwrap()
                },
            );
            assert!(
                matches!(
                    selected(&environment, operation),
                    Err(IngressError::UnsupportedNode { .. })
                ),
                "{changed}"
            );
            let engine = Engine::from_environment(environment);
            let options = KVMap::new();
            let before = engine.logical_root(&options);
            let source = format!("def changedAnswer : Nat := {operation} 43 10");
            assert!(matches!(
                engine.execute_source_definition(
                    source.as_bytes(),
                    &options,
                    EngineExecutionLimits::new(Budget::for_stack_bytes(STACK))
                ),
                Err(EngineExecutionError::Ingress(
                    IngressError::UnsupportedNode { .. }
                ))
            ));
            assert_eq!(engine.logical_root(&options), before);
        }

        for operation in ["Nat.div", "Nat.mod"] {
            let ConstantInfo::Defn(original) = fixture.environment.find(&name(operation)).unwrap()
            else {
                panic!("actual safe arithmetic");
            };
            let alternative = admit_constant(
                fixture.environment.clone(),
                original,
                "alternateArithmetic",
                7,
            );
            let environment = fln_elab::implemented_by::register(
                alternative.environment(),
                &name(operation),
                &name("alternateArithmetic"),
            )
            .unwrap();
            // The checked logical zero case keeps its original result. This
            // witness does not need to normalize the pin's proof-bearing fuel
            // recursion; the large arithmetic cases above execute unchanged.
            // Only executable selection changes, including bare/partial calls.
            execute_and_replay(
                &environment,
                &format!(
                    r#"
theorem logicalArithmetic : {operation} 0 0 = 0 := rfl
#eval {operation} 0 0
#eval (let calculate := {operation}; calculate 0 0)
#eval (let calculate := {operation} 0; calculate 0)
"#
                ),
                &[("7", None), ("7", None), ("7", None)],
            );

            // A checked source function may also select the genuine imported
            // native target, retaining its original logical constant body.
            let ordinary = admit_constant(
                fixture.environment.clone(),
                original,
                "ordinaryArithmetic",
                9,
            );
            let environment = fln_elab::implemented_by::register(
                ordinary.environment(),
                &name("ordinaryArithmetic"),
                &name(operation),
            )
            .unwrap();
            let expected = if operation == "Nat.div" { "4" } else { "3" };
            let row = format!("extern:{operation}");
            execute_and_replay(
                &environment,
                r#"
theorem logicalSource : ordinaryArithmetic 43 10 = 9 := rfl
#eval ordinaryArithmetic 43 10
#eval (let calculate := ordinaryArithmetic; calculate 43 10)
"#,
                &[(expected, Some(&row)), (expected, Some(&row))],
            );
        }
    });
}

#[test]
fn missing_foreign_and_exhausted_division_contracts_never_grant_native_authority() {
    with_fixture(|fixture| {
        for operation in ["Nat.div", "Nat.mod"] {
            let root = name(operation);
            assert!(!selected(&rebuild(fixture, None, Some(&root)), operation).unwrap());
            assert!(!selected(&rebuild(fixture, Some(&root), None), operation).unwrap());
            let helper = if operation == "Nat.div" {
                "Nat.div.go"
            } else {
                "Nat.modCore"
            };
            for missing in [helper, "Nat.rec", "Nat.div_rec_fuel_lemma"] {
                assert!(
                    matches!(
                        selected(&rebuild(fixture, Some(&name(missing)), None), operation),
                        Err(IngressError::UnsupportedNode { .. })
                    ),
                    "{operation} missing {missing}"
                );
            }
            for label in [operation, "Nat.sub"] {
                for entry in [
                    ExternEntry::Opaque,
                    ExternEntry::Standard {
                        backend: name("all"),
                        symbol: "foreign_division_contract".to_owned(),
                    },
                ] {
                    let changed =
                        externs::register(&fixture.environment, &name(label), vec![entry]).unwrap();
                    assert!(
                        matches!(
                            selected(&changed, operation),
                            Err(IngressError::UnsupportedNode { .. })
                        ),
                        "{operation} foreign {label}"
                    );
                }
            }
            let mut consumed = 0;
            assert!(
                matches(
                    &fixture.environment,
                    &root,
                    &mut None,
                    &mut consumed,
                    IngressLimits::default()
                )
                .unwrap()
            );
            assert!(consumed > rows(operation).len());
            let error = matches(
                &fixture.environment,
                &root,
                &mut None,
                &mut 0,
                IngressLimits {
                    max_nodes: consumed - 1,
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
            assert!(selected(&fixture.environment, operation).unwrap());
        }
        assert!(!selected(&Environment::new(), "Nat.div").unwrap());
        assert!(
            !selected(&fixture.environment, "Nat.modCore").unwrap(),
            "this feature selects only the two public source operations"
        );
    });
}
