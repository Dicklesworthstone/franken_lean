//! Actual pinned comparison data, not admission of an imported module closure.
//! Source examples and altered definitions still cross both ordinary checkers;
//! the full Bootstrap integration target separately admits the library itself.

use super::*;
use fln_comp::flbc::{self, ArgumentOwnership, Instruction, ResultOwnership};
use fln_elab::externs::{self, ExternEntry};
use fln_olean::source_extensions as metadata;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::path::PathBuf;
use std::sync::OnceLock;

const STACK: usize = 256 * 1024 * 1024;

struct Fixture {
    environment: Environment,
    prelude: Environment,
    externs: BTreeMap<Name, Vec<ExternEntry>>,
}

fn fixture() -> Option<&'static Fixture> {
    static FIXTURE: OnceLock<Option<Fixture>> = OnceLock::new();
    FIXTURE
        .get_or_init(|| {
            let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from) else {
                assert!(
                    std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                    "the actual pinned Reference library is required"
                );
                eprintln!("SKIP: pinned Reference lib/lean is absent");
                return None;
            };
            let mut constants = BTreeMap::new();
            let mut actual_externs = BTreeMap::new();
            let mut prelude_names = BTreeSet::new();
            let mut prelude_externs = BTreeMap::new();
            for module in ["Init/Prelude", "Init/Core", "Init/Data/String/Bootstrap"] {
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
                    OleanDecodeLimits::new(STACK),
                )
                .unwrap();
                let view = if decoded.module.is_module {
                    fln_olean::region::OleanView::parse_with_dependencies(
                        &parts[2],
                        &[&parts[0], &parts[1]],
                    )
                } else {
                    fln_olean::region::OleanView::parse(&parts[0])
                }
                .unwrap();
                let blocks: Vec<_> = view
                    .extension_payloads(OleanWalkBudget::default(), STACK)
                    .unwrap()
                    .into_iter()
                    .filter(|block| block.name == name(metadata::EXTERN_EXTENSION))
                    .collect();
                for row in metadata::decode(&blocks, metadata::DecodeLimits::default())
                    .unwrap()
                    .externs
                {
                    let entries = row
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
                        .collect::<Vec<_>>();
                    if let Some(previous) = actual_externs.insert(row.declaration, entries.clone())
                    {
                        assert_eq!(previous, entries);
                    }
                }
                if module == "Init/Prelude" {
                    prelude_externs = actual_externs.clone();
                    prelude_names.extend(decoded.constants.iter().map(|info| info.name().clone()));
                }
                for info in decoded.constants {
                    if let Some(previous) = constants.insert(info.name().clone(), info.clone()) {
                        assert_eq!(
                            previous, info,
                            "actual declarations are not selected to fit the inventory"
                        );
                    }
                }
            }
            let mut environment = Environment::new();
            for info in constants.into_values() {
                environment = environment.add_decl(info).unwrap();
            }
            for (label, entries) in &actual_externs {
                environment = externs::register(&environment, label, entries.clone()).unwrap();
            }
            let mut prelude = Environment::new();
            for label in prelude_names {
                prelude = prelude
                    .with_entry(environment.entry(&label).unwrap())
                    .unwrap();
            }
            for (label, entries) in prelude_externs {
                prelude = externs::register(&prelude, &label, entries).unwrap();
            }
            Some(Fixture {
                environment,
                prelude,
                externs: actual_externs,
            })
        })
        .as_ref()
}

fn with_fixture(test: impl FnOnce(&Fixture) + Send + 'static) {
    std::thread::Builder::new()
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

fn inventory(operation: Operation) -> BTreeMap<Name, &'static str> {
    let mut rows = BTreeMap::new();
    for line in DEPENDENCIES.lines() {
        let (mask, encoded, digest) = inventory_row(line);
        assert_ne!(mask, 0);
        if mask & operation.mask() != 0 {
            let label = dependency_name(encoded, &mut 0, IngressLimits::default()).unwrap();
            assert!(rows.insert(label, digest).is_none());
        }
    }
    rows
}

/// Recompute the complete graph independently of the frozen membership table.
fn actual_dependencies(environment: &Environment, operation: Operation) -> BTreeSet<Name> {
    actual_dependencies_from(
        environment,
        operation.source_name(),
        operation.uses_character(),
    )
}

fn actual_dependencies_from(
    environment: &Environment,
    root: Name,
    character: bool,
) -> BTreeSet<Name> {
    let mut pending = vec![root];
    if character {
        pending.push(name("Bool"));
    }
    let mut found = BTreeSet::new();
    let mut seen_expressions = HashSet::new();
    while let Some(label) = pending.pop() {
        if !found.insert(label.clone()) {
            continue;
        }
        assert!(found.len() <= 10_000);
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
            if !seen_expressions.insert(expression.clone()) {
                continue;
            }
            assert!(seen_expressions.len() <= 1_000_000);
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

fn matches(environment: &Environment, operation: Operation) -> Result<bool, IngressError> {
    contract_matches(
        environment,
        operation,
        &mut VerifiedDependencies::default(),
        &mut None,
        &mut 0,
        IngressLimits::default(),
    )
}

fn rebuild(fixture: &Fixture, omit: Option<&Name>, omit_extern: Option<&Name>) -> Environment {
    let mut environment = Environment::new();
    for (label, _) in fixture.environment.constants() {
        if omit != Some(label) {
            environment = environment
                .with_entry(fixture.environment.entry(label).unwrap())
                .unwrap();
        }
    }
    for (label, entries) in &fixture.externs {
        if omit != Some(label) && omit_extern != Some(label) {
            environment = externs::register(&environment, label, entries.clone()).unwrap();
        }
    }
    environment
}

#[test]
fn actual_string_inventories_close_the_pin_and_share_only_successful_checks() {
    with_fixture(|fixture| {
        assert_eq!(DEPENDENCIES.lines().count(), DEPENDENCY_COUNT);
        let mut verified = VerifiedDependencies::default();
        let mut externs = None;
        let mut work = 0;
        for (operation, count) in Operation::ALL
            .into_iter()
            .zip([325, 325, 325, 326, 325, 323, 323, 324])
        {
            let rows = inventory(operation);
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
            assert!(fixture.externs.contains_key(&operation.source_name()));
            assert!(
                contract_matches(
                    &fixture.environment,
                    operation,
                    &mut verified,
                    &mut externs,
                    &mut work,
                    IngressLimits::default()
                )
                .unwrap()
            );
        }
        assert!(verified.0.into_iter().all(|checked| checked));
        let mut fresh_work = 0;
        let mut fresh_externs = None;
        for operation in Operation::ALL {
            assert!(
                contract_matches(
                    &fixture.environment,
                    operation,
                    &mut VerifiedDependencies::default(),
                    &mut fresh_externs,
                    &mut fresh_work,
                    IngressLimits::default()
                )
                .unwrap()
            );
        }
        assert!(
            work < fresh_work,
            "shared dependencies are verified once, with every occurrence still charged"
        );
        assert!(matches(&fixture.environment, Operation::ByteSize).unwrap());
        assert!(
            Operation::from_name(&Name::str(Name::anonymous(), "String.Internal.posOf")).is_none()
        );
    });
}

#[test]
fn exact_char_and_position_adapters_execute_checked_source_and_replay_bytecode() {
    with_fixture(|fixture| {
        let engine = Engine::from_environment(fixture.environment.clone());
        let options = KVMap::new();
        let root = engine.logical_root(&options);
        let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
        let source = r#"
def seek : String → Char → String.Pos.Raw := String.Internal.posOf
def advance (s : String) (p : String.Pos.Raw) : String.Pos.Raw := String.Internal.next s p
#eval String.utf8ByteSize "é😀a"
#eval String.Pos.Raw.byteIdx (seek "aλ😀z" '😀')
#eval String.Internal.offsetOfPos "aλ😀z" (seek "aλ😀z" '😀')
#eval String.Pos.Raw.byteIdx (String.Internal.posOf "aλ😀z" 'x')
#eval String.Internal.offsetOfPos "L∃∀N" (String.Pos.Raw.mk 2)
#eval String.Internal.offsetOfPos "L∃∀N" (String.Pos.Raw.mk 50)
#eval String.Internal.extract "aλ😀z" (String.Pos.Raw.mk 1) (String.Pos.Raw.mk 7)
#eval String.Pos.Raw.byteIdx (advance "aλ😀z" (String.Pos.Raw.mk 1))
#eval String.Internal.pushn "x" 'λ' 3
#eval let find := String.Internal.posOf "aλ😀z"; String.Pos.Raw.byteIdx (find 'λ')
#eval let clip := String.Internal.extract "aλ😀z" (String.Pos.Raw.mk 1); clip (String.Pos.Raw.mk 3)
#eval let pad := String.Internal.pushn "pre" '😀'; pad 2
#eval String.Pos.Raw.byteIdx (String.Internal.posOf "λ\x00z" '\x00')
#eval String.Internal.pushn "unchanged" 'λ' 0
#eval String.Internal.foldl String.push "pre" "λ😀"
#eval if String.Internal.isEmpty "" then 42 else 0
"#;
        let run = || {
            engine
                .execute_source_commands_with_checks(source.as_bytes(), &options, limits)
                .unwrap_or_else(|error| panic!("checked native String adapters: {error:?}"))
                .into_complete()
                .unwrap()
        };
        let expected = [
            ClosedVmValue::Scalar(7),
            ClosedVmValue::Scalar(3),
            ClosedVmValue::Scalar(2),
            ClosedVmValue::Scalar(8),
            ClosedVmValue::Scalar(2),
            ClosedVmValue::Scalar(4),
            ClosedVmValue::String("λ😀".to_owned()),
            ClosedVmValue::Scalar(3),
            ClosedVmValue::String("xλλλ".to_owned()),
            ClosedVmValue::Scalar(1),
            ClosedVmValue::String("λ".to_owned()),
            ClosedVmValue::String("pre😀😀".to_owned()),
            ClosedVmValue::Scalar(2),
            ClosedVmValue::String("unchanged".to_owned()),
            ClosedVmValue::String("preλ😀".to_owned()),
            ClosedVmValue::Scalar(42),
        ];
        let first = run();
        let indices = &first.batch.source_evaluation_indices;
        assert_eq!(indices.len(), expected.len());
        let mut selected = BTreeSet::new();
        for (&index, expected) in indices.iter().zip(&expected) {
            let execution = &first.batch.executions[index];
            assert_eq!(
                execution.checker.ground,
                CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
            );
            assert_eq!(
                closed_vm_value(&execution.exit).unwrap().as_ref(),
                Some(expected)
            );
            let program =
                flbc::decode_canonical(&execution.flbc_artifact, flbc::CodecLimits::default())
                    .unwrap();
            assert_eq!(
                flbc::encode_canonical(&program, flbc::CodecLimits::default()).unwrap(),
                execution.flbc_artifact
            );
            for instruction in program
                .functions()
                .iter()
                .flat_map(|function| &function.code)
            {
                if let Instruction::Intrinsic {
                    row,
                    argument_ownership,
                    result_ownership,
                    ..
                } = instruction
                    && Operation::ALL
                        .iter()
                        .any(|operation| *row == format!("extern:{}", operation.label()))
                {
                    assert!(
                        argument_ownership
                            .iter()
                            .all(|ownership| *ownership == ArgumentOwnership::Borrowed)
                    );
                    assert_eq!(*result_ownership, ResultOwnership::Owned);
                    selected.insert(row.clone());
                }
            }
            let replay =
                execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
                    .unwrap()
                    .into_complete()
                    .unwrap();
            assert_eq!(closed_vm_value(&replay).unwrap().as_ref(), Some(expected));
        }
        assert_eq!(
            selected,
            Operation::ALL
                .map(|operation| format!("extern:{}", operation.label()))
                .into_iter()
                .collect()
        );
        let repeated = run();
        for &index in indices {
            assert_eq!(
                first.batch.executions[index].flbc_artifact,
                repeated.batch.executions[index].flbc_artifact
            );
        }
        assert_eq!(engine.logical_root(&options), root);
    });
}

#[test]
fn folded_source_callbacks_capture_strings_partially_apply_and_replay_unicode() {
    with_fixture(|fixture| {
        let engine = Engine::from_environment(fixture.environment.clone());
        let options = KVMap::new();
        let original_root = engine.logical_root(&options);
        let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
        let source = r#"
#eval String.Internal.foldl String.push "" "Aλ😀é\x00"
#eval String.Internal.foldl (fun acc c => String.push (String.push acc c) c) "" "λ😀"
#eval let suffix := "!"; String.Internal.foldl (fun acc c => String.Internal.append (String.push acc c) suffix) "pre" "aλ"
#eval let fold := String.Internal.foldl; fold String.push "pre" "λ😀"
#eval let fold := String.Internal.foldl String.push "pre"; fold "λ😀"
#eval String.Internal.foldl (fun acc c => String.push acc c) "initial" ""
#eval let isEmpty := String.Internal.isEmpty; if isEmpty "" then 42 else 0
#eval let isEmpty := String.Internal.isEmpty; if isEmpty "\x00" then 0 else 42
#eval if String.Internal.isEmpty "λ😀" then 0 else 42
"#;
        let expected = [
            ClosedVmValue::String("Aλ😀é\0".to_owned()),
            ClosedVmValue::String("λλ😀😀".to_owned()),
            ClosedVmValue::String("prea!λ!".to_owned()),
            ClosedVmValue::String("preλ😀".to_owned()),
            ClosedVmValue::String("preλ😀".to_owned()),
            ClosedVmValue::String("initial".to_owned()),
            ClosedVmValue::Scalar(42),
            ClosedVmValue::Scalar(42),
            ClosedVmValue::Scalar(42),
        ];
        let execute = || {
            engine
                .execute_source_commands_with_checks(source.as_bytes(), &options, limits)
                .unwrap_or_else(|error| panic!("captured/partial native String fold: {error:?}"))
                .into_complete()
                .unwrap()
        };
        let first = execute();
        assert_eq!(first.batch.source_evaluation_indices.len(), expected.len());
        for (&index, expected) in first.batch.source_evaluation_indices.iter().zip(&expected) {
            let execution = &first.batch.executions[index];
            assert_eq!(
                execution.checker.ground,
                CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
            );
            assert_eq!(
                closed_vm_value(&execution.exit).unwrap().as_ref(),
                Some(expected)
            );
            let decoded =
                flbc::decode_canonical(&execution.flbc_artifact, Default::default()).unwrap();
            assert_eq!(
                flbc::encode_canonical(&decoded, Default::default()).unwrap(),
                execution.flbc_artifact
            );
            let replay =
                execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
                    .unwrap()
                    .into_complete()
                    .unwrap();
            assert_eq!(closed_vm_value(&replay).unwrap().as_ref(), Some(expected));
        }
        let retry = execute();
        for &index in &first.batch.source_evaluation_indices {
            assert_eq!(
                first.batch.executions[index].flbc_artifact,
                retry.batch.executions[index].flbc_artifact
            );
        }
        assert_eq!(engine.logical_root(&options), original_root);
    });
}

#[test]
fn empty_source_fold_keeps_all_three_strict_operands_without_calling_the_callback() {
    with_fixture(|fixture| {
        let engine = Engine::from_environment(fixture.environment.clone());
        let options = KVMap::new();
        let original_root = engine.logical_root(&options);
        let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
        let source = |callback_cost: u64, initial_cost: u64, input_cost: u64, body_cost: u64| {
            format!(
                "def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1\n\
                 #eval String.Internal.foldl \
                 (let prepared : Nat := spend {callback_cost}; fun acc c => let visited : Nat := spend {body_cost}; String.push acc c) \
                 (let prepared : Nat := spend {initial_cost}; \"base\") \
                 (let prepared : Nat := spend {input_cost}; \"\")\n"
            )
        };
        let execute = |costs: [u64; 4]| {
            let source = source(costs[0], costs[1], costs[2], costs[3]);
            let complete = engine
                .execute_source_commands_with_checks(source.as_bytes(), &options, limits)
                .unwrap_or_else(|error| panic!("strict native String fold {costs:?}: {error:?}"))
                .into_complete()
                .unwrap();
            let index = *complete.batch.source_evaluation_indices.last().unwrap();
            let execution = &complete.batch.executions[index];
            assert_eq!(
                execution.checker.ground,
                CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
            );
            assert_eq!(
                closed_vm_value(&execution.exit).unwrap(),
                Some(ClosedVmValue::String("base".to_owned()))
            );
            let VmExit::Returned(result) = &execution.exit else {
                panic!("the empty fold must return its initialized String");
            };
            let replay =
                execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
                    .unwrap()
                    .into_complete()
                    .unwrap();
            assert_eq!(
                closed_vm_value(&replay).unwrap(),
                Some(ClosedVmValue::String("base".to_owned()))
            );
            result.usage.steps
        };
        let idle = execute([0, 0, 0, 0]);
        assert_eq!(
            execute([0, 0, 0, 30]),
            idle,
            "an empty input never executes the callback body"
        );
        for costs in [[30, 0, 0, 0], [0, 30, 0, 0], [0, 0, 30, 0]] {
            let busy = execute(costs);
            assert!(
                busy > idle + 30,
                "strict source operand disappeared: {costs:?}, {idle} vs {busy}"
            );
            let mut bounded = limits;
            bounded.vm.max_steps = idle;
            let source = source(costs[0], costs[1], costs[2], costs[3]);
            assert!(matches!(
                engine
                    .execute_source_commands_with_checks(source.as_bytes(), &options, bounded)
                    .unwrap(),
                Outcome::Inconclusive(_)
            ));
        }
        assert_eq!(engine.logical_root(&options), original_root);
    });
}

#[test]
fn missing_foreign_and_changed_dependencies_never_acquire_native_authority() {
    with_fixture(|fixture| {
        for operation in Operation::ALL {
            let requested = operation.source_name();
            let missing = rebuild(fixture, None, Some(&requested));
            assert!(!matches(&missing, operation).unwrap());
            let changed = externs::register(
                &fixture.environment,
                &requested,
                vec![ExternEntry::Standard {
                    backend: name("all"),
                    symbol: "foreign_string_operation".to_owned(),
                }],
            )
            .unwrap();
            assert!(matches(&changed, operation).is_err());
            for target in [
                requested.clone(),
                name("String.ofByteArray"),
                name("Nat.succ"),
            ] {
                let result = matches(&rebuild(fixture, Some(&target), None), operation);
                if target == requested {
                    assert!(
                        !result.unwrap(),
                        "removing the root also removes its required extern"
                    );
                } else {
                    assert!(
                        result.is_err(),
                        "{} omitted {}",
                        operation.label(),
                        target.to_display_string()
                    );
                }
            }
        }
        for target in [
            "Char.mk",
            "UInt32.ofBitVec",
            "BitVec.ofFin",
            "Fin.mk",
            "String.Pos.Raw.mk",
        ] {
            let target = name(target);
            let mut altered = fixture.environment.find(&target).unwrap().clone();
            let ConstantInfo::Ctor(value) = &mut altered else {
                unreachable!()
            };
            value.num_fields += 1;
            let changed = rebuild(fixture, Some(&target), None)
                .add_decl(altered)
                .unwrap();
            assert!(matches(&changed, Operation::PosOf).is_err());
        }
        let foreign_helper = externs::register(
            &fixture.environment,
            &name("String.toByteArray"),
            vec![ExternEntry::Opaque],
        )
        .unwrap();
        assert!(matches(&foreign_helper, Operation::ByteSize).is_err());
        assert!(matches(&fixture.environment, Operation::PosOf).unwrap());
    });
}

#[test]
fn imported_byte_size_executes_with_the_actual_prelude_alone() {
    with_fixture(|fixture| {
        for operation in Operation::ALL.into_iter().skip(1) {
            assert!(!fixture.prelude.contains(&operation.source_name()));
        }
        assert!(matches(&fixture.prelude, Operation::ByteSize).unwrap());
        let engine = Engine::from_environment(fixture.prelude.clone());
        let options = KVMap::new();
        let root = engine.logical_root(&options);
        let source = "#eval let bytes := String.utf8ByteSize; bytes \"é😀a\"";
        let run = engine
            .execute_source_commands_with_checks(
                source.as_bytes(),
                &options,
                EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        let execution = &run.batch.executions[run.batch.source_evaluation_indices[0]];
        assert_eq!(
            closed_vm_value(&execution.exit).unwrap(),
            Some(ClosedVmValue::Scalar(7))
        );
        let replay = execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(
            closed_vm_value(&replay).unwrap(),
            Some(ClosedVmValue::Scalar(7))
        );
        assert_eq!(engine.logical_root(&options), root);
    });
}

#[test]
fn existing_byte_size_seed_keeps_its_valid_and_foreign_extern_behavior() {
    let options = KVMap::new();
    let base = Engine::builder()
        .build_with_source_seed(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)))
        .unwrap()
        .into_complete()
        .unwrap();
    let requested = Operation::ByteSize.source_name();
    assert!(source_intrinsic_binding(base.environment(), &requested).is_some());
    for symbol in ["lean_string_utf8_byte_size", "foreign_byte_size"] {
        let engine = Engine::from_environment(
            externs::register(
                base.environment(),
                &requested,
                vec![ExternEntry::Standard {
                    backend: name("all"),
                    symbol: symbol.to_owned(),
                }],
            )
            .unwrap(),
        );
        let result = engine.execute_source_commands_with_checks(
            b"#eval String.utf8ByteSize \"abcdefg\"",
            &options,
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        );
        if symbol == "foreign_byte_size" {
            assert!(result.is_err());
        } else {
            let result = result.unwrap().into_complete().unwrap();
            assert_eq!(
                closed_vm_value(
                    &result.batch.executions[result.batch.source_evaluation_indices[0]].exit
                )
                .unwrap(),
                Some(ClosedVmValue::Scalar(7))
            );
        }
    }
}

#[test]
fn every_operation_remains_bounded_with_clean_retry() {
    with_fixture(|fixture| {
        for operation in Operation::ALL {
            let mut work = 0;
            assert!(
                contract_matches(
                    &fixture.environment,
                    operation,
                    &mut VerifiedDependencies::default(),
                    &mut None,
                    &mut work,
                    IngressLimits::default()
                )
                .unwrap()
            );
            assert!(work > 0);
            assert!(matches!(
                contract_matches(
                    &fixture.environment,
                    operation,
                    &mut VerifiedDependencies::default(),
                    &mut None,
                    &mut 0,
                    IngressLimits {
                        max_nodes: work - 1,
                        ..IngressLimits::default()
                    }
                ),
                Err(IngressError::ResourceLimit { .. })
            ));
            assert!(matches(&fixture.environment, operation).unwrap());
        }
    });
}

fn changed_body(operation: Operation, info: ConstantInfo) -> Declaration {
    let c = |label| Expr::const_(name(label), vec![]);
    let answer = Expr::lit(Literal::Nat(NatLit::from_u64(42)));
    let mut body = match operation.result() {
        Domain::Nat => answer,
        Domain::String => Expr::lit(Literal::Str("counterfeit".to_owned())),
        Domain::Position => Expr::app(c("String.Pos.Raw.mk"), answer),
        Domain::Bool => c("Bool.true"),
        _ => unreachable!(),
    };
    for domain in operation.domains().iter().rev() {
        body = Expr::lam(
            Name::anonymous(),
            domain.source_type(),
            body,
            BinderInfo::Default,
        );
    }
    match info {
        ConstantInfo::Defn(mut value) => {
            value.value = body;
            Declaration::Defn(value)
        }
        ConstantInfo::Opaque(mut value) => {
            value.value = body;
            Declaration::Opaque(value)
        }
        _ => unreachable!(),
    }
}

#[test]
fn well_typed_counterfeit_bodies_and_reserved_native_names_are_refused() {
    with_fixture(|fixture| {
        let options = KVMap::new();
        let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
        for operation in Operation::ALL {
            let requested = operation.source_name();
            let original = fixture.environment.find(&requested).unwrap().clone();
            let changed = Engine::from_environment(rebuild(fixture, Some(&requested), None))
                .admit_declaration(
                    changed_body(operation, original),
                    &options,
                    EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)),
                )
                .expect("the changed implementation remains well typed")
                .into_complete()
                .unwrap()
                .engine;
            let changed = Engine::from_environment(
                externs::register(
                    changed.environment(),
                    &requested,
                    fixture.externs[&requested].clone(),
                )
                .unwrap(),
            );
            assert!(matches(changed.environment(), operation).is_err());
            let root = changed.logical_root(&options);
            let source = format!("def refusedNative := {}", operation.label());
            assert!(
                changed
                    .execute_source_commands_with_checks(source.as_bytes(), &options, limits)
                    .is_err()
            );
            assert_eq!(changed.logical_root(&options), root);

            let collision = Declaration::Defn(DefinitionVal {
                base: ConstantVal {
                    name: operation.primitive(),
                    level_params: vec![],
                    type_: Expr::const_(name("Nat"), vec![]),
                },
                value: Expr::lit(Literal::Nat(NatLit::from_u64(0))),
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![operation.primitive()],
            });
            let occupied = Engine::from_environment(fixture.environment.clone())
                .admit_declaration(
                    collision,
                    &options,
                    EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)),
                )
                .unwrap()
                .into_complete()
                .unwrap()
                .engine;
            assert!(
                occupied
                    .execute_source_commands_with_checks(source.as_bytes(), &options, limits)
                    .is_err(),
                "a user declaration cannot impersonate the private scalar primitive"
            );
        }
    });
}
