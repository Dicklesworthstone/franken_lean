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

/// Every pinned module that defines a constant of the inventory. The closure
/// walk below refuses any omission, so this list cannot silently narrow it.
const MODULES: [&str; 81] = [
    "Init/ByCases",
    "Init/Classical",
    "Init/Control/Id",
    "Init/Control/Lawful/Basic",
    "Init/Core",
    "Init/Data/Array/Basic",
    "Init/Data/Array/Bootstrap",
    "Init/Data/Array/Extract",
    "Init/Data/Array/Lemmas",
    "Init/Data/Array/Set",
    "Init/Data/BEq",
    "Init/Data/BitVec/Basic",
    "Init/Data/BitVec/BasicAux",
    "Init/Data/BitVec/Bootstrap",
    "Init/Data/BitVec/Lemmas",
    "Init/Data/Bool",
    "Init/Data/ByteArray/Basic",
    "Init/Data/ByteArray/Bootstrap",
    "Init/Data/ByteArray/Lemmas",
    "Init/Data/Cast",
    "Init/Data/Char/Basic",
    "Init/Data/Int/Basic",
    "Init/Data/Int/DivMod/Basic",
    "Init/Data/Int/DivMod/Bootstrap",
    "Init/Data/Int/Lemmas",
    "Init/Data/Int/Order",
    "Init/Data/Int/Pow",
    "Init/Data/List/Basic",
    "Init/Data/List/BasicAux",
    "Init/Data/List/Control",
    "Init/Data/List/Lemmas",
    "Init/Data/List/Nat/TakeDrop",
    "Init/Data/List/Sublist",
    "Init/Data/List/TakeDrop",
    "Init/Data/List/ToArray",
    "Init/Data/Nat/Basic",
    "Init/Data/Nat/Bitwise/Basic",
    "Init/Data/Nat/Bitwise/Lemmas",
    "Init/Data/Nat/Div/Basic",
    "Init/Data/Nat/Div/Lemmas",
    "Init/Data/Nat/Dvd",
    "Init/Data/Nat/Gcd",
    "Init/Data/Nat/Lemmas",
    "Init/Data/Nat/Linear",
    "Init/Data/Nat/MinMax",
    "Init/Data/Nat/Order",
    "Init/Data/NeZero",
    "Init/Data/Option/Basic",
    "Init/Data/Option/Instances",
    "Init/Data/Option/Lemmas",
    "Init/Data/Order/Classes",
    "Init/Data/Order/Factories",
    "Init/Data/Order/Lemmas",
    "Init/Data/RArray",
    "Init/Data/Repr",
    "Init/Data/String/Basic",
    "Init/Data/String/Bootstrap",
    "Init/Data/String/Decode",
    "Init/Data/String/Defs",
    "Init/Data/String/Modify",
    "Init/Data/String/PosRaw",
    "Init/Data/ToString/Basic",
    "Init/Data/UInt/Basic",
    "Init/Data/UInt/BasicAux",
    "Init/Data/UInt/Bitwise",
    "Init/Data/UInt/Lemmas",
    "Init/Ext",
    "Init/GetElem",
    "Init/Omega/Coeffs",
    "Init/Omega/Constraint",
    "Init/Omega/Int",
    "Init/Omega/IntList",
    "Init/Omega/LinearCombo",
    "Init/Omega/Logic",
    "Init/Prelude",
    "Init/PropLemmas",
    "Init/SimpLemmas",
    "Init/SizeOf",
    "Init/Tactics",
    "Init/Util",
    "Init/WF",
];

struct Fixture {
    environment: Environment,
    prelude: Environment,
    externs: BTreeMap<Name, Vec<ExternEntry>>,
    /// Every loaded module whose artifacts carry each constant.
    owners: BTreeMap<Name, BTreeSet<&'static str>>,
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
            let mut owners = BTreeMap::new();
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
                    if module == "Init/Prelude" {
                        prelude_externs.insert(row.declaration.clone(), entries.clone());
                    }
                    if let Some(previous) = actual_externs.insert(row.declaration, entries.clone())
                    {
                        assert_eq!(previous, entries);
                    }
                }
                if module == "Init/Prelude" {
                    prelude_names.extend(decoded.constants.iter().map(|info| info.name().clone()));
                }
                for info in decoded.constants {
                    owners
                        .entry(info.name().clone())
                        .or_insert_with(BTreeSet::new)
                        .insert(module);
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
                owners,
            })
        })
        .as_ref()
}

/// The original Prelude and Bootstrap rows, every argument borrowed.
const BOOTSTRAP: [Operation; 8] = [
    Operation::ByteSize,
    Operation::PosOf,
    Operation::OffsetOfPos,
    Operation::Extract,
    Operation::Next,
    Operation::Pushn,
    Operation::Foldl,
    Operation::IsEmpty,
];

const SUBSTRING: [Operation; 11] = [
    Operation::Front,
    Operation::PosMin,
    Operation::PosSub,
    Operation::SubstringToString,
    Operation::SubstringDrop,
    Operation::SubstringFront,
    Operation::SubstringExtract,
    Operation::SubstringBeq,
    Operation::SubstringIsEmpty,
    Operation::SubstringGet,
    Operation::SubstringPrev,
];

/// The ownership the generated census row requires of an FLBC call.
fn generated_ownership(row: &str, arguments: usize) -> (Vec<ArgumentOwnership>, ResultOwnership) {
    use fln_vm::extern_row::{
        ArgumentOwnership as Contract, Ownership, ResultOwnership as ContractResult,
    };
    let generated = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .find(|generated| generated.id == row)
        .unwrap();
    let ownership = Ownership::parse(generated.ownership).unwrap();
    let arguments = ownership
        .argument_ownership(arguments)
        .unwrap()
        .into_iter()
        .map(|ownership| match ownership {
            Contract::Borrowed => ArgumentOwnership::Borrowed,
            Contract::Owned => ArgumentOwnership::Owned,
            Contract::Scalar => ArgumentOwnership::Scalar,
            Contract::Unique => ArgumentOwnership::Unique,
        })
        .collect();
    let result = match ownership.result_ownership().unwrap() {
        ContractResult::Owned => ResultOwnership::Owned,
        ContractResult::Scalar => ResultOwnership::Scalar,
        ContractResult::Borrowed => ResultOwnership::Borrowed,
        ContractResult::RawObject => ResultOwnership::RawObject,
    };
    (arguments, result)
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
        // The Basic-, PosRaw- and Modify-level closures are a different order
        // of magnitude from Bootstrap's, as measured with the pin itself.
        let counts = [
            325, 325, 325, 326, 325, 323, 323, 324, 351, 3413, 3413, 2318, 369, 3416, 3416, 4040,
            3653, 3396, 3413, 3415, 3415, 3416, 3935, 3413, 370, 341, 3396, 349, 17, 18, 328, 328,
            353, 328, 328, 328, 354, 328,
        ];
        assert_eq!(counts.len(), Operation::ALL.len());
        let mut defining = BTreeSet::new();
        for line in DEPENDENCIES.lines() {
            let (_, encoded, _) = inventory_row(line);
            let label = dependency_name(encoded, &mut 0, IngressLimits::default()).unwrap();
            defining.extend(fixture.owners[&label].iter().copied());
        }
        assert_eq!(
            defining,
            MODULES.into_iter().collect(),
            "the fixture loads exactly the modules defining the inventory"
        );
        for (operation, count) in Operation::ALL.into_iter().zip(counts) {
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
            // #eval's auxiliary is unsafe at the pin (BuiltinEvalCommand.lean:92).
            assert_eq!(
                execution.checker.ground,
                CheckerAdmissionGround::UnsafeQuarantine
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
                    assert_eq!(
                        (argument_ownership.clone(), *result_ownership),
                        generated_ownership(row, argument_ownership.len())
                    );
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
            BOOTSTRAP
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

/// The position-indexed rows on "aλ😀z" (a@0, λ@1, 😀@3, z@7, size 8): a
/// multi-byte character, a position inside one, the end, and partial use.
/// Each expected value is the pinned v4.32.0 runtime's own answer. A proof
/// is a logical argument the native row never receives, so one axiom supplies
/// every hypothesis; evaluation never inspects it.
#[test]
fn positioned_adapters_execute_checked_source_and_replay_bytecode() {
    with_fixture(|fixture| {
        let engine = Engine::from_environment(fixture.environment.clone());
        let options = KVMap::new();
        let root = engine.logical_root(&options);
        let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
        let source = r#"
axiom proof {p : Prop} : p
#eval (String.Pos.Raw.get "aλ😀z" (String.Pos.Raw.mk 1)).toNat
#eval (String.Pos.Raw.get "aλ😀z" (String.Pos.Raw.mk 2)).toNat
#eval (String.Pos.Raw.get "aλ😀z" (String.Pos.Raw.mk 8)).toNat
#eval (String.Internal.get "aλ😀z" (String.Pos.Raw.mk 3)).toNat
#eval String.Pos.Raw.set "aλ😀z" (String.Pos.Raw.mk 3) 'é'
#eval String.Pos.Raw.set "aλ😀z" (String.Pos.Raw.mk 2) 'X'
#eval String.Pos.Raw.set "aλ😀z" (String.Pos.Raw.mk 8) 'X'
#eval (String.decodeChar "aλ😀z" 3 proof).toNat
#eval (String.decodeChar "aλ😀z" 8 proof).toNat
#eval (String.getUTF8Byte "aλ😀z" (String.Pos.Raw.mk 1) proof).toNat
#eval (String.Pos.Raw.next' "aλ😀z" (String.Pos.Raw.mk 3) proof).byteIdx
#eval (String.Pos.Raw.next' "aλ😀z" (String.Pos.Raw.mk 4) proof).byteIdx
#eval String.Pos.Raw.extract "aλ😀z" (String.Pos.Raw.mk 1) (String.Pos.Raw.mk 7)
#eval @String.Pos.set "aλ😀z" (String.Pos.mk (String.Pos.Raw.mk 1) proof) 'X' proof
#eval @String.extract "aλ😀z" (String.Pos.mk (String.Pos.Raw.mk 1) proof) (String.Pos.mk (String.Pos.Raw.mk 7) proof)
#eval (String.toList "aλ😀z").length
#eval (String.toList "").length
#eval String.Internal.foldl String.push "" (String.ofList (String.toList "aλ😀z"))
#eval let get := String.Pos.Raw.get "aλ😀z"; (get (String.Pos.Raw.mk 7)).toNat
#eval let set := String.Pos.Raw.set; set "abc" (String.Pos.Raw.mk 1) 'B'
#eval (String.get "aλ😀z" (String.Pos.Raw.mk 3)).toNat
#eval (String.get' "aλ😀z" (String.Pos.Raw.mk 1) proof).toNat
#eval (String.Pos.Raw.get' "aλ😀z" (String.Pos.Raw.mk 7) proof).toNat
#eval (String.next' "aλ😀z" (String.Pos.Raw.mk 1) proof).byteIdx
#eval (@String.Pos.next "aλ😀z" (String.Pos.mk (String.Pos.Raw.mk 3) proof) proof).offset.byteIdx
#eval (@String.Pos.next "aλ😀z" (String.Pos.mk (String.Pos.Raw.mk 4) proof) proof).offset.byteIdx
#eval String.set "aλ😀z" (String.Pos.Raw.mk 1) 'L'
#eval String.set "aλ😀z" (String.Pos.Raw.mk 4) 'L'
#eval (String.getUtf8Byte "aλ😀z" (String.Pos.Raw.mk 3) proof).toNat
#eval (String.Internal.getUTF8Byte "aλ😀z" 2 proof).toNat
#eval (String.data "aλ😀z").length
#eval String.Internal.foldl String.push "" (String.ofList (String.data "aλ😀z"))
#eval let next := @String.Pos.next "aλ😀z"; (next (String.Pos.mk (String.Pos.Raw.mk 0) proof) proof).offset.byteIdx
"#;
        let run = || {
            engine
                .execute_source_commands_with_checks(source.as_bytes(), &options, limits)
                .unwrap_or_else(|error| panic!("checked positioned String adapters: {error:?}"))
                .into_complete()
                .unwrap()
        };
        let text = |value: &str| ClosedVmValue::String(value.to_owned());
        let expected = [
            ClosedVmValue::Scalar(955),
            ClosedVmValue::Scalar(65),
            ClosedVmValue::Scalar(65),
            ClosedVmValue::Scalar(128_512),
            text("aλéz"),
            text("aλ😀z"),
            text("aλ😀z"),
            ClosedVmValue::Scalar(128_512),
            ClosedVmValue::Scalar(0),
            ClosedVmValue::Scalar(206),
            ClosedVmValue::Scalar(7),
            ClosedVmValue::Scalar(5),
            text("λ😀"),
            text("aX😀z"),
            text("λ😀"),
            ClosedVmValue::Scalar(4),
            ClosedVmValue::Scalar(0),
            text("aλ😀z"),
            ClosedVmValue::Scalar(122),
            text("aBc"),
            // The deprecated aliases, each its own declaration and row.
            ClosedVmValue::Scalar(128_512),
            ClosedVmValue::Scalar(955),
            ClosedVmValue::Scalar(122),
            ClosedVmValue::Scalar(3),
            ClosedVmValue::Scalar(7),
            ClosedVmValue::Scalar(5),
            text("aL😀z"),
            text("aλ😀z"),
            ClosedVmValue::Scalar(240),
            ClosedVmValue::Scalar(187),
            ClosedVmValue::Scalar(4),
            text("aλ😀z"),
            ClosedVmValue::Scalar(1),
        ];
        let first = run();
        let indices = &first.batch.source_evaluation_indices;
        assert_eq!(indices.len(), expected.len());
        let mut selected = BTreeSet::new();
        for (&index, expected) in indices.iter().zip(&expected) {
            let execution = &first.batch.executions[index];
            assert_eq!(
                execution.checker.ground,
                CheckerAdmissionGround::UnsafeQuarantine
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
                    // Each operand keeps its own row's disposition: `set`'s
                    // String is owned and its Char a `value`; `get` returns one.
                    assert_eq!(
                        (argument_ownership.clone(), *result_ownership),
                        generated_ownership(row, argument_ownership.len()),
                        "{row}"
                    );
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
                .into_iter()
                .filter(|operation| {
                    !BOOTSTRAP.contains(operation) && !SUBSTRING.contains(operation)
                })
                .map(|operation| format!("extern:{}", operation.label()))
                .chain(["extern:String.Internal.foldl".to_owned()])
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

        // Past the terminator the pin's fast reads are undefined behavior.
        // Here they stop with a typed range refusal, never a guessed value.
        for call in [
            "(String.decodeChar \"aλ😀z\" 9 proof).toNat",
            "(String.getUTF8Byte \"aλ😀z\" (String.Pos.Raw.mk 9) proof).toNat",
            "(String.Pos.Raw.next' \"aλ😀z\" (String.Pos.Raw.mk 9) proof).byteIdx",
            "(String.get' \"aλ😀z\" (String.Pos.Raw.mk 9) proof).toNat",
            "(String.Pos.Raw.get' \"aλ😀z\" (String.Pos.Raw.mk 9) proof).toNat",
            "(String.next' \"aλ😀z\" (String.Pos.Raw.mk 9) proof).byteIdx",
            "(@String.Pos.next \"aλ😀z\" (String.Pos.mk (String.Pos.Raw.mk 9) proof) proof).offset.byteIdx",
            "(String.getUtf8Byte \"aλ😀z\" (String.Pos.Raw.mk 9) proof).toNat",
            "(String.Internal.getUTF8Byte \"aλ😀z\" 9 proof).toNat",
        ] {
            let source = format!("axiom proof {{p : Prop}} : p\n#eval {call}\n");
            let complete = engine
                .execute_source_commands_with_checks(source.as_bytes(), &options, limits)
                .unwrap()
                .into_complete()
                .unwrap();
            let execution = &complete.batch.executions[complete.batch.source_evaluation_indices[0]];
            assert!(
                matches!(
                    &execution.exit,
                    VmExit::Refused {
                        refusal: fln_vm::interpreter::VmRefusal::ArrayIndexOutOfBounds {
                            index: 9,
                            size: 9
                        },
                        ..
                    }
                ),
                "{call}: {:?}",
                execution.exit
            );
        }
    });
}

/// These answers follow the pinned exported Lean helpers, including the
/// surprising empty-slice front, invalid byte positions, and reads beyond the
/// slice stop. Source records keep Pos.Raw fields; only the private native
/// record has plain Nat offsets.
#[test]
fn substring_adapters_preserve_unicode_bounds_partial_calls_and_replay() {
    with_fixture(|fixture| {
        let engine = Engine::from_environment(fixture.environment.clone());
        let options = KVMap::new();
        let root = engine.logical_root(&options);
        let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
        let source = r#"
def middle : Substring.Raw := Substring.Raw.mk "aλ😀z" (String.Pos.Raw.mk 1) (String.Pos.Raw.mk 7)
def first : Substring.Raw := Substring.Raw.mk "aλ😀z" (String.Pos.Raw.mk 1) (String.Pos.Raw.mk 3)
def empty : Substring.Raw := Substring.Raw.mk "aλ😀z" (String.Pos.Raw.mk 3) (String.Pos.Raw.mk 3)
def badStart : Substring.Raw := Substring.Raw.mk "aλ😀z" (String.Pos.Raw.mk 2) (String.Pos.Raw.mk 7)
def badStop : Substring.Raw := Substring.Raw.mk "aλ😀z" (String.Pos.Raw.mk 1) (String.Pos.Raw.mk 4)
#eval (String.Internal.front "λ😀").toNat
#eval (String.Internal.front "").toNat
#eval (String.Internal.front "\x00z").toNat
#eval (String.Pos.Raw.Internal.min (String.Pos.Raw.mk 8) (String.Pos.Raw.mk 3)).byteIdx
#eval (String.Pos.Raw.Internal.min (String.Pos.Raw.mk 3000000000000000000000000000000) (String.Pos.Raw.mk 3)).byteIdx
#eval (String.Pos.Raw.Internal.sub (String.Pos.Raw.mk 8) (String.Pos.Raw.mk 3)).byteIdx
#eval (String.Pos.Raw.Internal.sub (String.Pos.Raw.mk 3) (String.Pos.Raw.mk 8)).byteIdx
#eval Substring.Raw.Internal.toString middle
#eval Substring.Raw.Internal.toString badStart
#eval Substring.Raw.Internal.toString badStop
#eval Substring.Raw.Internal.toString (Substring.Raw.mk "aλ😀z" (String.Pos.Raw.mk 7) (String.Pos.Raw.mk 1))
#eval Substring.Raw.Internal.toString (Substring.Raw.mk "aλ😀z" (String.Pos.Raw.mk 99) (String.Pos.Raw.mk 100))
#eval Substring.Raw.Internal.toString (Substring.Raw.Internal.drop middle 0)
#eval Substring.Raw.Internal.toString (Substring.Raw.Internal.drop middle 1)
#eval Substring.Raw.Internal.toString (Substring.Raw.Internal.drop middle 100)
#eval (Substring.Raw.Internal.drop middle 1).startPos.byteIdx
#eval (Substring.Raw.Internal.drop middle 1).stopPos.byteIdx
#eval (Substring.Raw.Internal.drop middle 1).str
#eval (Substring.Raw.Internal.front middle).toNat
#eval (Substring.Raw.Internal.front empty).toNat
#eval (Substring.Raw.Internal.front badStart).toNat
#eval Substring.Raw.Internal.toString (Substring.Raw.Internal.extract middle (String.Pos.Raw.mk 2) (String.Pos.Raw.mk 6))
#eval (Substring.Raw.Internal.extract middle (String.Pos.Raw.mk 4) (String.Pos.Raw.mk 2)).str
#eval Substring.Raw.Internal.toString (Substring.Raw.Internal.extract middle (String.Pos.Raw.mk 0) (String.Pos.Raw.mk 99))
#eval if Substring.Raw.Internal.beq middle (Substring.Raw.mk "λ😀" (String.Pos.Raw.mk 0) (String.Pos.Raw.mk 6)) then 42 else 0
#eval if Substring.Raw.Internal.beq badStart empty then 42 else 0
#eval if Substring.Raw.Internal.beq middle first then 0 else 42
#eval if Substring.Raw.Internal.isEmpty middle then 0 else 42
#eval if Substring.Raw.Internal.isEmpty empty then 42 else 0
#eval if Substring.Raw.Internal.isEmpty (Substring.Raw.mk "aλ😀z" (String.Pos.Raw.mk 7) (String.Pos.Raw.mk 1)) then 42 else 0
#eval (Substring.Raw.Internal.get first (String.Pos.Raw.mk 0)).toNat
#eval (Substring.Raw.Internal.get first (String.Pos.Raw.mk 1)).toNat
#eval (Substring.Raw.Internal.get first (String.Pos.Raw.mk 2)).toNat
#eval (Substring.Raw.Internal.get first (String.Pos.Raw.mk 6)).toNat
#eval (Substring.Raw.Internal.get first (String.Pos.Raw.mk 99)).toNat
#eval (Substring.Raw.Internal.prev middle (String.Pos.Raw.mk 0)).byteIdx
#eval (Substring.Raw.Internal.prev middle (String.Pos.Raw.mk 6)).byteIdx
#eval (Substring.Raw.Internal.prev middle (String.Pos.Raw.mk 7)).byteIdx
#eval (Substring.Raw.Internal.prev middle (String.Pos.Raw.mk 99)).byteIdx
#eval let drop := Substring.Raw.Internal.drop middle; Substring.Raw.Internal.toString (drop 1)
#eval let extract := Substring.Raw.Internal.extract middle (String.Pos.Raw.mk 2); Substring.Raw.Internal.toString (extract (String.Pos.Raw.mk 6))
#eval let get := Substring.Raw.Internal.get first; (get (String.Pos.Raw.mk 2)).toNat
#eval let same := Substring.Raw.Internal.beq middle; if same middle then 42 else 0
"#;
        let text = |value: &str| ClosedVmValue::String(value.to_owned());
        let scalar = ClosedVmValue::Scalar;
        let expected = [
            scalar(955),
            scalar(65),
            scalar(0),
            scalar(3),
            scalar(3),
            scalar(5),
            scalar(0),
            text("λ😀"),
            text(""),
            text("λ😀z"),
            text(""),
            text(""),
            text("λ😀"),
            text("😀"),
            text(""),
            scalar(3),
            scalar(7),
            text("aλ😀z"),
            scalar(955),
            scalar(128_512),
            scalar(65),
            text("😀"),
            text(""),
            text("λ😀"),
            scalar(42),
            scalar(42),
            scalar(42),
            scalar(42),
            scalar(42),
            scalar(42),
            scalar(955),
            scalar(65),
            scalar(128_512),
            scalar(122),
            scalar(65),
            scalar(0),
            scalar(2),
            scalar(6),
            scalar(98),
            text("😀"),
            text("😀"),
            scalar(128_512),
            scalar(42),
        ];
        let complete = engine
            .execute_source_commands_with_checks(source.as_bytes(), &options, limits)
            .unwrap_or_else(|error| panic!("checked native Substring adapters: {error:?}"))
            .into_complete()
            .unwrap();
        let indices = &complete.batch.source_evaluation_indices;
        assert_eq!(indices.len(), expected.len());
        let mut selected = BTreeSet::new();
        for (&index, expected) in indices.iter().zip(&expected) {
            let execution = &complete.batch.executions[index];
            assert_eq!(
                execution.checker.ground,
                CheckerAdmissionGround::UnsafeQuarantine
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
                    && SUBSTRING
                        .iter()
                        .any(|operation| *row == format!("extern:{}", operation.label()))
                {
                    assert_eq!(
                        (argument_ownership.clone(), *result_ownership),
                        generated_ownership(row, argument_ownership.len())
                    );
                    assert_eq!(
                        *result_ownership,
                        ResultOwnership::Owned,
                        "Bootstrap helpers box their results"
                    );
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
            SUBSTRING
                .map(|operation| format!("extern:{}", operation.label()))
                .into_iter()
                .collect()
        );
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
                CheckerAdmissionGround::UnsafeQuarantine
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
                CheckerAdmissionGround::UnsafeQuarantine
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
            let position_only = matches!(operation, Operation::PosMin | Operation::PosSub);
            let representation = if position_only {
                // These two rows operate on raw offsets alone. Their exact
                // pin closures bind Pos.Raw's constructor, not any String.
                assert!(
                    matches(
                        &rebuild(fixture, Some(&name("String.ofByteArray")), None),
                        operation
                    )
                    .unwrap(),
                    "raw position arithmetic does not depend on a String representation"
                );
                name("String.Pos.Raw.mk")
            } else {
                name("String.ofByteArray")
            };
            for target in [requested.clone(), representation, name("Nat.succ")] {
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
        Domain::Substring => [
            Expr::lit(Literal::Str("counterfeit".to_owned())),
            Expr::app(c("String.Pos.Raw.mk"), answer.clone()),
            Expr::app(c("String.Pos.Raw.mk"), answer),
        ]
        .into_iter()
        .fold(c("Substring.Raw.mk"), Expr::app),
        Domain::Bool => c("Bool.true"),
        Domain::Char => Expr::app(c("Char.ofNat"), answer),
        Domain::Byte => Expr::app(c("UInt8.ofNat"), answer),
        Domain::CharList => Expr::app(
            Expr::const_(name("List.nil"), vec![Level::zero()]),
            c("Char"),
        ),
        // `String.Pos.next` under its `s`, `pos` and `h` binders: `pos` itself.
        Domain::StringPosition => Expr::bvar(1).unwrap(),
        _ => unreachable!(),
    };
    if operation.dependent() {
        // Positions and proofs mention earlier binders: keep the telescope.
        let mut binders = Vec::new();
        let mut telescope = &info.constant_val().type_;
        for _ in operation.domains() {
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = telescope.node()
            else {
                unreachable!("the checked telescope binds every domain")
            };
            binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
            telescope = body;
        }
        for (binder_name, binder_type, binder_info) in binders.into_iter().rev() {
            body = Expr::lam(binder_name, binder_type, body, binder_info);
        }
    } else {
        for domain in operation.domains().iter().rev() {
            body = Expr::lam(
                Name::anonymous(),
                domain.source_type(),
                body,
                BinderInfo::Default,
            );
        }
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
            // `@` keeps an implicit String an argument of the reference.
            let explicit = if operation.dependent() { "@" } else { "" };
            let source = format!("def refusedNative := {explicit}{}", operation.label());
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

/// Compile a closed term along the runtime's own path after admission:
/// preparation, the executable closure, callable interfaces, FIR ingress and
/// the VM. Checked source cannot contain a malformed projection, so the
/// term is built here and never reaches a checker or an environment.
fn execute_unchecked(
    environment: &Environment,
    term: &Expr,
    type_: &Expr,
) -> Result<ClosedVmValue, IngressError> {
    let limits = IngressLimits::default();
    let mut preparation = crate::runtime::Preparation::new(environment, limits);
    let runtime_type = preparation.normalize_type(type_)?;
    let root = preparation.root_result(&runtime_type);
    let expression = preparation.expression_at_type(term, Some(type_.clone()))?;
    let mut catalog =
        crate::executable_dependencies(environment, &expression, limits, &mut preparation)?;
    preparation.refine_expression_captures(&expression)?;
    let interfaces =
        preparation.finalize_callables(&mut catalog.functions, &mut catalog.intrinsics)?;
    let ingress = fln_comp::ingress::lower_closed_expr_at_result(
        &expression,
        &catalog.scalar_constructors,
        &catalog.intrinsics,
        &preparation.constructors,
        preparation.callables(&catalog.functions),
        &interfaces,
        root,
        limits,
    )?;
    let lowered = fln_comp::fir::lower_to_flbc(ingress.fir()).unwrap();
    let artifact = flbc::encode_canonical(&lowered, flbc::CodecLimits::default()).unwrap();
    let exit = execute_flbc_artifact(&artifact, &KVMap::new(), Default::default())
        .unwrap()
        .into_complete()
        .unwrap();
    Ok(closed_vm_value(&exit).unwrap().unwrap())
}

/// `String` keeps its native representation, so no projection of it is read
/// as a field, and a malformed projection must not reach any lowering:
/// `String` has no field 2, a `Nat` operand is not a `String`, and a String
/// operand is not a `Pos.Raw` record. Each stops at preparation, before FIR
/// ingress, with its own typed refusal. The control projects a computed
/// record through the same path, so each refusal is about the malformed
/// projection, not the harness. Valid String byte views are exercised below
/// through both checked source and direct projection ingress.
#[test]
fn malformed_string_projections_stay_typed_refusals_below_the_checkers() {
    with_fixture(|fixture| {
        let environment = &fixture.environment;
        let c = |label| Expr::const_(name(label), vec![]);
        let nat = Expr::lit(Literal::Nat(NatLit::from_u64(5)));
        let text = Expr::lit(Literal::Str("aλ".to_owned()));
        let advanced = Expr::app(
            Expr::app(c("String.Internal.next"), text.clone()),
            Expr::app(
                c("String.Pos.Raw.mk"),
                Expr::lit(Literal::Nat(NatLit::from_u64(1))),
            ),
        );
        assert_eq!(
            execute_unchecked(
                environment,
                &Expr::proj(name("String.Pos.Raw"), 0, advanced),
                &c("Nat"),
            )
            .unwrap(),
            ClosedVmValue::Scalar(3)
        );
        for (structure, field, operand, refusal) in [
            (
                "String",
                2,
                text.clone(),
                "projection field outside constructor telescope",
            ),
            ("String", 0, nat, "projection receiver family mismatch"),
            (
                "String.Pos.Raw",
                0,
                text,
                "projection receiver family mismatch",
            ),
        ] {
            assert!(
                matches!(
                    execute_unchecked(
                        environment,
                        &Expr::proj(name(structure), field, operand),
                        &c("Nat"),
                    ),
                    Err(IngressError::UnsupportedNode { kind }) if kind == refusal
                ),
                "{structure} field {field}"
            );
        }
    });
}

#[test]
fn native_string_byte_views_feed_logical_consumers_and_replay() {
    with_fixture(|fixture| {
        let engine = Engine::from_environment(fixture.environment.clone());
        let options = KVMap::new();
        let root = engine.logical_root(&options);
        let source = r#"
def byteView (s : String) : ByteArray := s.toByteArray
def byteFingerprint (bytes : ByteArray) : Nat :=
  List.foldl (fun (total : Nat) (byte : UInt8) => total * 257 + UInt8.toNat byte)
    0 (Array.toList (ByteArray.data bytes))
def rebuildBytes (bytes : ByteArray) : ByteArray :=
  ByteArray.mk (Array.mk bytes.data.toList)
#eval byteFingerprint (byteView "")
#eval byteFingerprint (byteView "abc")
#eval byteFingerprint (byteView "A\x00λ")
#eval byteFingerprint (byteView "😀")
#eval let view := String.toByteArray; byteFingerprint (view "é")
#eval byteFingerprint (ByteArray.push ("é".toByteArray) (UInt8.ofNat 0))
#eval (String.toByteArray "λ").size
#eval byteFingerprint (rebuildBytes "A\x00λ".toByteArray)
"#;
        let run = engine
            .execute_source_commands_with_checks(
                source.as_bytes(),
                &options,
                EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
            )
            .unwrap_or_else(|error| panic!("checked String byte view: {error:?}"))
            .into_complete()
            .unwrap();
        let fingerprint = |bytes: &[u8]| {
            bytes
                .iter()
                .fold(0usize, |total, byte| total * 257 + usize::from(*byte))
        };
        let expected = [
            fingerprint(b""),
            fingerprint(b"abc"),
            fingerprint("A\0λ".as_bytes()),
            fingerprint("😀".as_bytes()),
            fingerprint("é".as_bytes()),
            fingerprint("é\0".as_bytes()),
            2,
            fingerprint("A\0λ".as_bytes()),
        ];
        assert_eq!(run.batch.source_evaluation_indices.len(), expected.len());
        for (&index, expected) in run.batch.source_evaluation_indices.iter().zip(expected) {
            let execution = &run.batch.executions[index];
            assert_eq!(
                closed_vm_value(&execution.exit).unwrap(),
                Some(ClosedVmValue::Scalar(expected))
            );
            let replay =
                execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
                    .unwrap()
                    .into_complete()
                    .unwrap();
            assert_eq!(
                closed_vm_value(&replay).unwrap(),
                Some(ClosedVmValue::Scalar(expected))
            );
        }
        // Direct Expr::Proj ingress must take the same bridge as named and
        // first-class String.toByteArray, without reading a native field.
        for text in ["", "é", "A\0λ", "😀"] {
            let field = Expr::proj(name("String"), 0, Expr::lit(Literal::Str(text.to_owned())));
            let size = Expr::app(Expr::const_(name("ByteArray.size"), vec![]), field);
            assert_eq!(
                execute_unchecked(
                    &fixture.environment,
                    &size,
                    &Expr::const_(name("Nat"), vec![]),
                )
                .unwrap(),
                ClosedVmValue::Scalar(text.len())
            );
        }
        assert_eq!(engine.logical_root(&options), root);
    });
}

#[test]
fn string_byte_views_use_native_arrays_of_checked_uint8_values() {
    with_fixture(|fixture| {
        let engine = Engine::from_environment(fixture.environment.clone());
        let options = KVMap::new();
        let root = engine.logical_root(&options);
        let source = r#"
#eval "".toByteArray
#eval "A\x00λ".toByteArray
#eval "😀".toByteArray
"#;
        let completed = engine
            .execute_source_commands_with_checks(
                source.as_bytes(),
                &options,
                EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
            )
            .unwrap_or_else(|error| panic!("checked native Array byte views: {error:?}"))
            .into_complete()
            .unwrap();
        let expected = ["", "A\0λ", "😀"];
        assert_eq!(
            completed.batch.source_evaluation_indices.len(),
            expected.len()
        );
        for (&index, expected) in completed
            .batch
            .source_evaluation_indices
            .iter()
            .zip(expected)
        {
            let execution = &completed.batch.executions[index];
            let program =
                flbc::decode_canonical(&execution.flbc_artifact, Default::default()).unwrap();
            assert!(
                program
                    .functions()
                    .iter()
                    .flat_map(|function| &function.code)
                    .any(
                        |instruction| matches!(instruction, Instruction::Intrinsic { row, .. }
                        if row == "extern:Array.mk")
                    ),
                "the byte view must construct native Array storage"
            );
            let replay =
                execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
                    .unwrap()
                    .into_complete()
                    .unwrap();
            for exit in [&execution.exit, &replay] {
                let VmExit::Returned(returned) = exit else {
                    panic!("checked byte view must return: {exit:?}");
                };
                let bytes = &returned.value;
                assert_eq!(bytes.header().tag, 0);
                assert_eq!(bytes.header().other, 1);
                let array = bytes.try_ctor_child(0).expect("ByteArray storage field");
                let (size, _) = array.try_array_view().expect("native Array UInt8 storage");
                assert_eq!(size, expected.len());
                for (index, expected) in expected.bytes().enumerate() {
                    let byte = array.array_child(index);
                    let bits = byte.try_ctor_child(0).expect("logical UInt8.ofBitVec");
                    let finite = bits.try_ctor_child(0).expect("logical BitVec.ofFin");
                    let natural = finite.try_ctor_child(0).expect("logical Fin.val");
                    assert_eq!(natural.unbox(), usize::from(expected));
                }
            }
        }
        assert_eq!(engine.logical_root(&options), root);
    });
}

#[test]
fn string_byte_view_preserves_strict_input_and_resource_refusal() {
    with_fixture(|fixture| {
        let engine = Engine::from_environment(fixture.environment.clone());
        let options = KVMap::new();
        let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
        let source = |cost: u64| {
            format!(
                "def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1\n\
                 #eval (let prepared : Nat := spend {cost}; \"\").toByteArray.size\n"
            )
        };
        let run = |cost, limits| {
            engine
                .execute_source_commands_with_checks(source(cost).as_bytes(), &options, limits)
                .unwrap()
        };
        let idle = run(0, limits).into_complete().unwrap();
        let index = idle.batch.source_evaluation_indices[0];
        let VmExit::Returned(result) = &idle.batch.executions[index].exit else {
            panic!("the empty byte view must return its logical size");
        };
        let idle_steps = result.usage.steps;
        let busy = run(30, limits).into_complete().unwrap();
        let index = busy.batch.source_evaluation_indices[0];
        assert_eq!(
            closed_vm_value(&busy.batch.executions[index].exit).unwrap(),
            Some(ClosedVmValue::Scalar(0))
        );
        let VmExit::Returned(result) = &busy.batch.executions[index].exit else {
            panic!("the strict byte view must return its logical size");
        };
        assert!(result.usage.steps > idle_steps + 30);
        let mut bounded = limits;
        bounded.vm.max_steps = idle_steps;
        assert!(matches!(run(30, bounded), Outcome::Inconclusive(_)));
        assert!(run(30, limits).into_complete().is_ok());
    });
}

#[test]
fn string_byte_view_refuses_a_foreign_projection_extern() {
    with_fixture(|fixture| {
        let environment = externs::register(
            &fixture.environment,
            &name("String.toByteArray"),
            vec![ExternEntry::Standard {
                backend: name("all"),
                symbol: "foreign_string_bytes".to_owned(),
            }],
        )
        .unwrap();
        let engine = Engine::from_environment(environment);
        let options = KVMap::new();
        let root = engine.logical_root(&options);
        assert!(
            engine
                .execute_source_commands_with_checks(
                    b"#eval (String.toByteArray \"hello\").size",
                    &options,
                    EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
                )
                .is_err()
        );
        assert_eq!(engine.logical_root(&options), root);
    });
}
