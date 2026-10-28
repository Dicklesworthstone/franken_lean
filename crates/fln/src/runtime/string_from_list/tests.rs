//! Actual pinned comparison data and checked source/native execution probes.
//!
//! The decoded fixture is not an admitted library. Authored definitions and
//! evaluation wrappers still cross both checkers; full Repr integration tests
//! separately exercise the same adapter after admission of its import closure.

use super::*;
use fln_comp::flbc::{self, ArgumentOwnership, Instruction, ResultOwnership};
use fln_core::diag::ResourceReason;
use fln_core::outcome::InconclusiveCause;
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
            let mut prelude = None;
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
                for info in decoded.constants {
                    if let Some(previous) = constants.insert(info.name().clone(), info.clone()) {
                        assert_eq!(
                            previous, info,
                            "the fixture does not select matching bodies"
                        );
                    }
                }
                if module == "Init/Prelude" {
                    prelude = Some(environment(&constants, &actual_externs));
                }
            }
            Some(Fixture {
                environment: environment(&constants, &actual_externs),
                prelude: prelude.unwrap(),
                externs: actual_externs,
            })
        })
        .as_ref()
}

fn environment(
    constants: &BTreeMap<Name, ConstantInfo>,
    declarations: &BTreeMap<Name, Vec<ExternEntry>>,
) -> Environment {
    let mut result = Environment::new();
    for info in constants.values() {
        result = result.add_decl(info.clone()).unwrap();
    }
    for (label, entries) in declarations {
        result = externs::register(&result, label, entries.clone()).unwrap();
    }
    result
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

fn rebuild(fixture: &Fixture, omit: Option<&Name>, omit_extern: Option<&Name>) -> Environment {
    let mut result = Environment::new();
    for (label, _) in fixture.environment.constants() {
        if omit != Some(label) {
            result = result
                .with_entry(fixture.environment.entry(label).unwrap())
                .unwrap();
        }
    }
    for (label, entries) in &fixture.externs {
        if omit != Some(label) && omit_extern != Some(label) {
            result = externs::register(&result, label, entries.clone()).unwrap();
        }
    }
    result
}

fn matches(environment: &Environment, root: Root) -> Result<bool, IngressError> {
    string_from_list::contract_matches(
        environment,
        &root.source_name(),
        &mut None,
        &mut 0,
        IngressLimits::default(),
    )
}

/// Recompute a root's complete graph independently of its frozen inventory.
fn actual_dependencies(environment: &Environment, root: Root) -> BTreeSet<Name> {
    let mut pending = vec![root.source_name()];
    let mut found = BTreeSet::new();
    let mut seen_expressions = HashSet::new();
    while let Some(label) = pending.pop() {
        if !found.insert(label.clone()) {
            continue;
        }
        assert!(found.len() <= 10_000);
        let info = environment.find(&label).unwrap();
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

/// One root's frozen inventory, with each row's digest checked against the
/// environment that defines it.
fn inventory(environment: &Environment, root: Root) -> BTreeSet<Name> {
    let mut expected = BTreeSet::new();
    for line in root.dependency_inventory().lines() {
        let (encoded, digest) = line.split_once('\t').unwrap();
        let mut label = Name::anonymous();
        for component in encoded.split('/') {
            label = if let Some(part) = component.strip_prefix("s:") {
                Name::str(label, part)
            } else {
                Name::num(
                    label,
                    component.strip_prefix("n:").unwrap().parse().unwrap(),
                )
            };
        }
        assert!(expected.insert(label.clone()));
        assert_eq!(environment.entry(&label).unwrap().digest().to_hex(), digest);
    }
    expected
}

#[test]
fn string_from_list_inventory_binds_the_complete_actual_prelude_closure() {
    with_fixture(|fixture| {
        let expected = inventory(&fixture.prelude, Root::OfList);
        assert_eq!(expected.len(), 320);
        assert_eq!(
            expected,
            actual_dependencies(&fixture.prelude, Root::OfList)
        );
        assert!(matches(&fixture.prelude, Root::OfList).unwrap());
        assert!(matches(&fixture.environment, Root::OfList).unwrap());
        // The deprecated alias is a Bootstrap declaration with its own closure,
        // which never passes through its target. The Prelude alone has neither
        // the alias nor its extern, so it stays on the ordinary path there.
        // Measured with the pin: the same 320 rows, except that the root and
        // its proof are `String.mk` and `String.mk._proof_1`.
        let alias = inventory(&fixture.environment, Root::Mk);
        assert_eq!(alias.len(), 320);
        assert_eq!(
            alias
                .symmetric_difference(&expected)
                .cloned()
                .collect::<BTreeSet<_>>(),
            [
                "String.mk",
                "String.mk._proof_1",
                "String.ofList",
                "String.ofList._proof_1"
            ]
            .map(name)
            .into_iter()
            .collect()
        );
        assert_eq!(alias, actual_dependencies(&fixture.environment, Root::Mk));
        assert!(alias.contains(&name("String.mk")));
        assert!(!alias.contains(&name("String.ofList")));
        assert!(!expected.contains(&name("String.mk")));
        assert!(matches(&fixture.environment, Root::Mk).unwrap());
        assert!(!fixture.prelude.contains(&name("String.mk")));
        assert!(!matches(&fixture.prelude, Root::Mk).unwrap());
        // Each root reads its own generated census row, never its target's.
        for (root, module) in [
            (Root::OfList, "Init.Prelude"),
            (Root::Mk, "Init.Data.String.Bootstrap"),
        ] {
            let row = fln_vm::extern_table_generated::EXTERN_ROWS
                .iter()
                .find(|row| row.name == root.label())
                .unwrap();
            assert_eq!(row.id, format!("extern:{}", root.label()));
            assert_eq!(
                (row.module, row.symbol, row.ownership),
                (
                    module,
                    "lean_string_mk",
                    "abi((cs: owned_arg) -> owned_res)"
                )
            );
        }
        assert!(!fixture.prelude.contains(&name("String.push")));
        // The initial executable traversal deliberately reuses the separately
        // checked Bootstrap push primitive; the root authority itself remains
        // the complete Prelude closure and does not request any IO definitions.
        let mut prelude = Preparation::new(&fixture.prelude, IngressLimits::default());
        assert!(
            prelude
                .string_from_list_call(&c("String.ofList"), &[])
                .is_err()
        );
        assert_eq!(prelude.string_from_list.verified, [false; 2]);
        assert!(!fixture.environment.contains(&name("IO.FS.Handle")));
    });
}

#[test]
fn logical_character_lists_execute_in_order_through_native_push_and_canonical_replay() {
    with_fixture(|fixture| {
        let engine = Engine::from_environment(fixture.environment.clone());
        let options = KVMap::new();
        let root = engine.logical_root(&options);
        let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
        // Every expected value is the pinned `lean`'s own output, for both
        // roots (`String.mk` under `set_option linter.deprecated false`).
        let expected = ["", "42", "Aλ😀\0é", "L∃∀N", "\0λ\0", "😀λ", "aéz"];
        for label in Root::ALL.map(Root::label) {
            let source = format!(
                r#"
def renderChars : List Char → String := {label}
def applyRenderer (render : List Char → String) (chars : List Char) : String := render chars
#eval {label} []
#eval {label} ['4', '2']
#eval renderChars ['A', 'λ', '😀', '\x00', 'e', '́']
#eval let render := {label}; render ['L', '∃', '∀', 'N']
#eval applyRenderer {label} ['\x00', 'λ', '\x00']
#eval let ch := '😀'; applyRenderer (fun chars => {label} (ch :: chars)) ['λ']
#eval {label} ['a', 'é', 'z']
"#
            );
            let run = || {
                engine
                    .execute_source_definitions(&[source.as_bytes()], &options, limits)
                    .unwrap_or_else(|error| panic!("checked {label} source: {error:?}"))
                    .into_complete()
                    .unwrap()
            };
            let first = run();
            assert_eq!(first.source_evaluation_indices.len(), expected.len());
            for (&index, expected) in first.source_evaluation_indices.iter().zip(expected) {
                let execution = &first.executions[index];
                // #eval's auxiliary is unsafe at the pin (BuiltinEvalCommand.lean:92).
                assert_eq!(
                    execution.checker.ground,
                    CheckerAdmissionGround::UnsafeQuarantine
                );
                let decoded =
                    flbc::decode_canonical(&execution.flbc_artifact, Default::default()).unwrap();
                assert_eq!(
                    flbc::encode_canonical(&decoded, Default::default()).unwrap(),
                    execution.flbc_artifact
                );
                assert!(decoded.functions().iter().flat_map(|function| &function.code).any(|instruction|
                    matches!(instruction, Instruction::Intrinsic { row, argument_ownership, result_ownership, .. }
                        if row == "extern:String.push"
                            && argument_ownership == &[ArgumentOwnership::Owned, ArgumentOwnership::Scalar]
                            && *result_ownership == ResultOwnership::Owned)
                ));
                let replay =
                    execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
                        .unwrap()
                        .into_complete()
                        .unwrap();
                for exit in [&execution.exit, &replay] {
                    assert_eq!(
                        closed_vm_value(exit).unwrap(),
                        Some(ClosedVmValue::String(expected.to_owned())),
                        "{label}"
                    );
                }
            }
            let repeated = run();
            for &index in &first.source_evaluation_indices {
                assert_eq!(
                    first.executions[index].flbc_artifact,
                    repeated.executions[index].flbc_artifact
                );
            }
        }
        assert_eq!(engine.logical_root(&options), root);
    });
}

#[test]
fn string_from_list_keeps_strict_list_producers_and_vm_exhaustion() {
    with_fixture(|fixture| {
        let engine = Engine::from_environment(fixture.environment.clone());
        let options = KVMap::new();
        let root = engine.logical_root(&options);
        let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
        for label in Root::ALL.map(Root::label) {
            let source = |cost| {
                format!(
                    "def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => Nat.succ (spend k)\n\
                 #eval let rendered := {label} (let paid : Nat := spend {cost}; ([] : List Char)); \"kept\"\n"
                )
            };
            let execute = |cost| {
                let source = source(cost);
                let batch = engine
                    .execute_source_definitions(&[source.as_bytes()], &options, limits)
                    .unwrap()
                    .into_complete()
                    .unwrap();
                let execution = &batch.executions[*batch.source_evaluation_indices.last().unwrap()];
                assert_eq!(
                    closed_vm_value(&execution.exit).unwrap(),
                    Some(ClosedVmValue::String("kept".to_owned()))
                );
                let VmExit::Returned(result) = &execution.exit else {
                    panic!("strict list producer returns");
                };
                let replay =
                    execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
                        .unwrap()
                        .into_complete()
                        .unwrap();
                let VmExit::Returned(replayed) = replay else {
                    panic!("strict list producer replays");
                };
                assert_eq!(result.usage.steps, replayed.usage.steps);
                result.usage.steps
            };
            let idle = execute(0);
            let busy = execute(30);
            assert!(
                busy > idle + 30,
                "the actual strict source operand of {label} must execute"
            );
            let mut bounded = limits;
            bounded.vm.max_steps = idle;
            let source_busy = source(30);
            assert!(matches!(
                engine.execute_source_definitions(&[source_busy.as_bytes()], &options, bounded).unwrap(),
                Outcome::Inconclusive(stop) if matches!(&stop.cause,
                    InconclusiveCause::ResourceExhausted { usage }
                        if usage.reason == ResourceReason::ExecutionSteps
                            && usage.allowed == idle && usage.observed == idle + 1)
            ));
            assert_eq!(
                execute(30),
                busy,
                "an exhausted execution does not spoil retry"
            );
        }
        assert_eq!(engine.logical_root(&options), root);
    });
}

#[test]
fn string_from_list_preserves_root_replacements_and_remains_a_native_replacement_target() {
    with_fixture(|fixture| {
        let engine = Engine::from_environment(fixture.environment.clone());
        let options = KVMap::new();
        let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
        let make_replacement = |original: &str, replacement: &str, text: &str| {
            let original = engine
                .environment()
                .find(&name(original))
                .unwrap()
                .constant_val();
            assert!(original.level_params.is_empty());
            let mut result = original.type_.clone();
            let mut binders = Vec::new();
            while let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = result.node()
            {
                binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
                result = body.clone();
            }
            assert_eq!(result, c("String"));
            let value = binders.into_iter().rev().fold(
                Expr::lit(Literal::Str(text.to_owned())),
                |body, (name, domain, style)| Expr::lam(name, domain, body, style),
            );
            let label = name(replacement);
            Declaration::Defn(DefinitionVal {
                base: fln_env::constants::ConstantVal {
                    name: label.clone(),
                    level_params: Vec::new(),
                    type_: original.type_.clone(),
                },
                value,
                hints: fln_env::constants::ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![label],
            })
        };
        let declarations = [
            make_replacement("String.ofList", "listReplacement", "root replacement"),
            make_replacement("String.ofList", "logicalRenderer", "logical renderer"),
            make_replacement("String.push", "pushReplacement", "helper replacement"),
            make_replacement("String.mk", "aliasReplacement", "alias replacement"),
        ];
        let admitted = engine
            .admit_declarations(
                &declarations,
                &options,
                EngineAdmissionLimits::new(limits.kernel),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
        let base_root = admitted.logical_root(&options);
        for (original, replacement, source, expected) in [
            (
                "String.ofList",
                "listReplacement",
                "#eval String.ofList ['λ']\n#eval let render := String.ofList; render ['😀']\n",
                ["root replacement", "root replacement"],
            ),
            (
                "logicalRenderer",
                "String.ofList",
                "#eval logicalRenderer ['λ', '😀']\n#eval let render := logicalRenderer; render ['\\x00', 'λ']\n",
                ["λ😀", "\0λ"],
            ),
            (
                "String.push",
                "pushReplacement",
                "#eval String.push \"\" 'λ'\n#eval let render := String.ofList; render ['λ', '😀']\n",
                ["helper replacement", "λ😀"],
            ),
            // The deprecated alias keeps its own replacement and is a native
            // target in its own right; neither root inherits the other's.
            (
                "String.mk",
                "aliasReplacement",
                "#eval String.mk ['λ']\n#eval let render := String.ofList; render ['😀']\n",
                ["alias replacement", "😀"],
            ),
            (
                "String.ofList",
                "listReplacement",
                "#eval String.mk ['λ']\n#eval let render := String.mk; render ['😀']\n",
                ["λ", "😀"],
            ),
            (
                "logicalRenderer",
                "String.mk",
                "#eval logicalRenderer ['λ', '😀']\n#eval let render := logicalRenderer; render ['\\x00', 'λ']\n",
                ["λ😀", "\0λ"],
            ),
        ] {
            let environment = fln_elab::implemented_by::register(
                admitted.environment(),
                &name(original),
                &name(replacement),
            )
            .unwrap();
            assert_eq!(
                environment.find(&name(original)),
                admitted.environment().find(&name(original))
            );
            assert_eq!(
                environment.find(&name(replacement)),
                admitted.environment().find(&name(replacement))
            );
            let engine = Engine::from_environment(environment);
            let run = engine
                .execute_source_definitions(&[source.as_bytes()], &options, limits)
                .unwrap_or_else(|error| panic!("{original} replaced by {replacement}: {error:?}"))
                .into_complete()
                .unwrap();
            assert_eq!(run.source_evaluation_indices.len(), expected.len());
            for (&index, expected) in run.source_evaluation_indices.iter().zip(expected) {
                let execution = &run.executions[index];
                assert_eq!(
                    execution.checker.ground,
                    CheckerAdmissionGround::UnsafeQuarantine
                );
                let replay =
                    execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
                        .unwrap()
                        .into_complete()
                        .unwrap();
                for exit in [&execution.exit, &replay] {
                    assert_eq!(
                        closed_vm_value(exit).unwrap(),
                        Some(ClosedVmValue::String(expected.to_owned()))
                    );
                }
            }
        }
        assert_eq!(admitted.logical_root(&options), base_root);
    });
}

#[test]
fn string_from_list_refuses_missing_foreign_and_changed_root_or_helper_contracts() {
    with_fixture(|fixture| {
        for (root, other, proof) in [
            (Root::OfList, Root::Mk, "String.ofList._proof_1"),
            (Root::Mk, Root::OfList, "String.mk._proof_1"),
        ] {
            let requested = root.source_name();
            let missing = rebuild(fixture, None, Some(&requested));
            assert!(!matches(&missing, root).unwrap());
            assert!(matches(&missing, other).unwrap());
            let foreign = externs::register(
                &missing,
                &requested,
                vec![ExternEntry::Standard {
                    backend: name("all"),
                    symbol: "foreign_string_from_list".to_owned(),
                }],
            )
            .unwrap();
            assert!(matches(&foreign, root).is_err());
            assert!(matches(&foreign, other).unwrap());
            let sibling = inventory(&fixture.environment, other);
            for label in [
                root.label(),
                proof,
                "List.rec",
                "String.utf8EncodeChar",
                "Char.mk",
            ] {
                let omitted = name(label);
                let environment = rebuild(fixture, Some(&omitted), None);
                assert!(
                    !matches(&environment, root).unwrap_or(false),
                    "missing {label}"
                );
                let mut changed = fixture.environment.find(&omitted).unwrap().clone();
                match &mut changed {
                    ConstantInfo::Defn(value) => value.value = nat::literal(0),
                    ConstantInfo::Thm(value) => value.value = c("True.intro"),
                    ConstantInfo::Rec(value) => value.num_minors += 1,
                    ConstantInfo::Ctor(value) => value.num_fields += 1,
                    _ => panic!("fixed contract mutation"),
                }
                let mut changed_environment = environment.add_decl(changed).unwrap();
                if let Some(entries) = fixture.externs.get(&omitted) {
                    changed_environment =
                        externs::register(&changed_environment, &omitted, entries.clone()).unwrap();
                }
                let mut preparation =
                    Preparation::new(&changed_environment, IngressLimits::default());
                assert!(
                    preparation
                        .string_from_list_call(&c(root.label()), &[])
                        .is_err(),
                    "{} changed {label}",
                    root.label()
                );
                assert_eq!(preparation.string_from_list.verified, [false; 2]);
                assert!(preparation.constructors.is_empty());
                // A change outside the sibling's own closure leaves it intact,
                // and a shared change refuses both.
                assert_eq!(
                    matches(&changed_environment, other).is_ok_and(|exact| exact),
                    !sibling.contains(&omitted),
                    "{} after changing {label}",
                    other.label()
                );
                if omitted == requested {
                    // Proving the sibling first never vouches for the changed root.
                    let mut preparation =
                        Preparation::new(&changed_environment, IngressLimits::default());
                    assert!(
                        preparation
                            .string_from_list_call(&c(other.label()), &[])
                            .unwrap()
                            .is_some()
                    );
                    assert!(
                        preparation
                            .string_from_list_call(&c(root.label()), &[])
                            .is_err()
                    );
                    let mut verified = [false; 2];
                    verified[other.index()] = true;
                    assert_eq!(preparation.string_from_list.verified, verified);
                }
            }
            for helper in ["String.push", "UInt32.ofBitVec"] {
                let helper = name(helper);
                let missing = rebuild(fixture, None, Some(&helper));
                let foreign = externs::register(
                    &missing,
                    &helper,
                    vec![ExternEntry::Standard {
                        backend: name("all"),
                        symbol: "foreign_list_helper".to_owned(),
                    }],
                )
                .unwrap();
                let mut preparation = Preparation::new(&foreign, IngressLimits::default());
                assert!(
                    preparation
                        .string_from_list_call(&c(root.label()), &[])
                        .is_err()
                );
                assert_eq!(preparation.string_from_list.verified, [false; 2]);
            }
        }
        let mut exact = Preparation::new(&fixture.environment, IngressLimits::default());
        for root in Root::ALL {
            assert!(
                exact
                    .string_from_list_call(&c(root.label()), &[])
                    .unwrap()
                    .is_some()
            );
        }
        assert_eq!(exact.string_from_list.verified, [true; 2]);
    });
}

/// A well-typed replacement body for a root: a constant String, or for the
/// deprecated alias a call to its own target. Either is kernel-checked and
/// still not the pin's declaration.
fn counterfeit_bodies(root: Root, info: &ConstantInfo) -> Vec<Declaration> {
    let ConstantInfo::Defn(original) = info else {
        unreachable!("both roots are definitions")
    };
    let characters = Expr::app(Expr::const_(name("List"), vec![Level::zero()]), c("Char"));
    let mut bodies = vec![Expr::lit(Literal::Str("counterfeit".to_owned()))];
    if root == Root::Mk {
        bodies.push(Expr::app(c("String.ofList"), Expr::bvar(0).unwrap()));
    }
    bodies
        .into_iter()
        .map(|body| {
            let mut value = original.clone();
            value.value = Expr::lam(name("data"), characters.clone(), body, BinderInfo::Default);
            Declaration::Defn(value)
        })
        .collect()
}

#[test]
fn well_typed_counterfeit_roots_and_reserved_adapter_names_are_refused() {
    with_fixture(|fixture| {
        let options = KVMap::new();
        let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
        for root in Root::ALL {
            let requested = root.source_name();
            let source = format!("def refusedNative := {}", root.label());
            // The exact pinned root compiles, so each refusal below is about
            // the change and not the program.
            assert!(
                Engine::from_environment(fixture.environment.clone())
                    .execute_source_commands_with_checks(source.as_bytes(), &options, limits)
                    .is_ok()
            );
            let original = fixture.environment.find(&requested).unwrap();
            for counterfeit in counterfeit_bodies(root, original) {
                let changed = Engine::from_environment(rebuild(fixture, Some(&requested), None))
                    .admit_declaration(
                        counterfeit,
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
                assert!(matches(changed.environment(), root).is_err());
                let logical = changed.logical_root(&options);
                assert!(
                    changed
                        .execute_source_commands_with_checks(source.as_bytes(), &options, limits)
                        .is_err(),
                    "counterfeit {}",
                    root.label()
                );
                assert_eq!(changed.logical_root(&options), logical);
            }
            let reserved = Name::num(name("_fln_runtime_string_from_list_scope"), 0);
            let collision = Declaration::Defn(DefinitionVal {
                base: fln_env::constants::ConstantVal {
                    name: reserved.clone(),
                    level_params: vec![],
                    type_: c("Nat"),
                },
                value: nat::literal(0),
                hints: fln_env::constants::ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![reserved],
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
            let mut preparation =
                Preparation::new(occupied.environment(), IngressLimits::default());
            assert!(matches!(
                preparation.string_from_list_call(&c(root.label()), &[]),
                Err(IngressError::UnsupportedNode { kind })
                    if kind == "lean_string_mk adapter name collision"
            ));
            assert!(
                occupied
                    .execute_source_commands_with_checks(source.as_bytes(), &options, limits)
                    .is_err(),
                "a user declaration cannot impersonate the {} adapter scope",
                root.label()
            );
        }
    });
}

#[test]
fn string_from_list_contract_and_adapter_remain_metered_on_cold_and_cached_paths() {
    with_fixture(|fixture| {
        let limits = IngressLimits::default();
        for root in Root::ALL {
            let head = c(root.label());
            let mut work = 0;
            assert!(
                string_from_list::contract_matches(
                    &fixture.environment,
                    &root.source_name(),
                    &mut None,
                    &mut work,
                    limits
                )
                .unwrap()
            );
            assert!(work > root.dependency_inventory().lines().count());
            for maximum in [0, work - 1] {
                assert!(matches!(string_from_list::contract_matches(
                    &fixture.environment, &root.source_name(), &mut None, &mut 0,
                    IngressLimits { max_nodes: maximum, ..limits }),
                    Err(IngressError::ResourceLimit { resource: IngressResource::Nodes, limit, observed })
                        if limit == maximum && observed > limit
                ));
            }
            let mut preparation = Preparation::new(&fixture.environment, limits);
            for (head, arguments) in [
                (c("Nat.succ"), Vec::new()),
                (
                    Expr::const_(root.source_name(), vec![Level::zero()]),
                    Vec::new(),
                ),
                (head.clone(), vec![nat::literal(0), nat::literal(0)]),
            ] {
                assert!(
                    preparation
                        .string_from_list_call(&head, &arguments)
                        .unwrap()
                        .is_none()
                );
            }
            assert_eq!(preparation.visited, 0);
            let first = preparation
                .string_from_list_call(&head, &[])
                .unwrap()
                .unwrap();
            assert!(!first.has_loose_bvars());
            let cold_work = preparation.visited;
            let second = preparation
                .string_from_list_call(&head, &[])
                .unwrap()
                .unwrap();
            assert!(!second.has_loose_bvars());
            let hit_work = preparation.visited - cold_work;
            assert!(hit_work > 0 && hit_work < cold_work);
            preparation.limits.max_nodes = preparation.visited;
            assert!(matches!(
                preparation.string_from_list_call(&head, &[]),
                Err(IngressError::ResourceLimit {
                    resource: IngressResource::Nodes,
                    ..
                })
            ));
            preparation.limits = limits;
            assert!(
                preparation
                    .string_from_list_call(&head, &[])
                    .unwrap()
                    .is_some()
            );
        }
    });
}
