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

fn matches(environment: &Environment) -> Result<bool, IngressError> {
    string_from_list::contract_matches(
        environment,
        &string_from_list::source_name(),
        &mut None,
        &mut 0,
        IngressLimits::default(),
    )
}

fn actual_dependencies(environment: &Environment) -> BTreeSet<Name> {
    let mut pending = vec![string_from_list::source_name()];
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

#[test]
fn string_from_list_inventory_binds_the_complete_actual_prelude_closure() {
    with_fixture(|fixture| {
        let mut expected = BTreeSet::new();
        for line in string_from_list::dependency_inventory().lines() {
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
            assert_eq!(
                fixture.prelude.entry(&label).unwrap().digest().to_hex(),
                digest
            );
        }
        assert_eq!(expected.len(), 320);
        assert_eq!(expected, actual_dependencies(&fixture.prelude));
        assert!(matches(&fixture.prelude).unwrap());
        assert!(matches(&fixture.environment).unwrap());
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
        assert!(!prelude.string_from_list.verified);
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
        let source = r#"
def renderChars : List Char → String := String.ofList
def applyRenderer (render : List Char → String) (chars : List Char) : String := render chars
#eval String.ofList []
#eval String.ofList ['4', '2']
#eval renderChars ['A', 'λ', '😀', '\x00', 'e', '́']
#eval let render := String.ofList; render ['L', '∃', '∀', 'N']
#eval applyRenderer String.ofList ['\x00', 'λ', '\x00']
#eval let ch := '😀'; applyRenderer (fun chars => String.ofList (ch :: chars)) ['λ']
"#;
        let expected = ["", "42", "Aλ😀\0é", "L∃∀N", "\0λ\0", "😀λ"];
        let run = || {
            engine
                .execute_source_definitions(&[source.as_bytes()], &options, limits)
                .unwrap_or_else(|error| panic!("checked String.ofList source: {error:?}"))
                .into_complete()
                .unwrap()
        };
        let first = run();
        assert_eq!(first.source_evaluation_indices.len(), expected.len());
        for (&index, expected) in first.source_evaluation_indices.iter().zip(expected) {
            let execution = &first.executions[index];
            assert_eq!(
                execution.checker.ground,
                CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
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
                    Some(ClosedVmValue::String(expected.to_owned()))
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
        let source = |cost| {
            format!(
                "def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => Nat.succ (spend k)\n\
             #eval let rendered := String.ofList (let paid : Nat := spend {cost}; ([] : List Char)); \"kept\"\n"
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
            "the actual strict source operand must execute"
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
                    CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
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
        let requested = string_from_list::source_name();
        let missing = rebuild(fixture, None, Some(&requested));
        assert!(!matches(&missing).unwrap());
        let foreign = externs::register(
            &missing,
            &requested,
            vec![ExternEntry::Standard {
                backend: name("all"),
                symbol: "foreign_string_from_list".to_owned(),
            }],
        )
        .unwrap();
        assert!(matches(&foreign).is_err());
        for label in [
            "String.ofList",
            "String.ofList._proof_1",
            "List.rec",
            "String.utf8EncodeChar",
            "Char.mk",
        ] {
            let omitted = name(label);
            let environment = rebuild(fixture, Some(&omitted), None);
            assert!(!matches(&environment).unwrap_or(false), "missing {label}");
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
            let mut preparation = Preparation::new(&changed_environment, IngressLimits::default());
            assert!(
                preparation
                    .string_from_list_call(&c("String.ofList"), &[])
                    .is_err(),
                "changed {label}"
            );
            assert!(!preparation.string_from_list.verified);
            assert!(preparation.constructors.is_empty());
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
                    .string_from_list_call(&c("String.ofList"), &[])
                    .is_err()
            );
            assert!(!preparation.string_from_list.verified);
        }
        let mut exact = Preparation::new(&fixture.environment, IngressLimits::default());
        assert!(
            exact
                .string_from_list_call(&c("String.ofList"), &[])
                .unwrap()
                .is_some()
        );
        assert!(exact.string_from_list.verified);
    });
}

#[test]
fn string_from_list_contract_and_adapter_remain_metered_on_cold_and_cached_paths() {
    with_fixture(|fixture| {
        let limits = IngressLimits::default();
        let head = c("String.ofList");
        let mut work = 0;
        assert!(
            string_from_list::contract_matches(
                &fixture.environment,
                &string_from_list::source_name(),
                &mut None,
                &mut work,
                limits
            )
            .unwrap()
        );
        assert!(work > 320);
        for maximum in [0, work - 1] {
            assert!(matches!(string_from_list::contract_matches(
                &fixture.environment, &string_from_list::source_name(), &mut None, &mut 0,
                IngressLimits { max_nodes: maximum, ..limits }),
                Err(IngressError::ResourceLimit { resource: IngressResource::Nodes, limit, observed })
                    if limit == maximum && observed > limit
            ));
        }
        let mut preparation = Preparation::new(&fixture.environment, limits);
        for (head, arguments) in [
            (c("Nat.succ"), Vec::new()),
            (
                Expr::const_(string_from_list::source_name(), vec![Level::zero()]),
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
    });
}
