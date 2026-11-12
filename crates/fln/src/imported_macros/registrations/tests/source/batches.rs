//! Constructed user/library inputs exercise the public artifact importer, VM,
//! source scope driver and both checkers. These are not Reference parity cells.
//! The only test-only authority is the existing empty user-code partition.
use super::*;
use crate::imported_macros::source::SourceMacroFileCheck;
use crate::source_check::modules::imported::{SourceOleanImport, SourceOleanImportLimits};
use crate::source_check::{SourceCheckError, SourceCheckLimits, SourceFileCheck};
use crate::{OleanCheckLimits, OleanModuleInput};
use fln_core::expr::BinderInfo;
use fln_core::level::Level;
use fln_olean::{ModuleExtensionInput, encode_module_with_extensions};
use std::cell::Cell;

/// The declarations themselves cross real artifact admission. `Lean.Macro` is
/// a valid local alias and every owner has a well-typed safe body. The separately
/// supplied compiler IR is untrusted, as it is for ordinary imported user code;
/// its behavior is not inferred from these kernel bodies.
fn artifact_fixture() -> (Engine, RegisteredMacros) {
    artifact_fixture_with_extra_rows(&[])
}

fn artifact_fixture_with_extra_rows(
    extra_rows: &[(&str, &str, Option<&str>)],
) -> (Engine, RegisteredMacros) {
    let (imported, code) = artifact_import_fixture_with_extra_rows(extra_rows);
    let registry = imported
        .prepare_imported_macros(
            &code,
            &VerifiedPartition::user_fixture(),
            &users(&code),
            MacroRegistryLimits::default(),
        )
        .unwrap();
    (imported.engine, registry)
}

pub(super) fn artifact_import_fixture() -> (SourceOleanImport, Vec<IrModule>) {
    artifact_import_fixture_with_extra_rows(&[])
}

pub(super) type FixtureArtifacts = Vec<(Name, Vec<u8>)>;

/// Artifact export requires every declaration to belong to its checked import
/// receipt. Keep the ordinary checking fixture's ambient seed separate: this
/// fixture encodes the checked foundation alongside the library and imports
/// the complete module into an empty engine through both checkers.
pub(super) fn artifact_build_fixture() -> (SourceOleanImport, Vec<IrModule>, FixtureArtifacts) {
    artifact_build_fixture_with_parser_metadata(&[], &[], &[], &[])
}

pub(super) fn artifact_build_fixture_with_parser_metadata(
    extra_rows: &[(&str, &str, Option<&str>)],
    extra_constants: &[ConstantInfo],
    parser_rows: &[Obj],
    extra_ir: &[IrDecl],
) -> (SourceOleanImport, Vec<IrModule>, FixtureArtifacts) {
    artifact_import_fixture_with_foundation(
        extra_rows,
        extra_constants,
        parser_rows,
        extra_ir,
        None,
        true,
    )
}

pub(super) fn artifact_import_fixture_with_extra_rows(
    extra_rows: &[(&str, &str, Option<&str>)],
) -> (SourceOleanImport, Vec<IrModule>) {
    artifact_import_fixture_with_parser_metadata(extra_rows, &[], &[], &[])
}

/// Additional syntax data crosses the same public artifact-admission boundary
/// as the original macro fixtures. Existing callers retain identical inputs.
pub(super) fn artifact_import_fixture_with_parser_metadata(
    extra_rows: &[(&str, &str, Option<&str>)],
    extra_constants: &[ConstantInfo],
    parser_rows: &[Obj],
    extra_ir: &[IrDecl],
) -> (SourceOleanImport, Vec<IrModule>) {
    artifact_import_fixture_with_parser_dependency(
        extra_rows,
        extra_constants,
        parser_rows,
        extra_ir,
        None,
    )
}

/// A parser-only ancestor retains its own complete journal and declarations.
/// Selecting a consumer's syntax must not silently select this journal too.
pub(super) fn artifact_import_fixture_with_parser_dependency(
    extra_rows: &[(&str, &str, Option<&str>)],
    extra_constants: &[ConstantInfo],
    parser_rows: &[Obj],
    extra_ir: &[IrDecl],
    dependency: Option<(&str, &[ConstantInfo], &[Obj])>,
) -> (SourceOleanImport, Vec<IrModule>) {
    let (imported, code, _) = artifact_import_fixture_with_foundation(
        extra_rows,
        extra_constants,
        parser_rows,
        extra_ir,
        dependency,
        false,
    );
    (imported, code)
}

fn artifact_import_fixture_with_foundation(
    extra_rows: &[(&str, &str, Option<&str>)],
    extra_constants: &[ConstantInfo],
    parser_rows: &[Obj],
    extra_ir: &[IrDecl],
    dependency: Option<(&str, &[ConstantInfo], &[Obj])>,
    include_foundation: bool,
) -> (SourceOleanImport, Vec<IrModule>, FixtureArtifacts) {
    let seed = Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .unwrap();
    let nat = Expr::const_(name("Nat"), vec![]);
    let mut macro_type = nat.clone();
    let mut body = Expr::lit(Literal::Nat(NatLit::from_u64(0)));
    for binder in ["state", "context", "syntax"] {
        macro_type = Expr::forall_e(name(binder), nat.clone(), macro_type, BinderInfo::Default);
        body = Expr::lam(name(binder), nat.clone(), body, BinderInfo::Default);
    }
    let definition = |label: &str, type_: Expr, value: Expr| {
        ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: name(label),
                level_params: vec![],
                type_,
            },
            value,
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![name(label)],
        })
    };
    let owners = [
        "SourceLibrary.right",
        "SourceLibrary.skip",
        "SourceLibrary.left",
        "SourceLibrary.diagnostic",
        "SourceLibrary.hasDecl",
        "SourceLibrary.preresolved",
        "SourceLibrary.attributeProbe",
    ];
    let mut constants: Vec<_> = if include_foundation {
        seed.environment()
            .constants()
            .map(|(_, declaration)| declaration.clone())
            .collect()
    } else {
        Vec::new()
    };
    constants.push(definition(
        "Lean.Macro",
        Expr::sort(Level::zero().succ().unwrap()),
        macro_type,
    ));
    constants.extend(owners.iter().map(|label| {
        definition(
            label,
            Expr::const_(name("Lean.Macro"), vec![]),
            body.clone(),
        )
    }));
    constants.extend_from_slice(extra_constants);
    let rows = [
        ("term_+_", "SourceLibrary.right", None),
        ("term_+_", "SourceLibrary.skip", None),
        ("term_+_", "SourceLibrary.left", Some("SourceScoped")),
        ("term_-_", "SourceLibrary.diagnostic", None),
        ("term_*_", "SourceLibrary.hasDecl", None),
        ("term_/_", "SourceLibrary.preresolved", None),
        (
            "Lean.Parser.Command.attribute",
            "SourceLibrary.attributeProbe",
            None,
        ),
    ]
    .into_iter()
    .chain(extra_rows.iter().copied())
    .map(|(key, declaration, scope)| {
        let pair = Obj::mk_ctor(
            0,
            vec![inject_name(&name(key)), inject_name(&name(declaration))],
            &[],
        );
        match scope {
            Some(namespace) => Obj::mk_ctor(1, vec![inject_name(&name(namespace)), pair], &[]),
            None => Obj::mk_ctor(0, vec![pair], &[]),
        }
    })
    .collect::<Vec<_>>();
    let extension = name(macros::MACRO_EXTENSION);
    let parser_extension = fln_olean::source_extensions::parsers::extension_name();
    let mut extensions = vec![ModuleExtensionInput {
        name: &extension,
        entries: &rows,
    }];
    if !parser_rows.is_empty() {
        extensions.push(ModuleExtensionInput {
            name: &parser_extension,
            entries: parser_rows,
        });
    }
    let header = || OleanWriteHeader {
        version: format::OLEAN_ACCEPTED_VERSIONS[0],
        flags: 1,
        lean_version: format::PIN_TAG.strip_prefix('v').unwrap(),
        githash: format::PIN_COMMIT,
        base_addr: (format::REGION_ALIGN * 2) as u64,
    };
    let dependency_name = dependency.map(|(label, _, _)| name(label));
    let dependency_bytes = dependency.map(|(_, constants, rows)| {
        encode_module_with_extensions(
            ModuleWriteInput {
                is_module: false,
                imports: &[],
                constants,
                extra_const_names: &[],
            },
            &[ModuleExtensionInput {
                name: &parser_extension,
                entries: rows,
            }],
            header(),
            WriteBudget::default(),
        )
        .unwrap()
        .bytes
    });
    let imports: Vec<_> = dependency_name
        .iter()
        .map(|module| fln_olean::region::ModuleImport {
            module: module.clone(),
            import_all: false,
            is_exported: false,
            is_meta: false,
        })
        .collect();
    let bytes = encode_module_with_extensions(
        ModuleWriteInput {
            is_module: false,
            imports: &imports,
            constants: &constants,
            extra_const_names: &[],
        },
        &extensions,
        header(),
        WriteBudget::default(),
    )
    .unwrap()
    .bytes;
    let module = name("SourceLibrary");
    let mut inputs = Vec::new();
    if let (Some(name), Some(bytes)) = (&dependency_name, &dependency_bytes) {
        inputs.push(OleanModuleInput {
            name,
            artifact: bytes,
            server_artifact: None,
            private_artifact: None,
        });
    }
    inputs.push(OleanModuleInput {
        name: &module,
        artifact: &bytes,
        server_artifact: None,
        private_artifact: None,
    });
    // Retain the exact physical inputs for rechecking emitted artifacts from
    // an empty engine; an admitted base cannot replace their import closure.
    let retained = if include_foundation {
        inputs
            .iter()
            .map(|input| (input.name.clone(), input.artifact.to_vec()))
            .collect()
    } else {
        Vec::new()
    };
    let total_bytes = bytes.len() + dependency_bytes.as_ref().map_or(0, Vec::len);
    let base = if include_foundation {
        Engine::builder().build_empty()
    } else {
        seed.clone()
    };
    let imported = base
        .import_olean_modules_for_source(
            &inputs,
            std::slice::from_ref(&module),
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(total_bytes, admission().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    if include_foundation {
        assert_eq!(
            imported.engine.imported_environment(),
            Some(imported.engine.environment()),
            "the artifact build foundation must be bound by ordinary import admission"
        );
    }
    for owner in owners {
        assert!(
            imported
                .checked
                .modules
                .iter()
                .find(|checked| checked.name == module)
                .unwrap()
                .declarations
                .iter()
                .any(|row| row.name == name(owner))
        );
        assert!(!seed.environment().contains(&name(owner)));
    }
    let mut declarations = vec![
        selecting_function("SourceLibrary.right", 2),
        function("SourceLibrary.skip", Behavior::Unsupported),
        selecting_function("SourceLibrary.left", 0),
        function("SourceLibrary.diagnostic", Behavior::Diagnostic),
        super::super::lookup::has_decl_selector("SourceLibrary.hasDecl"),
        preresolved_function(),
        function("SourceLibrary.attributeProbe", Behavior::Unsupported),
    ];
    declarations.extend_from_slice(extra_ir);
    (imported, code(declarations), retained)
}

/// Preserve the left identifier's spelling and exact backing source, but bind
/// it explicitly to `available`. Printing and reparsing would lose this target.
fn preresolved_function() -> IrDecl {
    let mut declaration = function("SourceLibrary.preresolved", Behavior::Identity);
    let IrDecl::Function { body, .. } = &mut declaration else {
        unreachable!()
    };
    body.stmts = vec![
        bind(3, IrExpr::Lit(IrLit::Num(IrNat::Small(0)))),
        bind(
            4,
            IrExpr::Fap {
                function: name("Lean.Syntax.getArg"),
                args: vec![IrArg::Var(0), IrArg::Var(3)],
            },
        ),
        bind(5, IrExpr::Proj { i: 0, x: 4 }),
        bind(6, IrExpr::Proj { i: 1, x: 4 }),
        bind(7, IrExpr::Proj { i: 2, x: 4 }),
        bind(8, IrExpr::Lit(IrLit::Str("available".into()))),
        bind(
            9,
            IrExpr::Fap {
                function: name("Lean.Name.mkStr1"),
                args: vec![IrArg::Var(8)],
            },
        ),
        bind(
            10,
            ctor(
                layout::PRERESOLVED_DECL,
                "Lean.Syntax.Preresolved.decl",
                &[9, 3],
            ),
        ),
        bind(11, ctor(layout::LIST_CONS, "List.cons", &[10, 3])),
        bind(
            12,
            ctor(layout::SYNTAX_IDENT, "Lean.Syntax.ident", &[5, 6, 7, 11]),
        ),
        bind(13, ctor(layout::RESULT_OK, "EStateM.Result.ok", &[12, 2])),
    ];
    *body.terminal = IrTerminal::Ret(IrArg::Var(13));
    declaration
}

fn batch(
    engine: &Engine,
    registry: &RegisteredMacros,
    sources: &[&[u8]],
    limits: MacroTreeLimits,
    cancellation: Option<&dyn CancellationProbe>,
) -> SourceMacroFileCheck {
    engine.check_source_files_with_imported_macros(
        sources,
        &KVMap::new(),
        SourceCheckLimits::new(admission()),
        SourceMacroInvocation {
            registry,
            context: &context(),
            state: MacroState {
                macro_scope: 17,
                ..MacroState::default()
            },
            lookup: None,
            limits,
            cancellation,
        },
    )
}

fn succeeded(report: &SourceMacroFileCheck) -> &SourceFileCheck {
    let Outcome::Complete(Ok(checked)) = &report.outcome else {
        panic!("{report:?}")
    };
    assert!(report.state.is_some());
    checked
}

#[test]
fn imported_macro_batches_restore_scopes_sections_in_commands_and_file_boundaries() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let first = b"namespace Client\n\
        def global : Nat := 7 + 11\n\
        section\nopen scoped SourceScoped\n\
        def opened : Nat := 7 + 11\n\
        section\ndef inherited : Nat := 7 + 11\nend\nend\n\
        def restored : Nat := 7 + 11\n\
        open scoped SourceScoped in\ndef oneCommand : Nat := 7 + 11\n\
        def afterIn : Nat := 7 + 11\nend Client\n\
        namespace SourceScoped.Inner\ndef implicitScope : Nat := 7 + 11\nend SourceScoped.Inner\n\
        def afterNamespace : Nat := 7 + 11\n\
        open SourceScoped\ndef endOfFile : Nat := 7 + 11\n";
    let second = b"def nextFile : Nat := 7 + 11\n";
    let report = batch(
        &engine,
        &registry,
        &[first, second],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    for (declaration, value) in [
        ("Client.global", 11),
        ("Client.opened", 7),
        ("Client.inherited", 7),
        ("Client.restored", 11),
        ("Client.oneCommand", 7),
        ("Client.afterIn", 11),
        ("SourceScoped.Inner.implicitScope", 7),
        ("afterNamespace", 11),
        ("endOfFile", 7),
        ("nextFile", 11),
    ] {
        assert_declared_value(&checked.engine, declaration, value);
    }
    assert_eq!(checked.files, 2);
    assert_eq!(report.attempts.len(), 15);
    assert_eq!(report.state.as_ref().unwrap().macro_scope, 32);
    assert!(checked.scope.namespace.is_anonymous());
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    // File restoration preserves an embedding's initially active snapshot.
    let active = registry.activate_scoped(&name("SourceScoped")).unwrap();
    let active_report = batch(
        &engine,
        &active,
        &[
            b"section\nend\ndef first : Nat := 7 + 11",
            b"def second : Nat := 7 + 11",
        ],
        MacroTreeLimits::default(),
        None,
    );
    assert_declared_value(&succeeded(&active_report).engine, "second", 7);
    assert_eq!(active_report.attempts.len(), 2);
}

#[test]
fn imported_macro_batches_observe_prior_admissions_and_preserve_resolved_syntax() {
    let (engine, registry) = artifact_fixture();
    let first = b"def before : Nat := 7 * 11\ndef available : Nat := 13\n";
    let second = "-- λ🦀\r\nnamespace Client\r\n\
        def shadow : Nat := 99\r\n\
        def lexical : Nat := 0 + shadow\r\n\
        def resolved : Nat := shadow / 0\r\n\
        example : resolved = 13 := by rfl\r\n\
        end Client\r\ndef after : Nat := 7 * 11\r\n";
    let report = batch(
        &engine,
        &registry,
        &[first, second.as_bytes()],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    for (declaration, value) in [
        ("before", 11),
        ("Client.lexical", 99),
        ("Client.resolved", 13),
        ("after", 7),
    ] {
        assert_declared_value(&checked.engine, declaration, value);
    }
    assert_eq!(report.attempts.len(), 5);
    // Pin evalTactic (Tactic/Basic.lean:194) allocates a scope even for native rfl.
    assert_eq!(report.state.as_ref().unwrap().macro_scope, 17 + 5 + 1);
    assert!(report.attempts.iter().any(|attempt| {
        attempt
            .native_functions
            .iter()
            .any(|name| name == "mirror:Lean.Macro.hasDecl")
    }));
    assert!(!engine.environment().contains(&name("available")));
}

#[test]
fn imported_macro_batches_share_attempt_step_visit_and_generation_budgets() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let first = b"def first : Nat := 7 + 11".as_slice();
    let second = b"def second : Nat := 13 + 17".as_slice();
    let sources = [first, second];
    let report = batch(
        &engine,
        &registry,
        &sources,
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    assert_eq!(report.attempts.len(), 4);
    assert_eq!(report.state.as_ref().unwrap().macro_scope, 21);
    let individual: Vec<_> = sources
        .iter()
        .map(|source| {
            batch(
                &engine,
                &registry,
                &[*source],
                MacroTreeLimits::default(),
                None,
            )
        })
        .collect();
    for report in &individual {
        succeeded(report);
    }
    assert_eq!(
        report.completed_vm_usage.steps,
        individual
            .iter()
            .map(|report| report.completed_vm_usage.steps)
            .sum::<u64>()
    );
    assert_eq!(
        report.tree_usage.visits,
        individual
            .iter()
            .map(|report| report.tree_usage.visits)
            .sum::<u64>()
    );
    assert_eq!(
        report.tree_usage.generated_nodes,
        individual
            .iter()
            .map(|report| report.tree_usage.generated_nodes)
            .sum::<usize>()
    );
    assert_eq!(
        report.tree_usage.generated_bytes,
        individual
            .iter()
            .map(|report| report.tree_usage.generated_bytes)
            .sum::<usize>()
    );
    assert!(report.tree_usage.generated_nodes > 0);
    assert!(report.tree_usage.generated_bytes > 0);
    let mut exact = MacroTreeLimits::default();
    exact.dispatch.max_attempts = report.attempts.len() as u64;
    exact.dispatch.execution.vm.max_steps = report.completed_vm_usage.steps;
    exact.max_visits = report.tree_usage.visits;
    exact.generation.max_nodes = report.tree_usage.generated_nodes;
    exact.generation.max_bytes = report.tree_usage.generated_bytes;
    let replay = batch(&engine, &registry, &sources, exact, None);
    assert_eq!(
        succeeded(&replay).result_logical_root,
        checked.result_logical_root
    );
    for resource in ["attempts", "steps", "visits", "nodes", "bytes"] {
        let mut limits = exact;
        match resource {
            "attempts" => limits.dispatch.max_attempts -= 1,
            "steps" => limits.dispatch.execution.vm.max_steps -= 1,
            "visits" => limits.max_visits -= 1,
            "nodes" => limits.generation.max_nodes -= 1,
            "bytes" => limits.generation.max_bytes -= 1,
            _ => unreachable!(),
        }
        let stopped = batch(&engine, &registry, &sources, limits, None);
        assert!(
            matches!(stopped.outcome, Outcome::Inconclusive(_)),
            "{resource}: {stopped:?}"
        );
        assert!(stopped.state.is_none(), "{resource}");
        assert!(
            stopped.attempts.len() >= 2,
            "{resource}: the first command completed"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), before);
    }
    // Traversal work is still cumulative when no registered macro is tried.
    let plain = [
        b"def plainA : Nat := 1".as_slice(),
        b"def plainB : Nat := 2".as_slice(),
    ];
    let plain_report = batch(&engine, &registry, &plain, MacroTreeLimits::default(), None);
    succeeded(&plain_report);
    assert!(plain_report.attempts.is_empty());
    assert!(plain_report.tree_usage.visits > 0);
    let limited = MacroTreeLimits {
        max_visits: plain_report.tree_usage.visits - 1,
        ..MacroTreeLimits::default()
    };
    let stopped = batch(&engine, &registry, &plain, limited, None);
    assert!(
        matches!(stopped.outcome, Outcome::Inconclusive(_)),
        "{stopped:?}"
    );
    assert!(stopped.attempts.is_empty());
    assert!(stopped.state.is_none());
}

#[test]
fn imported_macro_batches_discard_successful_prefixes_on_false_proofs_and_diagnostics() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let prefix = b"def checkedPrefix : Nat := 7 + 11".as_slice();
    let false_proof = batch(
        &engine,
        &registry,
        &[prefix, b"example : checkedPrefix = 18 := by rfl"],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(
            &false_proof.outcome,
            Outcome::Complete(Err(SourceCheckError::Command {
                file: 1,
                command: 1,
                ..
            }))
        ),
        "{false_proof:?}"
    );
    assert_eq!(false_proof.attempts.len(), 2);
    assert!(false_proof.state.is_none());
    let diagnostic = batch(
        &engine,
        &registry,
        &[prefix, b"def bad : Nat := 7 - 11"],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(&diagnostic.outcome, Outcome::Complete(Err(SourceCheckError::ImportedMacro { file: 1, command: 1, error, .. })) if matches!(error.as_ref(), SourceMacroError::Diagnostic { message, .. } if message == "λ\0diagnostic")),
        "{diagnostic:?}"
    );
    assert_eq!(diagnostic.attempts.len(), 3);
    assert!(diagnostic.state.is_none());
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    assert!(!engine.environment().contains(&name("checkedPrefix")));
    let good = batch(
        &engine,
        &registry,
        &[
            prefix,
            b"example : checkedPrefix = 11 := by rfl\ntheorem proof : checkedPrefix = 11 := by rfl",
        ],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&good);
    assert_eq!(checked.commands, 3);
    assert_eq!(checked.theorems, 1);
    assert_eq!(
        checked.engine.environment().len(),
        engine.environment().len() + 2
    );
    assert_declared_value(&checked.engine, "checkedPrefix", 11);
    assert!(checked.engine.environment().contains(&name("proof")));
}

#[test]
fn imported_macro_batches_interleave_source_templates_without_replaying_expansions() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let source = b"syntax \"localValue\" : term\n\
        macro_rules | `(localValue) => `(11)\n\
        macro \"throughImported\" : term => `(7 + 11)\n\
        macro \"unvisited\" : term => `(0 - 0)\n\
        def nativeToImported : Nat := throughImported\n\
        def importedToNative : Nat := 7 + localValue\n\
        def outerFirst : Nat := unvisited + localValue\n\
        example : nativeToImported = 11 := by rfl\n\
        example : importedToNative = 11 := by rfl\n\
        example : outerFirst = 11 := by rfl";
    let report = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    for declaration in ["nativeToImported", "importedToNative", "outerFirst"] {
        assert_declared_value(&checked.engine, declaration, 11);
    }
    // Exactly one quoted expansion and the two registered imported candidates
    // per definition. The imported outer macro discards `unvisited` before its
    // diagnostic-producing template can run.
    assert_eq!(report.attempts.len(), 9);
    // Each of the three native rfl invocations also takes evalTactic's scope.
    assert_eq!(report.state.as_ref().unwrap().macro_scope, 29);
    assert_eq!(
        report
            .attempts
            .iter()
            .filter(|attempt| attempt
                .native_functions
                .iter()
                .any(|name| name == "source-template:quoted"))
            .count(),
        3
    );
    assert!(
        report
            .attempts
            .iter()
            .all(|attempt| attempt.declaration != name("SourceLibrary.diagnostic"))
    );
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    assert!(!engine.environment().contains(&name("nativeToImported")));
}

#[test]
fn mixed_source_rules_extend_imported_kinds_with_registration_and_clause_fallback() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let source = b"def importedBefore : Nat := 1 + 9\n\
        macro_rules | `(1 + $rhs) => `(101) | `(2 + $rhs) => `(102)\n\
        macro_rules | `(3 + $rhs) => `(103)\n\
        def firstClause : Nat := 1 + 9\n\
        def secondClause : Nat := 2 + 9\n\
        def newestRegistration : Nat := 3 + 9\n\
        def importedFallback : Nat := 4 + 9";
    let report = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    for (declaration, value) in [
        ("importedBefore", 9),
        ("firstClause", 101),
        ("secondClause", 102),
        ("newestRegistration", 103),
        ("importedFallback", 9),
    ] {
        assert_declared_value(&checked.engine, declaration, value);
    }
    // Older clauses share one registration attempt/scope. Only an unsupported
    // registration advances to the next source registration or imported body.
    assert_eq!(report.attempts.len(), 11);
    assert_eq!(report.state.as_ref().unwrap().macro_scope, 28);
    let fallback: Vec<_> = report.attempts[7..]
        .iter()
        .map(|attempt| attempt.declaration.clone())
        .collect();
    assert_eq!(fallback[2], name("SourceLibrary.skip"));
    assert_eq!(fallback[3], name("SourceLibrary.right"));
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    let retry = batch(
        &engine,
        &registry,
        &[b"def originalRegistry : Nat := 1 + 9"],
        MacroTreeLimits::default(),
        None,
    );
    assert_declared_value(&succeeded(&retry).engine, "originalRegistry", 9);
}

#[test]
fn mixed_same_kind_scopes_follow_activation_and_registration_chronology() {
    let (engine, registry) = artifact_fixture();
    let source = b"macro_rules | `(7 + 11) => `(23)\n\
        def sourceFirst : Nat := 7 + 11\n\
        section\n\
        open scoped SourceScoped\n\
        def importedLater : Nat := 7 + 11\n\
        macro_rules | `(7 + 11) => `(41)\n\
        def sourceLater : Nat := 7 + 11\n\
        open scoped SourceScoped\n\
        def repeatedActivation : Nat := 7 + 11\n\
        section\n\
        local macro_rules | `(7 + 11) => `(43)\n\
        def localFirst : Nat := 7 + 11\n\
        end\n\
        def localRestored : Nat := 7 + 11\n\
        end\n\
        def globalSurvives : Nat := 7 + 11\n\
        open scoped SourceScoped in def temporarilyImported : Nat := 7 + 11\n\
        def temporaryRestored : Nat := 7 + 11\n\
        namespace SourceScoped\n\
        scoped macro_rules | `(7 + 11) => `(53)\n\
        def scopedSourceLater : Nat := 7 + 11\n\
        end SourceScoped\n\
        def scopedSourceInactive : Nat := 7 + 11\n\
        open scoped SourceScoped\n\
        def sourceBeforeImportedWithinActivation : Nat := 7 + 11";
    let report = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    for (declaration, value) in [
        ("sourceFirst", 23),
        ("importedLater", 7),
        ("sourceLater", 41),
        ("repeatedActivation", 41),
        ("localFirst", 43),
        ("localRestored", 41),
        ("globalSurvives", 41),
        ("temporarilyImported", 7),
        ("temporaryRestored", 41),
        ("SourceScoped.scopedSourceLater", 53),
        ("scopedSourceInactive", 41),
        ("sourceBeforeImportedWithinActivation", 53),
    ] {
        assert_declared_value(&checked.engine, declaration, value);
    }
    assert_eq!(report.attempts.len(), 12);
    assert_eq!(
        report
            .attempts
            .iter()
            .filter(|attempt| { attempt.declaration == name("SourceLibrary.left") })
            .count(),
        2
    );
}

#[test]
fn mixed_source_rules_preserve_scopes_already_active_at_the_call_boundary() {
    let (engine, registry) = artifact_fixture();
    let active = registry.activate_scoped(&name("SourceScoped")).unwrap();
    let report = batch(
        &engine,
        &active,
        &[b"macro_rules | `(7 + 11) => `(23)\n\
            def sourceAfterInitialActivation : Nat := 7 + 11\n\
            open scoped SourceScoped\n\
            def stillSource : Nat := 7 + 11"],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    for declaration in ["sourceAfterInitialActivation", "stillSource"] {
        assert_declared_value(&checked.engine, declaration, 23);
    }
    assert_eq!(report.attempts.len(), 2);
}

#[test]
fn mixed_same_kind_fallback_keeps_diagnostics_budgets_and_failed_transactions() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let source = b"def checkedPrefix : Nat := 8\n\
        macro_rules | `(3 + $rhs) => `(103)\n\
        def importedFallback : Nat := 4 + 9";
    let mut limits = MacroTreeLimits::default();
    limits.dispatch.max_attempts = 1;
    let limited = batch(&engine, &registry, &[source], limits, None);
    assert!(
        matches!(limited.outcome, Outcome::Inconclusive(_)),
        "{limited:?}"
    );
    assert_eq!(limited.attempts.len(), 1);
    assert!(limited.state.is_none());
    let recovered = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    assert_declared_value(&succeeded(&recovered).engine, "importedFallback", 9);
    assert_eq!(recovered.attempts.len(), 3);

    let source = b"def checkedPrefix : Nat := 8\n\
        macro_rules | `($lhs - 7) => `(99)\n\
        def refused : Nat := 0 - 11";
    let refused = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(&refused.outcome,
        Outcome::Complete(Err(SourceCheckError::ImportedMacro { error, .. }))
            if matches!(error.as_ref(), SourceMacroError::Diagnostic { declaration, .. }
                if *declaration == name("SourceLibrary.diagnostic"))),
        "{refused:?}"
    );
    assert_eq!(refused.attempts.len(), 2);
    assert!(refused.state.is_none());

    let malformed = batch(
        &engine,
        &registry,
        &[b"def checkedPrefix : Nat := 8\n\
            macro_rules | `(1 + $rhs) => `(101)\n\
            macro_rules | `(1 + $rhs) => do pure `(102)\n\
            def mustNotFallBack : Nat := 1 + 9"],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(malformed.outcome, Outcome::Complete(Err(_))),
        "{malformed:?}"
    );
    assert!(malformed.state.is_none());
    let unsupported_macro = batch(
        &engine,
        &registry,
        &["def checkedPrefix : Nat := 8\n\
           macro (name := «term_+_») \"unsupportedAdd \" lhs:term:max rhs:term:max : term => do pure rhs\n\
           def mustNotFallBack : Nat := unsupportedAdd 1 9"
            .as_bytes()],
        MacroTreeLimits::default(),
        None,
    );
    let Outcome::Complete(Err(error)) = &unsupported_macro.outcome else {
        panic!("{unsupported_macro:?}")
    };
    assert!(
        format!("{error:?}").contains("unsupported macro declaration"),
        "{unsupported_macro:?}"
    );
    assert!(unsupported_macro.state.is_none());
    assert!(unsupported_macro.attempts.is_empty());
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    for declaration in ["checkedPrefix", "refused", "mustNotFallBack"] {
        assert!(!engine.environment().contains(&name(declaration)));
    }
}

#[test]
fn mixed_macro_batches_restore_native_and_imported_scopes_together() {
    let (engine, registry) = artifact_fixture();
    let source = b"syntax \"localValue\" : term\n\
        macro_rules | `(localValue) => `(11)\n\
        section\n\
        local macro_rules | `(localValue) => `(7)\n\
        open scoped SourceScoped\n\
        def bothScoped : Nat := localValue + 13\n\
        end\n\
        def bothRestored : Nat := 0 + localValue\n\
        namespace NativeChoice\n\
        scoped macro_rules | `(localValue) => `(19)\n\
        end NativeChoice\n\
        def inactive : Nat := 0 + localValue\n\
        open scoped NativeChoice in def activeOnce : Nat := 0 + localValue\n\
        def inactiveAgain : Nat := 0 + localValue";
    let report = batch(
        &engine,
        &registry,
        &[source, b"def nextFile : Nat := 7 + 11"],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    for (declaration, value) in [
        ("bothScoped", 7),
        ("bothRestored", 11),
        ("inactive", 11),
        ("activeOnce", 19),
        ("inactiveAgain", 11),
        ("nextFile", 11),
    ] {
        assert_declared_value(&checked.engine, declaration, value);
    }
    assert_eq!(report.attempts.len(), 16);
    assert_eq!(report.state.as_ref().unwrap().macro_scope, 33);
}

#[test]
fn mixed_macro_failures_and_exhaustion_publish_no_prefix_or_state() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let cyclic = b"def checkedPrefix : Nat := 7 + 11\n\
        syntax \"cycleValue\" : term\n\
        macro_rules | `(cycleValue) => `(cycleValue)\n\
        def cyclic : Nat := cycleValue";
    let mut limits = MacroTreeLimits::default();
    limits.dispatch.max_attempts = 5;
    let stopped = batch(&engine, &registry, &[cyclic], limits, None);
    assert!(
        matches!(stopped.outcome, Outcome::Inconclusive(_)),
        "{stopped:?}"
    );
    assert_eq!(stopped.attempts.len(), 5);
    assert!(stopped.state.is_none());

    let diagnostic = b"def checkedPrefix : Nat := 7 + 11\n\
        macro \"badValue\" : term => `(0 - 0)\n\
        def refused : Nat := 0 + badValue";
    let refused = batch(
        &engine,
        &registry,
        &[diagnostic],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(&refused.outcome,
            Outcome::Complete(Err(SourceCheckError::ImportedMacro { error, .. }))
                if matches!(error.as_ref(), SourceMacroError::Diagnostic { declaration, .. }
                    if *declaration == name("SourceLibrary.diagnostic"))),
        "{refused:?}"
    );
    assert!(refused.state.is_none());
    assert_eq!(refused.attempts.len(), 6);

    let mut limits = MacroTreeLimits::default();
    limits.generation.max_nodes = 2;
    let generated = batch(
        &engine,
        &registry,
        &[b"def checkedPrefix : Nat := 7 + 11\n\
            macro \"anotherValue\" : term => `(11)\n\
            def exceedsOutputBudget : Nat := anotherValue"],
        limits,
        None,
    );
    assert!(
        matches!(generated.outcome, Outcome::Inconclusive(_)),
        "{generated:?}"
    );
    assert!(generated.state.is_none());

    let false_proof = b"def checkedPrefix : Nat := 7 + 11\n\
        macro \"falseProof\" : term => `(by rfl)\n\
        theorem invalid : (1 : Nat) = 2 := falseProof";
    let refused = batch(
        &engine,
        &registry,
        &[false_proof],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(refused.outcome, Outcome::Complete(Err(_))),
        "{refused:?}"
    );
    assert!(refused.state.is_none());
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    assert!(!engine.environment().contains(&name("checkedPrefix")));
    assert!(!engine.environment().contains(&name("invalid")));
}

#[test]
fn mixed_templates_preserve_definition_site_names_and_caller_captures() {
    let (engine, registry) = artifact_fixture();
    let source = b"namespace DefinitionSite\n\
        def saved : Nat := 37\n\
        notation \"the_saved_value_with_a_deliberately_long_definition_span\" => saved\n\
        end DefinitionSite\n\
        macro \"chooseCaller[\" x:term \"]\" : term => `(0 + $x)\n\
        namespace Client\n\
        def saved : Nat := 99\n\
        def definitionSite : Nat := 0 + the_saved_value_with_a_deliberately_long_definition_span\n\
        def callerSite : Nat := chooseCaller[saved]\n\
        end Client";
    let report = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    assert_declared_value(&checked.engine, "Client.definitionSite", 37);
    assert_declared_value(&checked.engine, "Client.callerSite", 99);
}

#[test]
fn mixed_macro_callbacks_reenter_the_exact_source_template_snapshot() {
    let (imported, mut code) = artifact_import_fixture();
    let declaration = code
        .iter_mut()
        .flat_map(|module| &mut module.decls)
        .find(|declaration| declaration.name() == &name("SourceLibrary.right"))
        .unwrap();
    *declaration =
        super::super::recursive::recursive_function_requiring_child("SourceLibrary.right", 2);
    let registry = imported
        .prepare_imported_macros(
            &code,
            &VerifiedPartition::user_fixture(),
            &users(&code),
            MacroRegistryLimits::default(),
        )
        .unwrap();
    let report = batch(
        &imported.engine,
        &registry,
        &[b"macro \"callbackValue\" : term => `(11)\n\
            def throughCallback : Nat := 0 + callbackValue"],
        MacroTreeLimits::default(),
        None,
    );
    assert_declared_value(&succeeded(&report).engine, "throughCallback", 11);
    assert_eq!(report.attempts.len(), 3);
    assert_eq!(report.state.as_ref().unwrap().macro_scope, 20);
    assert_eq!(report.attempts[0].declaration, name("SourceLibrary.skip"));
    assert_eq!(report.attempts[1].declaration, name("SourceLibrary.right"));
    assert!(
        report.attempts[2]
            .native_functions
            .iter()
            .any(|name| name == "source-template:quoted")
    );
}

#[test]
fn mixed_term_and_tactic_templates_reach_native_consumers_once() {
    let (engine, registry) = artifact_fixture();
    let report = batch(
        &engine,
        &registry,
        &[b"macro \"nativeValue\" : term => `(0 + 11)\n\
            macro \"nativeRfl\" : tactic => `(tactic| rfl)\n\
            def mixedCommand : Nat := nativeValue\n\
            theorem fromNativeTactic : mixedCommand = 11 := by nativeRfl\n\
            theorem fromImportedTerm : (11 : Nat) = 11 := by exact (0 + (by nativeRfl))"],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    assert_declared_value(&checked.engine, "mixedCommand", 11);
    assert_eq!(checked.theorems, 2);
    assert_eq!(
        report
            .attempts
            .iter()
            .filter(|attempt| attempt
                .native_functions
                .iter()
                .any(|name| name == "source-template:quoted"))
            .count(),
        3
    );
    assert_eq!(report.attempts.len(), 7);
}

#[test]
fn mixed_macro_registration_fallback_scopes_are_distinct_from_clause_fallback() {
    let (engine, registry) = artifact_fixture();
    let source = b"syntax \"pick[\" num \"]\" : term\n\
        macro_rules | `(pick[1]) => `(11) | `(pick[2]) => `(22)\n\
        macro_rules | `(pick[3]) => `(33)\n\
        def olderClause : Nat := 0 + pick[2]\n\
        def newestClause : Nat := 0 + pick[3]";
    let report = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    assert_declared_value(&checked.engine, "olderClause", 22);
    assert_declared_value(&checked.engine, "newestClause", 33);
    // Two imported attempts + two source registrations for olderClause;
    // two imported attempts + the newest source registration for newestClause.
    assert_eq!(report.attempts.len(), 7);
    assert_eq!(report.state.as_ref().unwrap().macro_scope, 24);
}

#[test]
fn mixed_source_tactic_registrations_keep_native_proof_backtracking() {
    let (engine, registry) = artifact_fixture();
    let report = batch(
        &engine,
        &registry,
        &[b"syntax \"nativeChoice\" : tactic\n\
            macro_rules | `(tactic| nativeChoice) => `(tactic| rfl)\n\
            macro_rules | `(tactic| nativeChoice) => `(tactic| exact (0 : Nat))\n\
            theorem restoredProof : (11 : Nat) = 11 := by nativeChoice"],
        MacroTreeLimits::default(),
        None,
    );
    assert_eq!(succeeded(&report).theorems, 1);
    assert_eq!(report.attempts.len(), 2);
    // evalTactic shares its one fresh scope between registrations, while each
    // successful expansion's native tactic execution enters its own scope.
    assert_eq!(report.state.as_ref().unwrap().macro_scope, 20);
}

#[test]
fn mixed_source_templates_keep_specialized_metadata_refusals_explicit() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let report = batch(
        &engine,
        &registry,
        &[b"def checkedPrefix : Nat := 0 + 11\n\
            macro \"fromMatch \" x:term:max : term => `(match $x:term with | Nat.zero => 41 | Nat.succ n => n)\n\
            def specialized : Nat := fromMatch (0 : Nat)"],
        MacroTreeLimits::default(),
        None,
    );
    let Outcome::Complete(Err(error)) = &report.outcome else {
        panic!("{report:?}")
    };
    assert_eq!(error.disposition(), ("capability", false, 5), "{report:?}");
    assert!(
        format!("{error:?}").contains("PreresolvedReference"),
        "{report:?}"
    );
    assert!(report.state.is_none());
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    assert!(!engine.environment().contains(&name("checkedPrefix")));
    assert!(!engine.environment().contains(&name("specialized")));

    // `apply` elaborates a complete term, so its quoted declaration target
    // remains usable even when a local shadows the target's namespace.
    let accepted = batch(
        &engine,
        &registry,
        &[b"def checkedPrefix : Nat := 0 + 11\n\
            macro \"fromApply\" : term => `(by apply Eq.refl)\n\
            theorem specialized (Eq : Nat) : (0 : Nat) = 0 := fromApply"],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&accepted);
    assert_eq!(checked.theorems, 1);
    assert_declared_value(&checked.engine, "checkedPrefix", 11);
    assert!(accepted.state.is_some());
    assert!(!accepted.attempts.is_empty());
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    assert!(!engine.environment().contains(&name("checkedPrefix")));
    assert!(!engine.environment().contains(&name("specialized")));
}

#[test]
fn generated_match_terms_keep_preresolved_globals_under_local_shadowing() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let source = b"macro_rules | `(typedMatch) => `(match (20 : Nat) with | _ => (match (Nat.succ Nat.zero : Nat) with | _ => Nat.succ Nat.zero))\n\
        def generatedMatchWithShadow (Nat : Type) : _root_.Nat := typedMatch\n\
        def generatedMatchValue : Nat := generatedMatchWithShadow Bool";
    let report = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    assert_declared_value(&succeeded(&report).engine, "generatedMatchValue", 1);
    assert!(report.state.is_some());
    assert!(!report.attempts.is_empty());
    assert_eq!(engine.logical_root(&KVMap::new()), before);

    // Only complete term operands may use ordinary pre-resolution. The
    // constructor name in a pattern is still consumed by a specialized path;
    // accepting it by its visible spelling would discard its quoted target.
    let refused = batch(
        &engine,
        &registry,
        &[b"def checkedPrefix : Nat := 7\n\
            macro_rules | `(constructorPattern) => `(match (Nat.zero : Nat) with | Nat.zero => Nat.succ Nat.zero | _ => Nat.zero)\n\
            def generatedPattern : Nat := constructorPattern"],
        MacroTreeLimits::default(),
        None,
    );
    let Outcome::Complete(Err(error)) = &refused.outcome else {
        panic!("{refused:?}")
    };
    assert_eq!(error.disposition(), ("capability", false, 5), "{refused:?}");
    assert!(
        format!("{error:?}").contains("PreresolvedReference"),
        "{refused:?}"
    );
    assert!(refused.state.is_none());
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    for label in ["checkedPrefix", "generatedPattern", "generatedMatchValue"] {
        assert!(!engine.environment().contains(&name(label)));
    }
}

#[test]
fn mixed_source_syntax_registration_supersedes_an_imported_macro_of_the_same_kind() {
    let (engine, registry) =
        artifact_fixture_with_extra_rows(&[("nativeLiteral", "SourceLibrary.right", None)]);
    let before = engine.logical_root(&KVMap::new());
    let source = b"def checkedPrefix : Nat := 7 + 11\n\
        syntax (name := nativeLiteral) \"clashValue\" : term\n\
        macro_rules | `(clashValue) => `(11)\n\
        def sourceOverride : Nat := clashValue";
    let report = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    assert_declared_value(&checked.engine, "checkedPrefix", 11);
    assert_declared_value(&checked.engine, "sourceOverride", 11);
    assert_eq!(report.attempts.len(), 3);
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    assert!(!engine.environment().contains(&name("checkedPrefix")));
}

#[test]
fn mixed_imported_native_journals_still_refuse_an_unknown_cross_import_order() {
    use fln_parse::extensions::{FileGrammar, with_grammar};

    let (_, registry) =
        artifact_fixture_with_extra_rows(&[("nativeLiteral", "SourceLibrary.right", None)]);
    let mut provider = FileGrammar::new(false, &[], Some(name("TemplateProvider")))
        .unwrap()
        .own_syntax_only();
    for source in [
        "syntax (name := nativeLiteral) \"clashValue\" : term",
        "macro_rules | `(clashValue) => `(11)",
    ] {
        let command = with_grammar(&provider.grammar(), || {
            fln_parse::parse_source_command(source.as_bytes())
        })
        .unwrap();
        provider.declare(command.syntax()).unwrap();
    }
    let journal = provider.export_native().unwrap();
    let mut consumer = FileGrammar::new(false, &[], Some(name("TemplateConsumer"))).unwrap();
    consumer.import_native(&journal).unwrap();
    registry.bind_source_grammar(&mut consumer);
    let error = registry
        .with_source_templates(
            &consumer.active_template_snapshot().unwrap(),
            &name("TemplateConsumer"),
        )
        .unwrap_err();
    assert!(
        matches!(error, MacroRegistrationError::Owner { declaration, reason, .. }
            if declaration == name("nativeLiteral")
                && reason.contains("no shared registration order")),
    );
}

#[test]
fn mixed_runtime_overrides_publish_local_effects_and_refuse_unordered_global_exports() {
    let (imported, code) = artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let report = super::modules::check(
        &imported,
        &code,
        &[
            (
                "Lib",
                "prelude\nimport SourceLibrary\n\
                 macro_rules | `(7 + 11) => `(23)\n\
                 def unpublishedOverride : Nat := 7 + 11",
            ),
            (
                "Main",
                "prelude\nimport Lib\ndef unpublishedSuccessor : Nat := unpublishedOverride",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    let Outcome::Complete(Err(error)) = &report.outcome else {
        panic!("{report:?}")
    };
    assert!(
        format!("{error:?}").contains("requires shared import registration order"),
        "{report:?}"
    );
    assert_eq!(report.attempts.len(), 1);
    assert!(report.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(
        !imported
            .engine
            .environment()
            .contains(&name("unpublishedOverride"))
    );
    assert!(
        !imported
            .engine
            .environment()
            .contains(&name("unpublishedSuccessor"))
    );

    let local = super::modules::check(
        &imported,
        &code,
        &[
            (
                "Lib",
                "prelude\nimport SourceLibrary\n\
                 section\nlocal macro_rules | `(7 + 11) => `(23)\n\
                 def fromLocalOverride : Nat := 7 + 11\nend",
            ),
            (
                "Main",
                "prelude\nimport Lib\n\
                 def importedLocalResult : Nat := fromLocalOverride\n\
                 def importedMacroRestored : Nat := 7 + 11",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    let checked = super::modules::succeeded(&local);
    assert_declared_value(&checked.checked.engine, "importedLocalResult", 23);
    assert_declared_value(&checked.checked.engine, "importedMacroRestored", 11);
    assert_eq!(local.attempts.len(), 3);
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

#[test]
fn mixed_atomic_templates_expand_at_native_term_and_literal_pattern_positions() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    // These role distinctions were separately checked against the exact pin.
    // The registered artifact `+` macro still runs in the same session.
    let source = br#"
structure Holder where
  magic : Nat
structure AtomicPair where
  fst : Nat
  snd : Nat
def magic : Nat := 3
def functionMacroTarget (x : Nat) : Nat := x
section
local macro_rules | `(1) => `(11)
local macro_rules | `("source") => `(23)
local macro_rules | `('a') => `(29)
local macro_rules | `(1.5) => `(31)
local macro_rules | `(magic) => `(7)
local macro_rules | `(functionMacroTarget) => `(fun (_ : Nat) => 7)
def atomicValue : Nat := 1
def rawUniverse : Sort 1 := Nat
def rawProjection : Nat := (AtomicPair.mk (Nat.succ Nat.zero) Nat.zero).1
theorem typeArgument : Eq 1 11 := Eq.refl 11
def fromTactic : Nat := by exact 1
def fromString : Nat := "source"
def fromChar : Nat := 'a'
def fromScientific : Nat := 1.5
def binder (magic : Nat) : Nat := magic
def punned (magic : Nat) : Holder := { magic }
def fieldLabel : Nat := ({ magic := 3 } : Holder).magic
def direct : Nat := functionMacroTarget 3
def parenthesized : Nat := (functionMacroTarget) 3
def explicit : Nat := @functionMacroTarget 3
def choose : Nat -> Nat
  | 1 => 42
  | _ => 0
def artifactThenAtomic : Nat := 5 + 1
end
def binderResult : Nat := binder 5
def punnedResult : Nat := (punned 5).magic
def patternResult : Nat := choose 11
theorem patternResult_eq : Eq patternResult 42 := Eq.refl patternResult
def restored : Nat := 1
"#;
    let report = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    for (declaration, expected) in [
        ("atomicValue", 11),
        ("rawProjection", 1),
        ("fromTactic", 11),
        ("fromString", 23),
        ("fromChar", 29),
        ("fromScientific", 31),
        ("binderResult", 7),
        ("punnedResult", 7),
        ("fieldLabel", 3),
        ("direct", 3),
        ("parenthesized", 7),
        ("explicit", 3),
        ("patternResult", 42),
        ("artifactThenAtomic", 11),
        ("restored", 1),
    ] {
        assert_declared_value(&checked.engine, declaration, expected);
    }
    assert!(
        report
            .attempts
            .iter()
            .any(|attempt| attempt.declaration == name("SourceLibrary.right"))
    );
    assert!(
        report
            .attempts
            .iter()
            .any(|attempt| attempt.declaration.parent().parent() == name("_fln.sourceTemplate"))
    );
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn mixed_atomic_templates_replay_from_native_modules_with_distinct_artifact_kinds() {
    let (imported, code) = artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let report = super::modules::check(
        &imported,
        &code,
        &[
            (
                "Lib",
                "prelude\nimport SourceLibrary\n\
                 macro_rules | `(1) => `(5 + 2)\n\
                 macro_rules | `(2) => `(11)\n\
                 def fromAtomicLibrary : Nat := 1",
            ),
            (
                "Main",
                "prelude\nimport Lib\n\
                 def replayedAtomic : Nat := 1\n\
                 theorem sameAtomic : Eq replayedAtomic fromAtomicLibrary := Eq.refl replayedAtomic",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    let checked = super::modules::succeeded(&report);
    assert_declared_value(&checked.checked.engine, "fromAtomicLibrary", 11);
    assert_declared_value(&checked.checked.engine, "replayedAtomic", 11);
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

#[test]
fn mixed_atomic_generated_terms_share_macro_state_and_resource_limits() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let source = b"macro_rules | `(1) => `(5 + 2)\n\
        macro_rules | `(2) => `(11)\n\
        def generated : Nat := 1";
    let report = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    assert_declared_value(&succeeded(&report).engine, "generated", 11);
    let mut exact = MacroTreeLimits::default();
    exact.dispatch.max_attempts = report.attempts.len() as u64;
    exact.dispatch.execution.vm.max_steps = report.completed_vm_usage.steps;
    exact.max_visits = report.tree_usage.visits;
    exact.generation.max_nodes = report.tree_usage.generated_nodes;
    exact.generation.max_bytes = report.tree_usage.generated_bytes;
    let replay = batch(&engine, &registry, &[source], exact, None);
    assert_eq!(replay.state, report.state);
    assert_eq!(
        succeeded(&replay).result_logical_root,
        succeeded(&report).result_logical_root
    );
    for resource in ["attempts", "steps", "visits", "nodes", "bytes"] {
        let mut limits = exact;
        match resource {
            "attempts" => limits.dispatch.max_attempts -= 1,
            "steps" => limits.dispatch.execution.vm.max_steps -= 1,
            "visits" => limits.max_visits -= 1,
            "nodes" => limits.generation.max_nodes -= 1,
            "bytes" => limits.generation.max_bytes -= 1,
            _ => unreachable!(),
        }
        let stopped = batch(&engine, &registry, &[source], limits, None);
        assert!(
            matches!(stopped.outcome, Outcome::Inconclusive(_)),
            "{resource}: {stopped:?}"
        );
        assert!(stopped.state.is_none());
    }
    for source in [
        b"macro_rules | `(1) => `(1)\ndef loop : Nat := 1".as_slice(),
        b"macro_rules | `(1) => `(1)\ndef loop : Nat -> Nat | 1 => 7 | _ => 0".as_slice(),
    ] {
        let mut limits = MacroTreeLimits::default();
        limits.dispatch.max_attempts = 5;
        let stopped = batch(&engine, &registry, &[source], limits, None);
        assert!(
            matches!(stopped.outcome, Outcome::Inconclusive(_)),
            "{stopped:?}"
        );
        assert!(stopped.state.is_none());
    }
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn mixed_atomic_patterns_compile_constructor_replacements_and_generated_children() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let report = batch(
        &engine,
        &registry,
        &[br#"
def magic : Nat := 3
section
local macro_rules | `(1) => `(_root_.Nat.succ _root_.Nat.zero)
local macro_rules | `(2) => `(_root_.Nat.succ 1)
local macro_rules | `(magic) => `(7)
def choose : Nat -> Nat
  | 1 => 41
  | 2 => 42
  | magic => magic
end
def first : Nat := choose 1
def second : Nat := choose 2
def fallback : Nat := choose 8
theorem firstChecked : Eq first 41 := Eq.refl first
theorem secondChecked : Eq second 42 := Eq.refl second
theorem fallbackChecked : Eq fallback 7 := Eq.refl fallback
"#],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    for (declaration, value) in [("first", 41), ("second", 42), ("fallback", 7)] {
        assert_declared_value(&checked.engine, declaration, value);
    }
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn mixed_atomic_patterns_compile_records_and_named_constructor_fields() {
    let (engine, registry) = artifact_fixture();
    let report = batch(
        &engine,
        &registry,
        &[br#"
structure PatternBox where
  value : Nat
  tag : Nat
inductive PatternChoice where
  | left (value : Nat)
  | right
section
local macro_rules | `('a') => `({ value := _root_.Nat.zero, tag := _ })
local macro_rules | `("left") => `(_root_.PatternChoice.left (value := _root_.Nat.zero))
local macro_rules | `("yes") => `(_root_.Bool.true)
def recordChoice : PatternBox -> Nat
  | 'a' => 41
  | _ => 42
def namedChoice : PatternChoice -> Nat
  | "left" => 43
  | _ => 44
def boolChoice : Bool -> Nat
  | "yes" => 45
  | false => 46
end
def recordHit : Nat := recordChoice { value := 0, tag := 5 }
def recordMiss : Nat := recordChoice { value := 1, tag := 5 }
def namedHit : Nat := namedChoice (.left 0)
def namedMiss : Nat := namedChoice (.left 2)
def boolHit : Nat := boolChoice true
def boolMiss : Nat := boolChoice false
"#],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    for (declaration, value) in [
        ("recordHit", 41),
        ("recordMiss", 42),
        ("namedHit", 43),
        ("namedMiss", 44),
        ("boolHit", 45),
        ("boolMiss", 46),
    ] {
        assert_declared_value(&checked.engine, declaration, value);
    }
}

#[test]
fn mixed_atomic_constructor_patterns_replay_from_native_module_journals() {
    let (imported, code) = artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let report = super::modules::check(
        &imported,
        &code,
        &[
            (
                "Lib",
                "prelude\nimport SourceLibrary\n\
                 macro_rules | `(1) => `(_root_.Nat.succ _root_.Nat.zero)\n\
                 def libraryChoice : Nat -> Nat | 1 => 42 | _ => 0",
            ),
            (
                "Main",
                "prelude\nimport Lib\n\
                 def clientChoice : Nat -> Nat | 1 => 43 | _ => 0\n\
                 def libraryHit : Nat := libraryChoice (Nat.succ Nat.zero)\n\
                 def clientHit : Nat := clientChoice (Nat.succ Nat.zero)\n\
                 theorem checkedLibrary : Eq libraryHit 42 := Eq.refl libraryHit\n\
                 theorem checkedClient : Eq clientHit 43 := Eq.refl clientHit",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    let checked = super::modules::succeeded(&report);
    assert_declared_value(&checked.checked.engine, "libraryHit", 42);
    assert_declared_value(&checked.checked.engine, "clientHit", 43);
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

#[test]
fn mixed_atomic_generated_pattern_trees_share_the_batch_budget_and_recover() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let source = br#"
def checkedPrefix : Nat := 5 + 7
macro_rules | `(1) => `(_root_.Nat.succ (_root_.Nat.succ _root_.Nat.zero))
def choose : Nat -> Nat | 1 => 42 | _ => 0
def result : Nat := choose (Nat.succ (Nat.succ Nat.zero))
"#;
    let report = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    assert_declared_value(&succeeded(&report).engine, "result", 42);
    assert!(report.completed_vm_usage.steps > 0, "{report:?}");
    let mut exact = MacroTreeLimits::default();
    exact.dispatch.max_attempts = report.attempts.len() as u64;
    exact.dispatch.execution.vm.max_steps = report.completed_vm_usage.steps;
    exact.max_visits = report.tree_usage.visits;
    exact.generation.max_nodes = report.tree_usage.generated_nodes;
    exact.generation.max_bytes = report.tree_usage.generated_bytes;
    for resource in ["attempts", "steps", "visits", "nodes", "bytes"] {
        let mut limits = exact;
        match resource {
            "attempts" => limits.dispatch.max_attempts -= 1,
            "steps" => limits.dispatch.execution.vm.max_steps -= 1,
            "visits" => limits.max_visits -= 1,
            "nodes" => limits.generation.max_nodes -= 1,
            "bytes" => limits.generation.max_bytes -= 1,
            _ => unreachable!(),
        }
        let stopped = batch(&engine, &registry, &[source], limits, None);
        assert!(
            matches!(stopped.outcome, Outcome::Inconclusive(_)),
            "{resource}: {stopped:?}"
        );
        assert!(stopped.state.is_none());
        assert_eq!(engine.logical_root(&KVMap::new()), before);
        assert!(!engine.environment().contains(&name("checkedPrefix")));
    }
    let recovered = batch(&engine, &registry, &[source], exact, None);
    assert_eq!(recovered.state, report.state);
    assert_eq!(
        succeeded(&recovered).result_logical_root,
        succeeded(&report).result_logical_root
    );
}

#[test]
fn mixed_atomic_patterns_reject_invalid_generated_patterns_without_publishing_a_prefix() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    for replacement in ["Nat.add Nat.zero Nat.zero", "Bool.true", "fun x => x"] {
        let source = format!(
            "def checkedPrefix : Nat := 5 + 7\n\
             macro_rules | `(1) => `({replacement})\n\
             def invalid : Nat -> Nat | 1 => 7 | _ => 0"
        );
        let report = batch(
            &engine,
            &registry,
            &[source.as_bytes()],
            MacroTreeLimits::default(),
            None,
        );
        assert!(
            matches!(report.outcome, Outcome::Complete(Err(_))),
            "{replacement}: {report:?}"
        );
        assert!(report.state.is_none());
        assert_eq!(engine.logical_root(&KVMap::new()), before);
        assert!(!engine.environment().contains(&name("checkedPrefix")));
    }
}

#[test]
fn mixed_atomic_pattern_chains_obey_the_macro_recursion_bound() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let context = MacroContext {
        max_recursion_depth: 20,
        ..context()
    };
    let mut limits = MacroTreeLimits::default();
    limits.dispatch.max_attempts = 1000;
    let report = engine.check_source_files_with_imported_macros(
        &[b"macro_rules | `(1) => `(1)\n\
            def patternLoop (n : Nat) : Nat := match n with | 1 => 7 | _ => 0"],
        &KVMap::new(),
        SourceCheckLimits::new(admission()),
        SourceMacroInvocation {
            registry: &registry,
            context: &context,
            state: MacroState::default(),
            lookup: None,
            limits,
            cancellation: None,
        },
    );
    let Outcome::Inconclusive(reason) = &report.outcome else {
        panic!("{report:?}")
    };
    assert!(
        matches!(&reason.cause,
        fln_core::outcome::InconclusiveCause::ResourceExhausted { usage }
            if matches!(usage.reason, fln_core::diag::ResourceReason::RecursionDepth { limit: 20 })
                && usage.allowed == 20 && usage.observed == 21),
        "{report:?}"
    );
    assert!(!report.attempts.is_empty() && report.attempts.len() < 1000);
    assert!(report.state.is_none());
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn generated_atomic_pattern_chains_count_the_outer_owned_expansion() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let context = MacroContext {
        max_recursion_depth: 20,
        ..context()
    };
    let mut source =
        String::from("macro_rules | `(outerTerm) => `(match (20 : Nat) with | 1 => 42 | _ => 0)\n");
    for value in 1..20 {
        source.push_str(&format!("macro_rules | `({value}) => `({})\n", value + 1));
    }
    source.push_str("def generatedPattern : Nat := outerTerm");
    let report = engine.check_source_files_with_imported_macros(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(admission()),
        SourceMacroInvocation {
            registry: &registry,
            context: &context,
            state: MacroState::default(),
            lookup: None,
            limits: MacroTreeLimits::default(),
            cancellation: None,
        },
    );
    let Outcome::Inconclusive(reason) = &report.outcome else {
        panic!("{report:?}")
    };
    assert!(
        matches!(&reason.cause,
        fln_core::outcome::InconclusiveCause::ResourceExhausted { usage }
            if matches!(usage.reason, fln_core::diag::ResourceReason::RecursionDepth { limit: 20 })
                && usage.allowed == 20 && usage.observed == 21),
        "{report:?}"
    );
    assert!(report.state.is_none());
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    assert!(!engine.environment().contains(&name("generatedPattern")));

    // With enough depth, the same generated discriminant type and literal
    // pattern chain must elaborate and reduce. The resource result above is
    // not allowed to mask a metadata refusal or leave the provider unusable.
    let recovered_context = MacroContext {
        max_recursion_depth: 128,
        ..context
    };
    let recovered = engine.check_source_files_with_imported_macros(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(admission()),
        SourceMacroInvocation {
            registry: &registry,
            context: &recovered_context,
            state: MacroState::default(),
            lookup: None,
            limits: MacroTreeLimits::default(),
            cancellation: None,
        },
    );
    assert_declared_value(&succeeded(&recovered).engine, "generatedPattern", 42);
    assert!(recovered.state.is_some());
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    assert!(!engine.environment().contains(&name("generatedPattern")));
}

#[test]
fn mixed_atomic_generated_diagnostics_keep_the_imported_failure_and_rollback() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let report = batch(
        &engine,
        &registry,
        &[b"def checkedPrefix : Nat := 5 + 7\n\
            macro_rules | `(1) => `(5 - 2)\n\
            def failure : Nat := 1"],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(report.outcome, Outcome::Complete(Err(_))),
        "{report:?}"
    );
    assert!(
        report
            .attempts
            .iter()
            .any(|attempt| attempt.declaration == name("SourceLibrary.diagnostic"))
    );
    assert!(
        format!("{:?}", report.outcome).contains("Diagnostic"),
        "{report:?}"
    );
    assert!(report.state.is_none());
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    assert!(!engine.environment().contains(&name("checkedPrefix")));
}

#[test]
fn generic_macro_tree_expansion_still_dispatches_atomic_nodes() {
    let kinds = ["num", "str", "char", "scientific", "name"];
    let rows: Vec<_> = kinds
        .iter()
        .map(|kind| (*kind, "SourceLibrary.diagnostic", None))
        .collect();
    let (_, registry) = artifact_fixture_with_extra_rows(&rows);
    for (kind, token) in kinds
        .into_iter()
        .zip(["1", "\"source\"", "'a'", "1.5", "`Nat"])
    {
        let source = SourceText::from_utf8(token.as_bytes()).unwrap();
        let mut syntax = Syntax::node(name(kind), vec![Syntax::atom(SourceInfo::None, token)]);
        if kind == "name" {
            syntax = Syntax::node(name("Lean.Parser.Term.quotedName"), vec![syntax]);
        }
        let raw = registry.expand_tree(
            &syntax,
            &source,
            &context(),
            MacroState::default(),
            MacroTreeLimits::default(),
            None,
        );
        assert!(matches!(
            raw.outcome,
            Outcome::Complete(Ok(MacroTreeResult::Error { .. }))
        ));
        assert_eq!(raw.attempts.len(), 1);
        let source_pass = registry.expand_source_tree_with_context(
            &syntax,
            MacroDispatchInvocation {
                source: &source,
                context: &context(),
                state: MacroState::default(),
                lookup: None,
            },
            MacroTreeLimits::default(),
            None,
        );
        assert!(matches!(source_pass.outcome,
            Outcome::Complete(Ok(MacroTreeResult::Expanded { syntax: preserved, .. })) if preserved == syntax));
        assert!(source_pass.attempts.is_empty());
    }
}

#[test]
fn mixed_atomic_templates_require_an_owned_provider_for_borrowed_sessions() {
    struct NeverCancelled;
    impl CancellationProbe for NeverCancelled {
        fn is_cancelled(&self) -> bool {
            false
        }
    }
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let source = b"def checkedPrefix : Nat := 5 + 7\n\
        macro_rules | `(1) => `(11)\n\
        def atomicValue : Nat := 1";
    let main_module = name("Main");
    let namespace = Name::anonymous();
    let lookup = crate::imported_macros::lookup::EnvironmentMacroLookup::new(
        engine.environment(),
        &main_module,
        &namespace,
        &[],
        &[],
    );
    for borrowed_lookup in [false, true] {
        let report = engine.check_source_files_with_imported_macros(
            &[source],
            &KVMap::new(),
            SourceCheckLimits::new(admission()),
            SourceMacroInvocation {
                registry: &registry,
                context: &context(),
                state: MacroState::default(),
                lookup: borrowed_lookup.then_some(&lookup as &dyn MacroLookup),
                limits: MacroTreeLimits::default(),
                cancellation: (!borrowed_lookup)
                    .then_some(&NeverCancelled as &dyn CancellationProbe),
            },
        );
        assert!(
            matches!(&report.outcome,
            Outcome::Complete(Err(SourceCheckError::ImportedMacro { error, .. }))
                    if matches!(error.as_ref(), SourceMacroError::AtomicExpansion { kind }
                        if *kind == name("num"))),
            "{report:?}"
        );
        assert!(report.state.is_none());
        assert_eq!(engine.logical_root(&KVMap::new()), before);
        assert!(!engine.environment().contains(&name("checkedPrefix")));
    }
}

#[test]
fn mixed_grammar_declarations_and_controls_respect_active_atomic_boundaries() {
    let (engine, registry) = artifact_fixture_with_extra_rows(&[(
        "ident",
        "SourceLibrary.diagnostic",
        Some("SourceAtoms"),
    )]);
    let before = engine.logical_root(&KVMap::new());
    let inactive = batch(
        &engine,
        &registry,
        &[b"macro \"dormantValue\" : term => `(11)\n\
            def fromInactive : Nat := 0 + dormantValue"],
        MacroTreeLimits::default(),
        None,
    );
    assert_declared_value(&succeeded(&inactive).engine, "fromInactive", 11);

    for (tail, declaration) in [
        ("macro \"blockedValue\" : term => `(11)", true),
        ("variable (x : Nat)", false),
    ] {
        let source = format!("def checkedPrefix : Nat := 7 + 11\nopen scoped SourceAtoms\n{tail}");
        let report = batch(
            &engine,
            &registry,
            &[source.as_bytes()],
            MacroTreeLimits::default(),
            None,
        );
        let Outcome::Complete(Err(SourceCheckError::ImportedMacro { error, .. })) = &report.outcome
        else {
            panic!("active atomic declaration/control boundary was not refused");
        };
        assert_eq!(error.disposition(), ("capability", false, 5));
        assert!(
            matches!(error.as_ref(), SourceMacroError::SyntaxDeclaration { kind }
                if declaration && *kind == name("ident"))
                || matches!(error.as_ref(), SourceMacroError::AtomicExpansion { kind }
                    if !declaration && *kind == name("ident")),
            "{error:?}"
        );
        assert_eq!(report.attempts.len(), 2);
        assert!(report.state.is_none());
        assert_eq!(engine.logical_root(&KVMap::new()), before);
        assert!(!engine.environment().contains(&name("checkedPrefix")));
    }
}

#[test]
fn imported_macro_batches_expand_variable_types_and_restore_variable_in_scopes() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let source = "-- λ🦀\r\nsection Outer\r\n\
        variable (x : Nat + Bool)\r\n\
        def fromBool : Bool := x\r\n\
        section\r\nopen scoped SourceScoped\r\n\
        variable (y : Nat + Bool)\r\n\
        def fromNat : Nat := y\r\n\
        def originalBool : Bool := x\r\nend\r\nend Outer\r\n\
        variable (z : Nat + Bool) in\r\ndef oneCommand : Bool := z\r\n\
        def afterIn : Nat := 7 + 11\r\n";
    let report = batch(
        &engine,
        &registry,
        &[source.as_bytes()],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    for (expression, value) in [
        ("fromBool true", 1),
        ("fromNat 7", 7),
        ("originalBool false", 0),
        ("oneCommand true", 1),
        ("afterIn", 11),
    ] {
        assert_declared_value(&checked.engine, expression, value);
    }
    assert!(checked.scope.variables.is_empty());
    assert_eq!(report.attempts.len(), 7);
    assert_eq!(report.state.as_ref().unwrap().macro_scope, 24);
    assert_eq!(engine.logical_root(&KVMap::new()), before);

    let escaped = batch(
        &engine,
        &registry,
        &[b"variable (z : Nat + Bool) in\ndef oneCommand : Bool := z\ndef escaped : Bool := z"],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(escaped.outcome, Outcome::Complete(Err(_))),
        "{escaped:?}"
    );
    assert_eq!(escaped.attempts.len(), 2);
    assert!(escaped.state.is_none());
    assert!(!engine.environment().contains(&name("oneCommand")));
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn imported_macro_batches_dispatch_the_complete_variable_command_and_preserve_its_shape() {
    let kind = "Lean.Parser.Command.variable";
    let source = b"variable (x : Nat + Bool)\ndef wouldPass : Bool := x";
    let (engine, registry) =
        artifact_fixture_with_extra_rows(&[(kind, "SourceLibrary.diagnostic", None)]);
    let before = engine.logical_root(&KVMap::new());
    let diagnosed = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(&diagnosed.outcome, Outcome::Complete(Err(SourceCheckError::ImportedMacro { error, .. }))
            if matches!(error.as_ref(), SourceMacroError::Diagnostic { reference, message, .. }
                if reference.kind() == Some(&name(kind)) && message == "λ\0diagnostic")),
        "{diagnosed:?}"
    );
    assert_eq!(diagnosed.attempts.len(), 1);
    assert_eq!(
        diagnosed.attempts[0].declaration,
        name("SourceLibrary.diagnostic")
    );
    assert!(diagnosed.state.is_none());
    assert!(!engine.environment().contains(&name("wouldPass")));
    assert_eq!(engine.logical_root(&KVMap::new()), before);

    let (engine, registry) =
        artifact_fixture_with_extra_rows(&[(kind, "SourceLibrary.skip", None)]);
    let declined = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    assert_declared_value(&succeeded(&declined).engine, "wouldPass true", 1);
    assert_eq!(declined.attempts.len(), 3);
    assert_eq!(declined.state.as_ref().unwrap().macro_scope, 20);

    // Selecting argument 2 of a two-argument variable command returns missing
    // syntax. It must not be interpreted as an empty or successful telescope.
    let (engine, registry) =
        artifact_fixture_with_extra_rows(&[(kind, "SourceLibrary.right", None)]);
    let malformed = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(&malformed.outcome, Outcome::Complete(Err(SourceCheckError::ImportedMacro { error, .. }))
            if matches!(error.as_ref(), SourceMacroError::ScopeControl { kind: actual } if actual == &name(kind))),
        "{malformed:?}"
    );
    assert_eq!(malformed.attempts.len(), 1);
    assert!(malformed.state.is_none());
    assert!(!engine.environment().contains(&name("wouldPass")));
}

#[test]
fn imported_macro_batches_refuse_active_native_scope_roots_instead_of_ignoring_them() {
    for (kind, source) in [
        (
            "Lean.Parser.Command.namespace",
            "namespace Client\ndef wouldPass : Nat := 7 + 11\nend Client",
        ),
        (
            "Lean.Parser.Command.open",
            "open scoped SourceScoped\ndef wouldPass : Nat := 7 + 11",
        ),
        (
            "Lean.Parser.Command.open",
            "open scoped SourceScoped in\ndef wouldPass : Nat := 7 + 11",
        ),
        (
            "Lean.Parser.Command.openScoped",
            "open scoped SourceScoped\ndef wouldPass : Nat := 7 + 11",
        ),
        (
            "Lean.Parser.Command.openScoped",
            "open scoped SourceScoped in\ndef wouldPass : Nat := 7 + 11",
        ),
        (
            "Lean.Parser.Command.openSimple",
            "open SourceScoped\ndef wouldPass : Nat := 7 + 11",
        ),
        (
            "Lean.Parser.Command.openOnly",
            "open Nat (succ)\ndef wouldPass : Nat := 7 + 11",
        ),
        (
            "Lean.Parser.Command.in",
            "open scoped SourceScoped in\ndef wouldPass : Nat := 7 + 11",
        ),
        (
            "Lean.Parser.Command.in",
            "variable (x : Nat + Bool) in\ndef wouldPass : Bool := x",
        ),
        (
            "Lean.Parser.Command.set_option",
            "set_option maxRecDepth 1024\ndef wouldPass : Nat := 7 + 11",
        ),
        (
            "Lean.Parser.Command.set_option",
            "set_option maxRecDepth 1024 in\ndef wouldPass : Nat := 7 + 11",
        ),
        (
            "num",
            "set_option maxRecDepth 1024\ndef wouldPass : Nat := 7 + 11",
        ),
        (
            "num",
            "set_option maxRecDepth 1024 in\ndef wouldPass : Nat := 7 + 11",
        ),
        // This string option is a parser fixture, not an admitted option row.
        // Its active syntax macro must be refused before native option policy.
        (
            "str",
            "set_option o \"text\"\ndef wouldPass : Nat := 7 + 11",
        ),
        (
            "str",
            "set_option o \"text\" in\ndef wouldPass : Nat := 7 + 11",
        ),
        (
            "false",
            "set_option autoLift false in\ndef wouldPass : Nat := 7 + 11",
        ),
    ] {
        let (engine, registry) =
            artifact_fixture_with_extra_rows(&[(kind, "SourceLibrary.diagnostic", None)]);
        let before = engine.logical_root(&KVMap::new());
        let refused = batch(
            &engine,
            &registry,
            &[source.as_bytes()],
            MacroTreeLimits::default(),
            None,
        );
        let Outcome::Complete(Err(error)) = &refused.outcome else {
            panic!("{kind}: {refused:?}")
        };
        assert!(
            matches!(error, SourceCheckError::ImportedMacro { error, .. }
                if matches!(error.as_ref(), SourceMacroError::ScopeControl { kind: actual } if actual == &name(kind))),
            "{kind}: {refused:?}"
        );
        assert_eq!(error.disposition(), ("capability", false, 5));
        assert!(refused.attempts.is_empty());
        assert!(refused.state.is_none());
        assert_eq!(engine.logical_root(&KVMap::new()), before);
        assert!(!engine.environment().contains(&name("wouldPass")));
        assert!(!engine.environment().contains(&name("Client.wouldPass")));
    }
}

#[test]
fn imported_macro_batches_expand_executable_attributes_before_validating_their_effects() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let source = b"axiom original : Bool + Nat\n\
        def replacement : Nat := 23\n\
        attribute [implemented_by replacement] original";
    let report = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    // The root macro runs, declines replacement, and leaves a real attribute
    // command to validate. Its work/state cannot disappear at the control seam.
    assert_eq!(report.attempts.len(), 3);
    assert_eq!(
        report.attempts[2].declaration,
        name("SourceLibrary.attributeProbe")
    );
    assert_eq!(report.state.as_ref().unwrap().macro_scope, 20);
    assert_eq!(
        fln_elab::implemented_by::ImplementedByTable::read(checked.engine.environment())
            .unwrap()
            .get(&name("original")),
        Some(&name("replacement")),
    );
    assert_declared_value(&checked.engine, "original", 23);
    assert_eq!(engine.logical_root(&KVMap::new()), before);

    let invalid = batch(
        &engine,
        &registry,
        &[b"axiom original : Bool + Nat\ndef replacement : Bool := true\nattribute [implemented_by replacement] original"],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(invalid.outcome, Outcome::Complete(Err(_))),
        "{invalid:?}"
    );
    assert_eq!(invalid.attempts.len(), 3);
    assert!(invalid.state.is_none());
    assert!(!engine.environment().contains(&name("original")));
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn imported_macro_batches_expand_mutual_signatures_and_bodies_before_atomic_admission() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let source = "-- λ🦀\n\
        namespace Group\nmutual\n  def first : Bool + Nat := 3 + second\n  def second : Bool + Nat := 7 + 11\n\
        end\nexample : first = 11 := by rfl\nend Group\n"
        .replace('\n', "\r\n");
    let report = batch(
        &engine,
        &registry,
        &[source.as_bytes()],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    assert_declared_value(&checked.engine, "Group.first", 11);
    assert_declared_value(&checked.engine, "Group.second", 11);
    assert_eq!(report.attempts.len(), 8);
    // The native rfl after the mutual block also enters evalTactic's fresh scope.
    assert_eq!(report.state.as_ref().unwrap().macro_scope, 17 + 8 + 1);
    assert_eq!(engine.logical_root(&KVMap::new()), before);

    let invalid = batch(
        &engine,
        &registry,
        &[br"def checkedPrefix : Nat := 5
mutual
  def first : Bool + Nat := 3 + second
  def second : Bool + Nat := 7 + true
end"],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(invalid.outcome, Outcome::Complete(Err(_))),
        "{invalid:?}"
    );
    assert_eq!(invalid.attempts.len(), 8);
    assert!(invalid.state.is_none());
    for declaration in ["checkedPrefix", "first", "second"] {
        assert!(!engine.environment().contains(&name(declaration)));
    }
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn imported_macro_batches_expand_mutually_inductive_constructor_types() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let source = br"mutual
  inductive MacroTree where
    | leaf (value : Bool + Nat)
    | node (children : MacroForest)
  inductive MacroForest where
    | nil
    | cons (tag : Bool + Nat) (head : MacroTree) (tail : MacroForest)
end
def unpack (tree : MacroTree) : Nat := match tree with
  | MacroTree.leaf n => n
  | MacroTree.node _ => 0
example : unpack (MacroTree.leaf 11) = 11 := by rfl
";
    let report = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    for declaration in ["MacroTree", "MacroForest"] {
        assert!(
            matches!(checked.engine.environment().find(&name(declaration)),
            Some(ConstantInfo::Induct(info)) if info.all.len() == 2)
        );
        assert!(
            matches!(checked.engine.environment().find(&name(&format!("{declaration}.rec"))),
            Some(ConstantInfo::Rec(info)) if info.num_motives == 2)
        );
    }
    assert_declared_value(&checked.engine, "unpack (MacroTree.leaf 11)", 11);
    assert_eq!(report.attempts.len(), 4);
    // Four macro attempts plus the example's native rfl each allocate a scope.
    assert_eq!(report.state.as_ref().unwrap().macro_scope, 17 + 4 + 1);
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn imported_macro_controls_and_mutual_members_share_one_budget() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let source = br"variable (x : Bool + Nat)
axiom checkedPrefix : Bool + Nat
def replacement : Nat := 13
attribute [implemented_by replacement] checkedPrefix
mutual
  def first : Bool + Nat := 3 + second
  def second : Bool + Nat := 7 + 11
end";
    let report = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    assert_eq!(report.attempts.len(), 13);
    assert_eq!(report.state.as_ref().unwrap().macro_scope, 30);
    assert_declared_value(&checked.engine, "first", 11);
    assert_declared_value(&checked.engine, "checkedPrefix", 13);
    let mut exact = MacroTreeLimits::default();
    exact.dispatch.max_attempts = report.attempts.len() as u64;
    exact.dispatch.execution.vm.max_steps = report.completed_vm_usage.steps;
    exact.max_visits = report.tree_usage.visits;
    exact.generation.max_nodes = report.tree_usage.generated_nodes;
    exact.generation.max_bytes = report.tree_usage.generated_bytes;
    let replay = batch(&engine, &registry, &[source], exact, None);
    assert_eq!(
        succeeded(&replay).result_logical_root,
        checked.result_logical_root
    );
    for resource in ["attempts", "steps", "visits", "nodes", "bytes"] {
        let mut limits = exact;
        match resource {
            "attempts" => limits.dispatch.max_attempts -= 1,
            "steps" => limits.dispatch.execution.vm.max_steps -= 1,
            "visits" => limits.max_visits -= 1,
            "nodes" => limits.generation.max_nodes -= 1,
            "bytes" => limits.generation.max_bytes -= 1,
            _ => unreachable!(),
        }
        let stopped = batch(&engine, &registry, &[source], limits, None);
        assert!(
            matches!(stopped.outcome, Outcome::Inconclusive(_)),
            "{resource}: {stopped:?}"
        );
        assert!(
            stopped.attempts.len() >= 5,
            "{resource}: controls and prefix completed"
        );
        assert!(stopped.state.is_none());
        assert_eq!(engine.logical_root(&KVMap::new()), before);
        for declaration in ["checkedPrefix", "replacement", "first", "second"] {
            assert!(!engine.environment().contains(&name(declaration)));
        }
    }
}

#[test]
fn imported_macro_batches_cancel_after_a_checked_prefix_without_returning_its_state() {
    struct Polls {
        count: Cell<usize>,
        stop_at: usize,
    }
    impl CancellationProbe for Polls {
        fn is_cancelled(&self) -> bool {
            let count = self.count.get() + 1;
            self.count.set(count);
            count >= self.stop_at
        }
    }
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let prefix = b"def checkedPrefix : Nat := 7 + 11".as_slice();
    let counter = Polls {
        count: Cell::new(0),
        stop_at: usize::MAX,
    };
    let first = batch(
        &engine,
        &registry,
        &[prefix],
        MacroTreeLimits::default(),
        Some(&counter),
    );
    succeeded(&first);
    let cancellation = Polls {
        count: Cell::new(0),
        stop_at: counter.count.get() + 2,
    };
    let stopped = batch(
        &engine,
        &registry,
        &[prefix, b"def suffix : Nat := 13 + 17"],
        MacroTreeLimits::default(),
        Some(&cancellation),
    );
    assert!(
        matches!(stopped.outcome, Outcome::Inconclusive(_)),
        "{stopped:?}"
    );
    assert!(stopped.attempts.len() >= first.attempts.len());
    assert!(stopped.completed_vm_usage.steps >= first.completed_vm_usage.steps);
    assert!(stopped.state.is_none());
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    assert!(!engine.environment().contains(&name("checkedPrefix")));
    let recovered = batch(
        &engine,
        &registry,
        &[prefix, b"def suffix : Nat := 13 + 17"],
        MacroTreeLimits::default(),
        None,
    );
    assert_declared_value(&succeeded(&recovered).engine, "suffix", 17);
    assert_eq!(recovered.state.as_ref().unwrap().macro_scope, 21);
}
