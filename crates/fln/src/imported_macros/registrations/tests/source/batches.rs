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
    let mut constants = vec![definition(
        "Lean.Macro",
        Expr::sort(Level::zero().succ().unwrap()),
        macro_type,
    )];
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
    let total_bytes = bytes.len() + dependency_bytes.as_ref().map_or(0, Vec::len);
    let imported = seed
        .import_olean_modules_for_source(
            &inputs,
            std::slice::from_ref(&module),
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(total_bytes, admission().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
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
    (imported, code(declarations))
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
fn imported_macro_batches_refuse_source_templates_without_replaying_native_expansion() {
    let (engine, registry) = artifact_fixture();
    let before = engine.logical_root(&KVMap::new());
    let source = b"def checkedPrefix : Nat := 7 + 11\n\
        syntax \"localValue\" : term\n\
        macro_rules | `(localValue) => `(11)\n\
        def templated : Nat := localValue";
    let refused = batch(
        &engine,
        &registry,
        &[source],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(&refused.outcome, Outcome::Complete(Err(SourceCheckError::ImportedMacro { error, .. })) if matches!(error.as_ref(), SourceMacroError::TemplateGrammar)),
        "{refused:?}"
    );
    assert_eq!(refused.attempts.len(), 2);
    assert!(refused.state.is_none());
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    assert!(!engine.environment().contains(&name("checkedPrefix")));
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
