//! Custom imported commands cross the real parser, macro VM and checker.
//!
//! The library is constructed and independently admitted, not Reference parity
//! evidence. Canonical declaration shapes come from the native parser itself;
//! the IR selects that parsed child without printing, reparsing or inventing
//! runtime layouts. Parentheses keep the nested command within one command slice.
use super::*;
use crate::source_check::SourceCheckError;
use crate::source_check::modules::SourceModuleCheckError;
use fln_core::name::LeafView;

#[derive(Clone, Copy, Debug)]
enum Payload {
    BuiltinCommand,
    Definition,
    PublicDefinition,
    Theorem,
    Example,
    Check,
    Namespace,
    Container,
}

fn structural_name(value: &Name) -> Expr {
    match value.leaf_view() {
        LeafView::Anonymous => constant("Lean.Name.anonymous"),
        LeafView::Str(component) => apply(
            "Lean.Name.str",
            [structural_name(&value.parent()), string(component)],
        ),
        LeafView::Num(component) => apply(
            "Lean.Name.num",
            [structural_name(&value.parent()), natural(component)],
        ),
    }
}

fn sequence(parts: impl IntoIterator<Item = Expr>) -> Expr {
    let mut parts = parts.into_iter();
    let Some(first) = parts.next() else {
        return apply("Lean.ParserDescr.const", [literal_name("ppSpace")]);
    };
    parts.fold(first, |left, right| {
        apply(
            "Lean.ParserDescr.binary",
            [literal_name("andthen"), left, right],
        )
    })
}

fn symbol(value: &str) -> Expr {
    apply("Lean.ParserDescr.symbol", [string(value)])
}

fn syntax_description(syntax: &Syntax) -> Expr {
    match syntax {
        Syntax::Node { kind, args, .. } => apply(
            "Lean.ParserDescr.node",
            [
                structural_name(kind),
                natural(1022),
                sequence(args.iter().map(syntax_description)),
            ],
        ),
        Syntax::Atom { val, .. } => symbol(val),
        Syntax::Ident { val, .. } if *val == name("TYPE") || *val == name("VALUE") => {
            apply("Lean.ParserDescr.cat", [literal_name("term"), natural(0)])
        }
        Syntax::Ident { val, .. } if *val == name("TARGET") => {
            apply("Lean.ParserDescr.const", [literal_name("ident")])
        }
        Syntax::Ident { .. } => panic!("the canonical template has an unmarked identifier"),
        Syntax::Missing => panic!("the canonical template must be completely parsed"),
    }
}

fn payload_description(payload: Payload) -> Expr {
    if matches!(payload, Payload::BuiltinCommand) {
        return apply(
            "Lean.ParserDescr.cat",
            [literal_name("command"), natural(0)],
        );
    }
    if matches!(payload, Payload::Namespace) {
        let syntax = fln_parse::command_scope::trees::tree(b"namespace TARGET")
            .unwrap()
            .unwrap();
        return syntax_description(&syntax);
    }
    let source = match payload {
        Payload::Definition | Payload::Container => "def TARGET : TYPE := VALUE",
        Payload::PublicDefinition => "public def TARGET : TYPE := VALUE",
        Payload::Theorem => "theorem TARGET : TYPE := VALUE",
        Payload::Example => "example : TYPE := VALUE",
        Payload::Check => "#check VALUE",
        Payload::BuiltinCommand | Payload::Namespace => unreachable!(),
    };
    let parsed = fln_parse::parse_source_command(source.as_bytes()).unwrap();
    let description = syntax_description(parsed.syntax());
    if matches!(payload, Payload::Container) {
        apply(
            "Lean.ParserDescr.node",
            [literal_name("null"), natural(1022), description],
        )
    } else {
        description
    }
}

fn command_rows(kind: &str, declaration: &str, token: &str, namespace: Option<&str>) -> Vec<Obj> {
    vec![
        scope(
            Obj::mk_ctor(wire::PARSER_ENTRY_TOKEN, vec![Obj::mk_string(token)], &[]),
            namespace,
        ),
        scope(
            Obj::mk_ctor(wire::PARSER_ENTRY_KIND, vec![inject_name(&name(kind))], &[]),
            None,
        ),
        scope(
            Obj::mk_ctor(
                wire::PARSER_ENTRY_PARSER,
                vec![
                    inject_name(&name("command")),
                    inject_name(&name(declaration)),
                    Obj::mk_nat(1000),
                ],
                &[],
            ),
            namespace,
        ),
    ]
}

fn command_fixture(payload: Payload, selected: Option<u64>) -> (SourceOleanImport, Vec<IrModule>) {
    let mut constants = Vec::new();
    for declaration in crate::imported_parsers::fixture_declarations() {
        match declaration {
            crate::Declaration::Inductive(block) => {
                constants.extend(block.types.into_iter().map(ConstantInfo::Induct));
                constants.extend(block.ctors.into_iter().map(ConstantInfo::Ctor));
                constants.extend(block.recursors.into_iter().map(ConstantInfo::Rec));
            }
            crate::Declaration::Defn(value) => constants.push(ConstantInfo::Defn(value)),
            _ => panic!("fixed parser datatype fixture"),
        }
    }
    let payload = payload_description(payload);
    let mut rows = Vec::new();
    for (kind, declaration, token, namespace) in [
        (
            "SourceLibrary.declare",
            "SourceLibrary.commandParser",
            "declare!",
            None,
        ),
        (
            "SourceLibrary.scopedDeclare",
            "SourceLibrary.scopedCommandParser",
            "scopedDeclare!",
            Some("SourceCommands"),
        ),
    ] {
        let description = apply(
            "Lean.ParserDescr.node",
            [
                literal_name(kind),
                natural(1022),
                sequence([symbol(token), symbol("("), payload.clone(), symbol(")")]),
            ],
        );
        constants.push(definition(
            declaration,
            constant(wire::PARSER_DESCR_TYPE),
            description,
        ));
        rows.extend(command_rows(kind, declaration, token, namespace));
    }
    let mut body = natural(0);
    for binder in ["state", "context", "syntax"] {
        body = Expr::lam(name(binder), constant("Nat"), body, BinderInfo::Default);
    }
    constants.push(definition(
        "SourceLibrary.commandMacro",
        constant("Lean.Macro"),
        body,
    ));
    let registrations = selected.map(|_| {
        [
            ("SourceLibrary.declare", "SourceLibrary.commandMacro", None),
            (
                "SourceLibrary.scopedDeclare",
                "SourceLibrary.commandMacro",
                Some("SourceCommands"),
            ),
        ]
    });
    let ir = selected.map(|index| selecting_function("SourceLibrary.commandMacro", index));
    let (mut imported, code) = batches::artifact_import_fixture_with_parser_metadata(
        registrations.as_ref().map_or(&[], |rows| rows.as_slice()),
        &constants,
        &rows,
        ir.as_slice(),
    );
    imported
        .enable_imported_syntax(&[name("SourceLibrary")], ParserRegistryLimits::default())
        .unwrap();
    (imported, code)
}

#[test]
fn imported_custom_commands_admit_named_declarations_between_ordinary_commands() {
    let (imported, code) = command_fixture(Payload::Definition, Some(2));
    let before = imported.engine.logical_root(&KVMap::new());
    let report = check(
        &imported,
        &code,
        &[(
            "Main",
            "prelude\nimport SourceLibrary\n\
            def before : Nat := 7\n\
            declare! (def first : Nat := 41)\n\
            declare! (def second : Nat := 42)\n\
            def after : Nat := second\n\
            theorem verified : first = 41 := by rfl",
        )],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    for (declaration, value) in [("before", 7), ("first", 41), ("second", 42), ("after", 42)] {
        assert_declared_value(&checked.checked.engine, declaration, value);
    }
    assert!(
        checked
            .checked
            .engine
            .environment()
            .contains(&name("verified"))
    );
    assert_eq!(
        report.attempts.len(),
        2,
        "each imported command expands once"
    );
    assert!(
        report
            .attempts
            .iter()
            .all(|attempt| attempt.declaration == name("SourceLibrary.commandMacro"))
    );
    assert_eq!(
        report.states.as_ref().unwrap()[&name("Main")].macro_scope,
        19
    );
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(!imported.engine.environment().contains(&name("first")));
}

#[test]
fn imported_custom_command_declarations_reach_program_execution() {
    let (imported, code) = command_fixture(Payload::Definition, Some(2));
    let declarations = users(&code);
    let compilation =
        MacroCompilationInputs::new(code, VerifiedPartition::user_fixture(), declarations);
    let report = execute_graph(
        &imported,
        compilation,
        &[(
            "Main",
            "prelude\nimport SourceLibrary\n\
            declare! (def chosen : Nat := 42)\n#eval chosen",
        )],
        crate::source_check::modules::execution::SourceProgramLimits::new(execution_limits()),
        MacroRegistryLimits::default(),
        None,
    );
    let Outcome::Complete(Ok(program)) = &report.outcome else {
        panic!("{report:?}")
    };
    let batch = &program.modules[0].commands.batch;
    assert_eq!(batch.source_evaluation_indices.len(), 1);
    let index = batch.source_evaluation_indices[0];
    assert_eq!(
        crate::closed_vm_value(&batch.executions[index].exit)
            .unwrap()
            .unwrap(),
        crate::ClosedVmValue::Scalar(42)
    );
    assert_eq!(report.attempts.len(), 1);
    assert!(report.completed_vm_usage.steps > 0);
    assert!(report.states.is_some());
}

#[test]
fn builtin_command_operands_reenter_the_imported_grammar_with_original_source_positions() {
    let (imported, code) = command_fixture(Payload::BuiltinCommand, Some(2));
    let source = "prelude\r\nimport SourceLibrary\r\n\
        declare! (declare! (def chosen : Nat := 42))\r\n\
        def copied : Nat := chosen";
    let report = check(
        &imported,
        &code,
        &[("Main", source)],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    assert_declared_value(&checked.checked.engine, "chosen", 42);
    assert_declared_value(&checked.checked.engine, "copied", 42);
    assert_eq!(report.attempts.len(), 2);
    assert_eq!(
        report.states.as_ref().unwrap()[&name("Main")].macro_scope,
        19
    );

    let declarations = users(&code);
    let compilation =
        MacroCompilationInputs::new(code, VerifiedPartition::user_fixture(), declarations);
    let source = format!("{source}\r\n#eval copied");
    let executed = execute_graph(
        &imported,
        compilation,
        &[("Main", &source)],
        crate::source_check::modules::execution::SourceProgramLimits::new(execution_limits()),
        MacroRegistryLimits::default(),
        None,
    );
    let Outcome::Complete(Ok(program)) = &executed.outcome else {
        panic!("{executed:?}")
    };
    let batch = &program.modules[0].commands.batch;
    assert_eq!(batch.source_evaluation_indices.len(), 1);
    let index = batch.source_evaluation_indices[0];
    assert_eq!(
        crate::closed_vm_value(&batch.executions[index].exit)
            .unwrap()
            .unwrap(),
        crate::ClosedVmValue::Scalar(42)
    );
    assert_eq!(executed.attempts.len(), 2);
    assert!(executed.completed_vm_usage.steps > 0);
    assert!(executed.states.is_some());
}

#[test]
fn custom_command_scopes_restore_and_do_not_escape_source_modules() {
    let (imported, code) = command_fixture(Payload::Definition, Some(2));
    let before = imported.engine.logical_root(&KVMap::new());
    let report = check(
        &imported,
        &code,
        &[
            (
                "Main",
                "prelude\nimport Library\ndeclare! (def next : Nat := inside)",
            ),
            (
                "Library",
                "prelude\nimport SourceLibrary\nsection\nopen scoped SourceCommands\n\
            scopedDeclare! (def inside : Nat := 17)\nend\n\
            declare! (def afterScope : Nat := 19)",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    for (declaration, value) in [("inside", 17), ("afterScope", 19), ("next", 17)] {
        assert_declared_value(&checked.checked.engine, declaration, value);
    }
    for source in [
        "prelude\nimport SourceLibrary\nscopedDeclare! (def unavailable : Nat := 1)",
        "prelude\nimport SourceLibrary\nsection\nopen scoped SourceCommands\nscopedDeclare! (def priorValue : Nat := 1)\nend\nscopedDeclare! (def unavailable : Nat := 2)",
    ] {
        let failed = check(
            &imported,
            &code,
            &[("Main", source)],
            MacroTreeLimits::default(),
            None,
        );
        assert!(
            matches!(failed.outcome, Outcome::Complete(Err(_))),
            "{failed:?}"
        );
        assert!(failed.states.is_none());
    }
    let isolated = check(
        &imported,
        &code,
        &[
            (
                "Main",
                "prelude\nimport Library\nscopedDeclare! (def unavailable : Nat := 2)",
            ),
            (
                "Library",
                "prelude\nimport SourceLibrary\nopen scoped SourceCommands\nscopedDeclare! (def available : Nat := 1)",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(isolated.outcome, Outcome::Complete(Err(_))),
        "{isolated:?}"
    );
    assert!(isolated.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

#[test]
fn custom_command_result_must_be_one_named_declaration() {
    for (payload, inner) in [
        (Payload::Example, "example : Nat := 0"),
        (Payload::Check, "#check Nat"),
        (Payload::Namespace, "namespace Hidden"),
        (Payload::Container, "def nested : Nat := 0"),
    ] {
        let (imported, code) = command_fixture(payload, Some(2));
        let before = imported.engine.logical_root(&KVMap::new());
        let source =
            format!("prelude\nimport SourceLibrary\ndef priorValue : Nat := 7\ndeclare! ({inner})");
        let report = check(
            &imported,
            &code,
            &[("Main", &source)],
            MacroTreeLimits::default(),
            None,
        );
        assert!(
            matches!(report.outcome, Outcome::Complete(Err(_))),
            "{report:?}"
        );
        assert_eq!(
            report.attempts.len(),
            1,
            "{payload:?}: the actual macro result must be refused: {report:?}"
        );
        assert!(report.states.is_none());
        assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
        assert!(!imported.engine.environment().contains(&name("priorValue")));
    }
    // An atom is valid Syntax, but is not a declaration. This crosses syntax
    // conversion successfully and must still fail the command-result boundary.
    let (imported, code) = command_fixture(Payload::Definition, Some(0));
    let report = check(
        &imported,
        &code,
        &[(
            "Main",
            "prelude\nimport SourceLibrary\ndeclare! (def discarded : Nat := 0)",
        )],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(report.outcome, Outcome::Complete(Err(_))),
        "{report:?}"
    );
    assert_eq!(report.attempts.len(), 1);
    assert!(report.states.is_none());
}

#[test]
fn generated_false_theorem_still_crosses_kernel_checking_and_rolls_back() {
    let (imported, code) = command_fixture(Payload::Theorem, Some(2));
    let before = imported.engine.logical_root(&KVMap::new());
    let good = check(
        &imported,
        &code,
        &[(
            "Main",
            "prelude\nimport SourceLibrary\ndeclare! (theorem good : 1 = 1 := by rfl)",
        )],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        succeeded(&good)
            .checked
            .engine
            .environment()
            .contains(&name("good"))
    );
    let bad = check(
        &imported,
        &code,
        &[(
            "Main",
            "prelude\nimport SourceLibrary\ndef priorValue : Nat := 7\ndeclare! (theorem bad : 0 = 1 := by rfl)",
        )],
        MacroTreeLimits::default(),
        None,
    );
    assert!(matches!(bad.outcome, Outcome::Complete(Err(_))), "{bad:?}");
    assert_eq!(bad.attempts.len(), 1, "{bad:?}");
    assert!(bad.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(!imported.engine.environment().contains(&name("bad")));
    assert!(!imported.engine.environment().contains(&name("priorValue")));
}

#[test]
fn a_command_parser_without_an_active_macro_cannot_grant_declaration_authority() {
    let (imported, code) = command_fixture(Payload::Definition, None);
    let before = imported.engine.logical_root(&KVMap::new());
    let report = check(
        &imported,
        &code,
        &[(
            "Main",
            "prelude\nimport SourceLibrary\ndeclare! (def unauthorized : Nat := 42)",
        )],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(report.outcome, Outcome::Complete(Err(_))),
        "{report:?}"
    );
    assert!(report.attempts.is_empty());
    assert!(report.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

#[test]
fn custom_command_errors_keep_the_original_file_byte_offset() {
    let (imported, code) = command_fixture(Payload::Definition, Some(2));
    let source = "prelude\r\nimport SourceLibrary\r\ndef α : Nat := 1\r\ndeclare! (def bad : Nat := unavailable)";
    let report = check(
        &imported,
        &code,
        &[("Main", source)],
        MacroTreeLimits::default(),
        None,
    );
    let Outcome::Complete(Err(SourceModuleCheckError::Source { error, .. })) = &report.outcome
    else {
        panic!("{report:?}")
    };
    let offset = match error {
        SourceCheckError::ImportedMacro { offset, .. }
        | SourceCheckError::Command { offset, .. } => *offset,
        _ => panic!("unexpected error: {error:?}"),
    };
    assert_eq!(offset, source.find("declare!").unwrap());
    assert_eq!(report.attempts.len(), 1);
    assert!(report.states.is_none());
}

#[test]
fn module_export_routing_uses_the_expanded_command_declaration() {
    let (imported, code) = command_fixture(Payload::PublicDefinition, Some(2));
    let report = check(
        &imported,
        &code,
        &[
            (
                "Main",
                "prelude\nimport Api\nnoncomputable def copied : Nat := visible",
            ),
            (
                "Api",
                "module\nprelude\npublic import SourceLibrary\ndeclare! (public def visible : Nat := 17)",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    assert!(
        checked
            .checked
            .engine
            .environment()
            .contains(&name("visible"))
    );
    assert!(
        checked
            .checked
            .engine
            .environment()
            .contains(&name("copied"))
    );
    assert_eq!(report.attempts.len(), 1);
    let (imported, code) = command_fixture(Payload::Definition, Some(2));
    let report = check(
        &imported,
        &code,
        &[
            (
                "Main",
                "prelude\nimport Api\ndef unavailable : Nat := hidden",
            ),
            (
                "Api",
                "module\nprelude\npublic import SourceLibrary\ndeclare! (def hidden : Nat := 17)",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(report.outcome, Outcome::Complete(Err(_))),
        "{report:?}"
    );
    assert_eq!(report.attempts.len(), 1);
    assert!(report.states.is_none());
}
