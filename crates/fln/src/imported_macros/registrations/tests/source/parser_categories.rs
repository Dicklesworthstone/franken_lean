//! Complete category journals cross artifact admission, parser reconstruction,
//! macro execution and the kernel. The constructed inputs below are integration
//! witnesses, not a claim of Reference-produced artifact or expansion parity.
use super::modules::{check, succeeded};
use super::parser_imports::{apply, constant, definition, literal_name, natural, scope, string};
use super::*;
use crate::imported_parsers::{ParserRegistrationError, ParserRegistryLimits};
use crate::source_check::modules::imported::SourceOleanImport;
use fln_core::expr::BinderInfo;
use fln_core::level::Level;
use fln_elab::inductive::{ConstructorSpec, InductiveSpec, inductive_declaration};
use fln_elab::records::RecordBudget;

use crate::imported_parsers::test_wire as wire;

#[derive(Clone, Copy)]
enum Quoter {
    Complete,
    Missing,
    Malformed,
}

fn append_declaration(constants: &mut Vec<ConstantInfo>, declaration: crate::Declaration) {
    match declaration {
        crate::Declaration::Inductive(block) => {
            constants.extend(block.types.into_iter().map(ConstantInfo::Induct));
            constants.extend(block.ctors.into_iter().map(ConstantInfo::Ctor));
            constants.extend(block.recursors.into_iter().map(ConstantInfo::Rec));
        }
        crate::Declaration::Defn(value) => constants.push(ConstantInfo::Defn(value)),
        _ => panic!("category fixture contains only data families and safe definitions"),
    }
}

fn category_family() -> crate::Declaration {
    // Init/Notation.lean defines `meta structure Parser.Category` inside Lean:
    // a genuine zero-field type with the constructor Lean.Parser.Category.mk.
    // Generate that family and let ordinary artifact admission check it.
    inductive_declaration(
        &InductiveSpec {
            name: name("Lean.Parser.Category"),
            level_params: vec![],
            parameters: vec![],
            indices: vec![],
            constructors: vec![ConstructorSpec {
                name: name("mk"),
                fields: vec![],
                result_indices: vec![],
            }],
            result_level: Level::one(),
        },
        RecordBudget::default(),
    )
    .unwrap()
}

fn sequence(left: Expr, right: Expr) -> Expr {
    apply(
        "Lean.ParserDescr.binary",
        [literal_name("andthen"), left, right],
    )
}

fn symbol(token: &str) -> Expr {
    apply("Lean.ParserDescr.symbol", [string(token)])
}

fn category(label: &str, precedence: u64) -> Expr {
    apply(
        "Lean.ParserDescr.cat",
        [literal_name(label), natural(precedence)],
    )
}

fn node(kind: &str, body: Expr) -> Expr {
    apply(
        "Lean.ParserDescr.node",
        [literal_name(kind), natural(1024), body],
    )
}

fn parser(category: &str, declaration: &str) -> Obj {
    scope(
        Obj::mk_ctor(
            wire::PARSER_ENTRY_PARSER,
            vec![
                inject_name(&name(category)),
                inject_name(&name(declaration)),
                Obj::mk_nat(1000),
            ],
            &[],
        ),
        None,
    )
}

fn select_path_function(label: &str, path: &[u64]) -> IrDecl {
    let mut declaration = function(label, Behavior::Identity);
    let IrDecl::Function { body, .. } = &mut declaration else {
        unreachable!()
    };
    body.stmts.clear();
    let mut selected = 0;
    let mut next = 3;
    for &index in path {
        body.stmts
            .push(bind(next, IrExpr::Lit(IrLit::Num(IrNat::Small(index)))));
        body.stmts.push(bind(
            next + 1,
            IrExpr::Fap {
                function: name("Lean.Syntax.getArg"),
                args: vec![IrArg::Var(selected), IrArg::Var(next)],
            },
        ));
        selected = next + 1;
        next += 2;
    }
    body.stmts.push(bind(
        next,
        ctor(layout::RESULT_OK, "EStateM.Result.ok", &[selected, 2]),
    ));
    *body.terminal = IrTerminal::Ret(IrArg::Var(next));
    declaration
}

fn fixture(quoter: Quoter) -> (SourceOleanImport, Vec<IrModule>) {
    let mut constants = Vec::new();
    for declaration in crate::imported_parsers::fixture_declarations() {
        append_declaration(&mut constants, declaration);
    }
    append_declaration(&mut constants, category_family());
    constants.push(definition(
        "Lean.Parser.Category.artifactData",
        constant("Lean.Parser.Category"),
        constant("Lean.Parser.Category.mk"),
    ));

    let quote_kind = if matches!(quoter, Quoter::Malformed) {
        "wrongCategory.quot"
    } else {
        "artifactData.quot"
    };
    constants.extend([
        definition(
            "SourceLibrary.datum",
            constant(wire::PARSER_DESCR_TYPE),
            node(
                "SourceLibrary.datum",
                sequence(
                    symbol("datum%"),
                    apply("Lean.ParserDescr.const", [literal_name("num")]),
                ),
            ),
        ),
        definition(
            "SourceLibrary.useDatum",
            constant(wire::PARSER_DESCR_TYPE),
            node(
                "SourceLibrary.useDatum",
                sequence(
                    symbol("useDatum%"),
                    sequence(category("artifactData", 0), symbol("endDatum%")),
                ),
            ),
        ),
        definition(
            "SourceLibrary.quoteDatum",
            constant(wire::PARSER_DESCR_TYPE),
            node(
                "SourceLibrary.quoteDatum",
                sequence(
                    symbol("quoteDatum%"),
                    sequence(category("term", 1024), symbol("endQuote%")),
                ),
            ),
        ),
        definition(
            "artifactData.quot",
            constant(wire::PARSER_DESCR_TYPE),
            // Exact declareSyntaxCatQuotParser shape in Lean/Elab/Syntax.lean,
            // including the opening symbol's pretty-printing space.
            node(
                "Lean.Parser.Term.quot",
                node(
                    quote_kind,
                    sequence(
                        symbol("`(artifactData| "),
                        sequence(category("artifactData", 0), symbol(")")),
                    ),
                ),
            ),
        ),
    ]);
    for owner in [
        "SourceLibrary.useDatumMacro",
        "SourceLibrary.quoteDatumMacro",
    ] {
        let mut value = natural(0);
        for binder in ["state", "context", "syntax"] {
            value = Expr::lam(name(binder), constant("Nat"), value, BinderInfo::Default);
        }
        constants.push(definition(owner, constant("Lean.Macro"), value));
    }

    let mut rows = vec![scope(
        Obj::mk_ctor(
            wire::PARSER_ENTRY_CATEGORY,
            vec![
                inject_name(&name("artifactData")),
                inject_name(&name("Lean.Parser.Category.artifactData")),
            ],
            &[wire::PARSER_IDENT_DEFAULT],
        ),
        None,
    )];
    for token in [
        "datum%",
        "useDatum%",
        "endDatum%",
        "quoteDatum%",
        "endQuote%",
        "`(artifactData|",
    ] {
        rows.push(scope(
            Obj::mk_ctor(wire::PARSER_ENTRY_TOKEN, vec![Obj::mk_string(token)], &[]),
            None,
        ));
    }
    for kind in [
        "SourceLibrary.datum",
        "SourceLibrary.useDatum",
        "SourceLibrary.quoteDatum",
        "artifactData.quot",
        "Lean.Parser.Term.quot",
    ] {
        rows.push(scope(
            Obj::mk_ctor(wire::PARSER_ENTRY_KIND, vec![inject_name(&name(kind))], &[]),
            None,
        ));
    }
    if !matches!(quoter, Quoter::Missing) {
        rows.push(parser("term", "artifactData.quot"));
    }
    rows.extend([
        parser("artifactData", "SourceLibrary.datum"),
        parser("term", "SourceLibrary.useDatum"),
        parser("term", "SourceLibrary.quoteDatum"),
    ]);
    batches::artifact_import_fixture_with_parser_metadata(
        &[
            (
                "SourceLibrary.useDatum",
                "SourceLibrary.useDatumMacro",
                None,
            ),
            (
                "SourceLibrary.quoteDatum",
                "SourceLibrary.quoteDatumMacro",
                None,
            ),
        ],
        &constants,
        &rows,
        &[
            select_path_function("SourceLibrary.useDatumMacro", &[1, 1]),
            select_path_function("SourceLibrary.quoteDatumMacro", &[1, 0, 1, 1]),
        ],
    )
}

const DECLARATIONS: &str = "prelude\nimport SourceLibrary\n\
    def categoryValue : Nat := useDatum% datum% 47 endDatum%\n\
    theorem category_ok : categoryValue = 47 := by rfl\n\
    def quotationValue : Nat := quoteDatum% `(artifactData| datum% 51) endQuote%\n\
    theorem quotation_ok : quotationValue = 51 := by rfl";

#[test]
fn checked_category_and_quotation_journals_drive_macro_values_and_kernel_proofs() {
    let (mut imported, code) = fixture(Quoter::Complete);
    let before = imported.engine.logical_root(&KVMap::new());
    imported
        .enable_imported_syntax(&[name("SourceLibrary")], ParserRegistryLimits::default())
        .unwrap();
    let report = check(
        &imported,
        &code,
        &[("Main", DECLARATIONS)],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    assert_declared_value(&checked.checked.engine, "categoryValue", 47);
    assert_declared_value(&checked.checked.engine, "quotationValue", 51);
    for theorem in ["category_ok", "quotation_ok"] {
        assert!(
            checked
                .checked
                .engine
                .environment()
                .contains(&name(theorem))
        );
    }
    assert_eq!(report.attempts.len(), 2);
    assert_eq!(
        report.attempts[0].declaration,
        name("SourceLibrary.useDatumMacro")
    );
    assert_eq!(
        report.attempts[1].declaration,
        name("SourceLibrary.quoteDatumMacro")
    );
    assert!(report.completed_vm_usage.steps > 0);

    let false_proof =
        format!("{DECLARATIONS}\ntheorem false_quotation : quotationValue = 47 := by rfl");
    let refused = check(
        &imported,
        &code,
        &[("Main", &false_proof)],
        MacroTreeLimits::default(),
        None,
    );
    assert!(matches!(refused.outcome, Outcome::Complete(Err(_))));
    assert_eq!(refused.attempts.len(), 2);
    assert!(refused.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(
        !imported
            .engine
            .environment()
            .contains(&name("categoryValue"))
    );
    assert!(
        !imported
            .engine
            .environment()
            .contains(&name("quotationValue"))
    );
}

#[test]
fn imported_category_quotation_executes_direct_evaluation_with_deferred_macros() {
    let (mut imported, code) = fixture(Quoter::Complete);
    let before = imported.engine.logical_root(&KVMap::new());
    imported
        .enable_imported_syntax(&[name("SourceLibrary")], ParserRegistryLimits::default())
        .unwrap();
    let declarations = users(&code);
    let compilation =
        MacroCompilationInputs::new(code, VerifiedPartition::user_fixture(), declarations);
    let run = |source: &str| {
        let module = name("Main");
        imported.execute_source_modules_with_deferred_imported_macros(
            &[crate::SourceModuleInput {
                name: &module,
                source: source.as_bytes(),
            }],
            &module,
            &KVMap::new(),
            crate::source_check::modules::execution::SourceProgramLimits::new(execution_limits()),
            crate::source_check::modules::SourceModuleDeferredMacroInputs {
                compilation: compilation.clone(),
                registry_limits: MacroRegistryLimits::default(),
                context: context(),
                state: MacroState {
                    macro_scope: 17,
                    ..MacroState::default()
                },
                limits: MacroTreeLimits::default(),
            },
            None,
            crate::EvaluationPresentation::Raw,
        )
    };
    let source = format!(
        "{DECLARATIONS}\n#eval categoryValue\n\
         #eval quoteDatum% `(artifactData| datum% 53) endQuote%"
    );
    let report = run(&source);
    let Outcome::Complete(Ok(program)) = &report.outcome else {
        panic!("{report:?}");
    };
    let batch = &program.modules[0].commands.batch;
    let values: Vec<_> = batch
        .source_evaluation_indices
        .iter()
        .map(|&index| {
            crate::closed_vm_value(&batch.executions[index].exit)
                .unwrap()
                .unwrap()
        })
        .collect();
    assert_eq!(
        values,
        [
            crate::ClosedVmValue::Scalar(47),
            crate::ClosedVmValue::Scalar(53)
        ]
    );
    assert_eq!(report.attempts.len(), 3);
    assert!(report.states.is_some());

    let malformed = format!("{source}\n#eval quoteDatum% `(artifactData| datum% 53 54) endQuote%");
    let refused = run(&malformed);
    assert!(matches!(refused.outcome, Outcome::Complete(Err(_))));
    assert!(refused.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(
        !imported
            .engine
            .environment()
            .contains(&name("categoryValue"))
    );
}

#[test]
fn category_and_token_rows_cannot_replace_a_missing_or_malformed_quotation_parser() {
    let (mut missing, code) = fixture(Quoter::Missing);
    let before = missing.engine.logical_root(&KVMap::new());
    missing
        .enable_imported_syntax(&[name("SourceLibrary")], ParserRegistryLimits::default())
        .unwrap();
    let ordinary = check(
        &missing,
        &code,
        &[(
            "Main",
            "prelude\nimport SourceLibrary\ndef categoryValue : Nat := useDatum% datum% 47 endDatum%",
        )],
        MacroTreeLimits::default(),
        None,
    );
    assert_declared_value(&succeeded(&ordinary).checked.engine, "categoryValue", 47);
    let quoted = check(
        &missing,
        &code,
        &[(
            "Main",
            "prelude\nimport SourceLibrary\ndef quotationValue : Nat := quoteDatum% `(artifactData| datum% 51) endQuote%",
        )],
        MacroTreeLimits::default(),
        None,
    );
    assert!(matches!(quoted.outcome, Outcome::Complete(Err(_))));
    assert!(quoted.attempts.is_empty());
    assert!(quoted.states.is_none());
    assert_eq!(missing.engine.logical_root(&KVMap::new()), before);

    let (mut malformed, code) = fixture(Quoter::Malformed);
    let before = malformed.engine.logical_root(&KVMap::new());
    let error = malformed
        .enable_imported_syntax(&[name("SourceLibrary")], ParserRegistryLimits::default())
        .unwrap_err();
    assert!(matches!(error, ParserRegistrationError::Description { .. }));
    assert!(!error.is_resource(), "{error}");
    let refused = check(
        &malformed,
        &code,
        &[("Main", DECLARATIONS)],
        MacroTreeLimits::default(),
        None,
    );
    assert!(matches!(refused.outcome, Outcome::Complete(Err(_))));
    assert!(refused.attempts.is_empty());
    assert!(refused.states.is_none());
    assert_eq!(malformed.engine.logical_root(&KVMap::new()), before);
}
