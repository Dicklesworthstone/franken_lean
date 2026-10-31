//! The pinned compiler must preserve the noinline MacroM helper call carrying
//! the native context, and the native execution must match the pin's result.
use super::*;
use crate::imported_macros::MacroExecutionError;
use fln_syntax::source::SourceInfo;
use std::path::PathBuf;
use std::process::Command;

#[test]
fn live_pinned_macro_context_forwarding_matches_reference_and_refuses_method_escape() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for macro context forwarding"
        );
        eprintln!("SKIP: macro context forwarding requires FLN_REFERENCE_LEAN");
        return;
    };
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(
        String::from_utf8(version.stdout).unwrap().trim(),
        fln_olean::format::PIN_COMMIT
    );
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!(
        "context-forwarding-{}-{unique}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let fixture = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../fln-olean/fixtures/ir/NativeContextForwardingModule.lean"
    ));
    std::fs::write(dir.join("NativeContextForwardingModule.lean"), fixture).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args([
            "-o",
            "NativeContextForwardingModule.olean",
            "NativeContextForwardingModule.lean",
        ])
        .output()
        .unwrap();
    std::fs::write(dir.join("compile.stdout"), &generated.stdout).unwrap();
    std::fs::write(dir.join("compile.stderr"), &generated.stderr).unwrap();
    assert!(
        generated.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&generated.stdout),
        String::from_utf8_lossy(&generated.stderr)
    );
    let mut module = crate::decode_ir_artifact(
        &std::fs::read(dir.join("NativeContextForwardingModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    std::fs::write(dir.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    let users = module
        .decls
        .iter()
        .filter_map(|declaration| match declaration {
            IrDecl::Function { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    let entry = name("forwardedContextMacro");
    let compiled = compile(
        std::slice::from_ref(&module),
        &entry,
        &VerifiedPartition::user_fixture(),
        &users,
        IrExecutionLimits::default(),
    )
    .unwrap_or_else(|error| panic!("{entry:?}: {error}; {dir:?}"));
    assert!(
        compiled
            .callable()
            .reference_functions()
            .iter()
            .any(|function| function.name == name("helperContextRef")),
        "the pin must preserve the actual helper, rather than inline away forwarding"
    );
    let input = Syntax::Atom {
        info: SourceInfo::None,
        val: "input".into(),
    };
    let state = MacroState::default();
    let report = compiled.execute(
        &input,
        &SourceText::from_utf8(b"").unwrap(),
        &MacroContext {
            quotation_context: name("Test"),
            current_macro_scope: 17,
            current_recursion_depth: 3,
            max_recursion_depth: 512,
        },
        &state,
        MacroLimits::default(),
        None,
    );
    let Outcome::Complete(Ok(MacroResult::Expanded {
        syntax,
        state: actual,
    })) = report.outcome
    else {
        panic!("{report:?}; {dir:?}")
    };
    assert_eq!(
        syntax,
        Syntax::node(name("forwarded"), vec![input.clone(), input])
    );
    assert_eq!(actual, state);

    std::fs::write(dir.join("Oracle.lean"), format!("{fixture}\n{ORACLE}")).unwrap();
    let oracle = Command::new(&reference)
        .current_dir(&dir)
        .arg("Oracle.lean")
        .output()
        .unwrap();
    std::fs::write(dir.join("oracle.stdout"), &oracle.stdout).unwrap();
    std::fs::write(dir.join("oracle.stderr"), &oracle.stderr).unwrap();
    assert!(
        oracle.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&oracle.stdout),
        String::from_utf8_lossy(&oracle.stderr)
    );
    assert_eq!(oracle.stdout, b"true\n", "{dir:?}");
    assert!(oracle.stderr.is_empty());

    // A real imported helper now requests the forbidden opaque field. The
    // call edge remains unchanged, so only interprocedural confinement can
    // distinguish this from the safe compiled helper above.
    let mut changed = false;
    for declaration in &mut module.decls {
        if let IrDecl::Function {
            name: helper,
            params,
            body,
            ..
        } = declaration
            && *helper == name("helperContextRef")
        {
            for statement in &mut body.stmts {
                if let IrStmt::VDecl {
                    expr: IrExpr::Proj { i, x },
                    ..
                } = statement
                    && *x == params[0].x
                    && *i == 5
                {
                    *i = layout::MACRO_CONTEXT_METHODS_FIELD;
                    changed = true;
                }
            }
        }
    }
    assert!(
        changed,
        "negative control must reach the pin's context projection"
    );
    assert!(matches!(
        compile(
            &[module],
            &entry,
            &VerifiedPartition::user_fixture(),
            &users,
            IrExecutionLimits::default()
        ),
        Err(MacroExecutionError::Compile(
            IrExecutionError::Unsupported {
                form: OBSERVATION,
                ..
            }
        ))
    ));
}

const ORACLE: &str = r#"
def sampleInput : Lean.Syntax := .atom .none "input"
def sampleContext : Lean.Macro.Context :=
  ⟨default, `Test, 17, 3, 512, sampleInput⟩
#eval show Bool from
  match forwardedContextMacro sampleInput sampleContext default with
  | .ok (.node .none kind #[.atom .none first, .atom .none second]) state =>
    kind == Lean.Name.mkStr1 "forwarded" && first == "input" && second == "input" &&
    state.macroScope == 0 && state.traceMsgs.isEmpty
  | _ => false
"#;
