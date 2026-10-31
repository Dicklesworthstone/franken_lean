//! Actual pin-compiled MacroM lookups with an explicit native environment.
//! The Reference is only the oracle; imported execution uses native lookup rows.

use super::*;
use crate::Environment;
use crate::imported_macros::lookup::EnvironmentMacroLookup;
use fln_core::expr::Expr;
use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};
use fln_vm::macro_native::MacroLookup;
use std::path::PathBuf;
use std::process::Command;

// These fixtures model the already-admitted snapshot at the embedding boundary.
// They do not claim that inserting an arbitrary axiom is an admission procedure.
fn environment(declaration: &Name) -> Environment {
    Environment::new()
        .add_decl(ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: declaration.clone(),
                level_params: Vec::new(),
                type_: Expr::const_(name("Nat"), Vec::new()),
            },
            is_unsafe: false,
        }))
        .unwrap()
}

fn identifier(value: Name) -> Syntax {
    Syntax::Ident {
        info: SourceInfo::None,
        raw_val: span(0, 5),
        val: value,
        preresolved: Vec::new(),
    }
}

#[test]
fn live_native_macro_lookup_uses_explicit_isolated_environments_and_preserves_state() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for native MacroM environment lookups"
        );
        eprintln!("SKIP: native macro lookup requires FLN_REFERENCE_LEAN");
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
    let dir = root.join(format!("macro-lookup-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let fixture = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../fln-olean/fixtures/ir/NativeMacroLookupModule.lean"
    ));
    std::fs::write(dir.join("NativeMacroLookupModule.lean"), fixture).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args([
            "-Dtrace.compiler.ir.result=true",
            "-o",
            "NativeMacroLookupModule.olean",
            "NativeMacroLookupModule.lean",
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
    let module = crate::decode_ir_artifact(
        &std::fs::read(dir.join("NativeMacroLookupModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    std::fs::write(dir.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .filter_map(|declaration| match declaration {
            IrDecl::Function { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    let prepare = |entry: &str| {
        assert!(module.decls.iter().any(|declaration| {
            matches!(declaration, IrDecl::Function { name: actual, params, .. }
                if actual == &name(entry) && params.len() == 3)
        }));
        compile(
            std::slice::from_ref(&module),
            &name(entry),
            &VerifiedPartition::user_fixture(),
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry}: {error}; {dir:?}"))
    };
    let namespace_macro = prepare("lookupNamespaceMacro");
    let has_decl_macro = prepare("lookupHasDeclMacro");
    let only_a = name("Provided.onlyA");
    let only_b = name("Provided.onlyB");
    let environment_a = environment(&only_a);
    let environment_b = environment(&only_b);
    let module_a = name("ModuleA");
    let module_b = name("ModuleB");
    let namespace_a = name("Live.SpaceA");
    let namespace_b = name("Live.SpaceB");
    let lookup_a = EnvironmentMacroLookup::new(&environment_a, &module_a, &namespace_a);
    let lookup_b = EnvironmentMacroLookup::new(&environment_b, &module_b, &namespace_b);
    let source = SourceText::from_utf8(b"value").unwrap();
    let context = MacroContext {
        quotation_context: name("Quotation.Origin"),
        current_macro_scope: 999,
        current_recursion_depth: 3,
        max_recursion_depth: 512,
    };
    assert_ne!(context.quotation_context, namespace_a);
    assert_ne!(context.quotation_context, namespace_b);
    let state = MacroState {
        macro_scope: 17,
        trace_messages: vec![(name("lookup.trace"), "λ\0🙂".into())],
        expanded_macro_declarations: vec![name("Earlier.macro")],
    };
    let input_a = identifier(only_a);
    let input_b = identifier(only_b);
    let check = |compiled: &CompiledMacro,
                 input: &Syntax,
                 lookup: &dyn MacroLookup,
                 expected: Syntax,
                 row: &str| {
        let report = compiled.execute_with_context(
            input,
            MacroInvocation {
                source: &source,
                context: &context,
                state: &state,
                lookup: Some(lookup),
            },
            MacroLimits::default(),
            None,
        );
        assert!(
            matches!(&report.outcome,
                Outcome::Complete(Ok(MacroResult::Expanded { syntax, state: observed }))
                    if syntax == &expected && observed == &state),
            "{report:?}; {dir:?}"
        );
        assert!(report.vm_usage.is_some_and(|usage| usage.steps > 0));
        assert!(report.native_functions.iter().any(|native| native == row));
        assert!(!report.reference_functions.is_empty());
        assert!(report.reference_functions.iter().all(|function| {
            function.producer() == "reference"
                && !function.name.to_display_string().starts_with("Lean.")
        }));
    };
    for (lookup, expected_namespace) in [
        (&lookup_a, &namespace_a),
        (&lookup_b, &namespace_b),
        (&lookup_a, &namespace_a),
    ] {
        check(
            &namespace_macro,
            &input_a,
            lookup,
            Syntax::node(expected_namespace.clone(), vec![input_a.clone()]),
            "mirror:Lean.Macro.getCurrNamespace",
        );
    }
    for (lookup, input, expected) in [
        (&lookup_a, &input_a, "present"),
        (&lookup_b, &input_a, "absent"),
        (&lookup_a, &input_b, "absent"),
        (&lookup_b, &input_b, "present"),
        (&lookup_a, &input_a, "present"),
    ] {
        check(
            &has_decl_macro,
            input,
            lookup,
            Syntax::atom(SourceInfo::None, expected),
            "mirror:Lean.Macro.hasDecl",
        );
    }
    check(
        &has_decl_macro,
        &Syntax::Missing,
        &lookup_a,
        Syntax::atom(SourceInfo::None, "absent"),
        "mirror:Lean.Macro.hasDecl",
    );
    for (compiled, operation) in [
        (&namespace_macro, "Lean.Macro.getCurrNamespace"),
        (&has_decl_macro, "Lean.Macro.hasDecl"),
    ] {
        let unavailable = compiled.execute(
            &input_a,
            &source,
            &context,
            &state,
            MacroLimits::default(),
            None,
        );
        assert!(
            matches!(unavailable.outcome,
                Outcome::Complete(Err(MacroExecutionError::Runtime(
                    VmRefusal::MacroLookupUnavailable { operation: actual }
                ))) if actual == operation),
            "{unavailable:?}"
        );
    }
    // A missing capability cannot poison a later explicitly authorized call.
    check(
        &has_decl_macro,
        &input_b,
        &lookup_b,
        Syntax::atom(SourceInfo::None, "present"),
        "mirror:Lean.Macro.hasDecl",
    );

    // Explicit Reference Methods callbacks keep this oracle Init-only. They
    // supply the same two finite snapshots; they are never product code.
    std::fs::write(
        dir.join("LookupOracle.lean"),
        format!("{fixture}\n{ORACLE}"),
    )
    .unwrap();
    let oracle = Command::new(&reference)
        .current_dir(&dir)
        .arg("LookupOracle.lean")
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
    assert_eq!(
        oracle.stdout,
        b"[true, true, true, true, true, true, true, true, true]\n"
    );
    assert!(oracle.stderr.is_empty());
}

const ORACLE: &str = r#"
def lookupInput (name : Lean.Name) : Lean.Syntax :=
  .ident .none ⟨"value", ⟨0⟩, ⟨5⟩⟩ name []

def lookupContext (namespaceName declaration : Lean.Name) : Lean.Macro.Context :=
  ⟨Lean.Macro.mkMethods {
    expandMacro? := fun _ => pure none
    getCurrNamespace := pure namespaceName
    hasDecl := fun name => pure (name == declaration)
    resolveNamespace := fun _ => pure []
    resolveGlobalName := fun _ => pure []
  }, `Quotation.Origin, 999, 3, 512, .missing⟩

def lookupSeed : Lean.MacroM Unit := do
  for _ in List.range 17 do
    Lean.Macro.withFreshMacroScope (pure ())
  Lean.Macro.trace `lookup.trace "λ\x00🙂"

def lookupCheck (action : Lean.Syntax → Lean.MacroM Lean.Syntax)
    (context : Lean.Macro.Context) (input expected : Lean.Syntax) : Bool :=
  match lookupSeed context default with
  | .ok _ before =>
    match action input context before with
    | .ok actual after =>
      reprStr actual == reprStr expected && after.macroScope == before.macroScope &&
        after.traceMsgs == before.traceMsgs
    | _ => false
  | _ => false

#eval Id.run do
  let first := lookupContext `Live.SpaceA `Provided.onlyA
  let second := lookupContext `Live.SpaceB `Provided.onlyB
  let a := lookupInput `Provided.onlyA
  let b := lookupInput `Provided.onlyB
  return [
    lookupCheck lookupNamespaceMacro first a (.node .none `Live.SpaceA #[a]),
    lookupCheck lookupNamespaceMacro second a (.node .none `Live.SpaceB #[a]),
    lookupCheck lookupNamespaceMacro first a (.node .none `Live.SpaceA #[a]),
    lookupCheck lookupHasDeclMacro first a (.atom .none "present"),
    lookupCheck lookupHasDeclMacro second a (.atom .none "absent"),
    lookupCheck lookupHasDeclMacro first b (.atom .none "absent"),
    lookupCheck lookupHasDeclMacro second b (.atom .none "present"),
    lookupCheck lookupHasDeclMacro first a (.atom .none "present"),
    lookupCheck lookupHasDeclMacro first .missing (.atom .none "absent")]
"#;
