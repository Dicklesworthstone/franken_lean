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
    let fixture = include_str!("../../../../fln-olean/fixtures/ir/NativeMacroLookupModule.lean");
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
    let resolve_namespace_macro = prepare("lookupResolveNamespaceMacro");
    // Exercise both the unchanged direct action (nested reset/reuse in the
    // default pin IR) and the separately factored pure construction helper.
    let resolve_global_macro = prepare("lookupResolveGlobalMacro");
    let separated_global_macro = prepare("lookupResolveGlobalSeparatedMacro");
    let only_a = name("Provided.onlyA");
    let only_b = name("Provided.onlyB");
    let environment_a = fln_elab::namespaces::register_module(
        &environment(&only_a),
        &[name("Live.SpaceA.LookupChild"), name("Other.LookupChild")],
    )
    .unwrap();
    let environment_b =
        fln_elab::namespaces::register_module(&environment(&only_b), &[name("LookupChild")])
            .unwrap();
    let module_a = name("ModuleA");
    let module_b = name("ModuleB");
    let namespace_a = name("Live.SpaceA");
    let namespace_b = name("Live.SpaceB");
    let opened_a = [name("Other")];
    let lookup_a =
        EnvironmentMacroLookup::new(&environment_a, &module_a, &namespace_a, &opened_a, &[]);
    let lookup_b = EnvironmentMacroLookup::new(&environment_b, &module_b, &namespace_b, &[], &[]);
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
    let child = identifier(name("LookupChild"));
    for (lookup, expected) in [
        (
            &lookup_a,
            Syntax::node(
                name("Live.SpaceA.LookupChild"),
                vec![Syntax::node(name("Other.LookupChild"), vec![child.clone()])],
            ),
        ),
        (
            &lookup_b,
            Syntax::node(name("LookupChild"), vec![child.clone()]),
        ),
        (
            &lookup_a,
            Syntax::node(
                name("Live.SpaceA.LookupChild"),
                vec![Syntax::node(name("Other.LookupChild"), vec![child.clone()])],
            ),
        ),
    ] {
        check(
            &resolve_namespace_macro,
            &child,
            lookup,
            expected,
            "mirror:Lean.Macro.resolveNamespace",
        );
    }
    check(
        &resolve_namespace_macro,
        &input_a,
        &lookup_a,
        Syntax::atom(SourceInfo::None, "absent"),
        "mirror:Lean.Macro.resolveNamespace",
    );
    for compiled in [&resolve_global_macro, &separated_global_macro] {
        for lookup in [&lookup_a, &lookup_b, &lookup_a] {
            let expected = if std::ptr::eq(lookup, &lookup_a) {
                Syntax::node(name("Provided.onlyA"), vec![input_a.clone()])
            } else {
                Syntax::atom(SourceInfo::None, "absent")
            };
            check(
                compiled,
                &input_a,
                lookup,
                expected,
                "mirror:Lean.Macro.resolveGlobalName",
            );
        }
        check(
            compiled,
            &identifier(name("Provided.onlyA.field")),
            &lookup_a,
            Syntax::node(
                name("Provided.onlyA"),
                vec![Syntax::atom(SourceInfo::None, "field")],
            ),
            "mirror:Lean.Macro.resolveGlobalName",
        );
    }
    for (compiled, operation) in [
        (&namespace_macro, "Lean.Macro.getCurrNamespace"),
        (&has_decl_macro, "Lean.Macro.hasDecl"),
        (&resolve_namespace_macro, "Lean.Macro.resolveNamespace"),
        (&resolve_global_macro, "Lean.Macro.resolveGlobalName"),
        (&separated_global_macro, "Lean.Macro.resolveGlobalName"),
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

    // Unlike the finite membership callbacks above, this oracle invokes the
    // pin's actual namespace resolver over its actual namespace extension.
    let namespace_environment = fln_elab::namespaces::register_module(
        &Environment::new(),
        &[
            name("Current.Child"),
            name("Current.Inner.Child"),
            name("First.Child"),
            name("Second.Child"),
            name("Child"),
        ],
    )
    .unwrap();
    let current = name("Current.Inner.Deep");
    let opened = [
        name("First"),
        name("Second"),
        name("Current.Inner"),
        name("First"),
    ];
    let lookup =
        EnvironmentMacroLookup::new(&namespace_environment, &module_a, &current, &opened, &[]);
    let expected = ["Child", "_root_.Child", "Missing"]
        .map(|query| {
            lookup
                .resolve_namespace(&name(query))
                .unwrap()
                .iter()
                .map(Name::to_display_string)
                .collect::<Vec<_>>()
                .join(",")
        })
        .join(";")
        + "\n";
    std::fs::write(dir.join("NamespaceOracle.lean"), NAMESPACE_ORACLE).unwrap();
    let oracle = Command::new(&reference)
        .current_dir(&dir)
        .arg("NamespaceOracle.lean")
        .output()
        .unwrap();
    std::fs::write(dir.join("namespace-oracle.stdout"), &oracle.stdout).unwrap();
    std::fs::write(dir.join("namespace-oracle.stderr"), &oracle.stderr).unwrap();
    assert!(oracle.status.success(), "{oracle:?}; {dir:?}");
    assert_eq!(oracle.stdout, expected.as_bytes(), "{dir:?}");
    assert!(oracle.stderr.is_empty());

    let main_module = name("GlobalOracle");
    let global_namespace = name("Current.Inner");
    let global_opens = [name("First"), name("Second"), name("First")];
    let explicit = [(1, name("chosen"), name("Target.two"))];
    let private = Name::num(name("_private.GlobalOracle"), 0).append_core(&name("hidden"));
    let mut scoped = fln_syntax::hygiene::MacroScopesView {
        name: name("record"),
        imported: Name::anonymous(),
        context: name("Quotation"),
        scopes: vec![7, 12],
    };
    let mut global_environment = [
        "Current.local",
        "local",
        "pooled",
        "First.pooled",
        "Second.pooled",
        "First.exact",
        "Second.First.exact",
        "First.record",
        "First.protected",
        "Target.one",
        "Target.two",
        "Target.two.child",
        "record",
    ]
    .into_iter()
    .map(name)
    .chain([private, scoped.review()])
    .fold(Environment::new(), |env, declaration| {
        env.add_decl(ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: declaration,
                level_params: Vec::new(),
                type_: Expr::const_(name("Nat"), Vec::new()),
            },
            is_unsafe: false,
        }))
        .unwrap()
    });
    for (alias, target) in [
        ("Current.local", "Target.one"),
        ("choice", "Target.one"),
        ("choice", "Target.two"),
        ("guarded", "First.protected"),
    ] {
        global_environment =
            fln_elab::aliases::register(&global_environment, &name(alias), &name(target)).unwrap();
    }
    global_environment =
        fln_elab::protected_names::register_module(&global_environment, &[name("First.protected")])
            .unwrap();
    let global_lookup = EnvironmentMacroLookup::new(
        &global_environment,
        &main_module,
        &global_namespace,
        &global_opens,
        &explicit,
    );
    scoped.name = name("record.field.tail");
    let queries: Vec<_> = [
        "local",
        "pooled",
        "First.exact",
        "record.field.tail",
        "_root_.local",
        "choice",
        "protected",
        "guarded",
        "First.protected",
        "hidden",
        "chosen",
        "chosen.child",
        "Missing",
        "Current.local.hcongr_2",
    ]
    .into_iter()
    .map(name)
    .chain([scoped.review()])
    .collect();
    let expected = queries
        .iter()
        .map(|query| {
            let candidates = global_lookup.resolve_global_name(query).unwrap();
            // Exercise the actual imported user function for the same query, so
            // native host results also traverse the VM's list/pair/string adapter.
            let input = identifier(query.clone());
            let syntax = match candidates.as_slice() {
                [] => Syntax::atom(SourceInfo::None, "absent"),
                [(target, fields)] if fields.is_empty() => {
                    Syntax::node(target.clone(), vec![input.clone()])
                }
                [(target, fields)] => Syntax::node(
                    target.clone(),
                    vec![Syntax::atom(SourceInfo::None, &fields[0])],
                ),
                [(first, _), (second, _), ..] => Syntax::node(
                    first.clone(),
                    vec![Syntax::node(second.clone(), vec![input.clone()])],
                ),
            };
            check(
                &resolve_global_macro,
                &input,
                &global_lookup,
                syntax,
                "mirror:Lean.Macro.resolveGlobalName",
            );
            candidates
                .iter()
                .map(|(name, fields)| format!("{}:{}", name.to_display_string(), fields.join(".")))
                .collect::<Vec<_>>()
                .join(",")
        })
        .collect::<Vec<_>>()
        .join(";")
        + "\n";
    assert!(
        !global_environment.contains(&name("Current.local.hcongr_2")),
        "lookup must not realize a reserved declaration"
    );
    std::fs::write(dir.join("GlobalOracle.lean"), GLOBAL_ORACLE).unwrap();
    let oracle = Command::new(&reference)
        .current_dir(&dir)
        .arg("GlobalOracle.lean")
        .output()
        .unwrap();
    std::fs::write(dir.join("global-oracle.stdout"), &oracle.stdout).unwrap();
    std::fs::write(dir.join("global-oracle.stderr"), &oracle.stderr).unwrap();
    assert!(oracle.status.success(), "{oracle:?}; {dir:?}");
    assert_eq!(oracle.stdout, expected.as_bytes(), "{dir:?}");
    assert!(oracle.stderr.is_empty());
}

const GLOBAL_ORACLE: &str = r#"
import Lean
axiom Current.local : Nat
axiom «local» : Nat
axiom pooled : Nat
axiom First.pooled : Nat
axiom Second.pooled : Nat
axiom First.exact : Nat
axiom Second.First.exact : Nat
axiom First.record : Nat
axiom First.protected : Nat
axiom Target.one : Nat
axiom Target.two : Nat
axiom Target.two.child : Nat
axiom record : Nat
private axiom hidden : Nat
open Lean Elab Command in
run_elab do
  let hygienicName := addMacroScope `Quotation (addMacroScope `Quotation `record 7) 12
  addDecl (.axiomDecl { name := hygienicName, levelParams := [], type := mkConst `Nat, isUnsafe := false })
  let env ← getEnv
  let env := [ (`Current.local, `Target.one), (`choice, `Target.one),
    (`choice, `Target.two), (`guarded, `First.protected) ].foldl
    (fun env (alias, target) => addAlias env alias target) env
  let env := addProtected env `First.protected
  let opens := [OpenDecl.simple `First [], .simple `Second [], .explicit `chosen `Target.two, .simple `First []]
  let queries := (["local", "pooled", "First.exact", "record.field.tail", "_root_.local", "choice",
    "protected", "guarded", "First.protected", "hidden", "chosen", "chosen.child", "Missing",
    "Current.local.hcongr_2"].map String.toName) ++
    [addMacroScope `Quotation (addMacroScope `Quotation `record.field.tail 7) 12]
  let rows := queries.map fun query =>
    (ResolveName.resolveGlobalName env {} `Current.Inner opens query).map fun (name, fields) =>
      name.toString ++ ":" ++ String.intercalate "." fields
  logInfo m!"{String.intercalate ";" (rows.map (String.intercalate ","))}"
"#;

const NAMESPACE_ORACLE: &str = r#"
import Lean
open Lean Elab Command in
run_elab do
  let env ← getEnv
  let env := [ `Current.Child, `Current.Inner.Child, `First.Child, `Second.Child, `Child ].foldl
    (fun env ns => env.registerNamespace ns) env
  let opens := [OpenDecl.simple `First [], .simple `Current.Inner [], .simple `Second [], .simple `First []]
  let rows := [ `Child, `_root_.Child, `Missing ].map fun query =>
    (ResolveName.resolveNamespace env `Current.Inner.Deep opens query).map (·.toString)
  logInfo m!"{String.intercalate ";" (rows.map (String.intercalate ","))}"
"#;

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
