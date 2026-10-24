//! Imported panicCore uses the pin's projection, not the source seed's alias.
//! The Reference is consumed only as checked artifact data, never executed.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, ClosedVmValue, Engine, EngineExecutionLimits, Environment, KVMap, Name,
    OleanCheckLimits, OleanModuleInput,
};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

const STACK: usize = 256 * 1024 * 1024;

fn diagnostic_import(library: &Path) -> Engine {
    // Admit the real helpers and Id.run without importing the unrelated String
    // theorem closure. Assertions below use an ordinary source-local HAppend
    // dictionary, including an override that checks normal instance resolution.
    let roots: Vec<_> = ["Init.Util", "Init.Control.Basic"]
        .into_iter()
        .map(|name| Name::from_components(name.split('.')))
        .collect();
    let mut pending: Vec<_> = roots.iter().cloned().map(|name| (name, false)).collect();
    let mut seen = BTreeSet::new();
    let mut ordered = Vec::new();
    let mut artifacts = BTreeMap::new();
    while let Some((name, finished)) = pending.pop() {
        if finished {
            ordered.push(name);
            continue;
        }
        if !seen.insert(name.clone()) {
            continue;
        }
        assert!(
            seen.len() <= 256,
            "bounded actual diagnostic import closure"
        );
        let path = library
            .join(name.to_display_string().replace('.', "/"))
            .with_extension("olean");
        let parts = [
            std::fs::read(&path).unwrap(),
            std::fs::read(path.with_extension("olean.server")).unwrap(),
            std::fs::read(path.with_extension("olean.private")).unwrap(),
        ];
        let imports =
            fln::olean_module_imports(&parts[0], fln::OleanDecodeLimits::new(STACK)).unwrap();
        artifacts.insert(name.clone(), parts);
        pending.push((name, true));
        pending.extend(imports.into_iter().rev().map(|name| (name, false)));
    }
    let inputs: Vec<_> = ordered
        .iter()
        .map(|name| {
            let [exported, server, private] = &artifacts[name];
            OleanModuleInput {
                name,
                artifact: exported,
                server_artifact: Some(server),
                private_artifact: Some(private),
            }
        })
        .collect();
    let jobs = fln::OleanFrontierJobs {
        threads: std::num::NonZeroUsize::new(2).unwrap(),
        worker_stack_bytes: STACK,
    };
    let imported = Engine::from_environment(Environment::new())
        .import_olean_modules_for_source(
            &inputs,
            &roots,
            &KVMap::new(),
            SourceOleanImportLimits {
                jobs,
                read_jobs: jobs,
                ..SourceOleanImportLimits::new(OleanCheckLimits::new(
                    STACK,
                    Budget::for_stack_bytes(STACK),
                ))
            },
        )
        .expect("actual diagnostic library admission")
        .into_complete()
        .expect("actual diagnostic library admission completes");
    assert_eq!(imported.modules.len(), ordered.len());
    imported.engine
}

fn assert_panic_site(
    expression: &fln::Expr,
    module: &str,
    declaration: &str,
    line: u64,
    column: u64,
) {
    let mut head = expression;
    // The written type ascription is retained as an identity let. Inspect
    // its value without accepting an arbitrary let body or reducing panic.
    while let fln::ExprNode::LetE { value, body, .. } = head.node() {
        assert!(matches!(body.node(), fln::ExprNode::BVar { idx: 0 }));
        head = value;
    }
    let mut arguments = Vec::new();
    while let fln::ExprNode::App { f, a } = head.node() {
        arguments.push(a);
        head = f;
    }
    arguments.reverse();
    assert!(
        matches!(head.node(), fln::ExprNode::Const { name, .. }
        if name == &Name::from_components(["panicWithPosWithDecl"])),
        "{expression:?}"
    );
    assert_eq!(arguments.len(), 7);
    for (argument, expected) in [(&arguments[2], module), (&arguments[3], declaration)] {
        assert!(
            matches!(argument.node(), fln::ExprNode::Lit { literal: fln::Literal::Str(value) }
            if value == expected)
        );
    }
    for (argument, expected) in [(arguments[4], line), (arguments[5], column)] {
        // The pin's pp.all form retains ordinary OfNat synthesis here, so
        // check both the literal and its selected Nat dictionary exactly.
        let literal = fln::Expr::lit(fln::Literal::Nat(fln::NatLit::from_u64(expected)));
        let constant =
            |name: &str, levels| fln::Expr::const_(Name::from_components(name.split('.')), levels);
        let numeral = [
            constant("Nat", Vec::new()),
            literal.clone(),
            fln::Expr::app(constant("instOfNatNat", Vec::new()), literal),
        ]
        .into_iter()
        .fold(
            constant("OfNat.ofNat", vec![fln::Level::zero()]),
            fln::Expr::app,
        );
        assert_eq!(argument, &numeral);
    }
}

#[test]
fn imported_panic_family_source_preserves_sites_defaults_and_lazy_continuations() {
    const CHILD: &str = "FLN_PANIC_SOURCE_TEST_CHILD";
    const TEST: &str =
        "imported_panic_family_source_preserves_sites_defaults_and_lazy_continuations";
    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .filter(|path| path.is_dir());
    let Some(library) = library else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the actual pinned diagnostic library is required"
        );
        eprintln!("SKIP: pinned Reference lib/lean is absent");
        return;
    };
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", TEST, "--nocapture"])
            .env(CHILD, "1")
            .env("LEAN_BACKTRACE", "0")
            .env_remove("LEAN_ABORT_ON_PANIC")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let stderr = String::from_utf8(output.stderr).unwrap();
        for expected in [
            "PANIC at Diagnostic.direct PanicSource:3:30: direct-source\n",
            "PANIC at _private.PanicSource.0.Diagnostic.hidden PanicSource:4:38: private-source\n",
            "PANIC at Diagnostic.α PanicSource:5:25: unicode-source\n",
            "assertion violation: ( 1  == 2 /- trivia 🙂 -/ )\n",
            "PANIC at _private.PanicSource.0._eval PanicSource:11:2: assertion violation: false\n  \n",
            "unreachable code has been reached\n",
            "assertion violation: (1 ==\n  2)\n",
            "custom-assert-message\n",
            "selected-default\n",
        ] {
            assert!(
                stderr.contains(expected),
                "missing {expected:?} in {stderr:?}"
            );
        }
        assert!(!stderr.contains("SHOULD_NOT_RUN"), "{stderr:?}");
        assert!(!stderr.contains("untaken-panic"), "{stderr:?}");
        assert!(!stderr.contains("admission-only"), "{stderr:?}");
        // This facade requests the raw Unit value and preserves strict work.
        // The pin's formatted #eval can discard an argument ignored by Repr
        // Unit; an opaque demand of that same argument still emits its panic.
        assert_eq!(
            stderr
                .matches(
                    "PANIC at _private.0._eval [anonymous]:1:83: assertion violation: (false)\n"
                )
                .count(),
            1,
            "{stderr:?}"
        );
        return;
    }
    std::thread::Builder::new().stack_size(STACK).spawn(move || {
        let engine = diagnostic_import(&library);
        let options = KVMap::new();
        let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
        let root = engine.logical_root(&options);
        let source = concat!(
            "-- checked diagnostic library\r\nnamespace Diagnostic\r\n",
            "def direct (_ : Nat) : Nat := panic! \"direct-source\"\r\n",
            "private def hidden (_ : Nat) : Nat := panic! \"private-source\"\r\n",
            "def α (_ : Nat) : Nat := panic! \"unicode-source\"\r\n",
            "#eval direct 0\r\n#eval hidden 0\r\n#eval α 0\r\n",
            "#eval letI : HAppend String String String := ⟨String.Internal.append⟩; assert! ( 1  == 2 /- trivia 🙂 -/ ); (42 : Nat)\r\n",
            "#eval letI : HAppend String String String := ⟨String.Internal.append⟩; Id.run do\r\n  assert! false\r\n  return (panic! \"SHOULD_NOT_RUN\" : Nat)\r\n",
            "#eval letI : HAppend String String String := ⟨String.Internal.append⟩; Id.run do\r\n  assert! true\r\n  return 42\r\n",
            "end Diagnostic\r\n#check (panic! \"query\" : Nat)\r\n",
        );
        let module = Name::from_components(["PanicSource"]);
        let result = engine.execute_source_modules_with_entry_checks(
            &[fln::SourceModuleInput { name: &module, source: source.as_bytes() }],
            &module, &options, limits,
        ).unwrap().into_complete().unwrap();
        let values: Vec<_> = result.entry.outputs.iter().filter_map(|output| {
            if let fln::SourceCommandOutput::Evaluation { execution_index, .. } = output {
                Some(fln::closed_vm_value(&result.entry.batch.executions[*execution_index].exit).unwrap())
            } else { None }
        }).collect();
        assert_eq!(values, [0, 0, 0, 0, 0, 42].map(|value| Some(ClosedVmValue::Scalar(value))));
        let fln::Declaration::Defn(query) = &result.entry.checks.last().unwrap().declaration else { panic!("checked query definition") };
        assert_panic_site(&query.value, "PanicSource", "_check", 17, 8);

        let terminal_name = Name::from_components(["TerminalPanic"]);
        let terminal = engine.check_terminal_source_modules(
            &[fln::SourceModuleInput { name: &terminal_name, source: b"-- checked diagnostic library\r\n\r\n#check (panic! \"terminal-query\" : Nat)" }],
            &terminal_name, &options, limits,
        ).unwrap().into_complete().unwrap();
        let fln::Declaration::Defn(query) = &terminal.check.declaration else { panic!("checked terminal query definition") };
        assert_panic_site(&query.value, "TerminalPanic", "_check", 3, 8);

        for (source, value) in [
            ("#eval Id.run do return 42", 42),
            ("#eval Id.run do return (42 : Nat)", 42),
            ("#eval (panic! \"monadic-default\" : Id Nat)", 0),
            ("#eval (unreachable! : Nat)", 0),
            ("#eval letI : HAppend String String String := ⟨String.Internal.append⟩; assert! true; (42 : Nat)", 42),
            ("#eval if true then 42 else panic! \"untaken-panic\"", 42),
            ("#eval letI : HAppend String String String := ⟨String.Internal.append⟩; assert! (1 ==\r\n  2); (42 : Nat)", 0),
            ("#eval letI : HAppend String String String := ⟨String.Internal.append⟩; assert! false; (panic! \"SHOULD_NOT_RUN\" : Nat)", 0),
            ("#eval letI : HAppend String String String := ⟨fun _ _ => \"custom-assert-message\"⟩; assert! false; (42 : Nat)", 0),
            ("#eval letI : Inhabited Nat := ⟨37⟩; (panic! \"selected-default\" : Nat)", 37),
        ] {
            let run = engine.execute_source_commands_with_checks(source.as_bytes(), &options, limits)
                .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
                .into_complete().unwrap();
            let execution = run.batch.executions.last().unwrap();
            assert_eq!(fln::closed_vm_value(&execution.exit).unwrap(), Some(ClosedVmValue::Scalar(value)), "{source}\n{:?}", execution.exit);
        }
        for source in [
            "#eval (() : Unit)",
            "#eval letI : HAppend String String String := ⟨String.Internal.append⟩; (Id.run (do assert! true) : Unit)",
            "#eval letI : HAppend String String String := ⟨String.Internal.append⟩; (Id.run (do assert! (false)) : Unit)",
        ] {
            let run = engine.execute_source_commands_with_checks(source.as_bytes(), &options, limits)
                .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
                .into_complete().unwrap();
            let exit = &run.batch.executions.last().unwrap().exit;
            let fln::VmExit::Returned(returned) = exit else { panic!("{source}\n{exit:?}") };
            // Unit is the admitted nullary constructor, outside the facade's
            // simple closed_vm_value projection.
            let Some(fln::ConstantInfo::Ctor(unit)) = engine.environment().find(&Name::from_components(["PUnit", "unit"])) else { panic!("the checked Unit constructor") };
            assert_eq!(unit.num_fields, 0);
            assert_eq!(fln::vm_value_kind(&returned.value), fln::VmValueKind::Ctor(u8::try_from(unit.cidx).unwrap()), "{source}");
            assert_eq!(returned.value.header().other, 0, "{source}");
            assert!(returned.value.try_ctor_child(0).is_none(), "{source}");
        }
        engine.admit_source_declaration(b"def admitted : Nat := panic! \"admission-only\"", &options, limits.admission())
            .unwrap().into_complete().unwrap();
        let standalone = engine.execute_source_definition(b"def standalone : Nat := panic! \"standalone-source\"", &options, limits)
            .unwrap().into_complete().unwrap();
        assert_eq!(fln::closed_vm_value(&standalone.exit).unwrap(), Some(ClosedVmValue::Scalar(0)));
        for (source, line) in [
            ("#check (panic! \"query-only\" : Nat)", 1),
            ("\r\n#check (panic! \"query-after-blank-line\" : Nat)", 2),
        ] {
            let checked = engine.check_source_command(source.as_bytes(), &options, limits.admission())
                .unwrap().into_complete().unwrap();
            let fln::Declaration::Defn(query) = checked.declaration else { panic!("checked query definition") };
            assert_panic_site(&query.value, &Name::anonymous().to_display_string(), "_check", line, 8);
        }
        for source in [
            "def refused : Empty := panic! \"uninhabited\"",
            "def refused : Empty := unreachable!",
            "def refused (x : Empty) : Empty := letI : HAppend String String String := ⟨String.Internal.append⟩; assert! true; x",
        ] {
            assert!(engine.admit_source_declaration(source.as_bytes(), &options, limits.admission()).is_err(), "missing Inhabited must be rejected: {source}");
        }
        assert_eq!(root, engine.logical_root(&options));
    }).unwrap().join().unwrap();
}

#[test]
fn imported_panic_returns_the_selected_default_including_partial_and_function_values() {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|path| path.is_dir());
    let Some(lib) = lib else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "FLN_REQUIRE_REFERENCE is set but the pinned Reference is absent"
        );
        eprintln!("SKIP: pinned Reference lib/lean is absent");
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let path = lib.join("Init/Prelude.olean");
            let parts = [
                std::fs::read(&path).unwrap(),
                std::fs::read(path.with_extension("olean.server")).unwrap(),
                std::fs::read(path.with_extension("olean.private")).unwrap(),
            ];
            let name = Name::from_components(["Init", "Prelude"]);
            let inputs = [OleanModuleInput {
                name: &name,
                artifact: &parts[0],
                server_artifact: Some(&parts[1]),
                private_artifact: Some(&parts[2]),
            }];
            let options = KVMap::new();
            let imported = Engine::from_environment(Environment::new())
                .import_olean_modules_for_source(
                    &inputs,
                    std::slice::from_ref(&name),
                    &options,
                    SourceOleanImportLimits::new(OleanCheckLimits::new(
                        256 * 1024 * 1024,
                        Budget::for_stack_bytes(STACK),
                    )),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            let engine = &imported.engine;
            assert!(
                engine
                    .environment()
                    .find(&Name::from_components(["default"]))
                    .is_none(),
                "the import must not be repaired by installing the seed-only alias"
            );
            let root = engine.logical_root(&options);
            for (source, expected) in [
                ("#eval (panicCore \"imported panic\" : Nat)", 0),
                ("#eval @panicCore Nat (Inhabited.mk 42) \"imported default\"", 42),
                ("#eval let fail : String -> Nat := @panicCore Nat (Inhabited.mk 42); fail \"partial imported panic\"", 42),
                ("#eval @panicCore (Nat -> Nat) (Inhabited.mk (fun n => n + 2)) \"function imported panic\" 40", 42),
            ] {
                let run = || {
                    engine
                        .execute_source_commands_with_checks(
                            source.as_bytes(),
                            &options,
                            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
                        )
                        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
                        .into_complete()
                        .unwrap_or_else(|outcome| panic!("{source}\n{outcome:?}"))
                };
                let first = run();
                let last = first.batch.executions.last().unwrap();
                assert_eq!(
                    fln::closed_vm_value(&last.exit).unwrap(),
                    Some(ClosedVmValue::Scalar(expected)),
                    "{source}"
                );
                let second = run();
                assert_eq!(
                    last.flbc_artifact,
                    second.batch.executions.last().unwrap().flbc_artifact,
                    "deterministic imported panic execution: {source}"
                );
                assert_eq!(root, engine.logical_root(&options));
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
