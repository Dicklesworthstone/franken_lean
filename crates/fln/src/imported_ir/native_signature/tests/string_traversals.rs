//! Imported callbacks use the erased calling convention; traversals remain
//! native and validate every callback result before resuming their work.

use super::boxed_primitives::STRING_TRAVERSALS;
use super::*;
use crate::imported_ir::EntryArgument;
use std::path::PathBuf;
use std::process::Command;

fn assert_replay(compiled: &CompiledIr, expected: &str, text: bool) {
    let bytes =
        flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&replay, flbc::CodecLimits::default()).unwrap(),
        bytes
    );
    for program in [compiled.program.program(), &replay] {
        let outcome = execute(program, ExecutionLimits::default(), None);
        let Outcome::Complete(VmExit::Returned(result)) = outcome else {
            panic!("traversal did not return: {outcome:?}");
        };
        let actual = if text {
            let (size, _, _, bytes) = result.value.try_string_view().expect("String result");
            assert_eq!(bytes[size - 1], 0);
            bytes[..size - 1]
                .iter()
                .map(u8::to_string)
                .collect::<Vec<_>>()
                .join(",")
        } else {
            nat_decimal(&result.value).expect("Nat result")
        };
        assert_eq!(actual, expected);
    }
}

#[test]
fn imported_folds_use_erased_native_callbacks_and_reusable_boxed_traversals() {
    for boxed in [false, true] {
        let mut statements = vec![
            bind(
                1,
                IrExpr::Pap {
                    function: name("String.push._boxed"),
                    args: vec![],
                },
            ),
            bind(2, IrExpr::Lit(IrLit::Str("prefix:".to_owned()))),
            bind(3, IrExpr::Lit(IrLit::Str("aλ😀\0z".to_owned()))),
        ];
        if boxed {
            statements.extend([
                bind(
                    4,
                    IrExpr::Pap {
                        function: name("String.Internal.foldl._boxed"),
                        args: vec![var(1), var(2)],
                    },
                ),
                bind(
                    5,
                    IrExpr::Ap {
                        x: 4,
                        args: vec![var(3)],
                    },
                ),
                bind(
                    6,
                    IrExpr::Ap {
                        x: 4,
                        args: vec![var(3)],
                    },
                ),
            ]);
        } else {
            statements.extend([
                call(5, "String.Internal.foldl", &[1, 2, 3]),
                call(6, "String.Internal.foldl", &[1, 2, 3]),
            ]);
        }
        statements.push(call(7, "String.append", &[5, 6]));
        let compiled = compile_declarations(vec![entry(statements, 7)]).unwrap();
        let expected = "prefix:aλ😀\0zprefix:aλ😀\0z"
            .as_bytes()
            .iter()
            .map(u8::to_string)
            .collect::<Vec<_>>()
            .join(",");
        assert_replay(&compiled, &expected, true);
        assert!(compiled.reference_functions().iter().all(|function| {
            function.name == name("Arity.main") && function.producer() == "reference"
        }));
        assert!(matches!(
            compiled
                .execute(
                    ExecutionLimits {
                        max_steps: 0,
                        ..ExecutionLimits::default()
                    },
                    None,
                )
                .outcome,
            Outcome::Inconclusive(_)
        ));
        assert!(matches!(
            compiled
                .execute(ExecutionLimits::default(), Some(&|| true))
                .outcome,
            Outcome::Inconclusive(_)
        ));
        assert_replay(&compiled, &expected, true);
    }
}

#[test]
fn traversal_prototypes_keep_raw_borrowing_and_boxed_boolean_results_distinct() {
    for target in STRING_TRAVERSALS {
        let row = crate::imported_ir::native_row(&name(target)).unwrap();
        let (types, result, boxed_result): (Vec<_>, _, _) = match target {
            "String.Internal.foldl" => (
                vec![IrType::Object, IrType::Object, IrType::Object],
                IrType::Object,
                IrType::Object,
            ),
            "String.Internal.nextWhile" => (
                vec![IrType::Object, IrType::Object, IrType::TObject],
                IrType::TObject,
                IrType::TObject,
            ),
            "Substring.Raw.Internal.takeWhile" => (
                vec![IrType::Object, IrType::Object],
                IrType::Object,
                IrType::Object,
            ),
            _ => (
                vec![IrType::Object, IrType::Object],
                IrType::UInt8,
                IrType::Tagged,
            ),
        };
        let params: Vec<_> = types
            .into_iter()
            .enumerate()
            .map(|(index, ty)| IrParam {
                x: index as u64,
                borrow: false,
                ty,
            })
            .collect();
        validate_extern_signature(row, &params, &result).unwrap();
        let bridge = BoxedNative::from_row(row).unwrap().unwrap();
        let wrapper = IrDecl::Function {
            name: Name::str(name(target), "_boxed"),
            params: params.clone(),
            result: boxed_result,
            body: IrBody {
                stmts: vec![],
                terminal: Box::new(IrTerminal::Unreachable),
            },
            sorry_dep: None,
        };
        bridge.validate_declaration(&wrapper).unwrap();
        for index in 0..params.len() {
            let mut changed = params.clone();
            changed[index].borrow = true;
            assert!(matches!(
                validate_extern_signature(row, &changed, &result),
                Err(IrExecutionError::NativeContract { .. })
            ));
            let mut changed = params.clone();
            changed[index].ty = IrType::Void;
            assert!(matches!(
                validate_extern_signature(row, &changed, &result),
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
        assert!(matches!(
            validate_extern_signature(row, &params, &IrType::Void),
            Err(IrExecutionError::NativeContract { .. })
        ));
    }
}

#[test]
fn live_pinned_traversals_run_imported_callbacks_and_all_five_boxed_entry_points() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for native String traversals"
        );
        eprintln!("SKIP: native String traversals require FLN_REFERENCE_LEAN");
        return;
    };
    let pin = include_str!("../../../../../../SUITE.lock")
        .lines()
        .find(|line| line.starts_with("reference "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|part| part.strip_prefix("commit="))
        })
        .unwrap();
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(String::from_utf8(version.stdout).unwrap().trim(), pin);
    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            reference
                .parent()
                .unwrap()
                .parent()
                .unwrap()
                .join("lib/lean")
        });
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!(
        "string-traversal-reference-{}-{stamp}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let source =
        include_str!("../../../../../fln-olean/fixtures/ir/NativeStringTraversalModule.lean");
    std::fs::write(dir.join("NativeStringTraversalModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args([
            "-j1",
            "-o",
            "NativeStringTraversalModule.olean",
            "NativeStringTraversalModule.lean",
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
        &std::fs::read(dir.join("NativeStringTraversalModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    std::fs::write(dir.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .map(|decl| decl.name().clone())
        .collect();
    assert!(users.iter().all(|name| {
        name.to_display_string()
            .starts_with("NativeStringTraversal.")
    }));
    let partials: BTreeSet<_> = module
        .decls
        .iter()
        .flat_map(|decl| match decl {
            IrDecl::Function { body, .. } => body.bodies(),
            IrDecl::Extern { .. } => Vec::new(),
        })
        .flat_map(|body| &body.stmts)
        .filter_map(|stmt| match stmt {
            IrStmt::VDecl {
                expr: IrExpr::Pap { function, .. },
                ..
            } => Some(function.clone()),
            _ => None,
        })
        .collect();
    let bytes = std::fs::read(library.join("Init/Data/String/Bootstrap.ir")).unwrap();
    fln_olean::pin::check_pinned_header(&bytes).unwrap();
    let bootstrap = crate::decode_ir_artifact(&bytes, 32 * 1024 * 1024).unwrap();
    let mut prototypes = IrModule::default();
    for target in STRING_TRAVERSALS {
        let row = crate::imported_ir::native_row(&name(target)).unwrap();
        let external = bootstrap
            .decls
            .iter()
            .find(|decl| decl.name() == &name(target))
            .unwrap();
        let IrDecl::Extern { params, result, .. } = external else {
            panic!("{target} must be an extern")
        };
        validate_extern_signature(row, params, result)
            .unwrap_or_else(|error| panic!("{target}: {error:?}; {external:?}"));
        let boxed = Name::str(name(target), "_boxed");
        assert!(
            partials.contains(&boxed),
            "{target} PAP was optimized away; {dir:?}"
        );
        let wrapper = bootstrap
            .decls
            .iter()
            .find(|decl| decl.name() == &boxed)
            .unwrap();
        BoxedNative::from_row(row)
            .unwrap()
            .unwrap()
            .validate_declaration(wrapper)
            .unwrap_or_else(|error| panic!("{target}: {error:?}; {wrapper:?}"));
        prototypes.decls.extend([external.clone(), wrapper.clone()]);
    }
    let string = |text: &str| EntryArgument::String(text.to_owned());
    let nat = |value| EntryArgument::Nat(IrNat::Small(value));
    let mut cases = Vec::new();
    for input in ["", "aλ😀\0z", "λ😀tail", "zfirst"] {
        for entry in ["foldDirect", "foldBoxed", "foldNested"] {
            cases.push((entry, vec![string("prefix:"), string(input)], true));
        }
        for entry in ["anyDirect", "anyBoxed"] {
            cases.push((entry, vec![string(input)], false));
        }
        for entry in ["nextWhileDirect", "nextWhileBoxed"] {
            for start in [0, 1, input.len() as u64] {
                cases.push((entry, vec![string(input), nat(start)], false));
            }
        }
        for entry in ["allDirect", "allBoxed", "takeWhileDirect", "takeWhileBoxed"] {
            cases.push((
                entry,
                vec![string(input), nat(0), nat(input.len() as u64)],
                false,
            ));
        }
    }
    let mut oracle_source = source.to_owned();
    for (entry, arguments, text) in &cases {
        let mut invocation = format!("NativeStringTraversal.{entry}");
        for argument in arguments {
            invocation.push(' ');
            invocation.push_str(&match argument {
                EntryArgument::Nat(IrNat::Small(value)) => value.to_string(),
                EntryArgument::String(value) => format!(
                    "\"{}\"",
                    value
                        .replace('\\', "\\\\")
                        .replace('"', "\\\"")
                        .replace('\0', "\\x00")
                ),
                _ => unreachable!("the fixture takes small naturals and UTF-8 strings"),
            });
        }
        if *text {
            oracle_source.push_str(&format!(
                "\n#eval IO.println (String.intercalate \",\" (({invocation}).toUTF8.toList.map (fun byte => toString byte.toNat)))\n"
            ));
        } else {
            oracle_source.push_str(&format!("\n#eval IO.println ({invocation})\n"));
        }
    }
    std::fs::write(dir.join("Oracle.lean"), oracle_source).unwrap();
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
    let output = String::from_utf8(oracle.stdout).unwrap();
    let expected: Vec<_> = output.lines().collect();
    assert_eq!(
        expected.len(),
        cases.len(),
        "unexpected oracle output: {output}"
    );
    let modules = [module, prototypes];
    let policy = VerifiedPartition::user_fixture();
    let mut observed = BTreeSet::new();
    for ((entry, arguments, text), expected) in cases.into_iter().zip(expected) {
        let compiled = compile(
            &modules,
            &name(&format!("NativeStringTraversal.{entry}")),
            &arguments,
            &policy,
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry} {arguments:?}: {error:?}; {dir:?}"));
        assert_replay(&compiled, expected, text);
        assert!(compiled.reference_functions().iter().all(|function| {
            function.producer() == "reference" && users.contains(&function.name)
        }));
        observed.extend(compiled.native_externs().iter().cloned());
        eprintln!("live Reference and Golem: {entry} {arguments:?} = {expected}");
    }
    for target in STRING_TRAVERSALS {
        assert!(
            observed.contains(&format!("extern:{target}")),
            "{target} was not linked"
        );
    }
}
