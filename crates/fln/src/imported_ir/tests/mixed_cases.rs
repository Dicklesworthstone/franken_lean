//! Sum-type defaults must distinguish tagged values without treating heaps as Nat.

use super::*;
use fln_olean::ir::{IrAlt, IrCtorInfo};
use std::path::PathBuf;
use std::process::Command;

fn info(tag: u64, fields: u64) -> IrCtorInfo {
    IrCtorInfo {
        name: name(&format!("LocalCase.ctor{tag}")),
        cidx: tag,
        size: fields,
        usize: 0,
        ssize: 0,
    }
}

fn packet_case(default: IrBody) -> IrDecl {
    body_function(
        "LocalCase.match",
        1,
        ir_body(
            Vec::new(),
            IrTerminal::Case {
                type_name: name("LocalCase.Packet"),
                x: 1,
                x_type: IrType::TObject,
                alts: vec![
                    IrAlt::Ctor {
                        info: info(0, 0),
                        body: ir_body(vec![number(2, 7)], IrTerminal::Ret(IrArg::Var(2))),
                    },
                    IrAlt::Ctor {
                        info: info(2, 1),
                        body: ir_body(
                            vec![binding(3, IrExpr::Proj { i: 0, x: 1 })],
                            IrTerminal::Ret(IrArg::Var(3)),
                        ),
                    },
                    IrAlt::Default { body: default },
                ],
            },
        ),
    )
}

fn returning_default() -> IrBody {
    ir_body(vec![number(4, 99)], IrTerminal::Ret(IrArg::Var(4)))
}

#[test]
fn object_cases_route_unmatched_scalars_and_heaps_to_the_default() {
    for (argument, expected) in [
        (nat(0), "7"),
        (nat(1), "99"),
        (nat(256), "99"),
        (nat(u64::MAX), "99"),
        (EntryArgument::String("heap λ\0🙂".to_owned()), "99"),
    ] {
        let compiled = compile_users(
            vec![packet_case(returning_default())],
            "LocalCase.match",
            &[argument],
            IrExecutionLimits::default(),
        )
        .unwrap();
        assert_native_owned_result(&compiled, expected);
    }

    for (tag, expected) in [(2, "42"), (3, "99"), (0, "99")] {
        let entry = function(
            "LocalCase.entry",
            1,
            vec![
                binding(
                    2,
                    IrExpr::Ctor {
                        info: info(tag, 1),
                        args: vec![IrArg::Var(1)],
                    },
                ),
                call(3, "LocalCase.match", &[2]),
            ],
            IrArg::Var(3),
        );
        let compiled = compile_users(
            vec![packet_case(returning_default()), entry],
            "LocalCase.entry",
            &[nat(42)],
            IrExecutionLimits::default(),
        )
        .unwrap();
        // Tag 0 with an object slot is not the fieldless constructor: matching
        // a scalar tag must not bypass the existing heap-shape predicate.
        assert_native_owned_result(&compiled, expected);
    }
}

#[test]
fn large_nullary_tags_keep_defaults_without_using_the_heap_tag_table() {
    let declaration = body_function(
        "LocalCase.wide",
        1,
        ir_body(
            Vec::new(),
            IrTerminal::Case {
                type_name: name("LocalCase.WideEnum"),
                x: 1,
                x_type: IrType::TObject,
                alts: vec![
                    IrAlt::Ctor {
                        info: info(300, 0),
                        body: ir_body(vec![number(2, 7)], IrTerminal::Ret(IrArg::Var(2))),
                    },
                    IrAlt::Default {
                        body: returning_default(),
                    },
                ],
            },
        ),
    );
    let mut limits = IrExecutionLimits::default();
    limits.fir.max_constructors = 0;
    for (argument, expected) in [
        (nat(300), "7"),
        (nat(301), "99"),
        (EntryArgument::String("heap default".to_owned()), "99"),
    ] {
        let compiled = compile_users(
            vec![declaration.clone()],
            "LocalCase.wide",
            &[argument],
            limits,
        )
        .unwrap();
        assert_native_owned_result(&compiled, expected);
    }
}

#[test]
fn nullary_defaults_keep_the_native_heap_list_representation() {
    let declaration = body_function(
        "NativeCase.nil",
        1,
        ir_body(
            Vec::new(),
            IrTerminal::Case {
                type_name: name("List"),
                x: 1,
                x_type: IrType::TObject,
                alts: vec![
                    IrAlt::Ctor {
                        info: IrCtorInfo {
                            name: name("List.nil"),
                            ..info(0, 0)
                        },
                        body: ir_body(vec![number(2, 11)], IrTerminal::Ret(IrArg::Var(2))),
                    },
                    IrAlt::Default {
                        body: ir_body(vec![number(3, 22)], IrTerminal::Ret(IrArg::Var(3))),
                    },
                ],
            },
        ),
    );
    for (with_item, expected) in [(false, "11"), (true, "22")] {
        let mut statements = vec![number(1, 0), call(2, "Array.emptyWithCapacity", &[1])];
        let array = if with_item {
            statements.extend([number(3, 42), call(4, "Array.push", &[2, 3])]);
            4
        } else {
            2
        };
        statements.extend([
            call(5, "Array.toList", &[array]),
            call(6, "NativeCase.nil", &[5]),
        ]);
        let entry = function("NativeCase.entry", 0, statements, IrArg::Var(6));
        let compiled = compile_users(
            vec![declaration.clone(), entry],
            "NativeCase.entry",
            &[],
            IrExecutionLimits::default(),
        )
        .unwrap();
        assert_native_owned_result(&compiled, expected);
    }
}

#[test]
fn selected_cases_do_not_run_the_default_and_stopped_dispatch_can_retry() {
    let compiled = compile_users(
        vec![packet_case(ir_body(Vec::new(), IrTerminal::Unreachable))],
        "LocalCase.match",
        &[nat(0)],
        IrExecutionLimits::default(),
    )
    .unwrap();
    let mut stopped = false;
    let mut complete = false;
    for max_steps in 0..64 {
        let outcome = compiled
            .execute(
                ExecutionLimits {
                    max_steps,
                    ..ExecutionLimits::default()
                },
                None,
            )
            .outcome;
        match outcome {
            Outcome::Complete(VmExit::Returned(value)) => {
                assert_eq!(crate::nat_decimal(&value.value).as_deref(), Some("7"));
                complete = true;
            }
            Outcome::Inconclusive(_) => stopped = true,
            other => panic!("default ran or dispatch failed: {other:?}"),
        }
    }
    assert!(stopped && complete);
    assert_native_owned_result(&compiled, "7");
}

#[test]
fn live_pin_syntax_option_and_user_sum_defaults_match_reference() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let lib = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(lib.parent()?.parent()?.join("bin/lean"))
        });
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required"
        );
        eprintln!("SKIP mixed-case IR: requires the pinned Reference");
        return;
    };
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(
        String::from_utf8(version.stdout).unwrap().trim(),
        crate::OLEAN_PIN_COMMIT
    );
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    std::fs::create_dir_all(&root).unwrap();
    let tick = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!("case-reference-{}-{tick}", std::process::id()));
    std::fs::create_dir(&dir).unwrap();
    let source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../fln-olean/fixtures/ir/CaseModule.lean"
    ));
    std::fs::write(dir.join("CaseModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args(["-o", "CaseModule.olean", "CaseModule.lean"])
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
        &std::fs::read(dir.join("CaseModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    std::fs::write(dir.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    let mut relevant_cases = 0;
    for declaration in &module.decls {
        if let IrDecl::Function { body, .. } = declaration {
            for body in body.bodies() {
                if let IrTerminal::Case { x_type: IrType::TObject | IrType::Object, alts, .. } = body.terminal.as_ref()
                    && alts.iter().any(|alt| matches!(alt, IrAlt::Default { .. }))
                    && alts.iter().any(|alt| matches!(alt, IrAlt::Ctor { info, .. } if info.size == 0 && info.usize == 0 && info.ssize == 0))
                {
                    relevant_cases += 1;
                }
            }
        }
    }
    assert!(
        relevant_cases >= 3,
        "pin optimized away the targeted cases: {dir:?}"
    );
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .filter_map(|declaration| match declaration {
            IrDecl::Function { name, .. } if native_row(name).is_none() => Some(name.clone()),
            _ => None,
        })
        .collect();
    let cases = [
        ("packetEntry", 0, "7"),
        ("packetEntry", 1, "99"),
        ("packetEntry", 2, "3"),
        ("packetEntry", 3, "99"),
        ("packetEntry", u64::MAX, "99"),
        ("syntaxEntry", 0, "11"),
        ("syntaxEntry", 1, "22"),
        ("optionEntry", 0, "13"),
        ("optionEntry", 1, "26"),
    ];
    let mut oracle_source = source.to_owned();
    for (entry, argument, _) in cases {
        oracle_source.push_str(&format!("\n#eval {entry} {argument}\n"));
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
        "{}{}",
        String::from_utf8_lossy(&oracle.stdout),
        String::from_utf8_lossy(&oracle.stderr)
    );
    let expected = cases
        .iter()
        .map(|(_, _, expected)| format!("{expected}\n"))
        .collect::<String>();
    assert_eq!(String::from_utf8(oracle.stdout).unwrap(), expected);
    for (entry, argument, expected) in cases {
        let compiled = compile(
            std::slice::from_ref(&module),
            &name(entry),
            &[nat(argument)],
            &bounded_partition(&[]),
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry} {argument}: {error:?}; {dir:?}"));
        assert!(
            compiled
                .program
                .program()
                .functions()
                .iter()
                .any(|function| function.code.iter().any(|instruction| matches!(
                    instruction,
                    flbc::Instruction::ScalarTagTest { .. }
                )))
        );
        assert_native_owned_result(&compiled, expected);
    }
}
