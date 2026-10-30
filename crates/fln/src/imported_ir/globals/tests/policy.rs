//! Initialization extends the selected executable closure, not its authority.
//! Small synthetic partitions below exercise the internal class gate only;
//! public callers still require the complete authenticated census partition.

use super::*;
use crate::imported_ir::{native_row, native_signature};

fn bounded_partition(rows: &[(&str, &str)]) -> VerifiedPartition {
    let mut text = format!("constant_count\t{}\n", rows.len());
    for (declaration, class) in rows {
        let key = format!(
            "a{}",
            declaration
                .split('.')
                .map(|part| format!("/s\"{part}\""))
                .collect::<String>()
        );
        text.push_str(&format!(
            "partition\t{key:?}\t{class}\ttest-bounded-initializer-policy\n"
        ));
    }
    VerifiedPartition {
        partition: CensusPartition::parse(&text, GraphArchiveLimits::default()).unwrap(),
    }
}

fn prepare_with_policy(
    module: &IrModule,
    entry: &str,
    partition: &VerifiedPartition,
    users: &BTreeSet<Name>,
    capture_output_bytes: Option<usize>,
) -> Result<CompiledIr, IrExecutionError> {
    compile_with_options(
        std::slice::from_ref(module),
        &name(entry),
        &[],
        partition,
        users,
        IrExecutionOptions {
            initialize_globals: true,
            capture_output_bytes,
            ..IrExecutionOptions::default()
        },
    )
}

#[test]
fn toolchain_initializer_bodies_and_descendants_cannot_be_reclassified_as_users() {
    let partition = bounded_partition(&[("Lean.Elab.Term.elabTerm", "toolchain-api")]);
    for initializer_name in ["Lean.Elab.Term.elabTerm", "Lean.Elab.Term.elabTerm._boxed"] {
        let mut module = module();
        module.decls[1] = initializer(initializer_name, None, 0);
        module.initializers[0].initializer = Some(name(initializer_name));
        let users = BTreeSet::from([name("g")]);
        assert!(matches!(
            prepare_with_policy(&module, "g", &partition, &users, None),
            Err(IrExecutionError::ToolchainApi(declaration))
                if declaration == name(initializer_name)
        ));
        let users = BTreeSet::from([name("g"), name(initializer_name)]);
        assert!(matches!(
            prepare_with_policy(&module, "g", &partition, &users, None),
            Err(IrExecutionError::UserOverridesCensus(declaration))
                if declaration == name(initializer_name)
        ));
    }
}

#[test]
fn initializer_journals_cannot_replace_extern_or_mirror_native_rows() {
    let partition = bounded_partition(&[]);
    for declaration in [
        "Nat.add",
        "ST.Prim.mkRef",
        "IO.getStdout",
        "Lean.Syntax.getArg",
        "Lean.Name.mkStr1",
    ] {
        assert!(
            native_row(&name(declaration)).is_some()
                || fln_vm::macro_native::row_for_name(&name(declaration)).is_some()
        );
        let mut module = module();
        module.decls[0] = global(declaration);
        module.initializers[0].declaration = name(declaration);
        for capture_output_bytes in [None, Some(128)] {
            assert!(matches!(
                prepare_with_policy(
                    &module,
                    declaration,
                    &partition,
                    &BTreeSet::from([name("initG")]),
                    capture_output_bytes,
                ),
                Err(IrExecutionError::InitializerContract {
                    declaration: refused,
                    detail: "initializer cannot replace a native declaration",
                }) if refused == name(declaration)
            ));
        }
    }
}

#[test]
fn initialized_globals_do_not_admit_phase_queries_or_other_host_effects() {
    let partition = bounded_partition(&[]);
    for effect in [
        "IO.initializing",
        "IO.getEnv",
        "IO.Process.spawn",
        "IO.FS.Handle.read",
    ] {
        let row = native_row(&name(effect)).unwrap();
        let arity = native_signature::ir_arity(row).unwrap();
        for partial in [false, true] {
            let mut module = module();
            let IrDecl::Function { body, .. } = &mut module.decls[1] else {
                unreachable!()
            };
            let call = if partial {
                IrExpr::Pap {
                    function: name(effect),
                    args: vec![],
                }
            } else {
                IrExpr::Fap {
                    function: name(effect),
                    args: vec![IrArg::Erased; arity],
                }
            };
            // The result is deliberately unused. A dead direct call or a
            // captured callback must still be authorized before optimization.
            body.stmts.insert(0, binding(3, IrType::TObject, call));
            for capture_output_bytes in [None, Some(128)] {
                assert!(
                    matches!(
                        prepare_with_policy(
                            &module,
                            "g",
                            &partition,
                            &BTreeSet::from([name("g"), name("initG")]),
                            capture_output_bytes,
                        ),
                        Err(IrExecutionError::Unsupported {
                            declaration,
                            form: "effectful native call",
                        }) if declaration == name(effect)
                    ),
                    "{effect}; partial={partial}; capture={capture_output_bytes:?}"
                );
            }
        }
    }
}

#[test]
fn native_initializer_names_cannot_supply_forged_interpreted_io_bodies() {
    let partition = bounded_partition(&[]);
    for initializer_name in [
        "Nat.add",
        "ST.Prim.mkRef",
        "IO.getStdout",
        "Lean.Syntax.getArg",
        "Lean.Name.mkStr1",
    ] {
        assert!(
            native_row(&name(initializer_name)).is_some()
                || fln_vm::macro_native::row_for_name(&name(initializer_name)).is_some()
        );
        let mut module = module();
        // This has exactly the accepted initializer telescope and a benign
        // IO.Result.ok body. Its native name must prevent that body being
        // accepted as the code that the initializer wrapper will dispatch.
        module.decls[1] = initializer(initializer_name, None, 0);
        module.initializers[0].initializer = Some(name(initializer_name));
        for capture_output_bytes in [None, Some(128)] {
            assert!(matches!(
                prepare_with_policy(
                    &module,
                    "g",
                    &partition,
                    &BTreeSet::from([name("g")]),
                    capture_output_bytes,
                ),
                Err(IrExecutionError::InitializerContract { declaration, .. })
                    if declaration == name("g")
            ));
        }
    }
}

#[test]
fn unselected_standalone_actions_in_other_modules_cannot_be_silently_omitted() {
    // A initializes a shared cell; B's standalone startup action writes it;
    // C reads A directly. No B declaration is in C's static call graph.
    let mut a = module();
    let IrDecl::Function { body, .. } = &mut a.decls[1] else {
        unreachable!()
    };
    body.stmts.insert(
        1,
        binding(
            3,
            IrType::TObject,
            IrExpr::Fap {
                function: name("ST.Prim.mkRef"),
                args: vec![IrArg::Var(1)],
            },
        ),
    );
    let IrStmt::VDecl {
        expr: IrExpr::Ctor { args, .. },
        ..
    } = &mut body.stmts[2]
    else {
        unreachable!()
    };
    args[0] = IrArg::Var(3);

    let mut action = initializer("B.advance", Some("g"), 0);
    let IrDecl::Function { body, .. } = &mut action else {
        unreachable!()
    };
    body.stmts.splice(
        1..1,
        [
            binding(
                3,
                IrType::TObject,
                IrExpr::Lit(IrLit::Num(IrNat::Small(43))),
            ),
            binding(
                4,
                IrType::TObject,
                IrExpr::Fap {
                    function: name("ST.Prim.Ref.set"),
                    args: vec![IrArg::Var(1), IrArg::Var(3)],
                },
            ),
            binding(5, IrType::TObject, IrExpr::Lit(IrLit::Num(IrNat::Small(0)))),
        ],
    );
    let IrStmt::VDecl {
        expr: IrExpr::Ctor { args, .. },
        ..
    } = body.stmts.last_mut().unwrap()
    else {
        unreachable!()
    };
    args[0] = IrArg::Var(5);
    let b = IrModule {
        decls: vec![action],
        initializers: vec![InitEntry {
            declaration: name("B.advance"),
            initializer: None,
        }],
        ..IrModule::default()
    };
    let c = IrModule {
        decls: vec![IrDecl::Function {
            name: name("C.read"),
            params: vec![],
            result: IrType::TObject,
            body: IrBody {
                stmts: vec![
                    binding(
                        1,
                        IrType::TObject,
                        IrExpr::Fap {
                            function: name("g"),
                            args: vec![],
                        },
                    ),
                    binding(
                        2,
                        IrType::TObject,
                        IrExpr::Fap {
                            function: name("ST.Prim.Ref.get"),
                            args: vec![IrArg::Var(1)],
                        },
                    ),
                ],
                terminal: Box::new(IrTerminal::Ret(IrArg::Var(2))),
            },
            sorry_dep: None,
        }],
        ..IrModule::default()
    };
    // Only A and C need user classification: B's startup action must not be
    // silently dropped merely because no selected declaration calls it.
    let users = BTreeSet::from([name("g"), name("initG"), name("C.read")]);
    let partition = bounded_partition(&[]);
    for modules in [vec![a.clone(), b.clone(), c.clone()], vec![c, b, a]] {
        assert!(matches!(
            compile_with_options(
                &modules,
                &name("C.read"),
                &[],
                &partition,
                &users,
                IrExecutionOptions {
                    initialize_globals: true,
                    ..IrExecutionOptions::default()
                },
            ),
            Err(IrExecutionError::InitializerContract { declaration, .. })
                if declaration == name("g")
        ));
    }
}
