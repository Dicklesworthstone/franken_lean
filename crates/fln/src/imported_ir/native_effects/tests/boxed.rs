//! First-class primitive actions retain the compiler's full boxed telescope.

use super::*;
use fln_olean::ir::IrParam;

fn partial(x: u64, operation: &str, args: Vec<IrArg>) -> IrStmt {
    bind(
        x,
        IrExpr::Pap {
            function: Name::str(name(operation), "_boxed"),
            args,
        },
    )
}

fn apply(x: u64, closure: u64, args: Vec<IrArg>) -> IrStmt {
    bind(x, IrExpr::Ap { x: closure, args })
}

fn staged_state_sequence() -> IrModule {
    entry(
        vec![
            num(1, 7),
            partial(2, "ST.Prim.mkRef", vec![IrArg::Erased]),
            apply(3, 2, vec![IrArg::Erased, var(1)]),
            apply(4, 3, vec![IrArg::Erased]),
            partial(
                5,
                "ST.Prim.Ref.get",
                vec![IrArg::Erased, IrArg::Erased, var(4)],
            ),
            apply(6, 5, vec![IrArg::Erased]),
            partial(7, "ST.Prim.Ref.set", vec![IrArg::Erased, IrArg::Erased]),
            apply(8, 7, vec![var(4)]),
            num(9, 19),
            apply(10, 8, vec![var(9)]),
            // Supplying the value leaves the world pending: no write yet.
            apply(11, 5, vec![IrArg::Erased]),
            apply(12, 10, vec![IrArg::Erased]),
            partial(
                13,
                "ST.Prim.Ref.swap",
                vec![IrArg::Erased, IrArg::Erased, var(4)],
            ),
            num(14, 23),
            apply(15, 13, vec![var(14), IrArg::Erased]),
            apply(16, 5, vec![IrArg::Erased]),
            partial(
                17,
                "ST.Prim.Ref.take",
                vec![IrArg::Erased, IrArg::Erased, var(4)],
            ),
            apply(18, 17, vec![IrArg::Erased]),
            // Reuse the setter with the same cell after taking its value.
            apply(19, 8, vec![var(1), IrArg::Erased]),
            apply(20, 5, vec![IrArg::Erased]),
            call(21, "Nat.add", &[6, 11]),
            call(22, "Nat.add", &[15, 16]),
            call(23, "Nat.add", &[18, 20]),
            call(24, "Nat.add", &[21, 22]),
            call(25, "Nat.add", &[24, 23]),
        ],
        25,
    )
}

fn boxed_declaration(operation: &str) -> IrDecl {
    let runtime = if matches!(operation, "ST.Prim.Ref.set" | "ST.Prim.Ref.swap") {
        2
    } else {
        1
    };
    IrDecl::Function {
        name: Name::str(name(operation), "_boxed"),
        params: (0..runtime + 3)
            .map(|index| IrParam {
                x: index as u64,
                borrow: false,
                ty: if index == runtime + 2 {
                    IrType::Tagged
                } else {
                    IrType::TObject
                },
            })
            .collect(),
        result: if operation == "ST.Prim.Ref.set" {
            IrType::Tagged
        } else {
            IrType::TObject
        },
        // Even a supplied body with a different result cannot replace a
        // reserved native wrapper. Only its reviewed signature is admitted.
        body: IrBody {
            stmts: vec![num(99, 999)],
            terminal: Box::new(IrTerminal::Ret(var(99))),
        },
        sorry_dep: None,
    }
}

#[test]
fn boxed_state_actions_keep_pending_worlds_and_share_cells_across_repeated_calls() {
    for prototypes in [false, true] {
        let mut module = staged_state_sequence();
        if prototypes {
            module.decls.extend(
                CELL_ROWS
                    .into_iter()
                    .chain(["ST.Prim.Ref.take"])
                    .map(boxed_declaration),
            );
        }
        let compiled = prepare(&module);
        // Reads are 7 before capture, 7 before execution, 19 before swap,
        // 23 after swap, 23 from take, then 7 after the reused setter refills.
        assert_nat_replay(&compiled, "86");
        for operation in CELL_ROWS.into_iter().chain(["ST.Prim.Ref.take"]) {
            assert!(
                compiled
                    .native_externs()
                    .contains(&format!("extern:{operation}"))
            );
            assert!(compiled.reference_functions().iter().all(|function| {
                function.name != name(operation)
                    && function.name != Name::str(name(operation), "_boxed")
            }));
        }
        let stopped = compiled.execute(
            ExecutionLimits {
                max_steps: 12,
                ..ExecutionLimits::default()
            },
            None,
        );
        assert!(matches!(stopped.outcome, Outcome::Inconclusive(_)));
        let cancelled = compiled.execute(ExecutionLimits::default(), Some(&|| true));
        assert!(matches!(cancelled.outcome, Outcome::Inconclusive(_)));
        assert_nat_replay(&compiled, "86");
    }
}

#[test]
fn direct_boxed_state_calls_keep_the_same_telescope_as_indirect_calls() {
    let mut module = state_sequence();
    let IrDecl::Function { body, .. } = &mut module.decls[0] else {
        unreachable!();
    };
    for statement in &mut body.stmts {
        if let IrStmt::VDecl {
            expr: IrExpr::Fap { function, args },
            ..
        } = statement
            && CELL_ROWS
                .iter()
                .any(|operation| *function == name(operation))
        {
            *function = Name::str(function.clone(), "_boxed");
            args.splice(0..0, [IrArg::Erased, IrArg::Erased]);
            args.push(IrArg::Erased);
        }
    }
    assert_nat_replay(&prepare(&module), "42");
}

#[test]
fn boxed_state_prototypes_bind_every_erased_world_borrowing_and_result_slot() {
    for operation in CELL_ROWS.into_iter().chain(["ST.Prim.Ref.take"]) {
        for mutation in 0..7 {
            let mut module = staged_state_sequence();
            let mut prototype = boxed_declaration(operation);
            let IrDecl::Function {
                params,
                result,
                sorry_dep,
                ..
            } = &mut prototype
            else {
                unreachable!();
            };
            match mutation {
                0 => params[0].ty = IrType::Erased,
                1 => params[1].ty = IrType::Tagged,
                2 => params.last_mut().unwrap().ty = IrType::TObject,
                3 => params[2].borrow = true,
                4 => {
                    params.pop();
                }
                5 => *result = IrType::UInt64,
                6 => *sorry_dep = Some(name("sorryAx")),
                _ => unreachable!(),
            }
            module.decls.push(prototype);
            let result = compile_module(
                &module,
                "LocalState.main",
                &[],
                IrExecutionLimits::default(),
            );
            assert!(
                matches!(result, Err(IrExecutionError::NativeContract { .. })),
                "{operation}, mutation {mutation}: {result:?}",
            );
        }
    }
}

#[test]
fn boxed_state_adapters_do_not_hide_invalid_captures_or_admit_other_effects() {
    for operation in CELL_ROWS.into_iter().chain(["ST.Prim.Ref.take"]) {
        let module = entry(vec![partial(1, operation, vec![var(999_999)])], 1);
        assert!(matches!(
            compile_module(
                &module,
                "LocalState.main",
                &[],
                IrExecutionLimits::default(),
            ),
            Err(IrExecutionError::IrValidation(_))
        ));
    }
    for operation in ["ST.Prim.Ref.ptrEq", "IO.initializing", "IO.getStdout"] {
        let module = entry(vec![partial(1, operation, vec![])], 1);
        assert!(matches!(
            compile_module(
                &module,
                "LocalState.main",
                &[],
                IrExecutionLimits::default(),
            ),
            Err(IrExecutionError::Unsupported { .. })
        ));
    }
}
