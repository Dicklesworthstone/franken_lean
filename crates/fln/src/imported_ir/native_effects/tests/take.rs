//! The destructive read used by the pin's public modify/modifyGet operations.

use super::*;
use fln_olean::ir::IrParam;
use fln_vm::interpreter::VmRefusal;

const TAKE: &str = "ST.Prim.Ref.take";

fn update_sequence() -> IrModule {
    entry(
        vec![
            num(1, 7),
            call(2, "ST.Prim.mkRef", &[1]),
            call(3, TAKE, &[2]),
            num(4, 1),
            call(5, "Nat.add", &[3, 4]),
            call(6, "ST.Prim.Ref.set", &[2, 5]),
            call(7, "ST.Prim.Ref.get", &[2]),
            call(8, "Nat.add", &[3, 7]),
        ],
        8,
    )
}

#[test]
fn take_moves_the_occupant_and_refill_is_visible_through_the_original_handle() {
    let compiled = prepare(&update_sequence());
    assert_nat_replay(&compiled, "15");
    assert!(
        compiled
            .native_externs()
            .contains(&format!("extern:{TAKE}"))
    );
    let row = native_row(&name(TAKE)).unwrap();
    assert_eq!(native_signature::inferred_arity(row).unwrap(), 1);
    let native = Native::new(row, 1).unwrap();
    assert_eq!(native.arguments, vec![flbc::ArgumentOwnership::Borrowed]);
    assert_eq!(native.result, flbc::ResultOwnership::Owned);
    assert_eq!(native.effect, fir::EffectClass::State);
}

#[test]
fn explicit_take_declarations_cannot_override_the_reviewed_runtime_arity() {
    for arity in 0..=5 {
        let mut module = update_sequence();
        module.decls.push(IrDecl::Extern {
            name: name(TAKE),
            params: (0..arity)
                .map(|x| IrParam {
                    x,
                    borrow: true,
                    ty: IrType::TObject,
                })
                .collect(),
            result: IrType::TObject,
            entries: vec![],
        });
        let compiled = compile_module(
            &module,
            "LocalState.main",
            &[],
            IrExecutionLimits::default(),
        );
        if arity == 1 {
            assert_nat_replay(&compiled.unwrap(), "15");
        } else {
            assert!(matches!(
                compiled,
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
    }
}

#[test]
fn take_bridge_refuses_contract_drift_without_erasing_other_rule_telescope_binders() {
    let row = *native_row(&name(TAKE)).unwrap();
    for changed in [
        GeneratedExternRow {
            name: "Other.take",
            ..row
        },
        GeneratedExternRow {
            module: "Other",
            ..row
        },
        GeneratedExternRow {
            kind: "defn",
            ..row
        },
        GeneratedExternRow {
            symbol: "other_take",
            ..row
        },
        GeneratedExternRow { levels: 1, ..row },
        GeneratedExternRow { arity: 4, ..row },
        GeneratedExternRow {
            effect: "pure",
            ..row
        },
        GeneratedExternRow {
            safety: "safe",
            ..row
        },
        GeneratedExternRow {
            ownership: "rule(borrowed-args,borrowed-result)",
            ..row
        },
    ] {
        assert!(matches!(
            native_signature::inferred_arity(&changed),
            Err(IrExecutionError::NativeContract { .. })
        ));
    }
    let mut unmodified = 0;
    for row in EXTERN_ROWS {
        if row.name != TAKE && row.ownership == "rule(borrowed-args,owned-result)" {
            assert_eq!(
                native_signature::inferred_arity(row).unwrap(),
                row.arity as usize
            );
            unmodified += 1;
        }
    }
    assert!(unmodified > 0);
}

#[test]
fn reusable_update_callbacks_take_once_per_invocation_and_share_the_cell() {
    let mut module = entry(
        vec![
            num(1, 7),
            call(2, "ST.Prim.mkRef", &[1]),
            bind(
                3,
                IrExpr::Pap {
                    function: name("LocalState.update"),
                    args: vec![var(2)],
                },
            ),
            num(4, 19),
            bind(
                5,
                IrExpr::Ap {
                    x: 3,
                    args: vec![var(4)],
                },
            ),
            num(6, 23),
            bind(
                7,
                IrExpr::Ap {
                    x: 3,
                    args: vec![var(6)],
                },
            ),
            call(8, "ST.Prim.Ref.get", &[2]),
            call(9, "Nat.add", &[5, 7]),
            call(10, "Nat.add", &[9, 8]),
        ],
        10,
    );
    module.decls.push(IrDecl::Function {
        name: name("LocalState.update"),
        params: (0..2)
            .map(|x| IrParam {
                x,
                borrow: false,
                ty: IrType::TObject,
            })
            .collect(),
        result: IrType::TObject,
        body: IrBody {
            stmts: vec![
                call(2, TAKE, &[0]),
                call(3, "Nat.add", &[2, 1]),
                call(4, "ST.Prim.Ref.set", &[0, 3]),
            ],
            terminal: Box::new(IrTerminal::Ret(var(2))),
        },
        sorry_dep: None,
    });
    // The callbacks return 7 and 26; the original handle now contains 49.
    assert_nat_replay(&prepare(&module), "82");
}

#[test]
fn taken_array_payloads_preserve_external_and_taken_aliases_during_updates() {
    let compiled = prepare(&entry(
        vec![
            num(1, 4),
            call(2, "Array.emptyWithCapacity", &[1]),
            num(3, 19),
            call(4, "Array.push", &[2, 3]),
            call(5, "ST.Prim.mkRef", &[4]),
            call(6, TAKE, &[5]),
            num(7, 23),
            call(8, "Array.push", &[6, 7]),
            call(9, "ST.Prim.Ref.set", &[5, 8]),
            call(10, "ST.Prim.Ref.get", &[5]),
            call(11, "Array.size", &[4]),
            call(12, "Array.size", &[6]),
            call(13, "Array.size", &[10]),
            call(14, "Nat.add", &[11, 12]),
            call(15, "Nat.add", &[14, 13]),
        ],
        15,
    ));
    // Both pre-update aliases retain one element; the refilled cell has two.
    assert_nat_replay(&compiled, "4");
}

#[test]
fn empty_cells_refuse_reads_takes_and_swaps_even_when_the_result_is_unused() {
    for operation in ["ST.Prim.Ref.get", TAKE, "ST.Prim.Ref.swap"] {
        let args = if operation.ends_with("swap") {
            vec![2, 3]
        } else {
            vec![2]
        };
        let compiled = prepare(&entry(
            vec![
                num(1, 7),
                call(2, "ST.Prim.mkRef", &[1]),
                call(3, TAKE, &[2]),
                call(4, operation, &args),
                num(5, 42),
            ],
            5,
        ));
        let bytes =
            flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default())
                .unwrap();
        let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
        for program in [compiled.program.program(), &replay] {
            assert!(matches!(
                execute(program, ExecutionLimits::default(), None),
                Outcome::Complete(VmExit::Refused {
                    refusal: VmRefusal::InvalidRefObject,
                    ..
                })
            ));
        }
    }
}

#[test]
fn take_checks_scalar_and_heap_handles_before_touching_the_cell() {
    for value in [
        num(1, 7),
        bind(1, IrExpr::Lit(IrLit::Str("not a cell".to_owned()))),
    ] {
        let compiled = prepare(&entry(vec![value, call(2, TAKE, &[1])], 2));
        assert!(matches!(
            compiled.execute(ExecutionLimits::default(), None).outcome,
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::TypeMismatch {
                    operation: TAKE,
                    argument: 0,
                    ..
                },
                ..
            })
        ));
    }
}

#[test]
fn stopping_between_take_and_refill_does_not_publish_a_result_or_poison_a_retry() {
    let compiled = prepare(&update_sequence());
    let mut stopped = false;
    let mut completed = false;
    for max_steps in 0..128 {
        match compiled
            .execute(
                ExecutionLimits {
                    max_steps,
                    ..ExecutionLimits::default()
                },
                None,
            )
            .outcome
        {
            Outcome::Inconclusive(_) => stopped = true,
            Outcome::Complete(VmExit::Returned(value)) => {
                assert_eq!(nat_decimal(&value.value).as_deref(), Some("15"));
                completed = true;
            }
            other => panic!("unexpected update outcome: {other:?}"),
        }
        assert_nat_replay(&compiled, "15");
    }
    assert!(stopped && completed);
}

fn reference_cell_form(mut module: IrModule) -> IrModule {
    for declaration in &mut module.decls {
        let IrDecl::Function { body, .. } = declaration else {
            continue;
        };
        for statement in &mut body.stmts {
            let IrStmt::VDecl {
                expr: IrExpr::Fap { function, args },
                ..
            } = statement
            else {
                continue;
            };
            let name = function.to_display_string();
            if name != TAKE && !CELL_ROWS.contains(&name.as_str()) {
                continue;
            }
            let mut full = vec![IrArg::Erased, IrArg::Erased];
            full.append(args);
            full.push(IrArg::Erased);
            *args = full;
        }
    }
    module
}

fn reference_cell_extern(operation: &str) -> IrDecl {
    let runtime = if matches!(operation, "ST.Prim.Ref.set" | "ST.Prim.Ref.swap") {
        2
    } else {
        1
    };
    IrDecl::Extern {
        name: name(operation),
        params: (0..runtime + 3)
            .map(|index| IrParam {
                x: index as u64,
                borrow: index == 2 && operation != "ST.Prim.mkRef",
                ty: if index < 2 {
                    IrType::Erased
                } else if index == runtime + 2 {
                    IrType::Void
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
        entries: vec![],
    }
}

#[test]
fn reference_cell_telescope_preserves_raw_values_and_native_operand_forms() {
    for (module, expected) in [(state_sequence(), "42"), (update_sequence(), "15")] {
        assert_nat_replay(&prepare(&module), expected);
        let mut full = reference_cell_form(module);
        assert_nat_replay(&prepare(&full), expected);
        for operation in CELL_ROWS.into_iter().chain([TAKE]) {
            full.decls.push(reference_cell_extern(operation));
        }
        assert_nat_replay(&prepare(&full), expected);
    }
}

#[test]
fn erased_cell_bridge_never_drops_data_or_hides_an_undefined_reference() {
    for operation in CELL_ROWS.into_iter().chain([TAKE]) {
        let source = || {
            reference_cell_form(if operation == TAKE {
                update_sequence()
            } else {
                state_sequence()
            })
        };
        let runtime = if matches!(operation, "ST.Prim.Ref.set" | "ST.Prim.Ref.swap") {
            2
        } else {
            1
        };
        for slot in [0, 1, runtime + 2] {
            let mut module = source();
            let IrDecl::Function { body, .. } = &mut module.decls[0] else {
                unreachable!();
            };
            for statement in &mut body.stmts {
                if let IrStmt::VDecl {
                    expr: IrExpr::Fap { function, args },
                    ..
                } = statement
                    && function == &name(operation)
                {
                    // This is a bound, ordinary data value, so the refusal
                    // specifically tests erasure, not a missing-variable error.
                    args[slot] = var(1);
                }
            }
            assert!(matches!(
                compile_module(
                    &module,
                    "LocalState.main",
                    &[],
                    IrExecutionLimits::default()
                ),
                Err(IrExecutionError::Unsupported {
                    form: "non-erased native state type or world operand",
                    ..
                })
            ));
        }
        let mut module = source();
        let IrDecl::Function { body, .. } = &mut module.decls[0] else {
            unreachable!();
        };
        for statement in &mut body.stmts {
            if let IrStmt::VDecl {
                expr: IrExpr::Fap { function, args },
                ..
            } = statement
                && function == &name(operation)
            {
                args[2] = var(999_999);
            }
        }
        assert!(matches!(
            compile_module(
                &module,
                "LocalState.main",
                &[],
                IrExecutionLimits::default()
            ),
            Err(IrExecutionError::IrValidation(_))
        ));
    }
}

#[test]
fn reference_cell_externs_bind_erasure_borrowing_and_result_representation() {
    for operation in CELL_ROWS.into_iter().chain([TAKE]) {
        for mutation in 0..5 {
            let mut module = reference_cell_form(if operation == TAKE {
                update_sequence()
            } else {
                state_sequence()
            });
            let mut external = reference_cell_extern(operation);
            let IrDecl::Extern { params, result, .. } = &mut external else {
                unreachable!();
            };
            match mutation {
                0 => params[0].ty = IrType::TObject,
                1 => params[1].ty = IrType::TObject,
                2 => params.last_mut().unwrap().ty = IrType::TObject,
                3 => params[2].borrow = !params[2].borrow,
                4 => *result = IrType::UInt64,
                _ => unreachable!(),
            }
            module.decls.push(external);
            assert!(matches!(
                compile_module(
                    &module,
                    "LocalState.main",
                    &[],
                    IrExecutionLimits::default()
                ),
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
    }
}

#[test]
fn reference_cell_bridge_authority_is_bound_to_each_generated_row() {
    for operation in CELL_ROWS.into_iter().chain([TAKE]) {
        let row = *native_row(&name(operation)).unwrap();
        let runtime = native_signature::inferred_arity(&row).unwrap();
        assert_eq!(
            native_signature::state_runtime_arity(&row).unwrap(),
            Some(runtime)
        );
        assert_eq!(
            native_signature::validated_ir_arity(&row, runtime).unwrap(),
            runtime
        );
        assert_eq!(
            native_signature::validated_ir_arity(&row, runtime + 3).unwrap(),
            runtime
        );
        for changed in [
            GeneratedExternRow {
                module: "Other",
                ..row
            },
            GeneratedExternRow {
                symbol: "other_cell_operation",
                ..row
            },
            GeneratedExternRow {
                arity: row.arity + 1,
                ..row
            },
            GeneratedExternRow {
                ownership: "rule(borrowed-args,borrowed-result)",
                ..row
            },
        ] {
            assert!(matches!(
                native_signature::state_runtime_arity(&changed),
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
    }
    assert_eq!(
        native_signature::state_runtime_arity(native_row(&name("Nat.add")).unwrap()).unwrap(),
        None
    );
}

#[test]
fn explicit_reference_cell_telescope_cannot_be_reinterpreted_as_native_calls_or_closures() {
    for operation in CELL_ROWS.into_iter().chain([TAKE]) {
        for partial in [false, true] {
            let mut module = reference_cell_form(if operation == TAKE {
                update_sequence()
            } else {
                state_sequence()
            });
            let IrDecl::Function { body, .. } = &mut module.decls[0] else {
                unreachable!();
            };
            for statement in &mut body.stmts {
                let IrStmt::VDecl { expr, .. } = statement else {
                    continue;
                };
                let IrExpr::Fap { function, args } = expr else {
                    continue;
                };
                if function != &name(operation) {
                    continue;
                }
                if partial {
                    let function = function.clone();
                    *expr = IrExpr::Pap {
                        function,
                        args: vec![],
                    };
                } else {
                    args.truncate(args.len() - 1);
                    args.drain(..2).for_each(drop);
                }
            }
            module.decls.push(reference_cell_extern(operation));
            let error = compile_module(
                &module,
                "LocalState.main",
                &[],
                IrExecutionLimits::default(),
            )
            .unwrap_err();
            assert!(matches!(
                error,
                IrExecutionError::Unsupported {
                    form: "first-class erased native state primitive"
                        | "native state call omits explicit erased telescope",
                    ..
                }
            ));
        }
    }
}
