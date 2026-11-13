use super::*;
use fln_vm::interpreter::VmRefusal;

pub(super) const NAMES: [&str; 18] = [
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.div",
    "Nat.mod",
    "Nat.pow",
    "Nat.pred",
    "Nat.beq",
    "Nat.ble",
    "Nat.decEq",
    "Nat.decLe",
    "Nat.decLt",
    "String.append",
    "String.push",
    "String.length",
    "String.utf8ByteSize",
    "String.decEq",
    "String.hash",
];

pub(super) const STRING_PREDICATES: [&str; 2] =
    ["String.Internal.isEmpty", "String.Internal.isPrefixOf"];

pub(super) const WORD_FAMILIES: [&str; 5] = ["UInt8", "UInt16", "UInt32", "UInt64", "USize"];
pub(super) const WORD_OPERATIONS: [&str; 18] = [
    "add",
    "sub",
    "mul",
    "div",
    "mod",
    "land",
    "lor",
    "xor",
    "shiftLeft",
    "shiftRight",
    "complement",
    "neg",
    "log2",
    "decEq",
    "decLe",
    "decLt",
    "ofNat",
    "toNat",
];

pub(super) fn names() -> Vec<String> {
    NAMES
        .into_iter()
        .map(str::to_owned)
        .chain(WORD_FAMILIES.into_iter().flat_map(|family| {
            WORD_OPERATIONS
                .into_iter()
                .map(move |operation| format!("{family}.{operation}"))
        }))
        .collect()
}

fn row(target: &str) -> &'static GeneratedExternRow {
    crate::imported_ir::native_row(&name(target)).unwrap()
}

#[test]
fn reviewed_boxed_primitives_bind_the_generated_row_before_admitting_a_wrapper() {
    for target in names()
        .into_iter()
        .chain(STRING_PREDICATES.into_iter().map(str::to_owned))
    {
        let original = row(&target);
        assert!(BoxedNative::from_row(original).unwrap().is_some());
        for changed in [
            GeneratedExternRow {
                name: "Foreign.value",
                ..*original
            },
            GeneratedExternRow {
                symbol: "foreign_value",
                ..*original
            },
            GeneratedExternRow {
                module: "Foreign",
                ..*original
            },
            GeneratedExternRow {
                kind: "axiom",
                ..*original
            },
            GeneratedExternRow {
                arity: original.arity + 1,
                ..*original
            },
            GeneratedExternRow {
                levels: 1,
                ..*original
            },
            GeneratedExternRow {
                ownership: if original.ownership == "rule(borrowed-args,owned-result)" {
                    "abi((s: borrowed_arg) -> owned_res)"
                } else {
                    "rule(borrowed-args,owned-result)"
                },
                ..*original
            },
            GeneratedExternRow {
                effect: "io",
                ..*original
            },
            GeneratedExternRow {
                safety: "unsafe",
                ..*original
            },
            GeneratedExternRow {
                partition: "library-code",
                ..*original
            },
            GeneratedExternRow {
                entry_scope: "unreviewed",
                ..*original
            },
            GeneratedExternRow {
                profile: "standard",
                ..*original
            },
        ] {
            assert!(
                matches!(
                    BoxedNative::from_row(&changed),
                    Err(IrExecutionError::NativeContract { .. })
                ),
                "{target}: {changed:?}"
            );
        }
    }
    for target in ["Nat.divExact", "Nat.gcd", "String.extract", "Int.divExact"] {
        assert!(BoxedNative::from_row(row(target)).unwrap().is_none());
    }
}

#[test]
fn primitive_prototypes_distinguish_borrowing_and_boxed_scalar_representations() {
    for (target, parameters, result, boxed_parameters, boxed_result) in [
        (
            "Nat.add",
            vec![(IrType::TObject, true), (IrType::TObject, true)],
            IrType::TObject,
            vec![IrType::TObject, IrType::TObject],
            IrType::TObject,
        ),
        (
            "Nat.decLt",
            vec![(IrType::TObject, true), (IrType::TObject, true)],
            IrType::UInt8,
            vec![IrType::TObject, IrType::TObject],
            IrType::Tagged,
        ),
        (
            "String.push",
            vec![(IrType::Object, false), (IrType::UInt32, false)],
            IrType::Object,
            vec![IrType::Object, IrType::TObject],
            IrType::Object,
        ),
        (
            "String.hash",
            vec![(IrType::Object, true)],
            IrType::UInt64,
            vec![IrType::Object],
            IrType::Object,
        ),
        (
            "String.Internal.isEmpty",
            vec![(IrType::Object, false)],
            IrType::UInt8,
            vec![IrType::Object],
            IrType::Tagged,
        ),
        (
            "String.Internal.isPrefixOf",
            vec![(IrType::Object, false), (IrType::Object, false)],
            IrType::UInt8,
            vec![IrType::Object, IrType::Object],
            IrType::Tagged,
        ),
        (
            "UInt16.add",
            vec![(IrType::UInt16, false), (IrType::UInt16, false)],
            IrType::UInt16,
            vec![IrType::Tagged, IrType::Tagged],
            IrType::Tagged,
        ),
        (
            "UInt64.decLt",
            vec![(IrType::UInt64, false), (IrType::UInt64, false)],
            IrType::UInt8,
            vec![IrType::Object, IrType::Object],
            IrType::Tagged,
        ),
        (
            "USize.ofNat",
            vec![(IrType::TObject, true)],
            IrType::USize,
            vec![IrType::TObject],
            IrType::TObject,
        ),
    ] {
        let native = row(target);
        let bridge = BoxedNative::from_row(native).unwrap().unwrap();
        let params: Vec<_> = parameters
            .into_iter()
            .enumerate()
            .map(|(x, (ty, borrow))| IrParam {
                x: x as u64,
                ty,
                borrow,
            })
            .collect();
        validate_extern_signature(native, &params, &result).unwrap();
        for index in 0..params.len() {
            let mut wrong = params.clone();
            wrong[index].borrow = !wrong[index].borrow;
            assert!(matches!(
                validate_extern_signature(native, &wrong, &result),
                Err(IrExecutionError::NativeContract { .. })
            ));
            wrong = params.clone();
            wrong[index].ty = IrType::Erased;
            assert!(matches!(
                validate_extern_signature(native, &wrong, &result),
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
        assert!(matches!(
            validate_extern_signature(native, &params, &IrType::Void),
            Err(IrExecutionError::NativeContract { .. })
        ));
        let prototype = IrDecl::Extern {
            name: Name::str(name(target), "_boxed"),
            params: boxed_parameters
                .into_iter()
                .enumerate()
                .map(|(x, ty)| IrParam {
                    x: x as u64,
                    ty,
                    borrow: false,
                })
                .collect(),
            result: boxed_result,
            entries: vec![],
        };
        bridge.validate_declaration(&prototype).unwrap();
        for index in 0..params.len() {
            for change_type in [false, true] {
                let mut wrong = prototype.clone();
                let IrDecl::Extern { params, .. } = &mut wrong else {
                    unreachable!()
                };
                if change_type {
                    params[index].ty = IrType::UInt64;
                } else {
                    params[index].borrow = true;
                }
                assert!(matches!(
                    bridge.validate_declaration(&wrong),
                    Err(IrExecutionError::NativeContract { .. })
                ));
            }
        }
        let mut wrong = prototype;
        let IrDecl::Extern { result, .. } = &mut wrong else {
            unreachable!()
        };
        *result = IrType::UInt64;
        assert!(matches!(
            bridge.validate_declaration(&wrong),
            Err(IrExecutionError::NativeContract { .. })
        ));
    }
}

#[test]
fn boxed_string_append_preserves_reused_consuming_captures_and_inputs() {
    let compiled = compile_declarations(vec![entry(
        vec![
            bind(1, IrExpr::Lit(IrLit::Str("λ".to_owned()))),
            bind(
                2,
                IrExpr::Pap {
                    function: name("String.append._boxed"),
                    args: vec![var(1)],
                },
            ),
            bind(3, IrExpr::Lit(IrLit::Str("🦀".to_owned()))),
            bind(
                4,
                IrExpr::Ap {
                    x: 2,
                    args: vec![var(3)],
                },
            ),
            bind(
                5,
                IrExpr::Ap {
                    x: 2,
                    args: vec![var(1)],
                },
            ),
            call(6, "String.length", &[1]),
            call(7, "String.length", &[4]),
            call(8, "String.utf8ByteSize", &[5]),
            call(9, "Nat.add", &[6, 7]),
            call(10, "Nat.add", &[9, 8]),
        ],
        10,
    )])
    .unwrap();
    assert_nat(&compiled, "7");
}

#[test]
fn boxed_word_add_reuses_capture_and_preserves_full_width() {
    let typed = |x, ty, expr| IrStmt::VDecl { x, ty, expr };
    let compiled = compile_declarations(vec![entry(
        vec![
            num(1, u64::MAX),
            typed(
                2,
                IrType::UInt64,
                IrExpr::Fap {
                    function: name("UInt64.ofNat"),
                    args: vec![var(1)],
                },
            ),
            num(3, 2),
            typed(
                4,
                IrType::UInt64,
                IrExpr::Fap {
                    function: name("UInt64.ofNat"),
                    args: vec![var(3)],
                },
            ),
            typed(
                5,
                IrType::Object,
                IrExpr::Box {
                    ty: IrType::UInt64,
                    x: 2,
                },
            ),
            typed(
                6,
                IrType::Object,
                IrExpr::Pap {
                    function: name("UInt64.add._boxed"),
                    args: vec![var(5)],
                },
            ),
            typed(
                7,
                IrType::Object,
                IrExpr::Box {
                    ty: IrType::UInt64,
                    x: 4,
                },
            ),
            typed(
                8,
                IrType::Object,
                IrExpr::Ap {
                    x: 6,
                    args: vec![var(7)],
                },
            ),
            typed(
                9,
                IrType::Object,
                IrExpr::Ap {
                    x: 6,
                    args: vec![var(5)],
                },
            ),
            typed(10, IrType::UInt64, IrExpr::Unbox { x: 8 }),
            typed(11, IrType::UInt64, IrExpr::Unbox { x: 9 }),
            call(12, "UInt64.toNat", &[10]),
            call(13, "UInt64.toNat", &[11]),
            call(14, "Nat.add", &[12, 13]),
        ],
        14,
    )])
    .unwrap();
    assert_nat(&compiled, &u64::MAX.to_string());
    assert!(
        compiled
            .reference_functions()
            .iter()
            .all(|function| { function.name == name("Arity.main") }),
        "native boxed wrappers never authorize interpreting toolchain bodies"
    );
}

#[test]
fn boxed_words_execute_native_arithmetic_decisions_and_conversions() {
    for (family, ty, boxed, mask) in [
        ("UInt8", IrType::UInt8, IrType::Tagged, u64::from(u8::MAX)),
        (
            "UInt16",
            IrType::UInt16,
            IrType::Tagged,
            u64::from(u16::MAX),
        ),
        (
            "UInt32",
            IrType::UInt32,
            IrType::TObject,
            u64::from(u32::MAX),
        ),
        ("UInt64", IrType::UInt64, IrType::Object, u64::MAX),
        ("USize", IrType::USize, IrType::TObject, usize::MAX as u64),
    ] {
        for (operation, operands, expected) in [
            ("add", vec![mask, 2], 1),
            ("sub", vec![0, 1], mask),
            ("mul", vec![42, 7], 294 & mask),
            ("div", vec![42, 7], 6),
            ("div", vec![42, 0], 0),
            ("mod", vec![43, 7], 1),
            ("mod", vec![43, 0], 43),
            ("land", vec![42, 7], 2),
            ("lor", vec![42, 7], 47),
            ("xor", vec![42, 7], 45),
            ("shiftLeft", vec![42, 7], 5376 & mask),
            ("shiftRight", vec![42, 2], 10),
            ("complement", vec![42], mask - 42),
            ("neg", vec![42], mask - 41),
            ("log2", vec![42], 5),
            ("decEq", vec![mask, mask], 1),
            ("decEq", vec![mask, 0], 0),
            ("decLe", vec![0, mask], 1),
            ("decLe", vec![mask, 0], 0),
            ("decLt", vec![0, mask], 1),
            ("decLt", vec![mask, mask], 0),
            ("ofNat", vec![u64::MAX], mask),
            ("toNat", vec![mask], mask),
        ] {
            let declaration = boxed_word_program(family, &ty, &boxed, operation, &operands);
            let compiled = compile_declarations(vec![declaration])
                .unwrap_or_else(|error| panic!("{family}.{operation}: {error}"));
            assert_nat(&compiled, &expected.to_string());
            assert!(
                compiled
                    .native_externs()
                    .contains(&format!("extern:{family}.{operation}"))
            );
            assert!(
                compiled
                    .reference_functions()
                    .iter()
                    .all(|function| function.name == name("Arity.main"))
            );
        }
    }
}

fn boxed_word_program(
    family: &str,
    ty: &IrType,
    boxed: &IrType,
    operation: &str,
    operands: &[u64],
) -> IrDecl {
    let mut statements = Vec::new();
    let mut arguments = Vec::new();
    for (index, &value) in operands.iter().enumerate() {
        let input = (index as u64) * 3 + 1;
        statements.push(num(input, value));
        if operation == "ofNat" {
            arguments.push(var(input));
        } else {
            statements.push(IrStmt::VDecl {
                x: input + 1,
                ty: ty.clone(),
                expr: IrExpr::Fap {
                    function: name(&format!("{family}.ofNat")),
                    args: vec![var(input)],
                },
            });
            statements.push(IrStmt::VDecl {
                x: input + 2,
                ty: boxed.clone(),
                expr: IrExpr::Box {
                    ty: ty.clone(),
                    x: input + 1,
                },
            });
            arguments.push(var(input + 2));
        }
    }
    let last = arguments.pop().unwrap();
    statements.push(IrStmt::VDecl {
        x: 10,
        ty: IrType::Object,
        expr: IrExpr::Pap {
            function: name(&format!("{family}.{operation}._boxed")),
            args: arguments,
        },
    });
    let decision = matches!(operation, "decEq" | "decLe" | "decLt");
    let result_type = if decision {
        IrType::Tagged
    } else if operation == "toNat" {
        if matches!(ty, IrType::UInt8 | IrType::UInt16) {
            IrType::Tagged
        } else {
            IrType::TObject
        }
    } else {
        boxed.clone()
    };
    statements.push(IrStmt::VDecl {
        x: 11,
        ty: result_type,
        expr: IrExpr::Ap {
            x: 10,
            args: vec![last],
        },
    });
    if operation == "toNat" {
        return entry(statements, 11);
    }
    statements.push(IrStmt::VDecl {
        x: 12,
        ty: if decision { IrType::UInt8 } else { ty.clone() },
        expr: IrExpr::Unbox { x: 11 },
    });
    statements.push(IrStmt::VDecl {
        x: 13,
        ty: if decision || matches!(ty, IrType::UInt8 | IrType::UInt16) {
            IrType::Tagged
        } else {
            IrType::TObject
        },
        expr: IrExpr::Fap {
            function: name(&format!(
                "{}.toNat",
                if decision { "UInt8" } else { family }
            )),
            args: vec![var(12)],
        },
    });
    entry(statements, 13)
}

#[test]
fn boxed_primitive_bodies_bad_scope_and_bad_values_cannot_replace_native_semantics() {
    let caller = |capture| {
        entry(
            vec![
                num(1, 19),
                num(2, 23),
                bind(
                    3,
                    IrExpr::Pap {
                        function: name("Nat.add._boxed"),
                        args: vec![capture],
                    },
                ),
                bind(
                    4,
                    IrExpr::Ap {
                        x: 3,
                        args: vec![var(2)],
                    },
                ),
            ],
            4,
        )
    };
    let forged = IrDecl::Function {
        name: name("Nat.add._boxed"),
        params: vec![
            IrParam {
                x: 1,
                borrow: false,
                ty: IrType::TObject,
            },
            IrParam {
                x: 2,
                borrow: false,
                ty: IrType::TObject,
            },
        ],
        result: IrType::TObject,
        body: IrBody {
            stmts: vec![num(3, 999)],
            terminal: Box::new(IrTerminal::Ret(var(3))),
        },
        sorry_dep: None,
    };
    assert_nat(
        &compile_declarations(vec![caller(var(1)), forged.clone()]).unwrap(),
        "42",
    );
    let mut sorry = forged;
    let IrDecl::Function { sorry_dep, .. } = &mut sorry else {
        unreachable!()
    };
    *sorry_dep = Some(name("sorryAx"));
    assert!(matches!(
        compile_declarations(vec![caller(var(1)), sorry]),
        Err(IrExecutionError::NativeContract { .. })
    ));
    assert!(matches!(
        compile_declarations(vec![caller(var(999))]),
        Err(IrExecutionError::IrValidation(_))
    ));
    let mut bad_value = caller(var(1));
    let IrDecl::Function { body, .. } = &mut bad_value else {
        unreachable!()
    };
    body.stmts[0] = bind(1, IrExpr::Lit(IrLit::Str("not a Nat".to_owned())));
    let compiled = compile_declarations(vec![bad_value]).unwrap();
    assert!(matches!(
        compiled.execute(ExecutionLimits::default(), None).outcome,
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::TypeMismatch { .. },
            ..
        })
    ));
    assert_nat(&compile_declarations(vec![caller(var(1))]).unwrap(), "42");
}
