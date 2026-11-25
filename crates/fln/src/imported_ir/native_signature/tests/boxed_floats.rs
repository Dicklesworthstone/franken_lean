//! Floating extern closures use the same native implementation as direct calls.
//! Exercise scalar boxing through IR, closure capture, FLBC and canonical replay.
use super::*;
use crate::imported_ir::EntryArgument;

const OPERATIONS: [&str; 38] = [
    "add",
    "sub",
    "mul",
    "div",
    "neg",
    "beq",
    "decLe",
    "decLt",
    "ofBits",
    "toBits",
    "abs",
    "sqrt",
    "ceil",
    "floor",
    "round",
    "sin",
    "cos",
    "tan",
    "asin",
    "acos",
    "atan",
    "sinh",
    "cosh",
    "tanh",
    "asinh",
    "acosh",
    "atanh",
    "exp",
    "exp2",
    "log",
    "log2",
    "log10",
    "cbrt",
    "pow",
    "atan2",
    "isNaN",
    "isFinite",
    "isInf",
];

fn boxed_scalar(ty: &IrType) -> IrType {
    // The pin's LCNF wrapper types, independently of the native bridge table.
    match ty {
        IrType::Float | IrType::Float32 | IrType::UInt64 => IrType::Object,
        IrType::UInt32 => IrType::TObject,
        IrType::UInt8 => IrType::Tagged,
        _ => unreachable!("fixture uses only reviewed scalar types"),
    }
}

fn compiled_closure(
    family: &str,
    operation: &str,
    input: IrType,
    result: IrType,
    bits: &[u64],
) -> CompiledIr {
    let floating_input = matches!(input, IrType::Float | IrType::Float32);
    let mut stmts = Vec::new();
    let mut boxed = Vec::new();
    let mut arguments = Vec::new();
    let mut params = Vec::new();
    for (index, bits) in bits.iter().copied().enumerate() {
        let parameter = index as u64 + 1;
        params.push(IrParam {
            x: parameter,
            ty: if floating_input {
                input.clone()
            } else {
                IrType::TObject
            },
            borrow: false,
        });
        arguments.push(match input {
            IrType::Float => EntryArgument::FloatBits(bits),
            IrType::Float32 => EntryArgument::Float32Bits(bits as u32),
            _ => EntryArgument::Nat(IrNat::Small(bits)),
        });
        let raw = if floating_input {
            parameter
        } else {
            let raw = 10 + parameter;
            stmts.push(IrStmt::VDecl {
                x: raw,
                ty: input.clone(),
                expr: IrExpr::Fap {
                    function: name(if input == IrType::UInt64 {
                        "UInt64.ofNat"
                    } else {
                        "UInt32.ofNat"
                    }),
                    args: vec![var(parameter)],
                },
            });
            raw
        };
        let x = 20 + parameter;
        stmts.push(IrStmt::VDecl {
            x,
            ty: boxed_scalar(&input),
            expr: IrExpr::Box {
                ty: input.clone(),
                x: raw,
            },
        });
        boxed.push(var(x));
    }
    let captured = usize::from(bits.len() == 2);
    stmts.push(bind(
        30,
        IrExpr::Pap {
            function: name(&format!("{family}.{operation}._boxed")),
            args: boxed[..captured].to_vec(),
        },
    ));
    // Applying the same closure twice must not consume the captured scalar box.
    for x in [31, 32] {
        stmts.push(IrStmt::VDecl {
            x,
            ty: boxed_scalar(&result),
            expr: IrExpr::Ap {
                x: 30,
                args: boxed[captured..].to_vec(),
            },
        });
    }
    stmts.push(IrStmt::VDecl {
        x: 33,
        ty: result.clone(),
        expr: IrExpr::Unbox { x: 32 },
    });
    let module = IrModule {
        decls: vec![IrDecl::Function {
            name: name("Arity.main"),
            params,
            result,
            body: IrBody {
                stmts,
                terminal: Box::new(IrTerminal::Ret(var(33))),
            },
            sorry_dep: None,
        }],
        ..IrModule::default()
    };
    let compiled = compile(
        &[module],
        &name("Arity.main"),
        &arguments,
        &VerifiedPartition::user_fixture(),
        &BTreeSet::from([name("Arity.main")]),
        IrExecutionLimits::default(),
    )
    .unwrap_or_else(|error| panic!("{family}.{operation}: {error:?}"));
    assert_eq!(compiled.reference_functions().len(), 1);
    assert_eq!(compiled.reference_functions()[0].name, name("Arity.main"));
    assert!(
        compiled
            .native_externs()
            .contains(&format!("extern:{family}.{operation}"))
    );
    compiled
}

fn assert_bits(compiled: &CompiledIr, result: &IrType, expected: u64) {
    let encoded =
        flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default()).unwrap();
    let decoded = flbc::decode_canonical(&encoded, flbc::CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&decoded, flbc::CodecLimits::default()).unwrap(),
        encoded
    );
    for program in [compiled.program.program(), &decoded] {
        let outcome = execute(program, ExecutionLimits::default(), None);
        let Outcome::Complete(VmExit::Returned(value)) = outcome else {
            panic!("{outcome:?}");
        };
        let actual = match result {
            IrType::Float | IrType::UInt64 => value.value.try_ctor_scalar_u64(0),
            IrType::Float32 => value.value.try_ctor_scalar_u32(0).map(u64::from),
            IrType::UInt8 | IrType::UInt32 => {
                assert!(value.value.is_scalar());
                Some(value.value.unbox() as u64)
            }
            _ => unreachable!("fixture result is a reviewed scalar"),
        };
        assert_eq!(actual, Some(expected), "{result:?}");
    }
}

#[test]
fn boxed_float_arithmetic_preserves_width_and_reusable_captures() {
    for (family, ty) in [("Float", IrType::Float), ("Float32", IrType::Float32)] {
        let bits = |value: f64| {
            if ty == IrType::Float {
                value.to_bits()
            } else {
                u64::from((value as f32).to_bits())
            }
        };
        for (operation, arguments, expected) in [
            ("add", vec![bits(1.5), bits(2.5)], bits(4.0)),
            ("sub", vec![bits(1.5), bits(2.5)], bits(-1.0)),
            ("mul", vec![bits(1.5), bits(2.5)], bits(3.75)),
            ("div", vec![bits(1.5), bits(2.5)], bits(0.6)),
            ("neg", vec![bits(0.0)], bits(-0.0)),
            ("div", vec![bits(-1.0), bits(0.0)], bits(f64::NEG_INFINITY)),
        ] {
            let compiled = compiled_closure(family, operation, ty.clone(), ty.clone(), &arguments);
            assert_bits(&compiled, &ty, expected);
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
            assert_bits(&compiled, &ty, expected);
        }
    }
    // A binary32 closure must round at binary32 precision.
    let compiled = compiled_closure(
        "Float32",
        "add",
        IrType::Float32,
        IrType::Float32,
        &[
            u64::from(16_777_216f32.to_bits()),
            u64::from(1f32.to_bits()),
        ],
    );
    assert_bits(
        &compiled,
        &IrType::Float32,
        u64::from(16_777_216f32.to_bits()),
    );
}

#[test]
fn boxed_float_comparisons_keep_nan_and_signed_zero_semantics() {
    for (family, ty) in [("Float", IrType::Float), ("Float32", IrType::Float32)] {
        let bits = |value: f64| {
            if ty == IrType::Float {
                value.to_bits()
            } else {
                u64::from((value as f32).to_bits())
            }
        };
        for (left, right, equal, le, lt) in [
            (-0.0, 0.0, 1, 1, 0),
            (1.5, 2.5, 0, 1, 1),
            (2.5, 1.5, 0, 0, 0),
            (f64::INFINITY, f64::INFINITY, 1, 1, 0),
            (f64::NAN, 1.0, 0, 0, 0),
            (1.0, f64::NAN, 0, 0, 0),
        ] {
            for (operation, expected) in [("beq", equal), ("decLe", le), ("decLt", lt)] {
                let compiled = compiled_closure(
                    family,
                    operation,
                    ty.clone(),
                    IrType::UInt8,
                    &[bits(left), bits(right)],
                );
                assert_bits(&compiled, &IrType::UInt8, expected);
            }
        }
    }
}

#[test]
fn boxed_float_bit_conversions_preserve_carriers_and_public_nan_normalization() {
    for (family, float, word, patterns, nan) in [
        (
            "Float",
            IrType::Float,
            IrType::UInt64,
            [0, 1 << 63, 1, 0x7ff0_0000_0000_0000, 0xfff0_0000_0000_4321],
            0x7ff8_0000_0000_0000,
        ),
        (
            "Float32",
            IrType::Float32,
            IrType::UInt32,
            [0, 1 << 31, 1, 0x7f80_0000, 0xff80_4321],
            0x7fc0_0000,
        ),
    ] {
        for (index, bits) in patterns.into_iter().enumerate() {
            let expected = if index == 4 { nan } else { bits };
            let of_bits = compiled_closure(family, "ofBits", word.clone(), float.clone(), &[bits]);
            assert_bits(&of_bits, &float, expected);
            let to_bits = compiled_closure(family, "toBits", float.clone(), word.clone(), &[bits]);
            assert_bits(&to_bits, &word, expected);
        }
    }
}

#[test]
fn boxed_float_math_preserves_owned_numerics_and_binary_argument_order() {
    for (family, ty) in [("Float", IrType::Float), ("Float32", IrType::Float32)] {
        let bits = |value: f64| {
            if ty == IrType::Float {
                value.to_bits()
            } else {
                u64::from((value as f32).to_bits())
            }
        };
        // Exact special values make this a bridge test rather than a second
        // approximation test for the separately tested owned math library.
        for (operation, input, expected) in [
            ("abs", -0.0, 0.0),
            ("abs", -3.5, 3.5),
            ("sqrt", 4.0, 2.0),
            ("ceil", -1.25, -1.0),
            ("floor", -1.25, -2.0),
            ("round", -1.5, -2.0),
            ("sin", 0.0, 0.0),
            ("cos", 0.0, 1.0),
            ("tan", 0.0, 0.0),
            ("asin", 0.0, 0.0),
            ("acos", 1.0, 0.0),
            ("atan", 0.0, 0.0),
            ("sinh", 0.0, 0.0),
            ("cosh", 0.0, 1.0),
            ("tanh", 0.0, 0.0),
            ("asinh", 0.0, 0.0),
            ("acosh", 1.0, 0.0),
            ("atanh", 0.0, 0.0),
            ("exp", 0.0, 1.0),
            ("exp2", 0.0, 1.0),
            ("log", 1.0, 0.0),
            ("log2", 1.0, 0.0),
            ("log10", 1.0, 0.0),
            ("cbrt", 0.0, 0.0),
        ] {
            let compiled =
                compiled_closure(family, operation, ty.clone(), ty.clone(), &[bits(input)]);
            assert_bits(&compiled, &ty, bits(expected));
        }
        for (operation, left, right, expected) in [
            ("pow", 2.0, -3.0, 0.125),
            ("pow", -2.0, 3.0, -8.0),
            ("atan2", -0.0, 1.0, -0.0),
            ("atan2", 1.0, 0.0, std::f64::consts::FRAC_PI_2),
        ] {
            let compiled = compiled_closure(
                family,
                operation,
                ty.clone(),
                ty.clone(),
                &[bits(left), bits(right)],
            );
            assert_bits(&compiled, &ty, bits(expected));
        }
    }
}

#[test]
fn boxed_float_classification_preserves_nan_infinities_and_signed_zero() {
    for (family, ty) in [("Float", IrType::Float), ("Float32", IrType::Float32)] {
        for (input, nan, finite, infinite) in [
            (0.0, 0, 1, 0),
            (-0.0, 0, 1, 0),
            (1.5, 0, 1, 0),
            (f64::from(f32::MAX), 0, 1, 0),
            (f64::INFINITY, 0, 0, 1),
            (f64::NEG_INFINITY, 0, 0, 1),
            (f64::NAN, 1, 0, 0),
        ] {
            let bits = if ty == IrType::Float {
                input.to_bits()
            } else {
                u64::from((input as f32).to_bits())
            };
            for (operation, expected) in [
                ("isNaN", nan),
                ("isFinite", finite),
                ("isInf", infinite),
            ] {
                let compiled =
                    compiled_closure(family, operation, ty.clone(), IrType::UInt8, &[bits]);
                assert_bits(&compiled, &IrType::UInt8, expected);
            }
        }
    }
}

#[test]
fn boxed_float_width_conversion_rounds_once_and_preserves_subnormals() {
    for (input, expected) in [
        (0, 0),
        (1 << 63, 1 << 31),
        (16_777_217f64.to_bits(), u64::from(16_777_216f32.to_bits())),
        (0x36a0_0000_0000_0000, 1),
        (0x3690_0000_0000_0000, 0),
        (0x36a8_0000_0000_0000, 2),
        (f64::MAX.to_bits(), u64::from(f32::INFINITY.to_bits())),
        (
            f64::NEG_INFINITY.to_bits(),
            u64::from(f32::NEG_INFINITY.to_bits()),
        ),
    ] {
        let compiled = compiled_closure(
            "Float",
            "toFloat32",
            IrType::Float,
            IrType::Float32,
            &[input],
        );
        assert_bits(&compiled, &IrType::Float32, expected);
    }
    for input in [0u32, 1 << 31, 1, 0x7f7f_ffff, 0x7f80_0000, 0xff80_0000] {
        let compiled = compiled_closure(
            "Float32",
            "toFloat",
            IrType::Float32,
            IrType::Float,
            &[u64::from(input)],
        );
        assert_bits(
            &compiled,
            &IrType::Float,
            f64::from(f32::from_bits(input)).to_bits(),
        );
    }
    for target in ["Float.toFloat32", "Float32.toFloat"] {
        let original = crate::imported_ir::native_row(&name(target)).unwrap();
        assert!(BoxedNative::from_row(original).unwrap().is_some());
        let changed = GeneratedExternRow {
            module: "Init.Data.Float",
            ..*original
        };
        assert!(matches!(
            BoxedNative::from_row(&changed),
            Err(IrExecutionError::NativeContract { .. })
        ));
    }
}

#[test]
fn float_closure_contracts_reject_changed_abi_and_unreviewed_operations() {
    for family in ["Float", "Float32"] {
        for operation in OPERATIONS {
            let target = format!("{family}.{operation}");
            let original = crate::imported_ir::native_row(&name(&target)).unwrap();
            assert!(BoxedNative::from_row(original).unwrap().is_some());
            for changed in [
                GeneratedExternRow {
                    symbol: "foreign_float",
                    ..*original
                },
                GeneratedExternRow {
                    module: "Foreign",
                    ..*original
                },
                GeneratedExternRow {
                    ownership: "rule(borrowed-args,owned-result)",
                    ..*original
                },
                GeneratedExternRow {
                    arity: original.arity + 1,
                    ..*original
                },
                GeneratedExternRow {
                    effect: "io",
                    ..*original
                },
                GeneratedExternRow {
                    partition: "library-code",
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
        let row = crate::imported_ir::native_row(&name(&format!("{family}.frExp"))).unwrap();
        assert!(BoxedNative::from_row(row).unwrap().is_none());
    }
}

#[test]
fn pinned_float_native_prototypes_match_boxed_and_unboxed_contracts() {
    let Some(library) = std::env::var_os("FLN_REFERENCE_LIB") else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference artifacts required for native float prototypes"
        );
        eprintln!("SKIP: native float prototypes require FLN_REFERENCE_LIB");
        return;
    };
    for family in ["Float", "Float32"] {
        let path = std::path::Path::new(&library).join(format!("Init/Data/{family}.ir"));
        let bytes = std::fs::read(&path).unwrap();
        fln_olean::pin::check_pinned_header(&bytes).unwrap();
        let module = crate::decode_ir_artifact(&bytes, 32 * 1024 * 1024).unwrap();
        let mut wanted: BTreeSet<_> = OPERATIONS
            .map(|operation| format!("{family}.{operation}"))
            .into_iter()
            .collect();
        if family == "Float32" {
            wanted.extend(["Float.toFloat32".to_owned(), "Float32.toFloat".to_owned()]);
        }
        let mut raw = BTreeSet::new();
        let mut boxed = BTreeSet::new();
        for declaration in module.decls {
            let (row, is_boxed) = match crate::imported_ir::native_row(declaration.name()) {
                Some(row) => (row, false),
                None => {
                    let Some(row) = boxed_row(declaration.name()) else {
                        continue;
                    };
                    (row, true)
                }
            };
            if !wanted.contains(row.name) {
                continue;
            }
            let bridge = BoxedNative::from_row(row).unwrap().unwrap();
            if is_boxed {
                bridge
                    .validate_declaration(&declaration)
                    .unwrap_or_else(|error| {
                        panic!("{} in {path:?}: {error}; {declaration:?}", row.name)
                    });
                assert!(boxed.insert(row.name.to_owned()));
            } else {
                let IrDecl::Extern { params, result, .. } = &declaration else {
                    panic!("{} is not a raw extern", row.name);
                };
                validate_extern_signature(row, params, result).unwrap_or_else(|error| {
                    panic!("{} in {path:?}: {error}; {declaration:?}", row.name)
                });
                assert!(raw.insert(row.name.to_owned()));
            }
        }
        assert_eq!(raw, wanted, "{family}: every raw native prototype");
        assert_eq!(boxed, wanted, "{family}: every compiler boxed prototype");
    }
}
