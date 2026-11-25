//! Native signed-word closures: carriers, signed semantics and retained captures.
use super::*;
use fln_vm::interpreter::VmRefusal;

const FAMILIES: [&str; 5] = ["Int8", "Int16", "Int32", "Int64", "ISize"];
const OPERATIONS: [&str; 19] = [
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
    "abs",
    "decEq",
    "decLe",
    "decLt",
    "ofNat",
    "ofInt",
    "toInt",
];

pub(super) fn names() -> Vec<String> {
    FAMILIES
        .into_iter()
        .flat_map(|family| {
            OPERATIONS
                .into_iter()
                .map(move |operation| format!("{family}.{operation}"))
                .chain(
                    FAMILIES
                        .into_iter()
                        .filter(move |target| *target != family)
                        .map(move |target| format!("{family}.to{target}")),
                )
        })
        .collect()
}

fn types(family: &str) -> (IrType, IrType, u32) {
    match family {
        "Int8" => (IrType::UInt8, IrType::Tagged, 8),
        "Int16" => (IrType::UInt16, IrType::Tagged, 16),
        "Int32" => (IrType::UInt32, IrType::TObject, 32),
        "Int64" => (IrType::UInt64, IrType::Object, 64),
        "ISize" => (IrType::USize, IrType::TObject, usize::BITS),
        _ => panic!("unreviewed signed family: {family}"),
    }
}

fn typed(x: u64, ty: IrType, expr: IrExpr) -> IrStmt {
    IrStmt::VDecl { x, ty, expr }
}

#[test]
fn signed_word_closures_authenticate_every_reviewed_native_row() {
    let names = names();
    assert_eq!(names.len(), 115);
    for target in names {
        let row = crate::imported_ir::native_row(&name(&target)).unwrap();
        assert!(BoxedNative::from_row(row).unwrap().is_some(), "{target}");
        for changed in [
            GeneratedExternRow {
                name: "Foreign.value",
                ..*row
            },
            GeneratedExternRow {
                symbol: "foreign_value",
                ..*row
            },
            GeneratedExternRow {
                module: "Foreign",
                ..*row
            },
            GeneratedExternRow {
                kind: "axiom",
                ..*row
            },
            GeneratedExternRow {
                arity: row.arity + 1,
                ..*row
            },
            GeneratedExternRow { levels: 1, ..*row },
            GeneratedExternRow {
                ownership: "rule(borrowed-args,owned-result)",
                ..*row
            },
            GeneratedExternRow {
                effect: "io",
                ..*row
            },
            GeneratedExternRow {
                safety: "unsafe",
                ..*row
            },
            GeneratedExternRow {
                partition: "library-code",
                ..*row
            },
            GeneratedExternRow {
                entry_class: "unreviewed",
                ..*row
            },
            GeneratedExternRow {
                entry_scope: "unreviewed",
                ..*row
            },
            GeneratedExternRow {
                mode: "unreviewed",
                ..*row
            },
            GeneratedExternRow {
                profile: "standard",
                ..*row
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
    for family in FAMILIES {
        // Floating conversions have a separate native signature and module.
        let row = crate::imported_ir::native_row(&name(&format!("{family}.toFloat"))).unwrap();
        assert!(BoxedNative::from_row(row).unwrap().is_none());
    }
}

#[test]
fn signed_word_closures_execute_boundary_arithmetic_and_reuse_each_capture() {
    for family in FAMILIES {
        let (_, _, bits) = types(family);
        let mask = u64::MAX >> (64 - bits);
        let sign = 1u64 << (bits - 1);
        let minimum = -i128::from(sign);
        for (operation, inputs, expected) in [
            ("add", vec![mask, 2], 1),
            ("add", vec![sign - 1, 1], minimum),
            ("sub", vec![sign, 1], i128::from(sign - 1)),
            ("mul", vec![mask - 6, 3], -21),
            ("div", vec![mask - 6, 3], -2),
            ("div", vec![sign, mask], minimum),
            ("div", vec![mask - 6, 0], 0),
            ("mod", vec![mask - 6, 3], -1),
            ("mod", vec![sign, mask], 0),
            ("mod", vec![mask - 6, 0], -7),
            ("land", vec![mask, 42], 42),
            ("lor", vec![mask - 1, 1], -1),
            ("xor", vec![mask, 42], -43),
            ("shiftLeft", vec![1, mask], minimum),
            ("shiftRight", vec![mask - 3, 1], -2),
            ("shiftRight", vec![mask - 3, mask], -1),
            ("complement", vec![42], -43),
            ("neg", vec![42], -42),
            ("neg", vec![sign], minimum),
            ("abs", vec![mask - 41], 42),
            ("abs", vec![sign], minimum),
            ("decEq", vec![mask, mask], 1),
            ("decEq", vec![mask, 0], 0),
            ("decLe", vec![mask, 0], 1),
            ("decLe", vec![0, mask], 0),
            ("decLt", vec![mask, 0], 1),
            ("decLt", vec![mask, mask], 0),
            ("ofNat", vec![u64::MAX], -1),
            ("toInt", vec![sign], minimum),
            ("toInt", vec![sign - 1], i128::from(sign - 1)),
        ] {
            let compiled = compile_declarations(vec![program(family, operation, &inputs, false)])
                .unwrap_or_else(|error| panic!("{family}.{operation} {inputs:?}: {error}"));
            let decision = operation.starts_with("dec");
            let encoded = if decision {
                expected as u128
            } else {
                signed_encoding(expected)
            };
            // Both calls use the same closure and boxed arguments.
            assert_nat(&compiled, &(2 * encoded).to_string());
            assert!(
                compiled
                    .native_externs()
                    .contains(&format!("extern:{family}.{operation}"))
            );
        }
        // A scalar Nat may carry more than an Int scalar's 32-bit payload.
        // Decoding it as Int would truncate or sign-extend these operands.
        for input in [1u64 << 31, 1u64 << 32, 1u64 << 40, 1u64 << 62] {
            let expected = signed_value(u128::from(input & mask), bits);
            let compiled =
                compile_declarations(vec![program(family, "ofNat", &[input], false)])
                    .unwrap();
            assert_nat(&compiled, &(2 * signed_encoding(expected)).to_string());
        }
        // A negative heap Int must truncate its two's-complement value,
        // rather than interpreting the magnitude as an unsigned Nat.
        let compiled = compile_declarations(vec![program(
            family,
            "ofInt",
            &[u64::MAX],
            true,
        )])
        .unwrap();
        assert_nat(&compiled, "4");
        assert!(matches!(
            compiled
                .execute(
                    ExecutionLimits {
                        max_steps: 0,
                        ..ExecutionLimits::default()
                    },
                    None
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
        assert_nat(&compiled, "4");
    }
}

#[test]
fn signed_word_conversions_sign_extend_then_truncate_at_the_destination() {
    for source in FAMILIES {
        let (_, _, source_bits) = types(source);
        let mask = u64::MAX >> (64 - source_bits);
        let sign = 1u64 << (source_bits - 1);
        for target in FAMILIES.into_iter().filter(|target| *target != source) {
            let (_, _, target_bits) = types(target);
            for input in [0, 1, sign - 1, sign, mask, 257 & mask] {
                let signed = signed_value(u128::from(input), source_bits);
                let target_mask = (1u128 << target_bits) - 1;
                let expected = signed_value((signed as u128) & target_mask, target_bits);
                let compiled = compile_declarations(vec![program(
                    source,
                    &format!("to{target}"),
                    &[input],
                    false,
                )])
                .unwrap_or_else(|error| panic!("{source}.to{target}({input}): {error}"));
                assert_nat(&compiled, &(2 * signed_encoding(expected)).to_string());
            }
        }
    }
}

fn signed_value(bits: u128, width: u32) -> i128 {
    let modulus = 1i128 << width;
    let bits = bits as i128;
    if bits >= modulus / 2 {
        bits - modulus
    } else {
        bits
    }
}

fn signed_encoding(value: i128) -> u128 {
    value.unsigned_abs() * 2 + u128::from(value < 0)
}

/// Build a real PAP/AP pipeline, retaining two results and reusing its
/// captures. Encode signed results in Nat so every bit, including the sign
/// and Int64::MIN, remains visible to the common FLBC roundtrip assertion.
fn program(family: &str, operation: &str, inputs: &[u64], negative: bool) -> IrDecl {
    let (carrier, boxed, _) = types(family);
    let mut statements = Vec::new();
    let mut arguments = Vec::new();
    for (index, &input) in inputs.iter().enumerate() {
        let x = index as u64 * 4 + 1;
        statements.push(num(x, input));
        if operation == "ofNat" {
            arguments.push(var(x));
        } else if operation == "ofInt" {
            statements.push(call(x + 1, "Int.ofNat", &[x]));
            if negative {
                statements.push(call(x + 2, "Int.neg", &[x + 1]));
                arguments.push(var(x + 2));
            } else {
                arguments.push(var(x + 1));
            }
        } else {
            statements.push(typed(
                x + 1,
                carrier.clone(),
                IrExpr::Fap {
                    function: name(&format!("{family}.ofNat")),
                    args: vec![var(x)],
                },
            ));
            statements.push(typed(
                x + 2,
                boxed.clone(),
                IrExpr::Box {
                    ty: carrier.clone(),
                    x: x + 1,
                },
            ));
            arguments.push(var(x + 2));
        }
    }
    let last = arguments.pop().unwrap();
    statements.push(typed(
        20,
        IrType::Object,
        IrExpr::Pap {
            function: name(&format!("{family}.{operation}._boxed")),
            args: arguments,
        },
    ));
    let decision = operation.starts_with("dec");
    let target = operation
        .strip_prefix("to")
        .filter(|target| FAMILIES.contains(target))
        .unwrap_or(family);
    let (result_carrier, result_boxed, _) = types(target);
    let result_type = if decision {
        IrType::Tagged
    } else if operation == "toInt" {
        if matches!(carrier, IrType::UInt8 | IrType::UInt16) {
            IrType::Tagged
        } else {
            IrType::TObject
        }
    } else {
        result_boxed
    };
    for result in [21, 22] {
        statements.push(typed(
            result,
            result_type.clone(),
            IrExpr::Ap {
                x: 20,
                args: vec![last.clone()],
            },
        ));
    }
    for (result, x) in [(21, 30), (22, 50)] {
        if decision {
            statements.push(typed(x, IrType::UInt8, IrExpr::Unbox { x: result }));
            statements.push(call(x + 10, "UInt8.toNat", &[x]));
        } else {
            if operation == "toInt" {
                statements.push(call(x + 1, "Int.add", &[result, 100]));
            } else {
                statements.push(typed(
                    x,
                    result_carrier.clone(),
                    IrExpr::Unbox { x: result },
                ));
                statements.push(call(x + 1, &format!("{target}.toInt"), &[x]));
            }
            statements.push(call(x + 2, "Int.natAbs", &[x + 1]));
            statements.push(num(x + 3, 2));
            statements.push(call(x + 4, "Nat.mul", &[x + 2, x + 3]));
            statements.push(typed(
                x + 5,
                IrType::UInt8,
                IrExpr::Fap {
                    function: name("Int.decLt"),
                    args: vec![var(x + 1), var(100)],
                },
            ));
            statements.push(call(x + 6, "UInt8.toNat", &[x + 5]));
            statements.push(call(x + 10, "Nat.add", &[x + 4, x + 6]));
        }
    }
    // Insert the shared Int zero before either signed result is inspected.
    statements.insert(0, num(101, 0));
    statements.insert(1, call(100, "Int.ofNat", &[101]));
    statements.push(call(70, "Nat.add", &[40, 60]));
    entry(statements, 70)
}

#[test]
fn signed_word_wrappers_refuse_forged_prototypes_and_bad_runtime_values() {
    for family in FAMILIES {
        let (carrier, boxed, _) = types(family);
        let target = format!("{family}.add");
        let row = crate::imported_ir::native_row(&name(&target)).unwrap();
        let bridge = BoxedNative::from_row(row).unwrap().unwrap();
        let parameters: Vec<_> = (0..2)
            .map(|x| IrParam {
                x,
                borrow: false,
                ty: carrier.clone(),
            })
            .collect();
        validate_extern_signature(row, &parameters, &carrier).unwrap();
        for index in 0..parameters.len() {
            let mut wrong = parameters.clone();
            wrong[index].borrow = true;
            assert!(validate_extern_signature(row, &wrong, &carrier).is_err());
            wrong = parameters.clone();
            wrong[index].ty = IrType::TObject;
            assert!(validate_extern_signature(row, &wrong, &carrier).is_err());
        }
        let wrapper = IrDecl::Extern {
            name: name(&format!("{target}._boxed")),
            params: vec![
                IrParam {
                    x: 0,
                    borrow: false,
                    ty: boxed.clone(),
                },
                IrParam {
                    x: 1,
                    borrow: false,
                    ty: boxed.clone(),
                },
            ],
            result: boxed,
            entries: vec![],
        };
        bridge.validate_declaration(&wrapper).unwrap();
        let IrDecl::Extern {
            mut params, result, ..
        } = wrapper
        else {
            unreachable!()
        };
        params[0].ty = IrType::Erased;
        assert!(
            bridge
                .validate_declaration(&IrDecl::Extern {
                    name: name(&format!("{target}._boxed")),
                    params,
                    result,
                    entries: vec![],
                })
                .is_err()
        );
    }
    let compiled = compile_declarations(vec![entry(
        vec![
            bind(1, IrExpr::Lit(IrLit::Str("not an Int64".to_owned()))),
            typed(
                2,
                IrType::Object,
                IrExpr::Pap {
                    function: name("Int64.neg._boxed"),
                    args: vec![],
                },
            ),
            typed(
                3,
                IrType::Object,
                IrExpr::Ap {
                    x: 2,
                    args: vec![var(1)],
                },
            ),
            typed(4, IrType::UInt64, IrExpr::Unbox { x: 3 }),
            call(5, "UInt64.toNat", &[4]),
        ],
        5,
    )])
    .unwrap();
    assert!(matches!(
        compiled.execute(ExecutionLimits::default(), None).outcome,
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::TypeMismatch { .. },
            ..
        })
    ));
}
