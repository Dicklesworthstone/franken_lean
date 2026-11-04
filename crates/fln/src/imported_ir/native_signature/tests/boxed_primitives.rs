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

fn row(target: &str) -> &'static GeneratedExternRow {
    crate::imported_ir::native_row(&name(target)).unwrap()
}

#[test]
fn reviewed_boxed_primitives_bind_the_generated_row_before_admitting_a_wrapper() {
    for target in NAMES {
        let original = row(target);
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
                ownership: "rule(borrowed-args,owned-result)",
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
    for target in ["Nat.divExact", "Nat.gcd", "String.extract", "UInt64.add"] {
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
