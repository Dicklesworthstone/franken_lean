use super::*;
use crate::ir::{IrDecodeLimits, IrModule, decode_ir};
use crate::region::{OleanView, WalkBudget};

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn header() -> OleanWriteHeader<'static> {
    OleanWriteHeader {
        version: 2,
        flags: 1,
        lean_version: "4.32.0",
        githash: "0123456789abcdef0123456789abcdef01234567",
        base_addr: 0x20_000,
    }
}

fn input(module: &IrModule) -> IrWriteInput<'_> {
    IrWriteInput {
        module: ModuleWriteInput {
            is_module: false,
            imports: &[],
            constants: &[],
            extra_const_names: &[],
        },
        declarations: &module.decls,
        initializers: &module.initializers,
        additional_extensions: &[],
    }
}

fn decode(bytes: &[u8]) -> IrModule {
    let view = OleanView::parse(bytes).unwrap();
    let blocks = view
        .extension_payloads(WalkBudget::default(), 64 * 1024 * 1024)
        .unwrap();
    decode_ir(&blocks, IrDecodeLimits::default()).unwrap()
}

fn body(stmts: Vec<IrStmt>, terminal: IrTerminal) -> IrBody {
    IrBody {
        stmts,
        terminal: Box::new(terminal),
    }
}

fn function(stmts: Vec<IrStmt>, terminal: IrTerminal) -> IrDecl {
    IrDecl::Function {
        name: name("Sample.f"),
        params: vec![IrParam {
            x: 31,
            borrow: true,
            ty: IrType::TObject,
        }],
        result: IrType::Object,
        body: body(stmts, terminal),
        sorry_dep: Some(name("Sample.sorry")),
    }
}

#[test]
fn every_ir_form_and_scalar_field_survives_fresh_emission() {
    // Representation coverage, deliberately NOT an executable/ownership proof.
    let info = IrCtorInfo {
        name: name("Sample.ctor"),
        cidx: 2,
        size: 3,
        usize: 5,
        ssize: 7,
    };
    let args = vec![IrArg::Var(19), IrArg::Erased, IrArg::Var(23)];
    let expressions = vec![
        IrExpr::Ctor {
            info: info.clone(),
            args: args.clone(),
        },
        IrExpr::Reset { n: 7, x: 11 },
        IrExpr::Reuse {
            x: 13,
            info: info.clone(),
            update_header: true,
            args: args.clone(),
        },
        IrExpr::Reuse {
            x: 17,
            info: info.clone(),
            update_header: false,
            args: vec![],
        },
        IrExpr::Proj { i: 3, x: 17 },
        IrExpr::UProj { i: 5, x: 19 },
        IrExpr::SProj {
            n: 3,
            offset: 7,
            x: 23,
        },
        IrExpr::Fap {
            function: name("Sample.direct"),
            args: args.clone(),
        },
        IrExpr::Pap {
            function: name("Sample.partial"),
            args: args.clone(),
        },
        IrExpr::Ap {
            x: 29,
            args: args.clone(),
        },
        IrExpr::Box {
            ty: IrType::UInt64,
            x: 31,
        },
        IrExpr::Unbox { x: 37 },
        IrExpr::Lit(IrLit::Num(IrNat::Small(u64::MAX))),
        IrExpr::Lit(IrLit::Num(IrNat::Big(vec![13, 17, 19]))),
        IrExpr::Lit(IrLit::Str("λ\0🦀".into())),
        IrExpr::IsShared { x: 41 },
    ];
    let mut stmts: Vec<_> = expressions
        .into_iter()
        .enumerate()
        .map(|(i, expr)| IrStmt::VDecl {
            x: 100 + i as u64,
            ty: IrType::Object,
            expr,
        })
        .collect();
    stmts.extend([
        IrStmt::JDecl {
            j: 200,
            params: vec![IrParam {
                x: 43,
                borrow: false,
                ty: IrType::UInt32,
            }],
            value: body(vec![], IrTerminal::Jmp { j: 211, args }),
        },
        IrStmt::Set {
            x: 47,
            i: 3,
            y: IrArg::Erased,
        },
        IrStmt::SetTag { x: 53, cidx: 7 },
        IrStmt::USet { x: 59, i: 5, y: 61 },
        IrStmt::SSet {
            x: 67,
            i: 7,
            offset: 11,
            y: 71,
            ty: IrType::UInt16,
        },
        IrStmt::Del { x: 73 },
    ]);
    for checked in [false, true] {
        for persistent in [false, true] {
            stmts.push(IrStmt::Inc {
                x: 79,
                n: 3,
                checked,
                persistent,
            });
            stmts.push(IrStmt::Dec {
                x: 83,
                n: 5,
                checked,
                persistent,
            });
        }
    }
    let types = vec![
        IrType::Float,
        IrType::UInt8,
        IrType::UInt16,
        IrType::UInt32,
        IrType::UInt64,
        IrType::USize,
        IrType::Erased,
        IrType::Object,
        IrType::TObject,
        IrType::Float32,
        IrType::Tagged,
        IrType::Void,
        IrType::Struct {
            lean_type: None,
            types: vec![],
        },
        IrType::Struct {
            lean_type: Some(name("Sample.Struct")),
            types: vec![IrType::Float32, IrType::UInt64],
        },
        IrType::Union {
            lean_type: name("Sample.Union"),
            types: vec![IrType::Object, IrType::UInt8],
        },
    ];
    let external = IrDecl::Extern {
        name: name("Sample.extern"),
        params: types
            .into_iter()
            .enumerate()
            .map(|(i, ty)| IrParam {
                x: i as u64,
                borrow: i % 2 == 0,
                ty,
            })
            .collect(),
        result: IrType::Void,
        entries: vec![
            IrExternEntry::Adhoc { backend: name("c") },
            IrExternEntry::Inline {
                backend: name("llvm"),
                pattern: "call #1 #2".into(),
            },
            IrExternEntry::Standard {
                backend: name("c"),
                function: "sample_ffi".into(),
            },
            IrExternEntry::Opaque,
        ],
    };
    let mut module = IrModule {
        decls: vec![
            function(
                stmts,
                IrTerminal::Case {
                    type_name: name("Sample.Data"),
                    x: 89,
                    x_type: IrType::Tagged,
                    alts: vec![
                        IrAlt::Ctor {
                            info,
                            body: body(vec![], IrTerminal::Ret(IrArg::Var(97))),
                        },
                        IrAlt::Default {
                            body: body(vec![], IrTerminal::Unreachable),
                        },
                    ],
                },
            ),
            external,
        ],
        initializers: vec![
            crate::initializers::InitEntry {
                declaration: name("Sample.z"),
                initializer: None,
            },
            crate::initializers::InitEntry {
                declaration: name("Sample.a"),
                initializer: Some(name("Sample.initA")),
            },
        ],
        uninterpreted: vec![],
    };
    module.decls.sort_by(|a, b| a.name().quick_cmp(b.name()));
    let encoded = encode_ir(input(&module), header(), IrWriteLimits::default()).unwrap();
    assert_eq!(decode(&encoded.bytes), module);
    assert_eq!(encoded.report.file_bytes, encoded.bytes.len() as u64);
    assert_eq!(
        encode_ir(input(&module), header(), IrWriteLimits::default())
            .unwrap()
            .bytes,
        encoded.bytes
    );
    module.decls.reverse();
    assert_eq!(
        encode_ir(input(&module), header(), IrWriteLimits::default())
            .unwrap()
            .bytes,
        encoded.bytes
    );
}

#[test]
fn long_instruction_chains_use_no_recursive_encoder_walk() {
    let module = IrModule {
        decls: vec![function(
            (0..20_000)
                .map(|x| IrStmt::Inc {
                    x,
                    n: 1,
                    checked: true,
                    persistent: false,
                })
                .collect(),
            IrTerminal::Ret(IrArg::Erased),
        )],
        ..IrModule::default()
    };
    let encoded = encode_ir(input(&module), header(), IrWriteLimits::default()).unwrap();
    assert_eq!(decode(&encoded.bytes), module);
}

#[test]
fn budgets_cover_the_whole_input_and_do_not_return_a_prefix() {
    let module = IrModule {
        decls: vec![function(vec![], IrTerminal::Ret(IrArg::Erased))],
        ..IrModule::default()
    };
    let limits = IrWriteLimits {
        max_entries: 0,
        ..IrWriteLimits::default()
    };
    assert!(matches!(
        encode_ir(input(&module), header(), limits),
        Err(IrWriteError::Limit {
            resource: "entries"
        })
    ));
    let limits = IrWriteLimits {
        max_nodes: 1,
        ..IrWriteLimits::default()
    };
    assert!(matches!(
        encode_ir(input(&module), header(), limits),
        Err(IrWriteError::Limit { resource: "nodes" })
    ));
    let limits = IrWriteLimits {
        container: WriteBudget {
            max_objects: 0,
            ..WriteBudget::default()
        },
        ..IrWriteLimits::default()
    };
    assert!(matches!(
        encode_ir(input(&module), header(), limits),
        Err(IrWriteError::Write(WriteError::Budget { .. }))
    ));
    let encoded = encode_ir(input(&module), header(), IrWriteLimits::default()).unwrap();
    let limits = IrWriteLimits {
        container: WriteBudget {
            max_bytes: encoded.bytes.len() as u64 - 1,
            ..WriteBudget::default()
        },
        ..IrWriteLimits::default()
    };
    assert!(matches!(
        encode_ir(input(&module), header(), limits),
        Err(IrWriteError::Write(WriteError::Budget { .. }))
    ));
}

#[test]
fn ambiguous_or_noncanonical_input_is_refused() {
    let decl = function(vec![], IrTerminal::Ret(IrArg::Erased));
    let duplicate = IrModule {
        decls: vec![decl.clone(), decl],
        ..IrModule::default()
    };
    assert!(matches!(
        encode_ir(input(&duplicate), header(), IrWriteLimits::default()),
        Err(IrWriteError::Write(WriteError::Contract {
            what: "duplicate IR declaration"
        }))
    ));
    let entry = crate::initializers::InitEntry {
        declaration: name("Sample.value"),
        initializer: None,
    };
    let duplicate = IrModule {
        initializers: vec![entry.clone(), entry],
        ..IrModule::default()
    };
    assert!(encode_ir(input(&duplicate), header(), IrWriteLimits::default()).is_err());
    for limbs in [vec![], vec![1], vec![1, 0]] {
        let module = IrModule {
            decls: vec![function(
                vec![IrStmt::VDecl {
                    x: 0,
                    ty: IrType::Object,
                    expr: IrExpr::Lit(IrLit::Num(IrNat::Big(limbs))),
                }],
                IrTerminal::Ret(IrArg::Var(0)),
            )],
            ..IrModule::default()
        };
        assert!(matches!(
            encode_ir(input(&module), header(), IrWriteLimits::default()),
            Err(IrWriteError::Write(WriteError::Contract {
                what: "noncanonical IR big Nat"
            }))
        ));
    }
}

#[test]
fn logical_constants_and_ambiguous_initializer_names_are_refused() {
    use fln_core::{expr::Expr, level::Level};
    use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};

    let module = IrModule::default();
    let constants = [ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: name("NotIR"),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        },
        is_unsafe: false,
    })];
    let mut value = input(&module);
    value.module.constants = &constants;
    assert!(matches!(
        encode_ir(value, header(), IrWriteLimits::default()),
        Err(IrWriteError::Write(WriteError::Contract {
            what: "IR container cannot hold logical constants"
        }))
    ));
    for entry in [
        crate::initializers::InitEntry {
            declaration: Name::anonymous(),
            initializer: None,
        },
        crate::initializers::InitEntry {
            declaration: name("Sample.value"),
            initializer: Some(Name::anonymous()),
        },
    ] {
        let module = IrModule {
            initializers: vec![entry],
            ..IrModule::default()
        };
        assert!(matches!(
            encode_ir(input(&module), header(), IrWriteLimits::default()),
            Err(IrWriteError::Write(WriteError::Contract {
                what: "invalid or duplicate IR initializer"
            }))
        ));
    }
}

#[test]
fn additional_extension_graphs_are_preserved_and_reserved_names_cannot_be_replaced() {
    let module = IrModule::default();
    let key = name("Sample.extra");
    let objects = vec![Obj::mk_string("retained")];
    let extra = [ModuleExtensionInput {
        name: &key,
        entries: &objects,
    }];
    let mut value = input(&module);
    value.additional_extensions = &extra;
    let encoded = encode_ir(value, header(), IrWriteLimits::default()).unwrap();
    assert_eq!(decode(&encoded.bytes).uninterpreted, vec![key.clone()]);
    let view = OleanView::parse(&encoded.bytes).unwrap();
    let blocks = view
        .extension_payloads(WalkBudget::default(), 64 * 1024 * 1024)
        .unwrap();
    let preserved = blocks.iter().find(|block| block.name == key).unwrap();
    assert_eq!(
        preserved.entries,
        vec![fln_rt::region::compact(&objects[0], 0).unwrap()]
    );
    let reserved = name(format::DECL_MAP_EXTENSION);
    let extra = [ModuleExtensionInput {
        name: &reserved,
        entries: &objects,
    }];
    let mut value = input(&module);
    value.additional_extensions = &extra;
    assert!(matches!(
        encode_ir(value, header(), IrWriteLimits::default()),
        Err(IrWriteError::Write(WriteError::Contract {
            what: "duplicate persistent extension name"
        }))
    ));
}
