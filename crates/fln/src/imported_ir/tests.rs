#![forbid(unsafe_code)]

use super::*;
use fln_olean::ir::{IrArg, IrBody, IrExpr, IrLit, IrParam, IrTerminal};

mod mixed_cases;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn fixture() -> IrModule {
    crate::decode_ir_artifact(
        include_bytes!("../../../fln-olean/fixtures/ir/Init.Data.Nat.Basic.ir"),
        32 * 1024 * 1024,
    )
    .expect("the committed pinned IR fixture decodes")
}

fn bounded_partition(rows: &[(&str, &str)]) -> VerifiedPartition {
    let mut text = format!("constant_count\t{}\n", rows.len());
    for (n, class) in rows {
        let key = format!(
            "a{}",
            n.split('.')
                .map(|p| format!("/s\"{p}\""))
                .collect::<String>()
        );
        text.push_str(&format!(
            "partition\t{:?}\t{class}\ttest-bounded-policy\n",
            key
        ));
    }
    VerifiedPartition {
        partition: CensusPartition::parse(&text, GraphArchiveLimits::default()).unwrap(),
    }
}

fn nat(n: u64) -> EntryArgument {
    EntryArgument::Nat(IrNat::Small(n))
}

fn returned(program: &CompiledIr) -> String {
    let result = program.execute(ExecutionLimits::default(), None);
    assert_eq!(result.reference_functions, program.reference_functions());
    assert!(
        result
            .reference_functions
            .iter()
            .all(|f| f.producer() == "reference")
    );
    match result.outcome {
        Outcome::Complete(VmExit::Returned(value)) => {
            crate::nat_decimal(&value.value).expect("Nat result")
        }
        other => panic!("IR execution did not return: {other:?}"),
    }
}

#[test]
fn sha256_matches_published_vectors_and_block_boundaries() {
    for (input, expected) in [
        (
            "",
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        ),
        (
            "abc",
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
        ),
        (
            "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
        ),
    ] {
        assert_eq!(sha256::hex_digest(input.as_bytes()), expected);
    }
    assert_eq!(
        sha256::hex_digest(&vec![b'a'; 1_000_000]),
        "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
    );
}

#[test]
fn annotation_only_partitions_cannot_authorize_execution() {
    assert!(matches!(
        VerifiedPartition::from_pinned_tsv("constant_count\t0\n"),
        Err(IrExecutionError::PartitionDigest)
    ));
    assert!(matches!(
        VerifiedPartition::from_pinned_tsv(""),
        Err(IrExecutionError::PartitionDigest)
    ));
}

#[test]
fn real_decoded_nat_ir_runs_both_case_arms_and_native_calls() {
    let policy = bounded_partition(&[
        ("Nat.blt", "library-code"),
        ("Nat.min", "library-code"),
        ("Nat.max", "library-code"),
    ]);
    let modules = [fixture()];
    for (entry, args, expected) in [
        ("Nat.blt", [2, 3], "1"),
        ("Nat.blt", [3, 2], "0"),
        ("Nat.blt", [3, 3], "0"),
        ("Nat.min", [2, 9], "2"),
        ("Nat.min", [9, 2], "2"),
        ("Nat.max", [2, 9], "9"),
        ("Nat.max", [9, 2], "9"),
    ] {
        let compiled = compile(
            &modules,
            &name(entry),
            &args.map(nat),
            &policy,
            &BTreeSet::new(),
            IrExecutionLimits::default(),
        )
        .unwrap();
        assert_eq!(returned(&compiled), expected, "{entry} {args:?}");
        assert_eq!(compiled.reference_functions.len(), 1);
        assert_eq!(compiled.reference_functions[0].name, name(entry));
        assert!(!compiled.native_externs().is_empty());
    }
}

#[test]
fn real_ir_multiword_naturals_preserve_arithmetic_and_case_results() {
    let policy = bounded_partition(&[("Nat.blt", "library-code"), ("Nat.min", "library-code")]);
    let large = EntryArgument::Nat(IrNat::Big(vec![0, 1]));
    let args = [large.clone(), nat(0)];
    let p = compile(
        &[fixture()],
        &name("Nat.min"),
        &args,
        &policy,
        &BTreeSet::new(),
        IrExecutionLimits::default(),
    )
    .unwrap();
    assert_eq!(returned(&p), "0");
    let p = compile(
        &[fixture()],
        &name("Nat.blt"),
        &[nat(u64::MAX), large],
        &policy,
        &BTreeSet::new(),
        IrExecutionLimits::default(),
    )
    .unwrap();
    assert_eq!(returned(&p), "1");
}

fn function(text: &str, arity: u64, stmts: Vec<IrStmt>, result: IrArg) -> IrDecl {
    IrDecl::Function {
        name: name(text),
        params: (1..=arity)
            .map(|x| IrParam {
                x,
                borrow: true,
                ty: IrType::TObject,
            })
            .collect(),
        result: IrType::TObject,
        body: IrBody {
            stmts,
            terminal: Box::new(IrTerminal::Ret(result)),
        },
        sorry_dep: None,
    }
}

fn binding(x: u64, expr: IrExpr) -> IrStmt {
    IrStmt::VDecl {
        x,
        ty: IrType::TObject,
        expr,
    }
}

fn module(decls: Vec<IrDecl>) -> IrModule {
    IrModule {
        decls,
        ..IrModule::default()
    }
}

#[test]
fn user_calls_and_captured_closures_share_code_identity_across_modules() {
    let policy = bounded_partition(&[]);
    let first = module(vec![function(
        "User.add",
        2,
        vec![binding(
            3,
            IrExpr::Fap {
                function: name("Nat.add"),
                args: vec![IrArg::Var(1), IrArg::Var(2)],
            },
        )],
        IrArg::Var(3),
    )]);
    let second = module(vec![function(
        "User.main",
        0,
        vec![
            binding(1, IrExpr::Lit(IrLit::Num(IrNat::Small(7)))),
            binding(
                2,
                IrExpr::Pap {
                    function: name("User.add"),
                    args: vec![IrArg::Var(1)],
                },
            ),
            binding(3, IrExpr::Lit(IrLit::Num(IrNat::Small(35)))),
            binding(
                4,
                IrExpr::Ap {
                    x: 2,
                    args: vec![IrArg::Var(3)],
                },
            ),
        ],
        IrArg::Var(4),
    )]);
    let users = BTreeSet::from([name("User.add"), name("User.main")]);
    let compiled = compile(
        &[first, second],
        &name("User.main"),
        &[],
        &policy,
        &users,
        IrExecutionLimits::default(),
    )
    .unwrap();
    assert_eq!(returned(&compiled), "42");
    assert_eq!(compiled.reference_functions.len(), 2);
    assert_eq!(compiled.native_externs(), ["extern:Nat.add"]);
}

#[test]
fn toolchain_api_unknown_names_and_wrappers_cannot_be_reclassified() {
    let policy = bounded_partition(&[
        ("Lean.Elab.Term.elabTerm", "toolchain-api"),
        ("Nat.blt", "library-code"),
    ]);
    for entry in ["Lean.Elab.Term.elabTerm", "Lean.Elab.Term.elabTerm._boxed"] {
        let modules = [module(vec![function(entry, 0, vec![], IrArg::Erased)])];
        assert!(matches!(
            compile(
                &modules,
                &name(entry),
                &[],
                &policy,
                &BTreeSet::new(),
                IrExecutionLimits::default(),
            ),
            Err(IrExecutionError::ToolchainApi(_))
        ));
        assert!(matches!(
            compile(
                &modules,
                &name(entry),
                &[],
                &policy,
                &BTreeSet::from([name(entry)]),
                IrExecutionLimits::default(),
            ),
            Err(IrExecutionError::UserOverridesCensus(_))
        ));
    }
    assert!(matches!(
        compile(
            &[fixture()],
            &name("Nat.blt._boxed"),
            &[nat(2), nat(3)],
            &policy,
            &BTreeSet::new(),
            IrExecutionLimits::default(),
        ),
        Err(IrExecutionError::Unclassified(_))
    ));
    assert!(matches!(
        compile(
            &[fixture()],
            &name("Nat.blt._boxed"),
            &[nat(2), nat(3)],
            &policy,
            &BTreeSet::from([name("Nat.blt._boxed")]),
            IrExecutionLimits::default(),
        ),
        Err(IrExecutionError::UserOverridesCensus(_))
    ));
    assert!(matches!(
        compile(
            &[module(vec![function(
                "Unknown.entry",
                0,
                vec![],
                IrArg::Erased
            )])],
            &name("Unknown.entry"),
            &[],
            &policy,
            &BTreeSet::new(),
            IrExecutionLimits::default(),
        ),
        Err(IrExecutionError::Unclassified(_))
    ));
}

#[test]
fn native_rows_override_forged_input_bodies() {
    let forged = function(
        "Nat.add",
        2,
        vec![binding(3, IrExpr::Lit(IrLit::Num(IrNat::Small(999))))],
        IrArg::Var(3),
    );
    let compiled = compile(
        &[module(vec![forged])],
        &name("Nat.add"),
        &[nat(20), nat(22)],
        &bounded_partition(&[]),
        &BTreeSet::new(),
        IrExecutionLimits::default(),
    )
    .unwrap();
    assert_eq!(returned(&compiled), "42");
    assert!(compiled.reference_functions().is_empty());
    assert_eq!(compiled.native_externs(), ["extern:Nat.add"]);
}

#[test]
fn execution_exhaustion_has_no_value_and_preserves_reference_provenance() {
    let compiled = compile(
        &[fixture()],
        &name("Nat.min"),
        &[nat(42), nat(9)],
        &bounded_partition(&[("Nat.min", "library-code")]),
        &BTreeSet::new(),
        IrExecutionLimits::default(),
    )
    .unwrap();
    let stopped = compiled.execute(
        ExecutionLimits {
            max_steps: 1,
            ..ExecutionLimits::default()
        },
        None,
    );
    assert!(matches!(stopped.outcome, Outcome::Inconclusive(_)));
    assert_eq!(stopped.reference_functions, compiled.reference_functions());
    assert_eq!(stopped.reference_functions[0].producer(), "reference");
    assert_eq!(returned(&compiled), "9");
}

#[test]
fn pinned_partition_authenticates_real_ir_and_rejects_modified_bytes() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../contracts/builtin_partition.tsv");
    let text = match std::fs::read_to_string(&path) {
        Ok(text) => text,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            eprintln!(
                "pinned census not materialized at {}; skipping full-policy check",
                path.display()
            );
            return;
        }
        Err(error) => panic!("read pinned census: {error}"),
    };
    let policy = VerifiedPartition::from_pinned_tsv(&text).unwrap();
    assert_eq!(
        policy.classify(&name("Nat.min")),
        Some(GraphClass::LibraryCode)
    );
    let compiled = compile(
        &[fixture()],
        &name("Nat.min"),
        &[nat(42), nat(9)],
        &policy,
        &BTreeSet::new(),
        IrExecutionLimits::default(),
    )
    .unwrap();
    assert_eq!(returned(&compiled), "9");
    let mut modified = text;
    modified.push('\n');
    assert!(matches!(
        VerifiedPartition::from_pinned_tsv(&modified),
        Err(IrExecutionError::PartitionDigest)
    ));
}

#[test]
fn object_constructors_cases_and_projection_execute_both_alternatives() {
    use fln_olean::ir::{IrAlt, IrCtorInfo};

    let none = IrCtorInfo {
        name: name("Option.none"),
        cidx: 0,
        size: 0,
        usize: 0,
        ssize: 0,
    };
    let some = IrCtorInfo {
        name: name("Option.some"),
        cidx: 1,
        size: 1,
        usize: 0,
        ssize: 0,
    };
    let mut unwrap = function("User.unwrap", 1, vec![], IrArg::Erased);
    let IrDecl::Function { body, .. } = &mut unwrap else {
        unreachable!()
    };
    *body = IrBody {
        stmts: vec![],
        terminal: Box::new(IrTerminal::Case {
            type_name: name("Option"),
            x: 1,
            x_type: IrType::TObject,
            alts: vec![
                IrAlt::Ctor {
                    info: none.clone(),
                    body: IrBody {
                        stmts: vec![binding(2, IrExpr::Lit(IrLit::Num(IrNat::Small(0))))],
                        terminal: Box::new(IrTerminal::Ret(IrArg::Var(2))),
                    },
                },
                IrAlt::Ctor {
                    info: some.clone(),
                    body: IrBody {
                        stmts: vec![binding(3, IrExpr::Proj { i: 0, x: 1 })],
                        terminal: Box::new(IrTerminal::Ret(IrArg::Var(3))),
                    },
                },
            ],
        }),
    };
    let some_entry = function(
        "User.some",
        0,
        vec![
            binding(1, IrExpr::Lit(IrLit::Num(IrNat::Small(42)))),
            binding(
                2,
                IrExpr::Ctor {
                    info: some,
                    args: vec![IrArg::Var(1)],
                },
            ),
            binding(
                3,
                IrExpr::Fap {
                    function: name("User.unwrap"),
                    args: vec![IrArg::Var(2)],
                },
            ),
        ],
        IrArg::Var(3),
    );
    let none_entry = function(
        "User.none",
        0,
        vec![
            binding(
                1,
                IrExpr::Ctor {
                    info: none,
                    args: vec![],
                },
            ),
            binding(
                2,
                IrExpr::Fap {
                    function: name("User.unwrap"),
                    args: vec![IrArg::Var(1)],
                },
            ),
        ],
        IrArg::Var(2),
    );
    let modules = [module(vec![unwrap, some_entry, none_entry])];
    let users = BTreeSet::from([name("User.unwrap"), name("User.some"), name("User.none")]);
    for (entry, expected) in [("User.some", "42"), ("User.none", "0")] {
        let compiled = compile(
            &modules,
            &name(entry),
            &[],
            &bounded_partition(&[]),
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap();
        assert_eq!(returned(&compiled), expected);
        assert_eq!(compiled.reference_functions().len(), 2);
    }
}

#[test]
fn borrowed_identity_returns_a_live_owned_string() {
    let compiled = compile(
        &[module(vec![function(
            "User.identity",
            1,
            vec![],
            IrArg::Var(1),
        )])],
        &name("User.identity"),
        &[EntryArgument::String("retained λ 🦀".to_owned())],
        &bounded_partition(&[]),
        &BTreeSet::from([name("User.identity")]),
        IrExecutionLimits::default(),
    )
    .unwrap();
    let result = compiled.execute(ExecutionLimits::default(), None);
    let Outcome::Complete(exit @ VmExit::Returned(_)) = result.outcome else {
        panic!("identity did not return: {:?}", result.outcome);
    };
    assert_eq!(
        crate::closed_vm_value(&exit).unwrap(),
        Some(crate::ClosedVmValue::String("retained λ 🦀".to_owned()))
    );
}

fn body_function(text: &str, arity: u64, body: IrBody) -> IrDecl {
    let mut declaration = function(text, arity, vec![], IrArg::Erased);
    let IrDecl::Function { body: target, .. } = &mut declaration else {
        unreachable!()
    };
    *target = body;
    declaration
}

fn ir_body(stmts: Vec<IrStmt>, terminal: IrTerminal) -> IrBody {
    IrBody {
        stmts,
        terminal: Box::new(terminal),
    }
}

fn join(j: u64, params: &[u64], value: IrBody) -> IrStmt {
    IrStmt::JDecl {
        j,
        params: params
            .iter()
            .map(|x| IrParam {
                x: *x,
                borrow: true,
                ty: IrType::TObject,
            })
            .collect(),
        value,
    }
}

fn jump(j: u64, args: &[u64]) -> IrTerminal {
    IrTerminal::Jmp {
        j,
        args: args.iter().copied().map(IrArg::Var).collect(),
    }
}

fn number(x: u64, n: u64) -> IrStmt {
    binding(x, IrExpr::Lit(IrLit::Num(IrNat::Small(n))))
}

fn call(x: u64, target: &str, args: &[u64]) -> IrStmt {
    binding(
        x,
        IrExpr::Fap {
            function: name(target),
            args: args.iter().copied().map(IrArg::Var).collect(),
        },
    )
}

fn compile_users(
    declarations: Vec<IrDecl>,
    entry: &str,
    args: &[EntryArgument],
    limits: IrExecutionLimits,
) -> Result<CompiledIr, IrExecutionError> {
    let users = declarations
        .iter()
        .map(|decl| decl.name().clone())
        .collect();
    compile(
        &[module(declarations)],
        &name(entry),
        args,
        &bounded_partition(&[]),
        &users,
        limits,
    )
}

#[test]
fn joins_merge_branch_arguments_with_lexical_captures_deterministically() {
    use fln_olean::ir::{IrAlt, IrCtorInfo};

    let mut declaration = body_function(
        "User.choose",
        2,
        ir_body(
            vec![
                number(3, 3),
                join(
                    4,
                    &[5],
                    ir_body(
                        vec![call(6, "Nat.mul", &[5, 3])],
                        IrTerminal::Ret(IrArg::Var(6)),
                    ),
                ),
            ],
            IrTerminal::Case {
                type_name: name("Bool"),
                x: 1,
                x_type: IrType::UInt8,
                alts: [(0, 7, 5), (1, 9, 2)]
                    .into_iter()
                    .map(|(tag, x, delta)| IrAlt::Ctor {
                        info: IrCtorInfo {
                            name: name(if tag == 0 { "Bool.false" } else { "Bool.true" }),
                            cidx: tag,
                            size: 0,
                            usize: 0,
                            ssize: 0,
                        },
                        body: ir_body(
                            vec![number(x, delta), call(x + 1, "Nat.add", &[2, x])],
                            jump(4, &[x + 1]),
                        ),
                    })
                    .collect(),
            },
        ),
    );
    let IrDecl::Function { params, .. } = &mut declaration else {
        unreachable!()
    };
    params[0].ty = IrType::UInt8;
    for (tag, expected) in [(0, "45"), (1, "36")] {
        let compile_once = || {
            compile_users(
                vec![declaration.clone()],
                "User.choose",
                &[nat(tag), nat(10)],
                IrExecutionLimits::default(),
            )
            .unwrap()
        };
        let compiled = compile_once();
        assert_eq!(returned(&compiled), expected);
        assert_eq!(compiled.reference_functions().len(), 2);
        assert!(
            compiled
                .reference_functions()
                .iter()
                .all(|f| f.name == name("User.choose"))
        );
        assert_eq!(
            flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default())
                .unwrap(),
            flbc::encode_canonical(
                compile_once().program.program(),
                flbc::CodecLimits::default()
            )
            .unwrap(),
        );
    }
}

#[test]
fn nested_joins_reach_prior_joins_with_their_original_capture_scope() {
    let declaration = body_function(
        "User.nested",
        1,
        ir_body(
            vec![
                join(
                    2,
                    &[3],
                    ir_body(
                        vec![call(4, "Nat.add", &[3, 1])],
                        IrTerminal::Ret(IrArg::Var(4)),
                    ),
                ),
                join(
                    6,
                    &[7],
                    ir_body(
                        vec![
                            number(8, 2),
                            join(
                                9,
                                &[10],
                                ir_body(vec![call(11, "Nat.mul", &[10, 8])], jump(2, &[11])),
                            ),
                        ],
                        jump(9, &[7]),
                    ),
                ),
            ],
            jump(6, &[1]),
        ),
    );
    for (n, expected) in [(7, "21"), (11, "33")] {
        let compiled = compile_users(
            vec![declaration.clone()],
            "User.nested",
            &[nat(n)],
            IrExecutionLimits::default(),
        )
        .unwrap();
        assert_eq!(returned(&compiled), expected);
        assert_eq!(compiled.reference_functions().len(), 4);
    }
}

#[test]
fn join_capture_preserves_heap_fields_after_the_parent_frame_is_released() {
    let declaration = body_function(
        "User.capture",
        1,
        ir_body(
            vec![
                binding(
                    2,
                    IrExpr::Ctor {
                        info: fln_olean::ir::IrCtorInfo {
                            name: name("Option.some"),
                            cidx: 1,
                            size: 1,
                            usize: 0,
                            ssize: 0,
                        },
                        args: vec![IrArg::Var(1)],
                    },
                ),
                join(
                    3,
                    &[],
                    ir_body(
                        vec![binding(4, IrExpr::Proj { i: 0, x: 2 })],
                        IrTerminal::Ret(IrArg::Var(4)),
                    ),
                ),
            ],
            jump(3, &[]),
        ),
    );
    let compiled = compile_users(
        vec![declaration],
        "User.capture",
        &[EntryArgument::String("retained λ 🦀".to_owned())],
        IrExecutionLimits::default(),
    )
    .unwrap();
    let result = compiled.execute(ExecutionLimits::default(), None);
    let Outcome::Complete(exit @ VmExit::Returned(_)) = result.outcome else {
        panic!("captured object did not return: {:?}", result.outcome);
    };
    assert_eq!(
        crate::closed_vm_value(&exit).unwrap(),
        Some(crate::ClosedVmValue::String("retained λ 🦀".to_owned()))
    );
}

#[test]
fn malformed_join_scopes_and_arities_are_rejected_before_execution() {
    let bodies = [
        // A join cannot see itself in its body.
        ir_body(
            vec![join(2, &[], ir_body(vec![], jump(2, &[])))],
            jump(2, &[]),
        ),
        // Nor can it see a declaration that follows it.
        ir_body(
            vec![
                join(2, &[], ir_body(vec![], jump(3, &[]))),
                join(3, &[], ir_body(vec![], IrTerminal::Ret(IrArg::Var(1)))),
            ],
            jump(2, &[]),
        ),
        // Join parameters do not escape into the enclosing continuation.
        ir_body(
            vec![join(
                2,
                &[3],
                ir_body(vec![], IrTerminal::Ret(IrArg::Var(3))),
            )],
            IrTerminal::Ret(IrArg::Var(3)),
        ),
        ir_body(
            vec![join(
                2,
                &[3],
                ir_body(vec![], IrTerminal::Ret(IrArg::Var(3))),
            )],
            jump(2, &[]),
        ),
    ];
    for body in bodies {
        let error = compile_users(
            vec![body_function("User.invalid", 1, body)],
            "User.invalid",
            &[nat(42)],
            IrExecutionLimits::default(),
        )
        .unwrap_err();
        assert!(
            matches!(error, IrExecutionError::IrValidation(_)),
            "{error:?}"
        );
        assert!(!error.is_resource());
    }
}

#[test]
fn lifted_join_functions_and_capture_expansion_obey_resource_limits() {
    let mut statements: Vec<_> = (2..=6).map(|x| number(x, x)).collect();
    statements.push(join(
        7,
        &[],
        ir_body(vec![], IrTerminal::Ret(IrArg::Var(1))),
    ));
    let declaration = body_function("User.bounded", 1, ir_body(statements, jump(7, &[])));
    let mut limits = IrExecutionLimits::default();
    limits.fir.max_functions = 2;
    let error = compile_users(
        vec![declaration.clone()],
        "User.bounded",
        &[nat(42)],
        limits,
    )
    .unwrap_err();
    assert!(matches!(
        error,
        IrExecutionError::Limit("lowered functions")
    ));
    assert!(error.is_resource());

    let mut limits = IrExecutionLimits::default();
    limits.fir.max_operands = 5;
    let error = compile_users(
        vec![declaration.clone()],
        "User.bounded",
        &[nat(42)],
        limits,
    )
    .unwrap_err();
    assert!(matches!(
        error,
        IrExecutionError::Limit("join capture operands")
    ));
    assert!(error.is_resource());

    let compiled = compile_users(
        vec![declaration],
        "User.bounded",
        &[nat(42)],
        IrExecutionLimits::default(),
    )
    .unwrap();
    assert_eq!(returned(&compiled), "42");
}

#[test]
fn a_long_join_chain_runs_with_one_vm_frame() {
    let statements = (0..64)
        .map(|i| {
            join(
                100 + i,
                &[200 + i],
                ir_body(
                    vec![],
                    if i == 0 {
                        IrTerminal::Ret(IrArg::Var(200))
                    } else {
                        jump(99 + i, &[200 + i])
                    },
                ),
            )
        })
        .collect();
    let compiled = compile_users(
        vec![body_function(
            "User.chain",
            1,
            ir_body(statements, jump(163, &[1])),
        )],
        "User.chain",
        &[nat(42)],
        IrExecutionLimits::default(),
    )
    .unwrap();
    assert_eq!(compiled.reference_functions().len(), 65);
    let result = compiled.execute(
        ExecutionLimits {
            max_stack_depth: 1,
            ..ExecutionLimits::default()
        },
        None,
    );
    match result.outcome {
        Outcome::Complete(VmExit::Returned(value)) => {
            assert_eq!(crate::nat_decimal(&value.value).unwrap(), "42");
        }
        other => panic!("join chain grew the stack or failed: {other:?}"),
    }
    assert_eq!(result.reference_functions, compiled.reference_functions());
}

#[test]
fn object_fields_project_across_function_and_module_boundaries() {
    let second = function(
        "User.second",
        1,
        vec![binding(2, IrExpr::Proj { i: 1, x: 1 })],
        IrArg::Var(2),
    );
    let entry = function(
        "User.pair",
        0,
        vec![
            number(1, 19),
            binding(2, IrExpr::Lit(IrLit::Str("retained λ 🦀".to_owned()))),
            binding(
                3,
                IrExpr::Ctor {
                    info: fln_olean::ir::IrCtorInfo {
                        name: name("Prod.mk"),
                        cidx: 0,
                        size: 2,
                        usize: 0,
                        ssize: 0,
                    },
                    args: vec![IrArg::Var(1), IrArg::Var(2)],
                },
            ),
            call(4, "User.second", &[3]),
        ],
        IrArg::Var(4),
    );
    let compiled = compile(
        &[module(vec![second]), module(vec![entry])],
        &name("User.pair"),
        &[],
        &bounded_partition(&[]),
        &BTreeSet::from([name("User.second"), name("User.pair")]),
        IrExecutionLimits::default(),
    )
    .unwrap();
    let result = compiled.execute(ExecutionLimits::default(), None);
    let Outcome::Complete(exit @ VmExit::Returned(_)) = result.outcome else {
        panic!("separate projection did not return: {:?}", result.outcome);
    };
    assert_eq!(
        crate::closed_vm_value(&exit).unwrap(),
        Some(crate::ClosedVmValue::String("retained λ 🦀".to_owned()))
    );
}

#[test]
fn generic_projection_refuses_nonconstructors_without_fabricating_a_value() {
    use fln_vm::interpreter::VmRefusal;

    for argument in [nat(42), EntryArgument::String("not a record".to_owned())] {
        let compiled = compile_users(
            vec![function(
                "User.project",
                1,
                vec![binding(2, IrExpr::Proj { i: 0, x: 1 })],
                IrArg::Var(2),
            )],
            "User.project",
            &[argument],
            IrExecutionLimits::default(),
        )
        .unwrap();
        assert!(matches!(
            compiled.execute(ExecutionLimits::default(), None).outcome,
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::TypeMismatch { .. },
                ..
            })
        ));
    }
}

#[test]
fn pinned_compiler_join_and_projection_ir_matches_reference_results() {
    // Generated from JoinModule.lean by the v4.32.0 Reference at
    // 8c9756b28d64dab099da31a4c09229a9e6a2ef35. These expectations were also
    // evaluated by that compiler; the fixture is decoded binary IR, not a
    // hand-authored translation of its printed trace.
    let module = crate::decode_ir_artifact(
        include_bytes!("../../../fln-olean/fixtures/ir/JoinModule.ir"),
        32 * 1024 * 1024,
    )
    .expect("pinned compiler join fixture decodes");
    let users = module
        .decls
        .iter()
        .map(|decl| decl.name().clone())
        .collect();
    let modules = [module];
    let policy = bounded_partition(&[]);
    for (entry, args, expected) in [
        ("joinChoice", vec![nat(0), nat(10)], "45"),
        ("joinChoice", vec![nat(1), nat(10)], "36"),
        ("joinChoice._boxed", vec![nat(0), nat(10)], "45"),
        ("joinChoice._boxed", vec![nat(1), nat(10)], "36"),
        ("joinNested", vec![nat(0), nat(0), nat(10)], "125"),
        ("joinNested", vec![nat(0), nat(1), nat(10)], "79"),
        ("joinNested", vec![nat(1), nat(0), nat(10)], "95"),
        ("joinNested", vec![nat(1), nat(1), nat(10)], "61"),
    ] {
        let compiled = compile(
            &modules,
            &name(entry),
            &args,
            &policy,
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap();
        assert_eq!(returned(&compiled), expected, "{entry} {args:?}");
        assert!(compiled.reference_functions().len() >= 2);
    }
    let compiled = compile(
        &modules,
        &name("fieldAnswer"),
        &[],
        &policy,
        &users,
        IrExecutionLimits::default(),
    )
    .unwrap();
    let result = compiled.execute(ExecutionLimits::default(), None);
    let Outcome::Complete(exit @ VmExit::Returned(_)) = result.outcome else {
        panic!(
            "pinned object projection did not return: {:?}",
            result.outcome
        );
    };
    assert_eq!(
        crate::closed_vm_value(&exit).unwrap(),
        Some(crate::ClosedVmValue::String("retained λ 🦀".to_owned()))
    );
}

#[test]
fn pinned_compiler_packed_records_match_reference_results_and_replay() {
    // Generated from PackedModule.lean by the v4.32.0 Reference at
    // 8c9756b28d64dab099da31a4c09229a9e6a2ef35. The same Reference evaluated
    // these three results. Decode its binary IR so source-order setters,
    // physical integer offsets, and the compiler's boxed closure are covered.
    let module = crate::decode_ir_artifact(
        include_bytes!("../../../fln-olean/fixtures/ir/PackedModule.ir"),
        32 * 1024 * 1024,
    )
    .expect("pinned compiler packed-record fixture decodes");
    let users = module
        .decls
        .iter()
        .map(|decl| decl.name().clone())
        .collect();
    let modules = [module];
    let policy = bounded_partition(&[]);
    for (entry, args, expected) in [
        ("packedAnswer", vec![], "18446744077445529267"),
        ("packedClosureAnswer", vec![], "18446744077445529272"),
        // This input wraps the UInt8 field while preserving all wider fields.
        ("packedResult", vec![nat(85)], "18446744077445529436"),
    ] {
        let compiled = compile(
            &modules,
            &name(entry),
            &args,
            &policy,
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("pinned packed entry {entry} {args:?}: {error:?}"));
        assert_native_owned_result(&compiled, expected);
        assert!(
            compiled
                .program
                .program()
                .functions()
                .iter()
                .flat_map(|function| &function.code)
                .any(|instruction| matches!(instruction, flbc::Instruction::CtorPacked { .. }))
        );
        assert!(
            compiled
                .program
                .program()
                .functions()
                .iter()
                .flat_map(|function| &function.code)
                .any(|instruction| matches!(instruction, flbc::Instruction::CtorScalar { .. }))
        );
    }
}

fn native_list_sum() -> IrDecl {
    use fln_olean::ir::{IrAlt, IrCtorInfo};

    let nil = IrCtorInfo {
        name: name("List.nil"),
        cidx: 0,
        size: 0,
        usize: 0,
        ssize: 0,
    };
    let cons = IrCtorInfo {
        name: name("List.cons"),
        cidx: 1,
        size: 2,
        usize: 0,
        ssize: 0,
    };
    body_function(
        "NativeLists.sum",
        1,
        ir_body(
            vec![],
            IrTerminal::Case {
                type_name: name("List"),
                x: 1,
                x_type: IrType::TObject,
                alts: vec![
                    IrAlt::Ctor {
                        info: nil,
                        body: ir_body(vec![number(2, 0)], IrTerminal::Ret(IrArg::Var(2))),
                    },
                    IrAlt::Ctor {
                        info: cons,
                        body: ir_body(
                            vec![
                                binding(3, IrExpr::Proj { i: 0, x: 1 }),
                                binding(4, IrExpr::Proj { i: 1, x: 1 }),
                                call(5, "NativeLists.sum", &[4]),
                                call(6, "Nat.add", &[3, 5]),
                            ],
                            IrTerminal::Ret(IrArg::Var(6)),
                        ),
                    },
                ],
            },
        ),
    )
}

fn native_array_extern(text: &str, arity: u64) -> IrDecl {
    IrDecl::Extern {
        name: name(text),
        params: (1..=arity)
            .map(|x| IrParam {
                x,
                borrow: text == "Array.emptyWithCapacity",
                ty: IrType::TObject,
            })
            .collect(),
        result: IrType::TObject,
        entries: Vec::new(),
    }
}

#[test]
fn native_arrays_feed_imported_list_recursion_and_preserve_shared_inputs() {
    let entry = body_function(
        "NativeLists.roundTrip",
        0,
        ir_body(
            vec![
                number(1, 0),
                call(2, "Array.emptyWithCapacity", &[1]),
                number(3, 19),
                call(4, "Array.push", &[2, 3]),
                number(5, 23),
                call(6, "Array.push", &[4, 5]),
                call(7, "Array.toList", &[6]),
                call(8, "NativeLists.sum", &[7]),
                call(9, "NativeLists.sum", &[7]),
                call(10, "Nat.add", &[8, 9]),
                call(11, "Array.toList", &[2]),
                call(12, "NativeLists.sum", &[11]),
                call(13, "Array.toList", &[4]),
                call(14, "NativeLists.sum", &[13]),
                call(15, "Nat.add", &[10, 12]),
                call(16, "Nat.add", &[15, 14]),
            ],
            IrTerminal::Ret(IrArg::Var(16)),
        ),
    );
    // These are erased executable arities, checked against the generated ABI
    // contracts; the source telescope also contains a static element type.
    let modules = [module(vec![
        native_list_sum(),
        entry,
        native_array_extern("Array.emptyWithCapacity", 1),
        native_array_extern("Array.push", 2),
        native_array_extern("Array.toList", 1),
    ])];
    let compiled = compile(
        &modules,
        &name("NativeLists.roundTrip"),
        &[],
        &bounded_partition(&[]),
        &BTreeSet::from([name("NativeLists.sum"), name("NativeLists.roundTrip")]),
        IrExecutionLimits::default(),
    )
    .unwrap();
    // Two reads of [19, 23], then the original empty and one-element arrays.
    assert_eq!(returned(&compiled), "103");
    assert!(
        compiled
            .native_externs()
            .iter()
            .any(|row| row == "extern:Array.toList")
    );
    let bytes = flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default())
        .expect("encode the native Array/List bridge");
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default())
        .expect("decode the native Array/List bridge");
    let outcome = fln_vm::interpreter::execute(&replay, ExecutionLimits::default(), None);
    let Outcome::Complete(VmExit::Returned(value)) = outcome else {
        panic!("Array/List replay did not return: {outcome:?}");
    };
    assert_eq!(
        crate::nat_decimal(&value.value).expect("Nat replay result"),
        "103"
    );
}

fn assert_native_owned_result(compiled: &CompiledIr, expected: &str) {
    assert_eq!(returned(compiled), expected);
    let bytes = flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default())
        .expect("encode native owned operands");
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default())
        .expect("decode native owned operands");
    let outcome = fln_vm::interpreter::execute(&replay, ExecutionLimits::default(), None);
    let Outcome::Complete(VmExit::Returned(value)) = outcome else {
        panic!("native owned operands replay did not return: {outcome:?}");
    };
    assert_eq!(
        crate::nat_decimal(&value.value).expect("Nat replay result"),
        expected
    );
}

#[test]
fn native_owned_operands_preserve_shared_strings_and_closure_captures() {
    for through_closure in [false, true] {
        let mut stmts = if through_closure {
            vec![
                binding(
                    2,
                    IrExpr::Pap {
                        function: name("String.append"),
                        args: vec![IrArg::Var(1)],
                    },
                ),
                binding(
                    3,
                    IrExpr::Ap {
                        x: 2,
                        args: vec![IrArg::Var(1)],
                    },
                ),
            ]
        } else {
            vec![call(3, "String.append", &[1, 1])]
        };
        // The same borrowed parameter supplies both the owned and borrowed
        // native operands, then remains readable after the call returns.
        stmts.extend([
            call(4, "String.length", &[1]),
            call(5, "String.length", &[3]),
            call(6, "Nat.add", &[4, 5]),
        ]);
        let compiled = compile_users(
            vec![function("User.sharedString", 1, stmts, IrArg::Var(6))],
            "User.sharedString",
            &[EntryArgument::String("λ🦀".to_owned())],
            IrExecutionLimits::default(),
        )
        .unwrap();
        assert_native_owned_result(&compiled, "6");
    }
}

#[test]
fn repeated_owned_native_operands_keep_distinct_references_and_move_last_uses() {
    let entry = function(
        "NativeLists.nested",
        0,
        vec![
            number(1, 0),
            call(2, "Array.emptyWithCapacity", &[1]),
            // The empty array is both the updated container and its element.
            // These two owned operands need distinct references to preserve
            // the inner empty array when the outer one acquires an element.
            call(3, "Array.push", &[2, 2]),
            call(4, "Array.getInternal", &[3, 1]),
            call(5, "Array.size", &[3]),
            call(6, "Array.size", &[4]),
            call(7, "Nat.add", &[5, 6]),
        ],
        IrArg::Var(7),
    );
    let modules = [module(vec![
        entry,
        native_array_extern("Array.emptyWithCapacity", 1),
        native_array_extern("Array.push", 2),
        native_array_extern("Array.getInternal", 2),
        native_array_extern("Array.size", 1),
    ])];
    let users = BTreeSet::from([name("NativeLists.nested")]);
    let compile_nested = |limits| {
        compile(
            &modules,
            &name("NativeLists.nested"),
            &[],
            &bounded_partition(&[]),
            &users,
            limits,
        )
    };
    let compiled = compile_nested(IrExecutionLimits::default()).unwrap();
    assert_native_owned_result(&compiled, "1");
    let function = compiled
        .reference_functions()
        .iter()
        .find(|function| function.name == name("NativeLists.nested"))
        .unwrap()
        .function;
    let code = &compiled.program.program().functions()[function.get() as usize].code;
    let args = code
        .iter()
        .find_map(|instruction| match instruction {
            flbc::Instruction::Intrinsic { row, args, .. } if row == "extern:Array.push" => {
                Some(args)
            }
            _ => None,
        })
        .unwrap();
    assert_ne!(args[0], args[1]);
    let retained = code.iter().find_map(|instruction| match instruction {
        flbc::Instruction::Copy { dst, src } if *dst == args[0] => Some(*src),
        _ => None,
    });
    let moved = code.iter().find_map(|instruction| match instruction {
        flbc::Instruction::Move { dst, src } if *dst == args[1] => Some(*src),
        _ => None,
    });
    assert!(
        retained.is_some(),
        "the first operand retains its reference"
    );
    assert_eq!(moved, retained, "the final operand transfers the last use");

    // Alias bindings count against the same bounded lowering budget as all
    // other values, and a refused compilation cannot poison a later retry.
    let values = compiled
        .program
        .program()
        .functions()
        .iter()
        .map(|function| usize::from(function.register_count))
        .sum::<usize>();
    let mut limits = IrExecutionLimits::default();
    limits.fir.max_values = values - 1;
    let error = compile_nested(limits).unwrap_err();
    assert!(matches!(error, IrExecutionError::Limit("lowered values")));
    assert!(error.is_resource());
    assert_native_owned_result(&compile_nested(IrExecutionLimits::default()).unwrap(), "1");
}

#[test]
fn imported_list_recursion_still_accepts_scalar_nil() {
    let entry = function(
        "NativeLists.scalarNil",
        0,
        vec![
            binding(
                1,
                IrExpr::Ctor {
                    info: fln_olean::ir::IrCtorInfo {
                        name: name("List.nil"),
                        cidx: 0,
                        size: 0,
                        usize: 0,
                        ssize: 0,
                    },
                    args: vec![],
                },
            ),
            call(2, "NativeLists.sum", &[1]),
        ],
        IrArg::Var(2),
    );
    let compiled = compile_users(
        vec![native_list_sum(), entry],
        "NativeLists.scalarNil",
        &[],
        IrExecutionLimits::default(),
    )
    .unwrap();
    assert_eq!(returned(&compiled), "0");
}

#[test]
fn scalar_constructor_tags_do_not_consume_the_heap_tag_namespace() {
    use fln_olean::ir::{IrAlt, IrCtorInfo};

    let info = |tag| IrCtorInfo {
        name: name("User.WideEnum"),
        cidx: tag,
        size: 0,
        usize: 0,
        ssize: 0,
    };
    let heap_max = u64::from(fln_rt::abi::TAG_MAX_CTOR_TAG);
    for ty in [IrType::Tagged, IrType::UInt32] {
        for (tag, expected) in [
            (heap_max, "11"),
            (255, "22"),
            (256, "33"),
            (0x1f980, "44"),
            (0x110000, "55"),
        ] {
            let mut alts: Vec<_> = [(heap_max, 11), (255, 22), (256, 33), (0x1f980, 44)]
                .into_iter()
                .enumerate()
                .map(|(index, (tag, answer))| {
                    let x = index as u64 + 2;
                    IrAlt::Ctor {
                        info: info(tag),
                        body: ir_body(vec![number(x, answer)], IrTerminal::Ret(IrArg::Var(x))),
                    }
                })
                .collect();
            alts.push(IrAlt::Default {
                body: ir_body(vec![number(6, 55)], IrTerminal::Ret(IrArg::Var(6))),
            });
            let expr = if matches!(&ty, IrType::UInt32) {
                IrExpr::Lit(IrLit::Num(IrNat::Small(tag)))
            } else {
                IrExpr::Ctor {
                    info: info(tag),
                    args: vec![],
                }
            };
            let declaration = body_function(
                "User.enumCase",
                0,
                ir_body(
                    vec![IrStmt::VDecl {
                        x: 1,
                        ty: ty.clone(),
                        expr,
                    }],
                    IrTerminal::Case {
                        type_name: name("User.WideEnum"),
                        x: 1,
                        x_type: ty.clone(),
                        alts,
                    },
                ),
            );
            let mut limits = IrExecutionLimits::default();
            // These values never allocate a heap constructor or need its table.
            limits.fir.max_constructors = 0;
            let compiled = compile_users(vec![declaration], "User.enumCase", &[], limits).unwrap();
            assert_eq!(
                returned(&compiled),
                expected,
                "scalar constructor tag {tag}"
            );
        }
    }
}

#[test]
fn large_scalar_tags_still_match_after_erasing_their_representation() {
    use fln_olean::ir::{IrAlt, IrCtorInfo};

    let info = IrCtorInfo {
        name: name("User.WideEnum.last"),
        cidx: 256,
        size: 0,
        usize: 0,
        ssize: 0,
    };
    let declaration = body_function(
        "User.erasedEnum",
        0,
        ir_body(
            vec![binding(
                1,
                IrExpr::Ctor {
                    info: info.clone(),
                    args: vec![],
                },
            )],
            IrTerminal::Case {
                type_name: name("User.WideEnum"),
                x: 1,
                x_type: IrType::TObject,
                alts: vec![IrAlt::Ctor {
                    info,
                    body: ir_body(vec![number(2, 42)], IrTerminal::Ret(IrArg::Var(2))),
                }],
            },
        ),
    );
    let mut limits = IrExecutionLimits::default();
    limits.fir.max_constructors = 0;
    let compiled = compile_users(vec![declaration], "User.erasedEnum", &[], limits).unwrap();
    assert_eq!(returned(&compiled), "42");
}

#[test]
fn scalar_tag_lowering_keeps_uninitialized_and_invalid_heap_layout_refusals() {
    use fln_olean::ir::{IrAlt, IrCtorInfo};

    for (usize, ssize) in [(1, 0), (0, 8)] {
        let info = IrCtorInfo {
            name: name("User.Packed.mk"),
            cidx: 0,
            size: 0,
            usize,
            ssize,
        };
        let declaration = function(
            "User.packedConstructor",
            0,
            vec![binding(
                1,
                IrExpr::Ctor {
                    info: info.clone(),
                    args: vec![],
                },
            )],
            IrArg::Var(1),
        );
        let case = body_function(
            "User.packedCase",
            1,
            ir_body(
                vec![],
                IrTerminal::Case {
                    type_name: name("User.Packed"),
                    x: 1,
                    x_type: IrType::TObject,
                    alts: vec![IrAlt::Ctor {
                        info,
                        body: ir_body(vec![], IrTerminal::Ret(IrArg::Var(1))),
                    }],
                },
            ),
        );
        let error = compile_users(
            vec![declaration],
            "User.packedConstructor",
            &[],
            IrExecutionLimits::default(),
        )
        .unwrap_err();
        assert!(
            matches!(
                error,
                IrExecutionError::Unsupported {
                    form: "uninitialized packed constructor",
                    ..
                }
            ),
            "{error:?}"
        );
        // Packed cases now execute, but a scalar is still not their heap
        // constructor. The existing unreachable arm must never return it.
        let compiled = compile_users(
            vec![case],
            "User.packedCase",
            &[nat(42)],
            IrExecutionLimits::default(),
        )
        .unwrap();
        assert!(matches!(
            compiled.execute(ExecutionLimits::default(), None).outcome,
            Outcome::Complete(VmExit::Panicked { message, .. })
                if message == "unreachable imported IR in User.packedCase"
        ));
    }

    let declaration = function(
        "User.invalidHeap",
        1,
        vec![binding(
            2,
            IrExpr::Ctor {
                info: IrCtorInfo {
                    name: name("User.Invalid.mk"),
                    cidx: u64::from(fln_rt::abi::TAG_MAX_CTOR_TAG) + 1,
                    size: 1,
                    usize: 0,
                    ssize: 0,
                },
                args: vec![IrArg::Var(1)],
            },
        )],
        IrArg::Var(2),
    );
    let error = compile_users(
        vec![declaration],
        "User.invalidHeap",
        &[nat(42)],
        IrExecutionLimits::default(),
    )
    .unwrap_err();
    assert!(
        matches!(error, IrExecutionError::IrValidation(_)),
        "{error:?}"
    );
    assert!(!error.is_resource());
}

fn packed_test_info(objects: u64, usize: u64, bytes: u64) -> fln_olean::ir::IrCtorInfo {
    fln_olean::ir::IrCtorInfo {
        name: name("Packed.Record.mk"),
        cidx: 0,
        size: objects,
        usize,
        ssize: bytes,
    }
}

#[test]
fn packed_integer_fields_cross_calls_joins_and_closure_captures() {
    for (ty, family, bytes, expected) in [
        (IrType::UInt8, "UInt8", 1, 0xfe),
        (IrType::UInt16, "UInt16", 2, 0xfedc),
        (IrType::UInt32, "UInt32", 4, 0xfedc_ba98),
        (IrType::UInt64, "UInt64", 8, (1u64 << 63) + 17),
        (IrType::USize, "USize", 0, (1u64 << 63) + 23),
    ] {
        let info = packed_test_info(1, u64::from(ty == IrType::USize), bytes);
        let projection = if ty == IrType::USize {
            IrExpr::UProj { i: 1, x: 1 }
        } else {
            IrExpr::SProj {
                n: 1,
                offset: 0,
                x: 1,
            }
        };
        let store = if ty == IrType::USize {
            IrStmt::USet { x: 2, i: 1, y: 3 }
        } else {
            IrStmt::SSet {
                x: 2,
                i: 1,
                offset: 0,
                y: 3,
                ty: ty.clone(),
            }
        };
        let read = function(
            "Packed.read",
            2,
            vec![
                wide_ir_binding(3, &ty, projection),
                call(4, &format!("{family}.toNat"), &[3]),
            ],
            IrArg::Var(4),
        );
        let entry = body_function(
            "Packed.entry",
            1,
            ir_body(
                vec![
                    binding(
                        2,
                        IrExpr::Ctor {
                            info,
                            args: vec![IrArg::Var(1)],
                        },
                    ),
                    // A real compiler sequence may compute/unbox the scalar
                    // after allocating the constructor, before its first use.
                    wide_ir_binding(3, &ty, IrExpr::Lit(IrLit::Num(IrNat::Small(expected)))),
                    store,
                    binding(
                        4,
                        IrExpr::Pap {
                            function: name("Packed.read"),
                            args: vec![IrArg::Var(2)],
                        },
                    ),
                    join(
                        5,
                        &[6],
                        ir_body(
                            vec![binding(
                                7,
                                IrExpr::Ap {
                                    x: 4,
                                    args: vec![IrArg::Var(6)],
                                },
                            )],
                            IrTerminal::Ret(IrArg::Var(7)),
                        ),
                    ),
                    number(8, 0),
                ],
                jump(5, &[8]),
            ),
        );
        let compiled = compile_users(
            vec![read, entry],
            "Packed.entry",
            &[EntryArgument::String("retained λ 🦀".to_owned())],
            IrExecutionLimits::default(),
        )
        .unwrap();
        assert_native_owned_result(&compiled, &expected.to_string());
        assert!(
            compiled
                .program
                .program()
                .functions()
                .iter()
                .flat_map(|function| &function.code)
                .any(|instruction| matches!(instruction, flbc::Instruction::CtorPacked { .. }))
        );
        assert!(
            compiled
                .program
                .program()
                .functions()
                .iter()
                .flat_map(|function| &function.code)
                .any(|instruction| matches!(instruction, flbc::Instruction::CtorScalar { .. }))
        );
    }
}

#[test]
fn packed_mixed_fields_keep_source_order_object_fields_and_case_defaults() {
    use fln_olean::ir::IrAlt;

    let info = packed_test_info(1, 1, 15);
    let scalars = [
        (IrType::UInt8, "UInt8", 14, 0xab),
        (IrType::USize, "USize", 0, (1u64 << 63) + 23),
        (IrType::UInt32, "UInt32", 8, 0xdead_beef),
        (IrType::UInt64, "UInt64", 0, (1u64 << 63) + 17),
        (IrType::UInt16, "UInt16", 12, 0xbeef),
    ];
    let mut make = vec![binding(
        2,
        IrExpr::Ctor {
            info: info.clone(),
            args: vec![IrArg::Var(1)],
        },
    )];
    let mut read = vec![
        binding(2, IrExpr::Proj { i: 0, x: 1 }),
        call(3, "String.length", &[2]),
    ];
    let mut sum = 3;
    for (index, (ty, family, offset, value)) in scalars.iter().enumerate() {
        let variable = index as u64 + 3;
        make.push(wide_ir_binding(
            variable,
            ty,
            IrExpr::Lit(IrLit::Num(IrNat::Small(*value))),
        ));
        make.push(if *ty == IrType::USize {
            IrStmt::USet {
                x: 2,
                i: 1,
                y: variable,
            }
        } else {
            IrStmt::SSet {
                x: 2,
                i: 2,
                offset: *offset,
                y: variable,
                ty: ty.clone(),
            }
        });
        let variable = index as u64 * 3 + 4;
        let projection = if *ty == IrType::USize {
            IrExpr::UProj { i: 1, x: 1 }
        } else {
            IrExpr::SProj {
                n: 2,
                offset: *offset,
                x: 1,
            }
        };
        read.push(wide_ir_binding(variable, ty, projection));
        read.push(call(variable + 1, &format!("{family}.toNat"), &[variable]));
        read.push(call(variable + 2, "Nat.add", &[sum, variable + 1]));
        sum = variable + 2;
    }
    make.push(call(8, "Packed.inspect", &[2]));
    let inspect = body_function(
        "Packed.inspect",
        1,
        ir_body(
            vec![],
            IrTerminal::Case {
                type_name: name("Packed.Record"),
                x: 1,
                x_type: IrType::TObject,
                alts: vec![
                    IrAlt::Ctor {
                        info,
                        body: ir_body(read, IrTerminal::Ret(IrArg::Var(sum))),
                    },
                    IrAlt::Default {
                        body: ir_body(vec![number(30, 7)], IrTerminal::Ret(IrArg::Var(30))),
                    },
                ],
            },
        ),
    );
    let make = function("Packed.mixed", 1, make, IrArg::Var(8));
    let mut other_info = packed_test_info(1, 0, 0);
    other_info.cidx = 1;
    let other = function(
        "Packed.other",
        1,
        vec![
            binding(
                2,
                IrExpr::Ctor {
                    info: other_info,
                    args: vec![IrArg::Var(1)],
                },
            ),
            call(3, "Packed.inspect", &[2]),
        ],
        IrArg::Var(3),
    );
    let expected = scalars
        .iter()
        .map(|(_, _, _, value)| u128::from(*value))
        .sum::<u128>()
        + 2;
    for (entry, expected) in [
        ("Packed.mixed", expected.to_string()),
        ("Packed.other", "7".to_owned()),
    ] {
        let compiled = compile_users(
            vec![make.clone(), inspect.clone(), other.clone()],
            entry,
            &[EntryArgument::String("λ🦀".to_owned())],
            IrExecutionLimits::default(),
        )
        .unwrap();
        assert_native_owned_result(&compiled, &expected);
    }
}

#[test]
fn packed_scalar_only_cases_keep_heap_tags_and_default_arms() {
    use fln_olean::ir::IrAlt;

    let mut info = packed_test_info(0, 0, 1);
    info.cidx = 3;
    let inspect = body_function(
        "Packed.scalarCase",
        1,
        ir_body(
            vec![],
            IrTerminal::Case {
                type_name: name("Packed.Record"),
                x: 1,
                x_type: IrType::TObject,
                alts: vec![
                    IrAlt::Ctor {
                        info: info.clone(),
                        body: ir_body(
                            vec![
                                wide_ir_binding(
                                    2,
                                    &IrType::UInt8,
                                    IrExpr::SProj {
                                        n: 0,
                                        offset: 0,
                                        x: 1,
                                    },
                                ),
                                call(3, "UInt8.toNat", &[2]),
                            ],
                            IrTerminal::Ret(IrArg::Var(3)),
                        ),
                    },
                    IrAlt::Default {
                        body: ir_body(vec![number(4, 99)], IrTerminal::Ret(IrArg::Var(4))),
                    },
                ],
            },
        ),
    );
    for (tag, expected) in [(3, "42"), (4, "99")] {
        let mut info = info.clone();
        info.cidx = tag;
        let entry = function(
            "Packed.scalarEntry",
            0,
            vec![
                binding(1, IrExpr::Ctor { info, args: vec![] }),
                wide_ir_binding(2, &IrType::UInt8, IrExpr::Lit(IrLit::Num(IrNat::Small(42)))),
                IrStmt::SSet {
                    x: 1,
                    i: 0,
                    offset: 0,
                    y: 2,
                    ty: IrType::UInt8,
                },
                call(3, "Packed.scalarCase", &[1]),
            ],
            IrArg::Var(3),
        );
        let compiled = compile_users(
            vec![inspect.clone(), entry],
            "Packed.scalarEntry",
            &[],
            IrExecutionLimits::default(),
        )
        .unwrap();
        assert_native_owned_result(&compiled, expected);
    }
}

#[test]
fn packed_initialization_refuses_gaps_overlap_object_slots_and_overflow() {
    let store = |i, offset, ty| IrStmt::SSet {
        x: 2,
        i,
        offset,
        y: 3,
        ty,
    };
    for (stores, expected) in [
        (vec![], "uninitialized packed constructor"),
        (
            vec![store(1, 0, IrType::UInt16)],
            "uninitialized packed constructor",
        ),
        (
            vec![store(1, 0, IrType::UInt32), store(1, 0, IrType::UInt32)],
            "packed scalar initialization layout",
        ),
        (
            vec![store(1, 1, IrType::UInt32)],
            "packed scalar initialization layout",
        ),
        (
            vec![store(0, 0, IrType::UInt32)],
            "packed scalar initialization layout",
        ),
        (
            vec![IrStmt::USet { x: 2, i: 1, y: 3 }],
            "packed scalar initialization layout",
        ),
        (
            vec![store(u64::MAX, 0, IrType::UInt32)],
            "packed scalar offset",
        ),
    ] {
        let mut stmts = vec![
            binding(
                2,
                IrExpr::Ctor {
                    info: packed_test_info(1, 0, 4),
                    args: vec![IrArg::Var(1)],
                },
            ),
            wide_ir_binding(
                3,
                &IrType::UInt32,
                IrExpr::Lit(IrLit::Num(IrNat::Small(42))),
            ),
        ];
        stmts.extend(stores);
        let error = compile_users(
            vec![function("Packed.invalid", 1, stmts, IrArg::Var(2))],
            "Packed.invalid",
            &[EntryArgument::String("retained".to_owned())],
            IrExecutionLimits::default(),
        )
        .unwrap_err();
        assert!(
            matches!(error, IrExecutionError::Unsupported { form, .. } if form == expected),
            "{error:?}"
        );
        assert!(!error.is_resource());
    }
}

#[test]
fn packed_initializers_validate_before_intervening_native_calls() {
    use fln_rt::obj::StdoutCapture;
    use fln_vm::interpreter::VmRefusal;

    for (ty, family, bytes) in [
        (IrType::UInt8, "UInt8", 1),
        (IrType::UInt16, "UInt16", 2),
        (IrType::UInt32, "UInt32", 4),
        (IrType::UInt64, "UInt64", 8),
        (IrType::USize, "USize", 0),
    ] {
        for valid in [false, true] {
            // Keep the entry parameter erased so malformed wide operands
            // reach the setter itself, instead of failing entry adaptation.
            let mut stmts = Vec::new();
            if valid {
                stmts.push(wide_ir_binding(
                    2,
                    &ty,
                    IrExpr::Lit(IrLit::Num(IrNat::Small(42))),
                ));
            }
            stmts.push(binding(
                3,
                IrExpr::Ctor {
                    info: packed_test_info(0, u64::from(ty == IrType::USize), bytes),
                    args: vec![],
                },
            ));
            let y = if valid { 2 } else { 1 };
            stmts.push(if ty == IrType::USize {
                IrStmt::USet { x: 3, i: 0, y }
            } else {
                IrStmt::SSet {
                    x: 3,
                    i: 0,
                    offset: 0,
                    y,
                    ty: ty.clone(),
                }
            });
            stmts.extend([
                binding(
                    4,
                    IrExpr::Lit(IrLit::Str("packed field initialized".to_owned())),
                ),
                binding(
                    5,
                    IrExpr::Pap {
                        function: name("Packed.continue"),
                        args: vec![],
                    },
                ),
                call(6, "dbgTrace", &[4, 5]),
                wide_ir_binding(
                    7,
                    &ty,
                    if ty == IrType::USize {
                        IrExpr::UProj { i: 0, x: 3 }
                    } else {
                        IrExpr::SProj {
                            n: 0,
                            offset: 0,
                            x: 3,
                        }
                    },
                ),
                call(8, &format!("{family}.toNat"), &[7]),
            ]);
            let modules = [module(vec![
                function("Packed.ordered", 1, stmts, IrArg::Var(8)),
                function("Packed.continue", 1, vec![number(2, 0)], IrArg::Var(2)),
                // The source telescope has a static type argument; the
                // generated native contract has two executable arguments.
                native_array_extern("dbgTrace", 2),
            ])];
            let compiled = compile(
                &modules,
                &name("Packed.ordered"),
                &[EntryArgument::String("invalid scalar carrier".to_owned())],
                &bounded_partition(&[]),
                &BTreeSet::from([name("Packed.ordered"), name("Packed.continue")]),
                IrExecutionLimits::default(),
            )
            .unwrap();
            let encoded =
                flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default())
                    .unwrap();
            let replay = flbc::decode_canonical(&encoded, flbc::CodecLimits::default()).unwrap();
            for program in [compiled.program.program(), &replay] {
                let capture = StdoutCapture::begin_evaluation(1024).unwrap();
                let outcome =
                    fln_vm::interpreter::execute(program, ExecutionLimits::default(), None);
                let captured = capture.finish();
                assert_eq!(captured.error, None);
                if valid {
                    let Outcome::Complete(VmExit::Returned(value)) = outcome else {
                        panic!("valid {family} interleaving did not return: {outcome:?}");
                    };
                    assert_eq!(crate::nat_decimal(&value.value).as_deref(), Some("42"));
                    assert_eq!(captured.bytes, b"packed field initialized\n");
                } else {
                    assert!(
                        matches!(
                            outcome,
                            Outcome::Complete(VmExit::Refused {
                                refusal: VmRefusal::TypeMismatch { operation, .. },
                                ..
                            }) if operation == format!("{family}.toNat")
                        ),
                        "malformed {family} initializer: {outcome:?}"
                    );
                    assert!(captured.bytes.is_empty(), "{family}: {captured:?}");
                }
            }
        }
    }
}

#[test]
fn packed_scalar_stores_are_refused_after_reads_calls_or_captures() {
    let store = IrStmt::SSet {
        x: 1,
        i: 0,
        offset: 0,
        y: 2,
        ty: IrType::UInt8,
    };
    for escape in [
        wide_ir_binding(
            3,
            &IrType::UInt8,
            IrExpr::SProj {
                n: 0,
                offset: 0,
                x: 1,
            },
        ),
        call(3, "Packed.identity", &[1, 2]),
        binding(
            3,
            IrExpr::Pap {
                function: name("Packed.identity"),
                args: vec![IrArg::Var(1)],
            },
        ),
        binding(
            3,
            IrExpr::Ctor {
                info: packed_test_info(1, 0, 0),
                args: vec![IrArg::Var(1)],
            },
        ),
    ] {
        let entry = function(
            "Packed.mutate",
            0,
            vec![
                binding(
                    1,
                    IrExpr::Ctor {
                        info: packed_test_info(0, 0, 1),
                        args: vec![],
                    },
                ),
                wide_ir_binding(2, &IrType::UInt8, IrExpr::Lit(IrLit::Num(IrNat::Small(42)))),
                store.clone(),
                escape,
                store.clone(),
            ],
            IrArg::Var(1),
        );
        let error = compile_users(
            vec![entry, function("Packed.identity", 2, vec![], IrArg::Var(1))],
            "Packed.mutate",
            &[],
            IrExecutionLimits::default(),
        )
        .unwrap_err();
        assert!(
            matches!(
                error,
                IrExecutionError::Unsupported {
                    form: "packed mutation after read or escape",
                    ..
                }
            ),
            "{error:?}"
        );
        assert!(!error.is_resource());
    }
}

#[test]
fn packed_projections_refuse_wrong_objects_and_full_width_bounds() {
    use fln_vm::interpreter::VmRefusal;

    let decode = function(
        "Packed.decode",
        1,
        vec![
            wide_ir_binding(
                2,
                &IrType::UInt64,
                IrExpr::SProj {
                    n: 0,
                    offset: 1,
                    x: 1,
                },
            ),
            call(3, "UInt64.toNat", &[2]),
        ],
        IrArg::Var(3),
    );
    for argument in [
        nat(42),
        EntryArgument::String("not a packed constructor".to_owned()),
    ] {
        let compiled = compile_users(
            vec![decode.clone()],
            "Packed.decode",
            &[argument],
            IrExecutionLimits::default(),
        )
        .unwrap();
        assert!(matches!(
            compiled.execute(ExecutionLimits::default(), None).outcome,
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::TypeMismatch { .. },
                ..
            })
        ));
    }
    for (objects, bytes) in [(1, 0), (0, 1)] {
        let mut stmts = vec![
            number(1, 42),
            binding(
                2,
                IrExpr::Ctor {
                    info: packed_test_info(objects, 0, bytes),
                    args: if objects == 0 {
                        vec![]
                    } else {
                        vec![IrArg::Var(1)]
                    },
                },
            ),
        ];
        if bytes != 0 {
            stmts.push(wide_ir_binding(
                3,
                &IrType::UInt8,
                IrExpr::Lit(IrLit::Num(IrNat::Small(42))),
            ));
            stmts.push(IrStmt::SSet {
                x: 2,
                i: 0,
                offset: 0,
                y: 3,
                ty: IrType::UInt8,
            });
        }
        stmts.push(call(4, "Packed.decode", &[2]));
        let compiled = compile_users(
            vec![
                decode.clone(),
                function("Packed.bounds", 0, stmts, IrArg::Var(4)),
            ],
            "Packed.bounds",
            &[],
            IrExecutionLimits::default(),
        )
        .unwrap();
        assert!(matches!(
            compiled.execute(ExecutionLimits::default(), None).outcome,
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::ConstructorScalarBounds { .. },
                ..
            })
        ));
    }
}

#[test]
fn packed_constructor_limits_stop_before_publication_and_allow_retry() {
    let make = function(
        "Packed.bounded",
        0,
        vec![
            binding(
                1,
                IrExpr::Ctor {
                    info: packed_test_info(0, 0, 1),
                    args: vec![],
                },
            ),
            wide_ir_binding(2, &IrType::UInt8, IrExpr::Lit(IrLit::Num(IrNat::Small(42)))),
            IrStmt::SSet {
                x: 1,
                i: 0,
                offset: 0,
                y: 2,
                ty: IrType::UInt8,
            },
            wide_ir_binding(
                3,
                &IrType::UInt8,
                IrExpr::SProj {
                    n: 0,
                    offset: 0,
                    x: 1,
                },
            ),
            call(4, "UInt8.toNat", &[3]),
        ],
        IrArg::Var(4),
    );
    for resource in [
        "packed constructor bytes",
        "packed constructor operands",
        "lowered values",
    ] {
        let mut limits = IrExecutionLimits::default();
        match resource {
            "packed constructor bytes" => limits.fir.max_literal_bytes = 0,
            "packed constructor operands" => limits.fir.max_operands = 0,
            _ => limits.fir.max_values = 2,
        }
        let error = compile_users(vec![make.clone()], "Packed.bounded", &[], limits).unwrap_err();
        assert!(
            matches!(error, IrExecutionError::Limit(name) if name == resource),
            "{error:?}"
        );
        assert!(error.is_resource());
    }
    let compiled = compile_users(
        vec![make],
        "Packed.bounded",
        &[],
        IrExecutionLimits::default(),
    )
    .unwrap();
    assert_native_owned_result(&compiled, "42");
}

fn wide_ir_binding(x: u64, ty: &IrType, expr: IrExpr) -> IrStmt {
    IrStmt::VDecl {
        x,
        ty: ty.clone(),
        expr,
    }
}

fn wide_ir_entry(mut declaration: IrDecl, ty: &IrType) -> IrDecl {
    let IrDecl::Function { params, .. } = &mut declaration else {
        unreachable!()
    };
    params[0].ty = ty.clone();
    declaration
}

fn assert_wide_ir_result(compiled: &CompiledIr, expected: u64) {
    assert_eq!(returned(compiled), expected.to_string());
    let bytes = flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default())
        .expect("encode wide scalar program");
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default())
        .expect("decode wide scalar program");
    let outcome = fln_vm::interpreter::execute(&replay, ExecutionLimits::default(), None);
    let Outcome::Complete(VmExit::Returned(value)) = outcome else {
        panic!("wide scalar replay did not return: {outcome:?}");
    };
    assert_eq!(
        crate::nat_decimal(&value.value).expect("Nat replay result"),
        expected.to_string()
    );
}

#[test]
fn wide_ir_literals_and_entry_arguments_preserve_high_bits_and_wrap_large_naturals() {
    for (ty, family) in [(IrType::UInt64, "UInt64"), (IrType::USize, "USize")] {
        for (literal, low) in [
            (IrNat::Small((1u64 << 63) - 1), (1u64 << 63) - 1),
            (IrNat::Small(1u64 << 63), 1u64 << 63),
            (IrNat::Small(u64::MAX), u64::MAX),
            (IrNat::Big(vec![17, 1]), 17),
            (IrNat::Big(vec![u64::MAX, u64::MAX]), u64::MAX),
        ] {
            let expected = if ty == IrType::USize {
                low as usize as u64
            } else {
                low
            };
            let literal_program = compile_users(
                vec![function(
                    "Wide.literal",
                    0,
                    vec![
                        wide_ir_binding(1, &ty, IrExpr::Lit(IrLit::Num(literal.clone()))),
                        call(2, &format!("{family}.toNat"), &[1]),
                    ],
                    IrArg::Var(2),
                )],
                "Wide.literal",
                &[],
                IrExecutionLimits::default(),
            )
            .expect("typed wide literals compile");
            assert_wide_ir_result(&literal_program, expected);
            let entry_program = compile_users(
                vec![wide_ir_entry(
                    function(
                        "Wide.entry",
                        1,
                        vec![call(2, &format!("{family}.toNat"), &[1])],
                        IrArg::Var(2),
                    ),
                    &ty,
                )],
                "Wide.entry",
                &[EntryArgument::Nat(literal)],
                IrExecutionLimits::default(),
            )
            .expect("wide entry parameters canonicalize through their native ABI");
            assert_wide_ir_result(&entry_program, expected);
            assert!(
                entry_program
                    .native_externs()
                    .iter()
                    .any(|row| row == &format!("extern:{family}.ofNat"))
            );
        }
    }
}

#[test]
fn boxed_wide_values_survive_constructor_join_and_captured_closure_boundaries() {
    use fln_olean::ir::IrCtorInfo;

    for (ty, family) in [(IrType::UInt64, "UInt64"), (IrType::USize, "USize")] {
        let callback = function(
            "Wide.callback",
            2,
            vec![
                wide_ir_binding(3, &ty, IrExpr::Unbox { x: 1 }),
                binding(
                    4,
                    IrExpr::Box {
                        ty: ty.clone(),
                        x: 3,
                    },
                ),
                wide_ir_binding(5, &ty, IrExpr::Unbox { x: 4 }),
                call(6, &format!("{family}.toNat"), &[5]),
            ],
            IrArg::Var(6),
        );
        let entry = body_function(
            "Wide.boundaries",
            0,
            ir_body(
                vec![
                    wide_ir_binding(10, &ty, IrExpr::Lit(IrLit::Num(IrNat::Small(u64::MAX)))),
                    binding(
                        11,
                        IrExpr::Box {
                            ty: ty.clone(),
                            x: 10,
                        },
                    ),
                    binding(
                        12,
                        IrExpr::Ctor {
                            info: IrCtorInfo {
                                name: name("Wide.payload"),
                                cidx: 0,
                                size: 1,
                                usize: 0,
                                ssize: 0,
                            },
                            args: vec![IrArg::Var(11)],
                        },
                    ),
                    join(
                        20,
                        &[21],
                        ir_body(
                            vec![
                                binding(22, IrExpr::Proj { i: 0, x: 21 }),
                                binding(
                                    23,
                                    IrExpr::Pap {
                                        function: name("Wide.callback"),
                                        args: vec![IrArg::Var(22)],
                                    },
                                ),
                                number(24, 0),
                                binding(
                                    25,
                                    IrExpr::Ap {
                                        x: 23,
                                        args: vec![IrArg::Var(24)],
                                    },
                                ),
                            ],
                            IrTerminal::Ret(IrArg::Var(25)),
                        ),
                    ),
                ],
                jump(20, &[12]),
            ),
        );
        let compiled = compile_users(
            vec![callback, entry],
            "Wide.boundaries",
            &[],
            IrExecutionLimits::default(),
        )
        .expect("boxed words cross object, join, and closure boundaries");
        let expected = if ty == IrType::USize {
            usize::MAX as u64
        } else {
            u64::MAX
        };
        assert_wide_ir_result(&compiled, expected);
        assert_eq!(compiled.reference_functions().len(), 3);
    }
}

#[test]
fn wide_ir_cases_compare_the_full_word_and_keep_the_default_arm() {
    use fln_olean::ir::{IrAlt, IrCtorInfo};

    for (ty, family) in [(IrType::UInt64, "UInt64"), (IrType::USize, "USize")] {
        let mut alts: Vec<_> = [(1u64 << 63, 2, 11), (u64::MAX, 3, 22)]
            .into_iter()
            .map(|(tag, x, result)| IrAlt::Ctor {
                info: IrCtorInfo {
                    name: name("Wide.tag"),
                    cidx: tag,
                    size: 0,
                    usize: 0,
                    ssize: 0,
                },
                body: ir_body(vec![number(x, result)], IrTerminal::Ret(IrArg::Var(x))),
            })
            .collect();
        alts.push(IrAlt::Default {
            body: ir_body(vec![number(4, 33)], IrTerminal::Ret(IrArg::Var(4))),
        });
        let declaration = wide_ir_entry(
            body_function(
                "Wide.case",
                1,
                ir_body(
                    vec![],
                    IrTerminal::Case {
                        type_name: name(family),
                        x: 1,
                        x_type: ty.clone(),
                        alts,
                    },
                ),
            ),
            &ty,
        );
        for (input, expected) in [(1u64 << 63, 11), (u64::MAX, 22), (7, 33)] {
            let compiled = compile_users(
                vec![declaration.clone()],
                "Wide.case",
                &[nat(input)],
                IrExecutionLimits::default(),
            )
            .expect("wide case tags do not require constructor header tags");
            assert_wide_ir_result(&compiled, expected);
            assert!(
                compiled
                    .native_externs()
                    .iter()
                    .any(|row| row == &format!("extern:{family}.decEq"))
            );
        }
    }
}

#[test]
fn wide_ir_unboxing_refuses_strings_and_object_field_constructors() {
    for (ty, family) in [(IrType::UInt64, "UInt64"), (IrType::USize, "USize")] {
        let decode = function(
            "Wide.decode",
            1,
            vec![
                wide_ir_binding(2, &ty, IrExpr::Unbox { x: 1 }),
                call(3, &format!("{family}.toNat"), &[2]),
            ],
            IrArg::Var(3),
        );
        let string = compile_users(
            vec![decode.clone()],
            "Wide.decode",
            &[EntryArgument::String("not a wide scalar".to_owned())],
            IrExecutionLimits::default(),
        )
        .unwrap();
        let constructor = compile_users(
            vec![
                decode,
                function(
                    "Wide.badConstructor",
                    0,
                    vec![
                        number(1, 42),
                        binding(
                            2,
                            IrExpr::Ctor {
                                info: fln_olean::ir::IrCtorInfo {
                                    name: name("Wide.objectField"),
                                    cidx: 0,
                                    size: 1,
                                    usize: 0,
                                    ssize: 0,
                                },
                                args: vec![IrArg::Var(1)],
                            },
                        ),
                        call(3, "Wide.decode", &[2]),
                    ],
                    IrArg::Var(3),
                ),
            ],
            "Wide.badConstructor",
            &[],
            IrExecutionLimits::default(),
        )
        .unwrap();
        for compiled in [string, constructor] {
            assert!(
                matches!(
                    compiled.execute(ExecutionLimits::default(), None).outcome,
                    Outcome::Complete(VmExit::Refused {
                        refusal: fln_vm::interpreter::VmRefusal::TypeMismatch { .. },
                        ..
                    })
                ),
                "wrong wide scalar carriers must refuse without fabricating a value"
            );
        }
    }
}

#[test]
fn wide_ir_native_arithmetic_wraps_without_losing_the_high_bit() {
    for (ty, family) in [(IrType::UInt64, "UInt64"), (IrType::USize, "USize")] {
        let compiled = compile_users(
            vec![function(
                "Wide.wrapAdd",
                0,
                vec![
                    wide_ir_binding(1, &ty, IrExpr::Lit(IrLit::Num(IrNat::Small(u64::MAX)))),
                    wide_ir_binding(2, &ty, IrExpr::Lit(IrLit::Num(IrNat::Small(1)))),
                    wide_ir_binding(
                        3,
                        &ty,
                        IrExpr::Fap {
                            function: name(&format!("{family}.add")),
                            args: vec![IrArg::Var(1), IrArg::Var(2)],
                        },
                    ),
                    call(4, &format!("{family}.toNat"), &[3]),
                ],
                IrArg::Var(4),
            )],
            "Wide.wrapAdd",
            &[],
            IrExecutionLimits::default(),
        )
        .expect("wide scalar arguments obey their native arithmetic contracts");
        assert_wide_ir_result(&compiled, 0);
    }
}

fn assert_float_ir_bits(compiled: &CompiledIr, ty: &IrType, expected: u64) {
    let bytes = flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default())
        .expect("encode floating scalar program");
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default())
        .expect("decode floating scalar program");
    for outcome in [
        compiled.execute(ExecutionLimits::default(), None).outcome,
        fln_vm::interpreter::execute(&replay, ExecutionLimits::default(), None),
    ] {
        let Outcome::Complete(VmExit::Returned(value)) = outcome else {
            panic!("floating scalar execution did not return: {outcome:?}");
        };
        assert!(!value.value.is_scalar());
        assert_eq!(value.value.header().tag, 0);
        assert_eq!(value.value.header().other, 0);
        let bits = if *ty == IrType::Float32 {
            value.value.try_ctor_scalar_u32(0).map(u64::from)
        } else {
            value.value.try_ctor_scalar_u64(0)
        };
        assert_eq!(bits, Some(expected));
    }
}

fn float_argument(ty: &IrType, bits: u64) -> EntryArgument {
    if *ty == IrType::Float32 {
        EntryArgument::Float32Bits(bits as u32)
    } else {
        EntryArgument::FloatBits(bits)
    }
}

#[test]
fn pinned_compiler_float_calls_callbacks_and_packed_records_match_reference() {
    // Binary IR produced from FloatModule.lean by the v4.32.0 Reference at
    // 8c9756b28d64dab099da31a4c09229a9e6a2ef35. The same pin evaluated these
    // results. The callbacks exercise compiler-generated _boxed adapters;
    // the mixed record has source-order stores at byte offsets 8, 12, 0.
    let module = crate::decode_ir_artifact(
        include_bytes!("../../../fln-olean/fixtures/ir/FloatModule.ir"),
        32 * 1024 * 1024,
    )
    .expect("pinned compiler float fixture decodes");
    let users = module
        .decls
        .iter()
        .map(|decl| decl.name().clone())
        .collect();
    let modules = [module];
    let policy = bounded_partition(&[]);
    for (entry, expected) in [
        ("float64Answer", "4"),
        ("float32Answer", "4"),
        ("floatingRecordAnswer", "9223372038993870855"),
        ("floatingJoinAnswer", "5"),
    ] {
        let compiled = compile(
            &modules,
            &name(entry),
            &[],
            &policy,
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("pinned float entry {entry}: {error:?}"));
        assert_native_owned_result(&compiled, expected);
        assert!(compiled.reference_functions().len() >= 2);
    }
    for (entry, ty, inputs, expected) in [
        (
            "float64Add._boxed",
            IrType::Float,
            [1.5f64.to_bits(), 2.5f64.to_bits()],
            4.0f64.to_bits(),
        ),
        (
            "float32Add._boxed",
            IrType::Float32,
            [u64::from(1.5f32.to_bits()), u64::from(2.5f32.to_bits())],
            u64::from(4.0f32.to_bits()),
        ),
    ] {
        let compiled = compile(
            &modules,
            &name(entry),
            &inputs.map(|bits| float_argument(&ty, bits)),
            &policy,
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap();
        assert_float_ir_bits(&compiled, &ty, expected);
    }
    for (branch, expected) in [(0, 7.0f64), (1, 5.0f64)] {
        let compiled = compile(
            &modules,
            &name("floatingChoose"),
            &[
                nat(branch),
                EntryArgument::FloatBits(2.5f64.to_bits()),
                EntryArgument::FloatBits(3.5f64.to_bits()),
            ],
            &policy,
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap();
        assert_float_ir_bits(&compiled, &IrType::Float, expected.to_bits());
    }
}

#[test]
fn floating_bits_survive_boxes_joins_closures_and_packed_fields_without_nan_normalization() {
    for (ty, width, patterns) in [
        (
            IrType::Float,
            8,
            [
                0,
                1u64 << 63,
                1,
                0x7ff0_0000_0000_0000,
                0xfff0_0000_0000_0000,
                0x7ff8_0000_0000_1234,
                0xfff0_0000_0000_4321,
            ],
        ),
        (
            IrType::Float32,
            4,
            [
                0,
                1u64 << 31,
                1,
                0x7f80_0000,
                0xff80_0000,
                0x7fc0_1234,
                0xff80_4321,
            ],
        ),
    ] {
        let callback = function(
            "Floating.callback",
            2,
            vec![
                wide_ir_binding(3, &ty, IrExpr::Unbox { x: 1 }),
                binding(
                    4,
                    IrExpr::Box {
                        ty: ty.clone(),
                        x: 3,
                    },
                ),
                wide_ir_binding(5, &ty, IrExpr::Unbox { x: 4 }),
            ],
            IrArg::Var(5),
        );
        let entry = wide_ir_entry(
            body_function(
                "Floating.boundaries",
                1,
                ir_body(
                    vec![
                        binding(
                            2,
                            IrExpr::Ctor {
                                info: packed_test_info(0, 0, width),
                                args: vec![],
                            },
                        ),
                        IrStmt::SSet {
                            x: 2,
                            i: 0,
                            offset: 0,
                            y: 1,
                            ty: ty.clone(),
                        },
                        wide_ir_binding(
                            5,
                            &ty,
                            IrExpr::SProj {
                                n: 0,
                                offset: 0,
                                x: 2,
                            },
                        ),
                        IrStmt::JDecl {
                            j: 3,
                            params: vec![IrParam {
                                x: 4,
                                borrow: true,
                                ty: ty.clone(),
                            }],
                            value: ir_body(
                                vec![
                                    binding(
                                        6,
                                        IrExpr::Box {
                                            ty: ty.clone(),
                                            x: 4,
                                        },
                                    ),
                                    binding(
                                        7,
                                        IrExpr::Pap {
                                            function: name("Floating.callback"),
                                            args: vec![IrArg::Var(6)],
                                        },
                                    ),
                                    number(8, 0),
                                    binding(
                                        9,
                                        IrExpr::Ap {
                                            x: 7,
                                            args: vec![IrArg::Var(8)],
                                        },
                                    ),
                                ],
                                IrTerminal::Ret(IrArg::Var(9)),
                            ),
                        },
                    ],
                    jump(3, &[5]),
                ),
            ),
            &ty,
        );
        for bits in patterns {
            let compiled = compile_users(
                vec![callback.clone(), entry.clone()],
                "Floating.boundaries",
                &[float_argument(&ty, bits)],
                IrExecutionLimits::default(),
            )
            .expect("floating carriers survive packed storage, joins, and callbacks");
            assert_float_ir_bits(&compiled, &ty, bits);
            assert_eq!(compiled.reference_functions().len(), 3);
        }
    }
}

#[test]
fn floating_unboxing_and_entry_parameters_refuse_non_scalar_carriers() {
    for ty in [IrType::Float, IrType::Float32] {
        let decode = function(
            "Floating.decode",
            1,
            vec![wide_ir_binding(2, &ty, IrExpr::Unbox { x: 1 })],
            IrArg::Var(2),
        );
        let identity = wide_ir_entry(function("Floating.identity", 1, vec![], IrArg::Var(1)), &ty);
        for declaration in [decode, identity] {
            for argument in [nat(42), EntryArgument::String("not a float".to_owned())] {
                let entry = declaration.name().to_display_string();
                let compiled = compile_users(
                    vec![declaration.clone()],
                    &entry,
                    &[argument],
                    IrExecutionLimits::default(),
                )
                .unwrap();
                assert!(matches!(
                    compiled.execute(ExecutionLimits::default(), None).outcome,
                    Outcome::Complete(VmExit::Refused {
                        refusal: fln_vm::interpreter::VmRefusal::TypeMismatch { .. },
                        ..
                    })
                ));
            }
        }
    }
}

#[test]
fn imported_public_float_of_bits_still_canonicalizes_nans() {
    for (ty, integer, family, input, expected) in [
        (
            IrType::Float,
            IrType::UInt64,
            "Float",
            0xfff0_0000_0000_4321,
            0x7ff8_0000_0000_0000,
        ),
        (
            IrType::Float32,
            IrType::UInt32,
            "Float32",
            0xff80_4321,
            0x7fc0_0000,
        ),
    ] {
        let compiled = compile_users(
            vec![function(
                "Floating.publicOfBits",
                0,
                vec![
                    wide_ir_binding(1, &integer, IrExpr::Lit(IrLit::Num(IrNat::Small(input)))),
                    wide_ir_binding(
                        2,
                        &ty,
                        IrExpr::Fap {
                            function: name(&format!("{family}.ofBits")),
                            args: vec![IrArg::Var(1)],
                        },
                    ),
                ],
                IrArg::Var(2),
            )],
            "Floating.publicOfBits",
            &[],
            IrExecutionLimits::default(),
        )
        .unwrap();
        assert_float_ir_bits(&compiled, &ty, expected);
    }
}

#[test]
fn unsupported_floating_literals_constructors_and_cases_never_become_naturals() {
    use fln_olean::ir::IrAlt;
    for ty in [IrType::Float, IrType::Float32] {
        for (expr, form) in [
            (
                IrExpr::Lit(IrLit::Num(IrNat::Small(1))),
                "floating numeric literal",
            ),
            (
                IrExpr::Ctor {
                    info: packed_test_info(0, 0, 0),
                    args: vec![],
                },
                "floating constructor",
            ),
        ] {
            let result = compile_users(
                vec![function(
                    "Floating.invalid",
                    0,
                    vec![wide_ir_binding(1, &ty, expr)],
                    IrArg::Var(1),
                )],
                "Floating.invalid",
                &[],
                IrExecutionLimits::default(),
            );
            assert!(
                matches!(result, Err(IrExecutionError::Unsupported { form: actual, .. }) if actual == form)
            );
        }
        let result = compile_users(
            vec![wide_ir_entry(
                body_function(
                    "Floating.invalidCase",
                    1,
                    ir_body(
                        vec![],
                        IrTerminal::Case {
                            type_name: name("Float"),
                            x: 1,
                            x_type: ty.clone(),
                            alts: vec![IrAlt::Default {
                                body: ir_body(vec![], IrTerminal::Ret(IrArg::Var(1))),
                            }],
                        },
                    ),
                ),
                &ty,
            )],
            "Floating.invalidCase",
            &[float_argument(&ty, 0)],
            IrExecutionLimits::default(),
        );
        assert!(matches!(
            result,
            Err(IrExecutionError::Unsupported {
                form: "floating constructor case",
                ..
            })
        ));
    }
}
