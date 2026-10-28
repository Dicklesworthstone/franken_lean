#![forbid(unsafe_code)]

use super::*;
use fln_olean::ir::{IrArg, IrBody, IrExpr, IrLit, IrParam, IrTerminal};

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
