use super::*;
use crate::imported_ir::{
    CompiledIr, EntryArgument, IrExecutionLimits, Native, VerifiedPartition, compile, native_row,
    native_signature,
};
use fln_comp::flbc;
use fln_core::outcome::Outcome;
use fln_hash::ir_graph::GraphArchiveLimits;
use fln_olean::ir::{
    IrArg, IrBody, IrDecl, IrExpr, IrLit, IrModule, IrNat, IrStmt, IrTerminal, IrType,
};
use fln_olean::ir_archive::CensusPartition;
use fln_vm::extern_table_generated::EXTERN_ROWS;
use fln_vm::interpreter::{ExecutionLimits, VmExit, execute, nat_decimal};
use std::collections::BTreeSet;

const CELL_ROWS: [&str; 4] = [
    "ST.Prim.mkRef",
    "ST.Prim.Ref.get",
    "ST.Prim.Ref.set",
    "ST.Prim.Ref.swap",
];

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn var(x: u64) -> IrArg {
    IrArg::Var(x)
}

fn bind(x: u64, expr: IrExpr) -> IrStmt {
    IrStmt::VDecl {
        x,
        ty: IrType::TObject,
        expr,
    }
}

fn num(x: u64, value: u64) -> IrStmt {
    bind(x, IrExpr::Lit(IrLit::Num(IrNat::Small(value))))
}

fn call(x: u64, target: &str, args: &[u64]) -> IrStmt {
    bind(
        x,
        IrExpr::Fap {
            function: name(target),
            args: args.iter().copied().map(var).collect(),
        },
    )
}

fn entry(stmts: Vec<IrStmt>, result: u64) -> IrModule {
    IrModule {
        decls: vec![IrDecl::Function {
            name: name("LocalState.main"),
            params: vec![],
            result: IrType::TObject,
            body: IrBody {
                stmts,
                terminal: Box::new(IrTerminal::Ret(var(result))),
            },
            sorry_dep: None,
        }],
        ..IrModule::default()
    }
}

fn compile_module(
    module: &IrModule,
    entry: &str,
    arguments: &[EntryArgument],
    limits: IrExecutionLimits,
) -> Result<CompiledIr, IrExecutionError> {
    let partition = VerifiedPartition {
        partition: CensusPartition::parse("constant_count\t0\n", GraphArchiveLimits::default())
            .unwrap(),
    };
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .filter_map(|declaration| match declaration {
            IrDecl::Function { name, .. } if native_row(name).is_none() => Some(name.clone()),
            _ => None,
        })
        .collect();
    compile(
        std::slice::from_ref(module),
        &name(entry),
        arguments,
        &partition,
        &users,
        limits,
    )
}

fn prepare(module: &IrModule) -> CompiledIr {
    compile_module(module, "LocalState.main", &[], IrExecutionLimits::default()).unwrap()
}

fn assert_nat_replay(compiled: &CompiledIr, expected: &str) {
    let bytes = flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default())
        .unwrap();
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&replay, flbc::CodecLimits::default()).unwrap(),
        bytes
    );
    // Every invocation creates fresh cells. The canonical object contains
    // instructions and literals, not state captured from an earlier run.
    for _ in 0..2 {
        for program in [compiled.program.program(), &replay] {
            let result = execute(program, ExecutionLimits::default(), None);
            let Outcome::Complete(VmExit::Returned(value)) = result else {
                panic!("{result:?}");
            };
            assert_eq!(nat_decimal(&value.value).as_deref(), Some(expected));
        }
    }
    assert!(
        compiled
            .reference_functions()
            .iter()
            .all(|function| function.producer() == "reference")
    );
}

fn state_sequence() -> IrModule {
    entry(
        vec![
            num(1, 7),
            call(2, "ST.Prim.mkRef", &[1]),
            num(3, 20),
            // This result is deliberately unused; the mutation must occur.
            call(4, "ST.Prim.Ref.set", &[2, 3]),
            num(5, 22),
            call(6, "ST.Prim.Ref.swap", &[2, 5]),
            call(7, "ST.Prim.Ref.get", &[2]),
            call(8, "Nat.add", &[6, 7]),
        ],
        8,
    )
}

#[test]
fn only_reviewed_local_cell_effects_are_newly_admitted() {
    for text in CELL_ROWS {
        let row = native_row(&name(text)).unwrap();
        let arity = native_signature::inferred_arity(row).unwrap();
        let native = Native::new(row, arity).unwrap();
        assert_eq!(native.effect, fir::EffectClass::State);
        let expected = if text.ends_with("set") || text.ends_with("swap") {
            2
        } else {
            1
        };
        assert_eq!(arity, expected);
    }
    let mut refused = 0;
    for row in EXTERN_ROWS {
        if row.effect == "pure" || CELL_ROWS.contains(&row.name) {
            continue;
        }
        assert!(
            matches!(
                Native::new(row, row.arity as usize),
                Err(IrExecutionError::Unsupported { .. })
            ),
            "{}",
            row.id
        );
        refused += 1;
    }
    assert!(refused > 0);
}

#[test]
fn local_state_executes_in_order_and_unused_writes_survive_replay() {
    let compiled = prepare(&state_sequence());
    assert_nat_replay(&compiled, "42");
    for text in CELL_ROWS {
        assert!(compiled.native_externs().contains(&format!("extern:{text}")));
    }
}

#[test]
fn native_state_closures_preserve_shared_handles_and_run_once_per_application() {
    let compiled = prepare(&entry(
        vec![
            num(1, 7),
            call(2, "ST.Prim.mkRef", &[1]),
            bind(
                3,
                IrExpr::Pap {
                    function: name("ST.Prim.Ref.swap"),
                    args: vec![var(2)],
                },
            ),
            call(4, "ST.Prim.Ref.get", &[2]),
            num(5, 19),
            bind(
                6,
                IrExpr::Ap {
                    x: 3,
                    args: vec![var(5)],
                },
            ),
            num(7, 23),
            bind(
                8,
                IrExpr::Ap {
                    x: 3,
                    args: vec![var(7)],
                },
            ),
            call(9, "ST.Prim.Ref.get", &[2]),
            call(10, "Nat.add", &[4, 6]),
            call(11, "Nat.add", &[8, 9]),
            call(12, "Nat.add", &[10, 11]),
        ],
        12,
    ));
    // Capturing a cell performs no swap. The two applications observe the
    // same cell: before=7, first old=7, second old=19, current=23.
    assert_nat_replay(&compiled, "56");
}

#[test]
fn owned_heap_payloads_outlive_replacement_and_keep_the_original_alias() {
    let compiled = prepare(&entry(
        vec![
            num(1, u64::MAX),
            call(2, "ST.Prim.mkRef", &[1]),
            num(3, 19),
            call(4, "ST.Prim.Ref.swap", &[2, 3]),
            call(5, "ST.Prim.Ref.get", &[2]),
            call(6, "Nat.add", &[1, 4]),
            call(7, "Nat.add", &[6, 5]),
        ],
        7,
    ));
    assert_nat_replay(&compiled, "36893488147419103249");
}

#[test]
fn reference_cells_compose_with_native_arrays_without_extern_stubs() {
    let compiled = prepare(&entry(
        vec![
            num(1, 4),
            call(2, "Array.emptyWithCapacity", &[1]),
            call(3, "ST.Prim.mkRef", &[2]),
            num(4, 42),
            call(5, "Array.push", &[2, 4]),
            call(6, "ST.Prim.Ref.set", &[3, 5]),
            call(7, "ST.Prim.Ref.get", &[3]),
            call(8, "Array.size", &[7]),
            call(9, "Array.size", &[2]),
            call(10, "Nat.add", &[8, 9]),
        ],
        10,
    ));
    assert_nat_replay(&compiled, "1");
}

#[test]
fn native_state_rejects_scalar_handles_instead_of_fabricating_results() {
    for operation in ["ST.Prim.Ref.get", "ST.Prim.Ref.set", "ST.Prim.Ref.swap"] {
        let args = if operation.ends_with("get") {
            vec![1]
        } else {
            vec![1, 2]
        };
        let compiled = prepare(&entry(
            vec![num(1, 19), num(2, 23), call(3, operation, &args)],
            3,
        ));
        let bytes =
            flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default())
                .unwrap();
        let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
        for program in [compiled.program.program(), &replay] {
            assert!(!matches!(
                execute(program, ExecutionLimits::default(), None),
                Outcome::Complete(VmExit::Returned(_))
            ));
        }
    }
}

#[test]
fn interrupted_state_runs_do_not_publish_results_or_contaminate_retries() {
    let compiled = prepare(&state_sequence());
    let mut stopped = false;
    let mut completed = false;
    // Exercise every short instruction prefix, including stops after writes.
    for max_steps in 0..64 {
        let result = compiled
            .execute(
                ExecutionLimits {
                    max_steps,
                    ..ExecutionLimits::default()
                },
                None,
            )
            .outcome;
        if let Outcome::Complete(VmExit::Returned(value)) = result {
            assert_eq!(nat_decimal(&value.value).as_deref(), Some("42"));
            completed = true;
        } else {
            stopped = true;
        }
        assert_nat_replay(&compiled, "42");
    }
    assert!(stopped && completed);
}

#[test]
fn local_state_preparation_is_bounded_and_does_not_mutate_input_ir() {
    let module = state_sequence();
    let before = module.clone();
    let mut limits = IrExecutionLimits::default();
    limits.ir.max_work = 0;
    let error = compile_module(&module, "LocalState.main", &[], limits).unwrap_err();
    assert!(error.is_resource());
    assert_eq!(module, before);
    assert_nat_replay(&prepare(&module), "42");
}

mod reference;
