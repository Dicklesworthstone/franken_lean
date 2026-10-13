//! FIR simplification is invisible to a program's answer (bead
//! `fln-golem-ordinary-loops-fbj6`): each FIR program here runs on Golem as
//! written and as `fir::optimize` rewrites it, through the engine's own
//! lowering, and the two must agree on the value or the panic.
//!
//! The matcher loop mirrors what ingress emits for
//! `def go : Nat → Nat → Nat | 0, acc => acc | n + 1, acc => go n (acc + n)`:
//! a matcher function taking its alternatives as closures, and recursion
//! through a closure over the function itself.
#![forbid(unsafe_code)]

use fln_comp::fir::{
    self, Binding, Block, BlockId, ClosureTypeDecl, ClosureTypeId, EffectClass, Function,
    FunctionId, IntrinsicDecl, IntrinsicId, Operation, Program, Terminator, ValidatedProgram,
    ValidationLimits, ValueId, ValueType,
};
use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as R, CodecLimits, ResultOwnership,
};
use fln_core::outcome::Outcome;
use fln_vm::interpreter::{self, ExecutionLimits, VmExit};

const fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
const fn b(n: u32) -> BlockId {
    BlockId::new(n)
}
const fn f(n: u32) -> FunctionId {
    FunctionId::new(n)
}
const NAT1: ClosureTypeId = ClosureTypeId::new(0);
const NAT2: ClosureTypeId = ClosureTypeId::new(1);
const ADD: IntrinsicId = IntrinsicId::new(0);
const MUL: IntrinsicId = IntrinsicId::new(1);
const PRED: IntrinsicId = IntrinsicId::new(2);

fn bind(id: u32, ty: ValueType, operation: Operation) -> Binding {
    Binding {
        id: v(id),
        ty,
        operation,
    }
}

fn block(id: u32, bindings: Vec<Binding>, terminator: Terminator) -> Block {
    Block {
        id: b(id),
        bindings,
        terminator,
    }
}

fn function(id: u32, parameters: Vec<ValueType>, blocks: Vec<Block>) -> Function {
    Function {
        id: f(id),
        parameter_ownership: vec![A::Borrowed; parameters.len()],
        parameters,
        result: ValueType::Nat,
        result_ownership: R::OwnedOrScalar,
        blocks,
    }
}

fn returning(value: u32) -> Terminator {
    Terminator::Return { value: v(value) }
}

fn intrinsic(id: IntrinsicId, args: &[u32]) -> Operation {
    Operation::Intrinsic {
        intrinsic: id,
        args: args.iter().copied().map(v).collect(),
    }
}

fn closure(closure_type: ClosureTypeId, target: u32, captures: &[u32]) -> Operation {
    Operation::Closure {
        closure_type,
        function: f(target),
        captures: captures.iter().copied().map(v).collect(),
        capture_ownership: vec![A::Borrowed; captures.len()],
    }
}

fn apply(target: u32, args: &[u32], result_ownership: R) -> Operation {
    Operation::Apply {
        closure: v(target),
        args: args.iter().copied().map(v).collect(),
        argument_ownership: vec![A::Borrowed; args.len()],
        result_ownership,
    }
}

fn call(target: u32, args: &[u32]) -> Operation {
    Operation::Call {
        function: f(target),
        args: args.iter().copied().map(v).collect(),
    }
}

fn nat_intrinsic(id: IntrinsicId, row: &str, arguments: usize) -> IntrinsicDecl {
    IntrinsicDecl {
        id,
        row: row.to_string(),
        arguments: vec![ValueType::Nat; arguments],
        argument_ownership: vec![A::Borrowed; arguments],
        result: ValueType::Nat,
        result_ownership: ResultOwnership::Owned,
        effect: EffectClass::Pure,
    }
}

fn closure_types() -> Vec<ClosureTypeDecl> {
    [NAT1, NAT2]
        .into_iter()
        .enumerate()
        .map(|(arity, id)| ClosureTypeDecl {
            id,
            parameters: vec![ValueType::Nat; arity + 1],
            parameter_ownership: vec![A::Borrowed; arity + 1],
            result: ValueType::Nat,
            result_ownership: R::OwnedOrScalar,
        })
        .collect()
}

fn program(functions: Vec<Function>) -> ValidatedProgram {
    let program = Program::new_with_closures(
        f(0),
        Vec::new(),
        Vec::new(),
        closure_types(),
        vec![
            nat_intrinsic(ADD, "extern:Nat.add", 2),
            nat_intrinsic(MUL, "extern:Nat.mul", 2),
            nat_intrinsic(PRED, "extern:Nat.pred", 1),
        ],
        functions,
    );
    fir::validate(program, ValidationLimits::default()).unwrap()
}

/// `go n 0` through a matcher with closure alternatives and a self-closure.
fn matcher_loop(n: u64) -> ValidatedProgram {
    let nat = ValueType::Nat;
    program(vec![
        function(
            0,
            Vec::new(),
            vec![block(
                0,
                vec![
                    bind(0, nat, Operation::Nat(n)),
                    bind(1, nat, Operation::Nat(0)),
                    bind(2, nat, call(1, &[0, 1])),
                ],
                returning(2),
            )],
        ),
        // go n acc: build the recursive closure and apply it.
        function(
            1,
            vec![nat, nat],
            vec![block(
                0,
                vec![
                    bind(2, ValueType::Closure(NAT2), closure(NAT2, 2, &[])),
                    bind(3, nat, apply(2, &[0, 1], R::OwnedOrScalar)),
                ],
                returning(3),
            )],
        ),
        // The body: alternatives as closures, dispatched by the matcher.
        function(
            2,
            vec![nat, nat],
            vec![block(
                0,
                vec![
                    bind(2, ValueType::Closure(NAT2), closure(NAT2, 2, &[])),
                    bind(3, ValueType::Closure(NAT1), closure(NAT1, 4, &[1])),
                    bind(4, ValueType::Closure(NAT1), closure(NAT1, 5, &[2, 1])),
                    bind(5, nat, call(3, &[0, 3, 4])),
                ],
                returning(5),
            )],
        ),
        // The matcher: zero goes to the first alternative, else the second.
        function(
            3,
            vec![nat, ValueType::Closure(NAT1), ValueType::Closure(NAT1)],
            vec![
                block(
                    0,
                    Vec::new(),
                    Terminator::BranchZero {
                        condition: v(0),
                        zero: b(1),
                        nonzero: b(2),
                    },
                ),
                block(
                    1,
                    vec![bind(3, nat, apply(1, &[0], R::OwnedOrScalar))],
                    returning(3),
                ),
                block(
                    2,
                    vec![bind(4, nat, apply(2, &[0], R::OwnedOrScalar))],
                    returning(4),
                ),
            ],
        ),
        // `| 0, acc => acc`
        function(4, vec![nat, nat], vec![block(0, Vec::new(), returning(0))]),
        // `| n + 1, acc => go n (acc + n)`, curried through the self-closure.
        function(
            5,
            vec![ValueType::Closure(NAT2), nat, nat],
            vec![block(
                0,
                vec![
                    bind(3, nat, intrinsic(PRED, &[2])),
                    bind(4, nat, intrinsic(PRED, &[2])),
                    bind(5, nat, intrinsic(ADD, &[1, 4])),
                    bind(6, ValueType::Closure(NAT1), apply(0, &[3], R::Owned)),
                    bind(7, nat, apply(6, &[5], R::OwnedOrScalar)),
                ],
                returning(7),
            )],
        ),
    ])
}

/// What the engine executes: plain lowering, then the canonical codec.
fn run(program: &ValidatedProgram) -> Result<VmExit, String> {
    let lowered = fir::lower_to_flbc(program).unwrap();
    let bytes = flbc::encode_canonical(&lowered, CodecLimits::default()).unwrap();
    let decoded = flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap();
    match interpreter::execute(&decoded, ExecutionLimits::default(), None) {
        Outcome::Complete(exit) => Ok(exit),
        other => Err(format!("execution stopped: {other:?}")),
    }
}

fn returned_nat(exit: &VmExit) -> Result<(usize, u64, u64), String> {
    match exit {
        VmExit::Returned(done) => {
            assert!(done.value.is_scalar(), "{done:?}");
            Ok((
                done.value.unbox(),
                done.usage.steps,
                done.usage.peak_stack_depth,
            ))
        }
        other => Err(format!("did not return: {other:?}")),
    }
}

fn optimized(program: &ValidatedProgram) -> ValidatedProgram {
    fir::optimize(program, ValidationLimits::default()).unwrap()
}

fn function_text(program: &ValidatedProgram, id: u32) -> String {
    let text = program.canonical_text();
    let start = text
        .find(&format!("function f{id} "))
        .expect("the function is printed");
    let end = text[start + 1..]
        .find("function f")
        .map_or(text.len(), |next| start + 1 + next);
    text[start..end].to_string()
}

#[test]
fn the_matcher_loop_answers_alike_and_runs_without_closures() -> Result<(), String> {
    for n in [0u64, 1, 2, 3, 1_000] {
        let written = matcher_loop(n);
        let simplified = optimized(&written);
        let (value, steps, _) = returned_nat(&run(&written)?)?;
        let (fast_value, fast_steps, fast_depth) = returned_nat(&run(&simplified)?)?;
        let expected = (0..n).sum::<u64>();
        assert_eq!(value as u64, expected, "n = {n} as written");
        assert_eq!(fast_value, value, "n = {n}");
        assert!(
            fast_steps < steps || n == 0,
            "n = {n}: {fast_steps} vs {steps}"
        );
        assert_eq!(fast_depth, 1, "n = {n}: the loop is a direct tail call");
        if n == 1_000 {
            // As written: eleven instructions per step, three of them closure
            // allocations. Simplified: test, both preds, add, tail call; the
            // repeated pred is the program's own work and still runs.
            assert!(steps > 10 * 1_000, "{steps}");
            assert!(fast_steps < 5 * 1_000 + 20, "{fast_steps}");
        }
    }
    let body = function_text(&optimized(&matcher_loop(5)), 2);
    assert!(!body.contains("closure"), "{body}");
    assert!(!body.contains("apply"), "{body}");
    assert!(
        body.contains("call f2"),
        "the recursion is a direct call: {body}"
    );
    Ok(())
}

/// Mutual recursion stays two calls: absorbing either would unroll the cycle.
#[test]
fn recursive_functions_are_called_not_absorbed() -> Result<(), String> {
    let nat = ValueType::Nat;
    let parity = |id: u32, base: u64, other: u32| {
        function(
            id,
            vec![nat],
            vec![
                block(
                    0,
                    Vec::new(),
                    Terminator::BranchZero {
                        condition: v(0),
                        zero: b(1),
                        nonzero: b(2),
                    },
                ),
                block(1, vec![bind(1, nat, Operation::Nat(base))], returning(1)),
                block(
                    2,
                    vec![
                        bind(2, nat, intrinsic(PRED, &[0])),
                        bind(3, nat, call(other, &[2])),
                    ],
                    returning(3),
                ),
            ],
        )
    };
    for n in [0u64, 7, 10_000] {
        let written = program(vec![
            function(
                0,
                Vec::new(),
                vec![block(
                    0,
                    vec![bind(0, nat, Operation::Nat(n)), bind(1, nat, call(1, &[0]))],
                    returning(1),
                )],
            ),
            parity(1, 1, 2),
            parity(2, 0, 1),
        ]);
        let simplified = optimized(&written);
        for id in [1, 2] {
            assert_eq!(
                function_text(&simplified, id),
                function_text(&written, id),
                "f{id} is part of a cycle"
            );
        }
        let (value, _, _) = returned_nat(&run(&written)?)?;
        let (fast_value, _, _) = returned_nat(&run(&simplified)?)?;
        assert_eq!(value, usize::from(n % 2 == 0));
        assert_eq!(fast_value, value);
    }
    Ok(())
}

/// Unread work still runs: a call, so its panic still surfaces, and every
/// intrinsic, so the engine's evaluation counts still see it.
#[test]
fn unread_calls_and_intrinsics_still_run() -> Result<(), String> {
    let nat = ValueType::Nat;
    let written = program(vec![
        function(
            0,
            Vec::new(),
            vec![block(
                0,
                vec![
                    bind(0, nat, Operation::Nat(4)),
                    bind(1, nat, intrinsic(ADD, &[0, 0])),
                    bind(2, nat, intrinsic(MUL, &[0, 0])),
                    bind(3, nat, call(1, &[0])),
                    bind(4, nat, intrinsic(PRED, &[0])),
                ],
                returning(4),
            )],
        ),
        function(
            1,
            vec![nat],
            vec![block(
                0,
                vec![bind(1, ValueType::String, Operation::String("boom".into()))],
                Terminator::Panic { message: v(1) },
            )],
        ),
    ]);
    let simplified = optimized(&written);
    let entry = function_text(&simplified, 0);
    assert_eq!(entry, function_text(&written, 0));
    assert!(entry.contains("call f1"), "{entry}");
    for intrinsic in [ADD, MUL, PRED] {
        let needle = format!("intrinsic i{} ", intrinsic.get());
        assert!(entry.contains(&needle), "{entry}");
    }
    for exit in [run(&written)?, run(&simplified)?] {
        assert!(
            matches!(&exit, VmExit::Panicked { message, .. } if message.contains("boom")),
            "{exit:?}"
        );
    }
    Ok(())
}

/// A function that consumes an operand keeps its program as written: one
/// value may not stand for two once either can be moved.
#[test]
fn a_function_that_consumes_an_operand_is_left_as_written() -> Result<(), String> {
    let nat = ValueType::Nat;
    let mut consuming = function(
        1,
        vec![nat, nat],
        vec![block(
            0,
            vec![
                bind(2, ValueType::Closure(NAT1), closure(NAT1, 2, &[0])),
                bind(3, nat, apply(2, &[1], R::OwnedOrScalar)),
            ],
            returning(3),
        )],
    );
    consuming.parameter_ownership = vec![A::Owned, A::Borrowed];
    let written = program(vec![
        function(
            0,
            Vec::new(),
            vec![block(
                0,
                vec![
                    bind(0, nat, Operation::Nat(40)),
                    bind(1, nat, Operation::Nat(2)),
                    bind(2, nat, call(1, &[0, 1])),
                ],
                returning(2),
            )],
        ),
        consuming,
        function(
            2,
            vec![nat, nat],
            vec![block(
                0,
                vec![bind(2, nat, intrinsic(ADD, &[0, 1]))],
                returning(2),
            )],
        ),
    ]);
    let simplified = optimized(&written);
    assert_eq!(function_text(&simplified, 0), function_text(&written, 0));
    assert_eq!(function_text(&simplified, 1), function_text(&written, 1));
    let (value, _, _) = returned_nat(&run(&written)?)?;
    let (fast_value, _, _) = returned_nat(&run(&simplified)?)?;
    assert_eq!((value, fast_value), (42, 42));
    Ok(())
}

/// A tail callee with several blocks continues the caller's block with its
/// entry; its other blocks follow, and their edges to one another are
/// renumbered with them.
#[test]
fn a_multi_block_tail_callee_keeps_its_internal_edges() -> Result<(), String> {
    let nat = ValueType::Nat;
    let branching = function(
        1,
        vec![nat, nat],
        vec![
            block(
                0,
                Vec::new(),
                Terminator::BranchZero {
                    condition: v(0),
                    zero: b(1),
                    nonzero: b(2),
                },
            ),
            block(1, Vec::new(), returning(1)),
            block(
                2,
                vec![bind(2, nat, intrinsic(ADD, &[0, 1]))],
                Terminator::Jump { target: b(3) },
            ),
            block(3, Vec::new(), returning(0)),
        ],
    );
    for (condition, expected) in [(0u64, 5usize), (3, 3)] {
        let written = program(vec![
            function(
                0,
                Vec::new(),
                vec![block(
                    0,
                    vec![
                        bind(0, nat, Operation::Nat(condition)),
                        bind(1, nat, Operation::Nat(5)),
                        bind(2, nat, call(1, &[0, 1])),
                    ],
                    returning(2),
                )],
            ),
            branching.clone(),
        ]);
        let simplified = optimized(&written);
        let entry = function_text(&simplified, 0);
        assert!(!entry.contains("call f1"), "{entry}");
        assert!(entry.contains("jump b3"), "{entry}");
        let (value, _, _) = returned_nat(&run(&written)?)?;
        let (fast_value, _, fast_depth) = returned_nat(&run(&simplified)?)?;
        assert_eq!((value, fast_value, fast_depth), (expected, expected, 1));
    }
    Ok(())
}

/// A recursive call followed by unread pure work, the shape ingress leaves
/// after every structural `succ` case, runs that work first and then calls in
/// tail position: the same value and the same instructions, in one frame.
#[test]
fn a_returned_call_moves_after_trailing_pure_work() -> Result<(), String> {
    let nat = ValueType::Nat;
    let countdown = function(
        1,
        vec![nat],
        vec![
            block(
                0,
                Vec::new(),
                Terminator::BranchZero {
                    condition: v(0),
                    zero: b(1),
                    nonzero: b(2),
                },
            ),
            block(1, Vec::new(), returning(0)),
            block(
                2,
                vec![
                    bind(1, nat, intrinsic(PRED, &[0])),
                    bind(2, nat, call(1, &[1])),
                    bind(3, nat, Operation::Nat(1)),
                    bind(4, nat, intrinsic(ADD, &[1, 3])),
                ],
                returning(2),
            ),
        ],
    );
    for n in [0u64, 1, 500] {
        let written = program(vec![
            function(
                0,
                Vec::new(),
                vec![block(
                    0,
                    vec![bind(0, nat, Operation::Nat(n)), bind(1, nat, call(1, &[0]))],
                    returning(1),
                )],
            ),
            countdown.clone(),
        ]);
        let simplified = optimized(&written);
        let (value, steps, depth) = returned_nat(&run(&written)?)?;
        let (fast_value, fast_steps, fast_depth) = returned_nat(&run(&simplified)?)?;
        assert_eq!((value, fast_value), (0, 0), "n = {n}");
        // Every instruction still runs except each level's own `Return`,
        // which a tail call does not execute.
        assert_eq!(
            fast_steps + n,
            steps,
            "n = {n}: the trailing work still runs"
        );
        assert_eq!(depth, n + 1, "n = {n}: as written, one frame per step");
        assert_eq!(fast_depth, 1, "n = {n}: simplified, a tail call");
    }
    Ok(())
}

/// Only work that runs no code moves: an unread call after the returned one
/// keeps its place, so of two panics the first one written still surfaces.
#[test]
fn a_trailing_call_keeps_its_place_after_the_returned_call() -> Result<(), String> {
    let nat = ValueType::Nat;
    let panicking = |id: u32, message: &str| {
        function(
            id,
            vec![nat],
            vec![block(
                0,
                vec![bind(
                    1,
                    ValueType::String,
                    Operation::String(message.into()),
                )],
                Terminator::Panic { message: v(1) },
            )],
        )
    };
    let written = program(vec![
        function(
            0,
            Vec::new(),
            vec![block(
                0,
                vec![
                    bind(0, nat, Operation::Nat(1)),
                    bind(1, nat, call(1, &[0])),
                    bind(2, nat, call(2, &[0])),
                ],
                returning(1),
            )],
        ),
        panicking(1, "first"),
        panicking(2, "second"),
    ]);
    let simplified = optimized(&written);
    for exit in [run(&written)?, run(&simplified)?] {
        assert!(
            matches!(&exit, VmExit::Panicked { message, .. } if message.contains("first")),
            "{exit:?}"
        );
    }
    Ok(())
}
