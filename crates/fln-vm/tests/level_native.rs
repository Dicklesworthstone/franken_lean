//! Universe metaprogram primitives through public FLBC dispatch and replay.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership, CallableResultOwnership, CodecLimits, Function, FunctionId,
    Instruction, OwnershipLimits, Program, Register, ResultOwnership, ValidatedProgram,
};
use fln_core::level::{LMVarId, Level, MAX_LEVEL_DEPTH};
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_rt::convert::{Conversion, inject_level, inject_name};
use fln_rt::native_heap::NativeHeap;
use fln_rt::obj::Obj;
use fln_vm::interpreter::{ExecutionLimits, VmExit, VmRefusal, execute_function};

fn program(row: &str, arity: u16) -> ValidatedProgram {
    let (argument_ownership, result_ownership) = fln_vm::macro_native::row_for_id(row)
        .map(|row| (row.argument_ownership(), row.result_ownership()))
        .unwrap_or((
            vec![ArgumentOwnership::Borrowed; usize::from(arity)],
            ResultOwnership::Owned,
        ));
    let stub = Function {
        id: FunctionId::new(0),
        arity: 0,
        parameter_ownership: vec![],
        result_ownership: CallableResultOwnership::Scalar,
        register_count: 1,
        code: vec![
            Instruction::Nat {
                dst: Register::new(0),
                value: 0,
            },
            Instruction::Return {
                src: Register::new(0),
            },
        ],
    };
    let native = Function {
        id: FunctionId::new(1),
        arity,
        parameter_ownership: vec![ArgumentOwnership::Owned; usize::from(arity)],
        result_ownership: if row == "extern:Lean.Level.beq" {
            CallableResultOwnership::Scalar
        } else {
            CallableResultOwnership::Owned
        },
        register_count: arity + 1,
        code: vec![
            Instruction::Intrinsic {
                dst: Register::new(arity),
                row: row.to_owned(),
                args: (0..arity).map(Register::new).collect(),
                argument_ownership,
                result_ownership,
            },
            Instruction::Return {
                src: Register::new(arity),
            },
        ],
    };
    let original = flbc::validate(Program::new(FunctionId::new(0), vec![stub, native])).unwrap();
    let owned = flbc::insert_ownership(&original, OwnershipLimits::default()).unwrap();
    let bytes = flbc::encode_canonical(owned.program(), CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&replay, CodecLimits::default()).unwrap(),
        bytes
    );
    replay
}

fn execute(program: &ValidatedProgram, args: Vec<Obj>) -> Outcome<VmExit> {
    execute_function(
        program,
        FunctionId::new(1),
        args,
        ExecutionLimits::default(),
        None,
    )
}

fn returned(program: &ValidatedProgram, args: Vec<Obj>) -> Obj {
    match execute(program, args) {
        Outcome::Complete(VmExit::Returned(result)) => result.value,
        other => panic!("native level call did not return: {other:?}"),
    }
}

fn object(level: Level) -> Obj {
    let mut heap = NativeHeap::new();
    let handle = heap.alloc(level);
    inject_level(&heap, handle).unwrap()
}

fn data_args(hash: u64, depth: usize, has_mvar: bool, has_param: bool) -> Vec<Obj> {
    vec![
        Obj::mk_ctor(0, vec![], &hash.to_ne_bytes()),
        Obj::mk_nat(depth),
        Obj::mk_nat(usize::from(has_mvar)),
        Obj::mk_nat(usize::from(has_param)),
    ]
}

#[test]
fn structural_equality_covers_every_constructor_without_universe_normalization() {
    let program = program("extern:Lean.Level.beq", 2);
    let u = Level::param(Name::str(Name::anonymous(), "u"));
    let v = Level::param(Name::str(Name::anonymous(), "v"));
    let numeric = Name::num(Name::str(Name::anonymous(), "u"), u64::MAX);
    let levels = [
        Level::zero(),
        Level::one(),
        u.clone(),
        v.clone(),
        Level::mvar(LMVarId(Name::str(Name::anonymous(), "u"))),
        Level::param(numeric.clone()),
        Level::mvar(LMVarId(numeric)),
        Level::max(u.clone(), v.clone()).unwrap(),
        Level::max(v.clone(), u.clone()).unwrap(),
        Level::imax(u, v).unwrap(),
        Level::max(Level::zero(), Level::one()).unwrap(),
    ];
    for (left_index, left) in levels.iter().enumerate() {
        for (right_index, right) in levels.iter().enumerate() {
            let left_object = object(left.clone());
            let alias = left_object.clone_ref();
            let result = returned(&program, vec![left_object, object(right.clone())]);
            assert!(result.is_scalar());
            assert_eq!(result.unbox(), usize::from(left_index == right_index));
            // A borrowed comparison must leave a retained input usable.
            assert_eq!(
                returned(&program, vec![alias, object(left.clone())]).unbox(),
                1
            );
        }
    }
}

#[test]
fn shared_and_deep_level_graphs_compare_without_expanding_their_tree() {
    let program = program("extern:Lean.Level.beq", 2);
    let mut shared = Level::param(Name::from_components(["shared"]));
    for _ in 0..32 {
        shared = Level::max(shared.clone(), shared).unwrap();
    }
    assert_eq!(
        returned(&program, vec![object(shared.clone()), object(shared)]).unbox(),
        1
    );
    let mut deep = Level::zero();
    for _ in 0..1024 {
        deep = deep.succ().unwrap();
    }
    assert_eq!(
        returned(&program, vec![object(deep.clone()), object(deep)]).unbox(),
        1
    );
}

#[test]
fn data_packing_keeps_low_hash_bits_flags_and_the_complete_depth_field() {
    let program = program("extern:Lean.Level.mkData", 4);
    for hash in [0, 0xffff_ffff, 0xfedc_ba98_7654_3210, u64::MAX] {
        for depth in [0, 1, 65536, MAX_LEVEL_DEPTH as usize] {
            for (mvar, parameter) in [(false, false), (true, false), (false, true), (true, true)] {
                let result = returned(&program, data_args(hash, depth, mvar, parameter));
                let expected = (hash & 0xffff_ffff)
                    | (u64::from(mvar) << 32)
                    | (u64::from(parameter) << 33)
                    | ((depth as u64) << 40);
                assert_eq!(result.try_ctor_scalar_u64(0), Some(expected));
            }
        }
    }
}

#[test]
fn computed_constructor_helpers_produce_checked_data_without_normalizing() {
    let name = Name::num(Name::from_components(["Scope", "λ"]), u64::MAX);
    let u = Level::param(name.clone());
    let v = Level::mvar(LMVarId(name.clone()));
    for (row, args, expected) in [
        (
            "mirror:Lean.Level.param._override",
            vec![inject_name(&name)],
            u.clone(),
        ),
        (
            "mirror:Lean.Level.mvar._override",
            vec![inject_name(&name)],
            v.clone(),
        ),
        (
            "mirror:Lean.Level.succ._override",
            vec![object(Level::zero())],
            Level::one(),
        ),
        (
            "mirror:Lean.Level.max._override",
            vec![object(u.clone()), object(v.clone())],
            Level::max(u.clone(), v.clone()).unwrap(),
        ),
        (
            "mirror:Lean.Level.imax._override",
            vec![object(u.clone()), object(v.clone())],
            Level::imax(u.clone(), v).unwrap(),
        ),
    ] {
        let program = program(row, args.len() as u16);
        let value = returned(&program, args);
        let mut heap = NativeHeap::new();
        let handle = Conversion::new().project_level(&mut heap, &value).unwrap();
        assert_eq!(heap.get(handle).unwrap(), &expected, "{row}");
    }
    for (row, argument) in [
        ("mirror:Lean.Level.succ._override", Obj::mk_nat(1)),
        (
            "mirror:Lean.Level.param._override",
            Obj::mk_string("not a Name"),
        ),
    ] {
        assert!(matches!(
            execute(&program(row, 1), vec![argument]),
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::InvalidCtorObject,
                ..
            })
        ));
    }
}

#[test]
fn malformed_levels_and_invalid_scalar_operands_are_refused() {
    let compare = program("extern:Lean.Level.beq", 2);
    for malformed in [
        Obj::mk_nat(1),
        Obj::mk_string("not a universe"),
        Obj::mk_ctor(1, vec![], &[]),
        // The shape is succ zero, but its cached data word is forged.
        Obj::mk_ctor(1, vec![Obj::mk_nat(0)], &0_u64.to_ne_bytes()),
    ] {
        // Even equal pointers must cross validation before comparison.
        let alias = malformed.clone_ref();
        assert!(matches!(
            execute(&compare, vec![malformed, alias]),
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::InvalidCtorObject,
                ..
            })
        ));
    }
    let pack = program("extern:Lean.Level.mkData", 4);
    let mut args = data_args(0, 0, false, false);
    args[2] = Obj::mk_nat(2);
    assert!(matches!(
        execute(&pack, args),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::InvalidBoolScalar { argument: 2, .. },
            ..
        })
    ));
    let mut args = data_args(0, 0, false, false);
    args[0] = Obj::mk_nat(0);
    assert!(matches!(
        execute(&pack, args),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::TypeMismatch { argument: 0, .. },
            ..
        })
    ));
    assert!(matches!(
        execute(&program("extern:Lean.Level.beq", 1), vec![Obj::mk_nat(0)]),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::IntrinsicArity { .. },
            ..
        })
    ));
}

#[test]
fn depth_exhaustion_cancellation_and_step_limits_remain_nonanswers() {
    let pack = program("extern:Lean.Level.mkData", 4);
    for depth in [
        Obj::mk_nat(MAX_LEVEL_DEPTH as usize + 1),
        Obj::mk_mpz(&[0, 1], false),
    ] {
        let mut args = data_args(0, 0, false, false);
        args[1] = depth;
        assert!(matches!(execute(&pack, args), Outcome::Inconclusive(_)));
    }
    for cancel in [false, true] {
        assert!(matches!(
            execute_function(
                &pack,
                FunctionId::new(1),
                data_args(42, 0, false, false),
                ExecutionLimits {
                    max_steps: if cancel { 100 } else { 0 },
                    ..ExecutionLimits::default()
                },
                cancel.then_some(&|| true),
            ),
            Outcome::Inconclusive(_)
        ));
    }
    assert_eq!(
        returned(&pack, data_args(42, 0, false, false)).try_ctor_scalar_u64(0),
        Some(42)
    );
}
