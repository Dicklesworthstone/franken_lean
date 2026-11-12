//! Name equality through the generated ABI, ownership insertion and canonical
//! FLBC replay. These calls exercise the public VM entrypoint with real objects.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as C, Function, FunctionId,
    Instruction as I, Program, Register, ResultOwnership as R, ValidatedProgram,
};
use fln_core::diag::ResourceReason;
use fln_core::lean_hash::mix_hash;
use fln_core::name::Name;
use fln_core::outcome::{InconclusiveCause, Outcome};
use fln_rt::convert::inject_name;
use fln_rt::obj::{Obj, shadow};
use fln_vm::extern_row::{ArgumentOwnership, Ownership, ResultOwnership};
use fln_vm::extern_table_generated::EXTERN_ROWS;
use fln_vm::interpreter::{ExecutionLimits, VmExit, VmRefusal, execute_function, nat_decimal};
use std::sync::Mutex;

static TEST_LOCK: Mutex<()> = Mutex::new(());

fn r(index: u16) -> Register {
    Register::new(index)
}

fn programs() -> [ValidatedProgram; 2] {
    let row = EXTERN_ROWS
        .iter()
        .find(|row| row.id == "extern:Lean.Name.beq")
        .unwrap();
    let contract = Ownership::parse(row.ownership).unwrap();
    assert_eq!(
        contract.argument_ownership(2).unwrap(),
        [ArgumentOwnership::Borrowed; 2]
    );
    assert_eq!(
        contract.result_ownership().unwrap(),
        ResultOwnership::Scalar
    );
    let source = flbc::validate(Program::new(
        FunctionId::new(0),
        vec![
            Function {
                id: FunctionId::new(0),
                arity: 0,
                parameter_ownership: Vec::new(),
                result_ownership: C::Scalar,
                register_count: 1,
                code: vec![
                    I::Nat {
                        dst: r(0),
                        value: 0,
                    },
                    I::Return { src: r(0) },
                ],
            },
            Function {
                id: FunctionId::new(1),
                arity: 2,
                parameter_ownership: vec![A::Owned; 2],
                result_ownership: C::Scalar,
                register_count: 3,
                code: vec![
                    I::Intrinsic {
                        dst: r(2),
                        row: row.id.to_owned(),
                        args: vec![r(0), r(1)],
                        argument_ownership: vec![A::Borrowed; 2],
                        result_ownership: R::Scalar,
                    },
                    I::Return { src: r(2) },
                ],
            },
        ],
    ))
    .unwrap();
    let owned = flbc::insert_ownership(&source, flbc::OwnershipLimits::default()).unwrap();
    flbc::validate_ownership_candidate(
        &source,
        owned.program().clone(),
        owned.witness().clone(),
        flbc::OwnershipLimits::default(),
    )
    .unwrap();
    let bytes = flbc::encode_canonical(owned.program(), flbc::CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&replay, flbc::CodecLimits::default()).unwrap(),
        bytes
    );
    [owned.into_program(), replay]
}

fn assert_equal(program: &ValidatedProgram, left: &Obj, right: &Obj, expected: bool) {
    let outcome = execute_function(
        program,
        FunctionId::new(1),
        vec![left.clone_ref(), right.clone_ref()],
        ExecutionLimits::default(),
        None,
    );
    let Outcome::Complete(VmExit::Returned(result)) = outcome else {
        panic!("{outcome:?}");
    };
    assert_eq!(
        nat_decimal(&result.value).as_deref(),
        Some(if expected { "1" } else { "0" })
    );
    assert!(result.value.is_scalar());
}

fn assert_refused(program: &ValidatedProgram, left: &Obj, right: &Obj) {
    assert!(matches!(
        execute_function(
            program,
            FunctionId::new(1),
            vec![left.clone_ref(), right.clone_ref()],
            ExecutionLimits::default(),
            None
        ),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::InvalidCtorObject,
            ..
        })
    ));
}

fn clean_shadow() {
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "Name comparison/refusal retained an owned object");
    assert!(events.iter().all(|event| !matches!(
        event.kind,
        shadow::EventKind::DoubleRelease | shadow::EventKind::ForeignPointer
    )));
}

#[test]
fn name_equality_preserves_structure_unicode_and_borrowed_inputs() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    {
        let mut names = vec![
            Name::anonymous(),
            Name::str(Name::anonymous(), ""),
            Name::str(Name::anonymous(), "A.B"),
            Name::from_components(["A", "B"]),
            Name::str(Name::anonymous(), "λ\0🙂"),
            Name::str(Name::anonymous(), "λ\0🙃"),
            Name::str(Name::anonymous(), "é"),
            Name::str(Name::anonymous(), "e\u{301}"),
            Name::num(Name::anonymous(), 0),
            Name::str(Name::anonymous(), "0"),
            Name::num(Name::from_components(["_hyg", "a"]), u64::MAX),
        ];
        let mut deep = Name::anonymous();
        for _ in 0..400 {
            deep = Name::str(deep, "part");
        }
        names.push(deep);
        for program in programs() {
            for left in &names {
                let first = inject_name(left);
                for right in &names {
                    let second = inject_name(right);
                    assert_equal(&program, &first, &second, left == right);
                }
                assert_equal(&program, &first, &first, true);
            }
            let scalar_zero = Obj::mk_nat(0);
            let heap_zero = Obj::mk_ctor(0, Vec::new(), &[]);
            assert_equal(&program, &scalar_zero, &heap_zero, true);
            let inline = Obj::mk_ctor(2, vec![Obj::mk_nat(0)], &u64::MAX.to_ne_bytes());
            assert_equal(
                &program,
                &inline,
                &inject_name(&Name::num(Name::anonymous(), u64::MAX)),
                true,
            );
        }
    }
    clean_shadow();
}

fn numeric(limbs: &[u64]) -> Obj {
    let component_hash = match limbs {
        [] => 0,
        [value] => *value,
        _ => 17,
    };
    Obj::mk_ctor(
        2,
        vec![Obj::mk_nat(0), Obj::mk_mpz(limbs, false)],
        &mix_hash(1723, component_hash).to_ne_bytes(),
    )
}

#[test]
fn colliding_big_natural_hashes_still_compare_every_limb() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    {
        for program in programs() {
            let a = numeric(&[7, 1]);
            let equal = numeric(&[7, 1]);
            let high = numeric(&[7, 2]);
            let low = numeric(&[8, 1]);
            let longer = numeric(&[7, 1, 1]);
            assert_equal(&program, &a, &equal, true);
            assert_equal(&program, &a, &a, true);
            for different in [high, low, longer, numeric(&[17])] {
                assert_equal(&program, &a, &different, false);
                assert_equal(&program, &different, &a, false);
            }
            assert_equal(
                &program,
                &numeric(&[1]),
                &inject_name(&Name::num(Name::anonymous(), 1)),
                true,
            );
            assert_equal(
                &program,
                &numeric(&[]),
                &inject_name(&Name::num(Name::anonymous(), 0)),
                true,
            );
            let normalized =
                Obj::mk_ctor(2, vec![Obj::mk_nat(0), Obj::mk_mpz(&[1, 0], false)], &[]);
            assert_equal(&program, &normalized, &numeric(&[1]), true);
        }
    }
    clean_shadow();
}

#[test]
fn invalid_cached_hashes_layouts_and_naturals_refuse_even_aliases() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    {
        let valid = inject_name(&Name::str(Name::anonymous(), "valid"));
        let invalid = vec![
            Obj::mk_nat(1),
            Obj::mk_string("not a name"),
            Obj::mk_ctor(3, Vec::new(), &[]),
            Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &[]),
            Obj::mk_ctor(1, vec![Obj::mk_nat(0)], &[]),
            Obj::mk_ctor(1, vec![Obj::mk_nat(0), Obj::mk_nat(0)], &[]),
            Obj::mk_ctor(
                1,
                vec![Obj::mk_nat(0), Obj::mk_string("valid")],
                &0u64.to_ne_bytes(),
            ),
            Obj::mk_ctor(
                1,
                vec![Obj::mk_nat(0), Obj::mk_string("valid"), Obj::mk_nat(0)],
                &[],
            ),
            Obj::mk_ctor(2, vec![Obj::mk_nat(0), Obj::mk_mpz(&[1], true)], &[]),
            Obj::mk_ctor(2, vec![Obj::mk_nat(0), Obj::mk_string("1")], &[]),
        ];
        for program in programs() {
            for value in &invalid {
                assert_refused(&program, value, &valid);
                assert_refused(&program, &valid, value);
                assert_refused(&program, value, value);
            }
            assert_equal(&program, &valid, &valid, true);
        }
    }
    clean_shadow();
}

#[test]
fn name_equality_resource_stops_are_inconclusive_and_do_not_poison_replay() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    {
        let oversized = Obj::mk_ctor(
            1,
            vec![
                Obj::mk_nat(0),
                Obj::mk_string(&"x".repeat(16 * 1024 * 1024)),
            ],
            &[],
        );
        let valid = inject_name(&Name::str(Name::anonymous(), "retry"));
        for program in programs() {
            let outcome = execute_function(
                &program,
                FunctionId::new(1),
                vec![oversized.clone_ref(), oversized.clone_ref()],
                ExecutionLimits::default(),
                None,
            );
            let Outcome::Inconclusive(stop) = outcome else {
                panic!("{outcome:?}");
            };
            assert!(
                matches!(stop.cause, InconclusiveCause::ResourceExhausted { usage } if matches!(usage.reason, ResourceReason::Memory { .. }) && usage.observed > usage.allowed)
            );
            assert!(matches!(
                execute_function(
                    &program,
                    FunctionId::new(1),
                    vec![valid.clone_ref(), valid.clone_ref()],
                    ExecutionLimits {
                        max_steps: 0,
                        ..ExecutionLimits::default()
                    },
                    None
                ),
                Outcome::Inconclusive(_)
            ));
            assert!(matches!(
                execute_function(
                    &program,
                    FunctionId::new(1),
                    vec![valid.clone_ref(), valid.clone_ref()],
                    ExecutionLimits::default(),
                    Some(&|| true)
                ),
                Outcome::Inconclusive(_)
            ));
            assert_equal(&program, &valid, &valid, true);
        }
    }
    clean_shadow();
}
