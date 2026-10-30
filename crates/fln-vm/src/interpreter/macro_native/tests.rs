use super::super::{
    ArgumentOwnership, CallableResultOwnership, ExecutionLimits, Outcome, ResultOwnership, VmExit,
    execute_function, resolve_intrinsic_plan,
};
use super::*;
use fln_comp::flbc;

fn atom(text: &str) -> Obj {
    Obj::mk_ctor(
        layout::SYNTAX_ATOM.tag,
        vec![Obj::mk_nat(layout::SOURCE_NONE_TAG), Obj::mk_string(text)],
        &[],
    )
}

fn node(kind: Name, children: Vec<Obj>) -> Obj {
    Obj::mk_ctor(
        layout::SYNTAX_NODE.tag,
        vec![
            Obj::mk_nat(layout::SOURCE_NONE_TAG),
            inject_name(&kind),
            Obj::mk_array(children),
        ],
        &[],
    )
}

fn invoke(intrinsic: Intrinsic, args: &[Obj]) -> Obj {
    let id = match intrinsic {
        Intrinsic::MkStr1 => "mirror:Lean.Name.mkStr1",
        Intrinsic::IsOfKind => "mirror:Lean.Syntax.isOfKind",
        Intrinsic::GetArg => "mirror:Lean.Syntax.getArg",
        Intrinsic::GetNumArgs => "mirror:Lean.Syntax.getNumArgs",
    };
    match intrinsic.invoke(id, args) {
        Ok(value) => value.into_object(),
        Err(_) => panic!("native {id} refused a valid input"),
    }
}

#[test]
fn native_kinds_include_missing_ident_and_atom_pseudo_kinds() {
    let ident = Obj::mk_ctor(
        layout::SYNTAX_IDENT.tag,
        vec![
            Obj::mk_nat(layout::SOURCE_NONE_TAG),
            Obj::mk_ctor(
                layout::SUBSTRING_RAW.tag,
                vec![Obj::mk_string("x"), Obj::mk_nat(0), Obj::mk_nat(1)],
                &[],
            ),
            inject_name(&Name::str(Name::anonymous(), "x")),
            Obj::mk_nat(layout::LIST_NIL_TAG),
        ],
        &[],
    );
    for (value, kind) in [
        (Obj::mk_nat(layout::SYNTAX_MISSING_TAG), "missing"),
        (ident, "ident"),
        (atom("A.B\0🙂"), "A.B\0🙂"),
        (node(Name::str(Name::anonymous(), "k"), vec![]), "k"),
    ] {
        let actual = invoke(
            Intrinsic::IsOfKind,
            &[
                value.clone_ref(),
                inject_name(&Name::str(Name::anonymous(), kind)),
            ],
        );
        assert_eq!(actual.unbox(), 1);
        assert_eq!(
            invoke(
                Intrinsic::IsOfKind,
                &[value, inject_name(&Name::anonymous())]
            )
            .unbox(),
            0
        );
    }
    let single = invoke(Intrinsic::MkStr1, &[Obj::mk_string("A.B")]);
    assert_eq!(
        Conversion::new().project_name(&single).unwrap(),
        Name::str(Name::anonymous(), "A.B")
    );
    assert_ne!(
        Conversion::new().project_name(&single).unwrap(),
        Name::from_components(["A", "B"])
    );
}

#[test]
fn native_argument_reads_borrow_and_preserve_missing_fallback() {
    let child = atom("λ\0🙂");
    let syntax = node(Name::str(Name::anonymous(), "k"), vec![child.clone_ref()]);
    let original = child.identity_token();
    assert_eq!(
        invoke(Intrinsic::GetNumArgs, &[syntax.clone_ref()]).unbox(),
        1
    );
    assert_eq!(
        invoke(Intrinsic::GetArg, &[syntax.clone_ref(), Obj::mk_nat(0)]).identity_token(),
        original
    );
    for index in [Obj::mk_nat(1), Obj::mk_mpz(&[0, 1], false)] {
        assert_eq!(
            invoke(Intrinsic::GetArg, &[syntax.clone_ref(), index]).unbox(),
            layout::SYNTAX_MISSING_TAG
        );
    }
    assert_eq!(
        invoke(Intrinsic::GetArg, &[child.clone_ref(), Obj::mk_nat(0)]).unbox(),
        layout::SYNTAX_MISSING_TAG
    );
    assert_eq!(invoke(Intrinsic::GetNumArgs, &[child]).unbox(), 0);
    let malformed = Obj::mk_ctor(layout::SYNTAX_NODE.tag, vec![], &[]);
    assert!(matches!(
        Intrinsic::GetNumArgs.invoke("mirror:Lean.Syntax.getNumArgs", &[malformed]),
        Err(IntrinsicFailure::Refused(VmRefusal::InvalidCtorObject))
    ));
}

#[test]
fn generated_mirror_contract_rejects_forged_arity_and_ownership() {
    for row in crate::macro_native::ROWS {
        let args = row.argument_ownership();
        let result = row.result_ownership();
        assert!(resolve_intrinsic_plan(row.id, &args, result).is_ok());
        assert!(matches!(
            resolve_intrinsic_plan(row.id, &[], result),
            Err(VmRefusal::IntrinsicArity { .. })
        ));
        let mut wrong = args.clone();
        wrong[0] = if args[0] == ArgumentOwnership::Borrowed {
            ArgumentOwnership::Owned
        } else {
            ArgumentOwnership::Borrowed
        };
        assert!(matches!(
            resolve_intrinsic_plan(row.id, &wrong, result),
            Err(VmRefusal::IntrinsicOwnershipMismatch { .. })
        ));
        assert!(matches!(
            resolve_intrinsic_plan(row.id, &args, ResultOwnership::Borrowed),
            Err(VmRefusal::IntrinsicResultOwnershipMismatch { .. })
        ));
    }
    assert!(matches!(
        resolve_intrinsic_plan(
            "mirror:Lean.Syntax.unimplemented",
            &[],
            ResultOwnership::RawObject
        ),
        Err(VmRefusal::UnknownIntrinsic { .. })
    ));
}

#[test]
fn callable_inputs_preserve_handles_and_replay_and_refuse_bad_entry_contracts() {
    let r = flbc::Register::new;
    let f = flbc::FunctionId::new;
    let source = flbc::Program::new(
        f(0),
        vec![
            flbc::Function {
                id: f(0),
                arity: 0,
                parameter_ownership: vec![],
                result_ownership: CallableResultOwnership::Scalar,
                register_count: 1,
                code: vec![
                    flbc::Instruction::Nat {
                        dst: r(0),
                        value: 99,
                    },
                    flbc::Instruction::Return { src: r(0) },
                ],
            },
            flbc::Function {
                id: f(1),
                arity: 1,
                parameter_ownership: vec![ArgumentOwnership::Borrowed],
                result_ownership: CallableResultOwnership::Erased,
                register_count: 1,
                code: vec![flbc::Instruction::Return { src: r(0) }],
            },
        ],
    );
    let checked = flbc::validate(source).unwrap();
    let checked = flbc::insert_ownership(&checked, flbc::OwnershipLimits::default()).unwrap();
    let bytes = flbc::encode_canonical(checked.program(), flbc::CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    for program in [checked.program(), &replay] {
        let value = atom("actual argument");
        let identity = value.identity_token();
        let answer = execute_function(program, f(1), vec![value], ExecutionLimits::default(), None);
        let Outcome::Complete(VmExit::Returned(value)) = answer else {
            panic!("{answer:?}")
        };
        assert_eq!(value.value.identity_token(), identity);
        for (function, arguments) in [(f(1), vec![]), (f(99), vec![Obj::mk_nat(0)])] {
            assert!(matches!(
                execute_function(
                    program,
                    function,
                    arguments,
                    ExecutionLimits::default(),
                    None
                ),
                Outcome::Complete(VmExit::Refused {
                    refusal: VmRefusal::CallableEntry { .. },
                    ..
                })
            ));
        }
        assert!(matches!(
            execute_function(
                program,
                f(1),
                vec![Obj::mk_nat(0)],
                ExecutionLimits {
                    max_steps: 0,
                    ..ExecutionLimits::default()
                },
                None
            ),
            Outcome::Inconclusive(_)
        ));
    }
}
