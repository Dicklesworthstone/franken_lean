use super::*;
use crate::interpreter::{IntrinsicImplementation, invoke_intrinsic};

const OF_ELEMS_ROW: &str = "mirror:Lean.Syntax.SepArray.ofElems";
const PUSH_ROW: &str = "mirror:Lean.Syntax.TSepArray.push._redArg";

fn owned_push(separator: &str, array: Obj, element: Obj) -> Obj {
    invoke_intrinsic(
        IntrinsicImplementation::MacroNative(Intrinsic::TSepArrayPush),
        PUSH_ROW,
        vec![Obj::mk_string(separator), array, element],
        ExecutionLimits::default().max_nat_magnitude_bytes,
    )
    .unwrap_or_else(|_| panic!("valid owned separated-array push"))
    .into_object()
}

fn assert_atom(value: &Obj, expected: &str) {
    check_layout(value, layout::SYNTAX_ATOM).unwrap();
    assert_eq!(child(value, 0).unwrap().unbox(), layout::SOURCE_NONE_TAG);
    assert_eq!(string(&child(value, 1).unwrap()).unwrap(), expected);
}

#[test]
fn of_elements_preserves_syntax_and_distinguishes_empty_separators() {
    let info = Obj::mk_ctor(
        layout::SOURCE_SYNTHETIC.tag,
        vec![Obj::mk_nat(2), Obj::mk_nat(9)],
        &[1],
    );
    let scoped_name = Name::num(Name::from_components(["item", "_@", "Main", "_hyg"]), 19);
    let scoped = invoke(Intrinsic::MkIdent, &[inject_name(&scoped_name)]);
    let marked = invoke(Intrinsic::SetInfo, &[info.clone_ref(), scoped]);
    let values = [marked, atom("λ\0"), Obj::mk_nat(layout::SYNTAX_MISSING_TAG)];
    for delimiter in ["", ",", "λ\0🙂"] {
        let text = Obj::mk_string(delimiter);
        for size in 0..=values.len() {
            let input = Obj::mk_array(values[..size].iter().map(Obj::clone_ref).collect());
            let output = invoke(
                Intrinsic::SepArrayOfElems,
                &[text.clone_ref(), input.clone_ref()],
            );
            assert_eq!(
                output.array_view().0,
                size.saturating_mul(2).saturating_sub(1)
            );
            assert_eq!(input.array_view().0, size);
            for (index, value) in values[..size].iter().enumerate() {
                assert_eq!(
                    output.array_child(index * 2).identity_token(),
                    value.identity_token()
                );
                assert_eq!(
                    input.array_child(index).identity_token(),
                    value.identity_token()
                );
                if index == 0 {
                    continue;
                }
                let separator = output.array_child(index * 2 - 1);
                if delimiter.is_empty() {
                    check_layout(&separator, layout::SYNTAX_NODE).unwrap();
                    assert_eq!(
                        child(&separator, 0).unwrap().unbox(),
                        layout::SOURCE_NONE_TAG
                    );
                    assert_eq!(
                        Conversion::new()
                            .project_name(&child(&separator, 1).unwrap())
                            .unwrap(),
                        Name::from_components(["null"])
                    );
                    assert_eq!(child(&separator, 2).unwrap().array_view().0, 0);
                } else {
                    assert_atom(&separator, delimiter);
                    assert_eq!(
                        child(&separator, 1).unwrap().identity_token(),
                        text.identity_token()
                    );
                }
                assert_eq!(
                    separator.identity_token(),
                    output.array_child(1).identity_token()
                );
            }
        }
    }
    // Sharing the complete syntax carrier also preserves its source and
    // hygienic name, including the identifier's remaining fields.
    assert_eq!(
        child(&values[0], 0).unwrap().identity_token(),
        info.identity_token()
    );
    assert_eq!(
        Conversion::new()
            .project_name(&child(&values[0], 2).unwrap())
            .unwrap(),
        scoped_name
    );
}

#[test]
fn typed_push_keeps_empty_odd_and_even_inputs_and_uses_atoms_for_empty_separators() {
    let values = [
        atom("first"),
        atom("old separator"),
        atom("last"),
        atom("trailing"),
    ];
    let appended = atom("tail");
    for delimiter in ["", ","] {
        for size in 0..=values.len() {
            let input = Obj::mk_array(values[..size].iter().map(Obj::clone_ref).collect());
            let output = owned_push(delimiter, input.clone_ref(), appended.clone_ref());
            let output_size = size + if size == 0 { 1 } else { 2 };
            assert_eq!(output.array_view().0, output_size);
            assert_eq!(input.array_view().0, size);
            for (index, value) in values[..size].iter().enumerate() {
                assert_eq!(
                    output.array_child(index).identity_token(),
                    value.identity_token()
                );
                assert_eq!(
                    input.array_child(index).identity_token(),
                    value.identity_token()
                );
            }
            assert_eq!(
                output.array_child(output_size - 1).identity_token(),
                appended.identity_token()
            );
            if size != 0 {
                assert_atom(&output.array_child(size), delimiter);
                if size.is_multiple_of(2) {
                    // A trailing separator is not repaired: the new separator
                    // itself occupies an even position in a malformed sequence.
                    let elements = invoke(Intrinsic::TSepArrayGetElems, &[output.clone_ref()]);
                    assert_eq!(
                        elements.array_child(size / 2).identity_token(),
                        output.array_child(size).identity_token()
                    );
                }
            }
        }
    }
}

#[test]
fn owned_sequence_push_reuses_capacity_and_isolates_retained_aliases() {
    let element = atom("item");
    let mut array = Obj::mk_array(Vec::new());
    let mut growths = 0;
    for _ in 0..256 {
        let identity = array.identity_token();
        let (size, capacity) = array.array_view();
        let required = size + if size == 0 { 1 } else { 2 };
        array = owned_push(",", array, element.clone_ref());
        assert_eq!(array.array_view().0, required);
        if capacity >= required {
            assert_eq!(
                array.identity_token(),
                identity,
                "owned dispatch must retain the unique array's spare capacity"
            );
        } else {
            growths += 1;
        }
    }
    assert!(
        growths <= 16,
        "a growing sequence must amortize allocation: {growths}"
    );
    let snapshot = array.clone_ref();
    let old_size = snapshot.array_view().0;
    let tail = atom("new tail");
    let array = owned_push("", array, tail.clone_ref());
    assert_ne!(array.identity_token(), snapshot.identity_token());
    assert_eq!(snapshot.array_view().0, old_size);
    assert_eq!(
        snapshot.array_child(old_size - 1).identity_token(),
        element.identity_token()
    );
    assert_eq!(array.array_view().0, old_size + 2);
    assert_atom(&array.array_child(old_size), "");
    assert_eq!(
        array.array_child(old_size + 1).identity_token(),
        tail.identity_token()
    );
}

#[test]
fn sequence_constructors_refuse_malformed_arguments_before_mutating_shared_inputs() {
    let input = Obj::mk_array(vec![atom("unchanged")]);
    for (intrinsic, row, args) in [
        (
            Intrinsic::SepArrayOfElems,
            OF_ELEMS_ROW,
            vec![Obj::mk_nat(0), input.clone_ref()],
        ),
        (
            Intrinsic::SepArrayOfElems,
            OF_ELEMS_ROW,
            vec![Obj::mk_string(","), Obj::mk_nat(0)],
        ),
        (
            Intrinsic::SepArrayOfElems,
            OF_ELEMS_ROW,
            vec![Obj::mk_string(","), Obj::mk_array(vec![Obj::mk_nat(99)])],
        ),
        (
            Intrinsic::TSepArrayPush,
            PUSH_ROW,
            vec![Obj::mk_nat(0), input.clone_ref(), atom("tail")],
        ),
        (
            Intrinsic::TSepArrayPush,
            PUSH_ROW,
            vec![
                Obj::mk_string(","),
                Obj::mk_string("not an array"),
                atom("tail"),
            ],
        ),
        (
            Intrinsic::TSepArrayPush,
            PUSH_ROW,
            vec![Obj::mk_string(","), input.clone_ref(), Obj::mk_nat(99)],
        ),
        (
            Intrinsic::TSepArrayPush,
            PUSH_ROW,
            vec![
                Obj::mk_string(","),
                input.clone_ref(),
                Obj::mk_ctor(layout::SYNTAX_NODE.tag, vec![Obj::mk_nat(0)], &[]),
            ],
        ),
    ] {
        assert!(
            matches!(
                invoke_intrinsic(
                    IntrinsicImplementation::MacroNative(intrinsic),
                    row,
                    args,
                    ExecutionLimits::default().max_nat_magnitude_bytes,
                ),
                Err(IntrinsicFailure::Refused(_))
            ),
            "{row}"
        );
        assert_eq!(input.array_view().0, 1);
        assert_atom(&input.array_child(0), "unchanged");
    }
    assert!(matches!(
        invoke_intrinsic(
            IntrinsicImplementation::MacroNative(Intrinsic::TSepArrayPush),
            PUSH_ROW,
            vec![Obj::mk_string(","), input.clone_ref()],
            ExecutionLimits::default().max_nat_magnitude_bytes,
        ),
        Err(IntrinsicFailure::Refused(VmRefusal::IntrinsicArity {
            expected: 3,
            actual: 2,
            ..
        }))
    ));
    assert_eq!(owned_push(",", input, atom("recovered")).array_view().0, 3);
}

fn small_arguments(intrinsic: Intrinsic, first: &Obj, last: &Obj, delimiter: &str) -> Vec<Obj> {
    match intrinsic {
        Intrinsic::SepArrayOfElems => vec![
            Obj::mk_string(delimiter),
            Obj::mk_array(vec![first.clone_ref(), last.clone_ref()]),
        ],
        Intrinsic::TSepArrayPush => vec![
            Obj::mk_string(delimiter),
            Obj::mk_array(vec![first.clone_ref()]),
            last.clone_ref(),
        ],
        _ => unreachable!("only sequence construction rows"),
    }
}

#[test]
fn sequence_output_caps_are_inconclusive_and_do_not_poison_recovery() {
    for (intrinsic, row, size) in [
        (
            Intrinsic::SepArrayOfElems,
            OF_ELEMS_ROW,
            MAX_SYNTAX_NODES as usize / 2 + 1,
        ),
        (
            Intrinsic::TSepArrayPush,
            PUSH_ROW,
            MAX_SYNTAX_NODES as usize - 1,
        ),
    ] {
        let input = Obj::mk_array(
            (0..size)
                .map(|_| Obj::mk_nat(layout::SYNTAX_MISSING_TAG))
                .collect(),
        );
        let mut args = vec![Obj::mk_string(","), input.clone_ref()];
        if intrinsic == Intrinsic::TSepArrayPush {
            args.push(atom("tail"));
        }
        assert!(matches!(
            invoke_intrinsic(
                IntrinsicImplementation::MacroNative(intrinsic), row,
                args.iter().map(Obj::clone_ref).collect(),
                ExecutionLimits::default().max_nat_magnitude_bytes,
            ),
            Err(IntrinsicFailure::MirrorResource { allowed: MAX_SYNTAX_NODES, observed, .. })
                if observed == MAX_SYNTAX_NODES + 1
        ));
        let program = lookup::callable_program(row);
        assert!(matches!(
            execute_function(
                &program,
                flbc::FunctionId::new(1),
                args,
                ExecutionLimits::default(),
                None
            ),
            Outcome::Inconclusive(_)
        ));
        assert_eq!(input.array_view().0, size);
        let outcome = execute_function(
            &program,
            flbc::FunctionId::new(1),
            small_arguments(intrinsic, &atom("first"), &atom("recovered"), ","),
            ExecutionLimits::default(),
            None,
        );
        let Outcome::Complete(VmExit::Returned(result)) = outcome else {
            panic!("{row}: {outcome:?}");
        };
        assert_eq!(result.value.array_view().0, 3);
        assert_atom(&result.value.array_child(2), "recovered");
    }
}

#[test]
fn sequence_construction_rows_execute_through_canonical_bytecode() {
    let first = atom("first");
    let last = atom("last");
    for (intrinsic, row) in [
        (Intrinsic::SepArrayOfElems, OF_ELEMS_ROW),
        (Intrinsic::TSepArrayPush, PUSH_ROW),
    ] {
        let program = lookup::callable_program(row);
        let bytes = flbc::encode_canonical(&program, flbc::CodecLimits::default()).unwrap();
        let decoded = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
        for delimiter in ["", ","] {
            for program in [&program, &decoded] {
                let outcome = execute_function(
                    program,
                    flbc::FunctionId::new(1),
                    small_arguments(intrinsic, &first, &last, delimiter),
                    ExecutionLimits::default(),
                    None,
                );
                let Outcome::Complete(VmExit::Returned(result)) = outcome else {
                    panic!("{row}: {outcome:?}");
                };
                assert_eq!(result.value.array_view().0, 3);
                assert_eq!(
                    result.value.array_child(0).identity_token(),
                    first.identity_token()
                );
                assert_eq!(
                    result.value.array_child(2).identity_token(),
                    last.identity_token()
                );
                let separator = result.value.array_child(1);
                if delimiter.is_empty() && intrinsic == Intrinsic::SepArrayOfElems {
                    check_layout(&separator, layout::SYNTAX_NODE).unwrap();
                    assert_eq!(child(&separator, 2).unwrap().array_view().0, 0);
                } else {
                    assert_atom(&separator, delimiter);
                }
            }
        }
    }
}

#[test]
fn cancelled_or_fuel_exhausted_sequence_calls_leave_inputs_reusable() {
    for (intrinsic, row) in [
        (Intrinsic::SepArrayOfElems, OF_ELEMS_ROW),
        (Intrinsic::TSepArrayPush, PUSH_ROW),
    ] {
        let program = lookup::callable_program(row);
        let first = atom("first");
        let last = atom("last");
        let args = small_arguments(intrinsic, &first, &last, ",");
        let input_size = args[1].array_view().0;
        for (limits, cancelled) in [
            (
                ExecutionLimits {
                    max_steps: 0,
                    ..ExecutionLimits::default()
                },
                false,
            ),
            (ExecutionLimits::default(), true),
        ] {
            let cancellation = || cancelled;
            assert!(matches!(
                execute_function(
                    &program,
                    flbc::FunctionId::new(1),
                    args.iter().map(Obj::clone_ref).collect(),
                    limits,
                    Some(&cancellation),
                ),
                Outcome::Inconclusive(_)
            ));
            assert_eq!(args[1].array_view().0, input_size);
        }
        let outcome = execute_function(
            &program,
            flbc::FunctionId::new(1),
            args,
            ExecutionLimits::default(),
            None,
        );
        let Outcome::Complete(VmExit::Returned(result)) = outcome else {
            panic!("{row}: {outcome:?}");
        };
        assert_eq!(result.value.array_view().0, 3);
        assert_eq!(
            result.value.array_child(0).identity_token(),
            first.identity_token()
        );
        assert_eq!(
            result.value.array_child(2).identity_token(),
            last.identity_token()
        );
    }
}
