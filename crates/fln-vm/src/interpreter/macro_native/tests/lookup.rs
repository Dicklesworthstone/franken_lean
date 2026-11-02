use super::*;
use crate::macro_native::ResolvedGlobals;
use std::cell::Cell;

struct Lookup {
    namespace: Name,
    declaration: Name,
    calls: Cell<usize>,
}

impl MacroLookup for Lookup {
    fn current_namespace(&self) -> &Name {
        self.calls.set(self.calls.get() + 1);
        &self.namespace
    }

    fn has_decl(&self, declaration: &Name) -> bool {
        self.calls.set(self.calls.get() + 1);
        *declaration == self.declaration
    }
}

fn lookup(namespace: &str) -> Lookup {
    Lookup {
        namespace: Name::from_components(namespace.split('.')),
        declaration: Name::from_components(["Present", "decl"]),
        calls: Cell::new(0),
    }
}

fn context() -> Obj {
    Obj::mk_ctor(
        layout::MACRO_CONTEXT.tag,
        vec![
            Obj::mk_nat(0),
            inject_name(&Name::from_components(["Quotation", "Context"])),
            Obj::mk_nat(13),
            Obj::mk_nat(2),
            Obj::mk_nat(512),
            Obj::mk_nat(layout::SYNTAX_MISSING_TAG),
        ],
        &[],
    )
}

fn state() -> Obj {
    Obj::mk_ctor(
        layout::MACRO_STATE.tag,
        vec![
            Obj::mk_nat(17),
            Obj::mk_nat(layout::LIST_NIL_TAG),
            Obj::mk_nat(layout::LIST_NIL_TAG),
        ],
        &[],
    )
}

fn result_payload(value: &Obj, state: &Obj) -> Obj {
    check_layout(value, layout::RESULT_OK).unwrap();
    assert_eq!(
        value.try_ctor_child(1).unwrap().identity_token(),
        state.identity_token(),
        "lookup preserves the exact state object"
    );
    value.try_ctor_child(0).unwrap()
}

#[test]
fn native_lookups_use_explicit_authority_and_preserve_state() {
    let lookup = lookup("Host.Current");
    let context = context();
    let state = state();
    let namespace = Intrinsic::GetCurrNamespace
        .invoke_with_lookup(
            "mirror:Lean.Macro.getCurrNamespace",
            &[context.clone_ref(), state.clone_ref()],
            Some(&lookup),
        )
        .unwrap_or_else(|_| panic!("valid namespace lookup was refused"))
        .into_object();
    assert_eq!(
        Conversion::new()
            .project_name(&result_payload(&namespace, &state))
            .unwrap(),
        lookup.namespace
    );
    for (declaration, expected) in [
        (lookup.declaration.clone(), true),
        (Name::from_components(["Absent", "decl"]), false),
        (Name::str(Name::anonymous(), "Present.decl"), false),
    ] {
        let result = Intrinsic::HasDecl
            .invoke_with_lookup(
                "mirror:Lean.Macro.hasDecl",
                &[
                    inject_name(&declaration),
                    context.clone_ref(),
                    state.clone_ref(),
                ],
                Some(&lookup),
            )
            .unwrap_or_else(|_| panic!("valid declaration lookup was refused"))
            .into_object();
        assert_eq!(
            result_payload(&result, &state).unbox(),
            usize::from(expected)
        );
    }
    assert_eq!(lookup.calls.get(), 4);
    assert!(matches!(
        Intrinsic::GetCurrNamespace
            .invoke("mirror:Lean.Macro.getCurrNamespace", &[context, state],),
        Err(IntrinsicFailure::Refused(
            VmRefusal::MacroLookupUnavailable {
                operation: "Lean.Macro.getCurrNamespace",
            }
        ))
    ));
    assert_eq!(lookup.calls.get(), 4);
}

#[test]
fn malformed_macro_carriers_do_not_invoke_host_lookups() {
    let lookup = lookup("Host");
    for (context, state) in [
        (Obj::mk_nat(0), state()),
        (context(), Obj::mk_nat(0)),
        (
            Obj::mk_ctor(layout::MACRO_CONTEXT.tag, vec![], &[]),
            state(),
        ),
        (
            context(),
            Obj::mk_ctor(layout::MACRO_STATE.tag, vec![], &[]),
        ),
    ] {
        assert!(matches!(
            Intrinsic::GetCurrNamespace.invoke_with_lookup(
                "mirror:Lean.Macro.getCurrNamespace",
                &[context, state],
                Some(&lookup),
            ),
            Err(IntrinsicFailure::Refused(VmRefusal::InvalidCtorObject))
        ));
    }
    assert!(matches!(
        Intrinsic::HasDecl.invoke_with_lookup(
            "mirror:Lean.Macro.hasDecl",
            &[Obj::mk_string("not a Name"), context(), state()],
            Some(&lookup),
        ),
        Err(IntrinsicFailure::Refused(_))
    ));
    assert_eq!(lookup.calls.get(), 0);
}

fn callable_program(row_id: &str) -> flbc::ValidatedProgram {
    let row = crate::macro_native::row_for_id(row_id).unwrap();
    let arity = u16::try_from(row.parameters.len()).unwrap();
    let register = flbc::Register::new;
    let function = flbc::FunctionId::new;
    let source = flbc::Program::new(
        function(0),
        vec![
            flbc::Function {
                id: function(0),
                arity: 0,
                parameter_ownership: vec![],
                result_ownership: CallableResultOwnership::Scalar,
                register_count: 1,
                code: vec![
                    flbc::Instruction::Nat {
                        dst: register(0),
                        value: 0,
                    },
                    flbc::Instruction::Return { src: register(0) },
                ],
            },
            flbc::Function {
                id: function(1),
                arity,
                parameter_ownership: vec![ArgumentOwnership::Borrowed; usize::from(arity)],
                result_ownership: CallableResultOwnership::Erased,
                register_count: arity + 1,
                code: vec![
                    flbc::Instruction::Intrinsic {
                        dst: register(arity),
                        row: row.id.into(),
                        args: (0..arity).map(register).collect(),
                        argument_ownership: row.argument_ownership(),
                        result_ownership: row.result_ownership(),
                    },
                    flbc::Instruction::Return {
                        src: register(arity),
                    },
                ],
            },
        ],
    );
    let checked = flbc::validate(source).unwrap();
    let managed = flbc::insert_ownership(&checked, flbc::OwnershipLimits::default()).unwrap();
    let bytes = flbc::encode_canonical(managed.program(), flbc::CodecLimits::default()).unwrap();
    flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap()
}

#[test]
fn vm_lookup_capability_is_isolated_per_invocation_and_obeys_stops() {
    let program = callable_program("mirror:Lean.Macro.getCurrNamespace");
    let first = lookup("First");
    let second = lookup("Second");
    for provider in [&first, &second, &first] {
        let state = state();
        let outcome = crate::interpreter::execute_function_with_macro_lookup(
            &program,
            flbc::FunctionId::new(1),
            vec![context(), state.clone_ref()],
            ExecutionLimits::default(),
            provider,
            None,
        );
        let Outcome::Complete(VmExit::Returned(result)) = outcome else {
            panic!("{outcome:?}")
        };
        assert_eq!(
            Conversion::new()
                .project_name(&result_payload(&result.value, &state))
                .unwrap(),
            provider.namespace
        );
    }
    assert!(matches!(
        execute_function(
            &program,
            flbc::FunctionId::new(1),
            vec![context(), state()],
            ExecutionLimits::default(),
            None,
        ),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::MacroLookupUnavailable { .. },
            ..
        })
    ));
    let calls = first.calls.get();
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
            crate::interpreter::execute_function_with_macro_lookup(
                &program,
                flbc::FunctionId::new(1),
                vec![context(), state()],
                limits,
                &first,
                Some(&cancellation),
            ),
            Outcome::Inconclusive(_)
        ));
    }
    assert_eq!(first.calls.get(), calls);
}

struct ResolutionLookup {
    namespace: Name,
    requested: Name,
    namespaces: Vec<Name>,
    globals: ResolvedGlobals,
    failure: Option<MacroLookupError>,
    calls: Cell<usize>,
}

impl MacroLookup for ResolutionLookup {
    fn current_namespace(&self) -> &Name {
        &self.namespace
    }

    fn has_decl(&self, _: &Name) -> bool {
        false
    }

    fn resolve_namespace(&self, requested: &Name) -> Result<Vec<Name>, MacroLookupError> {
        assert_eq!(requested, &self.requested);
        self.calls.set(self.calls.get() + 1);
        match &self.failure {
            Some(error) => Err(error.clone()),
            None => Ok(self.namespaces.clone()),
        }
    }

    fn resolve_global_name(&self, requested: &Name) -> Result<ResolvedGlobals, MacroLookupError> {
        assert_eq!(requested, &self.requested);
        self.calls.set(self.calls.get() + 1);
        match &self.failure {
            Some(error) => Err(error.clone()),
            None => Ok(self.globals.clone()),
        }
    }
}

fn resolution_lookup() -> ResolutionLookup {
    let first = Name::from_components(["First", "candidate"]);
    let second = Name::from_components(["Second", "candidate"]);
    ResolutionLookup {
        namespace: Name::from_components(["Current"]),
        requested: Name::from_components(["candidate", "field"]),
        namespaces: vec![first.clone(), second.clone(), first.clone()],
        globals: vec![
            (second, vec!["field".into(), "λ".into()]),
            (first, Vec::new()),
        ],
        failure: None,
        calls: Cell::new(0),
    }
}

fn list_values(value: &Obj) -> Vec<Obj> {
    let mut cursor = value.clone_ref();
    let mut result = Vec::new();
    while !cursor.is_scalar() {
        check_layout(&cursor, layout::LIST_CONS).unwrap();
        result.push(child(&cursor, 0).unwrap());
        cursor = child(&cursor, 1).unwrap();
    }
    assert_eq!(cursor.unbox(), layout::LIST_NIL_TAG);
    result
}

#[test]
fn native_resolution_preserves_overload_projection_order_and_complete_state() {
    let lookup = resolution_lookup();
    for (intrinsic, row) in [
        (
            Intrinsic::ResolveNamespace,
            "mirror:Lean.Macro.resolveNamespace",
        ),
        (
            Intrinsic::ResolveGlobalName,
            "mirror:Lean.Macro.resolveGlobalName",
        ),
    ] {
        let state = state();
        let value = intrinsic
            .invoke_with_lookup(
                row,
                &[inject_name(&lookup.requested), context(), state.clone_ref()],
                Some(&lookup),
            )
            .unwrap_or_else(|_| panic!("{row} refused an authorized query"))
            .into_object();
        let candidates = list_values(&result_payload(&value, &state));
        if intrinsic == Intrinsic::ResolveNamespace {
            let names: Vec<_> = candidates
                .iter()
                .map(|value| Conversion::new().project_name(value).unwrap())
                .collect();
            assert_eq!(names, lookup.namespaces);
        } else {
            let names: ResolvedGlobals = candidates
                .iter()
                .map(|value| {
                    check_layout(value, layout::PROD).unwrap();
                    let declaration = Conversion::new()
                        .project_name(&child(value, 0).unwrap())
                        .unwrap();
                    let projections = list_values(&child(value, 1).unwrap())
                        .iter()
                        .map(|value| string(value).unwrap().to_owned())
                        .collect();
                    (declaration, projections)
                })
                .collect();
            assert_eq!(names, lookup.globals);
        }
    }
    assert_eq!(lookup.calls.get(), 2);
}

#[test]
fn resolution_refusals_and_resource_stops_are_not_empty_answers() {
    for row in [
        "mirror:Lean.Macro.resolveNamespace",
        "mirror:Lean.Macro.resolveGlobalName",
    ] {
        let program = callable_program(row);
        for failure in [
            Some(MacroLookupError::Unavailable),
            Some(MacroLookupError::Invalid("corrupt namespace journal")),
            Some(MacroLookupError::Exhausted("alias metadata")),
            Some(MacroLookupError::Limit {
                resource: "namespace journal bytes",
                limit: 10,
                observed: 11,
            }),
            None,
        ] {
            let mut lookup = resolution_lookup();
            lookup.failure = failure.clone();
            lookup.namespaces.clear();
            lookup.globals.clear();
            let state = state();
            let outcome = crate::interpreter::execute_function_with_macro_lookup(
                &program,
                flbc::FunctionId::new(1),
                vec![inject_name(&lookup.requested), context(), state.clone_ref()],
                ExecutionLimits::default(),
                &lookup,
                None,
            );
            match failure {
                Some(MacroLookupError::Unavailable) => assert!(matches!(
                    outcome,
                    Outcome::Complete(VmExit::Refused {
                        refusal: VmRefusal::MacroLookupUnavailable { .. },
                        ..
                    })
                )),
                Some(MacroLookupError::Invalid(_)) => assert!(matches!(
                    outcome,
                    Outcome::Complete(VmExit::Refused {
                        refusal: VmRefusal::MacroLookupInvalid { .. },
                        ..
                    })
                )),
                Some(MacroLookupError::Limit { .. }) => {
                    let Outcome::Inconclusive(stop) = outcome else {
                        panic!("resource stop became an answer: {outcome:?}")
                    };
                    assert!(matches!(
                        stop.cause,
                        fln_core::outcome::InconclusiveCause::ResourceExhausted { .. }
                    ));
                }
                Some(MacroLookupError::Exhausted(_)) => {
                    let Outcome::Inconclusive(stop) = outcome else {
                        panic!("dependency exhaustion became an answer: {outcome:?}")
                    };
                    assert!(matches!(
                        stop.cause,
                        fln_core::outcome::InconclusiveCause::DependencyUnavailable { .. }
                    ));
                }
                None => {
                    let Outcome::Complete(VmExit::Returned(result)) = outcome else {
                        panic!("unresolved lookup did not return {row}: {outcome:?}")
                    };
                    let value = result_payload(&result.value, &state);
                    assert!(value.is_scalar());
                    assert_eq!(value.unbox(), layout::LIST_NIL_TAG);
                }
            }
            assert_eq!(lookup.calls.get(), 1);
        }
    }
}

#[test]
fn resolution_validates_arguments_and_does_not_invent_missing_authority() {
    let provider = resolution_lookup();
    let minimal = lookup("Minimal");
    for (intrinsic, row) in [
        (
            Intrinsic::ResolveNamespace,
            "mirror:Lean.Macro.resolveNamespace",
        ),
        (
            Intrinsic::ResolveGlobalName,
            "mirror:Lean.Macro.resolveGlobalName",
        ),
    ] {
        assert!(matches!(
            intrinsic.invoke_with_lookup(
                row,
                &[inject_name(&provider.requested), context(), state()],
                Some(&minimal)
            ),
            Err(IntrinsicFailure::Refused(
                VmRefusal::MacroLookupUnavailable { .. }
            ))
        ));
        for arguments in [
            vec![Obj::mk_string("not a Name"), context(), state()],
            vec![inject_name(&provider.requested), Obj::mk_nat(0), state()],
            vec![inject_name(&provider.requested), context(), Obj::mk_nat(0)],
        ] {
            assert!(matches!(
                intrinsic.invoke_with_lookup(row, &arguments, Some(&provider)),
                Err(IntrinsicFailure::Refused(_))
            ));
        }
    }
    assert_eq!(provider.calls.get(), 0);
    assert_eq!(minimal.calls.get(), 0);
}

#[test]
fn resolution_bounds_whole_lists_before_encoding_abi_values() {
    let names = vec![Name::anonymous(); MAX_NAME_NODES as usize + 1];
    assert!(matches!(
        namespace_candidates(&names),
        Err(IntrinsicFailure::MirrorResource {
            resource: "macro lookup nodes",
            ..
        })
    ));
    let text = "x".repeat(MAX_NAME_BYTES as usize / 2 + 1);
    let names = vec![(Name::anonymous(), vec![text.clone(), text])];
    assert!(matches!(
        global_candidates(&names),
        Err(IntrinsicFailure::MirrorResource {
            resource: "macro lookup bytes",
            ..
        })
    ));
    let overflowed = Name::num_overflowing(Name::anonymous(), 0);
    assert!(matches!(
        namespace_candidates(&[overflowed]),
        Err(IntrinsicFailure::Refused(VmRefusal::InvalidCtorObject))
    ));
}
