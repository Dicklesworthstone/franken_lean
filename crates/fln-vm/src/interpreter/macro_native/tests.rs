use super::super::{
    ArgumentOwnership, CallableResultOwnership, ExecutionLimits, Outcome, ResultOwnership, VmExit,
    execute_function, resolve_intrinsic_plan,
};
use super::*;
use fln_comp::flbc;

mod identifiers;
mod literals;
mod lookup;
mod numbers;
mod patterns;
mod sequences;
mod syntax_editing;

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
        Intrinsic::NameStr => "mirror:Lean.Name.str._override",
        Intrinsic::MkStr1 => "mirror:Lean.Name.mkStr1",
        Intrinsic::NameHasMacroScopes => "mirror:Lean.Name.hasMacroScopes",
        Intrinsic::NameEraseMacroScopes => "mirror:Lean.Name.eraseMacroScopes",
        Intrinsic::AddMacroScope => "mirror:Lean.addMacroScope",
        Intrinsic::MacroAddMacroScope => "mirror:Lean.Macro.addMacroScope",
        Intrinsic::IsOfKind => "mirror:Lean.Syntax.isOfKind",
        Intrinsic::GetArg => "mirror:Lean.Syntax.getArg",
        Intrinsic::GetNumArgs => "mirror:Lean.Syntax.getNumArgs",
        Intrinsic::IsNodeOf => "mirror:Lean.Syntax.isNodeOf",
        Intrinsic::MatchesNull => "mirror:Lean.Syntax.matchesNull",
        Intrinsic::MatchesIdent => "mirror:Lean.Syntax.matchesIdent",
        Intrinsic::MatchesLit => "mirror:Lean.Syntax.matchesLit",
        Intrinsic::GetOptional => "mirror:Lean.Syntax.getOptional?",
        Intrinsic::GetKind => "mirror:Lean.Syntax.getKind",
        Intrinsic::SetKind => "mirror:Lean.Syntax.setKind",
        Intrinsic::GetArgs => "mirror:Lean.Syntax.getArgs",
        Intrinsic::GetSepArgs => "mirror:Lean.Syntax.getSepArgs",
        Intrinsic::MkSepArray => "mirror:Lean.mkSepArray",
        Intrinsic::MkSep => "mirror:Lean.Syntax.mkSep",
        Intrinsic::SepArrayGetElems => "mirror:Lean.Syntax.SepArray.getElems._redArg",
        Intrinsic::TSepArrayGetElems => "mirror:Lean.Syntax.TSepArray.getElems._redArg",
        Intrinsic::SepArrayOfElems => "mirror:Lean.Syntax.SepArray.ofElems",
        Intrinsic::TSepArrayPush => "mirror:Lean.Syntax.TSepArray.push._redArg",
        Intrinsic::SetArgs => "mirror:Lean.Syntax.setArgs",
        Intrinsic::SetArg => "mirror:Lean.Syntax.setArg",
        Intrinsic::IsAtom => "mirror:Lean.Syntax.isAtom",
        Intrinsic::GetAtomVal => "mirror:Lean.Syntax.getAtomVal",
        Intrinsic::SetAtomVal => "mirror:Lean.Syntax.setAtomVal",
        Intrinsic::GetHeadInfo => "mirror:Lean.Syntax.getHeadInfo",
        Intrinsic::SourceInfoGetPos => "mirror:Lean.SourceInfo.getPos?",
        Intrinsic::SourceInfoGetTailPos => "mirror:Lean.SourceInfo.getTailPos?",
        Intrinsic::GetPos => "mirror:Lean.Syntax.getPos?",
        Intrinsic::GetTailPos => "mirror:Lean.Syntax.getTailPos?",
        Intrinsic::SourceInfoFromRef => "mirror:Lean.SourceInfo.fromRef",
        Intrinsic::MkAtom => "mirror:Lean.mkAtom",
        Intrinsic::MkAtomFrom => "mirror:Lean.mkAtomFrom",
        Intrinsic::MkIdent => "mirror:Lean.mkIdent",
        Intrinsic::MkIdentFrom => "mirror:Lean.mkIdentFrom",
        Intrinsic::MkCIdent => "mirror:Lean.mkCIdent",
        Intrinsic::MkCIdentFrom => "mirror:Lean.mkCIdentFrom",
        Intrinsic::MkLit => "mirror:Lean.Syntax.mkLit",
        Intrinsic::MkStrLit => "mirror:Lean.Syntax.mkStrLit",
        Intrinsic::IsLit => "mirror:Lean.Syntax.isLit?",
        Intrinsic::IsStrLit => "mirror:Lean.Syntax.isStrLit?",
        Intrinsic::GetString => "mirror:Lean.TSyntax.getString",
        Intrinsic::MkNumLit => "mirror:Lean.Syntax.mkNumLit",
        Intrinsic::MkNatLit => "mirror:Lean.Syntax.mkNatLit",
        Intrinsic::IsNatLit => "mirror:Lean.Syntax.isNatLit?",
        Intrinsic::GetNat => "mirror:Lean.TSyntax.getNat",
        Intrinsic::NatReprFast => "mirror:Nat.reprFast",
        Intrinsic::ReplaceRef => "mirror:Lean.replaceRef",
        Intrinsic::ThrowError => "mirror:Lean.Macro.throwError._redArg",
        Intrinsic::ThrowErrorAt => "mirror:Lean.Macro.throwErrorAt._redArg",
        Intrinsic::ThrowUnsupported => "mirror:Lean.Macro.throwUnsupported._redArg",
        Intrinsic::SetInfo => "mirror:Lean.Syntax.setInfo",
        Intrinsic::IsMissing => "mirror:Lean.Syntax.isMissing",
        Intrinsic::IsIdent => "mirror:Lean.Syntax.isIdent",
        Intrinsic::GetId => "mirror:Lean.Syntax.getId",
        Intrinsic::GetCurrNamespace => "mirror:Lean.Macro.getCurrNamespace",
        Intrinsic::HasDecl => "mirror:Lean.Macro.hasDecl",
        Intrinsic::ResolveNamespace => "mirror:Lean.Macro.resolveNamespace",
        Intrinsic::ResolveGlobalName => "mirror:Lean.Macro.resolveGlobalName",
        Intrinsic::ExpandMacro => "mirror:Lean.Macro.expandMacro?",
    };
    match intrinsic.invoke(id, args) {
        Ok(value) => value.into_object(),
        Err(_) => panic!("native {id} refused a valid input"),
    }
}

#[test]
fn native_name_constructor_preserves_components_hash_and_shared_inputs() {
    let parent = Name::num(Name::from_components(["Parent", "scope"]), u64::MAX);
    let parent_value = inject_name(&parent);
    for component in ["", "A.B", "λ\0🙂"] {
        let text = Obj::mk_string(component);
        let result = invoke(
            Intrinsic::NameStr,
            &[parent_value.clone_ref(), text.clone_ref()],
        );
        let expected = Name::str(parent.clone(), component);
        // The converter validates every stored computed hash, not just the
        // name's component sequence.
        assert_eq!(Conversion::new().project_name(&result).unwrap(), expected);
        assert_eq!(
            Conversion::new().project_name(&parent_value).unwrap(),
            parent
        );
        assert_eq!(string(&text).unwrap(), component);
    }
    for args in [
        vec![Obj::mk_nat(1), Obj::mk_string("x")],
        vec![inject_name(&parent), Obj::mk_nat(0)],
        vec![
            Obj::mk_ctor(1, vec![Obj::mk_nat(0), Obj::mk_string("forged")], &[0; 8]),
            Obj::mk_string("x"),
        ],
    ] {
        assert!(
            Intrinsic::NameStr
                .invoke("mirror:Lean.Name.str._override", &args)
                .is_err()
        );
    }
    let oversized_parent = inject_name(&Name::str(
        Name::anonymous(),
        "p".repeat((MAX_NAME_BYTES / 2) as usize),
    ));
    let oversized_component = Obj::mk_string(&"s".repeat((MAX_NAME_BYTES / 2 + 1) as usize));
    assert!(matches!(
        Intrinsic::NameStr.invoke(
            "mirror:Lean.Name.str._override",
            &[oversized_parent, oversized_component]
        ),
        Err(IntrinsicFailure::MirrorResource {
            resource: "name constructor bytes",
            ..
        })
    ));
    assert_eq!(
        Conversion::new()
            .project_name(&invoke(
                Intrinsic::NameStr,
                &[Obj::mk_nat(0), Obj::mk_string("recovered")]
            ))
            .unwrap(),
        Name::str(Name::anonymous(), "recovered")
    );
}

#[test]
fn recursive_expansion_requires_an_explicit_host_capability() {
    let row = "mirror:Lean.Macro.expandMacro?";
    assert!(matches!(
        Intrinsic::ExpandMacro.invoke(row, &[Obj::mk_nat(0), Obj::mk_nat(0), Obj::mk_nat(0)]),
        Err(IntrinsicFailure::Refused(
            VmRefusal::MacroExpansionUnavailable
        ))
    ));
    assert!(matches!(
        Intrinsic::ExpandMacro.invoke(row, &[]),
        Err(IntrinsicFailure::Refused(VmRefusal::IntrinsicArity {
            expected: 3,
            actual: 0,
            ..
        }))
    ));
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
fn native_scope_attachment_shares_the_hygiene_engine_and_preserves_state() {
    let context = inject_name(&Name::from_components(["Main"]));
    let original = inject_name(&Name::from_components(["α"]));
    let scoped = invoke(
        Intrinsic::AddMacroScope,
        &[context.clone_ref(), original.clone_ref(), Obj::mk_nat(17)],
    );
    assert_eq!(
        Conversion::new().project_name(&scoped).unwrap(),
        Name::num(Name::from_components(["α", "_@", "Main", "_hyg"]), 17)
    );
    assert_eq!(
        Conversion::new().project_name(&original).unwrap(),
        Name::from_components(["α"])
    );
    let repeated = invoke(
        Intrinsic::AddMacroScope,
        &[context.clone_ref(), scoped.clone_ref(), Obj::mk_nat(18)],
    );
    assert_eq!(
        Conversion::new().project_name(&repeated).unwrap(),
        Name::num(
            Name::num(Name::from_components(["α", "_@", "Main", "_hyg"]), 17),
            18
        )
    );
    let other = inject_name(&Name::from_components(["Other", "Module"]));
    let changed = invoke(
        Intrinsic::AddMacroScope,
        &[other, repeated, Obj::mk_nat(99)],
    );
    let imported = Name::num(
        Name::num(Name::from_components(["α", "_@", "Main"]), 17),
        18,
    );
    let expected = Name::num(
        Name::str(
            imported.append_core(&Name::from_components(["Other", "Module"])),
            "_hyg",
        ),
        99,
    );
    assert_eq!(Conversion::new().project_name(&changed).unwrap(), expected);

    for scope in [0, u64::MAX] {
        let value = invoke(
            Intrinsic::AddMacroScope,
            &[
                context.clone_ref(),
                original.clone_ref(),
                Obj::mk_mpz(&[scope], false),
            ],
        );
        assert_eq!(
            Conversion::new().project_name(&value).unwrap(),
            Name::num(Name::from_components(["α", "_@", "Main", "_hyg"]), scope)
        );
    }
    let state = Obj::mk_ctor(
        layout::MACRO_STATE.tag,
        vec![
            Obj::mk_nat(10),
            Obj::mk_nat(layout::LIST_NIL_TAG),
            Obj::mk_nat(layout::LIST_NIL_TAG),
        ],
        &[],
    );
    let ctx = Obj::mk_ctor(
        layout::MACRO_CONTEXT.tag,
        vec![
            Obj::mk_string("opaque methods must not be observed"),
            context,
            Obj::mk_nat(17),
            Obj::mk_nat(0),
            Obj::mk_nat(1000),
            Obj::mk_nat(layout::SYNTAX_MISSING_TAG),
        ],
        &[],
    );
    let program = lookup::callable_program("mirror:Lean.Macro.addMacroScope");
    let bytes = flbc::encode_canonical(&program, flbc::CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    for program in [&program, &replay] {
        let outcome = execute_function(
            program,
            flbc::FunctionId::new(1),
            vec![original.clone_ref(), ctx.clone_ref(), state.clone_ref()],
            ExecutionLimits::default(),
            None,
        );
        let Outcome::Complete(VmExit::Returned(result)) = outcome else {
            panic!("{outcome:?}")
        };
        check_layout(&result.value, layout::RESULT_OK).unwrap();
        assert_eq!(
            child(&result.value, 1).unwrap().identity_token(),
            state.identity_token()
        );
        assert_eq!(
            Conversion::new()
                .project_name(&child(&result.value, 0).unwrap())
                .unwrap(),
            Conversion::new().project_name(&scoped).unwrap()
        );
    }
}

#[test]
fn native_scope_attachment_refuses_malformed_data_and_preserves_resource_stops() {
    let row = "mirror:Lean.addMacroScope";
    let context = inject_name(&Name::from_components(["Main"]));
    let plain = inject_name(&Name::from_components(["α"]));
    for malformed in [
        Name::from_components(["x", "_hyg"]),
        Name::num(Name::from_components(["x", "Ctx", "_hyg"]), 5),
    ] {
        assert!(matches!(
            Intrinsic::AddMacroScope.invoke(
                row,
                &[context.clone_ref(), inject_name(&malformed), Obj::mk_nat(1)]
            ),
            Err(IntrinsicFailure::Refused(VmRefusal::InvalidCtorObject))
        ));
    }
    assert!(matches!(
        Intrinsic::AddMacroScope.invoke(
            row,
            &[
                context.clone_ref(),
                plain.clone_ref(),
                Obj::mk_mpz(&[1], true)
            ]
        ),
        Err(IntrinsicFailure::Refused(VmRefusal::TypeMismatch { .. }))
    ));
    assert!(matches!(
        Intrinsic::AddMacroScope.invoke(row, &[context.clone_ref(), plain.clone_ref()]),
        Err(IntrinsicFailure::Refused(VmRefusal::IntrinsicArity { .. }))
    ));
    let program = lookup::callable_program(row);
    for (scope, limits, cancellation) in [
        (
            Obj::mk_mpz(&[0, 1], false),
            ExecutionLimits::default(),
            None,
        ),
        (
            Obj::mk_nat(1),
            ExecutionLimits {
                max_steps: 0,
                ..ExecutionLimits::default()
            },
            None,
        ),
    ] {
        assert!(matches!(
            execute_function(
                &program,
                flbc::FunctionId::new(1),
                vec![context.clone_ref(), plain.clone_ref(), scope],
                limits,
                cancellation
            ),
            Outcome::Inconclusive(_)
        ));
    }
    let oversized_context = inject_name(&Name::str(
        Name::anonymous(),
        "c".repeat((MAX_NAME_BYTES / 2) as usize),
    ));
    let oversized_value = inject_name(&Name::str(
        Name::anonymous(),
        "v".repeat((MAX_NAME_BYTES / 2) as usize),
    ));
    assert!(matches!(
        Intrinsic::AddMacroScope.invoke(row, &[oversized_context, oversized_value, Obj::mk_nat(1)]),
        Err(IntrinsicFailure::MirrorResource {
            resource: "macro scope bytes",
            ..
        })
    ));
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
fn syntax_inspection_keeps_hygienic_names_and_distinguishes_pseudo_kinds() {
    let hygienic = Name::num(Name::from_components(["Main", "_hyg", "α"]), 37);
    let id = inject_name(&hygienic);
    let id_identity = id.identity_token();
    let ident = Obj::mk_ctor(
        layout::SYNTAX_IDENT.tag,
        vec![
            Obj::mk_nat(layout::SOURCE_NONE_TAG),
            Obj::mk_ctor(
                layout::SUBSTRING_RAW.tag,
                vec![Obj::mk_string(" α "), Obj::mk_nat(1), Obj::mk_nat(3)],
                &[],
            ),
            id,
            Obj::mk_nat(layout::LIST_NIL_TAG),
        ],
        &[],
    );
    assert_eq!(
        invoke(Intrinsic::GetId, &[ident.clone_ref()]).identity_token(),
        id_identity
    );
    for (syntax, expected_kind, missing, is_ident) in [
        (
            Obj::mk_nat(layout::SYNTAX_MISSING_TAG),
            Name::from_components(["missing"]),
            true,
            false,
        ),
        (ident, Name::from_components(["ident"]), false, true),
        (
            atom("A.B\0🙂"),
            Name::str(Name::anonymous(), "A.B\0🙂"),
            false,
            false,
        ),
        (
            node(Name::from_components(["missing"]), vec![]),
            Name::from_components(["missing"]),
            false,
            false,
        ),
        (
            atom("ident"),
            Name::from_components(["ident"]),
            false,
            false,
        ),
    ] {
        let kind = invoke(Intrinsic::GetKind, &[syntax.clone_ref()]);
        assert_eq!(
            Conversion::new().project_name(&kind).unwrap(),
            expected_kind
        );
        assert_eq!(
            invoke(Intrinsic::IsMissing, &[syntax.clone_ref()]).unbox(),
            usize::from(missing)
        );
        assert_eq!(
            invoke(Intrinsic::IsIdent, &[syntax.clone_ref()]).unbox(),
            usize::from(is_ident)
        );
        let actual_id = invoke(Intrinsic::GetId, &[syntax.clone_ref()]);
        assert_eq!(
            Conversion::new().project_name(&actual_id).unwrap(),
            if is_ident {
                hygienic.clone()
            } else {
                Name::anonymous()
            }
        );
        assert_eq!(
            invoke(Intrinsic::GetArgs, &[syntax])
                .try_array_view()
                .unwrap()
                .0,
            0
        );
    }
}

#[test]
fn syntax_updates_preserve_source_children_and_unmodified_aliases() {
    let original_kind = Name::from_components(["original", "kind"]);
    let replacement = Name::num(Name::from_components(["new", "_hyg"]), 91);
    let info = Obj::mk_ctor(
        layout::SOURCE_SYNTHETIC.tag,
        vec![Obj::mk_nat(1), Obj::mk_nat(5)],
        &[1],
    );
    let info_identity = info.identity_token();
    let child = atom("λ\0🙂");
    let child_identity = child.identity_token();
    let children = Obj::mk_array(vec![child]);
    let array_identity = children.identity_token();
    let syntax = Obj::mk_ctor(
        layout::SYNTAX_NODE.tag,
        vec![info, inject_name(&original_kind), children],
        &[],
    );
    assert_eq!(
        invoke(Intrinsic::GetArgs, &[syntax.clone_ref()]).identity_token(),
        array_identity
    );
    let changed = invoke(
        Intrinsic::SetKind,
        &[syntax.clone_ref(), inject_name(&replacement)],
    );
    assert_eq!(
        changed.try_ctor_child(0).unwrap().identity_token(),
        info_identity
    );
    let changed_args = invoke(Intrinsic::GetArgs, &[changed.clone_ref()]);
    assert_eq!(changed_args.identity_token(), array_identity);
    assert_eq!(changed_args.array_child(0).identity_token(), child_identity);
    assert_eq!(
        Conversion::new()
            .project_name(&invoke(Intrinsic::GetKind, &[changed]))
            .unwrap(),
        replacement
    );
    assert_eq!(
        Conversion::new()
            .project_name(&invoke(Intrinsic::GetKind, &[syntax]))
            .unwrap(),
        original_kind
    );
    let leaf = atom("leaf");
    assert_eq!(
        invoke(
            Intrinsic::SetKind,
            &[leaf.clone_ref(), inject_name(&replacement)]
        )
        .identity_token(),
        leaf.identity_token()
    );
    assert_eq!(
        invoke(
            Intrinsic::SetKind,
            &[
                Obj::mk_nat(layout::SYNTAX_MISSING_TAG),
                inject_name(&replacement)
            ]
        )
        .unbox(),
        layout::SYNTAX_MISSING_TAG
    );
}

#[test]
fn syntax_accessors_refuse_malformed_carriers_without_panicking() {
    for intrinsic in [
        Intrinsic::GetKind,
        Intrinsic::GetArgs,
        Intrinsic::IsMissing,
        Intrinsic::IsIdent,
        Intrinsic::GetId,
    ] {
        for malformed in [
            Obj::mk_nat(77),
            Obj::mk_ctor(layout::SYNTAX_IDENT.tag, vec![], &[]),
        ] {
            assert!(matches!(
                intrinsic.invoke("invalid syntax", &[malformed]),
                Err(IntrinsicFailure::Refused(VmRefusal::InvalidCtorObject))
            ));
        }
    }
    let malformed = Obj::mk_ctor(
        layout::SYNTAX_NODE.tag,
        vec![
            Obj::mk_nat(layout::SOURCE_NONE_TAG),
            inject_name(&Name::anonymous()),
            Obj::mk_string("not an array"),
        ],
        &[],
    );
    assert!(matches!(
        Intrinsic::GetArgs.invoke("mirror:Lean.Syntax.getArgs", &[malformed.clone_ref()]),
        Err(IntrinsicFailure::Refused(VmRefusal::InvalidArrayObject))
    ));
    assert!(matches!(
        Intrinsic::SetKind.invoke(
            "mirror:Lean.Syntax.setKind",
            &[malformed, inject_name(&Name::anonymous())]
        ),
        Err(IntrinsicFailure::Refused(VmRefusal::InvalidArrayObject))
    ));
    let malformed = Obj::mk_ctor(
        layout::SYNTAX_NODE.tag,
        vec![
            Obj::mk_nat(layout::SOURCE_NONE_TAG),
            Obj::mk_string("not a name"),
            Obj::mk_array(vec![]),
        ],
        &[],
    );
    assert!(matches!(
        Intrinsic::GetKind.invoke("mirror:Lean.Syntax.getKind", &[malformed]),
        Err(IntrinsicFailure::Refused(VmRefusal::InvalidCtorObject))
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
