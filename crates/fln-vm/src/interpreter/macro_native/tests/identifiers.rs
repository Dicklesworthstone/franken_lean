use super::*;

fn raw_spelling(value: &Obj) -> String {
    assert!(matches!(syntax_kind(value), Ok(SyntaxKind::Ident)));
    let raw = child(value, 1).unwrap();
    check_layout(&raw, layout::SUBSTRING_RAW).unwrap();
    let text = child(&raw, 0).unwrap();
    let text = string(&text).unwrap();
    assert_eq!(child(&raw, 1).unwrap().unbox(), 0);
    assert_eq!(child(&raw, 2).unwrap().unbox(), text.len());
    text.to_owned()
}

#[test]
fn identifier_constructors_preserve_structural_names_and_exact_raw_spelling() {
    let cases = [
        (Name::anonymous(), "[anonymous]"),
        (Name::str(Name::anonymous(), ""), "«»"),
        (Name::from_components(["Nat", "succ"]), "Nat.succ"),
        (Name::from_components(["A.B", "42"]), "«A.B».«42»"),
        (Name::from_components(["if", "then"]), "if.then"),
        (Name::from_components(["α₁", "é", "λ"]), "α₁.é.«λ»"),
        (
            Name::from_components(["漢", "🙂", "a\0b"]),
            "«漢».«🙂».«a\0b»",
        ),
        (Name::from_components(["a»b", "«"]), "a»b.««»"),
        (Name::from_components(["?u", "a b"]), "?u.a b"),
        (Name::from_components(["#0", "a b"]), "#0.a b"),
        (Name::from_components(["_", "a b"]), "_.«a b»"),
        (
            Name::from_components(["a b", "_inaccessible"]),
            "a b._inaccessible",
        ),
        (Name::from_components(["a b", "x✝"]), "a b.x✝"),
        (Name::from_components(["x✝", "a b"]), "«x✝».«a b»"),
        (
            Name::num(Name::from_components(["a b", "_hyg"]), 17),
            "a b._hyg.17",
        ),
        (
            Name::num(Name::str(Name::anonymous(), "42"), u64::MAX),
            "«42».18446744073709551615",
        ),
    ];
    for (native, expected) in cases {
        let value = inject_name(&native);
        let result = invoke(Intrinsic::MkIdent, &[value.clone_ref()]);
        assert_eq!(raw_spelling(&result), expected, "{native:?}");
        assert_eq!(child(&result, 0).unwrap().unbox(), layout::SOURCE_NONE_TAG);
        assert_eq!(
            child(&result, 2).unwrap().identity_token(),
            value.identity_token()
        );
        assert_eq!(child(&result, 3).unwrap().unbox(), layout::LIST_NIL_TAG);
        assert_eq!(
            Conversion::new()
                .project_name(&child(&result, 2).unwrap())
                .unwrap(),
            native
        );
    }
}

#[test]
fn constant_identifiers_use_reserved_hygiene_and_exact_preresolution() {
    for declaration in [
        Name::from_components(["Nat", "succ"]),
        Name::from_components(["a b", "λ"]),
    ] {
        let original = inject_name(&declaration);
        let result = invoke(Intrinsic::MkCIdent, &[original.clone_ref()]);
        let expected = fln_core::name::hygiene::add_macro_scope(
            &Name::from_components(["_internal"]),
            &declaration,
            fln_core::name::hygiene::RESERVED_MACRO_SCOPE,
        )
        .unwrap();
        assert_eq!(
            Conversion::new()
                .project_name(&child(&result, 2).unwrap())
                .unwrap(),
            expected
        );
        assert_eq!(
            raw_spelling(&result),
            format!("{}._@._internal._hyg.0", declaration.to_display_string())
        );
        let candidates = child(&result, 3).unwrap();
        check_layout(&candidates, layout::LIST_CONS).unwrap();
        assert_eq!(child(&candidates, 1).unwrap().unbox(), layout::LIST_NIL_TAG);
        let candidate = child(&candidates, 0).unwrap();
        check_layout(&candidate, layout::PRERESOLVED_DECL).unwrap();
        assert_eq!(
            child(&candidate, 0).unwrap().identity_token(),
            original.identity_token()
        );
        assert_eq!(child(&candidate, 1).unwrap().unbox(), layout::LIST_NIL_TAG);
    }
}

#[test]
fn identifier_reference_spans_use_the_same_canonical_fallback_and_keep_inputs_shared() {
    let original = inject_name(&Name::from_components(["long token λ"]));
    let first = Obj::mk_ctor(
        layout::SOURCE_SYNTHETIC.tag,
        vec![Obj::mk_nat(1), Obj::mk_nat(3)],
        &[1],
    );
    let last = Obj::mk_ctor(
        layout::SOURCE_SYNTHETIC.tag,
        vec![Obj::mk_nat(4), Obj::mk_nat(9)],
        &[0],
    );
    let reference = node(
        Name::from_components(["ref"]),
        vec![
            Obj::mk_ctor(
                layout::SYNTAX_ATOM.tag,
                vec![first.clone_ref(), Obj::mk_string("a")],
                &[],
            ),
            Obj::mk_ctor(
                layout::SYNTAX_ATOM.tag,
                vec![last.clone_ref(), Obj::mk_string("b")],
                &[],
            ),
        ],
    );
    for intrinsic in [Intrinsic::MkIdentFrom, Intrinsic::MkCIdentFrom] {
        for (canonical, stop) in [(false, 9), (true, 3)] {
            let result = invoke(
                intrinsic,
                &[
                    reference.clone_ref(),
                    original.clone_ref(),
                    Obj::mk_nat(usize::from(canonical)),
                ],
            );
            let info = child(&result, 0).unwrap();
            assert_eq!(child(&info, 0).unwrap().unbox(), 1);
            assert_eq!(child(&info, 1).unwrap().unbox(), stop);
            assert_eq!(
                source_position(&info, canonical, false, "test")
                    .unwrap_or_else(|_| panic!("valid source info must have a position"))
                    .unwrap()
                    .unbox(),
                1
            );
            assert_eq!(
                Conversion::new().project_name(&original).unwrap(),
                Name::from_components(["long token λ"])
            );
            assert!(!raw_spelling(&result).is_empty());
        }
    }
    assert_eq!(child(&first, 1).unwrap().unbox(), 3);
    assert_eq!(child(&last, 1).unwrap().unbox(), 9);
}

#[test]
fn identifier_constructors_refuse_malformed_names_flags_and_resource_exhaustion_then_recover() {
    let good = inject_name(&Name::from_components(["recover"]));
    for (intrinsic, row) in [
        (Intrinsic::MkIdent, "mirror:Lean.mkIdent"),
        (Intrinsic::MkCIdent, "mirror:Lean.mkCIdent"),
    ] {
        for bad in [
            Obj::mk_nat(1),
            Obj::mk_string("not a Name"),
            Obj::mk_ctor(1, vec![Obj::mk_nat(0), Obj::mk_string("forged")], &[0; 8]),
        ] {
            assert!(intrinsic.invoke(row, &[bad]).is_err());
        }
        let huge = inject_name(&Name::str(
            Name::anonymous(),
            "a".repeat(MAX_NAME_BYTES as usize),
        ));
        assert!(matches!(
            intrinsic.invoke(row, &[huge]),
            Err(IntrinsicFailure::MirrorResource { .. })
        ));
        assert!(!raw_spelling(&invoke(intrinsic, &[good.clone_ref()])).is_empty());
    }
    for (intrinsic, row) in [
        (Intrinsic::MkIdentFrom, "mirror:Lean.mkIdentFrom"),
        (Intrinsic::MkCIdentFrom, "mirror:Lean.mkCIdentFrom"),
    ] {
        assert!(
            intrinsic
                .invoke(row, &[Obj::mk_nat(0), good.clone_ref(), Obj::mk_nat(2)])
                .is_err()
        );
        assert!(
            intrinsic
                .invoke(row, &[Obj::mk_nat(99), good.clone_ref(), Obj::mk_nat(0)])
                .is_err()
        );
        assert!(
            !raw_spelling(&invoke(
                intrinsic,
                &[Obj::mk_nat(0), good.clone_ref(), Obj::mk_nat(0)]
            ))
            .is_empty()
        );
    }
}
