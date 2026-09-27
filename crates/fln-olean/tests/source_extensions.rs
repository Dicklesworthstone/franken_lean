//! The actual pinned Prelude journals, plus hostile captured-entry mutations.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_olean::region::{OleanView, OpaqueExtensionBlock, WalkBudget};
use fln_olean::source_extensions::{DecodeError, DecodeLimits, SourceExtensions, decode};
use fln_rt::convert::inject_name;
use fln_rt::obj::Obj;
use fln_rt::region::{compact, materialize};
use std::sync::OnceLock;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn blocks() -> &'static Vec<OpaqueExtensionBlock> {
    static BLOCKS: OnceLock<Vec<OpaqueExtensionBlock>> = OnceLock::new();
    BLOCKS.get_or_init(|| {
        let public = include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean");
        let server =
            include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean.server");
        let private =
            include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean.private");
        OleanView::parse_with_dependencies(private, &[public, server])
            .unwrap()
            .extension_payloads(WalkBudget::default(), 32 << 20)
            .unwrap()
    })
}
fn entry(extension: &str) -> Obj {
    materialize(
        &blocks()
            .iter()
            .find(|b| b.name == n(extension))
            .unwrap()
            .entries[0],
        0,
    )
    .unwrap()
}
fn one(extension: &str, object: &Obj) -> Vec<OpaqueExtensionBlock> {
    vec![OpaqueExtensionBlock {
        name: n(extension),
        entries: vec![compact(object, 0).unwrap()],
    }]
}
fn read(blocks: &[OpaqueExtensionBlock]) -> Result<SourceExtensions, DecodeError> {
    decode(blocks, DecodeLimits::default())
}

#[test]
fn real_prelude_decodes_class_outputs_instance_order_and_defaults() {
    let decoded = read(blocks()).unwrap();
    assert_eq!(
        (
            decoded.classes.len(),
            decoded.instances.len(),
            decoded.defaults.len()
        ),
        (75, 151, 18)
    );
    let addition = decoded
        .classes
        .iter()
        .find(|row| row.name == n("HAdd"))
        .unwrap();
    assert_eq!(addition.out_params, [2]);
    assert_eq!(addition.out_level_params, [2]);
    let beq = decoded
        .instances
        .iter()
        .find(|row| row.declaration == n("instBEqOfDecidableEq"))
        .unwrap();
    assert_eq!(beq.priority, 500);
    assert_eq!(beq.synth_order, [1]);
    assert!(beq.scope.is_none());
    let conjunction = decoded
        .instances
        .iter()
        .find(|row| row.declaration == n("instDecidableAnd"))
        .unwrap();
    assert_eq!(conjunction.synth_order, [2, 3]);
    assert!(decoded.defaults.iter().any(|row| row.class == n("OfNat")));
    assert!(decoded.uninterpreted.contains(&n("Lean.aliasExtension")));
    assert!(
        decoded
            .instances
            .iter()
            .all(|row| !row.value.has_expr_mvar() && !row.value.has_level_mvar())
    );
}

#[test]
fn companion_journals_are_cumulative_not_three_disjoint_fragments() {
    let public = include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean");
    let server =
        include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean.server");
    let expected = read(blocks()).unwrap();
    for (bytes, dependencies) in [
        (public.as_slice(), vec![]),
        (server.as_slice(), vec![public.as_slice()]),
    ] {
        let blocks = OleanView::parse_with_dependencies(bytes, &dependencies)
            .unwrap()
            .extension_payloads(WalkBudget::default(), 32 << 20)
            .unwrap();
        let actual = read(&blocks).unwrap();
        assert_eq!(actual.classes, expected.classes);
        assert_eq!(actual.instances, expected.instances);
        assert_eq!(actual.defaults, expected.defaults);
    }
}

#[test]
fn scope_is_retained_and_not_silently_promoted_to_global() {
    let wrapped = entry("Lean.Meta.instanceExtension");
    let original = wrapped.ctor_child(0);
    let fields = (0..5).map(|i| original.ctor_child(i)).collect();
    let scoped = Obj::mk_ctor(0, fields, &[2]);
    let scoped = Obj::mk_ctor(1, vec![inject_name(&n("Example")), scoped], &[]);
    let decoded = read(&one("Lean.Meta.instanceExtension", &scoped)).unwrap();
    assert_eq!(decoded.instances[0].scope, Some(n("Example")));
    let inconsistent = Obj::mk_ctor(1, vec![inject_name(&n("Example")), original], &[]);
    assert!(read(&one("Lean.Meta.instanceExtension", &inconsistent)).is_err());
}

#[test]
fn forged_names_shapes_and_duplicate_synthesis_indices_refuse() {
    let class = entry("Lean.classExtension");
    let wrong = Obj::mk_ctor(
        0,
        vec![
            Obj::mk_string("not a Name"),
            class.ctor_child(1),
            class.ctor_child(2),
        ],
        &[],
    );
    assert!(read(&one("Lean.classExtension", &wrong)).is_err());
    let repeated = Obj::mk_ctor(
        0,
        vec![
            class.ctor_child(0),
            Obj::mk_array(vec![Obj::mk_nat(0), Obj::mk_nat(0)]),
            class.ctor_child(2),
        ],
        &[],
    );
    assert!(read(&one("Lean.classExtension", &repeated)).is_err());
    assert!(read(&one("Lean.classExtension", &Obj::mk_nat(0))).is_err());
    let original = entry("Lean.Meta.instanceExtension").ctor_child(0);
    for (index, replacement) in [
        (3, Obj::mk_ctor(1, vec![inject_name(&n("forged"))], &[])),
        (4, Obj::mk_array(vec![Obj::mk_nat(1), Obj::mk_nat(1)])),
        (2, Obj::mk_mpz(&[1], true)),
    ] {
        let fields = (0..5)
            .map(|i| {
                if i == index {
                    replacement.clone_ref()
                } else {
                    original.ctor_child(i)
                }
            })
            .collect();
        let malformed = Obj::mk_ctor(0, vec![Obj::mk_ctor(0, fields, &[0])], &[]);
        assert!(read(&one("Lean.Meta.instanceExtension", &malformed)).is_err());
    }
}

#[test]
fn selected_payloads_are_cumulatively_bounded_and_no_prefix_escapes() {
    let only = one("Lean.classExtension", &entry("Lean.classExtension"));
    for limits in [
        DecodeLimits {
            max_bytes: 0,
            ..Default::default()
        },
        DecodeLimits {
            max_objects: 0,
            ..Default::default()
        },
        DecodeLimits {
            max_entries: 0,
            ..Default::default()
        },
    ] {
        assert!(matches!(
            decode(&only, limits),
            Err(DecodeError::Limit { .. })
        ));
    }
    let mut repeated = only.clone();
    let first = repeated[0].entries[0].clone();
    repeated[0].entries.push(first);
    assert!(
        decode(
            &repeated,
            DecodeLimits {
                max_bytes: only[0].entries[0].len(),
                ..Default::default()
            }
        )
        .unwrap_err()
        .is_resource()
    );
    repeated[0].entries.push(vec![]);
    assert!(
        read(&repeated).is_err(),
        "a valid prefix is not a successful result"
    );
}

#[test]
fn extension_names_are_structural_and_duplicate_blocks_refuse() {
    let only = one("Lean.classExtension", &entry("Lean.classExtension"));
    let duplicate = vec![only[0].clone(), only[0].clone()];
    assert!(read(&duplicate).is_err());
    let mut lookalike = only;
    lookalike[0].name = Name::from_components(["Lean.classExtension"]);
    let decoded = read(&lookalike).unwrap();
    assert!(decoded.classes.is_empty());
    assert_eq!(
        decoded.uninterpreted,
        [Name::from_components(["Lean.classExtension"])]
    );
}
