use super::*;
use crate::region::{OleanView, WalkBudget};
use crate::source_extensions::{self, DecodeLimits};

fn n(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn rows() -> Vec<StructureEntry> {
    let field = |name: &str, parent: Option<&str>, binder_info| StructureField {
        name: n(name),
        projection: n(&format!("Child.{name}")),
        subobject: parent.map(n),
        binder_info,
        auto_param: None,
    };
    vec![
        StructureEntry {
            name: n("Child"),
            fields: vec![
                field("toLeft", Some("Left"), BinderInfo::Default),
                field("toRight", Some("Right"), BinderInfo::InstImplicit),
                field("z", None, BinderInfo::Implicit),
                StructureField {
                    auto_param: Some(Expr::const_(n("Default.tactic"), vec![])),
                    ..field("a", None, BinderInfo::StrictImplicit)
                },
            ],
            parents: vec![
                StructureParent {
                    name: n("Right"),
                    subobject: true,
                    projection: n("Child.toRight"),
                },
                StructureParent {
                    name: n("Left"),
                    subobject: true,
                    projection: n("Child.toLeft"),
                },
                StructureParent {
                    name: n("Ancestor"),
                    subobject: false,
                    projection: n("Child.toAncestor"),
                },
            ],
        },
        StructureEntry {
            name: Name::str(Name::num(n("Generated"), 7), "Empty"),
            fields: vec![],
            parents: vec![],
        },
    ]
}

fn encode(
    structures: Vec<StructureEntry>,
    version: u8,
    budget: WriteBudget,
) -> WResult<EncodedModule> {
    encode_module_with_source_metadata(
        ModuleWriteInput {
            is_module: false,
            imports: &[],
            constants: &[],
            extra_const_names: &[],
        },
        &SourceMetadata {
            structures,
            ..SourceMetadata::default()
        },
        OleanWriteHeader {
            version,
            flags: 1,
            lean_version: format::PIN_TAG.strip_prefix('v').unwrap(),
            githash: format::PIN_COMMIT,
            base_addr: 2 * format::REGION_ALIGN as u64,
        },
        budget,
    )
}

#[test]
fn sorted_lookup_indexes_preserve_physical_fields_and_authored_parent_order() {
    for &version in format::OLEAN_ACCEPTED_VERSIONS {
        let mut expected = rows();
        let encoded = encode(expected.clone(), version, WriteBudget::default()).unwrap();
        let view = OleanView::parse(&encoded.bytes).unwrap();
        let blocks = view
            .extension_payloads(WalkBudget::default(), 1 << 20)
            .unwrap();
        let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
        expected.sort_by(|left, right| left.name.quick_cmp(&right.name));
        assert_eq!(decoded.structures, expected);
        assert!(
            decoded.uninterpreted.is_empty(),
            "the private extension uses a numeric zero Name component"
        );
        assert_eq!(
            encode(rows(), version, WriteBudget::default())
                .unwrap()
                .bytes,
            encoded.bytes
        );
    }
}

#[test]
fn structure_payloads_obey_exact_shared_object_and_byte_limits() {
    for &version in format::OLEAN_ACCEPTED_VERSIONS {
        let encoded = encode(rows(), version, WriteBudget::default()).unwrap();
        let exact = WriteBudget {
            max_bytes: encoded.report.file_bytes,
            max_objects: encoded.report.runtime_objects,
        };
        assert_eq!(encode(rows(), version, exact).unwrap().bytes, encoded.bytes);
        for budget in [
            WriteBudget {
                max_bytes: exact.max_bytes - 1,
                ..exact
            },
            WriteBudget {
                max_objects: exact.max_objects - 1,
                ..exact
            },
        ] {
            assert!(matches!(
                encode(rows(), version, budget),
                Err(WriteError::Budget { .. })
            ));
        }
    }
}

#[test]
fn malformed_field_identities_and_parent_relationships_are_refused() {
    let good = rows().remove(0);
    for case in 0..10 {
        let mut bad = good.clone();
        match case {
            0 => bad.name = Name::anonymous(),
            1 => bad.fields[0].name = n("invalid.qualified.label"),
            2 => bad.fields[0].projection = Name::anonymous(),
            3 => bad.fields[1].name = bad.fields[0].name.clone(),
            4 => bad.fields[1].projection = bad.fields[0].projection.clone(),
            5 => bad.parents.push(bad.parents[0].clone()),
            6 => bad.parents[0].projection = n("Child.notAField"),
            7 => bad.parents[0].subobject = false,
            8 => bad.fields[0].subobject = Some(bad.name.clone()),
            _ => bad.fields[0].subobject = bad.fields[1].subobject.clone(),
        }
        assert!(
            matches!(
                encode(vec![bad], 2, WriteBudget::default()),
                Err(WriteError::Contract { .. })
            ),
            "case {case}"
        );
    }
    assert!(matches!(
        encode(vec![good.clone(), good], 2, WriteBudget::default()),
        Err(WriteError::Contract { .. })
    ));
}
