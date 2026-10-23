use super::*;
use crate::region::{OleanView, WalkBudget};
use crate::source_extensions::{self, DecodeLimits};

fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn input() -> ModuleWriteInput<'static> {
    ModuleWriteInput {
        is_module: false,
        imports: &[],
        constants: &[],
        extra_const_names: &[],
    }
}
fn header(version: u8) -> OleanWriteHeader<'static> {
    OleanWriteHeader {
        version,
        flags: 1,
        lean_version: format::PIN_TAG.strip_prefix('v').unwrap(),
        githash: format::PIN_COMMIT,
        base_addr: 2 * format::REGION_ALIGN as u64,
    }
}
fn decoded(bytes: &[u8]) -> source_extensions::SourceExtensions {
    let blocks = OleanView::parse(bytes)
        .unwrap()
        .extension_payloads(WalkBudget::default(), 4 * 1024 * 1024)
        .unwrap();
    source_extensions::decode(&blocks, DecodeLimits::default()).unwrap()
}

#[test]
fn alias_only_artifacts_preserve_pair_direction_order_and_structural_names() {
    let escaped = Name::from_components(["Facade.with.dot", "x"]);
    let numeric = Name::str(Name::num(n("Generated"), 17), "x");
    let metadata = SourceMetadata {
        aliases: vec![
            AliasEntry {
                alias: n("z"),
                declaration: n("Source.x"),
            },
            AliasEntry {
                alias: n("a"),
                declaration: n("Other.y"),
            },
            AliasEntry {
                alias: n("z"),
                declaration: n("Other.y"),
            },
            AliasEntry {
                alias: n("z"),
                declaration: n("Source.x"),
            },
            AliasEntry {
                alias: escaped,
                declaration: n("Source.x"),
            },
            AliasEntry {
                alias: numeric,
                declaration: n("Other.y"),
            },
        ],
        ..SourceMetadata::default()
    };
    for version in [2, 3] {
        let encoded = encode_module_with_source_metadata(
            input(),
            &metadata,
            header(version),
            WriteBudget::default(),
        )
        .unwrap();
        assert_eq!(encoded.report.constants, 0);
        assert_eq!(decoded(&encoded.bytes).aliases, metadata.aliases);
        let again = encode_module_with_source_metadata(
            input(),
            &metadata,
            header(version),
            WriteBudget::default(),
        )
        .unwrap();
        assert_eq!(again.bytes, encoded.bytes);
    }
}

#[test]
fn unqualified_alias_metadata_is_not_lost_in_the_no_namespace_fast_path() {
    let metadata = SourceMetadata {
        aliases: vec![AliasEntry {
            alias: n("x"),
            declaration: n("Source.x"),
        }],
        ..SourceMetadata::default()
    };
    let encoded =
        encode_module_with_source_metadata(input(), &metadata, header(2), WriteBudget::default())
            .unwrap();
    let value = decoded(&encoded.bytes);
    assert_eq!(value.aliases, metadata.aliases);
    assert!(
        value.uninterpreted.is_empty(),
        "a target's namespace is not this module's namespace"
    );
}

#[test]
fn aliases_obey_exact_shared_byte_and_object_budgets() {
    let metadata = SourceMetadata {
        aliases: vec![AliasEntry {
            alias: n("Facade.x"),
            declaration: n("Source.x"),
        }],
        ..SourceMetadata::default()
    };
    let encoded =
        encode_module_with_source_metadata(input(), &metadata, header(2), WriteBudget::default())
            .unwrap();
    let exact = WriteBudget {
        max_bytes: encoded.report.file_bytes,
        max_objects: encoded.report.runtime_objects,
    };
    assert_eq!(
        encode_module_with_source_metadata(input(), &metadata, header(2), exact)
            .unwrap()
            .bytes,
        encoded.bytes
    );
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
            encode_module_with_source_metadata(input(), &metadata, header(2), budget),
            Err(WriteError::Budget { .. })
        ));
    }
    assert_eq!(
        encode_module_with_source_metadata(input(), &metadata, header(2), exact)
            .unwrap()
            .bytes,
        encoded.bytes
    );
}

#[test]
fn anonymous_alias_or_target_is_a_contract_error() {
    for (alias, declaration) in [
        (Name::anonymous(), n("Source.x")),
        (n("x"), Name::anonymous()),
    ] {
        let metadata = SourceMetadata {
            aliases: vec![AliasEntry { alias, declaration }],
            ..SourceMetadata::default()
        };
        assert!(matches!(
            encode_module_with_source_metadata(
                input(),
                &metadata,
                header(2),
                WriteBudget::default()
            ),
            Err(WriteError::Contract { .. })
        ));
    }
}
