//! Structural laws over the generated `.olean`/`.ilean` format contract
//! (`fln_olean::format`, bead franken_lean-53v). The header layout must be
//! internally coherent (contiguous offsets, packed size), and TRIPWIRE
//! expectations — independently recorded from the pin — kill a seeded mutation
//! of the generated constants by a named test.
//!
//! **What verifies `INVENTORY_DIGEST` is not here** (bead `franken_lean-pnav`).
//! [`pin_binding_is_present`] asserts its *shape* (64 characters), never that it
//! matches `contracts/olean_inventory.json`. That binding lives in
//! `scripts/e2e/contract_drift.sh`, registered in `scripts/check.sh`.

#![forbid(unsafe_code)]

use fln_olean::format;

#[test]
fn header_fields_are_contiguous_and_packed() {
    let fields = format::OLEAN_HEADER_FIELDS;
    assert!(fields.len() >= 6, "header implausibly small");
    let mut offset = 0;
    for f in fields {
        assert_eq!(
            f.offset, offset,
            "field {} not contiguous (offset {}, expected {})",
            f.name, f.offset, offset
        );
        offset += f.size;
    }
    assert_eq!(
        offset,
        format::OLEAN_HEADER_SIZE,
        "field sizes must sum to the packed header size"
    );
    let last = fields.last().expect("header nonempty (asserted above)");
    assert_eq!(last.size, 0, "last field must be the flexible data member");
    assert!(
        fields[..fields.len() - 1].iter().all(|f| f.size > 0),
        "only the trailing member may be flexible"
    );
}

#[test]
fn tripwire_header_shape_at_the_pin() {
    // Independently recorded from module.cpp at the pin.
    assert_eq!(&format::OLEAN_MAGIC, b"olean");
    assert_eq!(format::OLEAN_HEADER_SIZE, 88);
    assert_eq!(format::OLEAN_ACCEPTED_VERSIONS, &[2, 3]);
    assert_eq!(format::REGION_ALIGN, 1 << 16);
    assert_eq!(format::ILEAN_VERSION, 5);
    let names: Vec<&str> = format::OLEAN_HEADER_FIELDS.iter().map(|f| f.name).collect();
    assert_eq!(
        names,
        [
            "marker",
            "version",
            "flags",
            "lean_version",
            "githash",
            "base_addr",
            "data"
        ]
    );
}

#[test]
fn module_data_field_order_is_the_wire_layout() {
    // TRIPWIRE: the compacted object graph is the wire format, so declaration
    // order is layout. Independently recorded from Environment.lean at the pin.
    let names: Vec<&str> = format::MODULE_DATA_FIELDS.iter().map(|f| f.name).collect();
    assert_eq!(
        names,
        [
            "isModule",
            "imports",
            "constNames",
            "constants",
            "extraConstNames",
            "entries"
        ]
    );
    let import_names: Vec<&str> = format::IMPORT_FIELDS.iter().map(|f| f.name).collect();
    assert_eq!(names.len(), 6);
    assert_eq!(
        import_names,
        ["module", "importAll", "isExported", "isMeta"]
    );
    assert_eq!(
        format::IMPORT_FIELDS[1].default,
        Some("false"),
        "importAll defaults to false at the pin"
    );
}

#[test]
fn ilean_contract_is_versioned_json() {
    let names: Vec<&str> = format::ILEAN_FIELDS.iter().map(|f| f.name).collect();
    assert_eq!(
        names,
        ["version", "module", "directImports", "references", "decls"]
    );
    assert_eq!(format::ILEAN_FIELDS[0].default, Some("5"));
}

#[test]
fn pin_binding_is_present() {
    assert_eq!(format::PIN_COMMIT.len(), 40);
    assert!(format::PIN_COMMIT.chars().all(|c| c.is_ascii_hexdigit()));
    assert_eq!(format::INVENTORY_DIGEST.len(), 64);
    assert_eq!(format::PIN_TAG, "v4.32.0");
}
