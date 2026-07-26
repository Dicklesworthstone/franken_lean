//! Structural laws over the generated ABI contract (`fln_rt::abi`, bead
//! franken_lean-53v). These tests are the Rust-side seat of the drift tripwire:
//! the generated module must stay internally coherent, and a handful of
//! independently-recorded expectations (marked TRIPWIRE) exist so that a seeded
//! mutation of the generated constants is killed by a named test even before
//! the extractor's `--check` lane runs.
//!
//! **What verifies the digests is not here** (bead `franken_lean-pnav`).
//! [`pin_binding_is_present`] asserts *presence and shape* — that `PIN_COMMIT`
//! is 40 hex characters and the two digests are 64 — and deliberately not that
//! any of them matches its content. The binding against the pin lives in
//! `scripts/e2e/contract_drift.sh`, which regenerates from the vendored header
//! via `gen_abi_contract.py --check` and carries seeded mutants it must kill;
//! it runs weekly and on demand in `.github/workflows/contract-drift.yml`. Read
//! the name literally: *present*, not *verified*.

#![forbid(unsafe_code)]

use fln_rt::abi;

#[test]
fn tags_are_distinct_and_specials_are_contiguous() {
    let specials = [
        abi::TAG_PROMISE,
        abi::TAG_CLOSURE,
        abi::TAG_ARRAY,
        abi::TAG_STRUCT_ARRAY,
        abi::TAG_SCALAR_ARRAY,
        abi::TAG_STRING,
        abi::TAG_MPZ,
        abi::TAG_THUNK,
        abi::TAG_TASK,
        abi::TAG_REF,
        abi::TAG_EXTERNAL,
        abi::TAG_RESERVED,
    ];
    for (i, a) in specials.iter().enumerate() {
        for b in specials.iter().skip(i + 1) {
            assert_ne!(a, b, "special tags must be distinct");
        }
        assert!(
            *a > abi::TAG_MAX_CTOR_TAG,
            "special tag {a} must lie above the constructor range"
        );
    }
    let mut sorted = specials;
    sorted.sort_unstable();
    for pair in sorted.windows(2) {
        assert_eq!(
            pair[1] - pair[0],
            1,
            "special tags must form a contiguous run"
        );
    }
    // TRIPWIRE (independently recorded from lean.h at the pin): the special
    // range starts right after the constructor range and ends at 255.
    assert_eq!(abi::TAG_MAX_CTOR_TAG, 243);
    assert_eq!(abi::TAG_CLOSURE, 245);
    assert_eq!(abi::TAG_RESERVED, 255);
}

#[test]
fn object_header_is_the_documented_bitfield_packing() {
    let header = abi::LEAN_OBJECT_FIELDS;
    assert_eq!(header.len(), 4, "lean_object has exactly four fields");
    assert_eq!(header[0].name, "m_rc");
    assert_eq!(header[0].bits, None, "m_rc is a plain int, not a bitfield");
    assert_eq!(header[1].name, "m_cs_sz");
    assert_eq!(header[1].bits, Some(16));
    assert_eq!(header[2].name, "m_other");
    assert_eq!(header[2].bits, Some(8));
    assert_eq!(header[3].name, "m_tag");
    assert_eq!(header[3].bits, Some(8));
}

#[test]
fn every_object_struct_is_nonempty_with_monotone_lines() {
    assert!(!abi::OBJECT_STRUCTS.is_empty());
    for s in abi::OBJECT_STRUCTS {
        assert!(!s.fields.is_empty(), "struct {} has no fields", s.name);
        for f in s.fields {
            assert!(
                f.line > s.line,
                "field {}::{} line {} not inside struct starting at {}",
                s.name,
                f.name,
                f.line,
                s.line
            );
        }
    }
}

#[test]
fn census_is_sorted_nonempty_and_ownership_coherent() {
    let census = abi::FUNCTION_CENSUS;
    assert!(
        census.len() > 600,
        "census implausibly small: {}",
        census.len()
    );
    for pair in census.windows(2) {
        assert!(
            (pair[0].name, pair[0].line) < (pair[1].name, pair[1].line),
            "census must be strictly sorted by (name, line): {} vs {}",
            pair[0].name,
            pair[1].name
        );
    }
    for f in census {
        assert!(f.name.starts_with("lean"), "non-lean symbol {}", f.name);
        for p in f.params {
            let is_obj = matches!(
                p.ownership,
                abi::Ownership::OwnedArg
                    | abi::Ownership::BorrowedArg
                    | abi::Ownership::UniqueArg
                    | abi::Ownership::RawObject
            );
            assert_eq!(
                is_obj,
                p.c_type.contains("lean_obj") || p.c_type.contains("lean_object"),
                "{}: param ownership {:?} inconsistent with type {:?}",
                f.name,
                p.ownership,
                p.c_type
            );
        }
    }
}

#[test]
fn tripwire_known_symbols_have_recorded_shapes() {
    // Independently recorded from lean.h at the pin: these three symbols and
    // their ownership signatures. A perturbed census row dies here by name.
    let find = |name: &str| {
        let found = abi::FUNCTION_CENSUS.iter().find(|f| f.name == name);
        assert!(found.is_some(), "census lost {name}");
        found.expect("asserted above")
    };
    let push = find("lean_string_push");
    assert_eq!(push.linkage, abi::Linkage::Export);
    assert_eq!(push.ret_ownership, abi::Ownership::OwnedRes);
    assert_eq!(push.params.len(), 2);
    assert_eq!(push.params[0].ownership, abi::Ownership::OwnedArg);
    assert_eq!(push.params[1].ownership, abi::Ownership::Value);

    let mark = find("lean_mark_persistent");
    assert_eq!(mark.linkage, abi::Linkage::Export);

    let is_scalar = find("lean_is_scalar");
    assert_eq!(is_scalar.linkage, abi::Linkage::Inline);
}

#[test]
fn layout_constants_are_recorded() {
    // TRIPWIRE: independently recorded from lean.h at the pin.
    //
    // Scope, stated because the word "independently" invites a stronger reading
    // (bead `franken_lean-pnav`): these values were transcribed from what the
    // generator emitted, so this kills a LATER regeneration bug — a constant that
    // moves without the pin moving. It cannot catch a value that was already wrong
    // at extraction time, because the transcription came from the same source. The
    // check against the pin itself is `scripts/e2e/contract_drift.sh`.
    assert_eq!(abi::CLOSURE_MAX_ARGS, 16);
    assert_eq!(abi::OBJECT_SIZE_DELTA, 8);
    assert_eq!(abi::MAX_SMALL_OBJECT_SIZE, 4096);
    assert_eq!(abi::MAX_CTOR_FIELDS, 256);
    assert_eq!(abi::MAX_CTOR_SCALARS_SIZE, 1024);
    assert!(abi::MAX_SMALL_NAT_EXPR.contains("SIZE_MAX"));
}

#[test]
fn pin_binding_is_present() {
    assert_eq!(abi::PIN_COMMIT.len(), 40);
    assert!(abi::PIN_COMMIT.chars().all(|c| c.is_ascii_hexdigit()));
    assert_eq!(abi::LEAN_H_SHA256.len(), 64);
    assert_eq!(abi::INVENTORY_DIGEST.len(), 64);
    assert_eq!(abi::PIN_TAG, "v4.32.0");
}
