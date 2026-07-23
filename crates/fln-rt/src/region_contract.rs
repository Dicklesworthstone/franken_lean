//! Marrow's region-envelope contract partition — **@generated** by
//! `scripts/extract/gen_olean_contract.py`. DO NOT EDIT.
//!
//! Extracted from the pinned Reference (leanprover/lean4 v4.32.0,
//! commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35). Envelope subset only (magic, header
//! fields, accepted versions, region alignment); the full format
//! contract is single-sourced in `fln-olean::format`. Rendered
//! `pub(crate)` for the region engine; same inventory, same digest,
//! drift-checked together with the other three artifacts.

// Provenance-only items may be unused in some build profiles.
#![allow(dead_code)]

/// SHA-256 of `contracts/olean_inventory.json` this partition was rendered from.
pub(crate) const INVENTORY_DIGEST: &str = "901a2970a31a945a05bbf5e6f3bcb13fe01016a16930bcd654879403076437f8";
pub(crate) const PIN_TAG: &str = "v4.32.0";
pub(crate) const PIN_COMMIT: &str = "8c9756b28d64dab099da31a4c09229a9e6a2ef35";

/// `.olean` magic bytes — vendor/lean4-src/src/library/module.cpp:107
pub(crate) const OLEAN_MAGIC: [u8; 5] = *b"olean";
/// Fixed header size in bytes on LP64 (verified against the pin's static_assert).
pub(crate) const OLEAN_HEADER_SIZE: usize = 88;
/// Format versions the pinned loader accepts — vendor/lean4-src/src/library/module.cpp:492
pub(crate) const OLEAN_ACCEPTED_VERSIONS: &[u8] = &[2, 3];
/// Region payload/base alignment — vendor/lean4-src/src/library/module.cpp:273
pub(crate) const REGION_ALIGN: usize = 65536;

/// One fixed header field: byte offset, byte size, and provenance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct HeaderField {
    pub(crate) name: &'static str,
    pub(crate) c_type: &'static str,
    pub(crate) offset: usize,
    /// 0 marks the trailing flexible array member
    pub(crate) size: usize,
    /// 1-based line in `vendor/lean4-src/src/library/module.cpp`
    pub(crate) line: u32,
}

/// The on-disk `olean_header` — vendor/lean4-src/src/library/module.cpp:107, in file order.
pub(crate) const OLEAN_HEADER_FIELDS: &[HeaderField] = &[
    HeaderField { name: "marker", c_type: "char[5]", offset: 0, size: 5, line: 109 },
    HeaderField { name: "version", c_type: "uint8_t", offset: 5, size: 1, line: 113 },
    HeaderField { name: "flags", c_type: "uint8_t", offset: 6, size: 1, line: 117 },
    HeaderField { name: "lean_version", c_type: "char[33]", offset: 7, size: 33, line: 127 },
    HeaderField { name: "githash", c_type: "char[40]", offset: 40, size: 40, line: 130 },
    HeaderField { name: "base_addr", c_type: "size_t", offset: 80, size: 8, line: 132 },
    HeaderField { name: "data", c_type: "size_t[]", offset: 88, size: 0, line: 141 },
];

