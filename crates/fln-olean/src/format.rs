//! Grimoire's `.olean`/`.ilean` format constants — **@generated** by
//! `scripts/extract/gen_olean_contract.py`. DO NOT EDIT.
//!
//! Extracted from the pinned Reference (leanprover/lean4 v4.32.0,
//! commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35): the olean writer/loader, the
//! compactor, and the Lean-side module structures. The extraction law (plan
//! Appendix B, Rule D5/D9): format constants are derived, never remembered.
//! Header offsets follow the LP64 law (`size_t` = 8 bytes) and are verified
//! against the pin's own packing `static_assert` at extraction time.

/// SHA-256 of `contracts/olean_inventory.json`, the canonical inventory this
/// module was rendered from.
pub const INVENTORY_DIGEST: &str = "ecd0f18e64358bb69d1ce3e2880d08f5553d2f3789df46d531988cbfe7b577dc";
pub const PIN_TAG: &str = "v4.32.0";
pub const PIN_COMMIT: &str = "8c9756b28d64dab099da31a4c09229a9e6a2ef35";

/// `.olean` magic bytes — vendor/lean4-src/src/library/module.cpp:107
pub const OLEAN_MAGIC: [u8; 5] = *b"olean";
/// Fixed header size in bytes on LP64 (verified against the pin's static_assert).
pub const OLEAN_HEADER_SIZE: usize = 88;
/// Format versions the pinned loader accepts — vendor/lean4-src/src/library/module.cpp:492
pub const OLEAN_ACCEPTED_VERSIONS: &[u8] = &[2, 3];
/// Region payload/base alignment — vendor/lean4-src/src/library/module.cpp:273
pub const REGION_ALIGN: usize = 65536;
/// `.ilean` JSON format version — vendor/lean4-src/src/Lean/Server/References.lean:208
pub const ILEAN_VERSION: u64 = 5;

/// One fixed header field: byte offset, byte size, and provenance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HeaderField {
    pub name: &'static str,
    pub c_type: &'static str,
    pub offset: usize,
    /// 0 marks the trailing flexible array member
    pub size: usize,
    /// 1-based line in `vendor/lean4-src/src/library/module.cpp`
    pub line: u32,
}

/// The on-disk `olean_header` — vendor/lean4-src/src/library/module.cpp:107, in file order.
pub const OLEAN_HEADER_FIELDS: &[HeaderField] = &[
    HeaderField { name: "marker", c_type: "char[5]", offset: 0, size: 5, line: 109 },
    HeaderField { name: "version", c_type: "uint8_t", offset: 5, size: 1, line: 113 },
    HeaderField { name: "flags", c_type: "uint8_t", offset: 6, size: 1, line: 117 },
    HeaderField { name: "lean_version", c_type: "char[33]", offset: 7, size: 33, line: 127 },
    HeaderField { name: "githash", c_type: "char[40]", offset: 40, size: 40, line: 130 },
    HeaderField { name: "base_addr", c_type: "size_t", offset: 80, size: 8, line: 132 },
    HeaderField { name: "data", c_type: "size_t[]", offset: 88, size: 0, line: 141 },
];

/// One Lean-side structure field (name, type, default) with provenance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LeanField {
    pub name: &'static str,
    pub lean_type: &'static str,
    pub default: Option<&'static str>,
    pub line: u32,
}

/// `structure ModuleData` — vendor/lean4-src/src/Lean/Environment.lean:109, in declaration order
/// (the compacted object graph is the wire format; field order is layout).
pub const MODULE_DATA_FIELDS: &[LeanField] = &[
    LeanField { name: "isModule", lean_type: "Bool", default: None, line: 111 },
    LeanField { name: "imports", lean_type: "Array Import", default: None, line: 112 },
    LeanField { name: "constNames", lean_type: "Array Name", default: None, line: 119 },
    LeanField { name: "constants", lean_type: "Array ConstantInfo", default: None, line: 120 },
    LeanField { name: "extraConstNames", lean_type: "Array Name", default: None, line: 126 },
    LeanField { name: "entries", lean_type: "Array (Name × Array EnvExtensionEntry)", default: None, line: 127 },
];

/// `structure Import` — vendor/lean4-src/src/Lean/Setup.lean:25, in declaration order
/// (the compacted object graph is the wire format; field order is layout).
pub const IMPORT_FIELDS: &[LeanField] = &[
    LeanField { name: "module", lean_type: "Name", default: None, line: 26 },
    LeanField { name: "importAll", lean_type: "Bool", default: Some("false"), line: 28 },
    LeanField { name: "isExported", lean_type: "Bool", default: Some("true"), line: 30 },
    LeanField { name: "isMeta", lean_type: "Bool", default: Some("false"), line: 32 },
];

/// `structure Ilean` — vendor/lean4-src/src/Lean/Server/References.lean:206, in declaration order
/// (the compacted object graph is the wire format; field order is layout).
pub const ILEAN_FIELDS: &[LeanField] = &[
    LeanField { name: "version", lean_type: "Nat", default: Some("5"), line: 208 },
    LeanField { name: "module", lean_type: "Name", default: None, line: 210 },
    LeanField { name: "directImports", lean_type: "Array Lsp.ImportInfo", default: None, line: 212 },
    LeanField { name: "references", lean_type: "Lsp.ModuleRefs", default: None, line: 214 },
    LeanField { name: "decls", lean_type: "Lsp.Decls", default: None, line: 216 },
];

