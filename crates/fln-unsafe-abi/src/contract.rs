//! Marrow boundary-crate layout contract — **@generated** by `scripts/extract/gen_abi_contract.py`. DO NOT EDIT.
//!
//! Extracted from the pinned Reference header `vendor/lean4-src/src/include/lean/lean.h`
//! (leanprover/lean4 v4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35).
//! Layout partition only (tags, layout constants, struct field tables);
//! the function census is single-sourced in `fln-rt::abi`. Rendered
//! `pub(crate)` for the D3 boundary crate; same inventory, same digest,
//! drift-checked together with the other three artifacts.

// Generated tables are referenced from tests and layout asserts; items that
// are provenance-only (pin binding) may be unused in some build profiles.
#![allow(dead_code)]

/// SHA-256 of `contracts/abi_inventory.json` this module was rendered from.
pub(crate) const INVENTORY_DIGEST: &str = "3eefadc8e70c2fd711a95d47e033d26f7451d6066a06adbf0eedd7790d1018f6";
/// The Reference pin this contract is extracted from.
pub(crate) const PIN_TAG: &str = "v4.32.0";
pub(crate) const PIN_COMMIT: &str = "8c9756b28d64dab099da31a4c09229a9e6a2ef35";
/// SHA-256 of the pinned `lean.h` these constants were derived from.
pub(crate) const LEAN_H_SHA256: &str = "22eed50aa703c4403010fabc12a7231ffa34dc979bd59ca1bfbac13c29a1dad2";

// ---- object tags (lean.h tag block) ------------------------------------
/// `#define LeanMaxCtorTag 243` — vendor/lean4-src/src/include/lean/lean.h:92
pub(crate) const TAG_MAX_CTOR_TAG: u8 = 243;
/// `#define LeanPromise 244` — vendor/lean4-src/src/include/lean/lean.h:93
pub(crate) const TAG_PROMISE: u8 = 244;
/// `#define LeanClosure 245` — vendor/lean4-src/src/include/lean/lean.h:94
pub(crate) const TAG_CLOSURE: u8 = 245;
/// `#define LeanArray 246` — vendor/lean4-src/src/include/lean/lean.h:95
pub(crate) const TAG_ARRAY: u8 = 246;
/// `#define LeanStructArray 247` — vendor/lean4-src/src/include/lean/lean.h:96
pub(crate) const TAG_STRUCT_ARRAY: u8 = 247;
/// `#define LeanScalarArray 248` — vendor/lean4-src/src/include/lean/lean.h:97
pub(crate) const TAG_SCALAR_ARRAY: u8 = 248;
/// `#define LeanString 249` — vendor/lean4-src/src/include/lean/lean.h:98
pub(crate) const TAG_STRING: u8 = 249;
/// `#define LeanMPZ 250` — vendor/lean4-src/src/include/lean/lean.h:99
pub(crate) const TAG_MPZ: u8 = 250;
/// `#define LeanThunk 251` — vendor/lean4-src/src/include/lean/lean.h:100
pub(crate) const TAG_THUNK: u8 = 251;
/// `#define LeanTask 252` — vendor/lean4-src/src/include/lean/lean.h:101
pub(crate) const TAG_TASK: u8 = 252;
/// `#define LeanRef 253` — vendor/lean4-src/src/include/lean/lean.h:102
pub(crate) const TAG_REF: u8 = 253;
/// `#define LeanExternal 254` — vendor/lean4-src/src/include/lean/lean.h:103
pub(crate) const TAG_EXTERNAL: u8 = 254;
/// `#define LeanReserved 255` — vendor/lean4-src/src/include/lean/lean.h:104
pub(crate) const TAG_RESERVED: u8 = 255;

// ---- layout constants ---------------------------------------------------
/// `#define LEAN_CLOSURE_MAX_ARGS` — vendor/lean4-src/src/include/lean/lean.h:31
pub(crate) const CLOSURE_MAX_ARGS: usize = 16;
/// `#define LEAN_OBJECT_SIZE_DELTA` — vendor/lean4-src/src/include/lean/lean.h:32
pub(crate) const OBJECT_SIZE_DELTA: usize = 8;
/// `#define LEAN_MAX_SMALL_OBJECT_SIZE` — vendor/lean4-src/src/include/lean/lean.h:33
pub(crate) const MAX_SMALL_OBJECT_SIZE: usize = 4096;
/// `#define LEAN_MAX_CTOR_FIELDS` — vendor/lean4-src/src/include/lean/lean.h:106
pub(crate) const MAX_CTOR_FIELDS: usize = 256;
/// `#define LEAN_MAX_CTOR_SCALARS_SIZE` — vendor/lean4-src/src/include/lean/lean.h:107
pub(crate) const MAX_CTOR_SCALARS_SIZE: usize = 1024;
/// `#define LEAN_TASK_STATE_WAITING` — vendor/lean4-src/src/include/lean/lean.h:1341
pub(crate) const TASK_STATE_WAITING: usize = 0;
/// `#define LEAN_TASK_STATE_RUNNING` — vendor/lean4-src/src/include/lean/lean.h:1342
pub(crate) const TASK_STATE_RUNNING: usize = 1;
/// `#define LEAN_TASK_STATE_FINISHED` — vendor/lean4-src/src/include/lean/lean.h:1343
pub(crate) const TASK_STATE_FINISHED: usize = 2;
/// `#define LEAN_MAX_SMALL_NAT (SIZE_MAX >> 1)` — vendor/lean4-src/src/include/lean/lean.h:1380 (expression; platform-dependent width)
pub(crate) const MAX_SMALL_NAT_EXPR: &str = "(SIZE_MAX >> 1)";
/// `#define LEAN_MAX_SMALL_INT (sizeof(void*) == 8 ? INT_MAX : (INT_MAX >> 1))` — vendor/lean4-src/src/include/lean/lean.h:1588 (expression; platform-dependent width)
pub(crate) const MAX_SMALL_INT_EXPR: &str = "(sizeof(void*) == 8 ? INT_MAX : (INT_MAX >> 1))";
/// `#define LEAN_MIN_SMALL_INT (sizeof(void*) == 8 ? INT_MIN : (INT_MIN >> 1))` — vendor/lean4-src/src/include/lean/lean.h:1589 (expression; platform-dependent width)
pub(crate) const MIN_SMALL_INT_EXPR: &str = "(sizeof(void*) == 8 ? INT_MIN : (INT_MIN >> 1))";

// ---- object layout tables ----------------------------------------------
/// One C struct field of the object model, with provenance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct FieldSpec {
    pub(crate) name: &'static str,
    pub(crate) c_type: &'static str,
    /// bit width when the field is a C bitfield
    pub(crate) bits: Option<u8>,
    /// `Some("[]")`/`Some("[N]")` for array fields (flexible arrays are `[]`)
    pub(crate) array: Option<&'static str>,
    /// 1-based line in `vendor/lean4-src/src/include/lean/lean.h`
    pub(crate) line: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct StructSpec {
    pub(crate) name: &'static str,
    pub(crate) fields: &'static [FieldSpec],
    /// 1-based start line in `vendor/lean4-src/src/include/lean/lean.h`
    pub(crate) line: u32,
}

/// `lean_object` — vendor/lean4-src/src/include/lean/lean.h:143-148
pub(crate) const LEAN_OBJECT_FIELDS: &[FieldSpec] = &[
    FieldSpec { name: "m_rc", c_type: "int", bits: None, array: None, line: 144 },
    FieldSpec { name: "m_cs_sz", c_type: "unsigned", bits: Some(16), array: None, line: 145 },
    FieldSpec { name: "m_other", c_type: "unsigned", bits: Some(8), array: None, line: 146 },
    FieldSpec { name: "m_tag", c_type: "unsigned", bits: Some(8), array: None, line: 147 },
];
/// `lean_ctor_object` — vendor/lean4-src/src/include/lean/lean.h:182-185
pub(crate) const LEAN_CTOR_OBJECT_FIELDS: &[FieldSpec] = &[
    FieldSpec { name: "m_header", c_type: "lean_object", bits: None, array: None, line: 183 },
    FieldSpec { name: "m_objs", c_type: "lean_object *", bits: None, array: Some("[]"), line: 184 },
];
/// `lean_array_object` — vendor/lean4-src/src/include/lean/lean.h:188-193
pub(crate) const LEAN_ARRAY_OBJECT_FIELDS: &[FieldSpec] = &[
    FieldSpec { name: "m_header", c_type: "lean_object", bits: None, array: None, line: 189 },
    FieldSpec { name: "m_size", c_type: "size_t", bits: None, array: None, line: 190 },
    FieldSpec { name: "m_capacity", c_type: "size_t", bits: None, array: None, line: 191 },
    FieldSpec { name: "m_data", c_type: "lean_object *", bits: None, array: Some("[]"), line: 192 },
];
/// `lean_sarray_object` — vendor/lean4-src/src/include/lean/lean.h:196-201
pub(crate) const LEAN_SARRAY_OBJECT_FIELDS: &[FieldSpec] = &[
    FieldSpec { name: "m_header", c_type: "lean_object", bits: None, array: None, line: 197 },
    FieldSpec { name: "m_size", c_type: "size_t", bits: None, array: None, line: 198 },
    FieldSpec { name: "m_capacity", c_type: "size_t", bits: None, array: None, line: 199 },
    FieldSpec { name: "m_data", c_type: "uint8_t", bits: None, array: Some("[]"), line: 200 },
];
/// `lean_string_object` — vendor/lean4-src/src/include/lean/lean.h:203-209
pub(crate) const LEAN_STRING_OBJECT_FIELDS: &[FieldSpec] = &[
    FieldSpec { name: "m_header", c_type: "lean_object", bits: None, array: None, line: 204 },
    FieldSpec { name: "m_size", c_type: "size_t", bits: None, array: None, line: 205 },
    FieldSpec { name: "m_capacity", c_type: "size_t", bits: None, array: None, line: 206 },
    FieldSpec { name: "m_length", c_type: "size_t", bits: None, array: None, line: 207 },
    FieldSpec { name: "m_data", c_type: "char", bits: None, array: Some("[]"), line: 208 },
];
/// `lean_closure_object` — vendor/lean4-src/src/include/lean/lean.h:211-217
pub(crate) const LEAN_CLOSURE_OBJECT_FIELDS: &[FieldSpec] = &[
    FieldSpec { name: "m_header", c_type: "lean_object", bits: None, array: None, line: 212 },
    FieldSpec { name: "m_fun", c_type: "void *", bits: None, array: None, line: 213 },
    FieldSpec { name: "m_arity", c_type: "uint16_t", bits: None, array: None, line: 214 },
    FieldSpec { name: "m_num_fixed", c_type: "uint16_t", bits: None, array: None, line: 215 },
    FieldSpec { name: "m_objs", c_type: "lean_object *", bits: None, array: Some("[]"), line: 216 },
];
/// `lean_ref_object` — vendor/lean4-src/src/include/lean/lean.h:219-222
pub(crate) const LEAN_REF_OBJECT_FIELDS: &[FieldSpec] = &[
    FieldSpec { name: "m_header", c_type: "lean_object", bits: None, array: None, line: 220 },
    FieldSpec { name: "m_value", c_type: "lean_object *", bits: None, array: None, line: 221 },
];
/// `lean_thunk_object` — vendor/lean4-src/src/include/lean/lean.h:224-228
pub(crate) const LEAN_THUNK_OBJECT_FIELDS: &[FieldSpec] = &[
    FieldSpec { name: "m_header", c_type: "lean_object", bits: None, array: None, line: 225 },
    FieldSpec { name: "m_value", c_type: "_Atomic(lean_object *)", bits: None, array: None, line: 226 },
    FieldSpec { name: "m_closure", c_type: "_Atomic(lean_object *)", bits: None, array: None, line: 227 },
];
/// `lean_task_imp` — vendor/lean4-src/src/include/lean/lean.h:234-243
pub(crate) const LEAN_TASK_IMP_FIELDS: &[FieldSpec] = &[
    FieldSpec { name: "m_closure", c_type: "lean_object *", bits: None, array: None, line: 235 },
    FieldSpec { name: "m_head_dep", c_type: "struct lean_task *", bits: None, array: None, line: 236 },
    FieldSpec { name: "m_next_dep", c_type: "struct lean_task *", bits: None, array: None, line: 237 },
    FieldSpec { name: "m_prio", c_type: "unsigned", bits: None, array: None, line: 238 },
    FieldSpec { name: "m_canceled", c_type: "uint8_t", bits: None, array: None, line: 239 },
    FieldSpec { name: "m_keep_alive", c_type: "uint8_t", bits: None, array: None, line: 241 },
    FieldSpec { name: "m_deleted", c_type: "uint8_t", bits: None, array: None, line: 242 },
];
/// `lean_task_object` — vendor/lean4-src/src/include/lean/lean.h:296-300
pub(crate) const LEAN_TASK_OBJECT_FIELDS: &[FieldSpec] = &[
    FieldSpec { name: "m_header", c_type: "lean_object", bits: None, array: None, line: 297 },
    FieldSpec { name: "m_value", c_type: "_Atomic(lean_object *)", bits: None, array: None, line: 298 },
    FieldSpec { name: "m_imp", c_type: "lean_task_imp *", bits: None, array: None, line: 299 },
];
/// `lean_promise_object` — vendor/lean4-src/src/include/lean/lean.h:302-305
pub(crate) const LEAN_PROMISE_OBJECT_FIELDS: &[FieldSpec] = &[
    FieldSpec { name: "m_header", c_type: "lean_object", bits: None, array: None, line: 303 },
    FieldSpec { name: "m_result", c_type: "lean_task_object *", bits: None, array: None, line: 304 },
];
/// `lean_external_class` — vendor/lean4-src/src/include/lean/lean.h:310-313
pub(crate) const LEAN_EXTERNAL_CLASS_FIELDS: &[FieldSpec] = &[
    FieldSpec { name: "m_finalize", c_type: "lean_external_finalize_proc", bits: None, array: None, line: 311 },
    FieldSpec { name: "m_foreach", c_type: "lean_external_foreach_proc", bits: None, array: None, line: 312 },
];
/// `lean_external_object` — vendor/lean4-src/src/include/lean/lean.h:318-322
pub(crate) const LEAN_EXTERNAL_OBJECT_FIELDS: &[FieldSpec] = &[
    FieldSpec { name: "m_header", c_type: "lean_object", bits: None, array: None, line: 319 },
    FieldSpec { name: "m_class", c_type: "lean_external_class *", bits: None, array: None, line: 320 },
    FieldSpec { name: "m_data", c_type: "void *", bits: None, array: None, line: 321 },
];

/// Every object-model struct, in contract order.
pub(crate) const OBJECT_STRUCTS: &[StructSpec] = &[
    StructSpec { name: "lean_object", fields: LEAN_OBJECT_FIELDS, line: 143 },
    StructSpec { name: "lean_ctor_object", fields: LEAN_CTOR_OBJECT_FIELDS, line: 182 },
    StructSpec { name: "lean_array_object", fields: LEAN_ARRAY_OBJECT_FIELDS, line: 188 },
    StructSpec { name: "lean_sarray_object", fields: LEAN_SARRAY_OBJECT_FIELDS, line: 196 },
    StructSpec { name: "lean_string_object", fields: LEAN_STRING_OBJECT_FIELDS, line: 203 },
    StructSpec { name: "lean_closure_object", fields: LEAN_CLOSURE_OBJECT_FIELDS, line: 211 },
    StructSpec { name: "lean_ref_object", fields: LEAN_REF_OBJECT_FIELDS, line: 219 },
    StructSpec { name: "lean_thunk_object", fields: LEAN_THUNK_OBJECT_FIELDS, line: 224 },
    StructSpec { name: "lean_task_imp", fields: LEAN_TASK_IMP_FIELDS, line: 234 },
    StructSpec { name: "lean_task_object", fields: LEAN_TASK_OBJECT_FIELDS, line: 296 },
    StructSpec { name: "lean_promise_object", fields: LEAN_PROMISE_OBJECT_FIELDS, line: 302 },
    StructSpec { name: "lean_external_class", fields: LEAN_EXTERNAL_CLASS_FIELDS, line: 310 },
    StructSpec { name: "lean_external_object", fields: LEAN_EXTERNAL_OBJECT_FIELDS, line: 318 },
];

