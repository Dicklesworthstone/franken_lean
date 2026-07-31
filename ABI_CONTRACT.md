# ABI_CONTRACT.md — the `lean_object` ABI at the pin

> **@generated** by `scripts/extract/gen_abi_contract.py` (Rule D5/D9, plan Appendix B). DO NOT EDIT.
> Layout constants are derived, never remembered; regenerate with the script.
>
> pin: `leanprover/lean4` `v4.32.0` commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
> — tree `ba16913719a2f6a15a826918fbe6ba9dd5413e91`
> — the tag and commit above are **transcribed from `SUITE.lock`** and this
>   extractor verifies neither. The **tree is established at the producer**:
>   every run, before anything is rendered, invokes the one predicate in this
>   repository that establishes it — `scripts/evidence.py vendor-binding`,
>   the same one `scripts/verify_vendor_tree.sh` runs lane-side — which
>   recomputes the staged `vendor/lean4-src` tree and refuses unless it equals
>   the pinned tree. The extractor calls that predicate rather than
>   reimplementing tree hashing, so no second copy of it exists.
> — the **outcome is typed on stderr and is deliberately NOT rendered here**,
>   in three states: `established`; `inconclusive`, where the repository
>   `.git` is absent or is not a directory so the predicate cannot run at all
>   — an FL-INV-07 environment fault, never a verdict about the tree and
>   never a silent pass; and a hard failure, which *is* a verdict and stops
>   extraction. These bytes do not vary with that outcome on purpose: a cold
>   root built by `git archive` has no `.git`, so an artifact that varied
>   would report `--check` DRIFT for the ENVIRONMENT rather than for the
>   contract. The artifact states the rule; the run states the result.
> — so what remains UNESTABLISHED here is narrow and named: a run whose
>   establishment came back `inconclusive` renders these same bytes, and
>   only its stderr says so. Bead
>   `franken_lean-contract-pin-tree-producer-side-f8zo`.
> — what this extractor **does** establish: the vendored source below is
>   byte-identical to the installed pinned toolchain's own copy of it, and the
>   extraction fails if they differ. That source set is complete — this
>   extractor reads exactly one vendored file and records exactly one sha256,
>   which is the one dimension in which it is NOT short where the `.olean`
>   extractor was (bead `franken_lean-contract-pin-tree-unestablished-monc`).
> source: `vendor/lean4-src/src/include/lean/lean.h` (3352 lines, sha256 `22eed50aa703c4403010fabc12a7231ffa34dc979bd59ca1bfbac13c29a1dad2`)
> inventory: `contracts/abi_inventory.json` sha256 `3eefadc8e70c2fd711a95d47e033d26f7451d6066a06adbf0eedd7790d1018f6`
> rust: `crates/fln-rt/src/abi.rs` (rendered from the same inventory)
> rust (boundary): `crates/fln-unsafe-abi/src/contract.rs` (layout partition, `pub(crate)`, same inventory)

Scope of this slice (bead franken_lean-53v): object tags, layout constants,
object-header and object-struct field layouts, ownership conventions, and the
full `lean.h` function census with per-parameter ownership classes. The
per-symbol status taxonomy (NativeSafe / RawPlatform / CompatWrapper /
ReferenceSemanticAdapter / Unsupported) is a reviewed **policy join** against
this census and lands with the Marrow implementation beads — no symbol below
is implicitly classified by its absence.

## 1. Object tags

| tag | value | provenance |
|---|---|---|
| `LeanMaxCtorTag` | 243 | `vendor/lean4-src/src/include/lean/lean.h:92` |
| `LeanPromise` | 244 | `vendor/lean4-src/src/include/lean/lean.h:93` |
| `LeanClosure` | 245 | `vendor/lean4-src/src/include/lean/lean.h:94` |
| `LeanArray` | 246 | `vendor/lean4-src/src/include/lean/lean.h:95` |
| `LeanStructArray` | 247 | `vendor/lean4-src/src/include/lean/lean.h:96` |
| `LeanScalarArray` | 248 | `vendor/lean4-src/src/include/lean/lean.h:97` |
| `LeanString` | 249 | `vendor/lean4-src/src/include/lean/lean.h:98` |
| `LeanMPZ` | 250 | `vendor/lean4-src/src/include/lean/lean.h:99` |
| `LeanThunk` | 251 | `vendor/lean4-src/src/include/lean/lean.h:100` |
| `LeanTask` | 252 | `vendor/lean4-src/src/include/lean/lean.h:101` |
| `LeanRef` | 253 | `vendor/lean4-src/src/include/lean/lean.h:102` |
| `LeanExternal` | 254 | `vendor/lean4-src/src/include/lean/lean.h:103` |
| `LeanReserved` | 255 | `vendor/lean4-src/src/include/lean/lean.h:104` |

Constructor objects use tags `0..=LeanMaxCtorTag`; every value above is a
special object category.

## 2. Layout constants

| constant | value | provenance |
|---|---|---|
| `LEAN_CLOSURE_MAX_ARGS` | 16 | `vendor/lean4-src/src/include/lean/lean.h:31` |
| `LEAN_OBJECT_SIZE_DELTA` | 8 | `vendor/lean4-src/src/include/lean/lean.h:32` |
| `LEAN_MAX_SMALL_OBJECT_SIZE` | 4096 | `vendor/lean4-src/src/include/lean/lean.h:33` |
| `LEAN_MAX_CTOR_FIELDS` | 256 | `vendor/lean4-src/src/include/lean/lean.h:106` |
| `LEAN_MAX_CTOR_SCALARS_SIZE` | 1024 | `vendor/lean4-src/src/include/lean/lean.h:107` |
| `LEAN_TASK_STATE_WAITING` | 0 | `vendor/lean4-src/src/include/lean/lean.h:1341` |
| `LEAN_TASK_STATE_RUNNING` | 1 | `vendor/lean4-src/src/include/lean/lean.h:1342` |
| `LEAN_TASK_STATE_FINISHED` | 2 | `vendor/lean4-src/src/include/lean/lean.h:1343` |
| `LEAN_MAX_SMALL_NAT` | `(SIZE_MAX >> 1)` (expression) | `vendor/lean4-src/src/include/lean/lean.h:1380` |
| `LEAN_MAX_SMALL_INT` | `(sizeof(void*) == 8 ? INT_MAX : (INT_MAX >> 1))` (expression) | `vendor/lean4-src/src/include/lean/lean.h:1588` |
| `LEAN_MIN_SMALL_INT` | `(sizeof(void*) == 8 ? INT_MIN : (INT_MIN >> 1))` (expression) | `vendor/lean4-src/src/include/lean/lean.h:1589` |

## 3. Ownership conventions

| typedef | meaning | provenance |
|---|---|---|
| `lean_obj_arg` | Standard object argument. | `vendor/lean4-src/src/include/lean/lean.h:176` |
| `b_lean_obj_arg` | Borrowed object argument. | `vendor/lean4-src/src/include/lean/lean.h:177` |
| `u_lean_obj_arg` | Unique (aka non shared) object argument. | `vendor/lean4-src/src/include/lean/lean.h:178` |
| `lean_obj_res` | Standard object result. | `vendor/lean4-src/src/include/lean/lean.h:179` |
| `b_lean_obj_res` | Borrowed object result. | `vendor/lean4-src/src/include/lean/lean.h:180` |

The reference-count field `m_rc` encodes thread-state: `> 0` single-threaded,
`< 0` multi-threaded (atomic), `== 0` persistent (no RC; compacted regions).

## 4. Object structs

### `lean_object` — `vendor/lean4-src/src/include/lean/lean.h:143-148`

| field | C type | bits | array | line |
|---|---|---|---|---|
| `m_rc` | `int` | — | — | 144 |
| `m_cs_sz` | `unsigned` | 16 | — | 145 |
| `m_other` | `unsigned` | 8 | — | 146 |
| `m_tag` | `unsigned` | 8 | — | 147 |

### `lean_ctor_object` — `vendor/lean4-src/src/include/lean/lean.h:182-185`

| field | C type | bits | array | line |
|---|---|---|---|---|
| `m_header` | `lean_object` | — | — | 183 |
| `m_objs` | `lean_object *` | — | `[]` | 184 |

### `lean_array_object` — `vendor/lean4-src/src/include/lean/lean.h:188-193`

| field | C type | bits | array | line |
|---|---|---|---|---|
| `m_header` | `lean_object` | — | — | 189 |
| `m_size` | `size_t` | — | — | 190 |
| `m_capacity` | `size_t` | — | — | 191 |
| `m_data` | `lean_object *` | — | `[]` | 192 |

### `lean_sarray_object` — `vendor/lean4-src/src/include/lean/lean.h:196-201`

| field | C type | bits | array | line |
|---|---|---|---|---|
| `m_header` | `lean_object` | — | — | 197 |
| `m_size` | `size_t` | — | — | 198 |
| `m_capacity` | `size_t` | — | — | 199 |
| `m_data` | `uint8_t` | — | `[]` | 200 |

### `lean_string_object` — `vendor/lean4-src/src/include/lean/lean.h:203-209`

| field | C type | bits | array | line |
|---|---|---|---|---|
| `m_header` | `lean_object` | — | — | 204 |
| `m_size` | `size_t` | — | — | 205 |
| `m_capacity` | `size_t` | — | — | 206 |
| `m_length` | `size_t` | — | — | 207 |
| `m_data` | `char` | — | `[]` | 208 |

### `lean_closure_object` — `vendor/lean4-src/src/include/lean/lean.h:211-217`

| field | C type | bits | array | line |
|---|---|---|---|---|
| `m_header` | `lean_object` | — | — | 212 |
| `m_fun` | `void *` | — | — | 213 |
| `m_arity` | `uint16_t` | — | — | 214 |
| `m_num_fixed` | `uint16_t` | — | — | 215 |
| `m_objs` | `lean_object *` | — | `[]` | 216 |

### `lean_ref_object` — `vendor/lean4-src/src/include/lean/lean.h:219-222`

| field | C type | bits | array | line |
|---|---|---|---|---|
| `m_header` | `lean_object` | — | — | 220 |
| `m_value` | `lean_object *` | — | — | 221 |

### `lean_thunk_object` — `vendor/lean4-src/src/include/lean/lean.h:224-228`

| field | C type | bits | array | line |
|---|---|---|---|---|
| `m_header` | `lean_object` | — | — | 225 |
| `m_value` | `_Atomic(lean_object *)` | — | — | 226 |
| `m_closure` | `_Atomic(lean_object *)` | — | — | 227 |

### `lean_task_imp` — `vendor/lean4-src/src/include/lean/lean.h:234-243`

| field | C type | bits | array | line |
|---|---|---|---|---|
| `m_closure` | `lean_object *` | — | — | 235 |
| `m_head_dep` | `struct lean_task *` | — | — | 236 |
| `m_next_dep` | `struct lean_task *` | — | — | 237 |
| `m_prio` | `unsigned` | — | — | 238 |
| `m_canceled` | `uint8_t` | — | — | 239 |
| `m_keep_alive` | `uint8_t` | — | — | 241 |
| `m_deleted` | `uint8_t` | — | — | 242 |

### `lean_task_object` — `vendor/lean4-src/src/include/lean/lean.h:296-300`

| field | C type | bits | array | line |
|---|---|---|---|---|
| `m_header` | `lean_object` | — | — | 297 |
| `m_value` | `_Atomic(lean_object *)` | — | — | 298 |
| `m_imp` | `lean_task_imp *` | — | — | 299 |

### `lean_promise_object` — `vendor/lean4-src/src/include/lean/lean.h:302-305`

| field | C type | bits | array | line |
|---|---|---|---|---|
| `m_header` | `lean_object` | — | — | 303 |
| `m_result` | `lean_task_object *` | — | — | 304 |

### `lean_external_class` — `vendor/lean4-src/src/include/lean/lean.h:310-313`

| field | C type | bits | array | line |
|---|---|---|---|---|
| `m_finalize` | `lean_external_finalize_proc` | — | — | 311 |
| `m_foreach` | `lean_external_foreach_proc` | — | — | 312 |

### `lean_external_object` — `vendor/lean4-src/src/include/lean/lean.h:318-322`

| field | C type | bits | array | line |
|---|---|---|---|---|
| `m_header` | `lean_object` | — | — | 319 |
| `m_class` | `lean_external_class *` | — | — | 320 |
| `m_data` | `void *` | — | — | 321 |

## 5. Function census

211 `LEAN_EXPORT` prototypes; 565 `static inline` definitions.
Ownership classes: `owned_arg`/`borrowed_arg`/`unique_arg` (`lean_obj_arg`/
`b_lean_obj_arg`/`u_lean_obj_arg`), `owned_res`/`borrowed_res`, `raw_object`
(bare `lean_object *`), `value` (non-object). Duplicate names arise from
platform `#if` branches and are intentional; rows are keyed by (name, line).

| symbol | linkage | signature (ownership) | line |
|---|---|---|---|
| `lean_align` | inline | (v: value, a: value) -> value | 390 |
| `lean_alloc_array` | inline | (size: value, capacity: value) -> owned_res | 848 |
| `lean_alloc_closure` | inline | (fun: value, arity: value, num_fixed: value) -> owned_res | 800 |
| `lean_alloc_ctor` | inline | (tag: value, num_objs: value, scalar_sz: value) -> raw_object | 679 |
| `lean_alloc_ctor_memory` | inline | (sz: value) -> raw_object | 434 |
| `lean_alloc_external` | inline | (cls: value, data: value) -> raw_object | 1351 |
| `lean_alloc_object` | export | (sz: value) -> raw_object | 503 |
| `lean_alloc_sarray` | inline | (elem_size: value, size: value, capacity: value) -> owned_res | 1036 |
| `lean_alloc_sarray_would_overflow` | inline | (elem_size: value, capacity: value) -> value | 1026 |
| `lean_alloc_small` | export | (sz: value, slot_idx: value) -> value | 400 |
| `lean_alloc_small_object` | inline | (sz: value) -> raw_object | 409 |
| `lean_alloc_string` | inline | (size: value, capacity: value, len: value) -> owned_res | 1198 |
| `lean_apply_1` | export | (f: raw_object, a1: raw_object) -> raw_object | 827 |
| `lean_apply_10` | export | (f: raw_object, a1: raw_object, a2: raw_object, a3: raw_object, a4: raw_object, a5: raw_object, a6: raw_object, a7: raw_object, a8: raw_object, a9: raw_object, a10: raw_object) -> raw_object | 836 |
| `lean_apply_11` | export | (f: raw_object, a1: raw_object, a2: raw_object, a3: raw_object, a4: raw_object, a5: raw_object, a6: raw_object, a7: raw_object, a8: raw_object, a9: raw_object, a10: raw_object, a11: raw_object) -> raw_object | 837 |
| `lean_apply_12` | export | (f: raw_object, a1: raw_object, a2: raw_object, a3: raw_object, a4: raw_object, a5: raw_object, a6: raw_object, a7: raw_object, a8: raw_object, a9: raw_object, a10: raw_object, a11: raw_object, a12: raw_object) -> raw_object | 838 |
| `lean_apply_13` | export | (f: raw_object, a1: raw_object, a2: raw_object, a3: raw_object, a4: raw_object, a5: raw_object, a6: raw_object, a7: raw_object, a8: raw_object, a9: raw_object, a10: raw_object, a11: raw_object, a12: raw_object, a13: raw_object) -> raw_object | 839 |
| `lean_apply_14` | export | (f: raw_object, a1: raw_object, a2: raw_object, a3: raw_object, a4: raw_object, a5: raw_object, a6: raw_object, a7: raw_object, a8: raw_object, a9: raw_object, a10: raw_object, a11: raw_object, a12: raw_object, a13: raw_object, a14: raw_object) -> raw_object | 840 |
| `lean_apply_15` | export | (f: raw_object, a1: raw_object, a2: raw_object, a3: raw_object, a4: raw_object, a5: raw_object, a6: raw_object, a7: raw_object, a8: raw_object, a9: raw_object, a10: raw_object, a11: raw_object, a12: raw_object, a13: raw_object, a14: raw_object, a15: raw_object) -> raw_object | 841 |
| `lean_apply_16` | export | (f: raw_object, a1: raw_object, a2: raw_object, a3: raw_object, a4: raw_object, a5: raw_object, a6: raw_object, a7: raw_object, a8: raw_object, a9: raw_object, a10: raw_object, a11: raw_object, a12: raw_object, a13: raw_object, a14: raw_object, a15: raw_object, a16: raw_object) -> raw_object | 842 |
| `lean_apply_2` | export | (f: raw_object, a1: raw_object, a2: raw_object) -> raw_object | 828 |
| `lean_apply_3` | export | (f: raw_object, a1: raw_object, a2: raw_object, a3: raw_object) -> raw_object | 829 |
| `lean_apply_4` | export | (f: raw_object, a1: raw_object, a2: raw_object, a3: raw_object, a4: raw_object) -> raw_object | 830 |
| `lean_apply_5` | export | (f: raw_object, a1: raw_object, a2: raw_object, a3: raw_object, a4: raw_object, a5: raw_object) -> raw_object | 831 |
| `lean_apply_6` | export | (f: raw_object, a1: raw_object, a2: raw_object, a3: raw_object, a4: raw_object, a5: raw_object, a6: raw_object) -> raw_object | 832 |
| `lean_apply_7` | export | (f: raw_object, a1: raw_object, a2: raw_object, a3: raw_object, a4: raw_object, a5: raw_object, a6: raw_object, a7: raw_object) -> raw_object | 833 |
| `lean_apply_8` | export | (f: raw_object, a1: raw_object, a2: raw_object, a3: raw_object, a4: raw_object, a5: raw_object, a6: raw_object, a7: raw_object, a8: raw_object) -> raw_object | 834 |
| `lean_apply_9` | export | (f: raw_object, a1: raw_object, a2: raw_object, a3: raw_object, a4: raw_object, a5: raw_object, a6: raw_object, a7: raw_object, a8: raw_object, a9: raw_object) -> raw_object | 835 |
| `lean_apply_m` | export | (f: raw_object, n: value, args: raw_object) -> raw_object | 845 |
| `lean_apply_n` | export | (f: raw_object, n: value, args: raw_object) -> raw_object | 843 |
| `lean_array_byte_size` | inline | (o: raw_object) -> value | 857 |
| `lean_array_capacity` | inline | (o: borrowed_arg) -> value | 856 |
| `lean_array_cptr` | inline | (o: raw_object) -> raw_object | 863 |
| `lean_array_data_byte_size` | inline | (o: raw_object) -> value | 860 |
| `lean_array_fget` | inline | (a: borrowed_arg, i: borrowed_arg) -> owned_res | 914 |
| `lean_array_fget_borrowed` | inline | (a: borrowed_arg, i: borrowed_arg) -> owned_res | 918 |
| `lean_array_fset` | inline | (a: owned_arg, i: borrowed_arg, v: owned_arg) -> raw_object | 972 |
| `lean_array_fswap` | inline | (a: owned_arg, i: borrowed_arg, j: borrowed_arg) -> raw_object | 1008 |
| `lean_array_get` | inline | (def_val: borrowed_arg, a: borrowed_arg, i: borrowed_arg) -> raw_object | 924 |
| `lean_array_get_borrowed` | inline | (def_val: borrowed_arg, a: borrowed_arg, i: borrowed_arg) -> raw_object | 939 |
| `lean_array_get_core` | inline | (o: borrowed_arg, i: value) -> borrowed_res | 870 |
| `lean_array_get_panic` | export | (def_val: owned_arg) -> owned_res | 922 |
| `lean_array_get_size` | inline | (a: borrowed_arg) -> raw_object | 892 |
| `lean_array_mk` | export | (l: owned_arg) -> raw_object | 881 |
| `lean_array_pop` | inline | (a: owned_arg) -> raw_object | 987 |
| `lean_array_push` | export | (a: owned_arg, v: owned_arg) -> raw_object | 1021 |
| `lean_array_set` | inline | (a: owned_arg, i: borrowed_arg, v: owned_arg) -> raw_object | 978 |
| `lean_array_set_core` | inline | (o: unique_arg, i: value, v: owned_arg) -> value | 874 |
| `lean_array_set_panic` | export | (a: owned_arg, v: owned_arg) -> owned_res | 976 |
| `lean_array_set_size` | inline | (o: unique_arg, sz: value) -> value | 864 |
| `lean_array_size` | inline | (o: borrowed_arg) -> value | 855 |
| `lean_array_swap` | inline | (a: owned_arg, i: borrowed_arg, j: borrowed_arg) -> raw_object | 1012 |
| `lean_array_sz` | inline | (a: owned_arg) -> raw_object | 886 |
| `lean_array_to_list` | export | (a: owned_arg) -> raw_object | 882 |
| `lean_array_uget` | inline | (a: borrowed_arg, i: value) -> raw_object | 905 |
| `lean_array_uget_borrowed` | inline | (a: borrowed_arg, i: value) -> borrowed_res | 910 |
| `lean_array_uset` | inline | (a: owned_arg, i: value, v: owned_arg) -> raw_object | 964 |
| `lean_array_uswap` | inline | (a: owned_arg, i: value, j: value) -> raw_object | 999 |
| `lean_big_int64_to_int` | export | (n: value) -> raw_object | 1607 |
| `lean_big_int_to_int` | export | (n: value) -> raw_object | 1605 |
| `lean_big_int_to_nat` | export | (a: owned_arg) -> owned_res | 1867 |
| `lean_big_size_t_to_int` | export | (n: value) -> raw_object | 1606 |
| `lean_big_uint64_to_nat` | export | (n: value) -> owned_res | 1399 |
| `lean_big_usize_to_nat` | export | (n: value) -> owned_res | 1398 |
| `lean_bool_to_int16` | inline | (a: value) -> value | 1907 |
| `lean_bool_to_int32` | inline | (a: value) -> value | 1908 |
| `lean_bool_to_int64` | inline | (a: value) -> value | 1909 |
| `lean_bool_to_int8` | inline | (a: value) -> value | 1906 |
| `lean_bool_to_isize` | inline | (a: value) -> value | 1910 |
| `lean_bool_to_uint16` | inline | (a: value) -> value | 1902 |
| `lean_bool_to_uint32` | inline | (a: value) -> value | 1903 |
| `lean_bool_to_uint64` | inline | (a: value) -> value | 1904 |
| `lean_bool_to_uint8` | inline | (a: value) -> value | 1901 |
| `lean_bool_to_usize` | inline | (a: value) -> value | 1905 |
| `lean_box` | inline | (n: value) -> raw_object | 325 |
| `lean_box_float` | inline | (v: value) -> owned_res | 2899 |
| `lean_box_float32` | inline | (v: value) -> owned_res | 2909 |
| `lean_box_uint32` | inline | (v: value) -> owned_res | 2857 |
| `lean_box_uint64` | inline | (v: value) -> owned_res | 2879 |
| `lean_box_usize` | inline | (v: value) -> owned_res | 2889 |
| `lean_byte_array_data` | export | (a: owned_arg) -> owned_res | 1074 |
| `lean_byte_array_fget` | inline | (a: borrowed_arg, i: borrowed_arg) -> value | 1099 |
| `lean_byte_array_fset` | inline | (a: owned_arg, i: borrowed_arg, b: value) -> owned_res | 1127 |
| `lean_byte_array_get` | inline | (a: borrowed_arg, i: borrowed_arg) -> value | 1090 |
| `lean_byte_array_hash` | export | (a: borrowed_arg) -> value | 1076 |
| `lean_byte_array_mk` | export | (a: owned_arg) -> owned_res | 1073 |
| `lean_byte_array_push` | export | (a: owned_arg, b: value) -> owned_res | 1103 |
| `lean_byte_array_set` | inline | (a: owned_arg, i: borrowed_arg, b: value) -> owned_res | 1114 |
| `lean_byte_array_size` | inline | (a: borrowed_arg) -> owned_res | 1083 |
| `lean_byte_array_uget` | inline | (a: borrowed_arg, i: value) -> value | 1086 |
| `lean_byte_array_uset` | inline | (a: owned_arg, i: value, v: value) -> raw_object | 1105 |
| `lean_char_default_value` | inline | (()) -> value | 1211 |
| `lean_closure_arg_cptr` | inline | (o: raw_object) -> raw_object | 799 |
| `lean_closure_arity` | inline | (o: raw_object) -> value | 797 |
| `lean_closure_byte_size` | inline | (o: raw_object) -> value | 818 |
| `lean_closure_data_byte_size` | inline | (o: raw_object) -> value | 822 |
| `lean_closure_fun` | inline | (o: raw_object) -> value | 796 |
| `lean_closure_get` | inline | (o: borrowed_arg, i: value) -> borrowed_res | 810 |
| `lean_closure_num_fixed` | inline | (o: raw_object) -> value | 798 |
| `lean_closure_set` | inline | (o: unique_arg, i: value, a: owned_arg) -> value | 814 |
| `lean_copy_byte_array` | export | (a: owned_arg) -> owned_res | 1075 |
| `lean_copy_expand_array` | export | (a: owned_arg, expand: value) -> owned_res | 954 |
| `lean_copy_expand_array_nonlinear` | export | (a: owned_arg, expand: value) -> owned_res | 957 |
| `lean_copy_float_array` | export | (a: owned_arg) -> owned_res | 1135 |
| `lean_cstr_to_int` | export | (n: value) -> raw_object | 1604 |
| `lean_cstr_to_nat` | export | (n: value) -> owned_res | 1397 |
| `lean_ctor_get` | inline | (o: borrowed_arg, i: value) -> borrowed_res | 686 |
| `lean_ctor_get_float` | inline | (o: borrowed_arg, offset: value) -> value | 749 |
| `lean_ctor_get_float32` | inline | (o: borrowed_arg, offset: value) -> value | 754 |
| `lean_ctor_get_uint16` | inline | (o: borrowed_arg, offset: value) -> value | 734 |
| `lean_ctor_get_uint32` | inline | (o: borrowed_arg, offset: value) -> value | 739 |
| `lean_ctor_get_uint64` | inline | (o: borrowed_arg, offset: value) -> value | 744 |
| `lean_ctor_get_uint8` | inline | (o: borrowed_arg, offset: value) -> value | 729 |
| `lean_ctor_get_usize` | inline | (o: borrowed_arg, i: value) -> value | 724 |
| `lean_ctor_num_objs` | inline | (o: raw_object) -> value | 664 |
| `lean_ctor_obj_cptr` | inline | (o: raw_object) -> raw_object | 669 |
| `lean_ctor_release` | inline | (o: borrowed_arg, i: value) -> value | 713 |
| `lean_ctor_scalar_cptr` | inline | (o: raw_object) -> value | 674 |
| `lean_ctor_set` | inline | (o: borrowed_arg, i: value, v: owned_arg) -> value | 703 |
| `lean_ctor_set_float` | inline | (o: borrowed_arg, offset: value, v: value) -> value | 784 |
| `lean_ctor_set_float32` | inline | (o: borrowed_arg, offset: value, v: value) -> value | 789 |
| `lean_ctor_set_tag` | inline | (o: borrowed_arg, new_tag: value) -> value | 708 |
| `lean_ctor_set_uint16` | inline | (o: borrowed_arg, offset: value, v: value) -> value | 769 |
| `lean_ctor_set_uint32` | inline | (o: borrowed_arg, offset: value, v: value) -> value | 774 |
| `lean_ctor_set_uint64` | inline | (o: borrowed_arg, offset: value, v: value) -> value | 779 |
| `lean_ctor_set_uint8` | inline | (o: borrowed_arg, offset: value, v: value) -> value | 764 |
| `lean_ctor_set_usize` | inline | (o: borrowed_arg, i: value, v: value) -> value | 759 |
| `lean_dbg_sleep` | export | (ms: value, fn: owned_arg) -> raw_object | 2922 |
| `lean_dbg_trace` | export | (s: owned_arg, fn: owned_arg) -> raw_object | 2921 |
| `lean_dbg_trace_if_shared` | export | (s: owned_arg, a: owned_arg) -> raw_object | 2923 |
| `lean_dec` | inline | (o: raw_object) -> value | 583 |
| `lean_dec_ref` | inline | (o: raw_object) -> value | 574 |
| `lean_dec_ref_cold` | export | (o: raw_object) -> value | 572 |
| `lean_dec_ref_known` | inline | (o: raw_object, objs: value) -> value | 691 |
| `lean_decode_io_error` | export | (errnum: value, fname: borrowed_arg) -> owned_res | 2927 |
| `lean_decode_uv_error` | export | (errnum: value, fname: borrowed_arg) -> owned_res | 2928 |
| `lean_del_object` | inline | (o: raw_object) -> value | 507 |
| `lean_ensure_exclusive_array` | inline | (a: owned_arg) -> owned_res | 959 |
| `lean_expr_data` | inline | (expr: owned_arg) -> value | 3188 |
| `lean_finalize_task_manager` | export | (()) -> value | 1314 |
| `lean_float32_add` | inline | (a: value, b: value) -> value | 3157 |
| `lean_float32_beq` | inline | (a: value, b: value) -> value | 3162 |
| `lean_float32_decLe` | inline | (a: value, b: value) -> value | 3163 |
| `lean_float32_decLt` | inline | (a: value, b: value) -> value | 3164 |
| `lean_float32_div` | inline | (a: value, b: value) -> value | 3160 |
| `lean_float32_frexp` | export | (a: value) -> owned_res | 2853 |
| `lean_float32_isfinite` | export | (a: value) -> value | 2851 |
| `lean_float32_isinf` | export | (a: value) -> value | 2852 |
| `lean_float32_isnan` | export | (a: value) -> value | 2850 |
| `lean_float32_mul` | inline | (a: value, b: value) -> value | 3159 |
| `lean_float32_negate` | inline | (a: value) -> value | 3161 |
| `lean_float32_of_bits` | export | (u: value) -> value | 3155 |
| `lean_float32_once` | inline | (loc: value, tok: value, value) -> value | 3332 |
| `lean_float32_once_cold` | export | (loc: value, tok: value, value) -> value | 3330 |
| `lean_float32_scaleb` | export | (a: value, b: borrowed_arg) -> value | 2849 |
| `lean_float32_sub` | inline | (a: value, b: value) -> value | 3158 |
| `lean_float32_to_bits` | export | (d: value) -> value | 3156 |
| `lean_float32_to_float` | inline | (a: value) -> value | 3177 |
| `lean_float32_to_int16` | inline | (a: value) -> value | 3124 |
| `lean_float32_to_int32` | inline | (a: value) -> value | 3130 |
| `lean_float32_to_int64` | inline | (a: value) -> value | 3136 |
| `lean_float32_to_int8` | inline | (a: value) -> value | 3118 |
| `lean_float32_to_isize` | inline | (a: value) -> value | 3142 |
| `lean_float32_to_string` | export | (a: value) -> owned_res | 2848 |
| `lean_float32_to_uint16` | inline | (a: value) -> value | 3103 |
| `lean_float32_to_uint32` | inline | (a: value) -> value | 3106 |
| `lean_float32_to_uint64` | inline | (a: value) -> value | 3109 |
| `lean_float32_to_uint8` | inline | (a: value) -> value | 3100 |
| `lean_float32_to_usize` | inline | (a: value) -> value | 3112 |
| `lean_float_add` | inline | (a: value, b: value) -> value | 3080 |
| `lean_float_array_cptr` | inline | (a: borrowed_arg) -> value | 1146 |
| `lean_float_array_data` | export | (a: owned_arg) -> owned_res | 1134 |
| `lean_float_array_fget` | inline | (a: borrowed_arg, i: borrowed_arg) -> value | 1154 |
| `lean_float_array_fset` | inline | (a: owned_arg, i: borrowed_arg, d: value) -> owned_res | 1179 |
| `lean_float_array_get` | inline | (a: borrowed_arg, i: borrowed_arg) -> value | 1158 |
| `lean_float_array_mk` | export | (a: owned_arg) -> owned_res | 1133 |
| `lean_float_array_push` | export | (a: owned_arg, d: value) -> owned_res | 1168 |
| `lean_float_array_set` | inline | (a: owned_arg, i: borrowed_arg, d: value) -> owned_res | 1183 |
| `lean_float_array_size` | inline | (a: borrowed_arg) -> owned_res | 1142 |
| `lean_float_array_uget` | inline | (a: borrowed_arg, i: value) -> value | 1150 |
| `lean_float_array_uset` | inline | (a: owned_arg, i: value, d: value) -> owned_res | 1170 |
| `lean_float_beq` | inline | (a: value, b: value) -> value | 3085 |
| `lean_float_decLe` | inline | (a: value, b: value) -> value | 3086 |
| `lean_float_decLt` | inline | (a: value, b: value) -> value | 3087 |
| `lean_float_div` | inline | (a: value, b: value) -> value | 3083 |
| `lean_float_frexp` | export | (a: value) -> owned_res | 2844 |
| `lean_float_isfinite` | export | (a: value) -> value | 2842 |
| `lean_float_isinf` | export | (a: value) -> value | 2843 |
| `lean_float_isnan` | export | (a: value) -> value | 2841 |
| `lean_float_mul` | inline | (a: value, b: value) -> value | 3082 |
| `lean_float_negate` | inline | (a: value) -> value | 3084 |
| `lean_float_of_bits` | export | (u: value) -> value | 3078 |
| `lean_float_once` | inline | (loc: value, tok: value, value) -> value | 3341 |
| `lean_float_once_cold` | export | (loc: value, tok: value, value) -> value | 3339 |
| `lean_float_scaleb` | export | (a: value, b: borrowed_arg) -> value | 2840 |
| `lean_float_sub` | inline | (a: value, b: value) -> value | 3081 |
| `lean_float_to_bits` | export | (d: value) -> value | 3079 |
| `lean_float_to_float32` | inline | (a: value) -> value | 3176 |
| `lean_float_to_int16` | inline | (a: value) -> value | 3047 |
| `lean_float_to_int32` | inline | (a: value) -> value | 3053 |
| `lean_float_to_int64` | inline | (a: value) -> value | 3059 |
| `lean_float_to_int8` | inline | (a: value) -> value | 3041 |
| `lean_float_to_isize` | inline | (a: value) -> value | 3065 |
| `lean_float_to_string` | export | (a: value) -> owned_res | 2839 |
| `lean_float_to_uint16` | inline | (a: value) -> value | 3026 |
| `lean_float_to_uint32` | inline | (a: value) -> value | 3029 |
| `lean_float_to_uint64` | inline | (a: value) -> value | 3032 |
| `lean_float_to_uint8` | inline | (a: value) -> value | 3023 |
| `lean_float_to_usize` | inline | (a: value) -> value | 3035 |
| `lean_free_object` | export | (o: raw_object) -> value | 504 |
| `lean_free_small` | export | (p: value) -> value | 401 |
| `lean_free_small_object` | inline | (o: raw_object) -> value | 490 |
| `lean_get_external_class` | inline | (o: raw_object) -> value | 1359 |
| `lean_get_external_data` | inline | (o: raw_object) -> value | 1363 |
| `lean_get_max_ctor_fields` | inline | (_unit: owned_arg) -> owned_res | 3199 |
| `lean_get_max_ctor_scalars_size` | inline | (_unit: owned_arg) -> owned_res | 3203 |
| `lean_get_max_ctor_tag` | inline | (_unit: owned_arg) -> owned_res | 3211 |
| `lean_get_rc_mt_addr` | inline | (o: raw_object) -> value | 552 |
| `lean_get_slot_idx` | inline | (sz: value) -> value | 394 |
| `lean_get_usize_size` | inline | (_unit: owned_arg) -> owned_res | 3207 |
| `lean_has_rc` | inline | (o: raw_object) -> value | 548 |
| `lean_hashmap_mk_idx` | inline | (sz: owned_arg, hash: value) -> value | 3180 |
| `lean_hashset_mk_idx` | inline | (sz: owned_arg, hash: value) -> value | 3184 |
| `lean_inc` | inline | (o: raw_object) -> value | 581 |
| `lean_inc_heartbeat` | export | (()) -> value | 403 |
| `lean_inc_n` | inline | (o: raw_object, n: value) -> value | 582 |
| `lean_inc_ref` | inline | (o: raw_object) -> value | 568 |
| `lean_inc_ref_n` | inline | (o: raw_object, n: value) -> value | 556 |
| `lean_init_task_manager` | export | (()) -> value | 1312 |
| `lean_init_task_manager_using` | export | (num_workers: value) -> value | 1313 |
| `lean_int16_abs` | inline | (a: value) -> value | 2379 |
| `lean_int16_add` | inline | (a1: value, a2: value) -> value | 2307 |
| `lean_int16_complement` | inline | (a: value) -> value | 2373 |
| `lean_int16_dec_eq` | inline | (a1: value, a2: value) -> value | 2384 |
| `lean_int16_dec_le` | inline | (a1: value, a2: value) -> value | 2398 |
| `lean_int16_dec_lt` | inline | (a1: value, a2: value) -> value | 2391 |
| `lean_int16_div` | inline | (a1: value, a2: value) -> value | 2322 |
| `lean_int16_land` | inline | (a1: value, a2: value) -> value | 2338 |
| `lean_int16_lor` | inline | (a1: value, a2: value) -> value | 2345 |
| `lean_int16_mod` | inline | (a1: value, a2: value) -> value | 2330 |
| `lean_int16_mul` | inline | (a1: value, a2: value) -> value | 2317 |
| `lean_int16_neg` | inline | (a: value) -> value | 2302 |
| `lean_int16_of_big_int` | export | (a: borrowed_arg) -> value | 2272 |
| `lean_int16_of_int` | inline | (a: borrowed_arg) -> value | 2273 |
| `lean_int16_of_nat` | inline | (a: borrowed_arg) -> value | 2285 |
| `lean_int16_shift_left` | inline | (a1: value, a2: value) -> value | 2366 |
| `lean_int16_shift_right` | inline | (a1: value, a2: value) -> value | 2359 |
| `lean_int16_sub` | inline | (a1: value, a2: value) -> value | 2312 |
| `lean_int16_to_float` | inline | (a: value) -> value | 3094 |
| `lean_int16_to_float32` | inline | (a: value) -> value | 3171 |
| `lean_int16_to_int` | inline | (a: value) -> owned_res | 2297 |
| `lean_int16_to_int32` | inline | (a: value) -> value | 2407 |
| `lean_int16_to_int64` | inline | (a: value) -> value | 2408 |
| `lean_int16_to_int8` | inline | (a: value) -> value | 2406 |
| `lean_int16_to_isize` | inline | (a: value) -> value | 2409 |
| `lean_int16_xor` | inline | (a1: value, a2: value) -> value | 2352 |
| `lean_int32_abs` | inline | (a: value) -> value | 2519 |
| `lean_int32_add` | inline | (a1: value, a2: value) -> value | 2447 |
| `lean_int32_complement` | inline | (a: value) -> value | 2513 |
| `lean_int32_dec_eq` | inline | (a1: value, a2: value) -> value | 2524 |
| `lean_int32_dec_le` | inline | (a1: value, a2: value) -> value | 2538 |
| `lean_int32_dec_lt` | inline | (a1: value, a2: value) -> value | 2531 |
| `lean_int32_div` | inline | (a1: value, a2: value) -> value | 2462 |
| `lean_int32_land` | inline | (a1: value, a2: value) -> value | 2478 |
| `lean_int32_lor` | inline | (a1: value, a2: value) -> value | 2485 |
| `lean_int32_mod` | inline | (a1: value, a2: value) -> value | 2470 |
| `lean_int32_mul` | inline | (a1: value, a2: value) -> value | 2457 |
| `lean_int32_neg` | inline | (a: value) -> value | 2442 |
| `lean_int32_of_big_int` | export | (a: borrowed_arg) -> value | 2412 |
| `lean_int32_of_int` | inline | (a: borrowed_arg) -> value | 2413 |
| `lean_int32_of_nat` | inline | (a: borrowed_arg) -> value | 2425 |
| `lean_int32_shift_left` | inline | (a1: value, a2: value) -> value | 2506 |
| `lean_int32_shift_right` | inline | (a1: value, a2: value) -> value | 2499 |
| `lean_int32_sub` | inline | (a1: value, a2: value) -> value | 2452 |
| `lean_int32_to_float` | inline | (a: value) -> value | 3095 |
| `lean_int32_to_float32` | inline | (a: value) -> value | 3172 |
| `lean_int32_to_int` | inline | (a: value) -> owned_res | 2437 |
| `lean_int32_to_int16` | inline | (a: value) -> value | 2547 |
| `lean_int32_to_int64` | inline | (a: value) -> value | 2548 |
| `lean_int32_to_int8` | inline | (a: value) -> value | 2546 |
| `lean_int32_to_isize` | inline | (a: value) -> value | 2549 |
| `lean_int32_xor` | inline | (a1: value, a2: value) -> value | 2492 |
| `lean_int64_abs` | inline | (a: value) -> value | 2661 |
| `lean_int64_add` | inline | (a1: value, a2: value) -> value | 2587 |
| `lean_int64_complement` | inline | (a: value) -> value | 2655 |
| `lean_int64_dec_eq` | inline | (a1: value, a2: value) -> value | 2666 |
| `lean_int64_dec_le` | inline | (a1: value, a2: value) -> value | 2680 |
| `lean_int64_dec_lt` | inline | (a1: value, a2: value) -> value | 2673 |
| `lean_int64_div` | inline | (a1: value, a2: value) -> value | 2602 |
| `lean_int64_land` | inline | (a1: value, a2: value) -> value | 2620 |
| `lean_int64_lor` | inline | (a1: value, a2: value) -> value | 2627 |
| `lean_int64_mod` | inline | (a1: value, a2: value) -> value | 2611 |
| `lean_int64_mul` | inline | (a1: value, a2: value) -> value | 2597 |
| `lean_int64_neg` | inline | (a: value) -> value | 2582 |
| `lean_int64_of_big_int` | export | (a: borrowed_arg) -> value | 2552 |
| `lean_int64_of_int` | inline | (a: borrowed_arg) -> value | 2553 |
| `lean_int64_of_nat` | inline | (a: borrowed_arg) -> value | 2565 |
| `lean_int64_shift_left` | inline | (a1: value, a2: value) -> value | 2648 |
| `lean_int64_shift_right` | inline | (a1: value, a2: value) -> value | 2641 |
| `lean_int64_sub` | inline | (a1: value, a2: value) -> value | 2592 |
| `lean_int64_to_float` | inline | (a: value) -> value | 3096 |
| `lean_int64_to_float32` | inline | (a: value) -> value | 3173 |
| `lean_int64_to_int` | inline | (n: value) -> owned_res | 1618 |
| `lean_int64_to_int16` | inline | (a: value) -> value | 2689 |
| `lean_int64_to_int32` | inline | (a: value) -> value | 2690 |
| `lean_int64_to_int8` | inline | (a: value) -> value | 2688 |
| `lean_int64_to_int_sint` | inline | (a: value) -> owned_res | 2577 |
| `lean_int64_to_isize` | inline | (a: value) -> value | 2691 |
| `lean_int64_xor` | inline | (a1: value, a2: value) -> value | 2634 |
| `lean_int8_abs` | inline | (a: value) -> value | 2238 |
| `lean_int8_add` | inline | (a1: value, a2: value) -> value | 2166 |
| `lean_int8_complement` | inline | (a: value) -> value | 2232 |
| `lean_int8_dec_eq` | inline | (a1: value, a2: value) -> value | 2243 |
| `lean_int8_dec_le` | inline | (a1: value, a2: value) -> value | 2257 |
| `lean_int8_dec_lt` | inline | (a1: value, a2: value) -> value | 2250 |
| `lean_int8_div` | inline | (a1: value, a2: value) -> value | 2181 |
| `lean_int8_land` | inline | (a1: value, a2: value) -> value | 2197 |
| `lean_int8_lor` | inline | (a1: value, a2: value) -> value | 2204 |
| `lean_int8_mod` | inline | (a1: value, a2: value) -> value | 2189 |
| `lean_int8_mul` | inline | (a1: value, a2: value) -> value | 2176 |
| `lean_int8_neg` | inline | (a: value) -> value | 2161 |
| `lean_int8_of_big_int` | export | (a: borrowed_arg) -> value | 2131 |
| `lean_int8_of_int` | inline | (a: borrowed_arg) -> value | 2132 |
| `lean_int8_of_nat` | inline | (a: borrowed_arg) -> value | 2144 |
| `lean_int8_shift_left` | inline | (a1: value, a2: value) -> value | 2225 |
| `lean_int8_shift_right` | inline | (a1: value, a2: value) -> value | 2218 |
| `lean_int8_sub` | inline | (a1: value, a2: value) -> value | 2171 |
| `lean_int8_to_float` | inline | (a: value) -> value | 3093 |
| `lean_int8_to_float32` | inline | (a: value) -> value | 3170 |
| `lean_int8_to_int` | inline | (a: value) -> owned_res | 2156 |
| `lean_int8_to_int16` | inline | (a: value) -> value | 2265 |
| `lean_int8_to_int32` | inline | (a: value) -> value | 2266 |
| `lean_int8_to_int64` | inline | (a: value) -> value | 2267 |
| `lean_int8_to_isize` | inline | (a: value) -> value | 2268 |
| `lean_int8_xor` | inline | (a1: value, a2: value) -> value | 2211 |
| `lean_int_add` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1668 |
| `lean_int_big_add` | export | (a1: raw_object, a2: raw_object) -> raw_object | 1591 |
| `lean_int_big_div` | export | (a1: raw_object, a2: raw_object) -> raw_object | 1594 |
| `lean_int_big_div_exact` | export | (a1: raw_object, a2: raw_object) -> raw_object | 1595 |
| `lean_int_big_ediv` | export | (a1: raw_object, a2: raw_object) -> raw_object | 1597 |
| `lean_int_big_emod` | export | (a1: raw_object, a2: raw_object) -> raw_object | 1598 |
| `lean_int_big_eq` | export | (a1: raw_object, a2: raw_object) -> value | 1599 |
| `lean_int_big_le` | export | (a1: raw_object, a2: raw_object) -> value | 1600 |
| `lean_int_big_lt` | export | (a1: raw_object, a2: raw_object) -> value | 1601 |
| `lean_int_big_mod` | export | (a1: raw_object, a2: raw_object) -> raw_object | 1596 |
| `lean_int_big_mul` | export | (a1: raw_object, a2: raw_object) -> raw_object | 1593 |
| `lean_int_big_neg` | export | (a: raw_object) -> raw_object | 1590 |
| `lean_int_big_nonneg` | export | (a: raw_object) -> value | 1602 |
| `lean_int_big_sub` | export | (a1: raw_object, a2: raw_object) -> raw_object | 1592 |
| `lean_int_dec_eq` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> value | 1886 |
| `lean_int_dec_le` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> value | 1888 |
| `lean_int_dec_lt` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> value | 1890 |
| `lean_int_dec_nonneg` | inline | (a: borrowed_arg) -> value | 1892 |
| `lean_int_div` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1692 |
| `lean_int_div_exact` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1716 |
| `lean_int_ediv` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1773 |
| `lean_int_emod` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1807 |
| `lean_int_eq` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> value | 1839 |
| `lean_int_le` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> value | 1851 |
| `lean_int_lt` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> value | 1859 |
| `lean_int_mod` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1740 |
| `lean_int_mul` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1684 |
| `lean_int_ne` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> value | 1847 |
| `lean_int_neg` | inline | (a: borrowed_arg) -> owned_res | 1653 |
| `lean_int_neg_succ_of_nat` | inline | (a: owned_arg) -> owned_res | 1661 |
| `lean_int_sub` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1676 |
| `lean_int_to_int` | inline | (n: value) -> owned_res | 1609 |
| `lean_int_to_nat` | inline | (a: owned_arg) -> owned_res | 1868 |
| `lean_internal_is_stage0` | inline | (_unit: owned_arg) -> value | 3247 |
| `lean_internal_panic` | export | (msg: value) -> value | 336 |
| `lean_internal_panic_out_of_memory` | export | (()) -> value | 337 |
| `lean_internal_panic_overflow` | export | (()) -> value | 340 |
| `lean_internal_panic_rc_overflow` | export | (()) -> value | 339 |
| `lean_internal_panic_unreachable` | export | (()) -> value | 338 |
| `lean_io_cancel_core` | export | (t: borrowed_arg) -> value | 1339 |
| `lean_io_check_canceled_core` | export | (()) -> value | 1337 |
| `lean_io_get_task_state_core` | export | (t: borrowed_arg) -> value | 1345 |
| `lean_io_mark_end_initialization` | export | (()) -> value | 2951 |
| `lean_io_mk_world` | inline | (()) -> owned_res | 2930 |
| `lean_io_result_get_error` | inline | (r: borrowed_arg) -> borrowed_res | 2940 |
| `lean_io_result_get_value` | inline | (r: borrowed_arg) -> borrowed_res | 2939 |
| `lean_io_result_is_error` | inline | (r: borrowed_arg) -> value | 2938 |
| `lean_io_result_is_ok` | inline | (r: borrowed_arg) -> value | 2937 |
| `lean_io_result_mk_error` | inline | (e: owned_arg) -> owned_res | 2957 |
| `lean_io_result_mk_ok` | inline | (a: owned_arg) -> owned_res | 2952 |
| `lean_io_result_show_error` | export | (r: borrowed_arg) -> value | 2950 |
| `lean_io_result_take_value` | inline | (r: owned_arg) -> owned_res | 2942 |
| `lean_io_wait_any_core` | export | (task_list: borrowed_arg) -> borrowed_res | 1347 |
| `lean_is_array` | inline | (o: raw_object) -> value | 587 |
| `lean_is_big_object_tag` | inline | (tag: value) -> value | 109 |
| `lean_is_closure` | inline | (o: raw_object) -> value | 586 |
| `lean_is_ctor` | inline | (o: raw_object) -> value | 585 |
| `lean_is_exclusive` | inline | (o: raw_object) -> value | 612 |
| `lean_is_exclusive_obj` | inline | (o: raw_object) -> value | 620 |
| `lean_is_external` | inline | (o: raw_object) -> value | 594 |
| `lean_is_mpz` | inline | (o: raw_object) -> value | 590 |
| `lean_is_mt` | inline | (o: raw_object) -> value | 535 |
| `lean_is_persistent` | inline | (o: raw_object) -> value | 544 |
| `lean_is_promise` | inline | (o: raw_object) -> value | 593 |
| `lean_is_ref` | inline | (o: raw_object) -> value | 595 |
| `lean_is_sarray` | inline | (o: raw_object) -> value | 588 |
| `lean_is_scalar` | inline | (o: raw_object) -> value | 324 |
| `lean_is_shared` | inline | (o: raw_object) -> value | 624 |
| `lean_is_st` | inline | (o: raw_object) -> value | 539 |
| `lean_is_string` | inline | (o: raw_object) -> value | 589 |
| `lean_is_task` | inline | (o: raw_object) -> value | 592 |
| `lean_is_thunk` | inline | (o: raw_object) -> value | 591 |
| `lean_isize_abs` | inline | (a: value) -> value | 2805 |
| `lean_isize_add` | inline | (a1: value, a2: value) -> value | 2729 |
| `lean_isize_complement` | inline | (a: value) -> value | 2799 |
| `lean_isize_dec_eq` | inline | (a1: value, a2: value) -> value | 2810 |
| `lean_isize_dec_le` | inline | (a1: value, a2: value) -> value | 2824 |
| `lean_isize_dec_lt` | inline | (a1: value, a2: value) -> value | 2817 |
| `lean_isize_div` | inline | (a1: value, a2: value) -> value | 2744 |
| `lean_isize_land` | inline | (a1: value, a2: value) -> value | 2762 |
| `lean_isize_lor` | inline | (a1: value, a2: value) -> value | 2769 |
| `lean_isize_mod` | inline | (a1: value, a2: value) -> value | 2753 |
| `lean_isize_mul` | inline | (a1: value, a2: value) -> value | 2739 |
| `lean_isize_neg` | inline | (a: value) -> value | 2724 |
| `lean_isize_of_big_int` | export | (a: borrowed_arg) -> value | 2694 |
| `lean_isize_of_int` | inline | (a: borrowed_arg) -> value | 2695 |
| `lean_isize_of_nat` | inline | (a: borrowed_arg) -> value | 2707 |
| `lean_isize_shift_left` | inline | (a1: value, a2: value) -> value | 2791 |
| `lean_isize_shift_right` | inline | (a1: value, a2: value) -> value | 2783 |
| `lean_isize_sub` | inline | (a1: value, a2: value) -> value | 2734 |
| `lean_isize_to_float` | inline | (a: value) -> value | 3097 |
| `lean_isize_to_float32` | inline | (a: value) -> value | 3174 |
| `lean_isize_to_int` | inline | (a: value) -> owned_res | 2719 |
| `lean_isize_to_int16` | inline | (a: value) -> value | 2833 |
| `lean_isize_to_int32` | inline | (a: value) -> value | 2834 |
| `lean_isize_to_int64` | inline | (a: value) -> value | 2835 |
| `lean_isize_to_int8` | inline | (a: value) -> value | 2832 |
| `lean_isize_xor` | inline | (a1: value, a2: value) -> value | 2776 |
| `lean_manual_get_root` | inline | (_unit: owned_arg) -> owned_res | 3255 |
| `lean_mark_mt` | export | (o: raw_object) -> value | 632 |
| `lean_mark_persistent` | export | (o: raw_object) -> value | 633 |
| `lean_mk_array` | export | (n: owned_arg, v: owned_arg) -> raw_object | 1022 |
| `lean_mk_ascii_string_unchecked` | export | (s: value) -> owned_res | 1215 |
| `lean_mk_empty_array` | inline | (()) -> raw_object | 896 |
| `lean_mk_empty_array_with_capacity` | inline | (capacity: borrowed_arg) -> raw_object | 900 |
| `lean_mk_empty_byte_array` | inline | (capacity: borrowed_arg) -> owned_res | 1078 |
| `lean_mk_empty_float_array` | inline | (capacity: borrowed_arg) -> owned_res | 1137 |
| `lean_mk_io_error_already_exists` | export | (value, owned_arg) -> owned_res | 2963 |
| `lean_mk_io_error_already_exists_file` | export | (owned_arg, value, owned_arg) -> owned_res | 2964 |
| `lean_mk_io_error_eof` | export | (owned_arg) -> owned_res | 2965 |
| `lean_mk_io_error_hardware_fault` | export | (value, owned_arg) -> owned_res | 2966 |
| `lean_mk_io_error_illegal_operation` | export | (value, owned_arg) -> owned_res | 2967 |
| `lean_mk_io_error_inappropriate_type` | export | (value, owned_arg) -> owned_res | 2968 |
| `lean_mk_io_error_inappropriate_type_file` | export | (owned_arg, value, owned_arg) -> owned_res | 2969 |
| `lean_mk_io_error_interrupted` | export | (owned_arg, value, owned_arg) -> owned_res | 2970 |
| `lean_mk_io_error_invalid_argument` | export | (value, owned_arg) -> owned_res | 2971 |
| `lean_mk_io_error_invalid_argument_file` | export | (owned_arg, value, owned_arg) -> owned_res | 2972 |
| `lean_mk_io_error_no_file_or_directory` | export | (owned_arg, value, owned_arg) -> owned_res | 2973 |
| `lean_mk_io_error_no_such_thing` | export | (value, owned_arg) -> owned_res | 2974 |
| `lean_mk_io_error_no_such_thing_file` | export | (owned_arg, value, owned_arg) -> owned_res | 2975 |
| `lean_mk_io_error_other_error` | export | (value, owned_arg) -> owned_res | 2976 |
| `lean_mk_io_error_permission_denied` | export | (value, owned_arg) -> owned_res | 2977 |
| `lean_mk_io_error_permission_denied_file` | export | (owned_arg, value, owned_arg) -> owned_res | 2978 |
| `lean_mk_io_error_protocol_error` | export | (value, owned_arg) -> owned_res | 2979 |
| `lean_mk_io_error_resource_busy` | export | (value, owned_arg) -> owned_res | 2980 |
| `lean_mk_io_error_resource_exhausted` | export | (value, owned_arg) -> owned_res | 2981 |
| `lean_mk_io_error_resource_exhausted_file` | export | (owned_arg, value, owned_arg) -> owned_res | 2982 |
| `lean_mk_io_error_resource_vanished` | export | (value, owned_arg) -> owned_res | 2983 |
| `lean_mk_io_error_time_expired` | export | (value, owned_arg) -> owned_res | 2984 |
| `lean_mk_io_error_unsatisfied_constraints` | export | (value, owned_arg) -> owned_res | 2985 |
| `lean_mk_io_error_unsupported_operation` | export | (value, owned_arg) -> owned_res | 2986 |
| `lean_mk_io_user_error` | export | (str: owned_arg) -> owned_res | 2987 |
| `lean_mk_string` | export | (s: value) -> owned_res | 1216 |
| `lean_mk_string_from_bytes` | export | (s: value, sz: value) -> owned_res | 1213 |
| `lean_mk_string_from_bytes_unchecked` | export | (s: value, sz: value) -> owned_res | 1214 |
| `lean_mk_string_unchecked` | export | (s: value, sz: value, len: value) -> owned_res | 1212 |
| `lean_mk_thunk` | inline | (c: owned_arg) -> owned_res | 1278 |
| `lean_name_eq` | export | (n1: borrowed_arg, n2: borrowed_arg) -> value | 3001 |
| `lean_name_hash` | inline | (n: borrowed_arg) -> value | 3008 |
| `lean_name_hash_ptr` | inline | (n: borrowed_arg) -> value | 3003 |
| `lean_nat_abs` | inline | (i: borrowed_arg) -> owned_res | 1877 |
| `lean_nat_add` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1423 |
| `lean_nat_big_add` | export | (a1: raw_object, a2: raw_object) -> raw_object | 1383 |
| `lean_nat_big_div` | export | (a1: raw_object, a2: raw_object) -> raw_object | 1387 |
| `lean_nat_big_div_exact` | export | (a1: raw_object, a2: raw_object) -> raw_object | 1388 |
| `lean_nat_big_eq` | export | (a1: raw_object, a2: raw_object) -> value | 1390 |
| `lean_nat_big_land` | export | (a1: raw_object, a2: raw_object) -> raw_object | 1393 |
| `lean_nat_big_le` | export | (a1: raw_object, a2: raw_object) -> value | 1391 |
| `lean_nat_big_lor` | export | (a1: raw_object, a2: raw_object) -> raw_object | 1394 |
| `lean_nat_big_lt` | export | (a1: raw_object, a2: raw_object) -> value | 1392 |
| `lean_nat_big_mod` | export | (a1: raw_object, a2: raw_object) -> raw_object | 1389 |
| `lean_nat_big_mul` | export | (a1: raw_object, a2: raw_object) -> raw_object | 1385 |
| `lean_nat_big_shiftr` | export | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1570 |
| `lean_nat_big_sub` | export | (a1: raw_object, a2: raw_object) -> raw_object | 1384 |
| `lean_nat_big_succ` | export | (a: raw_object) -> raw_object | 1382 |
| `lean_nat_big_xor` | export | (a1: raw_object, a2: raw_object) -> raw_object | 1395 |
| `lean_nat_dec_eq` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> value | 1509 |
| `lean_nat_dec_le` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> value | 1527 |
| `lean_nat_dec_lt` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> value | 1541 |
| `lean_nat_div` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1459 |
| `lean_nat_div_exact` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1473 |
| `lean_nat_eq` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> value | 1499 |
| `lean_nat_gcd` | export | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1572 |
| `lean_nat_land` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1545 |
| `lean_nat_le` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> value | 1517 |
| `lean_nat_log2` | export | (a: borrowed_arg) -> owned_res | 1573 |
| `lean_nat_lor` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1553 |
| `lean_nat_lt` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> value | 1531 |
| `lean_nat_lxor` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1561 |
| `lean_nat_mod` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1486 |
| `lean_nat_mul` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1443 |
| `lean_nat_ne` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> value | 1513 |
| `lean_nat_overflow_mul` | export | (a1: value, a2: value) -> raw_object | 1386 |
| `lean_nat_pow` | export | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1571 |
| `lean_nat_pred` | inline | (n: borrowed_arg) -> owned_res | 3251 |
| `lean_nat_shiftl` | export | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1569 |
| `lean_nat_shiftr` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1575 |
| `lean_nat_sub` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> owned_res | 1430 |
| `lean_nat_succ` | inline | (a: borrowed_arg) -> owned_res | 1416 |
| `lean_nat_to_int` | inline | (a: owned_arg) -> owned_res | 1641 |
| `lean_notify_assert` | export | (fileName: value, line: value, condition: value) -> value | 66 |
| `lean_obj_once` | inline | (loc: raw_object, tok: value, raw_object) -> raw_object | 3278 |
| `lean_obj_once_cold` | export | (loc: raw_object, tok: value, raw_object) -> raw_object | 3276 |
| `lean_obj_tag` | inline | (o: raw_object) -> value | 597 |
| `lean_object_byte_size` | export | (o: raw_object) -> value | 526 |
| `lean_object_data_byte_size` | export | (o: raw_object) -> value | 533 |
| `lean_panic` | export | (msg: value, force_stderr: value) -> value | 332 |
| `lean_panic_fn` | export | (default_val: raw_object, msg: raw_object) -> raw_object | 333 |
| `lean_panic_fn_borrowed` | export | (default_val: borrowed_arg, msg: raw_object) -> raw_object | 334 |
| `lean_ptr_addr` | inline | (a: borrowed_arg) -> value | 2998 |
| `lean_ptr_other` | inline | (o: raw_object) -> value | 517 |
| `lean_ptr_tag` | inline | (o: raw_object) -> value | 513 |
| `lean_register_external_class` | export | (value, value) -> value | 315 |
| `lean_run_main` | export | (raw_object, argc: value, argv: value) -> raw_object | 3348 |
| `lean_runtime_hold` | inline | (a: borrowed_arg) -> owned_res | 3259 |
| `lean_sarray_byte_size` | inline | (o: raw_object) -> value | 1048 |
| `lean_sarray_capacity` | inline | (o: raw_object) -> value | 1047 |
| `lean_sarray_cptr` | inline | (o: raw_object) -> value | 1060 |
| `lean_sarray_data_byte_size` | inline | (o: raw_object) -> value | 1052 |
| `lean_sarray_dec_eq` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> value | 1067 |
| `lean_sarray_elem_size` | inline | (o: raw_object) -> value | 1043 |
| `lean_sarray_eq` | inline | (a1: borrowed_arg, a2: borrowed_arg) -> value | 1063 |
| `lean_sarray_eq_cold` | export | (a1: borrowed_arg, a2: borrowed_arg) -> value | 1062 |
| `lean_sarray_set_size` | inline | (o: unique_arg, sz: value) -> value | 1055 |
| `lean_sarray_size` | inline | (o: borrowed_arg) -> value | 1051 |
| `lean_scalar_to_int` | inline | (a: borrowed_arg) -> value | 1633 |
| `lean_scalar_to_int64` | inline | (a: borrowed_arg) -> value | 1625 |
| `lean_set_exit_on_panic` | export | (flag: value) -> value | 328 |
| `lean_set_external_data` | inline | (o: raw_object, data: value) -> raw_object | 1367 |
| `lean_set_non_heap_header` | inline | (o: raw_object, sz: value, tag: value, other: value) -> value | 647 |
| `lean_set_non_heap_header_for_big` | inline | (o: raw_object, tag: value, other: value) -> value | 658 |
| `lean_set_panic_messages` | export | (flag: value) -> value | 330 |
| `lean_set_st_header` | inline | (o: raw_object, tag: value, other: value) -> value | 635 |
| `lean_slice_dec_lt` | export | (s1: borrowed_arg, s2: borrowed_arg) -> value | 1274 |
| `lean_slice_hash` | export | (borrowed_arg) -> value | 1273 |
| `lean_small_mem_size` | export | (p: value) -> value | 402 |
| `lean_small_object_size` | inline | (o: raw_object) -> value | 467 |
| `lean_st_mk_ref` | export | (owned_arg) -> owned_res | 2991 |
| `lean_st_ref_get` | export | (borrowed_arg) -> owned_res | 2992 |
| `lean_st_ref_reset` | export | (borrowed_arg) -> owned_res | 2994 |
| `lean_st_ref_set` | export | (borrowed_arg, owned_arg) -> owned_res | 2993 |
| `lean_st_ref_swap` | export | (borrowed_arg, owned_arg) -> owned_res | 2995 |
| `lean_strict_and` | inline | (b1: value, b2: value) -> value | 3219 |
| `lean_strict_or` | inline | (b1: value, b2: value) -> value | 3215 |
| `lean_string_append` | export | (s1: owned_arg, s2: borrowed_arg) -> owned_res | 1225 |
| `lean_string_byte_size` | inline | (o: raw_object) -> value | 1209 |
| `lean_string_capacity` | inline | (o: raw_object) -> value | 1208 |
| `lean_string_compare` | export | (s1: borrowed_arg, s2: borrowed_arg) -> value | 1267 |
| `lean_string_cstr` | inline | (o: borrowed_arg) -> value | 1217 |
| `lean_string_data` | export | (s: owned_arg) -> owned_res | 1228 |
| `lean_string_data_byte_size` | inline | (o: raw_object) -> value | 1223 |
| `lean_string_dec_eq` | inline | (s1: borrowed_arg, s2: borrowed_arg) -> value | 1268 |
| `lean_string_dec_lt` | inline | (s1: borrowed_arg, s2: borrowed_arg) -> value | 1269 |
| `lean_string_eq` | inline | (s1: borrowed_arg, s2: borrowed_arg) -> value | 1262 |
| `lean_string_eq_cold` | export | (s1: borrowed_arg, s2: borrowed_arg) -> value | 1261 |
| `lean_string_get_byte_fast` | inline | (s: borrowed_arg, i: borrowed_arg) -> value | 1238 |
| `lean_string_hash` | export | (borrowed_arg) -> value | 1270 |
| `lean_string_len` | inline | (o: borrowed_arg) -> value | 1222 |
| `lean_string_length` | inline | (s: borrowed_arg) -> owned_res | 1226 |
| `lean_string_lt` | export | (s1: borrowed_arg, s2: borrowed_arg) -> value | 1266 |
| `lean_string_memcmp` | export | (s1: borrowed_arg, s2: borrowed_arg, lstart: borrowed_arg, rstart: borrowed_arg, len: borrowed_arg) -> value | 1272 |
| `lean_string_mk` | export | (cs: owned_arg) -> owned_res | 1227 |
| `lean_string_ne` | inline | (s1: borrowed_arg, s2: borrowed_arg) -> value | 1265 |
| `lean_string_of_usize` | export | (value) -> owned_res | 1271 |
| `lean_string_push` | export | (s: owned_arg, c: value) -> owned_res | 1224 |
| `lean_string_size` | inline | (o: borrowed_arg) -> value | 1221 |
| `lean_string_utf8_at_end` | inline | (s: borrowed_arg, i: borrowed_arg) -> value | 1256 |
| `lean_string_utf8_byte_size` | inline | (s: borrowed_arg) -> owned_res | 1260 |
| `lean_string_utf8_extract` | export | (s: borrowed_arg, b: borrowed_arg, e: borrowed_arg) -> owned_res | 1259 |
| `lean_string_utf8_get` | export | (s: borrowed_arg, i: borrowed_arg) -> value | 1229 |
| `lean_string_utf8_get_fast` | inline | (s: borrowed_arg, i: borrowed_arg) -> value | 1231 |
| `lean_string_utf8_get_fast_cold` | export | (str: value, i: value, size: value, c: value) -> value | 1230 |
| `lean_string_utf8_next` | export | (s: borrowed_arg, i: borrowed_arg) -> owned_res | 1244 |
| `lean_string_utf8_next_fast` | inline | (s: borrowed_arg, i: borrowed_arg) -> owned_res | 1246 |
| `lean_string_utf8_next_fast_cold` | export | (i: value, c: value) -> owned_res | 1245 |
| `lean_string_utf8_prev` | export | (s: borrowed_arg, i: borrowed_arg) -> owned_res | 1254 |
| `lean_string_utf8_set` | export | (s: owned_arg, i: borrowed_arg, c: value) -> owned_res | 1255 |
| `lean_system_platform_target` | inline | (_unit: owned_arg) -> owned_res | 3243 |
| `lean_task_bind` | inline | (x: owned_arg, f: owned_arg, prio: owned_arg, sync: value) -> owned_res | 1323 |
| `lean_task_bind_core` | export | (x: owned_arg, f: owned_arg, prio: value, sync: value, keep_alive: value) -> owned_res | 1321 |
| `lean_task_get` | export | (t: borrowed_arg) -> borrowed_res | 1327 |
| `lean_task_get_own` | inline | (t: owned_arg) -> owned_res | 1329 |
| `lean_task_map` | inline | (f: owned_arg, t: owned_arg, prio: owned_arg, sync: value) -> owned_res | 1326 |
| `lean_task_map_core` | export | (f: owned_arg, t: owned_arg, prio: value, sync: value, keep_alive: value) -> owned_res | 1324 |
| `lean_task_pure` | export | (a: owned_arg) -> owned_res | 1320 |
| `lean_task_spawn` | inline | (c: owned_arg, prio: owned_arg) -> owned_res | 1318 |
| `lean_task_spawn_core` | export | (c: owned_arg, prio: value, keep_alive: value) -> owned_res | 1316 |
| `lean_thunk_get` | inline | (t: borrowed_arg) -> borrowed_res | 1297 |
| `lean_thunk_get_core` | export | (t: raw_object) -> raw_object | 1295 |
| `lean_thunk_get_own` | inline | (t: borrowed_arg) -> owned_res | 1304 |
| `lean_thunk_pure` | inline | (v: owned_arg) -> owned_res | 1287 |
| `lean_to_array` | inline | (o: raw_object) -> value | 603 |
| `lean_to_closure` | inline | (o: raw_object) -> value | 602 |
| `lean_to_ctor` | inline | (o: raw_object) -> value | 601 |
| `lean_to_external` | inline | (o: raw_object) -> value | 610 |
| `lean_to_promise` | inline | (o: raw_object) -> value | 608 |
| `lean_to_ref` | inline | (o: raw_object) -> value | 609 |
| `lean_to_sarray` | inline | (o: raw_object) -> value | 604 |
| `lean_to_string` | inline | (o: raw_object) -> value | 605 |
| `lean_to_task` | inline | (o: raw_object) -> value | 607 |
| `lean_to_thunk` | inline | (o: raw_object) -> value | 606 |
| `lean_uint16_add` | inline | (a1: value, a2: value) -> value | 1958 |
| `lean_uint16_complement` | inline | (a: value) -> value | 1968 |
| `lean_uint16_dec_eq` | inline | (a1: value, a2: value) -> value | 1978 |
| `lean_uint16_dec_le` | inline | (a1: value, a2: value) -> value | 1980 |
| `lean_uint16_dec_lt` | inline | (a1: value, a2: value) -> value | 1979 |
| `lean_uint16_div` | inline | (a1: value, a2: value) -> value | 1961 |
| `lean_uint16_land` | inline | (a: value, b: value) -> value | 1963 |
| `lean_uint16_log2` | inline | (a: value) -> value | 1970 |
| `lean_uint16_lor` | inline | (a: value, b: value) -> value | 1964 |
| `lean_uint16_mod` | inline | (a1: value, a2: value) -> value | 1962 |
| `lean_uint16_mul` | inline | (a1: value, a2: value) -> value | 1960 |
| `lean_uint16_neg` | inline | (a: value) -> value | 1969 |
| `lean_uint16_of_big_nat` | export | (a: borrowed_arg) -> value | 1953 |
| `lean_uint16_of_nat` | inline | (a: borrowed_arg) -> value | 1954 |
| `lean_uint16_of_nat_mk` | inline | (a: owned_arg) -> value | 1956 |
| `lean_uint16_once` | inline | (loc: value, tok: value, value) -> value | 3296 |
| `lean_uint16_once_cold` | export | (loc: value, tok: value, value) -> value | 3294 |
| `lean_uint16_shift_left` | inline | (a: value, b: value) -> value | 1966 |
| `lean_uint16_shift_right` | inline | (a: value, b: value) -> value | 1967 |
| `lean_uint16_sub` | inline | (a1: value, a2: value) -> value | 1959 |
| `lean_uint16_to_float` | inline | (a: value) -> value | 3089 |
| `lean_uint16_to_float32` | inline | (a: value) -> value | 3166 |
| `lean_uint16_to_nat` | inline | (a: value) -> owned_res | 1957 |
| `lean_uint16_to_uint32` | inline | (a: value) -> value | 1984 |
| `lean_uint16_to_uint64` | inline | (a: value) -> value | 1985 |
| `lean_uint16_to_uint8` | inline | (a: value) -> value | 1983 |
| `lean_uint16_to_usize` | inline | (a: value) -> value | 1986 |
| `lean_uint16_xor` | inline | (a: value, b: value) -> value | 1965 |
| `lean_uint32_add` | inline | (a1: value, a2: value) -> value | 1995 |
| `lean_uint32_complement` | inline | (a: value) -> value | 2005 |
| `lean_uint32_dec_eq` | inline | (a1: value, a2: value) -> value | 2015 |
| `lean_uint32_dec_le` | inline | (a1: value, a2: value) -> value | 2017 |
| `lean_uint32_dec_lt` | inline | (a1: value, a2: value) -> value | 2016 |
| `lean_uint32_div` | inline | (a1: value, a2: value) -> value | 1998 |
| `lean_uint32_land` | inline | (a: value, b: value) -> value | 2000 |
| `lean_uint32_log2` | inline | (a: value) -> value | 2007 |
| `lean_uint32_lor` | inline | (a: value, b: value) -> value | 2001 |
| `lean_uint32_mod` | inline | (a1: value, a2: value) -> value | 1999 |
| `lean_uint32_mul` | inline | (a1: value, a2: value) -> value | 1997 |
| `lean_uint32_neg` | inline | (a: value) -> value | 2006 |
| `lean_uint32_of_big_nat` | export | (a: borrowed_arg) -> value | 1990 |
| `lean_uint32_of_nat` | inline | (a: borrowed_arg) -> value | 1991 |
| `lean_uint32_of_nat_mk` | inline | (a: owned_arg) -> value | 1993 |
| `lean_uint32_once` | inline | (loc: value, tok: value, value) -> value | 3305 |
| `lean_uint32_once_cold` | export | (loc: value, tok: value, value) -> value | 3303 |
| `lean_uint32_shift_left` | inline | (a: value, b: value) -> value | 2003 |
| `lean_uint32_shift_right` | inline | (a: value, b: value) -> value | 2004 |
| `lean_uint32_sub` | inline | (a1: value, a2: value) -> value | 1996 |
| `lean_uint32_to_float` | inline | (a: value) -> value | 3090 |
| `lean_uint32_to_float32` | inline | (a: value) -> value | 3167 |
| `lean_uint32_to_nat` | inline | (a: value) -> owned_res | 1994 |
| `lean_uint32_to_uint16` | inline | (a: value) -> value | 2021 |
| `lean_uint32_to_uint64` | inline | (a: value) -> value | 2022 |
| `lean_uint32_to_uint8` | inline | (a: value) -> value | 2020 |
| `lean_uint32_to_usize` | inline | (a: value) -> value | 2023 |
| `lean_uint32_xor` | inline | (a: value, b: value) -> value | 2002 |
| `lean_uint64_add` | inline | (a1: value, a2: value) -> value | 2032 |
| `lean_uint64_complement` | inline | (a: value) -> value | 2042 |
| `lean_uint64_dec_eq` | inline | (a1: value, a2: value) -> value | 2052 |
| `lean_uint64_dec_le` | inline | (a1: value, a2: value) -> value | 2054 |
| `lean_uint64_dec_lt` | inline | (a1: value, a2: value) -> value | 2053 |
| `lean_uint64_div` | inline | (a1: value, a2: value) -> value | 2035 |
| `lean_uint64_land` | inline | (a: value, b: value) -> value | 2037 |
| `lean_uint64_log2` | inline | (a: value) -> value | 2044 |
| `lean_uint64_lor` | inline | (a: value, b: value) -> value | 2038 |
| `lean_uint64_mix_hash` | inline | (h: value, k: value) -> value | 2055 |
| `lean_uint64_mod` | inline | (a1: value, a2: value) -> value | 2036 |
| `lean_uint64_mul` | inline | (a1: value, a2: value) -> value | 2034 |
| `lean_uint64_neg` | inline | (a: value) -> value | 2043 |
| `lean_uint64_of_big_nat` | export | (a: borrowed_arg) -> value | 2028 |
| `lean_uint64_of_nat` | inline | (a: borrowed_arg) -> value | 2029 |
| `lean_uint64_of_nat_mk` | inline | (a: owned_arg) -> value | 2031 |
| `lean_uint64_once` | inline | (loc: value, tok: value, value) -> value | 3314 |
| `lean_uint64_once_cold` | export | (loc: value, tok: value, value) -> value | 3312 |
| `lean_uint64_shift_left` | inline | (a: value, b: value) -> value | 2040 |
| `lean_uint64_shift_right` | inline | (a: value, b: value) -> value | 2041 |
| `lean_uint64_sub` | inline | (a1: value, a2: value) -> value | 2033 |
| `lean_uint64_to_float` | inline | (a: value) -> value | 3091 |
| `lean_uint64_to_float32` | inline | (a: value) -> value | 3168 |
| `lean_uint64_to_nat` | inline | (n: value) -> owned_res | 1409 |
| `lean_uint64_to_uint16` | inline | (a: value) -> value | 2068 |
| `lean_uint64_to_uint32` | inline | (a: value) -> value | 2069 |
| `lean_uint64_to_uint8` | inline | (a: value) -> value | 2067 |
| `lean_uint64_to_usize` | inline | (a: value) -> value | 2070 |
| `lean_uint64_xor` | inline | (a: value, b: value) -> value | 2039 |
| `lean_uint8_add` | inline | (a1: value, a2: value) -> value | 1920 |
| `lean_uint8_complement` | inline | (a: value) -> value | 1930 |
| `lean_uint8_dec_eq` | inline | (a1: value, a2: value) -> value | 1940 |
| `lean_uint8_dec_le` | inline | (a1: value, a2: value) -> value | 1942 |
| `lean_uint8_dec_lt` | inline | (a1: value, a2: value) -> value | 1941 |
| `lean_uint8_div` | inline | (a1: value, a2: value) -> value | 1923 |
| `lean_uint8_land` | inline | (a: value, b: value) -> value | 1925 |
| `lean_uint8_log2` | inline | (a: value) -> value | 1932 |
| `lean_uint8_lor` | inline | (a: value, b: value) -> value | 1926 |
| `lean_uint8_mod` | inline | (a1: value, a2: value) -> value | 1924 |
| `lean_uint8_mul` | inline | (a1: value, a2: value) -> value | 1922 |
| `lean_uint8_neg` | inline | (a: value) -> value | 1931 |
| `lean_uint8_of_big_nat` | export | (a: borrowed_arg) -> value | 1915 |
| `lean_uint8_of_nat` | inline | (a: borrowed_arg) -> value | 1916 |
| `lean_uint8_of_nat_mk` | inline | (a: owned_arg) -> value | 1918 |
| `lean_uint8_once` | inline | (loc: value, tok: value, value) -> value | 3287 |
| `lean_uint8_once_cold` | export | (loc: value, tok: value, value) -> value | 3285 |
| `lean_uint8_shift_left` | inline | (a: value, b: value) -> value | 1928 |
| `lean_uint8_shift_right` | inline | (a: value, b: value) -> value | 1929 |
| `lean_uint8_sub` | inline | (a1: value, a2: value) -> value | 1921 |
| `lean_uint8_to_float` | inline | (a: value) -> value | 3088 |
| `lean_uint8_to_float32` | inline | (a: value) -> value | 3165 |
| `lean_uint8_to_nat` | inline | (a: value) -> owned_res | 1919 |
| `lean_uint8_to_uint16` | inline | (a: value) -> value | 1946 |
| `lean_uint8_to_uint32` | inline | (a: value) -> value | 1947 |
| `lean_uint8_to_uint64` | inline | (a: value) -> value | 1948 |
| `lean_uint8_to_usize` | inline | (a: value) -> value | 1949 |
| `lean_uint8_xor` | inline | (a: value, b: value) -> value | 1927 |
| `lean_unbox` | inline | (o: raw_object) -> value | 326 |
| `lean_unbox_float` | inline | (o: borrowed_arg) -> value | 2905 |
| `lean_unbox_float32` | inline | (o: borrowed_arg) -> value | 2915 |
| `lean_unbox_uint32` | inline | (o: borrowed_arg) -> value | 2869 |
| `lean_unbox_uint64` | inline | (o: borrowed_arg) -> value | 2885 |
| `lean_unbox_usize` | inline | (o: borrowed_arg) -> value | 2895 |
| `lean_unsigned_to_nat` | inline | (n: value) -> owned_res | 1406 |
| `lean_usize_add` | inline | (a1: value, a2: value) -> value | 2078 |
| `lean_usize_add_checked` | inline | (a: value, b: value) -> value | 375 |
| `lean_usize_add_would_overflow` | inline | (a: value, b: value) -> value | 351 |
| `lean_usize_complement` | inline | (a: value) -> value | 2088 |
| `lean_usize_dec_eq` | inline | (a1: value, a2: value) -> value | 2098 |
| `lean_usize_dec_le` | inline | (a1: value, a2: value) -> value | 2100 |
| `lean_usize_dec_lt` | inline | (a1: value, a2: value) -> value | 2099 |
| `lean_usize_div` | inline | (a1: value, a2: value) -> value | 2081 |
| `lean_usize_land` | inline | (a: value, b: value) -> value | 2083 |
| `lean_usize_log2` | inline | (a: value) -> value | 2090 |
| `lean_usize_lor` | inline | (a: value, b: value) -> value | 2084 |
| `lean_usize_mod` | inline | (a1: value, a2: value) -> value | 2082 |
| `lean_usize_mul` | inline | (a1: value, a2: value) -> value | 2080 |
| `lean_usize_mul_checked` | inline | (a: value, b: value) -> value | 360 |
| `lean_usize_mul_would_overflow` | inline | (a: value, b: value) -> value | 342 |
| `lean_usize_neg` | inline | (a: value) -> value | 2089 |
| `lean_usize_of_big_nat` | export | (a: borrowed_arg) -> value | 2074 |
| `lean_usize_of_nat` | inline | (a: borrowed_arg) -> value | 2075 |
| `lean_usize_of_nat_mk` | inline | (a: owned_arg) -> value | 2077 |
| `lean_usize_once` | inline | (loc: value, tok: value, value) -> value | 3323 |
| `lean_usize_once_cold` | export | (loc: value, tok: value, value) -> value | 3321 |
| `lean_usize_shift_left` | inline | (a: value, b: value) -> value | 2086 |
| `lean_usize_shift_right` | inline | (a: value, b: value) -> value | 2087 |
| `lean_usize_sub` | inline | (a1: value, a2: value) -> value | 2079 |
| `lean_usize_to_float` | inline | (a: value) -> value | 3092 |
| `lean_usize_to_float32` | inline | (a: value) -> value | 3169 |
| `lean_usize_to_nat` | inline | (n: value) -> owned_res | 1400 |
| `lean_usize_to_uint16` | inline | (a: value) -> value | 2106 |
| `lean_usize_to_uint32` | inline | (a: value) -> value | 2107 |
| `lean_usize_to_uint64` | inline | (a: value) -> value | 2108 |
| `lean_usize_to_uint8` | inline | (a: value) -> value | 2105 |
| `lean_usize_xor` | inline | (a: value, b: value) -> value | 2085 |
| `lean_utf8_n_strlen` | export | (str: value, n: value) -> value | 1207 |
| `lean_utf8_strlen` | export | (str: value) -> value | 1206 |
| `lean_version_get_is_release` | inline | (_unit: owned_arg) -> value | 3235 |
| `lean_version_get_major` | inline | (_unit: owned_arg) -> owned_res | 3223 |
| `lean_version_get_minor` | inline | (_unit: owned_arg) -> owned_res | 3227 |
| `lean_version_get_patch` | inline | (_unit: owned_arg) -> owned_res | 3231 |
| `lean_version_get_special_desc` | inline | (_unit: owned_arg) -> owned_res | 3239 |
| `lean_void_mk` | inline | (a: owned_arg) -> owned_res | 2932 |

