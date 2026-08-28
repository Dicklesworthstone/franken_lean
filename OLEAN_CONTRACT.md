# OLEAN_CONTRACT.md — the `.olean`/`.ilean` format at the pin

> **@generated** by `scripts/extract/gen_olean_contract.py` (Rule D5/D9, plan Appendix B). DO NOT EDIT.
> Format constants are derived, never remembered; regenerate with the script.
>
> pin: `leanprover/lean4` `v4.32.0` commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
> — tag and commit are **established here**: cross-checked against the pinned
>   Reference binary's `lean --version` and against every pinned `.olean`
>   artifact's `lean_version` and `githash` fields.
> — tree `15bccb750e9d73cd2a40f488bec389504a87896c` is transcribed from `SUITE.lock` and is now
>   **established at the producer**: every run, before anything is
>   rendered, invokes the one predicate in this repository that establishes
>   it — `scripts/evidence.py vendor-binding`, the same one
>   `scripts/verify_vendor_tree.sh` runs lane-side — which recomputes the
>   staged `vendor/lean4-src` tree and refuses unless it equals the pinned
>   tree. The extractor calls that predicate rather than reimplementing
>   tree hashing, so no second copy of it exists.
> — the **outcome is typed on stderr and is deliberately NOT rendered
>   here**, in three states: `established`; `inconclusive`, where the
>   repository `.git` is absent or is not a directory so the predicate
>   cannot run at all — an FL-INV-07 environment fault, never a verdict
>   about the tree and never a silent pass; and a hard failure, which *is*
>   a verdict and stops extraction. These bytes do not vary with that
>   outcome on purpose: a cold root built by `git archive` has no `.git`,
>   so an artifact that varied would report `--check` DRIFT for the
>   ENVIRONMENT rather than for the contract. The artifact states the rule;
>   the run states the result.
> — so what remains UNESTABLISHED here is narrow and named: a run whose
>   establishment came back `inconclusive` renders these same bytes, and
>   only its stderr says so. Bead
>   `franken_lean-contract-pin-tree-producer-side-f8zo`.
> — what IS bound here is *content*: a sha256 is recorded below for **every**
>   vendored source this extractor reads, and that set is DERIVED from the
>   extractor's own path constants rather than listed, so it cannot fall
>   behind the reads. A change to any of them is caught; a staged tree
>   differing from the pin in a file this extractor does not read is not.
> inventory: `contracts/olean_inventory.json` sha256 `14c1203506c4838059ddda6ba90d62742a4c1e91d0bfe44ed8df193d42c7c2f6`
> rust: `crates/fln-olean/src/format.rs` (rendered from the same inventory)
>
> sources:
> - `vendor/lean4-src/src/runtime/compact.cpp` (736 lines, sha256 `490928b63b781f43956463bc418e3ab1cd218a4f438b72320a463f8dd12cde2c`)
> - `vendor/lean4-src/src/runtime/compact.h` (145 lines, sha256 `89c7868a99e9f494313a5ce6286cf41194e60fea0e0c7178947a0f8ad3673ab6`)
> - `vendor/lean4-src/src/Lean/CompactedRegion.lean` (111 lines, sha256 `56ef2a63c2394faefe590b58a5e3bd239589ddb6657a8523e5b0385800043f94`)
> - `vendor/lean4-src/src/Lean/Environment.lean` (2835 lines, sha256 `100b207523d1005ae87f62f4e1693806854a35c59cd9b3210dfeeaa875d0ff98`)
> - `vendor/lean4-src/src/Lean/Elab/Frontend.lean` (383 lines, sha256 `2616fef6e97c0a898d4b0c0e2207675c23396233748e5bf94b38fd72cf76733d`)
> - `vendor/lean4-src/src/Lean/Data/Lsp/Internal.lean` (426 lines, sha256 `ebcd1850babf4c78f50d03f76d7d1b15b0bd1f3506a8fb8b29db39682a53f6c2`)
> - `vendor/lean4-src/src/library/module.cpp` (632 lines, sha256 `7343bfc1691a72d8550e4159e03f22ba528edb1942963f4cf04bb2bfda0b9469`)
> - `vendor/lean4-src/src/Lean/Server/References.lean` (858 lines, sha256 `b7022ed1a659d5181735d9ef0cd2f13cc2e3f96b11f5ece3e6e5defe8363ee88`)
> - `vendor/lean4-src/src/Lean/Setup.lean` (204 lines, sha256 `7f085003e696df5c29af1dc1342ef3dfaaca70b6eaa5d357ce832abd49e9554c`)

## 1. The fixed header

Magic `"olean"`; fixed size **88 bytes** on LP64
(`size_t` = 8; offsets computed under that law and verified
against the pin's packing `static_assert`). Struct at `vendor/lean4-src/src/library/module.cpp:107`.

| offset | size | field | C type | provenance |
|---|---|---|---|---|
| 0 | 5 | `marker` | `char[5]` | `vendor/lean4-src/src/library/module.cpp:109` |
| 5 | 1 | `version` | `uint8_t` | `vendor/lean4-src/src/library/module.cpp:113` |
| 6 | 1 | `flags` | `uint8_t` | `vendor/lean4-src/src/library/module.cpp:117` |
| 7 | 33 | `lean_version` | `char[33]` | `vendor/lean4-src/src/library/module.cpp:127` |
| 40 | 40 | `githash` | `char[40]` | `vendor/lean4-src/src/library/module.cpp:130` |
| 80 | 8 | `base_addr` | `size_t` | `vendor/lean4-src/src/library/module.cpp:132` |
| 88 | flexible | `data` | `size_t[]` | `vendor/lean4-src/src/library/module.cpp:141` |

Accepted versions: **2, 3**
(`vendor/lean4-src/src/library/module.cpp:492`). v2 is the default format:
compacted data begins immediately at the end of the fixed header. v3
(`CompactedRegion.save (allowClosures := true)`) appends length-prefixed
sections after the header: `size_t data_size`, the compacted data, a
`uint32 num_closure_offsets` + `uint64` array of data-relative closure
`m_fun` offsets, and a `uint32 num_libs` relocation table of
`(size_t base_addr, uint32 id_len, char id[id_len])` rows (documented in the
header comment block itself). `flags` bit 0 records whether persisted bignums
use the GMP encoding; bits 1–7 are reserved.

Region payload and base address are aligned to **65536**
bytes (`vendor/lean4-src/src/library/module.cpp:273`). The file is mmapped at
`base_addr` when possible; every interior pointer was rewritten at save time to
`buffer_offset + base_addr`, so the mmap fast path needs no fixup at all, and
the fallback walk relocates pointer-by-pointer.

## 2. The compacted object graph

There is no field-by-field serializer: the Lean object graph **is** the wire
format. The compactor copies objects into a contiguous buffer (8-byte aligned,
zero-initialized), dedups by pointer identity and structural sharing, stores
the root as the first word of the data region, and rejects external objects.
Mechanically-found anchors into the pinned implementation:

| anchor | role |
|---|---|
| `vendor/lean4-src/src/library/module.cpp:273` (`const size_t ALIGN = `) | region payload/base alignment |
| `vendor/lean4-src/src/runtime/compact.cpp:257` (`void object_compactor::insert_string`) | string layout: header + inline UTF-8, no interior pointers |
| `vendor/lean4-src/src/runtime/compact.cpp:407` (`void object_compactor::insert_mpz`) | bignum layout: limbs copied after the mpz object; one interior pointer rewritten |
| `vendor/lean4-src/src/runtime/compact.cpp:368` (`bool object_compactor::insert_closure`) | closure layout (v3 only): m_fun offsets recorded for the trailer relocation table |
| `vendor/lean4-src/src/runtime/compact.cpp:566` (`object * region_reader::fix_object_ptr`) | load-side pointer fixup: address mapped back to buffer by base-address search |
| `vendor/lean4-src/src/runtime/compact.cpp:663` (`object * region_reader::read()`) | load walk: mmap-at-base fast path, else sequential object walk with fixups |
| `vendor/lean4-src/src/runtime/compact.h:40` (`class LEAN_EXPORT object_compactor {`) | save-side compactor state |
| `vendor/lean4-src/src/runtime/compact.h:103` (`class LEAN_EXPORT region_reader {`) | load-side reader state |

## 3. Lean-side module structures

### `structure ModuleData` — `vendor/lean4-src/src/Lean/Environment.lean:109`

| # | field | type | default | line |
|---|---|---|---|---|
| 0 | `isModule` | `Bool` | — | 111 |
| 1 | `imports` | `Array Import` | — | 112 |
| 2 | `constNames` | `Array Name` | — | 119 |
| 3 | `constants` | `Array ConstantInfo` | — | 120 |
| 4 | `extraConstNames` | `Array Name` | — | 126 |
| 5 | `entries` | `Array (Name × Array EnvExtensionEntry)` | — | 127 |

### `structure Import` — `vendor/lean4-src/src/Lean/Setup.lean:25`

| # | field | type | default | line |
|---|---|---|---|---|
| 0 | `module` | `Name` | — | 26 |
| 1 | `importAll` | `Bool` | `false` | 28 |
| 2 | `isExported` | `Bool` | `true` | 30 |
| 3 | `isMeta` | `Bool` | `false` | 32 |

### `structure Ilean` — `vendor/lean4-src/src/Lean/Server/References.lean:206`

| # | field | type | default | line |
|---|---|---|---|---|
| 0 | `version` | `Nat` | `5` | 208 |
| 1 | `module` | `Name` | — | 210 |
| 2 | `directImports` | `Array Lsp.ImportInfo` | — | 212 |
| 3 | `references` | `Lsp.ModuleRefs` | — | 214 |
| 4 | `decls` | `Lsp.Decls` | — | 216 |

`.ilean` is a JSON document (`FromJson`/`ToJson`), format version
**5**. `EnvExtensionEntry` payloads are opaque by
construction — each extension defines its own encoding via `exportEntriesFn`;
Grimoire preserves unknown payloads losslessly and never guesses (bead
franken_lean-y24 consumes this contract).

