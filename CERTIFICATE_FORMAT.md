# Declaration certificate format

Status: **OQ-8 resolved for schema v1**
Owner: W3 bead `fln-7zrh`
Implementation: `crates/fln-hash/src/certificate.rs`
Canonical schema: `fln.canon.declaration-certificate`, version `1`

## Decision

FrankenLean uses two deliberately separate formats.

1. `fln.canon.declaration-certificate/1` is the internal binary accelerator
   envelope. It binds the candidate to its environment, dependencies, declaration,
   term DAG, producer, build, mode, profile, policy, and fuel facts.
2. lean4export NDJSON `3.1.0` is the external kernel-language projection used for
   foreign checkers. It carries names, levels, expressions, and declarations. Facts
   that are not part of that kernel language remain in the certificate/receipt
   sidecar; registered extensions that have no reviewed projection are refused.

There is no projection called “drop.” Expression metadata is the sole nonsemantic
exception: the internal checked-term schema cannot contain it, and lean4export strips
it by default. Unsafe declarations require lean4export’s explicit `--export-unsafe`
option and never acquire authority merely by appearing in an export.

This decision is frozen against:

- lean4export revision
  `4e7915201d3f9f04470d9eae002fa695f7cdc589`, tag `v4.32.0`, format `3.1.0`;
- nanoda revision `ddfac2bf5a7b56cb46e141494427ff3dd55963c7`
  (`nanoda_lib` `0.4.10-beta`) as the first real foreign consumer.

Primary format sources:

- <https://github.com/leanprover/lean4export/tree/4e7915201d3f9f04470d9eae002fa695f7cdc589>
- <https://github.com/leanprover/lean4export/blob/4e7915201d3f9f04470d9eae002fa695f7cdc589/format_ndjson.md>
- <https://github.com/leanprover/lean4export/blob/4e7915201d3f9f04470d9eae002fa695f7cdc589/Export.lean>
- <https://github.com/ammkrn/nanoda_lib/tree/ddfac2bf5a7b56cb46e141494427ff3dd55963c7>

## Authority

A decoded certificate is a `DeclarationCertificateV1`, never an environment,
checked declaration, kernel verdict, or admission token. The codec depends only on
`fln-core`; it cannot call `fln-kernel`, `fln-checker`, or `fln-env`.

The producer’s result is named `ClaimedResultV1` because it is data to compare. The
only use action for a current, correctly bound candidate is `VerifyCandidate`.
Absent, malformed, unsupported, over-budget, cancelled, stale, extension-unknown, or
verification-failed candidates select `Recompute`. An internal fault quarantines the
attempt and selects recomputation in an independent process. None of these actions
returns a verdict.

The simple verifier/fallback execution path is a separate W3 authority. Receipts,
consensus records, signatures, and transparency checkpoints are also separate: they
attest evidence and never admit declarations.

## Canonical framing

All integers are little-endian. All variable bytes and strings use the shared
canonical `u64 length || payload` encoding. Vectors are `u64 count || elements`.
Booleans are exactly `0` or `1`; optionals are exactly `0` or `1 || value`.
Decoding must consume the entire input.

The top-level order is:

1. schema name and `u16` version;
2. binding;
3. judgment;
4. claimed result;
5. term DAG;
6. reduction hints;
7. extensions.

The binding order is:

1. epoch (`u128`);
2. mode;
3. reproducibility profile;
4. build-profile id (`u128`);
5. consensus policy;
6. environment root;
7. strictly increasing dependency roots;
8. declaration root;
9. term-DAG root;
10. kernel build root;
11. checker build root;
12. policy root;
13. registered engine id and nonzero engine version;
14. fuel-profile id, heartbeats, recursion depth, reduction steps, expanded weight,
    and allocation bytes.

Every root is exactly 32 bytes. The term root is recomputed over the encoded term DAG
under `Domain::Receipt`; a mismatch refuses the candidate. The full certificate digest
uses the same domain over the complete canonical envelope. Receipt schema work may
introduce a more specific domain only by adding a registered domain, never by changing
these historical bytes.

## Term DAG

Nodes are numbered by their vector index. Every edge must point to a smaller id, so
the graph is acyclic by construction and needs no recursive validation.

| Tag | Node | Payload |
|---:|---|---|
| 0 | `BVar` | index |
| 1 | `Sort` | canonical `Level` |
| 2 | `Const` | canonical `Name`, universe levels |
| 3 | `App` | function id, argument id |
| 4 | `Lam` | binder name/info, domain id, body id |
| 5 | `Forall` | binder name/info, domain id, body id |
| 6 | `Let` | declaration name, type/value/body ids |
| 7 | `Proj` | type name, projection index, structure id |
| 8 | `NatLiteral` | normalized little-endian limbs |
| 9 | `StringLiteral` | UTF-8 string |

Global names cannot be anonymous. Universe metavariables are refused. Natural
literals are normalized: zero has no limbs and a nonzero value cannot end in a zero
limb. Free variables, expression metavariables, and expression metadata have no
schema-v1 opcode.

## Judgments and claims

Judgment tags are:

| Tag | Judgment |
|---:|---|
| 0 | check declaration |
| 1 | infer type |
| 2 | definitional equality |
| 3 | weak-head normal form |
| 4 | validate inductive group |
| 5 | validate quotient package |

Declaration classes are axiom, definition, theorem, opaque, quotient, inductive,
constructor, and recursor. Claimed results are accepted or rejected; rejected claims
carry one stable class: ill-typed, definitional mismatch, universe violation,
positivity violation, declaration conflict, or unsafe declaration. Resource
exhaustion, cancellation, and internal faults are outcomes of a run and therefore
cannot be encoded as complete result claims.

## Replay hints and extensions

Hints are optional and untrusted:

- tag `0`: unfold one global declaration;
- tag `1`: replay one binary `Nat` operation.

The `Nat` inventory is add, sub, mul, div, mod, pow, gcd, equality, less-or-equal,
less-than, bit-and, bit-or, bit-xor, shift-left, and shift-right. Comparison operations
must carry a Boolean result; every other operation must carry a normalized `Nat`.

Extensions are strictly increasing unique `u32` ids, a critical bit, and opaque
payload bytes. Schema v1 registers no critical extension. Unknown advisory extensions
round-trip byte-for-byte. Any critical extension is therefore unknown and refused.
A future known critical feature requires a new reviewed schema version or a registry
amendment that defines its exact validation and export mapping.

## Resource totality

The caller supplies independent maximum input-byte and produced-node budgets through
`DecodeBudget`. Exceeding either produces `Outcome::Inconclusive`, not malformedness
and not a result claim. The flat outer graph, canonical nested `Name`/`Level` codecs,
no vector preallocation from untrusted counts, checked fixed-width roots/ids, and
whole-input byte budget bound memory and work without a host recursion limit.

An unlimited decode is suitable only for already trusted local bytes. Every artifact
boundary must use the budgeted entry point.

## lean4export alignment

Schema-v1 term nodes map one-for-one to lean4export expression rows. Constructors and
recursors remain members of an `inductive` group, matching export `3.1.0`; they are not
invented as free-standing declaration rows. The exporter’s complete row inventory
(meta, names, levels, expressions, axioms, definitions, opaques, theorems, quotient
package, and inductive groups) is frozen in `Lean4ExportRowV1`.

The following internal facts remain in the certificate/receipt sidecar because a
foreign checker recomputes rather than trusts them: claimed result, environment and
dependency roots, declaration root, engine/build/policy/fuel facts, mode, and build
profile. Extensions require a registered mapping. A projection that cannot represent
a semantic field fails before publishing an export.

The no-mock lane compiles one real Lean declaration with the pinned Reference,
exports its dependency closure filtered to that declaration with the pinned
lean4export binary, and checks it with pinned nanoda. It then presents a malformed
copy, requires typed nonzero failure and no authority, and rechecks the untouched
original byte-for-byte. Semantic results are canonical NDJSON; host, path, duration,
and process facts are kept in separate bounded telemetry.
