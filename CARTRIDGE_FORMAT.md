# Certificate cartridge format

Status: **OQ-13 resolved for schema v1**

Owner: W3 bead `franken_lean-eikp`

Implementation: `crates/fln-hash/src/cartridge.rs`
Handoff driver: `crates/fln-hash/examples/cartridge_handoff.rs`

Registered schemas:

- `fln.canon.warm-defeq-cache/1`
- `fln.canon.cartridge-manifest/1`
- `fln.canon.cartridge-archive/1`

## Decision

A certificate cartridge has one logical manifest identity and several transport
populations. The same manifest may be:

- **thin**: no frames are present;
- **partial**: at least one frame is present and at least one required frame is
  absent;
- **sealed**: every required frame is present and optional frames are absent;
- **complete**: every declared frame is present.

Adding or removing frames changes the archive digest but never the manifest root.
This is the thin/sealed law from plan §7.4: a shared-CAS reference and an air-gapped
object pack are transports of one logical cartridge, not different claims.

Frames and objects are content-addressed independently. A frame is validated before
it enters staging. The manifest declares the ordered chunk closure of every object,
so reassembly checks contiguous offsets, lengths, frame identities, and the final
typed object identity. A random-access index is derived from canonical archive bytes;
offsets supplied by a producer are never trusted.

OQ-13 is resolved narrowly: a warm definitional-equality cache is an **optional,
advisory receipt attachment**. It can supply replay hints only after every binding
coordinate is current and the reductions replay. Absence, an unknown version,
malformedness, a resource stop, cancellation, binding drift, replay failure, or an
unknown critical extension selects ordinary verification without the cache. An
internal fault quarantines the attempt and selects independent verification. No cache
state admits or rejects a declaration.

## Authority boundary

`fln-hash::cartridge` depends on `fln-core` and the sibling canonical/hash plane. It
does not depend on `fln-kernel`, `fln-checker`, or `fln-env`, and it exports no
environment mutation or verdict.

A decoded manifest proves only that a logical object graph is canonical and
self-consistent. A decoded archive additionally proves that every present frame is
declared and content-correct. A complete archive proves that the bytes declared by
the manifest are present. None of those facts proves a certificate judgment.

The simple certificate verifier and governed recomputation fallback are the next W3
authority (`fln-eeyn`). The cartridge format deliberately gives that verifier exact
bytes and exact bindings without trying to become it.

The filesystem handoff driver always emits `"authority":false`. Its `verify` command
checks transport completeness, object/frame hashes, the derived index, and nested
certificate and warm-cache codecs; it does not call the kernel or publish a
declaration.

## Shared canonical framing

All integers are little-endian. A `u128` is encoded as low `u64`, then high `u64`.
Variable bytes and UTF-8 strings use `u64 length || payload`. Vectors use
`u64 count || elements`. Booleans are exactly `0` or `1`. An optional value is a
Boolean followed by the value when present. Every digest/root is length-prefixed and
must contain exactly 32 bytes. Decoding must consume the complete input.

Unknown enum tags, noncanonical Booleans, trailing bytes, invalid UTF-8, structural
limit violations, and inconsistent declarations are typed completed refusals.
Exhausting the caller's input-byte or produced-node budget is
`Outcome::Inconclusive`, never malformedness and never a negative verdict.

Schema v1 registers no critical extension. Advisory extensions are strictly
increasing unique `u32` ids and round-trip their opaque payload byte-for-byte. Every
critical extension is unknown and refused.

## Content identities

The format uses the existing frozen `Domain::Receipt` hash domain with typed preimage
headers:

- frame id: canonical `"fln.cartridge.chunk/1" || frame-bytes`;
- object id: canonical `"fln.cartridge.object/1" || object-kind || object-bytes`;
- manifest root: canonical manifest bytes;
- archive digest: canonical archive bytes;
- warm-cache digest: canonical warm-cache bytes.

The typed schema names and object/frame preimage headers keep these uses distinct even
though they share the registered receipt hash domain. Introducing a new hash domain
would require the domain registry and independent host attestations; schema v1 does
not pretend that work happened.

Object ids include the kind. Identical bytes used as a fixture and as a certificate
therefore have different identities. Frame ids do not include an object id, allowing
identical chunks to be shared across objects without changing either object's
identity.

The deterministic builder treats repeated declarations of the same typed object as
one semantic request: `required` dominates `optional`, and the narrowest compatible
portability wins independent of insertion order. Two incompatible platform targets,
or a digest collision whose kind or bytes differ, fail closed as a conflicting object
declaration. The first caller can never silently choose the manifest.

## Manifest

The top-level canonical manifest order is:

1. schema name and `u16` version;
2. epoch (`u128`);
3. environment root;
4. strictly increasing root receipt ids;
5. strictly increasing objects;
6. strictly increasing chunk descriptors;
7. strictly increasing receipt attachments;
8. extensions.

An object record contains:

1. object id;
2. object-kind tag;
3. requirement tag;
4. portability tag and optional target;
5. complete object byte length;
6. ordered chunk references `(chunk id, offset, length)`.

Chunk offsets begin at zero, are contiguous, and sum exactly to the object length.
Every referenced chunk has one descriptor with the same length; every descriptor is
referenced. Empty objects still carry one zero-length frame, so an empty byte string
cannot be confused with an absent object.

Object-kind tags are:

| Tag | Kind |
|---:|---|
| 0 | declaration |
| 1 | dependency |
| 2 | receipt |
| 3 | certificate |
| 4 | fixture |
| 5 | schema |
| 6 | resource contract |
| 7 | witness |
| 8 | warm defeq cache |

Requirement tag `0` is required and tag `1` is optional. A witness or warm cache can
only be optional. Receipt, certificate, declaration, dependency, and warm-cache
objects cannot claim epoch-neutral portability.

Portability tags are:

| Tag | Meaning |
|---:|---|
| 0 | portable across epochs and targets |
| 1 | bound to the manifest epoch |
| 2 | bound to the manifest epoch and exact target string |

A platform target is nonempty, at most 128 ASCII bytes, and consists only of
alphanumeric characters plus `.`, `-`, and `_`. Portability is checked per object;
one incompatible object refuses reuse of that manifest at the destination.

A root receipt is a required object of kind `receipt`. Attachment records join a root
receipt to exactly one role-compatible object. Role tags are certificate, dependency,
fixture, schema, resource contract, witness, and warm cache in that order (`0` through
`6`). Every warm-cache object has exactly one warm-cache attachment and its receipt
also has a certificate attachment.

## Archive, streaming, and staging

The canonical archive order is:

1. schema name and `u16` version;
2. the complete canonical manifest as length-prefixed bytes;
3. strictly increasing present frames `(chunk id, length-prefixed bytes)`.

The nested manifest has its own `DecodeBudget`; the outer archive cannot silently
spend the manifest's allowance. Archive decoding validates the complete outer input,
then validates the nested manifest, then constructs the archive.

`CartridgeStreamDecoderV1` accepts arbitrary input boundaries, including empty pushes
and one-byte chunks. It publishes no archive while buffering. Cancellation and a
buffer limit return `Inconclusive`; only `finish` can publish a decoded value.

Object assembly receives an explicit byte allowance and checks the manifest's complete
logical length before allocation. This matters even when the archive itself is small:
many references to one shared frame can describe a much larger logical object. A
length beyond the allowance is `Inconclusive(ResourceExhausted)`, never malformedness.

`CartridgeStagerV1` starts from a validated manifest. `stage` checks declaration,
length, and digest before mutating its frame map. A corrupt or duplicate frame leaves
the previous staging state unchanged. `finalize_sealed` succeeds only when all
required frames are present; optional frames may remain absent.

`CartridgeIndexV1` parses canonical archive framing and records payload offsets it
observed. An indexed read rechecks its bounds and frame digest. The index is derived
and disposable; it is not part of manifest identity and carries no authority. Its
second framing pass runs under the same explicit outer decode budget rather than
silently reparsing hostile bytes without a meter.

## Warm defeq-cache payload

The cache binding order is:

1. receipt object id;
2. certificate object id;
3. epoch;
4. mode;
5. environment root;
6. kernel build root;
7. checker build root;
8. policy root;
9. fuel-profile root.

Entries are strictly increasing by their complete query key:

1. left term root;
2. right term root;
3. optional expected-type root;
4. transparency (`reducible`, `instances`, `semireducible`, or `all`);
5. common normal-form root;
6. left reduction-root trace;
7. right reduction-root trace.

Each trace is nonempty, begins at its corresponding query term, and ends at the
declared common normal form. These roots are replay instructions, not trusted
reductions. A consumer must match all nine binding coordinates, replay the traces
against the attached certificate terms, and independently confirm the defeq result
before using the hint.

The seven non-attachment coordinates are supplied through
`WarmDefeqContextV1` by the consumer. Receipt and certificate identities come from the
manifest attachment, and the certificate match searches for that exact attached
object rather than accepting whichever certificate sorts first. Constructing this
context from the cache being judged would be tautological and does not satisfy the
API contract.

`classify_present_warm_caches` keeps optional-cache health separate from cartridge
validity. Unsupported, malformed, stale, absent, cancelled, or resource-limited cache
data yields a `VerifyWithoutCache` decision; an internal fault yields
`QuarantineAndVerifyIndependently`. Only corruption of the outer content-addressed
object graph rejects the transport. A caller may consume only `ReplayHints` rows, and
even those remain subject to reduction replay.

The executable OQ-13 action table is:

| State | Action |
|---|---|
| current and exactly bound | replay hints, then verify |
| absent, unsupported, malformed, resource-limited, cancelled | verify without cache |
| binding mismatch, replay failure, unknown critical extension | verify without cache |
| internal fault | quarantine and verify independently |

The receipt attachment is optional in every row. A warm cache can never enter the
required verification closure.

## Structural ceilings

Schema v1 checks these format limits before allocation:

- 1,048,576 objects;
- 1,048,576 root receipts;
- 1,048,576 chunk descriptors;
- 1,048,576 chunks per object;
- 1,048,576 attachments;
- 1,048,576 warm-cache entries;
- 1,048,576 roots per reduction trace;
- 65,536 extensions;
- 16 MiB per extension payload.

These are format ceilings, not host performance claims. Artifact boundaries must also
provide input-byte and produced-node budgets. An unlimited decoder is only for bytes
already trusted by the caller.

## Evidence contract

The named Rust suites are:

- `cartridge_manifest_model`
- `streaming_boundary_property`
- `oq13_decision_model`
- `cartridge_codec_fuzz`

They cover all four transport populations, failure-atomic staging, random access,
portability, binding-field totality, one-byte and every-boundary streaming,
1/8/32 productive semantic identity, truncation and bit corruption, arbitrary bytes,
unknown versions, and typed resource/cancellation outcomes.

The `cartridge_no_mock_e2e` lane packages real filesystem artifacts from the pinned
certificate witness and foreign-checker flow. It verifies and extracts the pristine
pack, refuses a one-variable corrupt copy without publishing extraction state, and
then recovers the untouched pack byte-for-byte. Canonical semantic NDJSON carries
only roots, states, counts, and decisions; paths, timing, process ids, and byte counts
remain in a separate bounded telemetry record.
