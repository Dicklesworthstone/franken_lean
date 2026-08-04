# FL-INV-06 certificate-accepting path census — `fln-verdict`

Status: current-tree census of every implemented Verdict certificate-acceptance
join and every environment-publication route reachable from one. This is not a
future implementation or whole-Anvil invariant claim.

Evidence classes are intentionally mixed:

- **proof** for sealed-type and dependency reachability over the bound
  implementation inputs;
- **bounded_model** for planted certificate mutants, recovery cases, and the
  six-instance checker-cost corpus;
- **reading** where the current code has no stronger mechanism.

Tracking: the functional Verdict owner `franken_lean-lu5` is closed; the full
W7 owner `fln-h1k` remains open. The self-matching publication source guard
found while producing this census is tracked separately by open bug
`fln-h1k.1`.

## Measurement boundary

- Implementation source tree over the exact closure content:
  `bd30dc91e23e720373d5d82620a9855ee6560970`.
- Test/evidence tree over the exact closure content:
  `134844c9c3d4b18a8ac2c860d587ad99826014b5`.
- `solver.rs` blob:
  `1a37f15c78b3b8e9361032436a979723c85c3adf`.
- `tests/input_validation.rs` blob:
  `80a099aac74cd0f54cccfb5b00550aca747e2906`.
- `Cargo.toml` blob:
  `02f5879da3ac3fd41a5d857edc81473b822cf980`.
- Scope: every public or private callable that forms, decodes, semantically
  validates, or consumes an UNSAT certificate; every sealed intermediate that
  can carry such a certificate; and every environment route reachable from
  one.

Aliases that share one implementation join are grouped in one row. The
certificate-accepting join count in this boundary is exactly **nine**.
Certificate-accepting path cardinality: `9`.

The seventh row was added only after the executable census derived the new
production call at `solve_with_unsat_certificate`: one producer decode, one
independent check, and an exact-CNF `solve` fallback at that site. The eighth
and ninth rows bind the codec's framed decoder and structural-proof serializer;
the cancellation-free decoder is an alias of the framed decoder. Test bodies,
source-reading guard assertions, marker prose, and this document are outside
the call counter. Counting those mutable surfaces and then moving this pin
would bind the claim to its scaffolding rather than to the production consumer.

## Census

| # | Entry point and what it accepts | Unknown or drifted version | Failure disposition | Can engine output reach an environment without a kernel-checked artifact? | How established |
|---:|---|---|---|---|---|
| 1 | `UnsatProof::new(&Cnf, Vec<ProofStep>, SchemaLimits)` accepts structured proof steps and forms a structurally canonical certificate. It validates shape and dependency discipline, not rule semantics. | No wire version exists at this in-memory entry point. Invalid structure is a typed `SchemaError`. | `Err` contains no partial proof. There is no automatic recomputation and no acceptance. | **No.** `UnsatProof` cannot construct the sealed `CheckedUnsat` required by reflection, and no environment API accepts it. | **TYPE ARGUMENT** over private `CheckedUnsat` fields and the absence of any `UnsatProof` environment consumer. **READING** establishes the deliberately structural-only contract. |
| 2 | `UnsatProof::from_canonical_bytes(&[u8], &Cnf, SchemaLimits)` accepts versioned raw proof bytes for structural decoding. | Unknown version, schema kind, extension bits, opcodes, noncanonical bytes, truncation, and trailing bytes are typed `SchemaError`s. A structurally valid semantic mutant can decode by design and is not authority. | `Err` contains no proof. There is no recomputation or acceptance at this decoder; semantic authority requires row 3. | **No.** Its output has the same sealed-type boundary as row 1. | **PLANTED MUTANT:** `corrupted_producer_accepted_proof_is_refused_not_rubber_stamped` proves swapped resolution parents cross this decoder and are refused by row 3. **TYPE ARGUMENT** establishes nonreachability. |
| 3 | `check_unsat_streams` and `check_unsat_streams_with_cancel` share the independent streaming semantic checker over canonical CNF and proof streams. | Unknown CNF or proof versions and malformed, drifted, incomplete, or semantically invalid proofs are typed `Refused`, never `Verified`. | The direct API returns `Refused`, `Inconclusive`, or `InternalFault`; only `Verified` carries a receipt. It does not automatically recompute. The 512-case recovery consumer solves the exact CNF again and accepts only a different, newly checked artifact. | **No.** The receipt is counts-only and has no standalone serialization or admission route. No environment API accepts a `ProofCheckOutcome` or receipt. | **PLANTED MUTANTS:** four proof classes ×128 seeds prove exact refusal, no receipt, fresh recomputation, different replacement bytes, and independent replay. Unknown-version, opcode, corruption, and real-stream recovery cases provide adjacent controls. **TYPE ARGUMENT** covers the receipt algebra; **READING** covers the absence of automatic fallback. |
| 4 | `solve`, `solve_with_cancel`, and the incremental solve wrappers share `Engine::finish_unsat`, which submits the CDCL engine's exact CNF/proof bytes to row 3 before constructing `CheckedUnsat`. | The producer emits only the current schema. No caller can inject a version at this private join; any byte drift presented to row 3 is refused. | Checker refusal becomes `SolverInternalFault::ProofRefused`; checker faults remain `InternalFault`; checker cancellation or exhaustion remains `Inconclusive`. None carries a checked artifact. It does not retry because this path is the recomputation producer itself. | **No.** `CheckedUnsat` fields are private, and its only production construction occurs after `ProofCheckOutcome::Verified`. | **TYPE ARGUMENT** over the closed outcome and sealed constructor. **PLANTED MUTANTS:** the seeded solver/checker campaign and proof-logger corruption cases require every emitted proof to verify and every activated mutation to be refused. **READING** establishes the exhaustive terminal mapping. |
| 5 | `ReflectedTheoremArtifact::from_bitblast_unsat` accepts a `BitblastArtifact` plus sealed `CheckedUnsat` and forms a non-authoritative reflection candidate. | There is no caller-supplied version field. Exact CNF-byte mismatch is `ReflectedArtifactError::CnfMismatch`; row 6 replays the retained bytes again. | Failure is `Err`, with neither recomputation nor candidate acceptance. | **No.** The candidate has private fields, is not `Clone`, is explicitly non-authoritative, and exposes no publication method. | **TYPE ARGUMENT** over the sealed input and candidate. **PLANTED MUTANT:** `reflected_artifact_refuses_a_certificate_from_another_bitblast` activates the join with a checked certificate for distinct CNF bytes and requires exact mismatch refusal. |
| 6 | `publish_reflected_theorem` accepts the non-authoritative candidate, replays its exact certificate, compares the new and retained receipts, kernel-admits the exact owned theorem, names its council, and consumes Crucible's opaque checked capability to publish. | Unknown proof version and proof-byte or receipt drift are refused or typed internal fault before kernel admission/publication. | There is no automatic recomputation. Every proof, kernel, council, admission, cancellation, exhaustion, stale handoff, or duplicate failure returns without publishing; failure never becomes acceptance. | **No, at the bound source.** The only production environment mutation is `checked.publish(...)`, where `checked` is the exact capability returned by the kernel/council path. No raw kernel-check result or caller-owned declaration plan is publishable. | **TYPE ARGUMENT** over the opaque owned capability and exact-theorem handoff. **PLANTED MUTANTS:** unknown proof version, proof corruption, receipt drift, invalid reflected term, checker/kernel exhaustion, cancellation, and duplicate publication all assert an unchanged base; a positive control publishes the kernel-checked owner. **READING:** the positive source-string guard is not counted because `fln-h1k.1` proves it self-matches. |
| 7 | `solve_with_unsat_certificate` accepts an untrusted cached/foreign `UnsatCertificateCandidate`, rebinds it to the caller's exact CNF and current schemas, bounds both retained streams, producer-decodes the proof, and independently checks those exact bytes. `UnsatCertificateCandidate::from_checked` is a projection into that untrusted envelope, not a separate accepting join. | Envelope, declared CNF, declared proof, producer-decoder, independent-CNF-checker, and independent-proof-checker version refusals map to distinct `UnsatCertificateVersionBoundary` values. The full `u16` model permits exactly one current value and returns 65,535 typed `UnsupportedVersion` outcomes at each producer/checker stream boundary. | Every refusal branch calls authoritative `solve(cnf, limits)` on the exact caller-owned CNF. Exact facts record one attempt, refusal, and recomputation; successful recomputation records one recheck/returned artifact, while `Inconclusive`/`InternalFault` records one nonpublication and no artifact. | **No.** A refused attempt has no receipt/artifact field; a nonanswer has no `CheckedSolverArtifact`; the terminal value is never environment authority. Theorem publication still requires rows 5–6 and Crucible's opaque exact-theorem capability. | **PRODUCTION-SITE CENSUS:** the guard binds the decoder call to this function and excludes test/document decoys. **BOUNDED MODEL:** `production_certificate_wrapper_covers_every_reachable_refusal_branch` activates the real join, every reachable refusal class, exact recomputation, input substitution, nonpublication, and the accept/skip/reuse/version/input/nonanswer mutants. `certificate_version_policy_exhausts_the_u16_domain` enumerates all 65,536 values at both producer and independent-checker stream boundaries. Unit tests bind unreachable version mapping arms and both nonanswer packaging arms. |
| 8 | `decode_unsat_proof_with_cancellation` accepts a framed proof stream and an exact caller-owned canonical CNF, checks the proof schema, feature bits, CNF root, framing, bounds, and canonical records, then forms a structural `UnsatProof`. `decode_unsat_proof` is its no-cancellation alias. | Unknown proof schema/version, extension bits, record opcode, noncanonical encoding, truncation, trailing bytes, CNF-root drift, and cancellation are typed `VerdictCodecError` values. | `Err` contains no proof. Structural decoding never produces `CheckedUnsat`; semantic authority still requires row 3. | **No.** The result is only `UnsatProof`, which cannot construct the sealed `CheckedUnsat` required by reflection or an environment-publication route. | **PRODUCTION-SITE CENSUS:** the guard binds this function's one `UnsatProof::new` construction and its no-cancellation alias. **READING** establishes the structural-only result boundary. |
| 9 | `encode_unsat_proof` consumes an already structurally validated `UnsatProof` and writes its versioned canonical framed bytes. | It accepts no untrusted bytes or version field; the output always uses the current proof schema and feature set. | It cannot return a partial certificate because it returns only bytes from an already-constructed proof. | **No.** It neither constructs `CheckedUnsat` nor exposes an environment mutation route; later semantic authority still requires row 3. | **TYPE ARGUMENT** over the closed input/output surface. **PRODUCTION-SITE CENSUS:** the marker binds the serializer as a certificate-consuming production route. |

## Aliases and adjacent non-certificate outputs

`bv_decide` and `bv_decide_with_cancel` are orchestration aliases over rows
4–6, not a seventh certificate input: callers supply a proposition and theorem
request, never proof bytes or a certificate object. Their UNSAT branch can
publish only through row 6.

The SAT branch is adjacent engine-output evidence, not a certificate-accepting
path. `finish_sat` canonicalizes, decodes, and revalidates the model against
the exact CNF; `bv_decide` repeats the CNF/model decode and satisfaction check,
then returns a counterexample with no environment-publication route.

`AttemptOutcome::publishable_artifact` is a legacy projection helper with no
production callable returning `AttemptOutcome` and no environment consumer of
`PublishableArtifact`. Direct enum construction therefore does not create an
admission door. Receipt and artifact accessors likewise project already formed
values and are not additional acceptance joins.

## Simpler-than-recomputation evidence

At the bound source tree:

- the independent checker production prefix is 1,180 physical lines, versus
  2,226 before the solver's first test module;
- `checker.rs` imports only `std` collections and `Read`/`ErrorKind`, owns its
  own wire reader, clause state, and rule semantics, and does not name the
  producer's `UnsatProof`, `ProofStep`, `ProofRule`, `SchemaError`, or
  `from_canonical_bytes`;
- `checker_work_is_strictly_below_recomputation_on_unsat_corpus` requires
  checker work to be strictly lower than solver work on pigeonhole and complete
  assignment-cube instances of sizes 3, 4, and 5.

The third bullet is **bounded_model**, not a universal complexity proof. It
establishes six current corpus rows under the registered work meters. The
structural separation and smaller current source/dependency surface are
stronger than reading alone but do not upgrade that bounded cost measurement
into an invariant over every future certificate.

## Recovery boundary

`solve_with_unsat_certificate` is now the production cached/foreign-certificate
accelerator. It compares the envelope root and complete CNF bytes with the exact
caller-owned formula, checks all declared and embedded versions, enforces both
artifact byte bounds, producer-decodes and independently replays the proof, and
calls `solve` on that same formula after every refusal. It returns a checked
solver artifact, not environment authority.

`production_certificate_wrapper_covers_every_reachable_refusal_branch` calls
that public wrapper, first proving its verified control. Its refusal cells cover
envelope/root/declared-schema/exact-byte/artifact-size/producer/checker/checker-
exhaustion branches, compare every returned outcome with a fresh authoritative
`solve(cnf, limits)`, and bind the attempt/refusal/recompute/recheck/publication/
nonpublication facts. A semantic proof mutant proves the checker-refusal arm ran,
has no receipt, and yields different replacement bytes. An UNSAT candidate
presented with a SAT caller input is root-refused and returns checked SAT, killing
candidate-input substitution. An exhausted checker remains `Inconclusive` with
no artifact.

`certificate_fallback_nonanswers_kill_the_promotion_mutant` feeds both
`Inconclusive` and `InternalFault` through the production result-packaging helper
and requires zero rechecks/publications plus one nonpublication.
`certificate_version_refusals_name_every_decoder_boundary` binds the producer
and both independent-checker stream mappings. The exhaustive `u16` test then
requires one supported value and 65,535 exact typed refusals independently for
CNF producer decode, proof producer decode, CNF checker decode, and proof checker
decode.

The older
`altered_proofs_are_refused_and_recomputed_from_checked_artifacts` remains
supporting bounded evidence: for all 512 activated invalid/version-drifted
inputs it solves the exact CNF again, proves the replacement bytes differ from
the refused bytes, and independently replays the replacement receipt. It is no
longer cited as proof that a production wrapper exists.

The executable census proves that this production join and its decoder/checker
calls exist at the named site; it does not substitute for direct behavioral
coverage of every refusal branch. A future index or theorem-admission fast path
must still add its own production wrapper and planted bypass mutant. Citing the
direct checker or the 512-case harness for such a path would remain the
claim-without-producer defect described in `AGENTS.md`.

## Publication-guard finding

Current production code does consume Crucible's opaque capability, and the
behavioral mutants above exercise the real publication boundary. However,
`kernel_admission_boundary_has_no_raw_check_or_environment_plan_route` reads
all of `reflection.rs` and checks for the literal `checked.publish(`. The same
literal appears in the assertion itself. Removing the production occurrence
leaves the guard-body occurrence, so that positive source check cannot detect
the recurrence it claims to prevent.

Open bug `fln-h1k.1` owns the repair: scope the source census to production and
plant a mutant that removes the actual capability-consumption join. This gap
does not establish a present unchecked path; it disqualifies that one
self-matching assertion as recurrence evidence.

## Claim boundary

Established for the bound Verdict implementation:

- unknown or drifted proof versions do not silently verify;
- checker failure never produces a receipt, checked artifact, or publication;
- solver-produced UNSAT output is independently checked before it can inhabit
  `CheckedUnsat`;
- the cached/foreign-certificate wrapper directly refuses every reachable
  invalid/stale/mismatched/resource/version class and returns the exact
  authoritative recomputation outcome on the caller-owned CNF;
- the full `u16` domain has exactly one supported producer/checker stream
  version and 65,535 typed refusals at each modeled boundary;
- exact fallback cardinalities and nonpublication are tested for checked
  artifacts, `Inconclusive`, and `InternalFault`;
- publication replays the certificate and can mutate an environment only by
  consuming the kernel/council-owned exact-theorem capability;
- the named planted failures leave the base environment unchanged.

Not established:

- a universal proof that checker work is lower than recomputation for every
  input;
- FL-INV-06 enforcement for the stub `fln-anvil` crate or its future simp,
  arithmetic, grind, e-graph, index, or portfolio implementations;
- that the self-matching publication source guard detects removal of the
  production capability join.

The separate `fln-anvil` zero-path census must remain retained while empty.
This nonempty Verdict census does not replace or “tidy away” that evidence.

## Upgrade triggers

Re-run this census when any of the following changes:

1. a public or private certificate decoder, checker, checked-artifact
   constructor, or environment consumer is added;
2. `CheckedUnsat`, `ReflectedTheoremArtifact`, or the kernel publication
   capability changes visibility or construction;
3. the cached/foreign certificate fast path or its recomputation policy changes;
4. the certificate schema, checker policy, solver policy, or bitblast manifest
   version moves;
5. `fln-h1k.1` repairs the publication source guard.

Every new row must prove its planted mutation actually crossed the acceptance
boundary before its typed result, fallback, or nonpublication assertion is
counted.
