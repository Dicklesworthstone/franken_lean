# Lantern wire replay and transcript evidence

FrankenLean exposes five bounded transcript tools over one structural JSON-RPC and Content-Length framing model:

```text
fln-lsp-validate [--client-lifecycle | --client-session] [--] INPUT
fln-lsp-server-validate [--] INPUT
fln-lsp-inspect [--max-frames N] [--] INPUT
fln-lsp-replay [--client-lifecycle | --client-session] [--expect PATH] [--output PATH] [--] INPUT
fln-lsp-correlate [--] CLIENT SERVER
```

`INPUT`, `CLIENT`, and `SERVER` are exact framed byte streams, including headers, separators, and bodies. The tools do not sort or regenerate the supplied stream before validation or replay. Decoded string request IDs are re-escaped canonically only when an identity key or receipt field is constructed.

## Request-ID identity policy

Every strict session and correlation receipt names:

```text
number-lexeme-string-value-v1
```

The policy is intentionally explicit:

- JSON number IDs retain their exact source lexeme. `1.25e2` and `125` are different identities.
- JSON string IDs compare by decoded Unicode value. `"init"` and `"\u0069nit"` are the same identity and are rendered with deterministic JSON escaping.
- `null` remains `null`. It is accepted as a request-shaped ID for compatibility but cannot be a cancellation target.

Strict client-session evidence requires request IDs to be globally unique within the recorded client stream. JSON-RPC permits reuse after a response has completed, but a client-only stream has no server-response clock with which to prove that completion. Global uniqueness is therefore the conservative, timing-independent evidence rule.

## Three client validation grades

The grades are deliberately separate. A stronger grade never changes the meaning of a weaker one.

### 1. Syntax-only validation

```text
fln-lsp-validate INPUT
```

The default mode proves:

- bounded Content-Length framing;
- complete UTF-8 JSON syntax;
- a JSON-RPC 2.0 object envelope;
- deterministic request-ID decoding;
- generic parameter-container validity;
- aggregate frame, role, wire-byte, and body-byte accounting.

It does **not** require a complete lifecycle. This is intentional: malformed-order, role-inverted, and document-invalid streams remain useful inputs for replay and refusal tests.

Its receipt is:

```json
{
  "schema": "fln.lsp-transcript-validation/2",
  "frames": 4,
  "requests": 2,
  "notifications": 2,
  "wireBytes": 293,
  "bodyBytes": 205
}
```

`wireBytes` includes headers, CRLF separators, extension headers, and JSON bodies. `bodyBytes` includes JSON bodies only.

### 2. Client-lifecycle validation

```text
fln-lsp-validate --client-lifecycle INPUT
```

This adds a fail-closed client lifecycle. It requires:

- request-shaped `initialize` as the first frame;
- `initialized` before ordinary running traffic;
- exactly one running-state `shutdown` request;
- `exit` immediately after shutdown;
- no frame after exit and EOF in the terminal state;
- IDs on every known request-only method and no IDs on known notification-only methods;
- object params for known data-bearing methods;
- only missing or `null` params for `shutdown` and `exit`.

Unknown methods remain admissible while running so future extensions do not require weakening the validator. They cannot bypass initialization or terminal ordering.

The lifecycle receipt binds every handshake frame:

```json
{
  "schema": "fln.lsp-client-lifecycle/1",
  "finalState": "exited",
  "frames": 5,
  "requests": 3,
  "notifications": 2,
  "wireBytes": 394,
  "bodyBytes": 284,
  "initializeFrame": 1,
  "initializedFrame": 2,
  "shutdownFrame": 4,
  "exitFrame": 5
}
```

This grade still does not interpret document-session contents or cancellation targets.

### 3. Client-session validation

```text
fln-lsp-validate --client-session INPUT
```

This first requires the complete lifecycle above, then performs a bounded semantic pass over the client document and request session. It validates:

- nonempty `textDocument.uri` values;
- one integer version and complete text on `didOpen`;
- no duplicate open for the same URI;
- `didChange` only for an open document;
- strictly increasing change versions;
- exactly one unambiguous, unranged Full-sync content change;
- `didSave` and `didClose` only for open documents;
- optional save text as one valid string;
- `waitForDiagnostics` only for an open document and a nonnegative target version;
- whether each diagnostic wait targets the currently covered version or a future version;
- canonical global uniqueness for every client request ID;
- each `$/cancelRequest` target is a prior, non-null client request;
- no request is cancelled more than once;
- whether each cancellation targets a diagnostic wait or another request class;
- at most 1,024 simultaneously open documents;
- at most 4 MiB of aggregate open-document URI keys;
- at most 262,144 canonical request IDs and 32 MiB of retained canonical request-ID bytes.

Cancellation state is stored on the already bounded request record. The validator does not retain a second copy of each cancellation target ID.

The validator does not retain source text after each event. It buffers the complete input under the existing 256 MiB transcript ceiling so the lifecycle and semantic passes inspect identical bytes.

A successful session receipt is `fln.lsp-client-session/3` and exposes behavior, identity, and resource state:

```json
{
  "schema": "fln.lsp-client-session/3",
  "finalState": "exited",
  "idPolicy": "number-lexeme-string-value-v1",
  "frames": 10,
  "requests": 3,
  "notifications": 7,
  "wireBytes": 1042,
  "bodyBytes": 812,
  "initializeFrame": 1,
  "initializedFrame": 2,
  "shutdownFrame": 9,
  "exitFrame": 10,
  "documentsOpened": 1,
  "documentsChanged": 1,
  "documentsSaved": 1,
  "documentsClosed": 1,
  "diagnosticWaits": 1,
  "coveredVersionWaits": 0,
  "futureVersionWaits": 1,
  "cancellations": 1,
  "diagnosticWaitCancellationTargets": 1,
  "otherRequestCancellationTargets": 0,
  "uniqueRequestIds": 3,
  "requestIdBytes": 24,
  "requestIdCountCeiling": 262144,
  "requestIdByteCeiling": 33554432,
  "peakOpenDocuments": 1,
  "finalOpenDocuments": 0,
  "peakOpenUriBytes": 14,
  "finalOpenUriBytes": 0
}
```

Open documents are permitted at shutdown because LSP does not require a close notification for every document. The receipt exposes the final count and URI bytes rather than silently pretending cleanup occurred.

## Metadata-only inspection

`fln-lsp-inspect` emits one deterministic `fln.lsp-frame/2` NDJSON row per syntactically valid client frame. Rows contain:

- wire index;
- request or notification role;
- decoded method;
- canonical request-ID JSON, or `null` for a notification;
- `paramsKind` as `missing`, `object`, `array`, or `null`;
- JSON body byte count.

Parameter contents, document text, and source text are never emitted. Inspection buffers its independently bounded output and publishes nothing if a later frame is malformed or the selected frame ceiling is exceeded.

## Replay preflight grades

Default replay preserves adversarial testing:

```text
fln-lsp-replay INPUT
```

A syntactically valid stream may be replayed even when its role, lifecycle, document state, request-ID reuse, or cancellation behavior is deliberately wrong. Lantern itself determines the refusal bytes.

The strict preflights are:

```text
fln-lsp-replay --client-lifecycle INPUT
fln-lsp-replay --client-session INPUT
```

Both run before server execution, expected-stream comparison, stdout emission, or named output publication. `--client-session` is strictly stronger and includes document membership, Full-sync, version, wait-target, request-ID, cancellation-target, and resource validation.

A failed preflight therefore emits no partial server stream and creates no `--output` artifact.

When `--expect PATH` is present, the complete generated server stream is compared byte-for-byte with the expected stream. A mismatch reports the first differing byte offset and both lengths. `--output PATH` uses create-new semantics and never replaces an existing path. Without `--output`, server bytes go to stdout and human refusals remain on stderr.

## Structural server-stream validation

```text
fln-lsp-server-validate INPUT
```

The bounded server profile accepts:

- JSON-RPC 2.0 notifications with no ID and no result/error fields;
- responses with a canonical ID, no method or params, and exactly one `result` or object-valued `error` field;
- error objects with one signed 32-bit integer `code` and one string `message`.

Known Lantern notifications receive stronger payload validation:

- `textDocument/publishDiagnostics`: nonempty URI, diagnostics array, optional integer-or-null version;
- `$/lean/fileProgress`: nonempty `textDocument.uri` and processing array;
- `window/logMessage`: MessageType integer 1 through 4 and nonempty message;
- `$/lean/diagnosticOutcome`: the pinned projection schema plus the complete/authority/diagnostic-count covenant.

The server receipt is `fln.lsp-server-transcript/3`. It separates result responses, error responses, diagnostic publications, diagnostic outcomes, file-progress rows, log messages, and unknown notifications, and reports complete wire bytes, body bytes, decoded metadata bytes, the one-million-frame ceiling, and the 32 MiB decoded-metadata ceiling.

Malformed or duplicate result/error fields, result-plus-error responses, scalar error payloads, response params, notification result/error fields, invalid IDs, and malformed known notification payloads are refused. Server-initiated requests remain outside this bounded profile because the current correlator has no client-response stream with which to close that direction.

## Client/server correlation

```text
fln-lsp-correlate CLIENT SERVER
```

The client must pass `--client-session` semantics. The server must pass the structural server profile above. The join then requires:

- every client request has one globally unique canonical ID;
- every server response has one unique canonical ID;
- every client request ID has exactly one server result or error response;
- no server response refers to an unknown client request;
- client-session request-ID count and byte accounting agree with the independently rebuilt join index;
- each cancellation target still resolves to an earlier client request in the independent join pass;
- validated client request and server response counts equal the join count.

Both client-request and server-response indexes are separately bounded to 262,144 IDs and 32 MiB of canonical ID bytes. The cancellation-target subset is independently bounded by the same ceilings and reported separately.

A successful `fln.lsp-client-server-correlation/4` receipt names its input schemas and includes zero-unmatched response accounting, document/session counts, covered versus future waits, cancellation target classes, and the eventual server-response class for every cancelled target:

- `cancelledTargetRequestCancelledResponses`: error code `-32800`;
- `cancelledTargetResultResponses`: a normal result;
- `cancelledTargetOtherErrorResponses`: any other valid JSON-RPC error.

These three counts must sum to the cancellation-target count. A normal result after a cancellation request is disclosed rather than rejected because cancellation is advisory and separately recorded streams cannot establish whether the response raced with the cancellation.

The join proves identity, shape, classification, and count correlation only. Two independently recorded streams have no shared event clock, so it does **not** claim that a particular response occurred before or after a particular client notification. It also does not yet prove that an arbitrary result payload is semantically correct for its request method.

## What successful replay and correlation prove

For the supplied bytes and current build, successful default replay proves that:

- the stream obeyed Lantern framing strongly enough to reach the dispatcher;
- the dispatcher reached clean shutdown then exit;
- no bytes followed accepted exit;
- replay output remained within its independent ceiling;
- byte comparison and create-new output behavior were deterministic.

Lifecycle and session preflights add their respective client-side claims before any replay side effect. Server validation adds response and known-notification shape. Correlation adds canonical one-to-one request/response accounting and cancellation-response classification over separately validated streams.

Aggregate client, server, input, and expected streams are each bounded to 256 MiB. Replay output and inspection output have independent 256 MiB ceilings. Client document state, canonical request IDs, server decoded metadata, join indexes, and cancellation-target indexes have independent explicit limits.

## Deliberate evidence boundary

These are protocol evidence tools, not substitutes for the complete Lantern or Lean semantic oracle.

The standalone replay callback emits deterministic empty diagnostic sets for accepted document events. Successful replay or correlation therefore does **not** prove:

- source parsing or elaboration;
- kernel admission;
- trustworthy parser/elaborator source spans;
- goal, hover, completion, or definition semantics;
- Lean RPC semantics;
- shared import heaps or dependency invalidation;
- cancellation of active computation;
- crash isolation;
- arbitrary method-specific result correctness;
- cross-stream timing;
- unmodified `vscode-lean4` compatibility.

A release or gate claim must use the production Lantern callback and the required no-mock editor/session scenarios. These tools are useful for shrinking protocol failures, preserving exact framing regressions, proving failure isolation, and separating client, server, identity, cancellation, and later semantic divergence.

## Agent workflow

1. Preserve client and server streams exactly as observed.
2. Use syntax-only validation when invalid lifecycle or document behavior is itself the test subject.
3. Use `--client-lifecycle` for top-level protocol ordering and role claims.
4. Use `--client-session` for positive Full-sync document, request-ID, wait, and cancellation evidence.
5. Validate the server recording independently before interpreting a correlation failure.
6. Use the inspector to locate role, method, ID, and parameter-container mistakes without disclosing document contents.
7. Replay positive sessions with `--client-session --expect` and an unused `--output` path.
8. Correlate the exact client and server recordings when claiming response completeness or cancelled-target response classes.
9. Record executable identity, Git tree, transcript identities, exit status, first divergence, and output identity in the enclosing evidence bundle.
10. Reduce failures only in disposable copies by deleting complete frames; never edit body bytes and Content-Length independently.
11. Keep semantic and telemetry evidence separate. Byte equality, canonical ID joins, and response classifications are semantic protocol facts; host, duration, and path details are telemetry.

## Verification surface

Repository-owned unit and external-process tests cover:

- deterministic argument parsing and end-of-options behavior;
- syntax-only fixture compatibility;
- lifecycle ordering and known role/params contracts;
- document open/change/save/close coherence;
- monotone versions and Full-sync refusal;
- covered and future diagnostic-wait targets;
- canonical request-ID aliases, global uniqueness, and count/byte limits;
- prior-request cancellation targets, duplicate cancellation refusal, and target classes;
- document-count and URI-key resource boundaries;
- strict replay refusal before output publication;
- structural server notifications, result responses, and error responses;
- known server-notification payload refusal;
- duplicate, missing, unsolicited, and numerically normalized response refusal;
- cancelled-target result, RequestCancelled, and other-error classification;
- metadata-only inspection;
- exact replay repeatability and first-divergence reporting;
- deterministic fragment-width and truncated-body transport behavior.
