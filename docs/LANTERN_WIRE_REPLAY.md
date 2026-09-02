# Lantern wire replay and transcript evidence

FrankenLean exposes four bounded transcript tools over one structural JSON-RPC and Content-Length framing model:

```text
fln-lsp-validate [--client-lifecycle | --client-session] [--] INPUT
fln-lsp-inspect [--max-frames N] [--] INPUT
fln-lsp-replay [--client-lifecycle | --client-session] [--expect PATH] [--output PATH] [--] INPUT
fln-lsp-correlate [--] CLIENT SERVER
```

`INPUT`, `CLIENT`, and `SERVER` are exact framed byte streams, including headers, separators, and bodies. The tools do not normalize, sort, or regenerate the supplied bytes before validation or replay.

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
- lexical request-ID preservation;
- generic parameter-container validity;
- deterministic aggregate frame, role, wire-byte, and body-byte accounting.

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

This grade still does not interpret the contents of document events.

### 3. Client-session validation

```text
fln-lsp-validate --client-session INPUT
```

This first requires the complete lifecycle above, then performs a bounded semantic pass over the client document session. It validates:

- nonempty `textDocument.uri` values;
- one integer version and complete text on `didOpen`;
- no duplicate open for the same URI;
- `didChange` only for an open document;
- strictly increasing change versions;
- exactly one unambiguous, unranged Full-sync content change;
- `didSave` and `didClose` only for open documents;
- optional save text as one valid string;
- `waitForDiagnostics` only for an open document and a nonnegative integer target version;
- non-null numeric or string cancellation IDs;
- at most 1,024 simultaneously open documents;
- at most 4 MiB of aggregate open-document URI keys.

The validator does not retain source text after each event. It buffers the complete input under the existing 256 MiB transcript ceiling so the lifecycle and document-semantic passes inspect identical bytes.

A successful session receipt exposes both behavior and resource state:

```json
{
  "schema": "fln.lsp-client-session/1",
  "finalState": "exited",
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
  "cancellations": 1,
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
- exact lexical request ID, or `null` for a notification;
- `paramsKind` as `missing`, `object`, `array`, or `null`;
- JSON body byte count.

Parameter contents, document text, and source text are never emitted. Inspection buffers its independently bounded output and publishes nothing if a later frame is malformed or the selected frame ceiling is exceeded.

## Replay preflight grades

Default replay preserves adversarial testing:

```text
fln-lsp-replay INPUT
```

A syntactically valid stream may be replayed even when its role, lifecycle, or document state is deliberately wrong. Lantern itself determines the refusal bytes.

The strict preflights are:

```text
fln-lsp-replay --client-lifecycle INPUT
fln-lsp-replay --client-session INPUT
```

Both run before server execution, expected-stream comparison, stdout emission, or named output publication. `--client-session` is strictly stronger and includes document membership, Full-sync, version, wait-target, cancellation-ID, and URI-resource validation.

A failed preflight therefore emits no partial server stream and creates no `--output` artifact.

When `--expect PATH` is present, the complete generated server stream is compared byte-for-byte with the expected stream. A mismatch reports the first differing byte offset and both lengths. `--output PATH` uses create-new semantics and never replaces an existing path. Without `--output`, server bytes go to stdout and human refusals remain on stderr.

## Structural server-stream validation

`fln-lsp-correlate` validates the supplied server stream independently before joining it to the client stream. The current bounded server profile accepts:

- JSON-RPC 2.0 notifications with no ID, no result/error fields, and missing/object/array params;
- responses with an exact lexical ID, no method or params, and exactly one `result` or `error` field;
- error objects with one signed 32-bit integer `code` and one string `message`.

It rejects malformed or duplicate result/error fields, result-plus-error responses, response params, notification result/error fields, invalid IDs, and server-initiated requests. Server-initiated requests are not claimed because the current FrankenLean server does not issue them and the correlation tool has no client-response stream with which to close that direction.

## Exact client/server correlation

```text
fln-lsp-correlate CLIENT SERVER
```

The client must pass `--client-session` semantics. The server must pass the structural server profile above. The join then requires:

- every client request has a unique exact lexical ID;
- every server response has a unique exact lexical ID;
- every client request ID has exactly one server result or error response;
- no server response refers to an unknown client request;
- validated client request and server response counts equal the join count.

Numeric IDs are not normalized. A client ID `1.25e2` does not correlate with a server ID `125`, even though they represent the same mathematical number. FrankenLean's deterministic wire contract requires the server to echo the exact lexical ID it received.

A successful receipt is intentionally zero-unmatched:

```json
{
  "schema": "fln.lsp-client-server-correlation/1",
  "clientFrames": 7,
  "serverFrames": 5,
  "clientRequests": 3,
  "serverResponses": 3,
  "matchedResponses": 3,
  "unmatchedClientRequests": 0,
  "unsolicitedServerResponses": 0,
  "duplicateRequestIds": 0,
  "duplicateResponseIds": 0,
  "resultResponses": 2,
  "errorResponses": 1,
  "serverNotifications": 2,
  "clientWireBytes": 711,
  "serverWireBytes": 552,
  "documentsOpened": 1,
  "documentsChanged": 0,
  "documentsSaved": 0,
  "documentsClosed": 1,
  "diagnosticWaits": 0,
  "cancellations": 0,
  "finalOpenDocuments": 0
}
```

The join proves ID and count correlation only. Two independently recorded streams have no shared event clock, so this tool does **not** claim that a particular response occurred before or after a particular client notification. It also does not claim that a result payload is semantically correct for its method.

## What successful replay and correlation prove

For the supplied bytes and current build, successful default replay proves that:

- the stream obeyed Lantern framing strongly enough to reach the dispatcher;
- the dispatcher reached clean shutdown then exit;
- no bytes followed accepted exit;
- replay output remained within its independent ceiling;
- byte comparison and create-new output behavior were deterministic.

Lifecycle and session preflights add their respective client-side claims before any replay side effect. Correlation adds exact one-to-one request/response accounting over a separately validated server stream.

Aggregate client, server, input, and expected streams are each bounded to 256 MiB. Replay output and inspection output have independent 256 MiB ceilings. Client session state is independently bounded by document count and URI-key bytes.

## Deliberate evidence boundary

These are protocol evidence tools, not substitutes for the complete Lantern or Lean semantic oracle.

The standalone replay callback emits deterministic empty diagnostic sets for accepted document events. Successful replay or correlation therefore does **not** prove:

- source parsing or elaboration;
- kernel admission;
- source-position correctness;
- goal, hover, completion, or definition semantics;
- Lean RPC semantics;
- shared import heaps or dependency invalidation;
- active-work cancellation;
- crash isolation;
- method-specific response correctness;
- cross-stream timing;
- unmodified `vscode-lean4` compatibility.

A release or gate claim must use the production Lantern callback and the required no-mock editor/session scenarios. These tools are useful for shrinking protocol failures, preserving exact framing regressions, proving failure isolation, and separating client, server, correlation, and semantic divergence.

## Agent workflow

1. Preserve client and server streams exactly as observed.
2. Use syntax-only validation when invalid lifecycle or document behavior is itself the test subject.
3. Use `--client-lifecycle` for top-level protocol ordering and role claims.
4. Use `--client-session` for positive Full-sync document-session evidence.
5. Use the inspector to locate role, method, ID, and parameter-container mistakes without disclosing document contents.
6. Replay positive sessions with `--client-session --expect` and an unused `--output` path.
7. Correlate the exact client and server recordings when claiming response completeness.
8. Record executable identity, Git tree, transcript identities, exit status, first divergence, and output identity in the enclosing evidence bundle.
9. Reduce failures only in disposable copies by deleting complete frames; never edit body bytes and Content-Length independently.
10. Keep semantic and telemetry evidence separate. Byte equality and ID correlation are semantic protocol facts; host, duration, and path details are telemetry.

## Verification surface

Repository-owned unit and external-process tests cover:

- deterministic argument parsing and end-of-options behavior;
- syntax-only fixture compatibility;
- lifecycle ordering and known role/params contracts;
- document open/change/save/close coherence;
- monotone versions and Full-sync refusal;
- wait targets and cancellation IDs;
- document-count and URI-key resource boundaries;
- strict replay refusal before output publication;
- structural server notifications, result responses, and error responses;
- duplicate, missing, unsolicited, and lexically normalized response refusal;
- metadata-only inspection;
- exact replay repeatability and first-divergence reporting;
- deterministic fragment-width and truncated-body transport behavior.
