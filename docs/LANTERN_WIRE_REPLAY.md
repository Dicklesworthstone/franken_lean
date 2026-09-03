# Lantern wire replay and transcript evidence

FrankenLean exposes six bounded transcript tools over one structural JSON-RPC and Content-Length framing model:

```text
fln-lsp-validate [--client-lifecycle | --client-session] [--] INPUT
fln-lsp-server-validate [--] INPUT
fln-lsp-inspect [--max-frames N] [--] INPUT
fln-lsp-replay [--client-lifecycle | --client-session] [--expect PATH] [--output PATH] [--] INPUT
fln-lsp-correlate [--] CLIENT SERVER
fln-lsp-timeline [--] TIMELINE
```

`INPUT`, `CLIENT`, and `SERVER` are exact framed byte streams, including headers, separators, and bodies. The tools do not sort, normalize, or regenerate the supplied stream before validation or replay. Decoded string request IDs are re-escaped canonically only when an identity key or receipt field is constructed.

`TIMELINE` is a distinct, explicitly interleaved recording format. It is not inferred from two independently captured streams. Each outer Content-Length frame carries one typed direction plus one complete inner JSON-RPC object:

```json
{
  "schema": "fln.lsp-interleaved-event/1",
  "direction": "client",
  "message": {
    "jsonrpc": "2.0",
    "id": "init",
    "method": "initialize",
    "params": {}
  }
}
```

The outer stream preserves one recorder-defined event order. The inner client and server messages are reframed canonically only into bounded private projections used by the existing validators; the supplied outer bytes remain the authority for timeline byte accounting.

## Evidence ladder

The tools deliberately expose different grades. A stronger grade adds claims; it does not retroactively change the meaning of a weaker receipt.

| Grade | Command | Receipt | Additional authority |
|---|---|---|---|
| Framing and JSON shape | `fln-lsp-validate INPUT` | `fln.lsp-transcript-validation/2` | Complete framed bytes, valid UTF-8 JSON-RPC objects, roles, and wire/body accounting. |
| Client lifecycle | `fln-lsp-validate --client-lifecycle INPUT` | `fln.lsp-client-lifecycle/1` | Initialize/initialized/shutdown/exit order plus known request/notification roles and parameter-container contracts. |
| Client session | `fln-lsp-validate --client-session INPUT` | `fln.lsp-client-session/3` | Full-sync document state, monotone versions, wait classes, canonical request IDs, cancellation targets, and bounded retained metadata. |
| Server structure | `fln-lsp-server-validate INPUT` | `fln.lsp-server-transcript/3` | Response shape, known notification schemas, result/error counts, and bounded decoded server metadata. |
| Bidirectional join | `fln-lsp-correlate CLIENT SERVER` | `fln.lsp-client-server-correlation/5` | One-to-one canonical response IDs, cancellation-response classes, and the current method-to-response contract. |
| Interleaved record order | `fln-lsp-timeline TIMELINE` | `fln.lsp-interleaved-timeline/1` | All strict projected-stream claims plus request-before-response, initialize-response-before-initialized, shutdown-response-before-exit, cancellation-before-target-response, and no-event-after-exit evidence. |

Default replay intentionally accepts any syntax-valid client stream so malformed lifecycle and document behavior can remain executable negative fixtures. Strict replay preflights add lifecycle or session authority before any server execution or output publication.

## Request-ID identity

Every strict session and correlation receipt names:

```text
number-lexeme-string-value-v1
```

The policy is:

- JSON number IDs retain their exact source lexeme. `1.25e2` and `125` are different identities.
- JSON string IDs compare by decoded Unicode value. `"init"` and `"\u0069nit"` are the same identity and render with deterministic JSON escaping.
- `null` remains `null`. It may identify a request-shaped message for compatibility but cannot be a cancellation target.

Strict client-session evidence requires request IDs to be globally unique within the client recording. JSON-RPC permits reuse after a response completes, but a client-only stream has no server-response clock with which to prove that completion. Global uniqueness is therefore the conservative timing-independent evidence rule.

The interleaved timeline currently preserves that same globally unique profile rather than introducing a second request-ID policy. Its additional order evidence therefore strengthens the existing join without changing canonical identity.

## Syntax-only validation

```text
fln-lsp-validate INPUT
```

This proves:

- bounded Content-Length framing;
- complete UTF-8 JSON syntax;
- JSON-RPC 2.0 object envelopes;
- deterministic request-ID decoding;
- generic parameter-container validity;
- aggregate frame, role, wire-byte, and body-byte accounting.

It does not require a complete lifecycle. Its receipt reports `wireBytes`, including headers and separators, separately from JSON `bodyBytes`.

## Client lifecycle validation

```text
fln-lsp-validate --client-lifecycle INPUT
```

This additionally requires:

- request-shaped `initialize` as frame one;
- `initialized` before ordinary running traffic;
- exactly one running-state `shutdown` request;
- `exit` immediately after shutdown;
- no frame after exit and EOF in the terminal state;
- IDs on known request-only methods and no IDs on known notification-only methods;
- object parameters for known data-bearing methods;
- only missing or `null` parameters for `shutdown` and `exit`.

Unknown methods remain admissible while running so future extensions do not require weakening the validator. They cannot bypass initialization or terminal ordering.

## Client-session validation

```text
fln-lsp-validate --client-session INPUT
```

This first requires the complete lifecycle, then validates the client document and request session:

- nonempty document URIs;
- one integer version and complete source text on `didOpen`;
- no duplicate open for one URI;
- changes, saves, closes, and diagnostic waits only for open documents;
- strictly increasing `didChange` versions;
- exactly one unambiguous, unranged Full-sync content change;
- optional save text as one valid string;
- nonnegative diagnostic-wait target versions;
- covered-versus-future wait classification;
- globally unique canonical request IDs;
- cancellation targets bound to prior non-null requests;
- no duplicate cancellation of one target;
- diagnostic-wait-versus-other-request cancellation classification.

Cancellation state is stored on the existing request record rather than in another copied-ID map.

The principal client-session limits are:

```text
complete client stream:        256 MiB
simultaneously open documents: 1,024
aggregate open URI keys:       4 MiB
canonical request IDs:         262,144
canonical request-ID bytes:    32 MiB
```

`fln.lsp-client-session/3` reports all enforced behavioral and resource quantities, including covered/future waits, cancellation target classes, unique request IDs, request-ID bytes, peak/final open documents, and peak/final URI bytes. It never emits source text.

Open documents are permitted at shutdown because LSP does not require a close notification for every document. The receipt discloses final state instead of pretending cleanup occurred.

## Server transcript validation

```text
fln-lsp-server-validate INPUT
```

The bounded server profile accepts:

- JSON-RPC 2.0 notifications with no ID and no result/error fields;
- responses with a canonical ID, no method or params, and exactly one `result` or object-valued `error` field;
- error objects with one signed 32-bit integer `code` and one string `message`.

Known Lantern notifications receive stronger validation:

- `textDocument/publishDiagnostics`: nonempty URI, diagnostics array, optional integer-or-null version;
- `$/lean/fileProgress`: nonempty `textDocument.uri` and processing array;
- `window/logMessage`: MessageType integer 1 through 4 and nonempty message;
- `$/lean/diagnosticOutcome`: the current projection schema plus the complete/authority/diagnostic-count covenant.

`fln.lsp-server-transcript/3` separates result responses, error responses, diagnostic publications, diagnostic outcomes, file-progress notifications, log messages, and unknown notifications. It reports complete wire bytes, body bytes, decoded method/ID metadata bytes, the one-million-frame ceiling, and the 32 MiB decoded-metadata ceiling.

Malformed or duplicate result/error fields, result-plus-error responses, scalar error payloads, response params, notification result/error fields, invalid IDs, malformed known notification payloads, and server-initiated requests are refused. Server-initiated requests remain outside this bounded profile because the current evidence bundle has no client-response stream with which to close that direction.

## Method-bound bidirectional correlation

```text
fln-lsp-correlate CLIENT SERVER
```

The client must pass `--client-session`. The server must pass the structural server profile. The join requires:

- one globally unique canonical ID for every client request;
- one unique canonical ID for every server response;
- exactly one result or error response for every client request;
- no response for an unknown request;
- agreement between client-session and independently rebuilt request-ID count/byte accounting;
- independent confirmation that each cancellation target names an earlier client request;
- agreement between joined response totals and server result/error totals.

Client-request, server-response, and cancellation-target indexes are independently bounded to 262,144 IDs and 32 MiB of canonical ID bytes.

Correlation schema v5 adds:

```text
methodResponseSchema = fln.lsp-method-response/1
```

For the current bounded dispatcher, each joined response must satisfy this outer contract:

| Client request | Accepted server response |
|---|---|
| `initialize` | object-valued result |
| `shutdown` | `result: null` |
| `textDocument/waitForDiagnostics` | object-valued result, `RequestCancelled` (`-32800`), or `RequestFailed` (`-32803`) |
| `$/lean/plainGoal`, `$/lean/plainTermGoal`, hover, completion, definition | current no-information `result: null` |
| `$/lean/rpc/connect`, `$/lean/rpc/call` | `RequestFailed` (`-32803`) because RPC sessions are not implemented |
| any other request method | `MethodNotFound` (`-32601`) |

The receipt exposes exhaustive counters for each row and requires:

```text
method result classes == validated server result responses
method error classes  == validated server error responses
all method classes    == matched responses
method contract violations == 0
```

This prevents a transcript with the right IDs but the wrong dispatcher behavior from becoming successful evidence. For example, a hover response carrying `MethodNotFound` is rejected because the current server deliberately returns `null` for that no-information method.

The current method contract is intentionally an **outer** contract. It proves that initialize returns an object, not that every capability inside that object is correct. It proves that a successful diagnostic wait returns an object, not yet the exact inner object schema. Semantic editor methods currently return `null`; accepting that result is evidence of present behavior, not proof that useful hover, completion, definition, or goal semantics exist.

## Cancellation-bound response classification

The correlator also classifies the eventual response for each cancelled target:

- `cancelledTargetRequestCancelledResponses`: error `-32800`;
- `cancelledTargetResultResponses`: a normal result;
- `cancelledTargetOtherErrorResponses`: another valid error.

These counts must cover every cancellation target. A result after cancellation is disclosed rather than rejected because cancellation is advisory and independently recorded streams do not reveal whether completion raced with cancellation.

Method-bound response validation and cancellation classification are complementary. The former checks whether the response is legal for the request method; the latter reports how cancelled requests ultimately resolved.

## Interleaved event-order causality

```text
fln-lsp-timeline TIMELINE
```

A timeline is accepted only when every outer event uses exactly the registered event schema and a supported direction, and its `message` is an object-valued inner JSON-RPC message. A raw JSON-RPC frame is not silently treated as an interleaved event.

The validator constructs bounded client and server projections and subjects them to the same strict session, server, correlation, cancellation, and method-response passes described above. It then uses the shared outer record order to establish facts that two independent files cannot establish:

- a server response is never observed before its canonical client request;
- each request has at most one response event;
- the initialize response precedes the client `initialized` notification;
- the shutdown response precedes the client `exit` notification;
- each cancellation targets an earlier request that has not yet responded;
- each cancelled target's eventual response occurs after the cancellation event;
- duplicate cancellation and duplicate response events fail closed;
- no client or server event follows the terminal `exit` event.

The receipt is:

```text
fln.lsp-interleaved-timeline/1
```

and names:

```text
eventSchema     = fln.lsp-interleaved-event/1
causalitySchema = fln.lsp-cross-stream-causality/1
ordering         = record-order-v1
```

It publishes the lifecycle event indices, outer wire/body bytes, projected inner wire bytes, request-ID bytes, all enforced ceilings, cancellation counts, and explicit zero-violation fields. The complete `fln.lsp-client-server-correlation/5` receipt is nested rather than summarized, so downstream agents do not need to join two unbound receipts by prose.

Resource ceilings are explicit and fail closed:

```text
outer timeline bytes:          256 MiB
outer timeline events:         1,000,000
combined projected wire bytes: 256 MiB
canonical request IDs:         262,144
canonical request-ID bytes:    32 MiB
```

`record-order-v1` means only that event A was recorded before event B in the supplied authoritative sequence. It does **not** assert elapsed time, simultaneous arrival, scheduler execution, transport flush completion, CPU activity, or whether cancelled work had started. A producer must separately bind how it generated the sequence before promoting the receipt to production evidence.

The first timeline schema also deliberately stops short of document-check episode causality. It validates the projected client and server document facts, but does not yet prove that a particular `didOpen`/`didChange`/`didSave` caused a particular progress/publication sequence.

## Inspection and replay

`fln-lsp-inspect` emits one deterministic `fln.lsp-frame/2` NDJSON row per syntax-valid client frame. Rows contain index, role, method, canonical ID JSON, `paramsKind`, and body size. Parameter contents and source text are omitted.

```text
fln-lsp-replay INPUT
fln-lsp-replay --client-lifecycle INPUT
fln-lsp-replay --client-session INPUT
```

Strict preflight occurs before dispatcher execution, expected-stream comparison, stdout emission, or create-new output publication. Failed preflight therefore produces no partial server stream and creates no named output artifact.

With `--expect PATH`, the generated server stream is compared byte-for-byte with the expected stream and reports the first differing byte plus both lengths. `--output PATH` uses create-new semantics and never replaces an existing path.

## Evidence boundary

These tools prove bounded protocol facts about supplied recordings. They do not establish:

- source parsing, elaboration, or kernel admission;
- trustworthy elaborator or kernel source spans beyond the parser positions separately exercised by the production CLI tests;
- inner initialize capability correctness beyond the currently checked outer object;
- useful goal, hover, completion, or definition semantics;
- Lean RPC sessions;
- shared import heaps or dependency invalidation;
- cancellation of active computation;
- crash isolation;
- wall-clock timing, duration, scheduler order, or CPU-work intervals;
- complete document-to-progress-to-publication causality;
- that an interleaved recording was produced by the live server rather than a fixture generator;
- unmodified `vscode-lean4` compatibility.

Two independently supplied `CLIENT` and `SERVER` streams still establish no cross-stream order. Only the explicit `TIMELINE` profile makes record-order claims, and those claims remain bounded by the producer identity and ordering semantics attached to the supplied recording.

The standalone replay callback emits deterministic empty diagnostics for accepted document events. Release or gate claims must use the production callback and the required no-mock editor/session scenarios.

## Agent workflow

1. Preserve client and server streams exactly as observed.
2. Use syntax-only validation when invalid lifecycle or document behavior is the test subject.
3. Use `--client-lifecycle` for top-level ordering and method-role claims.
4. Use `--client-session` for positive Full-sync document, request-ID, wait, and cancellation evidence.
5. Validate the server stream independently before interpreting a join failure.
6. Use the inspector to locate role, method, ID, and parameter-container mistakes without disclosing source.
7. Replay positive sessions with `--client-session --expect` and an unused `--output` path.
8. Correlate exact client and server recordings when claiming response completeness, method-bound behavior, or cancellation-response classes.
9. Use an explicitly interleaved timeline only when the recorder can state what its event order means. Never synthesize order by zipping or timestamp-sorting independent streams.
10. Record executable identity, Git tree, transcript or timeline identity, exit status, first divergence, producer identity, and output identity in the enclosing evidence bundle.
11. Reduce failures only in disposable copies by deleting complete frames; never edit body bytes and Content-Length independently.
12. Keep semantic facts and telemetry separate. Byte equality, canonical joins, method classes, response classes, and record order are protocol facts; host, duration, and filesystem paths are telemetry.

## Focused verification surface

Repository-owned unit and installed-binary tests cover:

- deterministic arguments and end-of-options handling;
- syntax-only fixture compatibility;
- lifecycle ordering and role/params contracts;
- Full-sync document membership and monotone versions;
- covered and future diagnostic waits;
- canonical request-ID aliases, uniqueness, and resource limits;
- prior-request cancellation targets and duplicate cancellation refusal;
- strict replay refusal before output publication;
- known server notification schemas;
- missing, duplicate, unsolicited, and numerically normalized response refusal;
- all current request-to-response classes and representative mismatches;
- cancelled-target result, `RequestCancelled`, and other-error classification;
- interleaved response-before-request, lifecycle-response ordering, cancellation ordering, and post-exit refusal;
- nested timeline/correlation receipt accounting;
- metadata-only inspection;
- exact replay repeatability and first-divergence reporting;
- deterministic transport behavior for fragmented and truncated frames.
