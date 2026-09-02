# Lantern wire replay and transcript evidence

FrankenLean exposes five bounded transcript tools over one structural JSON-RPC and Content-Length framing model:

```text
fln-lsp-validate [--client-lifecycle | --client-session] [--] INPUT
fln-lsp-server-validate [--] INPUT
fln-lsp-inspect [--max-frames N] [--] INPUT
fln-lsp-replay [--client-lifecycle | --client-session] [--expect PATH] [--output PATH] [--] INPUT
fln-lsp-correlate [--] CLIENT SERVER
```

`INPUT`, `CLIENT`, and `SERVER` are exact framed byte streams, including headers, separators, and bodies. The tools do not sort, normalize, or regenerate the supplied stream before validation or replay. Decoded string request IDs are re-escaped canonically only when an identity key or receipt field is constructed.

## Evidence ladder

The tools deliberately expose different grades. A stronger grade adds claims; it does not retroactively change the meaning of a weaker receipt.

| Grade | Command | Receipt | Additional authority |
|---|---|---|---|
| Framing and JSON shape | `fln-lsp-validate INPUT` | `fln.lsp-transcript-validation/2` | Complete framed bytes, valid UTF-8 JSON-RPC objects, roles, and wire/body accounting. |
| Client lifecycle | `fln-lsp-validate --client-lifecycle INPUT` | `fln.lsp-client-lifecycle/1` | Initialize/initialized/shutdown/exit order plus known request/notification roles and parameter-container contracts. |
| Client session | `fln-lsp-validate --client-session INPUT` | `fln.lsp-client-session/3` | Full-sync document state, monotone versions, wait classes, canonical request IDs, cancellation targets, and bounded retained metadata. |
| Server structure | `fln-lsp-server-validate INPUT` | `fln.lsp-server-transcript/3` | Response shape, known notification schemas, result/error counts, and bounded decoded server metadata. |
| Bidirectional join | `fln-lsp-correlate CLIENT SERVER` | `fln.lsp-client-server-correlation/5` | One-to-one canonical response IDs, cancellation-response classes, and the current method-to-response contract. |

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
- trustworthy parser/elaborator source spans;
- inner initialize capability correctness beyond the currently checked outer object;
- useful goal, hover, completion, or definition semantics;
- Lean RPC sessions;
- shared import heaps or dependency invalidation;
- cancellation of active computation;
- crash isolation;
- cross-stream timing or response-after-cancellation order;
- complete document-to-progress-to-publication causality;
- unmodified `vscode-lean4` compatibility.

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
9. Record executable identity, Git tree, transcript identities, exit status, first divergence, and output identity in the enclosing evidence bundle.
10. Reduce failures only in disposable copies by deleting complete frames; never edit body bytes and Content-Length independently.
11. Keep semantic facts and telemetry separate. Byte equality, canonical joins, method classes, and response classes are protocol facts; host, duration, and filesystem paths are telemetry.

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
- metadata-only inspection;
- exact replay repeatability and first-divergence reporting;
- deterministic transport behavior for fragmented and truncated frames.
