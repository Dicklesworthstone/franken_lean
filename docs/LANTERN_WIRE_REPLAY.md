# Lantern wire replay and transcript evidence

FrankenLean exposes three bounded tools over one shared Content-Length frame and structural JSON-RPC model:

```text
fln-lsp-validate [--client-lifecycle] [--] INPUT
fln-lsp-inspect [--max-frames N] [--] INPUT
fln-lsp-replay [--client-lifecycle] [--expect PATH] [--output PATH] [--] INPUT
```

`INPUT` is the exact byte stream received from an LSP client: concatenated `Content-Length` frames, including headers and bodies. The tools do not normalize, sort, or regenerate those bytes before validation or replay.

## Two validation grades

The default `fln-lsp-validate INPUT` mode is deliberately **syntax-only**. It proves bounded framing, complete JSON syntax, JSON-RPC 2.0 envelope shape, lexical request-ID preservation, and generic parameter-container validity. It does not require a complete lifecycle. That permissiveness is intentional because malformed-order and method-role fixtures are useful inputs to the replay and refusal tests.

Its deterministic receipt is:

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

`wireBytes` covers headers, CRLF separators, extension headers, and JSON bodies. `bodyBytes` covers JSON bodies only. The receipt therefore exposes the exact resource quantity used by the aggregate input ceiling rather than hiding framing overhead.

`fln-lsp-validate --client-lifecycle INPUT` adds a fail-closed client state machine. It requires:

- a request-shaped `initialize` as the first frame;
- an `initialized` notification before ordinary running traffic;
- exactly one running-state `shutdown` request;
- an `exit` notification immediately after shutdown;
- no frame after exit and EOF in the `exited` state;
- request IDs on every known request-only method and no IDs on every known notification-only method;
- object params for known data-bearing LSP and Lean-extension methods;
- only missing or `null` params for `shutdown` and `exit`.

Unknown methods remain admissible during the running state so future extensions do not require weakening the validator. They do not bypass initialization or terminal shutdown ordering.

A successful lifecycle receipt uses a distinct schema and binds every handshake frame:

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

This mode validates the client stream only. It does not infer when a server response arrived and therefore does not claim cross-stream request-ID correlation.

## Metadata-only inspection

`fln-lsp-inspect` consumes the same validated frame stream and emits one deterministic NDJSON row per frame using `fln.lsp-frame/2`. Rows contain:

- wire index;
- request or notification role;
- decoded method;
- the exact lexical request ID, or `null` for a notification;
- `paramsKind` as `missing`, `object`, `array`, or `null`;
- JSON body byte count.

Parameter contents, document text, and source text are never included. Inspection buffers its bounded output and publishes nothing when a later frame is malformed or the selected frame ceiling is exceeded.

## Replay modes

By default, `fln-lsp-replay INPUT` preserves adversarial testing: a syntactically valid stream may be replayed even when its known method roles or lifecycle ordering are deliberately wrong. Lantern itself determines the resulting server bytes.

`fln-lsp-replay --client-lifecycle INPUT` performs the same strict lifecycle validation described above **before** server execution, expected-stream comparison, stdout emission, or named output publication. A failed preflight therefore creates no `--output` artifact and emits no partial server stream.

When `--expect PATH` is present, the complete emitted server stream is compared byte-for-byte with the expected framed stream. A mismatch reports the first differing byte offset and both stream lengths. When `--output PATH` is present, the actual stream is written with create-new semantics; an existing path is never overwritten. Without `--output`, the actual framed stream is written to standard output and human refusal text remains on standard error.

## What a successful replay proves

For the supplied stream and current build, default replay proves that:

- the complete client transcript obeyed Lantern's bounded framing rules strongly enough to reach the dispatcher;
- the dispatcher reached the clean `shutdown` then `exit` terminal state;
- no bytes followed the accepted `exit` notification;
- a repeated replay produced the same server bytes when compared with the same expected stream;
- output publication did not overwrite an existing named artifact.

With `--client-lifecycle`, it additionally proves the known method-role, parameter-container, and complete client-handshake rules above before any server side effect.

The replay inherits the transport's message, header-byte, and header-field ceilings. Aggregate input and expected transcript files are additionally bounded to 256 MiB each, and generated server output has an independent 256 MiB ceiling.

## Deliberate evidence boundary

These are **wire and lifecycle** tools, not substitutes for the complete Lantern or Lean semantic oracle.

The standalone replay callback emits deterministic empty diagnostic sets for accepted document events. A successful run therefore does **not** prove parsing, elaboration, kernel checking, goal rendering, RPC reference semantics, widget behavior, shared-import-heap behavior, asynchronous cancellation, crash isolation, or unmodified `vscode-lean4` compatibility. Those remain governed by `franken_lean-v2p` and its dependent editor/session evidence.

The strict lifecycle validator also does not yet prove the semantic contents of every method's params object, document open/change/version coherence, or correlation with the server response stream. The live Lantern dispatcher enforces a stronger bounded document state model; complete replay evidence will eventually join both directions and final server state.

A release or gate claim must use a real production Lantern callback and the required no-mock editor/session scenarios. Wire replay is useful for shrinking protocol failures, preserving exact framing regressions, and separating dispatcher nondeterminism from later semantic divergence.

## Agent workflow

1. Preserve the client stream exactly as observed; do not copy JSON bodies into a line-oriented format.
2. Run syntax-only validation first when the stream is a negative or adversarial fixture.
3. Run `--client-lifecycle` when the claim requires a protocol-valid client session rather than merely replayable bytes.
4. Use the inspector to locate frame role, method, ID, and parameter-container mistakes without disclosing document contents.
5. Preserve the complete expected server stream from the same epoch and mode.
6. Replay with `--client-lifecycle --expect` and an unused `--output` path for positive lifecycle evidence; omit the lifecycle flag only when the invalid client behavior is itself the test subject.
7. Record executable identity, Git tree, transcript identities, exit status, first divergence when present, and output artifact identity in the enclosing evidence bundle.
8. Reduce a failure by deleting whole request/notification frames only in a disposable copy. Never edit lengths or bodies independently.
9. Keep semantic and telemetry evidence separate. Byte equality is a semantic wire fact; host, duration, and path details are telemetry.

## Verification surface

Repository-owned unit and external-process tests cover deterministic argument parsing, syntax-only compatibility, known role and parameter-container refusals, clean and incomplete lifecycle termination, post-exit refusal, strict replay preflight before output publication, exact replay repeatability, metadata-only inspection, and first-divergence detection. Public transport model tests replay one and multiple frames through deterministic fragment widths from one through 64 bytes and verify truncated bodies remain typed `UnexpectedEof` failures.
