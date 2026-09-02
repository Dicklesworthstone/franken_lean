# Lantern wire replay

`fln-lsp-replay` is the bounded, deterministic replay surface for FrankenLean's current stdio LSP transport and lifecycle dispatcher.

```text
fln-lsp-replay [--expect PATH] [--output PATH] [--] INPUT
```

`INPUT` is the exact byte stream received from an LSP client: concatenated `Content-Length` frames, including headers and bodies. The tool does not reinterpret, normalize, sort, or regenerate those bytes before passing them to Lantern.

When `--expect PATH` is present, the complete emitted server stream is compared byte-for-byte with the expected framed stream. A mismatch reports the first differing byte offset and both stream lengths. When `--output PATH` is present, the actual stream is written with create-new semantics; an existing path is never overwritten. Without `--output`, the actual framed stream is written to standard output and human refusal text remains on standard error.

## What the replay proves

A successful replay proves, for the supplied stream and current build, that:

- the complete client transcript obeyed Lantern's bounded framing rules;
- the dispatcher reached the clean `shutdown` then `exit` terminal state;
- no bytes followed the accepted `exit` notification;
- a repeated replay produced the same server bytes when compared with the same expected stream;
- output publication did not overwrite an existing named artifact.

The replay inherits the transport's message, header-byte, and header-field ceilings. The aggregate input and expected transcript files are additionally bounded to 256 MiB each before replay.

## Deliberate evidence boundary

This is a **wire and lifecycle** oracle, not a substitute for the complete Lantern or Lean semantic oracle.

The standalone replay callback emits deterministic empty diagnostic sets for accepted document events. Therefore a successful run does **not** prove parsing, elaboration, kernel checking, goal rendering, RPC reference semantics, widget behavior, shared-import-heap behavior, crash isolation, or unmodified `vscode-lean4` compatibility. Those remain governed by `franken_lean-v2p` and its dependent editor/session evidence.

A release or gate claim must use a real production Lantern callback and the required no-mock editor/session scenarios. The wire replay is useful for shrinking protocol failures, preserving exact framing regressions, and separating dispatcher nondeterminism from later semantic divergence.

## Agent workflow

1. Preserve the client stream exactly as observed; do not copy JSON bodies into a line-oriented format.
2. Preserve the complete expected server stream from the same epoch and mode.
3. Replay once with `--expect` and an unused `--output` path.
4. Record the executable identity, Git tree, transcript identities, exit status, first divergence when present, and output artifact identity in the enclosing evidence bundle.
5. Reduce a failure by deleting whole request/notification frames only in a disposable copy. Never edit lengths or bodies independently.
6. Keep semantic and telemetry evidence separate. Byte equality is a semantic wire fact; host, duration, and path details are telemetry.

## Verification surface

The binary contains focused unit coverage for deterministic argument parsing, clean and unclean lifecycle termination, post-exit refusal, exact replay repeatability, and first-divergence detection. External-process tests exercise help and refusal behavior at the actual binary boundary. Public transport model tests replay one and multiple frames through every deterministic fragment width from one through 64 bytes and verify truncated bodies remain typed `UnexpectedEof` failures.
