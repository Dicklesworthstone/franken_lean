# Building Lantern interleaved timeline fixtures

Use [`scripts/build_lsp_timeline.py`](../scripts/build_lsp_timeline.py) to construct deterministic **fixtures** for `fln-lsp-timeline` without manually calculating Content-Length headers.

This helper is intentionally not a production recorder. Its receipt says:

```json
{"authority":false,"purpose":"fixture-generation"}
```

A generated stream may exercise validators and negative cells. It does not prove that the live server produced the events, that their order reflects wall-clock behavior, or that cancelled work was active.

## Source format

The input is UTF-8 text using one event per line:

```text
DIRECTION<TAB>RAW_JSON
```

`DIRECTION` is exactly `client` or `server`. The separator is one literal tab. `RAW_JSON` is one complete object-valued inner JSON-RPC message with no surrounding whitespace.

Example:

```text
client	{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}
server	{"jsonrpc":"2.0","id":"init","result":{"capabilities":{}}}
client	{"jsonrpc":"2.0","method":"initialized","params":{}}
client	{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}
server	{"jsonrpc":"2.0","id":"shutdown","result":null}
client	{"jsonrpc":"2.0","method":"exit","params":null}
```

Blank lines are ignored. Event order is source-line order. The tool never sorts or timestamp-merges events.

## Identity preservation

The inner message is validated as duplicate-free JSON but is **not reserialized**. This matters because Lantern's canonical ID policy distinguishes number lexemes:

```text
1.25e2 != 125
```

and compares strings by decoded value while retaining a deterministic rendered identity. A conventional Python `json.loads` followed by `json.dumps` could silently turn `1.25e2` into `125.0` or rewrite string escapes. The fixture builder emits the exact raw inner message bytes supplied after the tab.

The outer wrapper is deterministic:

```json
{
  "schema": "fln.lsp-interleaved-event/1",
  "direction": "client",
  "message": {}
}
```

Its Content-Length is calculated over the exact UTF-8 body bytes, including non-ASCII text.

## Build and validate

```bash
python3 scripts/build_lsp_timeline.py events.txt session.timeline
fln-lsp-timeline session.timeline
```

The output path is create-new. An existing file or symlink is refused and remains unchanged. The complete bytes are first written and synchronized to a sibling staging inode, then published through a no-clobber hard link.

On success the builder prints one `fln.lsp-timeline-fixture-build/1` JSON receipt containing:

- the source format and event schema;
- event count;
- input, outer-body, and complete wire bytes;
- SHA-256 of the exact input text;
- SHA-256 of the exact generated timeline;
- the output path;
- `authority:false` and `purpose:"fixture-generation"`.

Treat the hash as fixture identity, not semantic authority. The authoritative protocol receipt comes only from a successful `fln-lsp-timeline` run, and production evidence additionally needs a bound live recorder and executable identity.

## Limits

The helper fails closed at the same principal transport and timeline bounds:

```text
inner JSON-RPC message: 64 MiB
events:                  1,000,000
input text:              256 MiB
output timeline:         256 MiB
```

A wrapped outer event must also fit the 64 MiB per-frame transport ceiling. Aggregate limits include blank input lines and complete output framing.

## Focused regression

```bash
python3 scripts/test_build_lsp_timeline.py
```

The standard-library-only test covers:

- exact numeric request-ID lexeme retention;
- exact escaped-string spelling retention;
- UTF-8 Content-Length accounting with a non-BMP character;
- duplicate JSON key refusal;
- invalid direction and empty-input refusal;
- no-clobber publication preserving an existing target;
- the explicitly non-authoritative fixture receipt.

The test does not replace the Rust timeline tests. Run both the Python fixture regression and the pinned Rust gate before promoting the timeline surface.
