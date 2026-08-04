# Vellum green-tree and token-stream golden provenance

These fixtures freeze the observable form of Vellum's lexical and green-tree output. They are
deterministic, platform-independent, volatility 1, and compared exactly.

**The tests have no update mode and never write either this document or the corpus.** A golden that
can regenerate its own expectation is a mirror, not a golden. A tree-shape change FAILS
`golden_vellum` and stays failed until a human reads the diff and edits `vellum_goldens.hex` by
hand.

The current producer authority is `fln-syntax@0.0.0` at commit
`d5ecb96659c5830449c5f000d9d9a4b9cb320dc8`, with the token stream at schema
`fln.vellum.token-stream/1` and the green tree at `fln.vellum.green-tree/1`. Re-derived on
2026-07-26 at repository commit `b241943dec5c22c81d7bd51ab6e622ad8715fa86`, this producer
commit resolves uniquely and is an ancestor of `refs/heads/main`.

The superseded producer anchor `d64218a954f8447b3f29c4ca230ae5d158d56dc9` remains a real
commit object in this local repository only because the pre-filter-branch history is retained by
backup refs. It is **local-backup-only**, not an ancestor of `refs/heads/main`, and therefore
historical context rather than current evidence authority.

The token table is frozen in the test source, not here, because the table is a **parameter** of the
lexer: the same source lexes differently under a different table, so a golden without its table is
not reproducible.

## The golden is of the recoverable form, not the raw bytes

Held literally from bead `franken_lean-tkr2`. The lexer consumes the **crlfToLf-normalized view**,
so a green tree reconstructs the *view*; recovering the file is `SourceView::reconstruct_original`'s
job. A golden frozen against raw bytes would fail on every CRLF row, or be quietly relaxed until it
passed.

Each row therefore freezes **both** forms and the chain between them — `raw_hex` and `view_hex` —
and `every_golden_row_recovers_its_file_through_the_map` asserts
`tree.reconstruct(view) == view_hex` and `view.reconstruct_original() == raw_hex`. For any row the
view actually normalized, it also asserts the tree's reconstruction **differs** from the raw bytes, so
the map cannot be relaxed out of the suite without a failure.

## What each field is for

| Field | Why it is frozen |
|---|---|
| `raw_hex` | the input bytes, CRLF and all |
| `view_hex` | the normalized bytes the lexer consumed and the tree reconstructs |
| `tokens` | kind and **view** offsets per token, plus any refusal and its message |
| `tree` | the tree's shape: each leaf's `pos..end_pos` and the byte length of its leading and trailing trivia, then the epilogue |
| `producer`, `producer_commit` | which code produced it, so a stale golden can be reproduced |
| `lexer_schema`, `tree_schema` | the versioned shape of the two renderings |

The `tree` field records trivia **lengths per leaf** rather than only spans, because coverage and
ownership are different properties: a misattachment reconstructs the file perfectly and is invisible
to a byte comparison. This field is where it shows up.

## The reviewed corpus

| Golden | Input | What it pins |
|---|---|---|
| `empty` | `""` | the degenerate case: no leaves, no epilogue |
| `bare-ident` | `x` | a single leaf with no trivia on either side |
| `lf-simple` | `def f := 1\n` | the LF baseline, view identical to raw |
| `crlf-simple` | `def f := 1\r\n` | one CRLF normalized: raw ends `0d0a`, view ends `0a` |
| `crlf-two-lines` | two statements, CRLF | the interior CRLF, and the leading-trivia attachment across it |
| `lone-cr-preserved` | two statements, lone CR | a lone CR **survives** normalization and is a lexical refusal |
| `comment-and-trivia` | comment plus parens, CRLF | comment trivia and bracket tokens under normalization |
| `unicode-and-doc` | doc comment, `α`, `λ` | multi-byte tokens, and `/--` as a token rather than trivia |

Every nonempty row ending in LF also pins the terminal half of the attachment rule:
the final token owns that final newline as trailing trivia and the epilogue is empty.
This was remeasured by G0-4 against the SUITE.lock Reference after the earlier
goldens had assigned the newline to epilogue.

## The contrast the corpus exists for

`crlf-two-lines` and `lone-cr-preserved` are the same two statements differing **only** in line
terminator, and their trees differ in *attachment*:

    crlf-two-lines     ... leaf 9..10 lead0 trail0   leaf 11..14 lead1 trail1 ...
    lone-cr-preserved  ... leaf 9..10 lead0 trail1   leaf 11..14 lead0 trail1 ...

`chooseNiceTrailStop` stops a token's trailing trivia at the first newline, so the LF becomes the
**leading** trivia of the next line's `def`. A lone CR is not a newline, so it stays **trailing** on
the token before it — and the lexer additionally refuses it, which the `tokens` field records.

Both rows reconstruct their files byte-for-byte. A golden capturing only the reconstruction would
show them as equally correct. Only the `tree` field distinguishes them, which is the argument for
freezing shape rather than bytes alone.

## Verification performed before freezing

Every row was read, not merely generated:

* `crlf-simple` — confirmed `raw_hex` ends `0d0a` and `view_hex` ends `0a`.
* `lone-cr-preserved` — confirmed `raw_hex` and `view_hex` are **identical**, so the lone CR was
  preserved, and confirmed the `tokens` field carries
  `refused(isolated carriage returns are not allowed)`.
* `crlf-two-lines` vs `lone-cr-preserved` — confirmed the attachment contrast above.
* `empty` — confirmed `file[0] epilogue0` rather than a spurious leaf.

## The change ceremony

The regeneration path is `emit_corpus_for_review`, which is `#[ignore]`d and **only prints**:

    GOLDEN_COMMIT=$(git rev-parse HEAD) cargo test -p fln-syntax --test golden_vellum \
        -- --ignored --nocapture emit_corpus

Read the output, diff it against `vellum_goldens.hex`, and paste in only what you intend to change.
Printing rather than writing is deliberate: a suite that can rewrite its own expectation will
eventually do so on a run nobody read, and the first bug it accepts will be invisible.
