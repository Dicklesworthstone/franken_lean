#!/usr/bin/env bash
# gen_builtin_parser_table.sh — publish and drift-check the pin's builtin parser
# combinator-AST table (Step 1 of fln-generated-builtin-grammar-spike-kcvj;
# Rules D5/D8-2: derived from the pin, never hand-transcribed).
#
# Output:
#   contracts/REFERENCE_BUILTIN_PARSER_TABLE.jsonl
#     JSONL table containing:
#       * header row with schema version, pinned lean_version/githash, and counts;
#       * every strictly verified primitive constant (64 entries at v4.32.0:
#         51 direct Parser.mk/ParserFn leaves + 9 ParserFn helpers + 4 type/ctor names);
#       * every generatable Lean.Parser.* definition and helper function (541 entries
#         at v4.32.0: 480 parser definitions + 61 helpers) with normalized combinator AST
#         and `_regBuiltin` registrations.
#
# Usage: scripts/extract/gen_builtin_parser_table.sh [generate|--check]
# Exit: 0 ok / no drift, 1 drift, 2 setup failure (missing pin or commit mismatch),
#       3 extractor refusal (totality check failed or truncated output).

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
GENERATOR="$ROOT/scripts/extract/gen_builtin_parser_table.lean"
OUTPUT="$ROOT/contracts/REFERENCE_BUILTIN_PARSER_TABLE.jsonl"
MODE="${1:-generate}"

note() { printf '[gen_builtin_parser_table] %s\n' "$*" >&2; }

PIN_LINE="$(grep -E '^reference ' "$ROOT/SUITE.lock")"
PIN_TAG="$(sed -E 's/.*tag=([^ ]+).*/\1/' <<<"$PIN_LINE")"
PIN_COMMIT="$(sed -E 's/.*commit=([0-9a-f]{40}).*/\1/' <<<"$PIN_LINE")"

SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---$PIN_TAG"
LEAN="$SYSROOT/bin/lean"
if [ ! -x "$LEAN" ]; then
    note "setup failure: no Reference binary for $PIN_TAG (install: elan toolchain install leanprover/lean4:$PIN_TAG)"
    exit 2
fi
VERSION="$("$LEAN" --version)"
if ! grep -q "$PIN_COMMIT" <<<"$VERSION"; then
    note "setup failure: binary commit does not match SUITE.lock pin"
    note "  binary : $VERSION"
    note "  pinned : $PIN_TAG @ $PIN_COMMIT"
    exit 2
fi

emit_table() {
    local dest="$1" body status lines
    body="$(mktemp "${TMPDIR:-/tmp}/fln-builtin-parser-table.XXXXXX")"
    set +e
    (cd "$ROOT" && LEAN_SYSROOT="$SYSROOT" "$LEAN" --run "$GENERATOR") >"$body"
    status=$?
    set -e
    if [ "$status" -ne 0 ]; then
        note "extractor refused (exit $status); nothing published ($body)"
        exit 3
    fi
    lines="$(wc -l <"$body")"
    if [ "$lines" -lt 100 ] || ! head -n 1 "$body" | grep -q '"schema":"fln.builtin-parser-table/1"'; then
        note "extractor output looks incomplete ($lines lines at $body); nothing published"
        exit 3
    fi
    cp -- "$body" "$dest"
    chmod 0644 "$dest"
}

case "$MODE" in
    generate)
        mkdir -p "$(dirname "$OUTPUT")"
        candidate="${OUTPUT}.candidate"
        emit_table "$candidate"
        mv -- "$candidate" "$OUTPUT"
        note "wrote $OUTPUT ($(wc -l <"$OUTPUT") rows, sha256=$(sha256sum "$OUTPUT" | awk '{print $1}'))"
        ;;
    --check)
        if [ ! -f "$OUTPUT" ]; then
            note "drift: $OUTPUT does not exist; run scripts/extract/gen_builtin_parser_table.sh generate"
            exit 1
        fi
        scratch="$(mktemp "${TMPDIR:-/tmp}/fln-builtin-parser-table-check.XXXXXX")"
        emit_table "$scratch"
        if cmp -s -- "$scratch" "$OUTPUT"; then
            note "no drift: $OUTPUT matches pinned $PIN_TAG @ $PIN_COMMIT ($(wc -l <"$OUTPUT") rows)"
            exit 0
        else
            note "drift: $OUTPUT differs from freshly extracted table ($scratch)"
            diff -u -- "$OUTPUT" "$scratch" | head -n 60 >&2 || true
            exit 1
        fi
        ;;
    *)
        note "usage: $0 [generate|--check]"
        exit 2
        ;;
esac
