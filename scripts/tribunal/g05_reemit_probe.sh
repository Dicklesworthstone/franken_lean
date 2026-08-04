#!/usr/bin/env bash
# G0-5 no-mock probe: the emission-determinism cells against the REAL pinned
# Reference, plus the committed-fixture provenance check (bead franken_lean-0vf;
# plan §7.3, FL-INV-04, §18.2).
#
# Cells (every expected shape measured before this script encoded it — bead
# comments 1707/1710):
#   fresh-determinism   two `lean -o` emissions of the committed pilot source,
#                       byte-identical to each other
#   fixture-provenance  and byte-identical to the COMMITTED fixture
#                       crates/fln-olean/fixtures/g05_pilot.olean — regeneration
#                       drift is a pin move or a fixture edit, both deliberate acts
#   async-identity      -D Elab.async=true emits the SAME bytes (the R3-critical
#                       cell: emission is schedule-independent at the pin)
#   negative            a corrupted copy MUST fail the comparison
#
# Receipt: NDJSON, schema fln-g05-reemit-probe/1, to
# crates/fln-olean/evidence/g05_reemit_probe_<tag>.jsonl.
set -u -o pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
FIXDIR="$ROOT/crates/fln-olean/fixtures"
SCRATCH="${TMPDIR:-/tmp}/g05-reemit-probe.$$"

fail() {
  printf '[g05_reemit_probe] REFUSED: %s\n' "$*" >&2
  exit 2
}

mapfile -t rows < <(grep -E '^reference ' "$ROOT/SUITE.lock")
[ "${#rows[@]}" -eq 1 ] || fail "SUITE.lock must have exactly one Reference row"
PIN_TAG=""
for field in ${rows[0]}; do
  case "$field" in
    tag=*) PIN_TAG="${field#tag=}" ;;
  esac
done
[[ "$PIN_TAG" =~ ^v[0-9]+\.[0-9]+\.[0-9]+([.-][A-Za-z0-9.-]+)?$ ]] \
  || fail "Reference tag is malformed: $PIN_TAG"
LEAN="$HOME/.elan/toolchains/leanprover--lean4---$PIN_TAG/bin/lean"
[ -x "$LEAN" ] || fail "pinned Reference binary is not installed at $LEAN"

mkdir -p "$SCRATCH" || fail "cannot create scratch"
RECEIPT="$SCRATCH/receipt.jsonl"
: > "$RECEIPT"
emit() { printf '%s\n' "$1" >> "$RECEIPT"; }

cp "$FIXDIR/g05_pilot.lean" "$SCRATCH/pilot.lean" || fail "committed pilot source missing"
run_emit() {
  ( cd "$SCRATCH" && env -u LEAN_PATH -u LEAN_SYSROOT LC_ALL=C TZ=UTC \
      "$LEAN" "$@" pilot.lean )
}
run_emit -o run1.olean || fail "emission run 1 failed"
run_emit -o run2.olean || fail "emission run 2 failed"
cmp -s "$SCRATCH/run1.olean" "$SCRATCH/run2.olean" \
  || fail "two fresh emissions DIVERGED — emission determinism lost"
emit '{"schema":"fln-g05-reemit-probe/1","step":"fresh_determinism","runs_identical":true}'

cmp -s "$SCRATCH/run1.olean" "$FIXDIR/g05_pilot.olean" \
  || fail "fresh emission differs from the COMMITTED fixture — the pin moved or the fixture was edited; regenerate deliberately and land both together"
sha="$(sha256sum "$SCRATCH/run1.olean" | cut -d' ' -f1)"
emit "{\"schema\":\"fln-g05-reemit-probe/1\",\"step\":\"fixture_provenance\",\"fixture_identical\":true,\"sha256\":\"$sha\"}"

run_emit -D Elab.async=true -o run_async.olean || fail "async emission failed"
cmp -s "$SCRATCH/run_async.olean" "$SCRATCH/run1.olean" \
  || fail "async elaboration changed the emitted bytes — the R3 cell regressed"
emit '{"schema":"fln-g05-reemit-probe/1","step":"async_identity","identical_to_sync":true}'

cp "$SCRATCH/run1.olean" "$SCRATCH/corrupt.olean"
printf 'X' >> "$SCRATCH/corrupt.olean"
if cmp -s "$SCRATCH/corrupt.olean" "$FIXDIR/g05_pilot.olean"; then
  fail "negative control PASSED — the comparison is broken"
fi
emit '{"schema":"fln-g05-reemit-probe/1","step":"negative_control","corrupted_copy_detected":true}'
emit "{\"schema\":\"fln-g05-reemit-probe/1\",\"step\":\"summary\",\"pin\":\"$PIN_TAG\",\"verdict\":\"all-cells-hold\"}"

DEST="$ROOT/crates/fln-olean/evidence/g05_reemit_probe_$PIN_TAG.jsonl"
mkdir -p "$(dirname "$DEST")"
cp "$RECEIPT" "$DEST"
printf '[g05_reemit_probe] OK: determinism + provenance + async identity hold at %s; receipt %s\n' \
  "$PIN_TAG" "$DEST"
