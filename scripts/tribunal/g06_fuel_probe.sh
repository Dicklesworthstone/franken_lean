#!/usr/bin/env bash
# G0-6 fuel-parity rig seed: hold the PINNED per-file heartbeat thresholds to the real
# pinned Reference binary (bead franken_lean-7zr; plan §22.1-6, §6.3; feeds the
# faithful-mode differential rig).
#
# For every bracketed file the pinned threshold C (maxHeartbeats units, thousands of
# ticks) is verified at both edges: C-1 must produce the "(deterministic) timeout"
# marker and C must not. For every d1 reject the budget-1 cell must REJECT WITHOUT the
# marker — rejects are budget-independent on this slice and a timeout masking a reject
# is exactly the verdict drift this rig exists to catch. The verdict predicate is the
# MARKER, never the exit code: a d1 reject exits 1 at every budget by design.
#
# Thresholds were bisected on 2026-07-29 (bead comments 1664/1665, driver protocol in
# 1664). Regeneration is a deliberate act against the pin: re-bisect, update the table
# HERE, and land both with the measurement recorded on the bead. Receipt: NDJSON,
# schema fln-g06-fuel-thresholds/1, written to
# crates/fln-conformance/evidence/g06_fuel_parity/thresholds_<tag>.jsonl.
set -u -o pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRATCH="${TMPDIR:-/tmp}/g06-fuel-probe.$$"
MARKER='(deterministic) timeout'

fail() {
  printf '[g06_fuel_probe] REFUSED: %s\n' "$*" >&2
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

mkdir -p "$SCRATCH" || fail "cannot create scratch $SCRATCH"
RECEIPT="$SCRATCH/receipt.jsonl"
: > "$RECEIPT"

# file family threshold — thresholds bisected at the pin; "-" = no bracket at [1,2000].
TABLE=(
  "tests/elab/evalProp.lean c1 46"
  "tests/elab/mainType1.lean c1 23"
  "tests/elab/mainType2.lean c1 22"
  "tests/elab/mainType3.lean c1 22"
  "tests/elab/constDelab.lean c1 240"
  "tests/elab/univPolyEnum.lean c1 10"
  "tests/elab/1236.lean c1 30"
  "tests/elab/int_to_nat_bug.lean c1 20"
  "tests/elab/2009.lean c1 231"
  "tests/elab/WindowsNewlines.lean c1 -"
  "tests/elab_fail/2006.lean d1 -"
  "tests/elab_fail/partialVariable.lean d1 -"
  "tests/elab_fail/1690.lean d1 -"
  "tests/elab_fail/eoi.lean d1 -"
  "tests/elab_fail/1707.lean d1 -"
  "tests/elab_fail/newCatPanic.lean d1 -"
)

timed_out() {
  local budget="$1" path="$2" out
  out="$(env -u LEAN_PATH -u LEAN_SYSROOT LC_ALL=C TZ=UTC \
    "$LEAN" -D "maxHeartbeats=$budget" "$ROOT/vendor/lean4-src/$path" 2>&1)"
  case "$out" in
    *"$MARKER"*) return 0 ;;
    *) return 1 ;;
  esac
}

checked=0
for row in "${TABLE[@]}"; do
  read -r path fam c <<< "$row"
  if [ "$c" = "-" ]; then
    # Unbracketed: budget 1 must NOT time out (cheap accept or budget-independent
    # reject). A marker here means the reject/accept became budget-dependent.
    if timed_out 1 "$path"; then
      fail "$path: budget 1 now times out — the unbracketed cell drifted"
    fi
    printf '{"schema":"fln-g06-fuel-thresholds/1","file":"%s","family":"%s","threshold":null,"budget1_no_timeout":true}\n' \
      "$path" "$fam" >> "$RECEIPT"
  else
    timed_out "$((c - 1))" "$path" \
      || fail "$path: budget $((c - 1)) no longer times out — threshold fell below $c"
    if timed_out "$c" "$path"; then
      fail "$path: budget $c now times out — threshold rose above $c"
    fi
    printf '{"schema":"fln-g06-fuel-thresholds/1","file":"%s","family":"%s","threshold":%s,"edge_below_times_out":true,"edge_at_passes":true}\n' \
      "$path" "$fam" "$c" >> "$RECEIPT"
  fi
  checked=$((checked + 1))
done

# Negative control: a deliberately wrong threshold must FAIL the edge check — without
# this cell a broken timed_out() reporting false everywhere reads as all-green.
if timed_out 2000 "tests/elab/univPolyEnum.lean"; then
  fail "negative control: budget 2000 timed out on a 10-threshold file — probe broken"
fi
if ! timed_out 1 "tests/elab/constDelab.lean"; then
  fail "negative control: budget 1 did NOT time out on the 240-threshold file — probe broken"
fi
printf '{"schema":"fln-g06-fuel-thresholds/1","step":"negative_control","both_directions":true}\n' >> "$RECEIPT"
printf '{"schema":"fln-g06-fuel-thresholds/1","step":"summary","pin":"%s","files":%d,"verdict":"all-edges-hold"}\n' \
  "$PIN_TAG" "$checked" >> "$RECEIPT"

DEST="$ROOT/crates/fln-conformance/evidence/g06_fuel_parity/thresholds_$PIN_TAG.jsonl"
mkdir -p "$(dirname "$DEST")"
cp "$RECEIPT" "$DEST"
printf '[g06_fuel_probe] OK: %d files, every pinned edge holds at %s; receipt %s\n' \
  "$checked" "$PIN_TAG" "$DEST"
