#!/usr/bin/env bash
# Option-census probe: the binary half of the census cross-check, plus the measured
# refusal and precedence cells, against the REAL pinned Reference (bead
# franken_lean-4xsz; plan D5/D9; feeds the drop-in option contract).
#
# Cells, every one with its expected shape measured before this script encoded it:
#   dump           the binary's own registry via getOptionDeclsArray, run twice,
#                  byte-identical, then reconciled against contracts/option_census.ndjson
#                  by scripts/extract/option_census.py --crosscheck (which refuses on
#                  any source-only name, any unallowlisted binary-only name, and any
#                  literal default disagreement)
#   unknown        -D totally.unknown.option=true refuses naming the option
#   malformed-nat  -D maxHeartbeats=banana refuses demanding a natural number
#   malformed-bool -D pp.all=banana refuses demanding true/false
#   precedence     ONE run of x4_precedence.lean at -D maxHeartbeats=16: the def
#                  (line 1) and the unscoped theorem (line 4) both carry the
#                  deterministic-timeout marker while the scoped theorem (line 3,
#                  set_option maxHeartbeats 400 in) does not — proving CLI default
#                  application, in-file scoped override, and scope restoration in a
#                  single artifact
#   zero-disables  -D maxHeartbeats=0 completes the same file
#   negative       a corrupted census copy MUST fail the cross-check
#
# Receipt: NDJSON, schema fln-x4-option-probe/1, to
# crates/fln-conformance/evidence/option_census/probe_<tag>.jsonl.
set -u -o pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
FIXTURES="$ROOT/crates/fln-conformance/fixtures"
SCRATCH="${TMPDIR:-/tmp}/x4-option-probe.$$"

fail() {
  printf '[option_census_probe] REFUSED: %s\n' "$*" >&2
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

run_lean() {
  env -u LEAN_PATH -u LEAN_SYSROOT LC_ALL=C TZ=UTC "$LEAN" "$@"
}

# --- dump: twice, byte-identical, cross-checked --------------------------------
run_lean "$FIXTURES/x4_option_dump.lean" > "$SCRATCH/dump1.txt" 2>&1 \
  || fail "dump run 1 exited nonzero"
run_lean "$FIXTURES/x4_option_dump.lean" > "$SCRATCH/dump2.txt" 2>&1 \
  || fail "dump run 2 exited nonzero"
cmp -s "$SCRATCH/dump1.txt" "$SCRATCH/dump2.txt" || fail "registry dump DIVERGED between runs"
total_line="$(tail -1 "$SCRATCH/dump1.txt")"
[[ "$total_line" =~ ^TOTAL ]] || fail "dump missing its TOTAL line"
xc_out="$(python3 -I -S "$ROOT/scripts/extract/option_census.py" \
  --out "$ROOT/contracts/option_census.ndjson" \
  --crosscheck "$SCRATCH/dump1.txt")" || fail "cross-check refused: $xc_out"
emit "{\"schema\":\"fln-x4-option-probe/1\",\"step\":\"dump\",\"runs_identical\":true,\"binary_total\":\"${total_line#TOTAL	}\",\"crosscheck\":\"$xc_out\"}"

# --- refusal cells --------------------------------------------------------------
printf 'def x : Nat := 1\n' > "$SCRATCH/trivial.lean"
check_refusal() {
  local label="$1" needle="$2"
  shift 2
  local out rc=0
  out="$(run_lean "$@" "$SCRATCH/trivial.lean" 2>&1)" || rc=$?
  [ "$rc" -ne 0 ] || fail "$label: expected a refusal, got exit 0"
  case "$out" in
    *"$needle"*) ;;
    *) fail "$label: refusal text lost its shape: $out" ;;
  esac
  emit "{\"schema\":\"fln-x4-option-probe/1\",\"step\":\"$label\",\"refused\":true,\"shape_held\":true}"
}
check_refusal unknown "unknown configuration option 'totally.unknown.option'" \
  -D totally.unknown.option=true
check_refusal malformed-nat "it must be a natural number" -D maxHeartbeats=banana
check_refusal malformed-bool "it must be true/false" -D pp.all=banana

# --- precedence: one run, three facts -------------------------------------------
rc=0
out="$(run_lean -D maxHeartbeats=16 "$FIXTURES/x4_precedence.lean" 2>&1)" || rc=$?
[ "$rc" -ne 0 ] || fail "precedence: expected the CLI budget to red the unscoped lines"
markers="$(grep -c 'deterministic) timeout' <<< "$out" || true)"
[ "$markers" -eq 2 ] || fail "precedence: expected exactly 2 timeout markers, got $markers"
grep -q 'x4_precedence.lean:1:' <<< "$out" || fail "precedence: the def's timeout anchor moved"
grep -q 'x4_precedence.lean:4:' <<< "$out" || fail "precedence: the unscoped theorem's anchor moved"
if grep -q 'x4_precedence.lean:3:' <<< "$out"; then
  fail "precedence: the SCOPED theorem timed out — set_option no longer beats the CLI"
fi
run_lean -D maxHeartbeats=0 "$FIXTURES/x4_precedence.lean" > /dev/null 2>&1 \
  || fail "zero-disables: -D maxHeartbeats=0 no longer disables the limit"
emit '{"schema":"fln-x4-option-probe/1","step":"precedence","cli_default_applied":true,"scoped_override_wins":true,"scope_restored":true,"zero_disables":true}'

# --- negative control: a corrupted census must fail the cross-check -------------
sed 's/"default":"false"/"default":"true"/' "$ROOT/contracts/option_census.ndjson" \
  > "$SCRATCH/census_corrupt.ndjson"
if python3 -I -S "$ROOT/scripts/extract/option_census.py" \
  --out "$SCRATCH/census_corrupt.ndjson" \
  --crosscheck "$SCRATCH/dump1.txt" > /dev/null 2>&1; then
  fail "negative control: a flipped-defaults census PASSED the cross-check"
fi
emit '{"schema":"fln-x4-option-probe/1","step":"negative_control","corrupted_census_refused":true}'

emit "{\"schema\":\"fln-x4-option-probe/1\",\"step\":\"summary\",\"pin\":\"$PIN_TAG\",\"verdict\":\"all-cells-hold\"}"

DEST="$ROOT/crates/fln-conformance/evidence/option_census/probe_$PIN_TAG.jsonl"
mkdir -p "$(dirname "$DEST")"
cp "$RECEIPT" "$DEST"
printf '[option_census_probe] OK: dump identical + cross-checked, refusal shapes held, precedence proven at %s; receipt %s\n' \
  "$PIN_TAG" "$DEST"
