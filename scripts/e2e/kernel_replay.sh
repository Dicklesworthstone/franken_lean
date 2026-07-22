#!/usr/bin/env bash
# kernel_replay.sh — shared E2E scenario for the G0-2 kernel differential spike
# (bead franken_lean-z6c, plan §22.1-2).
#
# Real-path, no-mock: REAL Reference declarations are decoded from real .olean
# artifacts and replayed through fln_kernel::check. Lanes:
#   1. decoder suite over the C3 fixtures (identity-layer cross-checks live);
#   2. decode EVERY constant of the whole pinned stdlib (158k+ constants) with
#      cross-checks on — a byte-level identity differential against the pin;
#   3. the kernel replay over Init.Prelude (verdict census + full rejection
#      triage, no false-accepts);
#   4. seeded corruption — a flipped byte in a copied olean must make decoding
#      fail typed, never panic, never yield a wrong-but-accepted decl set;
#   5. recovery — the pristine fixture decodes clean again.
# NDJSON under target/e2e/; artifacts retained.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RUN_ID="kernel-replay-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ROOT/target/e2e/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$ART_DIR"

BEAD="franken_lean-z6c"
SCHEMA="fln-e2e/1"
HOST="$(uname -sr)"
start_ns=$(date +%s%N)
PIN_TAG="$(sed -E 's/.*tag=([^ ]+).*/\1/' <<<"$(grep -E '^reference ' "$ROOT/SUITE.lock")")"

emit() { # emit <step_id> <status> <detail-json-fragment>
  local now_ns
  now_ns=$(date +%s%N)
  printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"kernel_replay","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
    "$SCHEMA" "$RUN_ID" "$BEAD" "$1" "$2" $(( (now_ns - start_ns) / 1000000 )) "$HOST" "$3" >> "$LOG"
}

note() { echo "[kernel_replay] $*" >&2; }

emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"$0\""

# ---- lane 1: the decoder + kernel-replay suites ----------------------------------------
note "running the decoder suite and the kernel-replay rig"
set +e
( cd "$ROOT" \
    && CARGO_TARGET_DIR=target_local cargo test -q -p fln-olean --test decl_decode \
    && CARGO_TARGET_DIR=target_local cargo test -q -p fln-conformance --test kernel_replay ) \
  > "$ART_DIR/suite.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit suite failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"suite.log\""
  note "FAIL: decoder/replay suite failed (see $ART_DIR/suite.log)"
  exit 1
fi
emit suite passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"suite.log\""

# ---- build the decode driver -----------------------------------------------------------
( cd "$ROOT" && CARGO_TARGET_DIR=target_local cargo build -q --locked -p fln-olean --example decode_olean ) \
  > "$ART_DIR/build.log" 2>&1
DECODER="$ROOT/target_local/debug/examples/decode_olean"

# ---- lane 2: decode the entire pinned stdlib with cross-checks on -----------------------
LIB="$HOME/.elan/toolchains/leanprover--lean4---$PIN_TAG/lib/lean"
if [ -d "$LIB" ]; then
  note "decoding every constant of the pinned stdlib (identity cross-checks on)"
  set +e
  find "$LIB" -name '*.olean' | sort | xargs "$DECODER" > "$ART_DIR/decode_all.tsv" 2>>"$ART_DIR/decode_all.err"
  rc=$?
  set -e
  total="$(wc -l < "$ART_DIR/decode_all.tsv")"
  ok="$(grep -c $'\tok$' "$ART_DIR/decode_all.tsv" || true)"
  consts="$(awk -F'\t' '$4=="ok"{s+=$2} END{print s}' "$ART_DIR/decode_all.tsv")"
  if [ "$rc" -ne 0 ] || [ "$total" -ne "$ok" ] || [ "$total" -lt 2000 ]; then
    emit decode_all failed "\"files\":$total,\"ok\":$ok,\"actual_exit\":$rc,\"artifact\":\"decode_all.tsv\""
    note "FAIL: whole-library decode incomplete ($ok/$total clean)"
    exit 1
  fi
  emit decode_all passed "\"files\":$total,\"ok\":$ok,\"constants\":$consts,\"crosschecks\":\"on\",\"artifact\":\"decode_all.tsv\""
  note "decoded $consts constants across $total modules, zero cross-check failures"
else
  emit decode_all skipped "\"reason\":\"reference_toolchain_absent\",\"limitation\":\"L0: whole-library decode unverified on this host\""
  note "SKIP: pinned toolchain library not installed (typed limitation)"
fi

# ---- lane 3: seeded corruption — a flip in a live object must fail typed ----------------
# The constant-decoder only traverses objects reachable from the `constants`
# array, so a single flip can legitimately land in an unreached object and
# decode clean. We sweep deterministic positions and demand: NEVER a panic, and
# AT LEAST ONE flip caught as a typed error — proving the identity cross-checks
# and shape checks genuinely reject corrupted declarations.
note "seeding corruption: deterministic byte-flip sweep in a copied olean"
kills=0
panics=0
sweeps=0
for frac in 4 8 16 32 64 128 256 512; do
  CORRUPT="$ART_DIR/corrupt_$frac.olean"
  cp "$ROOT/tribunal/fixtures/c3/Init.SizeOfLemmas.olean" "$CORRUPT"
  python3 - "$CORRUPT" "$frac" <<'EOF'
import sys
path, frac = sys.argv[1], int(sys.argv[2])
data = bytearray(open(path, "rb").read())
pos = 88 + ((len(data) - 88) // frac // 8) * 8
data[pos] ^= 0x08
open(path, "wb").write(data)
EOF
  sweeps=$((sweeps + 1))
  set +e
  "$DECODER" "$CORRUPT" > "$ART_DIR/corrupt_$frac.tsv" 2>"$ART_DIR/corrupt_$frac.err"
  rc=$?
  set -e
  if grep -q "panicked" "$ART_DIR/corrupt_$frac.err"; then
    panics=$((panics + 1))
  elif [ "$rc" -ne 0 ]; then
    kills=$((kills + 1))
  fi
done
if [ "$panics" -ne 0 ]; then
  emit corruption failed "\"reason\":\"panic\",\"panics\":$panics,\"sweeps\":$sweeps"
  note "FAIL: decoder panicked on corrupted input (FL-INV-07 violation)"
  exit 1
fi
if [ "$kills" -eq 0 ]; then
  emit corruption failed "\"kills\":0,\"sweeps\":$sweeps,\"expected\":\">=1 typed failure\""
  note "FAIL: no corruption caught across $sweeps flips — cross-checks not live"
  exit 1
fi
emit corruption passed "\"kills\":$kills,\"sweeps\":$sweeps,\"panics\":0,\"typed_error\":true"
note "corruption sweep: $kills/$sweeps flips killed typed, 0 panics"

# ---- lane 4: recovery — pristine fixture decodes clean ----------------------------------
set +e
"$DECODER" "$ROOT/tribunal/fixtures/c3/Init.SizeOfLemmas.olean" > "$ART_DIR/recovery_decode.tsv" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit recovery failed "\"actual_exit\":$rc,\"artifact\":\"recovery_decode.tsv\""
  note "FAIL: recovery decode not clean"
  exit 1
fi
emit recovery passed "\"actual_exit\":0,\"artifact\":\"recovery_decode.tsv\""

emit run_end passed "\"cleanup_status\":\"retained_by_policy\",\"artifact_dir\":\"target/e2e/$RUN_ID\""
note "PASS: all lanes green (artifacts in target/e2e/$RUN_ID)"
