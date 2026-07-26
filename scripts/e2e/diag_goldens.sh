#!/usr/bin/env bash
# diag_goldens.sh — shared E2E scenario for the typed error taxonomy + faithful
# renderer (bead fln-rk6).
#
# Real-path, no-mock: the epoch lab's D1 diagnostic corpus is regenerated from the
# REAL pinned Reference binary and drift-checked, then the faithful-renderer goldens
# replay every captured frame byte-for-byte (cargo test), then a seeded corruption in
# a scratch copy of the lab must make the goldens FAIL (a mutated oracle frame our
# renderer no longer matches is a detected divergence, never a silent pass), then
# recovery against the pristine lab. NDJSON under target/e2e/; fixtures retained.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RUN_ID="diag-goldens-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ROOT/target/e2e/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$(dirname "$ART_DIR")"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  echo "[diag_goldens] setup failure: evidence directory already claimed: $ART_DIR" >&2
  exit 2
fi

BEAD="fln-rk6"
SCHEMA="fln-e2e/1"
HOST="$(uname -sr)"
start_ns=$(date +%s%N)

emit() { # emit <step_id> <status> <detail-json-fragment>
  local now_ns
  now_ns=$(date +%s%N)
  printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"diag_goldens","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
    "$SCHEMA" "$RUN_ID" "$BEAD" "$1" "$2" $(( (now_ns - start_ns) / 1000000 )) "$HOST" "$3" >> "$LOG"
}

note() { echo "[diag_goldens] $*" >&2; }

emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"$0\""

# ---- step 1: the D1 corpus is live oracle output (drift check) -------------------------
note "epoch-lab drift check (real pinned Reference binary)"
set +e
"$ROOT/scripts/tribunal/gen_epoch_manifest.sh" --check > "$ART_DIR/drift.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit drift failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"drift.log\""
  note "FAIL: epoch lab drifted (see $ART_DIR/drift.log)"
  exit "$rc"
fi
emit drift passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"drift.log\""

# ---- step 2: the goldens replay the real frames ----------------------------------------
note "replaying renderer goldens against the published lab"
set +e
( cd "$ROOT" && cargo test -q -p fln-conformance --test diag_render ) \
  > "$ART_DIR/goldens.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit goldens failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"goldens.log\""
  note "FAIL: renderer goldens failed against the published lab"
  exit 1
fi
emit goldens passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"goldens.log\""

# ---- step 3: seeded corruption must be detected ----------------------------------------
SCRATCH_REL="target/e2e/$RUN_ID/corrupted-lab"
SCRATCH="$ROOT/$SCRATCH_REL"
mkdir -p "$SCRATCH"
cp -r "$ROOT/tribunal/epochs/v4.32.0/." "$SCRATCH/"
# Mutate the frame shape in every transcript (an oracle format change). A parseable
# frame always replays self-consistently, so the detection law under test is the
# no-silent-skip floor: unparseable frames drop the golden count below the required
# minimum and the harness fails LOUDLY instead of skipping everything.
sed -i 's/: error/:  error/' "$SCRATCH"/transcripts/*.stdout
set +e
( cd "$ROOT" && FLN_EPOCH_LAB_DIR="$SCRATCH_REL" \
    cargo test -q -p fln-conformance --test diag_render ) \
  > "$ART_DIR/seeded.log" 2>&1
rc=$?
set -e
if [ "$rc" -eq 0 ]; then
  emit seeded_corruption failed "\"expected_exit\":\"nonzero\",\"actual_exit\":0,\"artifact\":\"seeded.log\""
  note "FAIL: corrupted oracle frame was not detected"
  exit 1
fi
emit seeded_corruption passed "\"expected_exit\":\"nonzero\",\"actual_exit\":$rc,\"detected\":\"frame corruption\",\"artifact\":\"seeded.log\""

# ---- step 4: recovery ------------------------------------------------------------------
set +e
( cd "$ROOT" && cargo test -q -p fln-conformance --test diag_render ) \
  > "$ART_DIR/recovered.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit recovery failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"recovered.log\""
  note "FAIL: pristine lab no longer passes"
  exit 1
fi
emit recovery passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"recovered.log\""

emit run_end passed "\"verdict\":\"pass\",\"artifacts_dir\":\"target/e2e/$RUN_ID\",\"cleanup_status\":\"retained_by_policy\""
note "PASS — artifacts in $ART_DIR"
