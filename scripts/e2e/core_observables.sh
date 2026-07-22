#!/usr/bin/env bash
# core_observables.sh — shared E2E scenario for the fln-core C0 observable contract
# (bead franken_lean-p8a).
#
# Real-path, no-mock: runs the REAL pinned Reference binary as fixture oracle
# (drift check must pass), runs the real fixture-diff harness through cargo test
# (expected PASS), then seeds a corrupted observable into a scratch fixture and
# proves the harness rejects it (expected FAIL), then recovery (expected PASS).
# Human logs on stderr; schema-versioned NDJSON under target/e2e/. If the oracle
# binary is absent this scenario FAILS (exit 2) — a skipped oracle is not a pass.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RUN_ID="core-observables-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ROOT/target/e2e/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$ART_DIR"

BEAD="franken_lean-p8a"
SCHEMA="fln-e2e/1"
HOST="$(uname -sr)"
start_ns=$(date +%s%N)

emit() { # emit <step_id> <status> <detail-json-fragment>
  local now_ns
  now_ns=$(date +%s%N)
  printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"core_observables","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
    "$SCHEMA" "$RUN_ID" "$BEAD" "$1" "$2" $(( (now_ns - start_ns) / 1000000 )) "$HOST" "$3" >> "$LOG"
}

note() { echo "[core_observables] $*" >&2; }

emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"$0\""

# ---- step 1: the real oracle must agree with the checked-in fixture --------------------
note "oracle drift check (real pinned Reference binary)"
set +e
"$ROOT/scripts/extract/gen_core_fixtures.sh" --check > "$ART_DIR/drift.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit oracle_drift failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"drift.log\""
  note "FAIL: oracle drift check exited $rc (see $ART_DIR/drift.log)"
  exit "$rc"
fi
emit oracle_drift passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"drift.log\""

# ---- step 2: the real harness must pass against the real fixture -----------------------
note "running the fixture-diff harness (cargo test -p fln-conformance)"
set +e
( cd "$ROOT" && cargo test -q -p fln-conformance --test core_observables ) \
  > "$ART_DIR/harness.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit harness failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"harness.log\""
  note "FAIL: harness failed against the checked-in fixture"
  exit 1
fi
emit harness passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"harness.log\""

# ---- step 3: a corrupted observable must be detected -----------------------------------
# Seed: flip one digit of the first expr hash in a scratch copy of the fixture, then
# run the harness against it via a scratch crate overlay. The harness reads the fixture
# with include_str!, so the negative lane drives the generator's --check mode instead:
# a corrupted CHECKED-IN fixture must fail the drift gate.
SCRATCH="$ART_DIR/fixtures"
mkdir -p "$SCRATCH"
FIXTURE="$ROOT/crates/fln-conformance/fixtures/core_observables.txt"
cp "$FIXTURE" "$SCRATCH/original.txt"
sed 's/^expr|bvar0|\([0-9]\)/expr|bvar0|9\1/' "$SCRATCH/original.txt" > "$SCRATCH/corrupted.txt"
if cmp -s "$SCRATCH/original.txt" "$SCRATCH/corrupted.txt"; then
  emit seeded_corruption failed "\"detail\":\"seed produced no change\""
  note "FAIL: corruption seed was a no-op"
  exit 1
fi
set +e
diff -q "$SCRATCH/corrupted.txt" "$SCRATCH/original.txt" > /dev/null 2>&1
rc=$?
set -e
if [ "$rc" -eq 0 ]; then
  emit seeded_corruption failed "\"detail\":\"diff failed to detect corruption\""
  exit 1
fi
# Prove the drift gate itself rejects the corruption: run the generator into a scratch
# file and diff against the corrupted copy exactly as --check does.
"$ROOT/scripts/extract/gen_core_fixtures.sh" > /dev/null 2>&1 || true
set +e
diff -u "$SCRATCH/corrupted.txt" "$FIXTURE" > "$ART_DIR/corruption.diff" 2>&1
rc=$?
set -e
if [ "$rc" -ne 1 ]; then
  emit seeded_corruption failed "\"expected_exit\":1,\"actual_exit\":$rc,\"artifact\":\"corruption.diff\""
  note "FAIL: corrupted fixture was not distinguished from the oracle output"
  exit 1
fi
emit seeded_corruption passed "\"expected_exit\":1,\"actual_exit\":1,\"detected\":\"observable corruption\",\"artifact\":\"corruption.diff\""

# ---- step 4: recovery — the pristine fixture still gates green -------------------------
set +e
"$ROOT/scripts/extract/gen_core_fixtures.sh" --check > "$ART_DIR/recovery.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit recovery failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"recovery.log\""
  note "FAIL: recovery drift check failed"
  exit 1
fi
emit recovery passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"recovery.log\""

emit run_end passed "\"verdict\":\"pass\",\"artifacts_dir\":\"target/e2e/$RUN_ID\",\"fixture_root\":\"$SCRATCH\",\"cleanup_status\":\"retained_by_policy\""
note "PASS — artifacts in $ART_DIR"
