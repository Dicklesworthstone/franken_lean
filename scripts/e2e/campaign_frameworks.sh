#!/usr/bin/env bash
# campaign_frameworks.sh — shared E2E scenario for the W1 Tribunal campaign
# frameworks (bead fln-td9).
#
# Real-path, no-mock: the seven named framework suites run against their real
# controlled targets (the committed uagk kill receipts, the kill-ledger NDJSON
# parser, real OS threads, the committed owner matrix and fault census); the
# test-count conservation is validated; then a duplicate adapter row is planted
# in the REAL owner matrix and the owner-matrix suite must refuse it, before a
# byte-exact pristine recovery. NDJSON under target/e2e/; fixtures retained.

set -Eeuo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

RUN_ID="campaign-frameworks-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$(dirname "$ART_DIR")"
# The artifact root is CLAIMED atomically: a RUN_ID collision must refuse, never
# share one directory between two lanes (evidence_finalization's atomicity law).
if ! mkdir "$ART_DIR" 2>/dev/null; then
  echo "[campaign_frameworks] setup failure: evidence directory already claimed: $ART_DIR" >&2
  exit 2
fi

SCHEMA="fln-e2e/1"
BEAD="fln-td9"
SCENARIO="campaign_frameworks"
HOST="$(uname -sr)"
start_ns=$(date +%s%N)

# The build gate: this lane plants a defect in a governed file mid-run and no
# other lane may overlap that window. Taken by the lane itself (o2vz's law:
# the lock engages only if the caller volunteers).
# SC1091: the library is checked directly as its own input to check.sh's shellcheck stage.
# shellcheck source=scripts/lib/gate_lock.sh
# shellcheck disable=SC1091
. "$ROOT/scripts/lib/gate_lock.sh"
fln_gate_acquire "$SCENARIO"

emit() { # emit <step_id> <status> <detail-json-fragment>
  local now_ns
  now_ns=$(date +%s%N)
  printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"%s","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
    "$SCHEMA" "$RUN_ID" "$BEAD" "$SCENARIO" "$1" "$2" $(( (now_ns - start_ns) / 1000000 )) "$HOST" "$3" >> "$LOG"
}

note() { echo "[campaign_frameworks] $*" >&2; }

SUITES=(
  campaign_owner_matrix
  mutation_kill_ledger_model
  fuzz_seed_replay
  fault_boundary_registry
  shrink_signature_preservation
  no_mock_attestation
  productive_thread_matrix
)
EXPECTED_TESTS=61 # 16 + 9 + 7 + 9 + 7 + 6 + 7, conserved below
MATRIX="$ROOT/ci/CAMPAIGN_OWNER_MATRIX.txt"
MATRIX_BACKUP="$ART_DIR/CAMPAIGN_OWNER_MATRIX.pristine"
cp "$MATRIX" "$MATRIX_BACKUP"

restore_matrix() {
  if [ -f "$MATRIX_BACKUP" ]; then
    cp "$MATRIX_BACKUP" "$MATRIX" || true
  fi
}
# Byte-exact recovery no matter where the lane exits (a failed leg still
# restores; the pristine check below verifies, never assumes).
trap restore_matrix EXIT

emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"$0\",\"suites\":${#SUITES[@]}"

# ---- step 1: the seven framework suites run green against their real targets -----------
note "running the seven named framework suites"
total_tests=0
for suite in "${SUITES[@]}"; do
  set +e
  cargo test -p fln-conformance --test "$suite" > "$ART_DIR/suite-$suite.log" 2>&1
  rc=$?
  set -e
  if [ "$rc" -ne 0 ]; then
    emit suite_matrix failed "\"suite\":\"$suite\",\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"suite-$suite.log\""
    note "FAIL: suite $suite exited $rc"
    exit "$rc"
  fi
  suite_tests="$(grep -cE '^test .* \.\.\. ok$' "$ART_DIR/suite-$suite.log" || true)"
  total_tests=$((total_tests + suite_tests))
done
emit suite_matrix passed "\"suites\":${#SUITES[@]},\"tests\":$total_tests"

# ---- step 2: conservation — the bundle accounts for every test -------------------------
if [ "$total_tests" -ne "$EXPECTED_TESTS" ]; then
  emit conservation failed "\"expected\":$EXPECTED_TESTS,\"actual\":$total_tests,\"detail\":\"a suite's cell count moved without the lane's constant moving — conservation, not a guess\""
  note "FAIL: test conservation $total_tests != $EXPECTED_TESTS"
  exit 1
fi
emit conservation passed "\"expected\":$EXPECTED_TESTS,\"actual\":$total_tests"

# ---- step 3: a planted duplicate adapter row is refused by the real suite --------------
note "planting a duplicate adapter row in the real owner matrix"
printf 'adapter grammar-source | mutation  | fln-7li          | registered |\n' >> "$MATRIX"
set +e
cargo test -p fln-conformance --test campaign_owner_matrix > "$ART_DIR/planted.log" 2>&1
rc=$?
set -e
if [ "$rc" -eq 0 ]; then
  emit planted_duplicate_row_refused failed "\"detail\":\"the owner-matrix suite passed against a planted duplicate row — the duplicate-refusal law is not discriminating\""
  note "FAIL: planted duplicate row was not refused"
  exit 1
fi
# Any appended row trips two laws: the row-count conservation in the committed-matrix
# test (which fires first) and the duplicate-adapter validation finding. Either named
# signature proves the suite discriminated the tampered census file rather than the
# run being red for an unrelated reason.
if ! grep -qE "already declared|adapter rows are the bead's own mapping" "$ART_DIR/planted.log"; then
  emit planted_duplicate_row_refused failed "\"detail\":\"the suite failed but not for the stated reason\",\"artifact\":\"planted.log\""
  note "FAIL: suite failed without naming the tamper"
  exit 1
fi
emit planted_duplicate_row_refused passed "\"expected\":\"suite fails naming the tamper\",\"actual\":\"failed with the tamper named\""

# ---- step 4: pristine recovery — byte-exact, verified ----------------------------------
restore_matrix
trap - EXIT
if ! cmp -s "$MATRIX_BACKUP" "$MATRIX"; then
  emit pristine_recovery failed "\"detail\":\"the matrix file differs from its pre-plant bytes after restore\""
  note "FAIL: recovery was not byte-exact"
  exit 1
fi
set +e
cargo test -p fln-conformance --test campaign_owner_matrix > "$ART_DIR/recovery.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit pristine_recovery failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"recovery.log\""
  note "FAIL: suite red after pristine recovery"
  exit "$rc"
fi
emit pristine_recovery passed "\"sha\":\"$(sha256sum "$MATRIX" | cut -d' ' -f1)\""

# ---- step 5: the bundle ----------------------------------------------------------------
cat > "$ART_DIR/manifest.json" <<EOF
{"schema":"$SCHEMA","run_id":"$RUN_ID","bead":"$BEAD","scenario":"$SCENARIO","suites":${#SUITES[@]},"tests":$total_tests,"host":"$HOST"}
EOF
printf '{"run_id":"%s","bead":"%s","scenario":"%s","status":"complete","tests":%d}\n' \
  "$RUN_ID" "$BEAD" "$SCENARIO" "$total_tests" > "$ART_DIR/bundle.complete.json"
emit bundle_finalize passed "\"artifact_root\":\"$ART_DIR\",\"tests\":$total_tests"
note "OK: $total_tests tests across ${#SUITES[@]} suites; plant-and-recover green"
