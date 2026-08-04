#!/usr/bin/env bash
# Per-epoch diagnostic projection no-mock lane (bead franken_lean-wlan).
# The Reference and FrankenLean adapters run in separate processes. Semantic
# comparison records and host/process telemetry are published to disjoint schemas
# and roots, then independently validated before the run manifest is sealed.

set -Eeuo pipefail

PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  printf '[diagnostic_projection] setup failure: python3 is required\n' >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
for required_command in cargo rg setsid sha256sum; do
  command -v "$required_command" >/dev/null 2>&1 || {
    printf '[diagnostic_projection] setup failure: %s is required\n' \
      "$required_command" >&2
    exit 2
  }
done

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
cd "$ROOT"
EVIDENCE="$ROOT/scripts/evidence.py"
BEAD="franken_lean-wlan"
SCENARIO="diagnostic_projection_no_mock_e2e"
RUN_ID="diagnostic-projection-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
RIG_DIR="$ART_DIR/rig-executions"
LOG="$ART_DIR/run.ndjson"
VENDOR_BINDING="$ART_DIR/vendor-binding.json"
BUILD_TARGET="${CARGO_TARGET_DIR:-$ROOT/target/cargo}/e2e-diagnostic-projection"
CAPTURE_BYTES="${FLN_E2E_CAPTURE_BYTES:-1048576}"
OUTPUT_BUDGET_BYTES="${FLN_E2E_OUTPUT_BUDGET_BYTES:-16777216}"
TIMEOUT_MS="${FLN_E2E_TIMEOUT_MS:-600000}"
GRACE_MS="${FLN_E2E_KILL_GRACE_MS:-2000}"
START_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
SEQ=0

INPUT_PATHS=(
  Cargo.toml
  Cargo.lock
  SUITE.lock
  rust-toolchain.toml
  .github/workflows/contract-drift.yml
  ci/VERIFICATION_MANIFEST.jsonl
  ci/WORKSPACE_GRAPH.txt
  crates/fln-core
  crates/fln-cli
  crates/fln-server
  crates/fln
  crates/fln-conformance
  tribunal/epochs/v4.32.0
  vendor/lean4-src/tests/elab_fail/1707.lean
  scripts/e2e/diag_goldens.sh
  scripts/evidence.py
)
HASH_ARGS=()
GOVERNED_ARGS=()
for input_path in "${INPUT_PATHS[@]}"; do
  HASH_ARGS+=(--path "$input_path")
  GOVERNED_ARGS+=(--governed-path "$input_path")
done

# shellcheck source=scripts/lib/gate_lock.sh
# shellcheck disable=SC1091
. "$ROOT/scripts/lib/gate_lock.sh"
trap 'fln_gate_release_note "$SCENARIO"' EXIT
fln_gate_acquire "$SCENARIO"

mkdir -p "$ART_ROOT"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  printf '[diagnostic_projection] setup failure: artifact path is not fresh: %s\n' \
    "$ART_DIR" >&2
  exit 2
fi
mkdir "$RIG_DIR"

"${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" \
  --vendor-path vendor/lean4-src --output "$VENDOR_BINDING" \
  --artifact-root "$ART_DIR"
INPUT_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path vendor/lean4-src
)"
HOST_FACTS_JSON="$(
  "${PYTHON[@]}" -c \
    'import json,platform; print(json.dumps({"machine":platform.machine(),"python":platform.python_version(),"release":platform.release(),"system":platform.system()},sort_keys=True,separators=(",",":")))'
)"

emit_event() {
  local sequence="$SEQ"
  SEQ=$((SEQ + 1))
  "${PYTHON[@]}" "$EVIDENCE" emit --file "$LOG" \
    --artifact-root "$ART_DIR" \
    --string schema fln.e2e/2 --string run_id "$RUN_ID" \
    --string bead "$BEAD" --string scenario "$SCENARIO" \
    --integer sequence "$sequence" \
    --integer monotonic_ns "$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')" \
    --string wall_time_utc "$(date -u -Is)" "$@"
}

emit_event --new-log --string event run_start \
  --json-value argv '["scripts/e2e/diag_goldens.sh"]' \
  --string cwd "$ROOT" \
  --append-string claim_ids FLN-DIAGNOSTIC-PROJECTION-PER-EPOCH-AND-FRONTEND \
  --append-string claim_ids FLN-DIAGNOSTIC-SEMANTIC-TELEMETRY-SEPARATION \
  --append-string invariant_ids FL-INV-07 \
  --append-string gate_ids W1 \
  --string parity_ledger_row not_applicable_bounded_diagnostic_projection_suite \
  --string epoch lean-v4.32.0 --string mode faithful \
  --string profile e2e --string platform "$(uname -srm)" \
  --integer thread_count 1 --string seed diagnostic-projection-v1 \
  --string cache_state "${FLN_E2E_CACHE_STATE:-uncontrolled}" \
  --string input_root "$INPUT_ROOT" \
  --string vendor_binding vendor-binding.json \
  --producer-binding-root "$ROOT" "${GOVERNED_ARGS[@]}" \
  --json-value host_facts "$HOST_FACTS_JSON" \
  --json-value budgets \
    "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$TIMEOUT_MS,\"kill_grace_ms\":$GRACE_MS}"

STEP="diagnostic_projection_contract"
METADATA="$ART_DIR/$STEP.meta.json"
STDOUT="$ART_DIR/$STEP.out"
STDERR="$ART_DIR/$STEP.err"
READINESS="$ART_DIR/$STEP.ready.json"
VALIDATION="$ART_DIR/$STEP.validation.json"
printf '[diagnostic_projection] running %s\n' "$STEP" >&2
rc=0
setsid -- "${PYTHON[@]}" "$EVIDENCE" run --cwd "$ROOT" \
  --metadata "$METADATA" --stdout "$STDOUT" --stderr "$STDERR" \
  --readiness "$READINESS" --artifact-root "$ART_DIR" \
  --capture-bytes "$CAPTURE_BYTES" \
  --output-budget-bytes "$OUTPUT_BUDGET_BYTES" \
  --timeout-ms "$TIMEOUT_MS" --grace-ms "$GRACE_MS" \
  --stage-id "$STEP" -- \
  env FLN_RIG_EXECUTION_DIR="$RIG_DIR" \
    FLN_DIAGNOSTIC_EVIDENCE_DIR="$ART_DIR" \
    FLN_DIAGNOSTIC_RUN_ID="$RUN_ID" \
    CARGO_TARGET_DIR="$BUILD_TARGET" \
    cargo test --locked -q -p fln-conformance --test diag_render || rc=$?
"${PYTHON[@]}" "$EVIDENCE" validate-supervisor --file "$METADATA" \
  --expected-stage-id "$STEP" --artifact-root "$ART_DIR" \
  --output "$VALIDATION"
if [ "$rc" -ne 0 ]; then
  printf '[diagnostic_projection] refused: cargo step exited %s; evidence=%s\n' \
    "$rc" "$ART_DIR" >&2
  exit "$rc"
fi

shopt -s nullglob
rig_records=("$RIG_DIR"/*.record)
if [ "${#rig_records[@]}" -ne 1 ] \
    || ! rg -q '^rig=test:fln-conformance::diag_render::diagnostic_projection_no_mock_e2e$' \
      "${rig_records[0]:-/dev/null}" \
    || ! rg -q '^disposition=executed$' "${rig_records[0]:-/dev/null}"; then
  printf '[diagnostic_projection] inconclusive: exact pin rig did not execute\n' >&2
  exit 3
fi

"${PYTHON[@]}" "$EVIDENCE" validate-diagnostic-projection \
  --semantic "$ART_DIR/semantic.ndjson" \
  --telemetry "$ART_DIR/telemetry.ndjson" \
  --run-id "$RUN_ID" --artifact-root "$ART_DIR" \
  --output "$ART_DIR/projection.validation.json"
SEMANTIC_ROOT="sha256:$(sha256sum "$ART_DIR/semantic.ndjson" | awk '{print $1}')"
TELEMETRY_ROOT="sha256:$(sha256sum "$ART_DIR/telemetry.ndjson" | awk '{print $1}')"
FINAL_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path vendor/lean4-src
)"
if [ "$FINAL_ROOT" != "$INPUT_ROOT" ]; then
  printf '[diagnostic_projection] inconclusive: governed inputs changed during run\n' >&2
  exit 3
fi

emit_event --string event step --string step_id "$STEP" \
  --string assertion pass --string expected exit_zero \
  --string actual pass --string input_root "$INPUT_ROOT" \
  --string final_state "$FINAL_ROOT" \
  --string validation_artifact "$STEP.validation.json" \
  --string expected_supervisor_classification pass \
  --integer expected_wrapper_exit 0 --integer expected_child_exit 0 \
  --string subject_root "$SEMANTIC_ROOT" \
  --string subject_final_state "$SEMANTIC_ROOT" \
  --string semantic_root "$SEMANTIC_ROOT" \
  --string telemetry_root "$TELEMETRY_ROOT" \
  --json-file supervisor "$METADATA"

END_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
emit_event --string event run_end --string verdict pass \
  --string reason_code all_diagnostic_projection_obligations_satisfied \
  --integer process_exit 0 --string active_step "$STEP" \
  --integer duration_ns "$((END_NS - START_NS))" \
  --string cleanup_status retained_by_policy \
  --string final_state "$FINAL_ROOT" --string logical_root "$FINAL_ROOT" \
  --string receipt_root "$SEMANTIC_ROOT" \
  --string first_divergence none --string evidence_manifest manifest.json \
  --string bundle_commit bundle.complete.json \
  --string evidence_state pending_bundle_commit
"${PYTHON[@]}" "$EVIDENCE" validate-run --file "$LOG" \
  --schema fln.e2e/2 --expected-verdict pass --artifact-root "$ART_DIR" \
  --output "$ART_DIR/run.validation.json"
"${PYTHON[@]}" "$EVIDENCE" manifest --art-dir "$ART_DIR" \
  --output "$ART_DIR/manifest.json" \
  --digest-output "$ART_DIR/manifest.digest" \
  --run-id "$RUN_ID" --bead "$BEAD" --scenario "$SCENARIO" \
  --verdict pass --input-root "$INPUT_ROOT" --final-root "$FINAL_ROOT"
"${PYTHON[@]}" "$EVIDENCE" validate-manifest --art-dir "$ART_DIR" \
  --manifest "$ART_DIR/manifest.json" --digest "$ART_DIR/manifest.digest" \
  --offline
"${PYTHON[@]}" "$EVIDENCE" complete-bundle --art-dir "$ART_DIR" \
  --manifest "$ART_DIR/manifest.json" \
  --digest "$ART_DIR/manifest.digest" \
  --output "$ART_DIR/bundle.complete.json" \
  --governed-root "$ROOT" "${GOVERNED_ARGS[@]}" \
  --expected-root "$FINAL_ROOT" --vendor-path vendor/lean4-src
"${PYTHON[@]}" "$EVIDENCE" adopt-bundle --art-dir "$ART_DIR" \
  --manifest "$ART_DIR/manifest.json" \
  --digest "$ART_DIR/manifest.digest" \
  --commit "$ART_DIR/bundle.complete.json" \
  --artifact-root "$ART_DIR" >/dev/null
"${PYTHON[@]}" "$EVIDENCE" validate-bundle --art-dir "$ART_DIR" \
  --manifest "$ART_DIR/manifest.json" \
  --digest "$ART_DIR/manifest.digest" \
  --commit "$ART_DIR/bundle.complete.json" \
  --artifact-root "$ART_DIR" >/dev/null

printf '[diagnostic_projection] PASS committed semantic=%s telemetry=%s evidence=%s\n' \
  "$SEMANTIC_ROOT" "$TELEMETRY_ROOT" "$ART_DIR" >&2
