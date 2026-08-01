#!/usr/bin/env bash
# W4 macro transaction no-mock evidence lane.
# The Rust driver uses the public transaction and quotation APIs; evidence.py
# independently validates canonical semantic rows and separate telemetry.

set -Eeuo pipefail

PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  printf '[macro_txn_no_mock_e2e] setup failure: python3 is required\n' >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
for required_command in cargo setsid sha256sum; do
  command -v "$required_command" >/dev/null 2>&1 || {
    printf '[macro_txn_no_mock_e2e] setup failure: %s is required\n' \
      "$required_command" >&2
    exit 2
  }
done

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
cd "$ROOT"
EVIDENCE="$ROOT/scripts/evidence.py"
SCHEMA="fln.e2e/2"
BEAD="franken_lean-qr74"
SCENARIO="macro_txn_no_mock_e2e"
RUN_ID="macro-txn-no-mock-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
VENDOR_PATH="vendor/lean4-src"
VENDOR_BINDING="$ART_DIR/vendor-binding.json"
BUILD_TARGET="${CARGO_TARGET_DIR:-$ROOT/target/cargo}/e2e-macro-txn"
CAPTURE_BYTES="${FLN_E2E_CAPTURE_BYTES:-262144}"
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
  ci/VERIFICATION_MANIFEST.jsonl
  crates/fln-core
  crates/fln-hash
  crates/fln-syntax
  crates/fln-parse
  scripts/check.sh
  scripts/e2e/macro_txn_no_mock_e2e.sh
  scripts/evidence.py
  scripts/lib/gate_lock.sh
  .github/workflows/ci.yml
  vendor/NOTICE
)
SUBJECT_PATHS=(
  crates/fln-parse/src/macro_expand.rs
  crates/fln-parse/src/macro_txn.rs
  crates/fln-parse/tests/macro_txn_state_model.rs
  crates/fln-parse/tests/read_set_completeness.rs
  crates/fln-parse/tests/nested_rollback_dpor.rs
  crates/fln-parse/tests/memoization_collision_mutations.rs
  crates/fln-parse/tests/macro_txn_no_mock_e2e.rs
)
HASH_ARGS=()
GOVERNED_ARGS=()
SUBJECT_HASH_ARGS=()
for input_path in "${INPUT_PATHS[@]}"; do
  HASH_ARGS+=(--path "$input_path")
  GOVERNED_ARGS+=(--governed-path "$input_path")
done
for subject_path in "${SUBJECT_PATHS[@]}"; do
  SUBJECT_HASH_ARGS+=(--path "$subject_path")
done

# shellcheck source=scripts/lib/gate_lock.sh
# shellcheck disable=SC1091
. "$ROOT/scripts/lib/gate_lock.sh"
trap 'fln_gate_release_note "$SCENARIO"' EXIT
fln_gate_acquire "$SCENARIO"

mkdir -p "$ART_ROOT"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  printf '[macro_txn_no_mock_e2e] setup failure: artifact path is not fresh: %s\n' \
    "$ART_DIR" >&2
  exit 2
fi

"${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" \
  --vendor-path "$VENDOR_PATH" --output "$VENDOR_BINDING" \
  --artifact-root "$ART_DIR" || {
    printf '[macro_txn_no_mock_e2e] setup failure: cannot bind vendored Reference\n' >&2
    exit 2
  }
INPUT_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path "$VENDOR_PATH"
)" || {
  printf '[macro_txn_no_mock_e2e] setup failure: cannot hash governed inputs\n' >&2
  exit 2
}
SUBJECT_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" \
    "${SUBJECT_HASH_ARGS[@]}"
)" || {
  printf '[macro_txn_no_mock_e2e] setup failure: cannot hash subject inputs\n' >&2
  exit 2
}
HOST_FACTS_JSON="$(
  "${PYTHON[@]}" -c \
    'import json,platform; print(json.dumps({"machine":platform.machine(),"python":platform.python_version(),"release":platform.release(),"system":platform.system()},sort_keys=True,separators=(",",":")))'
)"

emit_event() {
  local sequence="$SEQ"
  SEQ=$((SEQ + 1))
  "${PYTHON[@]}" "$EVIDENCE" emit --file "$LOG" \
    --artifact-root "$ART_DIR" \
    --string schema "$SCHEMA" --string run_id "$RUN_ID" \
    --string bead "$BEAD" --string scenario "$SCENARIO" \
    --integer sequence "$sequence" \
    --integer monotonic_ns "$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')" \
    --string wall_time_utc "$(date -u -Is)" "$@"
}

emit_event --new-log --string event run_start \
  --json-value argv '["scripts/e2e/macro_txn_no_mock_e2e.sh"]' \
  --string cwd "$ROOT" \
  --append-string claim_ids FLN-W4-MACRO-TXN-ATOMIC-PUBLICATION \
  --append-string claim_ids FLN-W4-MACRO-TXN-COLLISION-SAFE-MEMOIZATION \
  --append-string claim_ids FLN-W4-MACRO-TXN-COMPLETE-READ-SET \
  --append-string invariant_ids FL-INV-01 \
  --append-string invariant_ids FL-INV-07 \
  --append-string gate_ids W4 \
  --string parity_ledger_row not_applicable_w4_macro_transaction_slice \
  --string epoch internal-w4 --string mode sound \
  --string profile e2e --string platform "$(uname -srm)" \
  --integer thread_count 32 --string seed macro-txn-state-v1 \
  --string cache_state "${FLN_E2E_CACHE_STATE:-uncontrolled}" \
  --string input_root "$INPUT_ROOT" --string subject_root "$SUBJECT_ROOT" \
  --string vendor_binding vendor-binding.json \
  --producer-binding-root "$ROOT" "${GOVERNED_ARGS[@]}" \
  --json-value host_facts "$HOST_FACTS_JSON" \
  --json-value budgets \
    "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$TIMEOUT_MS,\"kill_grace_ms\":$GRACE_MS}"

run_step() {
  local step="$1"
  shift
  local metadata="$ART_DIR/$step.meta.json"
  local stdout="$ART_DIR/$step.out"
  local stderr="$ART_DIR/$step.err"
  local readiness="$ART_DIR/$step.ready.json"
  local validation="$ART_DIR/$step.validation.json"
  local wrapper_rc=0

  printf '[macro_txn_no_mock_e2e] running %s\n' "$step" >&2
  setsid -- "${PYTHON[@]}" "$EVIDENCE" run --cwd "$ROOT" \
    --metadata "$metadata" --stdout "$stdout" --stderr "$stderr" \
    --readiness "$readiness" --artifact-root "$ART_DIR" \
    --capture-bytes "$CAPTURE_BYTES" \
    --output-budget-bytes "$OUTPUT_BUDGET_BYTES" \
    --timeout-ms "$TIMEOUT_MS" --grace-ms "$GRACE_MS" \
    --stage-id "$step" -- "$@" || wrapper_rc=$?
  "${PYTHON[@]}" "$EVIDENCE" validate-supervisor --file "$metadata" \
    --expected-stage-id "$step" --artifact-root "$ART_DIR" \
    --output "$validation" || {
      printf '[macro_txn_no_mock_e2e] internal fault: invalid supervisor envelope for %s\n' \
        "$step" >&2
      exit 2
    }
  if [ "$wrapper_rc" -ne 0 ]; then
    printf '[macro_txn_no_mock_e2e] refused: %s exited %s; logs=%s\n' \
      "$step" "$wrapper_rc" "$ART_DIR" >&2
    exit "$wrapper_rc"
  fi
  local current_root
  current_root="$(
    "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
      --vendor-path "$VENDOR_PATH"
  )" || {
    printf '[macro_txn_no_mock_e2e] internal fault: cannot hash %s final inputs\n' \
      "$step" >&2
    exit 2
  }
  if [ "$current_root" != "$INPUT_ROOT" ]; then
    printf '[macro_txn_no_mock_e2e] inconclusive: governed inputs changed in %s\n' \
      "$step" >&2
    exit 3
  fi
  emit_event --string event step --string step_id "$step" \
    --string assertion pass --string expected exit_zero \
    --string actual pass --string input_root "$INPUT_ROOT" \
    --string final_state "$current_root" \
    --string validation_artifact "$step.validation.json" \
    --string expected_supervisor_classification pass \
    --integer expected_wrapper_exit 0 --integer expected_child_exit 0 \
    --string subject_root "$SUBJECT_ROOT" \
    --string subject_final_state "$SUBJECT_ROOT" \
    --json-file supervisor "$metadata"
}

run_step macro_txn_targets \
  env FLN_MACRO_TXN_E2E_ART_DIR="$ART_DIR" \
    FLN_MACRO_TXN_E2E_RUN_ID="$RUN_ID" \
    CARGO_TARGET_DIR="$BUILD_TARGET" \
  cargo test --locked -q -p fln-parse \
    --test macro_txn_state_model \
    --test read_set_completeness \
    --test nested_rollback_dpor \
    --test memoization_collision_mutations \
    --test macro_txn_no_mock_e2e -- --nocapture

run_step semantic_validation "${PYTHON[@]}" "$EVIDENCE" \
  validate-macro-txn-no-mock \
  --expected-run-id "$RUN_ID" \
  --semantic "$ART_DIR/semantic.ndjson" \
  --telemetry "$ART_DIR/telemetry.ndjson" \
  --artifact-root "$ART_DIR" \
  --output "$ART_DIR/semantic.validation.json"

run_step final_real_recheck \
  env CARGO_TARGET_DIR="$BUILD_TARGET" \
  cargo test --locked -q -p fln-parse \
    --test macro_txn_no_mock_e2e -- --nocapture

SEMANTIC_ROOT="$(
  "${PYTHON[@]}" -c \
    'import json,sys; print(json.load(open(sys.argv[1],encoding="utf-8"))["semantic_root"])' \
    "$ART_DIR/semantic.validation.json"
)"
FINAL_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path "$VENDOR_PATH"
)" || {
  printf '[macro_txn_no_mock_e2e] internal fault: cannot hash final inputs\n' >&2
  exit 2
}
if [ "$FINAL_ROOT" != "$INPUT_ROOT" ]; then
  printf '[macro_txn_no_mock_e2e] inconclusive: governed inputs changed during the run\n' >&2
  exit 3
fi

END_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
emit_event --string event run_end --string verdict pass \
  --string reason_code all_macro_transaction_obligations_satisfied \
  --integer process_exit 0 --string active_step final_real_recheck \
  --integer duration_ns "$((END_NS - START_NS))" \
  --string cleanup_status retained_by_policy \
  --string final_state "$FINAL_ROOT" --string logical_root "$FINAL_ROOT" \
  --string receipt_root "$SEMANTIC_ROOT" --string first_divergence none \
  --string evidence_manifest manifest.json \
  --string bundle_commit bundle.complete.json \
  --string evidence_state pending_bundle_commit

"${PYTHON[@]}" "$EVIDENCE" validate-run --file "$LOG" \
  --schema "$SCHEMA" --expected-verdict pass --artifact-root "$ART_DIR" \
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
  --expected-root "$FINAL_ROOT" --vendor-path "$VENDOR_PATH"
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

printf '[macro_txn_no_mock_e2e] PASS evidence=%s semantic_root=%s\n' \
  "$ART_DIR" "$SEMANTIC_ROOT" >&2
