#!/usr/bin/env bash
# G0-4 no-mock syntax/hygiene lane. Every named C0-C2 contract surface runs
# against the real workspace, the pin-dependent comparator must emit an
# EXECUTED record, and bounded supervisor logs plus a validated evidence
# manifest are retained under target/e2e. No fixture is regenerated in place.

set -Eeuo pipefail

PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  printf '[g0_4_no_mock_e2e] setup failure: python3 is required\n' >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
for required_command in cargo rg setsid; do
  command -v "$required_command" >/dev/null 2>&1 || {
    printf '[g0_4_no_mock_e2e] setup failure: %s is required\n' \
      "$required_command" >&2
    exit 2
  }
done

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
cd "$ROOT"
EVIDENCE="$ROOT/scripts/evidence.py"
BEAD="franken_lean-hly"
SCENARIO="g0_4_no_mock_e2e"
RUN_ID="g04-no-mock-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
RIG_DIR="$ART_DIR/rig-executions"
LOG="$ART_DIR/run.ndjson"
VENDOR_BINDING="$ART_DIR/vendor-binding.json"
BUILD_TARGET="${CARGO_TARGET_DIR:-$ROOT/target/cargo}/e2e-g04"
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
  ci/VERIFICATION_MANIFEST.jsonl
  crates/fln-core
  crates/fln-syntax
  crates/fln-parse
  crates/fln-conformance
  scripts/e2e/g0_4_no_mock_e2e.sh
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
  printf '[g0_4_no_mock_e2e] setup failure: artifact path is not fresh: %s\n' \
    "$ART_DIR" >&2
  exit 2
fi
mkdir "$RIG_DIR"

"${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" \
  --vendor-path vendor/lean4-src --output "$VENDOR_BINDING" \
  --artifact-root "$ART_DIR" || {
    printf '[g0_4_no_mock_e2e] setup failure: cannot bind vendored Reference\n' >&2
    exit 2
  }
INPUT_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path vendor/lean4-src
)" || {
  printf '[g0_4_no_mock_e2e] setup failure: cannot hash inputs\n' >&2
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
    --string schema fln.e2e/2 --string run_id "$RUN_ID" \
    --string bead "$BEAD" --string scenario "$SCENARIO" \
    --integer sequence "$sequence" \
    --integer monotonic_ns "$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')" \
    --string wall_time_utc "$(date -u -Is)" "$@"
}

emit_event --new-log --string event run_start \
  --json-value argv '["scripts/e2e/g0_4_no_mock_e2e.sh"]' \
  --string cwd "$ROOT" \
  --append-string claim_ids FLN-G04-HYGIENE-FIDELITY-PRICED-NOT-ASSUMED \
  --append-string invariant_ids FL-INV-01 \
  --append-string invariant_ids FL-INV-07 \
  --append-string gate_ids G0-4 \
  --string parity_ledger_row not_applicable_g04_spike_contract \
  --string epoch lean-v4.32.0 --string mode faithful \
  --string profile e2e --string platform "$(uname -srm)" \
  --integer thread_count 32 --string seed g04-manifest-v1 \
  --string cache_state "${FLN_E2E_CACHE_STATE:-uncontrolled}" \
  --string input_root "$INPUT_ROOT" \
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
  local rc=0

  printf '[g0_4_no_mock_e2e] running %s\n' "$step" >&2
  setsid -- "${PYTHON[@]}" "$EVIDENCE" run --cwd "$ROOT" \
    --metadata "$metadata" --stdout "$stdout" --stderr "$stderr" \
    --readiness "$readiness" --artifact-root "$ART_DIR" \
    --capture-bytes "$CAPTURE_BYTES" \
    --output-budget-bytes "$OUTPUT_BUDGET_BYTES" \
    --timeout-ms "$TIMEOUT_MS" --grace-ms "$GRACE_MS" \
    --stage-id "$step" -- "$@" || rc=$?
  "${PYTHON[@]}" "$EVIDENCE" validate-supervisor --file "$metadata" \
    --expected-stage-id "$step" --artifact-root "$ART_DIR" \
    --output "$validation" || {
      printf '[g0_4_no_mock_e2e] internal fault: invalid supervisor envelope for %s\n' \
        "$step" >&2
      exit 2
    }
  if [ "$rc" -ne 0 ]; then
    printf '[g0_4_no_mock_e2e] refused: %s exited %s; logs=%s\n' \
      "$step" "$rc" "$ART_DIR" >&2
    exit "$rc"
  fi
  local final_root
  final_root="$(
    "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
      --vendor-path vendor/lean4-src
  )" || {
    printf '[g0_4_no_mock_e2e] internal fault: cannot hash %s final inputs\n' \
      "$step" >&2
    exit 2
  }
  if [ "$final_root" != "$INPUT_ROOT" ]; then
    printf '[g0_4_no_mock_e2e] inconclusive: governed inputs changed in %s\n' \
      "$step" >&2
    exit 3
  fi
  emit_event --string event step --string step_id "$step" \
    --string assertion pass --string expected exit_zero \
    --string actual pass --string input_root "$INPUT_ROOT" \
    --string final_state "$final_root" \
    --string validation_artifact "$step.validation.json" \
    --string expected_supervisor_classification pass \
    --integer expected_wrapper_exit 0 --integer expected_child_exit 0 \
    --string subject_root "$INPUT_ROOT" \
    --string subject_final_state "$final_root" \
    --json-file supervisor "$metadata"
}

run_step syntax_hygiene_contract \
  env FLN_RIG_EXECUTION_DIR="$RIG_DIR" CARGO_TARGET_DIR="$BUILD_TARGET" \
  cargo test --locked -q -p fln-conformance \
    --test syntax_fixture_manifest \
    --test grammar_epoch_transition_model \
    --test hygiene_scope_capture_model \
    --test quotation_splice_model \
    --test syntax_budget_matrix \
    --test g0_4_no_mock_e2e

run_step pratt_precedence_contract \
  env CARGO_TARGET_DIR="$BUILD_TARGET" \
  cargo test --locked -q -p fln-parse --test pratt_precedence_model

run_step terminal_trivia_contract \
  env CARGO_TARGET_DIR="$BUILD_TARGET" \
  cargo test --locked -q -p fln-syntax --lib \
    a_terminal_token_keeps_its_final_comment_and_newline

shopt -s nullglob
rig_records=("$RIG_DIR"/*.record)
if [ "${#rig_records[@]}" -ne 1 ] \
    || ! rg -q '^rig=test:fln-conformance::g0_4_no_mock_e2e::g0_4_no_mock_e2e$' \
      "${rig_records[0]:-/dev/null}" \
    || ! rg -q '^disposition=executed$' "${rig_records[0]:-/dev/null}"; then
  printf '[g0_4_no_mock_e2e] inconclusive: pin-dependent comparator was not executed\n' >&2
  exit 3
fi

FINAL_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path vendor/lean4-src
)" || {
  printf '[g0_4_no_mock_e2e] internal fault: cannot hash final inputs\n' >&2
  exit 2
}
if [ "$FINAL_ROOT" != "$INPUT_ROOT" ]; then
  printf '[g0_4_no_mock_e2e] inconclusive: governed inputs changed during the run\n' >&2
  exit 3
fi

END_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
emit_event --string event run_end --string verdict pass \
  --string reason_code all_g04_obligations_satisfied \
  --integer process_exit 0 --string active_step terminal_trivia_contract \
  --integer duration_ns "$((END_NS - START_NS))" \
  --string cleanup_status retained_by_policy \
  --string final_state "$FINAL_ROOT" --string logical_root "$FINAL_ROOT" \
  --string receipt_root committed_g04_receipts \
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

printf '[g0_4_no_mock_e2e] PASS evidence=%s\n' "$ART_DIR" >&2
