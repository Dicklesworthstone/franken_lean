#!/usr/bin/env bash
# Real-path Verdict schema E2E. The Rust producer emits canonical semantic
# NDJSON and a separate bounded telemetry row; scripts/evidence.py independently
# decodes every wire artifact before this lane can publish a complete bundle.

set -Eeuo pipefail

PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  echo "[verdict_schema] setup failure: python3 is required" >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
HOSTILE_PYTHON_CONFIGURATION=()
while IFS= read -r environment_name; do
  [[ "$environment_name" == PYTHON* ]] \
    && HOSTILE_PYTHON_CONFIGURATION+=("$environment_name")
done < <(compgen -e | LC_ALL=C sort)
if ((${#HOSTILE_PYTHON_CONFIGURATION[@]} > 0)); then
  printf '[verdict_schema] setup failure: sealed_interpreter_hostile_environment names=%s\n' \
    "$(IFS=,; printf '%s' "${HOSTILE_PYTHON_CONFIGURATION[*]}")" >&2
  exit 2
fi
for required_command in setsid cargo; do
  command -v "$required_command" >/dev/null 2>&1 || {
    echo "[verdict_schema] setup failure: $required_command is required" >&2
    exit 2
  }
done

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
EVIDENCE="$ROOT/scripts/evidence.py"
SCHEMA="fln.e2e/2"
BEAD="franken_lean-o5rt"
SCENARIO="verdict_schema"
RUN_ID="verdict-schema-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
HUMAN="$ART_DIR/human.log"
VENDOR_PATH="vendor/lean4-src"
VENDOR_BINDING="$ART_DIR/vendor-binding.json"
BUILD_TARGET="${CARGO_TARGET_DIR:-$ROOT/target/cargo}/e2e-verdict-schema"
CAPTURE_BYTES="${FLN_E2E_CAPTURE_BYTES:-262144}"
OUTPUT_BUDGET_BYTES="${FLN_E2E_OUTPUT_BUDGET_BYTES:-16777216}"
TIMEOUT_MS="${FLN_E2E_TIMEOUT_MS:-300000}"
GRACE_MS="${FLN_E2E_KILL_GRACE_MS:-2000}"
READY_WAIT_MS="${FLN_E2E_READY_WAIT_MS:-30000}"
case "$READY_WAIT_MS" in
  ''|*[!0-9]*)
    echo "[verdict_schema] setup failure: FLN_E2E_READY_WAIT_MS must be numeric" >&2
    exit 2
    ;;
esac
if [ "$READY_WAIT_MS" -gt 30000 ]; then
  READY_WAIT_MS=30000
fi
MAX_SEMANTIC_BYTES=65536
MAX_TELEMETRY_BYTES=4096
START_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
SEQ=0
RUN_STARTED=0
ART_DIR_CLAIMED=0
FINAL_SET=0
FINAL_VERDICT=internal_fault
FINAL_REASON=uncommitted_exit
FINAL_EXIT=2
FINALIZING=0
ACTIVE_STEP=preflight
ACTIVE_RUNNER_PID=""
ACTIVE_RUNNER_START_TICKS=""
ACTIVE_READINESS=""
EVENT_COMMAND=()
TEST_FILTER="verdict_schema_no_mock_e2e::real_positive_failure_recovery_and_thread_matrix_share_authoritative_bytes"
FAILURE_MARKER="FLN_VERDICT_E2E_EXPECTED_FAILURE: unknown proof opcode 255 at byte 21"
INPUT_PATHS=(
  Cargo.toml Cargo.lock SUITE.lock rust-toolchain.toml
  ci crates tools scripts vendor/NOTICE .github/workflows/ci.yml
)
SUBJECT_PATHS=(
  crates/fln-verdict scripts/evidence.py scripts/e2e/verdict_schema.sh
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

if ! INPUT_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path "$VENDOR_PATH"
)"; then
  echo "[verdict_schema] setup failure: cannot hash governed inputs" >&2
  exit 2
fi
HOST_FACTS_JSON="$("${PYTHON[@]}" - <<'PY'
import json
import platform

print(json.dumps({
    "machine": platform.machine(),
    "python": platform.python_version(),
    "release": platform.release(),
    "system": platform.system(),
}, sort_keys=True, separators=(",", ":")))
PY
)"

note() {
  printf '[verdict_schema] %s\n' "$*" | tee -a "$HUMAN" >&2
}

build_event_command() {
  local sequence="$SEQ"
  SEQ=$((SEQ + 1))
  EVENT_COMMAND=("${PYTHON[@]}" "$EVIDENCE" emit --file "$LOG" \
    --artifact-root "$ART_DIR" --string schema "$SCHEMA" \
    --string run_id "$RUN_ID" --string bead "$BEAD" \
    --string scenario "$SCENARIO" --integer sequence "$sequence" \
    --integer monotonic_ns "$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')" \
    --string wall_time_utc "$(date -u -Is)" "$@")
}

emit_event() {
  build_event_command "$@"
  "${EVENT_COMMAND[@]}"
}

set_final() {
  FINAL_SET=1
  FINAL_VERDICT="$1"
  FINAL_REASON="$2"
  FINAL_EXIT="$3"
}

read_meta_field() {
  "${PYTHON[@]}" - "$1" "$2" <<'PY'
import json
import pathlib
import sys

value = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))[sys.argv[2]]
print("null" if value is None else value)
PY
}

hash_governed() {
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path "$VENDOR_PATH"
}

hash_subject() {
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${SUBJECT_HASH_ARGS[@]}"
}

terminate_unreleased_runner() {
  local pid="$1"
  setsid -- "${PYTHON[@]}" "$EVIDENCE" kill-direct-child --pid "$pid" \
    --expected-parent-pid "$$" --wait-ms 5000 || return 1
  wait "$pid" 2>/dev/null || true
}

bounded_readiness_wait() {
  local pid="$1" ready_path="$2" limit_ms="$3" state
  local ticks=$(( (limit_ms + 19) / 20 )) index
  for ((index = 0; index < ticks; index += 1)); do
    if [ -s "$ready_path" ]; then
      return 0
    fi
    if [ ! -r "/proc/$pid/stat" ]; then
      return 1
    fi
    state="$(awk '{print $3}' "/proc/$pid/stat" 2>/dev/null || printf X)"
    if [ "$state" = Z ]; then
      return 1
    fi
    sleep 0.02
  done
  return 1
}

stop_active_runner() {
  local signal_name="$1" state
  if [ -z "$ACTIVE_RUNNER_PID" ]; then
    return 0
  fi
  if bounded_readiness_wait \
      "$ACTIVE_RUNNER_PID" "$ACTIVE_READINESS" "$READY_WAIT_MS" \
      && [ -n "$ACTIVE_RUNNER_START_TICKS" ]; then
    "${PYTHON[@]}" "$EVIDENCE" signal-bound-process \
      --pid "$ACTIVE_RUNNER_PID" \
      --expected-start-ticks "$ACTIVE_RUNNER_START_TICKS" \
      --signal "$signal_name" >/dev/null 2>&1 || true
  fi
  for _ in $(seq 1 500); do
    if [ ! -r "/proc/$ACTIVE_RUNNER_PID/stat" ]; then
      break
    fi
    state="$(
      awk '{print $3}' "/proc/$ACTIVE_RUNNER_PID/stat" 2>/dev/null || printf X
    )"
    if [ "$state" = Z ]; then
      break
    fi
    sleep 0.02
  done
  if [ -r "/proc/$ACTIVE_RUNNER_PID/stat" ]; then
    state="$(
      awk '{print $3}' "/proc/$ACTIVE_RUNNER_PID/stat" 2>/dev/null || printf X
    )"
    if [ "$state" != Z ]; then
      "${PYTHON[@]}" "$EVIDENCE" emergency-kill --readiness "$ACTIVE_READINESS" \
        --expected-wrapper-pid "$ACTIVE_RUNNER_PID" \
        --expected-stage-id "$ACTIVE_STEP" >/dev/null 2>&1 || return 1
    fi
  fi
  wait "$ACTIVE_RUNNER_PID" 2>/dev/null || true
  ACTIVE_RUNNER_PID=""
  ACTIVE_RUNNER_START_TICKS=""
  ACTIVE_READINESS=""
}

# shellcheck disable=SC2317
on_signal() {
  local signal_name="$1" exit_code="$2"
  trap '' HUP INT TERM
  if ! stop_active_runner "$signal_name"; then
    set_final internal_fault process_tree_cleanup_unproven 2
    exit 2
  fi
  set_final cancelled "signal_$signal_name" "$exit_code"
  exit "$exit_code"
}

# shellcheck disable=SC2317
publish_early_partial() {
  local observed_rc="$1"
  trap '' HUP INT TERM
  trap - EXIT
  if [ "$FINAL_SET" -eq 0 ]; then
    set_final internal_fault \
      "$([ "$observed_rc" -eq 0 ] && printf early_uncommitted_success || printf early_unexpected_exit)" \
      2
  fi
  if [ "$ART_DIR_CLAIMED" -eq 1 ] && [ -d "$ART_DIR" ]; then
    "${PYTHON[@]}" "$EVIDENCE" publish-partial-bundle --art-dir "$ART_DIR" \
      --run-id "$RUN_ID" --bead "$BEAD" --scenario "$SCENARIO" \
      --step "$ACTIVE_STEP" --reason "$FINAL_REASON" \
      --classification "$FINAL_VERDICT" \
      --argv-json '["scripts/e2e/verdict_schema.sh"]' --cwd "$ROOT" \
      >/dev/null 2>&1 || true
  fi
  exit "$FINAL_EXIT"
}

# shellcheck disable=SC2317
on_exit() {
  local observed_rc="$1" final_root=unavailable first_divergence=none
  local publish_rc=0
  trap '' HUP INT TERM
  trap - EXIT
  set +e
  if [ "$RUN_STARTED" -eq 0 ]; then
    publish_early_partial "$observed_rc"
  fi
  if [ "$FINALIZING" -ne 0 ]; then
    exit 2
  fi
  FINALIZING=1
  if [ "$FINAL_SET" -eq 0 ]; then
    set_final internal_fault \
      "$([ "$observed_rc" -eq 0 ] && printf uncommitted_success || printf unexpected_shell_exit)" \
      2
  fi
  if final_root="$(hash_governed)"; then
    if [ "$FINAL_VERDICT" = pass ] && [ "$final_root" != "$INPUT_ROOT" ]; then
      set_final inconclusive final_workspace_changed 3
    fi
  else
    set_final internal_fault final_workspace_hash_unavailable 2
    final_root=unavailable
  fi
  if [ "$FINAL_VERDICT" != pass ]; then
    first_divergence="$FINAL_REASON"
  fi
  emit_event --string event run_end --string verdict "$FINAL_VERDICT" \
    --string reason_code "$FINAL_REASON" --integer process_exit "$FINAL_EXIT" \
    --string active_step "$ACTIVE_STEP" \
    --integer duration_ns "$(( $("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())') - START_NS ))" \
    --string cleanup_status retained_by_policy --string final_state "$final_root" \
    --string logical_root "$final_root" \
    --string receipt_root not_applicable_schema_contract \
    --string first_divergence "$first_divergence" \
    --string evidence_manifest manifest.json \
    --string bundle_commit bundle.complete.json \
    --string evidence_state pending_bundle_commit || publish_rc=2
  if [ "$publish_rc" -eq 0 ]; then
    "${PYTHON[@]}" "$EVIDENCE" validate-run --file "$LOG" --schema "$SCHEMA" \
      --expected-verdict "$FINAL_VERDICT" --artifact-root "$ART_DIR" \
      --output "$ART_DIR/run.validation.json" || publish_rc=2
  fi
  if [ "$publish_rc" -eq 0 ]; then
    "${PYTHON[@]}" "$EVIDENCE" manifest --art-dir "$ART_DIR" \
      --output "$ART_DIR/manifest.json" \
      --digest-output "$ART_DIR/manifest.digest" \
      --run-id "$RUN_ID" --bead "$BEAD" --scenario "$SCENARIO" \
      --verdict "$FINAL_VERDICT" --input-root "$INPUT_ROOT" \
      --final-root "$final_root" || publish_rc=2
  fi
  if [ "$publish_rc" -eq 0 ]; then
    "${PYTHON[@]}" "$EVIDENCE" complete-bundle --art-dir "$ART_DIR" \
      --manifest "$ART_DIR/manifest.json" \
      --digest "$ART_DIR/manifest.digest" \
      --output "$ART_DIR/bundle.complete.json" \
      --governed-root "$ROOT" "${GOVERNED_ARGS[@]}" \
      --expected-root "$final_root" --vendor-path "$VENDOR_PATH" || true
    "${PYTHON[@]}" "$EVIDENCE" adopt-bundle --art-dir "$ART_DIR" \
      --manifest "$ART_DIR/manifest.json" \
      --digest "$ART_DIR/manifest.digest" \
      --commit "$ART_DIR/bundle.complete.json" \
      --artifact-root "$ART_DIR" >/dev/null || publish_rc=2
  fi
  if [ "$publish_rc" -ne 0 ]; then
    printf '[verdict_schema] INTERNAL FAULT: incomplete bundle %s\n' \
      "$ART_DIR" >&2
    exit 2
  fi
  if [ "$FINAL_VERDICT" = pass ]; then
    printf '[verdict_schema] PASS — committed evidence: %s\n' "$ART_DIR" >&2
  fi
  exit "$FINAL_EXIT"
}

trap 'on_signal HUP 129' HUP
trap 'on_signal INT 130' INT
trap 'on_signal TERM 143' TERM
trap 'on_exit "$?"' EXIT
ACTIVE_STEP=artifact_directory_creation
mkdir -p "$(dirname "$ART_DIR")"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  # The leaf mkdir is the single-writer claim. The losing process owns no
  # artifact path and therefore must not run its already-armed finalizer.
  trap - EXIT
  echo "[verdict_schema] evidence directory already claimed: $ART_DIR" >&2
  exit 2
fi
ART_DIR_CLAIMED=1
ACTIVE_STEP=vendor_binding
"${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" \
  --vendor-path "$VENDOR_PATH" --output "$VENDOR_BINDING" \
  --artifact-root "$ART_DIR" || {
    set_final internal_fault early_vendor_binding_failure 2
    exit 2
  }
ACTIVE_STEP=run_start_emission
emit_event --new-log --string event run_start \
  --json-value argv '["scripts/e2e/verdict_schema.sh"]' --string cwd "$ROOT" \
  --append-string claim_ids franken_lean-o5rt-schema-contract \
  --append-string invariant_ids FL-INV-01 \
  --append-string invariant_ids FL-INV-06 \
  --append-string invariant_ids FL-INV-07 \
  --append-string gate_ids W7-verdict-contract \
  --string parity_ledger_row not_applicable_solver_independent_schema \
  --string epoch lean-v4.32.0 --string mode sound --string profile e2e \
  --string platform "$(uname -srm)" --integer thread_count 32 \
  --json-value thread_matrix '[1,8,32]' \
  --json-value host_facts "$HOST_FACTS_JSON" \
  --string seed verdict-schema-fixture-v1 \
  --string cache_state "${FLN_E2E_CACHE_STATE:-uncontrolled}" \
  --string input_root "$INPUT_ROOT" --string vendor_binding vendor-binding.json \
  --json-value budgets "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$TIMEOUT_MS,\"kill_grace_ms\":$GRACE_MS,\"max_semantic_bytes\":$MAX_SEMANTIC_BYTES,\"max_telemetry_bytes\":$MAX_TELEMETRY_BYTES,\"max_workers\":41}" \
  || {
    set_final internal_fault early_run_start_emission_failure 2
    exit 2
  }
: > "$HUMAN"
RUN_STARTED=1

supervise() {
  local step="$1"
  shift
  local -a semantic_args=()
  if [ "${1:-}" = --semantic-failure-exit ]; then
    semantic_args+=(--semantic-failure-exit "$2")
    shift 2
  fi
  LAST_META="$ART_DIR/$step.meta.json"
  LAST_OUT="$ART_DIR/$step.out"
  LAST_ERR="$ART_DIR/$step.err"
  LAST_READY="$ART_DIR/$step.ready.json"
  local launch_ready="$ART_DIR/$step.launch.ready.json"
  local launch_release="$ART_DIR/$step.launch.release.json"
  ACTIVE_STEP="$step"
  setsid -- "${PYTHON[@]}" "$EVIDENCE" run --cwd "$ROOT" \
    --metadata "$LAST_META" --stdout "$LAST_OUT" --stderr "$LAST_ERR" \
    --readiness "$LAST_READY" --launch-ready "$launch_ready" \
    --launch-release "$launch_release" --artifact-root "$ART_DIR" \
    --capture-bytes "$CAPTURE_BYTES" \
    --output-budget-bytes "$OUTPUT_BUDGET_BYTES" \
    --timeout-ms "$TIMEOUT_MS" --grace-ms "$GRACE_MS" \
    --stage-id "$step" "${semantic_args[@]}" -- "$@" &
  ACTIVE_RUNNER_PID=$!
  if ! ACTIVE_RUNNER_START_TICKS="$(
    setsid -- "${PYTHON[@]}" "$EVIDENCE" process-start-ticks \
      --pid "$ACTIVE_RUNNER_PID" --expected-parent-pid "$$" \
      --wait-ms "$READY_WAIT_MS" --session-leader 2>/dev/null
  )"; then
    terminate_unreleased_runner "$ACTIVE_RUNNER_PID" || true
    ACTIVE_RUNNER_PID=""
    set_final internal_fault active_runner_identity_unproven 2
    exit 2
  fi
  ACTIVE_READINESS="$LAST_READY"
  if ! setsid -- "${PYTHON[@]}" "$EVIDENCE" release-process-launch \
      --ready "$launch_ready" --output "$launch_release" \
      --artifact-root "$ART_DIR" --stage-id "$step" \
      --pid "$ACTIVE_RUNNER_PID" \
      --expected-start-ticks "$ACTIVE_RUNNER_START_TICKS" \
      --expected-parent-pid "$$" --wait-ms "$READY_WAIT_MS"; then
    stop_active_runner TERM || true
    set_final internal_fault active_runner_launch_unproven 2
    exit 2
  fi
  if wait "$ACTIVE_RUNNER_PID"; then
    LAST_RC=0
  else
    LAST_RC=$?
  fi
  ACTIVE_RUNNER_PID=""
  ACTIVE_RUNNER_START_TICKS=""
  ACTIVE_READINESS=""
}

inspect_supervisor() {
  local step="$1" expected_class
  if [ ! -s "$LAST_META" ]; then
    set_final internal_fault "$step:missing_supervisor_metadata" 2
    exit 2
  fi
  LAST_CLASSIFICATION="$(read_meta_field "$LAST_META" classification)"
  LAST_REASON="$(read_meta_field "$LAST_META" reason_code)"
  LAST_META_WRAPPER="$(read_meta_field "$LAST_META" wrapper_exit)"
  LAST_CHILD_EXIT="$(read_meta_field "$LAST_META" child_exit)"
  case "$LAST_RC" in
    0) expected_class=pass ;;
    1) expected_class=fail ;;
    2) expected_class=internal_fault ;;
    3) expected_class=inconclusive ;;
    4) expected_class=cancelled ;;
    *)
      set_final internal_fault "$step:unknown_wrapper_exit_$LAST_RC" 2
      exit 2
      ;;
  esac
  if [ "$LAST_META_WRAPPER" != "$LAST_RC" ] \
      || [ "$LAST_CLASSIFICATION" != "$expected_class" ]; then
    set_final internal_fault "$step:supervisor_envelope_disagreement" 2
    exit 2
  fi
  case "$LAST_RC" in
    2)
      set_final internal_fault "$step:$LAST_REASON" 2
      exit 2
      ;;
    3)
      set_final inconclusive "$step:$LAST_REASON" 3
      exit 3
      ;;
    4)
      set_final cancelled "$step:$LAST_REASON" 4
      exit 4
      ;;
  esac
}

record_step() {
  local step="$1" expected="$2" actual="$3" validation="$4"
  local expected_class="$5" expected_wrapper="$6" expected_child="$7"
  local subject_before="$8" subject_after="$9"
  local global_before="${10}" global_after="${11}"
  emit_event --string event step --string step_id "$step" \
    --string assertion pass --string expected "$expected" \
    --string actual "$actual" --string input_root "$global_before" \
    --string final_state "$global_after" \
    --string validation_artifact "$validation" \
    --string expected_supervisor_classification "$expected_class" \
    --integer expected_wrapper_exit "$expected_wrapper" \
    --integer expected_child_exit "$expected_child" \
    --string subject_root "$subject_before" \
    --string subject_final_state "$subject_after" \
    --json-file supervisor "$LAST_META"
}

record_failure() {
  local step="$1" reason="$2"
  note "FAIL step=$step: $reason"
  emit_event --string event step --string step_id "$step" \
    --string assertion fail --string expected "$reason" \
    --string actual "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
    --string input_root "$GLOBAL_BEFORE" --string final_state "$GLOBAL_AFTER" \
    --string validation_artifact not_applicable \
    --string expected_supervisor_classification "$LAST_CLASSIFICATION" \
    --integer expected_wrapper_exit "$LAST_RC" \
    --integer expected_child_exit "$LAST_CHILD_EXIT" \
    --string subject_root "$SUBJECT_BEFORE" \
    --string subject_final_state "$SUBJECT_AFTER" \
    --json-file supervisor "$LAST_META"
  set_final fail "$step:$reason" 1
  exit 1
}

snapshot_before() {
  local step="$1"
  SUBJECT_BEFORE="$(hash_subject)" || {
    set_final internal_fault "$step:subject_pre_hash_unavailable" 2
    exit 2
  }
  GLOBAL_BEFORE="$(hash_governed)" || {
    set_final internal_fault "$step:global_pre_hash_unavailable" 2
    exit 2
  }
}

snapshot_after() {
  local step="$1"
  SUBJECT_AFTER="$(hash_subject)" || {
    set_final internal_fault "$step:subject_post_hash_unavailable" 2
    exit 2
  }
  GLOBAL_AFTER="$(hash_governed)" || {
    set_final internal_fault "$step:global_post_hash_unavailable" 2
    exit 2
  }
  if [ "$SUBJECT_BEFORE" != "$SUBJECT_AFTER" ] \
      || [ "$GLOBAL_BEFORE" != "$GLOBAL_AFTER" ]; then
    note "INCONCLUSIVE step=$step: governed_inputs_changed"
    set_final inconclusive "$step:governed_inputs_changed" 3
    exit 3
  fi
}

run_phase() {
  local phase="$1" expected_class="$2" expected_wrapper="$3"
  local expected_child="$4"
  local semantic="$ART_DIR/$phase.semantic.ndjson"
  local telemetry="$ART_DIR/$phase.telemetry.ndjson"
  local validation="$ART_DIR/$phase.validation.json"
  local -a supervisor_args=() validator_args=()
  if [ "$expected_child" -ne 0 ]; then
    supervisor_args+=(--semantic-failure-exit "$expected_child")
  fi
  if [ "$phase" = recovery ]; then
    validator_args+=(--positive-semantic "$ART_DIR/positive.semantic.ndjson")
  fi
  snapshot_before "$phase"
  note "running phase=$phase expected=$expected_class/$expected_wrapper/$expected_child"
  supervise "$phase" "${supervisor_args[@]}" env \
    FLN_VERDICT_E2E_PHASE="$phase" \
    FLN_VERDICT_E2E_SEMANTIC_PATH="$semantic" \
    FLN_VERDICT_E2E_TELEMETRY_PATH="$telemetry" \
    CARGO_TARGET_DIR="$BUILD_TARGET" \
    cargo test --locked -q -p fln-verdict "$TEST_FILTER" \
    -- --exact --nocapture
  inspect_supervisor "$phase"
  snapshot_after "$phase"
  if [ "$LAST_CLASSIFICATION" != "$expected_class" ] \
      || [ "$LAST_RC" -ne "$expected_wrapper" ] \
      || [ "$LAST_CHILD_EXIT" != "$expected_child" ]; then
    record_failure "$phase" supervisor_contract_mismatch
  fi
  if [ "$phase" = failure ]; then
    grep -Fqx "$FAILURE_MARKER" "$LAST_OUT" || \
      record_failure "$phase" intended_reason_missing_from_stdout
    grep -Fq "$FAILURE_MARKER" "$LAST_ERR" || \
      record_failure "$phase" intended_reason_missing_from_stderr
  fi
  if ! "${PYTHON[@]}" "$EVIDENCE" validate-verdict-schema \
      --semantic "$semantic" --telemetry "$telemetry" \
      --stdout "$LAST_OUT" --stderr "$LAST_ERR" --phase "$phase" \
      --observed-exit "$LAST_CHILD_EXIT" "${validator_args[@]}" \
      --artifact-root "$ART_DIR" --output "$validation"; then
    record_failure "$phase" independent_semantic_validation_failed
  fi
  record_step "$phase" \
    "verdict-schema/1:$phase/$expected_class/wrapper=$expected_wrapper/child=$expected_child" \
    "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
    "${validation#"$ART_DIR"/}" "$expected_class" "$expected_wrapper" \
    "$expected_child" "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
    "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
}

run_phase positive pass 0 0
run_phase failure fail 1 101
run_phase recovery pass 0 0

ACTIVE_STEP=final_real_recheck
snapshot_before "$ACTIVE_STEP"
note "running final real fln-verdict crate recheck"
supervise "$ACTIVE_STEP" env CARGO_TARGET_DIR="$BUILD_TARGET" \
  cargo test --locked -q -p fln-verdict
inspect_supervisor "$ACTIVE_STEP"
snapshot_after "$ACTIVE_STEP"
if [ "$LAST_CLASSIFICATION" != pass ] || [ "$LAST_RC" -ne 0 ] \
    || [ "$LAST_CHILD_EXIT" != 0 ]; then
  record_failure "$ACTIVE_STEP" final_real_recheck_failed
fi
record_step "$ACTIVE_STEP" \
  "cargo-test/fln-verdict/pass/wrapper=0/child=0" \
  "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
  not_applicable pass 0 0 "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
  "$GLOBAL_BEFORE" "$GLOBAL_AFTER"

ACTIVE_STEP=final_real_recheck
set_final pass all_scenarios_satisfied 0
exit 0
