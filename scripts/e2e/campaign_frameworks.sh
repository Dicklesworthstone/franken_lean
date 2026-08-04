#!/usr/bin/env bash
# campaign_frameworks.sh — shared E2E scenario for the W1 Tribunal campaign
# frameworks (bead fln-td9), fln.e2e/2.
#
# Real-path, no-mock: the seven named framework suites run as supervised children
# against their real controlled targets (the committed uagk kill receipts, the
# kill-ledger NDJSON parser, real OS threads, the committed owner matrix and
# fault census); the 61-test conservation is validated; then a duplicate adapter
# row is planted in the REAL owner matrix and the owner-matrix suite must refuse
# it with the tamper named, before a byte-exact pristine recovery. Every child
# runs under the process-identity protocol; scripts/evidence.py independently
# validates the run record before the bundle completes.

set -Eeuo pipefail

PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  echo "[campaign_frameworks] setup failure: python3 is required" >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
HOSTILE_PYTHON_CONFIGURATION=()
while IFS= read -r environment_name; do
  [[ "$environment_name" == PYTHON* ]] \
    && HOSTILE_PYTHON_CONFIGURATION+=("$environment_name")
done < <(compgen -e | LC_ALL=C sort)
if ((${#HOSTILE_PYTHON_CONFIGURATION[@]} > 0)); then
  printf '[campaign_frameworks] setup failure: sealed_interpreter_hostile_environment names=%s\n' \
    "$(IFS=,; printf '%s' "${HOSTILE_PYTHON_CONFIGURATION[*]}")" >&2
  exit 2
fi
command -v setsid >/dev/null 2>&1 || {
  echo "[campaign_frameworks] setup failure: setsid is required" >&2
  exit 2
}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
EVIDENCE="$ROOT/scripts/evidence.py"
SCHEMA="fln.e2e/2"
BEAD="fln-td9"
SCENARIO="campaign_frameworks"
RUN_ID="campaign-frameworks-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
HUMAN="$ART_DIR/human.log"
VENDOR_PATH="vendor/lean4-src"
VENDOR_BINDING="$ART_DIR/vendor-binding.json"
CAPTURE_BYTES="${FLN_E2E_CAPTURE_BYTES:-262144}"
OUTPUT_BUDGET_BYTES="${FLN_E2E_OUTPUT_BUDGET_BYTES:-16777216}"
TIMEOUT_MS="${FLN_E2E_TIMEOUT_MS:-600000}"
GRACE_MS="${FLN_E2E_KILL_GRACE_MS:-2000}"
READY_WAIT_MS="${FLN_E2E_READY_WAIT_MS:-30000}"
case "$READY_WAIT_MS" in
  ''|*[!0-9]*)
    echo "[campaign_frameworks] setup failure: FLN_E2E_READY_WAIT_MS must be numeric" >&2
    exit 2
    ;;
esac
if [ "$READY_WAIT_MS" -gt 30000 ]; then
  READY_WAIT_MS=30000
fi
START_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
SEQ=0
ACTIVE_STEP=setup
ACTIVE_RUNNER_PID=""
ACTIVE_RUNNER_START_TICKS=""
ACTIVE_READINESS=""
FINAL_SET=0
FINAL_VERDICT=internal_fault
FINAL_REASON=uncommitted_exit
FINAL_EXIT=2
TERMINAL_EMITTED=0
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

# The build gate: this lane plants a defect in a governed file mid-run and no
# other lane may overlap that window (o2vz; closure_audit's wiring is the precedent).
# SC1091: the library is checked directly as its own input to check.sh's shellcheck stage.
# shellcheck source=scripts/lib/gate_lock.sh
# shellcheck disable=SC1091
. "$ROOT/scripts/lib/gate_lock.sh"
fln_gate_acquire "$SCENARIO"

INPUT_PATHS=(
  Cargo.toml Cargo.lock rust-toolchain.toml
  ci/CAMPAIGN_OWNER_MATRIX.txt ci/FAULT_BOUNDARY_REGISTRY.txt
  crates/fln-conformance/src/campaign.rs
  crates/fln-conformance/tests/campaign_owner_matrix.rs
  crates/fln-conformance/tests/mutation_kill_ledger_model.rs
  crates/fln-conformance/tests/fuzz_seed_replay.rs
  crates/fln-conformance/tests/fault_boundary_registry.rs
  crates/fln-conformance/tests/shrink_signature_preservation.rs
  crates/fln-conformance/tests/no_mock_attestation.rs
  crates/fln-conformance/tests/productive_thread_matrix.rs
  crates/fln-conformance/evidence/mandated_mutants/kills.jsonl
  scripts/e2e/campaign_frameworks.sh scripts/evidence.py scripts/check.sh
  .github/workflows/ci.yml
)
HASH_ARGS=()
GOVERNED_ARGS=()
for input_path in "${INPUT_PATHS[@]}"; do
  HASH_ARGS+=(--path "$input_path")
  GOVERNED_ARGS+=(--governed-path "$input_path")
done

if ! INPUT_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path "$VENDOR_PATH"
)"; then
  echo "[campaign_frameworks] setup failure: cannot hash governed inputs" >&2
  exit 2
fi

note() {
  printf '[campaign_frameworks] %s\n' "$*" | tee -a "$HUMAN" >&2
}

emit_event() {
  local sequence="$SEQ"
  SEQ=$((SEQ + 1))
  "${PYTHON[@]}" "$EVIDENCE" emit --file "$LOG" --artifact-root "$ART_DIR" \
    --string schema "$SCHEMA" --string run_id "$RUN_ID" --string bead "$BEAD" \
    --string scenario "$SCENARIO" --integer sequence "$sequence" \
    --integer monotonic_ns "$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')" \
    --string wall_time_utc "$(date -u -Is)" "$@"
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
  local signal_name="$1"
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
  return 0
}

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
  emit_event --string event step --string step_id "$step" \
    --string assertion pass --string expected "$expected" \
    --string actual "$actual" --string input_root "$subject_before" \
    --string final_state "$subject_after" \
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
    --string subject_root "$GLOBAL_BEFORE" \
    --string subject_final_state "$GLOBAL_AFTER" \
    --json-file supervisor "$LAST_META"
}

MATRIX="$ROOT/ci/CAMPAIGN_OWNER_MATRIX.txt"

restore_matrix() {
  if [ -f "$ART_DIR/CAMPAIGN_OWNER_MATRIX.pristine" ]; then
    cp "$ART_DIR/CAMPAIGN_OWNER_MATRIX.pristine" "$MATRIX" 2>/dev/null || true
  fi
}

finalize() {
  local exit_code="$1"
  stop_active_runner TERM || true
  restore_matrix
  if [ "$FINAL_SET" -eq 0 ]; then
    set_final internal_fault uncommitted_exit 2
  fi
  local first_divergence=none
  if [ "$FINAL_VERDICT" != "pass" ]; then
    first_divergence="$FINAL_REASON"
  fi
  local final_root
  if ! final_root="$(hash_governed)"; then
    final_root=unavailable
    if [ "$FINAL_VERDICT" = "pass" ]; then
      set_final internal_fault final_workspace_hash_unavailable 2
    fi
  fi
  if [ "$final_root" != "unavailable" ] && [ "$final_root" != "$INPUT_ROOT" ]; then
    if [ "$FINAL_VERDICT" = "pass" ]; then
      set_final inconclusive final_workspace_changed 3
    fi
  fi
  local publish_rc=0
  if [ "$TERMINAL_EMITTED" -eq 0 ]; then
    TERMINAL_EMITTED=1
    emit_event --string event run_end --string verdict "$FINAL_VERDICT" \
      --string reason_code "$FINAL_REASON" --integer process_exit "$FINAL_EXIT" \
      --string active_step "$ACTIVE_STEP" \
      --integer duration_ns "$(( $("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())') - START_NS ))" \
      --string cleanup_status retained_by_policy --string final_state "$final_root" \
      --string logical_root "$final_root" \
      --string receipt_root not_applicable_no_durable_store \
      --string first_divergence "$first_divergence" \
      --string evidence_manifest manifest.json \
      --string bundle_commit bundle.complete.json \
      --string evidence_state pending_bundle_commit || publish_rc=2
  else
    # The EXIT trap re-enters after an explicit finalize: the publish sequence is
    # not idempotent (validate-run refuses an existing output), so the second
    # entry ends here with the first entry's verdict already published.
    exit "$FINAL_EXIT"
  fi
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
      --vendor-path "$VENDOR_PATH" \
      --expected-root "$final_root" || true
    "${PYTHON[@]}" "$EVIDENCE" adopt-bundle --art-dir "$ART_DIR" \
      --manifest "$ART_DIR/manifest.json" \
      --digest "$ART_DIR/manifest.digest" \
      --commit "$ART_DIR/bundle.complete.json" \
      --artifact-root "$ART_DIR" >/dev/null || publish_rc=2
  fi
  if [ "$publish_rc" -ne 0 ]; then
    printf '[campaign_frameworks] INTERNAL FAULT: incomplete bundle %s\n' "$ART_DIR" >&2
    exit 2
  fi
  exit "$FINAL_EXIT"
}

# shellcheck disable=SC2317
on_signal() {
  local signal_name="$1" exit_code="$2"
  set_final cancelled "signal_$signal_name" "$exit_code"
  finalize "$exit_code"
}

# shellcheck disable=SC2317
trap 'on_signal INT 130' INT
# shellcheck disable=SC2317
trap 'on_signal TERM 143' TERM
trap 'finalize "$?"' EXIT

mkdir -p "$(dirname "$ART_DIR")"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  trap - EXIT
  echo "[campaign_frameworks] evidence directory already claimed: $ART_DIR" >&2
  exit 2
fi
: > "$HUMAN"

ACTIVE_STEP=vendor_binding
"${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" \
  --vendor-path "$VENDOR_PATH" --output "$VENDOR_BINDING" \
  --artifact-root "$ART_DIR" || {
    echo "[campaign_frameworks] setup failure: cannot bind the pinned Reference tree" >&2
    exit 2
  }

ACTIVE_STEP=run_start_emission
emit_event --new-log --string event run_start \
  --json-value argv '["scripts/e2e/campaign_frameworks.sh"]' \
  --string cwd "$ROOT" \
  --append-string claim_ids FLN-TRIBUNAL-CAMPAIGN-FRAMEWORKS-AND-OWNER-MATRIX-EXIST \
  --append-string invariant_ids FL-INV-01 --append-string invariant_ids FL-INV-07 \
  --append-string gate_ids W1 \
  --string parity_ledger_row not_applicable_campaign_machinery \
  --string epoch lean-v4.32.0 --string mode sound --string profile e2e \
  --string platform "$(uname -srm)" --integer thread_count 1 \
  --json-value thread_matrix '[1,8,32]' \
  --json-value host_facts "$HOST_FACTS_JSON" \
  --string seed not_applicable_deterministic_suites \
  --string cache_state "${FLN_E2E_CACHE_STATE:-uncontrolled}" \
  --string input_root "$INPUT_ROOT" \
  --string vendor_binding vendor-binding.json \
  --producer-binding-root "$ROOT" "${GOVERNED_ARGS[@]}" \
  --json-value budgets "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$TIMEOUT_MS,\"kill_grace_ms\":$GRACE_MS}"

SUITES=(
  campaign_owner_matrix
  mutation_kill_ledger_model
  fuzz_seed_replay
  fault_boundary_registry
  shrink_signature_preservation
  no_mock_attestation
  productive_thread_matrix
)
EXPECTED_TESTS=61 # 16 + 9 + 7 + 9 + 7 + 6 + 7, conserved in its own step

total_tests=0
for suite in "${SUITES[@]}"; do
  step="suite_${suite}"
  GLOBAL_BEFORE="$(hash_governed)"
  supervise "$step" cargo test -p fln-conformance --test "$suite"
  inspect_supervisor "$step"
  GLOBAL_AFTER="$(hash_governed)"
  if [ "$LAST_RC" -ne 0 ] || ! grep -q "test result: ok" "$LAST_OUT"; then
    record_failure "$step" "suite $suite green (exit 0, 'test result: ok')"
    set_final fail suite_red 1
    finalize 1
  fi
  suite_tests="$(grep -cE '^test .* \.\.\. ok$' "$LAST_OUT" || true)"
  total_tests=$((total_tests + suite_tests))
  record_step "$step" "suite $suite exits 0 with 'test result: ok'" \
    "exit 0, $suite_tests tests ok" "$step.out" \
    pass 0 0 "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
done

# ---- conservation -----------------------------------------------------------------------
step=conservation
GLOBAL_BEFORE="$(hash_governed)"
supervise "$step" "${PYTHON[@]}" -c \
  "import sys; sys.exit(0 if $total_tests == $EXPECTED_TESTS else 1)"
inspect_supervisor "$step"
GLOBAL_AFTER="$(hash_governed)"
if [ "$LAST_RC" -ne 0 ]; then
  record_failure "$step" "test conservation is exactly $EXPECTED_TESTS (measured $total_tests)"
  set_final fail conservation_mismatch 1
  finalize 1
fi
record_step "$step" "test conservation is exactly $EXPECTED_TESTS" \
  "$total_tests tests accounted" "$step.out" \
  pass 0 0 "$GLOBAL_BEFORE" "$GLOBAL_AFTER"

# ---- the planted duplicate row is refused ----------------------------------------------
step=planted_duplicate_row_refused
GLOBAL_BEFORE="$(hash_governed)"
cp "$MATRIX" "$ART_DIR/CAMPAIGN_OWNER_MATRIX.pristine"
printf 'adapter grammar-source | mutation  | fln-7li          | registered |\n' >> "$MATRIX"
supervise "$step" --semantic-failure-exit 101 \
  cargo test -p fln-conformance --test campaign_owner_matrix
inspect_supervisor "$step"
restore_matrix
GLOBAL_AFTER="$(hash_governed)"
if [ "$LAST_CLASSIFICATION" != "fail" ]; then
  record_failure "$step" "the owner-matrix suite refuses the planted duplicate (supervisor classification fail)"
  set_final fail planted_tamper_not_refused 1
  finalize 1
fi
# The tamper must be named, and libtest prints failures to stderr under --nocapture —
# grep BOTH captures (the house law for expected-fail cargo steps).
if ! grep -qE "already declared|adapter rows are the bead's own mapping" "$LAST_OUT" \
    && ! grep -qE "already declared|adapter rows are the bead's own mapping" "$LAST_ERR"; then
  record_failure "$step" "the refusal names the tamper (count conservation or the duplicate finding)"
  set_final fail planted_reason_wrong 1
  finalize 1
fi
record_step "$step" "the planted duplicate is refused with the tamper named" \
  "classification fail, child exit $LAST_CHILD_EXIT, tamper named" "$step.out" \
  fail 1 101 "$GLOBAL_BEFORE" "$GLOBAL_AFTER"

# ---- pristine recovery ------------------------------------------------------------------
step=pristine_recovery
GLOBAL_BEFORE="$(hash_governed)"
# ONE guardian per step (a second supervise under the same step id clashes on the
# launch-ready identity): the byte-exact check and the green suite run in one child,
# cmp's refusal surfacing as the child's exit before cargo starts.
# shellcheck disable=SC2016
supervise "$step" bash -c \
  'cmp -s "$1" "$2" && exec cargo test -p fln-conformance --test campaign_owner_matrix' \
  _ "$ART_DIR/CAMPAIGN_OWNER_MATRIX.pristine" "$MATRIX"
inspect_supervisor "$step"
GLOBAL_AFTER="$(hash_governed)"
if [ "$LAST_RC" -ne 0 ] || ! grep -q "test result: ok" "$LAST_OUT"; then
  record_failure "$step" "matrix byte-identical (cmp) and suite green after restore"
  set_final fail recovery_not_pristine 1
  finalize 1
fi
record_step "$step" "matrix byte-identical (cmp) and suite green after restore" \
  "cmp clean, exit 0, sha $(sha256sum "$MATRIX" | cut -d' ' -f1)" "$step.out" \
  pass 0 0 "$GLOBAL_BEFORE" "$GLOBAL_AFTER"

note "OK: $total_tests tests across ${#SUITES[@]} suites; plant-and-recover green"
set_final pass complete 0
finalize 0
