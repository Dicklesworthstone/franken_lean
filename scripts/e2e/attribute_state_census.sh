#!/usr/bin/env bash
# attribute_state_census.sh — shared E2E scenario for the pinned attribute-state
# census (bead fln-attribute-state-census-h14), fln.e2e/2.
#
# Real-path, no-mock: the checked-in extraction path runs offline against the
# pinned vendor tree (regenerate to a lane-local output, byte-compared against
# the committed census), the guard suite runs green, then two planted defects
# — a dropped marquee row and a malformed row — are each refused by the
# generator's own check and the guard suite, before a byte-exact pristine
# recovery. scripts/evidence.py independently validates the run record before
# the bundle completes.

set -Eeuo pipefail

PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  echo "[attribute_state_census] setup failure: python3 is required" >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
HOSTILE_PYTHON_CONFIGURATION=()
while IFS= read -r environment_name; do
  [[ "$environment_name" == PYTHON* ]] \
    && HOSTILE_PYTHON_CONFIGURATION+=("$environment_name")
done < <(compgen -e | LC_ALL=C sort)
if ((${#HOSTILE_PYTHON_CONFIGURATION[@]} > 0)); then
  printf '[attribute_state_census] setup failure: sealed_interpreter_hostile_environment names=%s\n' \
    "$(IFS=,; printf '%s' "${HOSTILE_PYTHON_CONFIGURATION[*]}")" >&2
  exit 2
fi
command -v setsid >/dev/null 2>&1 || {
  echo "[attribute_state_census] setup failure: setsid is required" >&2
  exit 2
}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
EVIDENCE="$ROOT/scripts/evidence.py"
SCHEMA="fln.e2e/2"
BEAD="fln-attribute-state-census-h14"
SCENARIO="attribute_state_census"
RUN_ID="attribute-state-census-$(date -u +%Y%m%dT%H%M%SZ)-$$"
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
    echo "[attribute_state_census] setup failure: FLN_E2E_READY_WAIT_MS must be numeric" >&2
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
  contracts/ATTRIBUTE_STATE_CENSUS.txt
  crates/fln-conformance/tests/attribute_state_census.rs
  scripts/extract/gen_attribute_state_census.py
  scripts/e2e/attribute_state_census.sh scripts/evidence.py scripts/check.sh
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
  echo "[attribute_state_census] setup failure: cannot hash governed inputs" >&2
  exit 2
fi

note() {
  printf '[attribute_state_census] %s\n' "$*" | tee -a "$HUMAN" >&2
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

CENSUS="$ROOT/contracts/ATTRIBUTE_STATE_CENSUS.txt"

restore_census() {
  if [ -f "$ART_DIR/ATTRIBUTE_STATE_CENSUS.pristine" ]; then
    cp "$ART_DIR/ATTRIBUTE_STATE_CENSUS.pristine" "$CENSUS" 2>/dev/null || true
  fi
}

finalize() {
  local exit_code="$1"
  stop_active_runner TERM || true
  restore_census
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
    printf '[attribute_state_census] INTERNAL FAULT: incomplete bundle %s\n' "$ART_DIR" >&2
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
  echo "[attribute_state_census] evidence directory already claimed: $ART_DIR" >&2
  exit 2
fi
: > "$HUMAN"

ACTIVE_STEP=vendor_binding
"${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" \
  --vendor-path "$VENDOR_PATH" --output "$VENDOR_BINDING" \
  --artifact-root "$ART_DIR" || {
    echo "[attribute_state_census] setup failure: cannot bind the pinned Reference tree" >&2
    exit 2
  }

ACTIVE_STEP=run_start_emission
emit_event --new-log --string event run_start \
  --json-value argv '["scripts/e2e/attribute_state_census.sh"]' \
  --string cwd "$ROOT" \
  --append-string claim_ids FLN-ATTRIBUTE-STATE-CENSUS-IS-MECHANICAL-AND-FROZEN \
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

GEN="scripts/extract/gen_attribute_state_census.py"

# ---- leg 1: the checked-in extraction path regenerates the committed census byte-for-byte
step=regenerate_and_check
GLOBAL_BEFORE="$(hash_governed)"
supervise "$step" "${PYTHON[@]}" "$ROOT/$GEN" --output "$ART_DIR/regenerated.txt"
inspect_supervisor "$step"
LAST_META_FIRST="$LAST_META"
supervise "${step}_diff" cmp -s "$ART_DIR/regenerated.txt" "$CENSUS"
inspect_supervisor "${step}_diff"
GLOBAL_AFTER="$(hash_governed)"
if [ "$LAST_RC" -ne 0 ]; then
  record_failure "$step" "the offline extraction reproduces the committed census byte-for-byte"
  set_final fail regeneration_drift 1
  finalize 1
fi
LAST_META="$LAST_META_FIRST"
record_step "$step" "offline extraction reproduces the committed census byte-for-byte"   "regenerated == committed (cmp clean)" "$step.out"   pass 0 0 "$GLOBAL_BEFORE" "$GLOBAL_AFTER"

# ---- leg 2: the guard suite runs green
step=guard_suite
GLOBAL_BEFORE="$(hash_governed)"
supervise "$step" cargo test -p fln-conformance --test attribute_state_census
inspect_supervisor "$step"
GLOBAL_AFTER="$(hash_governed)"
if [ "$LAST_RC" -ne 0 ] || ! grep -q "test result: ok" "$LAST_OUT"; then
  record_failure "$step" "the census guard suite is green"
  set_final fail guard_red 1
  finalize 1
fi
record_step "$step" "the census guard suite is green"   "exit 0, 'test result: ok'" "$step.out"   pass 0 0 "$GLOBAL_BEFORE" "$GLOBAL_AFTER"

# ---- leg 3: a planted dropped marquee row is refused by the generator's own check
step=pin_drift_refused
GLOBAL_BEFORE="$(hash_governed)"
cp "$CENSUS" "$ART_DIR/ATTRIBUTE_STATE_CENSUS.pristine"
"${PYTHON[@]}" - "$CENSUS" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text(encoding="utf-8")
lines = [line for line in text.splitlines() if not line.startswith("row=attr-simp-simp ")]
path.write_text("\n".join(lines) + "\n", encoding="utf-8")
PY
supervise "$step" --semantic-failure-exit 1 "${PYTHON[@]}" "$ROOT/$GEN" --check
inspect_supervisor "$step"
restore_census
GLOBAL_AFTER="$(hash_governed)"
if [ "$LAST_CLASSIFICATION" != "fail" ]; then
  record_failure "$step" "the generator's --check refuses the census with the simp row dropped"
  set_final fail drift_not_refused 1
  finalize 1
fi
record_step "$step" "a dropped marquee row is refused by the generator's own check"   "classification fail (drifted from pinned sources)" "$step.err"   fail 1 1 "$GLOBAL_BEFORE" "$GLOBAL_AFTER"

# ---- leg 4: a malformed row is refused by the guard suite
step=malformed_row_refused
GLOBAL_BEFORE="$(hash_governed)"
printf 'row=attr-malformed-x epoch=x\n' >> "$CENSUS"
supervise "$step" --semantic-failure-exit 101 cargo test -p fln-conformance --test attribute_state_census
inspect_supervisor "$step"
restore_census
GLOBAL_AFTER="$(hash_governed)"
if [ "$LAST_CLASSIFICATION" != "fail" ]; then
  record_failure "$step" "the guard suite refuses a census row missing its fields"
  set_final fail malformed_not_refused 1
  finalize 1
fi
# libtest prints failures to stderr under --nocapture; grep BOTH captures (the house law).
if ! grep -q "missing field\|not key=value" "$LAST_OUT" && ! grep -q "missing field\|not key=value" "$LAST_ERR"; then
  record_failure "$step" "the guard's refusal names the malformed row"
  set_final fail malformed_reason_wrong 1
  finalize 1
fi
record_step "$step" "a malformed row is refused with the shape named"   "classification fail, refusal names the malformed shape" "$step.err"   fail 1 101 "$GLOBAL_BEFORE" "$GLOBAL_AFTER"

# ---- leg 4b: a source beyond the byte budget is a typed refusal with exact usage
step=budget_refusal
GLOBAL_BEFORE="$(hash_governed)"
SCRATCH="$ART_DIR/scratch-vendor"
mkdir -p "$SCRATCH/src/Lean"
"${PYTHON[@]}" - "$SCRATCH/src/Lean/Big.lean" <<'PY'
import pathlib, sys
# 8 bytes per pad line; 600k lines is 4.8MB, over the 4MB input budget.
pathlib.Path(sys.argv[1]).write_text("def filler := 1\n" + "-- pad\n" * 600_000, encoding="utf-8")
PY
supervise "$step" --semantic-failure-exit 2 "${PYTHON[@]}" "$ROOT/$GEN" \
  --vendor-path "$SCRATCH" --output "$ART_DIR/budget-out.txt"
inspect_supervisor "$step"
GLOBAL_AFTER="$(hash_governed)"
if [ "$LAST_CLASSIFICATION" != "fail" ]; then
  record_failure "$step" "an oversized source is a typed budget refusal"
  set_final fail budget_not_enforced 1
  finalize 1
fi
if ! grep -q "budget refusal" "$LAST_ERR" && ! grep -q "budget refusal" "$LAST_OUT"; then
  record_failure "$step" "the refusal names the budget with exact usage"
  set_final fail budget_reason_wrong 1
  finalize 1
fi
record_step "$step" "a source beyond the byte budget is refused with exact usage" \
  "classification fail, budget refusal with the byte count" "$step.err" \
  fail 1 2 "$GLOBAL_BEFORE" "$GLOBAL_AFTER"

# ---- leg 5: pristine recovery — byte-exact, verified, and the generator's check green
step=pristine_recovery
GLOBAL_BEFORE="$(hash_governed)"
# shellcheck disable=SC2016
supervise "$step" bash -c \
  'cmp -s "$1" "$2" && shift 2 && exec "$@" --check' \
  _ "$ART_DIR/ATTRIBUTE_STATE_CENSUS.pristine" "$CENSUS" "${PYTHON[@]}" "$ROOT/$GEN"
inspect_supervisor "$step"
GLOBAL_AFTER="$(hash_governed)"
if [ "$LAST_RC" -ne 0 ]; then
  record_failure "$step" "the census is byte-identical to its pre-plant bytes and --check passes"
  set_final fail recovery_not_pristine 1
  finalize 1
fi
if ! grep -q "attribute-census: OK" "$LAST_OUT"; then
  record_failure "$step" "the generator's --check passes after the byte-exact restore"
  set_final fail recovery_check_red 1
  finalize 1
fi
record_step "$step" "census byte-identical and the generator's check passes"   "cmp clean, --check OK, sha $(sha256sum "$CENSUS" | cut -d' ' -f1)" "$step.out"   pass 0 0 "$GLOBAL_BEFORE" "$GLOBAL_AFTER"

note "OK: regeneration byte-identical; drift and malformed plants refused; recovery pristine"
set_final pass complete 0
finalize 0
