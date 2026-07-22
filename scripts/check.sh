#!/usr/bin/env bash
# scripts/check.sh — the single FrankenLean quality gate.
#
# Stages are append-only obligations: evidence harness self-test, fmt, check, clippy,
# tests, structural policy, exact Reference tree, and UBS.  Each command runs under a
# bounded supervisor that drains stdout/stderr to EOF, preserves useful head+tail
# captures, applies a monotonic timeout and total-output budget, and cancels the whole
# child process group.  The published fln.check/2 NDJSON has exactly one final terminal
# record plus a write-once SHA-256 artifact manifest.
#
# Exit taxonomy: 0 pass; 1 stage failure; 2 setup/evidence/internal fault;
# 3 resource exhaustion or timeout (inconclusive); 129/130/143 HUP/INT/TERM cancellation.

set -Eeuo pipefail

FINALIZER_PROBE=0
case "${1:-}" in
  --help|-h)
    sed -n '2,17p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
    exit 0
    ;;
  --self-test|"") ;;
  --finalizer-probe) FINALIZER_PROBE=1 ;;
  *) echo "unknown argument: $1 (see --help)" >&2; exit 2 ;;
esac

command -v python3 >/dev/null 2>&1 || {
  echo "[check] setup failure: python3 is required by the evidence harness" >&2
  exit 2
}
command -v setsid >/dev/null 2>&1 || {
  echo "[check] setup failure: setsid is required by the evidence finalizer" >&2
  exit 2
}

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO"
EVIDENCE="$REPO/scripts/evidence.py"
SCHEMA="fln.check/2"
SCENARIO="quality_gate"
BEAD="franken_lean-rur"
RUN_ID="check-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_CHECK_ART_ROOT:-$REPO/target/check}"
ART_DIR="${FLN_CHECK_ART_DIR:-$ART_ROOT/$RUN_ID}"
NDJSON="$ART_DIR/run.ndjson"
HUMAN="$ART_DIR/human.log"
CAPTURE_BYTES="${FLN_CHECK_CAPTURE_BYTES:-262144}"
OUTPUT_BUDGET_BYTES="${FLN_CHECK_OUTPUT_BUDGET_BYTES:-67108864}"
STAGE_TIMEOUT_MS="${FLN_CHECK_STAGE_TIMEOUT_MS:-1200000}"
KILL_GRACE_MS="${FLN_CHECK_KILL_GRACE_MS:-2000}"
READY_WAIT_MS="${FLN_CHECK_READY_WAIT_MS:-30000}"
PLANT="${FLN_CHECK_PLANT:-}"
FINALIZER_TEST_POINT="${FLN_FINALIZER_TEST_POINT:-}"
if [ "$FINALIZER_PROBE" -eq 1 ]; then
  case "$FINALIZER_TEST_POINT" in
    spawn_bind|active_wait|helper_failure|post_decision) ;;
    *) echo "invalid finalizer probe point: $FINALIZER_TEST_POINT" >&2; exit 2 ;;
  esac
  PROFILE=finalizer-self-test
elif [ -n "${FLN_CHECK_PROFILE:-}" ]; then
  PROFILE="$FLN_CHECK_PROFILE"
elif [ "${1:-}" = --self-test ]; then
  PROFILE=self-test-driver
elif [ -n "$PLANT" ]; then
  PROFILE=self-test-plant
elif [ "${CI:-}" = true ]; then
  PROFILE=ci
else
  PROFILE=local
fi
THREAD_COUNT="${FLN_CHECK_THREAD_COUNT:-1}"
SEED="${FLN_CHECK_SEED:-none}"
CACHE_STATE="${FLN_CHECK_CACHE_STATE:-uncontrolled}"
START_NS="$(python3 -c 'import time; print(time.monotonic_ns())')"
SEQ=0
ACTIVE_STAGE="setup"
ACTIVE_RUNNER_PID=""
ACTIVE_RUNNER_START_TICKS=""
ACTIVE_READINESS=""
ACTIVE_RUNNER_PROTOCOL=""
ACTIVE_RUNNER_ART_DIR=""
SPAWNING=0
PENDING_SIGNAL=""
PENDING_SIGNAL_EXIT=0
FINAL_SET=0
FINAL_VERDICT="internal_fault"
FINAL_REASON="uncommitted_exit"
FINAL_EXIT=2
TERMINAL_EMITTED=0
FINALIZING=0
FINALIZER_TRANSITION=0
FINALIZER_PID=""
FINALIZER_START_TICKS=""
FINALIZER_CLEANUP_UNPROVEN=0
FINALIZER_WAIT_UNSAFE=0
PROCESS_TREE_CLEANUP_UNPROVEN=0
FINALIZATION_SIGNAL=""
FINALIZATION_SIGNAL_EXIT=0
FINALIZATION_SIGNAL_GENERATION=0
FINALIZATION_DECISION="$ART_DIR/bundle.decision"
FINALIZER_TEST_CONTROL="$ART_DIR.control"
FINALIZER_TEST_READY="$FINALIZER_TEST_CONTROL/ready"
FINALIZER_TEST_RELEASE="$FINALIZER_TEST_CONTROL/release"
FINALIZER_TEST_ACK="$FINALIZER_TEST_CONTROL/signal-ack"
FINAL_ROOT_FILE="$ART_DIR/final-root.txt"
EVENT_COMMAND=()
INPUT_PATHS=(
  Cargo.toml Cargo.lock SUITE.lock rust-toolchain.toml ci crates tools
  vendor/NOTICE
  scripts/check.sh scripts/evidence.py scripts/verify_vendor_tree.sh
  scripts/e2e/structure_gate.sh scripts/e2e/closure_audit.sh
  scripts/e2e/structural_gate.sh scripts/e2e/core_observables.sh
  scripts/e2e/hash_identity.sh scripts/e2e/diag_goldens.sh
  scripts/e2e/env_snapshots.sh scripts/e2e/bignum_vectors.sh
  scripts/extract/gen_core_fixtures.sh scripts/extract/gen_core_fixtures.lean
  scripts/extract/convert_blake3_vectors.py scripts/extract/gen_bignum_vectors.py
  scripts/extract/gen_abi_contract.py scripts/extract/gen_olean_contract.py
  scripts/extract/gen_extern_census.sh scripts/extract/gen_extern_census.lean
  scripts/e2e/contract_drift.sh
  contracts ABI_CONTRACT.md OLEAN_CONTRACT.md rustfmt.toml
  scripts/tribunal/gen_epoch_manifest.sh scripts/tribunal/ref_vs_ref.sh
  tribunal
  .github/workflows/ci.yml
)
HASH_ARGS=()
GOVERNED_ARGS=()
for input_path in "${INPUT_PATHS[@]}"; do
  HASH_ARGS+=(--path "$input_path")
  GOVERNED_ARGS+=(--governed-path "$input_path")
done

UBS_SCOPE="${FLN_UBS_SCOPE:-changed}"
[ "${CI:-}" = true ] && UBS_SCOPE="${FLN_UBS_SCOPE:-all-tracked}"
UBS_INVENTORY="$ART_DIR/ubs-inventory.json"
VENDOR_PATH="vendor/lean4-src"
VENDOR_BINDING="$ART_DIR/vendor-binding.json"
GOVERNED_ROOT="$REPO"
HASH_CONTEXT_ARGS=(--inventory "$UBS_INVENTORY" --vendor-path "$VENDOR_PATH")
BUNDLE_CONTEXT_ARGS=(--inventory "$UBS_INVENTORY" --vendor-path "$VENDOR_PATH")
UBS_INVENTORY_BINDING=ubs-inventory.json
VENDOR_BINDING_BINDING=vendor-binding.json
mkdir -p "$(dirname "$ART_DIR")"
if [ -e "$ART_DIR" ] || [ -L "$ART_DIR" ]; then
  echo "[check] setup failure: refusing reused evidence directory: $ART_DIR" >&2
  exit 2
fi
mkdir "$ART_DIR"
if [ "$FINALIZER_PROBE" -eq 1 ]; then
  if [ -e "$FINALIZER_TEST_CONTROL" ] || [ -L "$FINALIZER_TEST_CONTROL" ]; then
    echo "[check] setup failure: refusing reused probe control directory" >&2
    exit 2
  fi
  mkdir "$FINALIZER_TEST_CONTROL"
  printf 'finalizer-probe\n' > "$ART_DIR/probe-input"
  GOVERNED_ROOT="$ART_DIR"
  HASH_ARGS=(--path probe-input)
  GOVERNED_ARGS=(--governed-path probe-input)
  HASH_CONTEXT_ARGS=()
  BUNDLE_CONTEXT_ARGS=()
  UBS_INVENTORY_BINDING=not_applicable_finalizer_self_test
  VENDOR_BINDING_BINDING=not_applicable_finalizer_self_test
else
  python3 "$EVIDENCE" ubs-inventory --root "$REPO" --scope "$UBS_SCOPE" \
    --output "$UBS_INVENTORY" --artifact-root "$ART_DIR" || {
      echo "[check] setup failure: cannot inventory UBS inputs" >&2
      exit 2
    }
  python3 "$EVIDENCE" vendor-binding --root "$REPO" --vendor-path "$VENDOR_PATH" \
    --output "$VENDOR_BINDING" --artifact-root "$ART_DIR" || {
      echo "[check] setup failure: cannot verify the pinned Reference tree" >&2
      exit 2
    }
fi
INPUT_ROOT="$(python3 "$EVIDENCE" hash-tree --root "$GOVERNED_ROOT" \
  "${HASH_ARGS[@]}" "${HASH_CONTEXT_ARGS[@]}")" || {
  echo "[check] setup failure: cannot hash governed inputs" >&2
  exit 2
}
HOST_FACTS_JSON="$(python3 - <<'PY'
import json, platform
print(json.dumps({
    "machine": platform.machine(),
    "python": platform.python_version(),
    "release": platform.release(),
    "system": platform.system(),
}, sort_keys=True, separators=(",", ":")))
PY
)"

RUN_ARGV_JSON="$(python3 - "${BASH_SOURCE[0]}" "${1:-}" <<'PY'
import json, sys
argv = [sys.argv[1]]
if sys.argv[2]:
    argv.append(sys.argv[2])
print(json.dumps(argv, separators=(",", ":")))
PY
)"

build_event_command() {
  local sequence="$SEQ"
  SEQ=$((SEQ + 1))
  EVENT_COMMAND=(python3 "$EVIDENCE" emit --file "$NDJSON" --artifact-root "$ART_DIR" \
    --string schema "$SCHEMA" \
    --string run_id "$RUN_ID" \
    --string bead "$BEAD" \
    --string scenario "$SCENARIO" \
    --integer sequence "$sequence" \
    --integer monotonic_ns "$(python3 -c 'import time; print(time.monotonic_ns())')" \
    --string wall_time_utc "$(date -u -Is)" \
    "$@")
}

emit_event() {
  build_event_command "$@"
  "${EVENT_COMMAND[@]}"
}

note() {
  printf '[check] %s\n' "$*" | tee -a "$HUMAN" >&2
}

set_final() {
  FINAL_SET=1
  FINAL_VERDICT="$1"
  FINAL_REASON="$2"
  FINAL_EXIT="$3"
}

mark_process_tree_cleanup_unproven() {
  PROCESS_TREE_CLEANUP_UNPROVEN=1
  trap '' HUP INT TERM
  set_final internal_fault process_tree_cleanup_unproven 2
}

# shellcheck disable=SC2317
finalizer_test_publish() {
  local path="$1" payload="$2" noclobber_was_set=0
  [ "$FINALIZER_PROBE" -eq 1 ] || return 0
  case $- in *C*) noclobber_was_set=1 ;; esac
  set -o noclobber
  printf '%s\n' "$payload" 2>/dev/null > "$path" || {
    [ "$noclobber_was_set" -eq 1 ] || set +o noclobber
    return 1
  }
  [ "$noclobber_was_set" -eq 1 ] || set +o noclobber
}

# shellcheck disable=SC2317
finalizer_test_checkpoint() {
  local point="$1" deadline
  [ "$FINALIZER_PROBE" -eq 1 ] || return 0
  [ "$FINALIZER_TEST_POINT" = "$point" ] || return 0
  finalizer_test_publish "$FINALIZER_TEST_READY" \
    "${FINALIZER_PID:-0} ${FINALIZER_START_TICKS:-0}" || return 1
  deadline=$((SECONDS + 120))
  while [ ! -s "$FINALIZER_TEST_RELEASE" ]; do
    if [ -n "$FINALIZATION_SIGNAL" ] \
        || [ "$PROCESS_TREE_CLEANUP_UNPROVEN" -ne 0 ]; then
      return 0
    fi
    [ "$SECONDS" -lt "$deadline" ] || return 1
    :
  done
}

# Called from the EXIT-trap finalizer.
# shellcheck disable=SC2317
build_terminal_command() {
  local final_root="$1" first_divergence=none
  if [ "$FINAL_VERDICT" != pass ]; then first_divergence="$FINAL_REASON"; fi
  build_event_command \
    --string event run_end \
    --string verdict "$FINAL_VERDICT" \
    --string reason_code "$FINAL_REASON" \
    --integer process_exit "$FINAL_EXIT" \
    --string active_stage "$ACTIVE_STAGE" \
    --integer duration_ns "$(( $(python3 -c 'import time; print(time.monotonic_ns())') - START_NS ))" \
    --string cleanup_status retained_by_policy \
    --string final_state "$final_root" \
    --string logical_root "$final_root" \
    --string receipt_root not_applicable_structural_gate \
    --string first_divergence "$first_divergence" \
    --string evidence_manifest manifest.json \
    --string bundle_commit bundle.complete.json \
    --string evidence_state pending_bundle_commit
}

# A targeted signal is forwarded only after the nested supervisor has installed
# its handlers and published the exact guardian/supervisor/child binding.
# shellcheck disable=SC2317
bounded_readiness_wait() {
  local pid="$1" ready_path="$2" limit_ms="$3" state
  local ticks=$(( (limit_ms + 19) / 20 )) index
  for ((index = 0; index < ticks; index += 1)); do
    if [ -s "$ready_path" ]; then return 0; fi
    if [ ! -r "/proc/$pid/stat" ]; then return 1; fi
    state="$(awk '{print $3}' "/proc/$pid/stat" 2>/dev/null || printf X)"
    if [ "$state" = Z ]; then return 1; fi
    sleep 0.02
  done
  return 1
}

# The launch gate guarantees that this direct child has not forked yet.
terminate_unreleased_runner() {
  local pid="$1"
  if ! setsid -- python3 "$EVIDENCE" kill-direct-child --pid "$pid" \
      --expected-parent-pid "$$" --wait-ms 5000; then
    return 1
  fi
  wait "$pid" 2>/dev/null || true
}

release_guardian_launch() {
  local stage="$1" pid="$2" ticks="$3" ready="$4" output="$5"
  for _ in 1 2; do
    if setsid -- python3 "$EVIDENCE" release-process-launch --ready "$ready" \
      --output "$output" --artifact-root "$ART_DIR" --stage-id "$stage" \
      --pid "$pid" --expected-start-ticks "$ticks" \
      --expected-parent-pid "$$" --wait-ms "$READY_WAIT_MS"; then
      return 0
    fi
  done
  return 1
}

# Invoked from signal handling; bounded so evidence publication cannot hang forever.
# shellcheck disable=SC2317
stop_active_runner() {
  local name="$1" pid="$ACTIVE_RUNNER_PID" state cleanup_rc=0 forced=0 runner_rc=0
  local protocol="$ACTIVE_RUNNER_PROTOCOL" runner_art_dir="$ACTIVE_RUNNER_ART_DIR"
  [ -n "$pid" ] || return 0
  if bounded_readiness_wait "$pid" "$ACTIVE_READINESS" "$READY_WAIT_MS" \
      && [ -n "$ACTIVE_RUNNER_START_TICKS" ]; then
    python3 "$EVIDENCE" signal-bound-process --pid "$pid" \
      --expected-start-ticks "$ACTIVE_RUNNER_START_TICKS" --signal "$name" \
      >/dev/null 2>&1 || true
  fi
  for _ in $(seq 1 500); do
    if [ ! -r "/proc/$pid/stat" ]; then break; fi
    state="$(awk '{print $3}' "/proc/$pid/stat" 2>/dev/null || printf X)"
    [ "$state" = Z ] && break
    sleep 0.02
  done
  if [ -r "/proc/$pid/stat" ]; then
    state="$(awk '{print $3}' "/proc/$pid/stat" 2>/dev/null || printf X)"
    if [ "$state" != Z ]; then
      if [ -f "$ACTIVE_READINESS" ]; then
        if ! python3 "$EVIDENCE" emergency-kill --readiness "$ACTIVE_READINESS" \
          --expected-wrapper-pid "$pid" --expected-stage-id "$ACTIVE_STAGE" \
          >/dev/null 2>&1; then
          cleanup_rc=1
        else
          forced=1
        fi
      else
        cleanup_rc=1
      fi
    fi
  fi
  if [ "$cleanup_rc" -ne 0 ]; then
    ACTIVE_RUNNER_PID=""
    ACTIVE_RUNNER_START_TICKS=""
    ACTIVE_READINESS=""
    ACTIVE_RUNNER_PROTOCOL=""
    ACTIVE_RUNNER_ART_DIR=""
    return "$cleanup_rc"
  fi
  wait "$pid" 2>/dev/null || runner_rc=$?
  if [ "$forced" -eq 0 ]; then
    case "$protocol" in
      guardian)
        case "$runner_rc" in 0|1|3|4) ;; *) cleanup_rc=1 ;; esac
        ;;
      nested-check)
        case "$name" in HUP|INT|TERM) ;; *) cleanup_rc=1 ;; esac
        if [ "$cleanup_rc" -eq 0 ] && {
          [ "$runner_rc" -ne 4 ] \
            || [ -z "$runner_art_dir" ] \
            || ! python3 "$EVIDENCE" validate-run \
              --file "$runner_art_dir/run.ndjson" --schema "$SCHEMA" \
              --expected-verdict cancelled --artifact-root "$ART_DIR" \
              >/dev/null 2>&1 \
            || ! python3 "$EVIDENCE" validate-bundle --art-dir "$runner_art_dir" \
              --manifest "$runner_art_dir/manifest.json" \
              --digest "$runner_art_dir/manifest.digest" \
              --commit "$runner_art_dir/bundle.complete.json" \
              --artifact-root "$runner_art_dir" >/dev/null 2>&1;
        }; then
          cleanup_rc=1
        fi
        ;;
      *) cleanup_rc=1 ;;
    esac
  fi
  ACTIVE_RUNNER_PID=""
  ACTIVE_RUNNER_START_TICKS=""
  ACTIVE_READINESS=""
  ACTIVE_RUNNER_PROTOCOL=""
  ACTIVE_RUNNER_ART_DIR=""
  return "$cleanup_rc"
}

# Invoked indirectly by trap.
# shellcheck disable=SC2317
on_signal() {
  local name="$1" exit_code="$2"
  if [ "$FINALIZER_TRANSITION" -eq 1 ]; then
    on_finalizer_signal "$name" "$exit_code"
    return 0
  fi
  trap '' HUP INT TERM
  if [ "$SPAWNING" -eq 1 ]; then
    PENDING_SIGNAL="$name"
    PENDING_SIGNAL_EXIT="$exit_code"
    trap 'on_signal HUP 129' HUP
    trap 'on_signal INT 130' INT
    trap 'on_signal TERM 143' TERM
    return 0
  fi
  if [ -n "$ACTIVE_RUNNER_PID" ]; then
    if ! stop_active_runner "$name"; then
      mark_process_tree_cleanup_unproven
      exit 2
    fi
  fi
  set_final cancelled "signal_$name" "$exit_code"
  exit "$exit_code"
}

# shellcheck disable=SC2317
contain_bound_finalizer() {
  if [ "$FINALIZER_PROBE" -eq 1 ] \
      && [ "$FINALIZER_TEST_POINT" = helper_failure ] \
      && [ -n "$FINALIZATION_SIGNAL" ]; then
    FINALIZER_CLEANUP_UNPROVEN=1
    FINALIZER_WAIT_UNSAFE=1
    mark_process_tree_cleanup_unproven
    return 1
  fi
  if [ -z "$FINALIZER_PID" ] || [ -z "$FINALIZER_START_TICKS" ]; then
    FINALIZER_CLEANUP_UNPROVEN=1
    FINALIZER_WAIT_UNSAFE=1
    mark_process_tree_cleanup_unproven
    return 1
  fi
  if ! setsid -- python3 "$EVIDENCE" kill-bound-group --pid "$FINALIZER_PID" \
      --expected-start-ticks "$FINALIZER_START_TICKS" \
      --expected-parent-pid "$$" >/dev/null 2>&1; then
    FINALIZER_CLEANUP_UNPROVEN=1
    FINALIZER_WAIT_UNSAFE=1
    mark_process_tree_cleanup_unproven
    return 1
  fi
  if ! setsid -- python3 "$EVIDENCE" assert-process-group-empty \
      --pgid "$FINALIZER_PID" --wait-ms 2000 >/dev/null 2>&1; then
    FINALIZER_CLEANUP_UNPROVEN=1
    FINALIZER_WAIT_UNSAFE=1
    mark_process_tree_cleanup_unproven
    return 1
  fi
  return 0
}

# Invoked only while the EXIT finalizer is active. A signal before the shared bundle
# decision interrupts the current publication command and leaves it uncommitted.
# shellcheck disable=SC2317
on_finalizer_signal() {
  local name="$1" exit_code="$2" noclobber_was_set=0
  trap '' HUP INT TERM
  if [ "$PROCESS_TREE_CLEANUP_UNPROVEN" -ne 0 ]; then return 0; fi
  case $- in *C*) noclobber_was_set=1 ;; esac
  set -o noclobber
  : 2>/dev/null > "$FINALIZATION_DECISION" || true
  [ "$noclobber_was_set" -eq 1 ] || set +o noclobber
  FINALIZATION_SIGNAL_GENERATION=$((FINALIZATION_SIGNAL_GENERATION + 1))
  if [ -s "$FINALIZATION_DECISION" ]; then
    finalizer_test_publish "$FINALIZER_TEST_ACK" "$name" || true
    trap '' HUP INT TERM
    return 0
  fi
  if [ -z "$FINALIZATION_SIGNAL" ]; then
    FINALIZATION_SIGNAL="$name"
    FINALIZATION_SIGNAL_EXIT="$exit_code"
  fi
  if [ -n "$FINALIZER_PID" ]; then
    if [ -n "$FINALIZER_START_TICKS" ]; then
      if ! contain_bound_finalizer; then return 0; fi
    elif ! terminate_unreleased_runner "$FINALIZER_PID"; then
      FINALIZER_CLEANUP_UNPROVEN=1
      FINALIZER_WAIT_UNSAFE=1
      mark_process_tree_cleanup_unproven
      return 0
    fi
  fi
  trap 'on_finalizer_signal HUP 129' HUP
  trap 'on_finalizer_signal INT 130' INT
  trap 'on_finalizer_signal TERM 143' TERM
}

# shellcheck disable=SC2317
run_finalizer_command() {
  local rc=0 generation binding_valid=1 resume_failed=0 wait_safe=1
  [ "$PROCESS_TREE_CLEANUP_UNPROVEN" -eq 0 ] || return 2
  [ "$FINALIZER_CLEANUP_UNPROVEN" -eq 0 ] || return 2
  [ -z "$FINALIZATION_SIGNAL" ] || return 125
  if [ -s "$FINALIZATION_DECISION" ]; then trap '' HUP INT TERM; fi
  setsid -- python3 "$EVIDENCE" stopped-exec \
    --expected-parent-pid "$$" -- "$@" &
  FINALIZER_PID=$!
  if ! finalizer_test_checkpoint spawn_bind; then
    if ! terminate_unreleased_runner "$FINALIZER_PID"; then
      FINALIZER_CLEANUP_UNPROVEN=1
      FINALIZER_WAIT_UNSAFE=1
      mark_process_tree_cleanup_unproven
    fi
    FINALIZER_PID=""
    return 2
  fi
  FINALIZER_START_TICKS="$(
    setsid -- python3 "$EVIDENCE" process-start-ticks --pid "$FINALIZER_PID" \
      --expected-parent-pid "$$" --wait-ms "$READY_WAIT_MS" \
      --session-leader --stopped \
      2>/dev/null
  )" || true
  case "$FINALIZER_START_TICKS" in ''|*[!0-9]*) binding_valid=0 ;; esac
  if [ "$binding_valid" -eq 0 ]; then
    # Without the binder's start ticks, only the exact direct-child pidfd helper
    # may act. The launch gate proves this child has not forked or execed yet.
    if ! terminate_unreleased_runner "$FINALIZER_PID"; then
      FINALIZER_CLEANUP_UNPROVEN=1
      FINALIZER_WAIT_UNSAFE=1
      mark_process_tree_cleanup_unproven
    fi
    FINALIZER_PID=""
    FINALIZER_START_TICKS=""
    return 2
  fi
  # A terminal trap can interrupt Bash's command-substitution wait after the
  # isolated binder emitted a valid identity, so the canonical digits are the proof.
  if [ -z "$FINALIZATION_SIGNAL" ]; then
    if ! setsid -- python3 "$EVIDENCE" resume-bound-process \
        --pid "$FINALIZER_PID" \
        --expected-start-ticks "$FINALIZER_START_TICKS" \
        --expected-parent-pid "$$"; then
      contain_bound_finalizer || wait_safe=0
      resume_failed=1
    fi
  fi
  if [ "$resume_failed" -eq 0 ]; then
    if ! finalizer_test_checkpoint active_wait \
        || ! finalizer_test_checkpoint helper_failure; then
      contain_bound_finalizer || wait_safe=0
      resume_failed=1
    fi
  fi
  if [ -n "$FINALIZATION_SIGNAL" ] && [ -n "$FINALIZER_START_TICKS" ]; then
    contain_bound_finalizer || wait_safe=0
  fi
  if [ "$wait_safe" -eq 1 ]; then
    while true; do
      generation="$FINALIZATION_SIGNAL_GENERATION"
      wait "$FINALIZER_PID" && rc=0 || rc=$?
      if [ "$FINALIZER_WAIT_UNSAFE" -ne 0 ]; then
        rc=2
        break
      fi
      case "$rc" in
        129|130|143)
          if [ "$generation" -ne "$FINALIZATION_SIGNAL_GENERATION" ]; then
            continue
          fi
          ;;
      esac
      break
    done
  else
    rc=2
  fi
  FINALIZER_PID=""
  FINALIZER_START_TICKS=""
  if [ "$resume_failed" -ne 0 ]; then return 2; fi
  return "$rc"
}

# shellcheck disable=SC2317
abort_if_finalizer_signalled() {
  if [ "$PROCESS_TREE_CLEANUP_UNPROVEN" -ne 0 ]; then
    note "INTERNAL FAULT: process-tree cleanup was not proven"
    exit 2
  fi
  if [ "$FINALIZER_CLEANUP_UNPROVEN" -ne 0 ]; then
    note "INTERNAL FAULT: finalizer cleanup was not proven"
    exit 2
  fi
  if [ -n "$FINALIZATION_SIGNAL" ]; then
    if [ -s "$FINALIZATION_DECISION" ]; then
      return 0
    fi
    note "CANCELLED: signal_$FINALIZATION_SIGNAL won evidence bundle decision: $ART_DIR"
    exit "$FINALIZATION_SIGNAL_EXIT"
  fi
}

# Invoked indirectly by trap.
# shellcheck disable=SC2317
on_exit() {
  local observed_rc="$1" final_root="unavailable" publish_rc=0 hash_rc=0
  trap 'on_finalizer_signal HUP 129' HUP
  trap 'on_finalizer_signal INT 130' INT
  trap 'on_finalizer_signal TERM 143' TERM
  trap - EXIT
  set +e
  if [ "$FINALIZING" -ne 0 ]; then
    exit 2
  fi
  FINALIZING=1
  if [ "$FINAL_SET" -eq 0 ]; then
    if [ "$observed_rc" -eq 0 ]; then
      set_final internal_fault uncommitted_success 2
    else
      set_final internal_fault unexpected_shell_exit 2
    fi
  fi
  if [ "$FINALIZER_PROBE" -eq 1 ] && {
    [ "$FINALIZER_TEST_POINT" = active_wait ] \
      || [ "$FINALIZER_TEST_POINT" = helper_failure ];
  }; then
    run_finalizer_command python3 -c 'import time; time.sleep(60)' \
      2>/dev/null || hash_rc=$?
  else
    run_finalizer_command python3 "$EVIDENCE" hash-tree --root "$GOVERNED_ROOT" \
      "${HASH_ARGS[@]}" "${HASH_CONTEXT_ARGS[@]}" \
      --output "$FINAL_ROOT_FILE" --artifact-root "$ART_DIR" \
      2>/dev/null || hash_rc=$?
  fi
  abort_if_finalizer_signalled
  if [ "$hash_rc" -eq 0 ]; then
    IFS= read -r final_root < "$FINAL_ROOT_FILE" || hash_rc=2
  fi
  if [ "$hash_rc" -ne 0 ]; then
    final_root="unavailable"
    set_final internal_fault final_workspace_hash_unavailable 2
  elif [ "$FINAL_VERDICT" = pass ] && [ "$final_root" != "$INPUT_ROOT" ]; then
    set_final inconclusive final_workspace_changed 3
  fi
  if [ "$TERMINAL_EMITTED" -eq 0 ]; then
    build_terminal_command "$final_root"
    if run_finalizer_command "${EVENT_COMMAND[@]}"; then
      TERMINAL_EMITTED=1
    else
      publish_rc=2
    fi
    abort_if_finalizer_signalled
  fi
  if [ "$publish_rc" -eq 0 ]; then
    run_finalizer_command python3 "$EVIDENCE" validate-run \
      --file "$NDJSON" --schema "$SCHEMA" --expected-verdict "$FINAL_VERDICT" \
      --artifact-root "$ART_DIR" --output "$ART_DIR/run.validation.json" || publish_rc=2
    abort_if_finalizer_signalled
  fi
  if [ "$publish_rc" -eq 0 ]; then
    run_finalizer_command python3 "$EVIDENCE" manifest \
      --art-dir "$ART_DIR" \
      --output "$ART_DIR/manifest.json" \
      --digest-output "$ART_DIR/manifest.digest" \
      --run-id "$RUN_ID" --bead "$BEAD" --scenario quality_gate \
      --verdict "$FINAL_VERDICT" --input-root "$INPUT_ROOT" --final-root "$final_root" \
      || publish_rc=2
    abort_if_finalizer_signalled
  fi
  if [ "$publish_rc" -eq 0 ]; then
    run_finalizer_command python3 "$EVIDENCE" complete-bundle --art-dir "$ART_DIR" \
      --manifest "$ART_DIR/manifest.json" --digest "$ART_DIR/manifest.digest" \
      --output "$ART_DIR/bundle.complete.json" --governed-root "$GOVERNED_ROOT" \
      "${GOVERNED_ARGS[@]}" --expected-root "$final_root" \
      "${BUNDLE_CONTEXT_ARGS[@]}" || true
    if ! finalizer_test_checkpoint post_decision; then publish_rc=2; fi
    if run_finalizer_command python3 "$EVIDENCE" validate-bundle --art-dir "$ART_DIR" \
        --manifest "$ART_DIR/manifest.json" --digest "$ART_DIR/manifest.digest" \
        --commit "$ART_DIR/bundle.complete.json" --artifact-root "$ART_DIR" \
        >/dev/null; then
      # A complete decision is the logical winner. Validation durably adopts its
      # canonical marker if the publisher died before linking or syncing it.
      trap '' HUP INT TERM
    else
      abort_if_finalizer_signalled
      publish_rc=2
    fi
  fi
  if [ "$publish_rc" -ne 0 ]; then
    note "INTERNAL FAULT: evidence bundle did not publish completely: $ART_DIR"
    exit 2
  fi
  if [ "$FINAL_VERDICT" = pass ]; then
    printf '[check] PASS — all obligations green; committed evidence: %s\n' "$ART_DIR" >&2
  else
    printf '[check] %s — reason=%s; committed evidence: %s\n' \
      "$FINAL_VERDICT" "$FINAL_REASON" "$ART_DIR" >&2
  fi
  exit "$FINAL_EXIT"
}

trap 'on_signal HUP 129' HUP
trap 'on_signal INT 130' INT
trap 'on_signal TERM 143' TERM
trap 'FINALIZER_TRANSITION=1 on_exit "$?"' EXIT

emit_event \
  --new-log \
  --string event run_start \
  --json-value argv "$RUN_ARGV_JSON" \
  --string cwd "$REPO" \
  --append-string claim_ids FLN-W1-SCAFFOLD \
  --append-string claim_ids FLN-QUALITY-GATE \
  --append-string invariant_ids FL-INV-01 \
  --append-string invariant_ids FL-INV-07 \
  --append-string invariant_ids D1 \
  --append-string invariant_ids D3 \
  --append-string gate_ids W1 \
  --append-string gate_ids G0-10 \
  --string parity_ledger_row not_applicable_structural_governance \
  --string epoch lean-v4.32.0 \
  --string mode sound \
  --string profile "$PROFILE" \
  --string platform "$(uname -srm)" \
  --json-value host_facts "$HOST_FACTS_JSON" \
  --integer thread_count "$THREAD_COUNT" \
  --string seed "$SEED" \
  --string cache_state "$CACHE_STATE" \
  --string input_root "$INPUT_ROOT" \
  --string ubs_inventory "$UBS_INVENTORY_BINDING" \
  --string vendor_binding "$VENDOR_BINDING_BINDING" \
  --json-value budgets "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"stage_timeout_ms\":$STAGE_TIMEOUT_MS,\"kill_grace_ms\":$KILL_GRACE_MS}" \
  --string rustc "$(rustc --version 2>/dev/null || printf unknown)" \
  --string planted "$PLANT"
: > "$HUMAN"

if [ "$FINALIZER_PROBE" -eq 1 ]; then
  ACTIVE_STAGE=finalizer-probe
  emit_event --string event self_test --string stage finalizer-probe \
    --boolean ok true --integer planted_exit 0 \
    --string artifact finalizer-probe
  set_final pass finalizer_probe_complete 0
  exit 0
fi

read_meta_field() {
  python3 - "$1" "$2" <<'PY'
import json, pathlib, sys
value = json.loads(pathlib.Path(sys.argv[1]).read_text())
field = value[sys.argv[2]]
if isinstance(field, bool):
    print("true" if field else "false")
elif field is None:
    print("null")
else:
    print(field)
PY
}

run_stage() {
  local name="$1"; shift
  local meta="$ART_DIR/$name.meta.json" out="$ART_DIR/$name.out" err="$ART_DIR/$name.err"
  local ready="$ART_DIR/$name.ready.json"
  local launch_ready="$ART_DIR/$name.launch.ready.json"
  local launch_release="$ART_DIR/$name.launch.release.json"
  local wrapper_rc classification reason recorded_wrapper planted=false
  local -a argv=("$@") semantic_args=()
  ACTIVE_STAGE="$name"
  if [ "$PLANT" = "$name" ]; then
    argv=(false)
    planted=true
    semantic_args=(--semantic-failure-exit 1)
  else
    case "$name" in
      shellcheck|fmt|structure-guard|vendor-tree|ubs)
        semantic_args=(--semantic-failure-exit 1)
        ;;
      check|clippy|test)
        semantic_args=(--semantic-failure-exit 101)
        ;;
    esac
  fi
  note "stage=$name: ${argv[*]}"
  local -a runner=(python3 "$EVIDENCE" run
    --cwd "$REPO"
    --metadata "$meta"
    --stdout "$out"
    --stderr "$err"
    --readiness "$ready"
    --launch-ready "$launch_ready"
    --launch-release "$launch_release"
    --artifact-root "$ART_DIR"
    --capture-bytes "$CAPTURE_BYTES"
    --output-budget-bytes "$OUTPUT_BUDGET_BYTES"
    --timeout-ms "$STAGE_TIMEOUT_MS"
    --grace-ms "$KILL_GRACE_MS"
    --stage-id "$name" "${semantic_args[@]}")
  [ "$planted" = true ] && runner+=(--planted)
  runner+=(-- "${argv[@]}")
  SPAWNING=1
  setsid -- "${runner[@]}" &
  ACTIVE_RUNNER_PID=$!
  if ! ACTIVE_RUNNER_START_TICKS="$(
    setsid -- python3 "$EVIDENCE" process-start-ticks --pid "$ACTIVE_RUNNER_PID" \
      --expected-parent-pid "$$" --wait-ms "$READY_WAIT_MS" --session-leader \
      2>/dev/null
  )"; then
    if ! terminate_unreleased_runner "$ACTIVE_RUNNER_PID"; then
      mark_process_tree_cleanup_unproven
      exit 2
    fi
    SPAWNING=0
    ACTIVE_RUNNER_PID=""
    if [ -n "$PENDING_SIGNAL" ]; then
      local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
      PENDING_SIGNAL=""
      set_final cancelled "signal_$pending_name" "$pending_exit"
      exit "$pending_exit"
    fi
    set_final internal_fault active_runner_identity_unproven 2
    exit 2
  fi
  if [ -n "$PENDING_SIGNAL" ]; then
    local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
    PENDING_SIGNAL=""
    if ! terminate_unreleased_runner "$ACTIVE_RUNNER_PID"; then
      mark_process_tree_cleanup_unproven
      exit 2
    fi
    SPAWNING=0
    ACTIVE_RUNNER_PID=""
    ACTIVE_RUNNER_START_TICKS=""
    set_final cancelled "signal_$pending_name" "$pending_exit"
    exit "$pending_exit"
  fi
  ACTIVE_READINESS="$ready"
  ACTIVE_RUNNER_PROTOCOL=guardian
  ACTIVE_RUNNER_ART_DIR="$ART_DIR"
  if ! release_guardian_launch "$name" "$ACTIVE_RUNNER_PID" \
      "$ACTIVE_RUNNER_START_TICKS" "$launch_ready" "$launch_release"; then
    local release_cleanup_failed=0
    if [ -s "$launch_release" ]; then
      if ! stop_active_runner TERM; then
        release_cleanup_failed=1
      fi
    else
      if ! terminate_unreleased_runner "$ACTIVE_RUNNER_PID"; then
        release_cleanup_failed=1
      fi
    fi
    if [ "$release_cleanup_failed" -ne 0 ]; then
      mark_process_tree_cleanup_unproven
      exit 2
    fi
    SPAWNING=0
    ACTIVE_RUNNER_PID=""
    ACTIVE_RUNNER_START_TICKS=""
    if [ -n "$PENDING_SIGNAL" ]; then
      local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
      PENDING_SIGNAL=""
      set_final cancelled "signal_$pending_name" "$pending_exit"
      exit "$pending_exit"
    fi
    set_final internal_fault active_runner_launch_unproven 2
    exit 2
  fi
  SPAWNING=0
  if [ -n "$PENDING_SIGNAL" ]; then
    local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
    PENDING_SIGNAL=""
    if ! stop_active_runner "$pending_name"; then
      mark_process_tree_cleanup_unproven
      exit 2
    fi
    set_final cancelled "signal_$pending_name" "$pending_exit"
    exit "$pending_exit"
  fi
  if wait "$ACTIVE_RUNNER_PID"; then
    wrapper_rc=0
  else
    wrapper_rc=$?
  fi
  ACTIVE_RUNNER_PID=""
  ACTIVE_RUNNER_START_TICKS=""
  ACTIVE_READINESS=""
  ACTIVE_RUNNER_PROTOCOL=""
  ACTIVE_RUNNER_ART_DIR=""
  if [ ! -f "$meta" ]; then
    emit_event --string event stage --string stage "$name" \
      --string outcome internal_fault --string reason_code missing_supervisor_metadata \
      --string expected exit_zero --string actual metadata_unavailable \
      --boolean supervisor_available false --integer wrapper_exit "$wrapper_rc"
    set_final internal_fault missing_supervisor_metadata 2
    exit 2
  fi
  classification="$(read_meta_field "$meta" classification)"
  reason="$(read_meta_field "$meta" reason_code)"
  recorded_wrapper="$(read_meta_field "$meta" wrapper_exit)"
  emit_event \
    --string event stage \
    --string stage "$name" \
    --string outcome "$classification" \
    --string reason_code "$reason" \
    --string expected exit_zero \
    --string actual "$classification" \
    --integer wrapper_exit "$wrapper_rc" \
    --json-file supervisor "$meta"
  if [ "$recorded_wrapper" != "$wrapper_rc" ]; then
    set_final internal_fault "$name:wrapper_exit_mismatch" 2
    exit 2
  fi
  if [ "$wrapper_rc" -eq 0 ] && [ "$classification" = pass ]; then
    note "ok stage=$name"
    return 0
  fi
  note "$classification stage=$name reason=$reason wrapper_exit=$wrapper_rc"
  note "captured stderr tail follows ($name)"
  tail -n 40 "$err" >&2 || true
  case "$wrapper_rc" in
    1) set_final fail "$name:$reason" 1; exit 1 ;;
    3) set_final inconclusive "$name:$reason" 3; exit 3 ;;
    4) set_final cancelled "$name:$reason" 4; exit 4 ;;
    *) set_final internal_fault "$name:$reason" 2; exit 2 ;;
  esac
}

skip_stage() {
  local name="$1" reason="$2"
  ACTIVE_STAGE="$name"
  emit_event --string event stage --string stage "$name" --string outcome skipped \
    --string reason_code typed_limitation --string expected not_applicable \
    --string actual skipped --string limitation "$reason"
  echo "[check] skip stage=$name: $reason" >&2
}

self_test() {
  local failures=0 stage rc child="$ART_DIR" child_pid wrapper_ready
  local wrapper_launch_ready wrapper_launch_release
  for stage in evidence-self-test shellcheck fmt check clippy test structure-guard vendor-tree ubs; do
    echo "[check:self-test] planting failure in stage=$stage" >&2
    child="$ART_DIR/selftest-$stage"
    wrapper_ready="$ART_DIR/selftest-$stage.guardian.ready.json"
    wrapper_launch_ready="$ART_DIR/selftest-$stage.guardian.launch.ready.json"
    wrapper_launch_release="$ART_DIR/selftest-$stage.guardian.launch.release.json"
    ACTIVE_STAGE="selftest-$stage"
    SPAWNING=1
    setsid -- python3 "$EVIDENCE" run --cwd "$REPO" \
      --metadata "$ART_DIR/selftest-$stage.guardian.meta.json" \
      --stdout "$ART_DIR/selftest-$stage.console.out" \
      --stderr "$ART_DIR/selftest-$stage.console.err" \
      --readiness "$wrapper_ready" \
      --launch-ready "$wrapper_launch_ready" \
      --launch-release "$wrapper_launch_release" \
      --artifact-root "$ART_DIR" \
      --capture-bytes "$CAPTURE_BYTES" --output-budget-bytes "$OUTPUT_BUDGET_BYTES" \
      --timeout-ms "$STAGE_TIMEOUT_MS" --grace-ms 60000 \
      --stage-id "selftest-$stage" --semantic-failure-exit 1 -- \
      env FLN_CHECK_PLANT="$stage" FLN_CHECK_ART_DIR="$child" \
        FLN_CHECK_PROFILE=self-test-plant bash "${BASH_SOURCE[0]}" &
    child_pid=$!
    ACTIVE_RUNNER_PID="$child_pid"
    if ! ACTIVE_RUNNER_START_TICKS="$(
      setsid -- python3 "$EVIDENCE" process-start-ticks --pid "$child_pid" \
        --expected-parent-pid "$$" --wait-ms "$READY_WAIT_MS" \
        --session-leader 2>/dev/null
    )"; then
      if ! terminate_unreleased_runner "$child_pid"; then
        mark_process_tree_cleanup_unproven
        exit 2
      fi
      SPAWNING=0
      ACTIVE_RUNNER_PID=""
      if [ -n "$PENDING_SIGNAL" ]; then
        local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
        PENDING_SIGNAL=""
        set_final cancelled "signal_$pending_name" "$pending_exit"
        exit "$pending_exit"
      fi
      set_final internal_fault active_runner_identity_unproven 2
      exit 2
    fi
    if [ -n "$PENDING_SIGNAL" ]; then
      local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
      PENDING_SIGNAL=""
      if ! terminate_unreleased_runner "$child_pid"; then
        mark_process_tree_cleanup_unproven
        exit 2
      fi
      SPAWNING=0
      ACTIVE_RUNNER_PID=""
      ACTIVE_RUNNER_START_TICKS=""
      set_final cancelled "signal_$pending_name" "$pending_exit"
      exit "$pending_exit"
    fi
    ACTIVE_READINESS="$wrapper_ready"
    ACTIVE_RUNNER_PROTOCOL=nested-check
    ACTIVE_RUNNER_ART_DIR="$child"
    if ! release_guardian_launch "selftest-$stage" "$child_pid" \
        "$ACTIVE_RUNNER_START_TICKS" "$wrapper_launch_ready" \
        "$wrapper_launch_release"; then
      local release_cleanup_failed=0
      if [ -s "$wrapper_launch_release" ]; then
        if ! stop_active_runner TERM; then
          release_cleanup_failed=1
        fi
      else
        if ! terminate_unreleased_runner "$child_pid"; then
          release_cleanup_failed=1
        fi
      fi
      if [ "$release_cleanup_failed" -ne 0 ]; then
        mark_process_tree_cleanup_unproven
        exit 2
      fi
      SPAWNING=0
      ACTIVE_RUNNER_PID=""
      ACTIVE_RUNNER_START_TICKS=""
      if [ -n "$PENDING_SIGNAL" ]; then
        local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
        PENDING_SIGNAL=""
        set_final cancelled "signal_$pending_name" "$pending_exit"
        exit "$pending_exit"
      fi
      set_final internal_fault active_runner_launch_unproven 2
      exit 2
    fi
    SPAWNING=0
    if [ -n "$PENDING_SIGNAL" ]; then
      local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
      PENDING_SIGNAL=""
      if ! stop_active_runner "$pending_name"; then
        mark_process_tree_cleanup_unproven
        exit 2
      fi
      set_final cancelled "signal_$pending_name" "$pending_exit"
      exit "$pending_exit"
    fi
    if wait "$child_pid"; then rc=0; else rc=$?; fi
    ACTIVE_RUNNER_PID=""
    ACTIVE_RUNNER_START_TICKS=""
    ACTIVE_READINESS=""
    ACTIVE_RUNNER_PROTOCOL=""
    ACTIVE_RUNNER_ART_DIR=""
    if [ "$rc" -eq 1 ] && python3 "$EVIDENCE" validate-run \
      --file "$child/run.ndjson" --schema "$SCHEMA" --expected-verdict fail \
      --expected-active-stage "$stage" --expected-planted-stage "$stage" \
      --artifact-root "$ART_DIR" --output "$ART_DIR/selftest-$stage.validation.json" \
      && python3 "$EVIDENCE" validate-bundle --art-dir "$child" \
        --manifest "$child/manifest.json" --digest "$child/manifest.digest" \
        --commit "$child/bundle.complete.json" --artifact-root "$child" >/dev/null; then
      echo "[check:self-test] ok — planted stage=$stage was caught and terminal" >&2
      emit_event --string event self_test --string stage "$stage" \
        --boolean ok true --integer planted_exit "$rc" --string artifact "selftest-$stage"
    else
      echo "[check:self-test] FAIL — stage=$stage exit=$rc" >&2
      failures=$((failures + 1))
      emit_event --string event self_test --string stage "$stage" \
        --boolean ok false --integer planted_exit "$rc" --string artifact "selftest-$stage"
    fi
  done

  echo "[check:self-test] sending TERM during child run initialization" >&2
  child="$ART_DIR/selftest-cancel-term"
  wrapper_ready="$ART_DIR/selftest-cancel-term.guardian.ready.json"
  wrapper_launch_ready="$ART_DIR/selftest-cancel-term.guardian.launch.ready.json"
  wrapper_launch_release="$ART_DIR/selftest-cancel-term.guardian.launch.release.json"
  ACTIVE_STAGE=selftest-cancel-term
  SPAWNING=1
  setsid -- python3 "$EVIDENCE" run --cwd "$REPO" \
    --metadata "$ART_DIR/selftest-cancel-term.guardian.meta.json" \
    --stdout "$ART_DIR/selftest-cancel-term.console.out" \
    --stderr "$ART_DIR/selftest-cancel-term.console.err" \
    --readiness "$wrapper_ready" \
    --launch-ready "$wrapper_launch_ready" \
    --launch-release "$wrapper_launch_release" \
    --artifact-root "$ART_DIR" \
    --capture-bytes "$CAPTURE_BYTES" --output-budget-bytes "$OUTPUT_BUDGET_BYTES" \
    --timeout-ms "$STAGE_TIMEOUT_MS" --grace-ms 60000 \
    --stage-id selftest-cancel-term -- \
    env FLN_CHECK_ART_DIR="$child" FLN_CHECK_PROFILE=self-test-cancellation \
      bash "${BASH_SOURCE[0]}" &
  child_pid=$!
  ACTIVE_RUNNER_PID="$child_pid"
  if ! ACTIVE_RUNNER_START_TICKS="$(
    setsid -- python3 "$EVIDENCE" process-start-ticks --pid "$child_pid" \
      --expected-parent-pid "$$" --wait-ms "$READY_WAIT_MS" \
      --session-leader 2>/dev/null
  )"; then
    if ! terminate_unreleased_runner "$child_pid"; then
      mark_process_tree_cleanup_unproven
      exit 2
    fi
    SPAWNING=0
    ACTIVE_RUNNER_PID=""
    if [ -n "$PENDING_SIGNAL" ]; then
      local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
      PENDING_SIGNAL=""
      set_final cancelled "signal_$pending_name" "$pending_exit"
      exit "$pending_exit"
    fi
    set_final internal_fault active_runner_identity_unproven 2
    exit 2
  fi
  if [ -n "$PENDING_SIGNAL" ]; then
    local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
    PENDING_SIGNAL=""
    if ! terminate_unreleased_runner "$child_pid"; then
      mark_process_tree_cleanup_unproven
      exit 2
    fi
    SPAWNING=0
    ACTIVE_RUNNER_PID=""
    ACTIVE_RUNNER_START_TICKS=""
    set_final cancelled "signal_$pending_name" "$pending_exit"
    exit "$pending_exit"
  fi
  ACTIVE_READINESS="$wrapper_ready"
  ACTIVE_RUNNER_PROTOCOL=nested-check
  ACTIVE_RUNNER_ART_DIR="$child"
  if ! release_guardian_launch selftest-cancel-term "$child_pid" \
      "$ACTIVE_RUNNER_START_TICKS" "$wrapper_launch_ready" \
      "$wrapper_launch_release"; then
    local release_cleanup_failed=0
    if [ -s "$wrapper_launch_release" ]; then
      if ! stop_active_runner TERM; then
        release_cleanup_failed=1
      fi
    else
      if ! terminate_unreleased_runner "$child_pid"; then
        release_cleanup_failed=1
      fi
    fi
    if [ "$release_cleanup_failed" -ne 0 ]; then
      mark_process_tree_cleanup_unproven
      exit 2
    fi
    SPAWNING=0
    ACTIVE_RUNNER_PID=""
    ACTIVE_RUNNER_START_TICKS=""
    if [ -n "$PENDING_SIGNAL" ]; then
      local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
      PENDING_SIGNAL=""
      set_final cancelled "signal_$pending_name" "$pending_exit"
      exit "$pending_exit"
    fi
    set_final internal_fault active_runner_launch_unproven 2
    exit 2
  fi
  SPAWNING=0
  if [ -n "$PENDING_SIGNAL" ]; then
    local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
    PENDING_SIGNAL=""
    if ! stop_active_runner "$pending_name"; then
      mark_process_tree_cleanup_unproven
      exit 2
    fi
    set_final cancelled "signal_$pending_name" "$pending_exit"
    exit "$pending_exit"
  fi
  for _ in $(seq 1 $((READY_WAIT_MS / 20))); do
    if compgen -G "$child/*.ready.json" >/dev/null; then break; fi
    sleep 0.02
  done
  if ! compgen -G "$child/*.ready.json" >/dev/null; then
    stop_active_runner TERM || true
    rc=2
  elif ! python3 "$EVIDENCE" signal-bound-process --pid "$child_pid" \
      --expected-start-ticks "$ACTIVE_RUNNER_START_TICKS" --signal TERM \
      >/dev/null 2>&1; then
    stop_active_runner TERM || true
    rc=2
  else
    if wait "$child_pid"; then rc=0; else rc=$?; fi
  fi
  ACTIVE_RUNNER_PID=""
  ACTIVE_RUNNER_START_TICKS=""
  ACTIVE_READINESS=""
  ACTIVE_RUNNER_PROTOCOL=""
  ACTIVE_RUNNER_ART_DIR=""
  if [ "$rc" -eq 4 ] && python3 "$EVIDENCE" validate-run \
    --file "$child/run.ndjson" --schema "$SCHEMA" --expected-verdict cancelled \
    --artifact-root "$ART_DIR" --output "$ART_DIR/selftest-cancel-term.validation.json" \
    && python3 "$EVIDENCE" validate-bundle --art-dir "$child" \
      --manifest "$child/manifest.json" --digest "$child/manifest.digest" \
      --commit "$child/bundle.complete.json" --artifact-root "$child" >/dev/null; then
    echo "[check:self-test] ok — TERM produced one validated cancelled terminal" >&2
    emit_event --string event self_test --string stage cancel-term \
      --boolean ok true --integer planted_exit "$rc" --string artifact selftest-cancel-term
  else
    echo "[check:self-test] FAIL — TERM child exit=$rc" >&2
    failures=$((failures + 1))
    emit_event --string event self_test --string stage cancel-term \
      --boolean ok false --integer planted_exit "$rc" --string artifact selftest-cancel-term
  fi
  if [ "$failures" -eq 0 ]; then
    set_final pass self_test_complete 0
    exit 0
  fi
  set_final fail self_test_failure 1
  echo "[check:self-test] FAIL — $failures planted stage(s) escaped" >&2
  exit 1
}

if [ "${1:-}" = "--self-test" ]; then
  self_test
fi

# --locked makes Cargo.lock drift a failure instead of silently rewriting it.
run_stage evidence-self-test python3 scripts/evidence.py self-test \
  --art-dir "$ART_DIR/evidence-self-test"
run_stage shellcheck shellcheck scripts/check.sh scripts/verify_vendor_tree.sh \
  scripts/e2e/structure_gate.sh scripts/e2e/closure_audit.sh scripts/e2e/structural_gate.sh \
  scripts/e2e/core_observables.sh scripts/extract/gen_core_fixtures.sh \
  scripts/e2e/hash_identity.sh scripts/e2e/diag_goldens.sh \
  scripts/e2e/env_snapshots.sh scripts/e2e/bignum_vectors.sh \
  scripts/e2e/contract_drift.sh scripts/extract/gen_extern_census.sh \
  scripts/tribunal/gen_epoch_manifest.sh scripts/tribunal/ref_vs_ref.sh
run_stage fmt cargo fmt --check
run_stage check cargo check --locked --all-targets
run_stage clippy cargo clippy --locked --all-targets -- -D warnings
run_stage test cargo test --locked
run_stage structure-guard cargo run -q --locked -p structure-guard -- --root "$REPO" --robot
run_stage vendor-tree bash scripts/verify_vendor_tree.sh

# The exact file set was materialized before run_start and is part of INPUT_ROOT.
python3 "$EVIDENCE" validate-ubs-inventory --root "$REPO" \
  --inventory "$UBS_INVENTORY" >/dev/null
UBS_COUNT="$(read_meta_field "$UBS_INVENTORY" count)"
if [ "$PLANT" = ubs ]; then
  run_stage ubs ubs --version
elif command -v ubs >/dev/null 2>&1; then
  if [ "$UBS_COUNT" -gt 0 ]; then
    run_stage ubs python3 "$EVIDENCE" exec-ubs-inventory \
      --root "$REPO" --inventory "$UBS_INVENTORY" -- ubs --ci
    python3 "$EVIDENCE" validate-ubs-inventory --root "$REPO" \
      --inventory "$UBS_INVENTORY" >/dev/null
  else
    skip_stage ubs "validated zero-file project-authored $UBS_SCOPE UBS scope"
  fi
elif [ "${CI:-}" = true ] || [ "${FLN_REQUIRE_UBS:-0}" = 1 ]; then
  run_stage ubs ubs --version
else
  skip_stage ubs "ubs binary not on PATH (local typed limitation; CI is fail-closed)"
fi

ACTIVE_STAGE="complete"
set_final pass all_stages_green 0
exit 0
