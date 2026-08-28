#!/usr/bin/env bash
# scripts/check.sh — the single FrankenLean quality gate.
#
# Stages are append-only obligations: evidence harness self-test, verification registry,
# shell policy, fmt, check, clippy, tests, structural policy, exact Reference tree, and
# UBS. Each command runs under a bounded supervisor that drains stdout/stderr to EOF,
# preserves useful head+tail captures, applies a monotonic timeout and total-output
# budget, and cancels the whole child process group. The published fln.check/2 NDJSON
# names every stage in canonical order: after the first failure every later obligation is
# explicit `not_run`. It has exactly one final terminal record plus a write-once SHA-256
# artifact manifest.
#
# Exit taxonomy: 0 pass; 1 stage failure; 2 setup/evidence/internal fault;
# 3 resource exhaustion or timeout (inconclusive); 129/130/143 HUP/INT/TERM cancellation.

set -Eeuo pipefail

FINALIZER_PROBE=0
EARLY_FAULT_PROBE=0
TRIBUNAL_MANIFEST_INVENTORY_ONLY=0
case "${1:-}" in
  --help|-h)
    sed -n '2,17p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
    exit 0
    ;;
  --self-test|"") ;;
  --tribunal-manifest-inventory) TRIBUNAL_MANIFEST_INVENTORY_ONLY=1 ;;
  --finalizer-probe) FINALIZER_PROBE=1 ;;
  --early-fault-probe) FINALIZER_PROBE=1; EARLY_FAULT_PROBE=1 ;;
  *) echo "unknown argument: $1 (see --help)" >&2; exit 2 ;;
esac

PYTHON_BIN="$(command -v python3 || true)"
[[ -n "$PYTHON_BIN" ]] || {
  echo "[check] setup failure: python3 is required by the evidence harness" >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
HOSTILE_PYTHON_CONFIGURATION=()
while IFS= read -r environment_name; do
  [[ "$environment_name" == PYTHON* ]] \
    && HOSTILE_PYTHON_CONFIGURATION+=("$environment_name")
done < <(compgen -e | LC_ALL=C sort)
if ((${#HOSTILE_PYTHON_CONFIGURATION[@]} > 0)); then
  printf '[check] setup failure: sealed_interpreter_hostile_environment names=%s\n' \
    "$(IFS=,; printf '%s' "${HOSTILE_PYTHON_CONFIGURATION[*]}")" >&2
  exit 2
fi
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

# The build gate, taken by the lane instead of by its caller — bead
# franken_lean-gate-lock-producer-optional-o2vz. The library landed VERIFIED AND DELIBERATELY
# UNWIRED at 5a94b48e, at core scope, so that this wiring could be judged on the core's measured
# behaviour rather than on a prediction of it; this is that wiring. Before it, the gate lockfile
# was named in zero executable surfaces, which left a FREE probe uninformative (an unwrapped lane
# takes no lock) and a HELD probe uninformative (anything at all may take the path).
#
# Placement is load-bearing in both directions and is stated as constructs, not line numbers,
# because a line number is a claim that rots: this sits AFTER the argument `case` closes, so
# `--help` exits without ever reaching the gate, and BEFORE the EXIT finalizer is installed, so a
# contention `exit 3` runs no finalizer and leaves no partial evidence behind.
#
# Rolling this out to the remaining sites is a SEPARATE decision, deliberately not taken here.
#
# SC1091 is disabled rather than followed: the library is named as its own input to the shellcheck
# stage below, so it is checked directly (exit 0) rather than through this `.`. Following it here
# would need `-x` on the whole stage, which changes the verdict for 25 other scripts at once.
# shellcheck source=scripts/lib/gate_lock.sh
# shellcheck disable=SC1091
. "$REPO/scripts/lib/gate_lock.sh"
# The authoritative lane owns the build gate. Its nested test-control consumers do not:
# evidence.py's self-test launches finalizer probes, early-envelope probes, and planted
# short-circuit runs of this same script while the parent lane still holds the lock. The
# parent also invokes the read-only tribunal-manifest inventory as one supervised stage.
# Making those children re-acquire the parent's non-inherited flock self-deadlocks them
# before they can publish a result.
#
# These are not alternate ways to run the quality gate. Each form is already bound into the
# terminal evidence as a probe or plant and cannot publish an ordinary pass. `--self-test`
# itself remains authoritative and takes the gate; only the children it launches match one
# of the conditions below.
if [ "$TRIBUNAL_MANIFEST_INVENTORY_ONLY" -eq 0 ] \
   && [ "$FINALIZER_PROBE" -eq 0 ] \
   && [ "$EARLY_FAULT_PROBE" -eq 0 ] \
   && [ -z "${FLN_CHECK_PLANT:-}" ] \
   && [ -z "${FLN_CHECK_PLANT_UNEXPECTED:-}" ]; then
  fln_gate_acquire "$SCENARIO"
fi

VERIFICATION_MANIFEST_REL="ci/VERIFICATION_MANIFEST.jsonl"
VERIFICATION_MANIFEST="$REPO/$VERIFICATION_MANIFEST_REL"
CHECK_STAGE_ORDER=(
  evidence-self-test verification-manifest shellcheck ubs-gate-classifier
  projection-guard-harness fmt check clippy contract-handoff-no-mock test
  tribunal-manifest-inventory epoch-lab-test
  epoch-lab-live-verify structure-guard vendor-tree ubs
)
RUN_ID="check-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_CHECK_ART_ROOT:-$REPO/target/check}"
ART_DIR="${FLN_CHECK_ART_DIR:-$ART_ROOT/$RUN_ID}"
# Per-attempt isolated build state for the sealed compiler lane (bead
# fln-evidence-runner-bootstrap-btk): never the user's ambient CARGO_HOME or
# target directory; target/ is gitignored and user caches are never touched.
SEALED_BUILD_ROOT="${FLN_CHECK_SEALED_BUILD_ROOT:-$REPO/target/sealed}/$RUN_ID"
NDJSON="$ART_DIR/run.ndjson"
HUMAN="$ART_DIR/human.log"
HUMAN_SEMANTIC="$ART_DIR/human.semantic.log"
CAPTURE_BYTES="${FLN_CHECK_CAPTURE_BYTES:-262144}"
OUTPUT_BUDGET_BYTES="${FLN_CHECK_OUTPUT_BUDGET_BYTES:-67108864}"
STAGE_TIMEOUT_MS="${FLN_CHECK_STAGE_TIMEOUT_MS:-1200000}"
KILL_GRACE_MS="${FLN_CHECK_KILL_GRACE_MS:-2000}"
READY_WAIT_MS="${FLN_CHECK_READY_WAIT_MS:-30000}"
PLANT="${FLN_CHECK_PLANT:-}"
PLANT_UNEXPECTED="${FLN_CHECK_PLANT_UNEXPECTED:-}"
# The run_start planted-stage binding carries the plant form so validation can
# hold each form to its own contract (semantic fail vs unexpected exit).
PLANT_BINDING="$PLANT"
[ -n "$PLANT_UNEXPECTED" ] && PLANT_BINDING="unexpected:$PLANT_UNEXPECTED"
FINALIZER_TEST_POINT="${FLN_FINALIZER_TEST_POINT:-}"
TEST_EARLY_FAULT="${FLN_CHECK_TEST_EARLY_FAULT:-}"
if [ "$EARLY_FAULT_PROBE" -eq 1 ]; then
  PROFILE=early-fault-self-test
elif [ "$FINALIZER_PROBE" -eq 1 ]; then
  case "$FINALIZER_TEST_POINT" in
    spawn_bind|active_wait|helper_failure|decision_write|marker_link|post_decision) ;;
    *) echo "invalid finalizer probe point: $FINALIZER_TEST_POINT" >&2; exit 2 ;;
  esac
  PROFILE=finalizer-self-test
elif [ -n "${FLN_CHECK_PROFILE:-}" ]; then
  PROFILE="$FLN_CHECK_PROFILE"
elif [ "${1:-}" = --self-test ]; then
  PROFILE=self-test-driver
elif [ -n "$PLANT" ] || [ -n "$PLANT_UNEXPECTED" ]; then
  PROFILE=self-test-plant
elif [ "${CI:-}" = true ]; then
  PROFILE=ci
else
  PROFILE=local
fi
THREAD_COUNT="${FLN_CHECK_THREAD_COUNT:-1}"
SEED="${FLN_CHECK_SEED:-none}"
CACHE_STATE="${FLN_CHECK_CACHE_STATE:-uncontrolled}"
START_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
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
HUMAN_LOG_SEALED=0
FINALIZING=0
RUN_STARTED=0
ART_DIR_CLAIMED=0
EARLY_STEP=preflight
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
CENSUS_AVAILABILITY_RECEIPT="$ART_DIR/contract-handoff-no-mock.availability.json"
CENSUS_SKIP_LIMITATION="census evidence is absent under probe_root=$REPO; the three named contract-handoff no-mock tests are typed skipped"
CENSUS_NO_MOCK_TESTS=(
  contract_handoff::tests::contract_handoff_no_mock_e2e
  real_workspace_is_structurally_clean
  robot_real_workspace_binds_complete_authority_evidence
)
EVENT_COMMAND=()
INPUT_PATHS=(
  Cargo.toml Cargo.lock SUITE.lock rust-toolchain.toml .beads/issues.jsonl
  ci crates tools
  vendor/NOTICE
  scripts/check.sh scripts/evidence.py scripts/verify_vendor_tree.sh
  scripts/lib/gate_lock.sh
  scripts/e2e/structure_gate.sh scripts/e2e/closure_audit.sh
  scripts/e2e/structural_gate.sh scripts/e2e/core_observables.sh
  scripts/e2e/hash_identity.sh scripts/e2e/diag_goldens.sh
  scripts/e2e/env_snapshots.sh scripts/e2e/bignum_vectors.sh
  scripts/e2e/campaign_frameworks.sh scripts/e2e/attribute_state_census.sh
  scripts/extract/gen_core_fixtures.sh scripts/extract/gen_core_fixtures.lean
  scripts/extract/gen_core_ext_fixtures.sh scripts/extract/gen_core_ext_fixtures.lean
  scripts/extract/convert_blake3_vectors.py scripts/extract/gen_bignum_vectors.py
  scripts/extract/gen_abi_contract.py scripts/extract/gen_olean_contract.py
  scripts/extract/gen_lsp_wire_census.py scripts/extract/gen_cli_lake_census.py
  scripts/extract/gen_attribute_state_census.py
  scripts/extract/gen_public_surface_contract.py
  scripts/extract/gen_extern_census.sh scripts/extract/gen_extern_census.lean
  scripts/e2e/contract_drift.sh scripts/e2e/contract_handoff.sh
  scripts/e2e/olean_resurrection.sh
  scripts/e2e/kernel_replay.sh scripts/e2e/lexer_no_mock_e2e.sh
  scripts/e2e/parser_corpus_no_mock_e2e.sh
  scripts/e2e/dynamic_parser_no_mock_e2e.sh
  scripts/e2e/suite_upgrade_candidate_preflight.sh
  scripts/e2e/suite_upgrade_no_mock_e2e.sh
  scripts/e2e/macro_txn_no_mock_e2e.sh
  scripts/e2e/cartridge_no_mock_e2e.sh
  scripts/e2e/certificate_format_no_mock_e2e.sh
  scripts/e2e/g0_4_no_mock_e2e.sh
  scripts/e2e/vellum_naming_no_mock_e2e.sh
  scripts/e2e/verdict_schema.sh scripts/e2e/unsafe_note_clippy.sh
  scripts/tribunal/leanchecker_witness.sh
  contracts ABI_CONTRACT.md OLEAN_CONTRACT.md rustfmt.toml
  scripts/tribunal/gen_epoch_manifest.sh scripts/tribunal/ref_vs_ref.sh
  scripts/git-hooks/pre-commit scripts/git-hooks/install.sh
  scripts/git-hooks/test_projection_guard.sh
  scripts/ubs_gate_classifier.sh scripts/test_ubs_gate_classifier.sh
  tribunal
  .github/workflows/ci.yml .github/workflows/contract-drift.yml
)
# Every Cargo manifest below tribunal/ is outside the root workspace by
# construction. Keep the registry exact so adding another nested Tribunal suite
# without adding its gate invocation cannot silently reduce coverage.
TRIBUNAL_NESTED_MANIFESTS=(
  tribunal/epoch-lab/Cargo.toml
)
verify_tribunal_manifest_inventory() {
  local -a expected=("$@") actual=()
  local manifest index mismatch=0
  mapfile -d "" -t actual < <(
    find tribunal -path "*/target" -prune -o -name Cargo.toml -print0 |
      LC_ALL=C sort -z
  )
  if ((${#actual[@]} != ${#expected[@]})); then
    mismatch=1
  else
    for index in "${!expected[@]}"; do
      if [[ "${actual[index]}" != "${expected[index]}" ]]; then
        mismatch=1
        break
      fi
    done
  fi
  for manifest in "${actual[@]}"; do
    if [[ -L "$REPO/$manifest" || ! -f "$REPO/$manifest" ]]; then
      printf "tribunal_manifest_inventory: non_regular_manifest=%s\n" \
        "$manifest" >&2
      return 1
    fi
  done
  if ((mismatch)); then
    printf "tribunal_manifest_inventory: unregistered_nested_suite\n" >&2
    printf "expected=%s\n" "$(IFS=,; printf "%s" "${expected[*]}")" >&2
    printf "actual=%s\n" "$(IFS=,; printf "%s" "${actual[*]}")" >&2
    return 1
  fi
  printf "tribunal_manifest_inventory: pass count=%d\n" "${#actual[@]}"
}
if ((TRIBUNAL_MANIFEST_INVENTORY_ONLY)); then
  verify_tribunal_manifest_inventory "${TRIBUNAL_NESTED_MANIFESTS[@]}"
  exit $?
fi
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
build_event_command() {
  local sequence="$SEQ"
  SEQ=$((SEQ + 1))
  EVENT_COMMAND=("${PYTHON[@]}" "$EVIDENCE" emit --file "$NDJSON" --artifact-root "$ART_DIR" \
    --string schema "$SCHEMA" \
    --string run_id "$RUN_ID" \
    --string bead "$BEAD" \
    --string scenario "$SCENARIO" \
    --integer sequence "$sequence" \
    --integer monotonic_ns "$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')" \
    --string wall_time_utc "$(date -u -Is)" \
    "$@")
}

emit_event() {
  build_event_command "$@"
  "${EVENT_COMMAND[@]}"
}

note() {
  if [ "$HUMAN_LOG_SEALED" -eq 1 ]; then
    printf '[check] %s\n' "$*" >&2
    return 0
  fi
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

# Typed early-envelope faults (bead fln-evidence-runner-bootstrap-btk): any
# failure between artifact-directory creation and the run_start emission still
# finalizes a typed durable PARTIAL bundle — never a complete one.
early_fault() {
  local reason="$1" message="$2"
  echo "[check] setup failure: $message" >&2
  set_final internal_fault "$reason" 2
  exit 2
}

# shellcheck disable=SC2317
finalize_early_envelope() {
  local observed_rc="$1"
  trap '' HUP INT TERM
  set +e
  if [ "$FINAL_SET" -eq 0 ]; then
    if [ "$observed_rc" -eq 0 ]; then
      set_final internal_fault "early_${EARLY_STEP}_uncommitted_success" 2
    else
      set_final internal_fault "early_${EARLY_STEP}_unexpected_exit" 2
    fi
  fi
  if [ "$ART_DIR_CLAIMED" -eq 1 ] && [ -d "$ART_DIR" ]; then
    note "typed early-envelope fault: step=$EARLY_STEP reason=$FINAL_REASON verdict=$FINAL_VERDICT"
    if ! "${PYTHON[@]}" "$EVIDENCE" publish-partial-bundle --art-dir "$ART_DIR" \
        --run-id "$RUN_ID" --bead "$BEAD" --scenario "$SCENARIO" \
        --step "$EARLY_STEP" --reason "$FINAL_REASON" \
        --classification "$FINAL_VERDICT" \
        --argv-json "${RUN_ARGV_JSON:-[\"scripts/check.sh\"]}" \
        --cwd "$REPO"; then
      printf '[check] INTERNAL FAULT: early evidence bundle did not publish: %s\n' \
        "$ART_DIR" >&2
      exit 2
    fi
    if ! "${PYTHON[@]}" "$EVIDENCE" validate-partial-bundle --art-dir "$ART_DIR" \
        --artifact-root "$ART_DIR" >/dev/null; then
      printf '[check] INTERNAL FAULT: early evidence bundle did not validate: %s\n' \
        "$ART_DIR" >&2
      exit 2
    fi
    printf '[check] %s — reason=%s; partial early-envelope evidence: %s\n' \
      "$FINAL_VERDICT" "$FINAL_REASON" "$ART_DIR" >&2
  fi
  exit "$FINAL_EXIT"
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
    --integer duration_ns "$(( $("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())') - START_NS ))" \
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
  if ! setsid -- "${PYTHON[@]}" "$EVIDENCE" kill-direct-child --pid "$pid" \
      --expected-parent-pid "$$" --wait-ms 5000; then
    return 1
  fi
  wait "$pid" 2>/dev/null || true
}

release_guardian_launch() {
  local stage="$1" pid="$2" ticks="$3" ready="$4" output="$5"
  for _ in 1 2; do
    if setsid -- "${PYTHON[@]}" "$EVIDENCE" release-process-launch --ready "$ready" \
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
    "${PYTHON[@]}" "$EVIDENCE" signal-bound-process --pid "$pid" \
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
        if ! "${PYTHON[@]}" "$EVIDENCE" emergency-kill --readiness "$ACTIVE_READINESS" \
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
            || ! "${PYTHON[@]}" "$EVIDENCE" validate-run \
              --file "$runner_art_dir/run.ndjson" --schema "$SCHEMA" \
              --expected-verdict cancelled --artifact-root "$ART_DIR" \
              >/dev/null 2>&1 \
            || ! "${PYTHON[@]}" "$EVIDENCE" validate-bundle --art-dir "$runner_art_dir" \
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
  if ! setsid -- "${PYTHON[@]}" "$EVIDENCE" kill-bound-group --pid "$FINALIZER_PID" \
      --expected-start-ticks "$FINALIZER_START_TICKS" \
      --expected-parent-pid "$$" >/dev/null 2>&1; then
    FINALIZER_CLEANUP_UNPROVEN=1
    FINALIZER_WAIT_UNSAFE=1
    mark_process_tree_cleanup_unproven
    return 1
  fi
  if ! setsid -- "${PYTHON[@]}" "$EVIDENCE" assert-process-group-empty \
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
  setsid -- "${PYTHON[@]}" "$EVIDENCE" stopped-exec \
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
    setsid -- "${PYTHON[@]}" "$EVIDENCE" process-start-ticks --pid "$FINALIZER_PID" \
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
    if ! setsid -- "${PYTHON[@]}" "$EVIDENCE" resume-bound-process \
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
  local -a MARKER_PAUSE_ARGS=()
  # Recorded FIRST, so it survives every later early-exit path in this finalizer. `|| true`
  # because `set -e` is in force and a journal write is never worth killing a finalizer over;
  # the kernel releases the gate when fd 9 closes regardless of whether this line ran.
  fln_gate_release_note "$SCENARIO" || true
  if [ "$RUN_STARTED" -eq 0 ]; then
    trap - EXIT
    finalize_early_envelope "$observed_rc"
  fi
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
    run_finalizer_command "${PYTHON[@]}" -c 'import time; time.sleep(60)' \
      2>/dev/null || hash_rc=$?
  else
    run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$GOVERNED_ROOT" \
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
    run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" render-check-human \
      --file "$NDJSON" --output "$HUMAN_SEMANTIC" --artifact-root "$ART_DIR" \
      || publish_rc=2
    abort_if_finalizer_signalled
  fi
  if [ "$publish_rc" -eq 0 ]; then
    run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" validate-run \
      --file "$NDJSON" --schema "$SCHEMA" --expected-verdict "$FINAL_VERDICT" \
      --artifact-root "$ART_DIR" --output "$ART_DIR/run.validation.json" || publish_rc=2
    abort_if_finalizer_signalled
  fi
  if [ "$publish_rc" -eq 0 ]; then
    # human.log is a manifested artifact. Append its terminal semantic record,
    # then permanently seal it before the manifest inventories any artifact.
    # Later publisher diagnostics remain visible on stderr but cannot invalidate
    # an already-generated manifest.
    note "terminal verdict=$FINAL_VERDICT reason=$FINAL_REASON process_exit=$FINAL_EXIT" \
      || publish_rc=2
    HUMAN_LOG_SEALED=1
    abort_if_finalizer_signalled
  fi
  if [ "$publish_rc" -eq 0 ]; then
    run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" manifest \
      --art-dir "$ART_DIR" \
      --output "$ART_DIR/manifest.json" \
      --digest-output "$ART_DIR/manifest.digest" \
      --run-id "$RUN_ID" --bead "$BEAD" --scenario quality_gate \
      --verdict "$FINAL_VERDICT" --input-root "$INPUT_ROOT" --final-root "$final_root" \
      || publish_rc=2
    abort_if_finalizer_signalled
  fi
  if [ "$publish_rc" -eq 0 ]; then
    # A signal at this checkpoint precedes the bundle decision, so cancellation
    # must win and the publisher below must never link a decision.
    if ! finalizer_test_checkpoint decision_write; then publish_rc=2; fi
    abort_if_finalizer_signalled
  fi
  if [ "$publish_rc" -eq 0 ]; then
    MARKER_PAUSE_ARGS=()
    if [ "$FINALIZER_PROBE" -eq 1 ] && [ "$FINALIZER_TEST_POINT" = marker_link ]; then
      # Hold the decision-to-marker window open so the probe can deliver a
      # signal that must lose against the already-linked decision.
      MARKER_PAUSE_ARGS=(
        --test-marker-pause-ready "$FINALIZER_TEST_READY"
        --test-marker-pause-release "$FINALIZER_TEST_RELEASE"
      )
    fi
    run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" complete-bundle --art-dir "$ART_DIR" \
      --manifest "$ART_DIR/manifest.json" --digest "$ART_DIR/manifest.digest" \
      --output "$ART_DIR/bundle.complete.json" --governed-root "$GOVERNED_ROOT" \
      "${GOVERNED_ARGS[@]}" --expected-root "$final_root" \
      "${BUNDLE_CONTEXT_ARGS[@]}" "${MARKER_PAUSE_ARGS[@]}" || true
    if ! finalizer_test_checkpoint post_decision; then publish_rc=2; fi
    if run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" adopt-bundle --art-dir "$ART_DIR" \
        --manifest "$ART_DIR/manifest.json" --digest "$ART_DIR/manifest.digest" \
        --commit "$ART_DIR/bundle.complete.json" --artifact-root "$ART_DIR" \
        >/dev/null; then
      # A complete decision is the logical winner. The named adoption operation
      # recovers its canonical marker if the publisher died before linking or
      # syncing it, then fully revalidates; validate-bundle itself stays
      # side-effect-free.
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

# Sealed build roots are per-run cold-build state (~8G each) that no later run
# ever reuses; unpruned they filled the disk twice on 2026-08-01 (bead
# franken_lean-bt75). A root is prunable only when the pid embedded in its
# RUN_ID is dead, so a live concurrent run's root is never touched; pid reuse
# merely defers that prune to a later run. Retained bundles under ART_ROOT name
# sealed paths as fact strings and nothing re-reads the tree, so pruning
# invalidates no published evidence. Best-effort by design: a failed prune is
# space hygiene lost, never a run obligation, and it runs before the evidence
# envelope opens so it adds no step to the finalizer state machine.
prune_dead_sealed_build_roots() {
  local parent="${FLN_CHECK_SEALED_BUILD_ROOT:-$REPO/target/sealed}"
  if [ ! -d "$parent" ]; then return 0; fi
  local root name pid
  for root in "$parent"/check-*-*; do
    if [ ! -d "$root" ]; then continue; fi
    name="${root##*/}"
    if [ "$name" = "$RUN_ID" ]; then continue; fi
    pid="${name##*-}"
    case "$pid" in '' | *[!0-9]*) continue ;; esac
    if [ -d "/proc/$pid" ]; then continue; fi
    rm -rf -- "$root" 2>/dev/null || true
  done
  return 0
}
if [ "${FLN_CHECK_KEEP_SEALED_ROOTS:-0}" != 1 ]; then
  prune_dead_sealed_build_roots
fi

# The evidence envelope starts at fresh artifact-directory acceptance: from
# here every step runs under the terminal/finalizer state machine and any
# fault still finalizes a typed durable partial bundle
# (bead fln-evidence-runner-bootstrap-btk).
EARLY_STEP=artifact_directory_creation
mkdir -p "$(dirname "$ART_DIR")"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  # The successful mkdir is the publisher-ownership linearization point. A
  # competing lane can observe the directory only after another process owns
  # it, so this process must disarm its finalizer and leave the winner untouched.
  trap - EXIT
  echo "[check] setup failure: evidence directory already claimed: $ART_DIR" >&2
  exit 2
fi
ART_DIR_CLAIMED=1
if [ "$EARLY_FAULT_PROBE" -eq 1 ] && [ "$TEST_EARLY_FAULT" = early_signal_hold ]; then
  # Deterministic early-signal window: the probe binds on the hold file and
  # delivers its signal while the envelope is still pre-run_start.
  : > "$ART_DIR/early.hold"
  for _ in $(seq 1 3000); do
    if [ -e "$ART_DIR/early.release" ]; then break; fi
    sleep 0.01
  done
fi
if [ "$FINALIZER_PROBE" -eq 1 ]; then
  EARLY_STEP=probe_control
  if [ "$EARLY_FAULT_PROBE" -eq 1 ] && [ "$TEST_EARLY_FAULT" = probe_control ]; then
    # A colliding regular file makes the real control mkdir below fail.
    : > "$FINALIZER_TEST_CONTROL"
  fi
  if [ -e "$FINALIZER_TEST_CONTROL" ] && [ ! -d "$FINALIZER_TEST_CONTROL" ]; then
    early_fault early_probe_control_failure "probe control path is not usable"
  fi
  if [ -d "$FINALIZER_TEST_CONTROL" ] || [ -L "$FINALIZER_TEST_CONTROL" ]; then
    early_fault early_probe_control_failure "refusing reused probe control directory"
  fi
  mkdir "$FINALIZER_TEST_CONTROL" \
    || early_fault early_probe_control_failure "cannot create probe control directory"
  printf 'finalizer-probe\n' > "$ART_DIR/probe-input"
  GOVERNED_ROOT="$ART_DIR"
  HASH_ARGS=(--path probe-input)
  GOVERNED_ARGS=(--governed-path probe-input)
  HASH_CONTEXT_ARGS=()
  BUNDLE_CONTEXT_ARGS=()
  UBS_INVENTORY_BINDING=not_applicable_finalizer_self_test
  VENDOR_BINDING_BINDING=not_applicable_finalizer_self_test
  if [ "$EARLY_FAULT_PROBE" -eq 1 ]; then
    # Deliberate early faults run the REAL commands against planted-real
    # obstructions (an output path occupied by a directory), so the failure
    # surface is the genuine write path, never a mock.
    case "$TEST_EARLY_FAULT" in
      ubs_inventory)
        EARLY_STEP=ubs_inventory
        mkdir "$UBS_INVENTORY"
        "${PYTHON[@]}" "$EVIDENCE" ubs-inventory --root "$ART_DIR" --scope all-tracked \
          --output "$UBS_INVENTORY" --artifact-root "$ART_DIR" \
          || early_fault early_ubs_inventory_failure "cannot inventory UBS inputs"
        early_fault early_ubs_inventory_failure "planted inventory collision did not fail"
        ;;
      vendor_binding)
        EARLY_STEP=vendor_binding
        mkdir "$VENDOR_BINDING"
        "${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ART_DIR" --vendor-path "$VENDOR_PATH" \
          --output "$VENDOR_BINDING" --artifact-root "$ART_DIR" \
          || early_fault early_vendor_binding_failure "cannot verify the pinned Reference tree"
        early_fault early_vendor_binding_failure "planted vendor collision did not fail"
        ;;
    esac
  fi
else
  EARLY_STEP=ubs_inventory
  "${PYTHON[@]}" "$EVIDENCE" ubs-inventory --root "$REPO" --scope "$UBS_SCOPE" \
    --output "$UBS_INVENTORY" --artifact-root "$ART_DIR" \
    || early_fault early_ubs_inventory_failure "cannot inventory UBS inputs"
  EARLY_STEP=vendor_binding
  "${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$REPO" --vendor-path "$VENDOR_PATH" \
    --output "$VENDOR_BINDING" --artifact-root "$ART_DIR" \
    || early_fault early_vendor_binding_failure "cannot verify the pinned Reference tree"
fi
EARLY_STEP=initial_hash
EARLY_HASH_ARGS=()
if [ "$EARLY_FAULT_PROBE" -eq 1 ] && [ "$TEST_EARLY_FAULT" = initial_hash ]; then
  # The planted mutation appends one byte to the probe's own governed input
  # while its snapshot is open — the ordinary stability law must fire.
  EARLY_HASH_ARGS=(--test-mutate-input probe-input)
fi
INPUT_ROOT="$("${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$GOVERNED_ROOT" \
  "${HASH_ARGS[@]}" "${HASH_CONTEXT_ARGS[@]}" "${EARLY_HASH_ARGS[@]}" \
  2>"$ART_DIR/initial-hash.err")" || {
  cat "$ART_DIR/initial-hash.err" >&2 || true
  if grep -q "changed while being read" "$ART_DIR/initial-hash.err" 2>/dev/null; then
    set_final inconclusive governed_input_mutation_during_initial_hash 3
    exit 3
  fi
  early_fault early_initial_hash_failure "cannot hash governed inputs"
}
EARLY_STEP=host_facts
HOST_FACTS_JSON="$("${PYTHON[@]}" - <<'PY'
import json, platform
print(json.dumps({
    "machine": platform.machine(),
    "python": platform.python_version(),
    "release": platform.release(),
    "system": platform.system(),
}, sort_keys=True, separators=(",", ":")))
PY
)" || early_fault early_host_facts_failure "cannot capture host facts"

EARLY_STEP=run_argv
RUN_ARGV_JSON="$("${PYTHON[@]}" - "${BASH_SOURCE[0]}" "${1:-}" <<'PY'
import json, sys
argv = [sys.argv[1]]
if sys.argv[2]:
    argv.append(sys.argv[2])
print(json.dumps(argv, separators=(",", ":")))
PY
)" || early_fault early_run_argv_failure "cannot capture the run argv"

EARLY_STEP=run_start_emission
if [ "$EARLY_FAULT_PROBE" -eq 1 ] && [ "$TEST_EARLY_FAULT" = run_start_emission ]; then
  # A directory at the log path makes the real append open fail typed.
  mkdir "$NDJSON"
fi
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
  --producer-binding-root "$REPO" "${GOVERNED_ARGS[@]}" \
  --string ubs_inventory "$UBS_INVENTORY_BINDING" \
  --string vendor_binding "$VENDOR_BINDING_BINDING" \
  --string verification_manifest "$VERIFICATION_MANIFEST_REL" \
  --json-value budgets "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"stage_timeout_ms\":$STAGE_TIMEOUT_MS,\"kill_grace_ms\":$KILL_GRACE_MS}" \
  --string rustc "$(rustc --version 2>/dev/null || printf unknown)" \
  --string planted "$PLANT_BINDING" \
  || early_fault early_run_start_emission_failure "cannot emit run_start"
EARLY_STEP=human_log
if [ "$EARLY_FAULT_PROBE" -eq 1 ] && [ "$TEST_EARLY_FAULT" = human_log ]; then
  mkdir "$HUMAN"
fi
: > "$HUMAN" || early_fault early_human_log_failure "cannot create the human log"
# From here the run log exists with its run_start, so the full finalizer owns
# terminal publication; the early-envelope partial machinery stands down.
RUN_STARTED=1

if [ "$FINALIZER_PROBE" -eq 1 ]; then
  ACTIVE_STAGE=finalizer-probe
  emit_event --string event self_test --string stage finalizer-probe \
    --boolean ok true --integer planted_exit 0 \
    --string artifact finalizer-probe
  if [ "$EARLY_FAULT_PROBE" -eq 1 ] && [ "$TEST_EARLY_FAULT" = post_run_start_drift ]; then
    # Deliberate concurrent source drift: the governed probe input mutates
    # after run_start, so final workspace hashing must type inconclusive.
    printf 'drift\n' >> "$ART_DIR/probe-input"
  fi
  if [ "$EARLY_FAULT_PROBE" -eq 1 ] && [ "$TEST_EARLY_FAULT" = post_run_start_abort ]; then
    # Deliberate internal fault after run_start: an unexpected shell exit
    # must still finalize a complete typed internal_fault bundle.
    exit 9
  fi
  set_final pass finalizer_probe_complete 0
  exit 0
fi

read_meta_field() {
  "${PYTHON[@]}" - "$1" "$2" <<'PY'
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

emit_not_run_after() {
  local failed_stage="$1" causal_reason="$2" stage seen=0
  for stage in "${CHECK_STAGE_ORDER[@]}"; do
    if [ "$seen" -eq 1 ]; then
      emit_event --string event stage --string stage "$stage" \
        --string outcome not_run --string reason_code blocked_by_prior_stage \
        --string expected not_run --string actual not_run \
        --string causal_stage "$failed_stage" \
        --string causal_reason "$causal_reason"
      note "not_run stage=$stage causal_stage=$failed_stage reason=$causal_reason"
    fi
    if [ "$stage" = "$failed_stage" ]; then seen=1; fi
  done
  if [ "$seen" -ne 1 ]; then
    set_final internal_fault unknown_failed_stage 2
    exit 2
  fi
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
  elif [ "$PLANT_UNEXPECTED" = "$name" ]; then
    # Deliberate unexpected-failure scenario (bead
    # fln-evidence-runner-bootstrap-btk): an exit code outside the stage's
    # registered semantic set must type as internal_fault, never as a
    # semantic stage failure.
    argv=(sh -c 'exit 7')
    planted=true
    semantic_args=()
  else
    case "$name" in
      verification-manifest|shellcheck|fmt|contract-handoff-no-mock|\
        tribunal-manifest-inventory|projection-guard-harness|\
        ubs-gate-classifier|\
        epoch-lab-live-verify|structure-guard|vendor-tree|ubs)
        semantic_args=(--semantic-failure-exit 1)
        ;;
      check|clippy|test|epoch-lab-test)
        semantic_args=(--semantic-failure-exit 101)
        ;;
    esac
  fi
  # Cargo-invoking stages run under the sealed compiler environment: hostile
  # ambient channels are rejected typed, the SUITE.lock-pinned toolchain
  # identity is verified, and build state is isolated per attempt.
  local -a sealed_args=()
  case "$name" in
    fmt|check|clippy|test|epoch-lab-test|epoch-lab-live-verify|structure-guard)
      sealed_args=(--sealed-cargo --suite-lock "$REPO/SUITE.lock"
        --sealed-build-root "$SEALED_BUILD_ROOT")
      ;;
  esac
  note "stage=$name: ${argv[*]}"
  local -a runner=("${PYTHON[@]}" "$EVIDENCE" run
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
    --stage-id "$name" "${semantic_args[@]}" "${sealed_args[@]}")
  [ "$planted" = true ] && runner+=(--planted)
  runner+=(-- "${argv[@]}")
  SPAWNING=1
  setsid -- "${runner[@]}" &
  ACTIVE_RUNNER_PID=$!
  if ! ACTIVE_RUNNER_START_TICKS="$(
    setsid -- "${PYTHON[@]}" "$EVIDENCE" process-start-ticks --pid "$ACTIVE_RUNNER_PID" \
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
    emit_not_run_after "$name" missing_supervisor_metadata
    set_final internal_fault missing_supervisor_metadata 2
    exit 2
  fi
  classification="$(read_meta_field "$meta" classification)"
  reason="$(read_meta_field "$meta" reason_code)"
  recorded_wrapper="$(read_meta_field "$meta" wrapper_exit)"
  if [ "$recorded_wrapper" != "$wrapper_rc" ]; then
    emit_event \
      --string event stage \
      --string stage "$name" \
      --string outcome internal_fault \
      --string reason_code wrapper_exit_mismatch \
      --string expected supervisor_wrapper_exit \
      --string actual shell_wrapper_exit_mismatch \
      --integer wrapper_exit "$wrapper_rc" \
      --json-file supervisor "$meta"
    emit_not_run_after "$name" wrapper_exit_mismatch
    set_final internal_fault "$name:wrapper_exit_mismatch" 2
    exit 2
  fi
  if [ "$wrapper_rc" -eq 0 ] && [ "$classification" = pass ]; then
    if [ "$name" = contract-handoff-no-mock ] \
      && [ "$(read_meta_field "$CENSUS_AVAILABILITY_RECEIPT" outcome)" = inconclusive ]; then
      skip_stage "$name" "$CENSUS_SKIP_LIMITATION"
      return 0
    fi
    emit_event \
      --string event stage \
      --string stage "$name" \
      --string outcome "$classification" \
      --string reason_code "$reason" \
      --string expected exit_zero \
      --string actual "$classification" \
      --integer wrapper_exit "$wrapper_rc" \
    --json-file supervisor "$meta"
    note "ok stage=$name"
    return 0
  fi
  emit_event \
    --string event stage \
    --string stage "$name" \
    --string outcome "$classification" \
    --string reason_code "$reason" \
    --string expected exit_zero \
    --string actual "$classification" \
    --integer wrapper_exit "$wrapper_rc" \
    --json-file supervisor "$meta"
  note "$classification stage=$name reason=$reason wrapper_exit=$wrapper_rc"
  note "captured stderr tail follows ($name)"
  tail -n 40 "$err" >&2 || true
  emit_not_run_after "$name" "$reason"
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
  local wrapper_launch_ready wrapper_launch_release cancel_meta
  for stage in "${CHECK_STAGE_ORDER[@]}"; do
    echo "[check:self-test] planting failure in stage=$stage" >&2
    child="$ART_DIR/selftest-$stage"
    wrapper_ready="$ART_DIR/selftest-$stage.guardian.ready.json"
    wrapper_launch_ready="$ART_DIR/selftest-$stage.guardian.launch.ready.json"
    wrapper_launch_release="$ART_DIR/selftest-$stage.guardian.launch.release.json"
    ACTIVE_STAGE="selftest-$stage"
    SPAWNING=1
    setsid -- "${PYTHON[@]}" "$EVIDENCE" run --cwd "$REPO" \
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
      setsid -- "${PYTHON[@]}" "$EVIDENCE" process-start-ticks --pid "$child_pid" \
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
    if [ "$rc" -eq 1 ] && "${PYTHON[@]}" "$EVIDENCE" validate-run \
      --file "$child/run.ndjson" --schema "$SCHEMA" --expected-verdict fail \
      --expected-active-stage "$stage" --expected-planted-stage "$stage" \
      --artifact-root "$ART_DIR" --output "$ART_DIR/selftest-$stage.validation.json" \
      && "${PYTHON[@]}" "$EVIDENCE" validate-bundle --art-dir "$child" \
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
  cancel_meta="$ART_DIR/selftest-cancel-term.guardian.meta.json"
  ACTIVE_STAGE=selftest-cancel-term
  SPAWNING=1
  setsid -- "${PYTHON[@]}" "$EVIDENCE" run --cwd "$REPO" \
    --metadata "$cancel_meta" \
    --stdout "$ART_DIR/selftest-cancel-term.console.out" \
    --stderr "$ART_DIR/selftest-cancel-term.console.err" \
    --readiness "$wrapper_ready" \
    --launch-ready "$wrapper_launch_ready" \
    --launch-release "$wrapper_launch_release" \
    --artifact-root "$ART_DIR" \
    --capture-bytes "$CAPTURE_BYTES" --output-budget-bytes "$OUTPUT_BUDGET_BYTES" \
    --timeout-ms "$STAGE_TIMEOUT_MS" --grace-ms 180000 \
    --stage-id selftest-cancel-term -- \
    env FLN_CHECK_ART_DIR="$child" FLN_CHECK_PROFILE=self-test-cancellation \
      bash "${BASH_SOURCE[0]}" &
  child_pid=$!
  ACTIVE_RUNNER_PID="$child_pid"
  if ! ACTIVE_RUNNER_START_TICKS="$(
    setsid -- "${PYTHON[@]}" "$EVIDENCE" process-start-ticks --pid "$child_pid" \
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
  local child_stage_ready="$child/evidence-self-test.ready.json"
  for _ in $(seq 1 $((READY_WAIT_MS / 20))); do
    if [ -s "$child_stage_ready" ]; then break; fi
    sleep 0.02
  done
  if [ ! -s "$child_stage_ready" ]; then
    stop_active_runner TERM || true
    rc=2
  elif ! "${PYTHON[@]}" "$EVIDENCE" signal-bound-process --pid "$child_pid" \
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
  if [ "$rc" -eq 4 ] \
    && [ "$(read_meta_field "$cancel_meta" classification)" = cancelled ] \
    && [ "$(read_meta_field "$cancel_meta" wrapper_exit)" = 4 ] \
    && [ "$(read_meta_field "$cancel_meta" child_exit)" = 143 ] \
    && "${PYTHON[@]}" "$EVIDENCE" validate-run \
    --file "$child/run.ndjson" --schema "$SCHEMA" --expected-verdict cancelled \
    --artifact-root "$ART_DIR" --output "$ART_DIR/selftest-cancel-term.validation.json" \
    && "${PYTHON[@]}" "$EVIDENCE" validate-bundle --art-dir "$child" \
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
run_stage evidence-self-test "${PYTHON[@]}" scripts/evidence.py self-test \
  --art-dir "$ART_DIR/evidence-self-test"
run_stage verification-manifest "${PYTHON[@]}" scripts/evidence.py \
  validate-verification-manifest --manifest "$VERIFICATION_MANIFEST" \
  --beads "$REPO/.beads/issues.jsonl"
run_stage shellcheck shellcheck scripts/check.sh scripts/lib/gate_lock.sh \
  scripts/verify_vendor_tree.sh \
  scripts/e2e/structure_gate.sh scripts/e2e/closure_audit.sh scripts/e2e/structural_gate.sh \
  scripts/e2e/core_observables.sh scripts/extract/gen_core_fixtures.sh \
  scripts/extract/gen_core_ext_fixtures.sh \
  scripts/e2e/hash_identity.sh scripts/e2e/diag_goldens.sh \
  scripts/e2e/env_snapshots.sh scripts/e2e/bignum_vectors.sh \
  scripts/e2e/campaign_frameworks.sh scripts/e2e/attribute_state_census.sh \
  scripts/e2e/contract_drift.sh scripts/e2e/contract_handoff.sh \
  scripts/e2e/olean_resurrection.sh \
  scripts/extract/gen_extern_census.sh scripts/extract/census_materialize.sh \
  scripts/e2e/kernel_replay.sh scripts/e2e/lexer_no_mock_e2e.sh \
  scripts/e2e/parser_corpus_no_mock_e2e.sh \
  scripts/e2e/dynamic_parser_no_mock_e2e.sh \
  scripts/e2e/suite_upgrade_candidate_preflight.sh \
  scripts/e2e/suite_upgrade_no_mock_e2e.sh \
  scripts/e2e/hygiene_no_mock_e2e.sh \
  scripts/e2e/macro_txn_no_mock_e2e.sh \
  scripts/e2e/cartridge_no_mock_e2e.sh \
  scripts/e2e/certificate_format_no_mock_e2e.sh \
  scripts/e2e/g0_4_no_mock_e2e.sh \
  scripts/e2e/vellum_naming_no_mock_e2e.sh \
  scripts/e2e/verdict_schema.sh scripts/e2e/unsafe_note_clippy.sh \
  scripts/tribunal/leanchecker_witness.sh \
  scripts/tribunal/gen_epoch_manifest.sh scripts/tribunal/ref_vs_ref.sh \
  scripts/git-hooks/pre-commit scripts/git-hooks/install.sh \
  scripts/git-hooks/test_projection_guard.sh \
  scripts/ubs_gate_classifier.sh scripts/test_ubs_gate_classifier.sh
# The projection, verification-coverage and D3 root-attribute guards in
# scripts/git-hooks/pre-commit are proved by scripts/git-hooks/test_projection_guard.sh,
# which until now was shellchecked directly above and EXECUTED BY NOTHING — named in
# INPUT_PATHS and in that shellcheck list, invoked nowhere in this repository. That is the
# documented-command-nobody-invokes shape sitting inside the feedback-loop closer it exists
# to prove (beads franken_lean-projection-republish-mechanical-voz4 and
# franken_lean-d3-root-attr-no-creation-affordance-sso4). Registration is the part that
# matters: a script can sit in the tree unrun for months, which this one did.
#
# A stage rather than an fln.e2e/2 lane, deliberately: the harness takes no gate lock and
# runs in about a second, so cheap-and-always-on beats correct-and-quarterly.
#
# The publisher is a deliberately NESTED workspace, so `cargo build -p` cannot reach it and
# the hook's own candidate search is repeated here. That is binary-path resolution, not a
# second copy of the projection predicate — that stays in the publisher, which is the whole
# reason the guard shells out to it instead of recomputing the hash.
PROJECTION_PUBLISHER=""
for publisher_candidate in \
  "${CARGO_TARGET_DIR:-$REPO/target}/debug/kernel-ownership-publisher" \
  "${CARGO_TARGET_DIR:-$REPO/target}/release/kernel-ownership-publisher" \
  "$REPO/tools/structure-guard/kernel-ownership-publisher/target/debug/kernel-ownership-publisher"; do
  if [ -x "$publisher_candidate" ]; then PROJECTION_PUBLISHER="$publisher_candidate"; break; fi
done
if [ -z "$PROJECTION_PUBLISHER" ]; then
  note "building kernel-ownership-publisher once for the projection-guard harness"
  (cd "$REPO/tools/structure-guard/kernel-ownership-publisher" && cargo build --quiet) || true
  for publisher_candidate in \
    "${CARGO_TARGET_DIR:-$REPO/target}/debug/kernel-ownership-publisher" \
    "$REPO/tools/structure-guard/kernel-ownership-publisher/target/debug/kernel-ownership-publisher"; do
    if [ -x "$publisher_candidate" ]; then PROJECTION_PUBLISHER="$publisher_candidate"; break; fi
  done
fi
# An absent publisher leaves this empty, the harness refuses with exit 2, and run_stage types
# that as an internal_fault rather than a semantic failure — an environment fault is not a
# finding about the code (FL-INV-07).
# The UBS terminal classifier is proved here for the same reason the projection guard is: a
# guard that is shellchecked and executed by nothing is the documented-command-nobody-invokes
# shape. Its two-way control is the load-bearing one — a timeout must type as a non-answer AND
# a genuine critical must still type as a rejection — because a classifier that stopped blocking
# on everything would satisfy the first half and silence every real finding.
run_stage ubs-gate-classifier bash "$REPO/scripts/test_ubs_gate_classifier.sh" \
  "$REPO/scripts/ubs_gate_classifier.sh"
run_stage projection-guard-harness bash "$REPO/scripts/git-hooks/test_projection_guard.sh" \
  "$REPO/scripts/git-hooks/pre-commit" \
  "$PROJECTION_PUBLISHER" \
  "$EVIDENCE" \
  "$VERIFICATION_MANIFEST" \
  "$REPO/.beads/issues.jsonl"
run_stage fmt cargo fmt --check
run_stage check cargo check --locked --all-targets
run_stage clippy cargo clippy --locked --all-targets -- -D warnings
run_stage contract-handoff-no-mock "${PYTHON[@]}" "$EVIDENCE" \
  classify-census-availability --root "$REPO" \
  --output "$CENSUS_AVAILABILITY_RECEIPT" --artifact-root "$ART_DIR"
CENSUS_AVAILABILITY="$(read_meta_field "$CENSUS_AVAILABILITY_RECEIPT" outcome)"
case "$CENSUS_AVAILABILITY" in
  available)
    run_stage test cargo test --locked
    ;;
  inconclusive)
    census_test_args=()
    for census_test in "${CENSUS_NO_MOCK_TESTS[@]}"; do
      census_test_args+=(--skip "$census_test")
    done
    run_stage test cargo test --locked -- "${census_test_args[@]}"
    ;;
  *)
    set_final internal_fault census_availability_receipt_invalid 2
    exit 2
    ;;
esac
run_stage tribunal-manifest-inventory \
  bash scripts/check.sh --tribunal-manifest-inventory
run_stage epoch-lab-test cargo test --locked \
  --manifest-path tribunal/epoch-lab/Cargo.toml
# The live verifier reserves exit 1 for a semantic chain mismatch. Its exit 2
# is a typed absent-epoch non-answer and intentionally remains non-semantic here,
# so the enclosing gate cannot misreport an inconclusive oracle as rejection.
run_stage epoch-lab-live-verify cargo run --locked \
  --manifest-path tribunal/epoch-lab/Cargo.toml -- verify v4.32.0
if [ "$CENSUS_AVAILABILITY" = available ]; then
  run_stage structure-guard cargo run -q --locked -p structure-guard -- \
    --root "$REPO" --robot
else
  run_stage structure-guard "${PYTHON[@]}" "$EVIDENCE" \
    exec-structure-guard-census-inconclusive --root "$REPO" \
    --receipt "$CENSUS_AVAILABILITY_RECEIPT" \
    --output "$ART_DIR/structure-guard.census-inconclusive.ndjson" \
    --validation "$ART_DIR/structure-guard.census-inconclusive.validation.json" \
    --artifact-root "$ART_DIR"
fi
run_stage vendor-tree bash scripts/verify_vendor_tree.sh

# The exact file set was materialized before run_start and is part of INPUT_ROOT.
"${PYTHON[@]}" "$EVIDENCE" validate-ubs-inventory --root "$REPO" \
  --inventory "$UBS_INVENTORY" >/dev/null
UBS_COUNT="$(read_meta_field "$UBS_INVENTORY" count)"
if [ "$PLANT" = ubs ]; then
  run_stage ubs ubs --version
elif command -v ubs >/dev/null 2>&1; then
  if [ "$UBS_COUNT" -gt 0 ]; then
    # The `--` target is the CLASSIFIER, not `ubs` itself, and that indirection is the whole
    # repair (bead fln-ubs-timeout-promoted-to-rejection-pekl). `ubs --ci` exits 1 for BOTH a
    # genuine critical finding and a scanner MODULE_TIMEOUT, so registering it directly against
    # --semantic-failure-exit 1 renders resource exhaustion as a REJECTION — an FL-INV-07
    # violation in a lane whose own run_start declares FL-INV-07. exec-ubs-inventory execs its
    # target with the validated paths appended. The classifier partitions the admitted .py/.rs
    # inputs, dispatches exactly one language module at a time in Python-then-Rust order, requires
    # each module to identify its scanner and account for its exact intended file count, and only
    # then aggregates their terminal MESSAGE TEXT. It exits 1 ONLY for completed_findings. Every
    # non-answer exits 2, which is outside this stage's semantic set and therefore types
    # internal_fault rather than fail.
    run_stage ubs "${PYTHON[@]}" "$EVIDENCE" exec-ubs-inventory \
      --root "$REPO" --inventory "$UBS_INVENTORY" -- \
      bash "$REPO/scripts/ubs_gate_classifier.sh"
    "${PYTHON[@]}" "$EVIDENCE" validate-ubs-inventory --root "$REPO" \
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
