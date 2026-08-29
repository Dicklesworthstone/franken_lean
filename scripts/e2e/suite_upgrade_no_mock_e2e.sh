#!/usr/bin/env bash
# Real no-mock suite-upgrade lane (bead fln-h25). Builds an isolated candidate
# *outside* the authoritative checkout, proves incomplete evidence cannot
# publish, proves a complete closure/contract/Tribunal/migration/rollback join
# can, plants cancellation, a hidden suite dependency, and a stale Tribunal
# root and proves each refuse, restores, and proves SUITE.lock is
# byte-identical to the start.
# The preflight helper remains the identity+content join; this script is the
# fln.e2e/2 evidence producer.

set -Eeuo pipefail

PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  printf '[suite_upgrade_no_mock_e2e] setup failure: python3 is required\n' >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
for required_command in cargo sha256sum setsid; do
  command -v "$required_command" >/dev/null 2>&1 || {
    printf '[suite_upgrade_no_mock_e2e] setup failure: %s is required\n' \
      "$required_command" >&2
    exit 2
  }
done

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
cd "$ROOT"
EVIDENCE="$ROOT/scripts/evidence.py"
PREFLIGHT="$ROOT/scripts/e2e/suite_upgrade_candidate_preflight.sh"
BEAD="fln-h25"
SCENARIO="suite_upgrade_no_mock_e2e"
RUN_ID="suite-upgrade-$(date -u +%Y%m%dt%H%M%Sz)-$$"
ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
VENDOR_BINDING="$ART_DIR/vendor-binding.json"
BUILD_TARGET="${CARGO_TARGET_DIR:-$ROOT/target/cargo}/e2e-suite-upgrade"
CAPTURE_BYTES="${FLN_E2E_CAPTURE_BYTES:-1048576}"
OUTPUT_BUDGET_BYTES="${FLN_E2E_OUTPUT_BUDGET_BYTES:-16777216}"
TIMEOUT_MS="${FLN_E2E_TIMEOUT_MS:-600000}"
GRACE_MS="${FLN_E2E_KILL_GRACE_MS:-2000}"
START_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
SEQ=0
CANDIDATE_DIR=""

INPUT_PATHS=(
  Cargo.toml Cargo.lock SUITE.lock rust-toolchain.toml
  crates/fln-conformance
  scripts/e2e/suite_upgrade_no_mock_e2e.sh
  scripts/e2e/suite_upgrade_candidate_preflight.sh
  scripts/evidence.py
  scripts/check.sh
  .github/workflows/contract-drift.yml
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
  printf '[suite_upgrade_no_mock_e2e] setup failure: artifact path is not fresh: %s\n' \
    "$ART_DIR" >&2
  exit 2
fi

"${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" \
  --vendor-path vendor/lean4-src --output "$VENDOR_BINDING" \
  --artifact-root "$ART_DIR" || {
    printf '[suite_upgrade_no_mock_e2e] setup failure: cannot bind vendored Reference\n' >&2
    exit 2
  }
INPUT_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path vendor/lean4-src
)" || {
  printf '[suite_upgrade_no_mock_e2e] setup failure: cannot hash inputs\n' >&2
  exit 2
}
AUTHORITATIVE_LOCK_ROOT="$(sha256sum -- "$ROOT/SUITE.lock")"
AUTHORITATIVE_LOCK_ROOT="${AUTHORITATIVE_LOCK_ROOT%% *}"
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

digest_file() {
  local digest_line
  digest_line="$(sha256sum -- "$1")" || return
  printf '%s\n' "${digest_line%% *}"
}

write_receipt() {
  local dest="$1"
  "${PYTHON[@]}" - "$dest" \
    "$RUN_ID" \
    "$OLD_LOCK_ROOT" \
    "$CANDIDATE_LOCK_ROOT" \
    "$CLOSURE_ROOT" \
    "$CONTRACT_CENSUS_ROOT" \
    "$TRIBUNAL_ROOT" \
    "$MIGRATION_ROOT" \
    "$ROLLBACK_ROOT" \
    "$EXTERNAL_EVIDENCE_ROOT" <<'PY'
import pathlib
import sys

(
    dest,
    run_id,
    old_lock_root,
    candidate_lock_root,
    closure_root,
    contract_census_root,
    tribunal_root,
    migration_root,
    rollback_root,
    external_evidence_root,
) = sys.argv[1:]
pathlib.Path(dest).write_text(
    '{"schema":"fln-suite-upgrade-candidate/2"'
    f',"run_id":"{run_id}"'
    ',"candidate_id":"isolated-upgrade-candidate"'
    ',"component_id":"suite-lock"'
    ',"ledger_transition_id":"upgrade-isolated"'
    ',"change":"upgrade"'
    f',"old_lock_root":"{old_lock_root}"'
    f',"candidate_lock_root":"{candidate_lock_root}"'
    f',"closure_root":"{closure_root}"'
    f',"contract_and_census_root":"{contract_census_root}"'
    f',"tribunal_root":"{tribunal_root}"'
    f',"migration_root":"{migration_root}"'
    f',"rollback_root":"{rollback_root}"'
    f',"external_evidence_root":"{external_evidence_root}"'
    ',"expected_stage":"complete-evidence-join"'
    ',"actual_stage":"complete-evidence-join"'
    ',"rollback_outcome":"rollback-proven"'
    ',"publication_authority":"current-lock-retained"'
    ',"cleanup":"candidate-retained"'
    f',"final_current_lock_root":"{old_lock_root}"'
    "}\n",
    encoding="utf-8",
)
PY
}

write_closure() {
  local dest="$1"
  local lock="$2"
  "${PYTHON[@]}" - "$dest" "$lock" <<'PY'
import pathlib
import sys

dest, lock_path = sys.argv[1], sys.argv[2]
names = []
for line in pathlib.Path(lock_path).read_text(encoding="utf-8").splitlines():
    stripped = line.strip()
    if stripped.startswith("suite "):
        name = stripped.split()[1]
        if name not in names:
            names.append(name)
body = ["schema fln-suite-upgrade-closure/1"]
body.extend(f"component {name}" for name in names)
pathlib.Path(dest).write_text("\n".join(body) + "\n", encoding="utf-8")
PY
}

write_evidence_file() {
  local dest="$1"
  local schema="$2"
  local payload="$3"
  printf '{"schema":"%s","candidate_id":"isolated-upgrade-candidate","payload":"%s"}\n' \
    "$schema" "$payload" >"$dest"
}

refresh_roots_from_candidate() {
  CANDIDATE_LOCK_ROOT="$(digest_file "$CANDIDATE_DIR/SUITE.lock")"
  CLOSURE_ROOT="$(digest_file "$CANDIDATE_DIR/closure.ndjson")"
  CONTRACT_CENSUS_ROOT="$(digest_file "$CANDIDATE_DIR/contract-census.ndjson")"
  TRIBUNAL_ROOT="$(digest_file "$CANDIDATE_DIR/tribunal.ndjson")"
  MIGRATION_ROOT="$(digest_file "$CANDIDATE_DIR/migration.ndjson")"
  ROLLBACK_ROOT="$(digest_file "$CANDIDATE_DIR/rollback.ndjson")"
  EXTERNAL_EVIDENCE_ROOT="$(digest_file "$CANDIDATE_DIR/external-evidence.ndjson")"
}

check_input_root() {
  local step="$1"
  local final_root
  final_root="$(
    "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
      --vendor-path vendor/lean4-src
  )" || {
    printf '[suite_upgrade_no_mock_e2e] internal fault: cannot hash %s final inputs\n' \
      "$step" >&2
    exit 2
  }
  if [ "$final_root" != "$INPUT_ROOT" ]; then
    printf '[suite_upgrade_no_mock_e2e] inconclusive: governed inputs changed in %s\n' \
      "$step" >&2
    exit 3
  fi
}

run_step() {
  local step="$1"
  shift
  local metadata="$ART_DIR/$step.meta.json"
  local stdout="$ART_DIR/$step.out"
  local stderr="$ART_DIR/$step.err"
  local readiness="$ART_DIR/$step.ready.json"
  local validation="$ART_DIR/$step.validation.json"
  local wrapper_rc=0

  printf '[suite_upgrade_no_mock_e2e] running %s\n' "$step" >&2
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
      printf '[suite_upgrade_no_mock_e2e] internal fault: invalid supervisor envelope for %s\n' \
        "$step" >&2
      exit 2
    }
  if [ "$wrapper_rc" -ne 0 ]; then
    printf '[suite_upgrade_no_mock_e2e] refused: %s exited %s; logs=%s\n' \
      "$step" "$wrapper_rc" "$ART_DIR" >&2
    exit "$wrapper_rc"
  fi
  check_input_root "$step"
  emit_event --string event step --string step_id "$step" \
    --string assertion pass --string expected exit_zero \
    --string actual pass --string input_root "$INPUT_ROOT" \
    --string final_state "$INPUT_ROOT" \
    --string validation_artifact "$step.validation.json" \
    --string expected_supervisor_classification pass \
    --integer expected_wrapper_exit 0 --integer expected_child_exit 0 \
    --string subject_root "$INPUT_ROOT" \
    --string subject_final_state "$INPUT_ROOT" \
    --string candidate_dir "$CANDIDATE_DIR" \
    --string old_lock_root "$OLD_LOCK_ROOT" \
    --string candidate_lock_root "$CANDIDATE_LOCK_ROOT" \
    --json-file supervisor "$metadata"
}

run_expected_failure() {
  local step="$1"
  local expected_wrapper="$2"
  local expected_child="$3"
  shift 3
  local metadata="$ART_DIR/$step.meta.json"
  local stdout="$ART_DIR/$step.out"
  local stderr="$ART_DIR/$step.err"
  local readiness="$ART_DIR/$step.ready.json"
  local validation="$ART_DIR/$step.validation.json"
  local wrapper_rc=0

  printf '[suite_upgrade_no_mock_e2e] running %s (expected wrapper %s child %s)\n' \
    "$step" "$expected_wrapper" "$expected_child" >&2
  setsid -- "${PYTHON[@]}" "$EVIDENCE" run --cwd "$ROOT" \
    --metadata "$metadata" --stdout "$stdout" --stderr "$stderr" \
    --readiness "$readiness" --artifact-root "$ART_DIR" \
    --capture-bytes "$CAPTURE_BYTES" \
    --output-budget-bytes "$OUTPUT_BUDGET_BYTES" \
    --timeout-ms "$TIMEOUT_MS" --grace-ms "$GRACE_MS" \
    --semantic-failure-exit "$expected_child" --stage-id "$step" -- "$@" \
    || wrapper_rc=$?
  "${PYTHON[@]}" "$EVIDENCE" validate-supervisor --file "$metadata" \
    --expected-stage-id "$step" --artifact-root "$ART_DIR" \
    --output "$validation" || {
      printf '[suite_upgrade_no_mock_e2e] internal fault: invalid failure envelope for %s\n' \
        "$step" >&2
      exit 2
    }
  if [ "$wrapper_rc" -ne "$expected_wrapper" ]; then
    printf '[suite_upgrade_no_mock_e2e] internal fault: %s expected wrapper %s, got %s\n' \
      "$step" "$expected_wrapper" "$wrapper_rc" >&2
    exit 2
  fi
  check_input_root "$step"
  emit_event --string event step --string step_id "$step" \
    --string assertion pass --string expected "semantic_failure_exit_${expected_child}" \
    --string actual expected_refusal --string input_root "$INPUT_ROOT" \
    --string final_state "$INPUT_ROOT" \
    --string validation_artifact "$step.validation.json" \
    --string expected_supervisor_classification fail \
    --integer expected_wrapper_exit "$expected_wrapper" \
    --integer expected_child_exit "$expected_child" \
    --string subject_root "$INPUT_ROOT" \
    --string subject_final_state "$INPUT_ROOT" \
    --string candidate_dir "$CANDIDATE_DIR" \
    --string old_lock_root "$OLD_LOCK_ROOT" \
    --string candidate_lock_root "$CANDIDATE_LOCK_ROOT" \
    --json-file supervisor "$metadata"
}

emit_event --new-log --string event run_start \
  --json-value argv '["scripts/e2e/suite_upgrade_no_mock_e2e.sh"]' \
  --string cwd "$ROOT" \
  --append-string claim_ids FLN-H25-SUITE-UPGRADE-NO-MOCK \
  --append-string invariant_ids FL-INV-07 \
  --append-string gate_ids W1 \
  --string parity_ledger_row not_applicable_w1_lock_protocol \
  --string epoch lean-v4.32.0 --string mode faithful \
  --string profile e2e --string platform "$(uname -srm)" \
  --integer thread_count 1 --string seed suite-upgrade-isolated-v1 \
  --string cache_state "${FLN_E2E_CACHE_STATE:-uncontrolled}" \
  --string input_root "$INPUT_ROOT" \
  --string vendor_binding vendor-binding.json \
  --producer-binding-root "$ROOT" "${GOVERNED_ARGS[@]}" \
  --json-value host_facts "$HOST_FACTS_JSON" \
  --json-value budgets \
    "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$TIMEOUT_MS,\"kill_grace_ms\":$GRACE_MS}"

# Isolated candidate lives outside the checkout. Overlap with ROOT is a
# preflight refusal. Default `/tmp` exists on GitHub runners and on this host;
# FLN_SUITE_UPGRADE_SCRATCH overrides when a caller needs a different root.
CANDIDATE_DIR="${FLN_SUITE_UPGRADE_SCRATCH:-/tmp}/${RUN_ID}-candidate"
if ! mkdir "$CANDIDATE_DIR" 2>/dev/null; then
  printf '[suite_upgrade_no_mock_e2e] setup failure: candidate path is not fresh: %s\n' \
    "$CANDIDATE_DIR" >&2
  exit 2
fi

OLD_LOCK_ROOT="$AUTHORITATIVE_LOCK_ROOT"
cp -- "$ROOT/SUITE.lock" "$CANDIDATE_DIR/SUITE.lock"
printf '\n# isolated-candidate-marker %s\n' "$RUN_ID" >>"$CANDIDATE_DIR/SUITE.lock"
write_closure "$CANDIDATE_DIR/closure.ndjson" "$CANDIDATE_DIR/SUITE.lock"
write_evidence_file "$CANDIDATE_DIR/contract-census.ndjson" \
  "fln-suite-upgrade-contract-census/1" "contract-census-${RUN_ID}"
write_evidence_file "$CANDIDATE_DIR/tribunal.ndjson" \
  "fln-suite-upgrade-tribunal/1" "tribunal-${RUN_ID}"
write_evidence_file "$CANDIDATE_DIR/migration.ndjson" \
  "fln-suite-upgrade-migration/1" "migration-${RUN_ID}"
write_evidence_file "$CANDIDATE_DIR/rollback.ndjson" \
  "fln-suite-upgrade-rollback/1" "rollback-${RUN_ID}"
write_evidence_file "$CANDIDATE_DIR/external-evidence.ndjson" \
  "fln-suite-upgrade-external/1" "external-${RUN_ID}"
refresh_roots_from_candidate
write_receipt "$CANDIDATE_DIR/candidate-receipt.ndjson"
if [ "$OLD_LOCK_ROOT" = "$CANDIDATE_LOCK_ROOT" ]; then
  printf '[suite_upgrade_no_mock_e2e] internal fault: isolated candidate did not change the lock root\n' >&2
  exit 2
fi
printf '[suite_upgrade_no_mock_e2e] isolated candidate at %s\n' "$CANDIDATE_DIR" >&2
run_step isolate_candidate \
  test -s "$CANDIDATE_DIR/candidate-receipt.ndjson" \
  -a -s "$CANDIDATE_DIR/SUITE.lock" \
  -a "$OLD_LOCK_ROOT" != "$CANDIDATE_LOCK_ROOT"

run_step failure_list \
  env CANDIDATE_DIR="$CANDIDATE_DIR" PREFLIGHT="$PREFLIGHT" bash -c '
set -euo pipefail
artifacts=(
  SUITE.lock
  candidate-receipt.ndjson
  closure.ndjson
  contract-census.ndjson
  tribunal.ndjson
  migration.ndjson
  rollback.ndjson
  external-evidence.ndjson
)
for artifact in "${artifacts[@]}"; do
  mv -- "$CANDIDATE_DIR/$artifact" "$CANDIDATE_DIR/$artifact.aside"
  rc=0
  FLN_SUITE_UPGRADE_CANDIDATE_DIR="$CANDIDATE_DIR" "$PREFLIGHT" || rc=$?
  mv -- "$CANDIDATE_DIR/$artifact.aside" "$CANDIDATE_DIR/$artifact"
  if [ "$rc" -eq 0 ]; then
    printf "omitting %s still published\n" "$artifact" >&2
    exit 1
  fi
  printf "omitting %s refused with exit %s\n" "$artifact" "$rc"
done
'

run_step complete_evidence_pass \
  env FLN_SUITE_UPGRADE_CANDIDATE_DIR="$CANDIDATE_DIR" \
    CARGO_TARGET_DIR="$BUILD_TARGET" \
    "$PREFLIGHT"

run_expected_failure cancelled_candidate_refused 1 101 \
  env FLN_SUITE_UPGRADE_CANCELLED=1 \
    FLN_SUITE_UPGRADE_CANDIDATE_DIR="$CANDIDATE_DIR" \
    CARGO_TARGET_DIR="$BUILD_TARGET" \
    "$PREFLIGHT"

cp -- "$CANDIDATE_DIR/SUITE.lock" "$CANDIDATE_DIR/SUITE.lock.aside"
cp -- "$CANDIDATE_DIR/candidate-receipt.ndjson" "$CANDIDATE_DIR/candidate-receipt.ndjson.aside"
printf 'suite undeclared-hidden commit=0000000000000000000000000000000000000000 path=/tmp/undeclared-hidden\n' \
  >>"$CANDIDATE_DIR/SUITE.lock"
refresh_roots_from_candidate
write_receipt "$CANDIDATE_DIR/candidate-receipt.ndjson"
run_expected_failure hidden_dependency_refused 1 101 \
  env FLN_SUITE_UPGRADE_CANDIDATE_DIR="$CANDIDATE_DIR" \
    CARGO_TARGET_DIR="$BUILD_TARGET" \
    "$PREFLIGHT"
mv -- "$CANDIDATE_DIR/SUITE.lock.aside" "$CANDIDATE_DIR/SUITE.lock"
mv -- "$CANDIDATE_DIR/candidate-receipt.ndjson.aside" "$CANDIDATE_DIR/candidate-receipt.ndjson"
refresh_roots_from_candidate

cp -- "$CANDIDATE_DIR/tribunal.ndjson" "$CANDIDATE_DIR/tribunal.ndjson.aside"
printf '{"schema":"fln-suite-upgrade-tribunal/1","stale":true}\n' \
  >"$CANDIDATE_DIR/tribunal.ndjson"
run_expected_failure stale_root_refused 1 101 \
  env FLN_SUITE_UPGRADE_CANDIDATE_DIR="$CANDIDATE_DIR" \
    CARGO_TARGET_DIR="$BUILD_TARGET" \
    "$PREFLIGHT"
mv -- "$CANDIDATE_DIR/tribunal.ndjson.aside" "$CANDIDATE_DIR/tribunal.ndjson"

run_step restore \
  env FLN_SUITE_UPGRADE_CANDIDATE_DIR="$CANDIDATE_DIR" \
    CARGO_TARGET_DIR="$BUILD_TARGET" \
    "$PREFLIGHT"

run_step unchanged_authoritative_lock \
  test "$(digest_file "$ROOT/SUITE.lock")" = "$AUTHORITATIVE_LOCK_ROOT"
final_lock_root="$AUTHORITATIVE_LOCK_ROOT"

FINAL_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path vendor/lean4-src
)" || {
  printf '[suite_upgrade_no_mock_e2e] internal fault: cannot hash final inputs\n' >&2
  exit 2
}
if [ "$FINAL_ROOT" != "$INPUT_ROOT" ]; then
  printf '[suite_upgrade_no_mock_e2e] inconclusive: governed inputs changed during the run\n' >&2
  exit 3
fi

END_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
emit_event --string event run_end --string verdict pass \
  --string reason_code all_h25_isolated_candidate_obligations_satisfied \
  --integer process_exit 0 --string active_step unchanged_authoritative_lock \
  --integer duration_ns "$((END_NS - START_NS))" \
  --string cleanup_status retained_by_policy \
  --string final_state "$FINAL_ROOT" --string logical_root "$FINAL_ROOT" \
  --string receipt_root "$CANDIDATE_DIR/candidate-receipt.ndjson" \
  --string first_divergence none --string evidence_manifest manifest.json \
  --string bundle_commit bundle.complete.json \
  --string evidence_state pending_bundle_commit \
  --string old_lock_root "$OLD_LOCK_ROOT" \
  --string candidate_lock_root "$CANDIDATE_LOCK_ROOT" \
  --string final_current_lock_root "$final_lock_root"
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

printf '[suite_upgrade_no_mock_e2e] PASS evidence=%s candidate=%s\n' \
  "$ART_DIR" "$CANDIDATE_DIR" >&2
