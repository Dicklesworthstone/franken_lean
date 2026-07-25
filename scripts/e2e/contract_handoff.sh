#!/usr/bin/env bash
# Authoritative W1 terminal contract handoff. Two archived clean checkouts run the
# real extractors under different sealed environments; generated Rust is compiled;
# then every named cross-surface drift class is planted in the retained scratch copy,
# refused for its typed reason, and repaired without touching the live workspace.

set -Eeuo pipefail

PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  echo "[contract_handoff] setup failure: python3 is required" >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
HOSTILE_PYTHON_CONFIGURATION=()
while IFS= read -r environment_name; do
  [[ "$environment_name" == PYTHON* ]] \
    && HOSTILE_PYTHON_CONFIGURATION+=("$environment_name")
done < <(compgen -e | LC_ALL=C sort)
if ((${#HOSTILE_PYTHON_CONFIGURATION[@]} > 0)); then
  printf '[contract_handoff] setup failure: sealed_interpreter_hostile_environment names=%s\n' \
    "$(IFS=,; printf '%s' "${HOSTILE_PYTHON_CONFIGURATION[*]}")" >&2
  exit 2
fi
for tool in git tar cargo sha256sum cmp; do
  command -v "$tool" >/dev/null 2>&1 || {
    printf '[contract_handoff] setup failure: %s is required\n' "$tool" >&2
    exit 2
  }
done

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
cd "$ROOT"
EVIDENCE="$ROOT/scripts/evidence.py"
SCHEMA="fln.e2e/2"
BEAD="franken_lean-w75y"
SCENARIO="contract_handoff"
RUN_ID="contract-handoff-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
HUMAN="$ART_DIR/human.log"
VENDOR_BINDING="$ART_DIR/vendor-binding.json"
CAPTURE_BYTES="${FLN_E2E_CAPTURE_BYTES:-524288}"
OUTPUT_BUDGET_BYTES="${FLN_E2E_OUTPUT_BUDGET_BYTES:-67108864}"
TIMEOUT_MS="${FLN_E2E_TIMEOUT_MS:-7200000}"
GRACE_MS="${FLN_E2E_KILL_GRACE_MS:-5000}"
START_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
SOURCE_COMMIT="$(git rev-parse HEAD)"
SCRATCH_BASE="/data/tmp/franken-lean-contract-handoff-$RUN_ID"
SCRATCH_A="$SCRATCH_BASE/cold-a"
SCRATCH_B="$SCRATCH_BASE/cold-b"
RETAINED="$ART_DIR/retained-mutants"
BUILD_A="/data/tmp/franken-lean-contract-handoff-build-$RUN_ID-a"
BUILD_B="/data/tmp/franken-lean-contract-handoff-build-$RUN_ID-b"
FULL_CENSUS="${FLN_CONTRACT_HANDOFF_FULL_CENSUS:-1}"

case "$FULL_CENSUS" in
  0|1) ;;
  *)
    echo "[contract_handoff] setup failure: FLN_CONTRACT_HANDOFF_FULL_CENSUS must be 0 or 1" >&2
    exit 2
    ;;
esac

INPUT_PATHS=(
  SUITE.lock rust-toolchain.toml
  contracts/CONTRACT_INVENTORY_V1.txt contracts/PIN_TARGET_INVENTORY.txt
  contracts/CONTRACT_HANDOFF_V1.txt contracts/CONTRACT_HANDOFF.txt
  contracts/ABI_TARGET_LAYOUT.txt contracts/OLEAN_ILEAN_FORMAT.txt
  contracts/EXTERN_BUILTIN_ENVIRONMENT.txt contracts/abi_inventory.json
  contracts/olean_inventory.json contracts/extern_census.tsv
  contracts/builtin_environment.tsv contracts/builtin_environment.001.tsv
  contracts/builtin_environment.002.tsv contracts/builtin_partition.tsv
  ci/PIN_TARGET_POLICY.txt ci/CONTRACT_HANDOFF_POLICY.txt
  ci/BUILTIN_PARTITION_POLICY.txt ci/VERIFICATION_MANIFEST.jsonl
  ABI_CONTRACT.md OLEAN_CONTRACT.md
  crates/fln-rt/src/abi.rs crates/fln-rt/src/region_contract.rs
  crates/fln-unsafe-abi/src/contract.rs crates/fln-olean/src/format.rs
  crates/fln-conformance/tests/contract_roots.rs
  scripts/extract/gen_abi_contract.py scripts/extract/gen_olean_contract.py
  scripts/extract/gen_extern_census.sh scripts/extract/gen_extern_census.lean
  scripts/extract/validate_extern_builtin_census.py
  scripts/e2e/contract_handoff.sh scripts/evidence.py scripts/check.sh
  tools/structure-guard .github/workflows/ci.yml vendor/NOTICE
)
HASH_ARGS=()
GOVERNED_ARGS=()
for input_path in "${INPUT_PATHS[@]}"; do
  HASH_ARGS+=(--path "$input_path")
  GOVERNED_ARGS+=(--governed-path "$input_path")
done

SUBJECT_PATHS=("${INPUT_PATHS[@]}")
SUBJECT_HASH_ARGS=()
for subject_path in "${SUBJECT_PATHS[@]}"; do
  SUBJECT_HASH_ARGS+=(--path "$subject_path")
done

if ! INPUT_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path vendor/lean4-src
)"; then
  echo "[contract_handoff] setup failure: cannot hash governed inputs" >&2
  exit 2
fi
required_field() {
  local path="$1" key="$2" value
  value="$(awk -v key="$key" '$1 == key { print $2; exit }' "$path")"
  if [ -z "$value" ]; then
    printf '[contract_handoff] setup failure: %s has no %s field\n' \
      "$path" "$key" >&2
    exit 2
  fi
  printf '%s\n' "$value"
}
HANDOFF_SCHEMA="$(required_field contracts/CONTRACT_HANDOFF.txt schema)"
HANDOFF_ROOT="$(required_field contracts/CONTRACT_HANDOFF.txt handoff-root)"
HANDOFF_POLICY_ROOT="$(required_field contracts/CONTRACT_HANDOFF.txt policy-root)"
OUTPUT_ROOT="$(required_field contracts/CONTRACT_HANDOFF.txt output-root)"
HANDOFF_ROWS="$(required_field contracts/CONTRACT_HANDOFF.txt row-count)"
HANDOFF_DOMAINS="$(required_field contracts/CONTRACT_HANDOFF.txt domain-count)"
INVENTORY_SCHEMA="$(required_field contracts/PIN_TARGET_INVENTORY.txt schema)"
INVENTORY_ROOT="$(required_field contracts/PIN_TARGET_INVENTORY.txt inventory-root)"
RAW_ROOT="$(required_field contracts/PIN_TARGET_INVENTORY.txt raw-root)"
INVENTORY_POLICY_ROOT="$(required_field contracts/PIN_TARGET_INVENTORY.txt policy-root)"
REFERENCE_ROOT="$(required_field contracts/PIN_TARGET_INVENTORY.txt reference-root)"
TARGET_TRIPLE="$(required_field SUITE.lock target)"
ABI_SCHEMA="$(required_field contracts/ABI_TARGET_LAYOUT.txt schema)"
FORMAT_SCHEMA="$(required_field contracts/OLEAN_ILEAN_FORMAT.txt schema)"
ENVIRONMENT_SCHEMA="$(required_field contracts/EXTERN_BUILTIN_ENVIRONMENT.txt schema)"
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

SEQ=0
FINAL_SET=0
FINAL_VERDICT=internal_fault
FINAL_REASON=uncommitted_exit
FINAL_EXIT=2
ACTIVE_STEP=setup
TERMINAL_EMITTED=0

note() {
  printf '[contract_handoff] %s\n' "$*" | tee -a "$HUMAN" >&2
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

hash_governed() {
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path vendor/lean4-src
}

hash_subject() {
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$1" "${SUBJECT_HASH_ARGS[@]}" \
    --vendor-path vendor/lean4-src
}

seal_archived_checkout() {
  local checkout="$1"
  local source_tree archived_tree
  git init --quiet --initial-branch=main "$checkout"
  git -C "$checkout" add --force -- .
  git -C "$checkout" \
    -c user.name=franken-lean-evidence \
    -c user.email=franken-lean-evidence.invalid \
    commit --quiet --message "retained archive of $SOURCE_COMMIT"
  source_tree="$(git rev-parse "$SOURCE_COMMIT^{tree}")"
  archived_tree="$(git -C "$checkout" rev-parse "HEAD^{tree}")"
  if [ "$archived_tree" != "$source_tree" ]; then
    printf '[contract_handoff] setup failure: archived tree drift source=%s archived=%s\n' \
      "$source_tree" "$archived_tree" >&2
    return 1
  fi
}

read_meta() {
  "${PYTHON[@]}" - "$1" "$2" <<'PY'
import json
import pathlib
import sys

value = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))[sys.argv[2]]
print("null" if value is None else value)
PY
}

finalize() {
  local observed_rc="$1" final_root validation_rc=0 bundle_rc=0
  trap - EXIT HUP INT TERM
  set +e
  if [ "$FINAL_SET" -eq 0 ]; then
    if [ "$observed_rc" -eq 0 ]; then
      set_final internal_fault uncommitted_success 2
    else
      set_final internal_fault unexpected_shell_exit 2
    fi
  fi
  final_root="$(hash_governed)" || {
    final_root=unavailable
    set_final internal_fault final_workspace_hash_unavailable 2
  }
  if [ "$FINAL_VERDICT" = pass ] && [ "$final_root" != "$INPUT_ROOT" ]; then
    set_final inconclusive final_workspace_changed 3
  fi
  local first_divergence=none
  [ "$FINAL_VERDICT" = pass ] || first_divergence="$FINAL_REASON"
  if [ "$TERMINAL_EMITTED" -eq 0 ]; then
    emit_event --string event run_end --string verdict "$FINAL_VERDICT" \
      --string reason_code "$FINAL_REASON" --integer process_exit "$FINAL_EXIT" \
      --string active_step "$ACTIVE_STEP" \
      --integer duration_ns "$(( $("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())') - START_NS ))" \
      --string cleanup_status retained_by_policy --string final_state "$final_root" \
      --string logical_root "$final_root" \
      --string receipt_root "$(awk '$1=="handoff-root"{print $2}' contracts/CONTRACT_HANDOFF.txt)" \
      --string first_divergence "$first_divergence" \
      --string evidence_manifest manifest.json \
      --string bundle_commit bundle.complete.json \
      --string evidence_state pending_bundle_commit || validation_rc=2
    TERMINAL_EMITTED=1
  fi
  if [ "$validation_rc" -eq 0 ]; then
    "${PYTHON[@]}" "$EVIDENCE" validate-run --file "$LOG" --schema "$SCHEMA" \
      --expected-verdict "$FINAL_VERDICT" --artifact-root "$ART_DIR" \
      --output "$ART_DIR/run.validation.json" || validation_rc=2
  fi
  if [ "$validation_rc" -eq 0 ]; then
    "${PYTHON[@]}" "$EVIDENCE" manifest --art-dir "$ART_DIR" \
      --output "$ART_DIR/manifest.json" --digest-output "$ART_DIR/manifest.digest" \
      --run-id "$RUN_ID" --bead "$BEAD" --scenario "$SCENARIO" \
      --verdict "$FINAL_VERDICT" --input-root "$INPUT_ROOT" --final-root "$final_root" \
      || validation_rc=2
  fi
  if [ "$validation_rc" -eq 0 ]; then
    "${PYTHON[@]}" "$EVIDENCE" complete-bundle --art-dir "$ART_DIR" \
      --manifest "$ART_DIR/manifest.json" --digest "$ART_DIR/manifest.digest" \
      --output "$ART_DIR/bundle.complete.json" --governed-root "$ROOT" \
      "${GOVERNED_ARGS[@]}" --expected-root "$final_root" \
      --vendor-path vendor/lean4-src || bundle_rc=$?
    "${PYTHON[@]}" "$EVIDENCE" adopt-bundle --art-dir "$ART_DIR" \
      --manifest "$ART_DIR/manifest.json" --digest "$ART_DIR/manifest.digest" \
      --commit "$ART_DIR/bundle.complete.json" --artifact-root "$ART_DIR" \
      >/dev/null || bundle_rc=2
  fi
  if [ "$validation_rc" -ne 0 ] || [ "$bundle_rc" -ne 0 ]; then
    printf '[contract_handoff] INTERNAL FAULT: evidence bundle incomplete: %s\n' \
      "$ART_DIR" >&2
    exit 2
  fi
  note "$FINAL_VERDICT reason=$FINAL_REASON evidence=$ART_DIR scratch=$SCRATCH_BASE"
  exit "$FINAL_EXIT"
}

on_signal() {
  local name="$1" code="$2"
  set_final cancelled "signal_$name" "$code"
  exit "$code"
}

trap 'on_signal HUP 129' HUP
trap 'on_signal INT 130' INT
trap 'on_signal TERM 143' TERM
trap 'finalize "$?"' EXIT

mkdir -p "$(dirname "$ART_DIR")"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  trap - EXIT
  echo "[contract_handoff] evidence directory already claimed: $ART_DIR" >&2
  exit 2
fi
mkdir "$RETAINED"
: > "$HUMAN"
"${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" \
  --vendor-path vendor/lean4-src --output "$VENDOR_BINDING" \
  --artifact-root "$ART_DIR"

emit_event --new-log --string event run_start \
  --json-value argv '["scripts/e2e/contract_handoff.sh"]' --string cwd "$ROOT" \
  --append-string claim_ids FLN-W1-CANONICAL-CONTRACT-HANDOFF \
  --append-string invariant_ids D5 --append-string invariant_ids D9 \
  --append-string invariant_ids FL-INV-01 --append-string invariant_ids FL-INV-07 \
  --append-string gate_ids W1 --append-string gate_ids G0-10 \
  --string parity_ledger_row not_applicable_contract_extraction \
  --string epoch lean-v4.32.0 --string mode sound --string profile e2e \
  --string platform "$(uname -srm)" --integer thread_count 1 \
  --string target "$TARGET_TRIPLE" \
  --string handoff_schema "$HANDOFF_SCHEMA" \
  --string inventory_schema "$INVENTORY_SCHEMA" \
  --string abi_schema "$ABI_SCHEMA" --string format_schema "$FORMAT_SCHEMA" \
  --string environment_schema "$ENVIRONMENT_SCHEMA" \
  --string extractor_versions \
  "suite-lock=1,lean-h-clang-layout=1,lean-format-source-and-pin-artifacts=1,lean-reference-environment-walk=2" \
  --string canonical_root "$HANDOFF_ROOT" \
  --string inventory_root "$INVENTORY_ROOT" --string raw_root "$RAW_ROOT" \
  --string reference_root "$REFERENCE_ROOT" \
  --string inventory_policy_root "$INVENTORY_POLICY_ROOT" \
  --string handoff_policy_root "$HANDOFF_POLICY_ROOT" \
  --string output_root "$OUTPUT_ROOT" --integer domain_rows "$HANDOFF_ROWS" \
  --integer domain_count "$HANDOFF_DOMAINS" \
  --string publication_authority atomic-published-observed \
  --json-value host_facts "$HOST_FACTS_JSON" \
  --string seed "$SOURCE_COMMIT" --string cache_state cold-archived-checkouts \
  --string input_root "$INPUT_ROOT" --string vendor_binding vendor-binding.json \
  --json-value budgets "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$TIMEOUT_MS,\"kill_grace_ms\":$GRACE_MS}"

note "materializing two retained cold checkouts from commit $SOURCE_COMMIT"
mkdir -p "$SCRATCH_A" "$SCRATCH_B"
git archive --format=tar "$SOURCE_COMMIT" | tar -xf - -C "$SCRATCH_A"
git archive --format=tar "$SOURCE_COMMIT" | tar -xf - -C "$SCRATCH_B"
seal_archived_checkout "$SCRATCH_A"
seal_archived_checkout "$SCRATCH_B"

run_step() {
  local step="$1" subject="$2" expected_class="$3" expected_wrapper="$4"
  local expected_child="$5" pattern_one="$6" pattern_two="$7"
  shift 7
  ACTIVE_STEP="$step"
  local global_before global_after subject_before subject_after
  local meta="$ART_DIR/$step.meta.json"
  local out="$ART_DIR/$step.out"
  local err="$ART_DIR/$step.err"
  local ready="$ART_DIR/$step.ready.json"
  local validation="$ART_DIR/$step.validation.json"
  global_before="$(hash_governed)"
  subject_before="$(hash_subject "$subject")"
  local -a semantic=()
  if [ "$expected_class" = fail ]; then
    semantic=(--semantic-failure-exit "$expected_child")
  fi
  set +e
  "${PYTHON[@]}" "$EVIDENCE" run --cwd "$subject" --metadata "$meta" \
    --stdout "$out" --stderr "$err" --readiness "$ready" \
    --artifact-root "$ART_DIR" --capture-bytes "$CAPTURE_BYTES" \
    --output-budget-bytes "$OUTPUT_BUDGET_BYTES" --timeout-ms "$TIMEOUT_MS" \
    --grace-ms "$GRACE_MS" --stage-id "$step" "${semantic[@]}" -- "$@"
  local wrapper=$?
  set -e
  "${PYTHON[@]}" "$EVIDENCE" validate-supervisor --file "$meta" \
    --expected-stage-id "$step" --artifact-root "$ART_DIR" --output "$validation"
  global_after="$(hash_governed)"
  subject_after="$(hash_subject "$subject")"
  local actual_class actual_child assertion=pass
  actual_class="$(read_meta "$meta" classification)"
  actual_child="$(read_meta "$meta" child_exit)"
  if [ "$wrapper" -ne "$expected_wrapper" ] \
      || [ "$actual_class" != "$expected_class" ] \
      || [ "$actual_child" != "$expected_child" ] \
      || [ "$global_before" != "$INPUT_ROOT" ] \
      || [ "$global_after" != "$INPUT_ROOT" ] \
      || [ "$subject_before" != "$subject_after" ]; then
    assertion=fail
  fi
  if [ "$pattern_one" != - ] \
      && ! grep -Fq -- "$pattern_one" "$out" "$err"; then
    assertion=fail
  fi
  if [ "$pattern_two" != - ] \
      && ! grep -Fq -- "$pattern_two" "$out" "$err"; then
    assertion=fail
  fi
  emit_event --string event step --string step_id "$step" \
    --string assertion "$assertion" \
    --string expected "$expected_class/exit=$expected_wrapper/child=$expected_child" \
    --string actual "$actual_class/exit=$wrapper/child=$actual_child" \
    --string input_root "$global_before" --string final_state "$global_after" \
    --string validation_artifact "$(basename "$validation")" \
    --string expected_supervisor_classification "$expected_class" \
    --integer expected_wrapper_exit "$expected_wrapper" \
    --integer expected_child_exit "$expected_child" \
    --string subject_root "$subject_before" \
    --string subject_final_state "$subject_after" --json-file supervisor "$meta"
  if [ "$assertion" != pass ]; then
    set_final fail "$step:assertion_failed" 1
    exit 1
  fi
}

# The variables below expand inside the isolated child shell, not in this runner.
# shellcheck disable=SC2016
regeneration_command='
set -euo pipefail
root="$1"
full="$2"
python3 -I -S "$root/scripts/extract/gen_abi_contract.py" --check
python3 -I -S "$root/scripts/extract/gen_olean_contract.py" --check
if [ "$full" = 1 ]; then
  "$root/scripts/extract/gen_extern_census.sh" --check
else
  "$root/scripts/extract/gen_extern_census.sh" --validate
fi
cargo run --locked -q -p structure-guard -- --root "$root" --robot
'

# As above, these positional parameters belong to the isolated child shell.
# shellcheck disable=SC2016
compile_command='
set -euo pipefail
root="$1"
cargo test --locked -p fln-rt -p fln-olean
cargo test --locked -p fln-conformance --test contract_roots
cargo test --locked -p structure-guard contract_handoff_no_mock_e2e
test -s "$root/contracts/CONTRACT_HANDOFF.txt"
'

run_step cold_regeneration_a "$SCRATCH_A" pass 0 0 \
  '"verdict":"pass"' '"canonical_root":"fnv1a64:' \
  env -i HOME="$HOME" PATH="$PATH" LANG=C LC_ALL=C TZ=UTC \
  CARGO_TARGET_DIR="$BUILD_A" /bin/bash -c "$regeneration_command" _ \
  "$SCRATCH_A" "$FULL_CENSUS"

run_step cold_regeneration_b "$SCRATCH_B" pass 0 0 \
  '"verdict":"pass"' '"canonical_root":"fnv1a64:' \
  env -i HOME="$HOME" PATH="$PATH" LANG=C.UTF-8 LC_ALL=C.UTF-8 \
  TZ=Pacific/Kiritimati SOURCE_DATE_EPOCH=123456789 RAYON_NUM_THREADS=8 \
  CARGO_TARGET_DIR="$BUILD_B" /bin/bash -c "$regeneration_command" _ \
  "$SCRATCH_B" "$FULL_CENSUS"

run_step canonical_join "$SCRATCH_A" pass 0 0 - - \
  cmp "$SCRATCH_A/contracts/CONTRACT_HANDOFF.txt" \
  "$SCRATCH_B/contracts/CONTRACT_HANDOFF.txt"

run_step generated_compile "$SCRATCH_A" pass 0 0 "test result: ok" - \
  env CARGO_TARGET_DIR="$BUILD_A" /bin/bash -c "$compile_command" _ "$SCRATCH_A"

retain_and_mutate() {
  local relative="$1" label="$2"
  shift 2
  cp --reflink=auto "$SCRATCH_A/$relative" "$RETAINED/$label.orig"
  "${PYTHON[@]}" - "$SCRATCH_A/$relative" "$@" <<'PY'
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
mode = sys.argv[2]
text = path.read_text(encoding="utf-8")
if mode == "append":
    mutated = text + sys.argv[3]
elif mode == "replace":
    before, after = sys.argv[3], sys.argv[4]
    if before not in text:
        raise SystemExit(f"mutation anchor absent: {before!r}")
    mutated = text.replace(before, after, 1)
elif mode == "drop":
    line = sys.argv[3]
    if line not in text:
        raise SystemExit(f"mutation row absent: {line!r}")
    mutated = text.replace(line, "", 1)
elif mode == "resize":
    size = int(sys.argv[3])
    if size <= len(text):
        raise SystemExit(f"resize must grow the fixture: {size} <= {len(text)}")
    mutated = text + ("#" * (size - len(text)))
else:
    raise SystemExit(f"unknown mutation mode: {mode}")
path.write_text(mutated, encoding="utf-8")
PY
}

repair_mutation() {
  local relative="$1" label="$2"
  mkdir -p "$RETAINED/$label"
  mv "$SCRATCH_A/$relative" "$RETAINED/$label/mutant"
  cp --reflink=auto "$RETAINED/$label.orig" "$SCRATCH_A/$relative"
}

GUARD="$BUILD_A/debug/structure-guard"
[ -x "$GUARD" ] || {
  set_final internal_fault frozen_guard_missing 2
  exit 2
}

retain_and_mutate ABI_CONTRACT.md markdown append $'\nplanted-render-drift\n'
run_step markdown_only_mutant "$SCRATCH_A" fail 1 1 \
  FLN-STRUCT-034 published_handoff_invalid \
  "$GUARD" --root "$SCRATCH_A" --robot
repair_mutation ABI_CONTRACT.md markdown
run_step markdown_only_recovery "$SCRATCH_A" pass 0 0 \
  '"verdict":"pass"' - "$GUARD" --root "$SCRATCH_A" --robot

retain_and_mutate crates/fln-rt/src/abi.rs constants replace \
  'pub const TAG_CLOSURE: u8 = 245;' 'pub const TAG_CLOSURE: u8 = 244;'
run_step constants_only_mutant "$SCRATCH_A" fail 1 1 \
  FLN-STRUCT-034 published_handoff_invalid \
  "$GUARD" --root "$SCRATCH_A" --robot
repair_mutation crates/fln-rt/src/abi.rs constants
run_step constants_only_recovery "$SCRATCH_A" pass 0 0 \
  '"verdict":"pass"' - "$GUARD" --root "$SCRATCH_A" --robot

POLICY_ROW='row abi-contract-markdown path=ABI_CONTRACT.md domain=abi role=markdown support=required
'
retain_and_mutate ci/CONTRACT_HANDOFF_POLICY.txt policy drop "$POLICY_ROW"
run_step policy_omission_mutant "$SCRATCH_A" fail 1 1 \
  FLN-STRUCT-034 handoff_policy_not_exact \
  "$GUARD" --root "$SCRATCH_A" --robot
repair_mutation ci/CONTRACT_HANDOFF_POLICY.txt policy
run_step policy_omission_recovery "$SCRATCH_A" pass 0 0 \
  '"verdict":"pass"' - "$GUARD" --root "$SCRATCH_A" --robot

STALE_POLICY_ROW='row stale-output path=contracts/stale.txt domain=abi role=markdown support=required
'
retain_and_mutate ci/CONTRACT_HANDOFF_POLICY.txt stale-policy append \
  "$STALE_POLICY_ROW"
run_step stale_policy_mutant "$SCRATCH_A" fail 1 1 \
  FLN-STRUCT-034 handoff_policy_not_exact \
  "$GUARD" --root "$SCRATCH_A" --robot
repair_mutation ci/CONTRACT_HANDOFF_POLICY.txt stale-policy
run_step stale_policy_recovery "$SCRATCH_A" pass 0 0 \
  '"verdict":"pass"' - "$GUARD" --root "$SCRATCH_A" --robot

retain_and_mutate ci/CONTRACT_HANDOFF_POLICY.txt duplicate-policy append \
  "$POLICY_ROW"
run_step duplicate_policy_mutant "$SCRATCH_A" fail 1 1 \
  FLN-STRUCT-034 handoff_policy_duplicate \
  "$GUARD" --root "$SCRATCH_A" --robot
repair_mutation ci/CONTRACT_HANDOFF_POLICY.txt duplicate-policy
run_step duplicate_policy_recovery "$SCRATCH_A" pass 0 0 \
  '"verdict":"pass"' - "$GUARD" --root "$SCRATCH_A" --robot

retain_and_mutate contracts/CONTRACT_HANDOFF_V1.txt schema replace \
  'handoff-schema fln-contract-handoff/1' \
  'handoff-schema fln-contract-handoff/999'
run_step incompatible_schema_mutant "$SCRATCH_A" fail 1 1 \
  FLN-STRUCT-034 handoff_schema_mismatch \
  "$GUARD" --root "$SCRATCH_A" --robot
repair_mutation contracts/CONTRACT_HANDOFF_V1.txt schema
run_step incompatible_schema_recovery "$SCRATCH_A" pass 0 0 \
  '"verdict":"pass"' - "$GUARD" --root "$SCRATCH_A" --robot

retain_and_mutate contracts/PIN_TARGET_INVENTORY.txt pin replace \
  'suite-lock-root fnv1a64:54c4ae5afb0b3bbb' \
  'suite-lock-root fnv1a64:04c4ae5afb0b3bbb'
run_step mixed_pin_mutant "$SCRATCH_A" fail 1 1 \
  FLN-STRUCT-032 published_inventory_invalid \
  "$GUARD" --root "$SCRATCH_A" --robot
repair_mutation contracts/PIN_TARGET_INVENTORY.txt pin
run_step mixed_pin_recovery "$SCRATCH_A" pass 0 0 \
  '"verdict":"pass"' - "$GUARD" --root "$SCRATCH_A" --robot

retain_and_mutate SUITE.lock reference-pin replace \
  'commit=8c9756b28d64dab099da31a4c09229a9e6a2ef35' \
  'commit=0c9756b28d64dab099da31a4c09229a9e6a2ef35'
run_step mixed_reference_mutant "$SCRATCH_A" fail 1 1 \
  FLN-STRUCT-032 published_inventory_invalid \
  "$GUARD" --root "$SCRATCH_A" --robot
repair_mutation SUITE.lock reference-pin
run_step mixed_reference_recovery "$SCRATCH_A" pass 0 0 \
  '"verdict":"pass"' - "$GUARD" --root "$SCRATCH_A" --robot

retain_and_mutate contracts/ABI_TARGET_LAYOUT.txt target replace \
  'pointer-bits=64' 'pointer-bits=32'
run_step host_target_substitution_mutant "$SCRATCH_A" fail 1 1 \
  FLN-STRUCT-032 abi_target_layout_invalid \
  "$GUARD" --root "$SCRATCH_A" --robot
repair_mutation contracts/ABI_TARGET_LAYOUT.txt target
run_step host_target_substitution_recovery "$SCRATCH_A" pass 0 0 \
  '"verdict":"pass"' - "$GUARD" --root "$SCRATCH_A" --robot

printf 'partial generated Rust\n' > \
  "$SCRATCH_A/crates/fln-rt/src/abi.rs.candidate"
run_step partial_publication_mutant "$SCRATCH_A" fail 1 1 \
  FLN-STRUCT-035 stale_source_candidate \
  "$GUARD" --root "$SCRATCH_A" --robot
mv "$SCRATCH_A/crates/fln-rt/src/abi.rs.candidate" \
  "$RETAINED/partial-abi.rs.candidate"
run_step partial_publication_recovery "$SCRATCH_A" pass 0 0 \
  '"verdict":"pass"' - "$GUARD" --root "$SCRATCH_A" --robot

cp --reflink=auto "$SCRATCH_A/contracts/CONTRACT_HANDOFF.txt" \
  "$SCRATCH_A/contracts/CONTRACT_HANDOFF.txt.candidate"
cp --reflink=auto "$SCRATCH_A/contracts/CONTRACT_HANDOFF.txt.candidate" \
  "$RETAINED/cancelled-complete-handoff.candidate"
run_step cancelled_publication_mutant "$SCRATCH_A" fail 1 1 \
  FLN-STRUCT-035 stale_candidate \
  "$GUARD" --root "$SCRATCH_A" --robot
run_step cancelled_publication_recovery "$SCRATCH_A" pass 0 0 \
  '"action":"recovered"' '"verdict":"pass"' \
  "$GUARD" --root "$SCRATCH_A" --recover-contract-handoff --robot

retain_and_mutate ci/CONTRACT_HANDOFF_POLICY.txt resource resize 1048577
run_step resource_exhaustion_mutant "$SCRATCH_A" fail 1 1 \
  FLN-STRUCT-035 resource_exhausted \
  "$GUARD" --root "$SCRATCH_A" --robot
repair_mutation ci/CONTRACT_HANDOFF_POLICY.txt resource
run_step resource_exhaustion_recovery "$SCRATCH_A" pass 0 0 \
  '"verdict":"pass"' - "$GUARD" --root "$SCRATCH_A" --robot

retain_and_mutate ABI_CONTRACT.md suppressed-drift append \
  $'\nplanted-suppressed-drift\n'
run_step suppressed_drift_mutant "$SCRATCH_A" fail 1 1 \
  'gen_abi_contract: DRIFT:' ABI_CONTRACT.md \
  python3 -I -S "$SCRATCH_A/scripts/extract/gen_abi_contract.py" --check
repair_mutation ABI_CONTRACT.md suppressed-drift
run_step suppressed_drift_recovery "$SCRATCH_A" pass 0 0 \
  'gen_abi_contract: check OK' - \
  python3 -I -S "$SCRATCH_A/scripts/extract/gen_abi_contract.py" --check

retain_and_mutate crates/fln-rt/src/abi.rs reference append \
  $'\nconst REFERENCE_RUNTIME: &str = ".elan/toolchains/reference";\n'
run_step reference_path_mutant "$SCRATCH_A" fail 1 1 \
  FLN-STRUCT-034 reference_runtime_path_leak \
  "$GUARD" --root "$SCRATCH_A" --robot
repair_mutation crates/fln-rt/src/abi.rs reference
run_step reference_path_recovery "$SCRATCH_A" pass 0 0 \
  '"verdict":"pass"' - "$GUARD" --root "$SCRATCH_A" --robot

retain_and_mutate crates/fln-rt/src/abi.rs mock append \
  $'\nconst FLN_MOCK_CONSUMER: bool = true;\n'
run_step mock_consumer_mutant "$SCRATCH_A" fail 1 1 \
  FLN-STRUCT-034 mock_consumer_substitution \
  "$GUARD" --root "$SCRATCH_A" --robot
repair_mutation crates/fln-rt/src/abi.rs mock
run_step mock_consumer_recovery "$SCRATCH_A" pass 0 0 \
  '"verdict":"pass"' - "$GUARD" --root "$SCRATCH_A" --robot

run_step final_handoff "$SCRATCH_A" pass 0 0 \
  '"verdict":"pass"' '"canonical_root":"fnv1a64:' \
  "$GUARD" --root "$SCRATCH_A" --robot

set_final pass all_contract_handoff_obligations_passed 0
