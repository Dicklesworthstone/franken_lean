#!/usr/bin/env bash
# W3 certificate-format and OQ-8 no-mock external-checker evidence lane.

set -Eeuo pipefail

PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  printf '[certificate_format_no_mock_e2e] setup failure: python3 is required\n' >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
for required_command in cargo elan git lake setsid sha256sum wc; do
  command -v "$required_command" >/dev/null 2>&1 || {
    printf '[certificate_format_no_mock_e2e] setup failure: %s is required\n' \
      "$required_command" >&2
    exit 2
  }
done

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
cd "$ROOT"
EVIDENCE="$ROOT/scripts/evidence.py"
SCHEMA="fln.e2e/2"
SEMANTIC_SCHEMA="fln.e2e.certificate-format-semantic/1"
TELEMETRY_SCHEMA="fln.e2e.certificate-format-telemetry/1"
BEAD="fln-7zrh"
SCENARIO="certificate_format_no_mock_e2e"
LEAN4EXPORT_REVISION="4e7915201d3f9f04470d9eae002fa695f7cdc589"
NANODA_REVISION="ddfac2bf5a7b56cb46e141494427ff3dd55963c7"
REFERENCE_REVISION="8c9756b28d64dab099da31a4c09229a9e6a2ef35"
REFERENCE_TOOLCHAIN="${FLN_REFERENCE_TOOLCHAIN:-leanprover/lean4:v4.32.0}"
LEAN4EXPORT_ROOT="${FLN_LEAN4EXPORT_ROOT:-}"
LEAN4EXPORT_BIN="${FLN_LEAN4EXPORT_BIN:-}"
NANODA_ROOT="${FLN_NANODA_ROOT:-}"
NANODA_BIN="${FLN_NANODA_BIN:-}"
RUN_ID="certificate-format-no-mock-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
SEMANTIC="$ART_DIR/semantic.ndjson"
TELEMETRY="$ART_DIR/telemetry.ndjson"
VENDOR_PATH="vendor/lean4-src"
VENDOR_BINDING="$ART_DIR/vendor-binding.json"
WITNESS="$ROOT/tribunal/fixtures/certificate-format/CertificateWitness.lean"
BUILD_TARGET="${CARGO_TARGET_DIR:-$ROOT/target/cargo}/e2e-certificate-format"
CAPTURE_BYTES="${FLN_E2E_CAPTURE_BYTES:-1048576}"
OUTPUT_BUDGET_BYTES="${FLN_E2E_OUTPUT_BUDGET_BYTES:-16777216}"
TIMEOUT_MS="${FLN_E2E_TIMEOUT_MS:-600000}"
GRACE_MS="${FLN_E2E_KILL_GRACE_MS:-2000}"
START_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
SEQ=0

if [ -z "$LEAN4EXPORT_ROOT" ] || [ -z "$LEAN4EXPORT_BIN" ] \
  || [ -z "$NANODA_ROOT" ] || [ -z "$NANODA_BIN" ]; then
  printf '%s\n' \
    '[certificate_format_no_mock_e2e] inconclusive: set FLN_LEAN4EXPORT_ROOT,' \
    'FLN_LEAN4EXPORT_BIN, FLN_NANODA_ROOT, and FLN_NANODA_BIN to pinned tools' >&2
  exit 3
fi

INPUT_PATHS=(
  Cargo.toml
  Cargo.lock
  SUITE.lock
  rust-toolchain.toml
  ci/VERIFICATION_MANIFEST.jsonl
  crates/fln-core
  crates/fln-hash
  CERTIFICATE_FORMAT.md
  tribunal/fixtures/certificate-format/CertificateWitness.lean
  scripts/e2e/certificate_format_no_mock_e2e.sh
  scripts/evidence.py
  scripts/lib/gate_lock.sh
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
  printf '[certificate_format_no_mock_e2e] setup failure: artifact path is not fresh: %s\n' \
    "$ART_DIR" >&2
  exit 2
fi

"${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" \
  --vendor-path "$VENDOR_PATH" --output "$VENDOR_BINDING" \
  --artifact-root "$ART_DIR" || {
    printf '[certificate_format_no_mock_e2e] setup failure: cannot bind vendored Reference\n' >&2
    exit 2
  }
INPUT_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path "$VENDOR_PATH"
)" || {
  printf '[certificate_format_no_mock_e2e] setup failure: cannot hash governed inputs\n' >&2
  exit 2
}

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
  --json-value argv '["scripts/e2e/certificate_format_no_mock_e2e.sh"]' \
  --string cwd "$ROOT" \
  --append-string claim_ids FLN-W3-CERTIFICATE-CANONICAL-ENVELOPE \
  --append-string claim_ids FLN-W3-OQ8-LOSSLESS-EXPORT-ALIGNMENT \
  --append-string invariant_ids FL-INV-01 \
  --append-string invariant_ids FL-INV-02 \
  --append-string invariant_ids FL-INV-07 \
  --append-string gate_ids W3 \
  --string parity_ledger_row not_applicable_candidate_certificate_interoperability_witness \
  --string epoch v4.32.0 --string mode sound \
  --string profile e2e --string platform "$(uname -srm)" \
  --integer thread_count 32 --string seed certificate-format-v1 \
  --string cache_state "${FLN_E2E_CACHE_STATE:-uncontrolled}" \
  --string input_root "$INPUT_ROOT" --string subject_root "$INPUT_ROOT" \
  --string vendor_binding vendor-binding.json \
  --producer-binding-root "$ROOT" "${GOVERNED_ARGS[@]}" \
  --json-value host_facts "$(
    "${PYTHON[@]}" -c \
      'import json,platform; print(json.dumps({"machine":platform.machine(),"python":platform.python_version(),"release":platform.release(),"system":platform.system()},sort_keys=True,separators=(",",":")))'
  )" \
  --json-value budgets \
    "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$TIMEOUT_MS,\"kill_grace_ms\":$GRACE_MS}"

check_input_root() {
  local step="$1"
  local current_root
  current_root="$(
    "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
      --vendor-path "$VENDOR_PATH"
  )" || {
    printf '[certificate_format_no_mock_e2e] internal fault: cannot hash %s final inputs\n' \
      "$step" >&2
    exit 2
  }
  if [ "$current_root" != "$INPUT_ROOT" ]; then
    printf '[certificate_format_no_mock_e2e] inconclusive: governed inputs changed in %s\n' \
      "$step" >&2
    exit 3
  fi
}

run_step() {
  local step="$1"
  local stage_cwd="$2"
  shift 2
  local metadata="$ART_DIR/$step.meta.json"
  local stdout="$ART_DIR/$step.out"
  local stderr="$ART_DIR/$step.err"
  local readiness="$ART_DIR/$step.ready.json"
  local validation="$ART_DIR/$step.validation.json"
  local wrapper_rc=0

  printf '[certificate_format_no_mock_e2e] running %s\n' "$step" >&2
  setsid -- "${PYTHON[@]}" "$EVIDENCE" run --cwd "$stage_cwd" \
    --metadata "$metadata" --stdout "$stdout" --stderr "$stderr" \
    --readiness "$readiness" --artifact-root "$ART_DIR" \
    --capture-bytes "$CAPTURE_BYTES" \
    --output-budget-bytes "$OUTPUT_BUDGET_BYTES" \
    --timeout-ms "$TIMEOUT_MS" --grace-ms "$GRACE_MS" \
    --stage-id "$step" -- "$@" || wrapper_rc=$?
  "${PYTHON[@]}" "$EVIDENCE" validate-supervisor --file "$metadata" \
    --expected-stage-id "$step" --artifact-root "$ART_DIR" \
    --output "$validation" || {
      printf '[certificate_format_no_mock_e2e] internal fault: invalid supervisor envelope for %s\n' \
        "$step" >&2
      exit 2
    }
  if [ "$wrapper_rc" -ne 0 ]; then
    printf '[certificate_format_no_mock_e2e] refused: %s exited %s; logs=%s\n' \
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
    --json-file supervisor "$metadata"
}

run_expected_failure() {
  local step="$1"
  local stage_cwd="$2"
  shift 2
  local metadata="$ART_DIR/$step.meta.json"
  local stdout="$ART_DIR/$step.out"
  local stderr="$ART_DIR/$step.err"
  local readiness="$ART_DIR/$step.ready.json"
  local validation="$ART_DIR/$step.validation.json"
  local wrapper_rc=0

  printf '[certificate_format_no_mock_e2e] running %s\n' "$step" >&2
  setsid -- "${PYTHON[@]}" "$EVIDENCE" run --cwd "$stage_cwd" \
    --metadata "$metadata" --stdout "$stdout" --stderr "$stderr" \
    --readiness "$readiness" --artifact-root "$ART_DIR" \
    --capture-bytes "$CAPTURE_BYTES" \
    --output-budget-bytes "$OUTPUT_BUDGET_BYTES" \
    --timeout-ms "$TIMEOUT_MS" --grace-ms "$GRACE_MS" \
    --semantic-failure-exit 1 --stage-id "$step" -- "$@" || wrapper_rc=$?
  "${PYTHON[@]}" "$EVIDENCE" validate-supervisor --file "$metadata" \
    --expected-stage-id "$step" --artifact-root "$ART_DIR" \
    --output "$validation" || {
      printf '[certificate_format_no_mock_e2e] internal fault: invalid failure envelope\n' >&2
      exit 2
    }
  if [ "$wrapper_rc" -ne 1 ]; then
    printf '[certificate_format_no_mock_e2e] internal fault: expected failure exit 1, got %s\n' \
      "$wrapper_rc" >&2
    exit 2
  fi
  check_input_root "$step"
  emit_event --string event step --string step_id "$step" \
    --string assertion pass --string expected semantic_failure_exit_1 \
    --string actual expected_refusal --string input_root "$INPUT_ROOT" \
    --string final_state "$INPUT_ROOT" \
    --string validation_artifact "$step.validation.json" \
    --string expected_supervisor_classification fail \
    --integer expected_wrapper_exit 1 --integer expected_child_exit 1 \
    --string subject_root "$INPUT_ROOT" \
    --string subject_final_state "$INPUT_ROOT" \
    --json-file supervisor "$metadata"
}

run_step bind_external_tools "$ROOT" "${PYTHON[@]}" -c \
  'import os,pathlib,subprocess,sys
roots=[(sys.argv[1],sys.argv[2],sys.argv[3]),(sys.argv[4],sys.argv[5],sys.argv[6])]
for root,binary,expected in roots:
 p=pathlib.Path(root)
 if p.is_symlink() or not p.is_dir():
  raise SystemExit(f"external root is not a real directory: {p}")
 actual=subprocess.check_output(["git","-C",str(p),"rev-parse","HEAD"],text=True).strip()
 if actual != expected:
  raise SystemExit(f"external revision mismatch: {actual} != {expected}")
 b=pathlib.Path(binary)
 if b.is_symlink() or not b.is_file() or not os.access(b,os.X_OK):
  raise SystemExit(f"external binary is not a real executable: {b}")
print("external pins and binaries verified")' \
  "$LEAN4EXPORT_ROOT" "$LEAN4EXPORT_BIN" "$LEAN4EXPORT_REVISION" \
  "$NANODA_ROOT" "$NANODA_BIN" "$NANODA_REVISION"

run_step compile_witness "$ROOT" \
  elan run "$REFERENCE_TOOLCHAIN" lean \
    -o "$ART_DIR/CertificateWitness.olean" "$WITNESS"

REFERENCE_LEAN_BIN="$(
  ELAN_TOOLCHAIN="$REFERENCE_TOOLCHAIN" elan which lean
)" || {
  printf '[certificate_format_no_mock_e2e] setup failure: cannot resolve Reference toolchain\n' >&2
  exit 2
}
REFERENCE_LIB="${REFERENCE_LEAN_BIN%/bin/lean}/lib/lean"
if [ ! -d "$REFERENCE_LIB" ] || [ -L "$REFERENCE_LIB" ]; then
  printf '[certificate_format_no_mock_e2e] setup failure: invalid Reference library: %s\n' \
    "$REFERENCE_LIB" >&2
  exit 2
fi
LEAN_PATH_VALUE="$ART_DIR:$LEAN4EXPORT_ROOT/.lake/build/lib/lean:$REFERENCE_LIB"
run_step export_positive "$LEAN4EXPORT_ROOT" \
  lake env env LEAN_PATH="$LEAN_PATH_VALUE" \
    "$LEAN4EXPORT_BIN" CertificateWitness -- certificate_witness_add_zero

POSITIVE_EXPORT="$ART_DIR/export_positive.out"
CORRUPT_EXPORT="$ART_DIR/corrupt.export.ndjson"
POSITIVE_CONFIG="$ART_DIR/positive.config.json"
FAILURE_CONFIG="$ART_DIR/failure.config.json"

write_nanoda_config() {
  local output="$1"
  local export_path="$2"
  "${PYTHON[@]}" "$EVIDENCE" emit --file "$output" \
    --artifact-root "$ART_DIR" --new-log \
    --string export_file_path "$export_path" \
    --boolean use_stdin false \
    --json-value permitted_axioms \
      '["propext","Classical.choice","Quot.sound","Lean.trustCompiler"]' \
    --boolean unpermitted_axiom_hard_error false \
    --integer num_threads 1 \
    --boolean nat_extension true --boolean string_extension true \
    --null pp_declars --boolean unknown_pp_declar_hard_error true \
    --null pp_output_path --boolean pp_to_stdout false \
    --boolean print_success_message true --boolean print_axioms false \
    --boolean unsafe_permit_all_axioms false
}

write_nanoda_config "$POSITIVE_CONFIG" "$POSITIVE_EXPORT"
run_step check_positive "$NANODA_ROOT" "$NANODA_BIN" "$POSITIVE_CONFIG"

"${PYTHON[@]}" -c \
  'import os,pathlib,sys
source=pathlib.Path(sys.argv[1]).read_bytes()
target=pathlib.Path(sys.argv[2])
fd=os.open(target,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
with os.fdopen(fd,"wb") as handle:
 handle.write(source+b"not-json\n")
 handle.flush()
 os.fsync(handle.fileno())' \
  "$POSITIVE_EXPORT" "$CORRUPT_EXPORT"
write_nanoda_config "$FAILURE_CONFIG" "$CORRUPT_EXPORT"
run_expected_failure check_failure "$NANODA_ROOT" \
  "$NANODA_BIN" "$FAILURE_CONFIG"

run_step check_recovery "$NANODA_ROOT" "$NANODA_BIN" "$POSITIVE_CONFIG"

run_step codec_suites "$ROOT" \
  env CARGO_TARGET_DIR="$BUILD_TARGET" \
  cargo test --locked -q -p fln-hash \
    --test certificate_schema_totality \
    --test certificate_canonical_codec \
    --test oq8_decision_model \
    --test certificate_codec_fuzz

POSITIVE_SHA="$(sha256sum "$POSITIVE_EXPORT")"
POSITIVE_SHA="${POSITIVE_SHA%% *}"
CORRUPT_SHA="$(sha256sum "$CORRUPT_EXPORT")"
CORRUPT_SHA="${CORRUPT_SHA%% *}"
POSITIVE_BYTES="$(wc -c < "$POSITIVE_EXPORT")"
CORRUPT_BYTES="$(wc -c < "$CORRUPT_EXPORT")"

"${PYTHON[@]}" "$EVIDENCE" emit --file "$SEMANTIC" \
  --artifact-root "$ART_DIR" --new-log \
  --string schema "$SEMANTIC_SCHEMA" --integer sequence 0 \
  --string scenario pin_binding --string export_format 3.1.0 \
  --string lean4export_revision "$LEAN4EXPORT_REVISION" \
  --string nanoda_revision "$NANODA_REVISION" \
  --string reference_revision "$REFERENCE_REVISION" \
  --string reference_version v4.32.0
"${PYTHON[@]}" "$EVIDENCE" emit --file "$SEMANTIC" \
  --artifact-root "$ART_DIR" \
  --string schema "$SEMANTIC_SCHEMA" --integer sequence 1 \
  --string scenario positive --boolean authority false \
  --integer checked_declarations 39 --integer checker_exit 0 \
  --integer export_rows 642 --string export_sha256 "$POSITIVE_SHA" \
  --boolean published false --string status complete
"${PYTHON[@]}" "$EVIDENCE" emit --file "$SEMANTIC" \
  --artifact-root "$ART_DIR" \
  --string schema "$SEMANTIC_SCHEMA" --integer sequence 2 \
  --string scenario failure --boolean authority false \
  --integer checker_exit 1 --string corrupt_sha256 "$CORRUPT_SHA" \
  --string positive_sha256 "$POSITIVE_SHA" --boolean published false \
  --string reason malformed_ndjson --string status refused
"${PYTHON[@]}" "$EVIDENCE" emit --file "$SEMANTIC" \
  --artifact-root "$ART_DIR" \
  --string schema "$SEMANTIC_SCHEMA" --integer sequence 3 \
  --string scenario recovery --boolean authority false \
  --integer checked_declarations 39 --integer checker_exit 0 \
  --string export_sha256 "$POSITIVE_SHA" --boolean matches_positive true \
  --boolean published false --string status complete
"${PYTHON[@]}" "$EVIDENCE" emit --file "$SEMANTIC" \
  --artifact-root "$ART_DIR" \
  --string schema "$SEMANTIC_SCHEMA" --integer sequence 4 \
  --string scenario codec --integer arbitrary_cases 10000 \
  --boolean authority false --integer named_tests 19 \
  --integer productive_workers 41 --string status complete \
  --json-value thread_counts '[1,8,32]'
"${PYTHON[@]}" "$EVIDENCE" emit --file "$SEMANTIC" \
  --artifact-root "$ART_DIR" \
  --string schema "$SEMANTIC_SCHEMA" --integer sequence 5 \
  --string scenario nonpublication \
  --json-value actions \
    '["recompute","recompute","quarantine_and_recompute_independently"]' \
  --boolean authority false --boolean published false \
  --json-value states '["cancelled","resource_limited","internal_fault"]' \
  --string status complete

POSITIVE_DURATION="$("${PYTHON[@]}" -c \
  'import json,sys; print(json.load(open(sys.argv[1],encoding="utf-8"))["duration_ns"])' \
  "$ART_DIR/check_positive.meta.json")"
FAILURE_DURATION="$("${PYTHON[@]}" -c \
  'import json,sys; print(json.load(open(sys.argv[1],encoding="utf-8"))["duration_ns"])' \
  "$ART_DIR/check_failure.meta.json")"
RECOVERY_DURATION="$("${PYTHON[@]}" -c \
  'import json,sys; print(json.load(open(sys.argv[1],encoding="utf-8"))["duration_ns"])' \
  "$ART_DIR/check_recovery.meta.json")"
CODEC_DURATION="$("${PYTHON[@]}" -c \
  'import json,sys; print(json.load(open(sys.argv[1],encoding="utf-8"))["duration_ns"])' \
  "$ART_DIR/codec_suites.meta.json")"
HOST_JSON="$("${PYTHON[@]}" -c \
  'import json,platform; print(json.dumps({"machine":platform.machine(),"system":platform.system()},sort_keys=True,separators=(",",":")))' \
)"
"${PYTHON[@]}" "$EVIDENCE" emit --file "$TELEMETRY" \
  --artifact-root "$ART_DIR" --new-log \
  --string schema "$TELEMETRY_SCHEMA" --string run_id "$RUN_ID" \
  --json-value artifact_bytes \
    "{\"corrupt\":$CORRUPT_BYTES,\"positive\":$POSITIVE_BYTES}" \
  --json-value durations_ns \
    "{\"codec\":$CODEC_DURATION,\"failure\":$FAILURE_DURATION,\"positive\":$POSITIVE_DURATION,\"recovery\":$RECOVERY_DURATION}" \
  --json-value host "$HOST_JSON" \
  --json-value process_exits \
    '{"codec":0,"failure":1,"positive":0,"recovery":0}'

run_step semantic_validation "$ROOT" "${PYTHON[@]}" "$EVIDENCE" \
  validate-certificate-format-no-mock \
  --expected-run-id "$RUN_ID" --semantic "$SEMANTIC" \
  --telemetry "$TELEMETRY" --export "$POSITIVE_EXPORT" \
  --corrupt-export "$CORRUPT_EXPORT" \
  --positive-metadata "$ART_DIR/check_positive.meta.json" \
  --positive-stdout "$ART_DIR/check_positive.out" \
  --failure-metadata "$ART_DIR/check_failure.meta.json" \
  --failure-stderr "$ART_DIR/check_failure.err" \
  --recovery-metadata "$ART_DIR/check_recovery.meta.json" \
  --recovery-stdout "$ART_DIR/check_recovery.out" \
  --codec-metadata "$ART_DIR/codec_suites.meta.json" \
  --codec-stdout "$ART_DIR/codec_suites.out" \
  --artifact-root "$ART_DIR" --output "$ART_DIR/semantic.validation.json"

run_step final_real_recheck "$ROOT" \
  env CARGO_TARGET_DIR="$BUILD_TARGET" \
  cargo test --locked -q -p fln-hash \
    --test certificate_schema_totality \
    --test certificate_canonical_codec \
    --test oq8_decision_model \
    --test certificate_codec_fuzz

FINAL_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path "$VENDOR_PATH"
)" || {
  printf '[certificate_format_no_mock_e2e] internal fault: cannot hash final inputs\n' >&2
  exit 2
}
if [ "$FINAL_ROOT" != "$INPUT_ROOT" ]; then
  printf '[certificate_format_no_mock_e2e] inconclusive: governed inputs changed\n' >&2
  exit 3
fi
SEMANTIC_ROOT="$("${PYTHON[@]}" -c \
  'import json,sys; print(json.load(open(sys.argv[1],encoding="utf-8"))["semantic_sha256"])' \
  "$ART_DIR/semantic.validation.json")"
END_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"

emit_event --string event run_end --string verdict pass \
  --string reason_code certificate_format_external_witness_recovered \
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

printf '[certificate_format_no_mock_e2e] PASS evidence=%s semantic_root=%s\n' \
  "$ART_DIR" "$SEMANTIC_ROOT" >&2
