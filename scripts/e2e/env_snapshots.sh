#!/usr/bin/env bash
# env_snapshots.sh — shared E2E scenario for the Grimoire environment (bead fln-amv).
#
# Real-path, no-mock: runs the real fln-env suite (persistent-map model tests,
# snapshot isolation, logical-root determinism across thread counts), captures
# detailed journal/checkpoint evidence through the real Environment APIs, then
# seeds a REAL bug class into an overlay workspace — add_decl silently dropping
# extension state — and proves the suite KILLS the mutant (a surviving mutant is
# a failed scenario), then delegates the historical full-hash bucket
# append-order proof to an authoritative nested fln.e2e/2 evidence bundle.
# NDJSON under target/e2e/.

set -euo pipefail

command -v python3 >/dev/null 2>&1 || {
  echo "[env_snapshots] setup failure: python3 is required" >&2
  exit 2
}
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
EVIDENCE="$ROOT/scripts/evidence.py"
RUN_ID="env-snapshots-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$ART_DIR"

BEAD="fln-amv"
SCHEMA="fln-e2e/1"
HOST="$(uname -sr)"
start_ns=$(date +%s%N)

emit() { # emit <step_id> <status> <detail-json-fragment>
  local now_ns
  now_ns=$(date +%s%N)
  printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"env_snapshots","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
    "$SCHEMA" "$RUN_ID" "$BEAD" "$1" "$2" $(( (now_ns - start_ns) / 1000000 )) "$HOST" "$3" >> "$LOG"
}

note() { echo "[env_snapshots] $*" >&2; }

emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"$0\""

# ---- step 1: the real suite ------------------------------------------------------------
note "running the fln-env suite (pmap model, isolation, root determinism)"
set +e
( cd "$ROOT" && CARGO_TARGET_DIR=target_local cargo test --locked -q -p fln-env ) \
  > "$ART_DIR/suite.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit suite failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"suite.log\""
  note "FAIL: fln-env suite failed (see $ART_DIR/suite.log)"
  exit 1
fi
emit suite passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"suite.log\""

# ---- step 2: detailed persistent-journal and checkpoint evidence -----------------------
note "capturing real Environment journal/checkpoint evidence"
set +e
( cd "$ROOT" && FLN_ENV_E2E_RUN_ID="$RUN_ID" CARGO_TARGET_DIR=target_local \
    cargo test --locked -q -p fln-env \
      extensions::tests::environment_state_e2e_emits_detailed_real_path_evidence \
      -- --exact --nocapture ) > "$ART_DIR/environment_state.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit environment_state failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"environment_state.log\""
  note "FAIL: real environment-state scenario failed (see $ART_DIR/environment_state.log)"
  exit 1
fi
evidence_count=$(awk 'index($0, "{\"schema\":\"fln.e2e.environment-state\",\"version\":1") == 1 { count++ } END { print count + 0 }' "$ART_DIR/environment_state.log")
passed_count=$(awk 'index($0, "{\"schema\":\"fln.e2e.environment-state\",\"version\":1") == 1 && index($0, "\"status\":\"pass\"") > 0 { count++ } END { print count + 0 }' "$ART_DIR/environment_state.log")
if [ "$evidence_count" -ne 4 ] || [ "$passed_count" -ne 4 ]; then
  emit environment_state failed "\"expected_records\":4,\"actual_records\":$evidence_count,\"passed_records\":$passed_count,\"artifact\":\"environment_state.log\""
  note "FAIL: environment-state evidence was missing, malformed, or non-passing"
  exit 1
fi
awk 'index($0, "{\"schema\":\"fln.e2e.environment-state\",\"version\":1") == 1 { print }' \
  "$ART_DIR/environment_state.log" >> "$LOG"
emit environment_state passed "\"expected_exit\":0,\"actual_exit\":0,\"evidence_records\":$evidence_count,\"artifact\":\"environment_state.log\""

# ---- step 4: extension-state mutant must be killed -------------------------------------
OVERLAY="$ART_DIR/overlay"
mkdir -p "$OVERLAY"
for crate in fln-core fln-hash fln-env; do
  cp -r "$ROOT/crates/$crate" "$OVERLAY/$crate"
done
cat > "$OVERLAY/Cargo.toml" <<'EOF'
[workspace]
resolver = "3"
members = ["fln-core", "fln-hash", "fln-env"]
EOF
cp "$ROOT/rust-toolchain.toml" "$OVERLAY/rust-toolchain.toml"
cp "$ROOT/Cargo.lock" "$OVERLAY/Cargo.lock"
# The mutant: add_decl silently discards extension state (a real bug class the
# snapshot/root tests exist to kill).
sed -i 's/extensions: self.extensions.clone(),/extensions: crate::pmap::PMap::new(),/' \
  "$OVERLAY/fln-env/src/environment.rs"
if ! grep -q "PMap::new()," "$OVERLAY/fln-env/src/environment.rs"; then
  emit seeded_mutant failed "\"detail\":\"mutation seed was a no-op\""
  note "FAIL: mutation seed did not apply"
  exit 1
fi
set +e
( cd "$OVERLAY" && CARGO_TARGET_DIR="$OVERLAY/target" cargo test --locked -q -p fln-env ) \
  > "$ART_DIR/mutant.log" 2>&1
rc=$?
set -e
if [ "$rc" -eq 0 ]; then
  emit seeded_mutant failed "\"expected_exit\":\"nonzero\",\"actual_exit\":0,\"artifact\":\"mutant.log\""
  note "FAIL: the extension-dropping mutant SURVIVED the suite"
  exit 1
fi
emit seeded_mutant passed "\"expected_exit\":\"nonzero\",\"actual_exit\":$rc,\"detected\":\"extension-state-dropping mutant killed\",\"artifact\":\"mutant.log\""

# ---- step 5: extension-state recovery — pristine overlay passes ------------------------
sed -i 's/extensions: crate::pmap::PMap::new(),/extensions: self.extensions.clone(),/' \
  "$OVERLAY/fln-env/src/environment.rs"
set +e
( cd "$OVERLAY" && CARGO_TARGET_DIR="$OVERLAY/target" cargo test --locked -q -p fln-env ) \
  > "$ART_DIR/recovered.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit recovery failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"recovered.log\""
  note "FAIL: pristine overlay no longer passes"
  exit 1
fi
emit recovery passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"recovered.log\""

# ---- nested fln-amv.10 collision evidence bundle --------------------------------------
# Collision detail belongs exclusively to this authoritative fln.e2e/2 child. The
# legacy parent journal receives one pointer only after the child bundle commits.
COLLISION_SCHEMA="fln.e2e/2"
COLLISION_BEAD="fln-amv.10"
COLLISION_SCENARIO="environment_collision"
COLLISION_RUN_ID="$RUN_ID-collision-fln-amv-10"
COLLISION_ART_DIR="$ART_DIR/collision-fln-amv.10"
COLLISION_LOG="$COLLISION_ART_DIR/run.ndjson"
COLLISION_HUMAN="$COLLISION_ART_DIR/human.log"
COLLISION_VENDOR_PATH="vendor/lean4-src"
COLLISION_VENDOR_BINDING="$COLLISION_ART_DIR/vendor-binding.json"
COLLISION_SEQ=0
COLLISION_START_NS="$(python3 -c 'import time; print(time.monotonic_ns())')"
COLLISION_CAPTURE_BYTES="${FLN_E2E_CAPTURE_BYTES:-262144}"
COLLISION_OUTPUT_BUDGET_BYTES="${FLN_E2E_OUTPUT_BUDGET_BYTES:-16777216}"
COLLISION_TIMEOUT_MS="${FLN_E2E_TIMEOUT_MS:-300000}"
COLLISION_GRACE_MS="${FLN_E2E_KILL_GRACE_MS:-2000}"
COLLISION_CACHE_STATE="${FLN_E2E_CACHE_STATE:-uncontrolled}"
COLLISION_CARGO_ARGV="cargo test --locked -q -p fln-env pmap::tests::environment_collision_e2e_emits_detailed_real_path_evidence -- --exact --nocapture"
COLLISION_INPUT_PATHS=(
  Cargo.toml Cargo.lock SUITE.lock rust-toolchain.toml
  crates/fln-core crates/fln-hash crates/fln-env
  vendor/NOTICE scripts/check.sh scripts/evidence.py scripts/verify_vendor_tree.sh
  scripts/e2e/env_snapshots.sh .github/workflows/ci.yml
)
COLLISION_HASH_ARGS=()
COLLISION_GOVERNED_ARGS=()
for collision_input_path in "${COLLISION_INPUT_PATHS[@]}"; do
  COLLISION_HASH_ARGS+=(--path "$collision_input_path")
  COLLISION_GOVERNED_ARGS+=(--governed-path "$collision_input_path")
done

collision_note() {
  printf '[env_snapshots:fln-amv.10] %s\n' "$*" | tee -a "$COLLISION_HUMAN" >&2
}

collision_emit_event() {
  local sequence="$COLLISION_SEQ"
  COLLISION_SEQ=$((COLLISION_SEQ + 1))
  python3 "$EVIDENCE" emit --file "$COLLISION_LOG" --artifact-root "$COLLISION_ART_DIR" \
    --string schema "$COLLISION_SCHEMA" --string run_id "$COLLISION_RUN_ID" \
    --string bead "$COLLISION_BEAD" --string scenario "$COLLISION_SCENARIO" \
    --integer sequence "$sequence" \
    --integer monotonic_ns "$(python3 -c 'import time; print(time.monotonic_ns())')" \
    --string wall_time_utc "$(date -u -Is)" "$@"
}

collision_hash_live() {
  python3 "$EVIDENCE" hash-tree --root "$ROOT" "${COLLISION_HASH_ARGS[@]}" \
    --vendor-path "$COLLISION_VENDOR_PATH"
}

collision_hash_subject() {
  python3 "$EVIDENCE" hash-tree --root "$1" --path "$2"
}

collision_file_sha256() {
  python3 - "$1" <<'PY'
import hashlib
import pathlib
import sys

digest = hashlib.sha256()
with pathlib.Path(sys.argv[1]).open("rb") as stream:
    for block in iter(lambda: stream.read(1024 * 1024), b""):
        digest.update(block)
print(digest.hexdigest())
PY
}

collision_meta_field() {
  python3 - "$1" "$2" <<'PY'
import json
import pathlib
import sys

value = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))[sys.argv[2]]
if value is None:
    print("null")
elif value is True:
    print("true")
elif value is False:
    print("false")
else:
    print(value)
PY
}

collision_supervise() {
  local step="$1" cwd="$2" semantic_exit="$3" planted="$4"
  shift 4
  local -a semantic_args=()
  COLLISION_LAST_META="$COLLISION_ART_DIR/$step.meta.json"
  COLLISION_LAST_OUT="$COLLISION_ART_DIR/$step.out"
  COLLISION_LAST_ERR="$COLLISION_ART_DIR/$step.err"
  COLLISION_LAST_READY="$COLLISION_ART_DIR/$step.ready.json"
  if [ "$semantic_exit" != none ]; then
    semantic_args+=(--semantic-failure-exit "$semantic_exit")
  fi
  if [ "$planted" = true ]; then
    semantic_args+=(--planted)
  fi
  collision_note "running step=$step cwd=$cwd"
  set +e
  python3 "$EVIDENCE" run --cwd "$cwd" \
    --metadata "$COLLISION_LAST_META" --stdout "$COLLISION_LAST_OUT" \
    --stderr "$COLLISION_LAST_ERR" --readiness "$COLLISION_LAST_READY" \
    --artifact-root "$COLLISION_ART_DIR" --capture-bytes "$COLLISION_CAPTURE_BYTES" \
    --output-budget-bytes "$COLLISION_OUTPUT_BUDGET_BYTES" \
    --timeout-ms "$COLLISION_TIMEOUT_MS" --grace-ms "$COLLISION_GRACE_MS" \
    --stage-id "$step" "${semantic_args[@]}" -- "$@"
  COLLISION_LAST_RC=$?
  set -e
}

collision_assert_supervisor() {
  local step="$1" expected_class="$2" expected_wrapper="$3" expected_child="$4"
  local expected_planted="$5"
  if [ ! -s "$COLLISION_LAST_META" ]; then
    collision_note "FAIL step=$step: missing supervisor metadata"
    exit 2
  fi
  COLLISION_LAST_CLASS="$(collision_meta_field "$COLLISION_LAST_META" classification)"
  COLLISION_LAST_WRAPPER="$(collision_meta_field "$COLLISION_LAST_META" wrapper_exit)"
  COLLISION_LAST_CHILD="$(collision_meta_field "$COLLISION_LAST_META" child_exit)"
  COLLISION_LAST_PLANTED="$(collision_meta_field "$COLLISION_LAST_META" planted)"
  if [ "$COLLISION_LAST_RC" != "$expected_wrapper" ] || \
     [ "$COLLISION_LAST_CLASS" != "$expected_class" ] || \
     [ "$COLLISION_LAST_WRAPPER" != "$expected_wrapper" ] || \
     [ "$COLLISION_LAST_CHILD" != "$expected_child" ] || \
     [ "$COLLISION_LAST_PLANTED" != "$expected_planted" ]; then
    collision_note "FAIL step=$step: expected $expected_class/wrapper=$expected_wrapper/child=$expected_child/planted=$expected_planted, got $COLLISION_LAST_CLASS/wrapper=$COLLISION_LAST_RC/child=$COLLISION_LAST_CHILD/planted=$COLLISION_LAST_PLANTED"
    exit 1
  fi
}

collision_record_step() {
  local step="$1" expected="$2" actual="$3" validation="$4"
  local expected_class="$5" expected_wrapper="$6" expected_child="$7"
  local subject_root="$8" subject_final_state="$9"
  local global_root="${10}" global_final_state="${11}"
  collision_emit_event --string event step --string step_id "$step" \
    --string assertion pass --string expected "$expected" --string actual "$actual" \
    --string input_root "$global_root" --string final_state "$global_final_state" \
    --string validation_artifact "$validation" \
    --string expected_supervisor_classification "$expected_class" \
    --integer expected_wrapper_exit "$expected_wrapper" \
    --integer expected_child_exit "$expected_child" \
    --string subject_root "$subject_root" \
    --string subject_final_state "$subject_final_state" \
    --json-file supervisor "$COLLISION_LAST_META"
}

collision_assert_unchanged() {
  local step="$1" subject_before="$2" subject_after="$3"
  local global_before="$4" global_after="$5"
  if [ "$subject_before" != "$subject_after" ]; then
    collision_note "FAIL step=$step: subject changed during supervised assertion"
    exit 3
  fi
  if [ "$global_before" != "$COLLISION_INPUT_ROOT" ] || \
     [ "$global_after" != "$COLLISION_INPUT_ROOT" ]; then
    collision_note "FAIL step=$step: governed live input changed"
    exit 3
  fi
}

# Hash the complete live input before creating a child directory that could look
# like committed evidence, then bind the exact pinned Reference tree.
if ! COLLISION_INPUT_ROOT="$(collision_hash_live)"; then
  note "FAIL: cannot hash fln-amv.10 governed inputs"
  exit 2
fi
if [ -e "$COLLISION_ART_DIR" ] || [ -L "$COLLISION_ART_DIR" ]; then
  note "FAIL: refusing reused collision evidence directory $COLLISION_ART_DIR"
  exit 2
fi
mkdir "$COLLISION_ART_DIR"
python3 "$EVIDENCE" vendor-binding --root "$ROOT" \
  --vendor-path "$COLLISION_VENDOR_PATH" --output "$COLLISION_VENDOR_BINDING" \
  --artifact-root "$COLLISION_ART_DIR" || {
    note "FAIL: cannot bind the pinned Reference tree for fln-amv.10"
    exit 2
  }

COLLISION_LIVE_SUBJECT_SHA="$(collision_file_sha256 "$ROOT/crates/fln-env/src/pmap.rs")"
COLLISION_LIVE_HEAD="$(git -C "$ROOT" rev-parse HEAD)"
collision_emit_event --new-log --string event run_start \
  --json-value argv '["scripts/e2e/env_snapshots.sh"]' \
  --string cwd "$ROOT" \
  --append-string claim_ids fln-amv.10-collision-canonicality \
  --append-string invariant_ids FL-INV-01 \
  --append-string gate_ids PG-5 \
  --string parity_ledger_row not_applicable_internal_data_structure_determinism \
  --string epoch lean-v4.32.0 --string mode sound --string profile e2e \
  --string platform "$(uname -srm)" \
  --json-value host_facts "$(python3 -c 'import json,platform; print(json.dumps({"system":platform.system(),"release":platform.release(),"machine":platform.machine(),"python":platform.python_version()},separators=(",",":")))')" \
  --integer thread_count 32 --string seed partition-rotation-v1 \
  --json-value thread_matrix '[1,8,32]' \
  --string cache_state "$COLLISION_CACHE_STATE" \
  --string input_root "$COLLISION_INPUT_ROOT" \
  --string vendor_binding vendor-binding.json \
  --string live_head "$COLLISION_LIVE_HEAD" \
  --string live_subject_sha256 "$COLLISION_LIVE_SUBJECT_SHA" \
  --json-value budgets "{\"capture_bytes_per_stream\":$COLLISION_CAPTURE_BYTES,\"output_budget_bytes\":$COLLISION_OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$COLLISION_TIMEOUT_MS,\"kill_grace_ms\":$COLLISION_GRACE_MS,\"max_collision_cardinality\":96}"
: > "$COLLISION_HUMAN"

if [ ! -f "$OVERLAY/Cargo.lock" ]; then
  collision_note "FAIL: recovered overlay lacks the Cargo.lock required by --locked"
  exit 2
fi
COLLISION_PRISTINE_SOURCE="$COLLISION_ART_DIR/pmap.pristine.rs"
cp -- "$OVERLAY/fln-env/src/pmap.rs" "$COLLISION_PRISTINE_SOURCE"
COLLISION_PRISTINE_SHA="$(collision_file_sha256 "$COLLISION_PRISTINE_SOURCE")"
if [ "$COLLISION_PRISTINE_SHA" != "$COLLISION_LIVE_SUBJECT_SHA" ]; then
  collision_note "FAIL: recovered overlay pmap.rs is not byte-identical to the live subject"
  exit 3
fi
COLLISION_PRISTINE_SUBJECT_ROOT="$(collision_hash_subject "$OVERLAY" fln-env/src/pmap.rs)"

# Positive: the live subject emits exactly the v2 rows for {1,8,32}.
COLLISION_POSITIVE_SUBJECT_BEFORE="$(collision_hash_subject "$ROOT" crates/fln-env/src/pmap.rs)"
COLLISION_POSITIVE_GLOBAL_BEFORE="$(collision_hash_live)"
collision_supervise collision_positive "$ROOT" none false \
  env FLN_ENV_E2E_RUN_ID="$COLLISION_RUN_ID" \
  FLN_ENV_E2E_STDOUT_ARTIFACT=collision_positive.out \
  FLN_ENV_E2E_STDERR_ARTIFACT=collision_positive.err \
  FLN_ENV_E2E_ARGV="$COLLISION_CARGO_ARGV" \
  FLN_ENV_E2E_CACHE_STATE="$COLLISION_CACHE_STATE" \
  CARGO_TARGET_DIR=target_local \
  cargo test --locked -q -p fln-env \
  pmap::tests::environment_collision_e2e_emits_detailed_real_path_evidence \
  -- --exact --nocapture
collision_assert_supervisor collision_positive pass 0 0 false
COLLISION_POSITIVE_SUBJECT_AFTER="$(collision_hash_subject "$ROOT" crates/fln-env/src/pmap.rs)"
COLLISION_POSITIVE_GLOBAL_AFTER="$(collision_hash_live)"
collision_assert_unchanged collision_positive \
  "$COLLISION_POSITIVE_SUBJECT_BEFORE" "$COLLISION_POSITIVE_SUBJECT_AFTER" \
  "$COLLISION_POSITIVE_GLOBAL_BEFORE" "$COLLISION_POSITIVE_GLOBAL_AFTER"
COLLISION_POSITIVE_VALIDATION="$COLLISION_ART_DIR/collision_positive.validation.json"
python3 "$EVIDENCE" validate-environment-collision \
  --file "$COLLISION_LAST_OUT" --stderr-file "$COLLISION_LAST_ERR" --phase positive \
  --expected-run-id "$COLLISION_RUN_ID" --observed-exit "$COLLISION_LAST_CHILD" \
  --expected-cwd "$ROOT/crates/fln-env" --expected-argv "$COLLISION_CARGO_ARGV" \
  --expected-stdout-artifact collision_positive.out \
  --expected-stderr-artifact collision_positive.err \
  --expected-cache-state "$COLLISION_CACHE_STATE" \
  --artifact-root "$COLLISION_ART_DIR" --output "$COLLISION_POSITIVE_VALIDATION"
collision_record_step collision_positive \
  "environment-collision/1:positive/pass/wrapper=0/child=0/sha256=$COLLISION_LIVE_SUBJECT_SHA" \
  "$COLLISION_LAST_CLASS/wrapper=$COLLISION_LAST_RC/child=$COLLISION_LAST_CHILD/sha256=$COLLISION_LIVE_SUBJECT_SHA" \
  collision_positive.validation.json pass 0 0 \
  "$COLLISION_POSITIVE_SUBJECT_BEFORE" "$COLLISION_POSITIVE_SUBJECT_AFTER" \
  "$COLLISION_POSITIVE_GLOBAL_BEFORE" "$COLLISION_POSITIVE_GLOBAL_AFTER"

# Mutant: change exactly one anchor in the retained overlay and classify Cargo's
# semantic test failure (101) as fail/wrapper=1, never as an internal fault.
if ! python3 - "$OVERLAY/fln-env/src/pmap.rs" <<'PY'
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
source = path.read_bytes()
anchor = b"new_entries.insert(pos, (key, value));"
replacement = b"new_entries.push((key, value));"
if source.count(anchor) != 1:
    raise SystemExit("collision mutation anchor count is not exactly one")
path.write_bytes(source.replace(anchor, replacement, 1))
PY
then
  collision_note "FAIL: collision mutation did not match exactly one overlay anchor"
  exit 2
fi
COLLISION_MUTANT_SHA="$(collision_file_sha256 "$OVERLAY/fln-env/src/pmap.rs")"
if [ "$COLLISION_MUTANT_SHA" = "$COLLISION_PRISTINE_SHA" ]; then
  collision_note "FAIL: collision mutation did not change the overlay subject"
  exit 2
fi
COLLISION_MUTANT_SUBJECT_BEFORE="$(collision_hash_subject "$OVERLAY" fln-env/src/pmap.rs)"
COLLISION_MUTANT_GLOBAL_BEFORE="$(collision_hash_live)"
collision_supervise collision_mutant "$OVERLAY" 101 true \
  env FLN_ENV_E2E_RUN_ID="$COLLISION_RUN_ID" \
  FLN_ENV_E2E_STDOUT_ARTIFACT=collision_mutant.out \
  FLN_ENV_E2E_STDERR_ARTIFACT=collision_mutant.err \
  FLN_ENV_E2E_ARGV="$COLLISION_CARGO_ARGV" \
  FLN_ENV_E2E_CACHE_STATE="$COLLISION_CACHE_STATE" \
  CARGO_TARGET_DIR="$OVERLAY/target" \
  cargo test --locked -q -p fln-env \
  pmap::tests::environment_collision_e2e_emits_detailed_real_path_evidence \
  -- --exact --nocapture
collision_assert_supervisor collision_mutant fail 1 101 true
COLLISION_MUTANT_SUBJECT_AFTER="$(collision_hash_subject "$OVERLAY" fln-env/src/pmap.rs)"
COLLISION_MUTANT_GLOBAL_AFTER="$(collision_hash_live)"
collision_assert_unchanged collision_mutant \
  "$COLLISION_MUTANT_SUBJECT_BEFORE" "$COLLISION_MUTANT_SUBJECT_AFTER" \
  "$COLLISION_MUTANT_GLOBAL_BEFORE" "$COLLISION_MUTANT_GLOBAL_AFTER"
COLLISION_MUTANT_VALIDATION="$COLLISION_ART_DIR/collision_mutant.validation.json"
python3 "$EVIDENCE" validate-environment-collision \
  --file "$COLLISION_LAST_OUT" --stderr-file "$COLLISION_LAST_ERR" --phase mutant \
  --expected-run-id "$COLLISION_RUN_ID" --observed-exit "$COLLISION_LAST_CHILD" \
  --expected-stdout-artifact collision_mutant.out \
  --expected-stderr-artifact collision_mutant.err \
  --artifact-root "$COLLISION_ART_DIR" --output "$COLLISION_MUTANT_VALIDATION"
collision_record_step collision_mutant \
  "environment-collision/1:mutant/fail/wrapper=1/child=101/pristine_sha256=$COLLISION_PRISTINE_SHA" \
  "$COLLISION_LAST_CLASS/wrapper=$COLLISION_LAST_RC/child=$COLLISION_LAST_CHILD/mutant_sha256=$COLLISION_MUTANT_SHA" \
  collision_mutant.validation.json fail 1 101 \
  "$COLLISION_MUTANT_SUBJECT_BEFORE" "$COLLISION_MUTANT_SUBJECT_AFTER" \
  "$COLLISION_MUTANT_GLOBAL_BEFORE" "$COLLISION_MUTANT_GLOBAL_AFTER"

# Recovery: restore the retained pristine bytes and require an exact SHA match
# before the independently supervised recovery assertion.
cp -- "$COLLISION_PRISTINE_SOURCE" "$OVERLAY/fln-env/src/pmap.rs"
COLLISION_RECOVERED_SHA="$(collision_file_sha256 "$OVERLAY/fln-env/src/pmap.rs")"
if [ "$COLLISION_RECOVERED_SHA" != "$COLLISION_PRISTINE_SHA" ]; then
  collision_note "FAIL: recovered pmap.rs does not byte-match the pristine overlay"
  exit 3
fi
COLLISION_RECOVERY_SUBJECT_BEFORE="$(collision_hash_subject "$OVERLAY" fln-env/src/pmap.rs)"
if [ "$COLLISION_RECOVERY_SUBJECT_BEFORE" != "$COLLISION_PRISTINE_SUBJECT_ROOT" ]; then
  collision_note "FAIL: recovered pmap.rs tree root differs from the pristine overlay"
  exit 3
fi
COLLISION_RECOVERY_GLOBAL_BEFORE="$(collision_hash_live)"
collision_supervise collision_recovery "$OVERLAY" none false \
  env FLN_ENV_E2E_RUN_ID="$COLLISION_RUN_ID" \
  FLN_ENV_E2E_STDOUT_ARTIFACT=collision_recovery.out \
  FLN_ENV_E2E_STDERR_ARTIFACT=collision_recovery.err \
  FLN_ENV_E2E_ARGV="$COLLISION_CARGO_ARGV" \
  FLN_ENV_E2E_CACHE_STATE="$COLLISION_CACHE_STATE" \
  CARGO_TARGET_DIR="$OVERLAY/target" \
  cargo test --locked -q -p fln-env \
  pmap::tests::environment_collision_e2e_emits_detailed_real_path_evidence \
  -- --exact --nocapture
collision_assert_supervisor collision_recovery pass 0 0 false
COLLISION_RECOVERY_SUBJECT_AFTER="$(collision_hash_subject "$OVERLAY" fln-env/src/pmap.rs)"
COLLISION_RECOVERY_GLOBAL_AFTER="$(collision_hash_live)"
collision_assert_unchanged collision_recovery \
  "$COLLISION_RECOVERY_SUBJECT_BEFORE" "$COLLISION_RECOVERY_SUBJECT_AFTER" \
  "$COLLISION_RECOVERY_GLOBAL_BEFORE" "$COLLISION_RECOVERY_GLOBAL_AFTER"
COLLISION_RECOVERY_VALIDATION="$COLLISION_ART_DIR/collision_recovery.validation.json"
python3 "$EVIDENCE" validate-environment-collision \
  --file "$COLLISION_LAST_OUT" --stderr-file "$COLLISION_LAST_ERR" --phase recovery \
  --expected-run-id "$COLLISION_RUN_ID" --observed-exit "$COLLISION_LAST_CHILD" \
  --expected-cwd "$OVERLAY/fln-env" --expected-argv "$COLLISION_CARGO_ARGV" \
  --expected-stdout-artifact collision_recovery.out \
  --expected-stderr-artifact collision_recovery.err \
  --expected-cache-state "$COLLISION_CACHE_STATE" \
  --artifact-root "$COLLISION_ART_DIR" --output "$COLLISION_RECOVERY_VALIDATION"
collision_record_step collision_recovery \
  "environment-collision/1:recovery/pass/wrapper=0/child=0/sha256=$COLLISION_PRISTINE_SHA" \
  "$COLLISION_LAST_CLASS/wrapper=$COLLISION_LAST_RC/child=$COLLISION_LAST_CHILD/sha256=$COLLISION_RECOVERED_SHA" \
  collision_recovery.validation.json pass 0 0 \
  "$COLLISION_RECOVERY_SUBJECT_BEFORE" "$COLLISION_RECOVERY_SUBJECT_AFTER" \
  "$COLLISION_RECOVERY_GLOBAL_BEFORE" "$COLLISION_RECOVERY_GLOBAL_AFTER"

COLLISION_FINAL_ROOT="$(collision_hash_live)"
if [ "$COLLISION_FINAL_ROOT" != "$COLLISION_INPUT_ROOT" ]; then
  collision_note "FAIL: collision child changed its governed live input"
  exit 3
fi
collision_emit_event --string event run_end --string verdict pass \
  --string reason_code all_obligations_passed --integer process_exit 0 \
  --string active_step collision_recovery \
  --integer duration_ns "$(( $(python3 -c 'import time; print(time.monotonic_ns())') - COLLISION_START_NS ))" \
  --string cleanup_status retained_by_policy \
  --string final_state "$COLLISION_FINAL_ROOT" \
  --string logical_root "$COLLISION_FINAL_ROOT" \
  --string receipt_root not_applicable_internal_determinism \
  --string first_divergence none \
  --string evidence_manifest manifest.json \
  --string bundle_commit bundle.complete.json \
  --string evidence_state pending_bundle_commit

python3 "$EVIDENCE" validate-run --file "$COLLISION_LOG" \
  --schema "$COLLISION_SCHEMA" --expected-verdict pass \
  --expected-active-stage collision_recovery \
  --artifact-root "$COLLISION_ART_DIR" \
  --output "$COLLISION_ART_DIR/run.validation.json"
python3 "$EVIDENCE" manifest --art-dir "$COLLISION_ART_DIR" \
  --output "$COLLISION_ART_DIR/manifest.json" \
  --digest-output "$COLLISION_ART_DIR/manifest.digest" \
  --run-id "$COLLISION_RUN_ID" --bead "$COLLISION_BEAD" \
  --scenario "$COLLISION_SCENARIO" --verdict pass \
  --input-root "$COLLISION_INPUT_ROOT" --final-root "$COLLISION_FINAL_ROOT"
python3 "$EVIDENCE" complete-bundle --art-dir "$COLLISION_ART_DIR" \
  --manifest "$COLLISION_ART_DIR/manifest.json" \
  --digest "$COLLISION_ART_DIR/manifest.digest" \
  --output "$COLLISION_ART_DIR/bundle.complete.json" \
  --governed-root "$ROOT" "${COLLISION_GOVERNED_ARGS[@]}" \
  --expected-root "$COLLISION_FINAL_ROOT" \
  --vendor-path "$COLLISION_VENDOR_PATH"
python3 "$EVIDENCE" validate-bundle --art-dir "$COLLISION_ART_DIR" \
  --manifest "$COLLISION_ART_DIR/manifest.json" \
  --digest "$COLLISION_ART_DIR/manifest.digest" \
  --commit "$COLLISION_ART_DIR/bundle.complete.json" \
  --artifact-root "$COLLISION_ART_DIR" >/dev/null

emit collision_bundle passed \
  "\"child_bead\":\"fln-amv.10\",\"child_schema\":\"fln.e2e/2\",\"child_bundle\":\"collision-fln-amv.10/bundle.complete.json\",\"child_verdict\":\"pass\""

emit run_end passed "\"verdict\":\"pass\",\"artifacts_dir\":\"$ART_DIR\",\"cleanup_status\":\"retained_by_policy\""
note "PASS — artifacts in $ART_DIR"
