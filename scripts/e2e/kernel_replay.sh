#!/usr/bin/env bash
# kernel_replay.sh — shared E2E scenario for the G0-2 kernel differential spike
# (bead franken_lean-z6c, plan §22.1-2) plus the authoritative admission-slice
# evidence bundle (bead franken_lean-ap6).
#
# Real-path, no-mock: REAL Reference declarations are decoded from real .olean
# artifacts and replayed through fln_kernel::check. The OUTER journal (legacy
# fln-e2e/1, bead z6c) keeps the original lanes:
#   1. decoder suite over the C3 fixtures (identity-layer cross-checks live);
#   2. decode EVERY constant of the whole pinned stdlib (158k+ constants) with
#      cross-checks on — a byte-level identity differential against the pin;
#   3. seeded corruption — a flipped byte in a copied olean must make decoding
#      fail typed, never panic, never yield a wrong-but-accepted decl set;
#   4. recovery — the pristine fixture decodes clean again.
#
# The NESTED fln.e2e/2 child bundle (bead franken_lean-ap6, scenario
# kernel_replay) is the admission acceptance evidence: the supervised
# {1,8,32}-thread no-mock replay with strict schema-versioned NDJSON rows
# validated by `evidence.py validate-kernel-admission` (thread-matrix byte
# identity, pinned census, six named admission mutants killed typed, exact
# budget boundaries, typed exhaustion), the census floor, seeded-corruption
# and pristine-recovery legs, lane-level output-budget exhaustion and
# recovery, readiness-gated process-tree cancellation and recovery, an
# injected internal-fault probe, and a final re-check against the pinned
# input root. NDJSON under target/e2e/; artifacts retained.

set -euo pipefail

PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  echo "[kernel_replay] setup failure: python3 is required" >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
HOSTILE_PYTHON_CONFIGURATION=()
while IFS= read -r environment_name; do
  [[ "$environment_name" == PYTHON* ]] \
    && HOSTILE_PYTHON_CONFIGURATION+=("$environment_name")
done < <(compgen -e | LC_ALL=C sort)
if ((${#HOSTILE_PYTHON_CONFIGURATION[@]} > 0)); then
  printf '[kernel_replay] setup failure: sealed_interpreter_hostile_environment names=%s\n' \
    "$(IFS=,; printf '%s' "${HOSTILE_PYTHON_CONFIGURATION[*]}")" >&2
  exit 2
fi

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
EVIDENCE="$ROOT/scripts/evidence.py"
RUN_ID="kernel-replay-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$(dirname "$ART_DIR")"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  echo "[kernel_replay] setup failure: evidence directory already claimed: $ART_DIR" >&2
  exit 2
fi

BEAD="franken_lean-z6c"
SCHEMA="fln-e2e/1"
HOST="$(uname -sr)"
start_ns=$(date +%s%N)
PIN_TAG="$(sed -E 's/.*tag=([^ ]+).*/\1/' <<<"$(grep -E '^reference ' "$ROOT/SUITE.lock")")"

emit() { # emit <step_id> <status> <detail-json-fragment>
  local now_ns
  now_ns=$(date +%s%N)
  printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"kernel_replay","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
    "$SCHEMA" "$RUN_ID" "$BEAD" "$1" "$2" $(( (now_ns - start_ns) / 1000000 )) "$HOST" "$3" >> "$LOG"
}

note() { echo "[kernel_replay] $*" >&2; }

emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"$0\""

# ---- lane 1: the decoder suite ---------------------------------------------------------
note "running the decoder suite"
set +e
( cd "$ROOT" && CARGO_TARGET_DIR=target_local cargo test --locked -q -p fln-olean --test decl_decode ) \
  > "$ART_DIR/suite.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit suite failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"suite.log\""
  note "FAIL: decoder suite failed (see $ART_DIR/suite.log)"
  exit 1
fi
emit suite passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"suite.log\""

# ---- build the decode driver -----------------------------------------------------------
( cd "$ROOT" && CARGO_TARGET_DIR=target_local cargo build -q --locked -p fln-olean --example decode_olean ) \
  > "$ART_DIR/build.log" 2>&1
DECODER="$ROOT/target_local/debug/examples/decode_olean"

LIB="${FLN_REFERENCE_LIB:-$HOME/.elan/toolchains/leanprover--lean4---$PIN_TAG/lib/lean}"

# ---- nested franken_lean-ap6 admission evidence bundle ---------------------------------
# The admission-slice acceptance evidence lives in this authoritative fln.e2e/2
# child. The legacy parent journal receives one pointer after the child bundle
# commits. Absent pinned toolchain = typed skip (L0 limitation), never a pass.
AP6_SCHEMA="fln.e2e/2"
AP6_BEAD="franken_lean-ap6"
AP6_SCENARIO="kernel_replay"
AP6_RUN_ID="$RUN_ID-admission-ap6"
AP6_ART_DIR="$ART_DIR/admission-ap6"
AP6_LOG="$AP6_ART_DIR/run.ndjson"
AP6_HUMAN="$AP6_ART_DIR/human.log"
AP6_VENDOR_PATH="vendor/lean4-src"
AP6_SEQ=0
AP6_START_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
AP6_CAPTURE_BYTES="${FLN_E2E_CAPTURE_BYTES:-262144}"
AP6_OUTPUT_BUDGET_BYTES="${FLN_E2E_OUTPUT_BUDGET_BYTES:-33554432}"
AP6_TIMEOUT_MS="${FLN_E2E_TIMEOUT_MS:-1800000}"
AP6_GRACE_MS="${FLN_E2E_KILL_GRACE_MS:-2000}"
AP6_READY_WAIT_MS="${FLN_E2E_READY_WAIT_MS:-60000}"
AP6_CACHE_STATE="${FLN_E2E_CACHE_STATE:-uncontrolled}"
AP6_CARGO_ARGV="cargo test --locked -q -p fln-conformance --test kernel_replay -- --nocapture"
AP6_FIXTURE="$ROOT/tribunal/fixtures/c3/Init.SizeOfLemmas.olean"
# The governed identity of THIS lane: the admission slice's own surfaces —
# the kernel, the replay rig, the pinned fixture, and the evidence tooling.
# Sibling crates (fln-core/hash/env/olean) are inputs via compilation, but
# their identity is enforced by the workspace gate (scripts/check.sh), not
# re-hashed here: on the shared multi-agent tree they change legitimately
# while this long lane runs, and a mid-lane sibling edit does not alter the
# binaries this lane already built and measured.
AP6_INPUT_PATHS=(
  SUITE.lock rust-toolchain.toml
  crates/fln-kernel crates/fln-conformance
  tribunal/fixtures/c3/Init.SizeOfLemmas.olean
  vendor/NOTICE scripts/evidence.py
  scripts/e2e/kernel_replay.sh
)
AP6_HASH_ARGS=()
AP6_GOVERNED_ARGS=()
for ap6_input_path in "${AP6_INPUT_PATHS[@]}"; do
  AP6_HASH_ARGS+=(--path "$ap6_input_path")
  AP6_GOVERNED_ARGS+=(--governed-path "$ap6_input_path")
done

ap6_note() {
  printf '[kernel_replay:ap6] %s\n' "$*" | tee -a "$AP6_HUMAN" >&2
}

ap6_emit_event() {
  local sequence="$AP6_SEQ"
  AP6_SEQ=$((AP6_SEQ + 1))
  "${PYTHON[@]}" "$EVIDENCE" emit --file "$AP6_LOG" --artifact-root "$AP6_ART_DIR" \
    --string schema "$AP6_SCHEMA" --string run_id "$AP6_RUN_ID" \
    --string bead "$AP6_BEAD" --string scenario "$AP6_SCENARIO" \
    --integer sequence "$sequence" \
    --integer monotonic_ns "$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')" \
    --string wall_time_utc "$(date -u -Is)" "$@"
}

ap6_hash_live() {
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${AP6_HASH_ARGS[@]}" \
    --vendor-path "$AP6_VENDOR_PATH"
}

ap6_meta_field() {
  "${PYTHON[@]}" - "$1" "$2" <<'PY'
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

ap6_meta_resource_field() {
  "${PYTHON[@]}" - "$1" "$2" <<'PY'
import json
import pathlib
import sys

value = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))["resource"][sys.argv[2]]
if value is None:
    print("null")
elif value is True:
    print("true")
elif value is False:
    print("false")
elif isinstance(value, list):
    print(len(value))
else:
    print(value)
PY
}

ap6_supervise() {
  local step="$1" cwd="$2" semantic_exit="$3" planted="$4"
  shift 4
  local -a extra_args=()
  AP6_LAST_META="$AP6_ART_DIR/$step.meta.json"
  AP6_LAST_OUT="$AP6_ART_DIR/$step.out"
  AP6_LAST_ERR="$AP6_ART_DIR/$step.err"
  AP6_LAST_READY="$AP6_ART_DIR/$step.ready.json"
  if [ "$semantic_exit" != none ]; then
    extra_args+=(--semantic-failure-exit "$semantic_exit")
  fi
  if [ "$planted" = true ]; then
    extra_args+=(--planted)
  fi
  ap6_note "running step=$step cwd=$cwd"
  set +e
  "${PYTHON[@]}" "$EVIDENCE" run --cwd "$cwd" \
    --metadata "$AP6_LAST_META" --stdout "$AP6_LAST_OUT" \
    --stderr "$AP6_LAST_ERR" --readiness "$AP6_LAST_READY" \
    --artifact-root "$AP6_ART_DIR" --capture-bytes "$AP6_CAPTURE_BYTES" \
    --output-budget-bytes "$AP6_OUTPUT_BUDGET_BYTES" \
    --timeout-ms "$AP6_TIMEOUT_MS" --grace-ms "$AP6_GRACE_MS" \
    --stage-id "$step" "${extra_args[@]}" -- "$@"
  AP6_LAST_RC=$?
  set -e
}

ap6_assert_supervisor() {
  local step="$1" expected_class="$2" expected_wrapper="$3" expected_child="$4"
  if [ ! -s "$AP6_LAST_META" ]; then
    ap6_note "FAIL step=$step: missing supervisor metadata"
    exit 2
  fi
  AP6_LAST_CLASS="$(ap6_meta_field "$AP6_LAST_META" classification)"
  AP6_LAST_WRAPPER="$(ap6_meta_field "$AP6_LAST_META" wrapper_exit)"
  AP6_LAST_CHILD="$(ap6_meta_field "$AP6_LAST_META" child_exit)"
  AP6_LAST_REASON="$(ap6_meta_field "$AP6_LAST_META" reason_code)"
  if [ "$AP6_LAST_RC" != "$expected_wrapper" ] || \
     [ "$AP6_LAST_CLASS" != "$expected_class" ] || \
     [ "$AP6_LAST_WRAPPER" != "$expected_wrapper" ] || \
     [ "$AP6_LAST_CHILD" != "$expected_child" ]; then
    ap6_note "FAIL step=$step: expected $expected_class/wrapper=$expected_wrapper/child=$expected_child, got $AP6_LAST_CLASS/wrapper=$AP6_LAST_RC/child=$AP6_LAST_CHILD/reason=$AP6_LAST_REASON"
    exit 1
  fi
}

# The per-step subject: the kernel, the replay rig, and the fixture the lane
# exercises — hashed before and after every step (unchanged or the step fails).
ap6_hash_subject() {
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" \
    --path crates/fln-kernel \
    --path crates/fln-conformance/tests/kernel_replay.rs \
    --path tribunal/fixtures/c3/Init.SizeOfLemmas.olean
}

ap6_assert_globals() {
  local step="$1" current
  current="$(ap6_hash_live)"
  if [ "$current" != "$AP6_INPUT_ROOT" ]; then
    ap6_note "FAIL step=$step: governed live input changed ($current)"
    exit 3
  fi
}

# Emit one fully-contracted fln.e2e/2 step: assertion, expected/actual,
# global roots (pinned to the run's input root), validation artifact,
# expected supervisor taxonomy, subject before/after, and the supervisor
# metadata itself.
ap6_record_step() {
  local step="$1" expected="$2" actual="$3" validation="$4"
  local expected_class="$5" expected_wrapper="$6" expected_child="$7"
  local subject_before="$8" subject_after="$9"
  if [ "$subject_before" != "$subject_after" ]; then
    ap6_note "FAIL step=$step: subject changed during assertion"
    exit 3
  fi
  ap6_assert_globals "$step"
  ap6_emit_event --string event step --string step_id "$step" \
    --string assertion pass --string expected "$expected" --string actual "$actual" \
    --string input_root "$AP6_INPUT_ROOT" --string final_state "$AP6_INPUT_ROOT" \
    --string validation_artifact "$validation" \
    --string expected_supervisor_classification "$expected_class" \
    --integer expected_wrapper_exit "$expected_wrapper" \
    --json-value expected_child_exit "$expected_child" \
    --string subject_root "$subject_before" \
    --string subject_final_state "$subject_after" \
    --json-file supervisor "$AP6_LAST_META"
}

if [ ! -d "$LIB" ]; then
  emit admission_bundle skipped "\"reason\":\"reference_toolchain_absent\",\"limitation\":\"L0: ap6 admission evidence unverifiable on this host\""
  note "SKIP: pinned toolchain library not installed — ap6 admission bundle skipped (typed limitation)"
  AP6_BUNDLE_PRESENT=0
else
  AP6_BUNDLE_PRESENT=1
  if ! AP6_INPUT_ROOT="$(ap6_hash_live)"; then
    note "FAIL: cannot hash franken_lean-ap6 governed inputs"
    exit 2
  fi
  if [ -e "$AP6_ART_DIR" ] || [ -L "$AP6_ART_DIR" ]; then
    note "FAIL: refusing reused admission evidence directory $AP6_ART_DIR"
    exit 2
  fi
  mkdir "$AP6_ART_DIR"
  "${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" \
    --vendor-path "$AP6_VENDOR_PATH" --output "$AP6_ART_DIR/vendor-binding.json" \
    --artifact-root "$AP6_ART_DIR" || {
      note "FAIL: cannot bind the pinned Reference tree for franken_lean-ap6"
      exit 2
    }
  AP6_LIVE_HEAD="$(git -C "$ROOT" rev-parse HEAD)"
  ap6_emit_event --new-log --string event run_start \
    --json-value argv '["scripts/e2e/kernel_replay.sh"]' \
    --string cwd "$ROOT" \
    --append-string claim_ids franken_lean-ap6-admission-determinism \
    --append-string claim_ids franken_lean-ap6-admission-fault-matrix \
    --append-string invariant_ids FL-INV-01 \
    --append-string invariant_ids FL-INV-02 \
    --append-string invariant_ids FL-INV-07 \
    --append-string gate_ids G1 \
    --string parity_ledger_row init-prelude-admission-replay \
    --string epoch "lean-$PIN_TAG" --string mode sound --string profile e2e \
    --string platform "$(uname -srm)" \
    --json-value host_facts "$("${PYTHON[@]}" -c 'import json,platform; print(json.dumps({"system":platform.system(),"release":platform.release(),"machine":platform.machine(),"python":platform.python_version()},separators=(",",":")))')" \
    --integer thread_count 32 --string seed module-order-kahn-v1 \
    --json-value thread_matrix '[1,8,32]' \
    --string cache_state "$AP6_CACHE_STATE" \
    --string input_root "$AP6_INPUT_ROOT" \
    --string vendor_binding vendor-binding.json \
    --string live_head "$AP6_LIVE_HEAD" \
    --json-value budgets "{\"capture_bytes_per_stream\":$AP6_CAPTURE_BYTES,\"output_budget_bytes\":$AP6_OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$AP6_TIMEOUT_MS,\"kill_grace_ms\":$AP6_GRACE_MS,\"kernel_step_budget\":10000000,\"kernel_depth_budget\":4096}"
  : > "$AP6_HUMAN"

  # Helper scripts for the pure-assertion steps (census + corruption), so
  # those steps run under the same supervisor discipline as everything else.
  AP6_CENSUS_CHECK="$AP6_ART_DIR/census_check.py"
  cat > "$AP6_CENSUS_CHECK" <<'PY'
import pathlib
import sys

lines = [
    line
    for line in pathlib.Path(sys.argv[1]).read_text(encoding="utf-8").splitlines()
    if line.startswith("kernel_replay census:")
]
if len(lines) != 1:
    raise SystemExit(f"expected exactly one census line, found {len(lines)}")
line = lines[0]
for needle in (
    "checked=2198 accepted=2198",
    "inconclusive=0",
    "rejected={}",
    "unchecked={}",
    "artifact_incomplete=6",
    "artifact_incomplete_witness="
    "c7fa135fc4f85a21488bfc2393cbe4f7fa81b13205dbf18023ced322b829e015",
    "nested_partial_blocks=0 nested_full_blocks=1",
):
    if needle not in line:
        raise SystemExit(f"census regressed: missing {needle!r} in {line!r}")
print(line)
PY
  AP6_CORRUPTION_SWEEP="$AP6_ART_DIR/corruption_sweep.py"
  cat > "$AP6_CORRUPTION_SWEEP" <<'PY'
import pathlib
import subprocess
import sys

decoder, fixture, out_dir = sys.argv[1], sys.argv[2], pathlib.Path(sys.argv[3])
kills = 0
panics = 0
sweeps = 0
pristine = pathlib.Path(fixture).read_bytes()
for frac in (4, 8, 16, 32, 64, 128, 256, 512):
    data = bytearray(pristine)
    pos = 88 + ((len(data) - 88) // frac // 8) * 8
    data[pos] ^= 0x08
    corrupt = out_dir / f"corrupt_{frac}.olean"
    corrupt.write_bytes(bytes(data))
    sweeps += 1
    proc = subprocess.run(
        [decoder, str(corrupt)], capture_output=True, text=True, check=False
    )
    (out_dir / f"corrupt_{frac}.tsv").write_text(proc.stdout, encoding="utf-8")
    (out_dir / f"corrupt_{frac}.err").write_text(proc.stderr, encoding="utf-8")
    if "panicked" in proc.stderr:
        panics += 1
    elif proc.returncode != 0:
        kills += 1
print(f"sweeps={sweeps} kills={kills} panics={panics}")
if panics != 0:
    raise SystemExit("decoder panicked on corrupted input (FL-INV-07 violation)")
if kills == 0:
    raise SystemExit("no corruption caught — cross-checks not live")
PY

  # -- step: decoder_suite — the identity layer under the replay is live -------
  AP6_SUBJECT_BEFORE="$(ap6_hash_subject)"
  ap6_supervise decoder_suite "$ROOT" 101 false \
    env CARGO_TARGET_DIR=target_local \
    cargo test --locked -q -p fln-olean --test decl_decode
  ap6_assert_supervisor decoder_suite pass 0 0
  ap6_record_step decoder_suite "decoder-suite/pass/wrapper=0/child=0" \
    "$AP6_LAST_CLASS/wrapper=$AP6_LAST_RC/child=$AP6_LAST_CHILD" \
    not_applicable pass 0 0 \
    "$AP6_SUBJECT_BEFORE" "$(ap6_hash_subject)"

  # -- step: admission_replay — the supervised no-mock replay + row validation -
  AP6_SUBJECT_BEFORE="$(ap6_hash_subject)"
  ap6_supervise admission_replay "$ROOT" 101 false \
    env FLN_KERNEL_E2E_RUN_ID="$AP6_RUN_ID" \
    FLN_KERNEL_E2E_STDOUT_ARTIFACT=admission_replay.out \
    FLN_KERNEL_E2E_STDERR_ARTIFACT=admission_replay.err \
    FLN_KERNEL_E2E_ARGV="$AP6_CARGO_ARGV" \
    FLN_KERNEL_E2E_CACHE_STATE="$AP6_CACHE_STATE" \
    CARGO_TARGET_DIR=target_local \
    cargo test --locked -q -p fln-conformance --test kernel_replay -- --nocapture
  ap6_assert_supervisor admission_replay pass 0 0
  AP6_ADMISSION_VALIDATION="$AP6_ART_DIR/admission_replay.validation.json"
  "${PYTHON[@]}" "$EVIDENCE" validate-kernel-admission \
    --file "$AP6_LAST_OUT" --stderr-file "$AP6_LAST_ERR" --phase positive \
    --expected-run-id "$AP6_RUN_ID" --observed-exit "$AP6_LAST_CHILD" \
    --expected-cwd "$ROOT/crates/fln-conformance" --expected-argv "$AP6_CARGO_ARGV" \
    --expected-stdout-artifact admission_replay.out \
    --expected-stderr-artifact admission_replay.err \
    --expected-cache-state "$AP6_CACHE_STATE" \
    --artifact-root "$AP6_ART_DIR" --output "$AP6_ADMISSION_VALIDATION"
  AP6_FIXTURE_ROOT="$("${PYTHON[@]}" - "$AP6_ADMISSION_VALIDATION" <<'PY'
import json
import pathlib
import sys

print(json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))["canonical_input_root"])
PY
)"
  AP6_VERDICT_DIGEST="$("${PYTHON[@]}" - "$AP6_ADMISSION_VALIDATION" <<'PY'
import json
import pathlib
import sys

print(json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))["verdict_stream_digest"])
PY
)"
  ap6_record_step admission_replay \
    "kernel-admission/1:positive/pass/threads=1,8,32/census=2198-accepted/mutants=6-killed" \
    "$AP6_LAST_CLASS/wrapper=$AP6_LAST_RC/child=$AP6_LAST_CHILD/digest=$AP6_VERDICT_DIGEST" \
    admission_replay.validation.json pass 0 0 \
    "$AP6_SUBJECT_BEFORE" "$(ap6_hash_subject)"
  ap6_note "admission replay validated: digest=$AP6_VERDICT_DIGEST fixture=$AP6_FIXTURE_ROOT"

  # -- step: census_floor — the pinned verdict census may only move by bead ----
  AP6_SUBJECT_BEFORE="$(ap6_hash_subject)"
  ap6_supervise census_floor "$ROOT" 1 false \
    "${PYTHON[@]}" "$AP6_CENSUS_CHECK" "$AP6_ART_DIR/admission_replay.err"
  ap6_assert_supervisor census_floor pass 0 0
  ap6_record_step census_floor \
    "checked=2198 accepted=2198 inconclusive=0 rejected={} unchecked={} artifact_incomplete=6 nested_partial_blocks=0 nested_full_blocks=1" \
    "$AP6_LAST_CLASS/wrapper=$AP6_LAST_RC/child=$AP6_LAST_CHILD/census_artifact=admission_replay.err" \
    not_applicable pass 0 0 \
    "$AP6_SUBJECT_BEFORE" "$(ap6_hash_subject)"

  # -- step: corruption — flipped bytes must die typed, never panic ------------
  AP6_SUBJECT_BEFORE="$(ap6_hash_subject)"
  ap6_supervise corruption "$ROOT" 1 false \
    "${PYTHON[@]}" "$AP6_CORRUPTION_SWEEP" "$DECODER" "$AP6_FIXTURE" "$AP6_ART_DIR"
  ap6_assert_supervisor corruption pass 0 0
  ap6_record_step corruption \
    "sweeps=8/panics=0/kills>=1/wrapper=0" \
    "$AP6_LAST_CLASS/wrapper=$AP6_LAST_RC/child=$AP6_LAST_CHILD/artifact=corruption.out" \
    not_applicable pass 0 0 \
    "$AP6_SUBJECT_BEFORE" "$(ap6_hash_subject)"

  # -- step: corruption_recovery — the pristine fixture decodes clean ----------
  AP6_SUBJECT_BEFORE="$(ap6_hash_subject)"
  ap6_supervise corruption_recovery "$ROOT" 1 false \
    "$DECODER" "$AP6_FIXTURE"
  ap6_assert_supervisor corruption_recovery pass 0 0
  ap6_record_step corruption_recovery "pristine-decode/pass/wrapper=0/child=0" \
    "$AP6_LAST_CLASS/wrapper=$AP6_LAST_RC/child=$AP6_LAST_CHILD" \
    not_applicable pass 0 0 \
    "$AP6_SUBJECT_BEFORE" "$(ap6_hash_subject)"

  # -- step: resource_exhaustion — a tiny output budget is typed Inconclusive --
  # One decode line is ~90 bytes; 32 repeats overrun the 256-byte budget with
  # certainty, so the supervisor must classify typed exhaustion, never a pass.
  AP6_EXHAUST_ARGS=()
  for _ in $(seq 32); do AP6_EXHAUST_ARGS+=("$AP6_FIXTURE"); done
  saved_budget="$AP6_OUTPUT_BUDGET_BYTES"
  saved_capture="$AP6_CAPTURE_BYTES"
  AP6_OUTPUT_BUDGET_BYTES=256
  AP6_CAPTURE_BYTES=256
  AP6_SUBJECT_BEFORE="$(ap6_hash_subject)"
  ap6_supervise resource_exhaustion "$ROOT" none false \
    "$DECODER" "${AP6_EXHAUST_ARGS[@]}"
  AP6_OUTPUT_BUDGET_BYTES="$saved_budget"
  AP6_CAPTURE_BYTES="$saved_capture"
  if [ "$AP6_LAST_RC" -ne 3 ]; then
    ap6_note "FAIL: output-budget exhaustion was not typed inconclusive (rc=$AP6_LAST_RC)"
    exit 1
  fi
  AP6_LAST_CLASS="$(ap6_meta_field "$AP6_LAST_META" classification)"
  AP6_LAST_REASON="$(ap6_meta_field "$AP6_LAST_META" reason_code)"
  AP6_LAST_CHILD="$(ap6_meta_field "$AP6_LAST_META" child_exit)"
  if [ "$AP6_LAST_CLASS" != inconclusive ] || [ "$AP6_LAST_REASON" != output_budget_exhausted ]; then
    ap6_note "FAIL: exhaustion classified $AP6_LAST_CLASS/$AP6_LAST_REASON"
    exit 1
  fi
  ap6_record_step resource_exhaustion \
    "inconclusive/output_budget_exhausted/wrapper=3" \
    "$AP6_LAST_CLASS/$AP6_LAST_REASON/wrapper=$AP6_LAST_RC/child=$AP6_LAST_CHILD" \
    not_applicable inconclusive 3 "$AP6_LAST_CHILD" \
    "$AP6_SUBJECT_BEFORE" "$(ap6_hash_subject)"

  # -- step: resource_recovery — the same decode under a real budget passes ----
  AP6_SUBJECT_BEFORE="$(ap6_hash_subject)"
  ap6_supervise resource_recovery "$ROOT" 1 false \
    "$DECODER" "$AP6_FIXTURE"
  ap6_assert_supervisor resource_recovery pass 0 0
  ap6_record_step resource_recovery "pristine-decode/pass/wrapper=0/child=0" \
    "$AP6_LAST_CLASS/wrapper=$AP6_LAST_RC/child=$AP6_LAST_CHILD" \
    not_applicable pass 0 0 \
    "$AP6_SUBJECT_BEFORE" "$(ap6_hash_subject)"

  # -- step: cancellation — readiness-gated SIGTERM tears down the real replay -
  AP6_SUBJECT_BEFORE="$(ap6_hash_subject)"
  AP6_LAST_META="$AP6_ART_DIR/cancellation.meta.json"
  AP6_LAST_OUT="$AP6_ART_DIR/cancellation.out"
  AP6_LAST_ERR="$AP6_ART_DIR/cancellation.err"
  AP6_LAST_READY="$AP6_ART_DIR/cancellation.ready.json"
  ap6_note "running step=cancellation (SIGTERM mid-replay)"
  set +e
  "${PYTHON[@]}" "$EVIDENCE" run --cwd "$ROOT" \
    --metadata "$AP6_LAST_META" --stdout "$AP6_LAST_OUT" \
    --stderr "$AP6_LAST_ERR" --readiness "$AP6_LAST_READY" \
    --artifact-root "$AP6_ART_DIR" --capture-bytes "$AP6_CAPTURE_BYTES" \
    --output-budget-bytes "$AP6_OUTPUT_BUDGET_BYTES" \
    --timeout-ms "$AP6_TIMEOUT_MS" --grace-ms "$AP6_GRACE_MS" \
    --stage-id cancellation -- \
    env FLN_KERNEL_E2E_RUN_ID="$AP6_RUN_ID-cancelled" \
    CARGO_TARGET_DIR=target_local \
    cargo test --locked -q -p fln-conformance --test kernel_replay -- --nocapture &
  AP6_CANCEL_PID=$!
  set -e
  ready_ticks=$(( (AP6_READY_WAIT_MS + 19) / 20 ))
  ready_ok=0
  for ((i = 0; i < ready_ticks; i += 1)); do
    if [ -s "$AP6_LAST_READY" ]; then ready_ok=1; break; fi
    if ! kill -0 "$AP6_CANCEL_PID" 2>/dev/null; then break; fi
    sleep 0.02
  done
  if [ "$ready_ok" -ne 1 ]; then
    ap6_note "FAIL: cancellation target never became ready"
    exit 2
  fi
  kill -TERM "$AP6_CANCEL_PID"
  set +e
  wait "$AP6_CANCEL_PID"
  AP6_LAST_RC=$?
  set -e
  if [ "$AP6_LAST_RC" -ne 4 ]; then
    ap6_note "FAIL: cancellation was not typed cancelled (rc=$AP6_LAST_RC)"
    exit 1
  fi
  AP6_LAST_CLASS="$(ap6_meta_field "$AP6_LAST_META" classification)"
  AP6_LAST_REASON="$(ap6_meta_field "$AP6_LAST_META" reason_code)"
  AP6_LAST_CHILD="$(ap6_meta_field "$AP6_LAST_META" child_exit)"
  AP6_TERM_SENT="$(ap6_meta_resource_field "$AP6_LAST_META" term_sent)"
  AP6_SURVIVORS="$(ap6_meta_resource_field "$AP6_LAST_META" surviving_pids)"
  if [ "$AP6_LAST_CLASS" != cancelled ] || [ "$AP6_LAST_REASON" != signal_SIGTERM ] \
     || [ "$AP6_TERM_SENT" != true ] || [ "$AP6_SURVIVORS" != 0 ]; then
    ap6_note "FAIL: cancellation contract: class=$AP6_LAST_CLASS reason=$AP6_LAST_REASON term_sent=$AP6_TERM_SENT survivors=$AP6_SURVIVORS"
    exit 1
  fi
  ap6_record_step cancellation \
    "cancelled/signal_SIGTERM/wrapper=4/child=null/survivors=0" \
    "$AP6_LAST_CLASS/$AP6_LAST_REASON/wrapper=$AP6_LAST_RC/child=$AP6_LAST_CHILD/survivors=$AP6_SURVIVORS" \
    not_applicable cancelled 4 "$AP6_LAST_CHILD" \
    "$AP6_SUBJECT_BEFORE" "$(ap6_hash_subject)"

  # -- step: cancellation_recovery — later valid work is unaffected ------------
  AP6_SUBJECT_BEFORE="$(ap6_hash_subject)"
  ap6_supervise cancellation_recovery "$ROOT" 1 false \
    "$DECODER" "$AP6_FIXTURE"
  ap6_assert_supervisor cancellation_recovery pass 0 0
  ap6_record_step cancellation_recovery "pristine-decode/pass/wrapper=0/child=0" \
    "$AP6_LAST_CLASS/wrapper=$AP6_LAST_RC/child=$AP6_LAST_CHILD" \
    not_applicable pass 0 0 \
    "$AP6_SUBJECT_BEFORE" "$(ap6_hash_subject)"

  # -- step: internal_fault_probe — an exec fault maps to the typed exit-2
  #    family with published metadata, never a pass, never a semantic verdict.
  #    (The deeper capture-publication fault, which by design suppresses the
  #    metadata itself, is probed in the outer journal after this bundle.)
  AP6_SUBJECT_BEFORE="$(ap6_hash_subject)"
  ap6_supervise internal_fault_probe "$ROOT" none false \
    "$AP6_ART_DIR/no-such-decoder" "$AP6_FIXTURE"
  if [ "$AP6_LAST_RC" -ne 2 ]; then
    ap6_note "FAIL: exec fault was not typed exit-2 (rc=$AP6_LAST_RC)"
    exit 1
  fi
  AP6_LAST_CLASS="$(ap6_meta_field "$AP6_LAST_META" classification)"
  AP6_LAST_CHILD="$(ap6_meta_field "$AP6_LAST_META" child_exit)"
  if [ "$AP6_LAST_CLASS" != setup_failure ] && [ "$AP6_LAST_CLASS" != internal_fault ]; then
    ap6_note "FAIL: exec fault classified $AP6_LAST_CLASS"
    exit 1
  fi
  ap6_record_step internal_fault_probe \
    "setup_failure-or-internal_fault/wrapper=2/never-a-verdict" \
    "$AP6_LAST_CLASS/wrapper=$AP6_LAST_RC/child=$AP6_LAST_CHILD" \
    not_applicable "$AP6_LAST_CLASS" 2 "$AP6_LAST_CHILD" \
    "$AP6_SUBJECT_BEFORE" "$(ap6_hash_subject)"

  # -- step: final_real_recheck — retained evidence still validates against the
  #    pinned fixture root, and the pristine decode still passes ----------------
  AP6_RECHECK_VALIDATION="$AP6_ART_DIR/final_recheck.validation.json"
  "${PYTHON[@]}" "$EVIDENCE" validate-kernel-admission \
    --file "$AP6_ART_DIR/admission_replay.out" \
    --stderr-file "$AP6_ART_DIR/admission_replay.err" --phase recovery \
    --expected-run-id "$AP6_RUN_ID" --observed-exit 0 \
    --expected-cwd "$ROOT/crates/fln-conformance" --expected-argv "$AP6_CARGO_ARGV" \
    --expected-stdout-artifact admission_replay.out \
    --expected-stderr-artifact admission_replay.err \
    --expected-cache-state "$AP6_CACHE_STATE" \
    --expected-input-root "$AP6_FIXTURE_ROOT" \
    --artifact-root "$AP6_ART_DIR" --output "$AP6_RECHECK_VALIDATION"
  AP6_SUBJECT_BEFORE="$(ap6_hash_subject)"
  ap6_supervise final_real_recheck "$ROOT" 1 false \
    "$DECODER" "$AP6_FIXTURE"
  ap6_assert_supervisor final_real_recheck pass 0 0
  AP6_FINAL_ROOT="$(ap6_hash_live)"
  if [ "$AP6_FINAL_ROOT" != "$AP6_INPUT_ROOT" ]; then
    ap6_note "FAIL: admission child changed its governed live input"
    exit 3
  fi
  ap6_record_step final_real_recheck \
    "kernel-admission/1:recovery/valid/input_root=$AP6_FIXTURE_ROOT/decode=clean" \
    "valid/input_root=$AP6_FIXTURE_ROOT/wrapper=$AP6_LAST_RC/child=$AP6_LAST_CHILD" \
    final_recheck.validation.json pass 0 0 \
    "$AP6_SUBJECT_BEFORE" "$(ap6_hash_subject)"

  ap6_emit_event --string event run_end --string verdict pass \
    --string reason_code all_obligations_passed --integer process_exit 0 \
    --string active_step final_real_recheck \
    --integer duration_ns "$(( $("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())') - AP6_START_NS ))" \
    --string cleanup_status retained_by_policy \
    --string final_state "$AP6_FINAL_ROOT" \
    --string logical_root "$AP6_FINAL_ROOT" \
    --string receipt_root not_applicable_admission_bootstrap \
    --string first_divergence none \
    --string evidence_manifest manifest.json \
    --string bundle_commit bundle.complete.json \
    --string evidence_state pending_bundle_commit

  "${PYTHON[@]}" "$EVIDENCE" validate-run --file "$AP6_LOG" \
    --schema "$AP6_SCHEMA" --expected-verdict pass \
    --expected-active-stage final_real_recheck \
    --artifact-root "$AP6_ART_DIR" \
    --output "$AP6_ART_DIR/run.validation.json"
  "${PYTHON[@]}" "$EVIDENCE" manifest --art-dir "$AP6_ART_DIR" \
    --output "$AP6_ART_DIR/manifest.json" \
    --digest-output "$AP6_ART_DIR/manifest.digest" \
    --run-id "$AP6_RUN_ID" --bead "$AP6_BEAD" \
    --scenario "$AP6_SCENARIO" --verdict pass \
    --input-root "$AP6_INPUT_ROOT" --final-root "$AP6_FINAL_ROOT"
  "${PYTHON[@]}" "$EVIDENCE" complete-bundle --art-dir "$AP6_ART_DIR" \
    --manifest "$AP6_ART_DIR/manifest.json" \
    --digest "$AP6_ART_DIR/manifest.digest" \
    --output "$AP6_ART_DIR/bundle.complete.json" \
    --governed-root "$ROOT" "${AP6_GOVERNED_ARGS[@]}" \
    --expected-root "$AP6_FINAL_ROOT" \
    --vendor-path "$AP6_VENDOR_PATH"
  "${PYTHON[@]}" "$EVIDENCE" validate-bundle --art-dir "$AP6_ART_DIR" \
    --manifest "$AP6_ART_DIR/manifest.json" \
    --digest "$AP6_ART_DIR/manifest.digest" \
    --commit "$AP6_ART_DIR/bundle.complete.json" \
    --artifact-root "$AP6_ART_DIR" >/dev/null

  emit admission_bundle passed \
    "\"child_bead\":\"franken_lean-ap6\",\"child_schema\":\"fln.e2e/2\",\"child_bundle\":\"admission-ap6/bundle.complete.json\",\"child_verdict\":\"pass\",\"verdict_stream_digest\":\"$AP6_VERDICT_DIGEST\""
  note "ap6 admission bundle committed (digest $AP6_VERDICT_DIGEST)"

  # ---- capture-publication internal fault probe (outer journal) --------------
  # The deepest fault class: the supervisor's own capture publication fails
  # (injected via the sanctioned --test-fault-point control, which requires
  # --planted). By design this fault suppresses trustworthy metadata; the
  # contract is exactly "wrapper exit 2, never a pass, never a verdict".
  set +e
  "${PYTHON[@]}" "$EVIDENCE" run --cwd "$ROOT" \
    --metadata "$ART_DIR/capture_fault_probe.meta.json" \
    --stdout "$ART_DIR/capture_fault_probe.out" \
    --stderr "$ART_DIR/capture_fault_probe.err" \
    --readiness "$ART_DIR/capture_fault_probe.ready.json" \
    --artifact-root "$ART_DIR" --capture-bytes 262144 \
    --output-budget-bytes 16777216 \
    --timeout-ms 300000 --grace-ms 2000 \
    --stage-id capture_fault_probe --planted \
    --test-fault-point capture_stdout -- \
    "$DECODER" "$ROOT/tribunal/fixtures/c3/Init.SizeOfLemmas.olean"
  rc=$?
  set -e
  if [ "$rc" -ne 2 ]; then
    emit capture_fault_probe failed "\"expected_exit\":2,\"actual_exit\":$rc"
    note "FAIL: injected capture fault was not typed internal_fault (rc=$rc)"
    exit 1
  fi
  emit capture_fault_probe passed "\"expected_exit\":2,\"actual_exit\":2,\"fault_point\":\"capture_stdout\",\"detail\":\"metadata suppressed by design; wrapper exit 2 only\""
  note "capture-publication fault probe: typed internal_fault (exit 2), no verdict"
fi

# ---- lane 1b: verdict-census floor (beads franken_lean-irm + franken_lean-ap6) ----------
# The literal-acceleration slice closed the last false-rejects (irm:
# 1755/1755 checkable); the admission slice then put EVERY declaration kind
# through the kernel (ap6: inductive blocks with recursor regeneration,
# quotients, all definition safeties) — 2198/2198 checked accepted, with
# exactly 6 non-safe helpers typed ArtifactIncomplete (bead franken_lean-
# artifact-incomplete-private-refs-sgt: their private auxiliary references
# are absent from the pin's own serialization; witnessed, never checked,
# never cached, never admitted) and 1 nested block under the full ruleset.
# The census may only move by a deliberate, bead-tracked change. The
# authoritative census evidence lives in the ap6 child bundle; this legacy
# step mirrors it.
if [ "$AP6_BUNDLE_PRESENT" -eq 1 ]; then
  emit census passed "\"checked\":2198,\"accepted\":2198,\"rejected\":0,\"inconclusive\":0,\"artifact_incomplete\":6,\"beads\":\"franken_lean-irm,franken_lean-ap6,franken_lean-artifact-incomplete-private-refs-sgt\",\"census_artifact\":\"admission-ap6/admission_replay.err\""
  note "census floor: Init.Prelude 2198/2198 checked accepted (6 typed inconclusive-artifact-incomplete), 0 rejected, 0 inconclusive"
else
  emit census skipped "\"reason\":\"reference_toolchain_absent\",\"limitation\":\"L0: verdict census unverified on this host\""
  note "SKIP: census floor unverifiable without the pinned toolchain (typed limitation)"
fi

# ---- lane 2: decode the entire pinned stdlib with cross-checks on -----------------------
if [ -d "$LIB" ]; then
  note "decoding every constant of the pinned stdlib (identity cross-checks on)"
  set +e
  find "$LIB" -name '*.olean' | sort | xargs "$DECODER" > "$ART_DIR/decode_all.tsv" 2>>"$ART_DIR/decode_all.err"
  rc=$?
  set -e
  total="$(wc -l < "$ART_DIR/decode_all.tsv")"
  ok="$(grep -c $'\tok$' "$ART_DIR/decode_all.tsv" || true)"
  consts="$(awk -F'\t' '$4=="ok"{s+=$2} END{print s}' "$ART_DIR/decode_all.tsv")"
  if [ "$rc" -ne 0 ] || [ "$total" -ne "$ok" ] || [ "$total" -lt 2000 ]; then
    emit decode_all failed "\"files\":$total,\"ok\":$ok,\"actual_exit\":$rc,\"artifact\":\"decode_all.tsv\""
    note "FAIL: whole-library decode incomplete ($ok/$total clean)"
    exit 1
  fi
  emit decode_all passed "\"files\":$total,\"ok\":$ok,\"constants\":$consts,\"crosschecks\":\"on\",\"artifact\":\"decode_all.tsv\""
  note "decoded $consts constants across $total modules, zero cross-check failures"
else
  emit decode_all skipped "\"reason\":\"reference_toolchain_absent\",\"limitation\":\"L0: whole-library decode unverified on this host\""
  note "SKIP: pinned toolchain library not installed (typed limitation)"
fi

# ---- lane 3: seeded corruption — a flip in a live object must fail typed ----------------
# The constant-decoder only traverses objects reachable from the `constants`
# array, so a single flip can legitimately land in an unreached object and
# decode clean. We sweep deterministic positions and demand: NEVER a panic, and
# AT LEAST ONE flip caught as a typed error — proving the identity cross-checks
# and shape checks genuinely reject corrupted declarations.
note "seeding corruption: deterministic byte-flip sweep in a copied olean"
kills=0
panics=0
sweeps=0
for frac in 4 8 16 32 64 128 256 512; do
  CORRUPT="$ART_DIR/corrupt_$frac.olean"
  cp "$ROOT/tribunal/fixtures/c3/Init.SizeOfLemmas.olean" "$CORRUPT"
  "${PYTHON[@]}" - "$CORRUPT" "$frac" <<'EOF'
import sys
path, frac = sys.argv[1], int(sys.argv[2])
data = bytearray(open(path, "rb").read())
pos = 88 + ((len(data) - 88) // frac // 8) * 8
data[pos] ^= 0x08
open(path, "wb").write(data)
EOF
  sweeps=$((sweeps + 1))
  set +e
  "$DECODER" "$CORRUPT" > "$ART_DIR/corrupt_$frac.tsv" 2>"$ART_DIR/corrupt_$frac.err"
  rc=$?
  set -e
  if grep -q "panicked" "$ART_DIR/corrupt_$frac.err"; then
    panics=$((panics + 1))
  elif [ "$rc" -ne 0 ]; then
    kills=$((kills + 1))
  fi
done
if [ "$panics" -ne 0 ]; then
  emit corruption failed "\"reason\":\"panic\",\"panics\":$panics,\"sweeps\":$sweeps"
  note "FAIL: decoder panicked on corrupted input (FL-INV-07 violation)"
  exit 1
fi
if [ "$kills" -eq 0 ]; then
  emit corruption failed "\"kills\":0,\"sweeps\":$sweeps,\"expected\":\">=1 typed failure\""
  note "FAIL: no corruption caught across $sweeps flips — cross-checks not live"
  exit 1
fi
emit corruption passed "\"kills\":$kills,\"sweeps\":$sweeps,\"panics\":0,\"typed_error\":true"
note "corruption sweep: $kills/$sweeps flips killed typed, 0 panics"

# ---- lane 4: recovery — pristine fixture decodes clean ----------------------------------
set +e
"$DECODER" "$ROOT/tribunal/fixtures/c3/Init.SizeOfLemmas.olean" > "$ART_DIR/recovery_decode.tsv" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit recovery failed "\"actual_exit\":$rc,\"artifact\":\"recovery_decode.tsv\""
  note "FAIL: recovery decode not clean"
  exit 1
fi
emit recovery passed "\"actual_exit\":0,\"artifact\":\"recovery_decode.tsv\""

emit run_end passed "\"cleanup_status\":\"retained_by_policy\",\"artifact_dir\":\"target/e2e/$RUN_ID\""
note "PASS: all lanes green (artifacts in target/e2e/$RUN_ID)"
