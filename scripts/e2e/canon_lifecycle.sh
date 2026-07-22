#!/usr/bin/env bash
# canon_lifecycle.sh — no-mock bounded-stack lifecycle proof for
# franken_lean-canon-stack-safe-drop-6gy.
#
# The real fln-core/fln-hash implementations run in sacrificial child processes.
# The positive matrix proves deep decode/encode/hash/share/drop plus partial-error
# cleanup and recovery. Test-only recursive encoder mutations must abort/fail and
# are followed by a clean recovery run. Human logs go to stderr and complete,
# bounded NDJSON/stdout/stderr artifacts remain under target/e2e/.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RUN_ID="canon-lifecycle-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="${FLN_E2E_ARTIFACT_DIR:-$ROOT/target/e2e/$RUN_ID}"
EVENTS="$ART_DIR/run.ndjson"
HUMAN="$ART_DIR/run.log"
DEPTH="${FLN_CANON_LIFECYCLE_DEPTH:-100000}"
RUNS="${FLN_CANON_LIFECYCLE_RUNS:-100}"
MILLION_DEPTH="${FLN_CANON_LIFECYCLE_MILLION_DEPTH:-1000000}"
TEST_NAME="canon::tests::deep_valid_lifecycle_is_stack_safe_in_subprocess"
BEAD="franken_lean-canon-stack-safe-drop-6gy"
SCHEMA="fln-e2e/1"
START_NS="$(date +%s%N)"
FINALIZED=0

mkdir -p "$ART_DIR"

note() {
  printf '[canon_lifecycle] %s\n' "$*" | tee -a "$HUMAN" >&2
}

emit() { # emit <step> <status> <json-fragment>
  local now_ns
  now_ns="$(date +%s%N)"
  printf '{"schema":"%s","run_id":"%s","scenario":"canon_lifecycle","step":"%s","status":"%s","bead":"%s","claim":"stack-safe-canonical-lifecycle","invariant":"FL-INV-07","workstream":"W1","elapsed_ms":%d,%s}\n' \
    "$SCHEMA" "$RUN_ID" "$1" "$2" "$BEAD" "$(( (now_ns - START_NS) / 1000000 ))" "$3" >> "$EVENTS"
}

finalize_on_exit() {
  local rc=$?
  if [ "$FINALIZED" -eq 0 ]; then
    emit run_end failed "\"expected_exit\":0,\"actual_exit\":$rc,\"cleanup\":\"artifacts-retained\",\"final_state\":\"unexpected-exit\""
    note "FAIL (exit $rc) — artifacts retained in $ART_DIR"
  fi
}
trap finalize_on_exit EXIT HUP INT TERM

SOURCE_HASH="$(sha256sum \
  "$ROOT/crates/fln-core/src/expr.rs" \
  "$ROOT/crates/fln-core/src/level.rs" \
  "$ROOT/crates/fln-hash/src/canon.rs" | sha256sum | cut -d' ' -f1)"
TOOLCHAIN="$(rustup show active-toolchain | cut -d' ' -f1)"
RUSTC_COMMIT="$(rustc -Vv | awk '/^commit-hash:/ {print $2}')"
HOST="$(uname -srm)"
emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"cargo test -q -p fln-hash $TEST_NAME -- --exact --nocapture\",\"epoch\":\"SUITE.lock\",\"mode\":\"sound\",\"profile\":\"test\",\"platform\":\"$HOST\",\"thread_count\":1,\"seed\":0,\"cache_state\":\"declared-existing\",\"toolchain\":\"$TOOLCHAIN\",\"rustc_commit\":\"$RUSTC_COMMIT\",\"canonical_input_hash\":\"$SOURCE_HASH\",\"depth\":$DEPTH,\"runs\":$RUNS,\"stack_bytes\":1048576"

note "positive stress: $RUNS sacrificial processes at depth $DEPTH"
set +e
( cd "$ROOT" && \
  FLN_CANON_LIFECYCLE_DEPTH="$DEPTH" \
  FLN_CANON_LIFECYCLE_NAME_DEPTH=1024 \
  FLN_CANON_LIFECYCLE_RUNS="$RUNS" \
  cargo test -q -p fln-hash "$TEST_NAME" -- --exact --nocapture \
) > "$ART_DIR/stress.stdout" 2> "$ART_DIR/stress.stderr"
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit stress failed "\"expected_exit\":0,\"actual_exit\":$rc,\"stdout\":\"stress.stdout\",\"stderr\":\"stress.stderr\",\"first_divergence\":\"positive-child-failure\""
  exit 1
fi
records="$(grep -c '\"schema\":\"fln.e2e.canon-lifecycle\"' "$ART_DIR/stress.stdout" || true)"
if [ "$records" -ne "$RUNS" ]; then
  emit stress failed "\"expected_records\":$RUNS,\"actual_records\":$records,\"stdout\":\"stress.stdout\",\"stderr\":\"stress.stderr\",\"first_divergence\":\"missing-child-terminal-record\""
  exit 1
fi
emit stress passed "\"expected_exit\":0,\"actual_exit\":0,\"expected_records\":$RUNS,\"actual_records\":$records,\"depth\":$DEPTH,\"stack_bytes\":1048576,\"stdout\":\"stress.stdout\",\"stderr\":\"stress.stderr\",\"cleanup\":\"zero-survivors\",\"final_state\":\"all-recovered\""

note "million-node boundary: one sacrificial process at depth $MILLION_DEPTH"
set +e
( cd "$ROOT" && \
  FLN_CANON_LIFECYCLE_DEPTH="$MILLION_DEPTH" \
  FLN_CANON_LIFECYCLE_NAME_DEPTH=100000 \
  FLN_CANON_LIFECYCLE_RUNS=1 \
  cargo test -q -p fln-hash "$TEST_NAME" -- --exact --nocapture \
) > "$ART_DIR/million.stdout" 2> "$ART_DIR/million.stderr"
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit million_boundary failed "\"expected_exit\":0,\"actual_exit\":$rc,\"depth\":$MILLION_DEPTH,\"stdout\":\"million.stdout\",\"stderr\":\"million.stderr\""
  exit 1
fi
emit million_boundary passed "\"expected_exit\":0,\"actual_exit\":0,\"depth\":$MILLION_DEPTH,\"stack_bytes\":1048576,\"stdout\":\"million.stdout\",\"stderr\":\"million.stderr\",\"cleanup\":\"complete\",\"final_state\":\"recovery-decoded\""

for mutant in recursive-level-encoder recursive-expr-encoder; do
  note "mutation kill: $mutant must fail in its sacrificial process"
  set +e
  ( cd "$ROOT" && \
    FLN_CANON_LIFECYCLE_DEPTH="$DEPTH" \
    FLN_CANON_LIFECYCLE_RUNS=1 \
    FLN_CANON_LIFECYCLE_MUTANT="$mutant" \
    cargo test -q -p fln-hash "$TEST_NAME" -- --exact --nocapture \
  ) > "$ART_DIR/$mutant.stdout" 2> "$ART_DIR/$mutant.stderr"
  rc=$?
  set -e
  if [ "$rc" -eq 0 ]; then
    emit "$mutant" failed "\"expected_exit\":\"nonzero\",\"actual_exit\":0,\"stdout\":\"$mutant.stdout\",\"stderr\":\"$mutant.stderr\",\"first_divergence\":\"recursive-mutant-survived\""
    exit 1
  fi
  emit "$mutant" passed "\"expected_exit\":\"nonzero\",\"actual_exit\":$rc,\"detected\":\"bounded-stack-recursion\",\"stdout\":\"$mutant.stdout\",\"stderr\":\"$mutant.stderr\",\"final_state\":\"mutant-killed\""
done

note "clean recovery after mutation probes"
set +e
( cd "$ROOT" && \
  FLN_CANON_LIFECYCLE_DEPTH=128 \
  FLN_CANON_LIFECYCLE_RUNS=1 \
  cargo test -q -p fln-hash "$TEST_NAME" -- --exact --nocapture \
) > "$ART_DIR/recovery.stdout" 2> "$ART_DIR/recovery.stderr"
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit recovery failed "\"expected_exit\":0,\"actual_exit\":$rc,\"stdout\":\"recovery.stdout\",\"stderr\":\"recovery.stderr\""
  exit 1
fi
emit recovery passed "\"expected_exit\":0,\"actual_exit\":0,\"stdout\":\"recovery.stdout\",\"stderr\":\"recovery.stderr\",\"cleanup\":\"complete\",\"final_state\":\"shallow-recovery-decoded\""

emit run_end passed "\"expected_exit\":0,\"actual_exit\":0,\"verdict\":\"pass\",\"artifacts_dir\":\"target/e2e/$RUN_ID\",\"cleanup\":\"zero-survivors-artifacts-retained\",\"final_state\":\"all-assertions-satisfied\""
FINALIZED=1
note "PASS — artifacts retained in $ART_DIR"
