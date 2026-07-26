#!/usr/bin/env bash
# ref_vs_ref.sh — the Reference-vs-Reference smoke differential AND the shared E2E
# scenario for the Tribunal bootstrap (bead fln-euo).
#
# Proves the harness plumbing end-to-end with the REAL pinned binary, no mocks:
#   1. run the C1 slice through the pinned Reference twice under the epoch lab's
#      normalization recipe — the two transcript sets must be byte-identical
#      (a nondeterministic oracle would poison every differential built on it);
#   2. the run must match the published epoch-lab baseline transcripts;
#   3. seeded divergence: a planted diff in a scratch transcript MUST be detected
#      and triaged, never normalized away;
#   4. recovery: the pristine set gates green again.
# Human logs on stderr; schema-versioned NDJSON under target/e2e/. Retained fixtures.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RUN_ID="ref-vs-ref-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ROOT/target/e2e/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$(dirname "$ART_DIR")"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  echo "[ref_vs_ref] setup failure: evidence directory already claimed: $ART_DIR" >&2
  exit 2
fi

BEAD="fln-euo"
SCHEMA="fln-e2e/1"
HOST="$(uname -sr)"
start_ns=$(date +%s%N)

emit() { # emit <step_id> <status> <detail-json-fragment>
  local now_ns
  now_ns=$(date +%s%N)
  printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"ref_vs_ref","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
    "$SCHEMA" "$RUN_ID" "$BEAD" "$1" "$2" $(( (now_ns - start_ns) / 1000000 )) "$HOST" "$3" >> "$LOG"
}

note() { echo "[ref_vs_ref] $*" >&2; }

emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"$0\""

# ---- oracle + epoch lab -----------------------------------------------------------------
PIN_LINE="$(grep -E '^reference ' "$ROOT/SUITE.lock")"
PIN_TAG="$(sed -E 's/.*tag=([^ ]+).*/\1/' <<<"$PIN_LINE")"
PIN_COMMIT="$(sed -E 's/.*commit=([0-9a-f]{40}).*/\1/' <<<"$PIN_LINE")"
LEAN="$HOME/.elan/toolchains/leanprover--lean4---$PIN_TAG/bin/lean"
EPOCH_DIR="$ROOT/tribunal/epochs/$PIN_TAG"
CORPUS_DIR="$ROOT/vendor/lean4-src/tests/elab"
if [ ! -x "$LEAN" ] || ! "$LEAN" --version | grep -q "$PIN_COMMIT"; then
  emit oracle failed "\"detail\":\"pinned Reference binary missing or wrong commit\""
  note "FAIL: pinned Reference binary unavailable (a skipped oracle is not a pass)"
  exit 2
fi
if [ ! -f "$EPOCH_DIR/MANIFEST.txt" ]; then
  emit oracle failed "\"detail\":\"epoch lab not published (run gen_epoch_manifest.sh)\""
  exit 2
fi
emit oracle passed "\"binary\":\"$("$LEAN" --version | tr -d '"')\""

oracle_env() { env -u LEAN_PATH -u LEAN_SYSROOT LC_ALL=C TZ=UTC "$@"; }

slice_files() {
  grep -E '^c1(-quirk)? ' "$EPOCH_DIR/MANIFEST.txt" | awk '{print $2}'
}

run_slice() { # run_slice <dest-dir>
  local dest="$1" file rc
  mkdir -p "$dest"
  while IFS= read -r file; do
    set +e
    oracle_env "$LEAN" "$CORPUS_DIR/$file" \
      > "$dest/$file.stdout" 2> "$dest/$file.stderr"
    rc=$?
    set -e
    printf 'exit %s\n' "$rc" > "$dest/$file.exit"
  done < <(slice_files)
}

# ---- step 1: run twice; byte-identical --------------------------------------------------
note "running the C1 slice through the pinned Reference, twice"
run_slice "$ART_DIR/run-a"
run_slice "$ART_DIR/run-b"
if ! diff -ur "$ART_DIR/run-a" "$ART_DIR/run-b" > "$ART_DIR/ref-vs-ref.diff" 2>&1; then
  emit determinism failed "\"artifact\":\"ref-vs-ref.diff\""
  note "FAIL: the Reference diverged from itself (see $ART_DIR/ref-vs-ref.diff)"
  exit 1
fi
emit determinism passed "\"files\":$(slice_files | wc -l)"

# ---- step 2: the run must match the published epoch-lab baseline ------------------------
if ! diff -ur "$EPOCH_DIR/transcripts" "$ART_DIR/run-a" > "$ART_DIR/baseline.diff" 2>&1; then
  emit baseline failed "\"artifact\":\"baseline.diff\""
  note "FAIL: live oracle behavior departed from the published epoch baseline"
  exit 1
fi
emit baseline passed "\"baseline\":\"tribunal/epochs/$PIN_TAG/transcripts\""

# ---- step 3: a planted divergence must be detected --------------------------------------
SEEDED="$ART_DIR/seeded"
cp -r "$ART_DIR/run-a" "$SEEDED"
FIRST_FILE="$(slice_files | head -1)"
printf 'PLANTED-DIVERGENCE: this line must be detected, never normalized away\n' \
  >> "$SEEDED/$FIRST_FILE.stdout"
if diff -ur "$ART_DIR/run-b" "$SEEDED" > "$ART_DIR/seeded.diff" 2>&1; then
  emit seeded_divergence failed "\"detail\":\"planted diff was not detected\""
  note "FAIL: planted divergence slipped through"
  exit 1
fi
if ! grep -q "PLANTED-DIVERGENCE" "$ART_DIR/seeded.diff"; then
  emit seeded_divergence failed "\"detail\":\"diff did not surface the planted body\""
  note "FAIL: divergence detected but the body was not surfaced for triage"
  exit 1
fi
emit seeded_divergence passed "\"detected\":\"PLANTED-DIVERGENCE\",\"artifact\":\"seeded.diff\""

# ---- step 4: recovery -------------------------------------------------------------------
if ! diff -ur "$ART_DIR/run-a" "$ART_DIR/run-b" > /dev/null 2>&1; then
  emit recovery failed "\"detail\":\"pristine sets no longer agree\""
  exit 1
fi
emit recovery passed "\"expected_exit\":0,\"actual_exit\":0"

emit run_end passed "\"verdict\":\"pass\",\"artifacts_dir\":\"target/e2e/$RUN_ID\",\"cleanup_status\":\"retained_by_policy\""
note "PASS — artifacts in $ART_DIR"
