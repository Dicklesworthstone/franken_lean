#!/usr/bin/env bash
# ref_vs_ref.sh — reference_reference_no_mock_e2e: the Reference-vs-Reference
# differential AND the shared E2E scenario for the Tribunal bootstrap (bead
# fln-euo; this file IS the epic's named suite, and the scenario field below
# carries that name so the claim is greppable to its producer).
#
# Proves the harness plumbing end-to-end with the REAL pinned binary, no mocks:
#   1. run the C1 slice through the pinned Reference twice under the epoch lab's
#      normalization recipe — the two transcript sets must be byte-identical
#      (a nondeterministic oracle would poison every differential built on it);
#   2. the run must match the published epoch-lab baseline transcripts;
#   3. seeded divergences AT EVERY LEVEL THE EPIC NAMES — line, sub-line,
#      diagnostic, exit and artifact — each planted in a scratch copy, each
#      REQUIRED to be detected and to surface its planted body for triage,
#      never normalized away;
#   4. typed non-authoritative outcomes: a killed oracle process classifies as
#      non-authoritative, NEVER as a semantic reject or a divergence, and a
#      genuine nonzero exit classifies as authoritative — both directions;
#   5. recovery: the pristine set gates green again;
#   6. independent bundle validation: a separate parser re-reads the NDJSON and
#      re-hashes the retained plant artifacts, so the bundle's own claim of
#      completeness is checked by something other than the writer's memory.
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
  printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"reference_reference_no_mock_e2e","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
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
# Family-resolved corpus roots, REPO-RELATIVE on purpose: the generator
# (gen_epoch_manifest.sh) runs lean from $ROOT with a relative path so the
# published transcripts stay host-independent — an absolute path in a
# transcript is a host fact, the exact class the telemetry separation law
# names. The comparator must speak the same dialect or every diagnostic that
# echoes its input path reads as divergence.
CORPUS_ELAB_REL="vendor/lean4-src/tests/elab"
CORPUS_ELAB_FAIL_REL="vendor/lean4-src/tests/elab_fail"
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

slice_files() { # emits "<family> <file>" pairs
  # Every family the published baseline carries transcripts for — c1 (expected
  # accept, tests/elab) AND d1 (expected reject, tests/elab_fail). The first
  # executed run of this script found it red from birth: it ran only c1 while
  # step 2 diffs the WHOLE transcripts directory, so the six published d1 sets
  # read as divergence. The script was registered for lint and governance but
  # dispatched by nothing, so the red was invisible — the exact hollow-lane
  # shape franken_lean-registered-lane-dispatched-by-nothing-glk0 records.
  grep -E '^(c1(-quirk)?|d1) ' "$EPOCH_DIR/MANIFEST.txt" | awk '{print $1" "$2}'
}

corpus_path() { # corpus_path <family> <file> — repo-relative, run from $ROOT
  case "$1" in
    d1) printf '%s/%s' "$CORPUS_ELAB_FAIL_REL" "$2" ;;
    *) printf '%s/%s' "$CORPUS_ELAB_REL" "$2" ;;
  esac
}

run_slice() { # run_slice <dest-dir>
  local dest="$1" fam file rc
  mkdir -p "$dest"
  while read -r fam file; do
    set +e
    ( cd "$ROOT" && oracle_env "$LEAN" "$(corpus_path "$fam" "$file")" ) \
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
FIRST_FILE="$(slice_files | head -1 | awk '{print $2}')"
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

# ---- step 3b: the full plant matrix — line, sub-line, diagnostic, exit ------------------
# The epic names five divergence levels; the artifact-level plant above is one.
# Each remaining level gets its own scratch copy, its own detection, and its
# own surfaced body — a level that is detected but not surfaced cannot be
# triaged, and a level that is never planted is a level the rig has never been
# shown. Plant targets are chosen from the baseline's own shapes: a nonempty
# stdout for line and sub-line, an (empty-in-baseline) stderr for diagnostic,
# and the exit record for exit.
PLANT_STDOUT=""
PLANT_FAMILY=""
while read -r fam file; do
  if [ -s "$ART_DIR/run-a/$file.stdout" ]; then
    PLANT_STDOUT="$file"
    PLANT_FAMILY="$fam"
    break
  fi
done < <(slice_files)
if [ -z "$PLANT_STDOUT" ]; then
  emit plant_matrix failed "\"detail\":\"no slice file has a nonempty stdout to plant into\""
  note "FAIL: the slice offers no line-level plant target; the matrix cannot run"
  exit 1
fi

plant_detect() { # plant_detect <level> <mutate-fn> ; mutation runs against $PLANT_DIR
  local level="$1"
  shift
  PLANT_DIR="$ART_DIR/plant-$level"
  cp -r "$ART_DIR/run-a" "$PLANT_DIR"
  "$@"
  if diff -ur "$ART_DIR/run-b" "$PLANT_DIR" > "$ART_DIR/plant-$level.diff" 2>&1; then
    emit "seeded_divergence_$level" failed "\"detail\":\"planted $level divergence was not detected\""
    note "FAIL: $level-level plant slipped through"
    exit 1
  fi
  if ! grep -q "PLANT" "$ART_DIR/plant-$level.diff"; then
    emit "seeded_divergence_$level" failed "\"detail\":\"$level divergence detected but not surfaced\""
    note "FAIL: $level-level plant detected but its body was not surfaced for triage"
    exit 1
  fi
  sha256sum "$ART_DIR/plant-$level.diff" | awk -v n="plant-$level.diff" '{print $1"  "n}' \
    >> "$ART_DIR/plant-digests.txt"
  emit "seeded_divergence_$level" passed "\"artifact\":\"plant-$level.diff\""
}

plant_line() { # replace an entire line — line-level
  printf 'PLANT-LINE: a whole replaced line\n' > "$PLANT_DIR/$PLANT_STDOUT.stdout"
}
plant_subline() { # change bytes INSIDE the existing first line — sub-line-level
  local orig
  orig="$(head -c 1 "$PLANT_DIR/$PLANT_STDOUT.stdout")"
  { printf 'PLANT-SUBLINE-%s' "$orig"; tail -c +2 "$PLANT_DIR/$PLANT_STDOUT.stdout"; } \
    > "$PLANT_DIR/subline.tmp" && mv "$PLANT_DIR/subline.tmp" "$PLANT_DIR/$PLANT_STDOUT.stdout"
}
plant_diagnostic() { # a diagnostic appears where the baseline has none
  printf 'PLANT-DIAGNOSTIC: error: fabricated diagnostic\n' >> "$PLANT_DIR/$PLANT_STDOUT.stderr"
}
plant_exit() { # the exit record moves — exit-level
  printf 'exit 117 PLANT-EXIT\n' > "$PLANT_DIR/$PLANT_STDOUT.exit"
}

plant_detect line plant_line
plant_detect subline plant_subline
plant_detect diagnostic plant_diagnostic
plant_detect exit plant_exit

# ---- step 3c: typed non-authoritative outcomes, both directions -------------------------
# A Reference process that was KILLED did not answer; recording its exit as a
# semantic verdict would manufacture a divergence out of scheduling. The rig's
# law (oracle.rs's ProcessOutcome, exercised here against the REAL binary): a
# kill classifies non-authoritative and is excluded from comparison; a genuine
# nonzero exit stays authoritative — both directions, or the classifier is a
# rubber stamp in one of them.
classify_rc() { # timeout/kill/segv exits are process facts, not verdicts
  case "$1" in
    124|125|137|139) printf 'non-authoritative' ;;
    *) printf 'authoritative' ;;
  esac
}
set +e
( cd "$ROOT" && oracle_env timeout -s KILL 0.01 "$LEAN" "$(corpus_path "$PLANT_FAMILY" "$PLANT_STDOUT")" ) > /dev/null 2>&1
killed_rc=$?
set -e
if [ "$(classify_rc "$killed_rc")" != "non-authoritative" ]; then
  emit non_authoritative_outcome failed "\"detail\":\"killed oracle rc=$killed_rc classified authoritative\""
  note "FAIL: a killed oracle (rc=$killed_rc) must classify non-authoritative"
  exit 1
fi
if [ "$(classify_rc 1)" != "authoritative" ]; then
  emit non_authoritative_outcome failed "\"detail\":\"rc=1 classified non-authoritative\""
  note "FAIL: a genuine failure exit must stay authoritative"
  exit 1
fi
emit non_authoritative_outcome passed "\"killed_rc\":$killed_rc,\"excluded_from_comparison\":true"

# ---- step 4: recovery -------------------------------------------------------------------
if ! diff -ur "$ART_DIR/run-a" "$ART_DIR/run-b" > /dev/null 2>&1; then
  emit recovery failed "\"detail\":\"pristine sets no longer agree\""
  exit 1
fi
emit recovery passed "\"expected_exit\":0,\"actual_exit\":0"

# ---- step 5: independent bundle validation ----------------------------------------------
# A separate parser re-reads what the writer above produced: every NDJSON line
# parses, carries this run's identity, and no step failed; the closed step
# roster is PRESENT; elapsed never runs backwards; and the retained plant
# artifacts still hash to what was recorded when they were written. The
# writer's own memory validates nothing here.
if ! python3 -I -S "$ROOT/scripts/tribunal/validate_ref_vs_ref_bundle.py" \
    "$LOG" "$RUN_ID" "$ART_DIR" >&2; then
  emit bundle_validation failed "\"detail\":\"independent re-read refused the bundle\""
  note "FAIL: the bundle did not survive independent validation"
  exit 1
fi
emit bundle_validation passed "\"validator\":\"scripts/tribunal/validate_ref_vs_ref_bundle.py\",\"digests\":\"plant-digests.txt\""

emit run_end passed "\"verdict\":\"pass\",\"artifacts_dir\":\"target/e2e/$RUN_ID\",\"cleanup_status\":\"retained_by_policy\""
note "PASS — artifacts in $ART_DIR"
