#!/usr/bin/env bash
# leanchecker_witness.sh — the FOREIGN kernel witness for the G0-2 differential
# (bead franken_lean-z6c; plan §8.3b, §18.1 "kernel verdicts diffed against
# lean4checker"; §8.7 standing kernel differential rig seed).
#
# The Oracle-Only Law (D8): `leanchecker` is the pinned Reference's independent
# kernel-replay tool; it participates here ONLY as a differential oracle inside
# the Tribunal, re-verifying that the C3 fixture modules type-check under the
# reference C++ kernel RIGHT NOW — a re-runnable confirmation, not merely "the
# olean exists". It is a dev/test lane, never a FrankenLean release component.
#
# This grounds the z6c kernel-replay premise (kernel_replay.rs: "the Reference
# accepted every declaration in this module") in an independent binary rather
# than in the artifact's mere existence. Lanes:
#   1. oracle provenance — leanchecker + lean located and commit-verified;
#   2. witness verdicts — leanchecker replays each C3 module through the
#      reference kernel; every one must be Accepted (exit 0, no exception);
#   3. anti-rubber-stamp — a nonexistent module MUST be reported as a failure,
#      proving the witness actually discriminates;
#   4. cross-reference — the witnessed modules are exactly the C3 corpus the
#      FrankenLean decoder+replay consumes.
# Human logs on stderr; schema-versioned NDJSON under target/e2e/. Retained.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RUN_ID="leanchecker-witness-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ROOT/target/e2e/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$(dirname "$ART_DIR")"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  echo "[leanchecker_witness] setup failure: evidence directory already claimed: $ART_DIR" >&2
  exit 2
fi

BEAD="franken_lean-z6c"
SCHEMA="fln-e2e/1"
HOST="$(uname -sr)"
start_ns=$(date +%s%N)

emit() { # emit <step_id> <status> <detail-json-fragment>
  local now_ns
  now_ns=$(date +%s%N)
  printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"leanchecker_witness","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
    "$SCHEMA" "$RUN_ID" "$BEAD" "$1" "$2" $(( (now_ns - start_ns) / 1000000 )) "$HOST" "$3" >> "$LOG"
}

note() { echo "[leanchecker_witness] $*" >&2; }

emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"$0\""

# ---- lane 1: oracle provenance (D8) ----------------------------------------------------
PIN_LINE="$(grep -E '^reference ' "$ROOT/SUITE.lock")"
PIN_TAG="$(sed -E 's/.*tag=([^ ]+).*/\1/' <<<"$PIN_LINE")"
PIN_COMMIT="$(sed -E 's/.*commit=([0-9a-f]{40}).*/\1/' <<<"$PIN_LINE")"
TC="$HOME/.elan/toolchains/leanprover--lean4---$PIN_TAG"
CHECKER="$TC/bin/leanchecker"
LEAN="$TC/bin/lean"
LIB="$TC/lib/lean"

if [ ! -x "$CHECKER" ] || [ ! -x "$LEAN" ] || [ ! -d "$LIB" ]; then
  # Typed, honest skip: the foreign witness is a real external binary; without
  # the pinned toolchain this lane cannot run. The z6c decoder/replay suites
  # still stand on their own (kernel_replay.sh).
  emit provenance skipped "\"reason\":\"reference_toolchain_absent\",\"limitation\":\"L0: foreign-witness differential unverified on this host\""
  note "SKIP: pinned leanchecker/lean not installed (typed limitation)"
  emit run_end skipped "\"cleanup_status\":\"retained_by_policy\",\"artifact_dir\":\"target/e2e/$RUN_ID\""
  exit 0
fi

VERSION="$("$LEAN" --version)"
if ! grep -q "$PIN_COMMIT" <<<"$VERSION"; then
  emit provenance failed "\"reason\":\"commit_mismatch\",\"binary\":\"$VERSION\",\"pinned\":\"$PIN_COMMIT\""
  note "FAIL: toolchain commit does not match SUITE.lock pin"
  exit 1
fi
emit provenance passed "\"oracle\":\"$VERSION\",\"checker\":\"leanchecker\",\"pin_tag\":\"$PIN_TAG\""
note "oracle: $VERSION (leanchecker)"

export PATH="$TC/bin:$PATH"
export LEAN_PATH="$LIB"

# witness <module> -> prints "accepted"/"rejected", writes stderr artifact
witness() { # witness <module> <artifact-basename>
  local module="$1" base="$2" out rc
  out="$ART_DIR/$base"
  set +e
  timeout 300 "$CHECKER" "$module" > "$out.out" 2> "$out.err"
  rc=$?
  set -e
  # leanchecker exits 0 and is silent on success; on any failure (missing
  # olean, kernel rejection) it prints an "uncaught exception"/"error" line.
  if [ "$rc" -eq 0 ] && ! grep -qiE 'uncaught exception|error' "$out.err" "$out.out"; then
    echo "accepted"
  else
    echo "rejected"
  fi
}

# ---- lane 2: witness verdicts over the C3 corpus ---------------------------------------
# module name -> the C3 fixture file it corresponds to (same bytes as the pin).
declare -A C3_MODULES=(
  [Init.BinderNameHint]=Init.BinderNameHint.olean
  [Init.SizeOfLemmas]=Init.SizeOfLemmas.olean
)
# Init is an aggregator (imports only); the two above carry real declarations.
witnessed=0
for module in "${!C3_MODULES[@]}"; do
  fixture="${C3_MODULES[$module]}"
  # Cross-reference: the module the oracle checks must be the same bytes as our
  # decoder's fixture. leanchecker reads from LEAN_PATH; confirm the fixture we
  # decode is byte-identical to the pinned olean the oracle will read.
  pinned_olean="$LIB/${module//.//}.olean"
  if ! cmp -s "$pinned_olean" "$ROOT/tribunal/fixtures/c3/$fixture"; then
    emit cross_ref failed "\"module\":\"$module\",\"reason\":\"fixture_differs_from_pinned_olean\""
    note "FAIL: C3 fixture $fixture is not byte-identical to the pinned $module olean"
    exit 1
  fi
  verdict="$(witness "$module" "witness_${module//./_}")"
  if [ "$verdict" != "accepted" ]; then
    emit witness failed "\"module\":\"$module\",\"verdict\":\"$verdict\",\"artifact\":\"witness_${module//./_}.err\""
    note "FAIL: foreign witness REJECTED $module — the replay premise is violated"
    exit 1
  fi
  witnessed=$((witnessed + 1))
  emit witness passed "\"module\":\"$module\",\"verdict\":\"accepted\",\"fixture\":\"$fixture\",\"fixture_matches_pin\":true,\"claim\":\"kernel-witness-agreement\",\"parity_ledger_row\":\"not_applicable_foreign_kernel_witness\""
  note "witness: $module accepted by the reference kernel (leanchecker), fixture matches pin"
done
emit witnesses passed "\"count\":$witnessed,\"all\":\"accepted\""

# ---- lane 3: anti-rubber-stamp — the witness must discriminate --------------------------
note "control: a nonexistent module must be reported rejected"
neg_verdict="$(witness Init.__fln_no_such_module__ witness_negative)"
if [ "$neg_verdict" != "rejected" ]; then
  emit discriminate failed "\"module\":\"Init.__fln_no_such_module__\",\"verdict\":\"$neg_verdict\",\"expected\":\"rejected\""
  note "FAIL: witness accepted a nonexistent module — it is a rubber stamp, not a check"
  exit 1
fi
emit discriminate passed "\"module\":\"Init.__fln_no_such_module__\",\"verdict\":\"rejected\""
note "control: nonexistent module correctly reported rejected"

emit run_end passed "\"cleanup_status\":\"retained_by_policy\",\"artifact_dir\":\"target/e2e/$RUN_ID\",\"witnessed\":$witnessed"
note "PASS: foreign-witness differential green ($witnessed modules independently re-verified)"
