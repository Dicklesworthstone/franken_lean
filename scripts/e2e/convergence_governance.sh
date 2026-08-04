#!/usr/bin/env bash
# convergence_governance.sh — retained no-mock R15 control-plane E2E (bead 149).
#
# This intentionally needs an EMPTY caller-provided scratch directory.  It creates a real br
# project there, invokes real br mutations and bv robot output, then preserves every input and
# report.  No production .beads state is read or changed, and this script never removes anything.

set -euo pipefail
set -C
umask 077
export LC_ALL=C
export CARGO_TERM_COLOR=never
export RUST_LOG=error

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
POLICY_JUDGE="$ROOT/scripts/convergence_governance.py"

usage() {
  printf 'usage: %s --scratch EMPTY_DIRECTORY\n' "$0" >&2
  exit 64
}

SCRATCH=""
while (($#)); do
  case "$1" in
    --scratch)
      (($# >= 2)) || usage
      SCRATCH="$2"
      shift 2
      ;;
    *) usage ;;
  esac
done

[[ -n "$SCRATCH" ]] || usage
[[ -d "$SCRATCH" ]] || { printf 'scratch directory does not exist: %s\n' "$SCRATCH" >&2; exit 64; }
[[ -z "$(find "$SCRATCH" -mindepth 1 -maxdepth 1 -print -quit)" ]] || {
  printf 'scratch directory is not empty; refusing to overwrite retained evidence: %s\n' "$SCRATCH" >&2
  exit 64
}
[[ -x "$POLICY_JUDGE" || -f "$POLICY_JUDGE" ]] || { printf 'missing policy judge\n' >&2; exit 1; }

run_id="149-governance-e2e-$(date -u +%Y%m%dT%H%M%SZ)-$$"
LOG="$SCRATCH/run.ndjson"
POLICY="$SCRATCH/policy.json"
REPORT="$SCRATCH/report.ndjson"
START_SECONDS=$SECONDS

sha256_file() {
  sha256sum -- "$1" | awk '{print $1}'
}

event() {
  local step="$1"
  local expected="$2"
  local actual="$3"
  local command="${4:--}"
  local stdout_path="${5:--}"
  local stderr_path="${6:--}"
  local report_path="${7:--}"
  local elapsed_ms=$((SECONDS * 1000 - START_SECONDS * 1000))
  jq -cn \
    --arg schema 'fln.convergence-governance-e2e/1' \
    --arg run_id "$run_id" \
    --arg bead 'franken_lean-convergence-wip-governance-149' \
    --arg step "$step" \
    --arg expected "$expected" \
    --arg actual "$actual" \
    --arg cwd "$SCRATCH" \
    --arg command "$command" \
    --arg stdout_path "$stdout_path" \
    --arg stderr_path "$stderr_path" \
    --arg report_path "$report_path" \
    --argjson elapsed_ms "$elapsed_ms" \
    '{schema:$schema,run_id:$run_id,bead:$bead,step:$step,expected:$expected,actual:$actual,cwd:$cwd,command:$command,stdout_path:$stdout_path,stderr_path:$stderr_path,report_path:$report_path,elapsed_ms:$elapsed_ms,final_state:"retained"}' \
    >> "$LOG"
}

id_from() {
  jq -er 'if type == "array" then .[0].id else .id end'
}

create() {
  local title="$1"
  br create "$title" --priority 1 --json --no-auto-flush --no-auto-import | id_from
}

write_policy() {
  local exception_expiry="$1"
  jq -n \
    --arg root "$ROOT_BEAD" --arg ready "$READY_BEAD" --arg blocked "$BLOCKED_BEAD" \
    --arg additive "$ADDITIVE_BEAD" --arg active1 "$ACTIVE1_BEAD" --arg active2 "$ACTIVE2_BEAD" \
    --arg active3 "$ACTIVE3_BEAD" --arg incident "$INCIDENT_BEAD" --arg later "$LATER_BEAD" \
    --arg expiry "$exception_expiry" \
    '{schema:"fln.convergence-governance-policy/1",policy_version:"e2e/1",workstreams:["W1","W2","W3"],wip:{max_active_workstreams:2,verification_reservation:1,incident_reservation:1},review:{authority:"e2e",cadence_days:1,next_review:"2026-08-05T00:00:00Z"},gates:[{id:"G0",state:"failed",root_beads:[$root]},{id:"G1",state:"not_yet_runnable",root_beads:[$later]}],exceptions:[{id:"INC-1",owner:"e2e",scope:"incident",expiry:$expiry,review:"2026-08-04T12:00:00Z"}],registry:[{id:$root,class:"prerequisite",workstream:"W1",gate:"G0"},{id:$ready,class:"prerequisite",workstream:"W1",gate:"G0"},{id:$blocked,class:"prerequisite",workstream:"W1",gate:"G0"},{id:$additive,class:"additive",workstream:"W3",gate:"G1"},{id:$active1,class:"implementation",workstream:"W1",gate:"G0"},{id:$active2,class:"implementation",workstream:"W2",gate:"G0"},{id:$active3,class:"implementation",workstream:"W3",gate:"G0"},{id:$incident,class:"incident",workstream:"W1",gate:"G0"}]}' \
    >| "$POLICY"
}

run_policy() {
  local name="$1"
  local expected_exit="$2"
  local stdout="$SCRATCH/$name.stdout"
  local stderr="$SCRATCH/$name.stderr"
  local retained_report="$SCRATCH/$name.report.ndjson"
  set +e
  python3 -I -S -B "$POLICY_JUDGE" --root "$SCRATCH" --policy "$POLICY" \
    --at 2026-08-04T10:10:00Z --check --ndjson "$REPORT" \
    > "$stdout" 2> "$stderr"
  local code=$?
  set -e
  cp -- "$REPORT" "$retained_report"
  local decision
  decision="$(jq -c '{verdict,reason:(.reason // "-"),graph_hash:(.graph_hash // "-"),evidence_hash:(.evidence_hash // "-"),config_hash:(.config_hash // "-"),selected:([.selected[]? | {id,reason}]),held:([.held[]? | {id,reason}])}' "$retained_report")"
  local actual
  actual="exit=$code stdout_sha256=$(sha256_file "$stdout") stderr_sha256=$(sha256_file "$stderr") report_sha256=$(sha256_file "$retained_report") decision=$decision"
  [[ "$code" == "$expected_exit" ]] || {
    event "$name" "exit=$expected_exit" "$actual" "python3 -I -S -B convergence_governance.py --root <scratch> --policy <scratch>/policy.json --at 2026-08-04T10:10:00Z --check --ndjson <scratch>/$name.report.ndjson" "$stdout" "$stderr" "$retained_report"
    printf 'policy %s returned %s, expected %s\n' "$name" "$code" "$expected_exit" >&2
    exit 1
  }
  event "$name" "exit=$expected_exit" "$actual" "python3 -I -S -B convergence_governance.py --root <scratch> --policy <scratch>/policy.json --at 2026-08-04T10:10:00Z --check --ndjson <scratch>/$name.report.ndjson" "$stdout" "$stderr" "$retained_report"
}

cd "$SCRATCH"
br init --prefix cg --json --no-auto-flush --no-auto-import > "$SCRATCH/br-init.json"
mkdir "$SCRATCH/ci"
printf '%s\n' '{"schema":"fln.verification-manifest/2","bead":"e2e","gate_ids":["G0"],"kind":"coverage"}' \
  > "$SCRATCH/ci/VERIFICATION_MANIFEST.jsonl"
event toolchain 'sealed command identities' "python=$(python3 -I -S --version 2>&1) br=$(br --version 2>&1) bv=$(bv --version 2>&1) judge_sha256=$(sha256_file "$POLICY_JUDGE")" 'br/bv/python versions collected before tracker mutation'
ROOT_BEAD="$(create root-prerequisite)"
READY_BEAD="$(create ready-g0-blocker)"
BLOCKED_BEAD="$(create dependency-blocked-g0-blocker)"
ADDITIVE_BEAD="$(create additive-feature)"
ACTIVE1_BEAD="$(create active-w1)"
ACTIVE2_BEAD="$(create active-w2)"
ACTIVE3_BEAD="$(create candidate-w3)"
INCIDENT_BEAD="$(create bounded-incident)"
LATER_BEAD="$(create later-gate)"
br dep add "$BLOCKED_BEAD" "$ROOT_BEAD" --json --no-auto-flush --no-auto-import > "$SCRATCH/dep.json"
for bead in "$ACTIVE1_BEAD" "$ACTIVE2_BEAD"; do
  br update "$bead" --status in_progress --assignee e2e --json --no-auto-flush --no-auto-import \
    > "$SCRATCH/$bead.active.json"
done
write_policy 2026-08-04T11:00:00Z
bv --db "$SCRATCH/.beads" --robot-graph --format json --no-cache > "$SCRATCH/bv-robot-graph.json"
jq -e '.adjacency and .data_hash' "$SCRATCH/bv-robot-graph.json" > /dev/null
event bv-robot-graph 'real robot graph' "present sha256=$(sha256_file "$SCRATCH/bv-robot-graph.json")" 'bv --db <scratch>/.beads --robot-graph --format json --no-cache' "$SCRATCH/bv-robot-graph.json"

run_policy normal 0
jq -e \
  --arg ready "$READY_BEAD" --arg blocked "$BLOCKED_BEAD" --arg additive "$ADDITIVE_BEAD" --arg incident "$INCIDENT_BEAD" \
  '.verdict == "complete" and ([.selected[] | select(.id == $ready and .reason == "earliest-gate-ready-blocker")] | length == 1) and ([.selected[] | select(.id == $incident and .reason == "bounded-incident-exception")] | length == 1) and ([.held[] | select(.id == $blocked and .reason == "dependency-blocked")] | length == 1) and ([.held[] | select(.id == $additive and .reason == "frozen-earliest-gate")] | length == 1)' \
  "$REPORT" > /dev/null
event normal-decision 'ready+incident selected; blocked+additive held' 'matched'

br update "$ACTIVE3_BEAD" --status in_progress --assignee e2e --json --no-auto-flush --no-auto-import \
  > "$SCRATCH/$ACTIVE3_BEAD.over-cap.json"
run_policy over-cap 2
jq -e '.verdict == "over_cap" and (.active_workstreams | length == 3)' "$REPORT" > /dev/null
event over-cap 'over_cap' 'matched'

br close "$ACTIVE3_BEAD" --reason 'E2E drain before expiry branch' --json --no-auto-flush --no-auto-import \
  > "$SCRATCH/$ACTIVE3_BEAD.closed.json"
write_policy 2026-08-04T10:10:00Z
run_policy expired-exception 2
jq -e '.verdict == "inconclusive" and (.reason | contains("exception-expired"))' "$REPORT" > /dev/null
event expired-exception 'typed inconclusive' 'matched'

write_policy 2026-08-04T11:00:00Z
br close "$ROOT_BEAD" --reason 'E2E unblock branch' --json --no-auto-flush --no-auto-import \
  > "$SCRATCH/$ROOT_BEAD.closed.json"
run_policy close-unblock 0
jq -e --arg blocked "$BLOCKED_BEAD" '[.selected[] | select(.id == $blocked and .reason == "earliest-gate-ready-blocker")] | length == 1' "$REPORT" > /dev/null
event close-unblock 'blocked bead becomes selected after root closes' 'matched'

br list --all --json --no-auto-flush --no-auto-import > "$SCRATCH/final-br-state.json"
event final-state 'production untouched; isolated br project retained' 'matched'
printf 'convergence-governance E2E: PASS; retained artifact root=%s run_id=%s\n' "$SCRATCH" "$run_id"
