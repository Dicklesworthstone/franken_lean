#!/usr/bin/env bash
# suite_upgrade_candidate_preflight.sh — refuse an incomplete suite-upgrade
# candidate before the governed no-mock runner is allowed to derive roots or
# invoke Cargo/Tribunal work. This is deliberately a preflight, not an
# evidence-bundle lane: no real candidate evidence bundle exists at HEAD yet.

set -Eeuo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
SCENARIO="suite_upgrade_no_mock_e2e"
CANDIDATE_DIR="${FLN_SUITE_UPGRADE_CANDIDATE_DIR:-}"
REQUIRED_ARTIFACTS=(
  SUITE.lock
  candidate-receipt.ndjson
  closure.ndjson
  contract-census.ndjson
  tribunal.ndjson
  migration.ndjson
  rollback.ndjson
  external-evidence.ndjson
)

if [ -z "$CANDIDATE_DIR" ]; then
  printf '%s\n' \
    '[suite_upgrade_candidate_preflight] inconclusive: set' \
    'FLN_SUITE_UPGRADE_CANDIDATE_DIR to an isolated candidate bundle' >&2
  exit 3
fi

if [ -L "$CANDIDATE_DIR" ] || [ ! -d "$CANDIDATE_DIR" ]; then
  printf '[suite_upgrade_candidate_preflight] refused: candidate root is not a real directory: %s\n' \
    "$CANDIDATE_DIR" >&2
  exit 1
fi

CANDIDATE_ROOT="$(cd "$CANDIDATE_DIR" && pwd -P)"
is_within() {
  local child="$1"
  local parent="$2"
  if [[ "$parent" == / ]]; then
    [[ "$child" == /* ]]
  else
    [[ "$child" == "$parent" || "$child" == "$parent"/* ]]
  fi
}

if is_within "$CANDIDATE_ROOT" "$ROOT" || is_within "$ROOT" "$CANDIDATE_ROOT"; then
  printf '%s\n' \
    '[suite_upgrade_candidate_preflight] refused: candidate root overlaps the authoritative checkout' >&2
  exit 1
fi

CANDIDATE_DIR="$CANDIDATE_ROOT"

for artifact in "${REQUIRED_ARTIFACTS[@]}"; do
  artifact_path="$CANDIDATE_DIR/$artifact"
  if [ -L "$artifact_path" ] || [ ! -f "$artifact_path" ] || [ ! -s "$artifact_path" ]; then
    printf '[suite_upgrade_candidate_preflight] refused: required candidate artifact is absent, symlinked, or empty: %s\n' \
      "$artifact" >&2
    exit 1
  fi
done

for required_command in cargo sha256sum; do
  command -v "$required_command" >/dev/null 2>&1 || {
    printf '[suite_upgrade_candidate_preflight] setup failure: %s is required\n' \
      "$required_command" >&2
    exit 2
  }
done

digest() {
  local digest_line
  digest_line="$(sha256sum -- "$1")" || return
  printf '%s\n' "${digest_line%% *}"
}

require_unchanged_root() {
  local label="$1"
  local expected_root="$2"
  local path="$3"
  local actual_root
  actual_root="$(digest "$path")" || actual_root=""
  if [[ -z "$actual_root" || "$actual_root" != "$expected_root" ]]; then
    printf '[suite_upgrade_candidate_preflight] inconclusive: %s changed during candidate preflight\n' \
      "$label" >&2
    return 1
  fi
}

current_lock_root="$(digest "$ROOT/SUITE.lock")"
candidate_lock_root="$(digest "$CANDIDATE_DIR/SUITE.lock")"
closure_root="$(digest "$CANDIDATE_DIR/closure.ndjson")"
contract_census_root="$(digest "$CANDIDATE_DIR/contract-census.ndjson")"
tribunal_root="$(digest "$CANDIDATE_DIR/tribunal.ndjson")"
migration_root="$(digest "$CANDIDATE_DIR/migration.ndjson")"
rollback_root="$(digest "$CANDIDATE_DIR/rollback.ndjson")"
external_evidence_root="$(digest "$CANDIDATE_DIR/external-evidence.ndjson")"

FLN_SUITE_UPGRADE_RECEIPT_PATH="$CANDIDATE_DIR/candidate-receipt.ndjson" \
FLN_SUITE_UPGRADE_CURRENT_LOCK_ROOT="$current_lock_root" \
FLN_SUITE_UPGRADE_CANDIDATE_LOCK_ROOT="$candidate_lock_root" \
FLN_SUITE_UPGRADE_CLOSURE_ROOT="$closure_root" \
FLN_SUITE_UPGRADE_CONTRACT_CENSUS_ROOT="$contract_census_root" \
FLN_SUITE_UPGRADE_TRIBUNAL_ROOT="$tribunal_root" \
FLN_SUITE_UPGRADE_MIGRATION_ROOT="$migration_root" \
FLN_SUITE_UPGRADE_ROLLBACK_ROOT="$rollback_root" \
FLN_SUITE_UPGRADE_EXTERNAL_EVIDENCE_ROOT="$external_evidence_root" \
  cargo test --locked -q -p fln-conformance --test suite_upgrade_governance \
    suite_upgrade_candidate_bundle_from_environment

if ! require_unchanged_root \
  'authoritative SUITE.lock' "$current_lock_root" "$ROOT/SUITE.lock" \
  || ! require_unchanged_root \
    'candidate SUITE.lock' "$candidate_lock_root" "$CANDIDATE_DIR/SUITE.lock" \
  || ! require_unchanged_root \
    'candidate closure evidence' "$closure_root" "$CANDIDATE_DIR/closure.ndjson" \
  || ! require_unchanged_root \
    'candidate contract/census evidence' "$contract_census_root" "$CANDIDATE_DIR/contract-census.ndjson" \
  || ! require_unchanged_root \
    'candidate Tribunal evidence' "$tribunal_root" "$CANDIDATE_DIR/tribunal.ndjson" \
  || ! require_unchanged_root \
    'candidate migration evidence' "$migration_root" "$CANDIDATE_DIR/migration.ndjson" \
  || ! require_unchanged_root \
    'candidate rollback evidence' "$rollback_root" "$CANDIDATE_DIR/rollback.ndjson" \
  || ! require_unchanged_root \
    'candidate external evidence' "$external_evidence_root" "$CANDIDATE_DIR/external-evidence.ndjson"; then
  exit 3
fi

printf '[suite_upgrade_candidate_preflight] ready: scenario=%s candidate=%s artifacts=%s\n' \
  "$SCENARIO" "$CANDIDATE_DIR" "${#REQUIRED_ARTIFACTS[@]}" >&2
