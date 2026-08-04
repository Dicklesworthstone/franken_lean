#!/usr/bin/env bash
# suite_upgrade_candidate_preflight.sh — refuse an incomplete suite-upgrade
# candidate before the governed no-mock runner is allowed to derive roots or
# invoke Cargo/Tribunal work. This is deliberately a preflight, not an
# fln.e2e/2 lane: no real candidate evidence bundle exists at HEAD yet.

set -Eeuo pipefail

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

for artifact in "${REQUIRED_ARTIFACTS[@]}"; do
  artifact_path="$CANDIDATE_DIR/$artifact"
  if [ -L "$artifact_path" ] || [ ! -f "$artifact_path" ] || [ ! -s "$artifact_path" ]; then
    printf '[suite_upgrade_candidate_preflight] refused: required candidate artifact is absent, symlinked, or empty: %s\n' \
      "$artifact" >&2
    exit 1
  fi
done

printf '[suite_upgrade_candidate_preflight] ready: scenario=%s candidate=%s artifacts=%s\n' \
  "$SCENARIO" "$CANDIDATE_DIR" "${#REQUIRED_ARTIFACTS[@]}" >&2
