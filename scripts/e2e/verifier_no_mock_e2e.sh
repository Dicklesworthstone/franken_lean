#!/usr/bin/env bash
# W3 certificate verifier and governed recomputation fallback no-mock evidence lane (fln-eeyn).

set -Eeuo pipefail

PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  printf "[verifier_no_mock_e2e] setup failure: python3 is required\n" >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
for required_command in cargo git sha256sum; do
  command -v "$required_command" >/dev/null 2>&1 || {
    printf "[verifier_no_mock_e2e] setup failure: %s is required\n"       "$required_command" >&2
    exit 2
  }
done

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
cd "$ROOT"
EVIDENCE="$ROOT/scripts/evidence.py"
BEAD="fln-eeyn"
SCENARIO="verifier_no_mock_e2e"

printf "[verifier_no_mock_e2e] Running certificate verifier suites under cargo test...\n"

cargo test -q -p fln-hash   --test certificate_verifier_model   --test verifier_independence_guard   --test fallback_outcome_matrix   --test verifier_adversarial_fuzz

printf "[verifier_no_mock_e2e] PASS all verifier test suites green\n"
