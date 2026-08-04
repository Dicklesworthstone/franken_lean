#!/usr/bin/env bash
# Verify that the staged Reference snapshot is the exact Git tree pinned by SUITE.lock.
# This is a CI/development integrity check; vendored Reference code is never built or run.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  echo "[verify_vendor_tree] setup failure: python3 is required" >&2
  exit 2
}
HOSTILE_PYTHON_CONFIGURATION=()
while IFS= read -r environment_name; do
  [[ "$environment_name" == PYTHON* ]] \
    && HOSTILE_PYTHON_CONFIGURATION+=("$environment_name")
done < <(compgen -e | LC_ALL=C sort)
if ((${#HOSTILE_PYTHON_CONFIGURATION[@]} > 0)); then
  printf '[verify_vendor_tree] setup failure: sealed_interpreter_hostile_environment names=%s\n' \
    "$(IFS=,; printf '%s' "${HOSTILE_PYTHON_CONFIGURATION[*]}")" >&2
  exit 2
fi
exec "$PYTHON_BIN" -I -S "$ROOT/scripts/evidence.py" vendor-binding \
  --root "$ROOT" --vendor-path vendor/lean4-src
