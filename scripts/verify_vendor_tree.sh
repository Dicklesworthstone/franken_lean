#!/usr/bin/env bash
# Verify that the staged Reference snapshot is the exact Git tree pinned by SUITE.lock.
# This is a CI/development integrity check; vendored Reference code is never built or run.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
exec python3 "$ROOT/scripts/evidence.py" vendor-binding \
  --root "$ROOT" --vendor-path vendor/lean4-src
