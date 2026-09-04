#!/usr/bin/env bash
set -euo pipefail

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$ROOT"

python3 -m unittest discover -s scripts -p 'test_frontier_select*.py'
python3 scripts/test_agent_handoff.py
python3 scripts/test_agent_handoff_hierarchy.py
python3 scripts/agent_handoff.py snapshot --strict --recent 8 --limit 8 \
  | python3 scripts/agent_handoff.py verify --current - >/dev/null
