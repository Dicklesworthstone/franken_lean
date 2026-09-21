#!/usr/bin/env -S python3 -I -S
from __future__ import annotations

from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))

from agent_handoff_lib import main

if __name__ == "__main__":
    raise SystemExit(main())
