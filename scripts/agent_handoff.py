#!/usr/bin/env python3
from __future__ import annotations

import sys

sys.dont_write_bytecode = True

from agent_handoff_lib import main

if __name__ == "__main__":
    raise SystemExit(main())
