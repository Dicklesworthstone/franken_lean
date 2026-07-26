#!/usr/bin/env bash
# python_isolation_probe.sh — the NEGATIVE probes for the trusted evidence
# interpreter (bead franken_lean-h40t; plan D8, FL-INV-07).
#
# scripts/evidence.py computes the governed tree hashes, validates run records,
# and publishes the bundle whose verdict every gate depends on. Python resolves
# imports from the running script's OWN DIRECTORY and from `PYTHONPATH` before
# the standard library, so a `hashlib.py` beside the script — or an ambient
# `PYTHONPATH` — replaces the module that computes the digests and decides the
# verdicts. `python3 -I` closes both channels.
#
# THIS PROBE EXISTS BECAUSE "-I IS SET" IS NOT EVIDENCE THAT -I WORKS. Asserting
# the flag proves the flag; it does not prove the channel is shut. So each
# vector is run TWICE:
#
#   1. NON-ISOLATED, which MUST be hijacked. If the hostile module fails to take
#      effect here, the probe has not reproduced the vector and its isolated
#      half proves nothing — a probe whose negative control does not fire is a
#      pass with no content. This is the anti-vacuity half and it is the reason
#      the script is worth more than an assertion.
#   2. ISOLATED, which MUST refuse.
#
# Both vectors, both directions, four outcomes, all four required.
#
# NOTHING IS WRITTEN INSIDE THE REPOSITORY. The hostile module is planted in a
# private temporary directory and removed on every exit path, including failure
# and interrupt: a probe that plants an attack module in the tree and dies
# before cleanup has manufactured the defect it was testing for.
#
# Usage:  scripts/tribunal/python_isolation_probe.sh
# Exit 0 = both vectors reproduced while unprotected AND refused under -I.
# Exit 1 = a vector was not refused under -I, or a negative control did not fire.
# Exit 2 = setup could not be established. Typed separately because "we could
#          not look" is not "we looked and found nothing" (FL-INV-07).

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RUN_ID="python-isolation-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ROOT/target/e2e/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$(dirname "$ART_DIR")"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  echo "[python_isolation_probe] setup failure: evidence directory already claimed: $ART_DIR" >&2
  exit 2
fi

SANDBOX="$(mktemp -d)"
# Deterministic teardown, deliberately NOT a recursive force-removal. AGENTS.md
# forbids that outright, and a probe is the last place to make an exception:
# every file this script creates is named below, so removing exactly those is
# both sufficient and auditable. `-B` on every interpreter invocation keeps
# Python from writing __pycache__ directories this list would not know about —
# and `-B` works under `-I`, whereas PYTHONDONTWRITEBYTECODE would be ignored by
# it, which is the whole point of isolation.
# shellcheck disable=SC2317  # invoked indirectly, by the trap below
cleanup() {
  rm -f "$SANDBOX/hostile/hashlib.py" "$SANDBOX/hostile/victim.py" \
    "$SANDBOX/neutral/victim.py"
  rmdir "$SANDBOX/hostile" "$SANDBOX/neutral" "$SANDBOX" 2>/dev/null || true
}
trap cleanup EXIT INT TERM

emit() { printf '%s\n' "$1" >>"$LOG"; }
say() { printf '[python-isolation] %s\n' "$1" >&2; }

setup_failure() {
  say "SETUP FAILURE: $1"
  emit "{\"schema\":\"fln.python-isolation-probe/1\",\"event\":\"run_end\",\"verdict\":\"inconclusive\",\"reason\":\"$1\"}"
  exit 2
}

command -v python3 >/dev/null || setup_failure "python3_absent"
PY_VERSION="$(python3 -c 'import sys; print(".".join(map(str, sys.version_info[:3])))' 2>/dev/null)" \
  || setup_failure "python3_unusable"

emit "{\"schema\":\"fln.python-isolation-probe/1\",\"event\":\"run_start\",\"run_id\":\"$RUN_ID\",\"python\":\"$PY_VERSION\"}"

# The hostile module. It shadows `hashlib`, which scripts/evidence.py imports and
# uses to compute governed digests. Its marker is unmistakable and could not be
# produced by the genuine module.
HOSTILE_DIR="$SANDBOX/hostile"
mkdir -p "$HOSTILE_DIR"
cat >"$HOSTILE_DIR/hashlib.py" <<'PYEOF'
HIJACKED = "hostile-hashlib-was-imported"


def sha256(*_args, **_kwargs):
    raise SystemExit("hostile sha256 reached")
PYEOF

# The victim reports which hashlib it actually got. It never trusts a flag; it
# reports an observable property of the imported module.
cat >"$HOSTILE_DIR/victim.py" <<'PYEOF'
import hashlib
import sys

print("HIJACKED" if getattr(hashlib, "HIJACKED", None) else "GENUINE")
print(f"isolated={bool(sys.flags.isolated)}")
PYEOF

FAILED=0
check() {
  local name="$1" expected="$2" actual="$3"
  if [[ "$actual" == "$expected" ]]; then
    say "ok   $name -> $actual"
    emit "{\"schema\":\"fln.python-isolation-probe/1\",\"event\":\"probe\",\"name\":\"$name\",\"expected\":\"$expected\",\"actual\":\"$actual\",\"pass\":true}"
  else
    FAILED=$((FAILED + 1))
    say "FAIL $name -> $actual (expected $expected)"
    emit "{\"schema\":\"fln.python-isolation-probe/1\",\"event\":\"probe\",\"name\":\"$name\",\"expected\":\"$expected\",\"actual\":\"$actual\",\"pass\":false}"
  fi
}

verdict_of() { head -1 "$1" 2>/dev/null || echo "NO_OUTPUT"; }

# ---- VECTOR 1: the script's own directory ---------------------------------
# `python3 path/to/victim.py` puts path/to/ at the front of sys.path.
python3 -B "$HOSTILE_DIR/victim.py" >"$ART_DIR/v1_plain.out" 2>&1
check "script_dir_vector_reproduces_while_unprotected" "HIJACKED" "$(verdict_of "$ART_DIR/v1_plain.out")"

python3 -IB "$HOSTILE_DIR/victim.py" >"$ART_DIR/v1_isolated.out" 2>&1
check "script_dir_vector_refused_under_isolation" "GENUINE" "$(verdict_of "$ART_DIR/v1_isolated.out")"

# ---- VECTOR 2: PYTHONPATH -------------------------------------------------
# Run the victim from a NEUTRAL directory so only PYTHONPATH can supply the
# hostile module; otherwise vector 1 would be doing the work and this probe
# would pass without ever exercising the environment channel.
NEUTRAL="$SANDBOX/neutral"
mkdir -p "$NEUTRAL"
cp "$HOSTILE_DIR/victim.py" "$NEUTRAL/victim.py"

PYTHONPATH="$HOSTILE_DIR" python3 -B "$NEUTRAL/victim.py" >"$ART_DIR/v2_plain.out" 2>&1
check "pythonpath_vector_reproduces_while_unprotected" "HIJACKED" "$(verdict_of "$ART_DIR/v2_plain.out")"

PYTHONPATH="$HOSTILE_DIR" python3 -IB "$NEUTRAL/victim.py" >"$ART_DIR/v2_isolated.out" 2>&1
check "pythonpath_vector_refused_under_isolation" "GENUINE" "$(verdict_of "$ART_DIR/v2_isolated.out")"

# ---- the flag is reported, and is NOT the evidence ------------------------
# Recorded because a reader will want it, and stated as secondary because the
# four checks above are the evidence: they observe which module was imported,
# not which flag was set.
ISO_LINE="$(sed -n '2p' "$ART_DIR/v1_isolated.out" 2>/dev/null)"
check "isolated_run_reports_the_flag" "isolated=True" "$ISO_LINE"

if [[ $FAILED -ne 0 ]]; then
  say "VERDICT fail — $FAILED of 5 checks did not hold"
  emit "{\"schema\":\"fln.python-isolation-probe/1\",\"event\":\"run_end\",\"verdict\":\"fail\",\"failed\":$FAILED}"
  exit 1
fi

say "VERDICT pass — both vectors reproduced while unprotected and refused under -I"
emit "{\"schema\":\"fln.python-isolation-probe/1\",\"event\":\"run_end\",\"verdict\":\"pass\",\"failed\":0}"
exit 0
