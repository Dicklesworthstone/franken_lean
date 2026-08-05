# shellcheck shell=bash
# scripts/lib/gate_lock.sh — the build gate, taken by the lane instead of by its caller.
#
# Bead franken_lean-gate-lock-producer-optional-o2vz. Before this file the gate lockfile was named
# in ZERO executable surfaces: it engaged only if the launcher volunteered a wrapper. That left a
# FREE probe uninformative (an unwrapped lane takes no lock) AND a HELD probe uninformative
# (anything at all can take the path) — the empty referent at the process layer, on both branches.
# Sourcing this makes "the lane ran" entail "the lock was held" by construction.
#
# NOT sourced from scripts/e2e/. `build_gate_governed_sets.rs` and the worktree-refusal scope guard
# both derive the lane population by listing `scripts/e2e/*.sh`, and both fail in either direction,
# so a helper placed there would move a count those guards pin. Verified before this file was
# written, not assumed.

FLN_GATE_LOCKFILE="${FLN_GATE_LOCKFILE:-/data/tmp/fln-gate.lockfile}"
FLN_GATE_JOURNAL="${FLN_GATE_JOURNAL:-/data/tmp/fln-gate.journal}"
FLN_GATE_WAIT_S="${FLN_GATE_WAIT_S:-2400}"
FLN_GATE_STATE="unset"

# A caller that still wraps us in `flock <lockfile> …` hands us an OPEN, LOCKED fd on the lockfile.
# flock(2) locks belong to the open file description, so that fd already holds the gate on our
# behalf and a second acquire blocks against our own launcher — measured: a nested `flock -w 2`
# waits the full timeout and fails (elapsed_ms=2011), so the legacy `-w 2400` form would hang 40
# minutes. Detect the inherited descriptor instead of re-acquiring.
fln_gate_inherited() {
  local fd target
  for fd in /proc/self/fd/*; do
    target=$(readlink "$fd" 2>/dev/null) || continue
    [ "$target" = "$FLN_GATE_LOCKFILE" ] && return 0
  done
  return 1
}

# An inherited fd is a HYPOTHESIS, not a holding, and believing it is this bead's own defect one
# layer inside its repair: a descriptor opened on the lockfile and never flocked is indistinguishable
# from a wrapper's by any path scan, so the naive detector reports "we hold the gate" while nothing
# holds it — and then journals that claim, making it durable rather than merely believed.
#
# flock(2) locks belong to the OPEN FILE DESCRIPTION, so a SECOND descriptor discriminates exactly:
# a genuine ancestor lock conflicts with it, a merely-open fd does not. Measured in both directions
# on a scratch lockfile (open-but-unlocked => ACQUIRED; genuine `flock <lock> child` => BLOCKED).
#
#   returns 0 => an ancestor genuinely holds the gate; do NOT re-acquire, that is the hang above.
#   returns 1 => the fd was a decoy and nothing held the gate; fd 9 now does, so this is a repair
#                and not merely a diagnosis.
#   returns 2 => the lockfile could not be opened at all.
#
# `-n`, never `-w`: this probe cannot block. `>>` rather than `>` so the open never truncates a
# file another process may be holding.
fln_gate_confirm_inherited() {
  exec 9>>"$FLN_GATE_LOCKFILE" || return 2
  if flock -n 9; then
    return 1
  fi
  return 0
}

# o2vz Finding 2: "held" with no producer is the empty referent. Name what holds it.
# Name what actually HOLDS the gate lock.
#
# NOT `fuser`, and not `lsof`. AGENTS.md measured both false at `f5359c22`, in the
# direction that manufactures the phantom freeze this function exists to prevent:
# a lock belongs to the open file DESCRIPTION, while those tools report every
# process holding a DESCRIPTOR. Against a process that had merely done
# `exec 7>><lock>` and never locked — with the gate FREE by ground truth —
# `fuser -v` and `lsof` each named it a holder. `fuser`'s own ACCESS column reads
# `F`, meaning open for writing; it never claimed to mean locked.
#
# `/proc/locks` is the kernel's record of actual holdings: one FLOCK row per held
# lock, carrying the holding pid and the file's MAJOR:MINOR:INODE. Match on the
# inode and exclude our own process tree.
#
# THREE OUTCOMES, NOT TWO, and that is the structural part rather than an edge
# case. `/proc/<pid>/cwd` is unreadable for a process owned by another user, which
# on this shared box is the COMMON case — so a two-bucket classifier must put
# every such holder somewhere and is wrong whichever it picks. An unattributed
# holder is reported as neither a lane nor a stray.
#
# What this does not earn: `/proc/locks` and `/proc/<pid>/cwd` are Linux-specific;
# a process that chdirs after launch reports where it IS, not where it started;
# and where a lock is held through a shared open file description the kernel
# records one pid while others hold it too, so naming the recorded holder is a
# judgement rather than a measurement.
# The checkout this gate belongs to. Derived from this script's own location, so
# a copy of the library in another repository compares against ITS root rather
# than against a transcribed path.
: "${FLN_GATE_REPO_ROOT:=$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")/../.." && pwd)}"

fln_gate_name_holder() {
  local inode named=0 line pid cwd
  inode=$(stat -c '%i' "$FLN_GATE_LOCKFILE" 2>/dev/null) || {
    echo "  (the lockfile could not be stat'd — INDETERMINATE, not free)"
    return
  }
  while IFS= read -r line; do
    # Blocked WAITER rows begin with `->` and shift every column, so they are
    # skipped deliberately: a waiter is not a holder, and misreading one as a
    # holder reports a freeze that does not exist.
    case "$line" in *"->"*) continue ;; esac
    case "$line" in *FLOCK*) : ;; *) continue ;; esac
    # Columns: N: FLOCK ADVISORY WRITE <pid> MAJ:MIN:INO <start> <end>
    # Split into NAMED fields rather than positional `set --`: the intent is
    # readable, and shellcheck does not have to be told that the word-splitting
    # is deliberate.
    local _idx _kind _mode _rw range
    read -r _idx _kind _mode _rw pid range _ <<<"$line"
    case "$range" in *:*:"$inode") : ;; *) continue ;; esac
    # Our own process tree holds nothing here and would self-match through any
    # probe we run; excluding it is what stops this reporting itself.
    [ "$pid" = "$$" ] && continue
    [ "$pid" = "$PPID" ] && continue
    named=1
    cwd=$(readlink "/proc/$pid/cwd" 2>/dev/null || true)
    if [ -z "$cwd" ]; then
      # Unreadable cwd: another user's process. Neither lane nor stray.
      echo "  pid $pid holds the gate — UNATTRIBUTED (cwd unreadable; likely another user)"
      ps -o pid=,stat=,args= -p "$pid" 2>/dev/null || true
    elif [ "$cwd" != "$FLN_GATE_REPO_ROOT" ]; then
      # A different checkout on this host. `scripts/check.sh` is not a unique
      # name on a machine hosting a dozen FrankenSuite repositories, so argv
      # alone would score this a lane and freeze a pane for nothing.
      echo "  pid $pid holds the gate from a FOREIGN checkout ($cwd) — not our lane"
      ps -o pid=,stat=,args= -p "$pid" 2>/dev/null || true
    else
      echo "  pid $pid holds the gate, cwd=$cwd"
      ps -o pid=,stat=,args= -p "$pid" 2>/dev/null || true
    fi
  done < /proc/locks
  [ "$named" = 1 ] || echo "  (no holder could be named — treat as INDETERMINATE, not as free)"
}

# Append-only, and OUTSIDE the repository on purpose: a write inside it would trip M1-M5 and kill
# the very lane this is protecting. A released flock leaves the lockfile at 0 bytes, so anything
# not recorded live is unrecoverable — which is why this is a separate file and not a field the
# run reports about itself.
fln_gate_journal() {
  printf '{"schema":"fln.gate-lock/1","event":"%s","scenario":"%s","pid":%d,"ppid":%d,"utc":"%s","argv0":"%s"}\n' \
    "$1" "$2" "$$" "$PPID" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$0" >>"$FLN_GATE_JOURNAL"
}

# Usage: fln_gate_acquire "<scenario>"   — call once, early, before any governed hashing.
fln_gate_acquire() {
  local scenario="${1:-unknown}"
  command -v flock >/dev/null 2>&1 || {
    echo "[gate] setup failure: flock is required to take the build gate" >&2
    exit 2
  }
  if fln_gate_inherited; then
    fln_gate_confirm_inherited
    case "$?" in
      0)
        FLN_GATE_STATE=inherited
        fln_gate_journal acquired-inherited "$scenario"
        return 0
        ;;
      1)
        # The descriptor was open but unlocked. We hold the real gate now, on fd 9.
        FLN_GATE_STATE=acquired
        fln_gate_journal acquired-after-unlocked-fd "$scenario"
        return 0
        ;;
      *)
        echo "[gate] setup failure: cannot open $FLN_GATE_LOCKFILE" >&2
        exit 2
        ;;
    esac
  fi
  exec 9>>"$FLN_GATE_LOCKFILE" || {
    echo "[gate] setup failure: cannot open $FLN_GATE_LOCKFILE" >&2
    exit 2
  }
  if ! flock -w "$FLN_GATE_WAIT_S" 9; then
    # Contention is NOT a finding about the code. FL-INV-07: typed inconclusive, never a stage
    # failure. 3 is check.sh's own inconclusive code and every lane's governed-input-changed code.
    echo "[gate] inconclusive: the build gate was not obtained within ${FLN_GATE_WAIT_S}s; held by:" >&2
    fln_gate_name_holder >&2
    exit 3
  fi
  FLN_GATE_STATE=acquired
  fln_gate_journal acquired "$scenario"
}

# Call from the EXIT finalizer; the kernel does the actual release when the fd closes.
fln_gate_release_note() {
  [ "$FLN_GATE_STATE" = "unset" ] || fln_gate_journal "released-$FLN_GATE_STATE" "${1:-unknown}"
}
