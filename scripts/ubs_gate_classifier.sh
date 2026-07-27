#!/usr/bin/env bash
# UBS terminal-mode classifier for the check.sh quality gate.
#
# Bead fln-ubs-timeout-promoted-to-rejection-pekl. THE DEFECT THIS EXISTS FOR: the gate typed a
# UBS scanner MODULE_TIMEOUT as a rejection. A 300 s module budget overrun followed by
# termination is resource exhaustion, and FL-INV-07 says resource exhaustion yields a typed
# Inconclusive/InternalFault outcome and is "never rendered as, cached as, or promoted to
# acceptance OR rejection". The run whose terminal record said
#   verdict=fail reason_code=ubs:child_exit_semantic_failure
# declared FL-INV-07 in its own run_start invariant_ids. The lane asserted the invariant it broke.
#
# WHY THE GATE COULD NOT SEE IT, and why the repair lives here rather than in the runner.
# `ubs --ci` exits 1 for BOTH a genuine critical finding and a module timeout. Measured, real
# runs, UBS v5.3.7:
#
#     class                              ubs --ci exit   terminal evidence
#     completed_clean                          0         Combined Summary, Files>0, Critical: 0
#     completed_findings                       1         Combined Summary, Files>0, Critical>0
#     staging_or_scanner_failure (timeout)     1         MODULE_TIMEOUT, Files: 0, Critical: 1
#     not_applicable_no_supported_inputs       0         "no supported languages detected"
#
# So the exit code is a two-to-one projection and the distinguishing fact exists ONLY in the
# terminal message text -- which is exactly what AGENTS.md's UBS section already states: "Its
# exit code is not a verdict." The gate was keyed to the one signal its own doctrine documents
# as insufficient.
#
# WHY NOT REPAIR scripts/evidence.py's classify_terminal INSTEAD. That is the more precise fix
# and it is blocked: `inconclusive` is reachable there only from a supervisor-observed timeout,
# an output-budget exhaustion, or a child signal -- there is NO child-exit path to it. A UBS
# module timeout is caught by UBS, which then exits 1 on its own, so from the supervisor's
# vantage it is an ordinary child exit and the fact never arrives. Reaching `inconclusive`
# therefore requires editing scripts/evidence.py, which stands as a dead pane's uncommitted
# work (bead franken_lean-h4o1) that may not be touched. This script reaches
# InternalFault instead -- the OTHER typed outcome FL-INV-07 names -- with no runner change.
#
# WHAT IT DELIBERATELY DOES NOT DO: it does not drop `ubs` from the gate's semantic-exit set.
# That "one line" repair would send a REAL critical finding to internal_fault, which is bead
# franken_lean-fmt-gate-env-fault-as-finding-u4j7 mirrored -- a code defect reported as an
# environment fault. The repair must DISTINGUISH, never reclassify wholesale.
#
# EXIT CONTRACT, read against run_stage's registration of --semantic-failure-exit 1 for ubs:
#     0  -> pass          completed_clean, and (disclosed below) not_applicable
#     1  -> fail          completed_findings ONLY. The single semantic exit.
#     2  -> internal_fault  every non-answer: scanner failure, timeout, zero-file scan,
#                           unparseable terminal. Outside the semantic set by construction.
#
# NO PIPELINE READS A VERDICT HERE. Every text probe reads a FILE, never `cmd | grep -q` under
# `set -o pipefail`: grep exits on its first match, leaving the writer blocked on a full pipe,
# and pipefail promotes the resulting SIGPIPE to the pipeline's status. That defect shipped in
# this repository's D3 hook and refused correct files 5-100% of the time depending on their size
# and line structure (bead franken_lean-d3-root-attr-no-creation-affordance-sso4, fixed at
# 60b2e176, characterised at 104fe6e5). A classifier that reads verdicts through pipes would
# reproduce it here, in the script whose whole purpose is to not misreport a non-answer.
set -uo pipefail

say() { printf 'ubs-gate: %s\n' "$1" >&2; }

if [ "$#" -eq 0 ]; then
    say 'REFUSED - no input paths were supplied.'
    say 'This script is invoked as the target of `evidence.py exec-ubs-inventory`, which appends'
    say 'the validated inventory paths to argv. An empty argv means the inventory was empty or'
    say 'the wiring changed; either way nothing was scanned and no verdict may be rendered.'
    exit 2
fi

WORK=$(mktemp -d "${TMPDIR:-/tmp}/ubs-gate.XXXXXXXX") || {
    say 'REFUSED - could not create a capture directory; the terminal text cannot be read.'
    exit 2
}
OUT="$WORK/ubs.out"
ERR="$WORK/ubs.err"

ubs --ci "$@" > "$OUT" 2> "$ERR"
ubs_exit=$?

# The child's own output is the stage's evidence: pass it through UNMODIFIED and FIRST, so the
# retained ubs.out/ubs.err artifacts are byte-identical to an unwrapped run and this script can
# never be accused of having eaten the finding it was judging.
cat "$OUT"
cat "$ERR" >&2

# ---- terminal facts, each read from a FILE -----------------------------------------------
# The LAST Combined Summary block is authoritative; UBS prints one per run at the end.
files=''
critical=''
warning=''
info=''
if grep -q 'Combined Summary' "$OUT"; then
    summary=$(sed -n '/Combined Summary/,$p' "$OUT" | tail -20)
    files=$(printf '%s\n' "$summary" | sed -n 's/^Files:[[:space:]]*\([0-9][0-9]*\).*/\1/p' | tail -1)
    critical=$(printf '%s\n' "$summary" | sed -n 's/^Critical:[[:space:]]*\([0-9][0-9]*\).*/\1/p' | tail -1)
    warning=$(printf '%s\n' "$summary" | sed -n 's/^Warning:[[:space:]]*\([0-9][0-9]*\).*/\1/p' | tail -1)
    info=$(printf '%s\n' "$summary" | sed -n 's/^Info:[[:space:]]*\([0-9][0-9]*\).*/\1/p' | tail -1)
fi

timed_out=no
if grep -q 'MODULE_TIMEOUT' "$OUT" || grep -q 'MODULE_TIMEOUT' "$ERR"; then
    timed_out=yes
fi

no_scanner=no
if grep -q 'no supported languages detected' "$OUT" \
    || grep -q 'nothing was checked (this is NOT a pass)' "$OUT"; then
    no_scanner=yes
fi

# ---- classification, most-specific first -------------------------------------------------
# Order matters and is the whole design. A timeout carrying `Critical: 1` must be typed by the
# TIMEOUT, never by the count: that count IS the timeout notice, one critical recorded over zero
# files scanned. Reading the count first is precisely how this defect was rendered as a
# rejection in the first place.
class=''
gate_exit=''
detail=''

if [ "$timed_out" = yes ]; then
    class=staging_or_scanner_failure
    gate_exit=2
    detail='a scanner module hit its budget and was terminated; the scan is partial'
elif [ "$no_scanner" = yes ]; then
    # AGENTS.md: "supplies no scanner evidence and is never called a pass, but it does not block
    # an unsupported-only documentation/JSONL commit". run_stage's vocabulary has no outcome for
    # "recorded non-pass that does not block", so the class is RECORDED here and not promoted to
    # a blocking type. Typing it internal_fault would wall a correct .toml-only change, since the
    # UBS inventory admits .toml while UBS supports no such scanner. Disclosed, not silent.
    class=not_applicable_no_supported_inputs
    gate_exit=0
    detail='NOT A PASS - zero scanner coverage; use the applicable validators for these inputs'
elif [ -z "$files" ] || [ -z "$critical" ]; then
    class=inconclusive
    gate_exit=2
    detail='no parseable Combined Summary; the terminal shape is not the one this gate reads'
elif [ "$files" -eq 0 ]; then
    # Bead R2, and it is independent of the timeout branch above: a scan accounting for ZERO
    # files may never produce a terminal verdict of any polarity, whatever it reports finding.
    class=no_scanner_executed
    gate_exit=2
    detail="scan accounted for 0 files while reporting Critical: $critical - a count with no referent"
elif [ "$ubs_exit" -eq 0 ] && [ "$critical" -eq 0 ]; then
    class=completed_clean
    gate_exit=0
    detail="$files file(s) accounted for, zero blocking findings"
elif [ "$critical" -gt 0 ]; then
    class=completed_findings
    gate_exit=1
    detail="$critical critical finding(s) over $files file(s) - a real verdict about the code"
elif [ "$ubs_exit" -ne 0 ]; then
    # Nonzero with a complete accounting and no criticals: --fail-on-warning, or a mode this
    # gate has not measured. Refuse rather than guess a polarity in either direction.
    class=inconclusive
    gate_exit=2
    detail="ubs exited $ubs_exit over $files file(s) with Critical: 0 - unmodelled terminal"
else
    class=inconclusive
    gate_exit=2
    detail='terminal facts could not be reconciled'
fi

# The machine-readable record. It is emitted for EVERY class including the passing ones, so a
# not_applicable run leaves positive evidence of its own zero coverage in the stage artifacts
# rather than being indistinguishable from a clean scan.
printf 'ubs-gate-classification: class=%s ubs_exit=%s gate_exit=%s files=%s critical=%s warning=%s info=%s\n' \
    "$class" "$ubs_exit" "$gate_exit" "${files:-unknown}" "${critical:-unknown}" \
    "${warning:-unknown}" "${info:-unknown}"
say "$class - $detail"
if [ "$gate_exit" -eq 2 ]; then
    say 'FL-INV-07: this is a NON-ANSWER, not a finding about the code. The gate types it'
    say 'internal_fault. Do not diagnose the repository from it, and do not retry until a run'
    say 'happens to succeed - that is how an unattributed green gets adopted.'
fi

# Non-recursive on purpose. This repository forbids unattended recursive deletion, and the two
# files below are the only ones this script created; if anything else is in there, `rmdir` fails
# harmlessly and the directory is left for a human rather than removed by a guess.
rm -f "$OUT" "$ERR"
rmdir "$WORK" 2>/dev/null || true
exit "$gate_exit"
