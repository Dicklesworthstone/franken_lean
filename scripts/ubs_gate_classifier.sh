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
# A second defect became observable when this wrapper first reached the real four-file gate:
# UBS's meta-runner launched its Python and Rust modules concurrently. Rust completed, while
# Python stopped partway through its category walk; the meta-runner still emitted a four-file,
# zero-critical Combined Summary and exited 1. The classifier correctly refused that terminal,
# but merely retrying the same concurrent orchestration could never establish an attributable
# green. This wrapper now dispatches each supported language in its own UBS invocation, in a
# fixed order, and aggregates only completed module answers. `--jobs=1` is not a substitute:
# UBS passes that hint to child scanners but still backgrounds the language modules themselves.
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
    # Backticks name the literal registered command surface in this diagnostic.
    # shellcheck disable=SC2016
    say 'This script is invoked as the target of `evidence.py exec-ubs-inventory`, which appends'
    say 'the validated inventory paths to argv. An empty argv means the inventory was empty or'
    say 'the wiring changed; either way nothing was scanned and no verdict may be rendered.'
    exit 2
fi

# The Python module's measured two-file run takes about sixteen minutes on this host. UBS's
# meta-runner default is 300 seconds, while check.sh's outer stage authority is 1,200 seconds.
# Give one language 1,080 seconds by default: enough for the measured scan, still strictly
# inside the outer supervisor so a wedged child is typed here before the whole stage is killed.
module_timeout_seconds=${FLN_UBS_MODULE_TIMEOUT_SECONDS:-${UBS_MODULE_TIMEOUT:-1080}}
case "$module_timeout_seconds" in
    ''|*[!0-9]*|0)
        say "REFUSED - UBS module timeout must be a positive integer, got: $module_timeout_seconds"
        exit 2
        ;;
esac

declare -a python_paths=()
declare -a rust_paths=()
declare -a toml_paths=()
for input_path in "$@"; do
    case "$input_path" in
        *.py) python_paths+=("$input_path") ;;
        *.rs) rust_paths+=("$input_path") ;;
        *.toml) toml_paths+=("$input_path") ;;
        *)
            say "REFUSED - input path has no governed UBS inventory suffix: $input_path"
            say 'The registered inventory admits only .py, .rs, and .toml paths. Accepting any'
            say 'other suffix here would make the wrapper and its input authority disagree.'
            exit 2
            ;;
    esac
done

expected_supported=$((${#python_paths[@]} + ${#rust_paths[@]}))
unsupported_count=${#toml_paths[@]}
if [ "$expected_supported" -eq 0 ]; then
    # `.toml` is intentionally in the project-authored change inventory but UBS v5.3.7 has no
    # TOML scanner. This is a recorded non-pass, not a synthetic clean invocation.
    printf 'ubs-gate-classification: class=not_applicable_no_supported_inputs ubs_exits=none gate_exit=0 expected_supported=0 accounted_supported=0 unsupported=%s files=0 critical=0 warning=0 info=0\n' \
        "$unsupported_count"
    say 'not_applicable_no_supported_inputs - NOT A PASS - zero scanner coverage; use the applicable validators for these inputs'
    exit 0
fi

WORK=$(mktemp -d "${TMPDIR:-/tmp}/ubs-gate.XXXXXXXX") || {
    say 'REFUSED - could not create a capture directory; the terminal text cannot be read.'
    exit 2
}

total_files=0
total_critical=0
total_warning=0
total_info=0
accounted_supported=0
exit_vector=''
timeout_seen=no
no_scanner_seen=no
inconclusive_seen=no
findings_seen=no

scan_language() {
    local language=$1
    shift
    local expected=$#
    local out="$WORK/$language.out"
    local err="$WORK/$language.err"
    local ubs_exit
    local summary=''
    local files=''
    local critical=''
    local warning=''
    local info=''
    local timed_out=no
    local no_scanner=no
    local scanner_identified=no
    local module_class=''
    local module_detail=''

    say "dispatching $language scanner over $expected governed input(s)"
    UBS_MODULE_TIMEOUT="$module_timeout_seconds" \
        ubs --only="$language" --ci "$@" > "$out" 2> "$err"
    ubs_exit=$?

    # Each child's bytes are passed through unmodified. With more than one language the stage
    # artifact is their fixed-order concatenation, followed by the wrapper's module and aggregate
    # records; it is intentionally no longer represented as one concurrent meta-runner answer.
    cat "$out"
    cat "$err" >&2

    # ---- terminal facts, each read from this module's capture FILE -----------------------
    # The LAST Combined Summary block is authoritative within one language invocation.
    if grep -q 'Combined Summary' "$out"; then
        summary=$(sed -n '/Combined Summary/,$p' "$out" | tail -20)
        files=$(printf '%s\n' "$summary" | sed -n 's/^Files:[[:space:]]*\([0-9][0-9]*\).*/\1/p' | tail -1)
        critical=$(printf '%s\n' "$summary" | sed -n 's/^Critical:[[:space:]]*\([0-9][0-9]*\).*/\1/p' | tail -1)
        warning=$(printf '%s\n' "$summary" | sed -n 's/^Warning:[[:space:]]*\([0-9][0-9]*\).*/\1/p' | tail -1)
        info=$(printf '%s\n' "$summary" | sed -n 's/^Info:[[:space:]]*\([0-9][0-9]*\).*/\1/p' | tail -1)
    fi
    if grep -q "^Detected: $language\$" "$out"; then
        scanner_identified=yes
    fi
    if grep -q 'MODULE_TIMEOUT' "$out" || grep -q 'MODULE_TIMEOUT' "$err"; then
        timed_out=yes
    fi
    if grep -q 'no supported languages detected' "$out" \
        || grep -q 'nothing was checked (this is NOT a pass)' "$out"; then
        no_scanner=yes
    fi

    # Order is load-bearing. A timeout's synthetic `Critical: 1` is not a code finding.
    if [ "$timed_out" = yes ]; then
        module_class=staging_or_scanner_failure
        module_detail='scanner module hit its budget and was terminated'
        timeout_seen=yes
    elif [ "$no_scanner" = yes ]; then
        module_class=no_scanner_executed
        module_detail='supported inputs were supplied but UBS reported no scanner'
        no_scanner_seen=yes
    elif [ -z "$files" ] || [ -z "$critical" ] || [ -z "$warning" ] || [ -z "$info" ]; then
        module_class=inconclusive
        module_detail='no complete parseable Combined Summary'
        inconclusive_seen=yes
    elif [ "$files" -eq 0 ]; then
        module_class=no_scanner_executed
        module_detail="scan accounted for 0 of $expected intended file(s)"
        no_scanner_seen=yes
    elif [ "$files" -ne "$expected" ]; then
        module_class=inconclusive
        module_detail="scan accounted for $files of $expected intended file(s)"
        inconclusive_seen=yes
    elif [ "$scanner_identified" != yes ]; then
        module_class=no_scanner_executed
        module_detail="terminal did not positively identify the requested $language scanner"
        no_scanner_seen=yes
    elif [ "$ubs_exit" -eq 0 ] && [ "$critical" -eq 0 ]; then
        module_class=completed_clean
        module_detail="$files file(s) accounted for, zero blocking findings"
    elif [ "$critical" -gt 0 ]; then
        module_class=completed_findings
        module_detail="$critical critical finding(s) over $files accounted file(s)"
        findings_seen=yes
    elif [ "$ubs_exit" -ne 0 ]; then
        module_class=inconclusive
        module_detail="ubs exited $ubs_exit with complete accounting and Critical: 0"
        inconclusive_seen=yes
    else
        module_class=inconclusive
        module_detail='terminal facts could not be reconciled'
        inconclusive_seen=yes
    fi

    if [ "$module_class" = completed_clean ] || [ "$module_class" = completed_findings ]; then
        accounted_supported=$((accounted_supported + files))
        total_files=$((total_files + files))
        total_critical=$((total_critical + critical))
        total_warning=$((total_warning + warning))
        total_info=$((total_info + info))
    fi
    if [ -n "$exit_vector" ]; then
        exit_vector="$exit_vector,"
    fi
    exit_vector="${exit_vector}${language}:${ubs_exit}"
    printf 'ubs-gate-module: language=%s class=%s ubs_exit=%s timeout_seconds=%s expected=%s files=%s critical=%s warning=%s info=%s\n' \
        "$language" "$module_class" "$ubs_exit" "$module_timeout_seconds" "$expected" "${files:-unknown}" \
        "${critical:-unknown}" "${warning:-unknown}" "${info:-unknown}"
    say "$language: $module_class - $module_detail"
}

# Fixed source order is itself part of the evidence: there is never more than one live UBS
# language module, independent of UBS's internal backgrounding policy.
if [ "${#python_paths[@]}" -gt 0 ]; then
    scan_language python "${python_paths[@]}"
fi
if [ "${#rust_paths[@]}" -gt 0 ]; then
    scan_language rust "${rust_paths[@]}"
fi

class=''
gate_exit=''
detail=''
if [ "$timeout_seen" = yes ]; then
    class=staging_or_scanner_failure
    gate_exit=2
    detail='at least one scanner module timed out; the aggregate is partial'
elif [ "$no_scanner_seen" = yes ]; then
    class=no_scanner_executed
    gate_exit=2
    detail='at least one intended scanner did not positively account for its inputs'
elif [ "$inconclusive_seen" = yes ]; then
    class=inconclusive
    gate_exit=2
    detail='at least one module returned an unmodelled or contradictory terminal'
elif [ "$findings_seen" = yes ]; then
    class=completed_findings
    gate_exit=1
    detail="$total_critical critical finding(s) over $accounted_supported accounted supported input(s)"
elif [ "$accounted_supported" -eq "$expected_supported" ]; then
    class=completed_clean
    gate_exit=0
    detail="$accounted_supported supported input(s) accounted for, zero blocking findings"
else
    class=inconclusive
    gate_exit=2
    detail="aggregate accounted for $accounted_supported of $expected_supported supported input(s)"
fi

# The machine-readable aggregate is emitted for every terminal class. `unsupported` counts
# governed .toml inputs, which remain outside UBS rather than being silently folded into Files.
printf 'ubs-gate-classification: class=%s ubs_exits=%s gate_exit=%s expected_supported=%s accounted_supported=%s unsupported=%s files=%s critical=%s warning=%s info=%s\n' \
    "$class" "$exit_vector" "$gate_exit" "$expected_supported" "$accounted_supported" \
    "$unsupported_count" "$total_files" "$total_critical" "$total_warning" "$total_info"
say "$class - $detail"
if [ "$gate_exit" -eq 2 ]; then
    say 'FL-INV-07: this is a NON-ANSWER, not a finding about the code. The gate types it'
    say 'internal_fault. Do not diagnose the repository from it, and do not retry until a run'
    say 'happens to succeed - that is how an unattributed green gets adopted.'
fi

# The per-language capture files are deliberately retained. AGENTS.md forbids deleting even
# files created by this process without explicit user permission; the authoritative gate also
# retains the byte-identical child streams in its own stage artifacts.
exit "$gate_exit"
