#!/usr/bin/env bash
#
# Run one sanitizer-instrumented test and judge it on TWO independent questions,
# because neither answers the other and each has a measured failure mode.
#
# 1. DID A RACE FIRE?  The answer is the EXIT CODE and nothing else. ThreadSanitizer
#    reports at process teardown, AFTER libtest has already printed its verdict.
#    Measured at 7b5dd549 against the real crate with dec_ref's mode probe at
#    rc.rs:167 reverted to a plain non-atomic read:
#
#        test tests::mark_mt_negates_and_atomics_conserve ... ok
#        test result: ok. 1 passed; 0 failed; ...
#
#    and the process exited 66 with two `WARNING: ThreadSanitizer: data race` lines.
#    So a caller that greps `test result: ok` reports clean while two races were
#    detected. This script checks the exit code FIRST, before reading any text.
#
# 2. DID THE TEST ACTUALLY RUN?  The exit code is BLIND to this: a libtest filter
#    matching nothing prints `0 passed; N filtered out` and exits 0. Measured at the
#    same commit — adding `-- --exact` to the short test name yielded exactly that,
#    `0 passed; 39 filtered out`, exit 0. A lane wired that way is a green that runs
#    no test. So a non-zero pass count is required, and this is the one place the
#    output text is read — for ANTI-VACUITY, never for the verdict.
#
# The two must be checked in this order. Reading text first would let a race-failed
# run be reported as a filter problem.
#
# Usage: run_sanitizer_test.sh <label> <command...>

set -uo pipefail

if [ "$#" -lt 2 ]; then
    echo "usage: $0 <label> <command...>" >&2
    exit 2
fi

label="$1"
shift

log="$(mktemp -t sanitizer-XXXXXX.log)"
trap 'rm -f "$log"' EXIT

# Deliberately NOT piped: a pipeline reports the last stage's status, and the exit
# code is the whole verdict here. Output is teed to the log and to the console so a
# CI reader still sees the race text, which prints on stderr above the summary.
set +e
"$@" >"$log" 2>&1
rc=$?
set -e

cat "$log"

# ---- question 1: the verdict. Exit code only, checked before any text is read.
if [ "$rc" -ne 0 ]; then
    echo "sanitizer[$label]: FAIL — process exited $rc." >&2
    echo "sanitizer[$label]: libtest's own line may say 'ok'; the sanitizer reports at" >&2
    echo "sanitizer[$label]: teardown. The exit code is the verdict. Race text is above." >&2
    exit "$rc"
fi

# ---- question 2: anti-vacuity. A pass count of zero is a broken run, not a clean one.
passed="$(sed -n 's/^test result: ok\. \([0-9]*\) passed.*/\1/p' "$log" | head -1)"
if [ -z "$passed" ]; then
    echo "sanitizer[$label]: FAIL — no libtest result line found; the harness did not" >&2
    echo "sanitizer[$label]: report at all. A zero exit here is not evidence of anything." >&2
    exit 1
fi
if [ "$passed" -eq 0 ]; then
    echo "sanitizer[$label]: FAIL — the filter matched NO test (0 passed)." >&2
    echo "sanitizer[$label]: libtest exits 0 when a filter matches nothing, so this would" >&2
    echo "sanitizer[$label]: otherwise be a green lane running no test. Fix the filter." >&2
    exit 1
fi

echo "sanitizer[$label]: OK — exit 0 and $passed test(s) actually ran."
