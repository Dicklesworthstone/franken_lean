#!/usr/bin/env bash
# Harness for scripts/ubs_gate_classifier.sh (bead fln-ubs-timeout-promoted-to-rejection-pekl).
#
# THE CONTROL THAT MATTERS IS THE SECOND ONE. A classifier that made the timeout stop blocking
# by making EVERYTHING stop blocking would pass every timeout cell here and be a catastrophe:
# it would silence every real critical finding, and nothing else in the gate would notice. That
# is the shape of gutting a judge. So every cell that proves a non-answer is typed 2 is paired
# with a cell proving a genuine finding is still typed 1.
#
# THE STUB IS THE APPARATUS AND IT IS CONTROLLED. Cells drive a fake `ubs` on PATH emitting
# terminal text COPIED FROM REAL RUNS (UBS v5.3.7), because reproducing a genuine 300 s module
# timeout per cell is not affordable and a hand-invented terminal shape would test the stub
# rather than UBS. The stub's fidelity is therefore itself asserted: the final cell runs the
# REAL ubs binary against a file with a real critical and requires the same class the stub cell
# claims. Without that, every result here is a statement about a fixture.
set -uo pipefail

CLASSIFIER=${1:?usage: test_ubs_gate_classifier.sh /path/to/ubs_gate_classifier.sh}
PASSES=0
FAILS=0
LAB=$(mktemp -d "${TMPDIR:-/tmp}/ubs-gate-lab.XXXXXXXX")
STUB_INDEX=0
STUB_BIN=''

note() { printf '  %s\n' "$1"; }

# stub_ubs <exit> <stdout-file> [stderr-file]
stub_ubs() {
    local rc=$1 out=$2 err=${3:-/dev/null}
    STUB_INDEX=$((STUB_INDEX + 1))
    STUB_BIN="$LAB/bin-$STUB_INDEX"
    mkdir "$STUB_BIN"
    {
        printf '#!/usr/bin/env bash\n'
        printf 'cat %q\n' "$out"
        printf 'cat %q >&2\n' "$err"
        printf 'exit %s\n' "$rc"
    } > "$STUB_BIN/ubs"
    chmod +x "$STUB_BIN/ubs"
}

# stub_ubs_by_language <python-exit> <python-stdout> <rust-exit> <rust-stdout>
# One stub varies by the wrapper's explicit --only argument, so a mixed-input cell proves both
# dispatches occurred and that their independently completed answers were aggregated.
stub_ubs_by_language() {
    local python_rc=$1 python_out=$2 rust_rc=$3 rust_out=$4
    STUB_INDEX=$((STUB_INDEX + 1))
    STUB_BIN="$LAB/bin-$STUB_INDEX"
    mkdir "$STUB_BIN"
    {
        printf '#!/usr/bin/env bash\n'
        printf 'case " $* " in\n'
        printf '  *" --only=python "*) cat %q; exit %s ;;\n' "$python_out" "$python_rc"
        printf '  *" --only=rust "*) cat %q; exit %s ;;\n' "$rust_out" "$rust_rc"
        printf '  *) printf "unexpected UBS fixture argv: %%s\\n" "$*" >&2; exit 99 ;;\n'
        printf 'esac\n'
    } > "$STUB_BIN/ubs"
    chmod +x "$STUB_BIN/ubs"
}

# check <name> <want_exit> <want_class> <got_exit> <got_text>
check() {
    local name=$1 want_exit=$2 want_class=$3 got_exit=$4 got_text=$5
    if [ "$got_exit" != "$want_exit" ]; then
        printf 'FAIL %s: wanted gate exit %s, got %s\n%s\n' "$name" "$want_exit" "$got_exit" "$got_text"
        FAILS=$((FAILS + 1))
        return
    fi
    if ! printf '%s' "$got_text" | grep -qF "class=$want_class"; then
        printf 'FAIL %s: exit %s correct but class was not %s\n%s\n' \
            "$name" "$want_exit" "$want_class" "$got_text"
        FAILS=$((FAILS + 1))
        return
    fi
    printf 'ok   %s (exit %s, class=%s)\n' "$name" "$got_exit" "$want_class"
    PASSES=$((PASSES + 1))
}

run_cell() { # emits: exit code on line 1 via global CELL_RC, text via CELL_TEXT
    CELL_TEXT=$(PATH="$STUB_BIN:$PATH" bash "$CLASSIFIER" "$@" 2>&1)
    CELL_RC=$?
}

# ---- terminal fixtures, copied from real UBS v5.3.7 runs -----------------------------------
cat > "$LAB/clean.out" <<'EOF'
UBS Meta-Runner v5.3.7
Detected: rust
──────── Combined Summary ────────
Files: 1
Critical: 0
Warning: 0
Info: 2
EOF

cat > "$LAB/findings.out" <<'EOF'
UBS Meta-Runner v5.3.7
Detected: rust
Priority Actions:
  FIX CRITICAL ISSUES IMMEDIATELY
──────── Combined Summary ────────
Files: 1
Critical: 1
Warning: 3
Info: 2
EOF

cat > "$LAB/python-clean.out" <<'EOF'
UBS Meta-Runner v5.3.7
Detected: python
──────── Combined Summary ────────
Files: 1
Critical: 0
Warning: 2
Info: 3
EOF

# Verbatim from target/check/check-20260727T055459Z-3616684/ubs.out, the run this bead is about.
cat > "$LAB/timeout.out" <<'EOF'
UBS Meta-Runner v5.3.7
Detected: python

──────── python ────────
MODULE_TIMEOUT: python
  Scanner module 'python' timed out after 300s (UBS_MODULE_TIMEOUT) and was terminated; the scan continued with a bounded partial result.
Critical issues: 1

──────── Combined Summary ────────
Files: 0
Critical: 1
Warning: 0
Info: 0
EOF
cat > "$LAB/timeout.err" <<'EOF'
Scanning python...
✗ Module 'python' timed out after 300s (MODULE_TIMEOUT); partial result recorded.
Finished python (300s)
EOF

cat > "$LAB/nolang.out" <<'EOF'
UBS Meta-Runner v5.3.7
Format:  text
⚠ no supported languages detected in /somewhere
UBS did not run any scanner: nothing was checked (this is NOT a pass).
Supported languages: js python cpp rust golang java ruby swift csharp elixir
EOF

cat > "$LAB/garbage.out" <<'EOF'
UBS Meta-Runner v5.3.7
something entirely unexpected happened and there is no summary block
EOF

cat > "$LAB/zerofiles.out" <<'EOF'
UBS Meta-Runner v5.3.7
Detected: rust
──────── Combined Summary ────────
Files: 0
Critical: 0
Warning: 0
Info: 0
EOF

cat > "$LAB/wrong-count.out" <<'EOF'
UBS Meta-Runner v5.3.7
Detected: rust
──────── Combined Summary ────────
Files: 2
Critical: 0
Warning: 0
Info: 0
EOF

cat > "$LAB/unidentified-clean.out" <<'EOF'
UBS Meta-Runner v5.3.7
──────── Combined Summary ────────
Files: 1
Critical: 0
Warning: 0
Info: 0
EOF

touch "$LAB/subject.py"
touch "$LAB/subject.rs"
touch "$LAB/subject.toml"

printf 'UBS gate classifier — %s\n' "$CLASSIFIER"

# ---- 1. THE DEFECT ITSELF: a module timeout must NOT be a rejection -----------------------
stub_ubs 1 "$LAB/timeout.out" "$LAB/timeout.err"
run_cell "$LAB/subject.py"
check 'a MODULE_TIMEOUT exiting 1 is a NON-ANSWER, not a rejection' \
    2 staging_or_scanner_failure "$CELL_RC" "$CELL_TEXT"

# ---- 2. THE PAIRED CONTROL, and the reason this harness is trustworthy ---------------------
# Identical exit code, identical invocation, different terminal text. If cell 1 passes and this
# one fails, the repair silenced real findings.
stub_ubs 1 "$LAB/findings.out"
run_cell "$LAB/subject.rs"
check 'a GENUINE critical finding exiting 1 is still a rejection' \
    1 completed_findings "$CELL_RC" "$CELL_TEXT"

# ---- 3. a clean scan still passes ----------------------------------------------------------
stub_ubs 0 "$LAB/clean.out"
run_cell "$LAB/subject.rs"
check 'a clean scan accounting for its files passes' \
    0 completed_clean "$CELL_RC" "$CELL_TEXT"

# ---- 4. R2: zero files accounted for may not yield a verdict of ANY polarity ----------------
stub_ubs 0 "$LAB/zerofiles.out"
run_cell "$LAB/subject.rs"
check 'a scan accounting for ZERO files is a non-answer even exiting 0' \
    2 no_scanner_executed "$CELL_RC" "$CELL_TEXT"

# ---- 5. positive but inexact file accounting is refused --------------------------------------
stub_ubs 0 "$LAB/wrong-count.out"
run_cell "$LAB/subject.rs"
check 'a scanner count that does not equal the intended file set is inconclusive' \
    2 inconclusive "$CELL_RC" "$CELL_TEXT"

# ---- 6. a summary without positive scanner identity is vacuous -------------------------------
stub_ubs 0 "$LAB/unidentified-clean.out"
run_cell "$LAB/subject.rs"
check 'a clean-looking summary without the requested scanner identity is a non-answer' \
    2 no_scanner_executed "$CELL_RC" "$CELL_TEXT"

# ---- 7. an unparseable terminal is refused, never guessed -----------------------------------
stub_ubs 0 "$LAB/garbage.out"
run_cell "$LAB/subject.rs"
check 'an unparseable terminal is inconclusive, not a pass' \
    2 inconclusive "$CELL_RC" "$CELL_TEXT"

# ---- 8. unsupported-only not_applicable is recorded and does NOT block -----------------------
run_cell "$LAB/subject.toml"
check 'no supported inputs is recorded as a non-pass and does not block' \
    0 not_applicable_no_supported_inputs "$CELL_RC" "$CELL_TEXT"

# ---- 9. unsupported siblings do not disappear from a completed supported scan ----------------
stub_ubs 0 "$LAB/clean.out"
run_cell "$LAB/subject.rs" "$LAB/subject.toml"
check 'a supported scan may complete while separately recording unsupported inputs' \
    0 completed_clean "$CELL_RC" "$CELL_TEXT"
if printf '%s' "$CELL_TEXT" | grep -qF 'unsupported=1'; then
    printf 'ok   a mixed supported/unsupported inventory discloses its zero-coverage member\n'
    PASSES=$((PASSES + 1))
else
    printf 'FAIL mixed supported/unsupported classification hid the unsupported member\n%s\n' "$CELL_TEXT"
    FAILS=$((FAILS + 1))
fi

# ---- 10. a supported input with no scanner is blocking, even when UBS exits zero --------------
stub_ubs 0 "$LAB/nolang.out"
run_cell "$LAB/subject.rs"
check 'a supported input whose scanner did not run is a blocking non-answer' \
    2 no_scanner_executed "$CELL_RC" "$CELL_TEXT"

# ---- 11. empty argv is refused: nothing scanned means no verdict -----------------------------
stub_ubs 0 "$LAB/clean.out"
CELL_TEXT=$(PATH="$STUB_BIN:$PATH" bash "$CLASSIFIER" 2>&1); CELL_RC=$?
if [ "$CELL_RC" -eq 2 ]; then
    printf 'ok   an empty input set is refused rather than passed (exit 2)\n'
    PASSES=$((PASSES + 1))
else
    printf 'FAIL an empty input set returned %s, expected 2\n%s\n' "$CELL_RC" "$CELL_TEXT"
    FAILS=$((FAILS + 1))
fi

# ---- 12. an invalid scanner budget is refused rather than silently replaced -------------------
CELL_TEXT=$(FLN_UBS_MODULE_TIMEOUT_SECONDS=unbounded PATH="$STUB_BIN:$PATH" \
    bash "$CLASSIFIER" "$LAB/subject.rs" 2>&1)
CELL_RC=$?
if [ "$CELL_RC" -eq 2 ] && printf '%s' "$CELL_TEXT" | grep -qF 'timeout must be a positive integer'; then
    printf 'ok   an invalid UBS module budget is refused rather than silently defaulted\n'
    PASSES=$((PASSES + 1))
else
    printf 'FAIL invalid UBS module budget returned an untyped or permissive result\n%s\n' "$CELL_TEXT"
    FAILS=$((FAILS + 1))
fi

# ---- 13. the child's own output must survive the wrapper -------------------------------------
# A classifier that swallowed UBS's text would destroy the stage's evidence while still
# returning the right code, and every cell above would still pass.
stub_ubs 1 "$LAB/findings.out"
run_cell "$LAB/subject.rs"
if printf '%s' "$CELL_TEXT" | grep -qF 'FIX CRITICAL ISSUES IMMEDIATELY'; then
    printf 'ok   the wrapper passes UBS output through rather than eating it\n'
    PASSES=$((PASSES + 1))
else
    printf 'FAIL the wrapper did not reproduce UBS output; stage evidence would be lost\n%s\n' "$CELL_TEXT"
    FAILS=$((FAILS + 1))
fi

# ---- 14. mixed languages are dispatched separately and aggregated in fixed order -------------
stub_ubs_by_language 0 "$LAB/python-clean.out" 1 "$LAB/findings.out"
run_cell "$LAB/subject.py" "$LAB/subject.rs"
check 'separate Python clean and Rust finding answers aggregate to a rejection' \
    1 completed_findings "$CELL_RC" "$CELL_TEXT"
if printf '%s' "$CELL_TEXT" | grep -qF 'ubs_exits=python:0,rust:1'; then
    printf 'ok   mixed-language dispatch records the fixed Python-then-Rust exit vector\n'
    PASSES=$((PASSES + 1))
else
    printf 'FAIL mixed-language dispatch did not record both modules in fixed order\n%s\n' "$CELL_TEXT"
    FAILS=$((FAILS + 1))
fi

# ---- 15. one incomplete language keeps the aggregate non-answer -------------------------------
# The Rust cell must still run after Python's malformed terminal; the exit vector proves the
# wrapper collected all available evidence without promoting the clean half to a global pass.
stub_ubs_by_language 1 "$LAB/garbage.out" 0 "$LAB/clean.out"
run_cell "$LAB/subject.py" "$LAB/subject.rs"
check 'one incomplete module dominates another module cleanly completing' \
    2 inconclusive "$CELL_RC" "$CELL_TEXT"
if printf '%s' "$CELL_TEXT" | grep -qF 'ubs_exits=python:1,rust:0'; then
    printf 'ok   dispatch continues after a module non-answer without hiding the partial result\n'
    PASSES=$((PASSES + 1))
else
    printf 'FAIL dispatch stopped early or lost the partial module exit vector\n%s\n' "$CELL_TEXT"
    FAILS=$((FAILS + 1))
fi

# ---- 16. THE STUB'S OWN FIDELITY, against the real binary ------------------------------------
# Everything above is a statement about fixtures unless the real tool agrees. This cell is
# skipped LOUDLY rather than silently when ubs is absent, because a silent skip here would leave
# the suite green while the only non-fixture cell never ran.
if command -v ubs >/dev/null 2>&1; then
    real=$LAB/real
    mkdir -p "$real"
    cat > "$real/dirty.rs" <<'RS'
#![forbid(unsafe_code)]
pub fn pick(v: &[u32], i: usize) -> u32 { v[i] }
pub fn parse(s: &str) -> u32 { s.parse().unwrap() }
pub fn check(secret: &str, given: &str) -> bool { secret == given }
RS
    CELL_TEXT=$(cd "$real" && bash "$CLASSIFIER" dirty.rs 2>&1); CELL_RC=$?
    check 'REAL ubs on a real critical finding types as a rejection' \
        1 completed_findings "$CELL_RC" "$CELL_TEXT"
else
    printf 'FAIL cell 16 could not run: ubs is not on PATH, so every cell above is a claim about a fixture\n'
    FAILS=$((FAILS + 1))
fi

printf '\n%s passed, %s failed\n' "$PASSES" "$FAILS"
# LAB and the classifier capture directories are intentionally retained. AGENTS.md forbids
# deleting even process-created files without explicit user permission.
[ "$FAILS" -eq 0 ]
