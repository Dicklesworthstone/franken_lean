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
trap 'rm -rf "$LAB"' EXIT

note() { printf '  %s\n' "$1"; }

# stub_ubs <exit> <stdout-file> [stderr-file]
stub_ubs() {
    local rc=$1 out=$2 err=${3:-/dev/null}
    mkdir -p "$LAB/bin"
    {
        printf '#!/usr/bin/env bash\n'
        printf 'cat %q\n' "$out"
        printf 'cat %q >&2\n' "$err"
        printf 'exit %s\n' "$rc"
    } > "$LAB/bin/ubs"
    chmod +x "$LAB/bin/ubs"
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
    CELL_TEXT=$(PATH="$LAB/bin:$PATH" bash "$CLASSIFIER" "$@" 2>&1)
    CELL_RC=$?
}

# ---- terminal fixtures, copied from real UBS v5.3.7 runs -----------------------------------
cat > "$LAB/clean.out" <<'EOF'
UBS Meta-Runner v5.3.7
──────── Combined Summary ────────
Files: 1
Critical: 0
Warning: 0
Info: 2
EOF

cat > "$LAB/findings.out" <<'EOF'
UBS Meta-Runner v5.3.7
Priority Actions:
  FIX CRITICAL ISSUES IMMEDIATELY
──────── Combined Summary ────────
Files: 1
Critical: 1
Warning: 3
Info: 2
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
──────── Combined Summary ────────
Files: 0
Critical: 0
Warning: 0
Info: 0
EOF

touch "$LAB/subject.rs"

printf 'UBS gate classifier — %s\n' "$CLASSIFIER"

# ---- 1. THE DEFECT ITSELF: a module timeout must NOT be a rejection -----------------------
stub_ubs 1 "$LAB/timeout.out" "$LAB/timeout.err"
run_cell "$LAB/subject.rs"
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

# ---- 5. an unparseable terminal is refused, never guessed -----------------------------------
stub_ubs 0 "$LAB/garbage.out"
run_cell "$LAB/subject.rs"
check 'an unparseable terminal is inconclusive, not a pass' \
    2 inconclusive "$CELL_RC" "$CELL_TEXT"

# ---- 6. not_applicable is recorded and does NOT block ---------------------------------------
stub_ubs 0 "$LAB/nolang.out"
run_cell "$LAB/subject.rs"
check 'no supported inputs is recorded as a non-pass and does not block' \
    0 not_applicable_no_supported_inputs "$CELL_RC" "$CELL_TEXT"

# ---- 7. empty argv is refused: nothing scanned means no verdict ------------------------------
stub_ubs 0 "$LAB/clean.out"
CELL_TEXT=$(PATH="$LAB/bin:$PATH" bash "$CLASSIFIER" 2>&1); CELL_RC=$?
if [ "$CELL_RC" -eq 2 ]; then
    printf 'ok   an empty input set is refused rather than passed (exit 2)\n'
    PASSES=$((PASSES + 1))
else
    printf 'FAIL an empty input set returned %s, expected 2\n%s\n' "$CELL_RC" "$CELL_TEXT"
    FAILS=$((FAILS + 1))
fi

# ---- 8. the child's own output must survive the wrapper --------------------------------------
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

# ---- 9. THE STUB'S OWN FIDELITY, against the real binary -------------------------------------
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
    printf 'FAIL cell 9 could not run: ubs is not on PATH, so every cell above is a claim about a fixture\n'
    FAILS=$((FAILS + 1))
fi

printf '\n%s passed, %s failed\n' "$PASSES" "$FAILS"
[ "$FAILS" -eq 0 ]
