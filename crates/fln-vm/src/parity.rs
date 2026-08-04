//! The G0-3 parity comparator: expected-output fixtures, the declared
//! normalizations, and the verdict Golem's execution is held to (bead
//! `franken_lean-7xe`; plan §22.1-3, feeds §11 and the C4 probe family).
//!
//! The committed fixtures (`fixtures/g03/*.lean` + `*.expected`) pin the
//! Reference's observable outputs, measured byte-deterministic across fresh-cwd
//! double runs. Two normalizations are DECLARED rather than silent, and each
//! `.expected` header records what was applied so the pin is honest about what
//! it excludes:
//!
//! - **cwd**: absolute run-directory prefixes become `<CWD>/` — the run
//!   location is host telemetry.
//! - **panic backtraces**: the `backtrace:` marker line and every frame line
//!   (`.so(` offsets, ` [0x` addresses) are dropped — ASLR addresses are host
//!   telemetry. The SEMANTIC panic surface that remains is the message line
//!   with its source anchor and the Inhabited-default recovery value, which is
//!   exactly the behavior a VM must reproduce.
//!
//! The comparator refuses malformed fixtures typed, reports the earliest
//! diverging line with both sides, and treats an exit-code mismatch as its own
//! divergence class — a VM that prints the right bytes with the wrong exit is
//! not at parity.

use std::fmt;

/// One parsed expected-output fixture.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expected {
    pub exit: i32,
    pub paths_normalized: bool,
    pub backtrace_lines_dropped: u32,
    pub body: String,
}

/// Typed refusal for a malformed `.expected` fixture.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpectedParseError {
    pub reason: String,
}

impl fmt::Display for ExpectedParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "malformed expected fixture: {}", self.reason)
    }
}

impl std::error::Error for ExpectedParseError {}

/// Parse an `.expected` fixture: one `# key=value ...` header line, then the
/// pinned body verbatim.
pub fn parse_expected(text: &str) -> Result<Expected, ExpectedParseError> {
    let refuse = |reason: &str| ExpectedParseError {
        reason: reason.to_string(),
    };
    let Some(rest) = text.strip_prefix("# ") else {
        return Err(refuse("missing '# ' header line"));
    };
    let (header, body) = rest
        .split_once('\n')
        .ok_or_else(|| refuse("header line has no terminator"))?;
    let mut exit = None;
    let mut paths_normalized = None;
    let mut dropped = None;
    for field in header.split_whitespace() {
        let (key, value) = field
            .split_once('=')
            .ok_or_else(|| refuse("header field without '='"))?;
        match key {
            "exit" => {
                exit = Some(
                    value
                        .parse::<i32>()
                        .map_err(|_| refuse("exit is not an integer"))?,
                )
            }
            "paths_normalized" => {
                paths_normalized = Some(match value {
                    "true" => true,
                    "false" => false,
                    _ => return Err(refuse("paths_normalized is not a boolean")),
                })
            }
            "backtrace_lines_dropped" => {
                dropped = Some(
                    value
                        .parse::<u32>()
                        .map_err(|_| refuse("backtrace_lines_dropped is not an integer"))?,
                )
            }
            other => return Err(refuse(&format!("unknown header field {other:?}"))),
        }
    }
    Ok(Expected {
        exit: exit.ok_or_else(|| refuse("header missing exit"))?,
        paths_normalized: paths_normalized
            .ok_or_else(|| refuse("header missing paths_normalized"))?,
        backtrace_lines_dropped: dropped
            .ok_or_else(|| refuse("header missing backtrace_lines_dropped"))?,
        body: body.to_string(),
    })
}

/// Apply the declared normalizations to a raw observed output. Returns the
/// normalized text and how many backtrace lines were dropped, so a comparison
/// can also hold the DROP COUNT to the fixture's declaration.
pub fn normalize(raw: &str, run_dir: &str) -> (String, u32) {
    let mut cwd_prefix = String::from(run_dir);
    if !cwd_prefix.ends_with('/') {
        cwd_prefix.push('/');
    }
    let mut kept = String::with_capacity(raw.len());
    let mut dropped = 0u32;
    for line in raw.split_inclusive('\n') {
        let content = line.trim_end_matches('\n');
        if content.trim() == "backtrace:" || content.contains(".so(") || content.contains(" [0x") {
            dropped += 1;
            continue;
        }
        kept.push_str(&line.replace(&cwd_prefix, "<CWD>/"));
    }
    (kept, dropped)
}

/// The comparator's verdict. `Diverges` carries the earliest differing line
/// with both sides; exit and drop-count mismatches are their own classes so a
/// triage never starts from a diff dump when a scalar already names the story.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParityVerdict {
    Match,
    ExitDiverges {
        expected: i32,
        actual: i32,
    },
    DropCountDiverges {
        declared: u32,
        observed: u32,
    },
    Diverges {
        line: usize,
        expected: String,
        actual: String,
    },
}

/// Hold a raw observation (stdout+stderr, exit) to an expected fixture.
pub fn compare(expected: &Expected, raw_output: &str, exit: i32, run_dir: &str) -> ParityVerdict {
    if exit != expected.exit {
        return ParityVerdict::ExitDiverges {
            expected: expected.exit,
            actual: exit,
        };
    }
    let (normalized, dropped) = normalize(raw_output, run_dir);
    if dropped != expected.backtrace_lines_dropped {
        return ParityVerdict::DropCountDiverges {
            declared: expected.backtrace_lines_dropped,
            observed: dropped,
        };
    }
    if normalized == expected.body {
        return ParityVerdict::Match;
    }
    let mut want = expected.body.lines();
    let mut got = normalized.lines();
    let mut line = 0usize;
    loop {
        line += 1;
        match (want.next(), got.next()) {
            (Some(w), Some(g)) if w == g => continue,
            (w, g) => {
                return ParityVerdict::Diverges {
                    line,
                    expected: w.unwrap_or("<absent>").to_string(),
                    actual: g.unwrap_or("<absent>").to_string(),
                };
            }
        }
    }
}

/// The committed corpus, compiled in so the comparator and its fixtures cannot
/// drift apart across checkouts (the k60n class, closed by construction).
pub const CORPUS: &[(&str, &str, &str)] = &[
    (
        "arrays",
        include_str!("../fixtures/g03/arrays.lean"),
        include_str!("../fixtures/g03/arrays.lean.expected"),
    ),
    (
        "closures",
        include_str!("../fixtures/g03/closures.lean"),
        include_str!("../fixtures/g03/closures.lean.expected"),
    ),
    (
        "io_file",
        include_str!("../fixtures/g03/io_file.lean"),
        include_str!("../fixtures/g03/io_file.lean.expected"),
    ),
    (
        "io_println",
        include_str!("../fixtures/g03/io_println.lean"),
        include_str!("../fixtures/g03/io_println.lean.expected"),
    ),
    (
        "nonterm_guard",
        include_str!("../fixtures/g03/nonterm_guard.lean"),
        include_str!("../fixtures/g03/nonterm_guard.lean.expected"),
    ),
    (
        "nonterm_partial_ok",
        include_str!("../fixtures/g03/nonterm_partial_ok.lean"),
        include_str!("../fixtures/g03/nonterm_partial_ok.lean.expected"),
    ),
    (
        "panics",
        include_str!("../fixtures/g03/panics.lean"),
        include_str!("../fixtures/g03/panics.lean.expected"),
    ),
    (
        "pure_nat",
        include_str!("../fixtures/g03/pure_nat.lean"),
        include_str!("../fixtures/g03/pure_nat.lean.expected"),
    ),
    (
        "strings",
        include_str!("../fixtures/g03/strings.lean"),
        include_str!("../fixtures/g03/strings.lean.expected"),
    ),
    (
        "tasks",
        include_str!("../fixtures/g03/tasks.lean"),
        include_str!("../fixtures/g03/tasks.lean.expected"),
    ),
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_committed_fixture_parses_with_pinned_censuses() {
        assert_eq!(CORPUS.len(), 10, "corpus census");
        let mut refusals = 0;
        let mut nonzero_exit = 0;
        let mut dropped_total = 0;
        for (name, source, expected) in CORPUS {
            assert!(!source.trim().is_empty(), "{name}: empty source");
            let e = parse_expected(expected).unwrap_or_else(|err| panic!("{name}: {err}"));
            if e.exit != 0 {
                nonzero_exit += 1;
            }
            dropped_total += e.backtrace_lines_dropped;
            if e.body.is_empty() {
                refusals += 1;
            }
        }
        assert_eq!(nonzero_exit, 1, "exactly the nonterm_guard refusal exits 1");
        assert_eq!(
            dropped_total, 101,
            "exactly the panic backtrace was dropped"
        );
        assert_eq!(refusals, 0, "every fixture pins a nonempty body");
    }

    #[test]
    fn the_comparator_matches_a_faithful_reproduction_and_names_a_drift() {
        let (_, _, expected_text) = CORPUS
            .iter()
            .find(|(n, _, _)| *n == "io_println")
            .expect("io_println exists");
        let e = parse_expected(expected_text).expect("parses");
        // A faithful reproduction (what Golem must produce) matches.
        assert_eq!(
            compare(&e, &e.body, e.exit, "/nonexistent/run"),
            ParityVerdict::Match
        );
        // A single flipped character is located by line with both sides.
        let drifted = e.body.replacen("second", "SECOND", 1);
        match compare(&e, &drifted, e.exit, "/nonexistent/run") {
            ParityVerdict::Diverges {
                line,
                expected,
                actual,
            } => {
                assert_eq!(line, 2);
                assert!(expected.contains("second") && actual.contains("SECOND"));
            }
            other => panic!("expected a located divergence, got {other:?}"),
        }
        // The wrong exit is its own verdict class, before any diff.
        assert_eq!(
            compare(&e, &e.body, 1, "/nonexistent/run"),
            ParityVerdict::ExitDiverges {
                expected: 0,
                actual: 1
            }
        );
    }

    #[test]
    fn normalization_reproduces_the_declared_panic_split() {
        // A synthetic raw panic blob with the measured shape: the semantic
        // three lines survive, the marker and frames drop, and the drop count
        // is held — so a VM whose panic path prints MORE or FEWER telemetry
        // lines than the Reference is caught by the count even when the
        // semantic lines agree.
        let raw = "42\nPANIC at risky panics:2:16: zero not allowed\nbacktrace:\n\
                   /x/libleanshared.so(+0x93) [0x7a7f]\n\
                   /x/libleanshared.so(lean_panic_fn+0x2b) [0x7a80]\n0\n";
        let (normalized, dropped) = normalize(raw, "/tmp/run");
        assert_eq!(
            normalized,
            "42\nPANIC at risky panics:2:16: zero not allowed\n0\n"
        );
        assert_eq!(dropped, 3);
        let e = Expected {
            exit: 0,
            paths_normalized: false,
            backtrace_lines_dropped: 3,
            body: normalized.clone(),
        };
        assert_eq!(compare(&e, raw, 0, "/tmp/run"), ParityVerdict::Match);
        // One extra frame line: the count catches it.
        let noisier = raw.replace(
            "backtrace:\n",
            "backtrace:\n/x/libleanshared.so(+0x1) [0x1]\n",
        );
        assert_eq!(
            compare(&e, &noisier, 0, "/tmp/run"),
            ParityVerdict::DropCountDiverges {
                declared: 3,
                observed: 4
            }
        );
    }

    #[test]
    fn cwd_normalization_rewrites_the_run_prefix_only() {
        let raw = "error at /tmp/run_xyz/file.lean:1: boom\nunrelated /other/path stays\n";
        let (normalized, dropped) = normalize(raw, "/tmp/run_xyz");
        assert_eq!(dropped, 0);
        assert_eq!(
            normalized,
            "error at <CWD>/file.lean:1: boom\nunrelated /other/path stays\n"
        );
    }

    #[test]
    fn hostile_expected_fixtures_refuse_typed_never_panic() {
        for junk in [
            "",
            "no header at all\nbody",
            "# exit=zero paths_normalized=false backtrace_lines_dropped=0\nx",
            "# exit=0 paths_normalized=maybe backtrace_lines_dropped=0\nx",
            "# exit=0 paths_normalized=false\nx",
            "# exit=0 paths_normalized=false backtrace_lines_dropped=0 mystery=1\nx",
        ] {
            assert!(parse_expected(junk).is_err(), "must refuse: {junk:?}");
        }
    }
}
