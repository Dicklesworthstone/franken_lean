//! Ordinary-Lean acceptance probe (bead fln-ordinary-lean-probe-g03u).
//!
//! Thirty ordinary Lean programs as people write them (implicit `Init`, no
//! `prelude`) live in `fixtures/ordinary_lean_probe/`: set A is the 2026-09-27
//! reality-check set, set B the 2026-10-04 one. Its `manifest.tsv` names each
//! program's set and records what the pinned Reference `lean <file>` does when
//! run from that directory: exit code, stdout and stderr.
//!
//! The corpus MEASURES; it does not gate the seed dialect. It is deliberately
//! outside `examples/` and the source ladder, whose freeze
//! (`source_reference_differential.rs`) forbids non-agreeing rows. The test
//! re-runs the pin and FrankenLean's `lean` personality on every program,
//! prints one line per program and the acceptance triple, and never fails on a
//! low score. It fails only when:
//! - FrankenLean's `lean` accepts (exits 0) a program the Reference rejects,
//!   the soundness direction;
//! - the scan is broken: a corpus below the floor, a program without a
//!   manifest row or a row without a program, a malformed row, or a row the
//!   live pin no longer reproduces (the expectations are the pin's own output,
//!   never hand-written);
//! - the pin is absent while `FLN_REQUIRE_REFERENCE` is set.
//!
//! Without the pin it prints a typed SKIP after checking the corpus against
//! its manifest. A program with no verdict within `PROGRAM_TIMEOUT` counts as
//! `timeout`, which is never acceptance (FL-INV-07).
//!
//! Run it with the output visible:
//! `cargo test -p fln-cli --release --test ordinary_lean_probe -- --nocapture`
//!
//! Consumers: operator steering and every reality check. Deletion condition:
//! the corpus-scale source differential (G4's T2 rig) subsumes it.
#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

const CORPUS: &str = "crates/fln-cli/tests/fixtures/ordinary_lean_probe";
const MANIFEST: &str = "manifest.tsv";
/// The declared population: 16 programs in set A and 14 in set B. A scan that
/// finds fewer is broken; it is never a smaller corpus.
const CORPUS_FLOOR: usize = 30;
const WORKERS: usize = 8;
const PROGRAM_TIMEOUT: Duration = Duration::from_secs(120);

/// One manifest row: a program, its set, and the pinned Reference's result.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Row {
    file: String,
    set: String,
    exit: i32,
    stdout: String,
    stderr: String,
}

/// One process run. `exit` is `None` when there was no verdict: a timeout or
/// a signal.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Run {
    exit: Option<i32>,
    stdout: String,
    stderr: String,
}

impl Run {
    fn accepts(&self) -> bool {
        self.exit == Some(0)
    }
}

#[derive(Debug, Clone)]
struct Observed {
    reference: Run,
    frankenlean: Run,
}

#[derive(Debug, Default)]
struct Report {
    lines: Vec<String>,
    problems: Vec<String>,
    programs: usize,
    agree: usize,
    reference_accepts: usize,
    both_accept: usize,
    identical: usize,
    false_accepts: usize,
    /// Per set: (accepted by both, accepted by the Reference).
    per_set: BTreeMap<String, (usize, usize)>,
}

fn reference_lean(root: &Path) -> Result<PathBuf, String> {
    let lock = std::fs::read_to_string(root.join("SUITE.lock"))
        .map_err(|error| format!("cannot read SUITE.lock: {error}"))?;
    let tag = lock
        .lines()
        .map(str::trim)
        .find(|line| line.starts_with("reference "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|word| word.strip_prefix("tag="))
        })
        .ok_or("SUITE.lock has no reference tag")?
        .to_owned();
    let toolchains = match std::env::var_os("ELAN_HOME") {
        Some(elan) => PathBuf::from(elan).join("toolchains"),
        None => std::env::var_os("HOME")
            .map(|home| PathBuf::from(home).join(".elan/toolchains"))
            .ok_or("neither ELAN_HOME nor HOME is set")?,
    };
    let lean = toolchains
        .join(format!("leanprover--lean4---{tag}"))
        .join("bin")
        .join("lean");
    if lean.is_file() {
        Ok(lean)
    } else {
        Err(format!(
            "pinned Reference lean not found at {}",
            lean.display()
        ))
    }
}

fn escape(text: &str) -> String {
    text.replace('\\', "\\\\")
        .replace('\n', "\\n")
        .replace('\t', "\\t")
        .replace('\r', "\\r")
}

fn unescape(field: &str) -> Result<String, String> {
    let mut out = String::new();
    let mut chars = field.chars();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            out.push(ch);
            continue;
        }
        match chars.next() {
            Some('\\') => out.push('\\'),
            Some('n') => out.push('\n'),
            Some('t') => out.push('\t'),
            Some('r') => out.push('\r'),
            other => return Err(format!("unknown escape after a backslash: {other:?}")),
        }
    }
    Ok(out)
}

fn parse_manifest(text: &str) -> Result<Vec<Row>, Vec<String>> {
    let mut rows = Vec::new();
    let mut problems = Vec::new();
    for (index, line) in text.lines().enumerate() {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let at = format!("{MANIFEST}:{}", index + 1);
        let fields: Vec<&str> = line.split('\t').collect();
        if fields.len() != 5 {
            problems.push(format!(
                "{at}: expected 5 tab-separated fields, found {}",
                fields.len()
            ));
            continue;
        }
        if !matches!(fields[1], "A" | "B") {
            problems.push(format!("{at}: set must be A or B, found {:?}", fields[1]));
        }
        let parsed = (
            fields[2].parse::<i32>().map_err(|error| error.to_string()),
            unescape(fields[3]),
            unescape(fields[4]),
        );
        match parsed {
            (Ok(exit), Ok(stdout), Ok(stderr)) => rows.push(Row {
                file: fields[0].to_owned(),
                set: fields[1].to_owned(),
                exit,
                stdout,
                stderr,
            }),
            (exit, stdout, stderr) => {
                for error in [exit.err(), stdout.err(), stderr.err()]
                    .into_iter()
                    .flatten()
                {
                    problems.push(format!("{at}: {error}"));
                }
            }
        }
    }
    if problems.is_empty() {
        Ok(rows)
    } else {
        Err(problems)
    }
}

/// A broken scan is refused, never scored: the corpus directory and the
/// manifest must name the same programs, and at least `CORPUS_FLOOR` of them.
fn scan_problems(files: &[String], rows: &[Row]) -> Vec<String> {
    let mut problems = Vec::new();
    let on_disk: BTreeSet<&str> = files.iter().map(String::as_str).collect();
    let mut recorded = BTreeSet::new();
    for row in rows {
        if !recorded.insert(row.file.as_str()) {
            problems.push(format!("duplicate manifest row for {}", row.file));
        }
        if !on_disk.contains(row.file.as_str()) {
            problems.push(format!(
                "the manifest row for {} names no program in the corpus",
                row.file
            ));
        }
    }
    for file in &on_disk {
        if !recorded.contains(file) {
            problems.push(format!(
                "{file} has no manifest row; record it from the pinned Reference"
            ));
        }
    }
    if on_disk.len() < CORPUS_FLOOR || recorded.len() < CORPUS_FLOOR {
        problems.push(format!(
            "the scan found {} programs and {} manifest rows, below the floor of \
             {CORPUS_FLOOR}; a broken scan is not a smaller corpus",
            on_disk.len(),
            recorded.len()
        ));
    }
    problems
}

/// The programs and manifest rows as checked in, or the broken-scan refusal.
fn load(corpus: &Path) -> (Vec<String>, Vec<Row>) {
    let mut files = Vec::new();
    if let Ok(entries) = std::fs::read_dir(corpus) {
        for entry in entries {
            let path = entry.expect("corpus entry").path();
            if path.extension().and_then(|ext| ext.to_str()) == Some("lean") {
                let name = path.file_name().expect("corpus file name");
                files.push(name.to_string_lossy().into_owned());
            }
        }
    }
    files.sort();
    let text = std::fs::read_to_string(corpus.join(MANIFEST)).unwrap_or_default();
    let (rows, problems) = match parse_manifest(&text) {
        Ok(rows) => {
            let problems = scan_problems(&files, &rows);
            (rows, problems)
        }
        Err(malformed) => (Vec::new(), malformed),
    };
    assert!(
        problems.is_empty(),
        "broken probe scan of {CORPUS}:\n{}",
        problems.join("\n")
    );
    (files, rows)
}

fn first_line(text: &str) -> String {
    text.lines().next().unwrap_or_default().to_owned()
}

fn score(rows: &[Row], observed: &BTreeMap<String, Observed>) -> Report {
    let mut report = Report::default();
    for row in rows {
        let Some(seen) = observed.get(&row.file) else {
            report.problems.push(format!(
                "{}: never observed; the run did not reach it",
                row.file
            ));
            continue;
        };
        report.programs += 1;
        let recorded = Run {
            exit: Some(row.exit),
            stdout: row.stdout.clone(),
            stderr: row.stderr.clone(),
        };
        if seen.reference != recorded {
            let exit = seen
                .reference
                .exit
                .map_or_else(|| "none".to_owned(), |code| code.to_string());
            report.problems.push(format!(
                "{}: the pinned Reference no longer reproduces its manifest row; it produced: \
                 {}\t{}\t{exit}\t{}\t{}",
                row.file,
                row.file,
                row.set,
                escape(&seen.reference.stdout),
                escape(&seen.reference.stderr)
            ));
        }
        let reference_accepts = seen.reference.accepts();
        let frankenlean_accepts = seen.frankenlean.accepts();
        if reference_accepts == frankenlean_accepts {
            report.agree += 1;
        }
        let output = if reference_accepts && frankenlean_accepts {
            if seen.frankenlean.stdout == seen.reference.stdout
                && seen.frankenlean.stderr == seen.reference.stderr
            {
                report.identical += 1;
                "identical"
            } else {
                "differ"
            }
        } else {
            "n/a"
        };
        if reference_accepts {
            report.reference_accepts += 1;
            let set = report.per_set.entry(row.set.clone()).or_default();
            set.1 += 1;
            if frankenlean_accepts {
                report.both_accept += 1;
                set.0 += 1;
            }
        } else if frankenlean_accepts {
            report.false_accepts += 1;
            report.problems.push(format!(
                "{}: FrankenLean's `lean` accepts a program the pinned Reference rejects \
                 (soundness direction); the Reference says: {}",
                row.file,
                first_line(&seen.reference.stdout)
            ));
        }
        let (verdict, note) = match seen.frankenlean.exit {
            Some(0) => ("accept", String::new()),
            Some(_) => ("reject", first_line(&seen.frankenlean.stderr)),
            None => ("timeout", format!("no verdict within {PROGRAM_TIMEOUT:?}")),
        };
        report.lines.push(format!(
            "{}\t{}\treference={}\tfrankenlean={verdict}\toutput={output}\t{note}",
            row.file,
            row.set,
            if reference_accepts {
                "accept"
            } else {
                "reject"
            },
        ));
    }
    report
}

fn summary(report: &Report) -> String {
    let sets = report
        .per_set
        .iter()
        .map(|(set, (both, reference))| format!("set {set} {both} of {reference}"))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "ordinary_lean_probe: Reference-accepted programs FrankenLean's `lean` accepts: {} of {} \
         ({sets}); of those, stdout and stderr identical: {} of {}; verdicts agree: {} of {}; \
         Reference-rejected programs FrankenLean accepts: {} of {}",
        report.both_accept,
        report.reference_accepts,
        report.identical,
        report.both_accept,
        report.agree,
        report.programs,
        report.false_accepts,
        report.programs - report.reference_accepts
    )
}

/// Run `program file` from the corpus directory, bounded by `PROGRAM_TIMEOUT`.
fn run(program: &Path, corpus: &Path, file: &str) -> Run {
    let mut child = Command::new(program)
        .arg(file)
        .current_dir(corpus)
        .env_remove("LEAN_PATH")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap_or_else(|error| panic!("spawn {}: {error}", program.display()));
    let mut stdout = child.stdout.take().expect("piped stdout");
    let mut stderr = child.stderr.take().expect("piped stderr");
    let stdout_reader = std::thread::spawn(move || {
        let mut bytes = Vec::new();
        stdout.read_to_end(&mut bytes).map(|_| bytes)
    });
    let stderr_reader = std::thread::spawn(move || {
        let mut bytes = Vec::new();
        stderr.read_to_end(&mut bytes).map(|_| bytes)
    });
    let deadline = Instant::now() + PROGRAM_TIMEOUT;
    let exit = loop {
        if let Some(status) = child.try_wait().expect("poll child") {
            break status.code();
        }
        if Instant::now() >= deadline {
            // A child that exited between the poll and the kill is reaped by
            // the wait below either way; neither outcome is a verdict.
            if let Err(error) = child.kill() {
                eprintln!("kill {} {file}: {error}", program.display());
            }
            child.wait().expect("reap timed-out child");
            break None;
        }
        std::thread::sleep(Duration::from_millis(20));
    };
    let collect = |reader: std::thread::JoinHandle<std::io::Result<Vec<u8>>>| {
        let bytes = reader
            .join()
            .expect("output reader")
            .expect("read child output");
        String::from_utf8_lossy(&bytes).into_owned()
    };
    Run {
        exit,
        stdout: collect(stdout_reader),
        stderr: collect(stderr_reader),
    }
}

#[test]
fn ordinary_lean_probe_measures_frankenlean_lean_against_the_pinned_reference() {
    let root = fln_core::checked_workspace_root!();
    let corpus = root.join(CORPUS);
    let (_, rows) = load(&corpus);
    let reference = match reference_lean(&root) {
        Ok(reference) => reference,
        Err(reason) => {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "FLN_REQUIRE_REFERENCE is set but {reason}"
            );
            eprintln!("SKIP ordinary_lean_probe: {reason}");
            return;
        }
    };
    let frankenlean = PathBuf::from(env!("CARGO_BIN_EXE_lean"));
    let next = AtomicUsize::new(0);
    let observed = Mutex::new(BTreeMap::new());
    std::thread::scope(|scope| {
        for _ in 0..WORKERS {
            scope.spawn(|| {
                loop {
                    let index = next.fetch_add(1, Ordering::Relaxed);
                    let Some(row) = rows.get(index) else { break };
                    let seen = Observed {
                        reference: run(&reference, &corpus, &row.file),
                        frankenlean: run(&frankenlean, &corpus, &row.file),
                    };
                    observed
                        .lock()
                        .expect("observation lock")
                        .insert(row.file.clone(), seen);
                }
            });
        }
    });
    let observed = observed.into_inner().expect("observation lock");
    let report = score(&rows, &observed);
    for line in &report.lines {
        eprintln!("{line}");
    }
    eprintln!("{}", summary(&report));
    assert!(
        report.problems.is_empty(),
        "{} probe problem(s):\n{}",
        report.problems.len(),
        report.problems.join("\n")
    );
}

#[test]
fn the_checked_in_corpus_matches_its_manifest() {
    let root = fln_core::checked_workspace_root!();
    let (files, rows) = load(&root.join(CORPUS));
    assert_eq!(files.len(), rows.len());
    let sets: BTreeMap<&str, usize> = rows.iter().fold(BTreeMap::new(), |mut sets, row| {
        *sets.entry(row.set.as_str()).or_default() += 1;
        sets
    });
    assert_eq!(sets, BTreeMap::from([("A", 16), ("B", 14)]));
}

fn row(file: &str, exit: i32, stdout: &str) -> Row {
    Row {
        file: file.to_owned(),
        set: "A".to_owned(),
        exit,
        stdout: stdout.to_owned(),
        stderr: String::new(),
    }
}

fn observed(reference: &Row, exit: Option<i32>, stdout: &str) -> Observed {
    Observed {
        reference: Run {
            exit: Some(reference.exit),
            stdout: reference.stdout.clone(),
            stderr: reference.stderr.clone(),
        },
        frankenlean: Run {
            exit,
            stdout: stdout.to_owned(),
            stderr: String::new(),
        },
    }
}

#[test]
fn a_planted_false_acceptance_fails_the_probe_and_a_low_score_does_not() {
    let rejected = row("wrong.lean", 1, "wrong.lean:1:0: error: Type mismatch\n");
    let accepted = row("ok.lean", 0, "42\n");
    let rows = vec![rejected.clone(), accepted.clone()];

    // FrankenLean refuses everything: the score is 0 of 1, and that is not a failure.
    let low = BTreeMap::from([
        ("wrong.lean".to_owned(), observed(&rejected, Some(1), "")),
        ("ok.lean".to_owned(), observed(&accepted, Some(1), "")),
    ]);
    let report = score(&rows, &low);
    assert!(report.problems.is_empty(), "{:?}", report.problems);
    assert_eq!((report.both_accept, report.reference_accepts), (0, 1));
    assert_eq!(report.agree, 1);

    // A timeout is not acceptance, in either direction.
    let silent = BTreeMap::from([
        ("wrong.lean".to_owned(), observed(&rejected, None, "")),
        ("ok.lean".to_owned(), observed(&accepted, None, "")),
    ]);
    let report = score(&rows, &silent);
    assert!(report.problems.is_empty(), "{:?}", report.problems);
    assert_eq!(report.both_accept, 0);

    // The planted program: FrankenLean accepts what the Reference rejects.
    let planted = BTreeMap::from([
        ("wrong.lean".to_owned(), observed(&rejected, Some(0), "")),
        ("ok.lean".to_owned(), observed(&accepted, Some(0), "42\n")),
    ]);
    let report = score(&rows, &planted);
    assert_eq!(report.false_accepts, 1);
    assert_eq!(report.problems.len(), 1, "{:?}", report.problems);
    assert!(
        report.problems[0].starts_with("wrong.lean: FrankenLean's `lean` accepts"),
        "{:?}",
        report.problems
    );
    assert_eq!((report.both_accept, report.identical), (1, 1));
}

#[test]
fn a_manifest_row_the_pin_no_longer_reproduces_is_refused() {
    let recorded = row("ok.lean", 0, "42\n");
    let mut seen = observed(&recorded, Some(1), "");
    seen.reference.stdout = "43\n".to_owned();
    let report = score(
        std::slice::from_ref(&recorded),
        &BTreeMap::from([("ok.lean".to_owned(), seen)]),
    );
    assert_eq!(report.problems.len(), 1, "{:?}", report.problems);
    assert!(
        report.problems[0].contains("no longer reproduces")
            && report.problems[0].ends_with("ok.lean\tA\t0\t43\\n\t"),
        "{:?}",
        report.problems
    );
}

#[test]
fn an_emptied_or_unmatched_corpus_is_refused_as_a_broken_scan() {
    assert!(!scan_problems(&[], &[]).is_empty());

    let files: Vec<String> = (0..CORPUS_FLOOR).map(|n| format!("p{n:02}.lean")).collect();
    let rows: Vec<Row> = files.iter().map(|file| row(file, 0, "")).collect();
    assert!(scan_problems(&files, &rows).is_empty());

    // A program with no row, and a row with no program.
    let mut extra_file = files.clone();
    extra_file.push("new.lean".to_owned());
    assert_eq!(scan_problems(&extra_file, &rows).len(), 1);
    let mut extra_row = rows.clone();
    extra_row.push(row("gone.lean", 0, ""));
    assert_eq!(scan_problems(&files, &extra_row).len(), 1);

    // One program short of the floor, with matching rows.
    assert_eq!(
        scan_problems(&files[1..], &rows[1..]).len(),
        1,
        "a shrunken corpus is a broken scan"
    );
}

#[test]
fn manifest_fields_round_trip_through_their_escapes() {
    let text = "a\\b\tc\nd\r";
    assert_eq!(unescape(&escape(text)).as_deref(), Ok(text));
    assert!(unescape("bad\\q").is_err());
    let manifest = format!("# comment\nx.lean\tB\t1\t{}\t\n", escape(text));
    let rows = parse_manifest(&manifest).expect("well-formed manifest");
    assert_eq!(rows.len(), 1);
    assert_eq!((rows[0].set.as_str(), rows[0].exit), ("B", 1));
    assert_eq!(rows[0].stdout, text);
    assert!(parse_manifest("x.lean\tC\t0\t\t\n").is_err());
    assert!(parse_manifest("x.lean\tA\t0\t\n").is_err());
}
