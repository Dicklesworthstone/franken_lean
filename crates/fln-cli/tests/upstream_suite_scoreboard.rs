//! Upstream suite scoreboard (bead fln-upstream-suite-scoreboard-n04o).
//!
//! The pinned Reference's own test programs, `vendor/lean4-src/tests/{elab,elab_fail,compile}`,
//! run through FrankenLean's drop-in `lean` and the pinned `lean`, one verdict per file. Unlike
//! the project's 114 examples and the 37-program probe, nobody here wrote these files, so the
//! score cannot be fitted to them one file at a time.
//!
//! Three checked-in tables:
//! - `fixtures/upstream_suite/oracle.tsv`: per file, the pinned `lean FILE` exit code, an
//!   FNV-1a digest of its stdout, whether that stdout is `volatile` (it differed between two pin
//!   runs, so only the exit code is compared), and the header the pin parsed
//!   (`scripts/extract/upstream_suite_headers.lean`), from which the stratum is derived. It is
//!   written only by `regenerate_the_upstream_oracle_from_the_pin`, which runs nothing but the
//!   pinned binary; expectations are never hand-written.
//! - `fixtures/upstream_suite/ledger.tsv`: per file, what FrankenLean's `lean` did, whether its
//!   stdout matched the pin's, and the first-refusal class from a closed set.
//!
//! The scoreboard run re-derives the oracle and fails only when:
//! - FrankenLean's `lean` exits 0 on a file the pin rejects (the soundness direction);
//! - a file the ledger records as accepted with identical stdout no longer is (the ratchet);
//! - the scan is broken: a directory below its floor, a file without a row or a row without a
//!   file, an unreadable entry, a malformed row, or a live pin EXIT CODE the oracle does not
//!   record (verdict drift);
//! - the pin is absent while `FLN_REQUIRE_REFERENCE` is set.
//!
//! A live pin stdout that differs from the recorded digest under the same exit code is reported
//! as host-dependent, not failed: some files print the host itself (`elab/async_systems_info`
//! prints `constrainedMemory`, the launching cgroup's limit), which no same-host volatility
//! measurement can catch. "Identical output" is therefore judged against the live pin's
//! stdout from the same run, never against the recorded digest. A live pin exit code the oracle
//! does not record is re-run once, alone; when the retry reproduces the oracle it is reported as
//! a host-dependent exit (`elab/async_systems_info` loses a race with the host's renicing daemon),
//! and when it does not, it is verdict drift and fails.
//!
//! It never fails on a low score. A file with no verdict within `FILE_TIMEOUT` is `timeout`,
//! which is never acceptance (FL-INV-07). Each file runs from a temporary copy of its
//! directory with `LEAN_PATH` unset, so nothing is ever written under `vendor/`.
//!
//! FrankenLean admits an explicit import closure itself, and nothing carries over between
//! runs: its reuse records go to a directory inside the run's copy. Every closure of a
//! non-`prelude` header contains `Init`, and admitting a closure does at least the work of
//! admitting any closure inside it. So a header-only `import Init` is run first, and when
//! even that is not admitted within `FILE_TIMEOUT`, those files are recorded as that measured
//! timeout rather than each spending `FILE_TIMEOUT` to find it again.
//!
//! Run it (pin required, about the pin's own elaboration time over 3,379 files):
//! `FLN_REQUIRE_REFERENCE=1 cargo test -p fln-cli --release --test upstream_suite_scoreboard \
//!  -- --ignored --nocapture upstream_suite_scoreboard_measures`
//! Advance the ratchet after a clean run with `FLN_UPSTREAM_LEDGER_WRITE=1`; re-record the
//! oracle (a pin bump) with `FLN_UPSTREAM_ORACLE_WRITE=1` and `regenerate_the_upstream_oracle`.
//!
//! Consumers: the source lane (the first-refusal histogram is its work queue), every reality
//! check, and `IMPLEMENTATION_STATUS.md`. Deletion condition: G4's corpus-scale T2 rig
//! subsumes it.
#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

const SUITE: &str = "vendor/lean4-src/tests";
/// The measured population at the pin, per directory. A scan that finds fewer is broken; it
/// is never a smaller suite. A vendor bump that adds files raises these with the oracle.
const DIRECTORIES: [(&str, usize); 3] = [("elab", 2995), ("elab_fail", 315), ("compile", 69)];
const ORACLE: &str = "crates/fln-cli/tests/fixtures/upstream_suite/oracle.tsv";
const LEDGER: &str = "crates/fln-cli/tests/fixtures/upstream_suite/ledger.tsv";
const HEADER_SCRIPT: &str = "scripts/extract/upstream_suite_headers.lean";
const WORKERS: usize = 16;
/// FrankenLean's runs of files with explicit imports share this smaller pool. Each may hold
/// a cold council of its whole closure (`import Init` alone took 631 s and 5.9 GB at 8
/// threads, measured 2026-10-07), and sixteen at once would contend for the host's memory.
const IMPORT_WORKERS: usize = 4;
/// The header-only program whose admission bounds every non-`prelude` import closure.
const INIT_STUB: &str = "fln-init-closure.lean";
/// Generous on purpose: at 60 s the pin's own verdict on its slowest file depended on host
/// load (one oracle recorded a timeout, the next an acceptance), and a verdict the host can
/// flip cannot anchor a drift check.
const FILE_TIMEOUT: Duration = Duration::from_secs(300);

/// What one process did. `exit` is `None` when there was no verdict: a timeout or a signal.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Run {
    exit: Option<i32>,
    stdout: String,
    stderr: String,
    /// Wall-clock milliseconds, reported per file and never compared.
    millis: u128,
}

impl Run {
    fn accepts(&self) -> bool {
        self.exit == Some(0)
    }
}

/// One oracle row: the pin's recorded behaviour on one file.
#[derive(Debug, Clone, PartialEq, Eq)]
struct OracleRow {
    file: String,
    exit: Option<i32>,
    digest: u64,
    volatile: bool,
    kind: String,
    imports: Vec<String>,
}

/// One ledger row: FrankenLean's recorded behaviour on one file.
#[derive(Debug, Clone, PartialEq, Eq)]
struct LedgerRow {
    file: String,
    exit: Option<i32>,
    output: String,
    class: String,
}

/// The FNV-1a digest of stdout. Stable across toolchains and dependency-free; it detects a
/// changed output, which is all the oracle needs (nothing here is adversarial).
fn digest(text: &str) -> u64 {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in text.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

fn exit_field(exit: Option<i32>) -> String {
    exit.map_or_else(|| "timeout".to_owned(), |code| code.to_string())
}

fn parse_exit(field: &str) -> Result<Option<i32>, String> {
    if field == "timeout" {
        return Ok(None);
    }
    field
        .parse::<i32>()
        .map(Some)
        .map_err(|error| format!("exit {field:?}: {error}"))
}

/// The stratum a file belongs to, from the header the pin parsed: what FrankenLean must have
/// before the file can pass.
fn stratum(kind: &str, imports: &[String]) -> &'static str {
    let under =
        |module: &str, root: &str| module == root || module.starts_with(&format!("{root}."));
    if kind == "unparsed" || kind == "unreadable" {
        "unparsed-header"
    } else if imports.is_empty() {
        if kind.ends_with("prelude") {
            "prelude"
        } else {
            "no-header"
        }
    } else if imports.iter().any(|module| under(module, "Lean")) {
        "lean-imports"
    } else if imports
        .iter()
        .all(|module| under(module, "Init") || under(module, "Std"))
    {
        "init-std-imports"
    } else {
        "other-imports"
    }
}

/// The first-refusal class of a FrankenLean `lean` run, from a closed set. The patterns are
/// the drop-in's own message shapes (measured 2026-10-07 over a sample of `tests/elab`).
fn refusal_class(run: &Run) -> String {
    if run.accepts() {
        return "accept".to_owned();
    }
    let Some(_) = run.exit else {
        return "timeout".to_owned();
    };
    let first = run.stderr.lines().next().unwrap_or_default();
    if first.contains("could not read source import closure")
        || first.contains("cannot resolve import")
        || first.contains("nor an .olean on the search path")
    {
        "import".to_owned()
    } else if first.starts_with("lean: capability: ") {
        "capability".to_owned()
    } else if first.contains("lexical analysis reported") {
        "lexer".to_owned()
    } else if let Some((_, rest)) = first.split_once("outside the bounded source grammar") {
        let expected = rest
            .split_once("expected ")
            .map(|(_, token)| {
                token
                    .chars()
                    .take_while(|ch| ch.is_ascii_alphanumeric())
                    .collect::<String>()
            })
            .filter(|token| !token.is_empty())
            .unwrap_or_else(|| "other".to_owned());
        format!("parser:{expected}")
    } else if first.contains("parse refused source") {
        "parser:other".to_owned()
    } else if first.contains("Unknown identifier")
        || first.contains("Unknown constant")
        || first.contains("unknown namespace")
    {
        "unknown-name".to_owned()
    } else if first.contains("elaboration refused source") {
        "elaboration".to_owned()
    } else if first.contains("compile") || first.contains("code generator") {
        "compile".to_owned()
    } else if first.contains("runtime") || first.contains("VM ") || first.contains("panicked") {
        "runtime".to_owned()
    } else {
        "other".to_owned()
    }
}

fn parse_oracle(text: &str) -> Result<Vec<OracleRow>, Vec<String>> {
    let mut rows = Vec::new();
    let mut problems = Vec::new();
    for (index, line) in text.lines().enumerate() {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let at = format!("oracle.tsv:{}", index + 1);
        let fields: Vec<&str> = line.split('\t').collect();
        if fields.len() != 6 {
            problems.push(format!("{at}: expected 6 fields, found {}", fields.len()));
            continue;
        }
        let exit = parse_exit(fields[1]);
        let digest = u64::from_str_radix(fields[2], 16).map_err(|error| error.to_string());
        let volatile = match fields[3] {
            "0" => Ok(false),
            "1" => Ok(true),
            other => Err(format!("volatile must be 0 or 1, found {other:?}")),
        };
        match (exit, digest, volatile) {
            (Ok(exit), Ok(digest), Ok(volatile)) => rows.push(OracleRow {
                file: fields[0].to_owned(),
                exit,
                digest,
                volatile,
                kind: fields[4].to_owned(),
                imports: fields[5]
                    .split(',')
                    .filter(|module| !module.is_empty())
                    .map(str::to_owned)
                    .collect(),
            }),
            (exit, digest, volatile) => {
                for error in [exit.err(), digest.err(), volatile.err()]
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

fn parse_ledger(text: &str) -> Result<Vec<LedgerRow>, Vec<String>> {
    let mut rows = Vec::new();
    let mut problems = Vec::new();
    for (index, line) in text.lines().enumerate() {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let at = format!("ledger.tsv:{}", index + 1);
        let fields: Vec<&str> = line.split('\t').collect();
        if fields.len() != 4 {
            problems.push(format!("{at}: expected 4 fields, found {}", fields.len()));
            continue;
        }
        if !matches!(fields[2], "identical" | "differ" | "n/a") {
            problems.push(format!(
                "{at}: output must be identical, differ or n/a, found {:?}",
                fields[2]
            ));
            continue;
        }
        match parse_exit(fields[1]) {
            Ok(exit) => rows.push(LedgerRow {
                file: fields[0].to_owned(),
                exit,
                output: fields[2].to_owned(),
                class: fields[3].to_owned(),
            }),
            Err(error) => problems.push(format!("{at}: {error}")),
        }
    }
    if problems.is_empty() {
        Ok(rows)
    } else {
        Err(problems)
    }
}

/// The population as found on disk: `dir/file.lean` for every `.lean` directly under each
/// suite directory. An unreadable entry is a problem, never a silently smaller suite.
fn scan(suite: &Path) -> (Vec<String>, Vec<String>) {
    let mut files = Vec::new();
    let mut problems = Vec::new();
    for (directory, _) in DIRECTORIES {
        match std::fs::read_dir(suite.join(directory)) {
            Ok(entries) => {
                for entry in entries {
                    match entry {
                        Ok(entry) => {
                            let path = entry.path();
                            if path.extension().and_then(|ext| ext.to_str()) == Some("lean")
                                && path.is_file()
                            {
                                files.push(format!(
                                    "{directory}/{}",
                                    entry.file_name().to_string_lossy()
                                ));
                            }
                        }
                        Err(error) => {
                            problems.push(format!("{directory}: unreadable entry: {error}"))
                        }
                    }
                }
            }
            Err(error) => problems.push(format!("{directory}: cannot read the directory: {error}")),
        }
    }
    files.sort();
    (files, problems)
}

/// A broken scan is refused, never scored: the population, the oracle and the ledger must name
/// the same files, and every directory must reach its floor.
fn scan_problems(files: &[String], oracle: &[OracleRow], ledger: &[LedgerRow]) -> Vec<String> {
    let mut problems = Vec::new();
    let on_disk: BTreeSet<&str> = files.iter().map(String::as_str).collect();
    for (table, names) in [
        (
            "oracle",
            oracle
                .iter()
                .map(|row| row.file.as_str())
                .collect::<Vec<_>>(),
        ),
        (
            "ledger",
            ledger
                .iter()
                .map(|row| row.file.as_str())
                .collect::<Vec<_>>(),
        ),
    ] {
        let mut seen = BTreeSet::new();
        for name in &names {
            if !seen.insert(*name) {
                problems.push(format!("duplicate {table} row for {name}"));
            }
            if !on_disk.contains(name) {
                problems.push(format!(
                    "the {table} row for {name} names no file in the suite"
                ));
            }
        }
        for file in &on_disk {
            if !seen.contains(file) {
                problems.push(format!("{file} has no {table} row"));
            }
        }
    }
    for (directory, floor) in DIRECTORIES {
        let found = files
            .iter()
            .filter(|file| {
                file.split_once('/')
                    .is_some_and(|(dir, _)| dir == directory)
            })
            .count();
        if found < floor {
            problems.push(format!(
                "{directory}: the scan found {found} files, below the floor of {floor}; a broken \
                 scan is not a smaller suite"
            ));
        }
    }
    problems
}

#[derive(Debug, Default)]
struct Report {
    lines: Vec<String>,
    problems: Vec<String>,
    /// Advanced ledger rows, written only on request after a run with no problems.
    ledger: Vec<LedgerRow>,
    improved: Vec<String>,
    /// Files whose live pin stdout differs from the recorded digest under the same exit code.
    host_dependent: Vec<String>,
    /// Per directory: (FrankenLean accepts of pin-accepted, pin-accepted, identical, false
    /// accepts, pin-rejected).
    per_directory: BTreeMap<String, (usize, usize, usize, usize, usize)>,
    /// Per stratum, over pin-accepted files: (FrankenLean accepts, pin-accepted).
    per_stratum: BTreeMap<String, (usize, usize)>,
    /// First-refusal classes over pin-accepted files FrankenLean does not accept.
    histogram: BTreeMap<String, usize>,
}

/// Re-run, once and alone, every file whose live pin exit code is not the oracle's, keeping the
/// second result. Returns the files whose retry reproduced the oracle: their verdict depends on
/// the host under load, not on the pin. `elab/async_systems_info` sets its own and its parent's
/// scheduling priority to 3 and asserts it took, which fails whenever a host daemon (here
/// `ananicy-cpp`, which renices `lean` to 15) got there first. A drift the retry repeats stays in
/// `pin` and fails `score` as before.
fn retry_drifted(
    oracle: &[OracleRow],
    pin: &mut BTreeMap<String, Run>,
    mut rerun: impl FnMut(&str) -> Run,
) -> Vec<String> {
    let mut reproduced = Vec::new();
    for row in oracle {
        if pin.get(&row.file).is_some_and(|live| live.exit != row.exit) {
            let again = rerun(&row.file);
            if again.exit == row.exit {
                reproduced.push(row.file.clone());
            }
            pin.insert(row.file.clone(), again);
        }
    }
    reproduced
}

/// Score one run against the oracle and the ledger. `pin` is the live pin result per file
/// (the re-derived oracle) and `subject` FrankenLean's.
fn score(
    oracle: &[OracleRow],
    ledger: &[LedgerRow],
    pin: &BTreeMap<String, Run>,
    subject: &BTreeMap<String, Run>,
) -> Report {
    let mut report = Report::default();
    let recorded: BTreeMap<&str, &LedgerRow> =
        ledger.iter().map(|row| (row.file.as_str(), row)).collect();
    for row in oracle {
        let (Some(live_pin), Some(seen)) = (pin.get(&row.file), subject.get(&row.file)) else {
            report.problems.push(format!(
                "{}: never observed; the run did not reach it",
                row.file
            ));
            continue;
        };
        if live_pin.exit != row.exit {
            // What the pin said is the evidence a reader needs to tell a pin change from a
            // host condition, so its first stderr line and last stdout line travel with it.
            let said = |text: &str, last: bool| {
                let line = if last { text.lines().last() } else { text.lines().next() };
                line.unwrap_or_default().chars().take(300).collect::<String>()
            };
            report.problems.push(format!(
                "{}: the pinned Reference no longer reproduces its oracle row (exit {} digest \
                 {:016x}); re-record the oracle only for a pin change. Pin stderr: {:?}; last \
                 stdout line: {:?}",
                row.file,
                exit_field(live_pin.exit),
                digest(&live_pin.stdout),
                said(&live_pin.stderr, false),
                said(&live_pin.stdout, true)
            ));
        } else if !row.volatile && digest(&live_pin.stdout) != row.digest {
            report.host_dependent.push(row.file.clone());
        }
        let directory = row
            .file
            .split_once('/')
            .map_or("?", |(dir, _)| dir)
            .to_owned();
        let totals = report.per_directory.entry(directory).or_default();
        let pin_accepts = row.exit == Some(0);
        // Against the live pin's stdout from this run; a volatile file compares exit codes only.
        let identical =
            pin_accepts && seen.accepts() && (row.volatile || seen.stdout == live_pin.stdout);
        let output = if pin_accepts && seen.accepts() {
            if identical { "identical" } else { "differ" }
        } else {
            "n/a"
        };
        let class = refusal_class(seen);
        if pin_accepts {
            totals.1 += 1;
            let stratum = report
                .per_stratum
                .entry(stratum(&row.kind, &row.imports).to_owned())
                .or_default();
            stratum.1 += 1;
            if seen.accepts() {
                totals.0 += 1;
                stratum.0 += 1;
                if identical {
                    totals.2 += 1;
                }
            } else {
                *report.histogram.entry(class.clone()).or_default() += 1;
            }
        } else {
            totals.4 += 1;
            if seen.accepts() {
                totals.3 += 1;
                report.problems.push(format!(
                    "{}: FrankenLean's `lean` accepts a file the pinned Reference rejects \
                     (soundness direction)",
                    row.file
                ));
            }
        }
        match recorded.get(row.file.as_str()) {
            Some(previous) if previous.output == "identical" && output != "identical" => {
                report.problems.push(format!(
                    "{}: regressed: the ledger records it accepted with identical output; now \
                     `{output}`, class `{class}`",
                    row.file
                ));
            }
            Some(previous) if previous.output != "identical" && output == "identical" => {
                report.improved.push(row.file.clone());
            }
            _ => {}
        }
        report.lines.push(format!(
            "{}\tpin={}\tfrankenlean={}\toutput={output}\tclass={class}\tpin_ms={}\tfrankenlean_ms={}",
            row.file,
            exit_field(row.exit),
            exit_field(seen.exit),
            live_pin.millis,
            seen.millis
        ));
        report.ledger.push(LedgerRow {
            file: row.file.clone(),
            exit: seen.exit,
            output: output.to_owned(),
            class,
        });
    }
    report
}

fn summary(report: &Report) -> String {
    let directories = report
        .per_directory
        .iter()
        .map(|(dir, (accepted, pin_accepted, identical, false_accepts, pin_rejected))| {
            format!(
                "{dir}: {accepted} of {pin_accepted} pin-accepted ({identical} identical stdout), \
                 false accepts {false_accepts} of {pin_rejected}"
            )
        })
        .collect::<Vec<_>>()
        .join("; ");
    let strata = report
        .per_stratum
        .iter()
        .map(|(stratum, (accepted, pin_accepted))| format!("{stratum} {accepted}/{pin_accepted}"))
        .collect::<Vec<_>>()
        .join(", ");
    let mut histogram: Vec<(&String, &usize)> = report.histogram.iter().collect();
    histogram.sort_by(|left, right| right.1.cmp(left.1).then(left.0.cmp(right.0)));
    let histogram = histogram
        .iter()
        .map(|(class, count)| format!("{class} {count}"))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "upstream_suite_scoreboard: {directories} | strata (pin-accepted): {strata} | first \
         refusals (pin-accepted files FrankenLean refuses): {histogram} | improved since the \
         ledger: {} | host-dependent pin stdout: {}",
        report.improved.len(),
        if report.host_dependent.is_empty() {
            "none".to_owned()
        } else {
            report.host_dependent.join(" ")
        }
    )
}

fn render_ledger(rows: &[LedgerRow]) -> String {
    let mut text = String::from(
        "# Upstream suite scoreboard ledger (bead fln-upstream-suite-scoreboard-n04o): what \
         FrankenLean's `lean` did per file.\n# Written only by the scoreboard run with \
         FLN_UPSTREAM_LEDGER_WRITE=1 after a run with no problems; never by hand.\n# file\t\
         frankenlean\toutput\tclass\n",
    );
    for row in rows {
        text.push_str(&format!(
            "{}\t{}\t{}\t{}\n",
            row.file,
            exit_field(row.exit),
            row.output,
            row.class
        ));
    }
    text
}

fn render_oracle(rows: &[OracleRow]) -> String {
    let mut text = String::from(
        "# Upstream suite oracle (bead fln-upstream-suite-scoreboard-n04o): the pinned `lean \
         FILE` per file.\n# Written only by regenerate_the_upstream_oracle_from_the_pin, which \
         runs nothing but the pinned binary; never by hand.\n# file\tpin_exit\tstdout_fnv1a\t\
         volatile\theader_kind\texplicit_imports\n",
    );
    for row in rows {
        text.push_str(&format!(
            "{}\t{}\t{:016x}\t{}\t{}\t{}\n",
            row.file,
            exit_field(row.exit),
            row.digest,
            u8::from(row.volatile),
            row.kind,
            row.imports.join(",")
        ));
    }
    text
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

/// Run `program file` from `directory`, bounded by `FILE_TIMEOUT`. FrankenLean keeps its
/// import reuse records in `reuse`; the pin ignores the variable.
fn run(program: &Path, directory: &Path, file: &str, reuse: &Path) -> Run {
    let mut child = Command::new(program)
        .arg(file)
        .current_dir(directory)
        .env_remove("LEAN_PATH")
        .env("FLN_IMPORT_REUSE_DIR", reuse)
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
    let started = Instant::now();
    let deadline = started + FILE_TIMEOUT;
    let exit = loop {
        if let Some(status) = child.try_wait().expect("poll child") {
            break status.code();
        }
        if Instant::now() >= deadline {
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
        millis: started.elapsed().as_millis(),
    }
}

/// Copy each suite directory into a fresh temporary tree, so a test that writes files never
/// writes under `vendor/`.
fn copy_suite(suite: &Path) -> PathBuf {
    fn copy_tree(from: &Path, to: &Path) {
        std::fs::create_dir_all(to).expect("create the copied directory");
        for entry in std::fs::read_dir(from).expect("read a suite directory") {
            let entry = entry.expect("suite entry");
            let target = to.join(entry.file_name());
            if entry.file_type().expect("entry type").is_dir() {
                copy_tree(&entry.path(), &target);
            } else {
                std::fs::copy(entry.path(), &target).expect("copy a suite file");
            }
        }
    }
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |elapsed| elapsed.as_nanos());
    let copy =
        std::env::temp_dir().join(format!("fln-upstream-suite-{}-{stamp}", std::process::id()));
    for (directory, _) in DIRECTORIES {
        copy_tree(&suite.join(directory), &copy.join(directory));
    }
    copy
}

/// Run `program` over `files` from the copied suite on `workers` threads.
fn run_all(program: &Path, copy: &Path, files: &[String], workers: usize) -> BTreeMap<String, Run> {
    let next = AtomicUsize::new(0);
    let observed = Mutex::new(BTreeMap::new());
    let reuse = copy.join("fln-import-reuse");
    std::thread::scope(|scope| {
        for _ in 0..workers {
            scope.spawn(|| {
                loop {
                    let index = next.fetch_add(1, Ordering::Relaxed);
                    let Some(file) = files.get(index) else { break };
                    let (directory, name) = file.split_once('/').expect("dir/file");
                    let seen = run(program, &copy.join(directory), name, &reuse);
                    observed
                        .lock()
                        .expect("observation lock")
                        .insert(file.clone(), seen);
                }
            });
        }
    });
    observed.into_inner().expect("observation lock")
}

/// FrankenLean over the suite: files without explicit imports on `WORKERS`, the rest on
/// `IMPORT_WORKERS`, after the header-only `import Init` decides whether the non-`prelude`
/// ones can be admitted at all (see the module documentation).
fn run_subject(
    program: &Path,
    copy: &Path,
    files: &[String],
    oracle: &[OracleRow],
) -> BTreeMap<String, Run> {
    let headers: BTreeMap<&str, &OracleRow> =
        oracle.iter().map(|row| (row.file.as_str(), row)).collect();
    let (imported, plain): (Vec<String>, Vec<String>) = files.iter().cloned().partition(|file| {
        headers
            .get(file.as_str())
            .is_some_and(|row| !row.imports.is_empty())
    });
    let mut observed = run_all(program, copy, &plain, WORKERS);
    std::fs::write(copy.join(INIT_STUB), "import Init\n").expect("write the Init stub");
    let init = run(program, copy, INIT_STUB, &copy.join("fln-import-reuse"));
    eprintln!(
        "upstream_suite_scoreboard: header-only `import Init`: exit {:?} in {} ms",
        init.exit, init.millis
    );
    let (bounded, measured): (Vec<String>, Vec<String>) = imported.into_iter().partition(|file| {
        init.exit.is_none()
            && headers
                .get(file.as_str())
                .is_some_and(|row| row.kind == "implicit")
    });
    observed.extend(run_all(program, copy, &measured, IMPORT_WORKERS));
    for file in bounded {
        observed.insert(file, closure_timeout(&init));
    }
    observed
}

/// The row of a file whose closure contains `Init` when the header-only `import Init`
/// had no verdict within `FILE_TIMEOUT`: that measured timeout, never a run of its own.
fn closure_timeout(init: &Run) -> Run {
    assert!(
        init.exit.is_none(),
        "only an unadmitted Init bounds a closure"
    );
    Run {
        exit: None,
        stdout: String::new(),
        stderr: format!(
            "not run: the header-only `import Init` was not admitted within {} s ({} ms), and this closure contains it",
            FILE_TIMEOUT.as_secs(),
            init.millis
        ),
        millis: init.millis,
    }
}

/// The checked-in tables, refused as a broken scan unless they name exactly the population.
/// `bootstrap` (the ledger writer) may start from no ledger at all: the first ledger is
/// written from a run, never by hand.
fn load(root: &Path, bootstrap: bool) -> (Vec<String>, Vec<OracleRow>, Vec<LedgerRow>) {
    let (files, mut problems) = scan(&root.join(SUITE));
    let oracle = std::fs::read_to_string(root.join(ORACLE))
        .map_err(|error| vec![format!("cannot read {ORACLE}: {error}")])
        .and_then(|text| parse_oracle(&text));
    let ledger = match std::fs::read_to_string(root.join(LEDGER)) {
        Err(error) if bootstrap && error.kind() == std::io::ErrorKind::NotFound => {
            if let Ok(oracle) = &oracle {
                problems.extend(scan_problems(
                    &files,
                    oracle,
                    &oracle
                        .iter()
                        .map(|row| LedgerRow {
                            file: row.file.clone(),
                            exit: None,
                            output: "n/a".to_owned(),
                            class: "unmeasured".to_owned(),
                        })
                        .collect::<Vec<_>>(),
                ));
            }
            assert!(
                problems.is_empty(),
                "broken upstream-suite scan:\n{}",
                problems.join("\n")
            );
            return (files, oracle.unwrap_or_default(), Vec::new());
        }
        read => read
            .map_err(|error| vec![format!("cannot read {LEDGER}: {error}")])
            .and_then(|text| parse_ledger(&text)),
    };
    let (oracle, ledger) = match (oracle, ledger) {
        (Ok(oracle), Ok(ledger)) => {
            problems.extend(scan_problems(&files, &oracle, &ledger));
            (oracle, ledger)
        }
        (oracle, ledger) => {
            problems.extend(oracle.err().into_iter().flatten());
            problems.extend(ledger.err().into_iter().flatten());
            (Vec::new(), Vec::new())
        }
    };
    assert!(
        problems.is_empty(),
        "broken upstream-suite scan:\n{}",
        problems.join("\n")
    );
    (files, oracle, ledger)
}

/// The pin is required, or the run is a typed SKIP.
fn require_pin(root: &Path, lane: &str) -> Option<PathBuf> {
    match reference_lean(root) {
        Ok(reference) => Some(reference),
        Err(reason) => {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "FLN_REQUIRE_REFERENCE is set but {reason}"
            );
            eprintln!("SKIP {lane}: {reason}");
            None
        }
    }
}

#[ignore = "cost: the pinned lean and FrankenLean's lean over 3,379 upstream test files; an on-demand pin-gated lane (bead fln-upstream-suite-scoreboard-n04o), run by contract-drift with FLN_REQUIRE_REFERENCE=1"]
#[test]
fn upstream_suite_scoreboard_measures_the_drop_in_against_the_pin() {
    let root = fln_core::checked_workspace_root!();
    let write = std::env::var_os("FLN_UPSTREAM_LEDGER_WRITE").is_some();
    let (files, oracle, ledger) = load(&root, write);
    let Some(reference) = require_pin(&root, "upstream_suite_scoreboard") else {
        return;
    };
    let frankenlean = PathBuf::from(env!("CARGO_BIN_EXE_lean"));
    let copy = copy_suite(&root.join(SUITE));
    let mut pin = run_all(&reference, &copy, &files, WORKERS);
    let reuse = copy.join("fln-import-reuse");
    let host_dependent_exits = retry_drifted(&oracle, &mut pin, |file| {
        let (directory, name) = file.split_once('/').expect("dir/file");
        run(&reference, &copy.join(directory), name, &reuse)
    });
    eprintln!(
        "upstream_suite_scoreboard: pin exits that drifted under load and reproduced the oracle alone: {}",
        if host_dependent_exits.is_empty() {
            "none".to_owned()
        } else {
            host_dependent_exits.join(" ")
        }
    );
    let subject = run_subject(&frankenlean, &copy, &files, &oracle);
    // The copy is this run's own scratch tree, created above; nothing else is removed.
    let _ = std::fs::remove_dir_all(&copy);
    let report = score(&oracle, &ledger, &pin, &subject);
    for line in &report.lines {
        eprintln!("{line}");
    }
    eprintln!("{}", summary(&report));
    if report.problems.is_empty() && write {
        std::fs::write(root.join(LEDGER), render_ledger(&report.ledger)).expect("write the ledger");
        eprintln!(
            "upstream_suite_scoreboard: ledger advanced ({} improved)",
            report.improved.len()
        );
    }
    assert!(
        report.problems.is_empty(),
        "{} scoreboard problem(s):\n{}",
        report.problems.len(),
        report.problems.join("\n")
    );
}

/// The oracle's only writer. It runs the pinned binary twice per file, each pass from its own
/// copy of the suite, so a stdout that depends on the working directory or differs between
/// runs is `volatile`, by measurement; and the pinned header parser once.
#[ignore = "writes fixtures/upstream_suite/oracle.tsv from the pinned lean; run only for a pin or vendor change, with FLN_UPSTREAM_ORACLE_WRITE=1"]
#[test]
fn regenerate_the_upstream_oracle_from_the_pin() {
    let root = fln_core::checked_workspace_root!();
    if std::env::var_os("FLN_UPSTREAM_ORACLE_WRITE").is_none() {
        eprintln!("SKIP regenerate_the_upstream_oracle: FLN_UPSTREAM_ORACLE_WRITE is not set");
        return;
    }
    let (files, problems) = scan(&root.join(SUITE));
    assert!(problems.is_empty(), "{problems:?}");
    let reference = reference_lean(&root).expect("the pinned lean");
    let copy = copy_suite(&root.join(SUITE));
    let first = run_all(&reference, &copy, &files, WORKERS);
    let other_copy = copy_suite(&root.join(SUITE));
    let second = run_all(&reference, &other_copy, &files, WORKERS);
    // The second copy is this run's own scratch tree, created above.
    let _ = std::fs::remove_dir_all(&other_copy);
    let mut headers = BTreeMap::new();
    for (directory, _) in DIRECTORIES {
        let names: Vec<String> = files
            .iter()
            .filter_map(|file| {
                file.strip_prefix(&format!("{directory}/"))
                    .map(str::to_owned)
            })
            .collect();
        let output = Command::new(&reference)
            .arg("--run")
            .arg(root.join(HEADER_SCRIPT))
            .args(&names)
            .current_dir(copy.join(directory))
            .env_remove("LEAN_PATH")
            .output()
            .expect("run the header script");
        assert!(output.status.success(), "{output:?}");
        for line in String::from_utf8_lossy(&output.stdout).lines() {
            let Some(row) = line.strip_prefix("HEADER ") else {
                continue;
            };
            let fields: Vec<&str> = row.split('\t').collect();
            assert_eq!(fields.len(), 3, "{line}");
            headers.insert(
                format!("{directory}/{}", fields[0]),
                (fields[1].to_owned(), fields[2].to_owned()),
            );
        }
    }
    let rows: Vec<OracleRow> = files
        .iter()
        .map(|file| {
            let (one, two) = (&first[file], &second[file]);
            assert_eq!(
                one.exit, two.exit,
                "{file}: the pin's exit code differs between two runs; such a file cannot be scored"
            );
            let (kind, imports) = headers
                .get(file)
                .unwrap_or_else(|| panic!("{file}: no header row"));
            OracleRow {
                file: file.clone(),
                exit: one.exit,
                digest: digest(&one.stdout),
                volatile: one.stdout != two.stdout,
                kind: kind.clone(),
                imports: imports
                    .split(',')
                    .filter(|module| !module.is_empty())
                    .map(str::to_owned)
                    .collect(),
            }
        })
        .collect();
    // The first copy is this run's own scratch tree too; the header script ran in it.
    let _ = std::fs::remove_dir_all(&copy);
    std::fs::write(root.join(ORACLE), render_oracle(&rows)).expect("write the oracle");
    eprintln!("regenerate_the_upstream_oracle: {} rows", rows.len());
}

#[test]
fn the_checked_in_tables_name_exactly_the_upstream_suite() {
    let root = fln_core::checked_workspace_root!();
    let (files, oracle, ledger) = load(&root, false);
    assert_eq!(
        (files.len(), oracle.len(), ledger.len()),
        (3379, 3379, 3379)
    );
}

fn oracle_row(file: &str, exit: i32, stdout: &str) -> OracleRow {
    OracleRow {
        file: file.to_owned(),
        exit: Some(exit),
        digest: digest(stdout),
        volatile: false,
        kind: "implicit".to_owned(),
        imports: Vec::new(),
    }
}

fn ran(exit: Option<i32>, stdout: &str, stderr: &str) -> Run {
    Run {
        exit,
        stdout: stdout.to_owned(),
        stderr: stderr.to_owned(),
        millis: 0,
    }
}

fn ledger_row(file: &str, exit: Option<i32>, output: &str) -> LedgerRow {
    LedgerRow {
        file: file.to_owned(),
        exit,
        output: output.to_owned(),
        class: if exit == Some(0) { "accept" } else { "other" }.to_owned(),
    }
}

#[test]
fn a_planted_false_accept_fails_and_a_low_score_or_a_timeout_does_not() {
    let rejected = oracle_row(
        "elab_fail/bad.lean",
        1,
        "bad.lean:1:0: error: Type mismatch\n",
    );
    let accepted = oracle_row("elab/ok.lean", 0, "42\n");
    let oracle = vec![rejected.clone(), accepted.clone()];
    let ledger = vec![
        ledger_row("elab_fail/bad.lean", Some(1), "n/a"),
        ledger_row("elab/ok.lean", Some(1), "n/a"),
    ];
    let pin = BTreeMap::from([
        (
            "elab_fail/bad.lean".to_owned(),
            ran(Some(1), "bad.lean:1:0: error: Type mismatch\n", ""),
        ),
        ("elab/ok.lean".to_owned(), ran(Some(0), "42\n", "")),
    ]);
    // FrankenLean refuses everything, or never answers: a low score, not a failure.
    for subject_exit in [Some(1), None] {
        let subject = BTreeMap::from([
            ("elab_fail/bad.lean".to_owned(), ran(subject_exit, "", "")),
            ("elab/ok.lean".to_owned(), ran(subject_exit, "", "")),
        ]);
        let report = score(&oracle, &ledger, &pin, &subject);
        assert!(report.problems.is_empty(), "{:?}", report.problems);
        assert_eq!(report.per_directory["elab"].0, 0);
    }
    // A timeout is classed as such, never as acceptance.
    assert_eq!(refusal_class(&ran(None, "", "")), "timeout");
    // The planted file: FrankenLean accepts what the pin rejects.
    let subject = BTreeMap::from([
        ("elab_fail/bad.lean".to_owned(), ran(Some(0), "", "")),
        ("elab/ok.lean".to_owned(), ran(Some(0), "42\n", "")),
    ]);
    let report = score(&oracle, &ledger, &pin, &subject);
    assert_eq!(report.problems.len(), 1, "{:?}", report.problems);
    assert!(report.problems[0].starts_with("elab_fail/bad.lean: FrankenLean's `lean` accepts"));
    assert_eq!(report.per_directory["elab"], (1, 1, 1, 0, 0));
    assert_eq!(report.improved, vec!["elab/ok.lean".to_owned()]);
}

#[test]
fn a_planted_regression_of_an_identical_row_fails_the_ratchet() {
    let accepted = oracle_row("elab/ok.lean", 0, "42\n");
    let ledger = vec![ledger_row("elab/ok.lean", Some(0), "identical")];
    let pin = BTreeMap::from([("elab/ok.lean".to_owned(), ran(Some(0), "42\n", ""))]);
    for (exit, stdout) in [(Some(1), ""), (Some(0), "43\n"), (None, "")] {
        let subject = BTreeMap::from([("elab/ok.lean".to_owned(), ran(exit, stdout, ""))]);
        let report = score(std::slice::from_ref(&accepted), &ledger, &pin, &subject);
        assert_eq!(
            report.problems.len(),
            1,
            "{exit:?} {stdout:?}: {:?}",
            report.problems
        );
        assert!(
            report.problems[0].contains("regressed"),
            "{:?}",
            report.problems
        );
    }
    // A volatile row compares the exit code only.
    let mut volatile = accepted.clone();
    volatile.volatile = true;
    let subject = BTreeMap::from([("elab/ok.lean".to_owned(), ran(Some(0), "other\n", ""))]);
    let report = score(std::slice::from_ref(&volatile), &ledger, &pin, &subject);
    assert!(report.problems.is_empty(), "{:?}", report.problems);
}

#[test]
fn a_drifted_pin_exit_is_retried_once_and_only_a_reproduced_one_is_forgiven() {
    let rows = vec![
        oracle_row("elab/flaky.lean", 0, ""),
        oracle_row("elab/moved.lean", 0, ""),
        oracle_row("elab/steady.lean", 0, ""),
    ];
    let mut pin = BTreeMap::from([
        ("elab/flaky.lean".to_owned(), ran(Some(1), "", "")),
        ("elab/moved.lean".to_owned(), ran(Some(1), "", "")),
        ("elab/steady.lean".to_owned(), ran(Some(0), "", "")),
    ]);
    let mut reruns = Vec::new();
    let reproduced = retry_drifted(&rows, &mut pin, |file| {
        reruns.push(file.to_owned());
        ran(Some(if file == "elab/flaky.lean" { 0 } else { 1 }), "", "")
    });
    assert_eq!(
        reruns,
        ["elab/flaky.lean", "elab/moved.lean"],
        "only drifted files rerun"
    );
    assert_eq!(reproduced, ["elab/flaky.lean"]);
    let ledger: Vec<_> = rows
        .iter()
        .map(|row| ledger_row(&row.file, Some(1), "n/a"))
        .collect();
    let subject: BTreeMap<_, _> = rows
        .iter()
        .map(|row| (row.file.clone(), ran(Some(1), "", "")))
        .collect();
    let report = score(&rows, &ledger, &pin, &subject);
    assert_eq!(report.problems.len(), 1, "{:?}", report.problems);
    assert!(report.problems[0].starts_with("elab/moved.lean: the pinned Reference no longer"));
}

#[test]
fn pin_drift_and_broken_scans_are_refused() {
    let accepted = oracle_row("elab/ok.lean", 0, "42\n");
    let ledger = vec![ledger_row("elab/ok.lean", Some(1), "n/a")];
    let subject = BTreeMap::from([("elab/ok.lean".to_owned(), ran(Some(1), "", ""))]);
    // A changed exit code is verdict drift; a changed stdout under the same exit code is
    // host-dependent output, reported and not failed.
    let drifted = BTreeMap::from([("elab/ok.lean".to_owned(), ran(Some(1), "", ""))]);
    let report = score(std::slice::from_ref(&accepted), &ledger, &drifted, &subject);
    assert_eq!(report.problems.len(), 1, "{:?}", report.problems);
    assert!(report.problems[0].contains("no longer reproduces"));
    let host = BTreeMap::from([("elab/ok.lean".to_owned(), ran(Some(0), "43\n", ""))]);
    let report = score(std::slice::from_ref(&accepted), &ledger, &host, &subject);
    assert!(report.problems.is_empty(), "{:?}", report.problems);
    assert_eq!(report.host_dependent, vec!["elab/ok.lean".to_owned()]);

    // A file without rows, a row without a file, and a directory below its floor.
    let files = vec!["elab/ok.lean".to_owned(), "elab/new.lean".to_owned()];
    let oracle = vec![accepted.clone(), oracle_row("elab/gone.lean", 0, "")];
    let ledger = vec![ledger_row("elab/ok.lean", Some(1), "n/a")];
    let problems = scan_problems(&files, &oracle, &ledger);
    for needle in [
        "elab/new.lean has no oracle row",
        "elab/new.lean has no ledger row",
        "the oracle row for elab/gone.lean names no file",
        "elab: the scan found 2 files, below the floor",
        "elab_fail: the scan found 0 files",
        "compile: the scan found 0 files",
    ] {
        assert!(
            problems.iter().any(|problem| problem.contains(needle)),
            "{needle}: {problems:?}"
        );
    }
    // An unreadable suite directory is a problem, never an empty suite.
    let (files, problems) = scan(Path::new("/nonexistent-fln-upstream-suite"));
    assert!(files.is_empty());
    assert_eq!(problems.len(), DIRECTORIES.len(), "{problems:?}");
}

#[test]
fn an_unadmitted_init_bounds_its_closures_as_timeouts_never_acceptance() {
    let init = ran(None, "", "");
    let row = closure_timeout(&init);
    assert!(!row.accepts());
    assert_eq!(refusal_class(&row), "timeout");
    assert!(row.stderr.contains("`import Init`"), "{row:?}");
    let admitted = std::panic::catch_unwind(|| closure_timeout(&ran(Some(0), "", "")));
    assert!(admitted.is_err(), "an admitted Init bounds nothing");
}

#[test]
fn first_refusals_fall_into_the_closed_classes() {
    let refused = |stderr: &str| refusal_class(&ran(Some(1), "", stderr));
    let batch = "lean: execution: definition batch command 0 failed: frontend refused source: ";
    assert_eq!(
        refused(
            "lean: input: could not read source import closure: cannot resolve import `Lean` as Lean.lean below any bounded ancestor of entry a.lean"
        ),
        "import"
    );
    assert_eq!(
        refused(
            "lean: input: import `Mathlib` is neither a source file (/t/Mathlib.lean) nor an .olean on the search path [/lib/lean]"
        ),
        "import"
    );
    assert_eq!(
        refused(
            "lean: capability: this entry's imports do not reach `Init`, so the pin would print its #eval"
        ),
        "capability"
    );
    assert_eq!(
        refused(&format!(
            "{batch}parse refused source: lexical analysis reported 2 diagnostic(s); first byte 4: token"
        )),
        "lexer"
    );
    assert_eq!(
        refused(&format!(
            "{batch}parse refused source: source is outside the bounded source grammar at byte 7; expected DefinitionKeyword"
        )),
        "parser:DefinitionKeyword"
    );
    assert_eq!(
        refused(&format!(
            "{batch}parse refused source: source is outside the bounded source grammar at byte 7; expected ScalarValue"
        )),
        "parser:ScalarValue"
    );
    assert_eq!(
        refused(&format!("{batch}parse refused source: something else")),
        "parser:other"
    );
    assert_eq!(
        refused(&format!(
            "{batch}elaboration refused source: Unknown identifier `IO`"
        )),
        "unknown-name"
    );
    assert_eq!(
        refused("lean: execution: definition batch command 3 failed: unknown namespace `Foo`"),
        "unknown-name"
    );
    assert_eq!(
        refused(&format!(
            "{batch}elaboration refused source: constructor escapes its telescope"
        )),
        "elaboration"
    );
    assert_eq!(
        refused(
            "lean: execution: definition batch command 1 failed: cannot execute section variable or attribute command: no definition body"
        ),
        "other"
    );
    assert_eq!(refusal_class(&ran(Some(0), "", "")), "accept");
}

#[test]
fn strata_come_from_the_parsed_header() {
    let imports = |list: &[&str]| {
        list.iter()
            .map(|module| (*module).to_owned())
            .collect::<Vec<_>>()
    };
    assert_eq!(stratum("implicit", &[]), "no-header");
    assert_eq!(stratum("module-implicit", &[]), "no-header");
    assert_eq!(stratum("prelude", &[]), "prelude");
    assert_eq!(
        stratum("implicit", &imports(&["Std.Tactic.Do"])),
        "init-std-imports"
    );
    assert_eq!(
        stratum("implicit", &imports(&["Init.Data.List", "Std"])),
        "init-std-imports"
    );
    assert_eq!(
        stratum(
            "module-prelude",
            &imports(&["Lean.DefEqAttrib", "Init.Data.Nat.Basic"])
        ),
        "lean-imports"
    );
    assert_eq!(stratum("implicit", &imports(&["Lean"])), "lean-imports");
    assert_eq!(
        stratum("implicit", &imports(&["Mathlib.Tactic"])),
        "other-imports"
    );
    assert_eq!(stratum("implicit", &imports(&["Leanish"])), "other-imports");
    assert_eq!(stratum("unparsed", &[]), "unparsed-header");
    assert_eq!(stratum("unreadable", &[]), "unparsed-header");
}

#[test]
fn the_tables_round_trip_through_their_renderers() {
    let oracle = vec![
        OracleRow {
            file: "elab/a.lean".to_owned(),
            exit: Some(0),
            digest: digest("x\n"),
            volatile: true,
            kind: "module-prelude".to_owned(),
            imports: vec!["Lean.A".to_owned(), "Init".to_owned()],
        },
        OracleRow {
            file: "compile/b.lean".to_owned(),
            exit: None,
            digest: digest(""),
            volatile: false,
            kind: "implicit".to_owned(),
            imports: Vec::new(),
        },
    ];
    assert_eq!(parse_oracle(&render_oracle(&oracle)), Ok(oracle));
    let ledger = vec![
        ledger_row("elab/a.lean", Some(0), "identical"),
        ledger_row("compile/b.lean", None, "n/a"),
    ];
    assert_eq!(parse_ledger(&render_ledger(&ledger)), Ok(ledger));
    assert!(parse_ledger("elab/a.lean\t0\tmaybe\taccept\n").is_err());
}
