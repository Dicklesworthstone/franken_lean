//! KERNEL_CONTRACT.md is CI-checked like code (bead franken_lean-79k):
//!
//! * **anchor resolution** — every cited Reference source location must exist at the
//!   pin, lie **inside the pinned vendor tree** (`vendor/lean4-src/`, never our own
//!   code), and carry its `expect="token"` on that exact line — drift fails;
//! * **coverage** — every rule names at least one fixture, or an explicit stub whose
//!   owner is a **real, tracked bead** — no silently unevidenced rule, no phantom
//!   owner;
//! * **terminal inventory join** — the bounded coverage matrix names every contract
//!   rule exactly once, in contract order, with the exact title and a typed evidence
//!   state; an implemented row cannot silently become uncovered and a not-yet-
//!   implemented row must name its production owner and policy;
//! * **ledger linkage** — every Parity-Ledger row on the `kernel` surface must name
//!   an existing rule id as its symbol — a dangling link fails.
//!
//! Rule-block grammar the checker parses (inside the markdown):
//!
//! ```text
//! ### KR-NNN · <title>
//! anchor: <repo-relative-path>:<line> (<function>) expect="<token>"
//! fixtures: <path>[, <path>...]        OR   fixtures: stub owner=<bead-id>
//! ```
//!
//! A rule may carry several `anchor:` lines; every one is resolved.
//!
//! The production validation is one function, [`validate`], exercised by the real
//! contract AND by the planted-drift/gap test — so weakening any check here fails
//! the mutation test, not just the (real) contract that happens to be clean today.

#![forbid(unsafe_code)]

use fln_conformance::ownership::{
    ExpectedManifestBinding, InputUsage, MANIFEST_RELATIVE_PATH, OwnershipEvidence,
    OwnershipFailure, OwnershipFailureClass, OwnershipLimits, OwnershipSourceMode,
    OwnershipSourceState, OwnershipUsage, SOURCE_RELATIVE_PATH, load_kernel_contract_ownership,
};
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// The pinned Reference source tree. Every kernel-rule anchor must live here: a rule
/// "anchored" to our own code or anything outside the pin proves nothing.
const PIN_TREE_PREFIX: &str = "vendor/lean4-src/";
const JUDGMENT_COVERAGE_RELATIVE_PATH: &str = "tribunal/fixtures/c3/JUDGMENT_INVENTORY_COVERAGE.md";

fn workspace_root() -> &'static Path {
    static ROOT: OnceLock<PathBuf> = OnceLock::new();
    ROOT.get_or_init(|| {
        let current = env::current_dir().expect("current directory");
        current
            .ancestors()
            .find(|candidate| {
                candidate.join("KERNEL_CONTRACT.md").is_file()
                    && candidate
                        .join("crates/fln-conformance/Cargo.toml")
                        .is_file()
            })
            .map(Path::to_path_buf)
            .expect("workspace root above the test working directory")
    })
    .as_path()
}

/// The full production validation of the parsed rule set against the workspace: the
/// single source of truth both the real-contract test and the planted-mutation test
/// run, so no check can be silently deleted without a test going red.
fn validate(rules: &[Rule], root: &Path) -> Vec<String> {
    let required_owners = required_stub_owners(rules);
    let ownership = load_kernel_contract_ownership(
        root,
        &required_owners,
        OwnershipSourceMode::RequireSource,
        OwnershipLimits::default(),
    );
    validate_with_ownership(rules, root, ownership)
}

fn required_stub_owners(rules: &[Rule]) -> BTreeSet<String> {
    rules
        .iter()
        .filter_map(|rule| rule.stub_owner.clone())
        .collect()
}

fn validate_with_ownership(
    rules: &[Rule],
    root: &Path,
    ownership: Result<OwnershipEvidence, OwnershipFailure>,
) -> Vec<String> {
    let mut failures: Vec<String> = Vec::new();
    let mut ids = BTreeSet::new();
    if let Err(error) = &ownership {
        failures.push(error.diagnostic());
    }
    for rule in rules {
        if !ids.insert(rule.id.clone()) {
            failures.push(format!("{}: duplicate rule id", rule.id));
        }
        if rule.anchors.is_empty() {
            failures.push(format!("{}: no Reference anchor", rule.id));
        }
        for (cited_line, path_token) in &rule.anchors {
            let (path, token) = path_token.split_once('|').expect("packed in parse");
            if !path.starts_with(PIN_TREE_PREFIX) {
                failures.push(format!(
                    "{}: anchor `{path}` is outside the pinned tree `{PIN_TREE_PREFIX}`",
                    rule.id
                ));
                continue;
            }
            let source = match fs::read_to_string(root.join(path)) {
                Ok(source) => source,
                Err(_) => {
                    failures.push(format!("{}: anchor file `{path}` missing", rule.id));
                    continue;
                }
            };
            match source.lines().nth(cited_line - 1) {
                None => failures.push(format!(
                    "{}: anchor {path}:{cited_line} beyond end of file",
                    rule.id
                )),
                Some(line) if !line.contains(token) => failures.push(format!(
                    "{}: anchor {path}:{cited_line} drifted — expected `{token}`, line is `{}`",
                    rule.id,
                    line.trim()
                )),
                Some(_) => {}
            }
        }
        // Coverage: fixtures exist, or an explicit stub whose owner is a real bead.
        if rule.fixtures.is_empty() && rule.stub_owner.is_none() {
            failures.push(format!(
                "{}: neither fixtures nor a stub owner (heading line {})",
                rule.id, rule.heading_line
            ));
        }
        if let (Some(owner), Ok(evidence)) = (&rule.stub_owner, &ownership)
            && !evidence.owners().contains(owner)
        {
            failures.push(format!(
                "{}: stub owner `{owner}` is not a tracked bead",
                rule.id
            ));
        }
        for fixture in &rule.fixtures {
            if !root.join(fixture).exists() {
                failures.push(format!("{}: fixture `{fixture}` missing", rule.id));
            }
        }
    }
    failures
}

#[derive(Clone, Debug, Default)]
struct Rule {
    id: String,
    title: String,
    heading_line: usize,
    anchors: Vec<(usize, String)>,
    fixtures: Vec<String>,
    stub_owner: Option<String>,
}

fn parse_rules(text: &str) -> (Vec<Rule>, Vec<String>) {
    let mut rules: Vec<Rule> = Vec::new();
    let mut problems: Vec<String> = Vec::new();
    for (idx, line) in text.lines().enumerate() {
        let lineno = idx + 1;
        if let Some(rest) = line.strip_prefix("### ") {
            if let Some(id) = rest.split_whitespace().next()
                && id.starts_with("KR-")
            {
                let title = rest
                    .split_once('·')
                    .map(|(_, title)| title.trim().to_string())
                    .unwrap_or_default();
                rules.push(Rule {
                    id: id.to_string(),
                    title,
                    heading_line: lineno,
                    ..Rule::default()
                });
            }
            continue;
        }
        let Some(rule) = rules.last_mut() else {
            continue;
        };
        if let Some(anchor) = line.trim().strip_prefix("anchor: ") {
            rules_push_anchor(rule, anchor, lineno, &mut problems);
        } else if let Some(fixtures) = line.trim().strip_prefix("fixtures: ") {
            if let Some(owner_part) = fixtures.strip_prefix("stub owner=") {
                let owner = owner_part.trim();
                if owner.is_empty() {
                    problems.push(format!("line {lineno}: stub without an owner"));
                } else {
                    rule.stub_owner = Some(owner.to_string());
                }
            } else {
                rule.fixtures.extend(
                    fixtures
                        .split(',')
                        .map(str::trim)
                        .filter(|s| !s.is_empty())
                        .map(str::to_string),
                );
            }
        }
    }
    (rules, problems)
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CoverageRow {
    id: String,
    title: String,
    real_module: String,
    fixture: String,
    model: String,
    status: String,
    line: usize,
}

fn parse_coverage_rows(text: &str) -> (Vec<CoverageRow>, Vec<String>) {
    let mut rows = Vec::new();
    let mut problems = Vec::new();
    for (index, raw_line) in text.lines().enumerate() {
        let line = raw_line.trim();
        if !line.starts_with("| KR-") {
            continue;
        }
        let Some(cells) = line
            .strip_prefix('|')
            .and_then(|line| line.strip_suffix('|'))
        else {
            problems.push(format!(
                "line {}: coverage row must start and end with `|`",
                index + 1
            ));
            continue;
        };
        let cells: Vec<&str> = cells.split('|').map(str::trim).collect();
        if cells.len() != 6 {
            problems.push(format!(
                "line {}: coverage row has {} columns, expected 6",
                index + 1,
                cells.len()
            ));
            continue;
        }
        let id = cells[0];
        if id.len() != 6
            || !id.starts_with("KR-")
            || !id.as_bytes()[3..].iter().all(u8::is_ascii_digit)
        {
            problems.push(format!(
                "line {}: malformed coverage rule id `{id}`",
                index + 1
            ));
            continue;
        }
        rows.push(CoverageRow {
            id: id.to_string(),
            title: cells[1].to_string(),
            real_module: cells[2].to_string(),
            fixture: cells[3].to_string(),
            model: cells[4].to_string(),
            status: cells[5].to_string(),
            line: index + 1,
        });
    }
    (rows, problems)
}

fn is_evidence_cell(value: &str) -> bool {
    !value.is_empty() && value != "—"
}

fn required_coverage_owners(rows: &[CoverageRow]) -> BTreeSet<String> {
    const OWNED_STATES: [&str; 2] = [
        "implemented-but-uncovered owner=",
        "not-yet-implemented owner=",
    ];
    rows.iter()
        .filter_map(|row| {
            OWNED_STATES.iter().find_map(|prefix| {
                row.status
                    .strip_prefix(prefix)
                    .and_then(|rest| rest.split_once(" — "))
                    .map(|(owner, _)| owner.to_string())
            })
        })
        .collect()
}

fn validate_owned_coverage_state(
    row: &CoverageRow,
    prefix: &str,
    tracked_owners: &BTreeSet<String>,
) -> Vec<String> {
    let mut findings = Vec::new();
    let Some(rest) = row.status.strip_prefix(prefix) else {
        return findings;
    };
    let Some((owner, policy)) = rest.split_once(" — ") else {
        findings.push(format!(
            "{}: `{}` status must name `owner=<bead> — <policy>`",
            row.id,
            prefix.trim_end_matches(" owner=")
        ));
        return findings;
    };
    if owner.is_empty() || policy.is_empty() {
        findings.push(format!(
            "{}: owned coverage status has an empty owner or policy",
            row.id
        ));
    } else if !tracked_owners.contains(owner) {
        findings.push(format!(
            "{}: coverage owner `{owner}` is not a tracked bead",
            row.id
        ));
    }
    findings
}

fn validate_coverage_status(row: &CoverageRow, tracked_owners: &BTreeSet<String>) -> Vec<String> {
    let mut findings = Vec::new();
    let has_real_module = is_evidence_cell(&row.real_module);
    let has_public_fixture = is_evidence_cell(&row.fixture) || is_evidence_cell(&row.model);
    let has_any_evidence = has_real_module || has_public_fixture;
    match row.status.as_str() {
        "implemented-and-covered" => {
            if !has_public_fixture {
                findings.push(format!(
                    "{}: status `{}` has no public fixture or model cell",
                    row.id, row.status
                ));
            }
        }
        "structurally-enforced" => {
            if !has_public_fixture {
                findings.push(format!(
                    "{}: structurally-enforced row has no named enforcement fixture",
                    row.id
                ));
            }
        }
        status => {
            if status.starts_with("implemented-but-uncovered owner=") {
                findings.extend(validate_owned_coverage_state(
                    row,
                    "implemented-but-uncovered owner=",
                    tracked_owners,
                ));
                if is_evidence_cell(&row.fixture) {
                    findings.push(format!(
                        "{}: implemented-but-uncovered row must not name a C0 fixture",
                        row.id
                    ));
                }
                return findings;
            }
            if status.starts_with("not-yet-implemented owner=") {
                findings.extend(validate_owned_coverage_state(
                    row,
                    "not-yet-implemented owner=",
                    tracked_owners,
                ));
                if has_any_evidence {
                    findings.push(format!(
                        "{}: not-yet-implemented row must not claim exercised evidence",
                        row.id
                    ));
                }
                return findings;
            }
            if status.starts_with("implemented-but-uncovered")
                || status.starts_with("not-yet-implemented")
            {
                findings.push(format!(
                    "{}: unsupported coverage status `{status}`",
                    row.id
                ));
                return findings;
            }
            findings.push(format!(
                "{}: unsupported coverage status `{status}`",
                row.id
            ));
        }
    }
    findings
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TestReference {
    target: String,
    test: String,
}

fn is_rust_identifier(value: &str) -> bool {
    let mut bytes = value.bytes();
    bytes
        .next()
        .is_some_and(|byte| byte == b'_' || byte.is_ascii_alphabetic())
        && bytes.all(|byte| byte == b'_' || byte.is_ascii_alphanumeric())
}

fn parse_test_references(
    row: &CoverageRow,
    label: &str,
    value: &str,
) -> (Vec<TestReference>, Vec<String>) {
    if !is_evidence_cell(value) {
        return (Vec::new(), Vec::new());
    }
    let mut references = Vec::new();
    let mut findings = Vec::new();
    for raw in value.split(';') {
        let reference = raw.trim();
        let Some((target, test)) = reference.split_once("::") else {
            findings.push(format!(
                "{}: {label} reference `{reference}` must be `<test-target>::<test-name>`",
                row.id
            ));
            continue;
        };
        if test.contains("::") || !is_rust_identifier(target) || !is_rust_identifier(test) {
            findings.push(format!(
                "{}: malformed {label} test reference `{reference}`",
                row.id
            ));
            continue;
        }
        references.push(TestReference {
            target: target.to_string(),
            test: test.to_string(),
        });
    }
    (references, findings)
}

fn test_functions(source: &str) -> BTreeSet<String> {
    let mut tests = BTreeSet::new();
    let mut has_test_attribute = false;
    for line in source.lines() {
        let line = line.trim();
        if line == "#[test]" {
            has_test_attribute = true;
            continue;
        }
        if let Some(rest) = line.strip_prefix("fn ") {
            if has_test_attribute
                && let Some((name, _)) = rest.split_once('(')
                && is_rust_identifier(name)
            {
                tests.insert(name.to_string());
            }
            has_test_attribute = false;
        } else if !line.is_empty() && !line.starts_with("#[") && !line.starts_with("//") {
            has_test_attribute = false;
        }
    }
    tests
}

fn test_reference_findings(rows: &[CoverageRow], root: &Path) -> Vec<String> {
    let mut findings = Vec::new();
    let mut registry: BTreeMap<String, Option<BTreeSet<String>>> = BTreeMap::new();
    for row in rows {
        for (label, value) in [("C0", row.fixture.as_str()), ("model", row.model.as_str())] {
            let (references, parse_findings) = parse_test_references(row, label, value);
            findings.extend(parse_findings);
            for reference in references {
                let tests = registry.entry(reference.target.clone()).or_insert_with(|| {
                    let path =
                        root.join(format!("crates/fln-kernel/tests/{}.rs", reference.target));
                    fs::read_to_string(path)
                        .ok()
                        .map(|source| test_functions(&source))
                });
                let Some(tests) = tests else {
                    findings.push(format!(
                        "{}: {label} target `{}` does not exist under crates/fln-kernel/tests",
                        row.id, reference.target
                    ));
                    continue;
                };
                if !tests.contains(&reference.test) {
                    findings.push(format!(
                        "{}: {label} test `{}::{}` does not exist or is not #[test]",
                        row.id, reference.target, reference.test
                    ));
                }
            }
        }
    }
    findings
}

fn coverage_findings(
    rules: &[Rule],
    rows: &[CoverageRow],
    tracked_owners: &BTreeSet<String>,
) -> Vec<String> {
    let mut findings = Vec::new();
    let mut by_id: BTreeMap<&str, &CoverageRow> = BTreeMap::new();
    for row in rows {
        if let Some(first) = by_id.insert(row.id.as_str(), row) {
            findings.push(format!(
                "{}: duplicate coverage rows at lines {} and {}",
                row.id, first.line, row.line
            ));
        }
        findings.extend(validate_coverage_status(row, tracked_owners));
    }

    let rule_ids: BTreeSet<&str> = rules.iter().map(|rule| rule.id.as_str()).collect();
    for rule in rules {
        let Some(row) = by_id.get(rule.id.as_str()) else {
            findings.push(format!("{}: missing from judgment coverage", rule.id));
            continue;
        };
        if row.title != rule.title {
            findings.push(format!(
                "{}: coverage title drifted — contract `{}`, coverage `{}`",
                rule.id, rule.title, row.title
            ));
        }
    }
    for row in rows {
        if !rule_ids.contains(row.id.as_str()) {
            findings.push(format!("{}: coverage row has no contract rule", row.id));
        }
    }

    let contract_order: Vec<&str> = rules.iter().map(|rule| rule.id.as_str()).collect();
    let coverage_order: Vec<&str> = rows.iter().map(|row| row.id.as_str()).collect();
    if contract_order != coverage_order {
        findings.push("judgment coverage order differs from KERNEL_CONTRACT.md".to_string());
    }
    findings
}

fn rules_push_anchor(rule: &mut Rule, anchor: &str, lineno: usize, problems: &mut Vec<String>) {
    // `<path>:<line> (<function>) expect="<token>"` — function is informative,
    // path/line/token are checked.
    let Some((location, tail)) = anchor.split_once(' ') else {
        problems.push(format!("line {lineno}: malformed anchor `{anchor}`"));
        return;
    };
    let Some((path, line_str)) = location.rsplit_once(':') else {
        problems.push(format!("line {lineno}: anchor without a line number"));
        return;
    };
    let Ok(cited_line) = line_str.parse::<usize>() else {
        problems.push(format!("line {lineno}: non-numeric anchor line"));
        return;
    };
    if cited_line == 0 {
        // Source line numbers are 1-based; `:0` is malformed (and would underflow
        // the `cited_line - 1` index in `validate`).
        problems.push(format!("line {lineno}: anchor line number must be >= 1"));
        return;
    }
    let token = tail
        .split_once("expect=\"")
        .and_then(|(_, rest)| rest.split_once('"'))
        .map(|(token, _)| token.to_string());
    let Some(token) = token else {
        problems.push(format!(
            "line {lineno}: anchor for {} lacks expect=\"token\"",
            rule.id
        ));
        return;
    };
    rule.anchors.push((cited_line, format!("{path}|{token}")));
}

#[test]
fn the_judgment_inventory_test_references_resolve() {
    let root = workspace_root();
    let coverage =
        fs::read_to_string(root.join(JUDGMENT_COVERAGE_RELATIVE_PATH)).expect("coverage exists");
    let (rows, problems) = parse_coverage_rows(&coverage);
    assert!(
        problems.is_empty(),
        "coverage parse problems:\n{}",
        problems.join("\n")
    );
    let findings = test_reference_findings(&rows, root);
    assert!(
        findings.is_empty(),
        "{} judgment-inventory test-reference finding(s):\n{}",
        findings.len(),
        findings.join("\n")
    );
}

#[test]
fn the_judgment_inventory_matches_the_contract_exactly() {
    let root = workspace_root();
    let contract = fs::read_to_string(root.join("KERNEL_CONTRACT.md")).expect("contract exists");
    let coverage =
        fs::read_to_string(root.join(JUDGMENT_COVERAGE_RELATIVE_PATH)).expect("coverage exists");
    let (rules, contract_problems) = parse_rules(&contract);
    let (rows, coverage_problems) = parse_coverage_rows(&coverage);
    assert!(
        contract_problems.is_empty() && coverage_problems.is_empty(),
        "inventory parse problems:\n{}",
        contract_problems
            .into_iter()
            .chain(coverage_problems)
            .collect::<Vec<_>>()
            .join("\n")
    );
    let required_owners = required_coverage_owners(&rows);
    let findings = match load_kernel_contract_ownership(
        root,
        &required_owners,
        OwnershipSourceMode::RequireSource,
        OwnershipLimits::default(),
    ) {
        Ok(evidence) => coverage_findings(&rules, &rows, evidence.owners()),
        Err(error) => vec![error.diagnostic()],
    };
    let findings = findings
        .into_iter()
        .chain(test_reference_findings(&rows, root))
        .collect::<Vec<_>>();
    assert!(
        findings.is_empty(),
        "{} judgment-inventory finding(s):\n{}",
        findings.len(),
        findings.join("\n")
    );
}

#[test]
fn the_judgment_inventory_join_rejects_missing_duplicate_drift_and_vacuity() {
    let rule = Rule {
        id: "KR-100".to_string(),
        title: "One rule".to_string(),
        ..Rule::default()
    };
    let row = CoverageRow {
        id: rule.id.clone(),
        title: rule.title.clone(),
        real_module: "—".to_string(),
        fixture: "named_public_authority_test".to_string(),
        model: "—".to_string(),
        status: "implemented-and-covered".to_string(),
        line: 10,
    };
    let tracked_owners = BTreeSet::from(["franken_lean-zht".to_string()]);
    assert!(
        coverage_findings(
            core::slice::from_ref(&rule),
            core::slice::from_ref(&row),
            &tracked_owners
        )
        .is_empty(),
        "the positive control must pass"
    );

    let has =
        |findings: &[String], needle: &str| findings.iter().any(|finding| finding.contains(needle));
    assert!(
        has(
            &coverage_findings(core::slice::from_ref(&rule), &[], &tracked_owners),
            "missing"
        ),
        "a missing rule row must fail"
    );
    assert!(
        has(
            &coverage_findings(
                core::slice::from_ref(&rule),
                &[row.clone(), row.clone()],
                &tracked_owners
            ),
            "duplicate"
        ),
        "a duplicate rule row must fail"
    );

    let mut extra = row.clone();
    extra.id = "KR-999".to_string();
    assert!(
        has(
            &coverage_findings(
                core::slice::from_ref(&rule),
                &[row.clone(), extra],
                &tracked_owners
            ),
            "no contract rule"
        ),
        "an extra rule row must fail"
    );

    let mut title_drift = row.clone();
    title_drift.title = "A different rule".to_string();
    assert!(
        has(
            &coverage_findings(
                core::slice::from_ref(&rule),
                &[title_drift],
                &tracked_owners
            ),
            "title drifted"
        ),
        "a stale title must fail"
    );

    let mut vacuous = row.clone();
    vacuous.real_module = "—".to_string();
    vacuous.fixture = "—".to_string();
    vacuous.model = "—".to_string();
    assert!(
        has(
            &coverage_findings(core::slice::from_ref(&rule), &[vacuous], &tracked_owners),
            "no public fixture"
        ),
        "an implemented-but-uncovered row must fail"
    );

    let mut untyped = row.clone();
    untyped.status = "**BLOCKER: later**".to_string();
    assert!(
        has(
            &coverage_findings(core::slice::from_ref(&rule), &[untyped], &tracked_owners),
            "unsupported coverage status"
        ),
        "a prose-only status must fail"
    );

    let not_implemented = CoverageRow {
        real_module: "—".to_string(),
        fixture: "—".to_string(),
        model: "—".to_string(),
        status: "not-yet-implemented owner=franken_lean-zht — scheduled production slice"
            .to_string(),
        ..row.clone()
    };
    assert!(
        coverage_findings(
            core::slice::from_ref(&rule),
            core::slice::from_ref(&not_implemented),
            &tracked_owners
        )
        .is_empty(),
        "a typed, owned not-yet-implemented row is honest and valid"
    );

    let phantom = CoverageRow {
        status:
            "not-yet-implemented owner=franken_lean-nonexistent-ZZZ — invented ownership must fail"
                .to_string(),
        ..not_implemented.clone()
    };
    assert!(
        has(
            &coverage_findings(core::slice::from_ref(&rule), &[phantom], &tracked_owners),
            "not a tracked bead"
        ),
        "an owned gap must not accept a phantom production owner"
    );

    let uncovered = CoverageRow {
        real_module: "P S M C3".to_string(),
        fixture: "—".to_string(),
        status: "implemented-but-uncovered owner=franken_lean-zht — external replay is not a discriminating public fixture"
            .to_string(),
        ..row.clone()
    };
    assert!(
        coverage_findings(
            core::slice::from_ref(&rule),
            core::slice::from_ref(&uncovered),
            &tracked_owners
        )
        .is_empty(),
        "an implemented gap may stay explicit while its external replay remains visible"
    );

    let mut generic_fixture = row.clone();
    generic_fixture.fixture = "k1_judgments (two anchors)".to_string();
    assert!(
        !parse_test_references(&generic_fixture, "C0", &generic_fixture.fixture)
            .1
            .is_empty(),
        "a prose fixture label must not masquerade as a bound test"
    );

    let mut missing_test = row;
    missing_test.fixture = "k1_judgments::definitely_not_a_real_test".to_string();
    assert!(
        has(
            &test_reference_findings(core::slice::from_ref(&missing_test), workspace_root()),
            "does not exist"
        ),
        "a stale canonical test reference must fail against the real test target"
    );
}

#[test]
fn the_contract_parses_resolves_and_covers() {
    let root = workspace_root();
    let text = fs::read_to_string(root.join("KERNEL_CONTRACT.md")).expect("contract exists");
    let (rules, problems) = parse_rules(&text);
    assert!(
        problems.is_empty(),
        "malformed rule blocks:\n{}",
        problems.join("\n")
    );
    assert!(
        rules.len() >= 30,
        "the judgment inventory is present ({} rules)",
        rules.len()
    );

    let failures = validate(&rules, root);
    assert!(
        failures.is_empty(),
        "{} contract check failure(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// One `git` invocation, with the same panic posture as the anchor guard: no
/// git means no history to check and the answer is typed, not faked.
fn git(root: &Path, args: &[&str]) -> String {
    let out = std::process::Command::new("git")
        .current_dir(root)
        .args(args)
        .output()
        .expect("git must run for the revision-discipline check");
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// The revision discipline's judge, split out so planted histories exercise the
/// same function the live history runs (79k gap 2: a commit touching a rule
/// statement must touch a linked fixture in the same change).
fn revision_findings(
    edits: &[(String, Vec<String>)],
    fixture_paths: &BTreeSet<String>,
    introduction: &str,
) -> Vec<String> {
    let mut findings = Vec::new();
    for (sha, files) in edits {
        if sha == introduction {
            continue; // the introduction creates the contract and its fixtures together
        }
        if !files.iter().any(|f| fixture_paths.contains(f)) {
            findings.push(format!(
                "{sha}: touched KERNEL_CONTRACT.md without touching any linked fixture"
            ));
        }
    }
    findings
}

#[test]
fn the_revision_discipline_binds_contract_edits_to_fixtures() {
    let root = workspace_root();
    let text = fs::read_to_string(root.join("KERNEL_CONTRACT.md")).expect("contract exists");
    let (rules, _) = parse_rules(&text);
    let fixture_paths: BTreeSet<String> = rules
        .iter()
        .flat_map(|rule| rule.fixtures.iter().cloned())
        .collect();
    assert!(
        !fixture_paths.is_empty(),
        "the contract must name real fixture paths for the discipline to bind"
    );

    // Planted controls through the same judge the live history runs: a
    // fixtureless edit must be flagged, and a fixture-touching edit must pass.
    let fake_sha = "deadbeefcafe".to_string();
    let planted = revision_findings(
        &[
            (fake_sha.clone(), vec!["KERNEL_CONTRACT.md".to_string()]),
            (
                "cafebead".to_string(),
                vec![
                    "KERNEL_CONTRACT.md".to_string(),
                    "crates/fln-kernel/tests/k1_judgments.rs".to_string(),
                ],
            ),
        ],
        &fixture_paths,
        "introduction-sha",
    );
    assert!(
        planted.iter().any(|finding| finding.contains(&fake_sha)),
        "a fixtureless contract edit must be flagged by the production judge"
    );
    assert_eq!(
        planted.len(),
        1,
        "a fixture-touching edit must pass the production judge"
    );

    // The live history: every post-introduction contract edit carries a linked
    // fixture, by construction of the introduction exemption.
    let introduction = git(
        root,
        &[
            "log",
            "--format=%H",
            "--reverse",
            "--",
            "KERNEL_CONTRACT.md",
        ],
    )
    .lines()
    .next()
    .expect("the contract has an introduction commit")
    .to_string();
    let log = git(root, &["log", "--format=%H", "--", "KERNEL_CONTRACT.md"]);
    let edits: Vec<(String, Vec<String>)> = log
        .lines()
        .map(|sha| {
            let files = git(
                root,
                &["diff-tree", "--no-commit-id", "--name-only", "-r", sha],
            )
            .lines()
            .map(str::to_string)
            .collect();
            (sha.to_string(), files)
        })
        .collect();
    assert!(
        !edits.is_empty(),
        "the contract has an edit history the discipline must walk"
    );
    let findings = revision_findings(&edits, &fixture_paths, &introduction);
    assert!(
        findings.is_empty(),
        "revision discipline violations:\n{}",
        findings.join("\n")
    );
}

#[test]
fn kernel_surface_ledger_rows_link_to_existing_rules() {
    let root = workspace_root();
    let contract = fs::read_to_string(root.join("KERNEL_CONTRACT.md")).expect("contract exists");
    let (rules, _) = parse_rules(&contract);
    let ids: BTreeSet<&str> = rules.iter().map(|r| r.id.as_str()).collect();

    let ledger_text = fs::read_to_string(root.join("ci/PARITY_LEDGER.txt")).expect("ledger exists");
    let ledger = fln_conformance::ledger::parse(&ledger_text).expect("ledger parses");
    for row in &ledger.rows {
        if row.surface == "kernel" {
            assert!(
                ids.contains(row.symbol.as_str()),
                "kernel ledger row `{}` does not name an existing KR- rule id",
                row.symbol
            );
        }
    }
}

#[test]
fn the_checker_detects_planted_drift_and_gaps() {
    // Every planted defect is fed through the REAL `validate` — the same function the
    // contract itself runs — so deleting or weakening a production check turns these
    // assertions red, not just the (currently clean) contract. A test that merely
    // reasserts the property inline would leave the production check unprotected.
    let root = workspace_root();

    let has = |failures: &[String], needle: &str| failures.iter().any(|f| f.contains(needle));

    // Planted drift: a real pin file, but the expect token is not on the cited line.
    let (rules, problems) = parse_rules(
        "### KR-999 · drift\n\
         anchor: vendor/lean4-src/src/kernel/type_checker.cpp:609 (x) expect=\"no-such-token-ZZZ\"\n\
         fixtures: stub owner=franken_lean-z6c\n",
    );
    assert!(problems.is_empty());
    assert!(
        has(&validate(&rules, root), "drifted"),
        "the production anchor-drift check must fire on planted drift"
    );

    // Malformed :0 anchor line is a parse-time problem, never a panic (a 1-based
    // line of 0 would otherwise underflow the `cited_line - 1` index in validate).
    let (_, problems) = parse_rules(
        "### KR-000 · zero\n\
         anchor: vendor/lean4-src/src/kernel/type_checker.cpp:0 (x) expect=\"reduce_nat\"\n",
    );
    assert!(
        problems.iter().any(|p| p.contains("must be >= 1")),
        "a :0 anchor line must be flagged, not panic"
    );

    // Planted off-pin anchor: resolves fine, but points outside the pinned tree.
    let (rules, _) = parse_rules(
        "### KR-996 · offpin\n\
         anchor: SUITE.lock:1 (x) expect=\"schema\"\n\
         fixtures: stub owner=franken_lean-z6c\n",
    );
    assert!(
        has(&validate(&rules, root), "outside the pinned tree"),
        "an anchor outside vendor/lean4-src must be rejected even when it resolves"
    );

    // Planted phantom owner: a stub whose owner is not a tracked bead.
    let (rules, _) = parse_rules(
        "### KR-995 · phantom\n\
         anchor: vendor/lean4-src/src/kernel/type_checker.cpp:609 (x) expect=\"reduce_nat\"\n\
         fixtures: stub owner=franken_lean-nonexistent-ZZZ\n",
    );
    assert!(
        has(&validate(&rules, root), "[bead-evidence/phantom-owner]"),
        "a stub owner that names no real bead must be rejected"
    );

    // Planted gap: a rule with neither fixtures nor stub.
    let (rules, _) = parse_rules(
        "### KR-998 · gap\nanchor: vendor/lean4-src/src/kernel/type_checker.cpp:609 (x) expect=\"reduce_nat\"\n",
    );
    assert!(
        has(&validate(&rules, root), "neither fixtures nor a stub owner"),
        "a rule with no evidence must be rejected"
    );

    // A fully-correct planted rule must pass `validate` clean — the checks are
    // discriminating, not blanket-failing.
    let (rules, _) = parse_rules(
        "### KR-994 · clean\n\
         anchor: vendor/lean4-src/src/kernel/type_checker.cpp:609 (x) expect=\"reduce_nat\"\n\
         fixtures: stub owner=franken_lean-z6c\n",
    );
    assert!(
        validate(&rules, root).is_empty(),
        "a well-formed rule must pass validation cleanly"
    );

    // Malformed stub (owner required) is caught at parse time.
    let (_, problems) = parse_rules("### KR-997 · bad\nfixtures: stub owner=\n");
    assert!(problems.iter().any(|p| p.contains("stub without an owner")));
}

#[test]
fn bead_ownership_evidence_failures_are_typed_and_fail_closed() {
    let root = workspace_root();
    let (rules, problems) = parse_rules(
        "### KR-993 · ownership evidence\n\
         anchor: vendor/lean4-src/src/kernel/type_checker.cpp:609 (x) expect=\"reduce_nat\"\n\
         fixtures: stub owner=franken_lean-z6c\n",
    );
    assert!(problems.is_empty());
    let required = required_stub_owners(&rules);

    let missing = load_kernel_contract_ownership(
        Path::new("/evidence-root-that-does-not-exist"),
        &required,
        OwnershipSourceMode::RequireSource,
        OwnershipLimits::default(),
    );
    let error = missing.as_ref().expect_err("missing evidence must refuse");
    assert_eq!(error.class(), OwnershipFailureClass::Missing);
    assert_eq!(error.binding(), None, "a missing input leaked a binding");
    let failures = validate_with_ownership(&rules, root, missing);
    assert!(
        failures.iter().any(|failure| {
            failure.contains("[bead-evidence/missing]") && failure.contains(MANIFEST_RELATIVE_PATH)
        }),
        "typed ownership failure must preserve class and path: {failures:?}"
    );

    let tracked = load_kernel_contract_ownership(
        root,
        &required,
        OwnershipSourceMode::RequireSource,
        OwnershipLimits::default(),
    );
    assert!(
        validate_with_ownership(&rules, root, tracked).is_empty(),
        "a real owner in valid evidence must pass the production validator"
    );
}

const OWNERSHIP_RESULT_SCHEMA: &str = "fln.kernel-contract-ownership-result/1";
const OWNERSHIP_PROBE_SCHEMA: &str = "fln.kernel-contract-ownership-probe/1";

struct DriverConfiguration {
    root: PathBuf,
    required_owners: BTreeSet<String>,
    source_mode: OwnershipSourceMode,
    limits: OwnershipLimits,
}

fn required_env(name: &str) -> Result<String, String> {
    env::var(name).map_err(|error| format!("{name} is required: {error}"))
}

fn required_env_u64(name: &str) -> Result<u64, String> {
    required_env(name)?
        .parse::<u64>()
        .map_err(|error| format!("{name} must be an unsigned integer: {error}"))
}

fn driver_configuration() -> Result<DriverConfiguration, String> {
    let root = PathBuf::from(required_env("FLN_OWNERSHIP_E2E_ROOT")?);
    let required_owner = required_env("FLN_OWNERSHIP_E2E_REQUIRED_OWNER")?;
    if required_owner.is_empty() {
        return Err("FLN_OWNERSHIP_E2E_REQUIRED_OWNER must not be empty".to_string());
    }
    let required_owners = BTreeSet::from([required_owner]);
    let diagnostic_bytes = usize::try_from(required_env_u64("FLN_OWNERSHIP_MAX_DIAGNOSTIC_BYTES")?)
        .map_err(|_| "FLN_OWNERSHIP_MAX_DIAGNOSTIC_BYTES does not fit usize".to_string())?;
    let limits = OwnershipLimits::try_new(
        required_env_u64("FLN_OWNERSHIP_MAX_FILE_BYTES")?,
        required_env_u64("FLN_OWNERSHIP_MAX_LINE_BYTES")?,
        required_env_u64("FLN_OWNERSHIP_MAX_RECORDS")?,
        required_env_u64("FLN_OWNERSHIP_MAX_ID_BYTES")?,
        required_env_u64("FLN_OWNERSHIP_MAX_PARSE_DEPTH")?,
        diagnostic_bytes,
    )
    .map_err(|error| error.to_string())?;
    let source_mode = match required_env("FLN_OWNERSHIP_E2E_POLICY")?.as_str() {
        "require-source" => OwnershipSourceMode::RequireSource,
        "manifest-only" => OwnershipSourceMode::ManifestOnly(
            ExpectedManifestBinding::from_lower_hex(
                &required_env("FLN_OWNERSHIP_EXPECTED_MANIFEST_HASH")?,
                &required_env("FLN_OWNERSHIP_EXPECTED_PROJECTION_HASH")?,
            )
            .map_err(|error| error.to_string())?,
        ),
        policy => {
            return Err(format!(
                "FLN_OWNERSHIP_E2E_POLICY must be require-source or manifest-only, got {policy:?}"
            ));
        }
    };
    Ok(DriverConfiguration {
        root,
        required_owners,
        source_mode,
        limits,
    })
}

fn input_usage_json(usage: &InputUsage) -> String {
    format!(
        concat!(
            "{{\"file_bytes\":{},",
            "\"line_bytes\":{},",
            "\"records\":{},",
            "\"id_bytes\":{},",
            "\"parse_depth\":{}}}"
        ),
        usage.file_bytes_observed(),
        usage.max_line_bytes_observed(),
        usage.records_observed(),
        usage.max_id_bytes_observed(),
        usage.max_parse_depth_observed()
    )
}

fn ownership_usage_json(usage: &OwnershipUsage) -> String {
    format!(
        concat!(
            "{{\"manifest\":{},",
            "\"source\":{},",
            "\"source_state\":\"{}\",",
            "\"required_owners\":{}}}"
        ),
        input_usage_json(usage.manifest()),
        input_usage_json(usage.source()),
        usage.source_state().as_str(),
        usage.required_owners()
    )
}

fn ownership_limits_json(limits: OwnershipLimits) -> String {
    format!(
        concat!(
            "{{\"max_file_bytes\":{},",
            "\"max_line_bytes\":{},",
            "\"max_records\":{},",
            "\"max_id_bytes\":{},",
            "\"max_parse_depth\":{},",
            "\"max_diagnostic_bytes\":{}}}"
        ),
        limits.max_file_bytes(),
        limits.max_line_bytes(),
        limits.max_records(),
        limits.max_id_bytes(),
        limits.max_parse_depth(),
        limits.max_diagnostic_bytes()
    )
}

fn json_string_contents(text: &str) -> String {
    use std::fmt::Write as _;

    let mut escaped = String::with_capacity(text.len());
    for character in text.chars() {
        match character {
            '"' => escaped.push_str("\\\""),
            '\\' => escaped.push_str("\\\\"),
            '\u{08}' => escaped.push_str("\\b"),
            '\u{0c}' => escaped.push_str("\\f"),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            control if control <= '\u{1f}' => {
                write!(&mut escaped, "\\u{:04x}", u32::from(control))
                    .expect("writing to String cannot fail");
            }
            other => escaped.push(other),
        }
    }
    escaped
}

fn ownership_result_json(
    result: &Result<OwnershipEvidence, OwnershipFailure>,
    limits: OwnershipLimits,
) -> String {
    let (classification, diagnostic, binding, usage) = match result {
        Ok(evidence) => (
            "ok",
            String::new(),
            Some(evidence.binding()),
            evidence.usage(),
        ),
        Err(error) => (
            error.result_classification(),
            error.diagnostic(),
            error.binding(),
            error.usage(),
        ),
    };
    let evidence_grade = if binding.is_some() {
        match usage.source_state() {
            OwnershipSourceState::PresentVerified => "source-bound",
            OwnershipSourceState::Absent => "manifest-only",
            OwnershipSourceState::NotAttempted
            | OwnershipSourceState::Unavailable
            | OwnershipSourceState::Present => "none",
        }
    } else {
        "none"
    };
    let (manifest_hash, projection_hash) = binding
        .map(|binding| {
            (
                binding.manifest_digest().to_hex(),
                binding.projection_digest().to_hex(),
            )
        })
        .unwrap_or_default();
    format!(
        concat!(
            "{{\"schema\":\"{}\",",
            "\"classification\":\"{}\",",
            "\"diagnostic\":\"{}\",",
            "\"evidence_grade\":\"{}\",",
            "\"limits\":{},",
            "\"manifest_hash\":\"{}\",",
            "\"manifest_path\":\"{}\",",
            "\"projection_hash\":\"{}\",",
            "\"source_path\":\"{}\",",
            "\"usage\":{}}}\n"
        ),
        OWNERSHIP_RESULT_SCHEMA,
        classification,
        json_string_contents(&diagnostic),
        evidence_grade,
        ownership_limits_json(limits),
        manifest_hash,
        MANIFEST_RELATIVE_PATH,
        projection_hash,
        SOURCE_RELATIVE_PATH,
        ownership_usage_json(usage)
    )
}

fn write_new_result(path: &Path, contents: &str) -> Result<(), String> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("create ownership result {}: {error}", path.display()))?;
    file.write_all(contents.as_bytes())
        .map_err(|error| format!("write ownership result {}: {error}", path.display()))?;
    file.flush()
        .map_err(|error| format!("flush ownership result {}: {error}", path.display()))?;
    file.sync_all()
        .map_err(|error| format!("sync ownership result {}: {error}", path.display()))
}

#[test]
fn ownership_evidence_process_driver() -> Result<(), String> {
    if env::var_os("FLN_OWNERSHIP_E2E_ROOT").is_none() {
        return Ok(());
    }
    let configuration = driver_configuration()?;
    let result = load_kernel_contract_ownership(
        &configuration.root,
        &configuration.required_owners,
        configuration.source_mode,
        configuration.limits,
    );
    let result_path = PathBuf::from(required_env("FLN_OWNERSHIP_E2E_RESULT")?);
    write_new_result(
        &result_path,
        &ownership_result_json(&result, configuration.limits),
    )?;
    match result {
        Ok(_) => Ok(()),
        Err(error) => Err(error.diagnostic()),
    }
}

#[test]
fn ownership_evidence_semantic_probe() -> Result<(), String> {
    if env::var_os("FLN_OWNERSHIP_E2E_ROOT").is_none() {
        return Ok(());
    }
    let configuration = driver_configuration()?;
    let evidence = load_kernel_contract_ownership(
        &configuration.root,
        &configuration.required_owners,
        configuration.source_mode,
        configuration.limits,
    )
    .map_err(|error| error.diagnostic())?;
    println!(
        concat!(
            "FLN_OWNERSHIP_PROBE ",
            "{{\"schema\":\"{}\",",
            "\"manifest_hash\":\"{}\",",
            "\"projection_hash\":\"{}\",",
            "\"record_count\":{},",
            "\"source_state\":\"{}\"}}"
        ),
        OWNERSHIP_PROBE_SCHEMA,
        evidence.binding().manifest_digest(),
        evidence.binding().projection_digest(),
        evidence.binding().record_count(),
        evidence.usage().source_state().as_str()
    );
    Ok(())
}
