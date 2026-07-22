//! KERNEL_CONTRACT.md is CI-checked like code (bead franken_lean-79k):
//!
//! * **anchor resolution** — every cited Reference source location must exist at the
//!   pin, lie **inside the pinned vendor tree** (`vendor/lean4-src/`, never our own
//!   code), and carry its `expect="token"` on that exact line — drift fails;
//! * **coverage** — every rule names at least one fixture, or an explicit stub whose
//!   owner is a **real, tracked bead** — no silently unevidenced rule, no phantom
//!   owner;
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

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

/// The pinned Reference source tree. Every kernel-rule anchor must live here: a rule
/// "anchored" to our own code or anything outside the pin proves nothing.
const PIN_TREE_PREFIX: &str = "vendor/lean4-src/";

fn workspace_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
}

/// The set of tracked bead ids (from the exported JSONL), for proving a stub's owner
/// actually exists. Parsed leniently: any `"id":"<id>"` occurrence counts.
fn tracked_bead_ids(root: &Path) -> BTreeSet<String> {
    let mut ids = BTreeSet::new();
    let Ok(text) = fs::read_to_string(root.join(".beads/issues.jsonl")) else {
        return ids;
    };
    let needle = "\"id\":\"";
    for line in text.lines() {
        let mut rest = line;
        while let Some(pos) = rest.find(needle) {
            rest = &rest[pos + needle.len()..];
            if let Some(end) = rest.find('"') {
                ids.insert(rest[..end].to_string());
                rest = &rest[end + 1..];
            } else {
                break;
            }
        }
    }
    ids
}

/// The full production validation of the parsed rule set against the workspace: the
/// single source of truth both the real-contract test and the planted-mutation test
/// run, so no check can be silently deleted without a test going red.
fn validate(rules: &[Rule], root: &Path) -> Vec<String> {
    let mut failures: Vec<String> = Vec::new();
    let mut ids = BTreeSet::new();
    let beads = tracked_bead_ids(root);
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
        if let Some(owner) = &rule.stub_owner
            && !beads.is_empty()
            && !beads.contains(owner)
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

#[derive(Debug, Default)]
struct Rule {
    id: String,
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
                rules.push(Rule {
                    id: id.to_string(),
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
        has(&validate(&rules, root), "not a tracked bead"),
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
