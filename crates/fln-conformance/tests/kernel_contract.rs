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
use std::io;
use std::path::Path;
use std::path::PathBuf;

/// The pinned Reference source tree. Every kernel-rule anchor must live here: a rule
/// "anchored" to our own code or anything outside the pin proves nothing.
const PIN_TREE_PREFIX: &str = "vendor/lean4-src/";

fn workspace_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
}

#[derive(Debug, PartialEq, Eq)]
enum BeadEvidenceError {
    Missing {
        path: PathBuf,
    },
    Unreadable {
        path: PathBuf,
        kind: io::ErrorKind,
    },
    Corrupt {
        path: PathBuf,
        line: usize,
        reason: &'static str,
    },
    Empty {
        path: PathBuf,
    },
}

impl BeadEvidenceError {
    fn diagnostic(&self) -> String {
        match self {
            Self::Missing { path } => format!(
                "[bead-evidence/missing] tracked ownership export `{}` is missing",
                path.display()
            ),
            Self::Unreadable { path, kind } => format!(
                "[bead-evidence/unreadable] tracked ownership export `{}` cannot be read ({kind:?})",
                path.display()
            ),
            Self::Corrupt { path, line, reason } => format!(
                "[bead-evidence/corrupt] tracked ownership export `{}` line {line} is invalid: {reason}",
                path.display()
            ),
            Self::Empty { path } => format!(
                "[bead-evidence/empty] tracked ownership export `{}` contains no issue ids",
                path.display()
            ),
        }
    }
}

struct JsonSyntax<'a> {
    bytes: &'a [u8],
    cursor: usize,
}

impl JsonSyntax<'_> {
    fn skip_space(&mut self) {
        while matches!(
            self.bytes.get(self.cursor),
            Some(b' ' | b'\n' | b'\r' | b'\t')
        ) {
            self.cursor += 1;
        }
    }

    fn take(&mut self, expected: u8) -> bool {
        if self.bytes.get(self.cursor) == Some(&expected) {
            self.cursor += 1;
            true
        } else {
            false
        }
    }

    fn parse_value(&mut self, depth: usize) -> bool {
        // The Beads export is generated metadata, not an unbounded semantic input.
        // Bound parser recursion so corrupt hostile evidence still fails typed rather
        // than threatening the test runner's stack.
        if depth > 128 {
            return false;
        }
        self.skip_space();
        match self.bytes.get(self.cursor).copied() {
            Some(b'{') => self.parse_object(depth + 1),
            Some(b'[') => self.parse_array(depth + 1),
            Some(b'"') => self.parse_string(),
            Some(b't') => self.parse_literal(b"true"),
            Some(b'f') => self.parse_literal(b"false"),
            Some(b'n') => self.parse_literal(b"null"),
            Some(b'-' | b'0'..=b'9') => self.parse_number(),
            _ => false,
        }
    }

    fn parse_object(&mut self, depth: usize) -> bool {
        if !self.take(b'{') {
            return false;
        }
        self.skip_space();
        if self.take(b'}') {
            return true;
        }
        loop {
            if !self.parse_string() {
                return false;
            }
            self.skip_space();
            if !self.take(b':') || !self.parse_value(depth) {
                return false;
            }
            self.skip_space();
            if self.take(b'}') {
                return true;
            }
            if !self.take(b',') {
                return false;
            }
            self.skip_space();
        }
    }

    fn parse_array(&mut self, depth: usize) -> bool {
        if !self.take(b'[') {
            return false;
        }
        self.skip_space();
        if self.take(b']') {
            return true;
        }
        loop {
            if !self.parse_value(depth) {
                return false;
            }
            self.skip_space();
            if self.take(b']') {
                return true;
            }
            if !self.take(b',') {
                return false;
            }
            self.skip_space();
        }
    }

    fn parse_string(&mut self) -> bool {
        if !self.take(b'"') {
            return false;
        }
        while let Some(byte) = self.bytes.get(self.cursor).copied() {
            self.cursor += 1;
            match byte {
                b'"' => return true,
                0..=31 => return false,
                b'\\' => {
                    let Some(escape) = self.bytes.get(self.cursor).copied() else {
                        return false;
                    };
                    self.cursor += 1;
                    match escape {
                        b'"' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't' => {}
                        b'u' => {
                            for _ in 0..4 {
                                if !matches!(
                                    self.bytes.get(self.cursor),
                                    Some(b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F')
                                ) {
                                    return false;
                                }
                                self.cursor += 1;
                            }
                        }
                        _ => return false,
                    }
                }
                _ => {}
            }
        }
        false
    }

    fn parse_literal(&mut self, literal: &[u8]) -> bool {
        if self.bytes.get(self.cursor..self.cursor + literal.len()) == Some(literal) {
            self.cursor += literal.len();
            true
        } else {
            false
        }
    }

    fn parse_number(&mut self) -> bool {
        self.take(b'-');
        match self.bytes.get(self.cursor).copied() {
            Some(b'0') => self.cursor += 1,
            Some(b'1'..=b'9') => {
                self.cursor += 1;
                while matches!(self.bytes.get(self.cursor), Some(b'0'..=b'9')) {
                    self.cursor += 1;
                }
            }
            _ => return false,
        }
        if self.take(b'.') {
            let start = self.cursor;
            while matches!(self.bytes.get(self.cursor), Some(b'0'..=b'9')) {
                self.cursor += 1;
            }
            if self.cursor == start {
                return false;
            }
        }
        if matches!(self.bytes.get(self.cursor), Some(b'e' | b'E')) {
            self.cursor += 1;
            if matches!(self.bytes.get(self.cursor), Some(b'+' | b'-')) {
                self.cursor += 1;
            }
            let start = self.cursor;
            while matches!(self.bytes.get(self.cursor), Some(b'0'..=b'9')) {
                self.cursor += 1;
            }
            if self.cursor == start {
                return false;
            }
        }
        true
    }
}

fn is_json_object(line: &str) -> bool {
    let mut parser = JsonSyntax {
        bytes: line.as_bytes(),
        cursor: 0,
    };
    parser.skip_space();
    if parser.bytes.get(parser.cursor) != Some(&b'{') || !parser.parse_value(0) {
        return false;
    }
    parser.skip_space();
    parser.cursor == parser.bytes.len()
}

fn tracked_bead_ids_from_read(
    path: &Path,
    read: io::Result<String>,
) -> Result<BTreeSet<String>, BeadEvidenceError> {
    let text = match read {
        Ok(text) => text,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return Err(BeadEvidenceError::Missing {
                path: path.to_path_buf(),
            });
        }
        Err(error) => {
            return Err(BeadEvidenceError::Unreadable {
                path: path.to_path_buf(),
                kind: error.kind(),
            });
        }
    };

    let mut ids = BTreeSet::new();
    for (index, line) in text.lines().enumerate() {
        let line_number = index + 1;
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let Some(rest) = line.strip_prefix("{\"id\":\"") else {
            return Err(BeadEvidenceError::Corrupt {
                path: path.to_path_buf(),
                line: line_number,
                reason: "expected a canonical Beads JSON object beginning with a string id",
            });
        };
        let Some(end) = rest.find('"') else {
            return Err(BeadEvidenceError::Corrupt {
                path: path.to_path_buf(),
                line: line_number,
                reason: "unterminated issue id",
            });
        };
        let id = &rest[..end];
        let canonical_id = id
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-' | b'.'));
        if id.is_empty() || !canonical_id || !is_json_object(line) {
            return Err(BeadEvidenceError::Corrupt {
                path: path.to_path_buf(),
                line: line_number,
                reason: "malformed issue object",
            });
        }
        if !ids.insert(id.to_string()) {
            return Err(BeadEvidenceError::Corrupt {
                path: path.to_path_buf(),
                line: line_number,
                reason: "duplicate issue id",
            });
        }
    }
    if ids.is_empty() {
        return Err(BeadEvidenceError::Empty {
            path: path.to_path_buf(),
        });
    }
    Ok(ids)
}

/// The set of tracked bead ids (from the exported JSONL), for proving a stub's owner
/// actually exists. The export is a required evidence input: unavailable or malformed
/// evidence is a typed validation failure, never permission to skip owner checks.
fn tracked_bead_ids(root: &Path) -> Result<BTreeSet<String>, BeadEvidenceError> {
    let path = root.join(".beads/issues.jsonl");
    tracked_bead_ids_from_read(&path, fs::read_to_string(&path))
}

/// The full production validation of the parsed rule set against the workspace: the
/// single source of truth both the real-contract test and the planted-mutation test
/// run, so no check can be silently deleted without a test going red.
fn validate(rules: &[Rule], root: &Path) -> Vec<String> {
    validate_with_beads(rules, root, tracked_bead_ids(root))
}

fn validate_with_beads(
    rules: &[Rule],
    root: &Path,
    beads: Result<BTreeSet<String>, BeadEvidenceError>,
) -> Vec<String> {
    let mut failures: Vec<String> = Vec::new();
    let mut ids = BTreeSet::new();
    if let Err(error) = &beads {
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
        if let (Some(owner), Ok(beads)) = (&rule.stub_owner, &beads)
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
    let tracked = tracked_bead_ids_from_read(
        Path::new("/mutation-fixture/.beads/issues.jsonl"),
        Ok("{\"id\":\"franken_lean-z6c\"}\n".to_string()),
    );
    assert!(
        has(
            &validate_with_beads(&rules, root, tracked),
            "not a tracked bead"
        ),
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
    let evidence_path = Path::new("/evidence-root/.beads/issues.jsonl");
    let (rules, problems) = parse_rules(
        "### KR-993 · ownership evidence\n\
         anchor: vendor/lean4-src/src/kernel/type_checker.cpp:609 (x) expect=\"reduce_nat\"\n\
         fixtures: stub owner=franken_lean-z6c\n",
    );
    assert!(problems.is_empty());

    let assert_failure = |evidence, class: &str| {
        let failures = validate_with_beads(&rules, root, evidence);
        assert!(
            failures.iter().any(|failure| {
                failure.contains(class) && failure.contains(&evidence_path.display().to_string())
            }),
            "ownership evidence failure must preserve its class and path: {failures:?}"
        );
    };

    let missing =
        tracked_bead_ids_from_read(evidence_path, Err(io::Error::from(io::ErrorKind::NotFound)));
    assert!(matches!(&missing, Err(BeadEvidenceError::Missing { .. })));
    assert_failure(missing, "[bead-evidence/missing]");

    let unreadable = tracked_bead_ids_from_read(
        evidence_path,
        Err(io::Error::from(io::ErrorKind::PermissionDenied)),
    );
    assert!(matches!(
        &unreadable,
        Err(BeadEvidenceError::Unreadable { kind, .. })
            if *kind == io::ErrorKind::PermissionDenied
    ));
    assert_failure(unreadable, "[bead-evidence/unreadable]");

    let corrupt = tracked_bead_ids_from_read(
        evidence_path,
        Ok("{\"id\":\"franken_lean-z6c\", definitely-not-json}\n".to_string()),
    );
    assert!(matches!(
        &corrupt,
        Err(BeadEvidenceError::Corrupt { line: 1, .. })
    ));
    assert_failure(corrupt, "[bead-evidence/corrupt]");

    let noncanonical_id = tracked_bead_ids_from_read(
        evidence_path,
        Ok("{\"id\":\"not a bead id\"}\n".to_string()),
    );
    assert!(matches!(
        &noncanonical_id,
        Err(BeadEvidenceError::Corrupt { line: 1, .. })
    ));
    assert_failure(noncanonical_id, "[bead-evidence/corrupt]");

    let empty = tracked_bead_ids_from_read(evidence_path, Ok(" \n\t\n".to_string()));
    assert!(matches!(&empty, Err(BeadEvidenceError::Empty { .. })));
    assert_failure(empty, "[bead-evidence/empty]");

    let duplicate = tracked_bead_ids_from_read(
        evidence_path,
        Ok("{\"id\":\"franken_lean-z6c\"}\n{\"id\":\"franken_lean-z6c\"}\n".to_string()),
    );
    assert!(matches!(
        &duplicate,
        Err(BeadEvidenceError::Corrupt { line: 2, .. })
    ));
    assert_failure(duplicate, "[bead-evidence/corrupt]");

    let tracked = tracked_bead_ids_from_read(
        evidence_path,
        Ok("{\"id\":\"franken_lean-z6c\"}\n".to_string()),
    );
    assert!(
        validate_with_beads(&rules, root, tracked).is_empty(),
        "a real owner in valid evidence must pass the production validator"
    );
}
