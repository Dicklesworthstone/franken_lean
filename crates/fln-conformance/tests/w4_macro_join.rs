//! Terminal W4 macro join for `franken_lean-4nv`.
//!
//! The parent epic is not closed by observing that two child beads happen to be
//! closed. Its contract requires one machine-readable join over the exact children,
//! their canonical coverage rows, and the no-mock scenarios that execute those rows.
//! This suite derives that join from the real tracker and verification manifest.
//!
//! The joined child root includes the child id and terminal state, the complete
//! canonical coverage row, and the complete scenario-registry row. Consequently the
//! root binds implementation commits, fixtures, named unit/property/metamorphic and
//! mutation suites, negative recovery, retained evidence notes, and CI dispatch
//! authority without copying those fields into a second hand-maintained contract.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use fln_conformance::execution::{Field, record_field};
use fln_hash::domain::{Domain, DomainHasher};

const PARENT: &str = "franken_lean-4nv";
const CHILDREN: [&str; 2] = ["franken_lean-7m54", "franken_lean-qr74"];
const JOIN_SCHEMA: &str = "fln.w4-macro-join/1";
const CHILD_SCHEMA: &str = "fln.w4-macro-child-row/1";
const JOIN_TEST: &str =
    "test:fln-conformance::w4_macro_join::the_terminal_w4_macro_join_binds_exact_child_rows";

const COVERAGE_TEXT_FIELDS: &[&str] = &[
    "claim_type",
    "evidence_kind",
    "kind",
    "owner",
    "skip",
    "workstream",
];

const COVERAGE_LIST_FIELDS: &[&str] = &[
    "artifacts",
    "behavior_notes",
    "boundary",
    "cancellation",
    "claim_ids",
    "error",
    "failure_atomicity",
    "fault",
    "fuzz",
    "gate_ids",
    "invariant_ids",
    "metamorphic",
    "mutation",
    "negative_recovery",
    "parity_rows",
    "property",
    "requirement_ids",
    "resource",
    "scenarios",
    "unit",
];

const REQUIRED_CHILD_LIST_FIELDS: &[&str] = &[
    "artifacts",
    "behavior_notes",
    "boundary",
    "cancellation",
    "claim_ids",
    "error",
    "failure_atomicity",
    "fault",
    "fuzz",
    "gate_ids",
    "invariant_ids",
    "metamorphic",
    "mutation",
    "negative_recovery",
    "parity_rows",
    "property",
    "requirement_ids",
    "resource",
    "scenarios",
    "unit",
];

#[derive(Clone, Debug)]
struct Issue {
    status: String,
}

#[derive(Clone, Debug)]
struct Coverage {
    raw: String,
    text: BTreeMap<&'static str, String>,
    lists: BTreeMap<&'static str, Vec<String>>,
    mock_only_false: bool,
}

impl Coverage {
    fn text(&self, key: &'static str) -> &str {
        self.text.get(key).map(String::as_str).unwrap_or("")
    }

    fn list(&self, key: &'static str) -> &[String] {
        self.lists.get(key).map(Vec::as_slice).unwrap_or(&[])
    }
}

#[derive(Clone, Debug)]
struct Scenario {
    raw: String,
    owner: String,
    activation: String,
    artifact_kind: String,
    claim_type: String,
    evidence_kind: String,
    gate_ids: Vec<String>,
    ci_required: bool,
}

#[derive(Clone, Debug)]
struct Snapshot {
    issues: BTreeMap<String, Issue>,
    coverage: BTreeMap<String, Coverage>,
    scenarios: BTreeMap<String, Scenario>,
}

fn root() -> PathBuf {
    fln_conformance::checked_workspace_root!()
}

fn read(path: &Path) -> Result<String, String> {
    fs::read_to_string(path).map_err(|error| format!("{}: {error}", path.display()))
}

fn text_field(line: &str, key: &str) -> Result<String, String> {
    match record_field(line, key) {
        Some(Field::Text(value)) => Ok(value),
        other => Err(format!("{key} is not one text field: {other:?}")),
    }
}

fn list_field(line: &str, key: &str) -> Result<Vec<String>, String> {
    match record_field(line, key) {
        Some(Field::List(value)) => Ok(value),
        other => Err(format!("{key} is not one string list: {other:?}")),
    }
}

fn compact_bool(line: &str, key: &str, value: bool) -> bool {
    let compact = format!("\"{key}\":{value}");
    let spaced = format!("\"{key}\": {value}");
    line.contains(&compact) || line.contains(&spaced)
}

fn parse_coverage(line: &str) -> Result<Coverage, String> {
    let mut text = BTreeMap::new();
    for &key in COVERAGE_TEXT_FIELDS {
        text.insert(key, text_field(line, key)?);
    }
    if text.get("kind").map(String::as_str) != Some("coverage") {
        return Err("the bead row is not kind=coverage".to_string());
    }

    let mut lists = BTreeMap::new();
    for &key in COVERAGE_LIST_FIELDS {
        lists.insert(key, list_field(line, key)?);
    }

    Ok(Coverage {
        raw: line.to_string(),
        text,
        lists,
        mock_only_false: compact_bool(line, "mock_only", false),
    })
}

fn parse_scenario(line: &str) -> Result<Scenario, String> {
    if text_field(line, "kind")? != "scenario" {
        return Err("the scenario row is not kind=scenario".to_string());
    }
    Ok(Scenario {
        raw: line.to_string(),
        owner: text_field(line, "owner")?,
        activation: text_field(line, "activation")?,
        artifact_kind: text_field(line, "artifact_kind")?,
        claim_type: text_field(line, "claim_type")?,
        evidence_kind: text_field(line, "evidence_kind")?,
        gate_ids: list_field(line, "gate_ids")?,
        ci_required: compact_bool(line, "ci_required", true),
    })
}

fn interesting_id(id: &str) -> bool {
    id == PARENT || CHILDREN.contains(&id)
}

fn expected_scenario(child: &str) -> &'static str {
    match child {
        "franken_lean-7m54" => "hygiene_no_mock_e2e",
        "franken_lean-qr74" => "macro_txn_no_mock_e2e",
        _ => "",
    }
}

fn parse_snapshot(tracker: &str, manifest: &str) -> Result<Snapshot, String> {
    let mut issues = BTreeMap::new();
    for (index, line) in tracker.lines().enumerate() {
        let Some(Field::Text(id)) = record_field(line, "id") else {
            continue;
        };
        if !interesting_id(&id) {
            continue;
        }
        let issue = Issue {
            status: text_field(line, "status")
                .map_err(|error| format!("tracker:{} {id}: {error}", index + 1))?,
        };
        if issues.insert(id.clone(), issue).is_some() {
            return Err(format!("tracker:{} duplicate issue {id}", index + 1));
        }
    }

    let mut coverage = BTreeMap::new();
    let mut scenarios = BTreeMap::new();
    let expected_scenarios: BTreeSet<&str> = CHILDREN
        .iter()
        .map(|child| expected_scenario(child))
        .collect();
    for (index, line) in manifest.lines().enumerate() {
        if let Some(Field::Text(bead)) = record_field(line, "bead")
            && interesting_id(&bead)
        {
            let row = parse_coverage(line)
                .map_err(|error| format!("manifest:{} {bead}: {error}", index + 1))?;
            if coverage.insert(bead.clone(), row).is_some() {
                return Err(format!("manifest:{} duplicate coverage {bead}", index + 1));
            }
        }

        let Some(Field::Text(scenario)) = record_field(line, "scenario") else {
            continue;
        };
        if !expected_scenarios.contains(scenario.as_str()) {
            continue;
        }
        let row = parse_scenario(line)
            .map_err(|error| format!("manifest:{} {scenario}: {error}", index + 1))?;
        if scenarios.insert(scenario.clone(), row).is_some() {
            return Err(format!(
                "manifest:{} duplicate scenario {scenario}",
                index + 1
            ));
        }
    }

    Ok(Snapshot {
        issues,
        coverage,
        scenarios,
    })
}

fn derive() -> Result<Snapshot, String> {
    let root = root();
    let tracker = read(&root.join(".beads/issues.jsonl"))?;
    let manifest = read(&root.join("ci/VERIFICATION_MANIFEST.jsonl"))?;
    parse_snapshot(&tracker, &manifest)
}

fn feed(hasher: &mut DomainHasher, value: &str) {
    hasher.update(&(value.len() as u64).to_le_bytes());
    hasher.update(value.as_bytes());
}

fn child_root(snapshot: &Snapshot, child: &str) -> Result<String, String> {
    let issue = snapshot
        .issues
        .get(child)
        .ok_or_else(|| format!("missing issue {child}"))?;
    let coverage = snapshot
        .coverage
        .get(child)
        .ok_or_else(|| format!("missing coverage {child}"))?;
    let scenario_name = expected_scenario(child);
    let scenario = snapshot
        .scenarios
        .get(scenario_name)
        .ok_or_else(|| format!("missing scenario {scenario_name}"))?;

    let mut hasher = DomainHasher::new(Domain::Fixture);
    for value in [
        CHILD_SCHEMA,
        child,
        issue.status.as_str(),
        coverage.raw.as_str(),
        scenario.raw.as_str(),
    ] {
        feed(&mut hasher, value);
    }
    Ok(format!("fln-fixture:{}", hasher.finalize().to_hex()))
}

fn join_root_from_pairs(mut pairs: Vec<(String, String)>) -> Result<String, String> {
    pairs.sort();
    let ids = pairs.iter().map(|(id, _)| id.as_str()).collect::<Vec<_>>();
    if ids != CHILDREN {
        return Err(format!(
            "the join child set is {ids:?}, expected {CHILDREN:?}"
        ));
    }

    let mut hasher = DomainHasher::new(Domain::Fixture);
    feed(&mut hasher, JOIN_SCHEMA);
    for (id, root) in pairs {
        feed(&mut hasher, &id);
        feed(&mut hasher, &root);
    }
    Ok(format!("fln-fixture:{}", hasher.finalize().to_hex()))
}

fn machine_note(snapshot: &Snapshot) -> Result<String, String> {
    let pairs = CHILDREN
        .iter()
        .map(|child| child_root(snapshot, child).map(|root| ((*child).to_string(), root)))
        .collect::<Result<Vec<_>, _>>()?;
    let join = join_root_from_pairs(pairs.clone())?;
    Ok(format!(
        "MACHINE JOIN ROOT. schema={JOIN_SCHEMA} child={} root={} child={} root={} join={join}",
        pairs[0].0, pairs[0].1, pairs[1].0, pairs[1].1
    ))
}

fn set(values: &[String]) -> BTreeSet<&str> {
    values.iter().map(String::as_str).collect()
}

fn judge(snapshot: &Snapshot) -> Vec<String> {
    let mut faults = Vec::new();

    match snapshot.issues.get(PARENT) {
        Some(issue) => {
            if !matches!(issue.status.as_str(), "in_progress" | "closed") {
                faults.push(format!("parent-status: {} is {}", PARENT, issue.status));
            }
        }
        None => faults.push(format!("parent-missing: {PARENT}")),
    }

    for child in CHILDREN {
        match snapshot.issues.get(child) {
            Some(issue) if issue.status == "closed" => {}
            Some(issue) => faults.push(format!(
                "child-status:{child}: expected closed, got {}",
                issue.status
            )),
            None => faults.push(format!("child-status:{child}: issue is absent")),
        }

        let Some(coverage) = snapshot.coverage.get(child) else {
            faults.push(format!("child-coverage:{child}: row is absent"));
            continue;
        };
        for (field, expected) in [
            ("claim_type", "bounded_model"),
            ("evidence_kind", "no_mock_e2e"),
            ("kind", "coverage"),
            ("owner", "FoggyForge"),
            ("skip", "none"),
            ("workstream", "W4"),
        ] {
            if coverage.text(field) != expected {
                faults.push(format!(
                    "child-text:{child}:{field}: expected {expected}, got {:?}",
                    coverage.text(field)
                ));
            }
        }
        if !coverage.mock_only_false {
            faults.push(format!(
                "child-mock:{child}: mock_only=false is not declared"
            ));
        }
        for &field in REQUIRED_CHILD_LIST_FIELDS {
            if coverage.list(field).is_empty() {
                faults.push(format!("child-field:{child}:{field}: list is empty"));
            }
        }

        let artifacts = coverage.list("artifacts");
        for prefix in ["bead-comment:", "commit:", "test:"] {
            if !artifacts.iter().any(|value| value.starts_with(prefix)) {
                faults.push(format!("child-artifact:{child}: no {prefix} referent"));
            }
        }
        if !coverage
            .list("behavior_notes")
            .iter()
            .any(|note| note.starts_with("AUTHORITATIVE EVIDENCE."))
        {
            faults.push(format!(
                "child-evidence:{child}: no authoritative retained-evidence note"
            ));
        }

        let expected = [expected_scenario(child), "quality_gate"]
            .into_iter()
            .collect::<BTreeSet<_>>();
        let actual = set(coverage.list("scenarios"));
        if actual != expected || actual.len() != coverage.list("scenarios").len() {
            faults.push(format!(
                "child-scenarios:{child}: expected {expected:?}, got {actual:?}"
            ));
        }

        let scenario_name = expected_scenario(child);
        match snapshot.scenarios.get(scenario_name) {
            Some(scenario) => {
                if scenario.owner != child {
                    faults.push(format!(
                        "scenario-owner:{scenario_name}: expected {child}, got {}",
                        scenario.owner
                    ));
                }
                for (field, actual, expected) in [
                    ("activation", scenario.activation.as_str(), "active"),
                    (
                        "artifact_kind",
                        scenario.artifact_kind.as_str(),
                        "single-bundle",
                    ),
                    ("claim_type", scenario.claim_type.as_str(), "bounded_model"),
                    (
                        "evidence_kind",
                        scenario.evidence_kind.as_str(),
                        "no_mock_e2e",
                    ),
                ] {
                    if actual != expected {
                        faults.push(format!(
                            "scenario-field:{scenario_name}:{field}: expected {expected}, got {actual}"
                        ));
                    }
                }
                if scenario.gate_ids != ["W4"] {
                    faults.push(format!(
                        "scenario-gate:{scenario_name}: expected [W4], got {:?}",
                        scenario.gate_ids
                    ));
                }
                if !scenario.ci_required {
                    faults.push(format!(
                        "scenario-ci:{scenario_name}: ci_required=true is absent"
                    ));
                }
            }
            None => faults.push(format!(
                "scenario-missing:{scenario_name}: registry row is absent"
            )),
        }
    }

    match snapshot.coverage.get(PARENT) {
        Some(parent) => {
            for (field, expected) in [
                ("claim_type", "bounded_model"),
                ("evidence_kind", "no_mock_e2e"),
                ("kind", "coverage"),
                ("owner", "FoggyForge"),
                ("skip", "none"),
                ("workstream", "W4"),
            ] {
                if parent.text(field) != expected {
                    faults.push(format!(
                        "parent-text:{field}: expected {expected}, got {:?}",
                        parent.text(field)
                    ));
                }
            }
            if !parent.mock_only_false {
                faults.push("parent-mock: mock_only=false is not declared".to_string());
            }
            let expected = [
                "hygiene_no_mock_e2e",
                "macro_txn_no_mock_e2e",
                "quality_gate",
            ]
            .into_iter()
            .collect::<BTreeSet<_>>();
            let actual = set(parent.list("scenarios"));
            if actual != expected || actual.len() != parent.list("scenarios").len() {
                faults.push(format!(
                    "parent-scenarios: expected {expected:?}, got {actual:?}"
                ));
            }
            if !parent
                .list("artifacts")
                .iter()
                .any(|value| value == JOIN_TEST)
            {
                faults.push(format!(
                    "parent-artifact: the runnable join {JOIN_TEST} is absent"
                ));
            }
            match machine_note(snapshot) {
                Ok(expected) => {
                    let machine_notes = parent
                        .list("behavior_notes")
                        .iter()
                        .filter(|note| note.starts_with("MACHINE JOIN ROOT."))
                        .collect::<Vec<_>>();
                    if machine_notes.len() != 1 || machine_notes[0].as_str() != expected {
                        faults.push(format!(
                            "parent-root: expected exactly {expected:?}, got {machine_notes:?}"
                        ));
                    }
                }
                Err(error) => faults.push(format!("parent-root: cannot derive join: {error}")),
            }
        }
        None => faults.push(format!("parent-coverage: {PARENT} row is absent")),
    }

    faults
}

fn assert_clean(snapshot: &Snapshot) {
    let faults = judge(snapshot);
    assert!(
        faults.is_empty(),
        "the terminal W4 macro join is not clean:\n{}\n\nderived machine note:\n{}",
        faults.join("\n"),
        machine_note(snapshot).unwrap_or_else(|error| format!("<unavailable: {error}>"))
    );
}

#[test]
fn the_terminal_w4_macro_join_binds_exact_child_rows() {
    let snapshot = derive().expect("the real tracker and manifest are readable");
    assert_clean(&snapshot);
}

#[test]
fn each_child_surface_and_root_mutant_is_killed() {
    let clean = derive().expect("the real tracker and manifest are readable");
    assert_clean(&clean);

    let mut status = clean.clone();
    status
        .issues
        .get_mut(CHILDREN[0])
        .expect("first child")
        .status = "in_progress".to_string();
    assert!(
        judge(&status)
            .iter()
            .any(|fault| fault.starts_with("child-status:"))
    );

    let mut mutation = clean.clone();
    mutation
        .coverage
        .get_mut(CHILDREN[1])
        .expect("second child")
        .lists
        .get_mut("mutation")
        .expect("mutation field")
        .clear();
    assert!(
        judge(&mutation)
            .iter()
            .any(|fault| fault.starts_with("child-field:"))
    );

    let mut owner = clean.clone();
    owner
        .scenarios
        .get_mut(expected_scenario(CHILDREN[0]))
        .expect("hygiene scenario")
        .owner = CHILDREN[1].to_string();
    assert!(
        judge(&owner)
            .iter()
            .any(|fault| fault.starts_with("scenario-owner:"))
    );

    let mut root = clean.clone();
    root.coverage
        .get_mut(CHILDREN[0])
        .expect("first child")
        .raw
        .push(' ');
    assert!(
        judge(&root)
            .iter()
            .any(|fault| fault.starts_with("parent-root:"))
    );

    let mut scenarios = clean.clone();
    scenarios
        .coverage
        .get_mut(PARENT)
        .expect("parent row")
        .lists
        .get_mut("scenarios")
        .expect("scenario field")
        .push("invented_macro_lane".to_string());
    assert!(
        judge(&scenarios)
            .iter()
            .any(|fault| fault.starts_with("parent-scenarios:"))
    );
}

#[test]
fn join_root_is_independent_of_child_enumeration_order() {
    let snapshot = derive().expect("the real tracker and manifest are readable");
    let forward = CHILDREN
        .iter()
        .map(|child| child_root(&snapshot, child).map(|root| ((*child).to_string(), root)))
        .collect::<Result<Vec<_>, _>>()
        .expect("the child roots derive");
    let mut reverse = forward.clone();
    reverse.reverse();
    assert_eq!(
        join_root_from_pairs(forward.clone()),
        join_root_from_pairs(reverse),
        "enumeration order cannot enter the canonical join"
    );

    let duplicate = vec![forward[0].clone(), forward[0].clone()];
    assert!(
        join_root_from_pairs(duplicate)
            .expect_err("a duplicate child cannot join")
            .contains("child set")
    );
}

#[test]
fn one_child_drift_then_exact_restoration_recovers_the_join() {
    let clean = derive().expect("the real tracker and manifest are readable");
    assert_clean(&clean);

    let mut drifted = clean.clone();
    drifted
        .coverage
        .get_mut(CHILDREN[1])
        .expect("second child")
        .raw
        .push(' ');
    assert!(
        judge(&drifted)
            .iter()
            .any(|fault| fault.starts_with("parent-root:")),
        "one changed child row must invalidate the parent root"
    );

    drifted.coverage.insert(
        CHILDREN[1].to_string(),
        clean
            .coverage
            .get(CHILDREN[1])
            .expect("clean second child")
            .clone(),
    );
    assert_clean(&drifted);
}

#[test]
fn child_status_and_required_evidence_drift_are_refused() {
    let clean = derive().expect("the real tracker and manifest are readable");
    assert_clean(&clean);

    let mut missing = clean.clone();
    missing.coverage.remove(CHILDREN[0]);
    assert!(
        judge(&missing)
            .iter()
            .any(|fault| fault.starts_with("child-coverage:"))
    );

    let mut no_artifacts = clean.clone();
    no_artifacts
        .coverage
        .get_mut(CHILDREN[1])
        .expect("second child")
        .lists
        .get_mut("artifacts")
        .expect("artifacts field")
        .clear();
    let faults = judge(&no_artifacts);
    assert!(faults.iter().any(|fault| fault.starts_with("child-field:")));
    assert!(
        faults
            .iter()
            .any(|fault| fault.starts_with("child-artifact:"))
    );
}

#[test]
fn malformed_or_duplicate_authority_rows_are_refused() {
    let root = root();
    let tracker = read(&root.join(".beads/issues.jsonl")).expect("tracker");
    let manifest = read(&root.join("ci/VERIFICATION_MANIFEST.jsonl")).expect("manifest");

    let parent_issue = tracker
        .lines()
        .find(|line| record_field(line, "id") == Some(Field::Text(PARENT.to_string())))
        .expect("parent issue row");
    let duplicate_tracker = format!("{tracker}\n{parent_issue}\n");
    assert!(
        parse_snapshot(&duplicate_tracker, &manifest)
            .expect_err("a duplicate tracker authority must be refused")
            .contains("duplicate issue")
    );

    let child_coverage = manifest
        .lines()
        .find(|line| record_field(line, "bead") == Some(Field::Text(CHILDREN[0].to_string())))
        .expect("child coverage row");
    let duplicate_manifest = format!("{manifest}\n{child_coverage}\n");
    assert!(
        parse_snapshot(&tracker, &duplicate_manifest)
            .expect_err("a duplicate child coverage authority must be refused")
            .contains("duplicate coverage")
    );

    let malformed = format!("{manifest}\n{{\"bead\":\"{}\"}}\n", CHILDREN[1]);
    assert!(
        parse_snapshot(&tracker, &malformed)
            .expect_err("a malformed child authority must be refused")
            .contains("is not one text field")
    );
}
