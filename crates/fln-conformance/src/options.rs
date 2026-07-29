//! The pinned option census: domain validator and the five named suites (bead
//! `franken_lean-4xsz`; plan D5/D9; feeds the drop-in option contract).
//!
//! The census artifact (`contracts/option_census.ndjson`) is extracted mechanically
//! by `scripts/extract/option_census.py` with two-layer totality (blocking rows plus
//! anchored raw-scan reconciliation); the binary half is
//! `scripts/tribunal/option_census_probe.sh`, whose receipt this module holds by
//! CONTENT. Raw observed facts and reviewed policy stay separate: the census rows
//! are facts; [`ROLE_RULES`] is the reviewed classification, expressed as ordered
//! prefix rules so the review is auditable and every row is classified or the suite
//! refuses — an unclassified option is a review-queue item, never a silent default.

/// Versioned schema of the census rows this module validates.
pub const OPTION_CENSUS_SCHEMA: &str = "fln.option-census/1";

/// One parsed census row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OptionRow {
    pub kind: String,
    pub name: String,
    pub value_type: String,
    pub default: String,
    pub source: String,
    pub deprecated_since: Option<String>,
}

/// Typed refusal for a malformed census line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CensusParseError {
    pub line: usize,
    pub reason: String,
}

fn field<'a>(line: &'a str, key: &str) -> Option<&'a str> {
    let tag = format!("\"{key}\":\"");
    let start = line.find(&tag)? + tag.len();
    let rest = &line[start..];
    let mut end = 0;
    let bytes = rest.as_bytes();
    while end < bytes.len() {
        if bytes[end] == b'\\' {
            end += 2;
            continue;
        }
        if bytes[end] == b'"' {
            return Some(&rest[..end]);
        }
        end += 1;
    }
    None
}

/// Parse the census NDJSON. Total: refuses malformed rows with their line.
pub fn parse_census(text: &str) -> Result<Vec<OptionRow>, CensusParseError> {
    let mut rows = Vec::new();
    for (i, line) in text.lines().enumerate() {
        let refuse = |reason: &str| CensusParseError {
            line: i + 1,
            reason: reason.to_string(),
        };
        if field(line, "schema") != Some(OPTION_CENSUS_SCHEMA) {
            return Err(refuse("wrong or missing schema"));
        }
        let kind = field(line, "kind").ok_or_else(|| refuse("missing kind"))?;
        match kind {
            "builtin_option" | "option" | "trace_class" => {
                let (Some(name), Some(vt), Some(default), Some(source)) = (
                    field(line, "name"),
                    field(line, "value_type"),
                    field(line, "default"),
                    field(line, "source"),
                ) else {
                    return Err(refuse("registration row missing a required field"));
                };
                rows.push(OptionRow {
                    kind: kind.to_string(),
                    name: name.to_string(),
                    value_type: vt.to_string(),
                    default: default.to_string(),
                    source: source.to_string(),
                    deprecated_since: field(line, "deprecated_since").map(String::from),
                });
            }
            "dynamic" | "blocking" => {
                if field(line, "source").is_none() {
                    return Err(refuse("dynamic/blocking row without a source anchor"));
                }
                rows.push(OptionRow {
                    kind: kind.to_string(),
                    name: field(line, "name").unwrap_or("?").to_string(),
                    value_type: String::new(),
                    default: String::new(),
                    source: field(line, "source").unwrap_or("?").to_string(),
                    deprecated_since: None,
                });
            }
            other => return Err(refuse(&format!("unknown row kind {other:?}"))),
        }
    }
    Ok(rows)
}

/// The value-type domain the pin actually uses; a new type is a census event,
/// not a silent pass.
pub const KNOWN_VALUE_TYPES: &[&str] = &["Bool", "Nat", "Int", "String", "Name"];

/// Named default constants at the pin, each binary-resolved by the probe's
/// cross-check (comment franken_lean-4xsz:1677). A named default outside this
/// table refuses domain validation until resolved by measurement.
pub const RESOLVED_NAMED_DEFAULTS: &[(&str, &str)] = &[
    ("defIndent", "2"),
    ("defUnicode", "true"),
    ("defWidth", "120"),
    ("defaultMaxRecDepth", "512"),
];

/// A domain violation, carrying the row's name and anchor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DomainViolation {
    pub name: String,
    pub source: String,
    pub reason: String,
}

fn default_well_formed(row: &OptionRow) -> bool {
    let d = row.default.as_str();
    let literal_ok = match row.value_type.as_str() {
        "Bool" => d == "true" || d == "false",
        "Nat" => !d.is_empty() && d.bytes().all(|b| b.is_ascii_digit() || b == b'_'),
        "Int" => {
            let body = d.strip_prefix('-').unwrap_or(d);
            !body.is_empty() && body.bytes().all(|b| b.is_ascii_digit() || b == b'_')
        }
        "String" => d.starts_with("\\\"") || !d.contains(":="),
        "Name" => !d.is_empty(),
        _ => false,
    };
    literal_ok || RESOLVED_NAMED_DEFAULTS.iter().any(|(n, _)| *n == d)
}

/// The domain validator: every registration row well-formed, or named violations.
pub fn validate_domains(rows: &[OptionRow]) -> Vec<DomainViolation> {
    let mut violations = Vec::new();
    for row in rows {
        if row.kind == "dynamic" || row.kind == "blocking" {
            continue;
        }
        let mut refuse = |reason: String| {
            violations.push(DomainViolation {
                name: row.name.clone(),
                source: row.source.clone(),
                reason,
            })
        };
        if row.name.is_empty()
            || !row
                .name
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '.' || c == '_' || c == '«' || c == '»')
        {
            refuse("option name outside the identifier grammar".to_string());
        }
        if !KNOWN_VALUE_TYPES.contains(&row.value_type.as_str()) {
            refuse(format!(
                "value type {:?} outside the measured domain",
                row.value_type
            ));
        } else if !default_well_formed(row) {
            refuse(format!(
                "default {:?} neither a literal of {} nor a resolved named constant",
                row.default, row.value_type
            ));
        }
        if row.kind == "trace_class" && (row.value_type != "Bool" || row.default != "false") {
            refuse("trace-class options are Bool:false by construction".to_string());
        }
        let anchored = row.source.rsplit_once(':').is_some_and(|(path, line)| {
            path.starts_with("vendor/lean4-src/src/") && line.bytes().all(|b| b.is_ascii_digit())
        });
        if !anchored {
            refuse(format!(
                "source anchor {:?} is not path:line into the pin",
                row.source
            ));
        }
    }
    violations
}

/// The reviewed role classification: ordered prefix rules, most specific first.
/// This is POLICY, deliberately separate from the extracted facts, and total by
/// construction of the suite that applies it — an unmatched option refuses.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum OptionRole {
    /// Changes accepted terms, verdicts, or elaboration semantics: cache-key input.
    Semantic,
    /// Budget/limit semantics: verdict-relevant through timeouts (cache-key input).
    ResourceBudget,
    /// Output shape only (pretty printing, formatting, message rendering).
    Presentation,
    /// Diagnostics and tracing: never semantic, never a cache key.
    Diagnostic,
    /// Server/frontend plumbing (async, internal wiring).
    Infrastructure,
}

/// Ordered (prefix, role) rules. First match wins; review happens HERE.
pub const ROLE_RULES: &[(&str, OptionRole)] = &[
    ("trace.", OptionRole::Diagnostic),
    ("diagnostics", OptionRole::Diagnostic),
    ("profiler", OptionRole::Diagnostic),
    ("debug.", OptionRole::Diagnostic),
    ("pp.", OptionRole::Presentation),
    ("format.", OptionRole::Presentation),
    ("printMessageEndPos", OptionRole::Presentation),
    ("linter.", OptionRole::Diagnostic),
    ("weak.", OptionRole::Infrastructure),
    ("maxHeartbeats", OptionRole::ResourceBudget),
    ("maxRecDepth", OptionRole::ResourceBudget),
    ("synthInstance.maxHeartbeats", OptionRole::ResourceBudget),
    ("synthInstance.maxSize", OptionRole::ResourceBudget),
    ("exponentiation.threshold", OptionRole::ResourceBudget),
    ("Elab.async", OptionRole::Infrastructure),
    ("Elab.inServer", OptionRole::Infrastructure),
    ("internal.", OptionRole::Infrastructure),
    ("stderrAsMessages", OptionRole::Infrastructure),
    ("server.", OptionRole::Infrastructure),
    ("interpreter.", OptionRole::Infrastructure),
    // The broad semantic tail: elaboration/kernel/compiler behavior switches.
    ("", OptionRole::Semantic),
];

pub fn classify_role(name: &str) -> OptionRole {
    for (prefix, role) in ROLE_RULES {
        if name.starts_with(prefix) {
            return *role;
        }
    }
    OptionRole::Semantic
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    const CENSUS: &str = include_str!("../../../contracts/option_census.ndjson");
    const PROBE_RECEIPT: &str = include_str!("../evidence/option_census/probe_v4.32.0.jsonl");

    #[test]
    fn option_inventory_totality() {
        let rows = parse_census(CENSUS).expect("the committed census parses totally");
        let count = |k: &str| rows.iter().filter(|r| r.kind == k).count();
        assert_eq!(rows.len(), 660, "row census");
        assert_eq!(count("builtin_option"), 257, "builtin census");
        assert_eq!(count("option"), 3, "plain-option census");
        assert_eq!(count("trace_class"), 397, "trace census");
        assert_eq!(count("dynamic"), 3, "dynamic census");
        assert_eq!(
            count("blocking"),
            0,
            "a blocking row means the pin grew a shape"
        );
        // Name uniqueness across all registrations.
        let mut names: BTreeMap<&str, &str> = BTreeMap::new();
        for r in rows
            .iter()
            .filter(|r| r.kind != "dynamic" && r.kind != "blocking")
        {
            if let Some(first) = names.insert(&r.name, &r.source) {
                panic!("duplicate option {} at {} and {}", r.name, first, r.source);
            }
        }
        // Deprecation facts are captured, not lost: exactly the two measured rows.
        let deprecated: Vec<&OptionRow> = rows
            .iter()
            .filter(|r| r.deprecated_since.is_some())
            .collect();
        assert_eq!(deprecated.len(), 2, "deprecated census");
        for d in &deprecated {
            assert!(d.name.starts_with("backward.eqns."), "{}", d.name);
            assert_eq!(d.deprecated_since.as_deref(), Some("2026-03-30"));
        }
        // Hostile bytes refuse typed, never panic.
        for junk in [
            "not json",
            "{\"schema\":\"wrong/1\",\"kind\":\"builtin_option\"}",
            "{\"schema\":\"fln.option-census/1\",\"kind\":\"mystery\",\"source\":\"x:1\"}",
            "{\"schema\":\"fln.option-census/1\",\"kind\":\"builtin_option\",\"name\":\"x\"}",
        ] {
            assert!(parse_census(junk).is_err(), "must refuse: {junk}");
        }
    }

    #[test]
    fn option_default_scope_model() {
        let rows = parse_census(CENSUS).expect("parses");
        let violations = validate_domains(&rows);
        assert!(
            violations.is_empty(),
            "domain violations against the pin's own registry:\n{violations:#?}"
        );
        // The validator is not vacuous: a planted bad row is refused in every
        // dimension it claims to check.
        let bad = OptionRow {
            kind: "builtin_option".to_string(),
            name: "bad name!".to_string(),
            value_type: "Float".to_string(),
            default: "maybe".to_string(),
            source: "elsewhere".to_string(),
            deprecated_since: None,
        };
        let planted = validate_domains(&[bad]);
        assert_eq!(
            planted.len(),
            3,
            "name, type, anchor all refused: {planted:#?}"
        );
        // And a wrong-typed default on a known type is its own refusal.
        let bad_default = OptionRow {
            kind: "builtin_option".to_string(),
            name: "x.y".to_string(),
            value_type: "Nat".to_string(),
            default: "true".to_string(),
            source: "vendor/lean4-src/src/Lean/X.lean:1".to_string(),
            deprecated_since: None,
        };
        assert_eq!(validate_domains(&[bad_default]).len(), 1);
    }

    #[test]
    fn option_precedence_lattice() {
        // The measured lattice facts live in the probe receipt, held by content:
        // CLI default application, in-file scoped override, scope restoration,
        // and zero-disables — all from ONE run against the real binary.
        let row = PROBE_RECEIPT
            .lines()
            .find(|l| l.contains("\"step\":\"precedence\""))
            .expect("the precedence cell is in the receipt");
        for fact in [
            "\"cli_default_applied\":true",
            "\"scoped_override_wins\":true",
            "\"scope_restored\":true",
            "\"zero_disables\":true",
        ] {
            assert!(row.contains(fact), "missing {fact} in {row}");
        }
        // Refusal shapes held, all three, each typed distinctly.
        for step in ["unknown", "malformed-nat", "malformed-bool"] {
            let row = PROBE_RECEIPT
                .lines()
                .find(|l| l.contains(&format!("\"step\":\"{step}\"")))
                .unwrap_or_else(|| panic!("{step} cell missing"));
            assert!(row.contains("\"refused\":true") && row.contains("\"shape_held\":true"));
        }
    }

    #[test]
    fn option_semantic_effect_classification() {
        let rows = parse_census(CENSUS).expect("parses");
        let mut by_role: BTreeMap<OptionRole, usize> = BTreeMap::new();
        for r in rows
            .iter()
            .filter(|r| r.kind != "dynamic" && r.kind != "blocking")
        {
            *by_role.entry(classify_role(&r.name)).or_default() += 1;
        }
        // Every option classified (the catch-all makes totality structural; the
        // REVIEW lives in the ordered rules above it). The census by role is
        // pinned so a rule edit shows its blast radius here.
        let total: usize = by_role.values().sum();
        assert_eq!(total, 657, "every registration row classified");
        assert_eq!(by_role[&OptionRole::Diagnostic], 452, "diagnostic census");
        assert_eq!(
            by_role[&OptionRole::Presentation],
            80,
            "presentation census"
        );
        assert_eq!(by_role[&OptionRole::ResourceBudget], 5, "budget census");
        assert_eq!(
            by_role[&OptionRole::Infrastructure],
            6,
            "infrastructure census"
        );
        assert_eq!(by_role[&OptionRole::Semantic], 114, "semantic census");
        // Direction cells: the classification is not order-blind.
        assert_eq!(classify_role("trace.Meta.isDefEq"), OptionRole::Diagnostic);
        assert_eq!(classify_role("pp.all"), OptionRole::Presentation);
        assert_eq!(classify_role("maxHeartbeats"), OptionRole::ResourceBudget);
        assert_eq!(
            classify_role("backward.eqns.nonrecursive"),
            OptionRole::Semantic
        );
    }

    #[test]
    fn option_census_no_mock_e2e() {
        // The probe receipt is the no-mock artifact: produced by the REAL pinned
        // binary via scripts/tribunal/option_census_probe.sh, held by content.
        assert!(
            PROBE_RECEIPT
                .lines()
                .all(|l| l.contains("\"schema\":\"fln-x4-option-probe/1\"")),
            "unversioned receipt row"
        );
        let dump = PROBE_RECEIPT
            .lines()
            .find(|l| l.contains("\"step\":\"dump\""))
            .expect("dump cell");
        assert!(dump.contains("\"runs_identical\":true"));
        assert!(dump.contains("\"binary_total\":\"661\""));
        assert!(dump.contains("binary_only_allowlisted=4"));
        assert!(dump.contains("source_rows=657"));
        assert!(
            PROBE_RECEIPT
                .contains("\"step\":\"negative_control\",\"corrupted_census_refused\":true"),
            "the receipt must carry its negative control"
        );
        assert!(
            PROBE_RECEIPT.contains("\"pin\":\"v4.32.0\"")
                && PROBE_RECEIPT.contains("\"verdict\":\"all-cells-hold\""),
            "the summary must bind the pin"
        );
    }
}
