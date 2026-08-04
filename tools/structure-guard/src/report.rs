//! Human and robot (NDJSON) rendering. Robot output is line-oriented, schema-versioned,
//! deterministic (findings pre-sorted by the checker), and never mixed with human
//! decoration (AGENTS.md, Agent Ergonomics).

use crate::NDJSON_SCHEMA;
use crate::checks::{AUTHORITY_COUNT_RULE, Finding, RunOutcome, TerminalSubject};
use crate::mode_closure::ModeClosureFacts;

/// FNV-1a 64-bit — a dependency-free content digest for run provenance. Labeled as
/// `fnv1a64` in output; not a cryptographic hash (fln-hash owns those, later).
pub fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in bytes {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

pub fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

pub fn render_human(root_display: &str, outcome: &RunOutcome) -> String {
    let mut out = String::new();
    let unestablished = outcome.unestablished();
    let unestablished_display = if unestablished.is_empty() {
        "none".to_string()
    } else {
        unestablished.join(",")
    };
    out.push_str(&format!(
        "structure-guard: root={root_display} root-identity={} crates={} edges={} graph-digest=fnv1a64:{:016x} contract-handoff-root={} data-grade={} unestablished={} governed-root=fnv1a64:{:016x}\n",
        outcome.root_identity,
        outcome.crate_count,
        outcome.edge_count,
        outcome.graph_digest,
        outcome.contract_handoff_root.as_deref().unwrap_or("unavailable"),
        outcome.data_grade(),
        unestablished_display,
        outcome.governed_root_after,
    ));
    // The human reader has the same problem the robot reader had: a verdict with no
    // scope beside it. Same facts, same derivation, one line up from the verdict.
    let d18 = &outcome.mode_closure;
    out.push_str(&format!(
        "structure-guard: d18-mode-closure scan={} product-roots={} closures-scanned={} closure-nodes={} frontier-surfaces={} nodes={} edges={}\n",
        d18.scan_class(),
        d18.product_roots,
        d18.closures_scanned,
        d18.closure_nodes,
        d18.frontier_surfaces,
        d18.nodes,
        d18.edges,
    ));
    // The covenant was walked on every run and its number thrown away unless it exceeded the
    // limit, so the only counter anyone could actually invoke was `wc -l` — and two of the
    // three kernel-size figures ever written down in this repository were that raw count
    // (bead `franken_lean-kernel-loc-covenant-not-disclosed-t0g7`). A wall, printed as a gauge.
    out.push_str(&covenant_human_line(&outcome.covenants));
    for f in &outcome.findings {
        out.push_str(&format!("{} {}: {}\n", f.code, f.path, f.detail));
    }
    out.push_str(&format!(
        "structure-guard: {} — {} finding(s)\n",
        outcome.verdict().to_ascii_uppercase(),
        outcome.findings.len()
    ));
    out
}

fn finding_ndjson(f: &Finding) -> String {
    format!(
        "{{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"finding\",\"code\":\"{}\",\"severity\":\"error\",\"path\":\"{}\",\"detail\":\"{}\"}}",
        json_escape(f.code),
        json_escape(&f.path),
        json_escape(&f.detail)
    )
}

fn optional_json_string(value: Option<&str>) -> String {
    value.map_or_else(
        || "null".to_string(),
        |value| format!("\"{}\"", json_escape(value)),
    )
}

/// The D18 mode-closure scope, rendered beside the verdict it qualifies (bead
/// `fln-q8qt`).
///
/// The counts existed on `RunOutcome` from the day D18 was registered and only the test
/// binary could read them, so a reader of a guard run saw `verdict=pass` with no way to
/// learn that the D18 check had traversed nothing at all. Emitting them here puts the
/// scope of the pass at the point the pass is read; `scan_class` is derived from
/// `closures_scanned` rather than stored, and a consumer re-checks that law against these
/// same numbers.
fn mode_closure_json(facts: &ModeClosureFacts) -> String {
    format!(
        "{{\"scan_class\":\"{}\",\"frontier_surfaces\":{},\"product_roots\":{},\"closures_scanned\":{},\"closure_nodes\":{},\"nodes\":{},\"edges\":{}}}",
        facts.scan_class(),
        facts.frontier_surfaces,
        facts.product_roots,
        facts.closures_scanned,
        facts.closure_nodes,
        facts.nodes,
        facts.edges,
    )
}

fn json_string_array(values: &[String]) -> String {
    let values = values
        .iter()
        .map(|value| format!("\"{}\"", json_escape(value)))
        .collect::<Vec<_>>()
        .join(",");
    format!("[{values}]")
}

/// Render the measured line-count covenants for the human record.
///
/// Every field is carried from the enforcing walk: `loc` is the value `count_loc` returned,
/// `limit` the declared cap, `headroom` their difference. Nothing here recomputes anything, so
/// there is no second copy that could drift from the first — which is the whole point of the
/// bead (`franken_lean-kernel-loc-covenant-not-disclosed-t0g7`). Tenths of a percent, so a
/// trend is readable without putting a float in an evidence record.
///
/// The same facts are emitted as `line_count_covenants` in the robot `run_end` line. The
/// versioned robot contract binds the producer, its evidence validator, shell contracts, and
/// fixtures together, so an omission cannot silently turn a machine-readable gauge back into a
/// human-only wall.
fn covenant_human_line(covenants: &[crate::checks::CovenantFact]) -> String {
    if covenants.is_empty() {
        // Not "no covenants" — this walk declares at least fln-kernel, so an empty set is a
        // counter that stopped counting. Said out loud rather than rendered as a blank, because
        // a disclosure that silently vanishes is worse than one that was never written.
        return "structure-guard: line-count-covenants NONE MEASURED — the covenant walk \
                produced no facts; this is a broken measurement, not a clean crate\n"
            .to_string();
    }
    let mut out = String::new();
    for c in covenants {
        // A zero limit is not a covenant; reporting it beats dividing by it.
        let permille = (c.loc * 1000).checked_div(c.limit).unwrap_or(0);
        out.push_str(&format!(
            "structure-guard: line-count-covenant {} loc={} max-loc={} headroom={} used={}.{}%\n",
            c.crate_name,
            c.loc,
            c.limit,
            c.headroom(),
            permille / 10,
            permille % 10
        ));
    }
    out
}

/// Render the measured covenants as one terminal robot field.
///
/// This reads the facts already carried out of the enforcing walk. `headroom` is derived here
/// from the same fact rather than counted again: an over-limit crate emits zero headroom and its
/// finding remains the enforcement verdict. The evidence consumer checks that relation, so a
/// transcribed number cannot become an independent, drifting producer.
fn line_count_covenants_json(covenants: &[crate::checks::CovenantFact]) -> String {
    let rows = covenants
        .iter()
        .map(|fact| {
            format!(
                "{{\"crate_name\":\"{}\",\"loc\":{},\"limit\":{},\"headroom\":{}}}",
                json_escape(&fact.crate_name),
                fact.loc,
                fact.limit,
                fact.headroom(),
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    format!("[{rows}]")
}

pub fn render_ndjson(root_display: &str, outcome: &RunOutcome, duration_ms: u128) -> String {
    let mut lines = Vec::with_capacity(outcome.findings.len() + 2);
    let compiler = &outcome.compiler_identity;
    let environment = &outcome.admitted_environment;
    let unestablished = outcome.unestablished();
    lines.push(format!(
        "{{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"run_start\",\"root\":\"{}\",\"root_identity\":\"{}\",\"graph_digest\":\"fnv1a64:{:016x}\",\"crates\":{},\"edges\":{},\"authority_inventory\":{{\"package_class\":\"workspace-graph-exact\",\"packages\":{},\"target_class\":\"cargo-auto-discovery-closed\",\"targets\":{},\"feature_class\":\"manifest-enumerated\",\"features\":{},\"target_triple_class\":\"suite-lock-declared\",\"target_triples\":{}}},\"effective_compiler_identity\":{{\"source\":\"{}\",\"channel\":{},\"release\":{},\"commit\":{},\"host\":{},\"contract_declared\":{},\"configuration_match\":{},\"contract_match\":{}}},\"admitted_environment\":{{\"policy\":\"{}\",\"admitted_names\":{},\"compiler_override_names\":{}}}}}",
        json_escape(root_display),
        json_escape(&outcome.root_identity),
        outcome.graph_digest,
        outcome.crate_count,
        outcome.edge_count,
        outcome.authority_inventory.packages,
        outcome.authority_inventory.targets,
        outcome.authority_inventory.features,
        outcome.authority_inventory.target_triples,
        json_escape(compiler.source),
        optional_json_string(compiler.channel.as_deref()),
        optional_json_string(compiler.release.as_deref()),
        optional_json_string(compiler.commit.as_deref()),
        optional_json_string(compiler.host.as_deref()),
        compiler.contract_declared,
        compiler.configuration_match,
        compiler.contract_match,
        json_escape(environment.policy),
        json_string_array(&environment.admitted_names),
        json_string_array(&environment.compiler_override_names),
    ));
    lines.extend(outcome.findings.iter().map(finding_ndjson));
    lines.push(format!(
        "{{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"run_end\",\"verdict\":\"{}\",\"exit_code\":{},\"findings\":{},\"authority\":\"{}\",\"data_grade\":\"{}\",\"unestablished\":{},\"contract_handoff_root\":{},\"traversal\":{{\"directories_visited\":{},\"files_discovered\":{},\"files_scanned\":{},\"files_skipped_unreadable\":{}}},\"mode_closure\":{},\"line_count_covenants\":{},\"authority_count_rule\":\"{AUTHORITY_COUNT_RULE}\",\"authority_count_rule_holds\":{},\"governed_root_before\":\"fnv1a64:{:016x}\",\"governed_root_after\":\"fnv1a64:{:016x}\",\"governed_root_unchanged\":{},\"duration_ms\":{duration_ms}}}",
        outcome.verdict(),
        outcome.exit_code(),
        outcome.findings.len(),
        outcome.authority.as_str(),
        outcome.data_grade(),
        json_string_array(&unestablished),
        optional_json_string(outcome.contract_handoff_root.as_deref()),
        outcome.traversal.directories_visited,
        outcome.traversal.files_discovered,
        outcome.traversal.files_scanned,
        outcome.traversal.files_skipped_unreadable,
        mode_closure_json(&outcome.mode_closure),
        line_count_covenants_json(&outcome.covenants),
        outcome.traversal.count_rule_holds(),
        outcome.governed_root_before,
        outcome.governed_root_after,
        outcome.governed_root_before == outcome.governed_root_after,
    ));
    lines.join("\n") + "\n"
}

/// Render a robot-visible setup failure. Robot mode must never move diagnostics to a
/// human-only stream or omit its terminal record.
pub fn render_setup_failure_ndjson(root_display: &str, error: &str, duration_ms: u128) -> String {
    let subject = TerminalSubject::NotStarted;
    format!(
        "{{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"run_start\",\"root\":\"{}\",\"root_identity\":null,\"graph_digest\":null,\"crates\":null,\"edges\":null,\"authority_inventory\":null,\"effective_compiler_identity\":null,\"admitted_environment\":null}}\n\
         {{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"run_end\",\"verdict\":\"setup_error\",\"exit_code\":2,\"findings\":0,\"authority\":\"not_established\",\"data_grade\":\"{}\",\"unestablished\":{},\"contract_handoff_root\":null,\"traversal\":null,\"mode_closure\":null,\"line_count_covenants\":null,\"authority_count_rule\":\"{AUTHORITY_COUNT_RULE}\",\"authority_count_rule_holds\":false,\"governed_root_before\":null,\"governed_root_after\":null,\"governed_root_unchanged\":false,\"reason_code\":\"setup_failure\",\"detail\":\"{}\",\"duration_ms\":{duration_ms}}}\n",
        json_escape(root_display),
        subject.data_grade(),
        json_string_array(&subject.unestablished()),
        json_escape(error)
    )
}

/// Render a robot-visible CLI parse failure. The CLI did not reach workspace setup,
/// but its request still receives a complete run envelope and terminal exit status.
pub fn render_cli_failure_ndjson(root_display: &str, error: &str, duration_ms: u128) -> String {
    let subject = TerminalSubject::NotStarted;
    format!(
        "{{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"run_start\",\"root\":\"{}\",\"root_identity\":null,\"graph_digest\":null,\"crates\":null,\"edges\":null,\"authority_inventory\":null,\"effective_compiler_identity\":null,\"admitted_environment\":null}}\n\
         {{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"run_end\",\"verdict\":\"setup_error\",\"exit_code\":2,\"findings\":0,\"authority\":\"not_established\",\"data_grade\":\"{}\",\"unestablished\":{},\"contract_handoff_root\":null,\"traversal\":null,\"mode_closure\":null,\"line_count_covenants\":null,\"authority_count_rule\":\"{AUTHORITY_COUNT_RULE}\",\"authority_count_rule_holds\":false,\"governed_root_before\":null,\"governed_root_after\":null,\"governed_root_unchanged\":false,\"reason_code\":\"cli_parse_failure\",\"detail\":\"{}\",\"duration_ms\":{duration_ms}}}\n",
        json_escape(root_display),
        subject.data_grade(),
        json_string_array(&subject.unestablished()),
        json_escape(error)
    )
}

/// Render help without leaking human decoration into robot mode. Help is a successful
/// request response, not a structural verdict, and is labeled accordingly.
pub fn render_help_ndjson(usage: &str, duration_ms: u128) -> String {
    let subject = TerminalSubject::NoAudit;
    format!(
        "{{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"run_start\",\"root\":null,\"root_identity\":null,\"graph_digest\":null,\"crates\":null,\"edges\":null,\"authority_inventory\":null,\"effective_compiler_identity\":null,\"admitted_environment\":null}}\n\
         {{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"help\",\"usage\":\"{}\"}}\n\
         {{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"run_end\",\"verdict\":\"pass\",\"exit_code\":0,\"findings\":0,\"authority\":\"not_applicable\",\"data_grade\":\"{}\",\"unestablished\":{},\"contract_handoff_root\":null,\"traversal\":null,\"mode_closure\":null,\"line_count_covenants\":null,\"authority_count_rule\":\"{AUTHORITY_COUNT_RULE}\",\"authority_count_rule_holds\":false,\"governed_root_before\":null,\"governed_root_after\":null,\"governed_root_unchanged\":false,\"reason_code\":\"help_requested\",\"duration_ms\":{duration_ms}}}\n",
        json_escape(usage),
        subject.data_grade(),
        json_string_array(&subject.unestablished()),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fnv_vectors() {
        assert_eq!(fnv1a64(b""), 0xcbf29ce484222325);
        assert_eq!(fnv1a64(b"a"), 0xaf63dc4c8601ec8c);
    }

    #[test]
    fn escaping() {
        assert_eq!(json_escape("a\"b\\c\nd"), "a\\\"b\\\\c\\nd");
    }

    /// The D18 scope must be a function of the facts, not a constant.
    ///
    /// The live workspace scan is vacuous — no crate declares a mode-bound product root —
    /// so every real run today renders `"scan_class":"vacuous"`. A renderer that
    /// hardcoded that word, or that transcribed the wrong count into the wrong key, would
    /// be indistinguishable from a correct one against the real workspace. These two
    /// cases are the only place the traversed rendering exists at all, which is why they
    /// carry distinct non-equal numbers in every field.
    #[test]
    fn the_rendered_d18_scope_tracks_the_facts_rather_than_a_constant() {
        let vacuous = ModeClosureFacts {
            frontier_surfaces: 1,
            product_roots: 0,
            closures_scanned: 0,
            closure_nodes: 0,
            nodes: 33,
            edges: 28,
        };
        assert_eq!(
            mode_closure_json(&vacuous),
            "{\"scan_class\":\"vacuous\",\"frontier_surfaces\":1,\"product_roots\":0,\
             \"closures_scanned\":0,\"closure_nodes\":0,\"nodes\":33,\"edges\":28}"
        );
        let traversed = ModeClosureFacts {
            frontier_surfaces: 2,
            product_roots: 3,
            closures_scanned: 4,
            closure_nodes: 5,
            nodes: 6,
            edges: 7,
        };
        assert_eq!(
            mode_closure_json(&traversed),
            "{\"scan_class\":\"traversed\",\"frontier_surfaces\":2,\"product_roots\":3,\
             \"closures_scanned\":4,\"closure_nodes\":5,\"nodes\":6,\"edges\":7}"
        );
    }

    #[test]
    fn robot_covenant_facts_carry_the_measured_value_and_derived_headroom() {
        let facts = [
            crate::checks::CovenantFact {
                crate_name: "fln-kernel".to_string(),
                loc: 6_112,
                limit: 12_000,
            },
            crate::checks::CovenantFact {
                crate_name: "fln-over-limit".to_string(),
                loc: 12_001,
                limit: 12_000,
            },
        ];
        assert_eq!(
            line_count_covenants_json(&facts),
            "[{\"crate_name\":\"fln-kernel\",\"loc\":6112,\"limit\":12000,\"headroom\":5888},{\"crate_name\":\"fln-over-limit\",\"loc\":12001,\"limit\":12000,\"headroom\":0}]"
        );
    }

    #[test]
    fn robot_setup_failure_is_terminal_and_escaped() {
        let rendered = render_setup_failure_ndjson("a\"b", "bad\nroot", 7);
        let lines: Vec<_> = rendered.lines().collect();
        assert_eq!(lines.len(), 2);
        assert!(lines[0].contains("\\\"b"));
        assert!(lines[1].contains("\"verdict\":\"setup_error\""));
        assert!(lines[1].contains("\"exit_code\":2"));
        assert!(lines[1].contains("\"data_grade\":\"not_established\""));
        assert!(lines[1].contains("\"unestablished\":[]"));
        assert!(lines[1].contains("\"line_count_covenants\":null"));
        assert!(lines[1].contains("bad\\nroot"));
    }

    #[test]
    fn robot_cli_failure_has_a_distinct_reason_code() {
        let rendered = render_cli_failure_ndjson(".", "unknown `x`", 3);
        let lines: Vec<_> = rendered.lines().collect();
        assert_eq!(lines.len(), 2);
        assert!(lines.iter().all(|line| line.contains(NDJSON_SCHEMA)));
        assert!(lines[1].contains("\"reason_code\":\"cli_parse_failure\""));
        assert!(lines[1].contains("\"exit_code\":2"));
        assert!(lines[1].contains("\"data_grade\":\"not_established\""));
        assert!(lines[1].contains("\"unestablished\":[]"));
        assert!(lines[1].contains("\"line_count_covenants\":null"));
    }

    #[test]
    fn robot_help_is_machine_only_and_terminal() {
        let rendered = render_help_ndjson("usage: x\n  --flag", 2);
        let lines: Vec<_> = rendered.lines().collect();
        assert_eq!(lines.len(), 3);
        assert!(lines.iter().all(|line| line.starts_with('{')));
        assert!(lines.iter().all(|line| line.contains(NDJSON_SCHEMA)));
        assert!(lines[1].contains("\"event\":\"help\""));
        assert!(lines[1].contains("usage: x\\n"));
        assert!(lines[2].contains("\"reason_code\":\"help_requested\""));
        assert!(lines[2].contains("\"exit_code\":0"));
        assert!(lines[2].contains("\"data_grade\":\"not_applicable\""));
        assert!(lines[2].contains("\"unestablished\":[]"));
        assert!(lines[2].contains("\"line_count_covenants\":null"));
    }
}
