//! Human and robot (NDJSON) rendering. Robot output is line-oriented, schema-versioned,
//! deterministic (findings pre-sorted by the checker), and never mixed with human
//! decoration (AGENTS.md, Agent Ergonomics).

use crate::NDJSON_SCHEMA;
use crate::checks::{AUTHORITY_COUNT_RULE, Finding, RunOutcome};

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
    out.push_str(&format!(
        "structure-guard: root={root_display} root-identity={} crates={} edges={} graph-digest=fnv1a64:{:016x} contract-handoff-root={} governed-root=fnv1a64:{:016x}\n",
        outcome.root_identity,
        outcome.crate_count,
        outcome.edge_count,
        outcome.graph_digest,
        outcome.contract_handoff_root.as_deref().unwrap_or("unavailable"),
        outcome.governed_root_after,
    ));
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

fn json_string_array(values: &[String]) -> String {
    let values = values
        .iter()
        .map(|value| format!("\"{}\"", json_escape(value)))
        .collect::<Vec<_>>()
        .join(",");
    format!("[{values}]")
}

pub fn render_ndjson(root_display: &str, outcome: &RunOutcome, duration_ms: u128) -> String {
    let mut lines = Vec::with_capacity(outcome.findings.len() + 2);
    let compiler = &outcome.compiler_identity;
    let environment = &outcome.admitted_environment;
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
        "{{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"run_end\",\"verdict\":\"{}\",\"exit_code\":{},\"findings\":{},\"authority\":\"{}\",\"contract_handoff_root\":{},\"traversal\":{{\"directories_visited\":{},\"files_discovered\":{},\"files_scanned\":{},\"files_skipped_unreadable\":{}}},\"authority_count_rule\":\"{AUTHORITY_COUNT_RULE}\",\"authority_count_rule_holds\":{},\"governed_root_before\":\"fnv1a64:{:016x}\",\"governed_root_after\":\"fnv1a64:{:016x}\",\"governed_root_unchanged\":{},\"duration_ms\":{duration_ms}}}",
        outcome.verdict(),
        outcome.exit_code(),
        outcome.findings.len(),
        outcome.authority.as_str(),
        optional_json_string(outcome.contract_handoff_root.as_deref()),
        outcome.traversal.directories_visited,
        outcome.traversal.files_discovered,
        outcome.traversal.files_scanned,
        outcome.traversal.files_skipped_unreadable,
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
    format!(
        "{{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"run_start\",\"root\":\"{}\",\"root_identity\":null,\"graph_digest\":null,\"crates\":null,\"edges\":null,\"authority_inventory\":null,\"effective_compiler_identity\":null,\"admitted_environment\":null}}\n\
         {{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"run_end\",\"verdict\":\"setup_error\",\"exit_code\":2,\"findings\":0,\"authority\":\"not_established\",\"contract_handoff_root\":null,\"traversal\":null,\"authority_count_rule\":\"{AUTHORITY_COUNT_RULE}\",\"authority_count_rule_holds\":false,\"governed_root_before\":null,\"governed_root_after\":null,\"governed_root_unchanged\":false,\"reason_code\":\"setup_failure\",\"detail\":\"{}\",\"duration_ms\":{duration_ms}}}\n",
        json_escape(root_display),
        json_escape(error)
    )
}

/// Render a robot-visible CLI parse failure. The CLI did not reach workspace setup,
/// but its request still receives a complete run envelope and terminal exit status.
pub fn render_cli_failure_ndjson(root_display: &str, error: &str, duration_ms: u128) -> String {
    format!(
        "{{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"run_start\",\"root\":\"{}\",\"root_identity\":null,\"graph_digest\":null,\"crates\":null,\"edges\":null,\"authority_inventory\":null,\"effective_compiler_identity\":null,\"admitted_environment\":null}}\n\
         {{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"run_end\",\"verdict\":\"setup_error\",\"exit_code\":2,\"findings\":0,\"authority\":\"not_established\",\"contract_handoff_root\":null,\"traversal\":null,\"authority_count_rule\":\"{AUTHORITY_COUNT_RULE}\",\"authority_count_rule_holds\":false,\"governed_root_before\":null,\"governed_root_after\":null,\"governed_root_unchanged\":false,\"reason_code\":\"cli_parse_failure\",\"detail\":\"{}\",\"duration_ms\":{duration_ms}}}\n",
        json_escape(root_display),
        json_escape(error)
    )
}

/// Render help without leaking human decoration into robot mode. Help is a successful
/// request response, not a structural verdict, and is labeled accordingly.
pub fn render_help_ndjson(usage: &str, duration_ms: u128) -> String {
    format!(
        "{{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"run_start\",\"root\":null,\"root_identity\":null,\"graph_digest\":null,\"crates\":null,\"edges\":null,\"authority_inventory\":null,\"effective_compiler_identity\":null,\"admitted_environment\":null}}\n\
         {{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"help\",\"usage\":\"{}\"}}\n\
         {{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"run_end\",\"verdict\":\"pass\",\"exit_code\":0,\"findings\":0,\"authority\":\"not_applicable\",\"contract_handoff_root\":null,\"traversal\":null,\"authority_count_rule\":\"{AUTHORITY_COUNT_RULE}\",\"authority_count_rule_holds\":false,\"governed_root_before\":null,\"governed_root_after\":null,\"governed_root_unchanged\":false,\"reason_code\":\"help_requested\",\"duration_ms\":{duration_ms}}}\n",
        json_escape(usage)
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

    #[test]
    fn robot_setup_failure_is_terminal_and_escaped() {
        let rendered = render_setup_failure_ndjson("a\"b", "bad\nroot", 7);
        let lines: Vec<_> = rendered.lines().collect();
        assert_eq!(lines.len(), 2);
        assert!(lines[0].contains("\\\"b"));
        assert!(lines[1].contains("\"verdict\":\"setup_error\""));
        assert!(lines[1].contains("\"exit_code\":2"));
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
    }
}
