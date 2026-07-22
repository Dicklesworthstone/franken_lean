//! Comparison classes as versioned normalizer code (plan §18.1, bead fln-euo).
//!
//! A comparison class says how two transcripts are compared: `exact` (byte
//! equality) or `semantic` (equality after a **named, versioned** normalizer).
//! The constitutional law: a normalizer may strip only declared-nonsemantic fields
//! and can never discard an error body to pass — enforced here structurally
//! ([`Normalizer::apply`] refuses outputs that lost an error marker) and by the
//! seeded-divergence tests (a planted diff must survive normalization).

/// The comparison class a Parity-Ledger row declares.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ComparisonClass {
    /// Byte equality; no normalizer runs.
    Exact,
    /// Equality after the named normalizer version.
    Semantic { normalizer: NormalizerId },
}

/// A frozen normalizer identity. Changing behavior requires a NEW id; ids never
/// change meaning.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NormalizerId {
    /// v1: declared-nonsemantic fields only —
    /// * absolute workspace/toolchain path prefixes → `<PATH>`;
    /// * CRLF → LF;
    /// * trailing whitespace per line.
    ///
    /// Nothing else. Error bodies, positions, severities, and message text all
    /// survive verbatim.
    PathsV1,
}

/// Typed refusal: the normalized output violated the never-discard-an-error law.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ErrorBodyDiscarded {
    pub marker: &'static str,
}

impl std::fmt::Display for ErrorBodyDiscarded {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "normalizer discarded an error body (marker `{}`) — forbidden",
            self.marker
        )
    }
}

/// Markers whose disappearance under normalization is constitutionally forbidden.
const ERROR_MARKERS: [&str; 3] = ["error", "Error", "sorry"];

#[derive(Debug, Clone)]
pub struct Normalizer {
    pub id: NormalizerId,
    /// Absolute prefixes declared nonsemantic (workspace root, toolchain root).
    path_prefixes: Vec<String>,
}

impl Normalizer {
    pub fn paths_v1(path_prefixes: Vec<String>) -> Normalizer {
        Normalizer {
            id: NormalizerId::PathsV1,
            path_prefixes,
        }
    }

    /// Apply the normalizer. Fails typed if an error marker present in the input is
    /// absent from the output — a normalizer can never pass by eating a diagnostic.
    pub fn apply(&self, input: &str) -> Result<String, ErrorBodyDiscarded> {
        let mut out = String::with_capacity(input.len());
        for line in input.split_inclusive('\n') {
            let (body, newline) = match line.strip_suffix('\n') {
                Some(body) => (body, true),
                None => (line, false),
            };
            let body = body.strip_suffix('\r').unwrap_or(body);
            let mut replaced = body.to_string();
            for prefix in &self.path_prefixes {
                if !prefix.is_empty() {
                    replaced = replaced.replace(prefix.as_str(), "<PATH>");
                }
            }
            out.push_str(replaced.trim_end());
            if newline {
                out.push('\n');
            }
        }
        for marker in ERROR_MARKERS {
            if input.contains(marker) && !out.contains(marker) {
                return Err(ErrorBodyDiscarded { marker });
            }
        }
        Ok(out)
    }
}

/// Compare two transcripts under a class. Returns `None` when they agree, or the
/// first divergence rendered for triage — a divergence is a finding, never noise.
pub fn compare(
    class: ComparisonClass,
    ours: &str,
    oracle: &str,
    normalizer: Option<&Normalizer>,
) -> Result<Option<String>, ErrorBodyDiscarded> {
    let (a, b) = match class {
        ComparisonClass::Exact => (ours.to_string(), oracle.to_string()),
        ComparisonClass::Semantic { normalizer: id } => {
            let n = normalizer.filter(|n| n.id == id);
            match n {
                Some(n) => (n.apply(ours)?, n.apply(oracle)?),
                None => {
                    // A declared normalizer that is not supplied cannot silently
                    // degrade to exact: surface it as a divergence.
                    return Ok(Some(format!(
                        "comparison class requires normalizer {id:?} but none was supplied"
                    )));
                }
            }
        }
    };
    if a == b {
        return Ok(None);
    }
    let first = a
        .lines()
        .zip(b.lines())
        .enumerate()
        .find(|(_, (x, y))| x != y)
        .map(|(i, (x, y))| format!("line {}: ours `{x}` vs oracle `{y}`", i + 1))
        .unwrap_or_else(|| {
            let (ours_lines, oracle_lines) = (a.lines().count(), b.lines().count());
            if ours_lines == oracle_lines {
                // Every common line matched and the counts agree, yet the strings
                // differ: the divergence is below line granularity (e.g. a missing
                // final newline). Say so instead of a self-contradictory count.
                format!(
                    "sub-line divergence (line endings or trailing bytes): ours {} bytes, oracle {} bytes",
                    a.len(),
                    b.len()
                )
            } else {
                format!("length divergence: ours {ours_lines} lines, oracle {oracle_lines} lines")
            }
        });
    Ok(Some(first))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn norm() -> Normalizer {
        Normalizer::paths_v1(vec!["/data/projects/franken_lean".to_string()])
    }

    #[test]
    fn paths_and_line_endings_are_declared_nonsemantic() {
        let input = "error: /data/projects/franken_lean/Foo.lean:3:1 bad thing\r\n";
        let out = norm().apply(input).expect("normalizes");
        assert_eq!(out, "error: <PATH>/Foo.lean:3:1 bad thing\n");
    }

    #[test]
    fn error_bodies_survive_and_planted_divergence_is_detected() {
        // Same error, different host paths: semantic-equal.
        let ours = "error: /data/projects/franken_lean/A.lean:1:0 unknown identifier 'x'\n";
        let oracle = "error: /data/projects/franken_lean/A.lean:1:0 unknown identifier 'x'\r\n";
        let class = ComparisonClass::Semantic {
            normalizer: NormalizerId::PathsV1,
        };
        assert_eq!(
            compare(class, ours, oracle, Some(&norm())).expect("law holds"),
            None
        );
        // Planted divergence in the MESSAGE must survive normalization.
        let diverged = ours.replace("'x'", "'y'");
        let finding = compare(class, ours, &diverged, Some(&norm()))
            .expect("law holds")
            .expect("planted divergence detected");
        assert!(finding.contains("'x'") && finding.contains("'y'"));
    }

    #[test]
    fn a_normalizer_that_would_eat_an_error_fails_typed() {
        // A pathological prefix covering the whole message: the error marker would
        // vanish, and apply() must refuse rather than pass.
        let evil = Normalizer {
            id: NormalizerId::PathsV1,
            path_prefixes: vec!["error".to_string()],
        };
        let result = evil.apply("error: it broke\n");
        assert_eq!(result, Err(ErrorBodyDiscarded { marker: "error" }));
    }

    #[test]
    fn exact_class_ignores_the_normalizer_and_missing_normalizer_diverges() {
        let class = ComparisonClass::Exact;
        assert!(
            compare(class, "a\n", "a \n", Some(&norm()))
                .expect("law holds")
                .is_some(),
            "exact means exact"
        );
        let semantic = ComparisonClass::Semantic {
            normalizer: NormalizerId::PathsV1,
        };
        let finding = compare(semantic, "a\n", "a\n", None).expect("law holds");
        assert!(
            finding
                .expect("missing normalizer surfaces")
                .contains("requires normalizer")
        );
    }

    #[test]
    fn sub_line_divergence_is_reported_meaningfully() {
        // Same line content, differing only in the trailing newline: the finding
        // must not claim a self-contradictory "length divergence" of equal counts.
        let finding = compare(ComparisonClass::Exact, "a", "a\n", None)
            .expect("law holds")
            .expect("diverges");
        assert!(finding.contains("sub-line divergence"), "{finding}");
    }

    #[test]
    fn divergence_reports_the_first_line() {
        let finding = compare(ComparisonClass::Exact, "a\nb\nc\n", "a\nx\nc\n", None)
            .expect("law holds")
            .expect("diverges");
        assert!(finding.starts_with("line 2:"));
    }
}
