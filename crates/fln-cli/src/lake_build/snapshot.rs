//! The content-bound record of the last successful `lake build` (bead
//! `franken_lean-z8j.1.2`): what each module was built from and what it produced.
//!
//! It is provenance for `fln build explain`, never authority: no build reads it, and
//! module reuse is decided by the record store alone. It is rewritten only by a
//! successful build, so after a failed one it still describes the last success.
use fln_hash::domain::{Domain, DomainHasher};

/// Beside the outputs, under the package's build directory.
pub(crate) const FILE: &str = "fln-build.snapshot";
const SCHEMA: &str = "fln.lake-build-snapshot/1";
/// More than a build may hold (256 modules, 4,096 imports, Init's 601 external modules).
const MAX_LINES: usize = 1 << 20;

/// The digest a snapshot names file contents by.
pub(crate) fn digest(bytes: &[u8]) -> String {
    let mut hasher = DomainHasher::new(Domain::ArtifactClosureComponent);
    hasher.update(b"fln.lake-file/1\0");
    hasher.update(bytes);
    hasher.finalize().to_hex()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ModuleRow {
    pub(crate) name: String,
    /// Relative to the package root.
    pub(crate) source: String,
    pub(crate) source_digest: String,
    /// In header order, the implicit `Init` included.
    pub(crate) imports: Vec<String>,
    /// Relative to the package root.
    pub(crate) artifact: String,
    pub(crate) artifact_digest: String,
    pub(crate) key: Option<String>,
    pub(crate) decision: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExternalRow {
    pub(crate) name: String,
    pub(crate) digest: String,
    pub(crate) imports: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Snapshot {
    pub(crate) posture: String,
    pub(crate) records: String,
    /// The targets the build was asked for, as `+Module:olean`.
    pub(crate) targets: Vec<String>,
    pub(crate) modules: Vec<ModuleRow>,
    pub(crate) externals: Vec<ExternalRow>,
}

fn escape(field: &str) -> String {
    let mut out = String::with_capacity(field.len());
    for c in field.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '\t' => out.push_str("\\t"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            c => out.push(c),
        }
    }
    out
}

fn unescape(field: &str) -> Result<String, String> {
    let mut out = String::with_capacity(field.len());
    let mut chars = field.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        out.push(match chars.next() {
            Some('\\') => '\\',
            Some('t') => '\t',
            Some('n') => '\n',
            Some('r') => '\r',
            _ => return Err("bad escape".to_owned()),
        });
    }
    Ok(out)
}

fn line(fields: &[&str]) -> String {
    let mut text = fields
        .iter()
        .map(|field| escape(field))
        .collect::<Vec<_>>()
        .join("\t");
    text.push('\n');
    text
}

impl Snapshot {
    pub(crate) fn to_text(&self) -> String {
        let mut text = format!("{SCHEMA}\n");
        text.push_str(&line(&["posture", &self.posture]));
        text.push_str(&line(&["records", &self.records]));
        for target in &self.targets {
            text.push_str(&line(&["target", target]));
        }
        for module in &self.modules {
            text.push_str(&line(&[
                "module",
                &module.name,
                &module.source,
                &module.source_digest,
                &module.artifact,
                &module.artifact_digest,
                module.key.as_deref().unwrap_or("-"),
                &module.decision,
            ]));
            for import in &module.imports {
                text.push_str(&line(&["import", import]));
            }
        }
        for external in &self.externals {
            text.push_str(&line(&["external", &external.name, &external.digest]));
            for import in &external.imports {
                text.push_str(&line(&["import", import]));
            }
        }
        text.push_str("end\n");
        text
    }

    /// Strict: the schema line, `posture` and `records` once each, then targets,
    /// modules and externals in that order, each `import` row belonging to the row
    /// before it, and `end` as the last line.
    pub(crate) fn parse(text: &str) -> Result<Self, String> {
        let mut lines = text.split('\n');
        if lines.next() != Some(SCHEMA) {
            return Err(format!("not a {SCHEMA} snapshot"));
        }
        let mut snapshot = Snapshot {
            posture: String::new(),
            records: String::new(),
            targets: Vec::new(),
            modules: Vec::new(),
            externals: Vec::new(),
        };
        // 0 header, 1 targets, 2 modules, 3 externals: rows never move backwards.
        let mut stage = 0;
        let mut owner: Option<bool> = None;
        let mut ended = false;
        for (index, raw) in lines.enumerate() {
            if index > MAX_LINES {
                return Err("snapshot is too long".to_owned());
            }
            if ended {
                if raw.is_empty() && index > 0 {
                    continue;
                }
                return Err(format!("line {} follows `end`", index + 2));
            }
            if raw == "end" {
                ended = true;
                continue;
            }
            let fields = raw
                .split('\t')
                .map(unescape)
                .collect::<Result<Vec<_>, _>>()
                .map_err(|error| format!("line {}: {error}", index + 2))?;
            let bad = || format!("line {}: malformed `{}` row", index + 2, fields[0]);
            match (fields[0].as_str(), fields.len()) {
                ("posture", 2) if index == 0 => snapshot.posture = fields[1].clone(),
                ("records", 2) if index == 1 => snapshot.records = fields[1].clone(),
                ("target", 2) if stage <= 1 && index >= 2 => {
                    stage = 1;
                    snapshot.targets.push(fields[1].clone());
                }
                ("module", 8) if stage <= 2 && index >= 2 => {
                    stage = 2;
                    owner = Some(true);
                    snapshot.modules.push(ModuleRow {
                        name: fields[1].clone(),
                        source: fields[2].clone(),
                        source_digest: fields[3].clone(),
                        artifact: fields[4].clone(),
                        artifact_digest: fields[5].clone(),
                        key: (fields[6] != "-").then(|| fields[6].clone()),
                        decision: fields[7].clone(),
                        imports: Vec::new(),
                    });
                }
                ("external", 3) if index >= 2 => {
                    stage = 3;
                    owner = Some(false);
                    snapshot.externals.push(ExternalRow {
                        name: fields[1].clone(),
                        digest: fields[2].clone(),
                        imports: Vec::new(),
                    });
                }
                ("import", 2) => match owner {
                    Some(true) => snapshot
                        .modules
                        .last_mut()
                        .ok_or_else(bad)?
                        .imports
                        .push(fields[1].clone()),
                    Some(false) => snapshot
                        .externals
                        .last_mut()
                        .ok_or_else(bad)?
                        .imports
                        .push(fields[1].clone()),
                    None => return Err(bad()),
                },
                _ => return Err(bad()),
            }
        }
        if !ended {
            return Err("snapshot has no `end` line".to_owned());
        }
        if snapshot.posture.is_empty() || snapshot.records.is_empty() || snapshot.targets.is_empty()
        {
            return Err("snapshot lacks its posture, records or targets".to_owned());
        }
        Ok(snapshot)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> Snapshot {
        Snapshot {
            posture: "reuse-verified".to_owned(),
            records: "on".to_owned(),
            targets: vec!["+Lib.Top:olean".to_owned()],
            modules: vec![ModuleRow {
                name: "Lib.Top".to_owned(),
                source: "Lib/Top.lean".to_owned(),
                source_digest: digest(b"source"),
                imports: vec!["Init".to_owned(), "Lib.Base".to_owned()],
                artifact: ".lake/build/lib/lean/Lib/Top.olean".to_owned(),
                artifact_digest: digest(b"artifact"),
                key: None,
                decision: "elaborated".to_owned(),
            }],
            externals: vec![ExternalRow {
                name: "Init\twith\\odd\nname".to_owned(),
                digest: digest(b"init"),
                imports: vec![],
            }],
        }
    }

    #[test]
    fn snapshots_round_trip_and_malformed_ones_are_refused() {
        let snapshot = sample();
        let text = snapshot.to_text();
        assert_eq!(Snapshot::parse(&text).unwrap(), snapshot);
        for broken in [
            String::new(),
            text.replace("end\n", ""),
            text.replace("fln.lake-build-snapshot/1", "fln.lake-build-snapshot/0"),
            text.replace("posture\t", "posture\tx\t"),
            format!("{text}module\tlate\n"),
            text.replace("import\tInit\n", "import\tInit\textra\n"),
            text.replace("\\t", "\\q"),
        ] {
            assert!(Snapshot::parse(&broken).is_err(), "{broken}");
        }
    }
}
