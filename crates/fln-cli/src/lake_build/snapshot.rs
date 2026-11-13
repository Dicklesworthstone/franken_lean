//! The content-bound record of the last successful `lake build` (bead
//! `franken_lean-z8j.1.2`): what each module was built from and what it produced.
//!
//! It is provenance for `fln build explain`, never authority: no build reads it, and
//! module reuse is decided by the record store alone. It is rewritten only by a
//! successful build, so after a failed one it still describes the last success.
use fln_hash::domain::{Domain, DomainHasher};
use std::path::Path;

/// Beside the outputs, under the package's build directory.
pub(crate) const FILE: &str = "fln-build.snapshot";
const SCHEMA: &str = "fln.lake-build-snapshot/4";
const IR_SCHEMA: &str = "fln.lake-build-snapshot/3";
const COMPANION_SCHEMA: &str = "fln.lake-build-snapshot/2";
const LEGACY_SCHEMA: &str = "fln.lake-build-snapshot/1";
/// More than a build may hold (256 modules, 4,096 imports, Init's 601 external modules).
const MAX_LINES: usize = 1 << 20;
/// Local dependency discovery admits at most 64 selected packages.
const MAX_CONFIGURATIONS: usize = 64;

/// The digest a snapshot names file contents by.
pub(crate) fn digest(bytes: &[u8]) -> String {
    let mut hasher = DomainHasher::new(Domain::ArtifactClosureComponent);
    hasher.update(b"fln.lake-file/1\0");
    hasher.update(bytes);
    hasher.finalize().to_hex()
}

/// Exact configuration contents selected by the current package resolver.
/// Paths are provenance only; callers must rediscover and validate their inputs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConfigRow {
    pub(crate) path: String,
    pub(crate) digest: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CompanionDigests {
    pub(crate) server: String,
    pub(crate) private: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ModuleRow {
    pub(crate) name: String,
    /// Source identity recorded by the build; never file-reading authority.
    pub(crate) source: String,
    pub(crate) source_digest: String,
    /// In header order, the implicit `Init` included.
    pub(crate) imports: Vec<String>,
    /// Output identity recorded by the build; never file-reading authority.
    pub(crate) artifact: String,
    pub(crate) artifact_digest: String,
    pub(crate) ir_digest: Option<String>,
    pub(crate) companions: Option<CompanionDigests>,
    pub(crate) key: Option<String>,
    pub(crate) decision: String,
}

impl ModuleRow {
    /// Derive all companion paths from the currently validated output location.
    /// The recorded artifact string is only compared as provenance by callers.
    pub(crate) fn output_files(&self, artifact: &Path) -> Vec<(String, &str)> {
        let mut files = vec![(
            artifact.display().to_string(),
            self.artifact_digest.as_str(),
        )];
        if let Some(parts) = &self.companions {
            files.extend([
                (
                    artifact
                        .with_extension("olean.server")
                        .display()
                        .to_string(),
                    parts.server.as_str(),
                ),
                (
                    artifact
                        .with_extension("olean.private")
                        .display()
                        .to_string(),
                    parts.private.as_str(),
                ),
            ]);
        }
        if let Some(digest) = &self.ir_digest {
            files.push((artifact.with_extension("ir").display().to_string(), digest));
        }
        files
    }
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
    /// The exact module/facet targets requested by the build.
    pub(crate) targets: Vec<String>,
    pub(crate) configurations: Vec<ConfigRow>,
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
        for configuration in &self.configurations {
            text.push_str(&line(&[
                "configuration",
                &configuration.path,
                &configuration.digest,
            ]));
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
            if let Some(parts) = &module.companions {
                text.push_str(&line(&["companions", &parts.server, &parts.private]));
            }
            if let Some(digest) = &module.ir_digest {
                text.push_str(&line(&["ir", digest]));
            }
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
    /// configurations, modules and externals in that order, each `import` row
    /// belonging to the row before it, and `end` as the last line.
    pub(crate) fn parse(text: &str) -> Result<Self, String> {
        let mut lines = text.split('\n');
        let schema = lines.next();
        if !matches!(
            schema,
            Some(SCHEMA | IR_SCHEMA | COMPANION_SCHEMA | LEGACY_SCHEMA)
        ) {
            return Err(format!("not a {SCHEMA} snapshot"));
        }
        let mut snapshot = Snapshot {
            posture: String::new(),
            records: String::new(),
            targets: Vec::new(),
            configurations: Vec::new(),
            modules: Vec::new(),
            externals: Vec::new(),
        };
        // 0 header, 1 targets, 2 configurations, 3 modules, 4 externals.
        // Rows never move backwards.
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
                ("configuration", 3) if schema == Some(SCHEMA) && stage <= 2 && index >= 2 => {
                    if fields[1].is_empty()
                        || fields[2].is_empty()
                        || snapshot.configurations.len() >= MAX_CONFIGURATIONS
                        || snapshot
                            .configurations
                            .iter()
                            .any(|row| row.path == fields[1])
                    {
                        return Err(bad());
                    }
                    stage = 2;
                    snapshot.configurations.push(ConfigRow {
                        path: fields[1].clone(),
                        digest: fields[2].clone(),
                    });
                }
                ("module", 8) if stage <= 3 && index >= 2 => {
                    stage = 3;
                    owner = Some(true);
                    snapshot.modules.push(ModuleRow {
                        name: fields[1].clone(),
                        source: fields[2].clone(),
                        source_digest: fields[3].clone(),
                        artifact: fields[4].clone(),
                        artifact_digest: fields[5].clone(),
                        ir_digest: None,
                        companions: None,
                        key: (fields[6] != "-").then(|| fields[6].clone()),
                        decision: fields[7].clone(),
                        imports: Vec::new(),
                    });
                }
                ("companions", 3)
                    if matches!(schema, Some(SCHEMA | IR_SCHEMA | COMPANION_SCHEMA))
                        && stage == 3
                        && owner == Some(true) =>
                {
                    let module = snapshot.modules.last_mut().ok_or_else(bad)?;
                    if module.companions.is_some()
                        || !module.imports.is_empty()
                        || fields[1].is_empty()
                        || fields[2].is_empty()
                    {
                        return Err(bad());
                    }
                    module.companions = Some(CompanionDigests {
                        server: fields[1].clone(),
                        private: fields[2].clone(),
                    });
                }
                ("external", 3) if index >= 2 => {
                    stage = 4;
                    owner = Some(false);
                    snapshot.externals.push(ExternalRow {
                        name: fields[1].clone(),
                        digest: fields[2].clone(),
                        imports: Vec::new(),
                    });
                }
                ("ir", 2)
                    if matches!(schema, Some(SCHEMA | IR_SCHEMA))
                        && stage == 3
                        && owner == Some(true) =>
                {
                    let module = snapshot.modules.last_mut().ok_or_else(bad)?;
                    if module.ir_digest.is_some()
                        || !module.imports.is_empty()
                        || fields[1].is_empty()
                    {
                        return Err(bad());
                    }
                    module.ir_digest = Some(fields[1].clone());
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
            configurations: vec![ConfigRow {
                path: "lakefile.toml".to_owned(),
                digest: digest(b"name = 'package'"),
            }],
            modules: vec![ModuleRow {
                name: "Lib.Top".to_owned(),
                source: "Lib/Top.lean".to_owned(),
                source_digest: digest(b"source"),
                imports: vec!["Init".to_owned(), "Lib.Base".to_owned()],
                artifact: ".lake/build/lib/lean/Lib/Top.olean".to_owned(),
                artifact_digest: digest(b"artifact"),
                ir_digest: None,
                companions: None,
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
            text.replace(SCHEMA, "fln.lake-build-snapshot/0"),
            text.replace("posture\t", "posture\tx\t"),
            format!("{text}module\tlate\n"),
            text.replace("import\tInit\n", "import\tInit\textra\n"),
            text.replace("\\t", "\\q"),
        ] {
            assert!(Snapshot::parse(&broken).is_err(), "{broken}");
        }
    }

    #[test]
    fn configurations_are_unique_and_precede_module_provenance() {
        let mut snapshot = sample();
        snapshot.configurations.push(ConfigRow {
            path: "../dependency/lakefile.toml".to_owned(),
            digest: digest(b"name = 'dependency'"),
        });
        let text = snapshot.to_text();
        assert_eq!(Snapshot::parse(&text).unwrap(), snapshot);
        let row = text
            .lines()
            .find(|line| line.starts_with("configuration\t"))
            .unwrap();
        let without = text.replace(&format!("{row}\n"), "");
        for broken in [
            text.replace(SCHEMA, IR_SCHEMA),
            text.replace(SCHEMA, COMPANION_SCHEMA),
            text.replace(SCHEMA, LEGACY_SCHEMA),
            text.replace(row, "configuration\t\tcontent"),
            text.replace(row, "configuration\tlakefile.toml\t"),
            text.replace(row, "configuration\tlakefile.toml"),
            text.replace(row, &format!("{row}\n{row}")),
            without.replace("end\n", &format!("{row}\nend\n")),
            text.replace(row, &format!("{row}\ntarget\t+Late:olean")),
        ] {
            assert!(Snapshot::parse(&broken).is_err(), "{broken}");
        }
        let mut too_many = sample();
        too_many.configurations = (0..=MAX_CONFIGURATIONS)
            .map(|index| ConfigRow {
                path: format!("package-{index}/lakefile.toml"),
                digest: digest(b"config"),
            })
            .collect();
        assert!(Snapshot::parse(&too_many.to_text()).is_err());
    }

    #[test]
    fn whole_families_round_trip_and_legacy_snapshots_remain_readable() {
        let mut snapshot = sample();
        snapshot.configurations.clear();
        for schema in [LEGACY_SCHEMA, COMPANION_SCHEMA, IR_SCHEMA] {
            assert_eq!(
                Snapshot::parse(&snapshot.to_text().replace(SCHEMA, schema)).unwrap(),
                snapshot
            );
        }
        snapshot.modules[0].companions = Some(CompanionDigests {
            server: digest(b"server"),
            private: digest(b"private"),
        });
        let text = snapshot.to_text();
        assert_eq!(Snapshot::parse(&text).unwrap(), snapshot);
        let artifact = Path::new(&snapshot.modules[0].artifact);
        assert_eq!(snapshot.modules[0].output_files(artifact).len(), 3);
        for schema in [COMPANION_SCHEMA, IR_SCHEMA] {
            assert_eq!(
                Snapshot::parse(&text.replace(SCHEMA, schema)).unwrap(),
                snapshot
            );
        }
        let row = text
            .lines()
            .find(|line| line.starts_with("companions\t"))
            .unwrap();
        for broken in [
            text.replace(SCHEMA, LEGACY_SCHEMA),
            text.replace(row, "companions\tone"),
            text.replace(row, "companions\t\tprivate"),
            text.replace(row, &format!("{row}\n{row}")),
            text.replace(row, &format!("import\tLate\n{row}")),
            text.replace("end\n", &format!("{row}\nend\n")),
        ] {
            assert!(Snapshot::parse(&broken).is_err(), "{broken}");
        }
    }

    #[test]
    fn executable_companions_participate_in_output_change_detection() {
        let mut snapshot = sample();
        snapshot.configurations.clear();
        snapshot.targets = vec!["+Lib.Top:ir".to_owned()];
        let ir_digest = digest(b"native executable IR");
        snapshot.modules[0].ir_digest = Some(ir_digest.clone());
        let text = snapshot.to_text();
        assert_eq!(Snapshot::parse(&text).unwrap(), snapshot);
        assert_eq!(
            Snapshot::parse(&text.replace(SCHEMA, IR_SCHEMA)).unwrap(),
            snapshot
        );
        let artifact = Path::new(&snapshot.modules[0].artifact);
        assert!(snapshot.modules[0].output_files(artifact).contains(&(
            ".lake/build/lib/lean/Lib/Top.ir".to_owned(),
            ir_digest.as_str(),
        )));
        let row = format!("ir\t{ir_digest}");
        for broken in [
            text.replace(SCHEMA, COMPANION_SCHEMA),
            text.replace(&row, "ir\t"),
            text.replace(&row, &format!("{row}\n{row}")),
            text.replace(&row, &format!("import\tLate\n{row}")),
        ] {
            assert!(Snapshot::parse(&broken).is_err(), "{broken}");
        }
    }

    #[test]
    fn output_paths_come_only_from_the_current_validated_destination() {
        let mut module = sample().modules.remove(0);
        module.artifact = "../../untrusted/Elsewhere.olean".to_owned();
        module.companions = Some(CompanionDigests {
            server: digest(b"server"),
            private: digest(b"private"),
        });
        module.ir_digest = Some(digest(b"ir"));
        let artifact = Path::new("dependency/build/lib/lean/Lib/Top.olean");
        let paths = module
            .output_files(artifact)
            .into_iter()
            .map(|(path, _)| path)
            .collect::<Vec<_>>();
        assert_eq!(
            paths,
            [
                artifact.display().to_string(),
                artifact
                    .with_extension("olean.server")
                    .display()
                    .to_string(),
                artifact
                    .with_extension("olean.private")
                    .display()
                    .to_string(),
                artifact.with_extension("ir").display().to_string(),
            ],
        );
        assert!(paths.iter().all(|path| !path.contains("untrusted")));
    }
}
