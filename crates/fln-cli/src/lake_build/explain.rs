//! `fln build explain`: why a module would rebuild, from the last successful build's
//! snapshot and the current tree (bead `franken_lean-z8j.1.2`). Nothing is elaborated
//! or admitted. The answer rests on file contents only, never on timestamps, output
//! presence alone, or what a source file says in its comments.
//!
//! The Reference decision is Lake's file-cone model. A module rebuilds when its source
//! bytes, its ordered imports or any external `.olean` in its import cone changed
//! since the recorded build, or when a local import rebuilds. A missing output
//! rebuilds that module alone. The native decision needs Ledger demand records,
//! which do not exist, so it is reported as unavailable rather than guessed.
use super::snapshot::{self, Snapshot};
use super::*;

const MAX_SNAPSHOT_BYTES: usize = 64 * 1024 * 1024;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Decision {
    UpToDate,
    Rebuild,
    /// An input could not be read, so no decision is claimed.
    Unknown,
}

impl Decision {
    fn as_str(self) -> &'static str {
        match self {
            Decision::UpToDate => "up-to-date",
            Decision::Rebuild => "rebuild",
            Decision::Unknown => "unknown",
        }
    }
}

/// One input whose content differs from the recorded build's. `None` is absent.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Changed {
    module: String,
    kind: &'static str,
    subject: String,
    old: Option<String>,
    new: Option<String>,
}

struct Explained {
    name: String,
    decision: Decision,
    /// Whether dependents rebuild because of it: a missing output does not change
    /// what importers are checked against.
    propagates: bool,
    reasons: Vec<String>,
}

/// A module as the tree holds it now.
struct Current {
    source: String,
    digest: std::result::Result<String, String>,
    /// `None` when the header cannot be read.
    imports: Option<Vec<Name>>,
}

enum Refusal {
    /// No snapshot exists: exit 5, the multiplexer's missing-capability code.
    Unavailable(String),
    Failure(Failure),
}
impl From<Failure> for Refusal {
    fn from(failure: Failure) -> Self {
        Refusal::Failure(failure)
    }
}

struct Report {
    package: String,
    snapshot: String,
    posture: String,
    records: String,
    target: Option<String>,
    decision: Decision,
    decision_reasons: Vec<String>,
    changed: Vec<Changed>,
    outputs: Vec<Changed>,
    modules: Vec<Explained>,
}

/// `Lib.Top`, `+Lib.Top:olean`, or the source path `Lib/Top.lean`.
fn target_name(text: &str) -> std::result::Result<Name, Failure> {
    if let Some(path) = text.strip_suffix(".lean") {
        return name(&path.trim_start_matches("./").replace(['/', '\\'], "."));
    }
    let bare = text.strip_prefix('+').unwrap_or(text);
    let bare = bare.strip_suffix(":olean").unwrap_or(bare);
    name(bare)
}

fn explain_report(directory: &Path, target: Option<&str>) -> std::result::Result<Report, Refusal> {
    let root = directory
        .canonicalize()
        .map_err(|error| Failure::io(directory, error))?;
    let config = config(&root)?;
    let path = root.join(&config.build_dir).join(snapshot::FILE);
    let relative = |path: &Path| {
        path.strip_prefix(&root)
            .unwrap_or(path)
            .display()
            .to_string()
    };
    match std::fs::symlink_metadata(&path) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            return Err(Refusal::Unavailable(format!(
                "build provenance is unavailable: no `lake build` snapshot at {}; cannot establish changed inputs, rebuild decisions or cache outcomes until `lake build +Module:olean` succeeds",
                relative(&path)
            )));
        }
        Err(error) => return Err(Failure::io(&path, error).into()),
        Ok(_) => {}
    }
    let text = read_bounded(&path, MAX_SNAPSHOT_BYTES, "build snapshot").map_err(Failure::from)?;
    let recorded = std::str::from_utf8(&text)
        .map_err(|_| "not UTF-8".to_owned())
        .and_then(Snapshot::parse)
        .map_err(|reason| {
            Failure::input(format!(
                "malformed build snapshot {}: {reason}",
                relative(&path)
            ))
        })?;
    let (libraries, recorded_entries) = plan(&root, &config, &recorded.targets)?;
    let entries = match target {
        Some(text) => {
            let module = target_name(text)?;
            let display = module.to_display_string();
            if !recorded.modules.iter().any(|row| row.name == display) {
                return Err(Failure::input(format!(
                    "module `{display}` is not part of the recorded build of {}",
                    recorded.targets.join(", ")
                ))
                .into());
            }
            vec![module]
        }
        None => recorded_entries,
    };

    // The current local import graph, from the entries, without elaborating.
    let mut current: BTreeMap<Name, Current> = BTreeMap::new();
    let mut external = BTreeSet::new();
    let mut pending: BTreeSet<Name> = entries.iter().cloned().collect();
    while let Some(module) = pending.pop_first() {
        if current.contains_key(&module) || external.contains(&module) {
            continue;
        }
        let Some(source) = source_path(&module, &libraries)? else {
            external.insert(module);
            continue;
        };
        if current.len() >= MAX_MODULES {
            return Err(Failure::new("resource", "source module count exceeds 256").into());
        }
        let bytes = read_bounded(&source, SOURCE_RUN_DEFAULT_MAX_BYTES, "Lake module source")
            .map_err(|error| error.to_string());
        let imports = bytes.as_ref().ok().and_then(|bytes| {
            parse_source_header(bytes).ok().map(|header| {
                let mut imports = header.imports;
                if !header.prelude && !imports.contains(&Name::from_components(["Init"])) {
                    imports.insert(0, Name::from_components(["Init"]));
                }
                imports
            })
        });
        for import in imports.iter().flatten() {
            pending.insert(import.clone());
        }
        current.insert(
            module,
            Current {
                source: relative(&source),
                digest: bytes.map(|bytes| snapshot::digest(&bytes)),
                imports,
            },
        );
    }
    let roots: Vec<Name> = external.iter().cloned().collect();
    let externals = if roots.is_empty() {
        Ok(BTreeMap::new())
    } else {
        source_check::external_inputs(&roots, &root).map(|inputs| {
            inputs
                .into_iter()
                .map(|input| (input.name, (input.digest.to_hex(), input.imports)))
                .collect::<BTreeMap<_, _>>()
        })
    };
    let recorded_externals: BTreeMap<&str, &str> = recorded
        .externals
        .iter()
        .map(|row| (row.name.as_str(), row.digest.as_str()))
        .collect();

    let mut decided: BTreeMap<Name, (Decision, bool)> = BTreeMap::new();
    let mut explained = Vec::new();
    let mut changed: Vec<Changed> = Vec::new();
    let mut outputs = Vec::new();
    // Postorder over the current graph; a module met again while open is a cycle.
    let mut open = BTreeSet::new();
    let mut stack: Vec<(Name, bool)> = entries.iter().rev().map(|n| (n.clone(), false)).collect();
    while let Some((module, expanded)) = stack.pop() {
        if decided.contains_key(&module) || !current.contains_key(&module) {
            continue;
        }
        let local_imports: Vec<Name> = current[&module]
            .imports
            .iter()
            .flatten()
            .filter(|import| current.contains_key(*import))
            .cloned()
            .collect();
        if !expanded {
            if !open.insert(module.clone()) {
                continue;
            }
            stack.push((module.clone(), true));
            for import in local_imports.iter().rev() {
                if open.contains(import) && !decided.contains_key(import) {
                    continue;
                }
                stack.push((import.clone(), false));
            }
            continue;
        }
        let now = &current[&module];
        let display = module.to_display_string();
        let row = recorded.modules.iter().find(|row| row.name == display);
        let mut rebuild = Vec::new();
        let mut unknown = Vec::new();
        let mut output_only = false;
        let mut note =
            |module: &str, kind, subject: String, old: Option<String>, new: Option<String>| {
                let entry = Changed {
                    module: module.to_owned(),
                    kind,
                    subject,
                    old,
                    new,
                };
                if !changed.contains(&entry) {
                    changed.push(entry);
                }
            };
        match (row, &now.digest) {
            (_, Err(reason)) => unknown.push(format!("source unreadable: {reason}")),
            (None, Ok(digest)) => {
                rebuild.push("not part of the recorded build".to_owned());
                note(
                    &display,
                    "source",
                    now.source.clone(),
                    None,
                    Some(digest.clone()),
                );
            }
            (Some(row), Ok(digest)) => {
                if &row.source_digest != digest || row.source != now.source {
                    rebuild.push("source changed".to_owned());
                    note(
                        &display,
                        "source",
                        now.source.clone(),
                        Some(row.source_digest.clone()),
                        Some(digest.clone()),
                    );
                }
            }
        }
        match (&now.imports, row) {
            (None, _) if now.digest.is_ok() => unknown.push("header unparseable".to_owned()),
            (Some(imports), Some(row)) => {
                let names: Vec<String> = imports.iter().map(Name::to_display_string).collect();
                if names != row.imports {
                    rebuild.push("imports changed".to_owned());
                    note(
                        &display,
                        "imports",
                        display.clone(),
                        Some(row.imports.join(" ")),
                        Some(names.join(" ")),
                    );
                }
            }
            _ => {}
        }
        // Every external module in this module's import cone, compared by content.
        let direct: Vec<Name> = now
            .imports
            .iter()
            .flatten()
            .filter(|import| external.contains(*import))
            .cloned()
            .collect();
        if !direct.is_empty() {
            match &externals {
                Err(reason) => unknown.push(format!("external imports unresolvable: {reason}")),
                Ok(externals) => {
                    let mut cone = BTreeSet::new();
                    let mut work = direct;
                    while let Some(name) = work.pop() {
                        if !cone.insert(name.clone()) {
                            continue;
                        }
                        if let Some((_, imports)) = externals.get(&name) {
                            work.extend(imports.iter().cloned());
                        }
                    }
                    for name in cone {
                        let display_name = name.to_display_string();
                        let now = externals.get(&name).map(|(digest, _)| digest.clone());
                        let then = recorded_externals
                            .get(display_name.as_str())
                            .map(|d| (*d).to_owned());
                        if now != then {
                            rebuild.push(format!("external import {display_name} changed"));
                            note(&display, "external", display_name, then, now);
                        }
                    }
                }
            }
        }
        for import in &local_imports {
            match decided.get(import) {
                Some((Decision::Rebuild, true)) => rebuild.push(format!(
                    "imports {}, which rebuilds",
                    import.to_display_string()
                )),
                Some((Decision::Unknown, _)) => unknown.push(format!(
                    "imports {}, whose decision is unknown",
                    import.to_display_string()
                )),
                None => unknown.push(format!(
                    "import cycle through {}",
                    import.to_display_string()
                )),
                _ => {}
            }
        }
        if let Some(row) = row {
            let artifact = root.join(&row.artifact);
            match std::fs::read(&artifact) {
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                    if rebuild.is_empty() {
                        output_only = true;
                    }
                    rebuild.push("output missing".to_owned());
                    outputs.push(Changed {
                        module: display.clone(),
                        kind: "output",
                        subject: row.artifact.clone(),
                        old: Some(row.artifact_digest.clone()),
                        new: None,
                    });
                }
                Err(error) => unknown.push(format!("output unreadable: {error}")),
                Ok(bytes) => {
                    let digest = snapshot::digest(&bytes);
                    if digest != row.artifact_digest {
                        outputs.push(Changed {
                            module: display.clone(),
                            kind: "output",
                            subject: row.artifact.clone(),
                            old: Some(row.artifact_digest.clone()),
                            new: Some(digest),
                        });
                    }
                }
            }
        }
        let decision = if !unknown.is_empty() {
            Decision::Unknown
        } else if !rebuild.is_empty() {
            Decision::Rebuild
        } else {
            Decision::UpToDate
        };
        decided.insert(
            module.clone(),
            (decision, decision == Decision::Rebuild && !output_only),
        );
        open.remove(&module);
        let mut reasons = unknown;
        reasons.extend(rebuild);
        explained.push(Explained {
            name: display,
            decision,
            propagates: decision == Decision::Rebuild && !output_only,
            reasons,
        });
    }
    let (decision, decision_reasons) = match target {
        Some(_) => {
            let module = explained.last().expect("the target is explained last");
            (module.decision, module.reasons.clone())
        }
        None => {
            let decisions: Vec<Decision> = explained.iter().map(|m| m.decision).collect();
            let decision = if decisions.contains(&Decision::Unknown) {
                Decision::Unknown
            } else if decisions.contains(&Decision::Rebuild) {
                Decision::Rebuild
            } else {
                Decision::UpToDate
            };
            let reasons = explained
                .iter()
                .filter(|m| m.decision != Decision::UpToDate)
                .map(|m| format!("{} {}", m.name, m.decision.as_str()))
                .collect();
            (decision, reasons)
        }
    };
    Ok(Report {
        package: config.name.clone(),
        snapshot: relative(&path),
        posture: recorded.posture,
        records: recorded.records,
        target: target.map(|_| entries[0].to_display_string()),
        decision,
        decision_reasons,
        changed,
        outputs,
        modules: explained,
    })
}

fn optional(value: &Option<String>) -> String {
    value.as_deref().map_or("null".to_owned(), json_string)
}

fn changed_json(rows: &[Changed]) -> String {
    rows.iter()
        .map(|row| {
            format!(
                "{{\"module\":{},\"kind\":{},\"subject\":{},\"old\":{},\"new\":{}}}",
                json_string(&row.module),
                json_string(row.kind),
                json_string(&row.subject),
                optional(&row.old),
                optional(&row.new)
            )
        })
        .collect::<Vec<_>>()
        .join(",")
}

fn changed_text(rows: &[Changed]) -> String {
    if rows.is_empty() {
        return "(none)\n".to_owned();
    }
    let show = |value: &Option<String>| value.clone().unwrap_or_else(|| "(absent)".to_owned());
    rows.iter()
        .enumerate()
        .map(|(index, row)| {
            format!(
                "{}{} {}: {} -> {}\n",
                if index == 0 {
                    ""
                } else {
                    "                      "
                },
                row.kind,
                row.subject,
                show(&row.old),
                show(&row.new)
            )
        })
        .collect()
}

fn render(report: &Report, json: bool) -> String {
    let reasons = |reasons: &[String]| {
        reasons
            .iter()
            .map(|reason| json_string(reason))
            .collect::<Vec<_>>()
            .join(",")
    };
    if json {
        let modules = report
            .modules
            .iter()
            .map(|module| {
                format!(
                    "{{\"name\":{},\"reference_decision\":{},\"propagates\":{},\"reasons\":[{}]}}",
                    json_string(&module.name),
                    json_string(module.decision.as_str()),
                    module.propagates,
                    reasons(&module.reasons)
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        format!(
            "{{\"schema\":\"fln.build-explain/2\",\"status\":{},\"package\":{},\"snapshot\":{},\"posture\":{},\"module_records\":{},\"target\":{},\"reference_model\":\"file-cone\",\"reference_decision\":{},\"reasons\":[{}],\"native_decision\":\"unavailable\",\"native_reason\":\"no Ledger records\",\"changed_inputs\":[{}],\"changed_outputs\":[{}],\"modules\":[{modules}]}}\n",
            json_string(if report.decision == Decision::Unknown {
                "incomplete"
            } else {
                "success"
            }),
            json_string(&report.package),
            json_string(&report.snapshot),
            json_string(&report.posture),
            json_string(&report.records),
            optional(&report.target),
            json_string(report.decision.as_str()),
            reasons(&report.decision_reasons),
            changed_json(&report.changed),
            changed_json(&report.outputs),
        )
    } else {
        let width = report
            .modules
            .iter()
            .map(|module| module.name.len())
            .max()
            .unwrap_or(0);
        let modules: String = report
            .modules
            .iter()
            .map(|module| {
                let reasons = if module.reasons.is_empty() {
                    String::new()
                } else {
                    format!(": {}", module.reasons.join("; "))
                };
                format!(
                    "    {:width$}  {}{reasons}\n",
                    module.name,
                    module.decision.as_str()
                )
            })
            .collect();
        let decision = if report.decision_reasons.is_empty() {
            report.decision.as_str().to_owned()
        } else {
            format!(
                "{} ({})",
                report.decision.as_str(),
                report.decision_reasons.join("; ")
            )
        };
        format!(
            "{} (package: {})\n  Snapshot:           {} (posture {}, module records {})\n  Reference decision: {decision}\n  Native decision:    unavailable (no Ledger records)\n  Changed inputs:     {}  Changed outputs:    {}  Modules:\n{modules}",
            match &report.target {
                Some(target) => format!("Target: {target}"),
                None => "Targets: the recorded build's".to_owned(),
            },
            report.package,
            report.snapshot,
            report.posture,
            report.records,
            changed_text(&report.changed),
            changed_text(&report.outputs),
        )
    }
}

/// `fln build explain [--dir D] [TARGET]`. Exit 0 with a decision; exit 5 when no
/// snapshot exists, or when the requested decision cannot be computed because an
/// input cannot be read (the report still says which); exit 1 on a refused input.
pub(crate) fn explain(
    directory: Option<&Path>,
    target: Option<&str>,
    json: bool,
) -> MultiplexerOutput {
    match explain_report(directory.unwrap_or(Path::new(".")), target) {
        Ok(report) => {
            let mut output = MultiplexerOutput::success(render(&report, json));
            if report.decision == Decision::Unknown {
                output.exit_code = 5;
            }
            output
        }
        Err(Refusal::Unavailable(detail)) => {
            let text = if json {
                format!(
                    "{{\"schema\":\"fln.build-explain/2\",\"status\":\"unsupported\",\"error\":{}}}\n",
                    json_string(&detail)
                )
            } else {
                format!("fln build explain: unsupported: {detail}\n")
            };
            MultiplexerOutput::failure(text, 5)
        }
        Err(Refusal::Failure(failure)) => {
            let text = if json {
                format!(
                    "{{\"schema\":\"fln.build-explain/2\",\"status\":\"error\",\"class\":{},\"error\":{}}}\n",
                    json_string(failure.class),
                    json_string(&failure.detail)
                )
            } else {
                format!("fln build explain: {}: {}\n", failure.class, failure.detail)
            };
            MultiplexerOutput::failure(text, 1)
        }
    }
}
