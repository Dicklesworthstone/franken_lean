//! Explicit imported-macro checking over the same captured artifact closure.
//! The census remains pinned, every registration must prepare, and no ambient
//! search root can supply code for an artifact selected from another root.
use super::*;
use fln::imported_ir::VerifiedPartition;
use fln::imported_macros::registrations::{MacroRegistryLimits, MacroTreeLimits};
use fln::imported_macros::{MacroContext, MacroState};
use fln::source_check::modules::SourceModuleMacroInputs;
use std::collections::BTreeSet;

const DEFAULT_IR_BYTES: usize = 64 * 1024 * 1024;
const MAX_PARTITION_BYTES: usize = 64 * 1024 * 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Config {
    partition: PathBuf,
    max_bytes: usize,
}

impl Config {
    pub(in crate::source_check) fn take(
        arguments: Vec<OsString>,
    ) -> Result<(Vec<OsString>, Option<Self>), UsageError> {
        let mut partition = None;
        let mut max_bytes = None;
        let mut kept = Vec::with_capacity(arguments.len());
        let mut options = true;
        let mut arguments = arguments.into_iter();
        while let Some(argument) = arguments.next() {
            if options && argument == "--" {
                options = false;
                kept.push(argument);
                continue;
            }
            let option = if options && argument == "--imported-macros" {
                Some(("--imported-macros", None))
            } else if options && argument == "--macro-max-bytes" {
                Some(("--macro-max-bytes", None))
            } else if options {
                argument.to_str().and_then(|text| {
                    text.strip_prefix("--imported-macros=")
                        .map(|value| ("--imported-macros", Some(OsString::from(value))))
                        .or_else(|| {
                            text.strip_prefix("--macro-max-bytes=")
                                .map(|value| ("--macro-max-bytes", Some(OsString::from(value))))
                        })
                })
            } else {
                None
            };
            let Some((option, inline)) = option else {
                kept.push(argument);
                continue;
            };
            let value = inline
                .or_else(|| arguments.next())
                .ok_or_else(|| UsageError(format!("{option} requires a following value")))?;
            if option == "--imported-macros" {
                if partition.is_some() {
                    return Err(UsageError(
                        "--imported-macros may be supplied at most once".to_owned(),
                    ));
                }
                if value.is_empty() {
                    return Err(UsageError(
                        "--imported-macros requires a census path".to_owned(),
                    ));
                }
                partition = Some(PathBuf::from(value));
            } else {
                if max_bytes.is_some() {
                    return Err(UsageError(
                        "--macro-max-bytes may be supplied at most once".to_owned(),
                    ));
                }
                max_bytes = Some(
                    value
                        .to_str()
                        .and_then(|value| value.parse::<u64>().ok())
                        .and_then(|value| usize::try_from(value).ok())
                        .ok_or_else(|| {
                            UsageError(
                                "--macro-max-bytes requires a non-negative byte count".to_owned(),
                            )
                        })?,
                );
            }
        }
        if max_bytes.is_some() && partition.is_none() {
            return Err(UsageError(
                "--macro-max-bytes requires --imported-macros".to_owned(),
            ));
        }
        Ok((
            kept,
            partition.map(|partition| Self {
                partition,
                max_bytes: max_bytes.unwrap_or(DEFAULT_IR_BYTES),
            }),
        ))
    }
}

/// Code and policy captured before admission; the receipt later supplies the
/// authoritative module owners and complete macro registration journals.
pub(in crate::source_check) struct Prepared {
    partition: VerifiedPartition,
    modules: Vec<fln::IrModule>,
    names: Vec<Name>,
    bytes: usize,
}

pub(in crate::source_check) struct Report {
    pub(in crate::source_check) attempts: usize,
    pub(in crate::source_check) vm_steps: u64,
    pub(in crate::source_check) syntax_visits: u64,
    ir_bytes: usize,
}

impl Report {
    pub(in crate::source_check) fn json(&self) -> String {
        format!(
            ",\"importedMacros\":{{\"producer\":\"reference\",\"attempts\":{},\"vmSteps\":{},\"syntaxVisits\":{},\"irBytes\":{}}}",
            self.attempts, self.vm_steps, self.syntax_visits, self.ir_bytes
        )
    }
}

fn read_failure(error: BoundedReadFailure) -> Failure {
    Failure {
        class: error.class(),
        detail: error.to_string(),
        authority: false,
        exit: error.exit_code(),
    }
}

fn policy_failure(detail: impl Into<String>) -> Failure {
    Failure {
        class: "policy-refusal",
        detail: detail.into(),
        authority: false,
        exit: 1,
    }
}

fn census_ancestor(partition: &VerifiedPartition, name: &Name) -> bool {
    let mut current = name.clone();
    loop {
        if partition.classify(&current).is_some() {
            return true;
        }
        let parent = current.parent();
        if parent == current {
            return false;
        }
        current = parent;
    }
}

fn owned_ancestor(owners: &BTreeSet<&Name>, name: &Name) -> bool {
    let mut current = name.clone();
    loop {
        if owners.contains(&current) {
            return true;
        }
        let parent = current.parent();
        if parent == current {
            return false;
        }
        current = parent;
    }
}

impl Loaded {
    pub(in crate::source_check) fn prepare_macros(
        &self,
        config: &Config,
    ) -> Result<Prepared, Failure> {
        if !matches!(&self.inputs, Inputs::Modules { .. }) || self.oleans.is_empty() {
            return Err(Failure::input(
                "--imported-macros requires one source entry with an external .olean import",
            ));
        }
        let bytes = read_bounded(
            &config.partition,
            MAX_PARTITION_BYTES,
            "pinned imported-macro census",
        )
        .map_err(read_failure)?;
        let text = std::str::from_utf8(&bytes)
            .map_err(|error| policy_failure(format!("imported-macro census: {error}")))?;
        let partition = VerifiedPartition::from_pinned_tsv(text)
            .map_err(|error| policy_failure(error.to_string()))?;
        let mut modules = Vec::new();
        let mut names = Vec::new();
        let mut total = 0usize;
        for artifact in &self.oleans {
            let path = artifact.artifact_path.with_extension("ir");
            let metadata = match std::fs::symlink_metadata(&path) {
                Ok(metadata) => metadata,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
                Err(error) => return Err(Failure::io(&path, error)),
            };
            if !metadata.is_file() {
                return Err(Failure::input(format!(
                    "{} is not a regular imported-macro IR file",
                    path.display()
                )));
            }
            let remaining = config.max_bytes.saturating_sub(total);
            let bytes =
                read_bounded(&path, remaining, "imported-macro IR").map_err(read_failure)?;
            total += bytes.len();
            let module = fln::decode_ir_artifact(&bytes, remaining).map_err(|error| Failure {
                class: if error.is_resource() {
                    "resource"
                } else {
                    "codec"
                },
                detail: format!("{}: {error}", path.display()),
                authority: false,
                exit: if error.is_resource() { 3 } else { 1 },
            })?;
            modules.push(module);
            names.push(artifact.name.clone());
        }
        Ok(Prepared {
            partition,
            modules,
            names,
            bytes: total,
        })
    }
}

impl Prepared {
    pub(in crate::source_check) fn check(
        &self,
        loaded: &Loaded,
        base: Option<&OleanBase>,
        limits: fln::SourceCheckLimits,
    ) -> Result<Outcome<(SourceFileCheck, Report)>, Failure> {
        let Inputs::Modules { names, sources } = &loaded.inputs else {
            return Err(Failure::input(
                "imported macros require a named source module",
            ));
        };
        let base = base.ok_or_else(|| {
            Failure::input("imported macros require an admitted artifact receipt")
        })?;
        let mut users = BTreeSet::new();
        for (name, code) in self.names.iter().zip(&self.modules) {
            let checked = base
                .receipt
                .checked
                .modules
                .iter()
                .find(|checked| &checked.name == name)
                .ok_or_else(|| {
                    Failure::input(format!(
                        "imported-macro IR has no checked owner module {}",
                        name.to_display_string()
                    ))
                })?;
            let owners = checked
                .decoded
                .constants
                .iter()
                .map(fln::ConstantInfo::name)
                .collect::<BTreeSet<_>>();
            for declaration in &code.decls {
                if let fln::IrDecl::Function { name, .. } = declaration
                    && !census_ancestor(&self.partition, name)
                    && owned_ancestor(&owners, name)
                {
                    // An actual admitted owner (or its compiler-generated
                    // descendant) grants user classification, never a module's
                    // spelling. The compiler still rejects native-row overrides.
                    users.insert(name.clone());
                }
            }
        }
        let inputs = names
            .iter()
            .zip(sources)
            .map(|(name, source)| SourceModuleInput { name, source })
            .collect::<Vec<_>>();
        let result = base.receipt.check_source_modules_with_imported_macros(
            &inputs,
            &names[0],
            &fln::KVMap::new(),
            SourceModuleCheckLimits::new(limits),
            SourceModuleMacroInputs {
                code: &self.modules,
                partition: &self.partition,
                user_declarations: &users,
                registry_limits: MacroRegistryLimits::default(),
                context: MacroContext {
                    quotation_context: names[0].clone(),
                    current_macro_scope: 0,
                    current_recursion_depth: 0,
                    max_recursion_depth: 1000,
                },
                state: MacroState::default(),
                limits: MacroTreeLimits::default(),
            },
            None,
        );
        let report = Report {
            attempts: result.attempts.len(),
            vm_steps: result.completed_vm_usage.steps,
            syntax_visits: result.tree_usage.visits,
            ir_bytes: self.bytes,
        };
        match result.outcome {
            Outcome::Complete(Ok(result)) => Ok(Outcome::Complete((result.checked, report))),
            Outcome::Complete(Err(error)) => {
                let (class, authority, exit) = error.disposition();
                Err(Failure {
                    class,
                    authority,
                    exit,
                    detail: error.to_string(),
                })
            }
            Outcome::Inconclusive(reason) => Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => Ok(Outcome::InternalFault(fault)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn user_helpers_need_structural_ownership_in_the_selected_module() {
        let owner = Name::from_components(["User", "macro"]);
        let other = Name::from_components(["Other", "macro"]);
        let owners = BTreeSet::from([&owner]);
        assert!(owned_ancestor(&owners, &owner));
        assert!(owned_ancestor(
            &owners,
            &Name::from_components(["User", "macro", "_lambda_1"])
        ));
        assert!(!owned_ancestor(&owners, &other));
        assert!(!owned_ancestor(
            &owners,
            &Name::from_components(["User", "macroSuffix"])
        ));
        assert!(!owned_ancestor(
            &owners,
            &Name::from_components(["User.macro", "_lambda_1"])
        ));
    }
}
