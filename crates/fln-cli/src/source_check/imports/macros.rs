//! Explicit imported-macro source commands over the same captured artifact closure.
//! The census remains pinned, every registration must validate, and no ambient
//! search root can supply code for an artifact selected from another root.
use super::*;
use fln::imported_ir::VerifiedPartition;
use fln::imported_macros::registrations::{
    MacroAttempt, MacroCompilationInputs, MacroRegistryLimits, MacroTreeLimits,
};
use fln::imported_macros::{MacroContext, MacroState};
use fln::source_check::modules::SourceModuleDeferredMacroInputs;
use std::collections::BTreeSet;

const DEFAULT_IR_BYTES: usize = 64 * 1024 * 1024;
const MAX_PARTITION_BYTES: usize = 64 * 1024 * 1024;
const MAX_REPORT_BYTES: usize = 16 * 1024 * 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Config {
    partition: PathBuf,
    max_bytes: usize,
    syntax_modules: Vec<Name>,
}

impl Config {
    /// Runtime personalities preserve their existing argument grammar. Their
    /// imported-macro mode is an explicit environment opt-in using the same
    /// verified policy and bounded companion loader as check-source.
    pub(in crate::source_check) fn from_environment() -> Result<Option<Self>, Failure> {
        Self::environment(
            std::env::var_os("FLN_MACRO_PARTITION"),
            std::env::var_os("FLN_SYNTAX_MODULES"),
        )
    }

    fn environment(
        partition: Option<OsString>,
        syntax: Option<OsString>,
    ) -> Result<Option<Self>, Failure> {
        let Some(partition) = partition else {
            if syntax.is_some() {
                return Err(Failure::input(
                    "FLN_SYNTAX_MODULES requires FLN_MACRO_PARTITION",
                ));
            }
            return Ok(None);
        };
        if partition.is_empty() {
            return Err(Failure::input("FLN_MACRO_PARTITION requires a census path"));
        }
        let syntax_modules = syntax
            .map(|syntax| {
                let syntax = syntax.to_str().ok_or_else(|| {
                    Failure::input("FLN_SYNTAX_MODULES requires UTF-8 module names")
                })?;
                syntax
                    .split(',')
                    .map(|name| {
                        syntax_module(std::ffi::OsStr::new(name.trim())).map_err(|detail| {
                            Failure::input(format!("FLN_SYNTAX_MODULES: {detail}"))
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .transpose()?
            .unwrap_or_default();
        Ok(Some(Self {
            partition: PathBuf::from(partition),
            max_bytes: DEFAULT_IR_BYTES,
            syntax_modules,
        }))
    }

    pub(in crate::source_check) fn take(
        arguments: Vec<OsString>,
    ) -> Result<(Vec<OsString>, Option<Self>), UsageError> {
        let mut partition = None;
        let mut max_bytes = None;
        let mut syntax_modules = Vec::new();
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
            } else if options && argument == "--imported-syntax" {
                Some(("--imported-syntax", None))
            } else if options {
                argument.to_str().and_then(|text| {
                    text.strip_prefix("--imported-macros=")
                        .map(|value| ("--imported-macros", Some(OsString::from(value))))
                        .or_else(|| {
                            text.strip_prefix("--macro-max-bytes=")
                                .map(|value| ("--macro-max-bytes", Some(OsString::from(value))))
                        })
                        .or_else(|| {
                            text.strip_prefix("--imported-syntax=")
                                .map(|value| ("--imported-syntax", Some(OsString::from(value))))
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
            } else if option == "--imported-syntax" {
                syntax_modules.push(
                    syntax_module(&value)
                        .map_err(|detail| UsageError(format!("--imported-syntax: {detail}")))?,
                );
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
        if !syntax_modules.is_empty() && partition.is_none() {
            return Err(UsageError(
                "--imported-syntax requires --imported-macros".to_owned(),
            ));
        }
        Ok((
            kept,
            partition.map(|partition| Self {
                partition,
                max_bytes: max_bytes.unwrap_or(DEFAULT_IR_BYTES),
                syntax_modules,
            }),
        ))
    }
}

fn syntax_module(value: &std::ffi::OsStr) -> Result<Name, &'static str> {
    let invalid = "expected one imported module name";
    let value = value.to_str().ok_or(invalid)?;
    if value.is_empty() || value.chars().any(char::is_control) {
        return Err(invalid);
    }
    // Reuse the import grammar so quoted and structural names match the names
    // in checked receipts. A selector cannot introduce another directive/body.
    let source = format!("prelude\nimport {value}\n");
    let mut header = parse_source_header(source.as_bytes()).map_err(|_| invalid)?;
    if header.imports.len() != 1 || header.body_start.0 != source.len() {
        return Err(invalid);
    }
    Ok(header.imports.remove(0))
}

/// Code and policy captured before admission; the receipt later supplies the
/// authoritative module owners and complete macro registration journals.
pub(in crate::source_check) struct Prepared {
    partition: VerifiedPartition,
    modules: Vec<fln::IrModule>,
    names: Vec<Name>,
    bytes: usize,
    syntax_modules: Vec<Name>,
}

/// Closure provenance for attempted macro dispatch, not a dynamic call trace.
pub(in crate::source_check) struct Report {
    pub(in crate::source_check) attempts: usize,
    pub(in crate::source_check) vm_steps: u64,
    pub(in crate::source_check) syntax_visits: u64,
    ir_bytes: usize,
    linked_json: String,
}

impl Report {
    pub(in crate::source_check) fn from_attempts(
        ir_bytes: usize,
        attempts: &[MacroAttempt],
        vm_steps: u64,
        syntax_visits: u64,
    ) -> Result<Self, Failure> {
        let mut reference = BTreeSet::new();
        let mut native = BTreeSet::new();
        for attempt in attempts {
            reference.extend(
                attempt
                    .reference_functions
                    .iter()
                    .map(|function| &function.name),
            );
            native.extend(attempt.native_functions.iter().map(String::as_str));
        }
        let mut linked_json = String::new();
        push_report(&mut linked_json, ",\"linkedReferenceFunctions\":[")?;
        for (index, name) in reference.into_iter().enumerate() {
            if index != 0 {
                push_report(&mut linked_json, ",")?;
            }
            push_report(
                &mut linked_json,
                &format!(
                    "{{\"name\":{},\"producer\":\"reference\"}}",
                    json_string(&name.to_display_string())
                ),
            )?;
        }
        push_report(&mut linked_json, "],\"linkedNativeFunctions\":[")?;
        for (index, name) in native.into_iter().enumerate() {
            if index != 0 {
                push_report(&mut linked_json, ",")?;
            }
            push_report(&mut linked_json, &json_string(name))?;
        }
        push_report(&mut linked_json, "]")?;
        Ok(Self {
            attempts: attempts.len(),
            vm_steps,
            syntax_visits,
            ir_bytes,
            linked_json,
        })
    }

    pub(in crate::source_check) fn json(&self) -> String {
        format!(
            ",\"importedMacros\":{{\"producer\":\"reference\",\"attempts\":{},\"vmSteps\":{},\"syntaxVisits\":{},\"irBytes\":{}{}}}",
            self.attempts, self.vm_steps, self.syntax_visits, self.ir_bytes, self.linked_json
        )
    }

    pub(in crate::source_check) fn sentence(&self) -> String {
        format!(
            "Imported macros: {} dispatch attempts, {} VM steps; linked user/library code produced by the Reference.",
            self.attempts, self.vm_steps
        )
    }
}

fn push_report(output: &mut String, text: &str) -> Result<(), Failure> {
    if output
        .len()
        .checked_add(text.len())
        .is_none_or(|length| length > MAX_REPORT_BYTES)
    {
        return Err(Failure::resource("imported macro report exceeds 16 MiB"));
    }
    output
        .try_reserve(text.len())
        .map_err(|_| Failure::resource("could not reserve imported macro report"))?;
    output.push_str(text);
    Ok(())
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
        self.prepare_artifact_macros(config)
    }

    /// Build front doors already hold a separately validated source graph. They
    /// need the same policy and exact companion paths without manufacturing a
    /// second source entry just to load its external executable inputs.
    pub(in crate::source_check) fn prepare_artifact_macros(
        &self,
        config: &Config,
    ) -> Result<Prepared, Failure> {
        if self.oleans.is_empty() {
            return Err(Failure::input(
                "imported macros require an external .olean import",
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
        let partition = VerifiedPartition::from_pinned_tsv(text).map_err(|error| {
            if error.is_resource() {
                Failure::resource(error.to_string())
            } else {
                policy_failure(error.to_string())
            }
        })?;
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
            syntax_modules: config.syntax_modules.clone(),
        })
    }
}

impl Prepared {
    pub(in crate::source_check) fn has_imported_syntax(&self) -> bool {
        !self.syntax_modules.is_empty()
    }

    pub(in crate::source_check) fn enable_syntax(
        &self,
        receipt: &mut SourceOleanImport,
    ) -> Result<(), Failure> {
        if self.has_imported_syntax() {
            receipt
                .enable_imported_syntax(
                    &self.syntax_modules,
                    fln::imported_parsers::ParserRegistryLimits::default(),
                )
                .map_err(|error| Failure {
                    class: if error.is_resource() {
                        "resource"
                    } else {
                        "capability"
                    },
                    authority: false,
                    exit: if error.is_resource() { 3 } else { 5 },
                    detail: error.to_string(),
                })?;
        }
        Ok(())
    }

    fn users(&self, receipt: &SourceOleanImport) -> Result<BTreeSet<Name>, Failure> {
        let mut users = BTreeSet::new();
        for (name, code) in self.names.iter().zip(&self.modules) {
            let checked = receipt
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
        Ok(users)
    }

    /// Move the captured code into the shared deferred registry without cloning
    /// the imported closure. Keep its byte count available for the final report.
    pub(in crate::source_check) fn into_inputs(
        self,
        receipt: &SourceOleanImport,
        vm: Option<fln::VmExecutionLimits>,
    ) -> Result<(SourceModuleDeferredMacroInputs, usize), Failure> {
        let users = self.users(receipt)?;
        let mut limits = MacroTreeLimits::default();
        if let Some(vm) = vm {
            limits.dispatch.execution.vm = vm;
        }
        Ok((
            SourceModuleDeferredMacroInputs {
                compilation: MacroCompilationInputs::new(self.modules, self.partition, users),
                registry_limits: MacroRegistryLimits::default(),
                context: MacroContext {
                    quotation_context: Name::anonymous(),
                    current_macro_scope: 0,
                    current_recursion_depth: 0,
                    max_recursion_depth: 1000,
                },
                state: MacroState::default(),
                limits,
            },
            self.bytes,
        ))
    }

    pub(in crate::source_check) fn check(
        self,
        loaded: &Loaded,
        base: Option<&mut OleanBase>,
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
        self.enable_syntax(&mut base.receipt)?;
        let (macro_inputs, ir_bytes) = self.into_inputs(&base.receipt, None)?;
        let inputs = names
            .iter()
            .zip(sources)
            .map(|(name, source)| SourceModuleInput { name, source })
            .collect::<Vec<_>>();
        let result = base
            .receipt
            .check_source_modules_with_deferred_imported_macros(
                &inputs,
                &names[0],
                &fln::KVMap::new(),
                SourceModuleCheckLimits::new(limits),
                macro_inputs,
                None,
            );
        let report = Report::from_attempts(
            ir_bytes,
            &result.attempts,
            result.completed_vm_usage.steps,
            result.tree_usage.visits,
        )?;
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

/// Preserve the library's inconclusive and fault variants at the command boundary.
pub(in crate::source_check) fn result<T, E>(
    outcome: Outcome<Result<T, E>>,
) -> Result<Outcome<T>, E> {
    match outcome {
        Outcome::Complete(Ok(value)) => Ok(Outcome::Complete(value)),
        Outcome::Complete(Err(error)) => Err(error),
        Outcome::Inconclusive(reason) => Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => Ok(Outcome::InternalFault(fault)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn syntax_selection_preserves_structural_names_and_option_boundary() {
        let (kept, config) = Config::take(
            [
                "--imported-syntax",
                "User.Notation",
                "--imported-macros=partition.tsv",
                "--imported-syntax=«Quoted.Module»",
                "--",
                "--imported-syntax",
            ]
            .into_iter()
            .map(OsString::from)
            .collect(),
        )
        .unwrap();
        assert_eq!(
            config.unwrap().syntax_modules,
            vec![
                Name::from_components(["User", "Notation"]),
                Name::from_components(["Quoted.Module"]),
            ]
        );
        assert_eq!(
            kept,
            vec![OsString::from("--"), OsString::from("--imported-syntax")]
        );
        for invalid in ["", "A B", "A\nimport B", "A\naxiom bad : Nat"] {
            assert!(syntax_module(std::ffi::OsStr::new(invalid)).is_err());
        }
    }

    #[test]
    fn runtime_syntax_selection_requires_macro_policy_and_complete_names() {
        let failure = Config::environment(None, Some(OsString::from("User.Syntax"))).unwrap_err();
        assert_eq!(failure.class, "input");
        assert_eq!(
            failure.detail,
            "FLN_SYNTAX_MODULES requires FLN_MACRO_PARTITION"
        );
        for invalid in ["", "User.Syntax,", ",User.Syntax", "User Syntax"] {
            assert!(
                Config::environment(
                    Some(OsString::from("partition.tsv")),
                    Some(OsString::from(invalid)),
                )
                .is_err()
            );
        }
        let selected = Config::environment(
            Some(OsString::from("partition.tsv")),
            Some(OsString::from("User.Syntax, Other.Notation")),
        )
        .unwrap_or_else(|error| panic!("{}", error.detail))
        .unwrap();
        assert_eq!(
            selected.syntax_modules,
            vec![
                Name::from_components(["User", "Syntax"]),
                Name::from_components(["Other", "Notation"]),
            ]
        );
        assert!(matches!(Config::environment(None, None), Ok(None)));
    }

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
