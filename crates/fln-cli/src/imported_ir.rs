//! The explicit `fln ir run` mixed-producer execution door.

use super::*;
use fln::imported_ir::{
    EntryArgument, IrExecutionError, IrExecutionLimits, IrNat, VerifiedPartition,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Arguments {
    entry: fln::Name,
    partition: PathBuf,
    users: BTreeSet<fln::Name>,
    values: Vec<EntryArgument>,
    paths: Vec<PathBuf>,
    max_bytes: usize,
    json: bool,
    vm: fln::VmExecutionLimits,
}

fn text(value: OsString, option: &str) -> Result<String, UsageError> {
    value
        .into_string()
        .map_err(|_| UsageError(format!("{option} requires UTF-8 text")))
}

fn parse_name(value: OsString, option: &str) -> Result<fln::Name, UsageError> {
    let text = text(value, option)?;
    if text.is_empty() || text.split('.').any(str::is_empty) {
        return Err(UsageError(format!(
            "{option} requires a nonempty dotted name"
        )));
    }
    Ok(fln::Name::from_components(text.split('.')))
}

pub(super) fn parse(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
    let mut args = arguments.into_iter();
    let mut entry = None;
    let mut partition = None;
    let mut users = BTreeSet::new();
    let mut values = Vec::new();
    let mut paths = Vec::new();
    let mut max_bytes = OLEAN_INSPECT_DEFAULT_MAX_BYTES;
    let mut json = false;
    let mut vm = fln::VmExecutionLimits::user_program();
    let mut options = true;
    while let Some(arg) = args.next() {
        if options && arg == "--" {
            options = false;
            continue;
        }
        if !options || !arg.to_string_lossy().starts_with('-') {
            paths.push(PathBuf::from(arg));
            continue;
        }
        let flag = text(arg, "option")?;
        let mut value = || {
            args.next()
                .ok_or_else(|| UsageError(format!("{flag} requires a value")))
        };
        match flag.as_str() {
            "--help" | "-h" => return Ok(MultiplexerCommand::Help),
            "--json" => json = true,
            "--entry" => {
                if entry.is_some() {
                    return Err(UsageError("--entry may be supplied only once".to_owned()));
                }
                entry = Some(parse_name(value()?, "--entry")?);
            }
            "--partition" => {
                if partition.is_some() {
                    return Err(UsageError(
                        "--partition may be supplied only once".to_owned(),
                    ));
                }
                partition = Some(PathBuf::from(value()?));
            }
            "--user" => {
                users.insert(parse_name(value()?, "--user")?);
            }
            "--nat" => {
                let number = text(value()?, "--nat")?.parse::<u64>().map_err(|_| {
                    UsageError("--nat requires an unsigned 64-bit integer".to_owned())
                })?;
                values.push(EntryArgument::Nat(IrNat::Small(number)));
            }
            "--string" => values.push(EntryArgument::String(text(value()?, "--string")?)),
            "--erased" => values.push(EntryArgument::Erased),
            "--max-bytes" => max_bytes = parse_byte_limit(&value()?)?,
            "--fln-max-steps" | "--fln-max-frames" => {
                let number = text(value()?, &flag)?
                    .parse::<u64>()
                    .map_err(|_| UsageError(format!("{flag} requires an unsigned integer")))?;
                if flag == "--fln-max-steps" {
                    vm.max_steps = number;
                } else {
                    vm.max_stack_depth = number;
                }
            }
            _ => return Err(UsageError(format!("unknown ir run option {flag:?}"))),
        }
    }
    let entry = entry.ok_or_else(|| UsageError("ir run requires --entry NAME".to_owned()))?;
    let partition = partition.ok_or_else(|| {
        UsageError("ir run requires --partition PATH to the pinned census".to_owned())
    })?;
    if paths.is_empty() {
        return Err(UsageError(
            "ir run requires at least one .ir PATH".to_owned(),
        ));
    }
    Ok(MultiplexerCommand::IrRun(Arguments {
        entry,
        partition,
        users,
        values,
        paths,
        max_bytes,
        json,
        vm,
    }))
}

fn failure(class: &str, detail: &str, json: bool, code: u8) -> MultiplexerOutput {
    let detail = BoundedText::new(detail.to_owned());
    let stderr = if json {
        format!(
            "{{\"schema\":\"fln.ir-run/1\",\"outcome\":\"error\",\"authority\":false,\"class\":{},\"detail\":{},\"detailTruncated\":{}}}\n",
            json_string(class),
            json_string(detail.text()),
            detail.truncated()
        )
    } else {
        format!("fln ir run: {class}: {}\n", detail.text())
    };
    MultiplexerOutput::failure(stderr, code)
}

fn preparation_failure(error: IrExecutionError, json: bool) -> MultiplexerOutput {
    if error.is_resource() {
        return failure("resource", &error.to_string(), json, 3);
    }
    let (class, code) = match error {
        IrExecutionError::PartitionDigest
        | IrExecutionError::Partition(_)
        | IrExecutionError::ToolchainApi(_)
        | IrExecutionError::UserOverridesCensus(_) => ("policy-refusal", 1),
        IrExecutionError::DuplicateDeclaration(_)
        | IrExecutionError::EntryArity { .. }
        | IrExecutionError::IrValidation(_) => ("invalid-ir", 1),
        IrExecutionError::Limit(_) => ("resource", 3),
        IrExecutionError::FirValidation(_) | IrExecutionError::Lowering(_) => {
            ("lowering-refusal", 3)
        }
        _ => ("unsupported", 3),
    };
    failure(class, &error.to_string(), json, code)
}

pub(super) fn run(arguments: Arguments) -> MultiplexerOutput {
    stdout_capture::json(arguments.json, "fln.ir-run/1", || run_uncaptured(arguments))
}

fn run_uncaptured(arguments: Arguments) -> MultiplexerOutput {
    let partition_bytes =
        match read_bounded(&arguments.partition, 64 * 1024 * 1024, "pinned IR census") {
            Ok(bytes) => bytes,
            Err(error) => return failure(error.class(), &error.to_string(), arguments.json, 3),
        };
    let partition_text = match std::str::from_utf8(&partition_bytes) {
        Ok(text) => text,
        Err(error) => return failure("policy-refusal", &error.to_string(), arguments.json, 1),
    };
    let policy = match VerifiedPartition::from_pinned_tsv(partition_text) {
        Ok(policy) => policy,
        Err(error) => return preparation_failure(error, arguments.json),
    };
    let mut modules = Vec::new();
    let mut bytes_read = 0usize;
    for path in &arguments.paths {
        let remaining = arguments.max_bytes.saturating_sub(bytes_read);
        let bytes = match read_bounded(path, remaining, "IR module") {
            Ok(bytes) => bytes,
            Err(error) => return failure(error.class(), &error.to_string(), arguments.json, 3),
        };
        bytes_read = bytes_read.saturating_add(bytes.len());
        match fln::decode_ir_artifact(&bytes, remaining) {
            Ok(module) => modules.push(module),
            Err(error) => {
                return failure(
                    if error.is_resource() {
                        "resource"
                    } else {
                        "codec"
                    },
                    &error.to_string(),
                    arguments.json,
                    if error.is_resource() { 3 } else { 1 },
                );
            }
        }
    }
    let compiled = match fln::imported_ir::compile(
        &modules,
        &arguments.entry,
        &arguments.values,
        &policy,
        &arguments.users,
        IrExecutionLimits::default(),
    ) {
        Ok(compiled) => compiled,
        Err(error) => return preparation_failure(error, arguments.json),
    };
    let execution = compiled.execute(arguments.vm, None);
    let reference = execution
        .reference_functions
        .iter()
        .map(|function| {
            format!(
                "{{\"name\":{},\"producer\":\"reference\",\"function\":{}}}",
                json_string(&function.name.to_display_string()),
                function.function.get()
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let natives = execution
        .native_externs
        .iter()
        .map(|row| json_string(row))
        .collect::<Vec<_>>()
        .join(",");
    let (outcome, value, detail, code, steps, peak) = match &execution.outcome {
        fln::Outcome::Complete(exit @ fln::VmExit::Returned(done)) => {
            let value = match closed_cli_value(exit) {
                Ok(value) => value,
                Err(error) => {
                    return failure("value-projection", &error.to_string(), arguments.json, 3);
                }
            };
            (
                "complete",
                value,
                None,
                0,
                Some(done.usage.steps),
                Some(done.usage.peak_stack_depth),
            )
        }
        fln::Outcome::Complete(fln::VmExit::Panicked { message, usage }) => (
            "program-panic",
            None,
            Some(message.clone()),
            1,
            Some(usage.steps),
            Some(usage.peak_stack_depth),
        ),
        fln::Outcome::Complete(fln::VmExit::Refused { refusal, usage }) => (
            "inconclusive",
            None,
            Some(refusal.to_string()),
            3,
            Some(usage.steps),
            Some(usage.peak_stack_depth),
        ),
        fln::Outcome::Inconclusive(reason) => (
            "inconclusive",
            None,
            Some(format!("{reason:?}")),
            3,
            None,
            None,
        ),
        fln::Outcome::InternalFault(fault) => (
            "internal-fault",
            None,
            Some(format!("{fault:?}")),
            4,
            None,
            None,
        ),
    };
    let report = if arguments.json {
        format!(
            "{{\"schema\":\"fln.ir-run/1\",\"outcome\":{},\"authority\":false,\"engine\":\"golem\",\"entry\":{},\"value\":{},\"detail\":{},\"steps\":{},\"peakStackDepth\":{},\"linkedReferenceFunctions\":[{}],\"nativeExterns\":[{}]}}\n",
            json_string(outcome),
            json_string(&arguments.entry.to_display_string()),
            value
                .as_ref()
                .map(SourceFinalValue::json)
                .unwrap_or_else(|| "null".to_owned()),
            detail
                .as_deref()
                .map(json_string)
                .unwrap_or_else(|| "null".to_owned()),
            steps
                .map(|n| n.to_string())
                .unwrap_or_else(|| "null".to_owned()),
            peak.map(|n| n.to_string())
                .unwrap_or_else(|| "null".to_owned()),
            reference,
            natives
        )
    } else {
        let mut text = format!(
            "IR execution: {outcome}\nentry: {}\n",
            arguments.entry.to_display_string()
        );
        if let Some(value) = value {
            text.push_str(&format!("value: {value}\n"));
        }
        if let Some(detail) = detail {
            text.push_str(&format!("detail: {detail}\n"));
        }
        for function in &execution.reference_functions {
            text.push_str(&format!(
                "linked function: {} (producer: reference)\n",
                function.name.to_display_string()
            ));
        }
        for native in &execution.native_externs {
            text.push_str(&format!("native extern: {native}\n"));
        }
        if let Some(steps) = steps {
            text.push_str(&format!("execution: {steps} steps\n"));
        }
        text
    };
    if code == 0 {
        MultiplexerOutput::success(report)
    } else {
        MultiplexerOutput::failure(report, code)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ir_execution_requires_explicit_policy_and_preserves_argument_order() {
        let missing = super::super::run(["ir", "run"].map(OsString::from));
        assert_eq!(missing.exit_code, 2);
        assert!(missing.stderr.contains("--entry"));
        let args = [
            "--entry",
            "User.main",
            "--partition",
            "p.tsv",
            "--nat",
            "7",
            "--string",
            "text",
            "--erased",
            "--fln-max-steps",
            "42",
            "input.ir",
        ];
        let MultiplexerCommand::IrRun(parsed) = parse(args.map(OsString::from).to_vec()).unwrap()
        else {
            panic!("IR run parser")
        };
        assert_eq!(
            parsed.values,
            vec![
                EntryArgument::Nat(IrNat::Small(7)),
                EntryArgument::String("text".into()),
                EntryArgument::Erased
            ]
        );
        assert_eq!(parsed.vm.max_steps, 42);
        assert_eq!(parsed.paths, vec![PathBuf::from("input.ir")]);
    }
}
