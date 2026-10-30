//! The explicit `fln ir run` mixed-producer execution door.

use super::*;
use fln::imported_ir::modules::{
    LoadedModules, ModuleArtifacts, ModuleLoadError, ModuleLoadLimits,
};
use fln::imported_ir::{
    EntryArgument, IrCapturedOutput, IrExecutionError, IrExecutionLimits, IrExecutionOptions,
    IrInitializationFailure, IrNat, VerifiedPartition,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Arguments {
    entry: fln::Name,
    partition: PathBuf,
    users: BTreeSet<fln::Name>,
    values: Vec<EntryArgument>,
    paths: Vec<PathBuf>,
    modules: Vec<fln::Name>,
    search_paths: Vec<PathBuf>,
    max_bytes: usize,
    capture_output: Option<usize>,
    initialize_globals: bool,
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
    let mut modules = Vec::new();
    let mut search_paths = Vec::new();
    let mut max_bytes = OLEAN_INSPECT_DEFAULT_MAX_BYTES;
    let mut capture_output = None;
    let mut initialize_globals = false;
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
            "--module" => {
                let module = parse_name(value()?, "--module")?;
                module_relative_path(&module).map_err(|error| UsageError(error.to_string()))?;
                modules.push(module);
            }
            "--search-path" => search_paths.push(PathBuf::from(value()?)),
            "--nat" => {
                let number = text(value()?, "--nat")?.parse::<u64>().map_err(|_| {
                    UsageError("--nat requires an unsigned 64-bit integer".to_owned())
                })?;
                values.push(EntryArgument::Nat(IrNat::Small(number)));
            }
            "--string" => values.push(EntryArgument::String(text(value()?, "--string")?)),
            "--erased" => values.push(EntryArgument::Erased),
            "--max-bytes" => max_bytes = parse_byte_limit(&value()?)?,
            "--initialize-globals" => {
                if initialize_globals {
                    return Err(UsageError(
                        "--initialize-globals may be supplied only once".to_owned(),
                    ));
                }
                initialize_globals = true;
            }
            "--capture-output" => {
                if capture_output.is_some() {
                    return Err(UsageError(
                        "--capture-output may be supplied only once".to_owned(),
                    ));
                }
                let bytes = text(value()?, "--capture-output")?
                    .parse::<usize>()
                    .map_err(|_| {
                        UsageError(
                            "--capture-output requires a non-negative byte allowance fitting this platform"
                                .to_owned(),
                        )
                    })?;
                capture_output = Some(bytes);
            }
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
    if paths.is_empty() && modules.is_empty() {
        return Err(UsageError(
            "ir run requires .ir PATHs or --module NAME with --search-path DIR".to_owned(),
        ));
    }
    if !paths.is_empty() && (!modules.is_empty() || !search_paths.is_empty()) {
        return Err(UsageError(
            "ir run cannot combine explicit .ir PATHs with module search".to_owned(),
        ));
    }
    if !modules.is_empty() && search_paths.is_empty() {
        return Err(UsageError(
            "ir run --module requires at least one --search-path DIR".to_owned(),
        ));
    }
    Ok(MultiplexerCommand::IrRun(Arguments {
        entry,
        partition,
        users,
        values,
        paths,
        modules,
        search_paths,
        max_bytes,
        capture_output,
        initialize_globals,
        json,
        vm,
    }))
}

/// A structural module component is one portable filename component. Never
/// split the display form: a quoted import can contain a dot in one component,
/// and an untrusted import cannot turn a slash or numeric name into a path.
fn module_relative_path(module: &fln::Name) -> Result<PathBuf, ModuleLoadError> {
    let invalid = || ModuleLoadError::Resolve {
        module: module.clone(),
        detail: "module name contains an unsafe filesystem component".to_owned(),
    };
    let mut components = Vec::new();
    let mut cursor = module.clone();
    let mut bytes = 0usize;
    while !cursor.is_anonymous() {
        if components.len() >= 128 {
            return Err(ModuleLoadError::Limit("module name components"));
        }
        let fln::LeafView::Str(part) = cursor.leaf_view() else {
            return Err(invalid());
        };
        bytes = bytes
            .checked_add(part.len())
            .filter(|bytes| *bytes <= 16 * 1024)
            .ok_or(ModuleLoadError::Limit("module name bytes"))?;
        let mut segments = Path::new(part).components();
        if part.is_empty()
            || part.ends_with(['.', ' '])
            || part.chars().any(|c| {
                c.is_control() || matches!(c, '/' | '\\' | ':' | '<' | '>' | '"' | '|' | '?' | '*')
            })
            || !matches!(segments.next(), Some(std::path::Component::Normal(_)))
            || segments.next().is_some()
        {
            return Err(invalid());
        }
        components.push(part.to_owned());
        cursor = cursor.parent();
    }
    if components.is_empty() {
        return Err(invalid());
    }
    Ok(components.iter().rev().collect())
}

fn module_file_error(module: &fln::Name, error: BoundedReadFailure) -> ModuleLoadError {
    match error {
        BoundedReadFailure::TooLarge { .. } => ModuleLoadError::Limit("artifact bytes"),
        BoundedReadFailure::Allocation { .. } => ModuleLoadError::Limit("artifact allocation"),
        BoundedReadFailure::Resource { .. } => ModuleLoadError::Limit("artifact read"),
        BoundedReadFailure::Input { .. } => ModuleLoadError::Resolve {
            module: module.clone(),
            detail: error.to_string(),
        },
    }
}

fn read_module_companion(
    path: &Path,
    module: &fln::Name,
    remaining: usize,
) -> Result<Option<Vec<u8>>, ModuleLoadError> {
    let error = |detail| ModuleLoadError::Resolve {
        module: module.clone(),
        detail,
    };
    let metadata = match std::fs::metadata(path) {
        Ok(metadata) => metadata,
        Err(failure) if failure.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(failure) => {
            return Err(error(format!(
                "cannot inspect {}: {failure}",
                path.display()
            )));
        }
    };
    if !metadata.is_file() {
        return Err(error(format!("{} is not a regular file", path.display())));
    }
    // The stream reader remains authoritative if the file changes after this
    // early size check. Both companions consume one cumulative allowance.
    if metadata.len() > remaining as u64 {
        return Err(ModuleLoadError::Limit("artifact bytes"));
    }
    let mut file = std::fs::File::open(path)
        .map_err(|failure| error(format!("cannot open {}: {failure}", path.display())))?;
    let opened = file
        .metadata()
        .map_err(|failure| error(format!("cannot inspect {}: {failure}", path.display())))?;
    if !opened.is_file() {
        return Err(error(format!("{} is not a regular file", path.display())));
    }
    read_bounded_from(&mut file, remaining, "IR module companion")
        .map(Some)
        .map_err(|failure| module_file_error(module, failure))
}

fn load_modules(arguments: &Arguments) -> Result<LoadedModules, ModuleLoadError> {
    let limits = ModuleLoadLimits {
        max_bytes: arguments.max_bytes,
        ..ModuleLoadLimits::default()
    };
    fln::imported_ir::modules::load(&arguments.modules, limits, |module, remaining| {
        let relative = module_relative_path(module)?;
        for root in &arguments.search_paths {
            let base = root.join(&relative);
            // Append extensions, preserving dots inside quoted components.
            let companion = |extension: &str| {
                let mut path = base.as_os_str().to_os_string();
                path.push(extension);
                PathBuf::from(path)
            };
            let Some(olean) = read_module_companion(&companion(".olean"), module, remaining)?
            else {
                continue;
            };
            // Select companions from the same search root. An absent .ir is
            // visible in the report; a later root cannot supply unrelated code
            // for a public import table selected from this root.
            let ir = read_module_companion(&companion(".ir"), module, remaining - olean.len())?;
            return Ok(Some(ModuleArtifacts { olean, ir }));
        }
        Ok(None)
    })
}

fn module_load_failure(error: ModuleLoadError, json: bool) -> MultiplexerOutput {
    if error.is_resource() {
        return failure("resource", &error.to_string(), json, 3);
    }
    let (class, code) = match error {
        ModuleLoadError::MissingModule(_) => ("missing-module", 3),
        ModuleLoadError::ImportCycle(_) => ("invalid-ir", 1),
        ModuleLoadError::Decode { .. } => ("codec", 1),
        _ => ("input", 1),
    };
    failure(class, &error.to_string(), json, code)
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

/// Preserve the complete accepted byte sequence, including NULs and newlines.
/// Canonical native String writes are UTF-8; a future binary diagnostic must
/// still be inspectable without replacement characters or raw JSON controls.
fn captured_output_data(output: &IrCapturedOutput) -> (&'static str, String) {
    match std::str::from_utf8(&output.bytes) {
        Ok(text) => ("utf-8", json_string(text)),
        Err(_) => {
            let mut data = String::from("[");
            for (index, byte) in output.bytes.iter().enumerate() {
                if index != 0 {
                    data.push(',');
                }
                data.push_str(&byte.to_string());
            }
            data.push(']');
            ("bytes", data)
        }
    }
}

fn captured_output_json(output: &IrCapturedOutput) -> String {
    let (encoding, data) = captured_output_data(output);
    format!(
        "{{\"encoding\":{},\"data\":{},\"byteLength\":{},\"maxBytes\":{}}}",
        json_string(encoding),
        data,
        output.bytes.len(),
        output.max_bytes
    )
}

fn initialization_failure_json(failure: &IrInitializationFailure) -> String {
    format!(
        "{{\"declaration\":{},\"initializer\":{},\"kind\":{},\"resultKind\":{}}}",
        json_string(&failure.declaration.to_display_string()),
        json_string(&failure.initializer.to_display_string()),
        json_string(if failure.malformed {
            "malformed-result"
        } else {
            "io-error"
        }),
        json_string(&vm_value_kind_name(fln::vm_value_kind(&failure.result))),
    )
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
    let mut loaded_names = Vec::new();
    let mut missing_ir = Vec::new();
    let mut bytes_read = 0usize;
    if arguments.modules.is_empty() {
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
    } else {
        let loaded = match load_modules(&arguments) {
            Ok(loaded) => loaded,
            Err(error) => return module_load_failure(error, arguments.json),
        };
        bytes_read = loaded.bytes_read();
        loaded_names = loaded.module_names().to_vec();
        missing_ir = loaded.missing_ir_modules().to_vec();
        modules = loaded.into_modules();
    }
    let compiled = fln::imported_ir::compile_with_options(
        &modules,
        &arguments.entry,
        &arguments.values,
        &policy,
        &arguments.users,
        IrExecutionOptions {
            limits: IrExecutionLimits::default(),
            capture_output_bytes: arguments.capture_output,
            initialize_globals: arguments.initialize_globals,
        },
    );
    let compiled = match compiled {
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
    let mut value_kind = None;
    let (outcome, value, detail, code, steps, peak) = match &execution.outcome {
        fln::Outcome::Complete(exit @ fln::VmExit::Returned(done)) => {
            if execution.captured_output.is_some() {
                // This is the physical return kind, not an inferred source
                // type or an interpretation of an IO.Result constructor tag.
                value_kind = Some(vm_value_kind_name(fln::vm_value_kind(&done.value)));
            }
            match closed_cli_value(exit) {
                Ok(value) => (
                    "complete",
                    value,
                    None,
                    0,
                    Some(done.usage.steps),
                    Some(done.usage.peak_stack_depth),
                ),
                Err(error) if execution.captured_output.is_none() => {
                    return failure("value-projection", &error.to_string(), arguments.json, 3);
                }
                Err(error) => (
                    "inconclusive",
                    None,
                    Some(format!("value projection: {error}")),
                    3,
                    Some(done.usage.steps),
                    Some(done.usage.peak_stack_depth),
                ),
            }
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
        let names = |names: &[fln::Name]| {
            names
                .iter()
                .map(|name| json_string(&name.to_display_string()))
                .collect::<Vec<_>>()
                .join(",")
        };
        let initialization_fields = if arguments.initialize_globals {
            format!(
                ",\"initializeGlobals\":true,\"initializationFailure\":{}",
                execution
                    .initialization_failure
                    .as_ref()
                    .map(initialization_failure_json)
                    .unwrap_or_else(|| "null".to_owned())
            )
        } else {
            String::new()
        };
        let output_fields = execution
            .captured_output
            .as_ref()
            .map_or_else(String::new, |output| {
                format!(
                    ",\"valueKind\":{},\"capturedOutput\":{}",
                    value_kind
                        .as_deref()
                        .map(json_string)
                        .unwrap_or_else(|| "null".to_owned()),
                    captured_output_json(output),
                )
            });
        format!(
            "{{\"schema\":\"fln.ir-run/1\",\"outcome\":{},\"authority\":false,\"engine\":\"golem\",\"entry\":{},\"value\":{},\"detail\":{},\"steps\":{},\"peakStackDepth\":{},\"linkedReferenceFunctions\":[{}],\"nativeExterns\":[{}],\"loadedModules\":[{}],\"missingIrModules\":[{}],\"artifactBytes\":{}{}{}}}\n",
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
            natives,
            names(&loaded_names),
            names(&missing_ir),
            bytes_read,
            initialization_fields,
            output_fields
        )
    } else {
        let mut text = format!(
            "IR execution: {outcome}\nentry: {}\n",
            arguments.entry.to_display_string()
        );
        if !loaded_names.is_empty() {
            text.push_str(&format!(
                "loaded modules: {} ({bytes_read} artifact bytes)\n",
                loaded_names.len()
            ));
            for module in &missing_ir {
                text.push_str(&format!(
                    "module without IR: {}\n",
                    module.to_display_string()
                ));
            }
        }
        if arguments.initialize_globals {
            text.push_str("global initialization: selected named dependency closure\n");
        }
        if let Some(failure) = &execution.initialization_failure {
            text.push_str(&format!(
                "initializer failure: {} (global: {}, kind: {}, result kind: {})\n",
                failure.initializer.to_display_string(),
                failure.declaration.to_display_string(),
                if failure.malformed {
                    "malformed-result"
                } else {
                    "io-error"
                },
                vm_value_kind_name(fln::vm_value_kind(&failure.result)),
            ));
        }
        if let Some(value) = value {
            text.push_str(&format!("value: {value}\n"));
        }
        if let Some(kind) = value_kind {
            text.push_str(&format!("value kind: {kind}\n"));
        }
        if let Some(output) = &execution.captured_output {
            let (encoding, data) = captured_output_data(output);
            text.push_str(&format!(
                "captured output ({} / {} bytes, {encoding}): {data}\n",
                output.bytes.len(),
                output.max_bytes
            ));
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

    fn temporary_root() -> PathBuf {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let tick = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "fln-ir-module-cli-{}-{tick}-{}",
            std::process::id(),
            NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path).unwrap();
        path
    }

    fn write_module(root: &Path, name: &str, imports: &[fln::Name], code: bool) -> usize {
        let imports: Vec<_> = imports
            .iter()
            .cloned()
            .map(|module| fln::OleanModuleImport {
                module,
                import_all: false,
                is_exported: false,
                is_meta: false,
            })
            .collect();
        let bytes = fln::encode_olean_module(
            fln::OleanModuleWriteInput {
                is_module: false,
                imports: &imports,
                constants: &[],
                extra_const_names: &[],
            },
            fln::OleanWriteHeader {
                version: fln::OLEAN_ACCEPTED_VERSIONS[0],
                flags: 1,
                lean_version: fln::OLEAN_PIN_TAG.strip_prefix('v').unwrap(),
                githash: fln::OLEAN_PIN_COMMIT,
                base_addr: fln::OLEAN_REGION_ALIGN as u64,
            },
            fln::OleanWriteBudget::default(),
        )
        .unwrap()
        .bytes;
        let path = root.join(name);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path.with_extension("olean"), &bytes).unwrap();
        let mut size = bytes.len();
        if code {
            let ir = include_bytes!("../../fln-olean/fixtures/ir/Init.Data.Nat.Basic.ir");
            std::fs::write(path.with_extension("ir"), ir).unwrap();
            size += ir.len();
        }
        size
    }

    fn module_arguments(root: &Path) -> Arguments {
        let args = [
            OsString::from("--entry"),
            OsString::from("Nat.min"),
            OsString::from("--partition"),
            OsString::from("p.tsv"),
            OsString::from("--module"),
            OsString::from("Root"),
            OsString::from("--search-path"),
            root.as_os_str().to_os_string(),
        ];
        let MultiplexerCommand::IrRun(arguments) = parse(args.to_vec()).unwrap() else {
            panic!("module parser");
        };
        arguments
    }

    fn name(text: &str) -> fln::Name {
        fln::Name::from_components(text.split('.'))
    }

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
        assert_eq!(parsed.capture_output, None);
        assert!(!parsed.initialize_globals);
    }

    #[test]
    fn global_initialization_is_explicit_unique_and_composes_with_both_input_modes() {
        for tail in [
            vec!["input.ir"],
            vec!["--module", "User.Main", "--search-path", "lib"],
        ] {
            let argv = [
                "--entry",
                "User.main",
                "--partition",
                "p.tsv",
                "--initialize-globals",
                "--capture-output",
                "0",
                "--erased",
            ]
            .into_iter()
            .chain(tail)
            .map(OsString::from)
            .collect();
            let MultiplexerCommand::IrRun(args) = parse(argv).unwrap() else {
                panic!("IR run parser");
            };
            assert!(args.initialize_globals);
            assert_eq!(args.capture_output, Some(0));
            assert_eq!(args.values, [EntryArgument::Erased]);
        }

        let duplicate = [
            "--entry",
            "User.main",
            "--partition",
            "p.tsv",
            "--initialize-globals",
            "--initialize-globals",
            "input.ir",
        ];
        let error = parse(duplicate.map(OsString::from).to_vec()).unwrap_err();
        assert_eq!(
            error.to_string(),
            "--initialize-globals may be supplied only once"
        );

        let literal_path = [
            "--entry",
            "User.main",
            "--partition",
            "p.tsv",
            "--",
            "--initialize-globals",
        ];
        let MultiplexerCommand::IrRun(args) =
            parse(literal_path.map(OsString::from).to_vec()).unwrap()
        else {
            panic!("IR run parser");
        };
        assert!(!args.initialize_globals);
        assert_eq!(args.paths, [PathBuf::from("--initialize-globals")]);
    }

    #[test]
    fn initialization_failure_report_distinguishes_io_errors_from_malformed_results() {
        use fln_rt::obj::Obj;

        for (malformed, result, kind, result_kind) in [
            (
                false,
                Obj::mk_ctor(1, vec![Obj::mk_string("stopped"), Obj::mk_nat(0)], &[]),
                "io-error",
                "constructor:1",
            ),
            (true, Obj::mk_nat(7), "malformed-result", "scalar"),
        ] {
            let failure = IrInitializationFailure {
                declaration: name("User.global"),
                initializer: fln::Name::str(name("User"), "quoted\"initializer\n"),
                result,
                malformed,
            };
            let json = initialization_failure_json(&failure);
            assert!(json.contains("\"declaration\":\"User.global\""), "{json}");
            assert!(
                json.contains("\"initializer\":\"User.quoted\\\"initializer\\n\""),
                "{json}"
            );
            assert!(json.contains(&format!("\"kind\":\"{kind}\"")), "{json}");
            assert!(
                json.contains(&format!("\"resultKind\":\"{result_kind}\"")),
                "{json}"
            );
            assert!(!json.contains('\n'), "{json}");
        }
    }

    #[test]
    fn output_capture_requires_an_explicit_unique_byte_allowance_including_zero() {
        for bytes in [0usize, 12, usize::MAX] {
            let argv = [
                "--entry",
                "User.main",
                "--partition",
                "p.tsv",
                "input.ir",
                "--capture-output",
                &bytes.to_string(),
            ];
            let MultiplexerCommand::IrRun(args) = parse(argv.map(OsString::from).to_vec()).unwrap()
            else {
                panic!("IR run parser");
            };
            assert_eq!(args.capture_output, Some(bytes));
        }
        for tail in [
            vec!["--capture-output"],
            vec!["--capture-output", "-1"],
            vec!["--capture-output", "NaN"],
            vec!["--capture-output", "18446744073709551616"],
            vec!["--capture-output", "0", "--capture-output", "1"],
        ] {
            let args = ["--entry", "User.main", "--partition", "p.tsv", "input.ir"]
                .into_iter()
                .chain(tail)
                .map(OsString::from)
                .collect();
            let error = parse(args).unwrap_err();
            assert!(error.to_string().contains("--capture-output"));
        }
    }

    #[test]
    fn captured_output_serializes_exact_bytes_without_control_or_binary_loss() {
        assert_eq!(
            captured_output_json(&IrCapturedOutput {
                bytes: "\0\"\\\nλ🙂".as_bytes().to_vec(),
                max_bytes: 16,
            }),
            "{\"encoding\":\"utf-8\",\"data\":\"\\u0000\\\"\\\\\\nλ🙂\",\"byteLength\":10,\"maxBytes\":16}",
        );
        assert_eq!(
            captured_output_json(&IrCapturedOutput {
                bytes: vec![0xff, 0, 0x80],
                max_bytes: 3,
            }),
            "{\"encoding\":\"bytes\",\"data\":[255,0,128],\"byteLength\":3,\"maxBytes\":3}",
        );
        assert_eq!(
            captured_output_json(&IrCapturedOutput {
                bytes: Vec::new(),
                max_bytes: 0
            }),
            "{\"encoding\":\"utf-8\",\"data\":\"\",\"byteLength\":0,\"maxBytes\":0}",
        );
    }

    #[test]
    fn installed_module_options_preserve_roots_and_refuse_ambiguous_modes() {
        let argv = [
            "--entry",
            "Nat.min",
            "--partition",
            "p.tsv",
            "--module",
            "Root",
            "--search-path",
            "first",
            "--module",
            "Other",
            "--search-path",
            "second",
        ];
        let MultiplexerCommand::IrRun(args) = parse(argv.map(OsString::from).to_vec()).unwrap()
        else {
            panic!("module parser");
        };
        assert_eq!(args.modules, [name("Root"), name("Other")]);
        assert_eq!(
            args.search_paths,
            [PathBuf::from("first"), PathBuf::from("second")]
        );
        for tail in [
            vec!["--module", "Root"],
            vec!["--search-path", "lib", "input.ir"],
            vec!["--module", "Root", "--search-path", "lib", "input.ir"],
            vec!["--module", "../escape", "--search-path", "lib"],
            vec!["--module", "A\\B", "--search-path", "lib"],
        ] {
            let argv: Vec<_> = ["--entry", "Nat.min", "--partition", "p.tsv"]
                .into_iter()
                .chain(tail)
                .map(OsString::from)
                .collect();
            assert!(parse(argv).is_err());
        }
    }

    #[test]
    fn filesystem_module_loader_closes_a_diamond_with_one_cumulative_byte_budget() {
        let root = temporary_root();
        let total = write_module(&root, "Root", &[name("Left"), name("Right")], false)
            + write_module(&root, "Left", &[name("Nested.Dependency")], false)
            + write_module(&root, "Right", &[name("Nested.Dependency")], false)
            + write_module(&root, "Nested/Dependency", &[], true);
        let mut args = module_arguments(&root);
        args.max_bytes = total;
        let loaded = load_modules(&args).unwrap();
        assert_eq!(loaded.bytes_read(), total);
        assert_eq!(
            loaded.module_names(),
            [
                name("Left"),
                name("Right"),
                name("Root"),
                name("Nested.Dependency")
            ]
        );
        assert_eq!(
            loaded.missing_ir_modules(),
            [name("Left"), name("Right"), name("Root")]
        );
        assert!(
            loaded
                .modules()
                .iter()
                .flat_map(|module| &module.decls)
                .any(|decl| decl.name() == &name("Nat.min"))
        );
        args.max_bytes = total - 1;
        let error = load_modules(&args).unwrap_err();
        assert!(error.is_resource());
        let output = module_load_failure(error, true);
        assert_eq!(output.exit_code, 3);
        assert!(output.stdout.is_empty());
        assert!(!output.stderr.contains("\"value\":"));
        args.max_bytes = total;
        assert_eq!(load_modules(&args).unwrap().bytes_read(), total);
    }

    #[test]
    fn module_search_never_mixes_companions_or_skips_a_corrupt_first_match() {
        let first = temporary_root();
        let second = temporary_root();
        write_module(&first, "Root", &[], false);
        write_module(&second, "Root", &[], true);
        let mut args = module_arguments(&first);
        args.search_paths.push(second.clone());
        let loaded = load_modules(&args).unwrap();
        assert_eq!(loaded.missing_ir_modules(), [name("Root")]);
        assert!(loaded.modules()[0].decls.is_empty());
        std::fs::write(first.join("Root.ir"), b"corrupt IR").unwrap();
        assert!(matches!(
            load_modules(&args),
            Err(ModuleLoadError::Decode {
                artifact: ".ir code",
                ..
            })
        ));
        std::fs::write(first.join("Root.olean"), b"corrupt olean").unwrap();
        assert!(matches!(
            load_modules(&args),
            Err(ModuleLoadError::Decode {
                artifact: ".olean import table",
                ..
            })
        ));

        let empty = temporary_root();
        let mut later = module_arguments(&empty);
        later.search_paths.push(second);
        assert!(
            load_modules(&later)
                .unwrap()
                .missing_ir_modules()
                .is_empty()
        );
        std::fs::create_dir(empty.join("Root.olean")).unwrap();
        assert!(matches!(
            load_modules(&later),
            Err(ModuleLoadError::Resolve { .. })
        ));
    }

    #[test]
    fn imported_names_and_missing_imports_are_checked_before_execution() {
        let root = temporary_root();
        write_module(&root, "Root", &[name("Missing")], false);
        let args = module_arguments(&root);
        assert!(
            matches!(load_modules(&args), Err(ModuleLoadError::MissingModule(module)) if module == name("Missing"))
        );
        for unsafe_name in [
            fln::Name::str(fln::Name::anonymous(), "../escape"),
            fln::Name::str(fln::Name::anonymous(), "A\\B"),
            fln::Name::str(fln::Name::anonymous(), "/absolute"),
            fln::Name::str(fln::Name::anonymous(), "bad\nname"),
            fln::Name::num(fln::Name::anonymous(), 1),
        ] {
            write_module(&root, "Root", &[unsafe_name], false);
            assert!(matches!(
                load_modules(&args),
                Err(ModuleLoadError::Resolve { .. })
            ));
        }
        assert_eq!(
            module_relative_path(&fln::Name::str(name("Nested"), "Part.Name")).unwrap(),
            PathBuf::from("Nested/Part.Name")
        );
        write_module(&root, "Root", &[name("Root")], false);
        assert!(matches!(
            load_modules(&args),
            Err(ModuleLoadError::ImportCycle(_))
        ));
    }
}
