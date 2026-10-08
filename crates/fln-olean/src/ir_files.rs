//! The file-to-validator-to-graph path for IR analysis.
//!
//! Files are data only. No Reference code, initializer, extern, or closure runs.
//! Limits cover actual input bytes and cumulative captured payload bytes across
//! the supplied closure; decoder object/node limits additionally apply per file.
//! DOT is a diagnostic export, not a canonical cache format or an execution
//! certificate. Census classification and content-addressed publication remain
//! separate obligations of `fln-ir-decoder-call-graph-sjzl`.

use crate::ir::graph::IrNodeKind;
use crate::ir::{IrDecodeError, IrDecodeLimits, IrModule, decode_ir};
use crate::ir_types::{IrTypeValidationError, IrTypeValidationSummary, check_after_structure};
use crate::ir_validate::{
    IrValidatedGraphError, IrValidationLimits, ValidatedIrCallGraph, build_validated_ir_call_graph,
};
use crate::region::{OleanView, RegionError, WalkBudget};
use fln_core::name::Name;
use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::io::{self, Read};
use std::path::{Path, PathBuf};

#[derive(Debug, Clone, Copy)]
pub struct IrFileLimits {
    pub max_files: usize,
    pub max_file_bytes: u64,
    pub max_total_bytes: u64,
    pub max_payload_bytes: usize,
    pub decode: IrDecodeLimits,
    pub validation: IrValidationLimits,
}

impl Default for IrFileLimits {
    fn default() -> Self {
        Self {
            max_files: 16_384,
            max_file_bytes: 256 * 1024 * 1024,
            max_total_bytes: 1024 * 1024 * 1024,
            max_payload_bytes: 1024 * 1024 * 1024,
            decode: IrDecodeLimits::default(),
            validation: IrValidationLimits::default(),
        }
    }
}

#[derive(Debug)]
pub enum IrFileError {
    EmptyInput,
    DuplicateInput(PathBuf),
    NonRegularFile(PathBuf),
    Limit { resource: &'static str },
    Io { path: PathBuf, source: io::Error },
    Container { path: PathBuf, source: RegionError },
    MissingIrBlock(PathBuf),
    Decode { path: PathBuf, source: IrDecodeError },
    Validation(IrValidatedGraphError),
    Representation(IrTypeValidationError),
}

impl IrFileError {
    /// Missing resources or unsupported container capabilities are not invalid IR.
    pub fn is_inconclusive(&self) -> bool {
        match self {
            Self::Limit { .. } | Self::Io { .. } | Self::NonRegularFile(_) => true,
            Self::Container { source, .. } => matches!(
                source,
                RegionError::BudgetExhausted { .. }
                    | RegionError::PayloadBudgetExhausted { .. }
                    | RegionError::UnsupportedVersion(_)
                    | RegionError::ClosureUnsupported { .. }
            ),
            Self::Decode { source, .. } => source.is_resource(),
            Self::Validation(source) => source.is_resource(),
            Self::Representation(source) => source.is_resource(),
            _ => false,
        }
    }
}

impl std::fmt::Display for IrFileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "IR file closure: {self:?}")
    }
}

impl std::error::Error for IrFileError {}

#[derive(Debug)]
pub struct CheckedIrFiles {
    pub checked: ValidatedIrCallGraph,
    pub input_bytes: u64,
    pub captured_payload_bytes: usize,
    /// Present only when the expression representation pass actually ran.
    /// Its work count includes the structural pass, not a fresh allowance.
    pub representation: Option<IrTypeValidationSummary>,
}

fn limit(resource: &'static str) -> IrFileError {
    IrFileError::Limit { resource }
}

/// Read a regular file under an actual-byte cap, not just a metadata estimate.
/// Paths are caller-selected; this is not a sandbox against concurrent hostile
/// filesystem mutation. Preflight avoids opening ordinary FIFOs/devices.
fn read_file(path: &Path, cap: u64) -> Result<Vec<u8>, IrFileError> {
    let io_error = |source| IrFileError::Io {
        path: path.to_owned(),
        source,
    };
    let metadata = std::fs::metadata(path).map_err(io_error)?;
    if !metadata.is_file() {
        return Err(IrFileError::NonRegularFile(path.to_owned()));
    }
    if metadata.len() > cap {
        return Err(limit("input bytes"));
    }
    let mut file = File::open(path).map_err(io_error)?;
    if !file.metadata().map_err(io_error)?.is_file() {
        return Err(IrFileError::NonRegularFile(path.to_owned()));
    }
    let mut out = Vec::new();
    let mut buffer = [0u8; 16 * 1024];
    loop {
        let size = match file.read(&mut buffer) {
            Ok(0) => break,
            Ok(size) => size,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(io_error(error)),
        };
        let next = out
            .len()
            .checked_add(size)
            .ok_or_else(|| limit("input bytes"))?;
        if next as u64 > cap {
            return Err(limit("input bytes"));
        }
        out.try_reserve(size)
            .map_err(|_| limit("input allocation"))?;
        out.extend_from_slice(&buffer[..size]);
    }
    Ok(out)
}

/// Validate the structure of exactly the supplied file closure. This retains
/// the original structural-only API; use [`check_ir_files_with_types`] for the
/// additional expression representation rules used by the command by default.
/// Imports are not fetched and missing signatures are not invented.
pub fn check_ir_files(
    paths: &[PathBuf],
    census_externs: &BTreeMap<Name, usize>,
    limits: IrFileLimits,
) -> Result<CheckedIrFiles, IrFileError> {
    check_files(paths, census_externs, limits, false)
}

/// Decode, structurally validate, then check expression representations before
/// returning any graph. Both passes share `validation.max_work`; a type-rule
/// refusal or resource stop returns no partial result. This does not check
/// ownership, constructor layouts or full application ABI signatures.
pub fn check_ir_files_with_types(
    paths: &[PathBuf],
    census_externs: &BTreeMap<Name, usize>,
    limits: IrFileLimits,
) -> Result<CheckedIrFiles, IrFileError> {
    check_files(paths, census_externs, limits, true)
}

fn check_files(
    paths: &[PathBuf],
    census_externs: &BTreeMap<Name, usize>,
    limits: IrFileLimits,
    check_types: bool,
) -> Result<CheckedIrFiles, IrFileError> {
    if paths.is_empty() {
        return Err(IrFileError::EmptyInput);
    }
    if paths.len() > limits.max_files {
        return Err(limit("files"));
    }
    let mut ordered = BTreeSet::new();
    for path in paths {
        if !ordered.insert(path) {
            return Err(IrFileError::DuplicateInput(path.clone()));
        }
    }
    let mut modules: Vec<IrModule> = Vec::new();
    let mut labels = Vec::new();
    let mut input_bytes = 0u64;
    let mut payload_bytes = 0usize;
    let mut declarations = 0usize;
    let wanted = Name::from_components(crate::ir_format::DECL_MAP_EXTENSION.split('.'));
    for path in ordered {
        let bytes = read_file(
            path,
            limits.max_file_bytes.min(limits.max_total_bytes - input_bytes),
        )?;
        input_bytes += bytes.len() as u64;
        let container_error = |source| IrFileError::Container {
            path: path.clone(),
            source,
        };
        let view = OleanView::parse(&bytes).map_err(container_error)?;
        let remaining = limits.max_payload_bytes - payload_bytes;
        let blocks = view
            .extension_payloads(WalkBudget::default(), remaining.min(limits.decode.max_bytes))
            .map_err(container_error)?;
        // decode_ir intentionally accepts an absent IR block as empty. A file
        // validation command must not call an unrelated .olean a checked IR file.
        if !blocks.iter().any(|block| block.name == wanted) {
            return Err(IrFileError::MissingIrBlock(path.clone()));
        }
        for block in &blocks {
            for entry in &block.entries {
                payload_bytes = payload_bytes
                    .checked_add(entry.len())
                    .filter(|n| *n <= limits.max_payload_bytes)
                    .ok_or_else(|| limit("captured payload bytes"))?;
            }
        }
        let decode_limits = IrDecodeLimits {
            max_decls: limits
                .decode
                .max_decls
                .min(limits.validation.max_declarations - declarations),
            ..limits.decode
        };
        let module = decode_ir(&blocks, decode_limits).map_err(|source| IrFileError::Decode {
            path: path.clone(),
            source,
        })?;
        declarations += module.decls.len();
        labels.push(format!("{path:?}"));
        modules.push(module);
    }
    let inputs: Vec<_> = labels
        .iter()
        .zip(&modules)
        .map(|(label, module)| (label.as_str(), module))
        .collect();
    let checked = build_validated_ir_call_graph(&inputs, census_externs, limits.validation)
        .map_err(IrFileError::Validation)?;
    let representation = if check_types {
        Some(check_after_structure(&modules, *checked.summary(), limits.validation)
            .map_err(IrFileError::Representation)?)
    } else {
        None
    };
    Ok(CheckedIrFiles {
        checked,
        input_bytes,
        captured_payload_bytes: payload_bytes,
        representation,
    })
}

struct Dot {
    text: String,
    cap: usize,
}

impl Dot {
    fn push(&mut self, text: &str) -> Result<(), IrFileError> {
        self.text
            .len()
            .checked_add(text.len())
            .filter(|n| *n <= self.cap)
            .ok_or_else(|| limit("DOT output bytes"))?;
        // Amortized growth: reserving an exact allocation for every escaped
        // character would make large graph reports needlessly quadratic.
        self.text
            .try_reserve(text.len())
            .map_err(|_| limit("DOT output allocation"))?;
        self.text.push_str(text);
        Ok(())
    }

    fn quote(&mut self, text: &str) -> Result<(), IrFileError> {
        self.push("\"")?;
        for c in text.chars() {
            match c {
                '"' => self.push("\\\"")?,
                '\\' => self.push("\\\\")?,
                '\n' => self.push("\\n")?,
                '\r' => self.push("\\r")?,
                '\t' => self.push("\\t")?,
                c if c.is_control() => self.push(&format!("<U+{:04X}>", u32::from(c)))?,
                c => self.push(c.encode_utf8(&mut [0; 4]))?,
            }
        }
        self.push("\"")
    }
}

/// Export the validated static graph as bounded DOT diagnostic text. Dense IDs
/// follow structural Name order (not input order or Display spelling), so two
/// distinct names with the same printed spelling never collapse into one node.
/// Module paths are omitted; this is not a hashed/census-classified artifact.
/// No partial output is returned if the byte cap is exceeded.
pub fn ir_graph_dot(
    checked: &ValidatedIrCallGraph,
    max_bytes: usize,
) -> Result<String, IrFileError> {
    let graph = checked.graph();
    let count = u32::try_from(graph.len()).map_err(|_| limit("DOT nodes"))?;
    if graph.len() > max_bytes {
        return Err(limit("DOT output bytes"));
    }
    let mut ids = Vec::new();
    ids.try_reserve_exact(graph.len())
        .map_err(|_| limit("DOT index allocation"))?;
    ids.extend(0..count);
    ids.sort_unstable_by(|a, b| graph.name(*a).cmp(graph.name(*b)));
    let mut remap = Vec::new();
    remap.try_reserve_exact(graph.len())
        .map_err(|_| limit("DOT index allocation"))?;
    remap.resize(graph.len(), 0);
    for (rank, id) in ids.iter().enumerate() {
        remap[*id as usize] = rank;
    }
    let mut out = Dot {
        text: String::new(),
        cap: max_bytes,
    };
    out.push("digraph IR {\n  // Structural validation only; closure-value calls have no static edge.\n")?;
    out.push(&format!(
        "  graph [fln_dynamic_calls=\"{}\"];\n",
        checked.summary().dynamic_calls,
    ))?;
    for id in ids {
        let rank = remap[id as usize];
        out.push(&format!("  n{rank} [label="))?;
        out.quote(&graph.name(id).to_display_string())?;
        let kind = match graph.kind(id) {
            IrNodeKind::Function => "function",
            IrNodeKind::Extern => "extern",
            IrNodeKind::Undeclared => "signature-only",
        };
        out.push(&format!(", fln_kind=\"{kind}\"];\n"))?;
        let mut targets = Vec::new();
        targets.try_reserve_exact(graph.callees(id).len())
            .map_err(|_| limit("DOT edge allocation"))?;
        targets.extend(graph.callees(id).iter().map(|target| remap[*target as usize]));
        targets.sort_unstable();
        for target in targets {
            out.push(&format!("  n{rank} -> n{target};\n"))?;
        }
    }
    out.push("}\n")?;
    Ok(out.text)
}

#[cfg(test)]
mod type_tests;
