//! Execute an explicitly selected closure of Reference-produced library/user IR
//! on Golem (D-24). Toolchain API bodies are never interpreted.
//!
//! The input remains untrusted: selection, IR validation, FIR validation and
//! FLBC's independent ownership pass all precede execution. The supported
//! slice includes calls, closures, acyclic join points, immutable constructors,
//! packed scalar fields and checked native reference-cell operations.
//! Reference cells retain State effects; host I/O and runtime-global effects
//! remain refused. Equivalent object updates use fresh construction.
//! Other mutation, reset/reuse and observable reference counts are refused.
//! Its RC annotations are replaced by Golem's checked managed ownership, not
//! executed as additional retains/releases on already managed values.
//!
//! This does not admit kernel declarations, run import initializers or replace
//! the sovereign compiler. Every linked interpreted function retains Reference
//! provenance in the compiled object and its execution report.

use fln_comp::{fir, flbc};
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_hash::ir_graph::{GraphArchiveLimits, GraphClass};
pub use fln_olean::ir::IrNat;
use fln_olean::ir::{IrBody, IrDecl, IrModule, IrStmt, IrTerminal, IrType};
use fln_olean::ir_archive::CensusPartition;
use fln_olean::ir_types::{IrTypeValidationError, validate_ir_types};
use fln_olean::ir_validate::IrValidationLimits;
use fln_vm::extern_row::{self, Ownership};
use fln_vm::extern_table_generated::{EXTERN_ROWS, GeneratedExternRow};
use fln_vm::interpreter::{CancellationProbe, ExecutionLimits, VmExit};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

mod constructor_updates;
mod lower;
mod native_effects;
mod native_signature;
mod sha256;

/// A census whose complete bytes match the checked-in pinned publication.
/// Constructing the graph reader's annotation-only `CensusPartition` cannot
/// construct this execution policy.
#[derive(Debug)]
pub struct VerifiedPartition {
    partition: CensusPartition,
}

impl VerifiedPartition {
    pub fn from_pinned_tsv(text: &str) -> Result<Self, IrExecutionError> {
        let limits = GraphArchiveLimits::default();
        if text.len() > limits.max_bytes {
            return Err(IrExecutionError::Limit("partition bytes"));
        }
        let envelope = include_str!("../../../contracts/EXTERN_BUILTIN_ENVIRONMENT.txt");
        let expected = envelope
            .lines()
            .find_map(|line| line.strip_prefix("builtin-partition-sha256\t"))
            .ok_or(IrExecutionError::PartitionDigest)?;
        if sha256::hex_digest(text.as_bytes()) != expected {
            return Err(IrExecutionError::PartitionDigest);
        }
        let partition = CensusPartition::parse(text, limits)
            .map_err(|error| IrExecutionError::Partition(error.to_string()))?;
        Ok(Self { partition })
    }

    pub fn classify(&self, name: &Name) -> Option<GraphClass> {
        self.partition.get(name)
    }
}

/// Values supplied to the zero-argument bytecode entry wrapper. Functions in
/// different input modules share one linked code table and closure identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EntryArgument {
    Nat(IrNat),
    String(String),
    /// IEEE-754 binary64 bits, including signed zero and NaN payloads.
    FloatBits(u64),
    /// IEEE-754 binary32 bits, including signed zero and NaN payloads.
    Float32Bits(u32),
    Erased,
}

/// Explicit resource ceilings for selection, lowering and validation.
#[derive(Clone, Copy, Debug)]
pub struct IrExecutionLimits {
    pub ir: IrValidationLimits,
    pub fir: fir::ValidationLimits,
    pub ownership: flbc::OwnershipLimits,
}

impl Default for IrExecutionLimits {
    fn default() -> Self {
        Self {
            ir: IrValidationLimits {
                max_declarations: 1 << 20,
                max_work: 8_000_000,
                max_depth: 128,
            },
            fir: fir::ValidationLimits::default(),
            ownership: flbc::OwnershipLimits::default(),
        }
    }
}

#[derive(Debug)]
pub enum IrExecutionError {
    PartitionDigest,
    Partition(String),
    DuplicateDeclaration(Name),
    MissingDeclaration(Name),
    ToolchainApi(Name),
    Unclassified(Name),
    UserOverridesCensus(Name),
    UnknownUser(Name),
    Unsupported {
        declaration: Name,
        form: &'static str,
    },
    NativeContract {
        declaration: Name,
        detail: String,
    },
    EntryArity {
        expected: usize,
        actual: usize,
    },
    Limit(&'static str),
    IrValidation(IrTypeValidationError),
    FirValidation(fir::ValidationError),
    Lowering(fir::LoweringError),
}

impl fmt::Display for IrExecutionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PartitionDigest => {
                f.write_str("IR execution requires the exact pinned census partition")
            }
            Self::Partition(detail) => write!(f, "IR execution census: {detail}"),
            Self::DuplicateDeclaration(name) => write!(
                f,
                "IR execution: duplicate declaration {}",
                name.to_display_string()
            ),
            Self::MissingDeclaration(name) => write!(
                f,
                "IR execution: missing declaration {}",
                name.to_display_string()
            ),
            Self::ToolchainApi(name) => write!(
                f,
                "IR execution refuses toolchain API body {}; a native implementation is required",
                name.to_display_string()
            ),
            Self::Unclassified(name) => write!(
                f,
                "IR execution refuses unclassified declaration {}",
                name.to_display_string()
            ),
            Self::UserOverridesCensus(name) => write!(
                f,
                "IR user classification cannot override the census for {}",
                name.to_display_string()
            ),
            Self::UnknownUser(name) => write!(
                f,
                "IR user declaration {} is absent from the supplied modules",
                name.to_display_string()
            ),
            Self::Unsupported { declaration, form } => write!(
                f,
                "IR execution: {}: unsupported {form}",
                declaration.to_display_string()
            ),
            Self::NativeContract {
                declaration,
                detail,
            } => write!(
                f,
                "IR native contract for {}: {detail}",
                declaration.to_display_string()
            ),
            Self::EntryArity { expected, actual } => write!(
                f,
                "IR entry expects {expected} arguments, received {actual}"
            ),
            Self::Limit(resource) => write!(f, "IR execution preparation exhausted {resource}"),
            Self::IrValidation(error) => write!(f, "{error}"),
            Self::FirValidation(error) => write!(f, "{error}"),
            Self::Lowering(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for IrExecutionError {}

impl IrExecutionError {
    /// Resource stops remain inconclusive at every validation layer.
    pub fn is_resource(&self) -> bool {
        match self {
            Self::Limit(_) => true,
            Self::IrValidation(error) => error.is_resource(),
            Self::FirValidation(error) => error.is_resource_exhaustion(),
            Self::Lowering(error) => error.is_resource_exhaustion(),
            _ => false,
        }
    }
}

/// Provenance is attached to each linked interpreted function. This is the
/// conservative linked set, not a claim that every function ran on every branch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceFunction {
    pub name: Name,
    pub function: flbc::FunctionId,
}

impl ReferenceFunction {
    pub const fn producer(&self) -> &'static str {
        "reference"
    }
}

#[derive(Debug)]
pub struct CompiledIr {
    program: flbc::OwnershipProgram,
    reference_functions: Vec<ReferenceFunction>,
    native_externs: Vec<String>,
}

/// The execution result and the producer identities of its linked code.
#[derive(Debug)]
pub struct IrExecution {
    pub outcome: Outcome<VmExit>,
    pub reference_functions: Vec<ReferenceFunction>,
    pub native_externs: Vec<String>,
}

impl CompiledIr {
    pub fn reference_functions(&self) -> &[ReferenceFunction] {
        &self.reference_functions
    }

    pub fn native_externs(&self) -> &[String] {
        &self.native_externs
    }

    pub fn execute(
        &self,
        limits: ExecutionLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> IrExecution {
        IrExecution {
            outcome: fln_vm::interpreter::execute(self.program.program(), limits, cancellation),
            reference_functions: self.reference_functions.clone(),
            native_externs: self.native_externs.clone(),
        }
    }
}

pub(super) fn unsupported(name: &Name, form: &'static str) -> IrExecutionError {
    IrExecutionError::Unsupported {
        declaration: name.clone(),
        form,
    }
}

fn native_row(name: &Name) -> Option<&'static GeneratedExternRow> {
    // Compare the structural Name, not its ambiguous dotted pretty printer.
    EXTERN_ROWS
        .iter()
        .find(|row| Name::from_components(row.name.split('.')) == *name)
}

fn classified_ancestor(partition: &VerifiedPartition, name: &Name) -> Option<GraphClass> {
    let mut current = name.clone();
    loop {
        if let Some(class) = partition.classify(&current) {
            return Some(class);
        }
        let parent = current.parent();
        if parent == current {
            return None;
        }
        current = parent;
    }
}

fn authorize(
    partition: &VerifiedPartition,
    users: &BTreeSet<Name>,
    name: &Name,
) -> Result<(), IrExecutionError> {
    match partition.classify(name) {
        Some(GraphClass::ToolchainApi) => Err(IrExecutionError::ToolchainApi(name.clone())),
        Some(GraphClass::LibraryCode | GraphClass::Data) => Ok(()),
        _ if classified_ancestor(partition, name) == Some(GraphClass::ToolchainApi) => {
            Err(IrExecutionError::ToolchainApi(name.clone()))
        }
        None if users.contains(name) => Ok(()),
        _ => Err(IrExecutionError::Unclassified(name.clone())),
    }
}

/// Compile only the statically reachable closure rooted at `entry`.
///
/// The partition is cryptographically pinned; `user_declarations` names actual
/// user code in the supplied modules and cannot reclassify a census name or a
/// compiler-generated descendant of one. Unknown imported library names remain
/// a refusal. Native census rows always select native implementations, even if
/// an input module also contains a body with that name.
pub fn compile(
    modules: &[IrModule],
    entry: &Name,
    arguments: &[EntryArgument],
    partition: &VerifiedPartition,
    user_declarations: &BTreeSet<Name>,
    limits: IrExecutionLimits,
) -> Result<CompiledIr, IrExecutionError> {
    let count = modules
        .iter()
        .try_fold(0usize, |n, m| n.checked_add(m.decls.len()))
        .ok_or(IrExecutionError::Limit("input declarations"))?;
    if count > limits.ir.max_declarations || user_declarations.len() > limits.ir.max_declarations {
        return Err(IrExecutionError::Limit("input declarations"));
    }
    if arguments.len() > limits.fir.max_operands {
        return Err(IrExecutionError::Limit("entry arguments"));
    }
    let literal_bytes = arguments
        .iter()
        .try_fold(0usize, |sum, argument| {
            let bytes = match argument {
                EntryArgument::Nat(IrNat::Big(limbs)) => limbs.len().checked_mul(8)?,
                EntryArgument::String(text) => text.len(),
                EntryArgument::FloatBits(_) => 8,
                EntryArgument::Float32Bits(_) => 4,
                _ => 0,
            };
            sum.checked_add(bytes)
        })
        .ok_or(IrExecutionError::Limit("entry literal bytes"))?;
    if literal_bytes > limits.fir.max_literal_bytes {
        return Err(IrExecutionError::Limit("entry literal bytes"));
    }
    let mut declarations = BTreeMap::new();
    for declaration in modules.iter().flat_map(|module| &module.decls) {
        if declarations
            .insert(declaration.name().clone(), declaration)
            .is_some()
        {
            return Err(IrExecutionError::DuplicateDeclaration(
                declaration.name().clone(),
            ));
        }
    }
    for name in user_declarations {
        if native_row(name).is_some() || classified_ancestor(partition, name).is_some() {
            return Err(IrExecutionError::UserOverridesCensus(name.clone()));
        }
        if !declarations.contains_key(name) {
            return Err(IrExecutionError::UnknownUser(name.clone()));
        }
    }
    let mut pending = BTreeSet::from([entry.clone()]);
    let mut selected = BTreeMap::new();
    let mut natives = BTreeMap::new();
    let mut work = 0u64;
    while let Some(name) = pending.pop_first() {
        if selected.contains_key(&name) || natives.contains_key(&name) {
            continue;
        }
        if selected.len().saturating_add(natives.len()) >= limits.fir.max_functions {
            return Err(IrExecutionError::Limit("selected functions"));
        }
        if let Some(row) = native_row(&name) {
            let arity = match declarations.get(&name) {
                Some(IrDecl::Extern { params, .. }) => params.len(),
                _ => native_signature::inferred_arity(row)?,
            };
            natives.insert(name, Native::new(row, arity)?);
            continue;
        }
        authorize(partition, user_declarations, &name)?;
        let declaration = declarations
            .get(&name)
            .ok_or_else(|| IrExecutionError::MissingDeclaration(name.clone()))?;
        let IrDecl::Function {
            body,
            params,
            result,
            sorry_dep,
            ..
        } = declaration
        else {
            return Err(unsupported(&name, "extern absent from the native census"));
        };
        if sorry_dep.is_some() {
            return Err(unsupported(&name, "sorry-dependent executable"));
        }
        inspect_body(&name, body, &mut work, limits)?;
        for ty in params.iter().map(|p| &p.ty).chain([result]) {
            check_type(&name, ty)?;
        }
        for callee in declaration.callees() {
            pending.insert(callee.clone());
        }
        selected.insert(name, *declaration);
    }
    let mut selected_module = IrModule {
        decls: selected.values().map(|decl| (*decl).clone()).collect(),
        ..IrModule::default()
    };
    let signatures = natives
        .iter()
        .map(|(name, native)| (name.clone(), native.arguments.len()))
        .collect();
    // Validate and authorize the original closure before eliminating anything:
    // even an unchosen allocation branch cannot hide an invalid declaration.
    validate_ir_types(
        std::slice::from_ref(&selected_module),
        &signatures,
        limits.ir,
    )
    .map_err(IrExecutionError::IrValidation)?;
    if constructor_updates::normalize(&mut selected_module, limits)? {
        validate_ir_types(
            std::slice::from_ref(&selected_module),
            &signatures,
            limits.ir,
        )
        .map_err(IrExecutionError::IrValidation)?;
    }
    let selected = selected_module
        .decls
        .iter()
        .map(|declaration| (declaration.name().clone(), declaration))
        .collect();
    lower::compile(&selected, &natives, entry, arguments, limits)
}

fn check_type(name: &Name, ty: &IrType) -> Result<(), IrExecutionError> {
    match ty {
        IrType::Object
        | IrType::TObject
        | IrType::Tagged
        | IrType::Erased
        | IrType::UInt8
        | IrType::UInt16
        | IrType::UInt32
        | IrType::UInt64
        | IrType::Float
        | IrType::Float32
        | IrType::USize => Ok(()),
        _ => Err(unsupported(name, "packed/unboxed IR representation")),
    }
}

fn inspect_body(
    name: &Name,
    body: &IrBody,
    work: &mut u64,
    limits: IrExecutionLimits,
) -> Result<(), IrExecutionError> {
    let mut pending = vec![(body, 1usize)];
    while let Some((body, depth)) = pending.pop() {
        if depth > limits.ir.max_depth.min(128) {
            return Err(IrExecutionError::Limit("IR body depth"));
        }
        *work = work.saturating_add(body.stmts.len() as u64 + 1);
        if *work > limits.ir.max_work {
            return Err(IrExecutionError::Limit("IR selection work"));
        }
        for stmt in &body.stmts {
            match stmt {
                IrStmt::VDecl { ty, expr, .. } => {
                    check_type(name, ty)?;
                    if matches!(ty, IrType::Float | IrType::Float32) {
                        match expr {
                            fln_olean::ir::IrExpr::Lit(fln_olean::ir::IrLit::Num(_)) => {
                                return Err(unsupported(name, "floating numeric literal"));
                            }
                            fln_olean::ir::IrExpr::Ctor { .. } => {
                                return Err(unsupported(name, "floating constructor"));
                            }
                            _ => {}
                        }
                    }
                    if let fln_olean::ir::IrExpr::Box { ty, .. } = expr {
                        check_type(name, ty)?;
                    }
                }
                IrStmt::JDecl { params, value, .. } => {
                    *work = work.saturating_add(params.len() as u64);
                    if *work > limits.ir.max_work {
                        return Err(IrExecutionError::Limit("IR selection work"));
                    }
                    for param in params {
                        check_type(name, &param.ty)?;
                    }
                    pending.push((value, depth + 1));
                }
                IrStmt::Inc { .. } | IrStmt::Dec { .. } | IrStmt::Del { .. } => {}
                // Lowering admits these only while filling a fresh, unread
                // constructor. The IR never acquires a mutable runtime handle.
                IrStmt::USet { .. } => {}
                IrStmt::SSet { ty, .. } => check_type(name, ty)?,
                // These reach lowering only if a bounded equivalence check
                // can replace the entire update region with fresh construction.
                // Any remaining mutation is still refused by the lowerer.
                IrStmt::Set { .. } | IrStmt::SetTag { .. } => {}
            }
        }
        if let IrTerminal::Case { alts, x_type, .. } = body.terminal.as_ref() {
            check_type(name, x_type)?;
            if matches!(x_type, IrType::Float | IrType::Float32) {
                return Err(unsupported(name, "floating constructor case"));
            }
            if alts.len() > limits.ir.max_depth.min(128) {
                return Err(IrExecutionError::Limit("case alternatives"));
            }
            for alt in alts {
                let child = match alt {
                    fln_olean::ir::IrAlt::Ctor { body, .. }
                    | fln_olean::ir::IrAlt::Default { body } => body,
                };
                pending.push((child, depth + 1));
            }
        }
    }
    Ok(())
}

struct Native {
    row: &'static GeneratedExternRow,
    arguments: Vec<flbc::ArgumentOwnership>,
    result: flbc::ResultOwnership,
    effect: fir::EffectClass,
}

impl Native {
    fn new(row: &'static GeneratedExternRow, arity: usize) -> Result<Self, IrExecutionError> {
        let name = Name::from_components(row.name.split('.'));
        let effect = native_effects::classify(row)?;
        if matches!(
            row.id,
            "extern:isExclusiveUnsafe" | "extern:dbgTraceIfShared" | "extern:ptrAddrUnsafe"
        ) {
            return Err(unsupported(
                &name,
                "native allocation or reference-count observation",
            ));
        }
        let error = |error: extern_row::ContractError| IrExecutionError::NativeContract {
            declaration: name.clone(),
            detail: error.to_string(),
        };
        let contract = Ownership::parse(row.ownership).map_err(error)?;
        // Explicit extern declarations and absent declarations use the same
        // runtime authority. Rule-only rows retain census arity unless a
        // reviewed native bridge binds their erased executable telescope.
        if arity != native_signature::inferred_arity(row)? {
            return Err(IrExecutionError::NativeContract {
                declaration: name.clone(),
                detail: "extern arity differs from the reviewed runtime signature".to_owned(),
            });
        }
        let arguments = contract
            .argument_ownership(arity)
            .map_err(error)?
            .into_iter()
            .map(|o| match o {
                extern_row::ArgumentOwnership::Owned => flbc::ArgumentOwnership::Owned,
                extern_row::ArgumentOwnership::Borrowed => flbc::ArgumentOwnership::Borrowed,
                extern_row::ArgumentOwnership::Unique => flbc::ArgumentOwnership::Unique,
                extern_row::ArgumentOwnership::Scalar => flbc::ArgumentOwnership::Scalar,
            })
            .collect();
        let result = match contract.result_ownership().map_err(error)? {
            extern_row::ResultOwnership::Owned => flbc::ResultOwnership::Owned,
            extern_row::ResultOwnership::Borrowed => flbc::ResultOwnership::Borrowed,
            extern_row::ResultOwnership::Scalar => flbc::ResultOwnership::Scalar,
            extern_row::ResultOwnership::RawObject => flbc::ResultOwnership::RawObject,
        };
        Ok(Self {
            row,
            arguments,
            result,
            effect,
        })
    }
}

#[cfg(test)]
mod tests;
