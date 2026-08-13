//! Versioned FLBC schema, canonical artifact codec, and whole-program validator
//! for the G0-3 prototype.
//!
//! This is the target-independent boundary between the prototype compiler and
//! Golem. [`decode_canonical`] enforces bounded framing before allocation and
//! returns only [`ValidatedProgram`], so register bounds, control-flow targets,
//! direct-call arities, constructor limits, and definite register
//! initialization are established before a Marrow object is touched. The later
//! W5 pipeline will add FIR provenance and stage witnesses; this module does not
//! claim those blocked production surfaces.

use fln_rt::abi;
use std::collections::VecDeque;
use std::fmt;

/// The only FLBC schema this build understands.
///
/// Version 3 adds checked constructor-field projection; version 4 binds every
/// intrinsic operand to its generated ABI ownership disposition; version 5
/// binds function parameters and direct-call operands to one ownership
/// contract; version 6 binds closure captures to the target parameter prefix;
/// version 7 binds explicit dynamic-application arguments; version 8 binds the
/// generated result ownership class of every intrinsic; version 9 binds the
/// Owned-or-Scalar result contract of every callable function and invocation;
/// version 10 makes each native `Lean.Core.checkSystem` observation point an
/// explicit artifact instruction carrying its diagnostic module name; version
/// 11 also admits a validated register operand for computed module names.
pub const FLBC_SCHEMA_VERSION: u16 = 11;

/// Canonical binary envelope version for persisted FLBC artifacts.
///
/// This is independent of [`FLBC_SCHEMA_VERSION`]: the envelope freezes byte
/// framing and opcode numbers, while the embedded schema version freezes the
/// program model accepted by [`validate`].
pub const FLBC_WIRE_VERSION: u16 = 7;

/// Canonical witness schema for the bounded ownership pass.
///
/// Version 2 adds acyclic-CFG insertion modes and explicit edge-block counts;
/// version 3 adds cyclic fixed-point insertion; version 4 binds inferred
/// last-use moves per function; version 5 distinguishes and counts admitted
/// straight-line register redefinitions; version 6 validates and counts
/// pre-existing ownership instructions; version 7 admits non-overlapping
/// acyclic CFG register reuse and binds its redefinition count; version 8 binds
/// the exact number of owned or unique extern operands consumed; version 9
/// separately binds owned or unique direct-call operands; version 10 binds
/// owned closure captures independently; version 11 binds dynamic Apply
/// consumes; version 12 binds borrowed-result promotions and raw-object
/// intrinsic results; version 13 binds function, direct-call, and dynamic-Apply
/// result ownership plus exact owned/scalar invocation counts; version 14
/// admits cyclic CFG register reuse and binds its redefinition count.
pub const OWNERSHIP_WITNESS_VERSION: u16 = 14;

const FLBC_MAGIC: [u8; 8] = *b"FLNFLBC\0";

const OP_NAT: u8 = 0;
const OP_STRING: u8 = 1;
const OP_COPY: u8 = 2;
const OP_MOVE: u8 = 3;
const OP_DROP: u8 = 4;
const OP_CTOR: u8 = 5;
const OP_ARRAY: u8 = 6;
const OP_INTRINSIC: u8 = 7;
const OP_CALL: u8 = 8;
const OP_CLOSURE: u8 = 9;
const OP_APPLY: u8 = 10;
const OP_JUMP: u8 = 11;
const OP_JUMP_IF_ZERO: u8 = 12;
const OP_RETURN: u8 = 13;
const OP_PANIC: u8 = 14;
const OP_CTOR_FIELD: u8 = 15;
const OP_CHECK_SYSTEM: u8 = 16;
const OP_CHECK_SYSTEM_VALUE: u8 = 17;

/// Explicit allocation and work ceilings for canonical FLBC artifacts.
///
/// A decoder checks these counts before allocating their corresponding table
/// or literal. Exceeding a ceiling is a typed resource stop, not a malformed
/// program verdict.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CodecLimits {
    pub max_artifact_bytes: usize,
    pub max_functions: usize,
    pub max_instructions: usize,
    pub max_operands: usize,
    pub max_literal_bytes: usize,
}

impl Default for CodecLimits {
    fn default() -> Self {
        Self {
            max_artifact_bytes: 64 * 1024 * 1024,
            max_functions: 65_536,
            max_instructions: 1_000_000,
            max_operands: 8_000_000,
            max_literal_bytes: 32 * 1024 * 1024,
        }
    }
}

/// Resource dimension named by a canonical codec stop.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CodecResource {
    ArtifactBytes,
    Functions,
    Instructions,
    Operands,
    LiteralBytes,
}

/// Typed canonical-codec refusal. No variant carries a partially validated
/// program, and [`decode_canonical`] returns an executable wrapper only after
/// the ordinary whole-program validator succeeds.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CodecError {
    ResourceLimit {
        resource: CodecResource,
        limit: usize,
        observed: usize,
    },
    LengthOverflow {
        field: &'static str,
        len: usize,
    },
    AllocationFailure {
        resource: CodecResource,
        requested: usize,
    },
    Truncated {
        offset: usize,
        needed: usize,
        remaining: usize,
    },
    BadMagic,
    UnsupportedWireVersion {
        seen: u16,
    },
    InvalidUtf8 {
        field: &'static str,
        offset: usize,
    },
    UnknownOpcode {
        opcode: u8,
        offset: usize,
    },
    InvalidArgumentOwnership {
        tag: u8,
        offset: usize,
    },
    InvalidResultOwnership {
        tag: u8,
        offset: usize,
    },
    InvalidCallableResultOwnership {
        tag: u8,
        offset: usize,
    },
    TrailingBytes {
        offset: usize,
        remaining: usize,
    },
    Validation(ValidationError),
}

impl fmt::Display for CodecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ResourceLimit {
                resource,
                limit,
                observed,
            } => write!(
                f,
                "FLBC codec resource {resource:?} observed {observed}, limit {limit}"
            ),
            Self::LengthOverflow { field, len } => {
                write!(f, "FLBC {field} length {len} does not fit u32 framing")
            }
            Self::AllocationFailure {
                resource,
                requested,
            } => write!(
                f,
                "FLBC codec could not reserve {requested} units for {resource:?}"
            ),
            Self::Truncated {
                offset,
                needed,
                remaining,
            } => write!(
                f,
                "FLBC artifact ends at offset {offset}: need {needed} bytes, have {remaining}"
            ),
            Self::BadMagic => write!(f, "FLBC artifact magic mismatch"),
            Self::UnsupportedWireVersion { seen } => {
                write!(f, "unsupported FLBC wire version {seen}")
            }
            Self::InvalidUtf8 { field, offset } => {
                write!(f, "FLBC {field} at offset {offset} is not UTF-8")
            }
            Self::UnknownOpcode { opcode, offset } => {
                write!(f, "unknown FLBC opcode {opcode} at offset {offset}")
            }
            Self::InvalidArgumentOwnership { tag, offset } => write!(
                f,
                "unknown FLBC argument ownership tag {tag} at offset {offset}"
            ),
            Self::InvalidResultOwnership { tag, offset } => write!(
                f,
                "unknown FLBC result ownership tag {tag} at offset {offset}"
            ),
            Self::InvalidCallableResultOwnership { tag, offset } => write!(
                f,
                "unknown FLBC callable result ownership tag {tag} at offset {offset}"
            ),
            Self::TrailingBytes { offset, remaining } => write!(
                f,
                "FLBC artifact has {remaining} trailing bytes after offset {offset}"
            ),
            Self::Validation(error) => write!(f, "decoded FLBC failed validation: {error}"),
        }
    }
}

impl std::error::Error for CodecError {}

impl CodecError {
    /// Whether this refusal is a budget or allocation failure, not a
    /// malformed-artifact refusal.
    pub fn is_resource_exhaustion(&self) -> bool {
        matches!(
            self,
            Self::ResourceLimit { .. } | Self::AllocationFailure { .. }
        )
    }
}

/// A function-table index.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FunctionId(u32);

impl FunctionId {
    pub const fn new(raw: u32) -> Self {
        Self(raw)
    }

    pub const fn get(self) -> u32 {
        self.0
    }

    fn index(self) -> Option<usize> {
        usize::try_from(self.0).ok()
    }
}

/// A frame-local register index.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Register(u16);

impl Register {
    pub const fn new(raw: u16) -> Self {
        Self(raw)
    }

    pub const fn get(self) -> u16 {
        self.0
    }

    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// A function-local instruction offset.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Pc(u32);

impl Pc {
    pub const fn new(raw: u32) -> Self {
        Self(raw)
    }

    pub const fn get(self) -> u32 {
        self.0
    }

    fn index(self) -> Option<usize> {
        usize::try_from(self.0).ok()
    }
}

/// Ownership disposition of one ABI argument.
///
/// `Owned` and `Unique` transfer the register's owned handle across the
/// intrinsic boundary. `Borrowed` and `Scalar` leave the register live and
/// supply a retained runtime handle. `Unique` additionally forbids using the
/// same register in any other operand of that instruction; alias-sensitive
/// heap uniqueness is a later compiler obligation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ArgumentOwnership {
    Borrowed,
    Owned,
    Unique,
    Scalar,
}

impl ArgumentOwnership {
    pub const fn token(self) -> &'static str {
        match self {
            Self::Borrowed => "borrowed",
            Self::Owned => "owned",
            Self::Unique => "unique",
            Self::Scalar => "scalar",
        }
    }

    pub const fn consumes(self) -> bool {
        matches!(self, Self::Owned | Self::Unique)
    }

    const fn wire_tag(self) -> u8 {
        match self {
            Self::Borrowed => 0,
            Self::Owned => 1,
            Self::Unique => 2,
            Self::Scalar => 3,
        }
    }

    fn from_wire_tag(tag: u8, offset: usize) -> Result<Self, CodecError> {
        match tag {
            0 => Ok(Self::Borrowed),
            1 => Ok(Self::Owned),
            2 => Ok(Self::Unique),
            3 => Ok(Self::Scalar),
            _ => Err(CodecError::InvalidArgumentOwnership { tag, offset }),
        }
    }
}

/// Ownership class of one intrinsic result.
///
/// Every class still produces one register-owned [`fln_rt::obj::Obj`] inside
/// Golem. `Borrowed` requires the row implementation to promote a reviewed
/// borrowed source before that source can die. `Scalar` requires a tagged
/// immediate. `RawObject` records that the generated C signature does not
/// itself state ownership; it is executable only through a row-specific native
/// implementation that returns an internally owned object.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ResultOwnership {
    Owned,
    Borrowed,
    Scalar,
    RawObject,
}

impl ResultOwnership {
    pub const fn token(self) -> &'static str {
        match self {
            Self::Owned => "owned",
            Self::Borrowed => "borrowed",
            Self::Scalar => "scalar",
            Self::RawObject => "raw-object",
        }
    }

    const fn wire_tag(self) -> u8 {
        match self {
            Self::Owned => 0,
            Self::Borrowed => 1,
            Self::Scalar => 2,
            Self::RawObject => 3,
        }
    }

    fn from_wire_tag(tag: u8, offset: usize) -> Result<Self, CodecError> {
        match tag {
            0 => Ok(Self::Owned),
            1 => Ok(Self::Borrowed),
            2 => Ok(Self::Scalar),
            3 => Ok(Self::RawObject),
            _ => Err(CodecError::InvalidResultOwnership { tag, offset }),
        }
    }
}

/// Ownership class of one target-independent callable result.
///
/// A completed function always transfers one register-owned [`fln_rt::obj::Obj`]
/// to its continuation. `Owned` requires a heap object; `Scalar` requires a
/// tagged immediate. Borrowed and unique callable results are deliberately not
/// representable in this bounded schema.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CallableResultOwnership {
    Owned,
    Scalar,
}

impl CallableResultOwnership {
    pub const fn token(self) -> &'static str {
        match self {
            Self::Owned => "owned",
            Self::Scalar => "scalar",
        }
    }

    const fn wire_tag(self) -> u8 {
        match self {
            Self::Owned => 0,
            Self::Scalar => 1,
        }
    }

    fn from_wire_tag(tag: u8, offset: usize) -> Result<Self, CodecError> {
        match tag {
            0 => Ok(Self::Owned),
            1 => Ok(Self::Scalar),
            _ => Err(CodecError::InvalidCallableResultOwnership { tag, offset }),
        }
    }
}

/// Target-independent register bytecode.
///
/// Every operand is an ABI-valued register at runtime. `Copy` retains an
/// object, `Move` transfers the owned handle and empties the source, and
/// `Drop` releases it. Aggregate operands are borrowed. Intrinsic and
/// direct-call operands carry their checked ownership disposition explicitly.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Instruction {
    Nat {
        dst: Register,
        value: u64,
    },
    String {
        dst: Register,
        value: String,
    },
    Copy {
        dst: Register,
        src: Register,
    },
    Move {
        dst: Register,
        src: Register,
    },
    Drop {
        src: Register,
    },
    Ctor {
        dst: Register,
        tag: u8,
        fields: Vec<Register>,
        scalar_bytes: Vec<u8>,
    },
    /// Read one constructor object field after checking its complete runtime
    /// object-slot shape. Validation guarantees `field < expected_fields`.
    CtorField {
        dst: Register,
        src: Register,
        expected_tag: u8,
        expected_fields: u16,
        field: u16,
    },
    Array {
        dst: Register,
        items: Vec<Register>,
    },
    Intrinsic {
        dst: Register,
        row: String,
        args: Vec<Register>,
        argument_ownership: Vec<ArgumentOwnership>,
        result_ownership: ResultOwnership,
    },
    Call {
        dst: Register,
        function: FunctionId,
        args: Vec<Register>,
        argument_ownership: Vec<ArgumentOwnership>,
        result_ownership: CallableResultOwnership,
    },
    /// Build a closure over the leading parameters of `function`. At least
    /// one parameter must remain open for later application.
    Closure {
        dst: Register,
        function: FunctionId,
        captures: Vec<Register>,
        capture_ownership: Vec<ArgumentOwnership>,
    },
    /// Apply one or more explicitly owned arguments. Under-application returns
    /// a new closure; exact application calls the target; over-application
    /// applies the remainder to the value returned by that call.
    Apply {
        dst: Register,
        closure: Register,
        args: Vec<Register>,
        argument_ownership: Vec<ArgumentOwnership>,
        result_ownership: CallableResultOwnership,
    },
    Jump {
        target: Pc,
    },
    JumpIfZero {
        cond: Register,
        zero: Pc,
        nonzero: Pc,
    },
    /// Native Mirror lowering of `Lean.Core.checkSystem`. The module name is
    /// diagnostic context; Golem samples cancellation and the command's
    /// allocation-heartbeat delta at this exact instruction.
    CheckSystem {
        module_name: String,
    },
    /// Dynamic form of [`Self::CheckSystem`] for a module name computed by the
    /// source program. The register is borrowed and must contain a `String`.
    CheckSystemValue {
        module_name: Register,
    },
    Return {
        src: Register,
    },
    Panic {
        message: Register,
    },
}

impl Instruction {
    fn read_registers(&self) -> Vec<Register> {
        match self {
            Self::Nat { .. }
            | Self::String { .. }
            | Self::Jump { .. }
            | Self::CheckSystem { .. } => Vec::new(),
            Self::Copy { src, .. }
            | Self::Move { src, .. }
            | Self::Drop { src }
            | Self::CtorField { src, .. }
            | Self::CheckSystemValue { module_name: src } => {
                vec![*src]
            }
            Self::Ctor { fields, .. } => fields.clone(),
            Self::Array { items, .. } => items.clone(),
            Self::Intrinsic { args, .. } | Self::Call { args, .. } => args.clone(),
            Self::Closure { captures, .. } => captures.clone(),
            Self::Apply { closure, args, .. } => {
                let mut reads = Vec::with_capacity(args.len() + 1);
                reads.push(*closure);
                reads.extend_from_slice(args);
                reads
            }
            Self::JumpIfZero { cond, .. } => vec![*cond],
            Self::Return { src } => vec![*src],
            Self::Panic { message } => vec![*message],
        }
    }

    fn written_register(&self) -> Option<Register> {
        match self {
            Self::Nat { dst, .. }
            | Self::String { dst, .. }
            | Self::Copy { dst, .. }
            | Self::Move { dst, .. }
            | Self::Ctor { dst, .. }
            | Self::CtorField { dst, .. }
            | Self::Array { dst, .. }
            | Self::Intrinsic { dst, .. }
            | Self::Call { dst, .. }
            | Self::Closure { dst, .. }
            | Self::Apply { dst, .. } => Some(*dst),
            Self::Drop { .. }
            | Self::Jump { .. }
            | Self::JumpIfZero { .. }
            | Self::CheckSystem { .. }
            | Self::CheckSystemValue { .. }
            | Self::Return { .. }
            | Self::Panic { .. } => None,
        }
    }
}

/// One canonical function-table row. Function ids must equal their table
/// indices; this removes an otherwise observable ordering choice.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Function {
    pub id: FunctionId,
    pub arity: u16,
    pub parameter_ownership: Vec<ArgumentOwnership>,
    pub result_ownership: CallableResultOwnership,
    pub register_count: u16,
    pub code: Vec<Instruction>,
}

/// An untrusted FLBC program. Constructing this type does not authorize
/// execution; pass it to [`validate`] to obtain the opaque wrapper.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program {
    pub schema_version: u16,
    pub entry: FunctionId,
    pub functions: Vec<Function>,
}

impl Program {
    pub fn new(entry: FunctionId, functions: Vec<Function>) -> Self {
        Self {
            schema_version: FLBC_SCHEMA_VERSION,
            entry,
            functions,
        }
    }
}

/// A program whose complete instruction graph passed [`validate`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValidatedProgram {
    program: Program,
}

impl ValidatedProgram {
    pub const fn entry(&self) -> FunctionId {
        self.program.entry
    }

    pub fn functions(&self) -> &[Function] {
        &self.program.functions
    }

    pub fn function(&self, id: FunctionId) -> Option<&Function> {
        id.index()
            .and_then(|index| self.program.functions.get(index))
    }

    pub const fn schema_version(&self) -> u16 {
        self.program.schema_version
    }
}

/// Explicit work ceilings for bounded ownership insertion and validation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct OwnershipLimits {
    pub max_functions: usize,
    pub max_source_instructions: usize,
    pub max_emitted_instructions: usize,
    pub max_registers: usize,
    pub max_value_epochs: usize,
    pub max_operands: usize,
    pub max_payload_bytes: usize,
    pub max_cfg_edges: usize,
    pub max_liveness_cells: usize,
    pub max_liveness_steps: usize,
    pub max_validation_cells: usize,
    pub max_validation_steps: usize,
}

impl Default for OwnershipLimits {
    fn default() -> Self {
        Self {
            max_functions: 65_536,
            max_source_instructions: 1_000_000,
            max_emitted_instructions: 2_000_000,
            max_registers: 8_000_000,
            max_value_epochs: 16_000_000,
            max_operands: 8_000_000,
            max_payload_bytes: 64 * 1024 * 1024,
            max_cfg_edges: 2_000_000,
            max_liveness_cells: 16_000_000,
            max_liveness_steps: 64_000_000,
            max_validation_cells: 32_000_000,
            max_validation_steps: 128_000_000,
        }
    }
}

/// Resource dimension named by an ownership-pass stop.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OwnershipResource {
    Functions,
    SourceInstructions,
    EmittedInstructions,
    Registers,
    ValueEpochs,
    Operands,
    PayloadBytes,
    CfgEdges,
    LivenessCells,
    LivenessSteps,
    ValidationCells,
    ValidationSteps,
}

/// Why one function was transformed or preserved byte-for-byte.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OwnershipMode {
    InsertedLinear,
    InsertedLinearReuse,
    InsertedAcyclicCfg,
    InsertedAcyclicCfgReuse,
    InsertedCyclicCfg,
    InsertedCyclicCfgReuse,
    ValidatedExistingOwnership,
    PreservedNonSsa,
}

impl OwnershipMode {
    pub const fn token(self) -> &'static str {
        match self {
            Self::InsertedLinear => "inserted-linear",
            Self::InsertedLinearReuse => "inserted-linear-reuse",
            Self::InsertedAcyclicCfg => "inserted-acyclic-cfg",
            Self::InsertedAcyclicCfgReuse => "inserted-acyclic-cfg-reuse",
            Self::InsertedCyclicCfg => "inserted-cyclic-cfg",
            Self::InsertedCyclicCfgReuse => "inserted-cyclic-cfg-reuse",
            Self::ValidatedExistingOwnership => "validated-existing-ownership",
            Self::PreservedNonSsa => "preserved-non-ssa",
        }
    }
}

/// One function-local row in the canonical ownership witness.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OwnershipFunctionWitness {
    pub function: FunctionId,
    pub mode: OwnershipMode,
    pub result_ownership: CallableResultOwnership,
    pub source_instructions: usize,
    pub emitted_instructions: usize,
    pub inserted_drops: usize,
    pub inferred_moves: usize,
    pub existing_drops: usize,
    pub existing_moves: usize,
    pub redefinitions: usize,
    pub edge_blocks: usize,
    pub consumed_extern_args: usize,
    pub consumed_call_args: usize,
    pub consumed_closure_captures: usize,
    pub consumed_apply_args: usize,
    pub borrowed_intrinsic_results: usize,
    pub raw_intrinsic_results: usize,
    pub owned_callable_results: usize,
    pub scalar_callable_results: usize,
}

/// Deterministic description of an ownership-pass result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OwnershipWitness {
    schema_version: u16,
    functions: Vec<OwnershipFunctionWitness>,
}

impl OwnershipWitness {
    /// Construct an untrusted witness for independent validation.
    pub fn new(schema_version: u16, functions: Vec<OwnershipFunctionWitness>) -> Self {
        Self {
            schema_version,
            functions,
        }
    }

    pub const fn schema_version(&self) -> u16 {
        self.schema_version
    }

    pub fn functions(&self) -> &[OwnershipFunctionWitness] {
        &self.functions
    }

    pub fn canonical_text(&self) -> String {
        let mut output = format!("flbc-ownership/{}\n", self.schema_version);
        for row in &self.functions {
            use std::fmt::Write as _;
            if row.mode == OwnershipMode::ValidatedExistingOwnership {
                let _ = writeln!(
                    output,
                    "function f{} mode={} result={} source={} emitted={} drops={} moves={} existing_drops={} existing_moves={} redefs={} edges={} extern_consumes={} call_consumes={} closure_consumes={} apply_consumes={} borrowed_results={} raw_results={} owned_callable_results={} scalar_callable_results={}",
                    row.function.get(),
                    row.mode.token(),
                    row.result_ownership.token(),
                    row.source_instructions,
                    row.emitted_instructions,
                    row.inserted_drops,
                    row.inferred_moves,
                    row.existing_drops,
                    row.existing_moves,
                    row.redefinitions,
                    row.edge_blocks,
                    row.consumed_extern_args,
                    row.consumed_call_args,
                    row.consumed_closure_captures,
                    row.consumed_apply_args,
                    row.borrowed_intrinsic_results,
                    row.raw_intrinsic_results,
                    row.owned_callable_results,
                    row.scalar_callable_results
                );
            } else {
                let _ = writeln!(
                    output,
                    "function f{} mode={} result={} source={} emitted={} drops={} moves={} redefs={} edges={} extern_consumes={} call_consumes={} closure_consumes={} apply_consumes={} borrowed_results={} raw_results={} owned_callable_results={} scalar_callable_results={}",
                    row.function.get(),
                    row.mode.token(),
                    row.result_ownership.token(),
                    row.source_instructions,
                    row.emitted_instructions,
                    row.inserted_drops,
                    row.inferred_moves,
                    row.redefinitions,
                    row.edge_blocks,
                    row.consumed_extern_args,
                    row.consumed_call_args,
                    row.consumed_closure_captures,
                    row.consumed_apply_args,
                    row.borrowed_intrinsic_results,
                    row.raw_intrinsic_results,
                    row.owned_callable_results,
                    row.scalar_callable_results
                );
            }
        }
        output
    }
}

/// An ordinary validated FLBC program whose ownership insertion was also
/// accepted by the independent source-to-candidate validator.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OwnershipProgram {
    program: ValidatedProgram,
    witness: OwnershipWitness,
}

impl OwnershipProgram {
    pub const fn program(&self) -> &ValidatedProgram {
        &self.program
    }

    pub const fn witness(&self) -> &OwnershipWitness {
        &self.witness
    }

    pub fn into_program(self) -> ValidatedProgram {
        self.program
    }
}

/// The exact witness counter that disagreed with independent validation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OwnershipWitnessCount {
    SourceInstructions,
    EmittedInstructions,
    InsertedDrops,
    InferredMoves,
    ExistingDrops,
    ExistingMoves,
    Redefinitions,
    EdgeBlocks,
    ConsumedExternArgs,
    ConsumedCallArgs,
    ConsumedClosureCaptures,
    ConsumedApplyArgs,
    BorrowedIntrinsicResults,
    RawIntrinsicResults,
    OwnedCallableResults,
    ScalarCallableResults,
}

impl OwnershipWitnessCount {
    const fn token(self) -> &'static str {
        match self {
            Self::SourceInstructions => "source instructions",
            Self::EmittedInstructions => "emitted instructions",
            Self::InsertedDrops => "inserted drops",
            Self::InferredMoves => "inferred moves",
            Self::ExistingDrops => "existing drops",
            Self::ExistingMoves => "existing moves",
            Self::Redefinitions => "redefinitions",
            Self::EdgeBlocks => "edge blocks",
            Self::ConsumedExternArgs => "consumed extern arguments",
            Self::ConsumedCallArgs => "consumed direct-call arguments",
            Self::ConsumedClosureCaptures => "consumed closure captures",
            Self::ConsumedApplyArgs => "consumed Apply arguments",
            Self::BorrowedIntrinsicResults => "borrowed intrinsic results",
            Self::RawIntrinsicResults => "raw intrinsic results",
            Self::OwnedCallableResults => "owned callable results",
            Self::ScalarCallableResults => "scalar callable results",
        }
    }
}

/// Typed ownership insertion or independent-validation refusal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OwnershipError {
    ResourceLimit {
        resource: OwnershipResource,
        limit: usize,
        observed: usize,
    },
    AllocationFailure {
        resource: OwnershipResource,
        requested: usize,
    },
    CandidateValidation(ValidationError),
    UnsupportedWitnessVersion {
        seen: u16,
    },
    FunctionCount {
        source: usize,
        candidate: usize,
        witness: usize,
    },
    ProgramIdentityChanged,
    FunctionRow {
        index: usize,
        source: FunctionId,
        candidate: FunctionId,
        witness: FunctionId,
    },
    WitnessResultOwnership {
        function: FunctionId,
        expected: CallableResultOwnership,
        actual: CallableResultOwnership,
    },
    Mode {
        function: FunctionId,
        expected: OwnershipMode,
        actual: OwnershipMode,
    },
    PreservedFunctionChanged {
        function: FunctionId,
    },
    FunctionMetadataChanged {
        function: FunctionId,
    },
    SkeletonMismatch {
        function: FunctionId,
        source_instruction: usize,
        candidate_instruction: usize,
    },
    DropSchedule {
        function: FunctionId,
        source_position: usize,
        expected: Option<Register>,
        actual: Option<Register>,
    },
    EdgeDropSchedule {
        function: FunctionId,
        source_instruction: usize,
        edge: u8,
        expected: Option<Register>,
        actual: Option<Register>,
    },
    ControlTarget {
        function: FunctionId,
        source_instruction: usize,
        edge: u8,
        expected: Pc,
        actual: Pc,
    },
    OwnershipState {
        function: FunctionId,
        source_position: usize,
        register: Register,
    },
    OwnershipOverwrite {
        function: FunctionId,
        source_position: usize,
        register: Register,
    },
    OwnershipLeak {
        function: FunctionId,
        source_position: usize,
        register: Register,
    },
    OwnershipJoin {
        function: FunctionId,
        candidate_instruction: usize,
        successor: usize,
        register: Register,
        expected_live: bool,
        actual_live: bool,
    },
    WitnessCount {
        function: FunctionId,
        count: OwnershipWitnessCount,
        expected: usize,
        actual: usize,
    },
}

impl fmt::Display for OwnershipError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ResourceLimit {
                resource,
                limit,
                observed,
            } => write!(
                formatter,
                "ownership resource {resource:?} observed {observed}, limit {limit}"
            ),
            Self::AllocationFailure {
                resource,
                requested,
            } => write!(
                formatter,
                "ownership allocation for {resource:?} refused {requested} items"
            ),
            Self::CandidateValidation(error) => {
                write!(
                    formatter,
                    "ownership candidate failed FLBC validation: {error}"
                )
            }
            Self::UnsupportedWitnessVersion { seen } => {
                write!(formatter, "unsupported ownership witness version {seen}")
            }
            Self::FunctionCount {
                source,
                candidate,
                witness,
            } => write!(
                formatter,
                "ownership function counts differ: source {source}, candidate {candidate}, witness {witness}"
            ),
            Self::ProgramIdentityChanged => {
                formatter.write_str("ownership candidate changed the FLBC schema or entry")
            }
            Self::FunctionRow {
                index,
                source,
                candidate,
                witness,
            } => write!(
                formatter,
                "ownership row {index} names source f{}, candidate f{}, witness f{}",
                source.get(),
                candidate.get(),
                witness.get()
            ),
            Self::WitnessResultOwnership {
                function,
                expected,
                actual,
            } => write!(
                formatter,
                "ownership function {} witness result ownership is {}, expected {}",
                function.get(),
                actual.token(),
                expected.token()
            ),
            Self::Mode {
                function,
                expected,
                actual,
            } => write!(
                formatter,
                "ownership function {} expected mode {}, observed {}",
                function.get(),
                expected.token(),
                actual.token()
            ),
            Self::PreservedFunctionChanged { function } => write!(
                formatter,
                "preserved ownership function {} changed bytes",
                function.get()
            ),
            Self::FunctionMetadataChanged { function } => write!(
                formatter,
                "ownership function {} changed id, arity, parameter ownership, or register width",
                function.get()
            ),
            Self::SkeletonMismatch {
                function,
                source_instruction,
                candidate_instruction,
            } => write!(
                formatter,
                "ownership function {} candidate instruction {candidate_instruction} differs from source instruction {source_instruction}",
                function.get()
            ),
            Self::DropSchedule {
                function,
                source_position,
                expected,
                actual,
            } => write!(
                formatter,
                "ownership function {} position {source_position} expected drop {:?}, observed {:?}",
                function.get(),
                expected.map(Register::get),
                actual.map(Register::get)
            ),
            Self::EdgeDropSchedule {
                function,
                source_instruction,
                edge,
                expected,
                actual,
            } => write!(
                formatter,
                "ownership function {} instruction {source_instruction} edge {edge} expected drop {:?}, observed {:?}",
                function.get(),
                expected.map(Register::get),
                actual.map(Register::get)
            ),
            Self::ControlTarget {
                function,
                source_instruction,
                edge,
                expected,
                actual,
            } => write!(
                formatter,
                "ownership function {} instruction {source_instruction} edge {edge} expected pc {}, observed pc {}",
                function.get(),
                expected.get(),
                actual.get()
            ),
            Self::OwnershipState {
                function,
                source_position,
                register,
            } => write!(
                formatter,
                "ownership function {} position {source_position} has invalid state for register {}",
                function.get(),
                register.get()
            ),
            Self::OwnershipOverwrite {
                function,
                source_position,
                register,
            } => write!(
                formatter,
                "ownership function {} position {source_position} overwrites live register {}",
                function.get(),
                register.get()
            ),
            Self::OwnershipLeak {
                function,
                source_position,
                register,
            } => write!(
                formatter,
                "ownership function {} position {source_position} abandons live register {}",
                function.get(),
                register.get()
            ),
            Self::OwnershipJoin {
                function,
                candidate_instruction,
                successor,
                register,
                expected_live,
                actual_live,
            } => write!(
                formatter,
                "ownership function {} candidate instruction {candidate_instruction} edge to {successor} disagrees for register {}: expected live={expected_live}, observed live={actual_live}",
                function.get(),
                register.get()
            ),
            Self::WitnessCount {
                function,
                count,
                expected,
                actual,
            } => write!(
                formatter,
                "ownership function {} witness {} count {actual}/{expected}",
                function.get(),
                count.token()
            ),
        }
    }
}

impl std::error::Error for OwnershipError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::CandidateValidation(error) => Some(error),
            _ => None,
        }
    }
}

impl OwnershipError {
    /// Whether this refusal is a budget or allocation failure, not a
    /// witness-shape refusal.
    pub fn is_resource_exhaustion(&self) -> bool {
        matches!(
            self,
            Self::ResourceLimit { .. } | Self::AllocationFailure { .. }
        )
    }
}

/// Exact reason an untrusted program was refused before execution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ValidationError {
    UnsupportedVersion {
        seen: u16,
    },
    EmptyProgram,
    NonCanonicalFunctionId {
        index: usize,
        seen: FunctionId,
    },
    MissingEntry {
        entry: FunctionId,
    },
    EntryHasParameters {
        entry: FunctionId,
        arity: u16,
    },
    RegisterFileTooSmall {
        function: FunctionId,
        arity: u16,
        registers: u16,
    },
    FunctionOwnershipArity {
        function: FunctionId,
        parameters: u16,
        ownership: usize,
    },
    EmptyFunction {
        function: FunctionId,
    },
    InstructionSpaceOverflow {
        function: FunctionId,
        count: usize,
    },
    RegisterOutOfBounds {
        function: FunctionId,
        pc: Pc,
        register: Register,
        register_count: u16,
    },
    ReadBeforeWrite {
        function: FunctionId,
        pc: Pc,
        register: Register,
    },
    JumpOutOfBounds {
        function: FunctionId,
        pc: Pc,
        target: Pc,
        instruction_count: usize,
    },
    MissingCallTarget {
        function: FunctionId,
        pc: Pc,
        target: FunctionId,
    },
    CallArity {
        function: FunctionId,
        pc: Pc,
        target: FunctionId,
        expected: u16,
        actual: usize,
    },
    CallOwnershipArity {
        function: FunctionId,
        pc: Pc,
        target: FunctionId,
        arguments: usize,
        ownership: usize,
    },
    CallOwnershipContract {
        function: FunctionId,
        pc: Pc,
        target: FunctionId,
        argument: usize,
        expected: ArgumentOwnership,
        actual: ArgumentOwnership,
    },
    CallResultOwnershipContract {
        function: FunctionId,
        pc: Pc,
        target: FunctionId,
        expected: CallableResultOwnership,
        actual: CallableResultOwnership,
    },
    CallConsumeAlias {
        function: FunctionId,
        pc: Pc,
        target: FunctionId,
        register: Register,
        first: usize,
        second: usize,
    },
    CallUniqueAlias {
        function: FunctionId,
        pc: Pc,
        target: FunctionId,
        register: Register,
        unique: usize,
        alias: usize,
    },
    MissingClosureTarget {
        function: FunctionId,
        pc: Pc,
        target: FunctionId,
    },
    ClosureCaptureArity {
        function: FunctionId,
        pc: Pc,
        target: FunctionId,
        target_arity: u16,
        captures: usize,
    },
    ClosureOwnershipArity {
        function: FunctionId,
        pc: Pc,
        target: FunctionId,
        captures: usize,
        ownership: usize,
    },
    ClosureOwnershipContract {
        function: FunctionId,
        pc: Pc,
        target: FunctionId,
        capture: usize,
        expected: ArgumentOwnership,
        actual: ArgumentOwnership,
    },
    ClosureConsumeAlias {
        function: FunctionId,
        pc: Pc,
        target: FunctionId,
        register: Register,
        first: usize,
        second: usize,
    },
    ClosureUniqueCapture {
        function: FunctionId,
        pc: Pc,
        target: FunctionId,
        capture: usize,
        register: Register,
    },
    ClosureArityOverflow {
        function: FunctionId,
        pc: Pc,
        target: FunctionId,
        target_arity: u16,
    },
    EmptyApply {
        function: FunctionId,
        pc: Pc,
    },
    ApplyOwnershipArity {
        function: FunctionId,
        pc: Pc,
        arguments: usize,
        ownership: usize,
    },
    ApplyConsumeAlias {
        function: FunctionId,
        pc: Pc,
        register: Register,
        first: usize,
        second: usize,
    },
    ApplyUniqueAlias {
        function: FunctionId,
        pc: Pc,
        register: Register,
        unique: usize,
        alias: usize,
    },
    ApplyUniqueClosureAlias {
        function: FunctionId,
        pc: Pc,
        register: Register,
        unique: usize,
    },
    InvalidExternRow {
        function: FunctionId,
        pc: Pc,
        row: String,
    },
    IntrinsicOwnershipArity {
        function: FunctionId,
        pc: Pc,
        arguments: usize,
        ownership: usize,
    },
    IntrinsicConsumeAlias {
        function: FunctionId,
        pc: Pc,
        register: Register,
        first: usize,
        second: usize,
    },
    IntrinsicUniqueAlias {
        function: FunctionId,
        pc: Pc,
        register: Register,
        unique: usize,
        alias: usize,
    },
    NatConstantOutOfRange {
        function: FunctionId,
        pc: Pc,
        value: u64,
    },
    CtorTagOutOfRange {
        function: FunctionId,
        pc: Pc,
        tag: u8,
    },
    TooManyCtorFields {
        function: FunctionId,
        pc: Pc,
        count: usize,
    },
    TooManyCtorScalarBytes {
        function: FunctionId,
        pc: Pc,
        count: usize,
    },
    CtorFieldShapeOutOfRange {
        function: FunctionId,
        pc: Pc,
        expected_fields: u16,
    },
    CtorFieldOutOfBounds {
        function: FunctionId,
        pc: Pc,
        expected_fields: u16,
        field: u16,
    },
    Fallthrough {
        function: FunctionId,
        pc: Pc,
    },
    UnreachableInstruction {
        function: FunctionId,
        pc: Pc,
    },
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedVersion { seen } => {
                write!(f, "unsupported FLBC schema version {seen}")
            }
            Self::EmptyProgram => write!(f, "FLBC function table is empty"),
            Self::NonCanonicalFunctionId { index, seen } => write!(
                f,
                "function table row {index} carries non-canonical id {}",
                seen.get()
            ),
            Self::MissingEntry { entry } => {
                write!(f, "entry function {} is absent", entry.get())
            }
            Self::EntryHasParameters { entry, arity } => {
                write!(f, "entry function {} has {arity} parameters", entry.get())
            }
            Self::RegisterFileTooSmall {
                function,
                arity,
                registers,
            } => write!(
                f,
                "function {} has {arity} parameters but only {registers} registers",
                function.get()
            ),
            Self::FunctionOwnershipArity {
                function,
                parameters,
                ownership,
            } => write!(
                f,
                "function {} has {parameters} parameters but {ownership} ownership dispositions",
                function.get()
            ),
            Self::EmptyFunction { function } => {
                write!(f, "function {} has no instructions", function.get())
            }
            Self::InstructionSpaceOverflow { function, count } => write!(
                f,
                "function {} has {count} instructions, beyond the FLBC pc space",
                function.get()
            ),
            Self::RegisterOutOfBounds {
                function,
                pc,
                register,
                register_count,
            } => write!(
                f,
                "function {} pc {} names register {} outside 0..{register_count}",
                function.get(),
                pc.get(),
                register.get()
            ),
            Self::ReadBeforeWrite {
                function,
                pc,
                register,
            } => write!(
                f,
                "function {} pc {} reads uninitialized register {}",
                function.get(),
                pc.get(),
                register.get()
            ),
            Self::JumpOutOfBounds {
                function,
                pc,
                target,
                instruction_count,
            } => write!(
                f,
                "function {} pc {} jumps to {} outside {instruction_count} instructions",
                function.get(),
                pc.get(),
                target.get()
            ),
            Self::MissingCallTarget {
                function,
                pc,
                target,
            } => write!(
                f,
                "function {} pc {} calls absent function {}",
                function.get(),
                pc.get(),
                target.get()
            ),
            Self::CallArity {
                function,
                pc,
                target,
                expected,
                actual,
            } => write!(
                f,
                "function {} pc {} calls function {} with {actual} args, expected {expected}",
                function.get(),
                pc.get(),
                target.get()
            ),
            Self::CallOwnershipArity {
                function,
                pc,
                target,
                arguments,
                ownership,
            } => write!(
                f,
                "function {} pc {} calls function {} with {arguments} arguments but {ownership} ownership dispositions",
                function.get(),
                pc.get(),
                target.get()
            ),
            Self::CallOwnershipContract {
                function,
                pc,
                target,
                argument,
                expected,
                actual,
            } => write!(
                f,
                "function {} pc {} call argument {argument} for function {} declares {}, expected {}",
                function.get(),
                pc.get(),
                target.get(),
                actual.token(),
                expected.token()
            ),
            Self::CallResultOwnershipContract {
                function,
                pc,
                target,
                expected,
                actual,
            } => write!(
                f,
                "function {} pc {} call result for function {} declares {}, expected {}",
                function.get(),
                pc.get(),
                target.get(),
                actual.token(),
                expected.token()
            ),
            Self::CallConsumeAlias {
                function,
                pc,
                target,
                register,
                first,
                second,
            } => write!(
                f,
                "function {} pc {} call to function {} consumes register {} in arguments {first} and {second}",
                function.get(),
                pc.get(),
                target.get(),
                register.get()
            ),
            Self::CallUniqueAlias {
                function,
                pc,
                target,
                register,
                unique,
                alias,
            } => write!(
                f,
                "function {} pc {} call to function {} has unique argument {unique} alias argument {alias} in register {}",
                function.get(),
                pc.get(),
                target.get(),
                register.get()
            ),
            Self::MissingClosureTarget {
                function,
                pc,
                target,
            } => write!(
                f,
                "function {} pc {} closes over absent function {}",
                function.get(),
                pc.get(),
                target.get()
            ),
            Self::ClosureCaptureArity {
                function,
                pc,
                target,
                target_arity,
                captures,
            } => write!(
                f,
                "function {} pc {} closes function {} with {captures} captures, but its arity {target_arity} requires at least one unapplied argument",
                function.get(),
                pc.get(),
                target.get()
            ),
            Self::ClosureOwnershipArity {
                function,
                pc,
                target,
                captures,
                ownership,
            } => write!(
                f,
                "function {} pc {} closure for function {} carries {ownership} ownership dispositions for {captures} captures",
                function.get(),
                pc.get(),
                target.get()
            ),
            Self::ClosureOwnershipContract {
                function,
                pc,
                target,
                capture,
                expected,
                actual,
            } => write!(
                f,
                "function {} pc {} closure for function {} capture {capture} ownership is {}, expected {}",
                function.get(),
                pc.get(),
                target.get(),
                actual.token(),
                expected.token()
            ),
            Self::ClosureConsumeAlias {
                function,
                pc,
                target,
                register,
                first,
                second,
            } => write!(
                f,
                "function {} pc {} closure for function {} consumes register {} at captures {first} and {second}",
                function.get(),
                pc.get(),
                target.get(),
                register.get()
            ),
            Self::ClosureUniqueCapture {
                function,
                pc,
                target,
                capture,
                register,
            } => write!(
                f,
                "function {} pc {} closure for function {} capture {capture} in register {} is unique, but reusable closures cannot retain a unique payload",
                function.get(),
                pc.get(),
                target.get(),
                register.get()
            ),
            Self::ClosureArityOverflow {
                function,
                pc,
                target,
                target_arity,
            } => write!(
                f,
                "function {} pc {} cannot encode function {} arity {target_arity} with the interpreter target word",
                function.get(),
                pc.get(),
                target.get()
            ),
            Self::EmptyApply { function, pc } => write!(
                f,
                "function {} pc {} applies no arguments",
                function.get(),
                pc.get()
            ),
            Self::ApplyOwnershipArity {
                function,
                pc,
                arguments,
                ownership,
            } => write!(
                f,
                "function {} pc {} applies {arguments} arguments with {ownership} ownership dispositions",
                function.get(),
                pc.get()
            ),
            Self::ApplyConsumeAlias {
                function,
                pc,
                register,
                first,
                second,
            } => write!(
                f,
                "function {} pc {} Apply consumes register {} in arguments {first} and {second}",
                function.get(),
                pc.get(),
                register.get()
            ),
            Self::ApplyUniqueAlias {
                function,
                pc,
                register,
                unique,
                alias,
            } => write!(
                f,
                "function {} pc {} Apply unique argument {unique} aliases argument {alias} in register {}",
                function.get(),
                pc.get(),
                register.get()
            ),
            Self::ApplyUniqueClosureAlias {
                function,
                pc,
                register,
                unique,
            } => write!(
                f,
                "function {} pc {} Apply unique argument {unique} aliases the closure in register {}",
                function.get(),
                pc.get(),
                register.get()
            ),
            Self::InvalidExternRow { function, pc, row } => write!(
                f,
                "function {} pc {} carries invalid extern row {row:?}",
                function.get(),
                pc.get()
            ),
            Self::IntrinsicOwnershipArity {
                function,
                pc,
                arguments,
                ownership,
            } => write!(
                f,
                "function {} pc {} has {arguments} intrinsic arguments but {ownership} ownership dispositions",
                function.get(),
                pc.get()
            ),
            Self::IntrinsicConsumeAlias {
                function,
                pc,
                register,
                first,
                second,
            } => write!(
                f,
                "function {} pc {} consumes register {} in intrinsic arguments {first} and {second}",
                function.get(),
                pc.get(),
                register.get()
            ),
            Self::IntrinsicUniqueAlias {
                function,
                pc,
                register,
                unique,
                alias,
            } => write!(
                f,
                "function {} pc {} unique intrinsic argument {unique} aliases argument {alias} in register {}",
                function.get(),
                pc.get(),
                register.get()
            ),
            Self::NatConstantOutOfRange {
                function,
                pc,
                value,
            } => write!(
                f,
                "function {} pc {} Nat constant {value} is not a tagged scalar",
                function.get(),
                pc.get()
            ),
            Self::CtorTagOutOfRange { function, pc, tag } => write!(
                f,
                "function {} pc {} constructor tag {tag} exceeds the ABI contract",
                function.get(),
                pc.get()
            ),
            Self::TooManyCtorFields {
                function,
                pc,
                count,
            } => write!(
                f,
                "function {} pc {} constructor has {count} object fields",
                function.get(),
                pc.get()
            ),
            Self::TooManyCtorScalarBytes {
                function,
                pc,
                count,
            } => write!(
                f,
                "function {} pc {} constructor has {count} scalar bytes",
                function.get(),
                pc.get()
            ),
            Self::CtorFieldShapeOutOfRange {
                function,
                pc,
                expected_fields,
            } => write!(
                f,
                "function {} pc {} projection expects {expected_fields} constructor fields outside the ABI contract",
                function.get(),
                pc.get()
            ),
            Self::CtorFieldOutOfBounds {
                function,
                pc,
                expected_fields,
                field,
            } => write!(
                f,
                "function {} pc {} projection field {field} is outside {expected_fields} constructor fields",
                function.get(),
                pc.get()
            ),
            Self::Fallthrough { function, pc } => write!(
                f,
                "function {} falls through after pc {}",
                function.get(),
                pc.get()
            ),
            Self::UnreachableInstruction { function, pc } => write!(
                f,
                "function {} pc {} is unreachable",
                function.get(),
                pc.get()
            ),
        }
    }
}

impl std::error::Error for ValidationError {}

/// Validate the complete function table and every function-local CFG.
pub fn validate(program: Program) -> Result<ValidatedProgram, ValidationError> {
    if program.schema_version != FLBC_SCHEMA_VERSION {
        return Err(ValidationError::UnsupportedVersion {
            seen: program.schema_version,
        });
    }
    if program.functions.is_empty() {
        return Err(ValidationError::EmptyProgram);
    }

    for (index, function) in program.functions.iter().enumerate() {
        if function.id.index() != Some(index) {
            return Err(ValidationError::NonCanonicalFunctionId {
                index,
                seen: function.id,
            });
        }
        if function.arity > function.register_count {
            return Err(ValidationError::RegisterFileTooSmall {
                function: function.id,
                arity: function.arity,
                registers: function.register_count,
            });
        }
        if usize::from(function.arity) != function.parameter_ownership.len() {
            return Err(ValidationError::FunctionOwnershipArity {
                function: function.id,
                parameters: function.arity,
                ownership: function.parameter_ownership.len(),
            });
        }
        if function.code.is_empty() {
            return Err(ValidationError::EmptyFunction {
                function: function.id,
            });
        }
        if u32::try_from(function.code.len()).is_err() {
            return Err(ValidationError::InstructionSpaceOverflow {
                function: function.id,
                count: function.code.len(),
            });
        }
    }

    let Some(entry) = program.entry.index().and_then(|i| program.functions.get(i)) else {
        return Err(ValidationError::MissingEntry {
            entry: program.entry,
        });
    };
    if entry.arity != 0 {
        return Err(ValidationError::EntryHasParameters {
            entry: entry.id,
            arity: entry.arity,
        });
    }

    for function in &program.functions {
        validate_function(&program, function)?;
    }
    Ok(ValidatedProgram { program })
}

/// Encode one validated program into its unique byte string for this wire version.
pub fn encode_canonical(
    program: &ValidatedProgram,
    limits: CodecLimits,
) -> Result<Vec<u8>, CodecError> {
    let mut encoder = Encoder::new(limits);
    encoder.raw(&FLBC_MAGIC)?;
    encoder.u16(FLBC_WIRE_VERSION)?;
    encoder.u16(program.schema_version())?;
    encoder.u32(program.entry().get())?;

    let functions = program.functions();
    ensure_limit(
        CodecResource::Functions,
        limits.max_functions,
        functions.len(),
    )?;
    encoder.len("function table", functions.len())?;
    for function in functions {
        encoder.u32(function.id.get())?;
        encoder.u16(function.arity)?;
        encoder.u16(function.register_count)?;
        encoder.argument_ownership(&function.parameter_ownership)?;
        encoder.callable_result_ownership(function.result_ownership)?;
        encoder.charge_instructions(function.code.len())?;
        encoder.len("instruction table", function.code.len())?;
        for instruction in &function.code {
            encode_instruction(&mut encoder, instruction)?;
        }
    }
    Ok(encoder.finish())
}

/// Decode a canonical artifact and validate the complete program before
/// returning an executable wrapper.
pub fn decode_canonical(bytes: &[u8], limits: CodecLimits) -> Result<ValidatedProgram, CodecError> {
    ensure_limit(
        CodecResource::ArtifactBytes,
        limits.max_artifact_bytes,
        bytes.len(),
    )?;
    let mut decoder = Decoder::new(bytes, limits);
    if decoder.array::<8>()? != FLBC_MAGIC {
        return Err(CodecError::BadMagic);
    }
    let wire_version = decoder.u16()?;
    if wire_version != FLBC_WIRE_VERSION {
        return Err(CodecError::UnsupportedWireVersion { seen: wire_version });
    }
    let schema_version = decoder.u16()?;
    let entry = FunctionId::new(decoder.u32()?);
    let function_count = decoder.len("function table")?;
    ensure_limit(
        CodecResource::Functions,
        limits.max_functions,
        function_count,
    )?;
    decoder.require_items(function_count, 16)?;
    let mut functions = Vec::new();
    functions
        .try_reserve_exact(function_count)
        .map_err(|_| CodecError::AllocationFailure {
            resource: CodecResource::Functions,
            requested: function_count,
        })?;
    for _ in 0..function_count {
        let id = FunctionId::new(decoder.u32()?);
        let arity = decoder.u16()?;
        let register_count = decoder.u16()?;
        let parameter_ownership = decoder.argument_ownership()?;
        let result_ownership = decoder.callable_result_ownership()?;
        let instruction_count = decoder.len("instruction table")?;
        decoder.charge_instructions(instruction_count)?;
        decoder.require_items(instruction_count, 3)?;
        let mut code = Vec::new();
        code.try_reserve_exact(instruction_count)
            .map_err(|_| CodecError::AllocationFailure {
                resource: CodecResource::Instructions,
                requested: instruction_count,
            })?;
        for _ in 0..instruction_count {
            code.push(decode_instruction(&mut decoder)?);
        }
        functions.push(Function {
            id,
            arity,
            parameter_ownership,
            result_ownership,
            register_count,
            code,
        });
    }
    if decoder.remaining() != 0 {
        return Err(CodecError::TrailingBytes {
            offset: decoder.offset,
            remaining: decoder.remaining(),
        });
    }
    validate(Program {
        schema_version,
        entry,
        functions,
    })
    .map_err(CodecError::Validation)
}

fn encode_instruction(encoder: &mut Encoder, instruction: &Instruction) -> Result<(), CodecError> {
    match instruction {
        Instruction::Nat { dst, value } => {
            encoder.u8(OP_NAT)?;
            encoder.register(*dst)?;
            encoder.u64(*value)
        }
        Instruction::String { dst, value } => {
            encoder.u8(OP_STRING)?;
            encoder.register(*dst)?;
            encoder.string("String literal", value)
        }
        Instruction::Copy { dst, src } => {
            encoder.u8(OP_COPY)?;
            encoder.register(*dst)?;
            encoder.register(*src)
        }
        Instruction::Move { dst, src } => {
            encoder.u8(OP_MOVE)?;
            encoder.register(*dst)?;
            encoder.register(*src)
        }
        Instruction::Drop { src } => {
            encoder.u8(OP_DROP)?;
            encoder.register(*src)
        }
        Instruction::Ctor {
            dst,
            tag,
            fields,
            scalar_bytes,
        } => {
            encoder.u8(OP_CTOR)?;
            encoder.register(*dst)?;
            encoder.u8(*tag)?;
            encoder.registers(fields)?;
            encoder.bytes("constructor scalar bytes", scalar_bytes)
        }
        Instruction::CtorField {
            dst,
            src,
            expected_tag,
            expected_fields,
            field,
        } => {
            encoder.u8(OP_CTOR_FIELD)?;
            encoder.register(*dst)?;
            encoder.register(*src)?;
            encoder.u8(*expected_tag)?;
            encoder.u16(*expected_fields)?;
            encoder.u16(*field)
        }
        Instruction::Array { dst, items } => {
            encoder.u8(OP_ARRAY)?;
            encoder.register(*dst)?;
            encoder.registers(items)
        }
        Instruction::Intrinsic {
            dst,
            row,
            args,
            argument_ownership,
            result_ownership,
        } => {
            encoder.u8(OP_INTRINSIC)?;
            encoder.register(*dst)?;
            encoder.string("intrinsic row", row)?;
            encoder.registers(args)?;
            encoder.argument_ownership(argument_ownership)?;
            encoder.result_ownership(*result_ownership)
        }
        Instruction::Call {
            dst,
            function,
            args,
            argument_ownership,
            result_ownership,
        } => {
            encoder.u8(OP_CALL)?;
            encoder.register(*dst)?;
            encoder.u32(function.get())?;
            encoder.registers(args)?;
            encoder.argument_ownership(argument_ownership)?;
            encoder.callable_result_ownership(*result_ownership)
        }
        Instruction::Closure {
            dst,
            function,
            captures,
            capture_ownership,
        } => {
            encoder.u8(OP_CLOSURE)?;
            encoder.register(*dst)?;
            encoder.u32(function.get())?;
            encoder.registers(captures)?;
            encoder.argument_ownership(capture_ownership)
        }
        Instruction::Apply {
            dst,
            closure,
            args,
            argument_ownership,
            result_ownership,
        } => {
            encoder.u8(OP_APPLY)?;
            encoder.register(*dst)?;
            encoder.register(*closure)?;
            encoder.registers(args)?;
            encoder.argument_ownership(argument_ownership)?;
            encoder.callable_result_ownership(*result_ownership)
        }
        Instruction::Jump { target } => {
            encoder.u8(OP_JUMP)?;
            encoder.u32(target.get())
        }
        Instruction::JumpIfZero {
            cond,
            zero,
            nonzero,
        } => {
            encoder.u8(OP_JUMP_IF_ZERO)?;
            encoder.register(*cond)?;
            encoder.u32(zero.get())?;
            encoder.u32(nonzero.get())
        }
        Instruction::CheckSystem { module_name } => {
            encoder.u8(OP_CHECK_SYSTEM)?;
            encoder.string("checkSystem module name", module_name)
        }
        Instruction::CheckSystemValue { module_name } => {
            encoder.u8(OP_CHECK_SYSTEM_VALUE)?;
            encoder.register(*module_name)
        }
        Instruction::Return { src } => {
            encoder.u8(OP_RETURN)?;
            encoder.register(*src)
        }
        Instruction::Panic { message } => {
            encoder.u8(OP_PANIC)?;
            encoder.register(*message)
        }
    }
}

fn decode_instruction(decoder: &mut Decoder<'_>) -> Result<Instruction, CodecError> {
    let opcode_offset = decoder.offset;
    let opcode = decoder.u8()?;
    match opcode {
        OP_NAT => Ok(Instruction::Nat {
            dst: decoder.register()?,
            value: decoder.u64()?,
        }),
        OP_STRING => Ok(Instruction::String {
            dst: decoder.register()?,
            value: decoder.string("String literal")?,
        }),
        OP_COPY => Ok(Instruction::Copy {
            dst: decoder.register()?,
            src: decoder.register()?,
        }),
        OP_MOVE => Ok(Instruction::Move {
            dst: decoder.register()?,
            src: decoder.register()?,
        }),
        OP_DROP => Ok(Instruction::Drop {
            src: decoder.register()?,
        }),
        OP_CTOR => Ok(Instruction::Ctor {
            dst: decoder.register()?,
            tag: decoder.u8()?,
            fields: decoder.registers()?,
            scalar_bytes: decoder.bytes("constructor scalar bytes")?,
        }),
        OP_CTOR_FIELD => Ok(Instruction::CtorField {
            dst: decoder.register()?,
            src: decoder.register()?,
            expected_tag: decoder.u8()?,
            expected_fields: decoder.u16()?,
            field: decoder.u16()?,
        }),
        OP_ARRAY => Ok(Instruction::Array {
            dst: decoder.register()?,
            items: decoder.registers()?,
        }),
        OP_INTRINSIC => Ok(Instruction::Intrinsic {
            dst: decoder.register()?,
            row: decoder.string("intrinsic row")?,
            args: decoder.registers()?,
            argument_ownership: decoder.argument_ownership()?,
            result_ownership: decoder.result_ownership()?,
        }),
        OP_CALL => Ok(Instruction::Call {
            dst: decoder.register()?,
            function: FunctionId::new(decoder.u32()?),
            args: decoder.registers()?,
            argument_ownership: decoder.argument_ownership()?,
            result_ownership: decoder.callable_result_ownership()?,
        }),
        OP_CLOSURE => Ok(Instruction::Closure {
            dst: decoder.register()?,
            function: FunctionId::new(decoder.u32()?),
            captures: decoder.registers()?,
            capture_ownership: decoder.argument_ownership()?,
        }),
        OP_APPLY => Ok(Instruction::Apply {
            dst: decoder.register()?,
            closure: decoder.register()?,
            args: decoder.registers()?,
            argument_ownership: decoder.argument_ownership()?,
            result_ownership: decoder.callable_result_ownership()?,
        }),
        OP_JUMP => Ok(Instruction::Jump {
            target: Pc::new(decoder.u32()?),
        }),
        OP_JUMP_IF_ZERO => Ok(Instruction::JumpIfZero {
            cond: decoder.register()?,
            zero: Pc::new(decoder.u32()?),
            nonzero: Pc::new(decoder.u32()?),
        }),
        OP_CHECK_SYSTEM => Ok(Instruction::CheckSystem {
            module_name: decoder.string("checkSystem module name")?,
        }),
        OP_CHECK_SYSTEM_VALUE => Ok(Instruction::CheckSystemValue {
            module_name: decoder.register()?,
        }),
        OP_RETURN => Ok(Instruction::Return {
            src: decoder.register()?,
        }),
        OP_PANIC => Ok(Instruction::Panic {
            message: decoder.register()?,
        }),
        opcode => Err(CodecError::UnknownOpcode {
            opcode,
            offset: opcode_offset,
        }),
    }
}

fn ensure_limit(resource: CodecResource, limit: usize, observed: usize) -> Result<(), CodecError> {
    if observed > limit {
        return Err(CodecError::ResourceLimit {
            resource,
            limit,
            observed,
        });
    }
    Ok(())
}

fn checked_total(
    resource: CodecResource,
    current: usize,
    added: usize,
    limit: usize,
) -> Result<usize, CodecError> {
    let observed = current.saturating_add(added);
    ensure_limit(resource, limit, observed)?;
    Ok(observed)
}

struct Encoder {
    bytes: Vec<u8>,
    limits: CodecLimits,
    instructions: usize,
    operands: usize,
    literal_bytes: usize,
}

impl Encoder {
    fn new(limits: CodecLimits) -> Self {
        Self {
            bytes: Vec::new(),
            limits,
            instructions: 0,
            operands: 0,
            literal_bytes: 0,
        }
    }

    fn finish(self) -> Vec<u8> {
        self.bytes
    }

    fn raw(&mut self, bytes: &[u8]) -> Result<(), CodecError> {
        checked_total(
            CodecResource::ArtifactBytes,
            self.bytes.len(),
            bytes.len(),
            self.limits.max_artifact_bytes,
        )?;
        self.bytes
            .try_reserve(bytes.len())
            .map_err(|_| CodecError::AllocationFailure {
                resource: CodecResource::ArtifactBytes,
                requested: bytes.len(),
            })?;
        self.bytes.extend_from_slice(bytes);
        Ok(())
    }

    fn u8(&mut self, value: u8) -> Result<(), CodecError> {
        self.raw(&[value])
    }

    fn u16(&mut self, value: u16) -> Result<(), CodecError> {
        self.raw(&value.to_le_bytes())
    }

    fn u32(&mut self, value: u32) -> Result<(), CodecError> {
        self.raw(&value.to_le_bytes())
    }

    fn u64(&mut self, value: u64) -> Result<(), CodecError> {
        self.raw(&value.to_le_bytes())
    }

    fn len(&mut self, field: &'static str, len: usize) -> Result<(), CodecError> {
        let len = u32::try_from(len).map_err(|_| CodecError::LengthOverflow { field, len })?;
        self.u32(len)
    }

    fn register(&mut self, register: Register) -> Result<(), CodecError> {
        self.operands = checked_total(
            CodecResource::Operands,
            self.operands,
            1,
            self.limits.max_operands,
        )?;
        self.u16(register.get())
    }

    fn registers(&mut self, registers: &[Register]) -> Result<(), CodecError> {
        self.operands = checked_total(
            CodecResource::Operands,
            self.operands,
            registers.len(),
            self.limits.max_operands,
        )?;
        self.len("register vector", registers.len())?;
        for register in registers {
            self.u16(register.get())?;
        }
        Ok(())
    }

    fn argument_ownership(&mut self, ownership: &[ArgumentOwnership]) -> Result<(), CodecError> {
        self.operands = checked_total(
            CodecResource::Operands,
            self.operands,
            ownership.len(),
            self.limits.max_operands,
        )?;
        self.len("intrinsic argument ownership", ownership.len())?;
        for disposition in ownership {
            self.u8(disposition.wire_tag())?;
        }
        Ok(())
    }

    fn result_ownership(&mut self, ownership: ResultOwnership) -> Result<(), CodecError> {
        self.operands = checked_total(
            CodecResource::Operands,
            self.operands,
            1,
            self.limits.max_operands,
        )?;
        self.u8(ownership.wire_tag())
    }

    fn callable_result_ownership(
        &mut self,
        ownership: CallableResultOwnership,
    ) -> Result<(), CodecError> {
        self.operands = checked_total(
            CodecResource::Operands,
            self.operands,
            1,
            self.limits.max_operands,
        )?;
        self.u8(ownership.wire_tag())
    }

    fn bytes(&mut self, field: &'static str, bytes: &[u8]) -> Result<(), CodecError> {
        self.literal_bytes = checked_total(
            CodecResource::LiteralBytes,
            self.literal_bytes,
            bytes.len(),
            self.limits.max_literal_bytes,
        )?;
        self.len(field, bytes.len())?;
        self.raw(bytes)
    }

    fn string(&mut self, field: &'static str, value: &str) -> Result<(), CodecError> {
        self.bytes(field, value.as_bytes())
    }

    fn charge_instructions(&mut self, count: usize) -> Result<(), CodecError> {
        self.instructions = checked_total(
            CodecResource::Instructions,
            self.instructions,
            count,
            self.limits.max_instructions,
        )?;
        Ok(())
    }
}

struct Decoder<'a> {
    bytes: &'a [u8],
    offset: usize,
    limits: CodecLimits,
    instructions: usize,
    operands: usize,
    literal_bytes: usize,
}

impl<'a> Decoder<'a> {
    fn new(bytes: &'a [u8], limits: CodecLimits) -> Self {
        Self {
            bytes,
            offset: 0,
            limits,
            instructions: 0,
            operands: 0,
            literal_bytes: 0,
        }
    }

    fn remaining(&self) -> usize {
        self.bytes.len().saturating_sub(self.offset)
    }

    fn require_items(&self, count: usize, minimum_width: usize) -> Result<(), CodecError> {
        let needed = count.saturating_mul(minimum_width);
        let remaining = self.remaining();
        if needed > remaining {
            return Err(CodecError::Truncated {
                offset: self.offset,
                needed,
                remaining,
            });
        }
        Ok(())
    }

    fn take(&mut self, count: usize) -> Result<&'a [u8], CodecError> {
        let remaining = self.remaining();
        let end = self
            .offset
            .checked_add(count)
            .filter(|end| *end <= self.bytes.len())
            .ok_or(CodecError::Truncated {
                offset: self.offset,
                needed: count,
                remaining,
            })?;
        let bytes = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(bytes)
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], CodecError> {
        let bytes = self.take(N)?;
        let mut result = [0; N];
        result.copy_from_slice(bytes);
        Ok(result)
    }

    fn u8(&mut self) -> Result<u8, CodecError> {
        Ok(self.array::<1>()?[0])
    }

    fn u16(&mut self) -> Result<u16, CodecError> {
        Ok(u16::from_le_bytes(self.array()?))
    }

    fn u32(&mut self) -> Result<u32, CodecError> {
        Ok(u32::from_le_bytes(self.array()?))
    }

    fn u64(&mut self) -> Result<u64, CodecError> {
        Ok(u64::from_le_bytes(self.array()?))
    }

    fn len(&mut self, _field: &'static str) -> Result<usize, CodecError> {
        Ok(self.u32()? as usize)
    }

    fn register(&mut self) -> Result<Register, CodecError> {
        self.operands = checked_total(
            CodecResource::Operands,
            self.operands,
            1,
            self.limits.max_operands,
        )?;
        Ok(Register::new(self.u16()?))
    }

    fn registers(&mut self) -> Result<Vec<Register>, CodecError> {
        let count = self.len("register vector")?;
        self.operands = checked_total(
            CodecResource::Operands,
            self.operands,
            count,
            self.limits.max_operands,
        )?;
        self.require_items(count, 2)?;
        let mut registers = Vec::new();
        registers
            .try_reserve_exact(count)
            .map_err(|_| CodecError::AllocationFailure {
                resource: CodecResource::Operands,
                requested: count,
            })?;
        for _ in 0..count {
            registers.push(Register::new(self.u16()?));
        }
        Ok(registers)
    }

    fn argument_ownership(&mut self) -> Result<Vec<ArgumentOwnership>, CodecError> {
        let count = self.len("intrinsic argument ownership")?;
        self.operands = checked_total(
            CodecResource::Operands,
            self.operands,
            count,
            self.limits.max_operands,
        )?;
        self.require_items(count, 1)?;
        let mut ownership = Vec::new();
        ownership
            .try_reserve_exact(count)
            .map_err(|_| CodecError::AllocationFailure {
                resource: CodecResource::Operands,
                requested: count,
            })?;
        for _ in 0..count {
            let offset = self.offset;
            let tag = self.u8()?;
            ownership.push(ArgumentOwnership::from_wire_tag(tag, offset)?);
        }
        Ok(ownership)
    }

    fn result_ownership(&mut self) -> Result<ResultOwnership, CodecError> {
        self.operands = checked_total(
            CodecResource::Operands,
            self.operands,
            1,
            self.limits.max_operands,
        )?;
        let offset = self.offset;
        let tag = self.u8()?;
        ResultOwnership::from_wire_tag(tag, offset)
    }

    fn callable_result_ownership(&mut self) -> Result<CallableResultOwnership, CodecError> {
        self.operands = checked_total(
            CodecResource::Operands,
            self.operands,
            1,
            self.limits.max_operands,
        )?;
        let offset = self.offset;
        let tag = self.u8()?;
        CallableResultOwnership::from_wire_tag(tag, offset)
    }

    fn bytes(&mut self, field: &'static str) -> Result<Vec<u8>, CodecError> {
        let count = self.len(field)?;
        self.literal_bytes = checked_total(
            CodecResource::LiteralBytes,
            self.literal_bytes,
            count,
            self.limits.max_literal_bytes,
        )?;
        let source = self.take(count)?;
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(count)
            .map_err(|_| CodecError::AllocationFailure {
                resource: CodecResource::LiteralBytes,
                requested: count,
            })?;
        bytes.extend_from_slice(source);
        Ok(bytes)
    }

    fn string(&mut self, field: &'static str) -> Result<String, CodecError> {
        let count = self.len(field)?;
        self.literal_bytes = checked_total(
            CodecResource::LiteralBytes,
            self.literal_bytes,
            count,
            self.limits.max_literal_bytes,
        )?;
        let offset = self.offset;
        let bytes = self.take(count)?;
        let value =
            std::str::from_utf8(bytes).map_err(|_| CodecError::InvalidUtf8 { field, offset })?;
        let mut owned = String::new();
        owned
            .try_reserve_exact(count)
            .map_err(|_| CodecError::AllocationFailure {
                resource: CodecResource::LiteralBytes,
                requested: count,
            })?;
        owned.push_str(value);
        Ok(owned)
    }

    fn charge_instructions(&mut self, count: usize) -> Result<(), CodecError> {
        self.instructions = checked_total(
            CodecResource::Instructions,
            self.instructions,
            count,
            self.limits.max_instructions,
        )?;
        Ok(())
    }
}

fn validate_function(program: &Program, function: &Function) -> Result<(), ValidationError> {
    for (offset, instruction) in function.code.iter().enumerate() {
        let pc = Pc::new(u32::try_from(offset).expect("instruction count checked above"));
        for register in instruction.read_registers() {
            check_register(function, pc, register)?;
        }
        if let Some(register) = instruction.written_register() {
            check_register(function, pc, register)?;
        }
        match instruction {
            Instruction::Jump { target } => check_target(function, pc, *target)?,
            Instruction::JumpIfZero { zero, nonzero, .. } => {
                check_target(function, pc, *zero)?;
                check_target(function, pc, *nonzero)?;
            }
            Instruction::Call {
                function: target,
                args,
                argument_ownership,
                result_ownership,
                ..
            } => {
                let Some(callee) = target.index().and_then(|i| program.functions.get(i)) else {
                    return Err(ValidationError::MissingCallTarget {
                        function: function.id,
                        pc,
                        target: *target,
                    });
                };
                if usize::from(callee.arity) != args.len() {
                    return Err(ValidationError::CallArity {
                        function: function.id,
                        pc,
                        target: *target,
                        expected: callee.arity,
                        actual: args.len(),
                    });
                }
                validate_call_ownership(
                    function,
                    pc,
                    *target,
                    args,
                    argument_ownership,
                    &callee.parameter_ownership,
                )?;
                if *result_ownership != callee.result_ownership {
                    return Err(ValidationError::CallResultOwnershipContract {
                        function: function.id,
                        pc,
                        target: *target,
                        expected: callee.result_ownership,
                        actual: *result_ownership,
                    });
                }
            }
            Instruction::Closure {
                function: target,
                captures,
                capture_ownership,
                ..
            } => {
                let Some(callee) = target.index().and_then(|i| program.functions.get(i)) else {
                    return Err(ValidationError::MissingClosureTarget {
                        function: function.id,
                        pc,
                        target: *target,
                    });
                };
                if captures.len() >= usize::from(callee.arity) {
                    return Err(ValidationError::ClosureCaptureArity {
                        function: function.id,
                        pc,
                        target: *target,
                        target_arity: callee.arity,
                        captures: captures.len(),
                    });
                }
                validate_closure_ownership(
                    function,
                    pc,
                    *target,
                    captures,
                    capture_ownership,
                    &callee.parameter_ownership[..captures.len()],
                )?;
                if callee.arity.checked_add(1).is_none() {
                    return Err(ValidationError::ClosureArityOverflow {
                        function: function.id,
                        pc,
                        target: *target,
                        target_arity: callee.arity,
                    });
                }
            }
            Instruction::Apply {
                closure,
                args,
                argument_ownership,
                ..
            } => {
                if args.is_empty() {
                    return Err(ValidationError::EmptyApply {
                        function: function.id,
                        pc,
                    });
                }
                validate_apply_ownership(function, pc, *closure, args, argument_ownership)?;
            }
            Instruction::Intrinsic {
                row,
                args,
                argument_ownership,
                ..
            } => {
                if !valid_extern_row(row) {
                    return Err(ValidationError::InvalidExternRow {
                        function: function.id,
                        pc,
                        row: row.clone(),
                    });
                }
                validate_intrinsic_ownership(function, pc, args, argument_ownership)?;
            }
            Instruction::Nat { value, .. } => {
                let max_small = (usize::MAX >> 1) as u64;
                if *value > max_small {
                    return Err(ValidationError::NatConstantOutOfRange {
                        function: function.id,
                        pc,
                        value: *value,
                    });
                }
            }
            Instruction::Ctor {
                tag,
                fields,
                scalar_bytes,
                ..
            } => {
                if *tag > abi::TAG_MAX_CTOR_TAG {
                    return Err(ValidationError::CtorTagOutOfRange {
                        function: function.id,
                        pc,
                        tag: *tag,
                    });
                }
                if fields.len() >= abi::MAX_CTOR_FIELDS {
                    return Err(ValidationError::TooManyCtorFields {
                        function: function.id,
                        pc,
                        count: fields.len(),
                    });
                }
                if scalar_bytes.len() >= abi::MAX_CTOR_SCALARS_SIZE {
                    return Err(ValidationError::TooManyCtorScalarBytes {
                        function: function.id,
                        pc,
                        count: scalar_bytes.len(),
                    });
                }
            }
            Instruction::CtorField {
                expected_tag,
                expected_fields,
                field,
                ..
            } => {
                if *expected_tag > abi::TAG_MAX_CTOR_TAG {
                    return Err(ValidationError::CtorTagOutOfRange {
                        function: function.id,
                        pc,
                        tag: *expected_tag,
                    });
                }
                if usize::from(*expected_fields) >= abi::MAX_CTOR_FIELDS {
                    return Err(ValidationError::CtorFieldShapeOutOfRange {
                        function: function.id,
                        pc,
                        expected_fields: *expected_fields,
                    });
                }
                if *field >= *expected_fields {
                    return Err(ValidationError::CtorFieldOutOfBounds {
                        function: function.id,
                        pc,
                        expected_fields: *expected_fields,
                        field: *field,
                    });
                }
            }
            Instruction::String { .. }
            | Instruction::Copy { .. }
            | Instruction::Move { .. }
            | Instruction::Drop { .. }
            | Instruction::Array { .. }
            | Instruction::CheckSystem { .. }
            | Instruction::CheckSystemValue { .. }
            | Instruction::Return { .. }
            | Instruction::Panic { .. } => {}
        }
    }

    validate_definite_initialization(function)
}

fn check_register(function: &Function, pc: Pc, register: Register) -> Result<(), ValidationError> {
    if register.get() >= function.register_count {
        return Err(ValidationError::RegisterOutOfBounds {
            function: function.id,
            pc,
            register,
            register_count: function.register_count,
        });
    }
    Ok(())
}

fn check_target(function: &Function, pc: Pc, target: Pc) -> Result<(), ValidationError> {
    if target
        .index()
        .is_none_or(|index| index >= function.code.len())
    {
        return Err(ValidationError::JumpOutOfBounds {
            function: function.id,
            pc,
            target,
            instruction_count: function.code.len(),
        });
    }
    Ok(())
}

fn valid_extern_row(row: &str) -> bool {
    row.strip_prefix("extern:").is_some_and(|name| {
        !name.is_empty() && !name.bytes().any(|byte| byte.is_ascii_whitespace())
    })
}

#[derive(Clone, Copy)]
struct SeenArgument {
    first: usize,
    consuming: Option<usize>,
    unique: Option<usize>,
}

#[derive(Clone, Copy)]
enum ArgumentAliasError {
    Consume {
        register: Register,
        first: usize,
        second: usize,
    },
    Unique {
        register: Register,
        unique: usize,
        alias: usize,
    },
}

fn validate_argument_aliases(
    register_count: u16,
    args: &[Register],
    ownership: &[ArgumentOwnership],
) -> Result<(), ArgumentAliasError> {
    let mut seen = vec![None::<SeenArgument>; usize::from(register_count)];
    for (argument, (register, disposition)) in args
        .iter()
        .copied()
        .zip(ownership.iter().copied())
        .enumerate()
    {
        let slot = &mut seen[register.index()];
        let Some(previous) = slot.as_mut() else {
            *slot = Some(SeenArgument {
                first: argument,
                consuming: disposition.consumes().then_some(argument),
                unique: (disposition == ArgumentOwnership::Unique).then_some(argument),
            });
            continue;
        };
        if disposition == ArgumentOwnership::Unique {
            return Err(ArgumentAliasError::Unique {
                register,
                unique: argument,
                alias: previous.first,
            });
        }
        if let Some(unique) = previous.unique {
            return Err(ArgumentAliasError::Unique {
                register,
                unique,
                alias: argument,
            });
        }
        if disposition.consumes() {
            if let Some(first) = previous.consuming {
                return Err(ArgumentAliasError::Consume {
                    register,
                    first,
                    second: argument,
                });
            }
            previous.consuming = Some(argument);
        }
    }
    Ok(())
}

fn validate_intrinsic_ownership(
    function: &Function,
    pc: Pc,
    args: &[Register],
    ownership: &[ArgumentOwnership],
) -> Result<(), ValidationError> {
    if args.len() != ownership.len() {
        return Err(ValidationError::IntrinsicOwnershipArity {
            function: function.id,
            pc,
            arguments: args.len(),
            ownership: ownership.len(),
        });
    }
    match validate_argument_aliases(function.register_count, args, ownership) {
        Ok(()) => Ok(()),
        Err(ArgumentAliasError::Consume {
            register,
            first,
            second,
        }) => Err(ValidationError::IntrinsicConsumeAlias {
            function: function.id,
            pc,
            register,
            first,
            second,
        }),
        Err(ArgumentAliasError::Unique {
            register,
            unique,
            alias,
        }) => Err(ValidationError::IntrinsicUniqueAlias {
            function: function.id,
            pc,
            register,
            unique,
            alias,
        }),
    }
}

fn validate_call_ownership(
    function: &Function,
    pc: Pc,
    target: FunctionId,
    args: &[Register],
    ownership: &[ArgumentOwnership],
    expected: &[ArgumentOwnership],
) -> Result<(), ValidationError> {
    if args.len() != ownership.len() {
        return Err(ValidationError::CallOwnershipArity {
            function: function.id,
            pc,
            target,
            arguments: args.len(),
            ownership: ownership.len(),
        });
    }
    if let Some((argument, (actual, expected))) = ownership
        .iter()
        .copied()
        .zip(expected.iter().copied())
        .enumerate()
        .find(|(_, (actual, expected))| actual != expected)
    {
        return Err(ValidationError::CallOwnershipContract {
            function: function.id,
            pc,
            target,
            argument,
            expected,
            actual,
        });
    }
    match validate_argument_aliases(function.register_count, args, ownership) {
        Ok(()) => Ok(()),
        Err(ArgumentAliasError::Consume {
            register,
            first,
            second,
        }) => Err(ValidationError::CallConsumeAlias {
            function: function.id,
            pc,
            target,
            register,
            first,
            second,
        }),
        Err(ArgumentAliasError::Unique {
            register,
            unique,
            alias,
        }) => Err(ValidationError::CallUniqueAlias {
            function: function.id,
            pc,
            target,
            register,
            unique,
            alias,
        }),
    }
}

fn validate_closure_ownership(
    function: &Function,
    pc: Pc,
    target: FunctionId,
    captures: &[Register],
    ownership: &[ArgumentOwnership],
    expected: &[ArgumentOwnership],
) -> Result<(), ValidationError> {
    if captures.len() != ownership.len() {
        return Err(ValidationError::ClosureOwnershipArity {
            function: function.id,
            pc,
            target,
            captures: captures.len(),
            ownership: ownership.len(),
        });
    }
    if let Some((capture, (actual, expected))) = ownership
        .iter()
        .copied()
        .zip(expected.iter().copied())
        .enumerate()
        .find(|(_, (actual, expected))| actual != expected)
    {
        return Err(ValidationError::ClosureOwnershipContract {
            function: function.id,
            pc,
            target,
            capture,
            expected,
            actual,
        });
    }
    if let Some(capture) = ownership
        .iter()
        .position(|disposition| *disposition == ArgumentOwnership::Unique)
    {
        return Err(ValidationError::ClosureUniqueCapture {
            function: function.id,
            pc,
            target,
            capture,
            register: captures[capture],
        });
    }
    match validate_argument_aliases(function.register_count, captures, ownership) {
        Ok(()) => Ok(()),
        Err(ArgumentAliasError::Consume {
            register,
            first,
            second,
        }) => Err(ValidationError::ClosureConsumeAlias {
            function: function.id,
            pc,
            target,
            register,
            first,
            second,
        }),
        Err(ArgumentAliasError::Unique {
            register, unique, ..
        }) => Err(ValidationError::ClosureUniqueCapture {
            function: function.id,
            pc,
            target,
            capture: unique,
            register,
        }),
    }
}

fn validate_apply_ownership(
    function: &Function,
    pc: Pc,
    closure: Register,
    args: &[Register],
    ownership: &[ArgumentOwnership],
) -> Result<(), ValidationError> {
    if args.len() != ownership.len() {
        return Err(ValidationError::ApplyOwnershipArity {
            function: function.id,
            pc,
            arguments: args.len(),
            ownership: ownership.len(),
        });
    }
    match validate_argument_aliases(function.register_count, args, ownership) {
        Ok(()) => {}
        Err(ArgumentAliasError::Consume {
            register,
            first,
            second,
        }) => {
            return Err(ValidationError::ApplyConsumeAlias {
                function: function.id,
                pc,
                register,
                first,
                second,
            });
        }
        Err(ArgumentAliasError::Unique {
            register,
            unique,
            alias,
        }) => {
            return Err(ValidationError::ApplyUniqueAlias {
                function: function.id,
                pc,
                register,
                unique,
                alias,
            });
        }
    }
    if let Some(unique) = args
        .iter()
        .zip(ownership)
        .position(|(register, disposition)| {
            *register == closure && *disposition == ArgumentOwnership::Unique
        })
    {
        return Err(ValidationError::ApplyUniqueClosureAlias {
            function: function.id,
            pc,
            register: closure,
            unique,
        });
    }
    Ok(())
}

fn validate_definite_initialization(function: &Function) -> Result<(), ValidationError> {
    let mut incoming = vec![None::<Vec<bool>>; function.code.len()];
    let mut entry = vec![false; usize::from(function.register_count)];
    entry[..usize::from(function.arity)].fill(true);
    incoming[0] = Some(entry);

    let mut queue = VecDeque::from([0usize]);
    while let Some(offset) = queue.pop_front() {
        let pc = Pc::new(u32::try_from(offset).expect("instruction count checked"));
        let mut state = incoming[offset]
            .clone()
            .expect("the work queue contains only reached instructions");
        let instruction = &function.code[offset];
        for register in instruction.read_registers() {
            if !state[register.index()] {
                return Err(ValidationError::ReadBeforeWrite {
                    function: function.id,
                    pc,
                    register,
                });
            }
        }

        match instruction {
            Instruction::Move { dst, src } if dst != src => {
                state[src.index()] = false;
                state[dst.index()] = true;
            }
            Instruction::Drop { src } => state[src.index()] = false,
            Instruction::Intrinsic { dst, .. }
            | Instruction::Call { dst, .. }
            | Instruction::Closure { dst, .. }
            | Instruction::Apply { dst, .. } => {
                ownership_consumes(instruction, |register| {
                    state[register.index()] = false;
                    Ok::<(), ValidationError>(())
                })?;
                state[dst.index()] = true;
            }
            _ => {
                if let Some(dst) = instruction.written_register() {
                    state[dst.index()] = true;
                }
            }
        }

        let mut successors = [None, None];
        match instruction {
            Instruction::Jump { target } => successors[0] = target.index(),
            Instruction::JumpIfZero { zero, nonzero, .. } => {
                successors[0] = zero.index();
                successors[1] = nonzero.index();
            }
            Instruction::Return { .. } | Instruction::Panic { .. } => {}
            _ => {
                let next = offset + 1;
                if next == function.code.len() {
                    return Err(ValidationError::Fallthrough {
                        function: function.id,
                        pc,
                    });
                }
                successors[0] = Some(next);
            }
        }

        for successor in successors.into_iter().flatten() {
            let changed = match &mut incoming[successor] {
                None => {
                    incoming[successor] = Some(state.clone());
                    true
                }
                Some(existing) => {
                    let mut changed = false;
                    for (known, arriving) in existing.iter_mut().zip(&state) {
                        let merged = *known && *arriving;
                        changed |= merged != *known;
                        *known = merged;
                    }
                    changed
                }
            };
            if changed {
                queue.push_back(successor);
            }
        }
    }

    if let Some((offset, _)) = incoming
        .iter()
        .enumerate()
        .find(|(_, state)| state.is_none())
    {
        return Err(ValidationError::UnreachableInstruction {
            function: function.id,
            pc: Pc::new(u32::try_from(offset).expect("instruction count checked")),
        });
    }
    Ok(())
}

fn ownership_reads<E>(
    instruction: &Instruction,
    mut visit: impl FnMut(Register) -> Result<(), E>,
) -> Result<(), E> {
    match instruction {
        Instruction::Nat { .. }
        | Instruction::String { .. }
        | Instruction::Jump { .. }
        | Instruction::CheckSystem { .. } => {}
        Instruction::Copy { src, .. }
        | Instruction::Move { src, .. }
        | Instruction::Drop { src }
        | Instruction::CtorField { src, .. }
        | Instruction::CheckSystemValue { module_name: src } => visit(*src)?,
        Instruction::Ctor { fields, .. } => {
            for register in fields {
                visit(*register)?;
            }
        }
        Instruction::Array { items, .. } => {
            for register in items {
                visit(*register)?;
            }
        }
        Instruction::Intrinsic { args, .. } | Instruction::Call { args, .. } => {
            for register in args {
                visit(*register)?;
            }
        }
        Instruction::Closure { captures, .. } => {
            for register in captures {
                visit(*register)?;
            }
        }
        Instruction::Apply { closure, args, .. } => {
            visit(*closure)?;
            for register in args {
                visit(*register)?;
            }
        }
        Instruction::JumpIfZero { cond, .. } => visit(*cond)?,
        Instruction::Return { src } => visit(*src)?,
        Instruction::Panic { message } => visit(*message)?,
    }
    Ok(())
}

fn ownership_consumes<E>(
    instruction: &Instruction,
    mut visit: impl FnMut(Register) -> Result<(), E>,
) -> Result<(), E> {
    match instruction {
        Instruction::Intrinsic {
            args,
            argument_ownership,
            ..
        }
        | Instruction::Call {
            args,
            argument_ownership,
            ..
        }
        | Instruction::Apply {
            args,
            argument_ownership,
            ..
        } => {
            for (register, disposition) in args.iter().zip(argument_ownership) {
                if disposition.consumes() {
                    visit(*register)?;
                }
            }
        }
        Instruction::Closure {
            captures,
            capture_ownership,
            ..
        } => {
            for (register, disposition) in captures.iter().zip(capture_ownership) {
                if disposition.consumes() {
                    visit(*register)?;
                }
            }
        }
        _ => {}
    }
    Ok(())
}

fn ownership_consumes_register(instruction: &Instruction, raw: usize) -> bool {
    let mut consumes = false;
    let _ = ownership_consumes(instruction, |register| {
        consumes |= register.index() == raw;
        Ok::<(), ()>(())
    });
    consumes
}

fn consumed_extern_argument_count(instruction: &Instruction) -> usize {
    match instruction {
        Instruction::Intrinsic {
            argument_ownership, ..
        } => argument_ownership
            .iter()
            .filter(|disposition| disposition.consumes())
            .count(),
        _ => 0,
    }
}

fn consumed_call_argument_count(instruction: &Instruction) -> usize {
    match instruction {
        Instruction::Call {
            argument_ownership, ..
        } => argument_ownership
            .iter()
            .filter(|disposition| disposition.consumes())
            .count(),
        _ => 0,
    }
}

fn consumed_closure_capture_count(instruction: &Instruction) -> usize {
    match instruction {
        Instruction::Closure {
            capture_ownership, ..
        } => capture_ownership
            .iter()
            .filter(|disposition| disposition.consumes())
            .count(),
        _ => 0,
    }
}

fn consumed_apply_argument_count(instruction: &Instruction) -> usize {
    match instruction {
        Instruction::Apply {
            argument_ownership, ..
        } => argument_ownership
            .iter()
            .filter(|disposition| disposition.consumes())
            .count(),
        _ => 0,
    }
}

fn borrowed_intrinsic_result_count(instruction: &Instruction) -> usize {
    usize::from(matches!(
        instruction,
        Instruction::Intrinsic {
            result_ownership: ResultOwnership::Borrowed,
            ..
        }
    ))
}

fn raw_intrinsic_result_count(instruction: &Instruction) -> usize {
    usize::from(matches!(
        instruction,
        Instruction::Intrinsic {
            result_ownership: ResultOwnership::RawObject,
            ..
        }
    ))
}

fn owned_callable_result_count(instruction: &Instruction) -> usize {
    usize::from(matches!(
        instruction,
        Instruction::Call {
            result_ownership: CallableResultOwnership::Owned,
            ..
        } | Instruction::Apply {
            result_ownership: CallableResultOwnership::Owned,
            ..
        }
    ))
}

fn scalar_callable_result_count(instruction: &Instruction) -> usize {
    usize::from(matches!(
        instruction,
        Instruction::Call {
            result_ownership: CallableResultOwnership::Scalar,
            ..
        } | Instruction::Apply {
            result_ownership: CallableResultOwnership::Scalar,
            ..
        }
    ))
}

fn ownership_operand_count(instruction: &Instruction) -> usize {
    match instruction {
        Instruction::Nat { .. }
        | Instruction::String { .. }
        | Instruction::Jump { .. }
        | Instruction::CheckSystem { .. } => 0,
        Instruction::Copy { .. }
        | Instruction::Move { .. }
        | Instruction::Drop { .. }
        | Instruction::CtorField { .. }
        | Instruction::CheckSystemValue { .. }
        | Instruction::JumpIfZero { .. }
        | Instruction::Return { .. }
        | Instruction::Panic { .. } => 1,
        Instruction::Ctor { fields, .. } => fields.len(),
        Instruction::Array { items, .. } => items.len(),
        Instruction::Intrinsic {
            args,
            argument_ownership,
            ..
        } => args
            .len()
            .saturating_add(argument_ownership.len())
            .saturating_add(1),
        Instruction::Call {
            args,
            argument_ownership,
            ..
        } => args
            .len()
            .saturating_add(argument_ownership.len())
            .saturating_add(1),
        Instruction::Closure {
            captures,
            capture_ownership,
            ..
        } => captures.len().saturating_add(capture_ownership.len()),
        Instruction::Apply {
            args,
            argument_ownership,
            ..
        } => args
            .len()
            .saturating_add(argument_ownership.len())
            .saturating_add(2),
    }
}

fn ownership_operand_total(function: &Function) -> usize {
    function.code.iter().map(ownership_operand_count).fold(
        function.parameter_ownership.len().saturating_add(1),
        usize::saturating_add,
    )
}

fn ownership_cfg_edge_count(instruction: &Instruction) -> usize {
    match instruction {
        Instruction::Return { .. } | Instruction::Panic { .. } => 0,
        Instruction::JumpIfZero { .. } => 2,
        _ => 1,
    }
}

fn ownership_payload_bytes(instruction: &Instruction) -> usize {
    match instruction {
        Instruction::String { value, .. } => value.len(),
        Instruction::Ctor { scalar_bytes, .. } => scalar_bytes.len(),
        Instruction::Intrinsic { row, .. } => row.len(),
        Instruction::CheckSystem { module_name } => module_name.len(),
        Instruction::Nat { .. }
        | Instruction::Copy { .. }
        | Instruction::Move { .. }
        | Instruction::Drop { .. }
        | Instruction::CtorField { .. }
        | Instruction::Array { .. }
        | Instruction::Call { .. }
        | Instruction::Closure { .. }
        | Instruction::Apply { .. }
        | Instruction::Jump { .. }
        | Instruction::JumpIfZero { .. }
        | Instruction::CheckSystemValue { .. }
        | Instruction::Return { .. }
        | Instruction::Panic { .. } => 0,
    }
}

fn ownership_terminal(instruction: &Instruction) -> Option<Register> {
    match instruction {
        Instruction::Return { src } => Some(*src),
        Instruction::Panic { message } => Some(*message),
        _ => None,
    }
}

fn ownership_add(
    resource: OwnershipResource,
    total: &mut usize,
    additional: usize,
    limit: usize,
) -> Result<(), OwnershipError> {
    let observed = total.checked_add(additional).unwrap_or(usize::MAX);
    if observed > limit {
        return Err(OwnershipError::ResourceLimit {
            resource,
            limit,
            observed,
        });
    }
    *total = observed;
    Ok(())
}

fn check_ownership_program_limits(
    program: &ValidatedProgram,
    limits: OwnershipLimits,
    emitted: bool,
) -> Result<(), OwnershipError> {
    if program.functions().len() > limits.max_functions {
        return Err(OwnershipError::ResourceLimit {
            resource: OwnershipResource::Functions,
            limit: limits.max_functions,
            observed: program.functions().len(),
        });
    }
    let mut instructions = 0usize;
    let mut registers = 0usize;
    let mut operands = 0usize;
    let mut payload_bytes = 0usize;
    let mut cfg_edges = 0usize;
    for function in program.functions() {
        ownership_add(
            if emitted {
                OwnershipResource::EmittedInstructions
            } else {
                OwnershipResource::SourceInstructions
            },
            &mut instructions,
            function.code.len(),
            if emitted {
                limits.max_emitted_instructions
            } else {
                limits.max_source_instructions
            },
        )?;
        ownership_add(
            OwnershipResource::Registers,
            &mut registers,
            usize::from(function.register_count),
            limits.max_registers,
        )?;
        ownership_add(
            OwnershipResource::Operands,
            &mut operands,
            function.parameter_ownership.len(),
            limits.max_operands,
        )?;
        for instruction in &function.code {
            ownership_add(
                OwnershipResource::Operands,
                &mut operands,
                ownership_operand_count(instruction),
                limits.max_operands,
            )?;
            ownership_add(
                OwnershipResource::PayloadBytes,
                &mut payload_bytes,
                ownership_payload_bytes(instruction),
                limits.max_payload_bytes,
            )?;
            ownership_add(
                OwnershipResource::CfgEdges,
                &mut cfg_edges,
                ownership_cfg_edge_count(instruction),
                limits.max_cfg_edges,
            )?;
        }
    }
    Ok(())
}

fn ownership_vec<T>(len: usize, resource: OwnershipResource) -> Result<Vec<T>, OwnershipError> {
    let mut values = Vec::new();
    values
        .try_reserve_exact(len)
        .map_err(|_| OwnershipError::AllocationFailure {
            resource,
            requested: len,
        })?;
    Ok(values)
}

fn ownership_clone_copy<T: Copy>(
    source: &[T],
    resource: OwnershipResource,
) -> Result<Vec<T>, OwnershipError> {
    let mut copy = ownership_vec(source.len(), resource)?;
    copy.extend_from_slice(source);
    Ok(copy)
}

fn ownership_clone_string(source: &str) -> Result<String, OwnershipError> {
    let mut copy = String::new();
    copy.try_reserve_exact(source.len())
        .map_err(|_| OwnershipError::AllocationFailure {
            resource: OwnershipResource::PayloadBytes,
            requested: source.len(),
        })?;
    copy.push_str(source);
    Ok(copy)
}

fn ownership_clone_instruction(instruction: &Instruction) -> Result<Instruction, OwnershipError> {
    Ok(match instruction {
        Instruction::Nat { dst, value } => Instruction::Nat {
            dst: *dst,
            value: *value,
        },
        Instruction::String { dst, value } => Instruction::String {
            dst: *dst,
            value: ownership_clone_string(value)?,
        },
        Instruction::Copy { dst, src } => Instruction::Copy {
            dst: *dst,
            src: *src,
        },
        Instruction::Move { dst, src } => Instruction::Move {
            dst: *dst,
            src: *src,
        },
        Instruction::Drop { src } => Instruction::Drop { src: *src },
        Instruction::Ctor {
            dst,
            tag,
            fields,
            scalar_bytes,
        } => Instruction::Ctor {
            dst: *dst,
            tag: *tag,
            fields: ownership_clone_copy(fields, OwnershipResource::Operands)?,
            scalar_bytes: ownership_clone_copy(scalar_bytes, OwnershipResource::PayloadBytes)?,
        },
        Instruction::CtorField {
            dst,
            src,
            expected_tag,
            expected_fields,
            field,
        } => Instruction::CtorField {
            dst: *dst,
            src: *src,
            expected_tag: *expected_tag,
            expected_fields: *expected_fields,
            field: *field,
        },
        Instruction::Array { dst, items } => Instruction::Array {
            dst: *dst,
            items: ownership_clone_copy(items, OwnershipResource::Operands)?,
        },
        Instruction::Intrinsic {
            dst,
            row,
            args,
            argument_ownership,
            result_ownership,
        } => Instruction::Intrinsic {
            dst: *dst,
            row: ownership_clone_string(row)?,
            args: ownership_clone_copy(args, OwnershipResource::Operands)?,
            argument_ownership: ownership_clone_copy(
                argument_ownership,
                OwnershipResource::Operands,
            )?,
            result_ownership: *result_ownership,
        },
        Instruction::Call {
            dst,
            function,
            args,
            argument_ownership,
            result_ownership,
        } => Instruction::Call {
            dst: *dst,
            function: *function,
            args: ownership_clone_copy(args, OwnershipResource::Operands)?,
            argument_ownership: ownership_clone_copy(
                argument_ownership,
                OwnershipResource::Operands,
            )?,
            result_ownership: *result_ownership,
        },
        Instruction::Closure {
            dst,
            function,
            captures,
            capture_ownership,
        } => Instruction::Closure {
            dst: *dst,
            function: *function,
            captures: ownership_clone_copy(captures, OwnershipResource::Operands)?,
            capture_ownership: ownership_clone_copy(
                capture_ownership,
                OwnershipResource::Operands,
            )?,
        },
        Instruction::Apply {
            dst,
            closure,
            args,
            argument_ownership,
            result_ownership,
        } => Instruction::Apply {
            dst: *dst,
            closure: *closure,
            args: ownership_clone_copy(args, OwnershipResource::Operands)?,
            argument_ownership: ownership_clone_copy(
                argument_ownership,
                OwnershipResource::Operands,
            )?,
            result_ownership: *result_ownership,
        },
        Instruction::Jump { target } => Instruction::Jump { target: *target },
        Instruction::JumpIfZero {
            cond,
            zero,
            nonzero,
        } => Instruction::JumpIfZero {
            cond: *cond,
            zero: *zero,
            nonzero: *nonzero,
        },
        Instruction::CheckSystem { module_name } => Instruction::CheckSystem {
            module_name: ownership_clone_string(module_name)?,
        },
        Instruction::CheckSystemValue { module_name } => Instruction::CheckSystemValue {
            module_name: *module_name,
        },
        Instruction::Return { src } => Instruction::Return { src: *src },
        Instruction::Panic { message } => Instruction::Panic { message: *message },
    })
}

fn ownership_is_control(instruction: &Instruction) -> bool {
    matches!(
        instruction,
        Instruction::Jump { .. } | Instruction::JumpIfZero { .. }
    )
}

fn ownership_successors(function: &Function, offset: usize) -> [Option<usize>; 2] {
    match &function.code[offset] {
        Instruction::Jump { target } => [target.index(), None],
        Instruction::JumpIfZero { zero, nonzero, .. } => [zero.index(), nonzero.index()],
        Instruction::Return { .. } | Instruction::Panic { .. } => [None, None],
        _ => [offset.checked_add(1), None],
    }
}

fn insertion_topological_order(function: &Function) -> Result<Option<Vec<usize>>, OwnershipError> {
    let instruction_count = function.code.len();
    let mut indegree = ownership_vec(instruction_count, OwnershipResource::CfgEdges)?;
    indegree.resize(instruction_count, 0usize);
    for offset in 0..instruction_count {
        for successor in ownership_successors(function, offset).into_iter().flatten() {
            indegree[successor] = indegree[successor].saturating_add(1);
        }
    }

    let mut queue = VecDeque::new();
    queue
        .try_reserve(instruction_count)
        .map_err(|_| OwnershipError::AllocationFailure {
            resource: OwnershipResource::SourceInstructions,
            requested: instruction_count,
        })?;
    for (offset, incoming) in indegree.iter().enumerate() {
        if *incoming == 0 {
            queue.push_back(offset);
        }
    }

    let mut order = ownership_vec(instruction_count, OwnershipResource::SourceInstructions)?;
    while let Some(offset) = queue.pop_front() {
        order.push(offset);
        for successor in ownership_successors(function, offset).into_iter().flatten() {
            indegree[successor] = indegree[successor].saturating_sub(1);
            if indegree[successor] == 0 {
                queue.push_back(successor);
            }
        }
    }
    Ok((order.len() == instruction_count).then_some(order))
}

fn validation_is_acyclic(function: &Function) -> Result<bool, OwnershipError> {
    let instruction_count = function.code.len();
    let mut colors = ownership_vec(instruction_count, OwnershipResource::ValidationCells)?;
    colors.resize(instruction_count, 0u8);
    let mut stack = ownership_vec(instruction_count, OwnershipResource::ValidationCells)?;

    for start in 0..instruction_count {
        if colors[start] != 0 {
            continue;
        }
        colors[start] = 1;
        stack.push((start, 0u8));
        while let Some((offset, next_edge)) = stack.last_mut() {
            if usize::from(*next_edge) == 2 {
                colors[*offset] = 2;
                stack.pop();
                continue;
            }
            let edge = usize::from(*next_edge);
            *next_edge = next_edge.saturating_add(1);
            let Some(successor) = ownership_successors(function, *offset)[edge] else {
                continue;
            };
            match colors[successor] {
                0 => {
                    colors[successor] = 1;
                    stack.push((successor, 0));
                }
                1 => return Ok(false),
                _ => {}
            }
        }
    }
    Ok(true)
}

struct InsertionClassification {
    mode: OwnershipMode,
    topological: Option<Vec<usize>>,
    redefinitions: usize,
}

fn insertion_classification(
    function: &Function,
) -> Result<InsertionClassification, OwnershipError> {
    if function.code.iter().any(|instruction| {
        matches!(
            instruction,
            Instruction::Move { .. } | Instruction::Drop { .. }
        )
    }) {
        return Ok(InsertionClassification {
            mode: OwnershipMode::ValidatedExistingOwnership,
            topological: None,
            redefinitions: 0,
        });
    }

    let has_control = function.code.iter().any(ownership_is_control);
    let register_count = usize::from(function.register_count);
    let mut defined = ownership_vec(register_count, OwnershipResource::Registers)?;
    defined.resize(register_count, false);
    defined[..usize::from(function.arity)].fill(true);
    let mut redefinitions = 0usize;
    let mut unsupported_overlap = false;
    for instruction in &function.code {
        if let Some(dst) = instruction.written_register() {
            if defined[dst.index()] {
                redefinitions = redefinitions.saturating_add(1);
                let mut reads_destination = false;
                ownership_reads(instruction, |register| {
                    reads_destination |= register == dst;
                    Ok::<(), OwnershipError>(())
                })?;
                let self_copy = matches!(
                    instruction,
                    Instruction::Copy {
                        dst: copy_dst,
                        src,
                    } if copy_dst == src
                );
                unsupported_overlap |= reads_destination
                    && !self_copy
                    && !ownership_consumes_register(instruction, dst.index());
            }
            defined[dst.index()] = true;
        }
    }
    if redefinitions != 0 {
        if unsupported_overlap {
            return Ok(InsertionClassification {
                mode: OwnershipMode::PreservedNonSsa,
                topological: None,
                redefinitions: 0,
            });
        }
        if !has_control {
            return Ok(InsertionClassification {
                mode: OwnershipMode::InsertedLinearReuse,
                topological: None,
                redefinitions,
            });
        }
        return Ok(match insertion_topological_order(function)? {
            Some(topological) => InsertionClassification {
                mode: OwnershipMode::InsertedAcyclicCfgReuse,
                topological: Some(topological),
                redefinitions,
            },
            None => InsertionClassification {
                mode: OwnershipMode::InsertedCyclicCfgReuse,
                topological: None,
                redefinitions,
            },
        });
    }
    if !has_control {
        return Ok(InsertionClassification {
            mode: OwnershipMode::InsertedLinear,
            topological: None,
            redefinitions: 0,
        });
    }
    let topological = insertion_topological_order(function)?;
    Ok(match topological {
        Some(topological) => InsertionClassification {
            mode: OwnershipMode::InsertedAcyclicCfg,
            topological: Some(topological),
            redefinitions: 0,
        },
        None => InsertionClassification {
            mode: OwnershipMode::InsertedCyclicCfg,
            topological: None,
            redefinitions: 0,
        },
    })
}

fn validation_mode(function: &Function) -> Result<OwnershipMode, OwnershipError> {
    let mut saw_ownership = false;
    for instruction in &function.code {
        saw_ownership |= matches!(
            instruction,
            Instruction::Move { .. } | Instruction::Drop { .. }
        );
    }
    if saw_ownership {
        return Ok(OwnershipMode::ValidatedExistingOwnership);
    }

    let register_count = usize::from(function.register_count);
    let mut definition = ownership_vec(register_count, OwnershipResource::Registers)?;
    definition.resize(register_count, None::<usize>);
    definition[..usize::from(function.arity)].fill(Some(0));
    let has_control = function.code.iter().any(ownership_is_control);
    let mut redefinitions = 0usize;
    let mut unsupported_overlap = false;
    for (offset, instruction) in function.code.iter().enumerate() {
        if let Some(dst) = instruction.written_register()
            && definition[dst.index()]
                .replace(offset.saturating_add(1))
                .is_some()
        {
            redefinitions = redefinitions.saturating_add(1);
            unsupported_overlap |= ownership_reads_register(instruction, dst.index())
                && !matches!(
                    instruction,
                    Instruction::Copy {
                        dst: copy_dst,
                        src,
                    } if copy_dst == src
                )
                && !ownership_consumes_register(instruction, dst.index());
        }
    }
    if redefinitions != 0 {
        if unsupported_overlap {
            return Ok(OwnershipMode::PreservedNonSsa);
        }
        if !has_control {
            return Ok(OwnershipMode::InsertedLinearReuse);
        }
        return if validation_is_acyclic(function)? {
            Ok(OwnershipMode::InsertedAcyclicCfgReuse)
        } else {
            Ok(OwnershipMode::InsertedCyclicCfgReuse)
        };
    }
    if !has_control {
        return Ok(OwnershipMode::InsertedLinear);
    }
    if validation_is_acyclic(function)? {
        Ok(OwnershipMode::InsertedAcyclicCfg)
    } else {
        Ok(OwnershipMode::InsertedCyclicCfg)
    }
}

fn emit_ownership_instruction(
    code: &mut Vec<Instruction>,
    instruction: Instruction,
    total_emitted: &mut usize,
    limits: OwnershipLimits,
) -> Result<(), OwnershipError> {
    ownership_add(
        OwnershipResource::EmittedInstructions,
        total_emitted,
        1,
        limits.max_emitted_instructions,
    )?;
    code.push(instruction);
    Ok(())
}

fn clone_preserved_function(
    source: &Function,
    mode: OwnershipMode,
    total_emitted: &mut usize,
    limits: OwnershipLimits,
) -> Result<(Function, OwnershipFunctionWitness), OwnershipError> {
    let mut code = ownership_vec(source.code.len(), OwnershipResource::EmittedInstructions)?;
    let mut existing_drops = 0usize;
    let mut existing_moves = 0usize;
    let mut consumed_extern_args = 0usize;
    let mut consumed_call_args = 0usize;
    let mut consumed_closure_captures = 0usize;
    let mut consumed_apply_args = 0usize;
    let mut borrowed_intrinsic_results = 0usize;
    let mut raw_intrinsic_results = 0usize;
    for instruction in &source.code {
        match instruction {
            Instruction::Drop { .. } => {
                existing_drops = existing_drops.saturating_add(1);
            }
            Instruction::Move { .. } => {
                existing_moves = existing_moves.saturating_add(1);
            }
            _ => {}
        }
        consumed_extern_args =
            consumed_extern_args.saturating_add(consumed_extern_argument_count(instruction));
        consumed_call_args =
            consumed_call_args.saturating_add(consumed_call_argument_count(instruction));
        consumed_closure_captures =
            consumed_closure_captures.saturating_add(consumed_closure_capture_count(instruction));
        consumed_apply_args =
            consumed_apply_args.saturating_add(consumed_apply_argument_count(instruction));
        borrowed_intrinsic_results =
            borrowed_intrinsic_results.saturating_add(borrowed_intrinsic_result_count(instruction));
        raw_intrinsic_results =
            raw_intrinsic_results.saturating_add(raw_intrinsic_result_count(instruction));
        emit_ownership_instruction(
            &mut code,
            ownership_clone_instruction(instruction)?,
            total_emitted,
            limits,
        )?;
    }
    let owned_callable_results = code.iter().map(owned_callable_result_count).sum();
    let scalar_callable_results = code.iter().map(scalar_callable_result_count).sum();
    let emitted_instructions = code.len();
    Ok((
        Function {
            id: source.id,
            arity: source.arity,
            parameter_ownership: ownership_clone_copy(
                &source.parameter_ownership,
                OwnershipResource::Operands,
            )?,
            result_ownership: source.result_ownership,
            register_count: source.register_count,
            code,
        },
        OwnershipFunctionWitness {
            function: source.id,
            mode,
            result_ownership: source.result_ownership,
            source_instructions: source.code.len(),
            emitted_instructions,
            inserted_drops: 0,
            inferred_moves: 0,
            existing_drops,
            existing_moves,
            redefinitions: 0,
            edge_blocks: 0,
            consumed_extern_args,
            consumed_call_args,
            consumed_closure_captures,
            consumed_apply_args,
            borrowed_intrinsic_results,
            raw_intrinsic_results,
            owned_callable_results,
            scalar_callable_results,
        },
    ))
}

fn linear_value_epoch_count(
    source: &Function,
    limits: OwnershipLimits,
) -> Result<usize, OwnershipError> {
    let writes = source
        .code
        .iter()
        .filter(|instruction| instruction.written_register().is_some())
        .count();
    let observed = usize::from(source.arity).saturating_add(writes);
    if observed > limits.max_value_epochs {
        return Err(OwnershipError::ResourceLimit {
            resource: OwnershipResource::ValueEpochs,
            limit: limits.max_value_epochs,
            observed,
        });
    }
    Ok(observed)
}

fn insert_linear_function(
    source: &Function,
    mode: OwnershipMode,
    redefinitions: usize,
    total_emitted: &mut usize,
    limits: OwnershipLimits,
) -> Result<(Function, OwnershipFunctionWitness), OwnershipError> {
    let register_count = usize::from(source.register_count);
    let epoch_count = linear_value_epoch_count(source, limits)?;
    let mut current_epoch = ownership_vec(register_count, OwnershipResource::Registers)?;
    current_epoch.resize(register_count, None::<usize>);
    for (raw, slot) in current_epoch
        .iter_mut()
        .enumerate()
        .take(usize::from(source.arity))
    {
        *slot = Some(raw);
    }
    let mut remaining = ownership_vec(epoch_count, OwnershipResource::ValueEpochs)?;
    remaining.resize(epoch_count, 0usize);
    let mut next_epoch = usize::from(source.arity);
    for instruction in &source.code {
        ownership_reads(instruction, |register| {
            let epoch = current_epoch[register.index()].ok_or(OwnershipError::OwnershipState {
                function: source.id,
                source_position: 0,
                register,
            })?;
            let slot = &mut remaining[epoch];
            *slot = slot.checked_add(1).unwrap_or(usize::MAX);
            if *slot > limits.max_operands {
                return Err(OwnershipError::ResourceLimit {
                    resource: OwnershipResource::Operands,
                    limit: limits.max_operands,
                    observed: *slot,
                });
            }
            Ok(())
        })?;
        ownership_consumes(instruction, |register| {
            current_epoch[register.index()] = None;
            Ok::<(), OwnershipError>(())
        })?;
        if let Some(dst) = instruction.written_register() {
            current_epoch[dst.index()] = Some(next_epoch);
            next_epoch = next_epoch.saturating_add(1);
        }
    }

    let capacity = source
        .code
        .len()
        .saturating_add(epoch_count)
        .min(limits.max_emitted_instructions);
    let mut code = ownership_vec(capacity, OwnershipResource::EmittedInstructions)?;
    let mut live = ownership_vec(register_count, OwnershipResource::Registers)?;
    live.resize(register_count, false);
    live[..usize::from(source.arity)].fill(true);
    current_epoch.fill(None);
    for (raw, slot) in current_epoch
        .iter_mut()
        .enumerate()
        .take(usize::from(source.arity))
    {
        *slot = Some(raw);
    }
    next_epoch = usize::from(source.arity);
    let mut inserted_drops = 0usize;
    let mut inferred_moves = 0usize;
    let mut consumed_extern_args = 0usize;
    let mut consumed_call_args = 0usize;
    let mut consumed_closure_captures = 0usize;
    let mut consumed_apply_args = 0usize;
    let mut borrowed_intrinsic_results = 0usize;
    let mut raw_intrinsic_results = 0usize;

    for raw in 0..usize::from(source.arity) {
        let epoch = current_epoch[raw].expect("parameter epoch was initialized");
        if remaining[epoch] == 0 {
            let register =
                Register::new(u16::try_from(raw).expect("parameter index is bounded by arity"));
            emit_ownership_instruction(
                &mut code,
                Instruction::Drop { src: register },
                total_emitted,
                limits,
            )?;
            live[raw] = false;
            inserted_drops = inserted_drops.saturating_add(1);
        }
    }

    for (offset, instruction) in source.code.iter().enumerate() {
        consumed_extern_args =
            consumed_extern_args.saturating_add(consumed_extern_argument_count(instruction));
        consumed_call_args =
            consumed_call_args.saturating_add(consumed_call_argument_count(instruction));
        consumed_closure_captures =
            consumed_closure_captures.saturating_add(consumed_closure_capture_count(instruction));
        consumed_apply_args =
            consumed_apply_args.saturating_add(consumed_apply_argument_count(instruction));
        borrowed_intrinsic_results =
            borrowed_intrinsic_results.saturating_add(borrowed_intrinsic_result_count(instruction));
        raw_intrinsic_results =
            raw_intrinsic_results.saturating_add(raw_intrinsic_result_count(instruction));
        let inferred_move = matches!(
            instruction,
            Instruction::Copy { src, .. }
                if current_epoch[src.index()].is_some_and(|epoch| remaining[epoch] == 1)
        );
        let emitted_instruction = match instruction {
            Instruction::Copy { dst, src } if inferred_move => Instruction::Move {
                dst: *dst,
                src: *src,
            },
            _ => ownership_clone_instruction(instruction)?,
        };
        emit_ownership_instruction(&mut code, emitted_instruction, total_emitted, limits)?;
        ownership_reads(instruction, |register| {
            let epoch = current_epoch[register.index()].ok_or(OwnershipError::OwnershipState {
                function: source.id,
                source_position: offset.saturating_add(1),
                register,
            })?;
            let slot = &mut remaining[epoch];
            *slot = slot.checked_sub(1).ok_or(OwnershipError::OwnershipState {
                function: source.id,
                source_position: offset.saturating_add(1),
                register,
            })?;
            Ok(())
        })?;
        ownership_consumes(instruction, |register| {
            if !live[register.index()] {
                return Err(OwnershipError::OwnershipState {
                    function: source.id,
                    source_position: offset.saturating_add(1),
                    register,
                });
            }
            live[register.index()] = false;
            current_epoch[register.index()] = None;
            Ok(())
        })?;

        if let Instruction::Copy { dst, src } = instruction
            && inferred_move
        {
            if !live[src.index()] || (dst != src && live[dst.index()]) {
                return Err(OwnershipError::OwnershipState {
                    function: source.id,
                    source_position: offset.saturating_add(1),
                    register: if !live[src.index()] { *src } else { *dst },
                });
            }
            if dst != src {
                live[src.index()] = false;
            }
            live[dst.index()] = true;
            inferred_moves = inferred_moves.saturating_add(1);
        } else if let Some(terminal) = ownership_terminal(instruction) {
            if !live[terminal.index()] {
                return Err(OwnershipError::OwnershipState {
                    function: source.id,
                    source_position: code.len(),
                    register: terminal,
                });
            }
            live[terminal.index()] = false;
            continue;
        } else if let Some(dst) = instruction.written_register() {
            if live[dst.index()] {
                return Err(OwnershipError::OwnershipState {
                    function: source.id,
                    source_position: offset.saturating_add(1),
                    register: dst,
                });
            }
            live[dst.index()] = true;
        }
        if let Some(dst) = instruction.written_register() {
            current_epoch[dst.index()] = Some(next_epoch);
            next_epoch = next_epoch.saturating_add(1);
        }
        for raw in 0..register_count {
            let exhausted = current_epoch[raw].is_some_and(|epoch| remaining[epoch] == 0);
            if live[raw] && exhausted {
                let register =
                    Register::new(u16::try_from(raw).expect("register index is bounded by width"));
                emit_ownership_instruction(
                    &mut code,
                    Instruction::Drop { src: register },
                    total_emitted,
                    limits,
                )?;
                live[raw] = false;
                inserted_drops = inserted_drops.saturating_add(1);
            }
        }
    }

    if let Some(raw) = live.iter().position(|is_live| *is_live) {
        return Err(OwnershipError::OwnershipState {
            function: source.id,
            source_position: source.code.len(),
            register: Register::new(
                u16::try_from(raw).expect("live register index is bounded by width"),
            ),
        });
    }
    let owned_callable_results = code.iter().map(owned_callable_result_count).sum();
    let scalar_callable_results = code.iter().map(scalar_callable_result_count).sum();
    let emitted_instructions = code.len();
    Ok((
        Function {
            id: source.id,
            arity: source.arity,
            parameter_ownership: ownership_clone_copy(
                &source.parameter_ownership,
                OwnershipResource::Operands,
            )?,
            result_ownership: source.result_ownership,
            register_count: source.register_count,
            code,
        },
        OwnershipFunctionWitness {
            function: source.id,
            mode,
            result_ownership: source.result_ownership,
            source_instructions: source.code.len(),
            emitted_instructions,
            inserted_drops,
            inferred_moves,
            existing_drops: 0,
            existing_moves: 0,
            redefinitions,
            edge_blocks: 0,
            consumed_extern_args,
            consumed_call_args,
            consumed_closure_captures,
            consumed_apply_args,
            borrowed_intrinsic_results,
            raw_intrinsic_results,
            owned_callable_results,
            scalar_callable_results,
        },
    ))
}

fn ownership_bits(len: usize, resource: OwnershipResource) -> Result<Vec<bool>, OwnershipError> {
    let mut bits = ownership_vec(len, resource)?;
    bits.resize(len, false);
    Ok(bits)
}

fn insertion_acyclic_liveness(
    source: &Function,
    topological: &[usize],
    limits: OwnershipLimits,
    liveness_cells: &mut usize,
    liveness_steps: &mut usize,
) -> Result<Vec<Vec<bool>>, OwnershipError> {
    let register_count = usize::from(source.register_count);
    let cells = source.code.len().saturating_mul(register_count);
    ownership_add(
        OwnershipResource::LivenessCells,
        liveness_cells,
        cells,
        limits.max_liveness_cells,
    )?;
    let edges = source
        .code
        .iter()
        .map(ownership_cfg_edge_count)
        .fold(0usize, usize::saturating_add);
    ownership_add(
        OwnershipResource::LivenessSteps,
        liveness_steps,
        source
            .code
            .len()
            .saturating_add(edges)
            .saturating_mul(register_count)
            .saturating_add(ownership_operand_total(source)),
        limits.max_liveness_steps,
    )?;

    let mut live_in = ownership_vec(source.code.len(), OwnershipResource::LivenessCells)?;
    for _ in 0..source.code.len() {
        live_in.push(ownership_bits(
            register_count,
            OwnershipResource::LivenessCells,
        )?);
    }
    for offset in topological.iter().rev().copied() {
        let mut live = ownership_bits(register_count, OwnershipResource::LivenessCells)?;
        for successor in ownership_successors(source, offset).into_iter().flatten() {
            for (slot, successor_live) in live.iter_mut().zip(&live_in[successor]) {
                *slot |= *successor_live;
            }
        }
        let instruction = &source.code[offset];
        if let Some(dst) = instruction.written_register() {
            live[dst.index()] = false;
        }
        ownership_consumes(instruction, |register| {
            live[register.index()] = false;
            Ok::<(), OwnershipError>(())
        })?;
        ownership_reads(instruction, |register| {
            live[register.index()] = true;
            Ok::<(), OwnershipError>(())
        })?;
        live_in[offset] = live;
    }
    Ok(live_in)
}

fn insertion_cyclic_liveness(
    source: &Function,
    limits: OwnershipLimits,
    liveness_cells: &mut usize,
    liveness_steps: &mut usize,
) -> Result<Vec<Vec<bool>>, OwnershipError> {
    let instruction_count = source.code.len();
    let register_count = usize::from(source.register_count);
    ownership_add(
        OwnershipResource::LivenessCells,
        liveness_cells,
        instruction_count.saturating_mul(register_count),
        limits.max_liveness_cells,
    )?;

    let mut predecessor_counts = ownership_vec(instruction_count, OwnershipResource::CfgEdges)?;
    predecessor_counts.resize(instruction_count, 0usize);
    for offset in 0..instruction_count {
        for successor in ownership_successors(source, offset).into_iter().flatten() {
            predecessor_counts[successor] = predecessor_counts[successor].saturating_add(1);
        }
    }
    let mut predecessors = ownership_vec(instruction_count, OwnershipResource::CfgEdges)?;
    for count in predecessor_counts {
        predecessors.push(ownership_vec(count, OwnershipResource::CfgEdges)?);
    }
    for offset in 0..instruction_count {
        for successor in ownership_successors(source, offset).into_iter().flatten() {
            predecessors[successor].push(offset);
        }
    }

    let mut live_in = ownership_vec(instruction_count, OwnershipResource::LivenessCells)?;
    for _ in 0..instruction_count {
        live_in.push(ownership_bits(
            register_count,
            OwnershipResource::LivenessCells,
        )?);
    }
    let mut queued = ownership_bits(instruction_count, OwnershipResource::LivenessSteps)?;
    let mut queue = VecDeque::new();
    queue
        .try_reserve(instruction_count)
        .map_err(|_| OwnershipError::AllocationFailure {
            resource: OwnershipResource::LivenessSteps,
            requested: instruction_count,
        })?;
    for offset in (0..instruction_count).rev() {
        queued[offset] = true;
        queue.push_back(offset);
    }

    while let Some(offset) = queue.pop_front() {
        queued[offset] = false;
        let successors = ownership_successors(source, offset);
        let successor_count = successors.iter().flatten().count();
        ownership_add(
            OwnershipResource::LivenessSteps,
            liveness_steps,
            1usize
                .saturating_add(
                    successor_count
                        .saturating_add(1)
                        .saturating_mul(register_count),
                )
                .saturating_add(ownership_operand_count(&source.code[offset])),
            limits.max_liveness_steps,
        )?;

        let mut live = ownership_bits(register_count, OwnershipResource::LivenessCells)?;
        for successor in successors.into_iter().flatten() {
            for (slot, successor_live) in live.iter_mut().zip(&live_in[successor]) {
                *slot |= *successor_live;
            }
        }
        let instruction = &source.code[offset];
        if let Some(dst) = instruction.written_register() {
            live[dst.index()] = false;
        }
        ownership_consumes(instruction, |register| {
            live[register.index()] = false;
            Ok::<(), OwnershipError>(())
        })?;
        ownership_reads(instruction, |register| {
            live[register.index()] = true;
            Ok::<(), OwnershipError>(())
        })?;

        if live == live_in[offset] {
            continue;
        }
        ownership_add(
            OwnershipResource::LivenessSteps,
            liveness_steps,
            predecessors[offset].len(),
            limits.max_liveness_steps,
        )?;
        live_in[offset] = live;
        for predecessor in &predecessors[offset] {
            if !queued[*predecessor] {
                queued[*predecessor] = true;
                queue.push_back(*predecessor);
            }
        }
    }
    Ok(live_in)
}

fn insertion_cfg_infers_move(source: &Function, live_in: &[Vec<bool>], offset: usize) -> bool {
    let Instruction::Copy { src, .. } = &source.code[offset] else {
        return false;
    };
    ownership_successors(source, offset)[0]
        .is_some_and(|successor| !live_in[successor][src.index()])
}

fn insertion_cfg_state_after_is_live(
    source: &Function,
    live_in: &[Vec<bool>],
    offset: usize,
    raw: usize,
) -> bool {
    let instruction = &source.code[offset];
    if insertion_cfg_infers_move(source, live_in, offset)
        && let Instruction::Copy { dst, src } = instruction
    {
        if src.index() == raw {
            return false;
        }
        if dst.index() == raw {
            return true;
        }
    }
    if instruction
        .written_register()
        .is_some_and(|register| register.index() == raw)
    {
        return true;
    }
    if ownership_consumes_register(instruction, raw) {
        return false;
    }
    live_in[offset][raw]
}

fn cfg_edge_drop_count(
    source: &Function,
    live_in: &[Vec<bool>],
    offset: usize,
    successor: usize,
) -> usize {
    (0..usize::from(source.register_count))
        .filter(|raw| {
            insertion_cfg_state_after_is_live(source, live_in, offset, *raw)
                && !live_in[successor][*raw]
        })
        .count()
}

struct CfgLayout {
    source_map: Vec<usize>,
    edge_starts: Vec<[Option<usize>; 2]>,
    emitted_instructions: usize,
    inserted_drops: usize,
    inferred_moves: usize,
    edge_blocks: usize,
}

fn cfg_layout_add(
    cursor: &mut usize,
    additional: usize,
    limits: OwnershipLimits,
) -> Result<(), OwnershipError> {
    ownership_add(
        OwnershipResource::EmittedInstructions,
        cursor,
        additional,
        limits.max_emitted_instructions,
    )
}

fn insertion_cfg_layout(
    source: &Function,
    live_in: &[Vec<bool>],
    limits: OwnershipLimits,
) -> Result<CfgLayout, OwnershipError> {
    let mut source_map = ownership_vec(source.code.len(), OwnershipResource::SourceInstructions)?;
    let mut edge_starts = ownership_vec(source.code.len(), OwnershipResource::SourceInstructions)?;
    edge_starts.resize(source.code.len(), [None, None]);

    let mut cursor = 0usize;
    let entry_drops = (0..usize::from(source.arity))
        .filter(|raw| !live_in[0][*raw])
        .count();
    cfg_layout_add(&mut cursor, entry_drops, limits)?;
    let mut inserted_drops = entry_drops;
    let mut inferred_moves = 0usize;

    for offset in 0..source.code.len() {
        source_map.push(cursor);
        cfg_layout_add(&mut cursor, 1, limits)?;
        inferred_moves = inferred_moves.saturating_add(usize::from(insertion_cfg_infers_move(
            source, live_in, offset,
        )));
        if !ownership_is_control(&source.code[offset])
            && let Some(successor) = ownership_successors(source, offset)[0]
        {
            let drops = cfg_edge_drop_count(source, live_in, offset, successor);
            cfg_layout_add(&mut cursor, drops, limits)?;
            inserted_drops = inserted_drops.saturating_add(drops);
        }
    }

    let mut edge_blocks = 0usize;
    for (offset, starts) in edge_starts.iter_mut().enumerate() {
        if !ownership_is_control(&source.code[offset]) {
            continue;
        }
        for (edge, successor) in ownership_successors(source, offset).into_iter().enumerate() {
            let Some(successor) = successor else {
                continue;
            };
            starts[edge] = Some(cursor);
            let drops = cfg_edge_drop_count(source, live_in, offset, successor);
            cfg_layout_add(&mut cursor, drops.saturating_add(1), limits)?;
            inserted_drops = inserted_drops.saturating_add(drops);
            edge_blocks = edge_blocks.saturating_add(1);
        }
    }
    Ok(CfgLayout {
        source_map,
        edge_starts,
        emitted_instructions: cursor,
        inserted_drops,
        inferred_moves,
        edge_blocks,
    })
}

fn ownership_pc(instruction: usize) -> Result<Pc, OwnershipError> {
    u32::try_from(instruction)
        .map(Pc::new)
        .map_err(|_| OwnershipError::ResourceLimit {
            resource: OwnershipResource::EmittedInstructions,
            limit: u32::MAX as usize,
            observed: instruction,
        })
}

fn clone_cfg_source_instruction(
    source: &Function,
    live_in: &[Vec<bool>],
    offset: usize,
    layout: &CfgLayout,
) -> Result<Instruction, OwnershipError> {
    match &source.code[offset] {
        Instruction::Jump { .. } => Ok(Instruction::Jump {
            target: ownership_pc(layout.edge_starts[offset][0].expect("Jump has one edge block"))?,
        }),
        Instruction::JumpIfZero { cond, .. } => Ok(Instruction::JumpIfZero {
            cond: *cond,
            zero: ownership_pc(
                layout.edge_starts[offset][0].expect("JumpIfZero has a zero edge block"),
            )?,
            nonzero: ownership_pc(
                layout.edge_starts[offset][1].expect("JumpIfZero has a nonzero edge block"),
            )?,
        }),
        Instruction::Copy { dst, src } if insertion_cfg_infers_move(source, live_in, offset) => {
            Ok(Instruction::Move {
                dst: *dst,
                src: *src,
            })
        }
        instruction => ownership_clone_instruction(instruction),
    }
}

fn emit_cfg_edge_drops(
    source: &Function,
    live_in: &[Vec<bool>],
    offset: usize,
    successor: usize,
    code: &mut Vec<Instruction>,
    total_emitted: &mut usize,
    limits: OwnershipLimits,
) -> Result<(), OwnershipError> {
    for raw in 0..usize::from(source.register_count) {
        if insertion_cfg_state_after_is_live(source, live_in, offset, raw)
            && !live_in[successor][raw]
        {
            emit_ownership_instruction(
                code,
                Instruction::Drop {
                    src: Register::new(
                        u16::try_from(raw).expect("register index is bounded by width"),
                    ),
                },
                total_emitted,
                limits,
            )?;
        }
    }
    Ok(())
}

fn build_cfg_function(
    source: &Function,
    live_in: &[Vec<bool>],
    mode: OwnershipMode,
    redefinitions: usize,
    total_emitted: &mut usize,
    limits: OwnershipLimits,
) -> Result<(Function, OwnershipFunctionWitness), OwnershipError> {
    let layout = insertion_cfg_layout(source, live_in, limits)?;
    let mut code = ownership_vec(
        layout.emitted_instructions,
        OwnershipResource::EmittedInstructions,
    )?;
    let mut consumed_extern_args = 0usize;
    let mut consumed_call_args = 0usize;
    let mut consumed_closure_captures = 0usize;
    let mut consumed_apply_args = 0usize;
    let mut borrowed_intrinsic_results = 0usize;
    let mut raw_intrinsic_results = 0usize;

    for (raw, is_live) in live_in[0]
        .iter()
        .take(usize::from(source.arity))
        .enumerate()
    {
        if !*is_live {
            emit_ownership_instruction(
                &mut code,
                Instruction::Drop {
                    src: Register::new(
                        u16::try_from(raw).expect("parameter index is bounded by arity"),
                    ),
                },
                total_emitted,
                limits,
            )?;
        }
    }
    for offset in 0..source.code.len() {
        consumed_extern_args = consumed_extern_args
            .saturating_add(consumed_extern_argument_count(&source.code[offset]));
        consumed_call_args =
            consumed_call_args.saturating_add(consumed_call_argument_count(&source.code[offset]));
        consumed_closure_captures = consumed_closure_captures
            .saturating_add(consumed_closure_capture_count(&source.code[offset]));
        consumed_apply_args =
            consumed_apply_args.saturating_add(consumed_apply_argument_count(&source.code[offset]));
        borrowed_intrinsic_results = borrowed_intrinsic_results
            .saturating_add(borrowed_intrinsic_result_count(&source.code[offset]));
        raw_intrinsic_results =
            raw_intrinsic_results.saturating_add(raw_intrinsic_result_count(&source.code[offset]));
        emit_ownership_instruction(
            &mut code,
            clone_cfg_source_instruction(source, live_in, offset, &layout)?,
            total_emitted,
            limits,
        )?;
        if !ownership_is_control(&source.code[offset])
            && let Some(successor) = ownership_successors(source, offset)[0]
        {
            emit_cfg_edge_drops(
                source,
                live_in,
                offset,
                successor,
                &mut code,
                total_emitted,
                limits,
            )?;
        }
    }
    for offset in 0..source.code.len() {
        if !ownership_is_control(&source.code[offset]) {
            continue;
        }
        for successor in ownership_successors(source, offset).into_iter().flatten() {
            emit_cfg_edge_drops(
                source,
                live_in,
                offset,
                successor,
                &mut code,
                total_emitted,
                limits,
            )?;
            emit_ownership_instruction(
                &mut code,
                Instruction::Jump {
                    target: ownership_pc(layout.source_map[successor])?,
                },
                total_emitted,
                limits,
            )?;
        }
    }
    if code.len() != layout.emitted_instructions {
        return Err(OwnershipError::SkeletonMismatch {
            function: source.id,
            source_instruction: source.code.len(),
            candidate_instruction: code.len(),
        });
    }
    let owned_callable_results = code.iter().map(owned_callable_result_count).sum();
    let scalar_callable_results = code.iter().map(scalar_callable_result_count).sum();
    let emitted_instructions = code.len();
    Ok((
        Function {
            id: source.id,
            arity: source.arity,
            parameter_ownership: ownership_clone_copy(
                &source.parameter_ownership,
                OwnershipResource::Operands,
            )?,
            result_ownership: source.result_ownership,
            register_count: source.register_count,
            code,
        },
        OwnershipFunctionWitness {
            function: source.id,
            mode,
            result_ownership: source.result_ownership,
            source_instructions: source.code.len(),
            emitted_instructions,
            inserted_drops: layout.inserted_drops,
            inferred_moves: layout.inferred_moves,
            existing_drops: 0,
            existing_moves: 0,
            redefinitions,
            edge_blocks: layout.edge_blocks,
            consumed_extern_args,
            consumed_call_args,
            consumed_closure_captures,
            consumed_apply_args,
            borrowed_intrinsic_results,
            raw_intrinsic_results,
            owned_callable_results,
            scalar_callable_results,
        },
    ))
}

fn insert_acyclic_cfg_function(
    source: &Function,
    classification: &InsertionClassification,
    total_emitted: &mut usize,
    liveness_cells: &mut usize,
    liveness_steps: &mut usize,
    limits: OwnershipLimits,
) -> Result<(Function, OwnershipFunctionWitness), OwnershipError> {
    let live_in = insertion_acyclic_liveness(
        source,
        classification
            .topological
            .as_deref()
            .expect("acyclic CFG classification carries its order"),
        limits,
        liveness_cells,
        liveness_steps,
    )?;
    build_cfg_function(
        source,
        &live_in,
        classification.mode,
        classification.redefinitions,
        total_emitted,
        limits,
    )
}

fn insert_cyclic_cfg_function(
    source: &Function,
    mode: OwnershipMode,
    redefinitions: usize,
    total_emitted: &mut usize,
    liveness_cells: &mut usize,
    liveness_steps: &mut usize,
    limits: OwnershipLimits,
) -> Result<(Function, OwnershipFunctionWitness), OwnershipError> {
    let live_in = insertion_cyclic_liveness(source, limits, liveness_cells, liveness_steps)?;
    build_cfg_function(source, &live_in, mode, redefinitions, total_emitted, limits)
}

/// Insert eager ownership drops and infer last-use ownership moves in admitted
/// straight-line functions and non-overlapping CFG register reuse, including
/// cycles.
///
/// Straight-line construction uses remaining-use counters. Acyclic-CFG
/// construction uses reverse-topological liveness; cyclic construction uses a
/// deterministic monotone bitset fixed point. A `Copy` becomes a `Move`
/// exactly when its source has no successor demand, removing the corresponding
/// retain and source drop. CFGs use path-specific edge blocks. Before
/// returning, every result passes ordinary FLBC validation and
/// [`validate_ownership_candidate`], whose algorithms are intentionally
/// separate.
pub fn insert_ownership(
    source: &ValidatedProgram,
    limits: OwnershipLimits,
) -> Result<OwnershipProgram, OwnershipError> {
    check_ownership_program_limits(source, limits, false)?;
    let mut functions = ownership_vec(source.functions().len(), OwnershipResource::Functions)?;
    let mut rows = ownership_vec(source.functions().len(), OwnershipResource::Functions)?;
    let mut total_emitted = 0usize;
    let mut liveness_cells = 0usize;
    let mut liveness_steps = 0usize;
    for function in source.functions() {
        let classification = insertion_classification(function)?;
        let (candidate, row) = match classification.mode {
            mode @ (OwnershipMode::InsertedLinear | OwnershipMode::InsertedLinearReuse) => {
                insert_linear_function(
                    function,
                    mode,
                    classification.redefinitions,
                    &mut total_emitted,
                    limits,
                )?
            }
            OwnershipMode::InsertedAcyclicCfg | OwnershipMode::InsertedAcyclicCfgReuse => {
                insert_acyclic_cfg_function(
                    function,
                    &classification,
                    &mut total_emitted,
                    &mut liveness_cells,
                    &mut liveness_steps,
                    limits,
                )?
            }
            mode @ (OwnershipMode::InsertedCyclicCfg | OwnershipMode::InsertedCyclicCfgReuse) => {
                insert_cyclic_cfg_function(
                    function,
                    mode,
                    classification.redefinitions,
                    &mut total_emitted,
                    &mut liveness_cells,
                    &mut liveness_steps,
                    limits,
                )?
            }
            mode => clone_preserved_function(function, mode, &mut total_emitted, limits)?,
        };
        functions.push(candidate);
        rows.push(row);
    }

    let candidate = validate(Program {
        schema_version: source.schema_version(),
        entry: source.entry(),
        functions,
    })
    .map_err(OwnershipError::CandidateValidation)?;
    validate_ownership_candidate(
        source,
        candidate,
        OwnershipWitness::new(OWNERSHIP_WITNESS_VERSION, rows),
        limits,
    )
}

struct DropSchedule<'a> {
    source: &'a Function,
    candidate: &'a Function,
    definitions: &'a [usize],
    last_reads: &'a [Option<usize>],
    moved_at: &'a [Option<usize>],
}

impl DropSchedule<'_> {
    fn validate_stage(
        &self,
        stage: usize,
        current_epochs: &[Option<usize>],
        live: &mut [bool],
        candidate_cursor: &mut usize,
    ) -> Result<usize, OwnershipError> {
        let mut drops = 0usize;
        for (raw, is_live) in live
            .iter_mut()
            .enumerate()
            .take(usize::from(self.source.register_count))
        {
            let Some(epoch) = current_epochs[raw] else {
                continue;
            };
            let register =
                Register::new(u16::try_from(raw).expect("register index is bounded by width"));
            if !*is_live {
                continue;
            }
            let defined = self.definitions[epoch];
            let drop_stage = self.last_reads[epoch].unwrap_or(defined).max(defined);
            if drop_stage != stage || self.moved_at[epoch] == Some(stage) {
                continue;
            }
            let actual =
                self.candidate.code.get(*candidate_cursor).and_then(
                    |instruction| match instruction {
                        Instruction::Drop { src } => Some(*src),
                        _ => None,
                    },
                );
            if actual != Some(register) {
                return Err(OwnershipError::DropSchedule {
                    function: self.source.id,
                    source_position: stage,
                    expected: Some(register),
                    actual,
                });
            }
            *is_live = false;
            *candidate_cursor = candidate_cursor.saturating_add(1);
            drops = drops.saturating_add(1);
        }
        if let Some(Instruction::Drop { src }) = self.candidate.code.get(*candidate_cursor) {
            return Err(OwnershipError::DropSchedule {
                function: self.source.id,
                source_position: stage,
                expected: None,
                actual: Some(*src),
            });
        }
        Ok(drops)
    }
}

fn validate_linear_candidate(
    source: &Function,
    candidate: &Function,
    limits: OwnershipLimits,
    validation_cells: &mut usize,
    validation_steps: &mut usize,
) -> Result<(usize, usize, usize), OwnershipError> {
    if source.id != candidate.id
        || source.arity != candidate.arity
        || source.parameter_ownership != candidate.parameter_ownership
        || source.result_ownership != candidate.result_ownership
        || source.register_count != candidate.register_count
    {
        return Err(OwnershipError::FunctionMetadataChanged {
            function: source.id,
        });
    }
    let register_count = usize::from(source.register_count);
    let epoch_count = linear_value_epoch_count(source, limits)?;
    let stages = source.code.len().saturating_add(1);
    let cells = stages
        .saturating_mul(register_count)
        .saturating_add(register_count)
        .saturating_add(epoch_count.saturating_mul(3));
    ownership_add(
        OwnershipResource::ValidationCells,
        validation_cells,
        cells,
        limits.max_validation_cells,
    )?;
    ownership_add(
        OwnershipResource::ValidationSteps,
        validation_steps,
        cells,
        limits.max_validation_steps,
    )?;

    let mut definitions = ownership_vec(epoch_count, OwnershipResource::ValueEpochs)?;
    definitions.resize(epoch_count, 0usize);
    let mut last_reads = ownership_vec(epoch_count, OwnershipResource::ValueEpochs)?;
    last_reads.resize(epoch_count, None::<usize>);
    let mut current_epochs = ownership_vec(register_count, OwnershipResource::Registers)?;
    current_epochs.resize(register_count, None::<usize>);
    let mut defined_registers = ownership_vec(register_count, OwnershipResource::Registers)?;
    defined_registers.resize(register_count, false);
    for raw in 0..usize::from(source.arity) {
        current_epochs[raw] = Some(raw);
        defined_registers[raw] = true;
    }
    let mut next_epoch = usize::from(source.arity);
    let mut redefinitions = 0usize;
    for (offset, instruction) in source.code.iter().enumerate() {
        let stage = offset.saturating_add(1);
        ownership_reads(instruction, |register| {
            let epoch = current_epochs[register.index()].ok_or(OwnershipError::OwnershipState {
                function: source.id,
                source_position: stage,
                register,
            })?;
            last_reads[epoch] = Some(stage);
            Ok::<(), OwnershipError>(())
        })?;
        ownership_consumes(instruction, |register| {
            current_epochs[register.index()] = None;
            Ok::<(), OwnershipError>(())
        })?;
        if let Some(dst) = instruction.written_register() {
            redefinitions =
                redefinitions.saturating_add(usize::from(defined_registers[dst.index()]));
            defined_registers[dst.index()] = true;
            definitions[next_epoch] = stage;
            current_epochs[dst.index()] = Some(next_epoch);
            next_epoch = next_epoch.saturating_add(1);
        }
    }
    let mut moved_at = ownership_vec(epoch_count, OwnershipResource::ValueEpochs)?;
    moved_at.resize(epoch_count, None::<usize>);
    current_epochs.fill(None);
    for (raw, slot) in current_epochs
        .iter_mut()
        .enumerate()
        .take(usize::from(source.arity))
    {
        *slot = Some(raw);
    }
    next_epoch = usize::from(source.arity);
    for (offset, instruction) in source.code.iter().enumerate() {
        let stage = offset.saturating_add(1);
        if let Instruction::Copy { src, .. } = instruction
            && current_epochs[src.index()].is_some_and(|epoch| last_reads[epoch] == Some(stage))
        {
            let epoch = current_epochs[src.index()].expect("copy source epoch exists");
            moved_at[epoch] = Some(stage);
        }
        ownership_consumes(instruction, |register| {
            current_epochs[register.index()] = None;
            Ok::<(), OwnershipError>(())
        })?;
        if let Some(dst) = instruction.written_register() {
            current_epochs[dst.index()] = Some(next_epoch);
            next_epoch = next_epoch.saturating_add(1);
        }
    }
    source
        .code
        .last()
        .and_then(ownership_terminal)
        .ok_or(OwnershipError::SkeletonMismatch {
            function: source.id,
            source_instruction: source.code.len().saturating_sub(1),
            candidate_instruction: candidate.code.len().saturating_sub(1),
        })?;

    let mut live = ownership_vec(register_count, OwnershipResource::Registers)?;
    live.resize(register_count, false);
    live[..usize::from(source.arity)].fill(true);
    current_epochs.fill(None);
    for (raw, slot) in current_epochs
        .iter_mut()
        .enumerate()
        .take(usize::from(source.arity))
    {
        *slot = Some(raw);
    }
    next_epoch = usize::from(source.arity);
    let mut candidate_cursor = 0usize;
    let schedule = DropSchedule {
        source,
        candidate,
        definitions: &definitions,
        last_reads: &last_reads,
        moved_at: &moved_at,
    };
    let mut drops =
        schedule.validate_stage(0, &current_epochs, &mut live, &mut candidate_cursor)?;
    let mut inferred_moves = 0usize;

    for (source_offset, source_instruction) in source.code.iter().enumerate() {
        let stage = source_offset.saturating_add(1);
        let Some(candidate_instruction) = candidate.code.get(candidate_cursor) else {
            return Err(OwnershipError::SkeletonMismatch {
                function: source.id,
                source_instruction: source_offset,
                candidate_instruction: candidate_cursor,
            });
        };
        let inferred_move = matches!(
            source_instruction,
            Instruction::Copy { src, .. }
                if current_epochs[src.index()]
                    .is_some_and(|epoch| moved_at[epoch] == Some(stage))
        );
        let skeleton_matches = match (source_instruction, candidate_instruction) {
            (
                Instruction::Copy {
                    dst: source_dst,
                    src: source_src,
                },
                Instruction::Move {
                    dst: candidate_dst,
                    src: candidate_src,
                },
            ) if inferred_move => source_dst == candidate_dst && source_src == candidate_src,
            (Instruction::Copy { .. }, _) if inferred_move => false,
            _ => candidate_instruction == source_instruction,
        };
        if !skeleton_matches {
            return Err(OwnershipError::SkeletonMismatch {
                function: source.id,
                source_instruction: source_offset,
                candidate_instruction: candidate_cursor,
            });
        }
        ownership_reads(source_instruction, |register| {
            if !live[register.index()] {
                return Err(OwnershipError::OwnershipState {
                    function: source.id,
                    source_position: source_offset.saturating_add(1),
                    register,
                });
            }
            Ok(())
        })?;
        ownership_consumes(source_instruction, |register| {
            if !live[register.index()] {
                return Err(OwnershipError::OwnershipState {
                    function: source.id,
                    source_position: stage,
                    register,
                });
            }
            live[register.index()] = false;
            current_epochs[register.index()] = None;
            Ok(())
        })?;
        if let Instruction::Copy { dst, src } = source_instruction
            && inferred_move
        {
            if !live[src.index()] || (dst != src && live[dst.index()]) {
                return Err(OwnershipError::OwnershipState {
                    function: source.id,
                    source_position: stage,
                    register: if !live[src.index()] { *src } else { *dst },
                });
            }
            if dst != src {
                live[src.index()] = false;
            }
            live[dst.index()] = true;
            inferred_moves = inferred_moves.saturating_add(1);
        } else if let Some(transferred) = ownership_terminal(source_instruction) {
            live[transferred.index()] = false;
        } else if let Some(dst) = source_instruction.written_register() {
            if live[dst.index()] {
                return Err(OwnershipError::OwnershipState {
                    function: source.id,
                    source_position: source_offset.saturating_add(1),
                    register: dst,
                });
            }
            live[dst.index()] = true;
        }
        if let Some(dst) = source_instruction.written_register() {
            current_epochs[dst.index()] = Some(next_epoch);
            next_epoch = next_epoch.saturating_add(1);
        }
        candidate_cursor = candidate_cursor.saturating_add(1);
        if ownership_terminal(source_instruction).is_none() {
            drops = drops.saturating_add(schedule.validate_stage(
                source_offset.saturating_add(1),
                &current_epochs,
                &mut live,
                &mut candidate_cursor,
            )?);
        }
    }

    if candidate_cursor != candidate.code.len() {
        return Err(OwnershipError::SkeletonMismatch {
            function: source.id,
            source_instruction: source.code.len(),
            candidate_instruction: candidate_cursor,
        });
    }
    if let Some(raw) = live.iter().position(|is_live| *is_live) {
        return Err(OwnershipError::OwnershipState {
            function: source.id,
            source_position: source.code.len(),
            register: Register::new(
                u16::try_from(raw).expect("live register index is bounded by width"),
            ),
        });
    }
    Ok((drops, inferred_moves, redefinitions))
}

fn ownership_reads_register(instruction: &Instruction, raw: usize) -> bool {
    let mut found = false;
    let _ = ownership_reads(instruction, |register| {
        found |= register.index() == raw;
        Ok::<(), ()>(())
    });
    found
}

fn validation_cfg_redefinitions(
    source: &Function,
    limits: OwnershipLimits,
    validation_cells: &mut usize,
    validation_steps: &mut usize,
) -> Result<usize, OwnershipError> {
    let register_count = usize::from(source.register_count);
    ownership_add(
        OwnershipResource::ValidationCells,
        validation_cells,
        register_count,
        limits.max_validation_cells,
    )?;
    ownership_add(
        OwnershipResource::ValidationSteps,
        validation_steps,
        source.code.len(),
        limits.max_validation_steps,
    )?;
    let mut defined = ownership_bits(register_count, OwnershipResource::ValidationCells)?;
    defined[..usize::from(source.arity)].fill(true);
    let mut redefinitions = 0usize;
    for instruction in &source.code {
        if let Some(dst) = instruction.written_register() {
            redefinitions = redefinitions.saturating_add(usize::from(defined[dst.index()]));
            defined[dst.index()] = true;
        }
    }
    Ok(redefinitions)
}

fn validation_cfg_demand(
    source: &Function,
    limits: OwnershipLimits,
    validation_cells: &mut usize,
    validation_steps: &mut usize,
) -> Result<Vec<Vec<bool>>, OwnershipError> {
    let instruction_count = source.code.len();
    let register_count = usize::from(source.register_count);
    let edge_count = source
        .code
        .iter()
        .map(ownership_cfg_edge_count)
        .fold(0usize, usize::saturating_add);
    let cells = instruction_count
        .saturating_add(edge_count)
        .saturating_mul(register_count);
    ownership_add(
        OwnershipResource::ValidationCells,
        validation_cells,
        cells,
        limits.max_validation_cells,
    )?;
    let mut predecessor_counts = ownership_vec(instruction_count, OwnershipResource::CfgEdges)?;
    predecessor_counts.resize(instruction_count, 0usize);
    for offset in 0..instruction_count {
        for successor in ownership_successors(source, offset).into_iter().flatten() {
            predecessor_counts[successor] = predecessor_counts[successor].saturating_add(1);
        }
    }
    let mut predecessors = ownership_vec(instruction_count, OwnershipResource::CfgEdges)?;
    for count in predecessor_counts {
        predecessors.push(ownership_vec(count, OwnershipResource::CfgEdges)?);
    }
    for offset in 0..instruction_count {
        for successor in ownership_successors(source, offset).into_iter().flatten() {
            predecessors[successor].push(offset);
        }
    }

    let mut demand = ownership_vec(instruction_count, OwnershipResource::ValidationCells)?;
    for _ in 0..instruction_count {
        demand.push(ownership_bits(
            register_count,
            OwnershipResource::ValidationCells,
        )?);
    }
    let mut queue = VecDeque::new();
    queue
        .try_reserve(instruction_count)
        .map_err(|_| OwnershipError::AllocationFailure {
            resource: OwnershipResource::ValidationCells,
            requested: instruction_count,
        })?;
    let scan_steps = instruction_count.saturating_add(ownership_operand_total(source));
    for register in (0..source.register_count).map(Register::new) {
        let raw = register.index();
        ownership_add(
            OwnershipResource::ValidationSteps,
            validation_steps,
            scan_steps,
            limits.max_validation_steps,
        )?;
        queue.clear();
        for (offset, instruction) in source.code.iter().enumerate() {
            if ownership_reads_register(instruction, raw) {
                demand[offset][raw] = true;
                queue.push_back(offset);
            }
        }
        while let Some(offset) = queue.pop_front() {
            ownership_add(
                OwnershipResource::ValidationSteps,
                validation_steps,
                1usize.saturating_add(predecessors[offset].len()),
                limits.max_validation_steps,
            )?;
            for predecessor in &predecessors[offset] {
                if source.code[*predecessor]
                    .written_register()
                    .is_some_and(|register| register.index() == raw)
                    || ownership_consumes_register(&source.code[*predecessor], raw)
                {
                    continue;
                }
                if !demand[*predecessor][raw] {
                    demand[*predecessor][raw] = true;
                    queue.push_back(*predecessor);
                }
            }
        }
    }
    Ok(demand)
}

fn validation_cfg_infers_move(source: &Function, demand: &[Vec<bool>], offset: usize) -> bool {
    let Instruction::Copy { src, .. } = &source.code[offset] else {
        return false;
    };
    ownership_successors(source, offset)[0].is_some_and(|successor| !demand[successor][src.index()])
}

fn validation_cfg_state_after_demand(
    source: &Function,
    demand: &[Vec<bool>],
    offset: usize,
    raw: usize,
) -> bool {
    let instruction = &source.code[offset];
    if validation_cfg_infers_move(source, demand, offset)
        && let Instruction::Copy { dst, src } = instruction
    {
        if src.index() == raw {
            return false;
        }
        if dst.index() == raw {
            return true;
        }
    }
    if instruction
        .written_register()
        .is_some_and(|register| register.index() == raw)
    {
        return true;
    }
    if ownership_consumes_register(instruction, raw) {
        return false;
    }
    demand[offset][raw]
}

fn cfg_drop_is_expected(
    source: &Function,
    demand: &[Vec<bool>],
    offset: usize,
    successor: usize,
    raw: usize,
) -> bool {
    validation_cfg_state_after_demand(source, demand, offset, raw) && !demand[successor][raw]
}

fn validate_cfg_entry_drops(
    source: &Function,
    candidate: &Function,
    demand: &[Vec<bool>],
    candidate_cursor: &mut usize,
) -> Result<usize, OwnershipError> {
    let mut drops = 0usize;
    for (raw, is_live) in demand[0].iter().take(usize::from(source.arity)).enumerate() {
        if *is_live {
            continue;
        }
        let register =
            Register::new(u16::try_from(raw).expect("parameter index is bounded by arity"));
        let actual =
            candidate
                .code
                .get(*candidate_cursor)
                .and_then(|instruction| match instruction {
                    Instruction::Drop { src } => Some(*src),
                    _ => None,
                });
        if actual != Some(register) {
            return Err(OwnershipError::DropSchedule {
                function: source.id,
                source_position: 0,
                expected: Some(register),
                actual,
            });
        }
        *candidate_cursor = candidate_cursor.saturating_add(1);
        drops = drops.saturating_add(1);
    }
    if let Some(Instruction::Drop { src }) = candidate.code.get(*candidate_cursor) {
        return Err(OwnershipError::DropSchedule {
            function: source.id,
            source_position: 0,
            expected: None,
            actual: Some(*src),
        });
    }
    Ok(drops)
}

fn validate_cfg_edge_drops(
    source: &Function,
    candidate: &Function,
    demand: &[Vec<bool>],
    offset: usize,
    successor: usize,
    edge: Option<u8>,
    candidate_cursor: &mut usize,
) -> Result<usize, OwnershipError> {
    let mut drops = 0usize;
    for raw in 0..usize::from(source.register_count) {
        if !cfg_drop_is_expected(source, demand, offset, successor, raw) {
            continue;
        }
        let register =
            Register::new(u16::try_from(raw).expect("register index is bounded by width"));
        let actual =
            candidate
                .code
                .get(*candidate_cursor)
                .and_then(|instruction| match instruction {
                    Instruction::Drop { src } => Some(*src),
                    _ => None,
                });
        if actual != Some(register) {
            return Err(match edge {
                Some(edge) => OwnershipError::EdgeDropSchedule {
                    function: source.id,
                    source_instruction: offset,
                    edge,
                    expected: Some(register),
                    actual,
                },
                None => OwnershipError::DropSchedule {
                    function: source.id,
                    source_position: offset.saturating_add(1),
                    expected: Some(register),
                    actual,
                },
            });
        }
        *candidate_cursor = candidate_cursor.saturating_add(1);
        drops = drops.saturating_add(1);
    }
    if let Some(Instruction::Drop { src }) = candidate.code.get(*candidate_cursor) {
        return Err(match edge {
            Some(edge) => OwnershipError::EdgeDropSchedule {
                function: source.id,
                source_instruction: offset,
                edge,
                expected: None,
                actual: Some(*src),
            },
            None => OwnershipError::DropSchedule {
                function: source.id,
                source_position: offset.saturating_add(1),
                expected: None,
                actual: Some(*src),
            },
        });
    }
    Ok(drops)
}

fn validate_cfg_candidate(
    source: &Function,
    candidate: &Function,
    count_redefinitions: bool,
    limits: OwnershipLimits,
    validation_cells: &mut usize,
    validation_steps: &mut usize,
) -> Result<(usize, usize, usize, usize), OwnershipError> {
    if source.id != candidate.id
        || source.arity != candidate.arity
        || source.parameter_ownership != candidate.parameter_ownership
        || source.result_ownership != candidate.result_ownership
        || source.register_count != candidate.register_count
    {
        return Err(OwnershipError::FunctionMetadataChanged {
            function: source.id,
        });
    }
    let redefinitions = if count_redefinitions {
        validation_cfg_redefinitions(source, limits, validation_cells, validation_steps)?
    } else {
        0
    };
    let demand = validation_cfg_demand(source, limits, validation_cells, validation_steps)?;
    let mut source_map = ownership_vec(source.code.len(), OwnershipResource::ValidationCells)?;
    let mut edge_starts = ownership_vec(source.code.len(), OwnershipResource::ValidationCells)?;
    edge_starts.resize(source.code.len(), [None, None]);

    let mut candidate_cursor = 0usize;
    let mut drops = validate_cfg_entry_drops(source, candidate, &demand, &mut candidate_cursor)?;
    let mut inferred_moves = 0usize;
    for (offset, source_instruction) in source.code.iter().enumerate() {
        source_map.push(candidate_cursor);
        let Some(candidate_instruction) = candidate.code.get(candidate_cursor) else {
            return Err(OwnershipError::SkeletonMismatch {
                function: source.id,
                source_instruction: offset,
                candidate_instruction: candidate_cursor,
            });
        };
        let skeleton_matches = match (source_instruction, candidate_instruction) {
            (Instruction::Jump { .. }, Instruction::Jump { .. }) => true,
            (
                Instruction::JumpIfZero {
                    cond: source_cond, ..
                },
                Instruction::JumpIfZero {
                    cond: candidate_cond,
                    ..
                },
            ) => source_cond == candidate_cond,
            (
                Instruction::Copy {
                    dst: source_dst,
                    src: source_src,
                },
                Instruction::Move {
                    dst: candidate_dst,
                    src: candidate_src,
                },
            ) if validation_cfg_infers_move(source, &demand, offset) => {
                source_dst == candidate_dst && source_src == candidate_src
            }
            (Instruction::Copy { .. }, _)
                if validation_cfg_infers_move(source, &demand, offset) =>
            {
                false
            }
            _ => source_instruction == candidate_instruction,
        };
        if !skeleton_matches {
            return Err(OwnershipError::SkeletonMismatch {
                function: source.id,
                source_instruction: offset,
                candidate_instruction: candidate_cursor,
            });
        }
        inferred_moves = inferred_moves.saturating_add(usize::from(validation_cfg_infers_move(
            source, &demand, offset,
        )));
        candidate_cursor = candidate_cursor.saturating_add(1);
        if !ownership_is_control(source_instruction)
            && let Some(successor) = ownership_successors(source, offset)[0]
        {
            drops = drops.saturating_add(validate_cfg_edge_drops(
                source,
                candidate,
                &demand,
                offset,
                successor,
                None,
                &mut candidate_cursor,
            )?);
        }
    }

    let mut edge_blocks = 0usize;
    for (offset, starts) in edge_starts.iter_mut().enumerate() {
        if !ownership_is_control(&source.code[offset]) {
            continue;
        }
        for (edge, successor) in ownership_successors(source, offset).into_iter().enumerate() {
            let Some(successor) = successor else {
                continue;
            };
            starts[edge] = Some(candidate_cursor);
            drops = drops.saturating_add(validate_cfg_edge_drops(
                source,
                candidate,
                &demand,
                offset,
                successor,
                Some(u8::try_from(edge).expect("two control edges fit u8")),
                &mut candidate_cursor,
            )?);
            let expected = ownership_pc(source_map[successor])?;
            let Some(candidate_instruction) = candidate.code.get(candidate_cursor) else {
                return Err(OwnershipError::SkeletonMismatch {
                    function: source.id,
                    source_instruction: offset,
                    candidate_instruction: candidate_cursor,
                });
            };
            let Instruction::Jump { target: actual } = candidate_instruction else {
                return Err(OwnershipError::SkeletonMismatch {
                    function: source.id,
                    source_instruction: offset,
                    candidate_instruction: candidate_cursor,
                });
            };
            if *actual != expected {
                return Err(OwnershipError::ControlTarget {
                    function: source.id,
                    source_instruction: offset,
                    edge: u8::try_from(edge).expect("two control edges fit u8"),
                    expected,
                    actual: *actual,
                });
            }
            candidate_cursor = candidate_cursor.saturating_add(1);
            edge_blocks = edge_blocks.saturating_add(1);
        }
    }
    if candidate_cursor != candidate.code.len() {
        return Err(OwnershipError::SkeletonMismatch {
            function: source.id,
            source_instruction: source.code.len(),
            candidate_instruction: candidate_cursor,
        });
    }

    for offset in 0..source.code.len() {
        let candidate_instruction = &candidate.code[source_map[offset]];
        match (&source.code[offset], candidate_instruction) {
            (Instruction::Jump { .. }, Instruction::Jump { target: actual }) => {
                let expected = ownership_pc(
                    edge_starts[offset][0].expect("Jump has one reconstructed edge block"),
                )?;
                if *actual != expected {
                    return Err(OwnershipError::ControlTarget {
                        function: source.id,
                        source_instruction: offset,
                        edge: 0,
                        expected,
                        actual: *actual,
                    });
                }
            }
            (Instruction::JumpIfZero { .. }, Instruction::JumpIfZero { zero, nonzero, .. }) => {
                for (edge, actual) in [*zero, *nonzero].into_iter().enumerate() {
                    let expected = ownership_pc(
                        edge_starts[offset][edge]
                            .expect("JumpIfZero has two reconstructed edge blocks"),
                    )?;
                    if actual != expected {
                        return Err(OwnershipError::ControlTarget {
                            function: source.id,
                            source_instruction: offset,
                            edge: u8::try_from(edge).expect("two control edges fit u8"),
                            expected,
                            actual,
                        });
                    }
                }
            }
            _ => {}
        }
    }
    Ok((drops, edge_blocks, inferred_moves, redefinitions))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct OwnershipInstructionCounts {
    drops: usize,
    moves: usize,
    consumed_extern_args: usize,
    consumed_call_args: usize,
    consumed_closure_captures: usize,
    consumed_apply_args: usize,
    borrowed_intrinsic_results: usize,
    raw_intrinsic_results: usize,
    owned_callable_results: usize,
    scalar_callable_results: usize,
}

fn validate_ownership_state(
    candidate: &Function,
    limits: OwnershipLimits,
    validation_cells: &mut usize,
    validation_steps: &mut usize,
) -> Result<OwnershipInstructionCounts, OwnershipError> {
    let register_count = usize::from(candidate.register_count);
    let cells = candidate.code.len().saturating_mul(register_count);
    ownership_add(
        OwnershipResource::ValidationCells,
        validation_cells,
        cells,
        limits.max_validation_cells,
    )?;
    let edges = candidate
        .code
        .iter()
        .map(ownership_cfg_edge_count)
        .fold(0usize, usize::saturating_add);
    ownership_add(
        OwnershipResource::ValidationSteps,
        validation_steps,
        candidate
            .code
            .len()
            .saturating_add(edges)
            .saturating_mul(register_count),
        limits.max_validation_steps,
    )?;

    let mut incoming = ownership_vec(candidate.code.len(), OwnershipResource::ValidationCells)?;
    incoming.resize_with(candidate.code.len(), || None::<Vec<bool>>);
    let mut entry = ownership_bits(register_count, OwnershipResource::ValidationCells)?;
    entry[..usize::from(candidate.arity)].fill(true);
    incoming[0] = Some(entry);
    let mut queue = VecDeque::new();
    queue
        .try_reserve(candidate.code.len())
        .map_err(|_| OwnershipError::AllocationFailure {
            resource: OwnershipResource::ValidationCells,
            requested: candidate.code.len(),
        })?;
    queue.push_back(0usize);
    let mut counts = OwnershipInstructionCounts {
        drops: 0,
        moves: 0,
        consumed_extern_args: 0,
        consumed_call_args: 0,
        consumed_closure_captures: 0,
        consumed_apply_args: 0,
        borrowed_intrinsic_results: 0,
        raw_intrinsic_results: 0,
        owned_callable_results: 0,
        scalar_callable_results: 0,
    };

    while let Some(offset) = queue.pop_front() {
        let mut state = ownership_clone_copy(
            incoming[offset]
                .as_ref()
                .expect("queue contains reached ownership instructions"),
            OwnershipResource::ValidationCells,
        )?;
        let instruction = &candidate.code[offset];
        ownership_reads(instruction, |register| {
            if !state[register.index()] {
                return Err(OwnershipError::OwnershipState {
                    function: candidate.id,
                    source_position: offset,
                    register,
                });
            }
            Ok(())
        })?;
        match instruction {
            Instruction::Drop { .. } => {
                counts.drops = counts.drops.saturating_add(1);
            }
            Instruction::Move { .. } => {
                counts.moves = counts.moves.saturating_add(1);
            }
            _ => {}
        }
        counts.consumed_extern_args = counts
            .consumed_extern_args
            .saturating_add(consumed_extern_argument_count(instruction));
        counts.consumed_call_args = counts
            .consumed_call_args
            .saturating_add(consumed_call_argument_count(instruction));
        counts.consumed_closure_captures = counts
            .consumed_closure_captures
            .saturating_add(consumed_closure_capture_count(instruction));
        counts.consumed_apply_args = counts
            .consumed_apply_args
            .saturating_add(consumed_apply_argument_count(instruction));
        counts.borrowed_intrinsic_results = counts
            .borrowed_intrinsic_results
            .saturating_add(borrowed_intrinsic_result_count(instruction));
        counts.raw_intrinsic_results = counts
            .raw_intrinsic_results
            .saturating_add(raw_intrinsic_result_count(instruction));
        counts.owned_callable_results = counts
            .owned_callable_results
            .saturating_add(owned_callable_result_count(instruction));
        counts.scalar_callable_results = counts
            .scalar_callable_results
            .saturating_add(scalar_callable_result_count(instruction));
        ownership_consumes(instruction, |register| {
            state[register.index()] = false;
            Ok::<(), OwnershipError>(())
        })?;
        match instruction {
            Instruction::Move { dst, src } if dst == src => {}
            Instruction::Move { dst, src } if dst != src => {
                if state[dst.index()] {
                    return Err(OwnershipError::OwnershipOverwrite {
                        function: candidate.id,
                        source_position: offset,
                        register: *dst,
                    });
                }
                state[src.index()] = false;
                state[dst.index()] = true;
            }
            Instruction::Drop { src } => state[src.index()] = false,
            Instruction::Return { src } => state[src.index()] = false,
            Instruction::Panic { message } => state[message.index()] = false,
            _ => {
                if let Some(dst) = instruction.written_register() {
                    if state[dst.index()] {
                        return Err(OwnershipError::OwnershipOverwrite {
                            function: candidate.id,
                            source_position: offset,
                            register: dst,
                        });
                    }
                    state[dst.index()] = true;
                }
            }
        }

        if matches!(
            instruction,
            Instruction::Return { .. } | Instruction::Panic { .. }
        ) && let Some(raw) = state.iter().position(|live| *live)
        {
            return Err(OwnershipError::OwnershipLeak {
                function: candidate.id,
                source_position: offset,
                register: Register::new(
                    u16::try_from(raw).expect("live register index is bounded by width"),
                ),
            });
        }
        for successor in ownership_successors(candidate, offset)
            .into_iter()
            .flatten()
        {
            match &mut incoming[successor] {
                None => {
                    incoming[successor] = Some(ownership_clone_copy(
                        &state,
                        OwnershipResource::ValidationCells,
                    )?);
                    queue.push_back(successor);
                }
                Some(expected) => {
                    if let Some((raw, (expected_live, actual_live))) = expected
                        .iter()
                        .zip(&state)
                        .enumerate()
                        .find(|(_, (expected_live, actual_live))| expected_live != actual_live)
                    {
                        return Err(OwnershipError::OwnershipJoin {
                            function: candidate.id,
                            candidate_instruction: offset,
                            successor,
                            register: Register::new(
                                u16::try_from(raw)
                                    .expect("join register index is bounded by width"),
                            ),
                            expected_live: *expected_live,
                            actual_live: *actual_live,
                        });
                    }
                }
            }
        }
    }
    Ok(counts)
}

/// Independently validate an ownership candidate and its witness.
///
/// This checker never uses the insertion pass's remaining-use counts,
/// topological order, liveness table, or layout builder. Linear functions use
/// definition/final-read positions. CFGs use per-register backward demand,
/// exact target and edge-block reconstruction, and exact-state join
/// simulation; the same algorithm reaches its own fixed point for cycles.
pub fn validate_ownership_candidate(
    source: &ValidatedProgram,
    candidate: ValidatedProgram,
    witness: OwnershipWitness,
    limits: OwnershipLimits,
) -> Result<OwnershipProgram, OwnershipError> {
    check_ownership_program_limits(source, limits, false)?;
    check_ownership_program_limits(&candidate, limits, true)?;
    if source.schema_version() != candidate.schema_version() || source.entry() != candidate.entry()
    {
        return Err(OwnershipError::ProgramIdentityChanged);
    }
    if witness.schema_version != OWNERSHIP_WITNESS_VERSION {
        return Err(OwnershipError::UnsupportedWitnessVersion {
            seen: witness.schema_version,
        });
    }
    if source.functions().len() != candidate.functions().len()
        || source.functions().len() != witness.functions.len()
    {
        return Err(OwnershipError::FunctionCount {
            source: source.functions().len(),
            candidate: candidate.functions().len(),
            witness: witness.functions.len(),
        });
    }

    let mut validation_cells = 0usize;
    let mut validation_steps = 0usize;
    for (index, ((source_function, candidate_function), row)) in source
        .functions()
        .iter()
        .zip(candidate.functions())
        .zip(&witness.functions)
        .enumerate()
    {
        if source_function.id != candidate_function.id || source_function.id != row.function {
            return Err(OwnershipError::FunctionRow {
                index,
                source: source_function.id,
                candidate: candidate_function.id,
                witness: row.function,
            });
        }
        if row.result_ownership != source_function.result_ownership {
            return Err(OwnershipError::WitnessResultOwnership {
                function: source_function.id,
                expected: source_function.result_ownership,
                actual: row.result_ownership,
            });
        }
        let expected_mode = validation_mode(source_function)?;
        if row.mode != expected_mode {
            return Err(OwnershipError::Mode {
                function: source_function.id,
                expected: expected_mode,
                actual: row.mode,
            });
        }
        let (
            drops,
            inferred_moves,
            redefinitions,
            edge_blocks,
            mut existing_drops,
            mut existing_moves,
            requires_state_validation,
            state_counts_are_existing,
        ) = match expected_mode {
            OwnershipMode::InsertedLinear | OwnershipMode::InsertedLinearReuse => {
                let (drops, inferred_moves, redefinitions) = validate_linear_candidate(
                    source_function,
                    candidate_function,
                    limits,
                    &mut validation_cells,
                    &mut validation_steps,
                )?;
                (drops, inferred_moves, redefinitions, 0, 0, 0, true, false)
            }
            mode @ (OwnershipMode::InsertedAcyclicCfg
            | OwnershipMode::InsertedAcyclicCfgReuse
            | OwnershipMode::InsertedCyclicCfg
            | OwnershipMode::InsertedCyclicCfgReuse) => {
                let (drops, edge_blocks, inferred_moves, redefinitions) = validate_cfg_candidate(
                    source_function,
                    candidate_function,
                    matches!(
                        mode,
                        OwnershipMode::InsertedAcyclicCfgReuse
                            | OwnershipMode::InsertedCyclicCfgReuse
                    ),
                    limits,
                    &mut validation_cells,
                    &mut validation_steps,
                )?;
                (
                    drops,
                    inferred_moves,
                    redefinitions,
                    edge_blocks,
                    0,
                    0,
                    true,
                    false,
                )
            }
            OwnershipMode::ValidatedExistingOwnership => {
                if source_function != candidate_function {
                    return Err(OwnershipError::PreservedFunctionChanged {
                        function: source_function.id,
                    });
                }
                (0, 0, 0, 0, 0, 0, true, true)
            }
            OwnershipMode::PreservedNonSsa => {
                if source_function != candidate_function {
                    return Err(OwnershipError::PreservedFunctionChanged {
                        function: source_function.id,
                    });
                }
                (0, 0, 0, 0, 0, 0, false, false)
            }
        };
        let (
            consumed_extern_args,
            consumed_call_args,
            consumed_closure_captures,
            consumed_apply_args,
            borrowed_intrinsic_results,
            raw_intrinsic_results,
            owned_callable_results,
            scalar_callable_results,
        ) = if requires_state_validation {
            let counts = validate_ownership_state(
                candidate_function,
                limits,
                &mut validation_cells,
                &mut validation_steps,
            )?;
            if state_counts_are_existing {
                existing_drops = counts.drops;
                existing_moves = counts.moves;
            }
            (
                counts.consumed_extern_args,
                counts.consumed_call_args,
                counts.consumed_closure_captures,
                counts.consumed_apply_args,
                counts.borrowed_intrinsic_results,
                counts.raw_intrinsic_results,
                counts.owned_callable_results,
                counts.scalar_callable_results,
            )
        } else {
            ownership_add(
                OwnershipResource::ValidationSteps,
                &mut validation_steps,
                candidate_function.code.len(),
                limits.max_validation_steps,
            )?;
            candidate_function.code.iter().fold(
                (
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                ),
                |(
                    extern_args,
                    call_args,
                    closure_captures,
                    apply_args,
                    borrowed_results,
                    raw_results,
                    owned_results,
                    scalar_results,
                ),
                 instruction| {
                    (
                        extern_args.saturating_add(consumed_extern_argument_count(instruction)),
                        call_args.saturating_add(consumed_call_argument_count(instruction)),
                        closure_captures
                            .saturating_add(consumed_closure_capture_count(instruction)),
                        apply_args.saturating_add(consumed_apply_argument_count(instruction)),
                        borrowed_results
                            .saturating_add(borrowed_intrinsic_result_count(instruction)),
                        raw_results.saturating_add(raw_intrinsic_result_count(instruction)),
                        owned_results.saturating_add(owned_callable_result_count(instruction)),
                        scalar_results.saturating_add(scalar_callable_result_count(instruction)),
                    )
                },
            )
        };
        let counts = [
            (
                OwnershipWitnessCount::SourceInstructions,
                source_function.code.len(),
                row.source_instructions,
            ),
            (
                OwnershipWitnessCount::EmittedInstructions,
                candidate_function.code.len(),
                row.emitted_instructions,
            ),
            (
                OwnershipWitnessCount::InsertedDrops,
                drops,
                row.inserted_drops,
            ),
            (
                OwnershipWitnessCount::InferredMoves,
                inferred_moves,
                row.inferred_moves,
            ),
            (
                OwnershipWitnessCount::ExistingDrops,
                existing_drops,
                row.existing_drops,
            ),
            (
                OwnershipWitnessCount::ExistingMoves,
                existing_moves,
                row.existing_moves,
            ),
            (
                OwnershipWitnessCount::Redefinitions,
                redefinitions,
                row.redefinitions,
            ),
            (
                OwnershipWitnessCount::EdgeBlocks,
                edge_blocks,
                row.edge_blocks,
            ),
            (
                OwnershipWitnessCount::ConsumedExternArgs,
                consumed_extern_args,
                row.consumed_extern_args,
            ),
            (
                OwnershipWitnessCount::ConsumedCallArgs,
                consumed_call_args,
                row.consumed_call_args,
            ),
            (
                OwnershipWitnessCount::ConsumedClosureCaptures,
                consumed_closure_captures,
                row.consumed_closure_captures,
            ),
            (
                OwnershipWitnessCount::ConsumedApplyArgs,
                consumed_apply_args,
                row.consumed_apply_args,
            ),
            (
                OwnershipWitnessCount::BorrowedIntrinsicResults,
                borrowed_intrinsic_results,
                row.borrowed_intrinsic_results,
            ),
            (
                OwnershipWitnessCount::RawIntrinsicResults,
                raw_intrinsic_results,
                row.raw_intrinsic_results,
            ),
            (
                OwnershipWitnessCount::OwnedCallableResults,
                owned_callable_results,
                row.owned_callable_results,
            ),
            (
                OwnershipWitnessCount::ScalarCallableResults,
                scalar_callable_results,
                row.scalar_callable_results,
            ),
        ];
        if let Some((count, expected, actual)) = counts
            .into_iter()
            .find(|(_, expected, actual)| expected != actual)
        {
            return Err(OwnershipError::WitnessCount {
                function: source_function.id,
                count,
                expected,
                actual,
            });
        }
    }
    Ok(OwnershipProgram {
        program: candidate,
        witness,
    })
}

#[cfg(test)]
mod codec_tests {
    use super::*;

    fn r(raw: u16) -> Register {
        Register::new(raw)
    }

    #[test]
    fn codec_and_ownership_resource_exhaustion_is_not_a_shape_refusal() {
        assert!(
            CodecError::ResourceLimit {
                resource: CodecResource::ArtifactBytes,
                limit: 0,
                observed: 1,
            }
            .is_resource_exhaustion()
        );
        assert!(!CodecError::BadMagic.is_resource_exhaustion());
        assert!(
            OwnershipError::AllocationFailure {
                resource: OwnershipResource::Functions,
                requested: 1,
            }
            .is_resource_exhaustion()
        );
        assert!(!OwnershipError::ProgramIdentityChanged.is_resource_exhaustion());
    }

    fn f(raw: u32) -> FunctionId {
        FunctionId::new(raw)
    }

    fn pc(raw: u32) -> Pc {
        Pc::new(raw)
    }

    fn function(id: u32, arity: u16, register_count: u16, code: Vec<Instruction>) -> Function {
        function_with_ownership(
            id,
            vec![ArgumentOwnership::Borrowed; usize::from(arity)],
            register_count,
            code,
        )
    }

    fn function_with_ownership(
        id: u32,
        parameter_ownership: Vec<ArgumentOwnership>,
        register_count: u16,
        code: Vec<Instruction>,
    ) -> Function {
        Function {
            id: f(id),
            arity: u16::try_from(parameter_ownership.len())
                .expect("test parameter ownership fits u16"),
            parameter_ownership,
            result_ownership: CallableResultOwnership::Scalar,
            register_count,
            code,
        }
    }

    fn minimal_program() -> ValidatedProgram {
        validate(Program::new(
            f(0),
            vec![function(
                0,
                0,
                1,
                vec![
                    Instruction::Nat {
                        dst: r(0),
                        value: 7,
                    },
                    Instruction::Return { src: r(0) },
                ],
            )],
        ))
        .expect("minimal FLBC is valid")
    }

    fn string_program() -> ValidatedProgram {
        validate(Program::new(
            f(0),
            vec![function(
                0,
                0,
                1,
                vec![
                    Instruction::String {
                        dst: r(0),
                        value: "payload".to_string(),
                    },
                    Instruction::Return { src: r(0) },
                ],
            )],
        ))
        .expect("String FLBC is valid")
    }

    fn every_opcode_program() -> ValidatedProgram {
        validate(Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    10,
                    vec![
                        Instruction::Nat {
                            dst: r(0),
                            value: 0,
                        },
                        Instruction::String {
                            dst: r(1),
                            value: "value".to_string(),
                        },
                        Instruction::Copy {
                            dst: r(2),
                            src: r(1),
                        },
                        Instruction::Move {
                            dst: r(3),
                            src: r(2),
                        },
                        Instruction::Drop { src: r(3) },
                        Instruction::Ctor {
                            dst: r(4),
                            tag: 1,
                            fields: vec![r(0), r(1)],
                            scalar_bytes: vec![0xA5, 0x5A],
                        },
                        Instruction::CtorField {
                            dst: r(3),
                            src: r(4),
                            expected_tag: 1,
                            expected_fields: 2,
                            field: 1,
                        },
                        Instruction::Array {
                            dst: r(5),
                            items: vec![r(4), r(3)],
                        },
                        Instruction::Intrinsic {
                            dst: r(6),
                            row: "extern:Array.size".to_string(),
                            args: vec![r(5)],
                            argument_ownership: vec![ArgumentOwnership::Borrowed],
                            result_ownership: ResultOwnership::RawObject,
                        },
                        Instruction::Closure {
                            dst: r(7),
                            function: f(1),
                            captures: vec![r(1)],
                            capture_ownership: vec![ArgumentOwnership::Borrowed],
                        },
                        Instruction::Apply {
                            dst: r(8),
                            closure: r(7),
                            args: vec![r(1)],
                            argument_ownership: vec![ArgumentOwnership::Borrowed],
                            result_ownership: CallableResultOwnership::Scalar,
                        },
                        Instruction::Call {
                            dst: r(9),
                            function: f(2),
                            args: vec![r(1)],
                            argument_ownership: vec![ArgumentOwnership::Borrowed],
                            result_ownership: CallableResultOwnership::Scalar,
                        },
                        Instruction::JumpIfZero {
                            cond: r(0),
                            zero: pc(13),
                            nonzero: pc(13),
                        },
                        Instruction::Jump { target: pc(14) },
                        Instruction::CheckSystem {
                            module_name: "Every.Opcode".to_string(),
                        },
                        Instruction::CheckSystemValue { module_name: r(1) },
                        Instruction::Return { src: r(9) },
                    ],
                ),
                function(
                    1,
                    2,
                    3,
                    vec![
                        Instruction::Copy {
                            dst: r(2),
                            src: r(0),
                        },
                        Instruction::Return { src: r(2) },
                    ],
                ),
                function(2, 1, 1, vec![Instruction::Return { src: r(0) }]),
                function(
                    3,
                    0,
                    1,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "panic".to_string(),
                        },
                        Instruction::Panic { message: r(0) },
                    ],
                ),
            ],
        ))
        .expect("the complete opcode fixture is valid")
    }

    fn ownership_source_program() -> ValidatedProgram {
        validate(Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    4,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "unused".to_string(),
                        },
                        Instruction::String {
                            dst: r(1),
                            value: "returned".to_string(),
                        },
                        Instruction::Copy {
                            dst: r(2),
                            src: r(1),
                        },
                        Instruction::Nat {
                            dst: r(3),
                            value: 7,
                        },
                        Instruction::Return { src: r(2) },
                    ],
                ),
                function(
                    1,
                    2,
                    3,
                    vec![
                        Instruction::Copy {
                            dst: r(2),
                            src: r(0),
                        },
                        Instruction::Return { src: r(2) },
                    ],
                ),
                function(
                    2,
                    0,
                    1,
                    vec![
                        Instruction::Nat {
                            dst: r(0),
                            value: 0,
                        },
                        Instruction::JumpIfZero {
                            cond: r(0),
                            zero: pc(2),
                            nonzero: pc(2),
                        },
                        Instruction::Return { src: r(0) },
                    ],
                ),
                function(
                    3,
                    0,
                    2,
                    vec![
                        Instruction::Nat {
                            dst: r(0),
                            value: 1,
                        },
                        Instruction::Drop { src: r(0) },
                        Instruction::Nat {
                            dst: r(1),
                            value: 2,
                        },
                        Instruction::Return { src: r(1) },
                    ],
                ),
                function(
                    4,
                    0,
                    1,
                    vec![
                        Instruction::Nat {
                            dst: r(0),
                            value: 1,
                        },
                        Instruction::Nat {
                            dst: r(0),
                            value: 2,
                        },
                        Instruction::Return { src: r(0) },
                    ],
                ),
                function(
                    5,
                    0,
                    2,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "unused-before-panic".to_string(),
                        },
                        Instruction::String {
                            dst: r(1),
                            value: "panic-message".to_string(),
                        },
                        Instruction::Panic { message: r(1) },
                    ],
                ),
                function(
                    6,
                    2,
                    3,
                    vec![
                        Instruction::Array {
                            dst: r(2),
                            items: vec![r(1), r(0)],
                        },
                        Instruction::Return { src: r(2) },
                    ],
                ),
            ],
        ))
        .expect("ownership source fixture is ordinarily valid")
    }

    fn cfg_ownership_source_program() -> ValidatedProgram {
        validate(Program::new(
            f(0),
            vec![function(
                0,
                0,
                4,
                vec![
                    Instruction::String {
                        dst: r(0),
                        value: "branch-owned".to_string(),
                    },
                    Instruction::String {
                        dst: r(1),
                        value: "shared-return".to_string(),
                    },
                    Instruction::Nat {
                        dst: r(2),
                        value: 0,
                    },
                    Instruction::JumpIfZero {
                        cond: r(2),
                        zero: pc(4),
                        nonzero: pc(6),
                    },
                    Instruction::Copy {
                        dst: r(3),
                        src: r(0),
                    },
                    Instruction::Jump { target: pc(7) },
                    Instruction::Jump { target: pc(7) },
                    Instruction::Return { src: r(1) },
                ],
            )],
        ))
        .expect("acyclic ownership fixture is ordinarily valid")
    }

    fn cyclic_ownership_source_program() -> ValidatedProgram {
        validate(Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    4,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "loop-return".to_string(),
                        },
                        Instruction::Nat {
                            dst: r(1),
                            value: 0,
                        },
                        Instruction::JumpIfZero {
                            cond: r(1),
                            zero: pc(6),
                            nonzero: pc(3),
                        },
                        Instruction::String {
                            dst: r(2),
                            value: "iteration-dead".to_string(),
                        },
                        Instruction::Copy {
                            dst: r(3),
                            src: r(0),
                        },
                        Instruction::Jump { target: pc(2) },
                        Instruction::Return { src: r(0) },
                    ],
                ),
                function(1, 0, 0, vec![Instruction::Jump { target: pc(0) }]),
                function(
                    2,
                    0,
                    1,
                    vec![
                        Instruction::Nat {
                            dst: r(0),
                            value: 1,
                        },
                        Instruction::Drop { src: r(0) },
                        Instruction::Jump { target: pc(2) },
                    ],
                ),
                function(
                    3,
                    0,
                    1,
                    vec![
                        Instruction::Nat {
                            dst: r(0),
                            value: 1,
                        },
                        Instruction::Nat {
                            dst: r(0),
                            value: 2,
                        },
                        Instruction::Jump { target: pc(1) },
                    ],
                ),
            ],
        ))
        .expect("cyclic ownership fixtures are ordinarily valid")
    }

    #[test]
    fn acyclic_cfg_ownership_uses_path_specific_edges_and_balances_joins() {
        let source = cfg_ownership_source_program();
        let inserted = insert_ownership(&source, OwnershipLimits::default())
            .expect("acyclic CFG ownership insertion");
        assert_eq!(
            inserted.witness().canonical_text(),
            concat!(
                "flbc-ownership/14\n",
                "function f0 mode=inserted-acyclic-cfg result=scalar source=8 emitted=16 drops=4 moves=1 redefs=0 edges=4 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
            )
        );
        assert_eq!(
            inserted.program().functions()[0].code,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "branch-owned".to_string(),
                },
                Instruction::String {
                    dst: r(1),
                    value: "shared-return".to_string(),
                },
                Instruction::Nat {
                    dst: r(2),
                    value: 0,
                },
                Instruction::JumpIfZero {
                    cond: r(2),
                    zero: pc(9),
                    nonzero: pc(11),
                },
                Instruction::Move {
                    dst: r(3),
                    src: r(0),
                },
                Instruction::Drop { src: r(3) },
                Instruction::Jump { target: pc(14) },
                Instruction::Jump { target: pc(15) },
                Instruction::Return { src: r(1) },
                Instruction::Drop { src: r(2) },
                Instruction::Jump { target: pc(4) },
                Instruction::Drop { src: r(0) },
                Instruction::Drop { src: r(2) },
                Instruction::Jump { target: pc(7) },
                Instruction::Jump { target: pc(8) },
                Instruction::Jump { target: pc(8) },
            ]
        );
        let canonical =
            encode_canonical(inserted.program(), CodecLimits::default()).expect("encode CFG");
        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    let repeated = insert_ownership(&source, OwnershipLimits::default())
                        .expect("threaded CFG ownership insertion");
                    (
                        repeated.witness().canonical_text(),
                        encode_canonical(repeated.program(), CodecLimits::default())
                            .expect("threaded CFG encoding"),
                    )
                }));
            }
            for join in joins {
                let (witness, bytes) = join.join().expect("CFG ownership worker");
                assert_eq!(witness, inserted.witness().canonical_text());
                assert_eq!(bytes, canonical);
            }
        });

        let mut omitted_move = inserted.program.program.clone();
        omitted_move.functions[0].code[4] = Instruction::Copy {
            dst: r(3),
            src: r(0),
        };
        let omitted_move =
            validate(omitted_move).expect("retaining the edge-local copy remains ordinary FLBC");
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                omitted_move,
                inserted.witness.clone(),
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::SkeletonMismatch {
                function,
                source_instruction: 4,
                candidate_instruction: 4,
            }) if function == f(0)
        ));

        let mut reversed_edge_drops = inserted.program.program.clone();
        reversed_edge_drops.functions[0].code.swap(11, 12);
        let reversed_edge_drops =
            validate(reversed_edge_drops).expect("reversed edge drops remain ordinary FLBC");
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                reversed_edge_drops,
                inserted.witness.clone(),
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::EdgeDropSchedule {
                function,
                source_instruction: 3,
                edge: 1,
                expected: Some(expected),
                actual: Some(actual),
            }) if function == f(0) && expected == r(0) && actual == r(2)
        ));

        let mut swapped_branch_edges = inserted.program.program.clone();
        assert!(matches!(
            swapped_branch_edges.functions[0].code[3],
            Instruction::JumpIfZero { .. }
        ));
        if let Instruction::JumpIfZero { zero, nonzero, .. } =
            &mut swapped_branch_edges.functions[0].code[3]
        {
            std::mem::swap(zero, nonzero);
        }
        let swapped_branch_edges =
            validate(swapped_branch_edges).expect("swapped branch edges remain ordinary FLBC");
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                swapped_branch_edges,
                inserted.witness.clone(),
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::ControlTarget {
                function,
                source_instruction: 3,
                edge: 0,
                expected,
                actual,
            }) if function == f(0) && expected == pc(9) && actual == pc(11)
        ));

        let mut wrong_edge_target = inserted.program.program.clone();
        wrong_edge_target.functions[0].code[14] = Instruction::Jump { target: pc(15) };
        let wrong_edge_target =
            validate(wrong_edge_target).expect("wrong edge target remains ordinary FLBC");
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                wrong_edge_target,
                inserted.witness.clone(),
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::ControlTarget {
                function,
                source_instruction: 5,
                edge: 0,
                expected,
                actual,
            }) if function == f(0) && expected == pc(8) && actual == pc(15)
        ));

        let mut forged_witness = inserted.witness.clone();
        forged_witness.functions[0].edge_blocks =
            forged_witness.functions[0].edge_blocks.saturating_add(1);
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                inserted.program.clone(),
                forged_witness,
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::WitnessCount {
                function,
                count: OwnershipWitnessCount::EdgeBlocks,
                expected: 4,
                actual: 5,
            }) if function == f(0)
        ));
    }

    #[test]
    fn acyclic_cfg_ownership_accepts_a_backward_numbered_edge() {
        let source = validate(Program::new(
            f(0),
            vec![function(
                0,
                0,
                2,
                vec![
                    Instruction::Nat {
                        dst: r(0),
                        value: 0,
                    },
                    Instruction::Jump { target: pc(4) },
                    Instruction::String {
                        dst: r(1),
                        value: "backward-target".to_string(),
                    },
                    Instruction::Return { src: r(0) },
                    Instruction::Jump { target: pc(2) },
                ],
            )],
        ))
        .expect("backward-numbered acyclic CFG is ordinarily valid");
        let inserted = insert_ownership(&source, OwnershipLimits::default())
            .expect("topological ownership insertion must not assume PC order");
        assert_eq!(
            inserted.witness().canonical_text(),
            concat!(
                "flbc-ownership/14\n",
                "function f0 mode=inserted-acyclic-cfg result=scalar source=5 emitted=8 drops=1 moves=0 redefs=0 edges=2 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
            )
        );
        assert_eq!(
            inserted.program().functions()[0].code,
            vec![
                Instruction::Nat {
                    dst: r(0),
                    value: 0,
                },
                Instruction::Jump { target: pc(6) },
                Instruction::String {
                    dst: r(1),
                    value: "backward-target".to_string(),
                },
                Instruction::Drop { src: r(1) },
                Instruction::Return { src: r(0) },
                Instruction::Jump { target: pc(7) },
                Instruction::Jump { target: pc(5) },
                Instruction::Jump { target: pc(2) },
            ]
        );
    }

    #[test]
    fn acyclic_cfg_ownership_balances_return_and_panic_terminals() {
        let source = validate(Program::new(
            f(0),
            vec![function(
                0,
                0,
                3,
                vec![
                    Instruction::String {
                        dst: r(0),
                        value: "returned".to_string(),
                    },
                    Instruction::String {
                        dst: r(1),
                        value: "panicked".to_string(),
                    },
                    Instruction::Nat {
                        dst: r(2),
                        value: 0,
                    },
                    Instruction::JumpIfZero {
                        cond: r(2),
                        zero: pc(4),
                        nonzero: pc(5),
                    },
                    Instruction::Return { src: r(0) },
                    Instruction::Panic { message: r(1) },
                ],
            )],
        ))
        .expect("return/panic acyclic CFG is ordinarily valid");
        let inserted = insert_ownership(&source, OwnershipLimits::default())
            .expect("return/panic ownership insertion");
        assert_eq!(
            inserted.witness().canonical_text(),
            concat!(
                "flbc-ownership/14\n",
                "function f0 mode=inserted-acyclic-cfg result=scalar source=6 emitted=12 drops=4 moves=0 redefs=0 edges=2 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
            )
        );
        assert_eq!(
            inserted.program().functions()[0].code,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "returned".to_string(),
                },
                Instruction::String {
                    dst: r(1),
                    value: "panicked".to_string(),
                },
                Instruction::Nat {
                    dst: r(2),
                    value: 0,
                },
                Instruction::JumpIfZero {
                    cond: r(2),
                    zero: pc(6),
                    nonzero: pc(9),
                },
                Instruction::Return { src: r(0) },
                Instruction::Panic { message: r(1) },
                Instruction::Drop { src: r(1) },
                Instruction::Drop { src: r(2) },
                Instruction::Jump { target: pc(4) },
                Instruction::Drop { src: r(0) },
                Instruction::Drop { src: r(2) },
                Instruction::Jump { target: pc(5) },
            ]
        );
    }

    #[test]
    fn acyclic_cfg_ownership_resources_are_typed_and_nonpublishing() {
        let source = cfg_ownership_source_program();
        let default = OwnershipLimits::default();
        let cases = [
            (
                OwnershipLimits {
                    max_cfg_edges: 7,
                    ..default
                },
                OwnershipResource::CfgEdges,
                7,
                8,
            ),
            (
                OwnershipLimits {
                    max_liveness_cells: 31,
                    ..default
                },
                OwnershipResource::LivenessCells,
                31,
                32,
            ),
            (
                OwnershipLimits {
                    max_liveness_steps: 66,
                    ..default
                },
                OwnershipResource::LivenessSteps,
                66,
                68,
            ),
            (
                OwnershipLimits {
                    max_validation_cells: 63,
                    ..default
                },
                OwnershipResource::ValidationCells,
                63,
                64,
            ),
            (
                OwnershipLimits {
                    max_validation_steps: 11,
                    ..default
                },
                OwnershipResource::ValidationSteps,
                11,
                12,
            ),
        ];
        for (limits, resource, limit, observed) in cases {
            assert_eq!(
                insert_ownership(&source, limits),
                Err(OwnershipError::ResourceLimit {
                    resource,
                    limit,
                    observed,
                })
            );
        }
    }

    #[test]
    fn cyclic_cfg_ownership_reaches_a_fixed_point_and_balances_backedges() {
        let source = cyclic_ownership_source_program();
        let loop_function = &source.functions()[0];
        let mut liveness_cells = 0;
        let mut liveness_steps = 0;
        let fixed = insertion_cyclic_liveness(
            loop_function,
            OwnershipLimits::default(),
            &mut liveness_cells,
            &mut liveness_steps,
        )
        .expect("cyclic liveness reaches its monotone fixed point");
        assert_eq!(
            fixed,
            vec![
                vec![false, false, false, false],
                vec![true, false, false, false],
                vec![true, true, false, false],
                vec![true, true, false, false],
                vec![true, true, false, false],
                vec![true, true, false, false],
                vec![true, false, false, false],
            ]
        );

        let mut one_pass_cells = 0;
        let mut one_pass_steps = 0;
        let source_order: Vec<_> = (0..loop_function.code.len()).collect();
        let one_pass = insertion_acyclic_liveness(
            loop_function,
            &source_order,
            OwnershipLimits::default(),
            &mut one_pass_cells,
            &mut one_pass_steps,
        )
        .expect("the explicit one-pass mutant remains bounded");
        assert!(!one_pass[5][r(1).index()]);
        assert!(fixed[5][r(1).index()]);

        let inserted = insert_ownership(&source, OwnershipLimits::default())
            .expect("cyclic CFG ownership insertion");
        assert_eq!(
            inserted.witness().canonical_text(),
            concat!(
                "flbc-ownership/14\n",
                "function f0 mode=inserted-cyclic-cfg result=scalar source=7 emitted=13 drops=3 moves=0 redefs=0 edges=3 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
                "function f1 mode=inserted-cyclic-cfg result=scalar source=1 emitted=2 drops=0 moves=0 redefs=0 edges=1 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
                "function f2 mode=validated-existing-ownership result=scalar source=3 emitted=3 drops=0 moves=0 existing_drops=1 existing_moves=0 redefs=0 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
                "function f3 mode=inserted-cyclic-cfg-reuse result=scalar source=3 emitted=6 drops=2 moves=0 redefs=1 edges=1 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
            )
        );
        assert_eq!(
            inserted.program().functions()[0].code,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "loop-return".to_string(),
                },
                Instruction::Nat {
                    dst: r(1),
                    value: 0,
                },
                Instruction::JumpIfZero {
                    cond: r(1),
                    zero: pc(9),
                    nonzero: pc(11),
                },
                Instruction::String {
                    dst: r(2),
                    value: "iteration-dead".to_string(),
                },
                Instruction::Drop { src: r(2) },
                Instruction::Copy {
                    dst: r(3),
                    src: r(0),
                },
                Instruction::Drop { src: r(3) },
                Instruction::Jump { target: pc(12) },
                Instruction::Return { src: r(0) },
                Instruction::Drop { src: r(1) },
                Instruction::Jump { target: pc(8) },
                Instruction::Jump { target: pc(3) },
                Instruction::Jump { target: pc(2) },
            ]
        );
        assert_eq!(
            inserted.program().functions()[1].code,
            vec![
                Instruction::Jump { target: pc(1) },
                Instruction::Jump { target: pc(0) },
            ]
        );
        assert_eq!(
            inserted.program().functions()[2],
            source.functions()[2],
            "pre-owned cycles remain byte-for-byte preserved"
        );
        assert_eq!(
            inserted.program().functions()[3].code,
            vec![
                Instruction::Nat {
                    dst: r(0),
                    value: 1,
                },
                Instruction::Drop { src: r(0) },
                Instruction::Nat {
                    dst: r(0),
                    value: 2,
                },
                Instruction::Drop { src: r(0) },
                Instruction::Jump { target: pc(5) },
                Instruction::Jump { target: pc(2) },
            ],
            "supported cyclic reuse retires both overwritten scalar epochs"
        );

        let canonical =
            encode_canonical(inserted.program(), CodecLimits::default()).expect("encode cycle");
        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    let repeated = insert_ownership(&source, OwnershipLimits::default())
                        .expect("threaded cyclic ownership insertion");
                    (
                        repeated.witness().canonical_text(),
                        encode_canonical(repeated.program(), CodecLimits::default())
                            .expect("threaded cyclic encoding"),
                    )
                }));
            }
            for join in joins {
                let (witness, bytes) = join.join().expect("cyclic ownership worker");
                assert_eq!(witness, inserted.witness().canonical_text());
                assert_eq!(bytes, canonical);
            }
        });

        let backedge_source = validate(Program::new(
            f(0),
            vec![function(
                0,
                0,
                4,
                vec![
                    Instruction::Nat {
                        dst: r(0),
                        value: 1,
                    },
                    Instruction::Jump { target: pc(2) },
                    Instruction::String {
                        dst: r(1),
                        value: "backedge-first".to_string(),
                    },
                    Instruction::String {
                        dst: r(2),
                        value: "backedge-second".to_string(),
                    },
                    Instruction::JumpIfZero {
                        cond: r(0),
                        zero: pc(2),
                        nonzero: pc(5),
                    },
                    Instruction::Copy {
                        dst: r(3),
                        src: r(2),
                    },
                    Instruction::Return { src: r(1) },
                ],
            )],
        ))
        .expect("two-drop backedge fixture is ordinary valid FLBC");
        let backedge_inserted = insert_ownership(&backedge_source, OwnershipLimits::default())
            .expect("two-drop backedge insertion");
        assert_eq!(
            backedge_inserted.witness().canonical_text(),
            concat!(
                "flbc-ownership/14\n",
                "function f0 mode=inserted-cyclic-cfg result=scalar source=7 emitted=14 drops=4 moves=1 redefs=0 edges=3 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
            )
        );
        assert_eq!(
            backedge_inserted.program().functions()[0].code[5],
            Instruction::Move {
                dst: r(3),
                src: r(2),
            },
            "the exit-only final copy transfers ownership"
        );
        assert_eq!(
            &backedge_inserted.program().functions()[0].code[9..=10],
            &[
                Instruction::Drop { src: r(1) },
                Instruction::Drop { src: r(2) },
            ]
        );
        let mut reversed_backedge_drops = backedge_inserted.program.program.clone();
        reversed_backedge_drops.functions[0].code.swap(9, 10);
        let reversed_backedge_drops = validate(reversed_backedge_drops)
            .expect("reversed backedge drops remain ordinary FLBC");
        assert!(matches!(
            validate_ownership_candidate(
                &backedge_source,
                reversed_backedge_drops,
                backedge_inserted.witness.clone(),
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::EdgeDropSchedule {
                function,
                source_instruction: 4,
                edge: 0,
                expected: Some(expected),
                actual: Some(actual),
            }) if function == f(0) && expected == r(1) && actual == r(2)
        ));

        let mut missing_exit_drop = inserted.program.program.clone();
        missing_exit_drop.functions[0].code[9] = Instruction::Nat {
            dst: r(1),
            value: 0,
        };
        let missing_exit_drop =
            validate(missing_exit_drop).expect("missing exit drop remains ordinary FLBC");
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                missing_exit_drop,
                inserted.witness.clone(),
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::EdgeDropSchedule {
                function,
                source_instruction: 2,
                edge: 0,
                expected: Some(expected),
                actual: None,
            }) if function == f(0) && expected == r(1)
        ));

        let mut wrong_backedge_target = inserted.program.program.clone();
        wrong_backedge_target.functions[0].code[12] = Instruction::Jump { target: pc(3) };
        let wrong_backedge_target =
            validate(wrong_backedge_target).expect("wrong backedge target remains ordinary FLBC");
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                wrong_backedge_target,
                inserted.witness.clone(),
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::ControlTarget {
                function,
                source_instruction: 5,
                edge: 0,
                expected,
                actual,
            }) if function == f(0) && expected == pc(2) && actual == pc(3)
        ));

        let mut forged_mode = inserted.witness.clone();
        forged_mode.functions[0].mode = OwnershipMode::InsertedAcyclicCfg;
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                inserted.program.clone(),
                forged_mode,
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::Mode {
                function,
                expected: OwnershipMode::InsertedCyclicCfg,
                actual: OwnershipMode::InsertedAcyclicCfg,
            }) if function == f(0)
        ));
    }

    #[test]
    fn cyclic_cfg_ownership_resources_are_typed_and_nonpublishing() {
        let source = cyclic_ownership_source_program();
        let default = OwnershipLimits::default();
        let cases = [
            (
                OwnershipLimits {
                    max_cfg_edges: 13,
                    ..default
                },
                OwnershipResource::CfgEdges,
                13,
                14,
            ),
            (
                OwnershipLimits {
                    max_liveness_cells: 27,
                    ..default
                },
                OwnershipResource::LivenessCells,
                27,
                28,
            ),
            (
                OwnershipLimits {
                    max_liveness_steps: 5,
                    ..default
                },
                OwnershipResource::LivenessSteps,
                5,
                6,
            ),
            (
                OwnershipLimits {
                    max_validation_cells: 55,
                    ..default
                },
                OwnershipResource::ValidationCells,
                55,
                56,
            ),
            (
                OwnershipLimits {
                    max_validation_steps: 10,
                    ..default
                },
                OwnershipResource::ValidationSteps,
                10,
                11,
            ),
        ];
        for (limits, resource, limit, observed) in cases {
            assert_eq!(
                insert_ownership(&source, limits),
                Err(OwnershipError::ResourceLimit {
                    resource,
                    limit,
                    observed,
                })
            );
        }

        let changed_self_loop = function(
            0,
            1,
            1,
            vec![Instruction::JumpIfZero {
                cond: r(0),
                zero: pc(0),
                nonzero: pc(0),
            }],
        );
        let mut liveness_cells = 0;
        let mut liveness_steps = 0;
        assert_eq!(
            insertion_cyclic_liveness(
                &changed_self_loop,
                OwnershipLimits {
                    max_liveness_steps: 6,
                    ..default
                },
                &mut liveness_cells,
                &mut liveness_steps,
            ),
            Err(OwnershipError::ResourceLimit {
                resource: OwnershipResource::LivenessSteps,
                limit: 6,
                observed: 7,
            }),
            "the two changed-state predecessor edges are charged before either can be reprocessed"
        );
    }

    #[test]
    fn ownership_state_simulator_refuses_an_unequal_cfg_join() {
        let candidate = validate(Program::new(
            f(0),
            vec![function(
                0,
                0,
                3,
                vec![
                    Instruction::String {
                        dst: r(0),
                        value: "one-path-only".to_string(),
                    },
                    Instruction::String {
                        dst: r(1),
                        value: "shared-return".to_string(),
                    },
                    Instruction::Nat {
                        dst: r(2),
                        value: 0,
                    },
                    Instruction::JumpIfZero {
                        cond: r(2),
                        zero: pc(4),
                        nonzero: pc(6),
                    },
                    Instruction::Drop { src: r(0) },
                    Instruction::Jump { target: pc(7) },
                    Instruction::Jump { target: pc(7) },
                    Instruction::Return { src: r(1) },
                ],
            )],
        ))
        .expect("unequal ownership states remain ordinary valid FLBC");
        assert!(matches!(
            insert_ownership(&candidate, OwnershipLimits::default()),
            Err(OwnershipError::OwnershipJoin {
                function,
                candidate_instruction: 5,
                successor: 7,
                register,
                expected_live,
                actual_live,
            }) if function == f(0)
                && register == r(0)
                && expected_live
                && !actual_live
        ));
    }

    #[test]
    fn ownership_state_simulator_refuses_an_unequal_backedge_join() {
        let candidate = validate(Program::new(
            f(0),
            vec![function(
                0,
                0,
                2,
                vec![
                    Instruction::Nat {
                        dst: r(0),
                        value: 1,
                    },
                    Instruction::Move {
                        dst: r(0),
                        src: r(0),
                    },
                    Instruction::JumpIfZero {
                        cond: r(0),
                        zero: pc(5),
                        nonzero: pc(3),
                    },
                    Instruction::String {
                        dst: r(1),
                        value: "backedge-only".to_string(),
                    },
                    Instruction::Jump { target: pc(2) },
                    Instruction::Return { src: r(0) },
                ],
            )],
        ))
        .expect("unequal backedge states remain ordinary valid FLBC");
        assert!(matches!(
            insert_ownership(&candidate, OwnershipLimits::default()),
            Err(OwnershipError::OwnershipJoin {
                function,
                candidate_instruction: 4,
                successor: 2,
                register,
                expected_live,
                actual_live,
            }) if function == f(0)
                && register == r(1)
                && !expected_live
                && actual_live
        ));
    }

    #[test]
    fn linear_ownership_insertion_is_canonical_eager_and_independently_checked() {
        let source = ownership_source_program();
        let inserted = insert_ownership(&source, OwnershipLimits::default())
            .expect("bounded linear ownership insertion");
        assert_eq!(
            inserted.program().functions()[0].code,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "unused".to_string(),
                },
                Instruction::Drop { src: r(0) },
                Instruction::String {
                    dst: r(1),
                    value: "returned".to_string(),
                },
                Instruction::Move {
                    dst: r(2),
                    src: r(1),
                },
                Instruction::Nat {
                    dst: r(3),
                    value: 7,
                },
                Instruction::Drop { src: r(3) },
                Instruction::Return { src: r(2) },
            ]
        );
        assert_eq!(
            inserted.program().functions()[1].code,
            vec![
                Instruction::Drop { src: r(1) },
                Instruction::Move {
                    dst: r(2),
                    src: r(0),
                },
                Instruction::Return { src: r(2) },
            ]
        );
        assert_eq!(
            inserted.witness().canonical_text(),
            concat!(
                "flbc-ownership/14\n",
                "function f0 mode=inserted-linear result=scalar source=5 emitted=7 drops=2 moves=1 redefs=0 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
                "function f1 mode=inserted-linear result=scalar source=2 emitted=3 drops=1 moves=1 redefs=0 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
                "function f2 mode=inserted-acyclic-cfg result=scalar source=3 emitted=5 drops=0 moves=0 redefs=0 edges=2 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
                "function f3 mode=validated-existing-ownership result=scalar source=4 emitted=4 drops=0 moves=0 existing_drops=1 existing_moves=0 redefs=0 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
                "function f4 mode=inserted-linear-reuse result=scalar source=3 emitted=4 drops=1 moves=0 redefs=1 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
                "function f5 mode=inserted-linear result=scalar source=3 emitted=4 drops=1 moves=0 redefs=0 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
                "function f6 mode=inserted-linear result=scalar source=2 emitted=4 drops=2 moves=0 redefs=0 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
            )
        );
        assert_eq!(
            inserted.program().functions()[2].code,
            vec![
                Instruction::Nat {
                    dst: r(0),
                    value: 0,
                },
                Instruction::JumpIfZero {
                    cond: r(0),
                    zero: pc(3),
                    nonzero: pc(4),
                },
                Instruction::Return { src: r(0) },
                Instruction::Jump { target: pc(2) },
                Instruction::Jump { target: pc(2) },
            ],
            "same-target branches still receive two explicit edge identities"
        );
        assert_eq!(
            inserted.program().functions()[3],
            source.functions()[3],
            "preexisting ownership remains byte-for-byte preserved"
        );
        assert_eq!(
            inserted.program().functions()[4].code,
            vec![
                Instruction::Nat {
                    dst: r(0),
                    value: 1,
                },
                Instruction::Drop { src: r(0) },
                Instruction::Nat {
                    dst: r(0),
                    value: 2,
                },
                Instruction::Return { src: r(0) },
            ],
            "each overwritten linear value receives its own ownership epoch"
        );
        assert_eq!(
            inserted.program().functions()[5].code,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "unused-before-panic".to_string(),
                },
                Instruction::Drop { src: r(0) },
                Instruction::String {
                    dst: r(1),
                    value: "panic-message".to_string(),
                },
                Instruction::Panic { message: r(1) },
            ],
            "panic keeps only its terminal message live"
        );
        assert_eq!(
            inserted.program().functions()[6].code,
            vec![
                Instruction::Array {
                    dst: r(2),
                    items: vec![r(1), r(0)],
                },
                Instruction::Drop { src: r(0) },
                Instruction::Drop { src: r(1) },
                Instruction::Return { src: r(2) },
            ],
            "same-stage drops are ascending even when operand order is not"
        );

        let canonical =
            encode_canonical(inserted.program(), CodecLimits::default()).expect("encode candidate");
        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    let repeated = insert_ownership(&source, OwnershipLimits::default())
                        .expect("threaded ownership insertion");
                    (
                        repeated.witness().canonical_text(),
                        encode_canonical(repeated.program(), CodecLimits::default())
                            .expect("threaded ownership encoding"),
                    )
                }));
            }
            for join in joins {
                let (witness, bytes) = join.join().expect("ownership worker");
                assert_eq!(witness, inserted.witness().canonical_text());
                assert_eq!(bytes, canonical);
            }
        });
    }

    #[test]
    fn straight_line_register_reuse_is_epoch_bound_and_independently_checked() {
        let source = validate(Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    1,
                    vec![
                        Instruction::Nat {
                            dst: r(0),
                            value: 0,
                        },
                        Instruction::Return { src: r(0) },
                    ],
                ),
                function(
                    1,
                    1,
                    3,
                    vec![
                        Instruction::Copy {
                            dst: r(0),
                            src: r(0),
                        },
                        Instruction::Copy {
                            dst: r(1),
                            src: r(0),
                        },
                        Instruction::String {
                            dst: r(0),
                            value: "first".to_string(),
                        },
                        Instruction::String {
                            dst: r(0),
                            value: "second".to_string(),
                        },
                        Instruction::Copy {
                            dst: r(2),
                            src: r(0),
                        },
                        Instruction::Return { src: r(2) },
                    ],
                ),
            ],
        ))
        .expect("straight-line register reuse is ordinary valid FLBC");
        let inserted = insert_ownership(&source, OwnershipLimits::default())
            .expect("each straight-line definition receives an ownership epoch");
        assert_eq!(
            inserted.witness().canonical_text(),
            concat!(
                "flbc-ownership/14\n",
                "function f0 mode=inserted-linear result=scalar source=2 emitted=2 drops=0 moves=0 redefs=0 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
                "function f1 mode=inserted-linear-reuse result=scalar source=6 emitted=8 drops=2 moves=3 redefs=3 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
            )
        );
        assert_eq!(
            inserted.program().functions()[1].code,
            vec![
                Instruction::Move {
                    dst: r(0),
                    src: r(0),
                },
                Instruction::Move {
                    dst: r(1),
                    src: r(0),
                },
                Instruction::Drop { src: r(1) },
                Instruction::String {
                    dst: r(0),
                    value: "first".to_string(),
                },
                Instruction::Drop { src: r(0) },
                Instruction::String {
                    dst: r(0),
                    value: "second".to_string(),
                },
                Instruction::Move {
                    dst: r(2),
                    src: r(0),
                },
                Instruction::Return { src: r(2) },
            ]
        );

        let canonical =
            encode_canonical(inserted.program(), CodecLimits::default()).expect("encode reuse");
        let decoded =
            decode_canonical(&canonical, CodecLimits::default()).expect("decode ownership output");
        validate_ownership_candidate(
            &source,
            decoded,
            inserted.witness.clone(),
            OwnershipLimits::default(),
        )
        .expect("the independent checker accepts the decoded epoch schedule");
        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    let repeated = insert_ownership(&source, OwnershipLimits::default())
                        .expect("threaded register-reuse insertion");
                    (
                        repeated.witness().canonical_text(),
                        encode_canonical(repeated.program(), CodecLimits::default())
                            .expect("threaded register-reuse encoding"),
                    )
                }));
            }
            for join in joins {
                let (witness, bytes) = join.join().expect("register-reuse worker");
                assert_eq!(witness, inserted.witness().canonical_text());
                assert_eq!(bytes, canonical);
            }
        });

        let mut omitted_self_move = inserted.program.program.clone();
        omitted_self_move.functions[1].code[0] = Instruction::Copy {
            dst: r(0),
            src: r(0),
        };
        let omitted_self_move =
            validate(omitted_self_move).expect("self-copy remains ordinary valid FLBC");
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                omitted_self_move,
                inserted.witness.clone(),
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::SkeletonMismatch {
                function,
                source_instruction: 0,
                candidate_instruction: 0,
            }) if function == f(1)
        ));

        let mut missing_epoch_drop = inserted.program.program.clone();
        assert_eq!(
            missing_epoch_drop.functions[1].code.remove(2),
            Instruction::Drop { src: r(1) }
        );
        let missing_epoch_drop =
            validate(missing_epoch_drop).expect("missing epoch drop remains ordinary FLBC");
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                missing_epoch_drop,
                inserted.witness.clone(),
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::DropSchedule {
                function,
                source_position: 2,
                expected: Some(register),
                ..
            }) if function == f(1) && register == r(1)
        ));

        let mut forged_redefinitions = inserted.witness.clone();
        forged_redefinitions.functions[1].redefinitions = forged_redefinitions.functions[1]
            .redefinitions
            .saturating_add(1);
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                inserted.program.clone(),
                forged_redefinitions,
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::WitnessCount {
                function,
                count: OwnershipWitnessCount::Redefinitions,
                expected: 3,
                actual: 4,
            }) if function == f(1)
        ));
        assert_eq!(
            insert_ownership(
                &source,
                OwnershipLimits {
                    max_value_epochs: 5,
                    ..OwnershipLimits::default()
                },
            ),
            Err(OwnershipError::ResourceLimit {
                resource: OwnershipResource::ValueEpochs,
                limit: 5,
                observed: 6,
            })
        );

        let overlapping = validate(Program::new(
            f(0),
            vec![function(
                0,
                0,
                1,
                vec![
                    Instruction::Nat {
                        dst: r(0),
                        value: 0,
                    },
                    Instruction::Array {
                        dst: r(0),
                        items: vec![r(0)],
                    },
                    Instruction::Return { src: r(0) },
                ],
            )],
        ))
        .expect("read/write overlap is ordinary valid FLBC");
        let preserved = insert_ownership(&overlapping, OwnershipLimits::default())
            .expect("unsupported overlap remains explicit and unchanged");
        assert_eq!(preserved.program().functions(), overlapping.functions());
        assert_eq!(
            preserved.witness().canonical_text(),
            concat!(
                "flbc-ownership/14\n",
                "function f0 mode=preserved-non-ssa result=scalar source=3 emitted=3 drops=0 moves=0 redefs=0 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
            )
        );
        let mut validation_cells = 0;
        let mut validation_steps = 0;
        assert!(matches!(
            validate_ownership_state(
                &overlapping.functions()[0],
                OwnershipLimits::default(),
                &mut validation_cells,
                &mut validation_steps,
            ),
            Err(OwnershipError::OwnershipOverwrite {
                function,
                source_position: 1,
                register,
            }) if function == f(0) && register == r(0)
        ));
    }

    #[test]
    fn acyclic_cfg_register_reuse_retires_each_path_local_value() {
        let source = validate(Program::new(
            f(0),
            vec![function(
                0,
                0,
                4,
                vec![
                    Instruction::String {
                        dst: r(0),
                        value: "initial".to_string(),
                    },
                    Instruction::Nat {
                        dst: r(1),
                        value: 1,
                    },
                    Instruction::JumpIfZero {
                        cond: r(1),
                        zero: pc(3),
                        nonzero: pc(5),
                    },
                    Instruction::String {
                        dst: r(0),
                        value: "zero".to_string(),
                    },
                    Instruction::Jump { target: pc(6) },
                    Instruction::String {
                        dst: r(0),
                        value: "nonzero".to_string(),
                    },
                    Instruction::Copy {
                        dst: r(2),
                        src: r(0),
                    },
                    Instruction::Return { src: r(2) },
                ],
            )],
        ))
        .expect("acyclic branch-local register reuse is ordinary valid FLBC");
        let inserted = insert_ownership(&source, OwnershipLimits::default())
            .expect("acyclic register reuse receives path-specific ownership");
        assert_eq!(
            inserted.witness().canonical_text(),
            concat!(
                "flbc-ownership/14\n",
                "function f0 mode=inserted-acyclic-cfg-reuse result=scalar source=8 emitted=14 drops=3 moves=1 redefs=2 edges=3 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
            )
        );
        assert_eq!(
            inserted.program().functions()[0].code,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "initial".to_string(),
                },
                Instruction::Drop { src: r(0) },
                Instruction::Nat {
                    dst: r(1),
                    value: 1,
                },
                Instruction::JumpIfZero {
                    cond: r(1),
                    zero: pc(9),
                    nonzero: pc(11),
                },
                Instruction::String {
                    dst: r(0),
                    value: "zero".to_string(),
                },
                Instruction::Jump { target: pc(13) },
                Instruction::String {
                    dst: r(0),
                    value: "nonzero".to_string(),
                },
                Instruction::Move {
                    dst: r(2),
                    src: r(0),
                },
                Instruction::Return { src: r(2) },
                Instruction::Drop { src: r(1) },
                Instruction::Jump { target: pc(4) },
                Instruction::Drop { src: r(1) },
                Instruction::Jump { target: pc(6) },
                Instruction::Jump { target: pc(7) },
            ]
        );
        assert_eq!(
            insert_ownership(
                &source,
                OwnershipLimits {
                    max_validation_cells: 3,
                    ..OwnershipLimits::default()
                },
            ),
            Err(OwnershipError::ResourceLimit {
                resource: OwnershipResource::ValidationCells,
                limit: 3,
                observed: 4,
            })
        );

        let canonical =
            encode_canonical(inserted.program(), CodecLimits::default()).expect("encode reuse CFG");
        let decoded =
            decode_canonical(&canonical, CodecLimits::default()).expect("decode reuse CFG");
        validate_ownership_candidate(
            &source,
            decoded,
            inserted.witness.clone(),
            OwnershipLimits::default(),
        )
        .expect("independent demand and state validation accept the decoded CFG");
        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    let repeated = insert_ownership(&source, OwnershipLimits::default())
                        .expect("threaded acyclic reuse insertion");
                    (
                        repeated.witness().canonical_text(),
                        encode_canonical(repeated.program(), CodecLimits::default())
                            .expect("threaded acyclic reuse encoding"),
                    )
                }));
            }
            for join in joins {
                let (witness, bytes) = join.join().expect("acyclic reuse worker");
                assert_eq!(witness, inserted.witness().canonical_text());
                assert_eq!(bytes, canonical);
            }
        });

        let mut missing_edge_drop = inserted.program.program.clone();
        missing_edge_drop.functions[0].code[9] = Instruction::Copy {
            dst: r(3),
            src: r(1),
        };
        let missing_edge_drop =
            validate(missing_edge_drop).expect("the edge-drop mutant is ordinary valid FLBC");
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                missing_edge_drop,
                inserted.witness.clone(),
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::EdgeDropSchedule {
                function,
                source_instruction: 2,
                edge: 0,
                expected: Some(register),
                actual: None,
            }) if function == f(0) && register == r(1)
        ));

        let mut wrong_edge_target = inserted.program.program.clone();
        let Instruction::JumpIfZero { zero, nonzero, .. } =
            &mut wrong_edge_target.functions[0].code[3]
        else {
            panic!("candidate instruction 3 remains the source branch");
        };
        *zero = pc(11);
        *nonzero = pc(9);
        let wrong_edge_target =
            validate(wrong_edge_target).expect("the retargeted candidate is ordinary valid FLBC");
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                wrong_edge_target,
                inserted.witness.clone(),
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::ControlTarget {
                function,
                source_instruction: 2,
                edge: 0,
                expected,
                actual,
            }) if function == f(0) && expected == pc(9) && actual == pc(11)
        ));

        let mut forged_redefinitions = inserted.witness.clone();
        forged_redefinitions.functions[0].redefinitions = 3;
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                inserted.program.clone(),
                forged_redefinitions,
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::WitnessCount {
                function,
                count: OwnershipWitnessCount::Redefinitions,
                expected: 2,
                actual: 3,
            }) if function == f(0)
        ));

        let entry_reuse = validate(Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    1,
                    vec![
                        Instruction::Nat {
                            dst: r(0),
                            value: 0,
                        },
                        Instruction::Return { src: r(0) },
                    ],
                ),
                function(
                    1,
                    1,
                    2,
                    vec![
                        Instruction::Nat {
                            dst: r(1),
                            value: 1,
                        },
                        Instruction::JumpIfZero {
                            cond: r(1),
                            zero: pc(2),
                            nonzero: pc(4),
                        },
                        Instruction::String {
                            dst: r(0),
                            value: "zero".to_string(),
                        },
                        Instruction::Jump { target: pc(5) },
                        Instruction::String {
                            dst: r(0),
                            value: "nonzero".to_string(),
                        },
                        Instruction::Return { src: r(0) },
                    ],
                ),
            ],
        ))
        .expect("both branches replace the entry parameter before use");
        let entry_owned = insert_ownership(&entry_reuse, OwnershipLimits::default())
            .expect("the dead entry epoch is retired before branch dispatch");
        assert_eq!(
            entry_owned.witness().canonical_text(),
            concat!(
                "flbc-ownership/14\n",
                "function f0 mode=inserted-linear result=scalar source=2 emitted=2 drops=0 moves=0 redefs=0 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
                "function f1 mode=inserted-acyclic-cfg-reuse result=scalar source=6 emitted=12 drops=3 moves=0 redefs=2 edges=3 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
            )
        );
        assert_eq!(
            entry_owned.program().functions()[1].code.first(),
            Some(&Instruction::Drop { src: r(0) }),
            "a parameter replaced on every path is retired at entry"
        );

        let cyclic = validate(Program::new(
            f(0),
            vec![function(
                0,
                0,
                1,
                vec![
                    Instruction::Nat {
                        dst: r(0),
                        value: 1,
                    },
                    Instruction::JumpIfZero {
                        cond: r(0),
                        zero: pc(4),
                        nonzero: pc(2),
                    },
                    Instruction::Nat {
                        dst: r(0),
                        value: 0,
                    },
                    Instruction::Jump { target: pc(1) },
                    Instruction::Return { src: r(0) },
                ],
            )],
        ))
        .expect("cyclic register reuse is ordinary valid FLBC");
        let inserted_cycle = insert_ownership(&cyclic, OwnershipLimits::default())
            .expect("cyclic register reuse reaches an ownership fixed point");
        assert_eq!(
            inserted_cycle.program().functions()[0].code,
            vec![
                Instruction::Nat {
                    dst: r(0),
                    value: 1,
                },
                Instruction::JumpIfZero {
                    cond: r(0),
                    zero: pc(5),
                    nonzero: pc(6),
                },
                Instruction::Nat {
                    dst: r(0),
                    value: 0,
                },
                Instruction::Jump { target: pc(8) },
                Instruction::Return { src: r(0) },
                Instruction::Jump { target: pc(4) },
                Instruction::Drop { src: r(0) },
                Instruction::Jump { target: pc(2) },
                Instruction::Jump { target: pc(1) },
            ]
        );
        assert_eq!(
            inserted_cycle.witness().canonical_text(),
            concat!(
                "flbc-ownership/14\n",
                "function f0 mode=inserted-cyclic-cfg-reuse result=scalar source=5 emitted=9 drops=1 moves=0 redefs=1 edges=3 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
            )
        );
    }

    #[test]
    fn cyclic_cfg_register_reuse_reaches_fixed_point_and_refuses_drift() {
        fn source(initial_condition: u64, next_condition: u64) -> ValidatedProgram {
            validate(Program::new(
                f(0),
                vec![function(
                    0,
                    0,
                    2,
                    vec![
                        Instruction::String {
                            dst: r(1),
                            value: "initial".to_string(),
                        },
                        Instruction::Nat {
                            dst: r(0),
                            value: initial_condition,
                        },
                        Instruction::JumpIfZero {
                            cond: r(0),
                            zero: pc(6),
                            nonzero: pc(3),
                        },
                        Instruction::String {
                            dst: r(1),
                            value: "iteration".to_string(),
                        },
                        Instruction::Nat {
                            dst: r(0),
                            value: next_condition,
                        },
                        Instruction::Jump { target: pc(2) },
                        Instruction::Return { src: r(1) },
                    ],
                )],
            ))
            .expect("cyclic register reuse is ordinary valid FLBC")
        }

        let source = source(1, 0);
        let inserted = insert_ownership(&source, OwnershipLimits::default())
            .expect("cyclic register reuse receives fixed-point ownership");
        assert_eq!(
            inserted.witness().canonical_text(),
            concat!(
                "flbc-ownership/14\n",
                "function f0 mode=inserted-cyclic-cfg-reuse result=scalar source=7 emitted=13 drops=3 moves=0 redefs=2 edges=3 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
            )
        );
        assert_eq!(
            inserted.program().functions()[0].code,
            vec![
                Instruction::String {
                    dst: r(1),
                    value: "initial".to_string(),
                },
                Instruction::Nat {
                    dst: r(0),
                    value: 1,
                },
                Instruction::JumpIfZero {
                    cond: r(0),
                    zero: pc(7),
                    nonzero: pc(9),
                },
                Instruction::String {
                    dst: r(1),
                    value: "iteration".to_string(),
                },
                Instruction::Nat {
                    dst: r(0),
                    value: 0,
                },
                Instruction::Jump { target: pc(12) },
                Instruction::Return { src: r(1) },
                Instruction::Drop { src: r(0) },
                Instruction::Jump { target: pc(6) },
                Instruction::Drop { src: r(0) },
                Instruction::Drop { src: r(1) },
                Instruction::Jump { target: pc(3) },
                Instruction::Jump { target: pc(2) },
            ]
        );

        let canonical = encode_canonical(inserted.program(), CodecLimits::default())
            .expect("cyclic reuse candidate encodes canonically");
        let decoded = decode_canonical(&canonical, CodecLimits::default())
            .expect("cyclic reuse candidate decodes");
        validate_ownership_candidate(
            &source,
            decoded,
            inserted.witness.clone(),
            OwnershipLimits::default(),
        )
        .expect("independent fixed point rebinds the decoded candidate");
        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    let repeated = insert_ownership(&source, OwnershipLimits::default())
                        .expect("threaded cyclic reuse insertion");
                    (
                        repeated.witness().canonical_text(),
                        encode_canonical(repeated.program(), CodecLimits::default())
                            .expect("threaded cyclic reuse encoding"),
                    )
                }));
            }
            for join in joins {
                let (witness, bytes) = join.join().expect("cyclic reuse worker");
                assert_eq!(witness, inserted.witness().canonical_text());
                assert_eq!(bytes, canonical);
            }
        });

        let mut missing_body_edge_drop = inserted.program.program.clone();
        missing_body_edge_drop.functions[0].code[10] = Instruction::Nat {
            dst: r(1),
            value: 0,
        };
        let missing_body_edge_drop = validate(missing_body_edge_drop)
            .expect("edge-retirement drift remains ordinary valid FLBC");
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                missing_body_edge_drop,
                inserted.witness.clone(),
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::EdgeDropSchedule {
                function,
                source_instruction: 2,
                edge: 1,
                expected: Some(register),
                actual: None,
            }) if function == f(0) && register == r(1)
        ));

        let mut wrong_body_edge = inserted.program.program.clone();
        let Instruction::JumpIfZero { zero, nonzero, .. } =
            &mut wrong_body_edge.functions[0].code[2]
        else {
            panic!("candidate instruction 2 remains the source branch");
        };
        *zero = pc(9);
        *nonzero = pc(7);
        let wrong_body_edge =
            validate(wrong_body_edge).expect("retargeted candidate remains ordinary valid FLBC");
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                wrong_body_edge,
                inserted.witness.clone(),
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::ControlTarget {
                function,
                source_instruction: 2,
                edge: 0,
                expected,
                actual,
            }) if function == f(0) && expected == pc(7) && actual == pc(9)
        ));

        let mut wrong_mode = inserted.witness.clone();
        wrong_mode.functions[0].mode = OwnershipMode::InsertedCyclicCfg;
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                inserted.program.clone(),
                wrong_mode,
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::Mode {
                function,
                expected: OwnershipMode::InsertedCyclicCfgReuse,
                actual: OwnershipMode::InsertedCyclicCfg,
            }) if function == f(0)
        ));
        let mut wrong_redefinitions = inserted.witness.clone();
        wrong_redefinitions.functions[0].redefinitions = 1;
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                inserted.program.clone(),
                wrong_redefinitions,
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::WitnessCount {
                function,
                count: OwnershipWitnessCount::Redefinitions,
                expected: 2,
                actual: 1,
            }) if function == f(0)
        ));

        assert!(matches!(
            insert_ownership(
                &source,
                OwnershipLimits {
                    max_liveness_steps: 1,
                    ..OwnershipLimits::default()
                },
            ),
            Err(OwnershipError::ResourceLimit {
                resource: OwnershipResource::LivenessSteps,
                limit: 1,
                observed,
            }) if observed > 1
        ));
        assert_eq!(
            insert_ownership(
                &source,
                OwnershipLimits {
                    max_validation_cells: 1,
                    ..OwnershipLimits::default()
                },
            ),
            Err(OwnershipError::ResourceLimit {
                resource: OwnershipResource::ValidationCells,
                limit: 1,
                observed: 2,
            })
        );

        let overlapping_cycle = validate(Program::new(
            f(0),
            vec![function(
                0,
                0,
                1,
                vec![
                    Instruction::Nat {
                        dst: r(0),
                        value: 1,
                    },
                    Instruction::JumpIfZero {
                        cond: r(0),
                        zero: pc(4),
                        nonzero: pc(2),
                    },
                    Instruction::Array {
                        dst: r(0),
                        items: vec![r(0)],
                    },
                    Instruction::Jump { target: pc(1) },
                    Instruction::Return { src: r(0) },
                ],
            )],
        ))
        .expect("cyclic read/write overlap is ordinary valid FLBC");
        let preserved = insert_ownership(&overlapping_cycle, OwnershipLimits::default())
            .expect("unsupported cyclic overlap stays explicit");
        assert_eq!(
            preserved.program().functions(),
            overlapping_cycle.functions()
        );
        assert_eq!(
            preserved.witness().functions[0].mode,
            OwnershipMode::PreservedNonSsa
        );
    }

    #[test]
    fn preexisting_move_and_drop_programs_remain_byte_for_byte_preserved() {
        let source = validate(Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    2,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "already-moved".to_string(),
                        },
                        Instruction::Move {
                            dst: r(1),
                            src: r(0),
                        },
                        Instruction::Return { src: r(1) },
                    ],
                ),
                function(
                    1,
                    0,
                    2,
                    vec![
                        Instruction::Nat {
                            dst: r(0),
                            value: 1,
                        },
                        Instruction::Drop { src: r(0) },
                        Instruction::Nat {
                            dst: r(1),
                            value: 2,
                        },
                        Instruction::Return { src: r(1) },
                    ],
                ),
                function(
                    2,
                    0,
                    1,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "self-move".to_string(),
                        },
                        Instruction::Move {
                            dst: r(0),
                            src: r(0),
                        },
                        Instruction::Return { src: r(0) },
                    ],
                ),
                function(
                    3,
                    0,
                    1,
                    vec![
                        Instruction::Nat {
                            dst: r(0),
                            value: 1,
                        },
                        Instruction::Drop { src: r(0) },
                        Instruction::Jump { target: pc(2) },
                    ],
                ),
            ],
        ))
        .expect("pre-owned functions are ordinary valid FLBC");
        let inserted = insert_ownership(&source, OwnershipLimits::default())
            .expect("pre-owned functions are preserved with a typed witness");
        assert_eq!(inserted.program().functions(), source.functions());
        assert_eq!(
            inserted.witness().canonical_text(),
            concat!(
                "flbc-ownership/14\n",
                "function f0 mode=validated-existing-ownership result=scalar source=3 emitted=3 drops=0 moves=0 existing_drops=0 existing_moves=1 redefs=0 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
                "function f1 mode=validated-existing-ownership result=scalar source=4 emitted=4 drops=0 moves=0 existing_drops=1 existing_moves=0 redefs=0 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
                "function f2 mode=validated-existing-ownership result=scalar source=3 emitted=3 drops=0 moves=0 existing_drops=0 existing_moves=1 redefs=0 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
                "function f3 mode=validated-existing-ownership result=scalar source=3 emitted=3 drops=0 moves=0 existing_drops=1 existing_moves=0 redefs=0 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
            )
        );
        let canonical =
            encode_canonical(inserted.program(), CodecLimits::default()).expect("encode pre-owned");
        let decoded =
            decode_canonical(&canonical, CodecLimits::default()).expect("decode pre-owned");
        validate_ownership_candidate(
            &source,
            decoded,
            inserted.witness.clone(),
            OwnershipLimits::default(),
        )
        .expect("decoded pre-owned bytes rebind to the independent state walk");
        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    let repeated = insert_ownership(&source, OwnershipLimits::default())
                        .expect("threaded pre-owned validation");
                    (
                        repeated.witness().canonical_text(),
                        encode_canonical(repeated.program(), CodecLimits::default())
                            .expect("threaded pre-owned encoding"),
                    )
                }));
            }
            for join in joins {
                let (witness, bytes) = join.join().expect("pre-owned worker");
                assert_eq!(witness, inserted.witness().canonical_text());
                assert_eq!(bytes, canonical);
            }
        });

        let mut forged_counts = inserted.witness.clone();
        forged_counts.functions[0].existing_moves =
            forged_counts.functions[0].existing_moves.saturating_add(1);
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                inserted.program.clone(),
                forged_counts,
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::WitnessCount {
                function,
                count: OwnershipWitnessCount::ExistingMoves,
                expected: 1,
                actual: 2,
            }) if function == f(0)
        ));
        assert!(matches!(
            insert_ownership(
                &source,
                OwnershipLimits {
                    max_validation_cells: 5,
                    ..OwnershipLimits::default()
                },
            ),
            Err(OwnershipError::ResourceLimit {
                resource: OwnershipResource::ValidationCells,
                limit: 5,
                observed: 6,
            })
        ));

        fn ordinary_preowned(register_count: u16, code: Vec<Instruction>) -> ValidatedProgram {
            validate(Program::new(
                f(0),
                vec![function(0, 0, register_count, code)],
            ))
            .expect("ownership mutant remains ordinary valid FLBC")
        }

        let live_destination = ordinary_preowned(
            2,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "source".to_string(),
                },
                Instruction::String {
                    dst: r(1),
                    value: "destination".to_string(),
                },
                Instruction::Move {
                    dst: r(1),
                    src: r(0),
                },
                Instruction::Return { src: r(1) },
            ],
        );
        assert!(matches!(
            insert_ownership(&live_destination, OwnershipLimits::default()),
            Err(OwnershipError::OwnershipOverwrite {
                source_position: 2,
                register,
                ..
            }) if register == r(1)
        ));

        let terminal_leak = ordinary_preowned(
            2,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "leaked".to_string(),
                },
                Instruction::Move {
                    dst: r(0),
                    src: r(0),
                },
                Instruction::String {
                    dst: r(1),
                    value: "returned".to_string(),
                },
                Instruction::Return { src: r(1) },
            ],
        );
        assert!(matches!(
            insert_ownership(&terminal_leak, OwnershipLimits::default()),
            Err(OwnershipError::OwnershipLeak {
                source_position: 3,
                register,
                ..
            }) if register == r(0)
        ));
    }

    #[test]
    fn ownership_validator_rejects_missing_drops_changed_skeleton_and_forged_witness() {
        let source = ownership_source_program();
        let inserted = insert_ownership(&source, OwnershipLimits::default())
            .expect("valid ownership candidate");

        let mut omitted_move = inserted.program.program.clone();
        assert!(matches!(
            omitted_move.functions[0].code[3],
            Instruction::Move { dst, src } if dst == r(2) && src == r(1)
        ));
        omitted_move.functions[0].code[3] = Instruction::Copy {
            dst: r(2),
            src: r(1),
        };
        let omitted_move =
            validate(omitted_move).expect("retaining the last-use copy remains ordinary FLBC");
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                omitted_move,
                inserted.witness.clone(),
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::SkeletonMismatch {
                function,
                source_instruction: 2,
                candidate_instruction: 3,
            }) if function == f(0)
        ));

        let mut missing_drop = inserted.program.program.clone();
        assert!(matches!(
            missing_drop.functions[0].code.remove(1),
            Instruction::Drop { src } if src == r(0)
        ));
        let missing_drop = validate(missing_drop).expect("missing drop remains ordinary FLBC");
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                missing_drop,
                inserted.witness.clone(),
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::DropSchedule {
                function,
                source_position: 1,
                expected: Some(register),
                actual: None,
            }) if function == f(0) && register == r(0)
        ));

        let mut reversed_drops = inserted.program.program.clone();
        reversed_drops.functions[6].code.swap(1, 2);
        let reversed_drops = validate(reversed_drops).expect("reversed drops remain ordinary FLBC");
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                reversed_drops,
                inserted.witness.clone(),
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::DropSchedule {
                function,
                source_position: 1,
                expected: Some(expected),
                actual: Some(actual),
            }) if function == f(6) && expected == r(0) && actual == r(1)
        ));

        let mut changed_skeleton = inserted.program.program.clone();
        let Instruction::String { value, .. } = &mut changed_skeleton.functions[0].code[0] else {
            panic!("fixture begins with a String");
        };
        *value = "mutated".to_string();
        let changed_skeleton =
            validate(changed_skeleton).expect("changed payload remains ordinary FLBC");
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                changed_skeleton,
                inserted.witness.clone(),
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::SkeletonMismatch {
                function,
                source_instruction: 0,
                candidate_instruction: 0,
            }) if function == f(0)
        ));

        let mut forged_witness = inserted.witness.clone();
        forged_witness.functions[0].inserted_drops =
            forged_witness.functions[0].inserted_drops.saturating_add(1);
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                inserted.program.clone(),
                forged_witness,
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::WitnessCount {
                function,
                count: OwnershipWitnessCount::InsertedDrops,
                expected: 2,
                actual: 3,
            }) if function == f(0)
        ));

        let mut forged_moves = inserted.witness.clone();
        forged_moves.functions[0].inferred_moves =
            forged_moves.functions[0].inferred_moves.saturating_add(1);
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                inserted.program.clone(),
                forged_moves,
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::WitnessCount {
                function,
                count: OwnershipWitnessCount::InferredMoves,
                expected: 1,
                actual: 2,
            }) if function == f(0)
        ));

        let wrong_version = OwnershipWitness::new(
            OWNERSHIP_WITNESS_VERSION.saturating_add(1),
            inserted.witness().functions().to_vec(),
        );
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                inserted.program.clone(),
                wrong_version,
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::UnsupportedWitnessVersion { seen })
                if seen == OWNERSHIP_WITNESS_VERSION.saturating_add(1)
        ));
    }

    #[test]
    fn ownership_validation_work_is_typed_and_failure_atomic() {
        let source = ownership_source_program();
        let default = OwnershipLimits::default();
        let cases = [
            (
                OwnershipLimits {
                    max_functions: 6,
                    ..default
                },
                OwnershipResource::Functions,
                6,
                7,
            ),
            (
                OwnershipLimits {
                    max_source_instructions: 4,
                    ..default
                },
                OwnershipResource::SourceInstructions,
                4,
                5,
            ),
            (
                OwnershipLimits {
                    max_emitted_instructions: 7,
                    ..default
                },
                OwnershipResource::EmittedInstructions,
                7,
                8,
            ),
            (
                OwnershipLimits {
                    max_registers: 3,
                    ..default
                },
                OwnershipResource::Registers,
                3,
                4,
            ),
            (
                OwnershipLimits {
                    max_operands: 13,
                    ..default
                },
                OwnershipResource::Operands,
                13,
                14,
            ),
            (
                OwnershipLimits {
                    max_payload_bytes: 5,
                    ..default
                },
                OwnershipResource::PayloadBytes,
                5,
                6,
            ),
            (
                OwnershipLimits {
                    max_validation_cells: 19,
                    ..default
                },
                OwnershipResource::ValidationCells,
                19,
                40,
            ),
        ];
        for (limits, resource, limit, observed) in cases {
            assert_eq!(
                insert_ownership(&source, limits),
                Err(OwnershipError::ResourceLimit {
                    resource,
                    limit,
                    observed,
                })
            );
        }
    }

    #[test]
    fn intrinsic_argument_ownership_is_consumptive_canonical_and_independently_bound() {
        fn owned_intrinsic(
            dst: Register,
            row: &str,
            args: Vec<Register>,
            argument_ownership: Vec<ArgumentOwnership>,
        ) -> Instruction {
            Instruction::Intrinsic {
                dst,
                row: row.to_string(),
                args,
                argument_ownership,
                result_ownership: ResultOwnership::Owned,
            }
        }

        let arity_drift = Program::new(
            f(0),
            vec![function(
                0,
                0,
                2,
                vec![
                    Instruction::Nat {
                        dst: r(0),
                        value: 1,
                    },
                    owned_intrinsic(r(1), "extern:Prototype.arity", vec![r(0)], Vec::new()),
                    Instruction::Return { src: r(1) },
                ],
            )],
        );
        assert!(matches!(
            validate(arity_drift),
            Err(ValidationError::IntrinsicOwnershipArity {
                arguments: 1,
                ownership: 0,
                ..
            })
        ));

        let duplicate_consume = Program::new(
            f(0),
            vec![function(
                0,
                0,
                2,
                vec![
                    Instruction::String {
                        dst: r(0),
                        value: "one token".to_string(),
                    },
                    owned_intrinsic(
                        r(1),
                        "extern:Prototype.doubleConsume",
                        vec![r(0), r(0)],
                        vec![ArgumentOwnership::Owned, ArgumentOwnership::Owned],
                    ),
                    Instruction::Return { src: r(1) },
                ],
            )],
        );
        assert!(matches!(
            validate(duplicate_consume),
            Err(ValidationError::IntrinsicConsumeAlias {
                register,
                first: 0,
                second: 1,
                ..
            }) if register == r(0)
        ));

        let unique_alias = Program::new(
            f(0),
            vec![function(
                0,
                0,
                2,
                vec![
                    Instruction::String {
                        dst: r(0),
                        value: "unique".to_string(),
                    },
                    owned_intrinsic(
                        r(1),
                        "extern:Prototype.unique",
                        vec![r(0), r(0)],
                        vec![ArgumentOwnership::Unique, ArgumentOwnership::Borrowed],
                    ),
                    Instruction::Return { src: r(1) },
                ],
            )],
        );
        assert!(matches!(
            validate(unique_alias),
            Err(ValidationError::IntrinsicUniqueAlias {
                register,
                unique: 0,
                alias: 1,
                ..
            }) if register == r(0)
        ));

        let use_after_consume = Program::new(
            f(0),
            vec![function(
                0,
                0,
                3,
                vec![
                    Instruction::String {
                        dst: r(0),
                        value: "consumed".to_string(),
                    },
                    owned_intrinsic(
                        r(1),
                        "extern:Prototype.consume",
                        vec![r(0)],
                        vec![ArgumentOwnership::Owned],
                    ),
                    Instruction::Copy {
                        dst: r(2),
                        src: r(0),
                    },
                    Instruction::Return { src: r(1) },
                ],
            )],
        );
        assert!(matches!(
            validate(use_after_consume),
            Err(ValidationError::ReadBeforeWrite { register, .. }) if register == r(0)
        ));

        let source = validate(Program::new(
            f(0),
            vec![function(
                0,
                0,
                3,
                vec![
                    Instruction::String {
                        dst: r(0),
                        value: "owned".to_string(),
                    },
                    Instruction::String {
                        dst: r(1),
                        value: "borrowed".to_string(),
                    },
                    owned_intrinsic(
                        r(2),
                        "extern:Prototype.consume",
                        vec![r(0), r(1)],
                        vec![ArgumentOwnership::Owned, ArgumentOwnership::Borrowed],
                    ),
                    Instruction::Return { src: r(2) },
                ],
            )],
        ))
        .expect("one owned and one borrowed intrinsic operand are valid");
        let limits = OwnershipLimits::default();
        let inserted = insert_ownership(&source, limits).expect("insert intrinsic ownership");
        assert_eq!(
            inserted.witness().canonical_text(),
            concat!(
                "flbc-ownership/14\n",
                "function f0 mode=inserted-linear result=scalar source=4 emitted=5 drops=1 moves=0 redefs=0 edges=0 extern_consumes=1 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
            )
        );
        assert!(matches!(
            &inserted.program().functions()[0].code[2],
            Instruction::Intrinsic {
                argument_ownership,
                ..
            } if argument_ownership
                == &[ArgumentOwnership::Owned, ArgumentOwnership::Borrowed]
        ));
        assert_eq!(
            inserted.program().functions()[0].code[3],
            Instruction::Drop { src: r(1) },
            "the dead borrowed operand is released after the call"
        );
        assert!(
            !inserted.program().functions()[0].code.iter().any(
                |instruction| matches!(instruction, Instruction::Drop { src } if *src == r(0))
            ),
            "the transferred operand is never dropped again"
        );

        let canonical =
            encode_canonical(inserted.program(), CodecLimits::default()).expect("encode modes");
        let decoded = decode_canonical(&canonical, CodecLimits::default()).expect("decode modes");
        assert_eq!(
            encode_canonical(&decoded, CodecLimits::default()).expect("re-encode modes"),
            canonical
        );
        validate_ownership_candidate(&source, decoded, inserted.witness.clone(), limits)
            .expect("decoded ownership candidate revalidates");

        let mut forged_count = inserted.witness.clone();
        forged_count.functions[0].consumed_extern_args = 0;
        assert!(matches!(
            validate_ownership_candidate(&source, inserted.program.clone(), forged_count, limits,),
            Err(OwnershipError::WitnessCount {
                count: OwnershipWitnessCount::ConsumedExternArgs,
                expected: 1,
                actual: 0,
                ..
            })
        ));

        let mut drift = inserted.program.program.clone();
        let Instruction::Intrinsic {
            argument_ownership, ..
        } = &mut drift.functions[0].code[2]
        else {
            panic!("candidate retains the intrinsic skeleton");
        };
        argument_ownership[0] = ArgumentOwnership::Unique;
        let drift = validate(drift).expect("consume-class drift remains ordinary valid FLBC");
        assert!(matches!(
            validate_ownership_candidate(&source, drift, inserted.witness.clone(), limits,),
            Err(OwnershipError::SkeletonMismatch { .. })
        ));

        let mut result_drift = inserted.program.program.clone();
        let Instruction::Intrinsic {
            result_ownership, ..
        } = &mut result_drift.functions[0].code[2]
        else {
            panic!("candidate retains the intrinsic result contract");
        };
        *result_ownership = ResultOwnership::Borrowed;
        let result_drift =
            validate(result_drift).expect("result-class drift remains ordinary valid FLBC");
        assert!(matches!(
            validate_ownership_candidate(&source, result_drift, inserted.witness.clone(), limits,),
            Err(OwnershipError::SkeletonMismatch { .. })
        ));

        let row = b"extern:Prototype.consume";
        let row_start = canonical
            .windows(row.len())
            .position(|window| window == row)
            .expect("intrinsic row bytes occur in the artifact");
        let ownership_tag = row_start
            .saturating_add(row.len())
            .saturating_add(4)
            .saturating_add(2 * 2)
            .saturating_add(4);
        let mut invalid_tag = canonical.clone();
        invalid_tag[ownership_tag] = 0xff;
        assert_eq!(
            decode_canonical(&invalid_tag, CodecLimits::default()),
            Err(CodecError::InvalidArgumentOwnership {
                tag: 0xff,
                offset: ownership_tag,
            })
        );
        let result_tag = ownership_tag.saturating_add(2);
        let mut invalid_result_tag = canonical.clone();
        invalid_result_tag[result_tag] = 0xff;
        assert_eq!(
            decode_canonical(&invalid_result_tag, CodecLimits::default()),
            Err(CodecError::InvalidResultOwnership {
                tag: 0xff,
                offset: result_tag,
            })
        );

        let expected_bytes = canonical;
        let expected_witness = inserted.witness().canonical_text();
        for _ in 0..8 {
            let repeated = insert_ownership(&source, limits).expect("repeat ownership");
            assert_eq!(
                encode_canonical(repeated.program(), CodecLimits::default()).expect("repeat bytes"),
                expected_bytes
            );
            assert_eq!(repeated.witness().canonical_text(), expected_witness);
        }
        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    let repeated = insert_ownership(&source, limits).expect("thread ownership");
                    (
                        encode_canonical(repeated.program(), CodecLimits::default())
                            .expect("thread bytes"),
                        repeated.witness().canonical_text(),
                    )
                }));
            }
            for join in joins {
                assert_eq!(
                    join.join().expect("ownership thread"),
                    (expected_bytes.clone(), expected_witness.clone())
                );
            }
        });

        assert_eq!(
            insert_ownership(
                &source,
                OwnershipLimits {
                    max_operands: 4,
                    ..limits
                },
            ),
            Err(OwnershipError::ResourceLimit {
                resource: OwnershipResource::Operands,
                limit: 4,
                observed: 5,
            })
        );
    }

    #[test]
    fn direct_call_parameter_ownership_is_consumptive_canonical_and_independently_bound() {
        fn direct_call(
            dst: Register,
            function: FunctionId,
            args: Vec<Register>,
            argument_ownership: Vec<ArgumentOwnership>,
        ) -> Instruction {
            Instruction::Call {
                dst,
                function,
                args,
                argument_ownership,
                result_ownership: CallableResultOwnership::Scalar,
            }
        }

        let function_arity_drift = Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    1,
                    vec![
                        Instruction::Nat {
                            dst: r(0),
                            value: 0,
                        },
                        Instruction::Return { src: r(0) },
                    ],
                ),
                Function {
                    id: f(1),
                    arity: 1,
                    parameter_ownership: Vec::new(),
                    result_ownership: CallableResultOwnership::Scalar,
                    register_count: 1,
                    code: vec![Instruction::Return { src: r(0) }],
                },
            ],
        );
        assert_eq!(
            validate(function_arity_drift),
            Err(ValidationError::FunctionOwnershipArity {
                function: f(1),
                parameters: 1,
                ownership: 0,
            })
        );

        let source = validate(Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    2,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "owned".to_string(),
                        },
                        Instruction::String {
                            dst: r(1),
                            value: "borrowed".to_string(),
                        },
                        direct_call(
                            r(0),
                            f(1),
                            vec![r(0), r(1)],
                            vec![ArgumentOwnership::Owned, ArgumentOwnership::Borrowed],
                        ),
                        Instruction::Return { src: r(0) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![ArgumentOwnership::Owned, ArgumentOwnership::Borrowed],
                    2,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        ))
        .expect("the call contract admits one owned and one borrowed argument");

        let mut ownership_arity_drift = source.program.clone();
        let Instruction::Call {
            argument_ownership, ..
        } = &mut ownership_arity_drift.functions[0].code[2]
        else {
            panic!("fixture retains its direct call");
        };
        argument_ownership.pop();
        assert_eq!(
            validate(ownership_arity_drift),
            Err(ValidationError::CallOwnershipArity {
                function: f(0),
                pc: pc(2),
                target: f(1),
                arguments: 2,
                ownership: 1,
            })
        );

        let mut contract_drift = source.program.clone();
        let Instruction::Call {
            argument_ownership, ..
        } = &mut contract_drift.functions[0].code[2]
        else {
            panic!("fixture retains its direct call");
        };
        argument_ownership[0] = ArgumentOwnership::Unique;
        assert_eq!(
            validate(contract_drift),
            Err(ValidationError::CallOwnershipContract {
                function: f(0),
                pc: pc(2),
                target: f(1),
                argument: 0,
                expected: ArgumentOwnership::Owned,
                actual: ArgumentOwnership::Unique,
            })
        );

        let duplicate_consume = Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    2,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "one token".to_string(),
                        },
                        direct_call(
                            r(1),
                            f(1),
                            vec![r(0), r(0)],
                            vec![ArgumentOwnership::Owned, ArgumentOwnership::Owned],
                        ),
                        Instruction::Return { src: r(1) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![ArgumentOwnership::Owned, ArgumentOwnership::Owned],
                    2,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        );
        assert!(matches!(
            validate(duplicate_consume),
            Err(ValidationError::CallConsumeAlias {
                target,
                register,
                first: 0,
                second: 1,
                ..
            }) if target == f(1) && register == r(0)
        ));

        let unique_alias = Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    2,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "unique".to_string(),
                        },
                        direct_call(
                            r(1),
                            f(1),
                            vec![r(0), r(0)],
                            vec![ArgumentOwnership::Unique, ArgumentOwnership::Borrowed],
                        ),
                        Instruction::Return { src: r(1) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![ArgumentOwnership::Unique, ArgumentOwnership::Borrowed],
                    2,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        );
        assert!(matches!(
            validate(unique_alias),
            Err(ValidationError::CallUniqueAlias {
                target,
                register,
                unique: 0,
                alias: 1,
                ..
            }) if target == f(1) && register == r(0)
        ));

        let use_after_consume = Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    3,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "consumed".to_string(),
                        },
                        direct_call(r(1), f(1), vec![r(0)], vec![ArgumentOwnership::Owned]),
                        Instruction::Copy {
                            dst: r(2),
                            src: r(0),
                        },
                        Instruction::Return { src: r(1) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![ArgumentOwnership::Owned],
                    1,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        );
        assert!(matches!(
            validate(use_after_consume),
            Err(ValidationError::ReadBeforeWrite {
                function,
                pc: at,
                register,
            }) if function == f(0) && at == pc(2) && register == r(0)
        ));

        let limits = OwnershipLimits::default();
        let inserted = insert_ownership(&source, limits).expect("insert direct-call ownership");
        let caller_witness = &inserted.witness().functions()[0];
        assert_eq!(caller_witness.consumed_call_args, 1);
        assert_eq!(caller_witness.consumed_extern_args, 0);
        assert_eq!(inserted.witness().functions()[1].consumed_call_args, 0);
        assert!(matches!(
            &inserted.program().functions()[0].code[2],
            Instruction::Call {
                dst,
                function,
                argument_ownership,
                ..
            } if *dst == r(0)
                && *function == f(1)
                && argument_ownership
                    == &[ArgumentOwnership::Owned, ArgumentOwnership::Borrowed]
        ));
        assert_eq!(
            inserted.program().functions()[0].code[3],
            Instruction::Drop { src: r(1) },
            "the borrowed argument remains caller-owned and is released after the call"
        );
        assert!(
            !inserted.program().functions()[0].code.iter().any(
                |instruction| matches!(instruction, Instruction::Drop { src } if *src == r(0))
            ),
            "the consumed register is immediately reusable for the call result"
        );
        assert_eq!(
            inserted.program().functions()[1].parameter_ownership,
            [ArgumentOwnership::Owned, ArgumentOwnership::Borrowed]
        );

        let canonical =
            encode_canonical(inserted.program(), CodecLimits::default()).expect("encode call");
        let decoded = decode_canonical(&canonical, CodecLimits::default()).expect("decode call");
        assert_eq!(
            encode_canonical(&decoded, CodecLimits::default()).expect("re-encode call"),
            canonical
        );
        validate_ownership_candidate(&source, decoded, inserted.witness.clone(), limits)
            .expect("decoded direct-call ownership rebinds independently");

        let mut forged_count = inserted.witness.clone();
        forged_count.functions[0].consumed_call_args = 0;
        assert!(matches!(
            validate_ownership_candidate(&source, inserted.program.clone(), forged_count, limits),
            Err(OwnershipError::WitnessCount {
                function,
                count: OwnershipWitnessCount::ConsumedCallArgs,
                expected: 1,
                actual: 0,
            }) if function == f(0)
        ));

        let expected_bytes = canonical;
        let expected_witness = inserted.witness().canonical_text();
        for _ in 0..8 {
            let repeated = insert_ownership(&source, limits).expect("repeat call ownership");
            assert_eq!(
                encode_canonical(repeated.program(), CodecLimits::default())
                    .expect("repeat call bytes"),
                expected_bytes
            );
            assert_eq!(repeated.witness().canonical_text(), expected_witness);
        }
        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    let repeated =
                        insert_ownership(&source, limits).expect("thread call ownership");
                    (
                        encode_canonical(repeated.program(), CodecLimits::default())
                            .expect("thread call bytes"),
                        repeated.witness().canonical_text(),
                    )
                }));
            }
            for join in joins {
                assert_eq!(
                    join.join().expect("call ownership thread"),
                    (expected_bytes.clone(), expected_witness.clone())
                );
            }
        });

        assert_eq!(
            insert_ownership(
                &source,
                OwnershipLimits {
                    max_operands: 7,
                    ..limits
                },
            ),
            Err(OwnershipError::ResourceLimit {
                resource: OwnershipResource::Operands,
                limit: 7,
                observed: 8,
            })
        );
    }

    #[test]
    fn closure_capture_ownership_is_consumptive_canonical_and_independently_bound() {
        fn closure(
            dst: Register,
            function: FunctionId,
            captures: Vec<Register>,
            capture_ownership: Vec<ArgumentOwnership>,
        ) -> Instruction {
            Instruction::Closure {
                dst,
                function,
                captures,
                capture_ownership,
            }
        }

        let source = validate(Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    3,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "owned capture".to_string(),
                        },
                        Instruction::String {
                            dst: r(1),
                            value: "borrowed capture".to_string(),
                        },
                        closure(
                            r(0),
                            f(1),
                            vec![r(0), r(1)],
                            vec![ArgumentOwnership::Owned, ArgumentOwnership::Borrowed],
                        ),
                        Instruction::Copy {
                            dst: r(2),
                            src: r(1),
                        },
                        Instruction::Return { src: r(0) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![
                        ArgumentOwnership::Owned,
                        ArgumentOwnership::Borrowed,
                        ArgumentOwnership::Borrowed,
                    ],
                    3,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        ))
        .expect("a reusable closure may move owned captures and clone borrowed captures");

        let mut ownership_arity_drift = source.program.clone();
        let Instruction::Closure {
            capture_ownership, ..
        } = &mut ownership_arity_drift.functions[0].code[2]
        else {
            panic!("fixture retains its closure");
        };
        capture_ownership.pop();
        assert_eq!(
            validate(ownership_arity_drift),
            Err(ValidationError::ClosureOwnershipArity {
                function: f(0),
                pc: pc(2),
                target: f(1),
                captures: 2,
                ownership: 1,
            })
        );

        let mut contract_drift = source.program.clone();
        let Instruction::Closure {
            capture_ownership, ..
        } = &mut contract_drift.functions[0].code[2]
        else {
            panic!("fixture retains its closure");
        };
        capture_ownership[0] = ArgumentOwnership::Borrowed;
        assert_eq!(
            validate(contract_drift),
            Err(ValidationError::ClosureOwnershipContract {
                function: f(0),
                pc: pc(2),
                target: f(1),
                capture: 0,
                expected: ArgumentOwnership::Owned,
                actual: ArgumentOwnership::Borrowed,
            })
        );

        let mut unique_capture = source.program.clone();
        unique_capture.functions[1].parameter_ownership[0] = ArgumentOwnership::Unique;
        let Instruction::Closure {
            capture_ownership, ..
        } = &mut unique_capture.functions[0].code[2]
        else {
            panic!("fixture retains its closure");
        };
        capture_ownership[0] = ArgumentOwnership::Unique;
        assert_eq!(
            validate(unique_capture),
            Err(ValidationError::ClosureUniqueCapture {
                function: f(0),
                pc: pc(2),
                target: f(1),
                capture: 0,
                register: r(0),
            })
        );

        let duplicate_consume = Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    2,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "one capture".to_string(),
                        },
                        closure(
                            r(1),
                            f(1),
                            vec![r(0), r(0)],
                            vec![ArgumentOwnership::Owned, ArgumentOwnership::Owned],
                        ),
                        Instruction::Return { src: r(1) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![
                        ArgumentOwnership::Owned,
                        ArgumentOwnership::Owned,
                        ArgumentOwnership::Borrowed,
                    ],
                    3,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        );
        assert!(matches!(
            validate(duplicate_consume),
            Err(ValidationError::ClosureConsumeAlias {
                target,
                register,
                first: 0,
                second: 1,
                ..
            }) if target == f(1) && register == r(0)
        ));

        let use_after_consume = Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    3,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "consumed capture".to_string(),
                        },
                        closure(r(1), f(1), vec![r(0)], vec![ArgumentOwnership::Owned]),
                        Instruction::Copy {
                            dst: r(2),
                            src: r(0),
                        },
                        Instruction::Return { src: r(1) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![ArgumentOwnership::Owned, ArgumentOwnership::Borrowed],
                    2,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        );
        assert!(matches!(
            validate(use_after_consume),
            Err(ValidationError::ReadBeforeWrite {
                function,
                pc: at,
                register,
            }) if function == f(0) && at == pc(2) && register == r(0)
        ));

        let limits = OwnershipLimits::default();
        let inserted = insert_ownership(&source, limits).expect("insert closure ownership");
        let caller_witness = &inserted.witness().functions()[0];
        assert_eq!(caller_witness.consumed_closure_captures, 1);
        assert_eq!(caller_witness.consumed_call_args, 0);
        assert_eq!(caller_witness.consumed_extern_args, 0);
        assert_eq!(
            inserted.witness().functions()[1].consumed_closure_captures,
            0
        );
        assert!(
            inserted.program().functions()[0]
                .code
                .iter()
                .any(|instruction| matches!(
                    instruction,
                    Instruction::Closure {
                        dst,
                        function,
                        capture_ownership,
                        ..
                    } if *dst == r(0)
                        && *function == f(1)
                        && capture_ownership
                            == &[ArgumentOwnership::Owned, ArgumentOwnership::Borrowed]
                ))
        );
        assert!(
            !inserted.program().functions()[0].code.iter().any(
                |instruction| matches!(instruction, Instruction::Drop { src } if *src == r(0))
            ),
            "the consumed register is immediately reusable for the closure shell"
        );

        let canonical =
            encode_canonical(inserted.program(), CodecLimits::default()).expect("encode closure");
        let decoded = decode_canonical(&canonical, CodecLimits::default()).expect("decode closure");
        assert_eq!(
            encode_canonical(&decoded, CodecLimits::default()).expect("re-encode closure"),
            canonical
        );
        validate_ownership_candidate(&source, decoded, inserted.witness.clone(), limits)
            .expect("decoded closure ownership rebinds independently");

        let mut forged_count = inserted.witness.clone();
        forged_count.functions[0].consumed_closure_captures = 0;
        assert!(matches!(
            validate_ownership_candidate(&source, inserted.program.clone(), forged_count, limits),
            Err(OwnershipError::WitnessCount {
                function,
                count: OwnershipWitnessCount::ConsumedClosureCaptures,
                expected: 1,
                actual: 0,
            }) if function == f(0)
        ));

        let expected_bytes = canonical;
        let expected_witness = inserted.witness().canonical_text();
        for _ in 0..8 {
            let repeated = insert_ownership(&source, limits).expect("repeat closure ownership");
            assert_eq!(
                encode_canonical(repeated.program(), CodecLimits::default())
                    .expect("repeat closure bytes"),
                expected_bytes
            );
            assert_eq!(repeated.witness().canonical_text(), expected_witness);
        }
        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    let repeated =
                        insert_ownership(&source, limits).expect("thread closure ownership");
                    (
                        encode_canonical(repeated.program(), CodecLimits::default())
                            .expect("thread closure bytes"),
                        repeated.witness().canonical_text(),
                    )
                }));
            }
            for join in joins {
                assert_eq!(
                    join.join().expect("closure ownership thread"),
                    (expected_bytes.clone(), expected_witness.clone())
                );
            }
        });

        assert_eq!(
            insert_ownership(
                &source,
                OwnershipLimits {
                    max_operands: 9,
                    ..limits
                },
            ),
            Err(OwnershipError::ResourceLimit {
                resource: OwnershipResource::Operands,
                limit: 9,
                observed: 10,
            })
        );
    }

    #[test]
    fn apply_argument_ownership_is_consumptive_canonical_and_independently_bound() {
        fn apply(
            dst: Register,
            closure: Register,
            args: Vec<Register>,
            argument_ownership: Vec<ArgumentOwnership>,
        ) -> Instruction {
            Instruction::Apply {
                dst,
                closure,
                args,
                argument_ownership,
                result_ownership: CallableResultOwnership::Scalar,
            }
        }

        let ownership_arity = Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    3,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "argument".to_string(),
                        },
                        Instruction::Closure {
                            dst: r(1),
                            function: f(1),
                            captures: Vec::new(),
                            capture_ownership: Vec::new(),
                        },
                        apply(r(2), r(1), vec![r(0)], Vec::new()),
                        Instruction::Return { src: r(2) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![ArgumentOwnership::Borrowed],
                    1,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        );
        assert_eq!(
            validate(ownership_arity),
            Err(ValidationError::ApplyOwnershipArity {
                function: f(0),
                pc: pc(2),
                arguments: 1,
                ownership: 0,
            })
        );

        let duplicate_consume = Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    3,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "one token".to_string(),
                        },
                        Instruction::Closure {
                            dst: r(1),
                            function: f(1),
                            captures: Vec::new(),
                            capture_ownership: Vec::new(),
                        },
                        apply(
                            r(2),
                            r(1),
                            vec![r(0), r(0)],
                            vec![ArgumentOwnership::Owned, ArgumentOwnership::Owned],
                        ),
                        Instruction::Return { src: r(2) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![ArgumentOwnership::Owned, ArgumentOwnership::Owned],
                    2,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        );
        assert!(matches!(
            validate(duplicate_consume),
            Err(ValidationError::ApplyConsumeAlias {
                function,
                pc: at,
                register,
                first: 0,
                second: 1,
            }) if function == f(0) && at == pc(2) && register == r(0)
        ));

        let unique_alias = Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    3,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "unique token".to_string(),
                        },
                        Instruction::Closure {
                            dst: r(1),
                            function: f(1),
                            captures: Vec::new(),
                            capture_ownership: Vec::new(),
                        },
                        apply(
                            r(2),
                            r(1),
                            vec![r(0), r(0)],
                            vec![ArgumentOwnership::Unique, ArgumentOwnership::Borrowed],
                        ),
                        Instruction::Return { src: r(2) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![ArgumentOwnership::Unique, ArgumentOwnership::Borrowed],
                    2,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        );
        assert!(matches!(
            validate(unique_alias),
            Err(ValidationError::ApplyUniqueAlias {
                function,
                pc: at,
                register,
                unique: 0,
                alias: 1,
            }) if function == f(0) && at == pc(2) && register == r(0)
        ));

        let unique_closure_alias = Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    2,
                    vec![
                        Instruction::Closure {
                            dst: r(0),
                            function: f(1),
                            captures: Vec::new(),
                            capture_ownership: Vec::new(),
                        },
                        apply(r(1), r(0), vec![r(0)], vec![ArgumentOwnership::Unique]),
                        Instruction::Return { src: r(1) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![ArgumentOwnership::Unique],
                    1,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        );
        assert!(matches!(
            validate(unique_closure_alias),
            Err(ValidationError::ApplyUniqueClosureAlias {
                function,
                pc: at,
                register,
                unique: 0,
            }) if function == f(0) && at == pc(1) && register == r(0)
        ));

        let use_after_consume = Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    4,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "consumed".to_string(),
                        },
                        Instruction::Closure {
                            dst: r(1),
                            function: f(1),
                            captures: Vec::new(),
                            capture_ownership: Vec::new(),
                        },
                        apply(r(2), r(1), vec![r(0)], vec![ArgumentOwnership::Owned]),
                        Instruction::Copy {
                            dst: r(3),
                            src: r(0),
                        },
                        Instruction::Return { src: r(2) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![ArgumentOwnership::Owned],
                    1,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        );
        assert!(matches!(
            validate(use_after_consume),
            Err(ValidationError::ReadBeforeWrite {
                function,
                pc: at,
                register,
            }) if function == f(0) && at == pc(3) && register == r(0)
        ));

        let source = validate(Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    3,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "owned".to_string(),
                        },
                        Instruction::String {
                            dst: r(1),
                            value: "borrowed".to_string(),
                        },
                        Instruction::Closure {
                            dst: r(2),
                            function: f(1),
                            captures: Vec::new(),
                            capture_ownership: Vec::new(),
                        },
                        apply(
                            r(0),
                            r(2),
                            vec![r(0), r(1)],
                            vec![ArgumentOwnership::Owned, ArgumentOwnership::Borrowed],
                        ),
                        Instruction::Return { src: r(0) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![ArgumentOwnership::Owned, ArgumentOwnership::Borrowed],
                    2,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        ))
        .expect("Apply may consume an argument into the same destination epoch");
        let limits = OwnershipLimits::default();
        let inserted = insert_ownership(&source, limits).expect("insert Apply ownership");
        let caller_witness = &inserted.witness().functions()[0];
        assert_eq!(caller_witness.consumed_apply_args, 1);
        assert_eq!(caller_witness.consumed_call_args, 0);
        assert_eq!(caller_witness.consumed_closure_captures, 0);
        assert_eq!(caller_witness.consumed_extern_args, 0);
        assert_eq!(inserted.witness().functions()[1].consumed_apply_args, 0);
        assert!(inserted.witness().canonical_text().contains(
            "function f0 mode=inserted-linear-reuse result=scalar source=5 emitted=7 drops=2 moves=0 redefs=1 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=1 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=1\n"
        ));
        assert!(
            inserted.program().functions()[0]
                .code
                .iter()
                .any(|instruction| matches!(
                    instruction,
                    Instruction::Apply {
                        dst,
                        closure,
                        argument_ownership,
                        ..
                    } if *dst == r(0)
                        && *closure == r(2)
                        && argument_ownership
                            == &[ArgumentOwnership::Owned, ArgumentOwnership::Borrowed]
                ))
        );
        assert!(
            !inserted.program().functions()[0].code.iter().any(
                |instruction| matches!(instruction, Instruction::Drop { src } if *src == r(0))
            ),
            "the transferred argument is immediately replaced by the Apply result"
        );

        let canonical =
            encode_canonical(inserted.program(), CodecLimits::default()).expect("encode Apply");
        let decoded = decode_canonical(&canonical, CodecLimits::default()).expect("decode Apply");
        assert_eq!(
            encode_canonical(&decoded, CodecLimits::default()).expect("re-encode Apply"),
            canonical
        );
        validate_ownership_candidate(&source, decoded, inserted.witness.clone(), limits)
            .expect("decoded Apply ownership rebinds independently");

        let mut forged_count = inserted.witness.clone();
        forged_count.functions[0].consumed_apply_args = 0;
        assert!(matches!(
            validate_ownership_candidate(&source, inserted.program.clone(), forged_count, limits),
            Err(OwnershipError::WitnessCount {
                function,
                count: OwnershipWitnessCount::ConsumedApplyArgs,
                expected: 1,
                actual: 0,
            }) if function == f(0)
        ));

        let mut drift = inserted.program.program.clone();
        let Instruction::Apply {
            argument_ownership, ..
        } = drift.functions[0]
            .code
            .iter_mut()
            .find(|instruction| matches!(instruction, Instruction::Apply { .. }))
            .expect("candidate retains the Apply skeleton")
        else {
            unreachable!("the selected instruction is Apply");
        };
        argument_ownership[0] = ArgumentOwnership::Unique;
        let drift = validate(drift).expect("consume-class drift remains ordinary valid FLBC");
        assert!(matches!(
            validate_ownership_candidate(&source, drift, inserted.witness.clone(), limits),
            Err(OwnershipError::SkeletonMismatch { .. })
        ));

        let apply_prefix = [OP_APPLY, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0];
        let apply_start = canonical
            .windows(apply_prefix.len())
            .position(|window| window == apply_prefix)
            .expect("the exact Apply prefix occurs in the artifact");
        let ownership_tag = apply_start.saturating_add(apply_prefix.len());
        let mut invalid_tag = canonical.clone();
        invalid_tag[ownership_tag] = 0xff;
        assert_eq!(
            decode_canonical(&invalid_tag, CodecLimits::default()),
            Err(CodecError::InvalidArgumentOwnership {
                tag: 0xff,
                offset: ownership_tag,
            })
        );

        let expected_bytes = canonical;
        let expected_witness = inserted.witness().canonical_text();
        for _ in 0..8 {
            let repeated = insert_ownership(&source, limits).expect("repeat Apply ownership");
            assert_eq!(
                encode_canonical(repeated.program(), CodecLimits::default())
                    .expect("repeat Apply bytes"),
                expected_bytes
            );
            assert_eq!(repeated.witness().canonical_text(), expected_witness);
        }
        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    let repeated =
                        insert_ownership(&source, limits).expect("thread Apply ownership");
                    (
                        encode_canonical(repeated.program(), CodecLimits::default())
                            .expect("thread Apply bytes"),
                        repeated.witness().canonical_text(),
                    )
                }));
            }
            for join in joins {
                assert_eq!(
                    join.join().expect("Apply ownership thread"),
                    (expected_bytes.clone(), expected_witness.clone())
                );
            }
        });

        assert_eq!(
            insert_ownership(
                &source,
                OwnershipLimits {
                    max_operands: 8,
                    ..limits
                },
            ),
            Err(OwnershipError::ResourceLimit {
                resource: OwnershipResource::Operands,
                limit: 8,
                observed: 9,
            })
        );
    }

    #[test]
    fn intrinsic_consumes_balance_acyclic_and_cyclic_cfg_edges() {
        fn consume(dst: Register, src: Register) -> Instruction {
            Instruction::Intrinsic {
                dst,
                row: "extern:Prototype.consume".to_string(),
                args: vec![src],
                argument_ownership: vec![ArgumentOwnership::Owned],
                result_ownership: ResultOwnership::Owned,
            }
        }

        let acyclic = validate(Program::new(
            f(0),
            vec![function(
                0,
                0,
                5,
                vec![
                    Instruction::String {
                        dst: r(0),
                        value: "branch-owned".to_string(),
                    },
                    Instruction::Nat {
                        dst: r(1),
                        value: 0,
                    },
                    Instruction::JumpIfZero {
                        cond: r(1),
                        zero: pc(3),
                        nonzero: pc(5),
                    },
                    consume(r(2), r(0)),
                    Instruction::Jump { target: pc(7) },
                    consume(r(3), r(0)),
                    Instruction::Jump { target: pc(7) },
                    Instruction::Nat {
                        dst: r(4),
                        value: 1,
                    },
                    Instruction::Return { src: r(4) },
                ],
            )],
        ))
        .expect("both acyclic paths consume the same incoming token");
        let acyclic_inserted =
            insert_ownership(&acyclic, OwnershipLimits::default()).expect("acyclic ownership");
        assert_eq!(
            acyclic_inserted.witness().functions()[0].mode,
            OwnershipMode::InsertedAcyclicCfg
        );
        assert_eq!(
            acyclic_inserted.witness().functions()[0].consumed_extern_args,
            2
        );
        assert!(
            !acyclic_inserted.program().functions()[0].code.iter().any(
                |instruction| matches!(instruction, Instruction::Drop { src } if *src == r(0))
            ),
            "neither branch drops the transferred entry token"
        );

        let cyclic = validate(Program::new(
            f(0),
            vec![function(
                0,
                0,
                3,
                vec![
                    Instruction::String {
                        dst: r(0),
                        value: "loop-live".to_string(),
                    },
                    Instruction::Nat {
                        dst: r(1),
                        value: 0,
                    },
                    Instruction::JumpIfZero {
                        cond: r(1),
                        zero: pc(4),
                        nonzero: pc(3),
                    },
                    Instruction::Jump { target: pc(2) },
                    consume(r(2), r(0)),
                    Instruction::Return { src: r(2) },
                ],
            )],
        ))
        .expect("the loop retains its token until the exit consume");
        let cyclic_inserted =
            insert_ownership(&cyclic, OwnershipLimits::default()).expect("cyclic ownership");
        assert_eq!(
            cyclic_inserted.witness().functions()[0].mode,
            OwnershipMode::InsertedCyclicCfg
        );
        assert_eq!(
            cyclic_inserted.witness().functions()[0].consumed_extern_args,
            1
        );
        assert!(
            !cyclic_inserted.program().functions()[0].code.iter().any(
                |instruction| matches!(instruction, Instruction::Drop { src } if *src == r(0))
            ),
            "the loop-exit transfer has no synthesized post-call drop"
        );
    }

    #[test]
    fn direct_call_consumes_balance_acyclic_and_cyclic_cfg_edges() {
        fn consume(
            dst: Register,
            target: FunctionId,
            src: Register,
            disposition: ArgumentOwnership,
        ) -> Instruction {
            Instruction::Call {
                dst,
                function: target,
                args: vec![src],
                argument_ownership: vec![disposition],
                result_ownership: CallableResultOwnership::Scalar,
            }
        }

        let acyclic = validate(Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    5,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "branch-owned".to_string(),
                        },
                        Instruction::Nat {
                            dst: r(1),
                            value: 0,
                        },
                        Instruction::JumpIfZero {
                            cond: r(1),
                            zero: pc(3),
                            nonzero: pc(5),
                        },
                        consume(r(2), f(1), r(0), ArgumentOwnership::Owned),
                        Instruction::Jump { target: pc(7) },
                        consume(r(3), f(1), r(0), ArgumentOwnership::Owned),
                        Instruction::Jump { target: pc(7) },
                        Instruction::Nat {
                            dst: r(4),
                            value: 1,
                        },
                        Instruction::Return { src: r(4) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![ArgumentOwnership::Owned],
                    1,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        ))
        .expect("both acyclic paths transfer the same incoming token");
        let acyclic_inserted =
            insert_ownership(&acyclic, OwnershipLimits::default()).expect("acyclic call ownership");
        assert_eq!(
            acyclic_inserted.witness().functions()[0].mode,
            OwnershipMode::InsertedAcyclicCfg
        );
        assert_eq!(
            acyclic_inserted.witness().functions()[0].consumed_call_args,
            2
        );
        assert!(
            !acyclic_inserted.program().functions()[0].code.iter().any(
                |instruction| matches!(instruction, Instruction::Drop { src } if *src == r(0))
            ),
            "neither branch drops the transferred entry token"
        );

        let cyclic = validate(Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    3,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "loop-unique".to_string(),
                        },
                        Instruction::Nat {
                            dst: r(1),
                            value: 0,
                        },
                        Instruction::JumpIfZero {
                            cond: r(1),
                            zero: pc(4),
                            nonzero: pc(3),
                        },
                        Instruction::Jump { target: pc(2) },
                        consume(r(2), f(1), r(0), ArgumentOwnership::Unique),
                        Instruction::Return { src: r(2) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![ArgumentOwnership::Unique],
                    1,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        ))
        .expect("the loop retains its unique token until the exit call");
        let cyclic_inserted =
            insert_ownership(&cyclic, OwnershipLimits::default()).expect("cyclic call ownership");
        assert_eq!(
            cyclic_inserted.witness().functions()[0].mode,
            OwnershipMode::InsertedCyclicCfg
        );
        assert_eq!(
            cyclic_inserted.witness().functions()[0].consumed_call_args,
            1
        );
        assert!(
            !cyclic_inserted.program().functions()[0].code.iter().any(
                |instruction| matches!(instruction, Instruction::Drop { src } if *src == r(0))
            ),
            "the loop-exit unique transfer has no synthesized post-call drop"
        );
    }

    #[test]
    fn apply_consumes_balance_acyclic_and_cyclic_cfg_edges() {
        fn consume(
            dst: Register,
            closure: Register,
            src: Register,
            disposition: ArgumentOwnership,
        ) -> Instruction {
            Instruction::Apply {
                dst,
                closure,
                args: vec![src],
                argument_ownership: vec![disposition],
                result_ownership: CallableResultOwnership::Scalar,
            }
        }

        let acyclic = validate(Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    6,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "branch-owned".to_string(),
                        },
                        Instruction::Nat {
                            dst: r(1),
                            value: 0,
                        },
                        Instruction::Closure {
                            dst: r(2),
                            function: f(1),
                            captures: Vec::new(),
                            capture_ownership: Vec::new(),
                        },
                        Instruction::JumpIfZero {
                            cond: r(1),
                            zero: pc(4),
                            nonzero: pc(6),
                        },
                        consume(r(3), r(2), r(0), ArgumentOwnership::Owned),
                        Instruction::Jump { target: pc(8) },
                        consume(r(4), r(2), r(0), ArgumentOwnership::Owned),
                        Instruction::Jump { target: pc(8) },
                        Instruction::Nat {
                            dst: r(5),
                            value: 1,
                        },
                        Instruction::Return { src: r(5) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![ArgumentOwnership::Owned],
                    1,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        ))
        .expect("both acyclic paths transfer the same incoming Apply argument");
        let acyclic_inserted = insert_ownership(&acyclic, OwnershipLimits::default())
            .expect("acyclic Apply ownership");
        assert_eq!(
            acyclic_inserted.witness().functions()[0].mode,
            OwnershipMode::InsertedAcyclicCfg
        );
        assert_eq!(
            acyclic_inserted.witness().functions()[0].consumed_apply_args,
            2
        );
        assert!(
            !acyclic_inserted.program().functions()[0].code.iter().any(
                |instruction| matches!(instruction, Instruction::Drop { src } if *src == r(0))
            ),
            "neither branch drops the transferred Apply argument"
        );

        let cyclic = validate(Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    4,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "loop-unique".to_string(),
                        },
                        Instruction::Nat {
                            dst: r(1),
                            value: 0,
                        },
                        Instruction::Closure {
                            dst: r(2),
                            function: f(1),
                            captures: Vec::new(),
                            capture_ownership: Vec::new(),
                        },
                        Instruction::JumpIfZero {
                            cond: r(1),
                            zero: pc(5),
                            nonzero: pc(4),
                        },
                        Instruction::Jump { target: pc(3) },
                        consume(r(3), r(2), r(0), ArgumentOwnership::Unique),
                        Instruction::Return { src: r(3) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![ArgumentOwnership::Unique],
                    1,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        ))
        .expect("the loop retains its unique token until the exit Apply");
        let cyclic_inserted =
            insert_ownership(&cyclic, OwnershipLimits::default()).expect("cyclic Apply ownership");
        assert_eq!(
            cyclic_inserted.witness().functions()[0].mode,
            OwnershipMode::InsertedCyclicCfg
        );
        assert_eq!(
            cyclic_inserted.witness().functions()[0].consumed_apply_args,
            1
        );
        assert!(
            !cyclic_inserted.program().functions()[0].code.iter().any(
                |instruction| matches!(instruction, Instruction::Drop { src } if *src == r(0))
            ),
            "the loop-exit unique Apply has no synthesized post-transfer drop"
        );
    }

    #[test]
    fn closure_captures_balance_acyclic_and_cyclic_cfg_edges() {
        fn consume(dst: Register, target: FunctionId, src: Register) -> Instruction {
            Instruction::Closure {
                dst,
                function: target,
                captures: vec![src],
                capture_ownership: vec![ArgumentOwnership::Owned],
            }
        }

        let acyclic = validate(Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    5,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "branch capture".to_string(),
                        },
                        Instruction::Nat {
                            dst: r(1),
                            value: 0,
                        },
                        Instruction::JumpIfZero {
                            cond: r(1),
                            zero: pc(3),
                            nonzero: pc(5),
                        },
                        consume(r(2), f(1), r(0)),
                        Instruction::Jump { target: pc(7) },
                        consume(r(3), f(1), r(0)),
                        Instruction::Jump { target: pc(7) },
                        Instruction::Nat {
                            dst: r(4),
                            value: 1,
                        },
                        Instruction::Return { src: r(4) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![ArgumentOwnership::Owned, ArgumentOwnership::Borrowed],
                    2,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        ))
        .expect("both acyclic paths transfer the same incoming capture");
        let acyclic_inserted = insert_ownership(&acyclic, OwnershipLimits::default())
            .expect("acyclic closure ownership");
        assert_eq!(
            acyclic_inserted.witness().functions()[0].mode,
            OwnershipMode::InsertedAcyclicCfg
        );
        assert_eq!(
            acyclic_inserted.witness().functions()[0].consumed_closure_captures,
            2
        );
        assert!(
            !acyclic_inserted.program().functions()[0].code.iter().any(
                |instruction| matches!(instruction, Instruction::Drop { src } if *src == r(0))
            ),
            "neither branch drops the transferred entry capture"
        );

        let cyclic = validate(Program::new(
            f(0),
            vec![
                function(
                    0,
                    0,
                    3,
                    vec![
                        Instruction::String {
                            dst: r(0),
                            value: "loop capture".to_string(),
                        },
                        Instruction::Nat {
                            dst: r(1),
                            value: 0,
                        },
                        Instruction::JumpIfZero {
                            cond: r(1),
                            zero: pc(4),
                            nonzero: pc(3),
                        },
                        Instruction::Jump { target: pc(2) },
                        consume(r(2), f(1), r(0)),
                        Instruction::Return { src: r(2) },
                    ],
                ),
                function_with_ownership(
                    1,
                    vec![ArgumentOwnership::Owned, ArgumentOwnership::Borrowed],
                    2,
                    vec![Instruction::Return { src: r(0) }],
                ),
            ],
        ))
        .expect("the loop retains its token until the exit closure");
        let cyclic_inserted = insert_ownership(&cyclic, OwnershipLimits::default())
            .expect("cyclic closure ownership");
        assert_eq!(
            cyclic_inserted.witness().functions()[0].mode,
            OwnershipMode::InsertedCyclicCfg
        );
        assert_eq!(
            cyclic_inserted.witness().functions()[0].consumed_closure_captures,
            1
        );
        assert!(
            !cyclic_inserted.program().functions()[0].code.iter().any(
                |instruction| matches!(instruction, Instruction::Drop { src } if *src == r(0))
            ),
            "the loop-exit transfer has no synthesized post-closure drop"
        );
    }

    #[test]
    fn callable_result_ownership_is_codec_validation_and_witness_bound() {
        let mut entry = function(
            0,
            0,
            2,
            vec![
                Instruction::Call {
                    dst: r(0),
                    function: f(1),
                    args: Vec::new(),
                    argument_ownership: Vec::new(),
                    result_ownership: CallableResultOwnership::Scalar,
                },
                Instruction::Call {
                    dst: r(1),
                    function: f(2),
                    args: Vec::new(),
                    argument_ownership: Vec::new(),
                    result_ownership: CallableResultOwnership::Owned,
                },
                Instruction::Return { src: r(1) },
            ],
        );
        entry.result_ownership = CallableResultOwnership::Owned;
        let scalar = function(
            1,
            0,
            1,
            vec![
                Instruction::Nat {
                    dst: r(0),
                    value: 7,
                },
                Instruction::Return { src: r(0) },
            ],
        );
        let mut owned = function(
            2,
            0,
            1,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "owned".to_string(),
                },
                Instruction::Return { src: r(0) },
            ],
        );
        owned.result_ownership = CallableResultOwnership::Owned;
        let program = Program::new(f(0), vec![entry, scalar, owned]);
        let source = validate(program.clone()).expect("both callable result classes validate");
        let bytes =
            encode_canonical(&source, CodecLimits::default()).expect("result classes encode");
        let decoded =
            decode_canonical(&bytes, CodecLimits::default()).expect("result classes decode");
        assert_eq!(decoded, source);

        let inserted = insert_ownership(&source, OwnershipLimits::default())
            .expect("ownership witness binds both callable result classes");
        assert_eq!(inserted.witness().functions()[0].owned_callable_results, 1);
        assert_eq!(inserted.witness().functions()[0].scalar_callable_results, 1);
        let mut forged_rows = inserted.witness().functions().to_vec();
        forged_rows[0].owned_callable_results = 0;
        let forged = OwnershipWitness::new(inserted.witness().schema_version(), forged_rows);
        assert!(matches!(
            validate_ownership_candidate(
                &source,
                inserted.program().clone(),
                forged,
                OwnershipLimits::default(),
            ),
            Err(OwnershipError::WitnessCount {
                function,
                count: OwnershipWitnessCount::OwnedCallableResults,
                expected: 1,
                actual: 0,
            }) if function == f(0)
        ));

        let mut mismatch = program;
        let Instruction::Call {
            result_ownership, ..
        } = &mut mismatch.functions[0].code[0]
        else {
            panic!("fixture retains its direct Call");
        };
        *result_ownership = CallableResultOwnership::Owned;
        assert_eq!(
            validate(mismatch),
            Err(ValidationError::CallResultOwnershipContract {
                function: f(0),
                pc: pc(0),
                target: f(1),
                expected: CallableResultOwnership::Scalar,
                actual: CallableResultOwnership::Owned,
            })
        );

        let mut invalid_tag =
            encode_canonical(&minimal_program(), CodecLimits::default()).expect("minimal bytes");
        invalid_tag[32] = 2;
        assert_eq!(
            decode_canonical(&invalid_tag, CodecLimits::default()),
            Err(CodecError::InvalidCallableResultOwnership { tag: 2, offset: 32 })
        );
    }

    #[test]
    fn minimal_encoding_is_a_frozen_little_endian_golden() {
        let bytes = encode_canonical(&minimal_program(), CodecLimits::default())
            .expect("encode the minimal fixture");
        assert_eq!(
            bytes,
            vec![
                70, 76, 78, 70, 76, 66, 67, 0, // magic
                7, 0, // wire version
                11, 0, // schema version
                0, 0, 0, 0, // entry
                1, 0, 0, 0, // function count
                0, 0, 0, 0, // function id
                0, 0, // arity
                1, 0, // register count
                0, 0, 0, 0, // parameter ownership count
                1, // scalar result ownership
                2, 0, 0, 0, // instruction count
                0, // Nat
                0, 0, // destination
                7, 0, 0, 0, 0, 0, 0, 0,  // value
                13, // Return
                0, 0, // source
            ]
        );
    }

    #[test]
    fn every_opcode_round_trips_and_reencodes_byte_identically() {
        let original = every_opcode_program();
        let bytes =
            encode_canonical(&original, CodecLimits::default()).expect("encode every opcode");
        let decoded =
            decode_canonical(&bytes, CodecLimits::default()).expect("decode every opcode");
        assert_eq!(decoded, original);
        assert_eq!(
            encode_canonical(&decoded, CodecLimits::default()).expect("re-encode every opcode"),
            bytes
        );
    }

    #[test]
    fn constructor_field_projection_shape_is_validated_before_execution() {
        fn projection_program(expected_tag: u8, expected_fields: u16, field: u16) -> Program {
            Program::new(
                f(0),
                vec![function(
                    0,
                    0,
                    3,
                    vec![
                        Instruction::Nat {
                            dst: r(0),
                            value: 7,
                        },
                        Instruction::Ctor {
                            dst: r(1),
                            tag: 1,
                            fields: vec![r(0)],
                            scalar_bytes: Vec::new(),
                        },
                        Instruction::CtorField {
                            dst: r(2),
                            src: r(1),
                            expected_tag,
                            expected_fields,
                            field,
                        },
                        Instruction::Return { src: r(2) },
                    ],
                )],
            )
        }

        validate(projection_program(1, 1, 0)).expect("checked projection is valid");

        let invalid_tag = abi::TAG_MAX_CTOR_TAG
            .checked_add(1)
            .expect("contract maximum leaves one invalid tag");
        assert!(matches!(
            validate(projection_program(invalid_tag, 1, 0)),
            Err(ValidationError::CtorTagOutOfRange { tag, .. }) if tag == invalid_tag
        ));

        let invalid_shape =
            u16::try_from(abi::MAX_CTOR_FIELDS).expect("ABI field ceiling fits the wire type");
        assert!(matches!(
            validate(projection_program(1, invalid_shape, 0)),
            Err(ValidationError::CtorFieldShapeOutOfRange {
                expected_fields,
                ..
            }) if expected_fields == invalid_shape
        ));

        assert!(matches!(
            validate(projection_program(1, 1, 1)),
            Err(ValidationError::CtorFieldOutOfBounds {
                expected_fields: 1,
                field: 1,
                ..
            })
        ));
    }

    #[test]
    fn every_truncation_and_envelope_drift_is_typed() {
        let bytes =
            encode_canonical(&every_opcode_program(), CodecLimits::default()).expect("encode");
        for end in 0..bytes.len() {
            assert!(
                decode_canonical(&bytes[..end], CodecLimits::default()).is_err(),
                "prefix of length {end} escaped"
            );
        }
        assert!(decode_canonical(&bytes, CodecLimits::default()).is_ok());

        let mut bad_magic = bytes.clone();
        bad_magic[0] ^= 1;
        assert_eq!(
            decode_canonical(&bad_magic, CodecLimits::default()),
            Err(CodecError::BadMagic)
        );

        let mut bad_wire = bytes.clone();
        bad_wire[8..10].copy_from_slice(&4u16.to_le_bytes());
        assert_eq!(
            decode_canonical(&bad_wire, CodecLimits::default()),
            Err(CodecError::UnsupportedWireVersion { seen: 4 })
        );

        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(matches!(
            decode_canonical(&trailing, CodecLimits::default()),
            Err(CodecError::TrailingBytes { remaining: 1, .. })
        ));
    }

    #[test]
    fn unknown_opcode_invalid_utf8_and_invalid_program_never_publish() {
        let mut unknown =
            encode_canonical(&minimal_program(), CodecLimits::default()).expect("encode");
        unknown[37] = 0xFF;
        assert_eq!(
            decode_canonical(&unknown, CodecLimits::default()),
            Err(CodecError::UnknownOpcode {
                opcode: 0xFF,
                offset: 37,
            })
        );

        let mut invalid_utf8 =
            encode_canonical(&string_program(), CodecLimits::default()).expect("encode");
        let payload = invalid_utf8
            .windows(b"payload".len())
            .position(|window| window == b"payload")
            .expect("payload bytes occur in the fixture");
        invalid_utf8[payload] = 0xFF;
        assert!(matches!(
            decode_canonical(&invalid_utf8, CodecLimits::default()),
            Err(CodecError::InvalidUtf8 {
                field: "String literal",
                ..
            })
        ));

        let mut invalid_registers =
            encode_canonical(&minimal_program(), CodecLimits::default()).expect("encode");
        invalid_registers[26..28].copy_from_slice(&0u16.to_le_bytes());
        assert!(matches!(
            decode_canonical(&invalid_registers, CodecLimits::default()),
            Err(CodecError::Validation(
                ValidationError::RegisterOutOfBounds { .. }
            ))
        ));
    }

    #[test]
    fn every_resource_dimension_stops_before_acceptance() {
        let minimal = minimal_program();
        let minimal_bytes =
            encode_canonical(&minimal, CodecLimits::default()).expect("encode minimal");
        let byte_limit = CodecLimits {
            max_artifact_bytes: minimal_bytes.len() - 1,
            ..CodecLimits::default()
        };
        assert!(matches!(
            encode_canonical(&minimal, byte_limit),
            Err(CodecError::ResourceLimit {
                resource: CodecResource::ArtifactBytes,
                ..
            })
        ));
        assert!(matches!(
            decode_canonical(&minimal_bytes, byte_limit),
            Err(CodecError::ResourceLimit {
                resource: CodecResource::ArtifactBytes,
                ..
            })
        ));

        let function_limit = CodecLimits {
            max_functions: 0,
            ..CodecLimits::default()
        };
        assert!(matches!(
            decode_canonical(&minimal_bytes, function_limit),
            Err(CodecError::ResourceLimit {
                resource: CodecResource::Functions,
                ..
            })
        ));

        let instruction_limit = CodecLimits {
            max_instructions: 1,
            ..CodecLimits::default()
        };
        assert!(matches!(
            decode_canonical(&minimal_bytes, instruction_limit),
            Err(CodecError::ResourceLimit {
                resource: CodecResource::Instructions,
                ..
            })
        ));

        let operand_limit = CodecLimits {
            max_operands: 0,
            ..CodecLimits::default()
        };
        assert!(matches!(
            decode_canonical(&minimal_bytes, operand_limit),
            Err(CodecError::ResourceLimit {
                resource: CodecResource::Operands,
                ..
            })
        ));

        let string = string_program();
        let string_bytes =
            encode_canonical(&string, CodecLimits::default()).expect("encode String");
        let literal_limit = CodecLimits {
            max_literal_bytes: 0,
            ..CodecLimits::default()
        };
        assert!(matches!(
            decode_canonical(&string_bytes, literal_limit),
            Err(CodecError::ResourceLimit {
                resource: CodecResource::LiteralBytes,
                ..
            })
        ));
    }

    #[test]
    fn impossible_declared_lengths_are_truncated_before_reservation() {
        let unbounded_counts = CodecLimits {
            max_functions: usize::MAX,
            max_instructions: usize::MAX,
            max_operands: usize::MAX,
            max_literal_bytes: usize::MAX,
            ..CodecLimits::default()
        };

        let mut function_count =
            encode_canonical(&minimal_program(), CodecLimits::default()).expect("encode");
        function_count[16..20].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(matches!(
            decode_canonical(&function_count, unbounded_counts),
            Err(CodecError::Truncated { .. })
        ));

        let mut instruction_count =
            encode_canonical(&minimal_program(), CodecLimits::default()).expect("encode");
        instruction_count[28..32].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(matches!(
            decode_canonical(&instruction_count, unbounded_counts),
            Err(CodecError::Truncated { .. })
        ));

        let mut literal_count =
            encode_canonical(&string_program(), CodecLimits::default()).expect("encode");
        literal_count[35..39].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(matches!(
            decode_canonical(&literal_count, unbounded_counts),
            Err(CodecError::Truncated { .. })
        ));
    }

    #[test]
    fn any_accepted_single_byte_mutation_is_already_canonical() {
        let bytes =
            encode_canonical(&every_opcode_program(), CodecLimits::default()).expect("encode");
        let mut accepted = 0usize;
        for index in 0..bytes.len() {
            let mut mutant = bytes.clone();
            mutant[index] ^= 1;
            if let Ok(decoded) = decode_canonical(&mutant, CodecLimits::default()) {
                accepted += 1;
                assert_eq!(
                    encode_canonical(&decoded, CodecLimits::default())
                        .expect("accepted artifact re-encodes"),
                    mutant,
                    "accepted mutation at byte {index} had a second encoding"
                );
            }
        }
        assert!(accepted > 0, "the canonicality check exercised no accept");
    }

    #[test]
    fn hostile_bytes_are_bounded_and_never_panic() {
        let limits = CodecLimits {
            max_artifact_bytes: 128,
            max_functions: 8,
            max_instructions: 32,
            max_operands: 64,
            max_literal_bytes: 64,
        };
        let mut state = 0xD1B5_4A32_D192_ED03u64;
        for len in 0..=128usize {
            let mut bytes = vec![0; len];
            for byte in &mut bytes {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                *byte = state as u8;
            }
            let _ = decode_canonical(&bytes, limits);
        }
    }

    #[test]
    fn canonical_bytes_are_identical_across_repetition_and_threads() {
        let program = every_opcode_program();
        let expected = encode_canonical(&program, CodecLimits::default()).expect("encode control");
        for _ in 0..32 {
            assert_eq!(
                encode_canonical(&program, CodecLimits::default()).expect("repeat encoding"),
                expected
            );
        }

        let workers: Vec<_> = (0..8)
            .map(|_| {
                let program = program.clone();
                std::thread::spawn(move || {
                    encode_canonical(&program, CodecLimits::default()).expect("threaded encoding")
                })
            })
            .collect();
        for worker in workers {
            assert_eq!(worker.join().expect("encoder thread completed"), expected);
        }
    }
}
