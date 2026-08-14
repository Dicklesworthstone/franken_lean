//! Target-neutral FIR schema, validator, canonical printer, and mandatory FLBC
//! lowering for the bounded G0-3 compiler prototype.
//!
//! FIR values are single-assignment ABI values. Function parameters occupy the
//! leading value ids, bindings are numbered canonically across blocks, and a
//! block may read only values initialized on every incoming edge. Intrinsic
//! signatures are part of the program identity; binding them to the generated
//! extern contract is a later source-ingress obligation, not something this
//! module silently assumes.
//!
//! [`lower_to_flbc`] accepts only [`ValidatedProgram`], chooses registers and
//! block offsets from canonical ids, and subjects the result to FLBC's
//! independent validator. It has no cross-stage fallback.

use crate::flbc;
use fln_rt::abi;
use std::collections::VecDeque;
use std::fmt;

/// The only FIR schema accepted by this prototype.
///
/// Version 6 makes semantic boxing boundaries explicit while preserving the
/// single Marrow ABI value domain; version 7 binds intrinsic argument
/// ownership; version 8 binds every function parameter and direct call;
/// version 9 binds closure captures to the target parameter prefix; version 10
/// binds dynamic Apply arguments; version 11 binds generated intrinsic result
/// ownership; version 12 binds Owned-or-Scalar callable results into every
/// function, closure signature, and dynamic application; version 13 represents
/// each `Lean.Core.checkSystem` call as an explicit effect checkpoint; version
/// 14 carries computed module-name values into that checkpoint.
pub const FIR_SCHEMA_VERSION: u16 = 14;

/// Explicit ceilings for FIR validation work.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ValidationLimits {
    pub max_functions: usize,
    pub max_constructors: usize,
    pub max_projections: usize,
    pub max_closure_types: usize,
    pub max_intrinsics: usize,
    pub max_blocks: usize,
    pub max_values: usize,
    pub max_operations: usize,
    pub max_operands: usize,
    pub max_literal_bytes: usize,
    pub max_dataflow_cells: usize,
}

impl Default for ValidationLimits {
    fn default() -> Self {
        Self {
            max_functions: 4_096,
            max_constructors: 65_536,
            max_projections: 65_536,
            max_closure_types: 65_536,
            max_intrinsics: 65_536,
            max_blocks: 65_536,
            max_values: 1_000_000,
            max_operations: 1_000_000,
            max_operands: 8_000_000,
            max_literal_bytes: 32 * 1024 * 1024,
            max_dataflow_cells: 64 * 1024 * 1024,
        }
    }
}

/// Resource dimension named by a validation refusal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValidationResource {
    Functions,
    Constructors,
    Projections,
    ClosureTypes,
    Intrinsics,
    Blocks,
    Values,
    Operations,
    Operands,
    LiteralBytes,
    DataflowCells,
}

/// Canonical function-table index.
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

/// Canonical block-table index within one function.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BlockId(u32);

impl BlockId {
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

/// Canonical single-assignment value index within one function.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ValueId(u32);

impl ValueId {
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

/// Canonical intrinsic-signature table index.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct IntrinsicId(u32);

impl IntrinsicId {
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

/// Canonical constructor-layout table index.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ConstructorId(u32);

impl ConstructorId {
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

/// Canonical projection-layout table index.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProjectionId(u32);

impl ProjectionId {
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

/// Canonical typed-closure signature table index.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ClosureTypeId(u32);

impl ClosureTypeId {
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

/// Target-neutral value class. Every class is represented by a Marrow
/// [`fln_rt::obj::Obj`] at execution time; the distinction is FIR validation
/// evidence, not a second runtime value domain.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ValueType {
    Unit,
    Bool,
    Nat,
    String,
    Constructor,
    Array,
    Ref,
    Thunk,
    Task,
    Closure(ClosureTypeId),
    Abi,
}

impl ValueType {
    const fn token(self) -> &'static str {
        match self {
            Self::Unit => "unit",
            Self::Bool => "bool",
            Self::Nat => "nat",
            Self::String => "string",
            Self::Constructor => "ctor",
            Self::Array => "array",
            Self::Ref => "ref",
            Self::Thunk => "thunk",
            Self::Task => "task",
            Self::Closure(_) => "closure",
            Self::Abi => "abi",
        }
    }

    const fn admits_callable_result(self, ownership: flbc::CallableResultOwnership) -> bool {
        match self {
            Self::Unit | Self::Bool => {
                matches!(ownership, flbc::CallableResultOwnership::Scalar)
            }
            Self::Nat => matches!(
                ownership,
                flbc::CallableResultOwnership::Scalar
                    | flbc::CallableResultOwnership::OwnedOrScalar
            ),
            Self::Abi => true,
            Self::String
            | Self::Constructor
            | Self::Array
            | Self::Ref
            | Self::Thunk
            | Self::Task
            | Self::Closure(_) => {
                matches!(ownership, flbc::CallableResultOwnership::Owned)
            }
        }
    }
}

/// Effect class carried by an intrinsic signature.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum EffectClass {
    Pure,
    State,
    Io,
    Task,
}

impl EffectClass {
    const fn token(self) -> &'static str {
        match self {
            Self::Pure => "pure",
            Self::State => "state",
            Self::Io => "io",
            Self::Task => "task",
        }
    }
}

/// One intrinsic signature bound into the FIR program identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IntrinsicDecl {
    pub id: IntrinsicId,
    pub row: String,
    pub arguments: Vec<ValueType>,
    pub argument_ownership: Vec<flbc::ArgumentOwnership>,
    pub result: ValueType,
    pub result_ownership: flbc::ResultOwnership,
    pub effect: EffectClass,
}

/// One typed constructor layout bound into the FIR program identity.
///
/// `fields` names the ABI-valued object slots. `static_scalar_bytes` fixes the
/// exact separately packed scalar payload for this bounded schema without
/// pretending that its byte-level ABI shape is a target-neutral FIR value type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConstructorDecl {
    pub id: ConstructorId,
    pub tag: u8,
    pub fields: Vec<ValueType>,
    pub static_scalar_bytes: Vec<u8>,
}

/// One source projection resolved to an exact constructor object slot.
///
/// The source structure name is resolution metadata and does not survive
/// canonical ingress. The referenced constructor supplies both the runtime
/// shape check and the result type, avoiding a second disagreeing layout.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectionDecl {
    pub id: ProjectionId,
    pub constructor: ConstructorId,
    pub field: u16,
}

/// One canonical callable closure signature.
///
/// Captures are deliberately absent: they are leading parameters of the
/// concrete target function and are checked at each closure-construction site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClosureTypeDecl {
    pub id: ClosureTypeId,
    pub parameters: Vec<ValueType>,
    pub parameter_ownership: Vec<flbc::ArgumentOwnership>,
    pub result: ValueType,
    pub result_ownership: flbc::CallableResultOwnership,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ApplicationResult {
    pub ty: ValueType,
    pub ownership: flbc::CallableResultOwnership,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ApplicationTypeError {
    EmptyArguments {
        closure_type: ClosureTypeId,
    },
    MissingClosureType {
        closure_type: ClosureTypeId,
    },
    PartialClosureTypeMissing {
        closure_type: ClosureTypeId,
        consumed: usize,
    },
    ArgumentType {
        closure_type: ClosureTypeId,
        argument: usize,
        expected: ValueType,
        actual: ValueType,
    },
    RemainderType {
        closure_type: ClosureTypeId,
        argument: usize,
        actual: ValueType,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ApplicationInferenceError<E> {
    Argument(E),
    Type(ApplicationTypeError),
}

/// One single-assignment FIR operation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Operation {
    Unit,
    Bool(bool),
    Nat(u64),
    String(String),
    Alias(ValueId),
    /// Preserve one concrete semantic value as an ABI-polymorphic value.
    ///
    /// This is an explicit FIR representation boundary, not a second runtime
    /// object domain. Mandatory FLBC lowering emits an ownership-preserving
    /// copy of the same Marrow object.
    Box(ValueId),
    /// Recover the declared concrete semantic class of an ABI-polymorphic value.
    ///
    /// The already-elaborated source contract supplies `ty`; this operation
    /// performs no hidden host conversion and lowers to an ordinary FLBC copy.
    Unbox {
        value: ValueId,
        ty: ValueType,
    },
    Ctor {
        constructor: ConstructorId,
        fields: Vec<ValueId>,
    },
    Project {
        projection: ProjectionId,
        value: ValueId,
    },
    Array {
        items: Vec<ValueId>,
    },
    Intrinsic {
        intrinsic: IntrinsicId,
        args: Vec<ValueId>,
    },
    /// The effect checkpoint defined by `Lean.Core.checkSystem`.
    ///
    /// The module name is semantic diagnostic context. The operation produces
    /// Unit and lowers to the explicit FLBC checkpoint followed by its scalar
    /// Unit value, so a stop cannot publish the binding.
    CheckSystem {
        module_name: String,
    },
    /// A `Lean.Core.checkSystem` checkpoint whose diagnostic module name is a
    /// computed `String` value. The operand is borrowed.
    CheckSystemValue {
        module_name: ValueId,
    },
    Call {
        function: FunctionId,
        args: Vec<ValueId>,
    },
    Closure {
        closure_type: ClosureTypeId,
        function: FunctionId,
        captures: Vec<ValueId>,
        capture_ownership: Vec<flbc::ArgumentOwnership>,
    },
    Apply {
        closure: ValueId,
        args: Vec<ValueId>,
        argument_ownership: Vec<flbc::ArgumentOwnership>,
        result_ownership: flbc::CallableResultOwnership,
    },
}

struct OperationReads<'a> {
    first: Option<ValueId>,
    rest: std::slice::Iter<'a, ValueId>,
}

impl Iterator for OperationReads<'_> {
    type Item = ValueId;

    fn next(&mut self) -> Option<Self::Item> {
        self.first.take().or_else(|| self.rest.next().copied())
    }
}

impl Operation {
    fn reads(&self) -> OperationReads<'_> {
        let empty = [].iter();
        match self {
            Self::Unit
            | Self::Bool(_)
            | Self::Nat(_)
            | Self::String(_)
            | Self::CheckSystem { .. } => OperationReads {
                first: None,
                rest: empty,
            },
            Self::Alias(value)
            | Self::Box(value)
            | Self::Unbox { value, .. }
            | Self::Project { value, .. }
            | Self::CheckSystemValue { module_name: value } => OperationReads {
                first: Some(*value),
                rest: empty,
            },
            Self::Ctor { fields, .. } => OperationReads {
                first: None,
                rest: fields.iter(),
            },
            Self::Array { items } => OperationReads {
                first: None,
                rest: items.iter(),
            },
            Self::Intrinsic { args, .. } | Self::Call { args, .. } => OperationReads {
                first: None,
                rest: args.iter(),
            },
            Self::Closure { captures, .. } => OperationReads {
                first: None,
                rest: captures.iter(),
            },
            Self::Apply { closure, args, .. } => OperationReads {
                first: Some(*closure),
                rest: args.iter(),
            },
        }
    }

    fn operand_count(&self) -> usize {
        match self {
            Self::Closure {
                captures,
                capture_ownership,
                ..
            } => captures.len().saturating_add(capture_ownership.len()),
            Self::Apply {
                args,
                argument_ownership,
                ..
            } => args
                .len()
                .saturating_add(argument_ownership.len())
                .saturating_add(2),
            _ => self.reads().count(),
        }
    }

    fn literal_bytes(&self) -> usize {
        match self {
            Self::String(value) => value.len(),
            Self::CheckSystem { module_name } => module_name.len(),
            _ => 0,
        }
    }
}

/// One canonical value definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Binding {
    pub id: ValueId,
    pub ty: ValueType,
    pub operation: Operation,
}

/// Structured control terminator. Blocks never fall through implicitly.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Terminator {
    Jump {
        target: BlockId,
    },
    BranchZero {
        condition: ValueId,
        zero: BlockId,
        nonzero: BlockId,
    },
    Return {
        value: ValueId,
    },
    Panic {
        message: ValueId,
    },
}

impl Terminator {
    fn reads(&self) -> &[ValueId] {
        match self {
            Self::Jump { .. } => &[],
            Self::BranchZero { condition, .. } => std::slice::from_ref(condition),
            Self::Return { value } => std::slice::from_ref(value),
            Self::Panic { message } => std::slice::from_ref(message),
        }
    }

    fn successors(&self) -> [Option<BlockId>; 2] {
        match self {
            Self::Jump { target } => [Some(*target), None],
            Self::BranchZero { zero, nonzero, .. } => [Some(*zero), Some(*nonzero)],
            Self::Return { .. } | Self::Panic { .. } => [None, None],
        }
    }
}

/// One canonically numbered basic block.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Block {
    pub id: BlockId,
    pub bindings: Vec<Binding>,
    pub terminator: Terminator,
}

/// One canonically numbered FIR function.
///
/// Parameters occupy values `0..parameters.len()`. Bindings continue that
/// numbering across blocks in block-table order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Function {
    pub id: FunctionId,
    pub parameters: Vec<ValueType>,
    pub parameter_ownership: Vec<flbc::ArgumentOwnership>,
    pub result: ValueType,
    pub result_ownership: flbc::CallableResultOwnership,
    pub blocks: Vec<Block>,
}

/// Untrusted FIR. Constructing this type does not authorize lowering.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program {
    pub schema_version: u16,
    pub entry: FunctionId,
    pub constructors: Vec<ConstructorDecl>,
    pub projections: Vec<ProjectionDecl>,
    pub closure_types: Vec<ClosureTypeDecl>,
    pub intrinsics: Vec<IntrinsicDecl>,
    pub functions: Vec<Function>,
}

impl Program {
    pub fn new(
        entry: FunctionId,
        constructors: Vec<ConstructorDecl>,
        projections: Vec<ProjectionDecl>,
        intrinsics: Vec<IntrinsicDecl>,
        functions: Vec<Function>,
    ) -> Self {
        Self {
            schema_version: FIR_SCHEMA_VERSION,
            entry,
            constructors,
            projections,
            closure_types: Vec::new(),
            intrinsics,
            functions,
        }
    }

    pub fn new_with_closures(
        entry: FunctionId,
        constructors: Vec<ConstructorDecl>,
        projections: Vec<ProjectionDecl>,
        closure_types: Vec<ClosureTypeDecl>,
        intrinsics: Vec<IntrinsicDecl>,
        functions: Vec<Function>,
    ) -> Self {
        Self {
            schema_version: FIR_SCHEMA_VERSION,
            entry,
            constructors,
            projections,
            closure_types,
            intrinsics,
            functions,
        }
    }
}

/// FIR whose tables, types, CFG, resource use, and definite initialization
/// passed [`validate`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValidatedProgram {
    program: Program,
}

impl ValidatedProgram {
    pub const fn entry(&self) -> FunctionId {
        self.program.entry
    }

    pub fn intrinsics(&self) -> &[IntrinsicDecl] {
        &self.program.intrinsics
    }

    pub fn constructors(&self) -> &[ConstructorDecl] {
        &self.program.constructors
    }

    pub fn projections(&self) -> &[ProjectionDecl] {
        &self.program.projections
    }

    pub fn closure_types(&self) -> &[ClosureTypeDecl] {
        &self.program.closure_types
    }

    pub fn functions(&self) -> &[Function] {
        &self.program.functions
    }

    pub const fn schema_version(&self) -> u16 {
        self.program.schema_version
    }

    /// Deterministic target-neutral rendering. Text parsing is deliberately
    /// outside this bounded checkpoint.
    pub fn write_canonical(&self, output: &mut impl fmt::Write) -> fmt::Result {
        writeln!(
            output,
            "fir/{} entry=f{}",
            self.program.schema_version,
            self.program.entry.get()
        )?;
        for constructor in &self.program.constructors {
            write!(
                output,
                "constructor c{} tag={} fields=[",
                constructor.id.get(),
                constructor.tag
            )?;
            write_types(output, &constructor.fields)?;
            output.write_str("] scalar_bytes=")?;
            write_hex_bytes(output, &constructor.static_scalar_bytes)?;
            output.write_char('\n')?;
        }
        for projection in &self.program.projections {
            writeln!(
                output,
                "projection p{} constructor=c{} field={}",
                projection.id.get(),
                projection.constructor.get(),
                projection.field
            )?;
        }
        for closure_type in &self.program.closure_types {
            write!(output, "closure_type s{} params=[", closure_type.id.get())?;
            write_types(output, &closure_type.parameters)?;
            output.write_str("] ownership=")?;
            write_argument_ownership(output, &closure_type.parameter_ownership)?;
            output.write_str(" result=")?;
            write_type(output, closure_type.result)?;
            writeln!(
                output,
                " result_ownership={}",
                closure_type.result_ownership.token()
            )?;
        }
        for intrinsic in &self.program.intrinsics {
            write!(output, "intrinsic i{} row=", intrinsic.id.get())?;
            write_hex_bytes(output, intrinsic.row.as_bytes())?;
            write!(output, " args=[")?;
            write_types(output, &intrinsic.arguments)?;
            output.write_str("] ownership=[")?;
            for (index, disposition) in intrinsic.argument_ownership.iter().enumerate() {
                if index != 0 {
                    output.write_char(',')?;
                }
                output.write_str(disposition.token())?;
            }
            output.write_str("] result=")?;
            write_type(output, intrinsic.result)?;
            writeln!(
                output,
                " result_ownership={} effect={}",
                intrinsic.result_ownership.token(),
                intrinsic.effect.token()
            )?;
        }
        for function in &self.program.functions {
            write!(output, "function f{} params=[", function.id.get())?;
            write_types(output, &function.parameters)?;
            output.write_str("] ownership=[")?;
            for (index, disposition) in function.parameter_ownership.iter().enumerate() {
                if index != 0 {
                    output.write_char(',')?;
                }
                output.write_str(disposition.token())?;
            }
            output.write_str("] result=")?;
            write_type(output, function.result)?;
            writeln!(
                output,
                " result_ownership={}",
                function.result_ownership.token()
            )?;
            for block in &function.blocks {
                writeln!(output, " block b{}", block.id.get())?;
                for binding in &block.bindings {
                    write!(output, "  v{}:", binding.id.get())?;
                    write_type(output, binding.ty)?;
                    output.write_str(" = ")?;
                    write_operation(output, &binding.operation)?;
                    output.write_char('\n')?;
                }
                output.write_str("  ")?;
                write_terminator(output, &block.terminator)?;
                output.write_char('\n')?;
            }
        }
        Ok(())
    }

    pub fn canonical_text(&self) -> String {
        let mut output = String::new();
        self.write_canonical(&mut output)
            .expect("writing to String is infallible");
        output
    }
}

/// Exact reason an untrusted FIR program was refused.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ValidationError {
    ResourceLimit {
        resource: ValidationResource,
        limit: usize,
        observed: usize,
    },
    AllocationFailure {
        resource: ValidationResource,
        requested: usize,
    },
    UnsupportedVersion {
        seen: u16,
    },
    EmptyProgram,
    NonCanonicalConstructorId {
        index: usize,
        seen: ConstructorId,
    },
    ConstructorTagOutOfRange {
        constructor: ConstructorId,
        tag: u8,
    },
    TooManyConstructorFields {
        constructor: ConstructorId,
        count: usize,
    },
    TooManyConstructorScalarBytes {
        constructor: ConstructorId,
        count: usize,
    },
    NonCanonicalProjectionId {
        index: usize,
        seen: ProjectionId,
    },
    ProjectionMissingConstructor {
        projection: ProjectionId,
        constructor: ConstructorId,
    },
    ProjectionFieldOutOfBounds {
        projection: ProjectionId,
        constructor: ConstructorId,
        field: u16,
        field_count: usize,
    },
    NonCanonicalClosureTypeId {
        index: usize,
        seen: ClosureTypeId,
    },
    EmptyClosureType {
        closure_type: ClosureTypeId,
    },
    ClosureTypeOwnershipArity {
        closure_type: ClosureTypeId,
        parameters: usize,
        ownership: usize,
    },
    ClosureTypeResultOwnership {
        closure_type: ClosureTypeId,
        result: ValueType,
        ownership: flbc::CallableResultOwnership,
    },
    ClosureTypesNotSorted {
        previous: ClosureTypeId,
        current: ClosureTypeId,
    },
    MissingClosureType {
        closure_type: ClosureTypeId,
    },
    NonCanonicalIntrinsicId {
        index: usize,
        seen: IntrinsicId,
    },
    InvalidIntrinsicRow {
        intrinsic: IntrinsicId,
        row_bytes: usize,
    },
    IntrinsicRowsNotSorted {
        previous: IntrinsicId,
        current: IntrinsicId,
    },
    IntrinsicOwnershipArity {
        intrinsic: IntrinsicId,
        arguments: usize,
        ownership: usize,
    },
    NonCanonicalFunctionId {
        index: usize,
        seen: FunctionId,
    },
    FunctionOwnershipArity {
        function: FunctionId,
        parameters: usize,
        ownership: usize,
    },
    FunctionResultOwnership {
        function: FunctionId,
        result: ValueType,
        ownership: flbc::CallableResultOwnership,
    },
    MissingEntry {
        entry: FunctionId,
    },
    EntryHasParameters {
        entry: FunctionId,
        count: usize,
    },
    EmptyFunction {
        function: FunctionId,
    },
    NonCanonicalBlockId {
        function: FunctionId,
        index: usize,
        seen: BlockId,
    },
    NonCanonicalValueId {
        function: FunctionId,
        block: BlockId,
        expected: usize,
        seen: ValueId,
    },
    RegisterWidthExceeded {
        function: FunctionId,
        values: usize,
    },
    UnknownValue {
        function: FunctionId,
        block: BlockId,
        value: ValueId,
    },
    ReadBeforeDefinition {
        function: FunctionId,
        block: BlockId,
        value: ValueId,
    },
    BindingType {
        function: FunctionId,
        block: BlockId,
        value: ValueId,
        declared: ValueType,
        inferred: ValueType,
    },
    RedundantBox {
        function: FunctionId,
        block: BlockId,
        value: ValueId,
    },
    UnboxOperandType {
        function: FunctionId,
        block: BlockId,
        actual: ValueType,
    },
    CheckSystemModuleNameType {
        function: FunctionId,
        block: BlockId,
        actual: ValueType,
    },
    RedundantUnbox {
        function: FunctionId,
        block: BlockId,
        value: ValueId,
    },
    MissingIntrinsic {
        function: FunctionId,
        block: BlockId,
        intrinsic: IntrinsicId,
    },
    IntrinsicArity {
        function: FunctionId,
        block: BlockId,
        intrinsic: IntrinsicId,
        expected: usize,
        actual: usize,
    },
    IntrinsicArgumentType {
        function: FunctionId,
        block: BlockId,
        intrinsic: IntrinsicId,
        argument: usize,
        expected: ValueType,
        actual: ValueType,
    },
    MissingCallTarget {
        function: FunctionId,
        block: BlockId,
        target: FunctionId,
    },
    CallArity {
        function: FunctionId,
        block: BlockId,
        target: FunctionId,
        expected: usize,
        actual: usize,
    },
    CallArgumentType {
        function: FunctionId,
        block: BlockId,
        target: FunctionId,
        argument: usize,
        expected: ValueType,
        actual: ValueType,
    },
    MissingClosureTarget {
        function: FunctionId,
        block: BlockId,
        target: FunctionId,
    },
    ClosureTargetArityOverflow {
        function: FunctionId,
        block: BlockId,
        target: FunctionId,
        target_parameters: usize,
    },
    ClosureTargetShape {
        function: FunctionId,
        block: BlockId,
        target: FunctionId,
        captures: usize,
        parameters: usize,
        target_parameters: usize,
    },
    ClosureOwnershipArity {
        function: FunctionId,
        block: BlockId,
        target: FunctionId,
        captures: usize,
        ownership: usize,
    },
    ClosureOwnershipContract {
        function: FunctionId,
        block: BlockId,
        target: FunctionId,
        capture: usize,
        expected: flbc::ArgumentOwnership,
        actual: flbc::ArgumentOwnership,
    },
    ClosureUniqueCapture {
        function: FunctionId,
        block: BlockId,
        target: FunctionId,
        capture: usize,
    },
    ClosureCaptureType {
        function: FunctionId,
        block: BlockId,
        target: FunctionId,
        capture: usize,
        expected: ValueType,
        actual: ValueType,
    },
    ClosureParameterType {
        function: FunctionId,
        block: BlockId,
        target: FunctionId,
        parameter: usize,
        expected: ValueType,
        actual: ValueType,
    },
    ClosureParameterOwnership {
        function: FunctionId,
        block: BlockId,
        target: FunctionId,
        parameter: usize,
        expected: flbc::ArgumentOwnership,
        actual: flbc::ArgumentOwnership,
    },
    ClosureResultType {
        function: FunctionId,
        block: BlockId,
        target: FunctionId,
        expected: ValueType,
        actual: ValueType,
    },
    ClosureResultOwnership {
        function: FunctionId,
        block: BlockId,
        target: FunctionId,
        expected: flbc::CallableResultOwnership,
        actual: flbc::CallableResultOwnership,
    },
    ApplyOperandType {
        function: FunctionId,
        block: BlockId,
        actual: ValueType,
    },
    EmptyApply {
        function: FunctionId,
        block: BlockId,
        closure_type: ClosureTypeId,
    },
    ApplyOwnershipArity {
        function: FunctionId,
        block: BlockId,
        closure_type: ClosureTypeId,
        arguments: usize,
        ownership: usize,
    },
    ApplyOwnershipContract {
        function: FunctionId,
        block: BlockId,
        closure_type: ClosureTypeId,
        argument: usize,
        expected: flbc::ArgumentOwnership,
        actual: flbc::ArgumentOwnership,
    },
    ApplyResultOwnershipContract {
        function: FunctionId,
        block: BlockId,
        closure_type: ClosureTypeId,
        expected: flbc::CallableResultOwnership,
        actual: flbc::CallableResultOwnership,
    },
    ApplyPartialClosureTypeMissing {
        function: FunctionId,
        block: BlockId,
        closure_type: ClosureTypeId,
        consumed: usize,
    },
    ApplyArgumentType {
        function: FunctionId,
        block: BlockId,
        closure_type: ClosureTypeId,
        argument: usize,
        expected: ValueType,
        actual: ValueType,
    },
    ApplyRemainderType {
        function: FunctionId,
        block: BlockId,
        closure_type: ClosureTypeId,
        argument: usize,
        actual: ValueType,
    },
    NatConstantOutOfRange {
        function: FunctionId,
        block: BlockId,
        value: u64,
    },
    MissingConstructor {
        function: FunctionId,
        block: BlockId,
        constructor: ConstructorId,
    },
    ConstructorArity {
        function: FunctionId,
        block: BlockId,
        constructor: ConstructorId,
        expected: usize,
        actual: usize,
    },
    ConstructorArgumentType {
        function: FunctionId,
        block: BlockId,
        constructor: ConstructorId,
        argument: usize,
        expected: ValueType,
        actual: ValueType,
    },
    MissingProjection {
        function: FunctionId,
        block: BlockId,
        projection: ProjectionId,
    },
    ProjectionOperandType {
        function: FunctionId,
        block: BlockId,
        projection: ProjectionId,
        actual: ValueType,
    },
    JumpOutOfBounds {
        function: FunctionId,
        block: BlockId,
        target: BlockId,
        block_count: usize,
    },
    EntryHasPredecessor {
        function: FunctionId,
        block: BlockId,
    },
    BranchConditionType {
        function: FunctionId,
        block: BlockId,
        actual: ValueType,
    },
    ReturnType {
        function: FunctionId,
        block: BlockId,
        expected: ValueType,
        actual: ValueType,
    },
    PanicMessageType {
        function: FunctionId,
        block: BlockId,
        actual: ValueType,
    },
    UnreachableBlock {
        function: FunctionId,
        block: BlockId,
    },
}

impl fmt::Display for ValidationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ResourceLimit {
                resource,
                limit,
                observed,
            } => write!(
                formatter,
                "FIR resource {resource:?} observed {observed}, limit {limit}"
            ),
            Self::AllocationFailure {
                resource,
                requested,
            } => write!(
                formatter,
                "FIR validator could not reserve {requested} units for {resource:?}"
            ),
            Self::UnsupportedVersion { seen } => {
                write!(formatter, "unsupported FIR schema version {seen}")
            }
            Self::EmptyProgram => formatter.write_str("FIR function table is empty"),
            Self::NonCanonicalConstructorId { index, seen } => write!(
                formatter,
                "constructor table index {index} carries id {}",
                seen.get()
            ),
            Self::ConstructorTagOutOfRange { constructor, tag } => write!(
                formatter,
                "constructor {} tag {tag} exceeds the ABI range",
                constructor.get()
            ),
            Self::TooManyConstructorFields { constructor, count } => write!(
                formatter,
                "constructor {} declares {count} object fields",
                constructor.get()
            ),
            Self::TooManyConstructorScalarBytes { constructor, count } => write!(
                formatter,
                "constructor {} declares {count} scalar bytes",
                constructor.get()
            ),
            Self::NonCanonicalProjectionId { index, seen } => write!(
                formatter,
                "projection table index {index} carries id {}",
                seen.get()
            ),
            Self::ProjectionMissingConstructor {
                projection,
                constructor,
            } => write!(
                formatter,
                "projection {} references missing constructor {}",
                projection.get(),
                constructor.get()
            ),
            Self::ProjectionFieldOutOfBounds {
                projection,
                constructor,
                field,
                field_count,
            } => write!(
                formatter,
                "projection {} names field {field} outside constructor {} with {field_count} fields",
                projection.get(),
                constructor.get()
            ),
            Self::NonCanonicalClosureTypeId { index, seen } => write!(
                formatter,
                "closure type table index {index} carries id {}",
                seen.get()
            ),
            Self::EmptyClosureType { closure_type } => write!(
                formatter,
                "closure type {} has no callable parameters",
                closure_type.get()
            ),
            Self::ClosureTypeOwnershipArity {
                closure_type,
                parameters,
                ownership,
            } => write!(
                formatter,
                "closure type {} has {parameters} typed parameters but {ownership} ownership dispositions",
                closure_type.get()
            ),
            Self::ClosureTypeResultOwnership {
                closure_type,
                result,
                ownership,
            } => write!(
                formatter,
                "closure type {} result {result:?} cannot carry {} ownership",
                closure_type.get(),
                ownership.token()
            ),
            Self::ClosureTypesNotSorted { previous, current } => write!(
                formatter,
                "closure types are not strictly sorted at ids {} then {}",
                previous.get(),
                current.get()
            ),
            Self::MissingClosureType { closure_type } => write!(
                formatter,
                "value type references missing closure type {}",
                closure_type.get()
            ),
            Self::NonCanonicalIntrinsicId { index, seen } => write!(
                formatter,
                "intrinsic table index {index} carries id {}",
                seen.get()
            ),
            Self::InvalidIntrinsicRow {
                intrinsic,
                row_bytes,
            } => write!(
                formatter,
                "intrinsic {} has an invalid {row_bytes}-byte row id",
                intrinsic.get(),
            ),
            Self::IntrinsicRowsNotSorted { previous, current } => write!(
                formatter,
                "intrinsic rows are not strictly sorted at ids {} then {}",
                previous.get(),
                current.get(),
            ),
            Self::IntrinsicOwnershipArity {
                intrinsic,
                arguments,
                ownership,
            } => write!(
                formatter,
                "intrinsic {} has {arguments} typed arguments but {ownership} ownership dispositions",
                intrinsic.get()
            ),
            Self::NonCanonicalFunctionId { index, seen } => write!(
                formatter,
                "function table index {index} carries id {}",
                seen.get()
            ),
            Self::FunctionOwnershipArity {
                function,
                parameters,
                ownership,
            } => write!(
                formatter,
                "function {} has {parameters} typed parameters but {ownership} ownership dispositions",
                function.get()
            ),
            Self::FunctionResultOwnership {
                function,
                result,
                ownership,
            } => write!(
                formatter,
                "function {} result {result:?} cannot carry {} ownership",
                function.get(),
                ownership.token()
            ),
            Self::MissingEntry { entry } => {
                write!(formatter, "entry function {} does not exist", entry.get())
            }
            Self::EntryHasParameters { entry, count } => write!(
                formatter,
                "entry function {} has {count} parameters",
                entry.get()
            ),
            Self::EmptyFunction { function } => {
                write!(formatter, "function {} has no blocks", function.get())
            }
            Self::NonCanonicalBlockId {
                function,
                index,
                seen,
            } => write!(
                formatter,
                "function {} block index {index} carries id {}",
                function.get(),
                seen.get()
            ),
            Self::NonCanonicalValueId {
                function,
                block,
                expected,
                seen,
            } => write!(
                formatter,
                "function {} block {} expected value {expected}, saw {}",
                function.get(),
                block.get(),
                seen.get()
            ),
            Self::RegisterWidthExceeded { function, values } => write!(
                formatter,
                "function {} has {values} values beyond FLBC register width",
                function.get()
            ),
            Self::UnknownValue {
                function,
                block,
                value,
            } => write!(
                formatter,
                "function {} block {} references unknown value {}",
                function.get(),
                block.get(),
                value.get()
            ),
            Self::ReadBeforeDefinition {
                function,
                block,
                value,
            } => write!(
                formatter,
                "function {} block {} reads value {} before every predecessor defines it",
                function.get(),
                block.get(),
                value.get()
            ),
            Self::BindingType {
                function,
                block,
                value,
                declared,
                inferred,
            } => write!(
                formatter,
                "function {} block {} value {} declares {declared:?}, inferred {inferred:?}",
                function.get(),
                block.get(),
                value.get()
            ),
            Self::RedundantBox {
                function,
                block,
                value,
            } => write!(
                formatter,
                "function {} block {} boxes already-ABI value {}",
                function.get(),
                block.get(),
                value.get()
            ),
            Self::UnboxOperandType {
                function,
                block,
                actual,
            } => write!(
                formatter,
                "function {} block {} unboxes {actual:?} instead of Abi",
                function.get(),
                block.get()
            ),
            Self::CheckSystemModuleNameType {
                function,
                block,
                actual,
            } => write!(
                formatter,
                "function {} block {} checkSystem module name is {actual:?}, expected String",
                function.get(),
                block.get()
            ),
            Self::RedundantUnbox {
                function,
                block,
                value,
            } => write!(
                formatter,
                "function {} block {} unboxes value {} back to Abi",
                function.get(),
                block.get(),
                value.get()
            ),
            Self::MissingIntrinsic {
                function,
                block,
                intrinsic,
            } => write!(
                formatter,
                "function {} block {} references missing intrinsic {}",
                function.get(),
                block.get(),
                intrinsic.get()
            ),
            Self::IntrinsicArity {
                function,
                block,
                intrinsic,
                expected,
                actual,
            } => write!(
                formatter,
                "function {} block {} intrinsic {} expects {expected} args, got {actual}",
                function.get(),
                block.get(),
                intrinsic.get()
            ),
            Self::IntrinsicArgumentType {
                function,
                block,
                intrinsic,
                argument,
                expected,
                actual,
            } => write!(
                formatter,
                "function {} block {} intrinsic {} arg {argument} expects {expected:?}, got {actual:?}",
                function.get(),
                block.get(),
                intrinsic.get()
            ),
            Self::MissingCallTarget {
                function,
                block,
                target,
            } => write!(
                formatter,
                "function {} block {} calls missing function {}",
                function.get(),
                block.get(),
                target.get()
            ),
            Self::CallArity {
                function,
                block,
                target,
                expected,
                actual,
            } => write!(
                formatter,
                "function {} block {} call f{} expects {expected} args, got {actual}",
                function.get(),
                block.get(),
                target.get()
            ),
            Self::CallArgumentType {
                function,
                block,
                target,
                argument,
                expected,
                actual,
            } => write!(
                formatter,
                "function {} block {} call f{} arg {argument} expects {expected:?}, got {actual:?}",
                function.get(),
                block.get(),
                target.get()
            ),
            Self::MissingClosureTarget {
                function,
                block,
                target,
            } => write!(
                formatter,
                "function {} block {} builds a closure for missing function {}",
                function.get(),
                block.get(),
                target.get()
            ),
            Self::ClosureTargetArityOverflow {
                function,
                block,
                target,
                target_parameters,
            } => write!(
                formatter,
                "function {} block {} closure target {} has {target_parameters} parameters, which cannot be encoded with the interpreter target word",
                function.get(),
                block.get(),
                target.get()
            ),
            Self::ClosureTargetShape {
                function,
                block,
                target,
                captures,
                parameters,
                target_parameters,
            } => write!(
                formatter,
                "function {} block {} closure target {} has {target_parameters} parameters, but {captures} captures plus {parameters} callable parameters were declared",
                function.get(),
                block.get(),
                target.get()
            ),
            Self::ClosureOwnershipArity {
                function,
                block,
                target,
                captures,
                ownership,
            } => write!(
                formatter,
                "function {} block {} closure target {} carries {ownership} ownership dispositions for {captures} captures",
                function.get(),
                block.get(),
                target.get()
            ),
            Self::ClosureOwnershipContract {
                function,
                block,
                target,
                capture,
                expected,
                actual,
            } => write!(
                formatter,
                "function {} block {} closure target {} capture {capture} ownership is {}, expected {}",
                function.get(),
                block.get(),
                target.get(),
                actual.token(),
                expected.token()
            ),
            Self::ClosureUniqueCapture {
                function,
                block,
                target,
                capture,
            } => write!(
                formatter,
                "function {} block {} closure target {} capture {capture} is unique, but reusable closures cannot retain a unique payload",
                function.get(),
                block.get(),
                target.get()
            ),
            Self::ClosureCaptureType {
                function,
                block,
                target,
                capture,
                expected,
                actual,
            } => write!(
                formatter,
                "function {} block {} closure target {} capture {capture} expects {expected:?}, got {actual:?}",
                function.get(),
                block.get(),
                target.get()
            ),
            Self::ClosureParameterType {
                function,
                block,
                target,
                parameter,
                expected,
                actual,
            } => write!(
                formatter,
                "function {} block {} closure target {} callable parameter {parameter} declares {actual:?}, expected {expected:?}",
                function.get(),
                block.get(),
                target.get()
            ),
            Self::ClosureParameterOwnership {
                function,
                block,
                target,
                parameter,
                expected,
                actual,
            } => write!(
                formatter,
                "function {} block {} closure target {} callable parameter {parameter} ownership is {}, expected {}",
                function.get(),
                block.get(),
                target.get(),
                actual.token(),
                expected.token()
            ),
            Self::ClosureResultType {
                function,
                block,
                target,
                expected,
                actual,
            } => write!(
                formatter,
                "function {} block {} closure target {} returns {actual:?}, expected {expected:?}",
                function.get(),
                block.get(),
                target.get()
            ),
            Self::ClosureResultOwnership {
                function,
                block,
                target,
                expected,
                actual,
            } => write!(
                formatter,
                "function {} block {} closure target {} result ownership is {}, expected {}",
                function.get(),
                block.get(),
                target.get(),
                actual.token(),
                expected.token()
            ),
            Self::ApplyOperandType {
                function,
                block,
                actual,
            } => write!(
                formatter,
                "function {} block {} applies {actual:?}, expected a typed closure",
                function.get(),
                block.get()
            ),
            Self::EmptyApply {
                function,
                block,
                closure_type,
            } => write!(
                formatter,
                "function {} block {} closure type {} has an empty application",
                function.get(),
                block.get(),
                closure_type.get()
            ),
            Self::ApplyOwnershipArity {
                function,
                block,
                closure_type,
                arguments,
                ownership,
            } => write!(
                formatter,
                "function {} block {} closure type {} has {arguments} arguments but {ownership} ownership dispositions",
                function.get(),
                block.get(),
                closure_type.get()
            ),
            Self::ApplyOwnershipContract {
                function,
                block,
                closure_type,
                argument,
                expected,
                actual,
            } => write!(
                formatter,
                "function {} block {} closure type {} argument {argument} ownership is {}, expected {}",
                function.get(),
                block.get(),
                closure_type.get(),
                actual.token(),
                expected.token()
            ),
            Self::ApplyResultOwnershipContract {
                function,
                block,
                closure_type,
                expected,
                actual,
            } => write!(
                formatter,
                "function {} block {} closure type {} application result ownership is {}, expected {}",
                function.get(),
                block.get(),
                closure_type.get(),
                actual.token(),
                expected.token()
            ),
            Self::ApplyPartialClosureTypeMissing {
                function,
                block,
                closure_type,
                consumed,
            } => write!(
                formatter,
                "function {} block {} closure type {} has no canonical suffix after {consumed} arguments",
                function.get(),
                block.get(),
                closure_type.get()
            ),
            Self::ApplyArgumentType {
                function,
                block,
                closure_type,
                argument,
                expected,
                actual,
            } => write!(
                formatter,
                "function {} block {} closure type {} arg {argument} expects {expected:?}, got {actual:?}",
                function.get(),
                block.get(),
                closure_type.get()
            ),
            Self::ApplyRemainderType {
                function,
                block,
                closure_type,
                argument,
                actual,
            } => write!(
                formatter,
                "function {} block {} closure type {} returns {actual:?}, so argument {argument} has no closure to apply",
                function.get(),
                block.get(),
                closure_type.get()
            ),
            Self::NatConstantOutOfRange {
                function,
                block,
                value,
            } => write!(
                formatter,
                "function {} block {} Nat {value} exceeds the ABI scalar range",
                function.get(),
                block.get()
            ),
            Self::MissingConstructor {
                function,
                block,
                constructor,
            } => write!(
                formatter,
                "function {} block {} references missing constructor {}",
                function.get(),
                block.get(),
                constructor.get()
            ),
            Self::ConstructorArity {
                function,
                block,
                constructor,
                expected,
                actual,
            } => write!(
                formatter,
                "function {} block {} constructor {} expects {expected} fields, got {actual}",
                function.get(),
                block.get(),
                constructor.get()
            ),
            Self::ConstructorArgumentType {
                function,
                block,
                constructor,
                argument,
                expected,
                actual,
            } => write!(
                formatter,
                "function {} block {} constructor {} field {argument} expects {expected:?}, got {actual:?}",
                function.get(),
                block.get(),
                constructor.get()
            ),
            Self::MissingProjection {
                function,
                block,
                projection,
            } => write!(
                formatter,
                "function {} block {} references missing projection {}",
                function.get(),
                block.get(),
                projection.get()
            ),
            Self::ProjectionOperandType {
                function,
                block,
                projection,
                actual,
            } => write!(
                formatter,
                "function {} block {} projection {} expects a constructor, got {actual:?}",
                function.get(),
                block.get(),
                projection.get()
            ),
            Self::JumpOutOfBounds {
                function,
                block,
                target,
                block_count,
            } => write!(
                formatter,
                "function {} block {} jumps to {} with {block_count} blocks",
                function.get(),
                block.get(),
                target.get()
            ),
            Self::EntryHasPredecessor { function, block } => write!(
                formatter,
                "function {} block {} jumps to canonical entry block 0",
                function.get(),
                block.get()
            ),
            Self::BranchConditionType {
                function,
                block,
                actual,
            } => write!(
                formatter,
                "function {} block {} branches on {actual:?}, expected Nat or Bool",
                function.get(),
                block.get()
            ),
            Self::ReturnType {
                function,
                block,
                expected,
                actual,
            } => write!(
                formatter,
                "function {} block {} returns {actual:?}, expected {expected:?}",
                function.get(),
                block.get()
            ),
            Self::PanicMessageType {
                function,
                block,
                actual,
            } => write!(
                formatter,
                "function {} block {} panics with {actual:?}, expected String",
                function.get(),
                block.get()
            ),
            Self::UnreachableBlock { function, block } => write!(
                formatter,
                "function {} block {} is unreachable",
                function.get(),
                block.get()
            ),
        }
    }
}

impl std::error::Error for ValidationError {}

impl ValidationError {
    /// Whether this refusal is a budget or allocation failure, not a
    /// program-shape refusal.
    pub fn is_resource_exhaustion(&self) -> bool {
        matches!(
            self,
            Self::ResourceLimit { .. } | Self::AllocationFailure { .. }
        )
    }
}

/// Validate all FIR tables and every function CFG before lowering.
pub fn validate(
    program: Program,
    limits: ValidationLimits,
) -> Result<ValidatedProgram, ValidationError> {
    if program.schema_version != FIR_SCHEMA_VERSION {
        return Err(ValidationError::UnsupportedVersion {
            seen: program.schema_version,
        });
    }
    if program.functions.is_empty() {
        return Err(ValidationError::EmptyProgram);
    }
    charge(
        ValidationResource::Functions,
        program.functions.len(),
        limits.max_functions,
    )?;
    charge(
        ValidationResource::Constructors,
        program.constructors.len(),
        limits.max_constructors,
    )?;
    charge(
        ValidationResource::Projections,
        program.projections.len(),
        limits.max_projections,
    )?;
    charge(
        ValidationResource::ClosureTypes,
        program.closure_types.len(),
        limits.max_closure_types,
    )?;
    charge(
        ValidationResource::Intrinsics,
        program.intrinsics.len(),
        limits.max_intrinsics,
    )?;

    let mut blocks = 0usize;
    let mut values = 0usize;
    let mut operations = 0usize;
    let mut operands = 0usize;
    let mut literal_bytes = 0usize;
    let mut dataflow_cells = 0usize;

    for constructor in &program.constructors {
        operands = checked_total(
            ValidationResource::Operands,
            operands,
            constructor.fields.len(),
            limits.max_operands,
        )?;
        literal_bytes = checked_total(
            ValidationResource::LiteralBytes,
            literal_bytes,
            constructor.static_scalar_bytes.len(),
            limits.max_literal_bytes,
        )?;
    }
    for intrinsic in &program.intrinsics {
        operands = checked_total(
            ValidationResource::Operands,
            operands,
            intrinsic.arguments.len(),
            limits.max_operands,
        )?;
        literal_bytes = checked_total(
            ValidationResource::LiteralBytes,
            literal_bytes,
            intrinsic.row.len(),
            limits.max_literal_bytes,
        )?;
    }
    for closure_type in &program.closure_types {
        operands = checked_total(
            ValidationResource::Operands,
            operands,
            closure_type
                .parameters
                .len()
                .saturating_add(closure_type.parameter_ownership.len()),
            limits.max_operands,
        )?;
    }
    for function in &program.functions {
        operands = checked_total(
            ValidationResource::Operands,
            operands,
            function.parameter_ownership.len(),
            limits.max_operands,
        )?;
        let function_bindings = function
            .blocks
            .iter()
            .try_fold(0usize, |total, block| {
                total.checked_add(block.bindings.len())
            })
            .unwrap_or(usize::MAX);
        let function_values = function.parameters.len().saturating_add(function_bindings);
        let function_cells = function.blocks.len().saturating_mul(function_values);
        dataflow_cells = checked_total(
            ValidationResource::DataflowCells,
            dataflow_cells,
            function_cells,
            limits.max_dataflow_cells,
        )?;
        blocks = checked_total(
            ValidationResource::Blocks,
            blocks,
            function.blocks.len(),
            limits.max_blocks,
        )?;
        values = checked_total(
            ValidationResource::Values,
            values,
            function.parameters.len(),
            limits.max_values,
        )?;
        for block in &function.blocks {
            values = checked_total(
                ValidationResource::Values,
                values,
                block.bindings.len(),
                limits.max_values,
            )?;
            operations = checked_total(
                ValidationResource::Operations,
                operations,
                block.bindings.len(),
                limits.max_operations,
            )?;
            operands = checked_total(
                ValidationResource::Operands,
                operands,
                block.terminator.reads().len(),
                limits.max_operands,
            )?;
            for binding in &block.bindings {
                operands = checked_total(
                    ValidationResource::Operands,
                    operands,
                    binding.operation.operand_count(),
                    limits.max_operands,
                )?;
                literal_bytes = checked_total(
                    ValidationResource::LiteralBytes,
                    literal_bytes,
                    binding.operation.literal_bytes(),
                    limits.max_literal_bytes,
                )?;
            }
        }
    }

    validate_constructors(&program.constructors)?;
    validate_projections(&program.projections, &program.constructors)?;
    validate_closure_types(&program.closure_types)?;
    validate_program_types(&program)?;
    validate_intrinsics(&program.intrinsics)?;
    for (index, function) in program.functions.iter().enumerate() {
        if function.id.index() != Some(index) {
            return Err(ValidationError::NonCanonicalFunctionId {
                index,
                seen: function.id,
            });
        }
        if function.parameters.len() != function.parameter_ownership.len() {
            return Err(ValidationError::FunctionOwnershipArity {
                function: function.id,
                parameters: function.parameters.len(),
                ownership: function.parameter_ownership.len(),
            });
        }
        if !function
            .result
            .admits_callable_result(function.result_ownership)
        {
            return Err(ValidationError::FunctionResultOwnership {
                function: function.id,
                result: function.result,
                ownership: function.result_ownership,
            });
        }
    }
    let Some(entry) = program
        .entry
        .index()
        .and_then(|index| program.functions.get(index))
    else {
        return Err(ValidationError::MissingEntry {
            entry: program.entry,
        });
    };
    if !entry.parameters.is_empty() {
        return Err(ValidationError::EntryHasParameters {
            entry: entry.id,
            count: entry.parameters.len(),
        });
    }

    for function in &program.functions {
        validate_function(&program, function, limits)?;
    }
    Ok(ValidatedProgram { program })
}

fn validate_constructors(constructors: &[ConstructorDecl]) -> Result<(), ValidationError> {
    for (index, constructor) in constructors.iter().enumerate() {
        if constructor.id.index() != Some(index) {
            return Err(ValidationError::NonCanonicalConstructorId {
                index,
                seen: constructor.id,
            });
        }
        if constructor.tag > abi::TAG_MAX_CTOR_TAG {
            return Err(ValidationError::ConstructorTagOutOfRange {
                constructor: constructor.id,
                tag: constructor.tag,
            });
        }
        if constructor.fields.len() >= abi::MAX_CTOR_FIELDS {
            return Err(ValidationError::TooManyConstructorFields {
                constructor: constructor.id,
                count: constructor.fields.len(),
            });
        }
        if constructor.static_scalar_bytes.len() >= abi::MAX_CTOR_SCALARS_SIZE {
            return Err(ValidationError::TooManyConstructorScalarBytes {
                constructor: constructor.id,
                count: constructor.static_scalar_bytes.len(),
            });
        }
    }
    Ok(())
}

fn validate_projections(
    projections: &[ProjectionDecl],
    constructors: &[ConstructorDecl],
) -> Result<(), ValidationError> {
    for (index, projection) in projections.iter().enumerate() {
        if projection.id.index() != Some(index) {
            return Err(ValidationError::NonCanonicalProjectionId {
                index,
                seen: projection.id,
            });
        }
        let Some(constructor) = projection
            .constructor
            .index()
            .and_then(|index| constructors.get(index))
        else {
            return Err(ValidationError::ProjectionMissingConstructor {
                projection: projection.id,
                constructor: projection.constructor,
            });
        };
        if usize::from(projection.field) >= constructor.fields.len() {
            return Err(ValidationError::ProjectionFieldOutOfBounds {
                projection: projection.id,
                constructor: projection.constructor,
                field: projection.field,
                field_count: constructor.fields.len(),
            });
        }
    }
    Ok(())
}

fn validate_closure_types(closure_types: &[ClosureTypeDecl]) -> Result<(), ValidationError> {
    let mut previous: Option<&ClosureTypeDecl> = None;
    for (index, closure_type) in closure_types.iter().enumerate() {
        if closure_type.id.index() != Some(index) {
            return Err(ValidationError::NonCanonicalClosureTypeId {
                index,
                seen: closure_type.id,
            });
        }
        if closure_type.parameters.is_empty() {
            return Err(ValidationError::EmptyClosureType {
                closure_type: closure_type.id,
            });
        }
        if closure_type.parameters.len() != closure_type.parameter_ownership.len() {
            return Err(ValidationError::ClosureTypeOwnershipArity {
                closure_type: closure_type.id,
                parameters: closure_type.parameters.len(),
                ownership: closure_type.parameter_ownership.len(),
            });
        }
        if !closure_type
            .result
            .admits_callable_result(closure_type.result_ownership)
        {
            return Err(ValidationError::ClosureTypeResultOwnership {
                closure_type: closure_type.id,
                result: closure_type.result,
                ownership: closure_type.result_ownership,
            });
        }
        if let Some(previous) = previous
            && previous
                .parameters
                .cmp(&closure_type.parameters)
                .then_with(|| {
                    previous
                        .parameter_ownership
                        .cmp(&closure_type.parameter_ownership)
                })
                .then_with(|| previous.result.cmp(&closure_type.result))
                .then_with(|| {
                    previous
                        .result_ownership
                        .cmp(&closure_type.result_ownership)
                })
                != std::cmp::Ordering::Less
        {
            return Err(ValidationError::ClosureTypesNotSorted {
                previous: previous.id,
                current: closure_type.id,
            });
        }
        previous = Some(closure_type);
    }
    Ok(())
}

fn validate_program_types(program: &Program) -> Result<(), ValidationError> {
    for constructor in &program.constructors {
        for ty in &constructor.fields {
            validate_value_type(program, *ty)?;
        }
    }
    for closure_type in &program.closure_types {
        for ty in &closure_type.parameters {
            validate_value_type(program, *ty)?;
        }
        validate_value_type(program, closure_type.result)?;
    }
    for intrinsic in &program.intrinsics {
        for ty in &intrinsic.arguments {
            validate_value_type(program, *ty)?;
        }
        validate_value_type(program, intrinsic.result)?;
    }
    for function in &program.functions {
        for ty in &function.parameters {
            validate_value_type(program, *ty)?;
        }
        validate_value_type(program, function.result)?;
        for block in &function.blocks {
            for binding in &block.bindings {
                validate_value_type(program, binding.ty)?;
            }
        }
    }
    Ok(())
}

fn validate_value_type(program: &Program, ty: ValueType) -> Result<(), ValidationError> {
    if let ValueType::Closure(closure_type) = ty
        && closure_type
            .index()
            .is_none_or(|index| index >= program.closure_types.len())
    {
        return Err(ValidationError::MissingClosureType { closure_type });
    }
    Ok(())
}

fn closure_type_for_signature(
    closure_types: &[ClosureTypeDecl],
    parameters: &[ValueType],
    parameter_ownership: &[flbc::ArgumentOwnership],
    result: ValueType,
    result_ownership: flbc::CallableResultOwnership,
) -> Option<ClosureTypeId> {
    closure_types
        .binary_search_by(|candidate| {
            candidate
                .parameters
                .as_slice()
                .cmp(parameters)
                .then_with(|| {
                    candidate
                        .parameter_ownership
                        .as_slice()
                        .cmp(parameter_ownership)
                })
                .then_with(|| candidate.result.cmp(&result))
                .then_with(|| candidate.result_ownership.cmp(&result_ownership))
        })
        .ok()
        .and_then(|index| closure_types.get(index))
        .map(|candidate| candidate.id)
}

pub(crate) fn infer_application_type<E>(
    closure_types: &[ClosureTypeDecl],
    mut closure_type: ClosureTypeId,
    argument_count: usize,
    mut argument_type: impl FnMut(usize, ValueType, flbc::ArgumentOwnership) -> Result<ValueType, E>,
) -> Result<ApplicationResult, ApplicationInferenceError<E>> {
    if argument_count == 0 {
        return Err(ApplicationInferenceError::Type(
            ApplicationTypeError::EmptyArguments { closure_type },
        ));
    }

    let mut argument_offset = 0usize;
    loop {
        let signature = closure_type
            .index()
            .and_then(|index| closure_types.get(index))
            .ok_or(ApplicationInferenceError::Type(
                ApplicationTypeError::MissingClosureType { closure_type },
            ))?;
        let remaining_arguments = argument_count.saturating_sub(argument_offset);
        let consumed = remaining_arguments.min(signature.parameters.len());
        for (local_argument, (expected, expected_ownership)) in signature
            .parameters
            .iter()
            .copied()
            .zip(signature.parameter_ownership.iter().copied())
            .take(consumed)
            .enumerate()
        {
            let argument = argument_offset.saturating_add(local_argument);
            let actual = argument_type(argument, expected, expected_ownership)
                .map_err(ApplicationInferenceError::Argument)?;
            if actual != expected {
                return Err(ApplicationInferenceError::Type(
                    ApplicationTypeError::ArgumentType {
                        closure_type,
                        argument,
                        expected,
                        actual,
                    },
                ));
            }
        }

        if consumed < signature.parameters.len() {
            let remaining_parameters = &signature.parameters[consumed..];
            let remaining_ownership = &signature.parameter_ownership[consumed..];
            let partial = closure_type_for_signature(
                closure_types,
                remaining_parameters,
                remaining_ownership,
                signature.result,
                signature.result_ownership,
            )
            .ok_or(ApplicationInferenceError::Type(
                ApplicationTypeError::PartialClosureTypeMissing {
                    closure_type,
                    consumed,
                },
            ))?;
            return Ok(ApplicationResult {
                ty: ValueType::Closure(partial),
                ownership: flbc::CallableResultOwnership::Owned,
            });
        }

        argument_offset = argument_offset.saturating_add(consumed);
        if argument_offset == argument_count {
            return Ok(ApplicationResult {
                ty: signature.result,
                ownership: signature.result_ownership,
            });
        }
        let ValueType::Closure(next_closure_type) = signature.result else {
            return Err(ApplicationInferenceError::Type(
                ApplicationTypeError::RemainderType {
                    closure_type,
                    argument: argument_offset,
                    actual: signature.result,
                },
            ));
        };
        closure_type = next_closure_type;
    }
}

fn validate_intrinsics(intrinsics: &[IntrinsicDecl]) -> Result<(), ValidationError> {
    let mut previous: Option<&IntrinsicDecl> = None;
    for (index, intrinsic) in intrinsics.iter().enumerate() {
        if intrinsic.id.index() != Some(index) {
            return Err(ValidationError::NonCanonicalIntrinsicId {
                index,
                seen: intrinsic.id,
            });
        }
        if !valid_extern_row(&intrinsic.row) {
            return Err(ValidationError::InvalidIntrinsicRow {
                intrinsic: intrinsic.id,
                row_bytes: intrinsic.row.len(),
            });
        }
        if intrinsic.arguments.len() != intrinsic.argument_ownership.len() {
            return Err(ValidationError::IntrinsicOwnershipArity {
                intrinsic: intrinsic.id,
                arguments: intrinsic.arguments.len(),
                ownership: intrinsic.argument_ownership.len(),
            });
        }
        if let Some(previous) = previous
            && previous.row >= intrinsic.row
        {
            return Err(ValidationError::IntrinsicRowsNotSorted {
                previous: previous.id,
                current: intrinsic.id,
            });
        }
        previous = Some(intrinsic);
    }
    Ok(())
}

fn validate_function(
    program: &Program,
    function: &Function,
    limits: ValidationLimits,
) -> Result<(), ValidationError> {
    if function.blocks.is_empty() {
        return Err(ValidationError::EmptyFunction {
            function: function.id,
        });
    }
    let binding_count = function
        .blocks
        .iter()
        .try_fold(0usize, |total, block| {
            total.checked_add(block.bindings.len())
        })
        .ok_or(ValidationError::ResourceLimit {
            resource: ValidationResource::Values,
            limit: limits.max_values,
            observed: usize::MAX,
        })?;
    let value_count = function.parameters.len().checked_add(binding_count).ok_or(
        ValidationError::ResourceLimit {
            resource: ValidationResource::Values,
            limit: limits.max_values,
            observed: usize::MAX,
        },
    )?;
    if value_count > usize::from(u16::MAX) {
        return Err(ValidationError::RegisterWidthExceeded {
            function: function.id,
            values: value_count,
        });
    }
    let dataflow_cells =
        function
            .blocks
            .len()
            .checked_mul(value_count)
            .ok_or(ValidationError::ResourceLimit {
                resource: ValidationResource::DataflowCells,
                limit: limits.max_dataflow_cells,
                observed: usize::MAX,
            })?;
    charge(
        ValidationResource::DataflowCells,
        dataflow_cells,
        limits.max_dataflow_cells,
    )?;

    let mut value_types = Vec::new();
    value_types
        .try_reserve_exact(value_count)
        .map_err(|_| ValidationError::AllocationFailure {
            resource: ValidationResource::Values,
            requested: value_count,
        })?;
    value_types.extend_from_slice(&function.parameters);
    let mut next_value = function.parameters.len();
    for (block_index, block) in function.blocks.iter().enumerate() {
        if block.id.index() != Some(block_index) {
            return Err(ValidationError::NonCanonicalBlockId {
                function: function.id,
                index: block_index,
                seen: block.id,
            });
        }
        for binding in &block.bindings {
            if binding.id.index() != Some(next_value) {
                return Err(ValidationError::NonCanonicalValueId {
                    function: function.id,
                    block: block.id,
                    expected: next_value,
                    seen: binding.id,
                });
            }
            value_types.push(binding.ty);
            next_value += 1;
        }
    }

    for block in &function.blocks {
        for binding in &block.bindings {
            let inferred =
                infer_operation_type(program, function, block, &value_types, &binding.operation)?;
            if inferred != binding.ty {
                return Err(ValidationError::BindingType {
                    function: function.id,
                    block: block.id,
                    value: binding.id,
                    declared: binding.ty,
                    inferred,
                });
            }
        }
        validate_terminator_shape(function, block, &value_types)?;
        for target in block.terminator.successors().into_iter().flatten() {
            if target
                .index()
                .is_none_or(|index| index >= function.blocks.len())
            {
                return Err(ValidationError::JumpOutOfBounds {
                    function: function.id,
                    block: block.id,
                    target,
                    block_count: function.blocks.len(),
                });
            }
            if target == BlockId::new(0) {
                return Err(ValidationError::EntryHasPredecessor {
                    function: function.id,
                    block: block.id,
                });
            }
        }
    }

    validate_definite_initialization(function, value_count)
}

fn infer_operation_type(
    program: &Program,
    function: &Function,
    block: &Block,
    value_types: &[ValueType],
    operation: &Operation,
) -> Result<ValueType, ValidationError> {
    match operation {
        Operation::Unit => Ok(ValueType::Unit),
        Operation::Bool(_) => Ok(ValueType::Bool),
        Operation::Nat(value) => {
            if *value > (usize::MAX >> 1) as u64 {
                return Err(ValidationError::NatConstantOutOfRange {
                    function: function.id,
                    block: block.id,
                    value: *value,
                });
            }
            Ok(ValueType::Nat)
        }
        Operation::String(_) => Ok(ValueType::String),
        Operation::CheckSystem { .. } => Ok(ValueType::Unit),
        Operation::CheckSystemValue { module_name } => {
            let actual = value_type(function, block, value_types, *module_name)?;
            match actual {
                ValueType::String => Ok(ValueType::Unit),
                actual => Err(ValidationError::CheckSystemModuleNameType {
                    function: function.id,
                    block: block.id,
                    actual,
                }),
            }
        }
        Operation::Alias(value) => value_type(function, block, value_types, *value),
        Operation::Box(value) => {
            let actual = value_type(function, block, value_types, *value)?;
            if actual == ValueType::Abi {
                return Err(ValidationError::RedundantBox {
                    function: function.id,
                    block: block.id,
                    value: *value,
                });
            }
            Ok(ValueType::Abi)
        }
        Operation::Unbox { value, ty } => {
            let actual = value_type(function, block, value_types, *value)?;
            if actual != ValueType::Abi {
                return Err(ValidationError::UnboxOperandType {
                    function: function.id,
                    block: block.id,
                    actual,
                });
            }
            if *ty == ValueType::Abi {
                return Err(ValidationError::RedundantUnbox {
                    function: function.id,
                    block: block.id,
                    value: *value,
                });
            }
            Ok(*ty)
        }
        Operation::Ctor {
            constructor,
            fields,
        } => {
            let Some(declaration) = constructor
                .index()
                .and_then(|index| program.constructors.get(index))
            else {
                return Err(ValidationError::MissingConstructor {
                    function: function.id,
                    block: block.id,
                    constructor: *constructor,
                });
            };
            if fields.len() != declaration.fields.len() {
                return Err(ValidationError::ConstructorArity {
                    function: function.id,
                    block: block.id,
                    constructor: *constructor,
                    expected: declaration.fields.len(),
                    actual: fields.len(),
                });
            }
            for (argument, (value, expected)) in fields.iter().zip(&declaration.fields).enumerate()
            {
                let actual = value_type(function, block, value_types, *value)?;
                if actual != *expected {
                    return Err(ValidationError::ConstructorArgumentType {
                        function: function.id,
                        block: block.id,
                        constructor: *constructor,
                        argument,
                        expected: *expected,
                        actual,
                    });
                }
            }
            Ok(ValueType::Constructor)
        }
        Operation::Project { projection, value } => {
            let Some(declaration) = projection
                .index()
                .and_then(|index| program.projections.get(index))
            else {
                return Err(ValidationError::MissingProjection {
                    function: function.id,
                    block: block.id,
                    projection: *projection,
                });
            };
            let actual = value_type(function, block, value_types, *value)?;
            if actual != ValueType::Constructor {
                return Err(ValidationError::ProjectionOperandType {
                    function: function.id,
                    block: block.id,
                    projection: *projection,
                    actual,
                });
            }
            let constructor = declaration
                .constructor
                .index()
                .and_then(|index| program.constructors.get(index))
                .ok_or(ValidationError::ProjectionMissingConstructor {
                    projection: declaration.id,
                    constructor: declaration.constructor,
                })?;
            constructor
                .fields
                .get(usize::from(declaration.field))
                .copied()
                .ok_or(ValidationError::ProjectionFieldOutOfBounds {
                    projection: declaration.id,
                    constructor: declaration.constructor,
                    field: declaration.field,
                    field_count: constructor.fields.len(),
                })
        }
        Operation::Array { items } => {
            for value in items {
                value_type(function, block, value_types, *value)?;
            }
            Ok(ValueType::Array)
        }
        Operation::Intrinsic { intrinsic, args } => {
            let Some(declaration) = intrinsic
                .index()
                .and_then(|index| program.intrinsics.get(index))
            else {
                return Err(ValidationError::MissingIntrinsic {
                    function: function.id,
                    block: block.id,
                    intrinsic: *intrinsic,
                });
            };
            if args.len() != declaration.arguments.len() {
                return Err(ValidationError::IntrinsicArity {
                    function: function.id,
                    block: block.id,
                    intrinsic: *intrinsic,
                    expected: declaration.arguments.len(),
                    actual: args.len(),
                });
            }
            for (argument, (value, expected)) in args.iter().zip(&declaration.arguments).enumerate()
            {
                let actual = value_type(function, block, value_types, *value)?;
                if actual != *expected {
                    return Err(ValidationError::IntrinsicArgumentType {
                        function: function.id,
                        block: block.id,
                        intrinsic: *intrinsic,
                        argument,
                        expected: *expected,
                        actual,
                    });
                }
            }
            Ok(declaration.result)
        }
        Operation::Call {
            function: target,
            args,
        } => {
            let Some(callee) = target
                .index()
                .and_then(|index| program.functions.get(index))
            else {
                return Err(ValidationError::MissingCallTarget {
                    function: function.id,
                    block: block.id,
                    target: *target,
                });
            };
            if args.len() != callee.parameters.len() {
                return Err(ValidationError::CallArity {
                    function: function.id,
                    block: block.id,
                    target: *target,
                    expected: callee.parameters.len(),
                    actual: args.len(),
                });
            }
            for (argument, (value, expected)) in args.iter().zip(&callee.parameters).enumerate() {
                let actual = value_type(function, block, value_types, *value)?;
                if actual != *expected {
                    return Err(ValidationError::CallArgumentType {
                        function: function.id,
                        block: block.id,
                        target: *target,
                        argument,
                        expected: *expected,
                        actual,
                    });
                }
            }
            Ok(callee.result)
        }
        Operation::Closure {
            closure_type,
            function: target,
            captures,
            capture_ownership,
        } => {
            let signature = closure_type
                .index()
                .and_then(|index| program.closure_types.get(index))
                .ok_or(ValidationError::MissingClosureType {
                    closure_type: *closure_type,
                })?;
            let callee = target
                .index()
                .and_then(|index| program.functions.get(index))
                .ok_or(ValidationError::MissingClosureTarget {
                    function: function.id,
                    block: block.id,
                    target: *target,
                })?;
            if callee.parameters.len() == usize::from(u16::MAX) {
                return Err(ValidationError::ClosureTargetArityOverflow {
                    function: function.id,
                    block: block.id,
                    target: *target,
                    target_parameters: callee.parameters.len(),
                });
            }
            let expected_parameters = captures.len().saturating_add(signature.parameters.len());
            if expected_parameters != callee.parameters.len() {
                return Err(ValidationError::ClosureTargetShape {
                    function: function.id,
                    block: block.id,
                    target: *target,
                    captures: captures.len(),
                    parameters: signature.parameters.len(),
                    target_parameters: callee.parameters.len(),
                });
            }
            if captures.len() != capture_ownership.len() {
                return Err(ValidationError::ClosureOwnershipArity {
                    function: function.id,
                    block: block.id,
                    target: *target,
                    captures: captures.len(),
                    ownership: capture_ownership.len(),
                });
            }
            if let Some((capture, (actual, expected))) = capture_ownership
                .iter()
                .copied()
                .zip(callee.parameter_ownership[..captures.len()].iter().copied())
                .enumerate()
                .find(|(_, (actual, expected))| actual != expected)
            {
                return Err(ValidationError::ClosureOwnershipContract {
                    function: function.id,
                    block: block.id,
                    target: *target,
                    capture,
                    expected,
                    actual,
                });
            }
            if let Some(capture) = capture_ownership
                .iter()
                .position(|disposition| *disposition == flbc::ArgumentOwnership::Unique)
            {
                return Err(ValidationError::ClosureUniqueCapture {
                    function: function.id,
                    block: block.id,
                    target: *target,
                    capture,
                });
            }
            for (capture, (value, expected)) in captures.iter().zip(&callee.parameters).enumerate()
            {
                let actual = value_type(function, block, value_types, *value)?;
                if actual != *expected {
                    return Err(ValidationError::ClosureCaptureType {
                        function: function.id,
                        block: block.id,
                        target: *target,
                        capture,
                        expected: *expected,
                        actual,
                    });
                }
            }
            for (parameter, (expected, actual)) in signature
                .parameters
                .iter()
                .zip(&callee.parameters[captures.len()..])
                .enumerate()
            {
                if expected != actual {
                    return Err(ValidationError::ClosureParameterType {
                        function: function.id,
                        block: block.id,
                        target: *target,
                        parameter,
                        expected: *expected,
                        actual: *actual,
                    });
                }
            }
            for (parameter, (expected, actual)) in signature
                .parameter_ownership
                .iter()
                .zip(&callee.parameter_ownership[captures.len()..])
                .enumerate()
            {
                if expected != actual {
                    return Err(ValidationError::ClosureParameterOwnership {
                        function: function.id,
                        block: block.id,
                        target: *target,
                        parameter,
                        expected: *expected,
                        actual: *actual,
                    });
                }
            }
            if signature.result != callee.result {
                return Err(ValidationError::ClosureResultType {
                    function: function.id,
                    block: block.id,
                    target: *target,
                    expected: signature.result,
                    actual: callee.result,
                });
            }
            if signature.result_ownership != callee.result_ownership {
                return Err(ValidationError::ClosureResultOwnership {
                    function: function.id,
                    block: block.id,
                    target: *target,
                    expected: signature.result_ownership,
                    actual: callee.result_ownership,
                });
            }
            Ok(ValueType::Closure(*closure_type))
        }
        Operation::Apply {
            closure,
            args,
            argument_ownership,
            result_ownership,
        } => {
            let actual = value_type(function, block, value_types, *closure)?;
            let ValueType::Closure(closure_type) = actual else {
                return Err(ValidationError::ApplyOperandType {
                    function: function.id,
                    block: block.id,
                    actual,
                });
            };
            if args.len() != argument_ownership.len() {
                return Err(ValidationError::ApplyOwnershipArity {
                    function: function.id,
                    block: block.id,
                    closure_type,
                    arguments: args.len(),
                    ownership: argument_ownership.len(),
                });
            }
            match infer_application_type(
                &program.closure_types,
                closure_type,
                args.len(),
                |argument, _expected, expected_ownership| {
                    let actual_ownership = argument_ownership[argument];
                    if actual_ownership != expected_ownership {
                        return Err(ValidationError::ApplyOwnershipContract {
                            function: function.id,
                            block: block.id,
                            closure_type,
                            argument,
                            expected: expected_ownership,
                            actual: actual_ownership,
                        });
                    }
                    value_type(function, block, value_types, args[argument])
                },
            ) {
                Ok(result) => {
                    if result.ownership != *result_ownership {
                        return Err(ValidationError::ApplyResultOwnershipContract {
                            function: function.id,
                            block: block.id,
                            closure_type,
                            expected: result.ownership,
                            actual: *result_ownership,
                        });
                    }
                    Ok(result.ty)
                }
                Err(ApplicationInferenceError::Argument(error)) => Err(error),
                Err(ApplicationInferenceError::Type(ApplicationTypeError::EmptyArguments {
                    closure_type,
                })) => Err(ValidationError::EmptyApply {
                    function: function.id,
                    block: block.id,
                    closure_type,
                }),
                Err(ApplicationInferenceError::Type(
                    ApplicationTypeError::MissingClosureType { closure_type },
                )) => Err(ValidationError::MissingClosureType { closure_type }),
                Err(ApplicationInferenceError::Type(
                    ApplicationTypeError::PartialClosureTypeMissing {
                        closure_type,
                        consumed,
                    },
                )) => Err(ValidationError::ApplyPartialClosureTypeMissing {
                    function: function.id,
                    block: block.id,
                    closure_type,
                    consumed,
                }),
                Err(ApplicationInferenceError::Type(ApplicationTypeError::ArgumentType {
                    closure_type,
                    argument,
                    expected,
                    actual,
                })) => Err(ValidationError::ApplyArgumentType {
                    function: function.id,
                    block: block.id,
                    closure_type,
                    argument,
                    expected,
                    actual,
                }),
                Err(ApplicationInferenceError::Type(ApplicationTypeError::RemainderType {
                    closure_type,
                    argument,
                    actual,
                })) => Err(ValidationError::ApplyRemainderType {
                    function: function.id,
                    block: block.id,
                    closure_type,
                    argument,
                    actual,
                }),
            }
        }
    }
}

fn validate_terminator_shape(
    function: &Function,
    block: &Block,
    value_types: &[ValueType],
) -> Result<(), ValidationError> {
    match block.terminator {
        Terminator::Jump { .. } => Ok(()),
        Terminator::BranchZero { condition, .. } => {
            let actual = value_type(function, block, value_types, condition)?;
            if !matches!(actual, ValueType::Nat | ValueType::Bool) {
                return Err(ValidationError::BranchConditionType {
                    function: function.id,
                    block: block.id,
                    actual,
                });
            }
            Ok(())
        }
        Terminator::Return { value } => {
            let actual = value_type(function, block, value_types, value)?;
            if actual != function.result {
                return Err(ValidationError::ReturnType {
                    function: function.id,
                    block: block.id,
                    expected: function.result,
                    actual,
                });
            }
            Ok(())
        }
        Terminator::Panic { message } => {
            let actual = value_type(function, block, value_types, message)?;
            if actual != ValueType::String {
                return Err(ValidationError::PanicMessageType {
                    function: function.id,
                    block: block.id,
                    actual,
                });
            }
            Ok(())
        }
    }
}

fn validate_definite_initialization(
    function: &Function,
    value_count: usize,
) -> Result<(), ValidationError> {
    let mut incoming = Vec::new();
    incoming
        .try_reserve_exact(function.blocks.len())
        .map_err(|_| ValidationError::AllocationFailure {
            resource: ValidationResource::Blocks,
            requested: function.blocks.len(),
        })?;
    incoming.resize_with(function.blocks.len(), || None::<Vec<bool>>);

    let mut entry = Vec::new();
    entry
        .try_reserve_exact(value_count)
        .map_err(|_| ValidationError::AllocationFailure {
            resource: ValidationResource::Values,
            requested: value_count,
        })?;
    entry.resize(value_count, false);
    entry[..function.parameters.len()].fill(true);
    incoming[0] = Some(entry);

    let mut queue = VecDeque::new();
    queue
        .try_reserve(function.blocks.len())
        .map_err(|_| ValidationError::AllocationFailure {
            resource: ValidationResource::Blocks,
            requested: function.blocks.len(),
        })?;
    queue.push_back(0usize);

    while let Some(block_index) = queue.pop_front() {
        let block = &function.blocks[block_index];
        let mut state = clone_bits(
            incoming[block_index]
                .as_ref()
                .expect("queue contains reached blocks"),
        )?;
        for binding in &block.bindings {
            for value in binding.operation.reads() {
                require_initialized(function, block, &state, value)?;
            }
            state[binding.id.index().expect("canonical value id")] = true;
        }
        for value in block.terminator.reads() {
            require_initialized(function, block, &state, *value)?;
        }
        for target in block.terminator.successors().into_iter().flatten() {
            let target_index = target.index().expect("validated block target");
            let changed = match &mut incoming[target_index] {
                None => {
                    incoming[target_index] = Some(clone_bits(&state)?);
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
                queue.push_back(target_index);
            }
        }
    }

    if let Some((index, _)) = incoming
        .iter()
        .enumerate()
        .find(|(_, state)| state.is_none())
    {
        return Err(ValidationError::UnreachableBlock {
            function: function.id,
            block: BlockId::new(u32::try_from(index).expect("canonical block id")),
        });
    }
    Ok(())
}

fn clone_bits(bits: &[bool]) -> Result<Vec<bool>, ValidationError> {
    let mut clone = Vec::new();
    clone
        .try_reserve_exact(bits.len())
        .map_err(|_| ValidationError::AllocationFailure {
            resource: ValidationResource::Values,
            requested: bits.len(),
        })?;
    clone.extend_from_slice(bits);
    Ok(clone)
}

fn require_initialized(
    function: &Function,
    block: &Block,
    state: &[bool],
    value: ValueId,
) -> Result<(), ValidationError> {
    let Some(index) = value.index().filter(|index| *index < state.len()) else {
        return Err(ValidationError::UnknownValue {
            function: function.id,
            block: block.id,
            value,
        });
    };
    if !state[index] {
        return Err(ValidationError::ReadBeforeDefinition {
            function: function.id,
            block: block.id,
            value,
        });
    }
    Ok(())
}

fn value_type(
    function: &Function,
    block: &Block,
    value_types: &[ValueType],
    value: ValueId,
) -> Result<ValueType, ValidationError> {
    value
        .index()
        .and_then(|index| value_types.get(index).copied())
        .ok_or(ValidationError::UnknownValue {
            function: function.id,
            block: block.id,
            value,
        })
}

/// Whether a row id has the canonical bounded `extern:<name>` envelope.
///
/// This checks only FIR syntax. Binding the id to the generated extern contract
/// remains a source-ingress obligation.
pub fn valid_extern_row(row: &str) -> bool {
    row.len() <= 4_096
        && row.strip_prefix("extern:").is_some_and(|name| {
            !name.is_empty()
                && !name
                    .chars()
                    .any(|character| character.is_control() || character.is_whitespace())
        })
}

fn charge(
    resource: ValidationResource,
    observed: usize,
    limit: usize,
) -> Result<(), ValidationError> {
    if observed > limit {
        return Err(ValidationError::ResourceLimit {
            resource,
            limit,
            observed,
        });
    }
    Ok(())
}

fn checked_total(
    resource: ValidationResource,
    current: usize,
    added: usize,
    limit: usize,
) -> Result<usize, ValidationError> {
    let observed = current.saturating_add(added);
    charge(resource, observed, limit)?;
    Ok(observed)
}

/// Exact failure from mandatory validated-FIR to validated-FLBC lowering.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LoweringError {
    AllocationFailure {
        table: &'static str,
        requested: usize,
    },
    WidthOverflow {
        field: &'static str,
        observed: usize,
    },
    InternalInvariant {
        reason: &'static str,
    },
    FlbcValidation(flbc::ValidationError),
    OwnershipInsertion(flbc::OwnershipError),
}

impl fmt::Display for LoweringError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AllocationFailure { table, requested } => {
                write!(
                    formatter,
                    "FIR lowering could not reserve {requested} {table}"
                )
            }
            Self::WidthOverflow { field, observed } => {
                write!(
                    formatter,
                    "FIR lowering {field} width overflow at {observed}"
                )
            }
            Self::InternalInvariant { reason } => {
                write!(
                    formatter,
                    "validated FIR invariant failed during lowering: {reason}"
                )
            }
            Self::FlbcValidation(error) => {
                write!(
                    formatter,
                    "lowered FLBC failed independent validation: {error}"
                )
            }
            Self::OwnershipInsertion(error) => {
                write!(
                    formatter,
                    "lowered FLBC failed bounded ownership insertion: {error}"
                )
            }
        }
    }
}

impl std::error::Error for LoweringError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::FlbcValidation(error) => Some(error),
            Self::OwnershipInsertion(error) => Some(error),
            _ => None,
        }
    }
}

impl LoweringError {
    /// Whether this refusal is a budget or allocation failure, including
    /// ownership-insertion resource refusals.
    pub fn is_resource_exhaustion(&self) -> bool {
        match self {
            Self::AllocationFailure { .. } => true,
            Self::OwnershipInsertion(error) => error.is_resource_exhaustion(),
            _ => false,
        }
    }

    /// Whether this refusal is an internal accounting fault, never a source
    /// verdict.
    pub fn is_internal_fault(&self) -> bool {
        matches!(self, Self::InternalInvariant { .. })
    }
}

/// Deterministically lower validated target-neutral FIR to independently
/// validated FLBC. Failure publishes no FLBC wrapper and never falls back
/// across stages.
pub fn lower_to_flbc(program: &ValidatedProgram) -> Result<flbc::ValidatedProgram, LoweringError> {
    let mut functions = Vec::new();
    functions
        .try_reserve_exact(program.program.functions.len())
        .map_err(|_| LoweringError::AllocationFailure {
            table: "functions",
            requested: program.program.functions.len(),
        })?;
    for function in &program.program.functions {
        functions.push(lower_function(&program.program, function)?);
    }
    let entry = flbc::FunctionId::new(program.program.entry.get());
    flbc::validate(flbc::Program::new(entry, functions)).map_err(LoweringError::FlbcValidation)
}

/// Lower validated FIR and then insert independently validated eager drops for
/// every straight-line or CFG SSA function admitted by the bounded ownership
/// pass, including graphs with backedges.
pub fn lower_to_flbc_with_ownership(
    program: &ValidatedProgram,
    limits: flbc::OwnershipLimits,
) -> Result<flbc::OwnershipProgram, LoweringError> {
    let lowered = lower_to_flbc(program)?;
    flbc::insert_ownership(&lowered, limits).map_err(LoweringError::OwnershipInsertion)
}

fn lower_function(program: &Program, function: &Function) -> Result<flbc::Function, LoweringError> {
    let binding_count = function
        .blocks
        .iter()
        .try_fold(0usize, |total, block| {
            total.checked_add(block.bindings.len())
        })
        .ok_or(LoweringError::WidthOverflow {
            field: "binding count",
            observed: usize::MAX,
        })?;
    let value_count = function.parameters.len().checked_add(binding_count).ok_or(
        LoweringError::WidthOverflow {
            field: "register count",
            observed: usize::MAX,
        },
    )?;
    let lowered_binding_count = function
        .blocks
        .iter()
        .try_fold(0usize, |total, block| {
            block.bindings.iter().try_fold(total, |total, binding| {
                total.checked_add(lowered_binding_width(binding))
            })
        })
        .ok_or(LoweringError::WidthOverflow {
            field: "instruction count",
            observed: usize::MAX,
        })?;
    let instruction_count = lowered_binding_count
        .checked_add(function.blocks.len())
        .ok_or(LoweringError::WidthOverflow {
            field: "instruction count",
            observed: usize::MAX,
        })?;
    let arity =
        u16::try_from(function.parameters.len()).map_err(|_| LoweringError::WidthOverflow {
            field: "arity",
            observed: function.parameters.len(),
        })?;
    let register_count = u16::try_from(value_count).map_err(|_| LoweringError::WidthOverflow {
        field: "register count",
        observed: value_count,
    })?;

    let mut block_starts = Vec::new();
    block_starts
        .try_reserve_exact(function.blocks.len())
        .map_err(|_| LoweringError::AllocationFailure {
            table: "block starts",
            requested: function.blocks.len(),
        })?;
    let mut offset = 0usize;
    for block in &function.blocks {
        block_starts.push(
            u32::try_from(offset).map_err(|_| LoweringError::WidthOverflow {
                field: "program counter",
                observed: offset,
            })?,
        );
        for binding in &block.bindings {
            offset = offset.checked_add(lowered_binding_width(binding)).ok_or(
                LoweringError::WidthOverflow {
                    field: "program counter",
                    observed: usize::MAX,
                },
            )?;
        }
        offset = offset.checked_add(1).ok_or(LoweringError::WidthOverflow {
            field: "program counter",
            observed: usize::MAX,
        })?;
    }

    let mut code = Vec::new();
    code.try_reserve_exact(instruction_count)
        .map_err(|_| LoweringError::AllocationFailure {
            table: "instructions",
            requested: instruction_count,
        })?;
    for block in &function.blocks {
        for binding in &block.bindings {
            lower_binding(program, binding, &mut code)?;
        }
        code.push(lower_terminator(&block.terminator, &block_starts)?);
    }

    Ok(flbc::Function {
        id: flbc::FunctionId::new(function.id.get()),
        arity,
        parameter_ownership: clone_argument_ownership(&function.parameter_ownership)?,
        result_ownership: function.result_ownership,
        register_count,
        code,
    })
}

const fn lowered_binding_width(binding: &Binding) -> usize {
    match binding.operation {
        Operation::CheckSystem { .. } | Operation::CheckSystemValue { .. } => 2,
        _ => 1,
    }
}

fn lower_binding(
    program: &Program,
    binding: &Binding,
    code: &mut Vec<flbc::Instruction>,
) -> Result<(), LoweringError> {
    if let Operation::CheckSystem { module_name } = &binding.operation {
        let module_name = clone_string(module_name, "checkSystem module name bytes")?;
        let dst = lower_register(binding.id)?;
        code.push(flbc::Instruction::CheckSystem { module_name });
        code.push(flbc::Instruction::Nat { dst, value: 0 });
        return Ok(());
    }
    if let Operation::CheckSystemValue { module_name } = &binding.operation {
        let dst = lower_register(binding.id)?;
        code.push(flbc::Instruction::CheckSystemValue {
            module_name: lower_register(*module_name)?,
        });
        code.push(flbc::Instruction::Nat { dst, value: 0 });
        return Ok(());
    }
    code.push(lower_single_binding(program, binding)?);
    Ok(())
}

fn lower_single_binding(
    program: &Program,
    binding: &Binding,
) -> Result<flbc::Instruction, LoweringError> {
    let dst = lower_register(binding.id)?;
    match &binding.operation {
        Operation::Unit => Ok(flbc::Instruction::Nat { dst, value: 0 }),
        Operation::Bool(value) => Ok(flbc::Instruction::Nat {
            dst,
            value: u64::from(*value),
        }),
        Operation::Nat(value) => Ok(flbc::Instruction::Nat { dst, value: *value }),
        Operation::String(value) => Ok(flbc::Instruction::String {
            dst,
            value: clone_string(value, "string bytes")?,
        }),
        Operation::Alias(src) => Ok(flbc::Instruction::Copy {
            dst,
            src: lower_register(*src)?,
        }),
        Operation::Box(src) | Operation::Unbox { value: src, .. } => Ok(flbc::Instruction::Copy {
            dst,
            src: lower_register(*src)?,
        }),
        Operation::Ctor {
            constructor,
            fields,
        } => {
            let declaration = constructor
                .index()
                .and_then(|index| program.constructors.get(index))
                .ok_or(LoweringError::InternalInvariant {
                    reason: "validated constructor id disappeared",
                })?;
            Ok(flbc::Instruction::Ctor {
                dst,
                tag: declaration.tag,
                fields: lower_registers(fields)?,
                scalar_bytes: clone_bytes(
                    &declaration.static_scalar_bytes,
                    "constructor scalar bytes",
                )?,
            })
        }
        Operation::Project { projection, value } => {
            let projection = projection
                .index()
                .and_then(|index| program.projections.get(index))
                .ok_or(LoweringError::InternalInvariant {
                    reason: "validated projection id disappeared",
                })?;
            let constructor = projection
                .constructor
                .index()
                .and_then(|index| program.constructors.get(index))
                .ok_or(LoweringError::InternalInvariant {
                    reason: "validated projection constructor disappeared",
                })?;
            let expected_fields = u16::try_from(constructor.fields.len()).map_err(|_| {
                LoweringError::WidthOverflow {
                    field: "projection constructor field count",
                    observed: constructor.fields.len(),
                }
            })?;
            Ok(flbc::Instruction::CtorField {
                dst,
                src: lower_register(*value)?,
                expected_tag: constructor.tag,
                expected_fields,
                field: projection.field,
            })
        }
        Operation::Array { items } => Ok(flbc::Instruction::Array {
            dst,
            items: lower_registers(items)?,
        }),
        Operation::Intrinsic { intrinsic, args } => {
            let declaration = intrinsic
                .index()
                .and_then(|index| program.intrinsics.get(index))
                .ok_or(LoweringError::InternalInvariant {
                    reason: "validated intrinsic id disappeared",
                })?;
            Ok(flbc::Instruction::Intrinsic {
                dst,
                row: clone_string(&declaration.row, "intrinsic row bytes")?,
                args: lower_registers(args)?,
                argument_ownership: clone_argument_ownership(&declaration.argument_ownership)?,
                result_ownership: declaration.result_ownership,
            })
        }
        Operation::CheckSystem { .. } => Err(LoweringError::InternalInvariant {
            reason: "checkSystem binding bypassed its two-instruction lowering",
        }),
        Operation::CheckSystemValue { .. } => Err(LoweringError::InternalInvariant {
            reason: "dynamic checkSystem binding bypassed its two-instruction lowering",
        }),
        Operation::Call { function, args } => {
            let declaration = function
                .index()
                .and_then(|index| program.functions.get(index))
                .ok_or(LoweringError::InternalInvariant {
                    reason: "validated call target disappeared",
                })?;
            Ok(flbc::Instruction::Call {
                dst,
                function: flbc::FunctionId::new(function.get()),
                args: lower_registers(args)?,
                argument_ownership: clone_argument_ownership(&declaration.parameter_ownership)?,
                result_ownership: declaration.result_ownership,
            })
        }
        Operation::Closure {
            function,
            captures,
            capture_ownership,
            ..
        } => Ok(flbc::Instruction::Closure {
            dst,
            function: flbc::FunctionId::new(function.get()),
            captures: lower_registers(captures)?,
            capture_ownership: clone_argument_ownership(capture_ownership)?,
        }),
        Operation::Apply {
            closure,
            args,
            argument_ownership,
            result_ownership,
        } => Ok(flbc::Instruction::Apply {
            dst,
            closure: lower_register(*closure)?,
            args: lower_registers(args)?,
            argument_ownership: clone_argument_ownership(argument_ownership)?,
            result_ownership: *result_ownership,
        }),
    }
}

fn lower_terminator(
    terminator: &Terminator,
    block_starts: &[u32],
) -> Result<flbc::Instruction, LoweringError> {
    match *terminator {
        Terminator::Jump { target } => Ok(flbc::Instruction::Jump {
            target: lower_target(target, block_starts)?,
        }),
        Terminator::BranchZero {
            condition,
            zero,
            nonzero,
        } => Ok(flbc::Instruction::JumpIfZero {
            cond: lower_register(condition)?,
            zero: lower_target(zero, block_starts)?,
            nonzero: lower_target(nonzero, block_starts)?,
        }),
        Terminator::Return { value } => Ok(flbc::Instruction::Return {
            src: lower_register(value)?,
        }),
        Terminator::Panic { message } => Ok(flbc::Instruction::Panic {
            message: lower_register(message)?,
        }),
    }
}

fn lower_target(target: BlockId, starts: &[u32]) -> Result<flbc::Pc, LoweringError> {
    target
        .index()
        .and_then(|index| starts.get(index).copied())
        .map(flbc::Pc::new)
        .ok_or(LoweringError::InternalInvariant {
            reason: "validated block target disappeared",
        })
}

fn lower_register(value: ValueId) -> Result<flbc::Register, LoweringError> {
    u16::try_from(value.get())
        .map(flbc::Register::new)
        .map_err(|_| LoweringError::WidthOverflow {
            field: "register id",
            observed: value.index().unwrap_or(usize::MAX),
        })
}

fn lower_registers(values: &[ValueId]) -> Result<Vec<flbc::Register>, LoweringError> {
    let mut registers = Vec::new();
    registers
        .try_reserve_exact(values.len())
        .map_err(|_| LoweringError::AllocationFailure {
            table: "operand registers",
            requested: values.len(),
        })?;
    for value in values {
        registers.push(lower_register(*value)?);
    }
    Ok(registers)
}

fn clone_string(value: &str, table: &'static str) -> Result<String, LoweringError> {
    let mut clone = String::new();
    clone
        .try_reserve_exact(value.len())
        .map_err(|_| LoweringError::AllocationFailure {
            table,
            requested: value.len(),
        })?;
    clone.push_str(value);
    Ok(clone)
}

fn clone_bytes(value: &[u8], table: &'static str) -> Result<Vec<u8>, LoweringError> {
    let mut clone = Vec::new();
    clone
        .try_reserve_exact(value.len())
        .map_err(|_| LoweringError::AllocationFailure {
            table,
            requested: value.len(),
        })?;
    clone.extend_from_slice(value);
    Ok(clone)
}

fn clone_argument_ownership(
    value: &[flbc::ArgumentOwnership],
) -> Result<Vec<flbc::ArgumentOwnership>, LoweringError> {
    let mut clone = Vec::new();
    clone
        .try_reserve_exact(value.len())
        .map_err(|_| LoweringError::AllocationFailure {
            table: "intrinsic argument ownership",
            requested: value.len(),
        })?;
    clone.extend_from_slice(value);
    Ok(clone)
}

fn write_types(output: &mut impl fmt::Write, values: &[ValueType]) -> fmt::Result {
    for (index, value) in values.iter().enumerate() {
        if index != 0 {
            output.write_char(',')?;
        }
        write_type(output, *value)?;
    }
    Ok(())
}

fn write_type(output: &mut impl fmt::Write, value: ValueType) -> fmt::Result {
    match value {
        ValueType::Closure(closure_type) => write!(output, "closure:s{}", closure_type.get()),
        _ => output.write_str(value.token()),
    }
}

fn write_values(output: &mut impl fmt::Write, values: &[ValueId]) -> fmt::Result {
    output.write_char('[')?;
    for (index, value) in values.iter().enumerate() {
        if index != 0 {
            output.write_char(',')?;
        }
        write!(output, "v{}", value.get())?;
    }
    output.write_char(']')
}

fn write_argument_ownership(
    output: &mut impl fmt::Write,
    ownership: &[flbc::ArgumentOwnership],
) -> fmt::Result {
    output.write_char('[')?;
    for (index, disposition) in ownership.iter().enumerate() {
        if index != 0 {
            output.write_char(',')?;
        }
        output.write_str(disposition.token())?;
    }
    output.write_char(']')
}

fn write_hex_bytes(output: &mut impl fmt::Write, bytes: &[u8]) -> fmt::Result {
    write!(output, "{}:", bytes.len())?;
    for byte in bytes {
        write!(output, "{byte:02x}")?;
    }
    Ok(())
}

fn write_operation(output: &mut impl fmt::Write, operation: &Operation) -> fmt::Result {
    match operation {
        Operation::Unit => output.write_str("unit"),
        Operation::Bool(value) => write!(output, "bool {}", u8::from(*value)),
        Operation::Nat(value) => write!(output, "nat {value}"),
        Operation::String(value) => {
            output.write_str("string ")?;
            write_hex_bytes(output, value.as_bytes())
        }
        Operation::Alias(value) => write!(output, "alias v{}", value.get()),
        Operation::Box(value) => write!(output, "box v{}", value.get()),
        Operation::Unbox { value, ty } => {
            output.write_str("unbox ")?;
            write_type(output, *ty)?;
            write!(output, " v{}", value.get())
        }
        Operation::Ctor {
            constructor,
            fields,
        } => {
            write!(output, "ctor c{} fields=", constructor.get())?;
            write_values(output, fields)
        }
        Operation::Project { projection, value } => {
            write!(output, "project p{} v{}", projection.get(), value.get())
        }
        Operation::Array { items } => {
            output.write_str("array ")?;
            write_values(output, items)
        }
        Operation::Intrinsic { intrinsic, args } => {
            write!(output, "intrinsic i{} ", intrinsic.get())?;
            write_values(output, args)
        }
        Operation::CheckSystem { module_name } => {
            output.write_str("check_system ")?;
            write_hex_bytes(output, module_name.as_bytes())
        }
        Operation::CheckSystemValue { module_name } => {
            write!(output, "check_system_value v{}", module_name.get())
        }
        Operation::Call { function, args } => {
            write!(output, "call f{} ", function.get())?;
            write_values(output, args)
        }
        Operation::Closure {
            closure_type,
            function,
            captures,
            capture_ownership,
        } => {
            write!(
                output,
                "closure s{} f{} captures=",
                closure_type.get(),
                function.get()
            )?;
            write_values(output, captures)?;
            output.write_str(" ownership=")?;
            write_argument_ownership(output, capture_ownership)
        }
        Operation::Apply {
            closure,
            args,
            argument_ownership,
            result_ownership,
        } => {
            write!(output, "apply v{} args=", closure.get())?;
            write_values(output, args)?;
            output.write_str(" ownership=")?;
            write_argument_ownership(output, argument_ownership)?;
            write!(output, " result_ownership={}", result_ownership.token())
        }
    }
}

fn write_terminator(output: &mut impl fmt::Write, terminator: &Terminator) -> fmt::Result {
    match terminator {
        Terminator::Jump { target } => write!(output, "jump b{}", target.get()),
        Terminator::BranchZero {
            condition,
            zero,
            nonzero,
        } => write!(
            output,
            "branch_zero v{} zero=b{} nonzero=b{}",
            condition.get(),
            zero.get(),
            nonzero.get()
        ),
        Terminator::Return { value } => write!(output, "return v{}", value.get()),
        Terminator::Panic { message } => write!(output, "panic v{}", message.get()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::flbc::{CodecLimits, encode_canonical};

    fn f(raw: u32) -> FunctionId {
        FunctionId::new(raw)
    }

    #[test]
    fn resource_exhaustion_classifiers_do_not_promote_shape_refusals() {
        assert!(
            ValidationError::ResourceLimit {
                resource: ValidationResource::Functions,
                limit: 0,
                observed: 1,
            }
            .is_resource_exhaustion()
        );
        assert!(!ValidationError::EmptyProgram.is_resource_exhaustion());
        assert!(
            LoweringError::AllocationFailure {
                table: "functions",
                requested: 1,
            }
            .is_resource_exhaustion()
        );
        assert!(
            LoweringError::InternalInvariant {
                reason: "register file shrank",
            }
            .is_internal_fault()
        );
        assert!(
            !LoweringError::InternalInvariant {
                reason: "register file shrank",
            }
            .is_resource_exhaustion()
        );
        assert!(
            LoweringError::OwnershipInsertion(crate::flbc::OwnershipError::AllocationFailure {
                resource: crate::flbc::OwnershipResource::Functions,
                requested: 1,
            })
            .is_resource_exhaustion()
        );
    }

    fn b(raw: u32) -> BlockId {
        BlockId::new(raw)
    }

    fn v(raw: u32) -> ValueId {
        ValueId::new(raw)
    }

    fn i(raw: u32) -> IntrinsicId {
        IntrinsicId::new(raw)
    }

    fn c(raw: u32) -> ConstructorId {
        ConstructorId::new(raw)
    }

    fn p(raw: u32) -> ProjectionId {
        ProjectionId::new(raw)
    }

    fn s(raw: u32) -> ClosureTypeId {
        ClosureTypeId::new(raw)
    }

    fn sample_constructor() -> ConstructorDecl {
        ConstructorDecl {
            id: c(0),
            tag: 0,
            fields: vec![ValueType::Unit, ValueType::Bool, ValueType::String],
            static_scalar_bytes: vec![0xAB],
        }
    }

    fn sample_constructor_operation(
        program: &mut Program,
    ) -> Option<(&mut ConstructorId, &mut Vec<ValueId>)> {
        match &mut program.functions[0].blocks[0].bindings[7].operation {
            Operation::Ctor {
                constructor,
                fields,
            } => Some((constructor, fields)),
            _ => None,
        }
    }

    fn sample_projection_operation(
        program: &mut Program,
    ) -> Option<(&mut ProjectionId, &mut ValueId)> {
        match &mut program.functions[0].blocks[0].bindings[8].operation {
            Operation::Project { projection, value } => Some((projection, value)),
            _ => None,
        }
    }

    fn nat_add() -> IntrinsicDecl {
        IntrinsicDecl {
            id: i(0),
            row: "extern:Nat.add".to_string(),
            arguments: vec![ValueType::Nat, ValueType::Nat],
            argument_ownership: vec![
                flbc::ArgumentOwnership::Borrowed,
                flbc::ArgumentOwnership::Borrowed,
            ],
            result: ValueType::Nat,
            result_ownership: flbc::ResultOwnership::Owned,
            effect: EffectClass::Pure,
        }
    }

    fn branch_program() -> Program {
        Program::new(
            f(0),
            Vec::new(),
            Vec::new(),
            vec![nat_add()],
            vec![Function {
                id: f(0),
                parameters: Vec::new(),
                parameter_ownership: Vec::new(),
                result: ValueType::Nat,
                result_ownership: flbc::CallableResultOwnership::Scalar,
                blocks: vec![
                    Block {
                        id: b(0),
                        bindings: vec![
                            Binding {
                                id: v(0),
                                ty: ValueType::Nat,
                                operation: Operation::Nat(1),
                            },
                            Binding {
                                id: v(1),
                                ty: ValueType::Nat,
                                operation: Operation::Nat(2),
                            },
                            Binding {
                                id: v(2),
                                ty: ValueType::Nat,
                                operation: Operation::Intrinsic {
                                    intrinsic: i(0),
                                    args: vec![v(0), v(1)],
                                },
                            },
                        ],
                        terminator: Terminator::BranchZero {
                            condition: v(2),
                            zero: b(1),
                            nonzero: b(2),
                        },
                    },
                    Block {
                        id: b(1),
                        bindings: vec![Binding {
                            id: v(3),
                            ty: ValueType::Nat,
                            operation: Operation::Nat(10),
                        }],
                        terminator: Terminator::Return { value: v(3) },
                    },
                    Block {
                        id: b(2),
                        bindings: vec![Binding {
                            id: v(4),
                            ty: ValueType::Nat,
                            operation: Operation::Nat(20),
                        }],
                        terminator: Terminator::Return { value: v(4) },
                    },
                ],
            }],
        )
    }

    fn boxing_program() -> Program {
        Program::new(
            f(0),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            vec![Function {
                id: f(0),
                parameters: Vec::new(),
                parameter_ownership: Vec::new(),
                result: ValueType::Nat,
                result_ownership: flbc::CallableResultOwnership::Scalar,
                blocks: vec![Block {
                    id: b(0),
                    bindings: vec![
                        Binding {
                            id: v(0),
                            ty: ValueType::Nat,
                            operation: Operation::Nat(41),
                        },
                        Binding {
                            id: v(1),
                            ty: ValueType::Abi,
                            operation: Operation::Box(v(0)),
                        },
                        Binding {
                            id: v(2),
                            ty: ValueType::Nat,
                            operation: Operation::Unbox {
                                value: v(1),
                                ty: ValueType::Nat,
                            },
                        },
                    ],
                    terminator: Terminator::Return { value: v(2) },
                }],
            }],
        )
    }

    fn all_operations_program() -> Program {
        Program::new_with_closures(
            f(0),
            vec![sample_constructor()],
            vec![ProjectionDecl {
                id: p(0),
                constructor: c(0),
                field: 2,
            }],
            vec![ClosureTypeDecl {
                id: s(0),
                parameters: vec![ValueType::Nat],
                parameter_ownership: vec![flbc::ArgumentOwnership::Borrowed],
                result: ValueType::Nat,
                result_ownership: flbc::CallableResultOwnership::Scalar,
            }],
            vec![nat_add()],
            vec![
                Function {
                    id: f(0),
                    parameters: Vec::new(),
                    parameter_ownership: Vec::new(),
                    result: ValueType::Nat,
                    result_ownership: flbc::CallableResultOwnership::Scalar,
                    blocks: vec![Block {
                        id: b(0),
                        bindings: vec![
                            Binding {
                                id: v(0),
                                ty: ValueType::Nat,
                                operation: Operation::Nat(1),
                            },
                            Binding {
                                id: v(1),
                                ty: ValueType::Nat,
                                operation: Operation::Nat(2),
                            },
                            Binding {
                                id: v(2),
                                ty: ValueType::Nat,
                                operation: Operation::Intrinsic {
                                    intrinsic: i(0),
                                    args: vec![v(0), v(1)],
                                },
                            },
                            Binding {
                                id: v(3),
                                ty: ValueType::Nat,
                                operation: Operation::Alias(v(2)),
                            },
                            Binding {
                                id: v(4),
                                ty: ValueType::Unit,
                                operation: Operation::Unit,
                            },
                            Binding {
                                id: v(5),
                                ty: ValueType::Bool,
                                operation: Operation::Bool(true),
                            },
                            Binding {
                                id: v(6),
                                ty: ValueType::String,
                                operation: Operation::String("fir".to_string()),
                            },
                            Binding {
                                id: v(7),
                                ty: ValueType::Constructor,
                                operation: Operation::Ctor {
                                    constructor: c(0),
                                    fields: vec![v(4), v(5), v(6)],
                                },
                            },
                            Binding {
                                id: v(8),
                                ty: ValueType::String,
                                operation: Operation::Project {
                                    projection: p(0),
                                    value: v(7),
                                },
                            },
                            Binding {
                                id: v(9),
                                ty: ValueType::Array,
                                operation: Operation::Array {
                                    items: vec![v(7), v(8)],
                                },
                            },
                            Binding {
                                id: v(10),
                                ty: ValueType::Nat,
                                operation: Operation::Call {
                                    function: f(1),
                                    args: vec![v(3)],
                                },
                            },
                            Binding {
                                id: v(11),
                                ty: ValueType::Closure(s(0)),
                                operation: Operation::Closure {
                                    closure_type: s(0),
                                    function: f(2),
                                    captures: Vec::new(),
                                    capture_ownership: Vec::new(),
                                },
                            },
                            Binding {
                                id: v(12),
                                ty: ValueType::Nat,
                                operation: Operation::Apply {
                                    closure: v(11),
                                    args: vec![v(10)],
                                    argument_ownership: vec![flbc::ArgumentOwnership::Borrowed],
                                    result_ownership: flbc::CallableResultOwnership::Scalar,
                                },
                            },
                        ],
                        terminator: Terminator::Return { value: v(12) },
                    }],
                },
                Function {
                    id: f(1),
                    parameters: vec![ValueType::Nat],
                    parameter_ownership: vec![flbc::ArgumentOwnership::Borrowed],
                    result: ValueType::Nat,
                    result_ownership: flbc::CallableResultOwnership::Scalar,
                    blocks: vec![Block {
                        id: b(0),
                        bindings: vec![
                            Binding {
                                id: v(1),
                                ty: ValueType::Nat,
                                operation: Operation::Nat(1),
                            },
                            Binding {
                                id: v(2),
                                ty: ValueType::Nat,
                                operation: Operation::Intrinsic {
                                    intrinsic: i(0),
                                    args: vec![v(0), v(1)],
                                },
                            },
                        ],
                        terminator: Terminator::Return { value: v(2) },
                    }],
                },
                Function {
                    id: f(2),
                    parameters: vec![ValueType::Nat],
                    parameter_ownership: vec![flbc::ArgumentOwnership::Borrowed],
                    result: ValueType::Nat,
                    result_ownership: flbc::CallableResultOwnership::Scalar,
                    blocks: vec![Block {
                        id: b(0),
                        bindings: vec![Binding {
                            id: v(1),
                            ty: ValueType::Nat,
                            operation: Operation::Alias(v(0)),
                        }],
                        terminator: Terminator::Return { value: v(1) },
                    }],
                },
            ],
        )
    }

    fn check_system_program() -> Program {
        Program::new(
            f(0),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            vec![Function {
                id: f(0),
                parameters: Vec::new(),
                parameter_ownership: Vec::new(),
                result: ValueType::Nat,
                result_ownership: flbc::CallableResultOwnership::Scalar,
                blocks: vec![
                    Block {
                        id: b(0),
                        bindings: vec![
                            Binding {
                                id: v(0),
                                ty: ValueType::Unit,
                                operation: Operation::CheckSystem {
                                    module_name: "Lake.Build".to_string(),
                                },
                            },
                            Binding {
                                id: v(1),
                                ty: ValueType::Nat,
                                operation: Operation::Nat(0),
                            },
                        ],
                        terminator: Terminator::Jump { target: b(1) },
                    },
                    Block {
                        id: b(1),
                        bindings: vec![Binding {
                            id: v(2),
                            ty: ValueType::Nat,
                            operation: Operation::Nat(7),
                        }],
                        terminator: Terminator::Return { value: v(2) },
                    },
                ],
            }],
        )
    }

    fn dynamic_check_system_program() -> Program {
        Program::new(
            f(0),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            vec![Function {
                id: f(0),
                parameters: Vec::new(),
                parameter_ownership: Vec::new(),
                result: ValueType::Unit,
                result_ownership: flbc::CallableResultOwnership::Scalar,
                blocks: vec![Block {
                    id: b(0),
                    bindings: vec![
                        Binding {
                            id: v(0),
                            ty: ValueType::String,
                            operation: Operation::String("Lake.Dynamic".to_string()),
                        },
                        Binding {
                            id: v(1),
                            ty: ValueType::Unit,
                            operation: Operation::CheckSystemValue { module_name: v(0) },
                        },
                    ],
                    terminator: Terminator::Return { value: v(1) },
                }],
            }],
        )
    }

    #[test]
    fn every_supported_operation_and_control_form_lowers_to_valid_flbc() {
        let validated = validate(all_operations_program(), ValidationLimits::default())
            .expect("the complete operation fixture is valid");
        let lowered = lower_to_flbc(&validated).expect("mandatory lowering succeeds");
        assert_eq!(lowered.functions().len(), 3);
        assert_eq!(lowered.functions()[0].code.len(), 14);
        assert_eq!(lowered.functions()[1].code.len(), 3);
        assert_eq!(lowered.functions()[2].code.len(), 2);
        assert!(matches!(
            &lowered.functions()[0].code[7],
            flbc::Instruction::Ctor {
                tag: 0,
                fields,
                scalar_bytes,
                ..
            } if fields.len() == 3 && scalar_bytes == &[0xAB]
        ));
        assert!(matches!(
            lowered.functions()[0].code[8],
            flbc::Instruction::CtorField {
                expected_tag: 0,
                expected_fields: 3,
                field: 2,
                ..
            }
        ));
        assert_eq!(
            lowered.functions()[1].parameter_ownership,
            [flbc::ArgumentOwnership::Borrowed]
        );
        assert!(matches!(
            &lowered.functions()[0].code[10],
            flbc::Instruction::Call {
                function,
                argument_ownership,
                ..
            } if *function == flbc::FunctionId::new(1)
                && argument_ownership == &[flbc::ArgumentOwnership::Borrowed]
        ));
        assert!(matches!(
            &lowered.functions()[0].code[11],
            flbc::Instruction::Closure {
                function,
                captures,
                capture_ownership,
                ..
            } if *function == flbc::FunctionId::new(2)
                && captures.is_empty()
                && capture_ownership.is_empty()
        ));
        assert!(matches!(
            &lowered.functions()[0].code[12],
            flbc::Instruction::Apply { args, .. } if args.len() == 1
        ));

        let check_system = validate(check_system_program(), ValidationLimits::default())
            .expect("typed checkSystem is valid");
        assert!(
            check_system
                .canonical_text()
                .contains("v0:unit = check_system 10:4c616b652e4275696c64\n")
        );
        let lowered_check_system =
            lower_to_flbc(&check_system).expect("checkSystem lowering succeeds");
        assert_eq!(lowered_check_system.functions()[0].code.len(), 6);
        assert!(matches!(
            &lowered_check_system.functions()[0].code[0],
            flbc::Instruction::CheckSystem { module_name } if module_name == "Lake.Build"
        ));
        assert!(matches!(
            lowered_check_system.functions()[0].code[1],
            flbc::Instruction::Nat {
                dst,
                value: 0,
            } if dst == flbc::Register::new(0)
        ));
        assert!(matches!(
            lowered_check_system.functions()[0].code[3],
            flbc::Instruction::Jump { target } if target == flbc::Pc::new(4)
        ));

        let dynamic_check_system =
            validate(dynamic_check_system_program(), ValidationLimits::default())
                .expect("a computed String module name is valid");
        assert!(
            dynamic_check_system
                .canonical_text()
                .contains("v1:unit = check_system_value v0\n")
        );
        let lowered_dynamic =
            lower_to_flbc(&dynamic_check_system).expect("dynamic checkSystem lowering succeeds");
        assert!(matches!(
            lowered_dynamic.functions()[0].code.as_slice(),
            [
                flbc::Instruction::String { dst, .. },
                flbc::Instruction::CheckSystemValue { module_name },
                flbc::Instruction::Nat { value: 0, .. },
                flbc::Instruction::Return { .. },
            ] if dst == module_name
        ));

        let mut wrong_dynamic_module_type = dynamic_check_system_program();
        wrong_dynamic_module_type.functions[0].blocks[0].bindings[0] = Binding {
            id: v(0),
            ty: ValueType::Nat,
            operation: Operation::Nat(0),
        };
        assert_eq!(
            validate(wrong_dynamic_module_type, ValidationLimits::default(),),
            Err(ValidationError::CheckSystemModuleNameType {
                function: f(0),
                block: b(0),
                actual: ValueType::Nat,
            })
        );

        let mut wrong_check_system_type = check_system_program();
        wrong_check_system_type.functions[0].blocks[0].bindings[0].ty = ValueType::String;
        assert_eq!(
            validate(wrong_check_system_type, ValidationLimits::default()),
            Err(ValidationError::BindingType {
                function: f(0),
                block: b(0),
                value: v(0),
                declared: ValueType::String,
                inferred: ValueType::Unit,
            })
        );

        let branch = validate(branch_program(), ValidationLimits::default())
            .expect("the branch fixture is valid");
        let lowered_branch = lower_to_flbc(&branch).expect("branch lowering succeeds");
        assert!(matches!(
            lowered_branch.functions()[0].code[3],
            flbc::Instruction::JumpIfZero {
                zero,
                nonzero,
                ..
            } if zero == flbc::Pc::new(4) && nonzero == flbc::Pc::new(6)
        ));

        let panicking = Program::new(
            f(0),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            vec![Function {
                id: f(0),
                parameters: Vec::new(),
                parameter_ownership: Vec::new(),
                result: ValueType::Nat,
                result_ownership: flbc::CallableResultOwnership::Scalar,
                blocks: vec![Block {
                    id: b(0),
                    bindings: vec![Binding {
                        id: v(0),
                        ty: ValueType::String,
                        operation: Operation::String("boom".to_string()),
                    }],
                    terminator: Terminator::Panic { message: v(0) },
                }],
            }],
        );
        let validated_panic =
            validate(panicking, ValidationLimits::default()).expect("typed panic is valid");
        let lowered_panic = lower_to_flbc(&validated_panic).expect("panic lowering succeeds");
        assert!(matches!(
            lowered_panic.functions()[0].code[1],
            flbc::Instruction::Panic { message } if message == flbc::Register::new(0)
        ));
    }

    #[test]
    fn intrinsic_result_ownership_is_canonical_and_lowers_exactly() {
        let mut program = branch_program();
        program.intrinsics[0].result_ownership = flbc::ResultOwnership::Borrowed;
        let validated = validate(program, ValidationLimits::default())
            .expect("closed FIR result ownership is valid");
        assert!(
            validated
                .canonical_text()
                .contains("result_ownership=borrowed effect=pure\n")
        );

        let lowered =
            lower_to_flbc(&validated).expect("FIR carries result ownership into validated FLBC");
        assert!(matches!(
            lowered.functions()[0].code[2],
            flbc::Instruction::Intrinsic {
                result_ownership: flbc::ResultOwnership::Borrowed,
                ..
            }
        ));
    }

    #[test]
    fn callable_result_ownership_is_type_checked_and_application_bound() {
        let mut wrong_function = all_operations_program();
        wrong_function.functions[0].result_ownership = flbc::CallableResultOwnership::Owned;
        assert_eq!(
            validate(wrong_function, ValidationLimits::default()),
            Err(ValidationError::FunctionResultOwnership {
                function: f(0),
                result: ValueType::Nat,
                ownership: flbc::CallableResultOwnership::Owned,
            })
        );

        let mut wrong_closure_type = all_operations_program();
        wrong_closure_type.closure_types[0].result_ownership = flbc::CallableResultOwnership::Owned;
        assert_eq!(
            validate(wrong_closure_type, ValidationLimits::default()),
            Err(ValidationError::ClosureTypeResultOwnership {
                closure_type: s(0),
                result: ValueType::Nat,
                ownership: flbc::CallableResultOwnership::Owned,
            })
        );

        let mut wrong_apply = all_operations_program();
        let Operation::Apply {
            result_ownership, ..
        } = &mut wrong_apply.functions[0].blocks[0].bindings[12].operation
        else {
            panic!("fixture retains its typed Apply");
        };
        *result_ownership = flbc::CallableResultOwnership::Owned;
        assert_eq!(
            validate(wrong_apply, ValidationLimits::default()),
            Err(ValidationError::ApplyResultOwnershipContract {
                function: f(0),
                block: b(0),
                closure_type: s(0),
                expected: flbc::CallableResultOwnership::Scalar,
                actual: flbc::CallableResultOwnership::Owned,
            })
        );
    }

    #[test]
    fn explicit_abi_boxing_is_canonical_and_lowers_without_conversion() {
        let validated = validate(boxing_program(), ValidationLimits::default())
            .expect("one explicit ABI round trip is valid");
        assert_eq!(
            validated.canonical_text(),
            concat!(
                "fir/14 entry=f0\n",
                "function f0 params=[] ownership=[] result=nat result_ownership=scalar\n",
                " block b0\n",
                "  v0:nat = nat 41\n",
                "  v1:abi = box v0\n",
                "  v2:nat = unbox nat v1\n",
                "  return v2\n",
            )
        );

        let lowered = lower_to_flbc(&validated).expect("boxing lowers through validated FLBC");
        assert!(matches!(
            lowered.functions()[0].code.as_slice(),
            [
                flbc::Instruction::Nat { value: 41, .. },
                flbc::Instruction::Copy { .. },
                flbc::Instruction::Copy { .. },
                flbc::Instruction::Return { .. },
            ]
        ));
    }

    #[test]
    fn malformed_abi_boxing_boundaries_are_refused_exactly() {
        let mut redundant_box = boxing_program();
        redundant_box.functions[0].result = ValueType::Abi;
        redundant_box.functions[0].blocks[0].bindings[2] = Binding {
            id: v(2),
            ty: ValueType::Abi,
            operation: Operation::Box(v(1)),
        };
        assert!(matches!(
            validate(redundant_box, ValidationLimits::default()),
            Err(ValidationError::RedundantBox {
                function,
                block,
                value,
            }) if function == f(0) && block == b(0) && value == v(1)
        ));

        let mut concrete_source = boxing_program();
        concrete_source.functions[0].blocks[0].bindings[1] = Binding {
            id: v(1),
            ty: ValueType::Nat,
            operation: Operation::Unbox {
                value: v(0),
                ty: ValueType::Nat,
            },
        };
        assert!(matches!(
            validate(concrete_source, ValidationLimits::default()),
            Err(ValidationError::UnboxOperandType {
                function,
                block,
                actual: ValueType::Nat,
            }) if function == f(0) && block == b(0)
        ));

        let mut redundant_unbox = boxing_program();
        redundant_unbox.functions[0].result = ValueType::Abi;
        redundant_unbox.functions[0].blocks[0].bindings[2] = Binding {
            id: v(2),
            ty: ValueType::Abi,
            operation: Operation::Unbox {
                value: v(1),
                ty: ValueType::Abi,
            },
        };
        assert!(matches!(
            validate(redundant_unbox, ValidationLimits::default()),
            Err(ValidationError::RedundantUnbox {
                function,
                block,
                value,
            }) if function == f(0) && block == b(0) && value == v(1)
        ));
    }

    #[test]
    fn schema_type_and_effect_tokens_are_total_and_stable() {
        let types = [
            ValueType::Unit,
            ValueType::Bool,
            ValueType::Nat,
            ValueType::String,
            ValueType::Constructor,
            ValueType::Array,
            ValueType::Ref,
            ValueType::Thunk,
            ValueType::Task,
            ValueType::Closure(ClosureTypeId::new(0)),
            ValueType::Abi,
        ];
        assert_eq!(
            types.map(ValueType::token),
            [
                "unit", "bool", "nat", "string", "ctor", "array", "ref", "thunk", "task",
                "closure", "abi",
            ]
        );
        assert_eq!(
            [
                EffectClass::Pure,
                EffectClass::State,
                EffectClass::Io,
                EffectClass::Task,
            ]
            .map(EffectClass::token),
            ["pure", "state", "io", "task"]
        );
    }

    #[test]
    fn canonical_text_and_flbc_bytes_are_identical_across_threads() {
        let validated =
            validate(all_operations_program(), ValidationLimits::default()).expect("valid FIR");
        let text = validated.canonical_text();
        let lowered = lower_to_flbc(&validated).expect("lower");
        let bytes =
            encode_canonical(&lowered, CodecLimits::default()).expect("canonical FLBC bytes");

        for _ in 0..16 {
            assert_eq!(validated.canonical_text(), text);
            let repeated = lower_to_flbc(&validated).expect("repeat lower");
            assert_eq!(
                encode_canonical(&repeated, CodecLimits::default()).expect("repeat encode"),
                bytes
            );
        }
        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    let rendered = validated.canonical_text();
                    let lowered = lower_to_flbc(&validated).expect("thread lower");
                    let encoded =
                        encode_canonical(&lowered, CodecLimits::default()).expect("thread encode");
                    (rendered, encoded)
                }));
            }
            for join in joins {
                let (rendered, encoded) = join.join().expect("worker");
                assert_eq!(rendered, text);
                assert_eq!(encoded, bytes);
            }
        });
    }

    #[test]
    fn branch_join_requires_definition_on_every_predecessor() {
        let program = Program::new(
            f(0),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            vec![Function {
                id: f(0),
                parameters: Vec::new(),
                parameter_ownership: Vec::new(),
                result: ValueType::Nat,
                result_ownership: flbc::CallableResultOwnership::Scalar,
                blocks: vec![
                    Block {
                        id: b(0),
                        bindings: vec![Binding {
                            id: v(0),
                            ty: ValueType::Nat,
                            operation: Operation::Nat(1),
                        }],
                        terminator: Terminator::BranchZero {
                            condition: v(0),
                            zero: b(1),
                            nonzero: b(2),
                        },
                    },
                    Block {
                        id: b(1),
                        bindings: vec![Binding {
                            id: v(1),
                            ty: ValueType::Nat,
                            operation: Operation::Nat(9),
                        }],
                        terminator: Terminator::Jump { target: b(3) },
                    },
                    Block {
                        id: b(2),
                        bindings: Vec::new(),
                        terminator: Terminator::Jump { target: b(3) },
                    },
                    Block {
                        id: b(3),
                        bindings: Vec::new(),
                        terminator: Terminator::Return { value: v(1) },
                    },
                ],
            }],
        );
        assert!(matches!(
            validate(program, ValidationLimits::default()),
            Err(ValidationError::ReadBeforeDefinition {
                function,
                block,
                value,
            }) if function == f(0) && block == b(3) && value == v(1)
        ));
    }

    #[test]
    fn malformed_tables_types_cfg_and_widths_never_publish() {
        let mut wrong_version = branch_program();
        wrong_version.schema_version += 1;
        assert!(matches!(
            validate(wrong_version, ValidationLimits::default()),
            Err(ValidationError::UnsupportedVersion { .. })
        ));

        let mut bad_intrinsic_id = branch_program();
        bad_intrinsic_id.intrinsics[0].id = i(1);
        assert!(matches!(
            validate(bad_intrinsic_id, ValidationLimits::default()),
            Err(ValidationError::NonCanonicalIntrinsicId { .. })
        ));

        let mut bad_row = branch_program();
        bad_row.intrinsics[0].row = "not-an-extern".to_string();
        assert_eq!(
            validate(bad_row, ValidationLimits::default()),
            Err(ValidationError::InvalidIntrinsicRow {
                intrinsic: i(0),
                row_bytes: 13,
            })
        );

        let mut bad_ownership_arity = branch_program();
        bad_ownership_arity.intrinsics[0].argument_ownership.pop();
        assert_eq!(
            validate(bad_ownership_arity, ValidationLimits::default()),
            Err(ValidationError::IntrinsicOwnershipArity {
                intrinsic: i(0),
                arguments: 2,
                ownership: 1,
            })
        );

        let mut unsorted_intrinsics = all_operations_program();
        let mut second_intrinsic = unsorted_intrinsics.intrinsics[0].clone();
        second_intrinsic.id = i(1);
        second_intrinsic.row = "extern:a".to_string();
        unsorted_intrinsics.intrinsics[0].row = "extern:z".to_string();
        unsorted_intrinsics.intrinsics.push(second_intrinsic);
        assert_eq!(
            validate(unsorted_intrinsics, ValidationLimits::default()),
            Err(ValidationError::IntrinsicRowsNotSorted {
                previous: i(0),
                current: i(1),
            })
        );

        let mut bad_function_id = branch_program();
        bad_function_id.functions[0].id = f(1);
        assert!(matches!(
            validate(bad_function_id, ValidationLimits::default()),
            Err(ValidationError::NonCanonicalFunctionId { .. })
        ));

        let mut bad_function_ownership = branch_program();
        bad_function_ownership.functions[0]
            .parameter_ownership
            .push(flbc::ArgumentOwnership::Borrowed);
        assert_eq!(
            validate(bad_function_ownership, ValidationLimits::default()),
            Err(ValidationError::FunctionOwnershipArity {
                function: f(0),
                parameters: 0,
                ownership: 1,
            })
        );

        let mut bad_block_id = branch_program();
        bad_block_id.functions[0].blocks[1].id = b(9);
        assert!(matches!(
            validate(bad_block_id, ValidationLimits::default()),
            Err(ValidationError::NonCanonicalBlockId { .. })
        ));

        let mut bad_value_id = branch_program();
        bad_value_id.functions[0].blocks[0].bindings[1].id = v(9);
        assert!(matches!(
            validate(bad_value_id, ValidationLimits::default()),
            Err(ValidationError::NonCanonicalValueId { .. })
        ));

        let mut wrong_binding_type = branch_program();
        wrong_binding_type.functions[0].blocks[0].bindings[0].ty = ValueType::String;
        assert!(matches!(
            validate(wrong_binding_type, ValidationLimits::default()),
            Err(ValidationError::BindingType { .. })
        ));

        let mut wrong_intrinsic_arity = branch_program();
        wrong_intrinsic_arity.functions[0].blocks[0].bindings[2].operation = Operation::Intrinsic {
            intrinsic: i(0),
            args: vec![v(0)],
        };
        assert!(matches!(
            validate(wrong_intrinsic_arity, ValidationLimits::default()),
            Err(ValidationError::IntrinsicArity { .. })
        ));

        let mut bad_target = branch_program();
        bad_target.functions[0].blocks[0].terminator = Terminator::Jump { target: b(99) };
        assert!(matches!(
            validate(bad_target, ValidationLimits::default()),
            Err(ValidationError::JumpOutOfBounds { .. })
        ));

        let mut unreachable = branch_program();
        unreachable.functions[0].blocks[0].terminator = Terminator::Jump { target: b(1) };
        assert!(matches!(
            validate(unreachable, ValidationLimits::default()),
            Err(ValidationError::UnreachableBlock { block, .. }) if block == b(2)
        ));

        let mut wrong_return = branch_program();
        wrong_return.functions[0].blocks[1].bindings[0].ty = ValueType::String;
        wrong_return.functions[0].blocks[1].bindings[0].operation =
            Operation::String("wrong".to_string());
        assert!(matches!(
            validate(wrong_return, ValidationLimits::default()),
            Err(ValidationError::ReturnType { .. })
        ));

        let entry = Function {
            id: f(0),
            parameters: Vec::new(),
            parameter_ownership: Vec::new(),
            result: ValueType::Nat,
            result_ownership: flbc::CallableResultOwnership::Scalar,
            blocks: vec![Block {
                id: b(0),
                bindings: vec![Binding {
                    id: v(0),
                    ty: ValueType::Nat,
                    operation: Operation::Nat(0),
                }],
                terminator: Terminator::Return { value: v(0) },
            }],
        };
        let oversized = Function {
            id: f(1),
            parameters: vec![ValueType::Abi; usize::from(u16::MAX) + 1],
            parameter_ownership: vec![flbc::ArgumentOwnership::Borrowed; usize::from(u16::MAX) + 1],
            result: ValueType::Abi,
            result_ownership: flbc::CallableResultOwnership::Owned,
            blocks: vec![Block {
                id: b(0),
                bindings: Vec::new(),
                terminator: Terminator::Return { value: v(0) },
            }],
        };
        let limits = ValidationLimits {
            max_values: usize::from(u16::MAX) + 2,
            max_dataflow_cells: usize::from(u16::MAX) + 2,
            ..ValidationLimits::default()
        };
        assert!(matches!(
            validate(
                Program::new(
                    f(0),
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                    vec![entry, oversized],
                ),
                limits
            ),
            Err(ValidationError::RegisterWidthExceeded { function, .. }) if function == f(1)
        ));
    }

    #[test]
    fn constructor_layout_table_binds_ids_abi_shape_and_field_types() {
        let mut bad_id = all_operations_program();
        bad_id.constructors[0].id = c(1);
        assert_eq!(
            validate(bad_id, ValidationLimits::default()),
            Err(ValidationError::NonCanonicalConstructorId {
                index: 0,
                seen: c(1),
            })
        );

        let mut bad_tag = all_operations_program();
        bad_tag.constructors[0].tag = abi::TAG_MAX_CTOR_TAG
            .checked_add(1)
            .expect("contract maximum leaves one invalid u8");
        assert!(matches!(
            validate(bad_tag, ValidationLimits::default()),
            Err(ValidationError::ConstructorTagOutOfRange {
                constructor,
                ..
            }) if constructor == c(0)
        ));

        let mut too_many_fields = all_operations_program();
        too_many_fields.constructors[0].fields = vec![ValueType::Abi; abi::MAX_CTOR_FIELDS];
        assert_eq!(
            validate(too_many_fields, ValidationLimits::default()),
            Err(ValidationError::TooManyConstructorFields {
                constructor: c(0),
                count: abi::MAX_CTOR_FIELDS,
            })
        );

        let mut too_many_scalars = all_operations_program();
        too_many_scalars.constructors[0].static_scalar_bytes = vec![0; abi::MAX_CTOR_SCALARS_SIZE];
        assert_eq!(
            validate(too_many_scalars, ValidationLimits::default()),
            Err(ValidationError::TooManyConstructorScalarBytes {
                constructor: c(0),
                count: abi::MAX_CTOR_SCALARS_SIZE,
            })
        );

        let mut missing = all_operations_program();
        let (constructor, _) =
            sample_constructor_operation(&mut missing).expect("fixture constructor");
        *constructor = c(1);
        assert!(matches!(
            validate(missing, ValidationLimits::default()),
            Err(ValidationError::MissingConstructor {
                constructor,
                ..
            }) if constructor == c(1)
        ));

        let mut wrong_arity = all_operations_program();
        let (_, fields) =
            sample_constructor_operation(&mut wrong_arity).expect("fixture constructor");
        fields.pop();
        assert!(matches!(
            validate(wrong_arity, ValidationLimits::default()),
            Err(ValidationError::ConstructorArity {
                constructor,
                expected: 3,
                actual: 2,
                ..
            }) if constructor == c(0)
        ));

        let mut wrong_type = all_operations_program();
        let (_, fields) =
            sample_constructor_operation(&mut wrong_type).expect("fixture constructor");
        fields[0] = v(0);
        assert!(matches!(
            validate(wrong_type, ValidationLimits::default()),
            Err(ValidationError::ConstructorArgumentType {
                constructor,
                argument: 0,
                expected: ValueType::Unit,
                actual: ValueType::Nat,
                ..
            }) if constructor == c(0)
        ));
    }

    #[test]
    fn projection_table_binds_ids_constructor_shape_operand_and_result_type() {
        let mut bad_id = all_operations_program();
        bad_id.projections[0].id = p(1);
        assert_eq!(
            validate(bad_id, ValidationLimits::default()),
            Err(ValidationError::NonCanonicalProjectionId {
                index: 0,
                seen: p(1),
            })
        );

        let mut missing_constructor = all_operations_program();
        missing_constructor.projections[0].constructor = c(1);
        assert_eq!(
            validate(missing_constructor, ValidationLimits::default()),
            Err(ValidationError::ProjectionMissingConstructor {
                projection: p(0),
                constructor: c(1),
            })
        );

        let mut bad_field = all_operations_program();
        bad_field.projections[0].field = 3;
        assert_eq!(
            validate(bad_field, ValidationLimits::default()),
            Err(ValidationError::ProjectionFieldOutOfBounds {
                projection: p(0),
                constructor: c(0),
                field: 3,
                field_count: 3,
            })
        );

        let mut missing_projection = all_operations_program();
        let (projection, _) =
            sample_projection_operation(&mut missing_projection).expect("fixture projection");
        *projection = p(1);
        assert!(matches!(
            validate(missing_projection, ValidationLimits::default()),
            Err(ValidationError::MissingProjection { projection, .. }) if projection == p(1)
        ));

        let mut wrong_operand = all_operations_program();
        let (_, value) =
            sample_projection_operation(&mut wrong_operand).expect("fixture projection");
        *value = v(0);
        assert!(matches!(
            validate(wrong_operand, ValidationLimits::default()),
            Err(ValidationError::ProjectionOperandType {
                projection,
                actual: ValueType::Nat,
                ..
            }) if projection == p(0)
        ));

        let mut wrong_result = all_operations_program();
        wrong_result.functions[0].blocks[0].bindings[8].ty = ValueType::Nat;
        assert!(matches!(
            validate(wrong_result, ValidationLimits::default()),
            Err(ValidationError::BindingType {
                value,
                declared: ValueType::Nat,
                inferred: ValueType::String,
                ..
            }) if value == v(8)
        ));
    }

    #[test]
    fn closure_signatures_bind_targets_captures_applications_and_result_types() {
        let mut noncanonical = all_operations_program();
        noncanonical.closure_types[0].id = s(1);
        assert_eq!(
            validate(noncanonical, ValidationLimits::default()),
            Err(ValidationError::NonCanonicalClosureTypeId {
                index: 0,
                seen: s(1),
            })
        );

        let mut empty = all_operations_program();
        empty.closure_types[0].parameters.clear();
        assert_eq!(
            validate(empty, ValidationLimits::default()),
            Err(ValidationError::EmptyClosureType { closure_type: s(0) })
        );

        let mut closure_type_ownership_arity = all_operations_program();
        closure_type_ownership_arity.closure_types[0]
            .parameter_ownership
            .clear();
        assert_eq!(
            validate(closure_type_ownership_arity, ValidationLimits::default()),
            Err(ValidationError::ClosureTypeOwnershipArity {
                closure_type: s(0),
                parameters: 1,
                ownership: 0,
            })
        );

        let mut duplicate = all_operations_program();
        duplicate.closure_types.push(ClosureTypeDecl {
            id: s(1),
            parameters: vec![ValueType::Nat],
            parameter_ownership: vec![flbc::ArgumentOwnership::Borrowed],
            result: ValueType::Nat,
            result_ownership: flbc::CallableResultOwnership::Scalar,
        });
        assert_eq!(
            validate(duplicate, ValidationLimits::default()),
            Err(ValidationError::ClosureTypesNotSorted {
                previous: s(0),
                current: s(1),
            })
        );

        let mut missing_type = all_operations_program();
        missing_type.functions[0].blocks[0].bindings[11].ty = ValueType::Closure(s(9));
        assert_eq!(
            validate(missing_type, ValidationLimits::default()),
            Err(ValidationError::MissingClosureType { closure_type: s(9) })
        );

        let mut missing_target = all_operations_program();
        missing_target.functions[0].blocks[0].bindings[11].operation = Operation::Closure {
            closure_type: s(0),
            function: f(9),
            captures: Vec::new(),
            capture_ownership: Vec::new(),
        };
        assert_eq!(
            validate(missing_target, ValidationLimits::default()),
            Err(ValidationError::MissingClosureTarget {
                function: f(0),
                block: b(0),
                target: f(9),
            })
        );

        let mut arity_overflow = all_operations_program();
        arity_overflow.closure_types[0].parameters = vec![ValueType::Nat; usize::from(u16::MAX)];
        arity_overflow.closure_types[0].parameter_ownership =
            vec![flbc::ArgumentOwnership::Borrowed; usize::from(u16::MAX)];
        arity_overflow.functions[2].parameters = vec![ValueType::Nat; usize::from(u16::MAX)];
        arity_overflow.functions[2].parameter_ownership =
            vec![flbc::ArgumentOwnership::Borrowed; usize::from(u16::MAX)];
        assert_eq!(
            validate(arity_overflow, ValidationLimits::default()),
            Err(ValidationError::ClosureTargetArityOverflow {
                function: f(0),
                block: b(0),
                target: f(2),
                target_parameters: usize::from(u16::MAX),
            })
        );

        let mut wrong_shape = all_operations_program();
        wrong_shape.functions[2].parameters.push(ValueType::Nat);
        wrong_shape.functions[2]
            .parameter_ownership
            .push(flbc::ArgumentOwnership::Borrowed);
        assert_eq!(
            validate(wrong_shape, ValidationLimits::default()),
            Err(ValidationError::ClosureTargetShape {
                function: f(0),
                block: b(0),
                target: f(2),
                captures: 0,
                parameters: 1,
                target_parameters: 2,
            })
        );

        let mut owned_capture = all_operations_program();
        owned_capture.functions[2]
            .parameters
            .insert(0, ValueType::Nat);
        owned_capture.functions[2]
            .parameter_ownership
            .insert(0, flbc::ArgumentOwnership::Owned);
        owned_capture.functions[2].blocks[0].bindings[0].id = v(2);
        owned_capture.functions[2].blocks[0].terminator = Terminator::Return { value: v(2) };
        owned_capture.functions[0].blocks[0].bindings[11].operation = Operation::Closure {
            closure_type: s(0),
            function: f(2),
            captures: vec![v(0)],
            capture_ownership: vec![flbc::ArgumentOwnership::Owned],
        };
        let validated_owned = validate(owned_capture.clone(), ValidationLimits::default())
            .expect("the capture vector matches the target parameter prefix");
        let lowered_owned =
            lower_to_flbc(&validated_owned).expect("owned closure capture lowers to FLBC");
        assert!(matches!(
            &lowered_owned.functions()[0].code[11],
            flbc::Instruction::Closure {
                function,
                captures,
                capture_ownership,
                ..
            } if *function == flbc::FunctionId::new(2)
                && captures == &[flbc::Register::new(0)]
                && capture_ownership == &[flbc::ArgumentOwnership::Owned]
        ));

        let mut ownership_arity = owned_capture.clone();
        let Operation::Closure {
            capture_ownership, ..
        } = &mut ownership_arity.functions[0].blocks[0].bindings[11].operation
        else {
            panic!("fixture retains its closure");
        };
        capture_ownership.clear();
        assert_eq!(
            validate(ownership_arity, ValidationLimits::default()),
            Err(ValidationError::ClosureOwnershipArity {
                function: f(0),
                block: b(0),
                target: f(2),
                captures: 1,
                ownership: 0,
            })
        );

        let mut ownership_contract = owned_capture.clone();
        let Operation::Closure {
            capture_ownership, ..
        } = &mut ownership_contract.functions[0].blocks[0].bindings[11].operation
        else {
            panic!("fixture retains its closure");
        };
        capture_ownership[0] = flbc::ArgumentOwnership::Borrowed;
        assert_eq!(
            validate(ownership_contract, ValidationLimits::default()),
            Err(ValidationError::ClosureOwnershipContract {
                function: f(0),
                block: b(0),
                target: f(2),
                capture: 0,
                expected: flbc::ArgumentOwnership::Owned,
                actual: flbc::ArgumentOwnership::Borrowed,
            })
        );

        let mut unique_capture = owned_capture;
        unique_capture.functions[2].parameter_ownership[0] = flbc::ArgumentOwnership::Unique;
        let Operation::Closure {
            capture_ownership, ..
        } = &mut unique_capture.functions[0].blocks[0].bindings[11].operation
        else {
            panic!("fixture retains its closure");
        };
        capture_ownership[0] = flbc::ArgumentOwnership::Unique;
        assert_eq!(
            validate(unique_capture, ValidationLimits::default()),
            Err(ValidationError::ClosureUniqueCapture {
                function: f(0),
                block: b(0),
                target: f(2),
                capture: 0,
            })
        );

        let mut wrong_capture = all_operations_program();
        wrong_capture.functions[2]
            .parameters
            .insert(0, ValueType::Nat);
        wrong_capture.functions[2]
            .parameter_ownership
            .insert(0, flbc::ArgumentOwnership::Borrowed);
        wrong_capture.functions[0].blocks[0].bindings[11].operation = Operation::Closure {
            closure_type: s(0),
            function: f(2),
            captures: vec![v(6)],
            capture_ownership: vec![flbc::ArgumentOwnership::Borrowed],
        };
        assert_eq!(
            validate(wrong_capture, ValidationLimits::default()),
            Err(ValidationError::ClosureCaptureType {
                function: f(0),
                block: b(0),
                target: f(2),
                capture: 0,
                expected: ValueType::Nat,
                actual: ValueType::String,
            })
        );

        let mut wrong_parameter = all_operations_program();
        wrong_parameter.functions[2].parameters[0] = ValueType::String;
        assert_eq!(
            validate(wrong_parameter, ValidationLimits::default()),
            Err(ValidationError::ClosureParameterType {
                function: f(0),
                block: b(0),
                target: f(2),
                parameter: 0,
                expected: ValueType::Nat,
                actual: ValueType::String,
            })
        );

        let mut wrong_parameter_ownership = all_operations_program();
        wrong_parameter_ownership.functions[2].parameter_ownership[0] =
            flbc::ArgumentOwnership::Owned;
        assert_eq!(
            validate(wrong_parameter_ownership, ValidationLimits::default()),
            Err(ValidationError::ClosureParameterOwnership {
                function: f(0),
                block: b(0),
                target: f(2),
                parameter: 0,
                expected: flbc::ArgumentOwnership::Borrowed,
                actual: flbc::ArgumentOwnership::Owned,
            })
        );

        let mut wrong_result = all_operations_program();
        wrong_result.functions[2].result = ValueType::String;
        wrong_result.functions[2].result_ownership = flbc::CallableResultOwnership::Owned;
        assert_eq!(
            validate(wrong_result, ValidationLimits::default()),
            Err(ValidationError::ClosureResultType {
                function: f(0),
                block: b(0),
                target: f(2),
                expected: ValueType::Nat,
                actual: ValueType::String,
            })
        );

        let mut scalar_apply = all_operations_program();
        scalar_apply.functions[0].blocks[0].bindings[12].operation = Operation::Apply {
            closure: v(10),
            args: vec![v(10)],
            argument_ownership: vec![flbc::ArgumentOwnership::Borrowed],
            result_ownership: flbc::CallableResultOwnership::Scalar,
        };
        assert_eq!(
            validate(scalar_apply, ValidationLimits::default()),
            Err(ValidationError::ApplyOperandType {
                function: f(0),
                block: b(0),
                actual: ValueType::Nat,
            })
        );

        let mut wrong_arity = all_operations_program();
        wrong_arity.functions[0].blocks[0].bindings[12].operation = Operation::Apply {
            closure: v(11),
            args: Vec::new(),
            argument_ownership: Vec::new(),
            result_ownership: flbc::CallableResultOwnership::Scalar,
        };
        assert_eq!(
            validate(wrong_arity, ValidationLimits::default()),
            Err(ValidationError::EmptyApply {
                function: f(0),
                block: b(0),
                closure_type: s(0),
            })
        );

        let mut scalar_overapplication = all_operations_program();
        scalar_overapplication.functions[0].blocks[0].bindings[12].operation = Operation::Apply {
            closure: v(11),
            args: vec![v(10), v(10)],
            argument_ownership: vec![
                flbc::ArgumentOwnership::Borrowed,
                flbc::ArgumentOwnership::Borrowed,
            ],
            result_ownership: flbc::CallableResultOwnership::Scalar,
        };
        assert_eq!(
            validate(scalar_overapplication, ValidationLimits::default()),
            Err(ValidationError::ApplyRemainderType {
                function: f(0),
                block: b(0),
                closure_type: s(0),
                argument: 1,
                actual: ValueType::Nat,
            })
        );

        let mut wrong_argument = all_operations_program();
        wrong_argument.functions[0].blocks[0].bindings[12].operation = Operation::Apply {
            closure: v(11),
            args: vec![v(6)],
            argument_ownership: vec![flbc::ArgumentOwnership::Borrowed],
            result_ownership: flbc::CallableResultOwnership::Scalar,
        };
        assert_eq!(
            validate(wrong_argument, ValidationLimits::default()),
            Err(ValidationError::ApplyArgumentType {
                function: f(0),
                block: b(0),
                closure_type: s(0),
                argument: 0,
                expected: ValueType::Nat,
                actual: ValueType::String,
            })
        );

        let mut apply_ownership_arity = all_operations_program();
        let Operation::Apply {
            argument_ownership, ..
        } = &mut apply_ownership_arity.functions[0].blocks[0].bindings[12].operation
        else {
            panic!("fixture retains its Apply");
        };
        argument_ownership.clear();
        assert_eq!(
            validate(apply_ownership_arity, ValidationLimits::default()),
            Err(ValidationError::ApplyOwnershipArity {
                function: f(0),
                block: b(0),
                closure_type: s(0),
                arguments: 1,
                ownership: 0,
            })
        );

        let mut apply_ownership_contract = all_operations_program();
        let Operation::Apply {
            argument_ownership, ..
        } = &mut apply_ownership_contract.functions[0].blocks[0].bindings[12].operation
        else {
            panic!("fixture retains its Apply");
        };
        argument_ownership[0] = flbc::ArgumentOwnership::Owned;
        assert_eq!(
            validate(apply_ownership_contract, ValidationLimits::default()),
            Err(ValidationError::ApplyOwnershipContract {
                function: f(0),
                block: b(0),
                closure_type: s(0),
                argument: 0,
                expected: flbc::ArgumentOwnership::Borrowed,
                actual: flbc::ArgumentOwnership::Owned,
            })
        );

        let mut owned_apply = all_operations_program();
        owned_apply.closure_types[0].parameter_ownership[0] = flbc::ArgumentOwnership::Owned;
        owned_apply.functions[2].parameter_ownership[0] = flbc::ArgumentOwnership::Owned;
        let Operation::Apply {
            argument_ownership, ..
        } = &mut owned_apply.functions[0].blocks[0].bindings[12].operation
        else {
            panic!("fixture retains its Apply");
        };
        argument_ownership[0] = flbc::ArgumentOwnership::Owned;
        let owned_apply = validate(owned_apply, ValidationLimits::default())
            .expect("Apply ownership matches the callable suffix");
        let lowered = lower_to_flbc(&owned_apply).expect("owned Apply lowers to FLBC");
        assert!(matches!(
            &lowered.functions()[0].code[12],
            flbc::Instruction::Apply {
                closure,
                args,
                argument_ownership,
                ..
            } if *closure == flbc::Register::new(11)
                && args == &[flbc::Register::new(10)]
                && argument_ownership == &[flbc::ArgumentOwnership::Owned]
        ));
    }

    #[test]
    fn typed_application_chains_cover_partial_repeated_and_overapplication() {
        let program = Program::new_with_closures(
            f(0),
            Vec::new(),
            Vec::new(),
            vec![
                ClosureTypeDecl {
                    id: s(0),
                    parameters: vec![ValueType::Nat],
                    parameter_ownership: vec![flbc::ArgumentOwnership::Borrowed],
                    result: ValueType::Nat,
                    result_ownership: flbc::CallableResultOwnership::Scalar,
                },
                ClosureTypeDecl {
                    id: s(1),
                    parameters: vec![ValueType::Nat],
                    parameter_ownership: vec![flbc::ArgumentOwnership::Borrowed],
                    result: ValueType::Closure(s(0)),
                    result_ownership: flbc::CallableResultOwnership::Owned,
                },
                ClosureTypeDecl {
                    id: s(2),
                    parameters: vec![ValueType::Nat, ValueType::Nat],
                    parameter_ownership: vec![
                        flbc::ArgumentOwnership::Borrowed,
                        flbc::ArgumentOwnership::Borrowed,
                    ],
                    result: ValueType::Nat,
                    result_ownership: flbc::CallableResultOwnership::Scalar,
                },
            ],
            vec![nat_add()],
            vec![
                Function {
                    id: f(0),
                    parameters: Vec::new(),
                    parameter_ownership: Vec::new(),
                    result: ValueType::Nat,
                    result_ownership: flbc::CallableResultOwnership::Scalar,
                    blocks: vec![Block {
                        id: b(0),
                        bindings: vec![
                            Binding {
                                id: v(0),
                                ty: ValueType::Nat,
                                operation: Operation::Nat(20),
                            },
                            Binding {
                                id: v(1),
                                ty: ValueType::Nat,
                                operation: Operation::Nat(22),
                            },
                            Binding {
                                id: v(2),
                                ty: ValueType::Closure(s(2)),
                                operation: Operation::Closure {
                                    closure_type: s(2),
                                    function: f(3),
                                    captures: Vec::new(),
                                    capture_ownership: Vec::new(),
                                },
                            },
                            Binding {
                                id: v(3),
                                ty: ValueType::Closure(s(0)),
                                operation: Operation::Apply {
                                    closure: v(2),
                                    args: vec![v(0)],
                                    argument_ownership: vec![flbc::ArgumentOwnership::Borrowed],
                                    result_ownership: flbc::CallableResultOwnership::Owned,
                                },
                            },
                            Binding {
                                id: v(4),
                                ty: ValueType::Nat,
                                operation: Operation::Apply {
                                    closure: v(3),
                                    args: vec![v(1)],
                                    argument_ownership: vec![flbc::ArgumentOwnership::Borrowed],
                                    result_ownership: flbc::CallableResultOwnership::Scalar,
                                },
                            },
                            Binding {
                                id: v(5),
                                ty: ValueType::Closure(s(1)),
                                operation: Operation::Closure {
                                    closure_type: s(1),
                                    function: f(1),
                                    captures: Vec::new(),
                                    capture_ownership: Vec::new(),
                                },
                            },
                            Binding {
                                id: v(6),
                                ty: ValueType::Nat,
                                operation: Operation::Apply {
                                    closure: v(5),
                                    args: vec![v(0), v(1)],
                                    argument_ownership: vec![
                                        flbc::ArgumentOwnership::Borrowed,
                                        flbc::ArgumentOwnership::Borrowed,
                                    ],
                                    result_ownership: flbc::CallableResultOwnership::Scalar,
                                },
                            },
                            Binding {
                                id: v(7),
                                ty: ValueType::Nat,
                                operation: Operation::Intrinsic {
                                    intrinsic: i(0),
                                    args: vec![v(4), v(6)],
                                },
                            },
                        ],
                        terminator: Terminator::Return { value: v(7) },
                    }],
                },
                Function {
                    id: f(1),
                    parameters: vec![ValueType::Nat],
                    parameter_ownership: vec![flbc::ArgumentOwnership::Borrowed],
                    result: ValueType::Closure(s(0)),
                    result_ownership: flbc::CallableResultOwnership::Owned,
                    blocks: vec![Block {
                        id: b(0),
                        bindings: vec![Binding {
                            id: v(1),
                            ty: ValueType::Closure(s(0)),
                            operation: Operation::Closure {
                                closure_type: s(0),
                                function: f(2),
                                captures: vec![v(0)],
                                capture_ownership: vec![flbc::ArgumentOwnership::Borrowed],
                            },
                        }],
                        terminator: Terminator::Return { value: v(1) },
                    }],
                },
                Function {
                    id: f(2),
                    parameters: vec![ValueType::Nat, ValueType::Nat],
                    parameter_ownership: vec![
                        flbc::ArgumentOwnership::Borrowed,
                        flbc::ArgumentOwnership::Borrowed,
                    ],
                    result: ValueType::Nat,
                    result_ownership: flbc::CallableResultOwnership::Scalar,
                    blocks: vec![Block {
                        id: b(0),
                        bindings: vec![Binding {
                            id: v(2),
                            ty: ValueType::Nat,
                            operation: Operation::Intrinsic {
                                intrinsic: i(0),
                                args: vec![v(0), v(1)],
                            },
                        }],
                        terminator: Terminator::Return { value: v(2) },
                    }],
                },
                Function {
                    id: f(3),
                    parameters: vec![ValueType::Nat, ValueType::Nat],
                    parameter_ownership: vec![
                        flbc::ArgumentOwnership::Borrowed,
                        flbc::ArgumentOwnership::Borrowed,
                    ],
                    result: ValueType::Nat,
                    result_ownership: flbc::CallableResultOwnership::Scalar,
                    blocks: vec![Block {
                        id: b(0),
                        bindings: vec![Binding {
                            id: v(2),
                            ty: ValueType::Nat,
                            operation: Operation::Intrinsic {
                                intrinsic: i(0),
                                args: vec![v(0), v(1)],
                            },
                        }],
                        terminator: Terminator::Return { value: v(2) },
                    }],
                },
            ],
        );
        let validated =
            validate(program, ValidationLimits::default()).expect("typed application chains");
        let lowered = lower_to_flbc(&validated).expect("application chains lower to FLBC");
        let apply_widths = lowered
            .functions()
            .iter()
            .flat_map(|function| &function.code)
            .filter_map(|instruction| match instruction {
                flbc::Instruction::Apply { args, .. } => Some(args.len()),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(apply_widths, [1, 1, 2]);

        let missing_suffix = Program::new_with_closures(
            f(0),
            Vec::new(),
            Vec::new(),
            vec![ClosureTypeDecl {
                id: s(0),
                parameters: vec![ValueType::String, ValueType::String],
                parameter_ownership: vec![
                    flbc::ArgumentOwnership::Borrowed,
                    flbc::ArgumentOwnership::Borrowed,
                ],
                result: ValueType::Nat,
                result_ownership: flbc::CallableResultOwnership::Scalar,
            }],
            Vec::new(),
            vec![
                Function {
                    id: f(0),
                    parameters: Vec::new(),
                    parameter_ownership: Vec::new(),
                    result: ValueType::Abi,
                    result_ownership: flbc::CallableResultOwnership::Owned,
                    blocks: vec![Block {
                        id: b(0),
                        bindings: vec![
                            Binding {
                                id: v(0),
                                ty: ValueType::String,
                                operation: Operation::String("partial".to_string()),
                            },
                            Binding {
                                id: v(1),
                                ty: ValueType::Closure(s(0)),
                                operation: Operation::Closure {
                                    closure_type: s(0),
                                    function: f(1),
                                    captures: Vec::new(),
                                    capture_ownership: Vec::new(),
                                },
                            },
                            Binding {
                                id: v(2),
                                ty: ValueType::Abi,
                                operation: Operation::Apply {
                                    closure: v(1),
                                    args: vec![v(0)],
                                    argument_ownership: vec![flbc::ArgumentOwnership::Borrowed],
                                    result_ownership: flbc::CallableResultOwnership::Owned,
                                },
                            },
                        ],
                        terminator: Terminator::Return { value: v(2) },
                    }],
                },
                Function {
                    id: f(1),
                    parameters: vec![ValueType::String, ValueType::String],
                    parameter_ownership: vec![
                        flbc::ArgumentOwnership::Borrowed,
                        flbc::ArgumentOwnership::Borrowed,
                    ],
                    result: ValueType::Nat,
                    result_ownership: flbc::CallableResultOwnership::Scalar,
                    blocks: vec![Block {
                        id: b(0),
                        bindings: vec![Binding {
                            id: v(2),
                            ty: ValueType::Nat,
                            operation: Operation::Nat(0),
                        }],
                        terminator: Terminator::Return { value: v(2) },
                    }],
                },
            ],
        );
        assert_eq!(
            validate(missing_suffix, ValidationLimits::default()),
            Err(ValidationError::ApplyPartialClosureTypeMissing {
                function: f(0),
                block: b(0),
                closure_type: s(0),
                consumed: 1,
            })
        );
    }

    #[test]
    fn every_resource_dimension_is_checked_before_authority() {
        let program = all_operations_program();
        let cases = [
            (
                ValidationResource::Functions,
                ValidationLimits {
                    max_functions: 1,
                    ..ValidationLimits::default()
                },
            ),
            (
                ValidationResource::Constructors,
                ValidationLimits {
                    max_constructors: 0,
                    ..ValidationLimits::default()
                },
            ),
            (
                ValidationResource::Projections,
                ValidationLimits {
                    max_projections: 0,
                    ..ValidationLimits::default()
                },
            ),
            (
                ValidationResource::ClosureTypes,
                ValidationLimits {
                    max_closure_types: 0,
                    ..ValidationLimits::default()
                },
            ),
            (
                ValidationResource::Intrinsics,
                ValidationLimits {
                    max_intrinsics: 0,
                    ..ValidationLimits::default()
                },
            ),
            (
                ValidationResource::Blocks,
                ValidationLimits {
                    max_blocks: 1,
                    ..ValidationLimits::default()
                },
            ),
            (
                ValidationResource::Values,
                ValidationLimits {
                    max_values: 1,
                    ..ValidationLimits::default()
                },
            ),
            (
                ValidationResource::Operations,
                ValidationLimits {
                    max_operations: 1,
                    ..ValidationLimits::default()
                },
            ),
            (
                ValidationResource::Operands,
                ValidationLimits {
                    max_operands: 1,
                    ..ValidationLimits::default()
                },
            ),
            (
                ValidationResource::LiteralBytes,
                ValidationLimits {
                    max_literal_bytes: 1,
                    ..ValidationLimits::default()
                },
            ),
            (
                ValidationResource::DataflowCells,
                ValidationLimits {
                    max_dataflow_cells: 1,
                    ..ValidationLimits::default()
                },
            ),
        ];
        for (resource, limits) in cases {
            assert!(matches!(
                validate(program.clone(), limits),
                Err(ValidationError::ResourceLimit {
                    resource: actual,
                    ..
                }) if actual == resource
            ));
        }
    }
}
