//! Canonical Boolean and fixed-width bitvector translation to Verdict CNF.
//!
//! The translator has two passes. The first pass checks every construct against
//! [`BITBLAST_MANIFEST`], validates widths and input reuse, and enforces structural
//! budgets without allocating a SAT variable. Only a fully supported tree reaches
//! the encoding pass. Consequently an unsupported construct in a semantically dead
//! branch is still a typed refusal, never a silently approximated formula.

use std::collections::BTreeMap;

use crate::{
    Clause, ClauseId, Cnf, InputClause, Literal, Polarity, SchemaError, SchemaLimits, VariableId,
};

/// Version of the in-memory supported/refused contract.
///
/// This is not a new durable wire schema. The only bytes emitted by this module
/// use the already-registered [`crate::CNF_SCHEMA`].
pub const BITBLAST_MANIFEST_VERSION: u16 = 1;

/// Stable identity carried by a bitblast artifact and later reflection provenance.
pub const BITBLAST_MANIFEST_ID: &str = "fln.verdict.bitblast-supported-refused/1";

/// Registered policy for every semantically free translation order.
pub const CANONICAL_BITBLAST_POLICY_ID: &str = "fln.verdict.bitblast.canonical/1";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BitblastDeterminismPolicy {
    pub policy_id: &'static str,
    pub traversal_order: &'static str,
    pub input_bit_order: &'static str,
    pub fresh_variable_order: &'static str,
    pub gate_clause_order: &'static str,
    pub final_clause_order: &'static str,
}

pub const CANONICAL_BITBLAST_POLICY: BitblastDeterminismPolicy = BitblastDeterminismPolicy {
    policy_id: CANONICAL_BITBLAST_POLICY_ID,
    traversal_order: "depth-first-left-to-right-after-whole-tree-manifest-preflight",
    input_bit_order: "least-significant-bit-first",
    fresh_variable_order: "first-structural-occurrence-then-gate-construction-order",
    gate_clause_order: "fixed-tseitin-template-order-with-canonical-literals",
    final_clause_order: "monotone-clause-id-emission-order",
};

/// Closed construct vocabulary governed by the v1 manifest.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum BitblastConstruct {
    BooleanConstant = 1,
    BooleanInput = 2,
    BooleanNot = 3,
    BooleanAnd = 4,
    BooleanOr = 5,
    BooleanXor = 6,
    BooleanImplication = 7,
    BooleanIff = 8,
    BitvectorConstant = 9,
    BitvectorInput = 10,
    BitwiseNot = 11,
    BitwiseAnd = 12,
    BitwiseOr = 13,
    BitwiseXor = 14,
    TwosComplementNegation = 15,
    WrappingAddition = 16,
    WrappingSubtraction = 17,
    WrappingMultiplication = 18,
    ShiftLeft = 19,
    LogicalShiftRight = 20,
    ArithmeticShiftRight = 21,
    Equality = 22,
    Inequality = 23,
    UnsignedLessThan = 24,
    UnsignedLessOrEqual = 25,
    UnsignedGreaterThan = 26,
    UnsignedGreaterOrEqual = 27,
    SignedLessThan = 28,
    SignedLessOrEqual = 29,
    SignedGreaterThan = 30,
    SignedGreaterOrEqual = 31,
    RotateLeft = 32,
    RotateRight = 33,
    UnsignedDivision = 34,
    UnsignedRemainder = 35,
    SignedDivision = 36,
    SignedRemainder = 37,
    Concatenation = 38,
    Extraction = 39,
    ZeroExtension = 40,
    SignExtension = 41,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BitblastSupport {
    Supported,
    Refused { code: &'static str },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BitblastManifestRow {
    pub construct: BitblastConstruct,
    pub support: BitblastSupport,
    pub semantics: &'static str,
}

const SUPPORTED: BitblastSupport = BitblastSupport::Supported;

/// Exact v1 supported/refused rows. Their order is part of the manifest.
pub const BITBLAST_MANIFEST_ROWS: &[BitblastManifestRow] = &[
    BitblastManifestRow {
        construct: BitblastConstruct::BooleanConstant,
        support: SUPPORTED,
        semantics: "exact true or false Boolean value",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::BooleanInput,
        support: SUPPORTED,
        semantics: "one SAT variable per Boolean symbol",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::BooleanNot,
        support: SUPPORTED,
        semantics: "Boolean complement",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::BooleanAnd,
        support: SUPPORTED,
        semantics: "strict binary conjunction",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::BooleanOr,
        support: SUPPORTED,
        semantics: "strict binary disjunction",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::BooleanXor,
        support: SUPPORTED,
        semantics: "strict binary exclusive-or",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::BooleanImplication,
        support: SUPPORTED,
        semantics: "not-left or right",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::BooleanIff,
        support: SUPPORTED,
        semantics: "Boolean equality",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::BitvectorConstant,
        support: SUPPORTED,
        semantics: "exact declared-width bits in least-significant-first order",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::BitvectorInput,
        support: SUPPORTED,
        semantics: "one SAT variable per bit, allocated least-significant first",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::BitwiseNot,
        support: SUPPORTED,
        semantics: "pointwise complement at unchanged width",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::BitwiseAnd,
        support: SUPPORTED,
        semantics: "pointwise conjunction of equal-width operands",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::BitwiseOr,
        support: SUPPORTED,
        semantics: "pointwise disjunction of equal-width operands",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::BitwiseXor,
        support: SUPPORTED,
        semantics: "pointwise exclusive-or of equal-width operands",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::TwosComplementNegation,
        support: SUPPORTED,
        semantics: "two's-complement negation modulo 2^width",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::WrappingAddition,
        support: SUPPORTED,
        semantics: "addition modulo 2^width; final carry is discarded",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::WrappingSubtraction,
        support: SUPPORTED,
        semantics: "subtraction modulo 2^width using two's complement",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::WrappingMultiplication,
        support: SUPPORTED,
        semantics: "schoolbook multiplication modulo 2^width; high bits are discarded",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::ShiftLeft,
        support: SUPPORTED,
        semantics: "unsigned dynamic amount; low zero fill; amount >= width yields zero",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::LogicalShiftRight,
        support: SUPPORTED,
        semantics: "unsigned dynamic amount; high zero fill; amount >= width yields zero",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::ArithmeticShiftRight,
        support: SUPPORTED,
        semantics: "unsigned dynamic amount; sign fill; amount >= width yields all sign bits",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::Equality,
        support: SUPPORTED,
        semantics: "all corresponding bits equal; zero-width values are equal",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::Inequality,
        support: SUPPORTED,
        semantics: "Boolean complement of equal-width equality",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::UnsignedLessThan,
        support: SUPPORTED,
        semantics: "unsigned lexicographic comparison from most-significant bit",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::UnsignedLessOrEqual,
        support: SUPPORTED,
        semantics: "unsigned less-than or equality",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::UnsignedGreaterThan,
        support: SUPPORTED,
        semantics: "unsigned less-than with operands reversed",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::UnsignedGreaterOrEqual,
        support: SUPPORTED,
        semantics: "unsigned greater-than or equality",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::SignedLessThan,
        support: SUPPORTED,
        semantics: "two's-complement comparison; zero-width value denotes zero",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::SignedLessOrEqual,
        support: SUPPORTED,
        semantics: "signed less-than or equality",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::SignedGreaterThan,
        support: SUPPORTED,
        semantics: "signed less-than with operands reversed",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::SignedGreaterOrEqual,
        support: SUPPORTED,
        semantics: "signed greater-than or equality",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::RotateLeft,
        support: BitblastSupport::Refused {
            code: "FLN-BITBLAST-REFUSED-ROTATE-LEFT",
        },
        semantics: "not in the v1 encoding surface",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::RotateRight,
        support: BitblastSupport::Refused {
            code: "FLN-BITBLAST-REFUSED-ROTATE-RIGHT",
        },
        semantics: "not in the v1 encoding surface",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::UnsignedDivision,
        support: BitblastSupport::Refused {
            code: "FLN-BITBLAST-REFUSED-UNSIGNED-DIVISION",
        },
        semantics: "not in the v1 encoding surface",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::UnsignedRemainder,
        support: BitblastSupport::Refused {
            code: "FLN-BITBLAST-REFUSED-UNSIGNED-REMAINDER",
        },
        semantics: "not in the v1 encoding surface",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::SignedDivision,
        support: BitblastSupport::Refused {
            code: "FLN-BITBLAST-REFUSED-SIGNED-DIVISION",
        },
        semantics: "not in the v1 encoding surface",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::SignedRemainder,
        support: BitblastSupport::Refused {
            code: "FLN-BITBLAST-REFUSED-SIGNED-REMAINDER",
        },
        semantics: "not in the v1 encoding surface",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::Concatenation,
        support: BitblastSupport::Refused {
            code: "FLN-BITBLAST-REFUSED-CONCATENATION",
        },
        semantics: "not in the v1 encoding surface",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::Extraction,
        support: BitblastSupport::Refused {
            code: "FLN-BITBLAST-REFUSED-EXTRACTION",
        },
        semantics: "not in the v1 encoding surface",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::ZeroExtension,
        support: BitblastSupport::Refused {
            code: "FLN-BITBLAST-REFUSED-ZERO-EXTENSION",
        },
        semantics: "not in the v1 encoding surface",
    },
    BitblastManifestRow {
        construct: BitblastConstruct::SignExtension,
        support: BitblastSupport::Refused {
            code: "FLN-BITBLAST-REFUSED-SIGN-EXTENSION",
        },
        semantics: "not in the v1 encoding surface",
    },
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BitblastManifest {
    pub id: &'static str,
    pub version: u16,
    pub policy_id: &'static str,
    pub width_semantics: &'static str,
    pub bit_order: &'static str,
    pub overflow_semantics: &'static str,
    pub signed_semantics: &'static str,
    pub shift_semantics: &'static str,
    pub rows: &'static [BitblastManifestRow],
}

impl BitblastManifest {
    pub fn row(self, construct: BitblastConstruct) -> Option<&'static BitblastManifestRow> {
        self.rows.iter().find(|row| row.construct == construct)
    }
}

pub const BITBLAST_MANIFEST: BitblastManifest = BitblastManifest {
    id: BITBLAST_MANIFEST_ID,
    version: BITBLAST_MANIFEST_VERSION,
    policy_id: CANONICAL_BITBLAST_POLICY_ID,
    width_semantics: "all widths from zero through the explicit operation budget; operands requiring equality must have exactly equal widths",
    bit_order: "bit index zero and serialized input position zero are least significant",
    overflow_semantics: "negation, addition, subtraction, and multiplication are modulo 2^width; width zero has the unique empty value",
    signed_semantics: "signed comparisons use width-indexed two's-complement interpretation; unsigned comparisons use natural binary interpretation",
    shift_semantics: "shift amounts are unsigned bitvectors; amounts at least the value width saturate to the operation's documented fill",
    rows: BITBLAST_MANIFEST_ROWS,
};

/// Stable source-level symbol. Boolean and bitvector inputs share one namespace.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BitblastSymbol(u32);

impl BitblastSymbol {
    pub const fn new(raw: u32) -> Option<Self> {
        if raw == 0 { None } else { Some(Self(raw)) }
    }

    pub const fn get(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoolBinaryOp {
    And,
    Or,
    Xor,
    Implication,
    Iff,
}

impl BoolBinaryOp {
    const fn construct(self) -> BitblastConstruct {
        match self {
            Self::And => BitblastConstruct::BooleanAnd,
            Self::Or => BitblastConstruct::BooleanOr,
            Self::Xor => BitblastConstruct::BooleanXor,
            Self::Implication => BitblastConstruct::BooleanImplication,
            Self::Iff => BitblastConstruct::BooleanIff,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BvUnaryOp {
    Not,
    Negate,
}

impl BvUnaryOp {
    const fn construct(self) -> BitblastConstruct {
        match self {
            Self::Not => BitblastConstruct::BitwiseNot,
            Self::Negate => BitblastConstruct::TwosComplementNegation,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BvBinaryOp {
    And,
    Or,
    Xor,
    Add,
    Subtract,
    Multiply,
}

impl BvBinaryOp {
    const fn construct(self) -> BitblastConstruct {
        match self {
            Self::And => BitblastConstruct::BitwiseAnd,
            Self::Or => BitblastConstruct::BitwiseOr,
            Self::Xor => BitblastConstruct::BitwiseXor,
            Self::Add => BitblastConstruct::WrappingAddition,
            Self::Subtract => BitblastConstruct::WrappingSubtraction,
            Self::Multiply => BitblastConstruct::WrappingMultiplication,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BvShiftOp {
    Left,
    LogicalRight,
    ArithmeticRight,
}

impl BvShiftOp {
    const fn construct(self) -> BitblastConstruct {
        match self {
            Self::Left => BitblastConstruct::ShiftLeft,
            Self::LogicalRight => BitblastConstruct::LogicalShiftRight,
            Self::ArithmeticRight => BitblastConstruct::ArithmeticShiftRight,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BvComparison {
    Equal,
    NotEqual,
    UnsignedLessThan,
    UnsignedLessOrEqual,
    UnsignedGreaterThan,
    UnsignedGreaterOrEqual,
    SignedLessThan,
    SignedLessOrEqual,
    SignedGreaterThan,
    SignedGreaterOrEqual,
}

impl BvComparison {
    const fn construct(self) -> BitblastConstruct {
        match self {
            Self::Equal => BitblastConstruct::Equality,
            Self::NotEqual => BitblastConstruct::Inequality,
            Self::UnsignedLessThan => BitblastConstruct::UnsignedLessThan,
            Self::UnsignedLessOrEqual => BitblastConstruct::UnsignedLessOrEqual,
            Self::UnsignedGreaterThan => BitblastConstruct::UnsignedGreaterThan,
            Self::UnsignedGreaterOrEqual => BitblastConstruct::UnsignedGreaterOrEqual,
            Self::SignedLessThan => BitblastConstruct::SignedLessThan,
            Self::SignedLessOrEqual => BitblastConstruct::SignedLessOrEqual,
            Self::SignedGreaterThan => BitblastConstruct::SignedGreaterThan,
            Self::SignedGreaterOrEqual => BitblastConstruct::SignedGreaterOrEqual,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnsupportedBvOp {
    RotateLeft,
    RotateRight,
    UnsignedDivision,
    UnsignedRemainder,
    SignedDivision,
    SignedRemainder,
    Concatenation,
    Extraction,
    ZeroExtension,
    SignExtension,
}

impl UnsupportedBvOp {
    pub const ALL: [Self; 10] = [
        Self::RotateLeft,
        Self::RotateRight,
        Self::UnsignedDivision,
        Self::UnsignedRemainder,
        Self::SignedDivision,
        Self::SignedRemainder,
        Self::Concatenation,
        Self::Extraction,
        Self::ZeroExtension,
        Self::SignExtension,
    ];

    pub const fn construct(self) -> BitblastConstruct {
        match self {
            Self::RotateLeft => BitblastConstruct::RotateLeft,
            Self::RotateRight => BitblastConstruct::RotateRight,
            Self::UnsignedDivision => BitblastConstruct::UnsignedDivision,
            Self::UnsignedRemainder => BitblastConstruct::UnsignedRemainder,
            Self::SignedDivision => BitblastConstruct::SignedDivision,
            Self::SignedRemainder => BitblastConstruct::SignedRemainder,
            Self::Concatenation => BitblastConstruct::Concatenation,
            Self::Extraction => BitblastConstruct::Extraction,
            Self::ZeroExtension => BitblastConstruct::ZeroExtension,
            Self::SignExtension => BitblastConstruct::SignExtension,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BvExpr {
    Constant {
        bits_lsb_first: Box<[bool]>,
    },
    Input {
        symbol: BitblastSymbol,
        width: u32,
    },
    Unary {
        op: BvUnaryOp,
        value: Box<Self>,
    },
    Binary {
        op: BvBinaryOp,
        left: Box<Self>,
        right: Box<Self>,
    },
    Shift {
        op: BvShiftOp,
        value: Box<Self>,
        amount: Box<Self>,
    },
    Unsupported {
        op: UnsupportedBvOp,
        width: u32,
    },
}

impl BvExpr {
    pub fn constant(bits_lsb_first: Vec<bool>) -> Self {
        Self::Constant {
            bits_lsb_first: bits_lsb_first.into_boxed_slice(),
        }
    }

    pub const fn input(symbol: BitblastSymbol, width: u32) -> Self {
        Self::Input { symbol, width }
    }

    pub fn unary(op: BvUnaryOp, value: Self) -> Self {
        Self::Unary {
            op,
            value: Box::new(value),
        }
    }

    pub fn binary(op: BvBinaryOp, left: Self, right: Self) -> Self {
        Self::Binary {
            op,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    pub fn shift(op: BvShiftOp, value: Self, amount: Self) -> Self {
        Self::Shift {
            op,
            value: Box::new(value),
            amount: Box::new(amount),
        }
    }

    pub const fn unsupported(op: UnsupportedBvOp, width: u32) -> Self {
        Self::Unsupported { op, width }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoolExpr {
    Constant(bool),
    Input(BitblastSymbol),
    Not(Box<Self>),
    Binary {
        op: BoolBinaryOp,
        left: Box<Self>,
        right: Box<Self>,
    },
    Compare {
        op: BvComparison,
        left: Box<BvExpr>,
        right: Box<BvExpr>,
    },
}

impl BoolExpr {
    pub fn logical_not(value: Self) -> Self {
        Self::Not(Box::new(value))
    }

    pub fn binary(op: BoolBinaryOp, left: Self, right: Self) -> Self {
        Self::Binary {
            op,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    pub fn compare(op: BvComparison, left: BvExpr, right: BvExpr) -> Self {
        Self::Compare {
            op,
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BitblastInputKind {
    Boolean,
    Bitvector { width: u32 },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BitblastInputBinding {
    symbol: BitblastSymbol,
    kind: BitblastInputKind,
    variables_lsb_first: Box<[VariableId]>,
}

impl BitblastInputBinding {
    pub const fn symbol(&self) -> BitblastSymbol {
        self.symbol
    }

    pub const fn kind(&self) -> BitblastInputKind {
        self.kind
    }

    pub fn variables_lsb_first(&self) -> &[VariableId] {
        &self.variables_lsb_first
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BitblastResource {
    Width,
    AstNodes,
    Depth,
    Inputs,
    Variables,
    Clauses,
    Literals,
    WorkUnits,
    EncodedBytes,
    AddressSpace,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BitblastLimits {
    pub max_width: u32,
    pub max_ast_nodes: u64,
    pub max_depth: u32,
    pub max_inputs: u32,
    pub max_variables: u32,
    pub max_clauses: u64,
    pub max_literals: u64,
    pub max_work_units: u64,
    pub schema: SchemaLimits,
}

impl Default for BitblastLimits {
    fn default() -> Self {
        Self {
            max_width: 4_096,
            max_ast_nodes: 1_000_000,
            max_depth: 512,
            max_inputs: 1_000_000,
            max_variables: 4_000_000,
            max_clauses: 32_000_000,
            max_literals: 128_000_000,
            max_work_units: 500_000_000,
            schema: SchemaLimits::default(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BitblastRefusal {
    UnsupportedConstruct {
        construct: BitblastConstruct,
        reason_code: &'static str,
    },
    WidthMismatch {
        construct: BitblastConstruct,
        left: u32,
        right: u32,
    },
    InputKindConflict {
        symbol: BitblastSymbol,
        first: BitblastInputKind,
        later: BitblastInputKind,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BitblastInconclusive {
    Cancelled,
    ResourceExhausted {
        resource: BitblastResource,
        limit: u64,
        actual: u64,
    },
    AllocationRefused {
        resource: BitblastResource,
        requested: u64,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BitblastInternalFault {
    MissingManifestRow { construct: BitblastConstruct },
    VariableIdSpaceExhausted,
    ClauseIdSpaceExhausted,
    ArithmeticOverflow { field: &'static str },
    Schema(SchemaError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BitblastFacts {
    pub ast_nodes: u64,
    pub max_depth: u32,
    pub inputs: u32,
    pub variables: u32,
    pub clauses: u64,
    pub literals: u64,
    pub work_units: u64,
    pub encoded_bytes: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BitblastArtifact {
    cnf: Cnf,
    inputs: Box<[BitblastInputBinding]>,
    facts: BitblastFacts,
}

impl BitblastArtifact {
    pub const fn manifest_id(&self) -> &'static str {
        BITBLAST_MANIFEST_ID
    }

    pub const fn manifest_version(&self) -> u16 {
        BITBLAST_MANIFEST_VERSION
    }

    pub const fn policy_id(&self) -> &'static str {
        CANONICAL_BITBLAST_POLICY_ID
    }

    pub const fn cnf(&self) -> &Cnf {
        &self.cnf
    }

    pub fn cnf_bytes(&self) -> Vec<u8> {
        self.cnf.to_canonical_bytes()
    }

    pub fn inputs(&self) -> &[BitblastInputBinding] {
        &self.inputs
    }

    pub fn input(&self, symbol: BitblastSymbol) -> Option<&BitblastInputBinding> {
        self.inputs
            .binary_search_by_key(&symbol, BitblastInputBinding::symbol)
            .ok()
            .map(|index| &self.inputs[index])
    }

    pub const fn facts(&self) -> BitblastFacts {
        self.facts
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BitblastOutcome {
    Complete(BitblastArtifact),
    Refused(BitblastRefusal),
    Inconclusive(BitblastInconclusive),
    InternalFault(BitblastInternalFault),
}

impl BitblastOutcome {
    pub const fn artifact(&self) -> Option<&BitblastArtifact> {
        match self {
            Self::Complete(artifact) => Some(artifact),
            Self::Refused(_) | Self::Inconclusive(_) | Self::InternalFault(_) => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum InputShape {
    Boolean,
    Bitvector(u32),
}

impl InputShape {
    const fn public(self) -> BitblastInputKind {
        match self {
            Self::Boolean => BitblastInputKind::Boolean,
            Self::Bitvector(width) => BitblastInputKind::Bitvector { width },
        }
    }
}

enum Stop {
    Refused(BitblastRefusal),
    Inconclusive(BitblastInconclusive),
    InternalFault(BitblastInternalFault),
}

type BlastResult<T> = Result<T, Stop>;

struct Preflight<'a, F> {
    limits: BitblastLimits,
    cancelled: &'a mut F,
    inputs: BTreeMap<BitblastSymbol, InputShape>,
    ast_nodes: u64,
    max_depth: u32,
    work_units: u64,
}

impl<'a, F> Preflight<'a, F>
where
    F: FnMut() -> bool,
{
    fn new(limits: BitblastLimits, cancelled: &'a mut F) -> Self {
        Self {
            limits,
            cancelled,
            inputs: BTreeMap::new(),
            ast_nodes: 0,
            max_depth: 0,
            work_units: 0,
        }
    }

    fn enter(&mut self, depth: u32, construct: BitblastConstruct) -> BlastResult<()> {
        self.check_cancelled()?;
        self.ast_nodes = self.ast_nodes.checked_add(1).ok_or(Stop::InternalFault(
            BitblastInternalFault::ArithmeticOverflow { field: "AST nodes" },
        ))?;
        enforce(
            BitblastResource::AstNodes,
            self.limits.max_ast_nodes,
            self.ast_nodes,
        )?;
        enforce(
            BitblastResource::Depth,
            u64::from(self.limits.max_depth),
            u64::from(depth),
        )?;
        self.max_depth = self.max_depth.max(depth);
        self.charge_work(1)?;
        let row = BITBLAST_MANIFEST.row(construct).ok_or(Stop::InternalFault(
            BitblastInternalFault::MissingManifestRow { construct },
        ))?;
        match row.support {
            BitblastSupport::Supported => Ok(()),
            BitblastSupport::Refused { code } => {
                Err(Stop::Refused(BitblastRefusal::UnsupportedConstruct {
                    construct,
                    reason_code: code,
                }))
            }
        }
    }

    fn charge_work(&mut self, amount: u64) -> BlastResult<()> {
        self.work_units = self
            .work_units
            .checked_add(amount)
            .ok_or(Stop::InternalFault(
                BitblastInternalFault::ArithmeticOverflow {
                    field: "preflight work units",
                },
            ))?;
        enforce(
            BitblastResource::WorkUnits,
            self.limits.max_work_units,
            self.work_units,
        )
    }

    fn check_cancelled(&mut self) -> BlastResult<()> {
        if (self.cancelled)() {
            Err(Stop::Inconclusive(BitblastInconclusive::Cancelled))
        } else {
            Ok(())
        }
    }

    fn width(&self, width: u64) -> BlastResult<u32> {
        enforce(
            BitblastResource::Width,
            u64::from(self.limits.max_width),
            width,
        )?;
        u32::try_from(width).map_err(|_| {
            Stop::Inconclusive(BitblastInconclusive::ResourceExhausted {
                resource: BitblastResource::Width,
                limit: u64::from(u32::MAX),
                actual: width,
            })
        })
    }

    fn bind_input(&mut self, symbol: BitblastSymbol, later: InputShape) -> BlastResult<()> {
        if let Some(first) = self.inputs.get(&symbol).copied() {
            if first != later {
                return Err(Stop::Refused(BitblastRefusal::InputKindConflict {
                    symbol,
                    first: first.public(),
                    later: later.public(),
                }));
            }
            return Ok(());
        }
        let actual = u64::try_from(self.inputs.len())
            .ok()
            .and_then(|count| count.checked_add(1))
            .ok_or(Stop::InternalFault(
                BitblastInternalFault::ArithmeticOverflow {
                    field: "input count",
                },
            ))?;
        enforce(
            BitblastResource::Inputs,
            u64::from(self.limits.max_inputs),
            actual,
        )?;
        self.inputs.insert(symbol, later);
        Ok(())
    }

    fn bool_expr(&mut self, expr: &BoolExpr, depth: u32) -> BlastResult<()> {
        match expr {
            BoolExpr::Constant(_) => self.enter(depth, BitblastConstruct::BooleanConstant),
            BoolExpr::Input(symbol) => {
                self.enter(depth, BitblastConstruct::BooleanInput)?;
                self.bind_input(*symbol, InputShape::Boolean)
            }
            BoolExpr::Not(value) => {
                self.enter(depth, BitblastConstruct::BooleanNot)?;
                self.bool_expr(value, next_depth(depth)?)
            }
            BoolExpr::Binary { op, left, right } => {
                self.enter(depth, op.construct())?;
                let child_depth = next_depth(depth)?;
                self.bool_expr(left, child_depth)?;
                self.bool_expr(right, child_depth)
            }
            BoolExpr::Compare { op, left, right } => {
                self.enter(depth, op.construct())?;
                let child_depth = next_depth(depth)?;
                let left_width = self.bv_expr(left, child_depth)?;
                let right_width = self.bv_expr(right, child_depth)?;
                same_width(op.construct(), left_width, right_width)
            }
        }
    }

    fn bv_expr(&mut self, expr: &BvExpr, depth: u32) -> BlastResult<u32> {
        match expr {
            BvExpr::Constant { bits_lsb_first } => {
                self.enter(depth, BitblastConstruct::BitvectorConstant)?;
                self.width(usize_u64(bits_lsb_first.len())?)
            }
            BvExpr::Input { symbol, width } => {
                self.enter(depth, BitblastConstruct::BitvectorInput)?;
                let width = self.width(u64::from(*width))?;
                self.bind_input(*symbol, InputShape::Bitvector(width))?;
                Ok(width)
            }
            BvExpr::Unary { op, value } => {
                self.enter(depth, op.construct())?;
                self.bv_expr(value, next_depth(depth)?)
            }
            BvExpr::Binary { op, left, right } => {
                self.enter(depth, op.construct())?;
                let child_depth = next_depth(depth)?;
                let left_width = self.bv_expr(left, child_depth)?;
                let right_width = self.bv_expr(right, child_depth)?;
                same_width(op.construct(), left_width, right_width)?;
                Ok(left_width)
            }
            BvExpr::Shift { op, value, amount } => {
                self.enter(depth, op.construct())?;
                let child_depth = next_depth(depth)?;
                let width = self.bv_expr(value, child_depth)?;
                let _amount_width = self.bv_expr(amount, child_depth)?;
                Ok(width)
            }
            BvExpr::Unsupported { op, width } => {
                self.enter(depth, op.construct())?;
                self.width(u64::from(*width))
            }
        }
    }
}

fn same_width(construct: BitblastConstruct, left: u32, right: u32) -> BlastResult<()> {
    if left == right {
        Ok(())
    } else {
        Err(Stop::Refused(BitblastRefusal::WidthMismatch {
            construct,
            left,
            right,
        }))
    }
}

fn next_depth(depth: u32) -> BlastResult<u32> {
    depth.checked_add(1).ok_or(Stop::InternalFault(
        BitblastInternalFault::ArithmeticOverflow { field: "AST depth" },
    ))
}

fn usize_u64(value: usize) -> BlastResult<u64> {
    u64::try_from(value).map_err(|_| {
        Stop::Inconclusive(BitblastInconclusive::AllocationRefused {
            resource: BitblastResource::AddressSpace,
            requested: u64::MAX,
        })
    })
}

fn enforce(resource: BitblastResource, limit: u64, actual: u64) -> BlastResult<()> {
    if actual > limit {
        Err(Stop::Inconclusive(
            BitblastInconclusive::ResourceExhausted {
                resource,
                limit,
                actual,
            },
        ))
    } else {
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Wire {
    Constant(bool),
    Literal(Literal),
}

impl Wire {
    const fn negate(self) -> Self {
        match self {
            Self::Constant(value) => Self::Constant(!value),
            Self::Literal(literal) => Self::Literal(Literal::new(
                literal.variable(),
                match literal.polarity() {
                    Polarity::Negative => Polarity::Positive,
                    Polarity::Positive => Polarity::Negative,
                },
            )),
        }
    }
}

#[derive(Debug)]
enum PendingInput {
    Boolean(VariableId),
    Bitvector(Box<[VariableId]>),
}

struct Translator<'a, F> {
    limits: BitblastLimits,
    cancelled: &'a mut F,
    inputs: BTreeMap<BitblastSymbol, PendingInput>,
    clauses: Vec<InputClause>,
    next_variable: u64,
    next_clause: u64,
    ast_nodes: u64,
    max_depth: u32,
    work_units: u64,
    literal_count: u64,
}

impl<'a, F> Translator<'a, F>
where
    F: FnMut() -> bool,
{
    fn new(
        limits: BitblastLimits,
        cancelled: &'a mut F,
        ast_nodes: u64,
        max_depth: u32,
        work_units: u64,
    ) -> Self {
        Self {
            limits,
            cancelled,
            inputs: BTreeMap::new(),
            clauses: Vec::new(),
            next_variable: 1,
            next_clause: 1,
            ast_nodes,
            max_depth,
            work_units,
            literal_count: 0,
        }
    }

    fn check_cancelled(&mut self) -> BlastResult<()> {
        if (self.cancelled)() {
            Err(Stop::Inconclusive(BitblastInconclusive::Cancelled))
        } else {
            Ok(())
        }
    }

    fn charge_work(&mut self, amount: u64) -> BlastResult<()> {
        self.check_cancelled()?;
        self.work_units = self
            .work_units
            .checked_add(amount)
            .ok_or(Stop::InternalFault(
                BitblastInternalFault::ArithmeticOverflow {
                    field: "translation work units",
                },
            ))?;
        enforce(
            BitblastResource::WorkUnits,
            self.limits.max_work_units,
            self.work_units,
        )
    }

    fn allocate_variable(&mut self) -> BlastResult<VariableId> {
        self.charge_work(1)?;
        let effective_limit = self
            .limits
            .max_variables
            .min(self.limits.schema.max_variables);
        enforce(
            BitblastResource::Variables,
            u64::from(effective_limit),
            self.next_variable,
        )?;
        let raw = u32::try_from(self.next_variable)
            .map_err(|_| Stop::InternalFault(BitblastInternalFault::VariableIdSpaceExhausted))?;
        let variable = VariableId::new(raw)
            .map_err(|error| Stop::InternalFault(BitblastInternalFault::Schema(error)))?;
        self.next_variable = self
            .next_variable
            .checked_add(1)
            .ok_or(Stop::InternalFault(
                BitblastInternalFault::VariableIdSpaceExhausted,
            ))?;
        Ok(variable)
    }

    fn emit_clause(&mut self, wires: &[Wire]) -> BlastResult<()> {
        self.charge_work(1)?;
        let actual_clauses = self.next_clause.checked_add(0).ok_or(Stop::InternalFault(
            BitblastInternalFault::ClauseIdSpaceExhausted,
        ))?;
        let effective_clause_limit = self.limits.max_clauses.min(self.limits.schema.max_clauses);
        enforce(
            BitblastResource::Clauses,
            effective_clause_limit,
            actual_clauses,
        )?;

        let mut literals = Vec::new();
        literals.try_reserve(wires.len()).map_err(|_| {
            Stop::Inconclusive(BitblastInconclusive::AllocationRefused {
                resource: BitblastResource::Literals,
                requested: usize_u64(wires.len()).unwrap_or(u64::MAX),
            })
        })?;
        for wire in wires {
            match wire {
                Wire::Constant(true) => return Ok(()),
                Wire::Constant(false) => {}
                Wire::Literal(literal) => literals.push(*literal),
            }
        }
        let clause = Clause::new(literals)
            .map_err(|error| Stop::InternalFault(BitblastInternalFault::Schema(error)))?;
        let added_literals = usize_u64(clause.literals().len())?;
        let actual_literals =
            self.literal_count
                .checked_add(added_literals)
                .ok_or(Stop::InternalFault(
                    BitblastInternalFault::ArithmeticOverflow {
                        field: "CNF literal count",
                    },
                ))?;
        let effective_literal_limit = self
            .limits
            .max_literals
            .min(self.limits.schema.max_literals);
        enforce(
            BitblastResource::Literals,
            effective_literal_limit,
            actual_literals,
        )?;
        self.clauses.try_reserve(1).map_err(|_| {
            Stop::Inconclusive(BitblastInconclusive::AllocationRefused {
                resource: BitblastResource::Clauses,
                requested: actual_clauses,
            })
        })?;
        let id = ClauseId::new(self.next_clause)
            .map_err(|error| Stop::InternalFault(BitblastInternalFault::Schema(error)))?;
        self.clauses.push(InputClause::new(id, clause));
        self.literal_count = actual_literals;
        self.next_clause = self.next_clause.checked_add(1).ok_or(Stop::InternalFault(
            BitblastInternalFault::ClauseIdSpaceExhausted,
        ))?;
        Ok(())
    }

    fn fresh_wire(&mut self) -> BlastResult<Wire> {
        Ok(Wire::Literal(Literal::new(
            self.allocate_variable()?,
            Polarity::Positive,
        )))
    }

    fn and(&mut self, left: Wire, right: Wire) -> BlastResult<Wire> {
        self.charge_work(1)?;
        match (left, right) {
            (Wire::Constant(false), _) | (_, Wire::Constant(false)) => Ok(Wire::Constant(false)),
            (Wire::Constant(true), value) | (value, Wire::Constant(true)) => Ok(value),
            (left, right) if left == right => Ok(left),
            (left, right) if left == right.negate() => Ok(Wire::Constant(false)),
            (left, right) => {
                let output = self.fresh_wire()?;
                self.emit_clause(&[output.negate(), left])?;
                self.emit_clause(&[output.negate(), right])?;
                self.emit_clause(&[output, left.negate(), right.negate()])?;
                Ok(output)
            }
        }
    }

    fn or(&mut self, left: Wire, right: Wire) -> BlastResult<Wire> {
        self.charge_work(1)?;
        match (left, right) {
            (Wire::Constant(true), _) | (_, Wire::Constant(true)) => Ok(Wire::Constant(true)),
            (Wire::Constant(false), value) | (value, Wire::Constant(false)) => Ok(value),
            (left, right) if left == right => Ok(left),
            (left, right) if left == right.negate() => Ok(Wire::Constant(true)),
            (left, right) => {
                let output = self.fresh_wire()?;
                self.emit_clause(&[output, left.negate()])?;
                self.emit_clause(&[output, right.negate()])?;
                self.emit_clause(&[output.negate(), left, right])?;
                Ok(output)
            }
        }
    }

    fn xor(&mut self, left: Wire, right: Wire) -> BlastResult<Wire> {
        self.charge_work(1)?;
        match (left, right) {
            (Wire::Constant(false), value) | (value, Wire::Constant(false)) => Ok(value),
            (Wire::Constant(true), value) | (value, Wire::Constant(true)) => Ok(value.negate()),
            (left, right) if left == right => Ok(Wire::Constant(false)),
            (left, right) if left == right.negate() => Ok(Wire::Constant(true)),
            (left, right) => {
                let output = self.fresh_wire()?;
                self.emit_clause(&[left.negate(), right.negate(), output.negate()])?;
                self.emit_clause(&[left, right, output.negate()])?;
                self.emit_clause(&[left, right.negate(), output])?;
                self.emit_clause(&[left.negate(), right, output])?;
                Ok(output)
            }
        }
    }

    fn iff(&mut self, left: Wire, right: Wire) -> BlastResult<Wire> {
        Ok(self.xor(left, right)?.negate())
    }

    fn mux(&mut self, condition: Wire, when_true: Wire, when_false: Wire) -> BlastResult<Wire> {
        if when_true == when_false {
            return Ok(when_true);
        }
        match condition {
            Wire::Constant(true) => Ok(when_true),
            Wire::Constant(false) => Ok(when_false),
            condition => {
                let selected_true = self.and(condition, when_true)?;
                let selected_false = self.and(condition.negate(), when_false)?;
                self.or(selected_true, selected_false)
            }
        }
    }

    fn bool_input(&mut self, symbol: BitblastSymbol) -> BlastResult<Wire> {
        if let Some(binding) = self.inputs.get(&symbol) {
            return match binding {
                PendingInput::Boolean(variable) => {
                    Ok(Wire::Literal(Literal::new(*variable, Polarity::Positive)))
                }
                PendingInput::Bitvector(variables) => {
                    Err(Stop::Refused(BitblastRefusal::InputKindConflict {
                        symbol,
                        first: BitblastInputKind::Bitvector {
                            width: u32::try_from(variables.len()).unwrap_or(u32::MAX),
                        },
                        later: BitblastInputKind::Boolean,
                    }))
                }
            };
        }
        let variable = self.allocate_variable()?;
        self.inputs.insert(symbol, PendingInput::Boolean(variable));
        Ok(Wire::Literal(Literal::new(variable, Polarity::Positive)))
    }

    fn bv_input(&mut self, symbol: BitblastSymbol, width: u32) -> BlastResult<Vec<Wire>> {
        if let Some(binding) = self.inputs.get(&symbol) {
            return match binding {
                PendingInput::Boolean(_) => {
                    Err(Stop::Refused(BitblastRefusal::InputKindConflict {
                        symbol,
                        first: BitblastInputKind::Boolean,
                        later: BitblastInputKind::Bitvector { width },
                    }))
                }
                PendingInput::Bitvector(variables) => {
                    let first_width = u32::try_from(variables.len()).unwrap_or(u32::MAX);
                    if first_width != width {
                        return Err(Stop::Refused(BitblastRefusal::InputKindConflict {
                            symbol,
                            first: BitblastInputKind::Bitvector { width: first_width },
                            later: BitblastInputKind::Bitvector { width },
                        }));
                    }
                    let mut wires = fallible_vec(variables.len(), BitblastResource::Variables)?;
                    wires.extend(
                        variables.iter().copied().map(|variable| {
                            Wire::Literal(Literal::new(variable, Polarity::Positive))
                        }),
                    );
                    Ok(wires)
                }
            };
        }

        let width_usize = usize::try_from(width).map_err(|_| {
            Stop::Inconclusive(BitblastInconclusive::AllocationRefused {
                resource: BitblastResource::AddressSpace,
                requested: u64::from(width),
            })
        })?;
        let mut variables = fallible_vec(width_usize, BitblastResource::Variables)?;
        let mut wires = fallible_vec(width_usize, BitblastResource::Variables)?;
        for _ in 0..width {
            let variable = self.allocate_variable()?;
            variables.push(variable);
            wires.push(Wire::Literal(Literal::new(variable, Polarity::Positive)));
        }
        self.inputs.insert(
            symbol,
            PendingInput::Bitvector(variables.into_boxed_slice()),
        );
        Ok(wires)
    }

    fn bool_expr(&mut self, expr: &BoolExpr) -> BlastResult<Wire> {
        self.check_cancelled()?;
        match expr {
            BoolExpr::Constant(value) => Ok(Wire::Constant(*value)),
            BoolExpr::Input(symbol) => self.bool_input(*symbol),
            BoolExpr::Not(value) => Ok(self.bool_expr(value)?.negate()),
            BoolExpr::Binary { op, left, right } => {
                let left = self.bool_expr(left)?;
                let right = self.bool_expr(right)?;
                match op {
                    BoolBinaryOp::And => self.and(left, right),
                    BoolBinaryOp::Or => self.or(left, right),
                    BoolBinaryOp::Xor => self.xor(left, right),
                    BoolBinaryOp::Implication => self.or(left.negate(), right),
                    BoolBinaryOp::Iff => self.iff(left, right),
                }
            }
            BoolExpr::Compare { op, left, right } => {
                let left = self.bv_expr(left)?;
                let right = self.bv_expr(right)?;
                self.compare(*op, &left, &right)
            }
        }
    }

    fn bv_expr(&mut self, expr: &BvExpr) -> BlastResult<Vec<Wire>> {
        self.check_cancelled()?;
        match expr {
            BvExpr::Constant { bits_lsb_first } => {
                let mut wires = fallible_vec(bits_lsb_first.len(), BitblastResource::Variables)?;
                wires.extend(bits_lsb_first.iter().copied().map(Wire::Constant));
                Ok(wires)
            }
            BvExpr::Input { symbol, width } => self.bv_input(*symbol, *width),
            BvExpr::Unary { op, value } => {
                let value = self.bv_expr(value)?;
                match op {
                    BvUnaryOp::Not => {
                        let mut output = fallible_vec(value.len(), BitblastResource::Variables)?;
                        output.extend(value.into_iter().map(Wire::negate));
                        Ok(output)
                    }
                    BvUnaryOp::Negate => {
                        let zeros = constant_wires(value.len(), false)?;
                        self.subtract_vectors(&zeros, &value)
                    }
                }
            }
            BvExpr::Binary { op, left, right } => {
                let left = self.bv_expr(left)?;
                let right = self.bv_expr(right)?;
                match op {
                    BvBinaryOp::And => self.pointwise(&left, &right, Self::and),
                    BvBinaryOp::Or => self.pointwise(&left, &right, Self::or),
                    BvBinaryOp::Xor => self.pointwise(&left, &right, Self::xor),
                    BvBinaryOp::Add => self.add_vectors(&left, &right, Wire::Constant(false)),
                    BvBinaryOp::Subtract => self.subtract_vectors(&left, &right),
                    BvBinaryOp::Multiply => self.multiply_vectors(&left, &right),
                }
            }
            BvExpr::Shift { op, value, amount } => {
                let value = self.bv_expr(value)?;
                let amount = self.bv_expr(amount)?;
                self.shift_vector(*op, value, &amount)
            }
            BvExpr::Unsupported { op, .. } => {
                let construct = op.construct();
                let row = BITBLAST_MANIFEST.row(construct).ok_or(Stop::InternalFault(
                    BitblastInternalFault::MissingManifestRow { construct },
                ))?;
                let BitblastSupport::Refused { code } = row.support else {
                    return Err(Stop::InternalFault(
                        BitblastInternalFault::MissingManifestRow { construct },
                    ));
                };
                Err(Stop::Refused(BitblastRefusal::UnsupportedConstruct {
                    construct,
                    reason_code: code,
                }))
            }
        }
    }

    fn pointwise(
        &mut self,
        left: &[Wire],
        right: &[Wire],
        operation: fn(&mut Self, Wire, Wire) -> BlastResult<Wire>,
    ) -> BlastResult<Vec<Wire>> {
        if left.len() != right.len() {
            return Err(Stop::InternalFault(
                BitblastInternalFault::ArithmeticOverflow {
                    field: "preflight width agreement",
                },
            ));
        }
        let mut output = fallible_vec(left.len(), BitblastResource::Variables)?;
        for (left, right) in left.iter().copied().zip(right.iter().copied()) {
            output.push(operation(self, left, right)?);
        }
        Ok(output)
    }

    fn add_vectors(
        &mut self,
        left: &[Wire],
        right: &[Wire],
        mut carry: Wire,
    ) -> BlastResult<Vec<Wire>> {
        if left.len() != right.len() {
            return Err(Stop::InternalFault(
                BitblastInternalFault::ArithmeticOverflow {
                    field: "preflight addition width agreement",
                },
            ));
        }
        let mut output = fallible_vec(left.len(), BitblastResource::Variables)?;
        for (left, right) in left.iter().copied().zip(right.iter().copied()) {
            let pair_xor = self.xor(left, right)?;
            output.push(self.xor(pair_xor, carry)?);
            let both = self.and(left, right)?;
            let carry_pair = self.and(carry, pair_xor)?;
            carry = self.or(both, carry_pair)?;
        }
        Ok(output)
    }

    fn subtract_vectors(&mut self, left: &[Wire], right: &[Wire]) -> BlastResult<Vec<Wire>> {
        let mut complement = fallible_vec(right.len(), BitblastResource::Variables)?;
        complement.extend(right.iter().copied().map(Wire::negate));
        self.add_vectors(left, &complement, Wire::Constant(true))
    }

    fn multiply_vectors(&mut self, left: &[Wire], right: &[Wire]) -> BlastResult<Vec<Wire>> {
        if left.len() != right.len() {
            return Err(Stop::InternalFault(
                BitblastInternalFault::ArithmeticOverflow {
                    field: "preflight multiplication width agreement",
                },
            ));
        }
        let width = left.len();
        let mut result = constant_wires(width, false)?;
        for (right_index, right_bit) in right.iter().copied().enumerate() {
            let mut partial = constant_wires(width, false)?;
            for output_index in right_index..width {
                partial[output_index] = self.and(left[output_index - right_index], right_bit)?;
            }
            result = self.add_vectors(&result, &partial, Wire::Constant(false))?;
        }
        Ok(result)
    }

    fn shift_vector(
        &mut self,
        op: BvShiftOp,
        mut value: Vec<Wire>,
        amount: &[Wire],
    ) -> BlastResult<Vec<Wire>> {
        let width = value.len();
        for (stage, condition) in amount.iter().copied().enumerate() {
            let distance = if stage >= u32::BITS as usize {
                None
            } else {
                1_usize.checked_shl(stage as u32)
            };
            let sign = value.last().copied().unwrap_or(Wire::Constant(false));
            let mut shifted = fallible_vec(width, BitblastResource::Variables)?;
            for index in 0..width {
                let source = match op {
                    BvShiftOp::Left => distance
                        .and_then(|distance| index.checked_sub(distance))
                        .and_then(|source| value.get(source).copied())
                        .unwrap_or(Wire::Constant(false)),
                    BvShiftOp::LogicalRight => distance
                        .and_then(|distance| index.checked_add(distance))
                        .and_then(|source| value.get(source).copied())
                        .unwrap_or(Wire::Constant(false)),
                    BvShiftOp::ArithmeticRight => distance
                        .and_then(|distance| index.checked_add(distance))
                        .and_then(|source| value.get(source).copied())
                        .unwrap_or(sign),
                };
                shifted.push(source);
            }
            let mut selected = fallible_vec(width, BitblastResource::Variables)?;
            for (shifted, original) in shifted.into_iter().zip(value) {
                selected.push(self.mux(condition, shifted, original)?);
            }
            value = selected;
        }
        Ok(value)
    }

    fn equal_vectors(&mut self, left: &[Wire], right: &[Wire]) -> BlastResult<Wire> {
        if left.len() != right.len() {
            return Err(Stop::InternalFault(
                BitblastInternalFault::ArithmeticOverflow {
                    field: "preflight equality width agreement",
                },
            ));
        }
        let mut equal = Wire::Constant(true);
        for (left, right) in left.iter().copied().zip(right.iter().copied()) {
            let bit_equal = self.iff(left, right)?;
            equal = self.and(equal, bit_equal)?;
        }
        Ok(equal)
    }

    fn unsigned_less(&mut self, left: &[Wire], right: &[Wire]) -> BlastResult<Wire> {
        if left.len() != right.len() {
            return Err(Stop::InternalFault(
                BitblastInternalFault::ArithmeticOverflow {
                    field: "preflight comparison width agreement",
                },
            ));
        }
        let mut less = Wire::Constant(false);
        let mut prefix_equal = Wire::Constant(true);
        for (left, right) in left.iter().copied().zip(right.iter().copied()).rev() {
            let bit_less = self.and(left.negate(), right)?;
            let first_difference_less = self.and(prefix_equal, bit_less)?;
            less = self.or(less, first_difference_less)?;
            let bit_equal = self.iff(left, right)?;
            prefix_equal = self.and(prefix_equal, bit_equal)?;
        }
        Ok(less)
    }

    fn signed_less(&mut self, left: &[Wire], right: &[Wire]) -> BlastResult<Wire> {
        if left.is_empty() && right.is_empty() {
            return Ok(Wire::Constant(false));
        }
        let left_sign = left.last().copied().ok_or(Stop::InternalFault(
            BitblastInternalFault::ArithmeticOverflow {
                field: "signed comparison left width",
            },
        ))?;
        let right_sign = right.last().copied().ok_or(Stop::InternalFault(
            BitblastInternalFault::ArithmeticOverflow {
                field: "signed comparison right width",
            },
        ))?;
        let signs_differ = self.xor(left_sign, right_sign)?;
        let unsigned = self.unsigned_less(left, right)?;
        self.mux(signs_differ, left_sign, unsigned)
    }

    fn compare(&mut self, op: BvComparison, left: &[Wire], right: &[Wire]) -> BlastResult<Wire> {
        let equal = self.equal_vectors(left, right)?;
        match op {
            BvComparison::Equal => Ok(equal),
            BvComparison::NotEqual => Ok(equal.negate()),
            BvComparison::UnsignedLessThan => self.unsigned_less(left, right),
            BvComparison::UnsignedLessOrEqual => {
                let less = self.unsigned_less(left, right)?;
                self.or(less, equal)
            }
            BvComparison::UnsignedGreaterThan => self.unsigned_less(right, left),
            BvComparison::UnsignedGreaterOrEqual => {
                let greater = self.unsigned_less(right, left)?;
                self.or(greater, equal)
            }
            BvComparison::SignedLessThan => self.signed_less(left, right),
            BvComparison::SignedLessOrEqual => {
                let less = self.signed_less(left, right)?;
                self.or(less, equal)
            }
            BvComparison::SignedGreaterThan => self.signed_less(right, left),
            BvComparison::SignedGreaterOrEqual => {
                let greater = self.signed_less(right, left)?;
                self.or(greater, equal)
            }
        }
    }

    fn assert_root(&mut self, root: Wire) -> BlastResult<()> {
        match root {
            Wire::Constant(true) => Ok(()),
            Wire::Constant(false) => self.emit_clause(&[]),
            root => self.emit_clause(&[root]),
        }
    }

    fn finish(self) -> BlastResult<BitblastArtifact> {
        let variable_count = self
            .next_variable
            .checked_sub(1)
            .and_then(|value| u32::try_from(value).ok())
            .ok_or(Stop::InternalFault(
                BitblastInternalFault::VariableIdSpaceExhausted,
            ))?;
        let clause_count = self.next_clause.checked_sub(1).ok_or(Stop::InternalFault(
            BitblastInternalFault::ClauseIdSpaceExhausted,
        ))?;
        let encoded_bytes = 25_u64
            .checked_add(clause_count.checked_mul(16).ok_or(Stop::InternalFault(
                BitblastInternalFault::ArithmeticOverflow {
                    field: "CNF clause byte width",
                },
            ))?)
            .and_then(|bytes| {
                self.literal_count
                    .checked_mul(5)
                    .and_then(|literal_bytes| bytes.checked_add(literal_bytes))
            })
            .ok_or(Stop::InternalFault(
                BitblastInternalFault::ArithmeticOverflow {
                    field: "CNF encoded bytes",
                },
            ))?;
        enforce(
            BitblastResource::EncodedBytes,
            self.limits.schema.max_encoded_bytes,
            encoded_bytes,
        )?;

        let cnf = Cnf::new(variable_count, self.clauses, self.limits.schema)
            .map_err(|error| Stop::InternalFault(BitblastInternalFault::Schema(error)))?;
        let input_count = u32::try_from(self.inputs.len()).map_err(|_| {
            Stop::InternalFault(BitblastInternalFault::ArithmeticOverflow {
                field: "published input count",
            })
        })?;
        let mut inputs = fallible_vec(self.inputs.len(), BitblastResource::Inputs)?;
        for (symbol, binding) in self.inputs {
            match binding {
                PendingInput::Boolean(variable) => {
                    inputs.push(BitblastInputBinding {
                        symbol,
                        kind: BitblastInputKind::Boolean,
                        variables_lsb_first: Box::new([variable]),
                    });
                }
                PendingInput::Bitvector(variables) => {
                    let width = u32::try_from(variables.len()).map_err(|_| {
                        Stop::InternalFault(BitblastInternalFault::ArithmeticOverflow {
                            field: "published bitvector width",
                        })
                    })?;
                    inputs.push(BitblastInputBinding {
                        symbol,
                        kind: BitblastInputKind::Bitvector { width },
                        variables_lsb_first: variables,
                    });
                }
            }
        }
        Ok(BitblastArtifact {
            facts: BitblastFacts {
                ast_nodes: self.ast_nodes,
                max_depth: self.max_depth,
                inputs: input_count,
                variables: variable_count,
                clauses: clause_count,
                literals: self.literal_count,
                work_units: self.work_units,
                encoded_bytes,
            },
            cnf,
            inputs: inputs.into_boxed_slice(),
        })
    }
}

fn constant_wires(width: usize, value: bool) -> BlastResult<Vec<Wire>> {
    let mut wires = fallible_vec(width, BitblastResource::Variables)?;
    wires.resize(width, Wire::Constant(value));
    Ok(wires)
}

fn fallible_vec<T>(capacity: usize, resource: BitblastResource) -> BlastResult<Vec<T>> {
    let mut values = Vec::new();
    values.try_reserve(capacity).map_err(|_| {
        Stop::Inconclusive(BitblastInconclusive::AllocationRefused {
            resource,
            requested: u64::try_from(capacity).unwrap_or(u64::MAX),
        })
    })?;
    Ok(values)
}

fn outcome<T>(
    result: BlastResult<T>,
    complete: impl FnOnce(T) -> BitblastOutcome,
) -> BitblastOutcome {
    match result {
        Ok(value) => complete(value),
        Err(stop) => stopped(stop),
    }
}

fn stopped(stop: Stop) -> BitblastOutcome {
    match stop {
        Stop::Refused(refusal) => BitblastOutcome::Refused(refusal),
        Stop::Inconclusive(inconclusive) => BitblastOutcome::Inconclusive(inconclusive),
        Stop::InternalFault(fault) => BitblastOutcome::InternalFault(fault),
    }
}

/// Translate one proposition under the frozen v1 manifest and canonical policy.
pub fn bitblast(expr: &BoolExpr, limits: BitblastLimits) -> BitblastOutcome {
    bitblast_with_cancel(expr, limits, || false)
}

/// As [`bitblast`], observing cancellation at deterministic work boundaries.
pub fn bitblast_with_cancel<F>(
    expr: &BoolExpr,
    limits: BitblastLimits,
    mut cancelled: F,
) -> BitblastOutcome
where
    F: FnMut() -> bool,
{
    let preflight_result = {
        let mut preflight = Preflight::new(limits, &mut cancelled);
        match preflight.bool_expr(expr, 1) {
            Ok(()) => Ok((
                preflight.ast_nodes,
                preflight.max_depth,
                preflight.work_units,
            )),
            Err(stop) => Err(stop),
        }
    };
    let (ast_nodes, max_depth, work_units) = match preflight_result {
        Ok(facts) => facts,
        Err(stop) => return stopped(stop),
    };

    let mut translator = Translator::new(limits, &mut cancelled, ast_nodes, max_depth, work_units);
    let result = translator
        .bool_expr(expr)
        .and_then(|root| translator.assert_root(root))
        .and_then(|()| translator.finish());
    outcome(result, BitblastOutcome::Complete)
}
