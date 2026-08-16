//! Checker-owned values and decoder for the shared canonical term schemas.
//!
//! Only the frozen schema identities are imported from `fln-hash`. The parser,
//! arenas, budgets, cancellation checkpoints, and error taxonomy live here. In
//! particular, successful decoding never constructs `fln-core` expression or level
//! heap nodes. Flat arenas also make destruction independent of input nesting.

use fln_hash::canon::{SCHEMA_EXPR, SCHEMA_LEVEL, SCHEMA_NAME, SchemaId};

const MAX_LEVEL_DEPTH: u32 = 16_777_215;
// The packed covenant stores `index + 1` in 20 bits, so the largest index is
// one below the largest representable span.
pub(crate) const MAX_BVAR_INDEX: u32 = (1 << 20) - 2;

const NAME_ANON: u8 = 0;
const NAME_STR: u8 = 1;
const NAME_NUM: u8 = 2;
const NAME_NUM_OVERFLOW: u8 = 3;

const LEVEL_ZERO: u8 = 0;
const LEVEL_SUCC: u8 = 1;
const LEVEL_MAX: u8 = 2;
const LEVEL_IMAX: u8 = 3;
const LEVEL_PARAM: u8 = 4;
const LEVEL_MVAR: u8 = 5;

const EXPR_BVAR: u8 = 0;
const EXPR_FVAR: u8 = 1;
const EXPR_MVAR: u8 = 2;
const EXPR_SORT: u8 = 3;
const EXPR_CONST: u8 = 4;
const EXPR_APP: u8 = 5;
const EXPR_LAM: u8 = 6;
const EXPR_FORALL: u8 = 7;
const EXPR_LET: u8 = 8;
const EXPR_LIT_NAT: u8 = 9;
const EXPR_LIT_STR: u8 = 10;
const EXPR_MDATA: u8 = 11;
const EXPR_PROJ: u8 = 12;

const DATA_STRING: u8 = 0;
const DATA_BOOL: u8 = 1;
const DATA_NAME: u8 = 2;
const DATA_NAT: u8 = 3;
const DATA_INT: u8 = 4;
const DATA_SYNTAX: u8 = 5;

/// One component of a hierarchical Lean name.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum NamePart {
    Numeric { value: u64, overflowed: bool },
    Text(String),
}

/// Checker-owned name representation: root-to-leaf components, no cached hash.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct WireName {
    parts: Vec<NamePart>,
}

impl WireName {
    pub fn parts(&self) -> &[NamePart] {
        &self.parts
    }

    pub fn is_anonymous(&self) -> bool {
        self.parts.is_empty()
    }

    pub(crate) fn from_parts(parts: Vec<NamePart>) -> WireName {
        WireName { parts }
    }
}

/// Lean's `Name.lt`: compare outer leaf constructors before prefixes, but compare
/// prefixes before component values when those constructors agree.
///
/// The parts are stored root-to-leaf, so a derived `Vec` order would be wrong for
/// names such as `z.1` and `a.x`: numeric leaves sort before string leaves without
/// consulting those prefixes. The first pass checks constructors leaf-to-root; only
/// when all constructors and lengths agree may values be compared root-to-leaf.
impl Ord for WireName {
    fn cmp(&self, other: &WireName) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        let mut left = self.parts.len();
        let mut right = other.parts.len();
        while left > 0 && right > 0 {
            match (&self.parts[left - 1], &other.parts[right - 1]) {
                (NamePart::Numeric { .. }, NamePart::Text(_)) => return Ordering::Less,
                (NamePart::Text(_), NamePart::Numeric { .. }) => return Ordering::Greater,
                (NamePart::Numeric { .. }, NamePart::Numeric { .. })
                | (NamePart::Text(_), NamePart::Text(_)) => {
                    left -= 1;
                    right -= 1;
                }
            }
        }
        match left.cmp(&right) {
            Ordering::Equal => self.parts.iter().cmp(other.parts.iter()),
            order => order,
        }
    }
}

impl PartialOrd for WireName {
    fn partial_cmp(&self, other: &WireName) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Index into a [`WireLevel`] arena.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LevelId(u32);

impl LevelId {
    pub(crate) const ZERO: LevelId = LevelId(0);

    pub const fn index(self) -> usize {
        self.0 as usize
    }

    pub(crate) fn from_index(index: usize) -> Option<LevelId> {
        (index < u32::MAX as usize).then_some(LevelId(index as u32))
    }
}

/// Checker-owned universe node. Child references always point backward in the arena.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LevelNode {
    Zero,
    Succ(LevelId),
    Max(LevelId, LevelId),
    IMax(LevelId, LevelId),
    Parameter(WireName),
    Meta(WireName),
}

/// One independently decoded universe value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WireLevel {
    nodes: Vec<LevelNode>,
    root: LevelId,
}

impl WireLevel {
    pub fn nodes(&self) -> &[LevelNode] {
        &self.nodes
    }

    pub const fn root(&self) -> LevelId {
        self.root
    }

    pub fn node(&self, id: LevelId) -> Option<&LevelNode> {
        self.nodes.get(id.index())
    }

    pub(crate) fn from_parts(nodes: Vec<LevelNode>, root: LevelId) -> WireLevel {
        WireLevel { nodes, root }
    }
}

/// Index into a [`WireExpr`] term arena.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExprId(u32);

impl ExprId {
    pub(crate) const ZERO: ExprId = ExprId(0);

    pub const fn index(self) -> usize {
        self.0 as usize
    }

    pub(crate) fn from_index(index: usize) -> Option<ExprId> {
        (index < u32::MAX as usize).then_some(ExprId(index as u32))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinderStyle {
    Default,
    Implicit,
    StrictImplicit,
    InstanceImplicit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MetadataValue {
    Text(String),
    Bool(bool),
    Name(WireName),
    Nat(u64),
    Int(i64),
    Syntax(u64),
}

/// Checker-owned expression node. Recursive shape is represented by arena indexes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprNode {
    Bound {
        index: u32,
    },
    Free {
        name: WireName,
    },
    Meta {
        name: WireName,
    },
    Sort {
        level: LevelId,
    },
    Constant {
        name: WireName,
        levels: Vec<LevelId>,
    },
    Apply {
        function: ExprId,
        argument: ExprId,
    },
    Lambda {
        binder_name: WireName,
        binder_type: ExprId,
        body: ExprId,
        style: BinderStyle,
    },
    Forall {
        binder_name: WireName,
        binder_type: ExprId,
        body: ExprId,
        style: BinderStyle,
    },
    Let {
        declaration_name: WireName,
        type_: ExprId,
        value: ExprId,
        body: ExprId,
        non_dependent: bool,
    },
    NatLiteral {
        limbs_le: Vec<u64>,
    },
    StringLiteral(String),
    Metadata {
        entries: Vec<(WireName, MetadataValue)>,
        expression: ExprId,
    },
    Projection {
        structure_name: WireName,
        index: u64,
        expression: ExprId,
    },
}

pub(crate) fn usize_units(value: usize) -> u64 {
    u64::try_from(value).unwrap_or(u64::MAX)
}

pub(crate) fn name_owned_units(name: &WireName) -> u64 {
    name.parts().iter().fold(0u64, |units, part| {
        let payload = match part {
            NamePart::Numeric { .. } => 0,
            NamePart::Text(text) => usize_units(text.len()),
        };
        units.saturating_add(1).saturating_add(payload)
    })
}

fn metadata_owned_units(value: &MetadataValue) -> u64 {
    match value {
        MetadataValue::Text(text) => usize_units(text.len()),
        MetadataValue::Name(name) => name_owned_units(name),
        MetadataValue::Bool(_)
        | MetadataValue::Nat(_)
        | MetadataValue::Int(_)
        | MetadataValue::Syntax(_) => 0,
    }
}

pub(crate) fn level_owned_units(node: &LevelNode) -> u64 {
    1u64.saturating_add(match node {
        LevelNode::Parameter(name) | LevelNode::Meta(name) => name_owned_units(name),
        LevelNode::Zero | LevelNode::Succ(_) | LevelNode::Max(_, _) | LevelNode::IMax(_, _) => 0,
    })
}

pub(crate) fn expression_owned_units(node: &ExprNode) -> u64 {
    let payload = match node {
        ExprNode::Bound { .. } | ExprNode::Sort { .. } | ExprNode::Apply { .. } => 0,
        ExprNode::Free { name } | ExprNode::Meta { name } => name_owned_units(name),
        ExprNode::Constant { name, levels } => {
            name_owned_units(name).saturating_add(usize_units(levels.len()))
        }
        ExprNode::Lambda { binder_name, .. } | ExprNode::Forall { binder_name, .. } => {
            name_owned_units(binder_name)
        }
        ExprNode::Let {
            declaration_name, ..
        } => name_owned_units(declaration_name),
        ExprNode::NatLiteral { limbs_le } => usize_units(limbs_le.len()),
        ExprNode::StringLiteral(text) => usize_units(text.len()),
        ExprNode::Metadata { entries, .. } => entries.iter().fold(0u64, |units, (name, value)| {
            units
                .saturating_add(1)
                .saturating_add(name_owned_units(name))
                .saturating_add(metadata_owned_units(value))
        }),
        ExprNode::Projection { structure_name, .. } => name_owned_units(structure_name),
    };
    1u64.saturating_add(payload)
}

/// One independently decoded expression and all levels embedded in it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WireExpr {
    nodes: Vec<ExprNode>,
    levels: Vec<LevelNode>,
    root: ExprId,
}

impl WireExpr {
    pub fn nodes(&self) -> &[ExprNode] {
        &self.nodes
    }

    pub fn levels(&self) -> &[LevelNode] {
        &self.levels
    }

    pub const fn root(&self) -> ExprId {
        self.root
    }

    pub fn node(&self, id: ExprId) -> Option<&ExprNode> {
        self.nodes.get(id.index())
    }

    pub fn level(&self, id: LevelId) -> Option<&LevelNode> {
        self.levels.get(id.index())
    }

    pub(crate) fn from_parts(
        nodes: Vec<ExprNode>,
        levels: Vec<LevelNode>,
        root: ExprId,
    ) -> WireExpr {
        WireExpr {
            nodes,
            levels,
            root,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DecodeLimit {
    InputBytes,
    ProducedUnits,
}

/// Caller-owned limits for one decode.
///
/// Produced units count arena nodes, name components, metadata entries, and
/// arbitrary-precision natural limbs. Input bytes are admitted as one bounded
/// slice before semantic parsing starts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DecodeBudget {
    pub max_input_bytes: u64,
    pub max_produced_units: u64,
}

impl DecodeBudget {
    pub const fn new(max_input_bytes: u64, max_produced_units: u64) -> DecodeBudget {
        DecodeBudget {
            max_input_bytes,
            max_produced_units,
        }
    }

    pub const fn unlimited() -> DecodeBudget {
        DecodeBudget::new(u64::MAX, u64::MAX)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodeStop {
    Resource {
        limit: DecodeLimit,
        allowed: u64,
        observed: u64,
        at: usize,
    },
    Cancelled {
        at: usize,
        polls: u64,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MalformedKind {
    Truncated,
    LengthExceedsAddressSpace,
    InvalidUtf8,
    SchemaName,
    SchemaVersion,
    TrailingBytes,
    UnknownNameTag(u8),
    AnonymousNameComponent,
    UnknownLevelTag(u8),
    LevelDepth,
    UnknownExprTag(u8),
    BoundIndex,
    UnknownBinderTag(u8),
    NonCanonicalBool(u8),
    UnknownMetadataTag(u8),
    NonCanonicalNat,
    ArenaOverflow,
    ValueStack,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Malformed {
    pub at: usize,
    pub kind: MalformedKind,
}

/// Malformedness is a completed verdict about the bytes. Resource/cancellation is a
/// typed non-answer and cannot be collapsed into it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodeOutcome<T> {
    Complete(Result<T, Malformed>),
    Inconclusive(DecodeStop),
}

enum StepError {
    Malformed(Malformed),
    Stopped(DecodeStop),
}

struct Reader<'a, 'p> {
    bytes: &'a [u8],
    at: usize,
    budget: DecodeBudget,
    produced_units: u64,
    polls: u64,
    cancelled: &'p mut dyn FnMut() -> bool,
}

impl<'a, 'p> Reader<'a, 'p> {
    fn new(
        bytes: &'a [u8],
        budget: DecodeBudget,
        cancelled: &'p mut dyn FnMut() -> bool,
    ) -> Reader<'a, 'p> {
        Reader {
            bytes,
            at: 0,
            budget,
            produced_units: 0,
            polls: 0,
            cancelled,
        }
    }

    fn malformed(&self, kind: MalformedKind) -> StepError {
        StepError::Malformed(Malformed { at: self.at, kind })
    }

    fn admit_input(&mut self) -> Result<(), StepError> {
        self.checkpoint()?;
        let observed = u64::try_from(self.bytes.len())
            .map_err(|_| self.malformed(MalformedKind::LengthExceedsAddressSpace))?;
        if observed > self.budget.max_input_bytes {
            return Err(StepError::Stopped(DecodeStop::Resource {
                limit: DecodeLimit::InputBytes,
                allowed: self.budget.max_input_bytes,
                observed,
                at: self.at,
            }));
        }
        Ok(())
    }

    fn checkpoint(&mut self) -> Result<(), StepError> {
        self.polls = self.polls.saturating_add(1);
        if (self.cancelled)() {
            return Err(StepError::Stopped(DecodeStop::Cancelled {
                at: self.at,
                polls: self.polls,
            }));
        }
        Ok(())
    }

    fn charge_unit(&mut self) -> Result<(), StepError> {
        self.checkpoint()?;
        let observed = self.produced_units.saturating_add(1);
        if observed > self.budget.max_produced_units {
            return Err(StepError::Stopped(DecodeStop::Resource {
                limit: DecodeLimit::ProducedUnits,
                allowed: self.budget.max_produced_units,
                observed,
                at: self.at,
            }));
        }
        self.produced_units = observed;
        Ok(())
    }

    fn take(&mut self, count: usize) -> Result<&'a [u8], StepError> {
        self.checkpoint()?;
        let Some(end) = self.at.checked_add(count) else {
            return Err(self.malformed(MalformedKind::LengthExceedsAddressSpace));
        };
        if end > self.bytes.len() {
            return Err(self.malformed(MalformedKind::Truncated));
        }
        if end as u64 > self.budget.max_input_bytes {
            return Err(StepError::Stopped(DecodeStop::Resource {
                limit: DecodeLimit::InputBytes,
                allowed: self.budget.max_input_bytes,
                observed: end as u64,
                at: self.at,
            }));
        }
        let result = &self.bytes[self.at..end];
        self.at = end;
        Ok(result)
    }

    fn u8(&mut self) -> Result<u8, StepError> {
        Ok(self.take(1)?[0])
    }

    fn u16(&mut self) -> Result<u16, StepError> {
        let raw = self.take(2)?;
        Ok(u16::from_le_bytes([raw[0], raw[1]]))
    }

    fn u32(&mut self) -> Result<u32, StepError> {
        let raw = self.take(4)?;
        Ok(u32::from_le_bytes([raw[0], raw[1], raw[2], raw[3]]))
    }

    fn u64(&mut self) -> Result<u64, StepError> {
        let raw = self.take(8)?;
        Ok(u64::from_le_bytes([
            raw[0], raw[1], raw[2], raw[3], raw[4], raw[5], raw[6], raw[7],
        ]))
    }

    fn i64(&mut self) -> Result<i64, StepError> {
        let raw = self.take(8)?;
        Ok(i64::from_le_bytes([
            raw[0], raw[1], raw[2], raw[3], raw[4], raw[5], raw[6], raw[7],
        ]))
    }

    fn bool(&mut self) -> Result<bool, StepError> {
        let value = self.u8()?;
        match value {
            0 => Ok(false),
            1 => Ok(true),
            other => Err(self.malformed(MalformedKind::NonCanonicalBool(other))),
        }
    }

    fn bytes(&mut self) -> Result<&'a [u8], StepError> {
        let count = self.u64()?;
        let count = usize::try_from(count)
            .map_err(|_| self.malformed(MalformedKind::LengthExceedsAddressSpace))?;
        self.take(count)
    }

    fn text(&mut self) -> Result<&'a str, StepError> {
        let raw = self.bytes()?;
        std::str::from_utf8(raw).map_err(|_| self.malformed(MalformedKind::InvalidUtf8))
    }

    fn schema(&mut self, expected: SchemaId) -> Result<(), StepError> {
        if self.text()? != expected.name {
            return Err(self.malformed(MalformedKind::SchemaName));
        }
        if self.u16()? != expected.version {
            return Err(self.malformed(MalformedKind::SchemaVersion));
        }
        Ok(())
    }

    fn finish(&self) -> Result<(), StepError> {
        if self.at == self.bytes.len() {
            Ok(())
        } else {
            Err(self.malformed(MalformedKind::TrailingBytes))
        }
    }
}

fn outcome<T>(result: Result<T, StepError>) -> DecodeOutcome<T> {
    match result {
        Ok(value) => DecodeOutcome::Complete(Ok(value)),
        Err(StepError::Malformed(error)) => DecodeOutcome::Complete(Err(error)),
        Err(StepError::Stopped(stop)) => DecodeOutcome::Inconclusive(stop),
    }
}

fn decode_name_value(reader: &mut Reader<'_, '_>) -> Result<WireName, StepError> {
    let count = reader.u64()?;
    let mut parts = Vec::new();
    for _ in 0..count {
        reader.charge_unit()?;
        let part = match reader.u8()? {
            NAME_STR => NamePart::Text(reader.text()?.to_owned()),
            NAME_NUM => NamePart::Numeric {
                value: reader.u64()?,
                overflowed: false,
            },
            NAME_NUM_OVERFLOW => NamePart::Numeric {
                value: reader.u64()?,
                overflowed: true,
            },
            NAME_ANON => return Err(reader.malformed(MalformedKind::AnonymousNameComponent)),
            tag => return Err(reader.malformed(MalformedKind::UnknownNameTag(tag))),
        };
        parts.push(part);
    }
    Ok(WireName { parts })
}

struct LevelBuilder {
    nodes: Vec<LevelNode>,
    depths: Vec<u32>,
}

impl LevelBuilder {
    fn new() -> LevelBuilder {
        LevelBuilder {
            nodes: Vec::new(),
            depths: Vec::new(),
        }
    }

    fn push(&mut self, node: LevelNode, depth: u32, at: usize) -> Result<LevelId, StepError> {
        if depth > MAX_LEVEL_DEPTH || self.nodes.len() >= u32::MAX as usize {
            return Err(StepError::Malformed(Malformed {
                at,
                kind: if depth > MAX_LEVEL_DEPTH {
                    MalformedKind::LevelDepth
                } else {
                    MalformedKind::ArenaOverflow
                },
            }));
        }
        let id = LevelId(self.nodes.len() as u32);
        self.nodes.push(node);
        self.depths.push(depth);
        Ok(id)
    }

    fn depth(&self, id: LevelId, at: usize) -> Result<u32, StepError> {
        self.depths.get(id.index()).copied().ok_or({
            StepError::Malformed(Malformed {
                at,
                kind: MalformedKind::ValueStack,
            })
        })
    }
}

#[derive(Clone, Copy)]
enum LevelTask {
    Read,
    BuildSucc,
    BuildMax,
    BuildIMax,
}

fn decode_level_value(
    reader: &mut Reader<'_, '_>,
    builder: &mut LevelBuilder,
) -> Result<LevelId, StepError> {
    let mut tasks = vec![LevelTask::Read];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            LevelTask::Read => {
                reader.charge_unit()?;
                let value = match reader.u8()? {
                    LEVEL_ZERO => Some(builder.push(LevelNode::Zero, 0, reader.at)?),
                    LEVEL_SUCC => {
                        tasks.push(LevelTask::BuildSucc);
                        tasks.push(LevelTask::Read);
                        None
                    }
                    LEVEL_MAX => {
                        tasks.push(LevelTask::BuildMax);
                        tasks.push(LevelTask::Read);
                        tasks.push(LevelTask::Read);
                        None
                    }
                    LEVEL_IMAX => {
                        tasks.push(LevelTask::BuildIMax);
                        tasks.push(LevelTask::Read);
                        tasks.push(LevelTask::Read);
                        None
                    }
                    LEVEL_PARAM => Some(builder.push(
                        LevelNode::Parameter(decode_name_value(reader)?),
                        0,
                        reader.at,
                    )?),
                    LEVEL_MVAR => Some(builder.push(
                        LevelNode::Meta(decode_name_value(reader)?),
                        0,
                        reader.at,
                    )?),
                    tag => return Err(reader.malformed(MalformedKind::UnknownLevelTag(tag))),
                };
                if let Some(value) = value {
                    values.push(value);
                }
            }
            LevelTask::BuildSucc => {
                let child = values
                    .pop()
                    .ok_or_else(|| reader.malformed(MalformedKind::ValueStack))?;
                let depth = builder.depth(child, reader.at)?.saturating_add(1);
                values.push(builder.push(LevelNode::Succ(child), depth, reader.at)?);
            }
            LevelTask::BuildMax | LevelTask::BuildIMax => {
                let right = values
                    .pop()
                    .ok_or_else(|| reader.malformed(MalformedKind::ValueStack))?;
                let left = values
                    .pop()
                    .ok_or_else(|| reader.malformed(MalformedKind::ValueStack))?;
                let depth = builder
                    .depth(left, reader.at)?
                    .max(builder.depth(right, reader.at)?)
                    .saturating_add(1);
                let node = match task {
                    LevelTask::BuildMax => LevelNode::Max(left, right),
                    LevelTask::BuildIMax => LevelNode::IMax(left, right),
                    LevelTask::Read | LevelTask::BuildSucc => {
                        return Err(reader.malformed(MalformedKind::ValueStack));
                    }
                };
                values.push(builder.push(node, depth, reader.at)?);
            }
        }
    }
    if values.len() == 1 {
        Ok(values[0])
    } else {
        Err(reader.malformed(MalformedKind::ValueStack))
    }
}

fn push_expr(nodes: &mut Vec<ExprNode>, node: ExprNode, at: usize) -> Result<ExprId, StepError> {
    if nodes.len() >= u32::MAX as usize {
        return Err(StepError::Malformed(Malformed {
            at,
            kind: MalformedKind::ArenaOverflow,
        }));
    }
    let id = ExprId(nodes.len() as u32);
    nodes.push(node);
    Ok(id)
}

fn binder_style(reader: &mut Reader<'_, '_>) -> Result<BinderStyle, StepError> {
    let tag = reader.u8()?;
    match tag {
        0 => Ok(BinderStyle::Default),
        1 => Ok(BinderStyle::Implicit),
        2 => Ok(BinderStyle::StrictImplicit),
        3 => Ok(BinderStyle::InstanceImplicit),
        other => Err(reader.malformed(MalformedKind::UnknownBinderTag(other))),
    }
}

fn metadata_entries(
    reader: &mut Reader<'_, '_>,
) -> Result<Vec<(WireName, MetadataValue)>, StepError> {
    let count = reader.u64()?;
    let mut entries = Vec::new();
    for _ in 0..count {
        reader.charge_unit()?;
        let key = decode_name_value(reader)?;
        let value = match reader.u8()? {
            DATA_STRING => MetadataValue::Text(reader.text()?.to_owned()),
            DATA_BOOL => MetadataValue::Bool(reader.bool()?),
            DATA_NAME => MetadataValue::Name(decode_name_value(reader)?),
            DATA_NAT => MetadataValue::Nat(reader.u64()?),
            DATA_INT => MetadataValue::Int(reader.i64()?),
            DATA_SYNTAX => MetadataValue::Syntax(reader.u64()?),
            tag => return Err(reader.malformed(MalformedKind::UnknownMetadataTag(tag))),
        };
        entries.push((key, value));
    }
    Ok(entries)
}

enum ExprTask {
    Read,
    BuildApply,
    BuildLambda(WireName),
    BuildForall(WireName),
    BuildLet(WireName),
    BuildMetadata(Vec<(WireName, MetadataValue)>),
    BuildProjection(WireName, u64),
}

fn decode_expr_value(
    reader: &mut Reader<'_, '_>,
    levels: &mut LevelBuilder,
) -> Result<(Vec<ExprNode>, ExprId), StepError> {
    let mut tasks = vec![ExprTask::Read];
    let mut values = Vec::new();
    let mut nodes = Vec::new();

    while let Some(task) = tasks.pop() {
        match task {
            ExprTask::Read => {
                reader.charge_unit()?;
                let value = match reader.u8()? {
                    EXPR_BVAR => {
                        let index = reader.u32()?;
                        if index > MAX_BVAR_INDEX {
                            return Err(reader.malformed(MalformedKind::BoundIndex));
                        }
                        Some(push_expr(&mut nodes, ExprNode::Bound { index }, reader.at)?)
                    }
                    EXPR_FVAR => Some(push_expr(
                        &mut nodes,
                        ExprNode::Free {
                            name: decode_name_value(reader)?,
                        },
                        reader.at,
                    )?),
                    EXPR_MVAR => Some(push_expr(
                        &mut nodes,
                        ExprNode::Meta {
                            name: decode_name_value(reader)?,
                        },
                        reader.at,
                    )?),
                    EXPR_SORT => Some(push_expr(
                        &mut nodes,
                        ExprNode::Sort {
                            level: decode_level_value(reader, levels)?,
                        },
                        reader.at,
                    )?),
                    EXPR_CONST => {
                        let name = decode_name_value(reader)?;
                        let count = reader.u64()?;
                        let mut arguments = Vec::new();
                        for _ in 0..count {
                            arguments.push(decode_level_value(reader, levels)?);
                        }
                        Some(push_expr(
                            &mut nodes,
                            ExprNode::Constant {
                                name,
                                levels: arguments,
                            },
                            reader.at,
                        )?)
                    }
                    EXPR_APP => {
                        tasks.push(ExprTask::BuildApply);
                        tasks.push(ExprTask::Read);
                        tasks.push(ExprTask::Read);
                        None
                    }
                    EXPR_LAM => {
                        let name = decode_name_value(reader)?;
                        tasks.push(ExprTask::BuildLambda(name));
                        tasks.push(ExprTask::Read);
                        tasks.push(ExprTask::Read);
                        None
                    }
                    EXPR_FORALL => {
                        let name = decode_name_value(reader)?;
                        tasks.push(ExprTask::BuildForall(name));
                        tasks.push(ExprTask::Read);
                        tasks.push(ExprTask::Read);
                        None
                    }
                    EXPR_LET => {
                        let name = decode_name_value(reader)?;
                        tasks.push(ExprTask::BuildLet(name));
                        tasks.push(ExprTask::Read);
                        tasks.push(ExprTask::Read);
                        tasks.push(ExprTask::Read);
                        None
                    }
                    EXPR_LIT_NAT => {
                        let count = reader.u64()?;
                        let mut limbs = Vec::new();
                        for _ in 0..count {
                            reader.charge_unit()?;
                            limbs.push(reader.u64()?);
                        }
                        if limbs.last() == Some(&0) {
                            return Err(reader.malformed(MalformedKind::NonCanonicalNat));
                        }
                        Some(push_expr(
                            &mut nodes,
                            ExprNode::NatLiteral { limbs_le: limbs },
                            reader.at,
                        )?)
                    }
                    EXPR_LIT_STR => Some(push_expr(
                        &mut nodes,
                        ExprNode::StringLiteral(reader.text()?.to_owned()),
                        reader.at,
                    )?),
                    EXPR_MDATA => {
                        let entries = metadata_entries(reader)?;
                        tasks.push(ExprTask::BuildMetadata(entries));
                        tasks.push(ExprTask::Read);
                        None
                    }
                    EXPR_PROJ => {
                        let name = decode_name_value(reader)?;
                        let index = reader.u64()?;
                        tasks.push(ExprTask::BuildProjection(name, index));
                        tasks.push(ExprTask::Read);
                        None
                    }
                    tag => return Err(reader.malformed(MalformedKind::UnknownExprTag(tag))),
                };
                if let Some(value) = value {
                    values.push(value);
                }
            }
            ExprTask::BuildApply => {
                let argument = values
                    .pop()
                    .ok_or_else(|| reader.malformed(MalformedKind::ValueStack))?;
                let function = values
                    .pop()
                    .ok_or_else(|| reader.malformed(MalformedKind::ValueStack))?;
                values.push(push_expr(
                    &mut nodes,
                    ExprNode::Apply { function, argument },
                    reader.at,
                )?);
            }
            ExprTask::BuildLambda(binder_name) => {
                let body = values
                    .pop()
                    .ok_or_else(|| reader.malformed(MalformedKind::ValueStack))?;
                let binder_type = values
                    .pop()
                    .ok_or_else(|| reader.malformed(MalformedKind::ValueStack))?;
                let style = binder_style(reader)?;
                values.push(push_expr(
                    &mut nodes,
                    ExprNode::Lambda {
                        binder_name,
                        binder_type,
                        body,
                        style,
                    },
                    reader.at,
                )?);
            }
            ExprTask::BuildForall(binder_name) => {
                let body = values
                    .pop()
                    .ok_or_else(|| reader.malformed(MalformedKind::ValueStack))?;
                let binder_type = values
                    .pop()
                    .ok_or_else(|| reader.malformed(MalformedKind::ValueStack))?;
                let style = binder_style(reader)?;
                values.push(push_expr(
                    &mut nodes,
                    ExprNode::Forall {
                        binder_name,
                        binder_type,
                        body,
                        style,
                    },
                    reader.at,
                )?);
            }
            ExprTask::BuildLet(declaration_name) => {
                let body = values
                    .pop()
                    .ok_or_else(|| reader.malformed(MalformedKind::ValueStack))?;
                let value = values
                    .pop()
                    .ok_or_else(|| reader.malformed(MalformedKind::ValueStack))?;
                let type_ = values
                    .pop()
                    .ok_or_else(|| reader.malformed(MalformedKind::ValueStack))?;
                let non_dependent = reader.bool()?;
                values.push(push_expr(
                    &mut nodes,
                    ExprNode::Let {
                        declaration_name,
                        type_,
                        value,
                        body,
                        non_dependent,
                    },
                    reader.at,
                )?);
            }
            ExprTask::BuildMetadata(entries) => {
                let expression = values
                    .pop()
                    .ok_or_else(|| reader.malformed(MalformedKind::ValueStack))?;
                values.push(push_expr(
                    &mut nodes,
                    ExprNode::Metadata {
                        entries,
                        expression,
                    },
                    reader.at,
                )?);
            }
            ExprTask::BuildProjection(structure_name, index) => {
                let expression = values
                    .pop()
                    .ok_or_else(|| reader.malformed(MalformedKind::ValueStack))?;
                values.push(push_expr(
                    &mut nodes,
                    ExprNode::Projection {
                        structure_name,
                        index,
                        expression,
                    },
                    reader.at,
                )?);
            }
        }
    }

    if values.len() == 1 {
        Ok((nodes, values[0]))
    } else {
        Err(reader.malformed(MalformedKind::ValueStack))
    }
}

fn run_name(
    bytes: &[u8],
    budget: DecodeBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<WireName, StepError> {
    let mut reader = Reader::new(bytes, budget, cancelled);
    reader.admit_input()?;
    reader.schema(SCHEMA_NAME)?;
    let value = decode_name_value(&mut reader)?;
    reader.finish()?;
    Ok(value)
}

fn run_level(
    bytes: &[u8],
    budget: DecodeBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<WireLevel, StepError> {
    let mut reader = Reader::new(bytes, budget, cancelled);
    reader.admit_input()?;
    reader.schema(SCHEMA_LEVEL)?;
    let mut builder = LevelBuilder::new();
    let root = decode_level_value(&mut reader, &mut builder)?;
    reader.finish()?;
    Ok(WireLevel {
        nodes: builder.nodes,
        root,
    })
}

fn run_expr(
    bytes: &[u8],
    budget: DecodeBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<WireExpr, StepError> {
    let mut reader = Reader::new(bytes, budget, cancelled);
    reader.admit_input()?;
    reader.schema(SCHEMA_EXPR)?;
    let mut levels = LevelBuilder::new();
    let (nodes, root) = decode_expr_value(&mut reader, &mut levels)?;
    reader.finish()?;
    Ok(WireExpr {
        nodes,
        levels: levels.nodes,
        root,
    })
}

pub fn decode_name(bytes: &[u8], budget: DecodeBudget) -> DecodeOutcome<WireName> {
    decode_name_with(bytes, budget, || false)
}

pub fn decode_name_with(
    bytes: &[u8],
    budget: DecodeBudget,
    mut cancelled: impl FnMut() -> bool,
) -> DecodeOutcome<WireName> {
    outcome(run_name(bytes, budget, &mut cancelled))
}

pub fn decode_level(bytes: &[u8], budget: DecodeBudget) -> DecodeOutcome<WireLevel> {
    decode_level_with(bytes, budget, || false)
}

pub fn decode_level_with(
    bytes: &[u8],
    budget: DecodeBudget,
    mut cancelled: impl FnMut() -> bool,
) -> DecodeOutcome<WireLevel> {
    outcome(run_level(bytes, budget, &mut cancelled))
}

pub fn decode_expr(bytes: &[u8], budget: DecodeBudget) -> DecodeOutcome<WireExpr> {
    decode_expr_with(bytes, budget, || false)
}

pub fn decode_expr_with(
    bytes: &[u8],
    budget: DecodeBudget,
    mut cancelled: impl FnMut() -> bool,
) -> DecodeOutcome<WireExpr> {
    outcome(run_expr(bytes, budget, &mut cancelled))
}
