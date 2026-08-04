//! Canonical serialization (bead franken_lean-rps, requirements b/c).
//!
//! One versioned schema per durable value shape; exactly one valid byte encoding per
//! value (no encoder freedom: fixed-width little-endian integers, u64 length prefixes,
//! u8 enum tags in declaration order). The semantic-hash / byte-hash distinction of
//! plan §7.3 is structural here: a *semantic* digest is a domain hash over THIS
//! canonical encoding, while a *byte* digest covers whatever artifact bytes exist on
//! disk — re-encoding or compression can change the latter without pretending to
//! change the former.
//!
//! Decoding is total over arbitrary bytes: every failure is a typed [`CanonError`],
//! never a panic (D8 taxonomy).

use fln_core::diag::{Diagnostic, ErrorValue, ResourceReason, Severity};
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::{DataValue, KVMap, SyntaxHandle};
use fln_core::pos::Position;

/// A frozen schema identity: name + version. Bumping the version is the only legal
/// way to change an encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SchemaId {
    pub name: &'static str,
    pub version: u16,
}

pub const SCHEMA_NAME: SchemaId = SchemaId {
    name: "fln.canon.name",
    version: 1,
};
pub const SCHEMA_LEVEL: SchemaId = SchemaId {
    name: "fln.canon.level",
    version: 1,
};
pub const SCHEMA_EXPR: SchemaId = SchemaId {
    name: "fln.canon.expr",
    version: 1,
};
pub const SCHEMA_KVMAP: SchemaId = SchemaId {
    name: "fln.canon.kvmap",
    version: 1,
};

/// Typed decode failure. `at` is the byte offset of the failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonError {
    pub at: usize,
    pub what: &'static str,
}

impl std::fmt::Display for CanonError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "canonical decode failed at byte {}: {}",
            self.at, self.what
        )
    }
}

/// Canonical byte writer.
#[derive(Debug, Default)]
pub struct CanonWriter {
    buf: Vec<u8>,
}

impl CanonWriter {
    pub fn new() -> CanonWriter {
        CanonWriter::default()
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.buf
    }

    pub fn u8(&mut self, v: u8) {
        self.buf.push(v);
    }

    pub fn u16(&mut self, v: u16) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    pub fn u32(&mut self, v: u32) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    pub fn u64(&mut self, v: u64) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    pub fn i64(&mut self, v: i64) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    pub fn bool(&mut self, v: bool) {
        self.buf.push(u8::from(v));
    }

    /// Length-prefixed bytes (u64 LE length).
    pub fn bytes(&mut self, v: &[u8]) {
        self.u64(v.len() as u64);
        self.buf.extend_from_slice(v);
    }

    pub fn str(&mut self, v: &str) {
        self.bytes(v.as_bytes());
    }

    /// The schema header every top-level encoding starts with.
    pub fn schema(&mut self, id: SchemaId) {
        self.str(id.name);
        self.u16(id.version);
    }
}

/// Canonical byte reader.
#[derive(Debug)]
pub struct CanonReader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> CanonReader<'a> {
    pub fn new(bytes: &'a [u8]) -> CanonReader<'a> {
        CanonReader { bytes, at: 0 }
    }

    fn err(&self, what: &'static str) -> CanonError {
        CanonError { at: self.at, what }
    }

    fn take(&mut self, n: usize) -> Result<&'a [u8], CanonError> {
        let end = self
            .at
            .checked_add(n)
            .filter(|end| *end <= self.bytes.len())
            .ok_or_else(|| self.err("input truncated"))?;
        let slice = &self.bytes[self.at..end];
        self.at = end;
        Ok(slice)
    }

    pub fn u8(&mut self) -> Result<u8, CanonError> {
        Ok(self.take(1)?[0])
    }

    pub fn u16(&mut self) -> Result<u16, CanonError> {
        Ok(u16::from_le_bytes(self.take(2)?.try_into().expect("len 2")))
    }

    pub fn u32(&mut self) -> Result<u32, CanonError> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().expect("len 4")))
    }

    pub fn u64(&mut self) -> Result<u64, CanonError> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().expect("len 8")))
    }

    pub fn i64(&mut self) -> Result<i64, CanonError> {
        Ok(i64::from_le_bytes(self.take(8)?.try_into().expect("len 8")))
    }

    pub fn bool(&mut self) -> Result<bool, CanonError> {
        match self.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(self.err("non-canonical bool")),
        }
    }

    pub fn bytes(&mut self) -> Result<&'a [u8], CanonError> {
        let len = self.u64()?;
        let len = usize::try_from(len).map_err(|_| self.err("length exceeds address space"))?;
        self.take(len)
    }

    pub fn str(&mut self) -> Result<&'a str, CanonError> {
        let raw = self.bytes()?;
        std::str::from_utf8(raw).map_err(|_| self.err("invalid UTF-8"))
    }

    pub fn expect_schema(&mut self, id: SchemaId) -> Result<(), CanonError> {
        let name = self.str()?;
        if name != id.name {
            return Err(self.err("schema name mismatch"));
        }
        let version = self.u16()?;
        if version != id.version {
            return Err(self.err("schema version mismatch"));
        }
        Ok(())
    }

    /// Decoding must consume every byte — trailing garbage is non-canonical.
    pub fn finish(self) -> Result<(), CanonError> {
        if self.at == self.bytes.len() {
            Ok(())
        } else {
            Err(self.err("trailing bytes after value"))
        }
    }
}

/// A value with exactly one canonical encoding under a frozen schema.
pub trait Canonical: Sized {
    const SCHEMA: SchemaId;

    fn write_body(&self, w: &mut CanonWriter);
    fn read_body(r: &mut CanonReader<'_>) -> Result<Self, CanonError>;

    /// Schema-headed encoding of one top-level value.
    fn to_canonical_bytes(&self) -> Vec<u8> {
        let mut w = CanonWriter::new();
        w.schema(Self::SCHEMA);
        self.write_body(&mut w);
        w.into_bytes()
    }

    /// Total inverse of [`Canonical::to_canonical_bytes`].
    fn from_canonical_bytes(bytes: &[u8]) -> Result<Self, CanonError> {
        let mut r = CanonReader::new(bytes);
        r.expect_schema(Self::SCHEMA)?;
        let value = Self::read_body(&mut r)?;
        r.finish()?;
        Ok(value)
    }
}

// ---- Name ------------------------------------------------------------------------------

const NAME_ANON: u8 = 0;
const NAME_STR: u8 = 1;
const NAME_NUM: u8 = 2;
const NAME_NUM_OVERFLOW: u8 = 3;

impl Canonical for Name {
    const SCHEMA: SchemaId = SCHEMA_NAME;

    fn write_body(&self, w: &mut CanonWriter) {
        // Components root-to-leaf so decoding is a single forward fold.
        let mut chain = Vec::new();
        let mut cursor = self.clone();
        while !cursor.is_anonymous() {
            chain.push(cursor.clone());
            cursor = cursor.parent();
        }
        w.u64(chain.len() as u64);
        for link in chain.iter().rev() {
            match link.leaf() {
                NameLeaf::Str(s) => {
                    w.u8(NAME_STR);
                    w.str(s);
                }
                NameLeaf::Num(v, false) => {
                    w.u8(NAME_NUM);
                    w.u64(v);
                }
                NameLeaf::Num(v, true) => {
                    w.u8(NAME_NUM_OVERFLOW);
                    w.u64(v);
                }
                NameLeaf::Anonymous => w.u8(NAME_ANON),
            }
        }
    }

    fn read_body(r: &mut CanonReader<'_>) -> Result<Name, CanonError> {
        let count = r.u64()?;
        let mut name = Name::anonymous();
        for _ in 0..count {
            name = match r.u8()? {
                NAME_STR => Name::str(name, r.str()?),
                NAME_NUM => Name::num(name, r.u64()?),
                NAME_NUM_OVERFLOW => Name::num_overflowing(name, r.u64()?),
                NAME_ANON => return Err(r.err_public("anonymous inside a component chain")),
                _ => return Err(r.err_public("unknown name component tag")),
            };
        }
        Ok(name)
    }
}

/// Leaf view used by the canonical encoder (kept here so fln-core's API stays small).
enum NameLeaf<'a> {
    Anonymous,
    Str(&'a str),
    Num(u64, bool),
}

trait NameLeafExt {
    fn leaf(&self) -> NameLeaf<'_>;
}

impl NameLeafExt for Name {
    fn leaf(&self) -> NameLeaf<'_> {
        match self.leaf_view() {
            fln_core::name::LeafView::Anonymous => NameLeaf::Anonymous,
            fln_core::name::LeafView::Str(s) => NameLeaf::Str(s),
            fln_core::name::LeafView::Num(v) => NameLeaf::Num(v, self.component_overflowed()),
        }
    }
}

impl CanonReader<'_> {
    fn err_public(&self, what: &'static str) -> CanonError {
        CanonError { at: self.at, what }
    }
}

// ---- Level -----------------------------------------------------------------------------

const LEVEL_ZERO: u8 = 0;
const LEVEL_SUCC: u8 = 1;
const LEVEL_MAX: u8 = 2;
const LEVEL_IMAX: u8 = 3;
const LEVEL_PARAM: u8 = 4;
const LEVEL_MVAR: u8 = 5;

impl Canonical for Level {
    const SCHEMA: SchemaId = SCHEMA_LEVEL;

    fn write_body(&self, w: &mut CanonWriter) {
        use fln_core::level::LevelView;
        let mut pending = vec![self];
        while let Some(level) = pending.pop() {
            match level.view() {
                LevelView::Zero => w.u8(LEVEL_ZERO),
                LevelView::Succ(inner) => {
                    w.u8(LEVEL_SUCC);
                    pending.push(inner);
                }
                LevelView::Max(a, b) => {
                    w.u8(LEVEL_MAX);
                    pending.push(b);
                    pending.push(a);
                }
                LevelView::IMax(a, b) => {
                    w.u8(LEVEL_IMAX);
                    pending.push(b);
                    pending.push(a);
                }
                LevelView::Param(name) => {
                    w.u8(LEVEL_PARAM);
                    name.write_body(w);
                }
                LevelView::MVar(id) => {
                    w.u8(LEVEL_MVAR);
                    id.0.write_body(w);
                }
            }
        }
    }

    fn read_body(r: &mut CanonReader<'_>) -> Result<Level, CanonError> {
        // Iterative, not recursive: decode depth is bounded by the heap work-stack
        // (input size), never by the call stack. A recursive descent here would
        // overflow the stack — an uncatchable SIGABRT, worse than a panic — on a
        // deeply nested but tiny hostile encoding (franken_lean-fnj, D8/FL-INV-07).
        read_level_iter(r)
    }
}

/// One pending step of the iterative [`Level`] decoder.
enum LevelTask {
    /// Read one node (tag + any leaf fields); recursive nodes push their build
    /// step plus a `Read` per child.
    Read,
    BuildSucc,
    BuildMax,
    BuildIMax,
}

/// Decode one `Level` with an explicit heap work-stack (see [`Level::read_body`]).
/// The byte grammar is identical to the recursive form; only the control stack
/// moved off the call stack.
fn read_level_iter(r: &mut CanonReader<'_>) -> Result<Level, CanonError> {
    let underflow = |r: &CanonReader<'_>| r.err_public("level value-stack underflow");
    let too_deep = |r: &CanonReader<'_>| r.err_public("level depth exceeds the 24-bit covenant");
    let mut tasks = vec![LevelTask::Read];
    let mut values: Vec<Level> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            LevelTask::Read => match r.u8()? {
                LEVEL_ZERO => values.push(Level::zero()),
                LEVEL_SUCC => {
                    tasks.push(LevelTask::BuildSucc);
                    tasks.push(LevelTask::Read);
                }
                LEVEL_MAX => {
                    // Push the builder first (runs last), then the two child reads;
                    // the LIFO order reads child `a` before child `b`, matching the
                    // encoder's left-to-right emission.
                    tasks.push(LevelTask::BuildMax);
                    tasks.push(LevelTask::Read);
                    tasks.push(LevelTask::Read);
                }
                LEVEL_IMAX => {
                    tasks.push(LevelTask::BuildIMax);
                    tasks.push(LevelTask::Read);
                    tasks.push(LevelTask::Read);
                }
                LEVEL_PARAM => values.push(Level::param(Name::read_body(r)?)),
                LEVEL_MVAR => values.push(Level::mvar(LMVarId(Name::read_body(r)?))),
                _ => return Err(r.err_public("unknown level tag")),
            },
            LevelTask::BuildSucc => {
                let u = values.pop().ok_or_else(|| underflow(r))?;
                values.push(u.succ().map_err(|_| too_deep(r))?);
            }
            LevelTask::BuildMax => {
                let b = values.pop().ok_or_else(|| underflow(r))?;
                let a = values.pop().ok_or_else(|| underflow(r))?;
                values.push(Level::max(a, b).map_err(|_| too_deep(r))?);
            }
            LevelTask::BuildIMax => {
                let b = values.pop().ok_or_else(|| underflow(r))?;
                let a = values.pop().ok_or_else(|| underflow(r))?;
                values.push(Level::imax(a, b).map_err(|_| too_deep(r))?);
            }
        }
    }
    // A well-formed single-value stream reduces to exactly one root.
    match values.len() {
        1 => Ok(values.pop().expect("length checked")),
        _ => Err(r.err_public("level value-stack did not reduce to a single root")),
    }
}

// ---- KVMap / DataValue -----------------------------------------------------------------

const DV_STRING: u8 = 0;
const DV_BOOL: u8 = 1;
const DV_NAME: u8 = 2;
const DV_NAT: u8 = 3;
const DV_INT: u8 = 4;
const DV_SYNTAX: u8 = 5;

impl Canonical for KVMap {
    const SCHEMA: SchemaId = SCHEMA_KVMAP;

    fn write_body(&self, w: &mut CanonWriter) {
        // Insertion order IS the value (upstream KVMap is an ordered assoc list).
        w.u64(self.entries().len() as u64);
        for (key, value) in self.entries() {
            key.write_body(w);
            match value {
                DataValue::OfString(v) => {
                    w.u8(DV_STRING);
                    w.str(v);
                }
                DataValue::OfBool(v) => {
                    w.u8(DV_BOOL);
                    w.bool(*v);
                }
                DataValue::OfName(v) => {
                    w.u8(DV_NAME);
                    v.write_body(w);
                }
                DataValue::OfNat(v) => {
                    w.u8(DV_NAT);
                    w.u64(*v);
                }
                DataValue::OfInt(v) => {
                    w.u8(DV_INT);
                    w.i64(*v);
                }
                DataValue::OfSyntax(v) => {
                    w.u8(DV_SYNTAX);
                    w.u64(v.0);
                }
            }
        }
    }

    fn read_body(r: &mut CanonReader<'_>) -> Result<KVMap, CanonError> {
        let count = r.u64()?;
        let mut map = KVMap::new();
        for _ in 0..count {
            let key = Name::read_body(r)?;
            let value = match r.u8()? {
                DV_STRING => DataValue::OfString(r.str()?.to_string()),
                DV_BOOL => DataValue::OfBool(r.bool()?),
                DV_NAME => DataValue::OfName(Name::read_body(r)?),
                DV_NAT => DataValue::OfNat(r.u64()?),
                DV_INT => DataValue::OfInt(r.i64()?),
                DV_SYNTAX => DataValue::OfSyntax(SyntaxHandle(r.u64()?)),
                _ => return Err(r.err_public("unknown data-value tag")),
            };
            map.insert(key, value);
        }
        Ok(map)
    }
}

// ---- Expr ------------------------------------------------------------------------------

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

fn binder_info_tag(bi: BinderInfo) -> u8 {
    // The upstream toUInt64 encodings (Expr.lean:163-168).
    bi.to_u64() as u8
}

fn binder_info_from_tag(tag: u8) -> Option<BinderInfo> {
    Some(match tag {
        0 => BinderInfo::Default,
        1 => BinderInfo::Implicit,
        2 => BinderInfo::StrictImplicit,
        3 => BinderInfo::InstImplicit,
        _ => return None,
    })
}

impl Canonical for Expr {
    const SCHEMA: SchemaId = SCHEMA_EXPR;

    fn write_body(&self, w: &mut CanonWriter) {
        enum WriteTask<'a> {
            Expr(&'a Expr),
            BinderInfo(BinderInfo),
            NonDep(bool),
        }

        let mut pending = vec![WriteTask::Expr(self)];
        while let Some(task) = pending.pop() {
            let WriteTask::Expr(expr) = task else {
                match task {
                    WriteTask::BinderInfo(info) => w.u8(binder_info_tag(info)),
                    WriteTask::NonDep(value) => w.bool(value),
                    WriteTask::Expr(_) => unreachable!("matched above"),
                }
                continue;
            };

            match expr.node() {
                ExprNode::BVar { idx } => {
                    w.u8(EXPR_BVAR);
                    w.u32(*idx);
                }
                ExprNode::FVar { id } => {
                    w.u8(EXPR_FVAR);
                    id.0.write_body(w);
                }
                ExprNode::MVar { id } => {
                    w.u8(EXPR_MVAR);
                    id.0.write_body(w);
                }
                ExprNode::Sort { level } => {
                    w.u8(EXPR_SORT);
                    level.write_body(w);
                }
                ExprNode::Const { name, levels } => {
                    w.u8(EXPR_CONST);
                    name.write_body(w);
                    w.u64(levels.len() as u64);
                    for level in levels {
                        level.write_body(w);
                    }
                }
                ExprNode::App { f, a } => {
                    w.u8(EXPR_APP);
                    pending.push(WriteTask::Expr(a));
                    pending.push(WriteTask::Expr(f));
                }
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => {
                    w.u8(EXPR_LAM);
                    binder_name.write_body(w);
                    pending.push(WriteTask::BinderInfo(*binder_info));
                    pending.push(WriteTask::Expr(body));
                    pending.push(WriteTask::Expr(binder_type));
                }
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => {
                    w.u8(EXPR_FORALL);
                    binder_name.write_body(w);
                    pending.push(WriteTask::BinderInfo(*binder_info));
                    pending.push(WriteTask::Expr(body));
                    pending.push(WriteTask::Expr(binder_type));
                }
                ExprNode::LetE {
                    decl_name,
                    type_,
                    value,
                    body,
                    non_dep,
                } => {
                    w.u8(EXPR_LET);
                    decl_name.write_body(w);
                    pending.push(WriteTask::NonDep(*non_dep));
                    pending.push(WriteTask::Expr(body));
                    pending.push(WriteTask::Expr(value));
                    pending.push(WriteTask::Expr(type_));
                }
                ExprNode::Lit { literal } => match literal {
                    Literal::Nat(n) => {
                        w.u8(EXPR_LIT_NAT);
                        w.u64(n.limbs_le().len() as u64);
                        for limb in n.limbs_le() {
                            w.u64(*limb);
                        }
                    }
                    Literal::Str(s) => {
                        w.u8(EXPR_LIT_STR);
                        w.str(s);
                    }
                },
                ExprNode::MData { data, expr } => {
                    w.u8(EXPR_MDATA);
                    data.write_body(w);
                    pending.push(WriteTask::Expr(expr));
                }
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => {
                    w.u8(EXPR_PROJ);
                    struct_name.write_body(w);
                    w.u64(*idx);
                    pending.push(WriteTask::Expr(expr));
                }
            }
        }
    }

    fn read_body(r: &mut CanonReader<'_>) -> Result<Expr, CanonError> {
        // Iterative, not recursive: see [`Level::read_body`]. A recursive descent
        // here overflows the call stack (SIGABRT, not a typed error) on a deeply
        // nested but tiny hostile encoding — e.g. a chain of `App` tags
        // (franken_lean-fnj, D8/FL-INV-07).
        read_expr_iter(r)
    }
}

/// One pending step of the iterative [`Expr`] decoder. Post-order scalar fields
/// (a binder's `BinderInfo`, a `let`'s `nonDep` flag) are read when the builder
/// runs — by then the child reads have advanced the cursor to exactly that field.
enum ExprTask {
    /// Read one node (tag + leaf fields); recursive nodes push their builder plus
    /// a `Read` per `Expr` child.
    Read,
    BuildApp,
    BuildLam(Name),
    BuildForall(Name),
    BuildLet(Name),
    BuildMData(KVMap),
    BuildProj(Name, u64),
}

/// Decode one `Expr` with an explicit heap work-stack (see [`Expr::read_body`]).
/// Byte-for-byte the same grammar as the recursive form; `Level`, `Name`, and
/// `KVMap` children decode through their own bounded readers, so total call-stack
/// depth is a small constant regardless of the term's nesting.
fn read_expr_iter(r: &mut CanonReader<'_>) -> Result<Expr, CanonError> {
    let underflow = |r: &CanonReader<'_>| r.err_public("expr value-stack underflow");
    let mut tasks = vec![ExprTask::Read];
    let mut values: Vec<Expr> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            ExprTask::Read => match r.u8()? {
                EXPR_BVAR => values.push(
                    Expr::bvar(r.u32()?)
                        .map_err(|_| r.err_public("bvar exceeds the 20-bit range covenant"))?,
                ),
                EXPR_FVAR => values.push(Expr::fvar(FVarId(Name::read_body(r)?))),
                EXPR_MVAR => values.push(Expr::mvar(MVarId(Name::read_body(r)?))),
                EXPR_SORT => values.push(Expr::sort(read_level_iter(r)?)),
                EXPR_CONST => {
                    let name = Name::read_body(r)?;
                    let count = r.u64()?;
                    let mut levels = Vec::new();
                    for _ in 0..count {
                        levels.push(read_level_iter(r)?);
                    }
                    values.push(Expr::const_(name, levels));
                }
                EXPR_APP => {
                    // Builder first (runs last); the two child reads follow so LIFO
                    // reads `f` before `a`, matching the encoder.
                    tasks.push(ExprTask::BuildApp);
                    tasks.push(ExprTask::Read);
                    tasks.push(ExprTask::Read);
                }
                EXPR_LAM => {
                    let binder_name = Name::read_body(r)?;
                    tasks.push(ExprTask::BuildLam(binder_name));
                    tasks.push(ExprTask::Read);
                    tasks.push(ExprTask::Read);
                }
                EXPR_FORALL => {
                    let binder_name = Name::read_body(r)?;
                    tasks.push(ExprTask::BuildForall(binder_name));
                    tasks.push(ExprTask::Read);
                    tasks.push(ExprTask::Read);
                }
                EXPR_LET => {
                    let decl_name = Name::read_body(r)?;
                    tasks.push(ExprTask::BuildLet(decl_name));
                    tasks.push(ExprTask::Read);
                    tasks.push(ExprTask::Read);
                    tasks.push(ExprTask::Read);
                }
                EXPR_LIT_NAT => {
                    let count = r.u64()?;
                    let mut limbs = Vec::new();
                    for _ in 0..count {
                        limbs.push(r.u64()?);
                    }
                    let lit = NatLit::from_limbs_le(limbs.clone());
                    if lit.limbs_le() != limbs.as_slice() {
                        // Trailing zero limbs would give two encodings of one value.
                        return Err(r.err_public("non-normalized nat literal limbs"));
                    }
                    values.push(Expr::lit(Literal::Nat(lit)));
                }
                EXPR_LIT_STR => values.push(Expr::lit(Literal::Str(r.str()?.to_string()))),
                EXPR_MDATA => {
                    let data = KVMap::read_body(r)?;
                    tasks.push(ExprTask::BuildMData(data));
                    tasks.push(ExprTask::Read);
                }
                EXPR_PROJ => {
                    let struct_name = Name::read_body(r)?;
                    let idx = r.u64()?;
                    tasks.push(ExprTask::BuildProj(struct_name, idx));
                    tasks.push(ExprTask::Read);
                }
                _ => return Err(r.err_public("unknown expr tag")),
            },
            ExprTask::BuildApp => {
                let a = values.pop().ok_or_else(|| underflow(r))?;
                let f = values.pop().ok_or_else(|| underflow(r))?;
                values.push(Expr::app(f, a));
            }
            ExprTask::BuildLam(binder_name) => {
                let body = values.pop().ok_or_else(|| underflow(r))?;
                let binder_type = values.pop().ok_or_else(|| underflow(r))?;
                let bi = binder_info_from_tag(r.u8()?)
                    .ok_or_else(|| r.err_public("unknown binder-info tag"))?;
                values.push(Expr::lam(binder_name, binder_type, body, bi));
            }
            ExprTask::BuildForall(binder_name) => {
                let body = values.pop().ok_or_else(|| underflow(r))?;
                let binder_type = values.pop().ok_or_else(|| underflow(r))?;
                let bi = binder_info_from_tag(r.u8()?)
                    .ok_or_else(|| r.err_public("unknown binder-info tag"))?;
                values.push(Expr::forall_e(binder_name, binder_type, body, bi));
            }
            ExprTask::BuildLet(decl_name) => {
                let body = values.pop().ok_or_else(|| underflow(r))?;
                let value = values.pop().ok_or_else(|| underflow(r))?;
                let type_ = values.pop().ok_or_else(|| underflow(r))?;
                let non_dep = r.bool()?;
                values.push(Expr::let_e(decl_name, type_, value, body, non_dep));
            }
            ExprTask::BuildMData(data) => {
                let expr = values.pop().ok_or_else(|| underflow(r))?;
                values.push(Expr::mdata(data, expr));
            }
            ExprTask::BuildProj(struct_name, idx) => {
                let expr = values.pop().ok_or_else(|| underflow(r))?;
                values.push(Expr::proj(struct_name, idx, expr));
            }
        }
    }
    match values.len() {
        1 => Ok(values.pop().expect("length checked")),
        _ => Err(r.err_public("expr value-stack did not reduce to a single root")),
    }
}

// ---- Diagnostic (the D8 typed error taxonomy, versioned on the wire) -------------------

pub const SCHEMA_DIAG: SchemaId = SchemaId {
    name: "fln.canon.diag",
    version: 1,
};

const SEV_INFO: u8 = 0;
const SEV_WARN: u8 = 1;
const SEV_ERROR: u8 = 2;

const RES_HEARTBEATS: u8 = 0;
const RES_REC_DEPTH: u8 = 1;
const RES_CANCELLED: u8 = 2;
const RES_MEMORY: u8 = 3;

fn write_resource(w: &mut CanonWriter, resource: &ResourceReason) {
    match resource {
        ResourceReason::Heartbeats { consumed, limit } => {
            w.u8(RES_HEARTBEATS);
            w.u64(*consumed);
            w.u64(*limit);
        }
        ResourceReason::RecursionDepth { limit } => {
            w.u8(RES_REC_DEPTH);
            w.u64(*limit);
        }
        ResourceReason::Cancelled => w.u8(RES_CANCELLED),
        ResourceReason::Memory { limit_bytes } => {
            w.u8(RES_MEMORY);
            w.u64(*limit_bytes);
        }
    }
}

fn read_resource(r: &mut CanonReader<'_>) -> Result<ResourceReason, CanonError> {
    Ok(match r.u8()? {
        RES_HEARTBEATS => ResourceReason::Heartbeats {
            consumed: r.u64()?,
            limit: r.u64()?,
        },
        RES_REC_DEPTH => ResourceReason::RecursionDepth { limit: r.u64()? },
        RES_CANCELLED => ResourceReason::Cancelled,
        RES_MEMORY => ResourceReason::Memory {
            limit_bytes: r.u64()?,
        },
        _ => return Err(r.err_public("unknown resource-reason tag")),
    })
}

// Variant tags in taxonomy declaration order — frozen; a new variant appends.
const EV_SYNTAX: u8 = 0;
const EV_MACRO: u8 = 1;
const EV_ELAB: u8 = 2;
const EV_KERNEL_REJECT: u8 = 3;
const EV_KERNEL_INCONCLUSIVE: u8 = 4;
const EV_ARTIFACT_CORRUPT: u8 = 5;
const EV_ARTIFACT_EPOCH: u8 = 6;
const EV_ABI: u8 = 7;
const EV_CAPABILITY: u8 = 8;
const EV_PLUGIN: u8 = 9;
const EV_BUILD: u8 = 10;
const EV_PROTOCOL: u8 = 11;
const EV_REPLAY: u8 = 12;
const EV_INTERNAL: u8 = 13;

fn write_error_value(w: &mut CanonWriter, value: &ErrorValue) {
    match value {
        ErrorValue::SyntaxFailure { message } => {
            w.u8(EV_SYNTAX);
            w.str(message);
        }
        ErrorValue::MacroFailure {
            macro_name,
            message,
        } => {
            w.u8(EV_MACRO);
            macro_name.write_body(w);
            w.str(message);
        }
        ErrorValue::ElaborationFailure { message } => {
            w.u8(EV_ELAB);
            w.str(message);
        }
        ErrorValue::KernelRejection {
            decl,
            stable_error_class,
            message,
        } => {
            w.u8(EV_KERNEL_REJECT);
            decl.write_body(w);
            w.str(stable_error_class);
            w.str(message);
        }
        ErrorValue::KernelInconclusive { decl, resource } => {
            w.u8(EV_KERNEL_INCONCLUSIVE);
            decl.write_body(w);
            write_resource(w, resource);
        }
        ErrorValue::ArtifactCorrupt { path, detail } => {
            w.u8(EV_ARTIFACT_CORRUPT);
            w.str(path);
            w.str(detail);
        }
        ErrorValue::ArtifactEpochMismatch {
            path,
            expected_epoch,
            found_epoch,
        } => {
            w.u8(EV_ARTIFACT_EPOCH);
            w.str(path);
            w.str(expected_epoch);
            w.str(found_epoch);
        }
        ErrorValue::AbiViolation { symbol, detail } => {
            w.u8(EV_ABI);
            w.str(symbol);
            w.str(detail);
        }
        ErrorValue::CapabilityDenied { capability, detail } => {
            w.u8(EV_CAPABILITY);
            w.str(capability);
            w.str(detail);
        }
        ErrorValue::PluginCrashed { plugin, detail } => {
            w.u8(EV_PLUGIN);
            w.str(plugin);
            w.str(detail);
        }
        ErrorValue::BuildFailure { job, detail } => {
            w.u8(EV_BUILD);
            w.str(job);
            w.str(detail);
        }
        ErrorValue::ProtocolFailure { detail } => {
            w.u8(EV_PROTOCOL);
            w.str(detail);
        }
        ErrorValue::ReplayDivergence { detail } => {
            w.u8(EV_REPLAY);
            w.str(detail);
        }
        ErrorValue::InternalInvariantViolation { invariant, detail } => {
            w.u8(EV_INTERNAL);
            w.str(invariant);
            w.str(detail);
        }
    }
}

fn read_error_value(r: &mut CanonReader<'_>) -> Result<ErrorValue, CanonError> {
    Ok(match r.u8()? {
        EV_SYNTAX => ErrorValue::SyntaxFailure {
            message: r.str()?.to_string(),
        },
        EV_MACRO => ErrorValue::MacroFailure {
            macro_name: Name::read_body(r)?,
            message: r.str()?.to_string(),
        },
        EV_ELAB => ErrorValue::ElaborationFailure {
            message: r.str()?.to_string(),
        },
        EV_KERNEL_REJECT => ErrorValue::KernelRejection {
            decl: Name::read_body(r)?,
            stable_error_class: r.str()?.to_string(),
            message: r.str()?.to_string(),
        },
        EV_KERNEL_INCONCLUSIVE => ErrorValue::KernelInconclusive {
            decl: Name::read_body(r)?,
            resource: read_resource(r)?,
        },
        EV_ARTIFACT_CORRUPT => ErrorValue::ArtifactCorrupt {
            path: r.str()?.to_string(),
            detail: r.str()?.to_string(),
        },
        EV_ARTIFACT_EPOCH => ErrorValue::ArtifactEpochMismatch {
            path: r.str()?.to_string(),
            expected_epoch: r.str()?.to_string(),
            found_epoch: r.str()?.to_string(),
        },
        EV_ABI => ErrorValue::AbiViolation {
            symbol: r.str()?.to_string(),
            detail: r.str()?.to_string(),
        },
        EV_CAPABILITY => ErrorValue::CapabilityDenied {
            capability: r.str()?.to_string(),
            detail: r.str()?.to_string(),
        },
        EV_PLUGIN => ErrorValue::PluginCrashed {
            plugin: r.str()?.to_string(),
            detail: r.str()?.to_string(),
        },
        EV_BUILD => ErrorValue::BuildFailure {
            job: r.str()?.to_string(),
            detail: r.str()?.to_string(),
        },
        EV_PROTOCOL => ErrorValue::ProtocolFailure {
            detail: r.str()?.to_string(),
        },
        EV_REPLAY => ErrorValue::ReplayDivergence {
            detail: r.str()?.to_string(),
        },
        EV_INTERNAL => ErrorValue::InternalInvariantViolation {
            invariant: r.str()?.to_string(),
            detail: r.str()?.to_string(),
        },
        _ => return Err(r.err_public("unknown error-value tag (newer taxonomy version?)")),
    })
}

impl Canonical for Diagnostic {
    const SCHEMA: SchemaId = SCHEMA_DIAG;

    fn write_body(&self, w: &mut CanonWriter) {
        w.str(&self.file_name);
        w.u64(self.pos.line as u64);
        w.u64(self.pos.column as u64);
        match &self.end_pos {
            Some(end) => {
                w.u8(1);
                w.u64(end.line as u64);
                w.u64(end.column as u64);
            }
            None => w.u8(0),
        }
        w.u8(match self.severity {
            Severity::Information => SEV_INFO,
            Severity::Warning => SEV_WARN,
            Severity::Error => SEV_ERROR,
        });
        match &self.error_name {
            Some(name) => {
                w.u8(1);
                name.write_body(w);
            }
            None => w.u8(0),
        }
        w.str(&self.caption);
        write_error_value(w, &self.value);
    }

    fn read_body(r: &mut CanonReader<'_>) -> Result<Diagnostic, CanonError> {
        let file_name = r.str()?.to_string();
        let line = usize::try_from(r.u64()?).map_err(|_| r.err_public("line overflow"))?;
        let column = usize::try_from(r.u64()?).map_err(|_| r.err_public("column overflow"))?;
        let end_pos = match r.u8()? {
            0 => None,
            1 => Some(Position {
                line: usize::try_from(r.u64()?).map_err(|_| r.err_public("line overflow"))?,
                column: usize::try_from(r.u64()?).map_err(|_| r.err_public("column overflow"))?,
            }),
            _ => return Err(r.err_public("non-canonical option tag")),
        };
        let severity = match r.u8()? {
            SEV_INFO => Severity::Information,
            SEV_WARN => Severity::Warning,
            SEV_ERROR => Severity::Error,
            _ => return Err(r.err_public("unknown severity tag")),
        };
        let error_name = match r.u8()? {
            0 => None,
            1 => Some(Name::read_body(r)?),
            _ => return Err(r.err_public("non-canonical option tag")),
        };
        let caption = r.str()?.to_string();
        let value = read_error_value(r)?;
        Ok(Diagnostic {
            file_name,
            pos: Position { line, column },
            end_pos,
            severity,
            error_name,
            caption,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::level::Level;

    // Test-only mutations used by the no-mock E2E lane. They deliberately restore
    // the exact bug class: syntax-depth recursion on a bounded worker stack. The
    // parent process must observe their fatal exit instead of accepting them.
    #[derive(Clone, Copy)]
    struct RecursiveLevelEncoder(fn(&Level, &mut CanonWriter, RecursiveLevelEncoder));

    impl RecursiveLevelEncoder {
        fn encode(self, level: &Level, w: &mut CanonWriter) {
            (self.0)(level, w, self);
        }
    }

    fn recursive_level_encoder_step(
        level: &Level,
        w: &mut CanonWriter,
        recurse: RecursiveLevelEncoder,
    ) {
        use fln_core::level::LevelView;
        match level.view() {
            LevelView::Zero => w.u8(LEVEL_ZERO),
            LevelView::Succ(inner) => {
                w.u8(LEVEL_SUCC);
                recurse.encode(inner, w);
                std::hint::black_box(w.buf.len());
            }
            _ => panic!("the level mutation probe expects a Succ chain"),
        }
    }

    fn recursive_level_encoder_mutant(level: &Level, w: &mut CanonWriter) {
        RecursiveLevelEncoder(recursive_level_encoder_step).encode(level, w);
    }

    #[derive(Clone, Copy)]
    struct RecursiveExprEncoder(fn(&Expr, &mut CanonWriter, RecursiveExprEncoder));

    impl RecursiveExprEncoder {
        fn encode(self, expr: &Expr, w: &mut CanonWriter) {
            (self.0)(expr, w, self);
        }
    }

    fn recursive_expr_encoder_step(
        expr: &Expr,
        w: &mut CanonWriter,
        recurse: RecursiveExprEncoder,
    ) {
        match expr.node() {
            ExprNode::BVar { idx } => {
                w.u8(EXPR_BVAR);
                w.u32(*idx);
            }
            ExprNode::App { f, a } => {
                w.u8(EXPR_APP);
                recurse.encode(f, w);
                recurse.encode(a, w);
                std::hint::black_box(w.buf.len());
            }
            _ => panic!("the expression mutation probe expects an App chain"),
        }
    }

    fn recursive_expr_encoder_mutant(expr: &Expr, w: &mut CanonWriter) {
        RecursiveExprEncoder(recursive_expr_encoder_step).encode(expr, w);
    }

    // Frozen test oracle for the recursive writer grammar that preceded 265f260.
    // Keep this deliberately shallow-only: its purpose is byte compatibility, not
    // lifecycle safety. Every nested canonical payload routes through the matching
    // pre-change helper so the iterative implementation never acts as its own oracle.
    fn prechange_name_body(name: &Name, w: &mut CanonWriter) {
        fn components(name: &Name, out: &mut Vec<Name>) {
            if name.is_anonymous() {
                return;
            }
            components(&name.parent(), out);
            out.push(name.clone());
        }

        let mut chain = Vec::new();
        components(name, &mut chain);
        w.u64(chain.len() as u64);
        for link in chain {
            match link.leaf() {
                NameLeaf::Str(value) => {
                    w.u8(NAME_STR);
                    w.str(value);
                }
                NameLeaf::Num(value, false) => {
                    w.u8(NAME_NUM);
                    w.u64(value);
                }
                NameLeaf::Num(value, true) => {
                    w.u8(NAME_NUM_OVERFLOW);
                    w.u64(value);
                }
                NameLeaf::Anonymous => w.u8(NAME_ANON),
            }
        }
    }

    fn prechange_level_body(level: &Level, w: &mut CanonWriter) {
        use fln_core::level::LevelView;

        match level.view() {
            LevelView::Zero => w.u8(LEVEL_ZERO),
            LevelView::Succ(inner) => {
                w.u8(LEVEL_SUCC);
                prechange_level_body(inner, w);
            }
            LevelView::Max(left, right) => {
                w.u8(LEVEL_MAX);
                prechange_level_body(left, w);
                prechange_level_body(right, w);
            }
            LevelView::IMax(left, right) => {
                w.u8(LEVEL_IMAX);
                prechange_level_body(left, w);
                prechange_level_body(right, w);
            }
            LevelView::Param(name) => {
                w.u8(LEVEL_PARAM);
                prechange_name_body(name, w);
            }
            LevelView::MVar(id) => {
                w.u8(LEVEL_MVAR);
                prechange_name_body(&id.0, w);
            }
        }
    }

    fn prechange_kvmap_body(map: &KVMap, w: &mut CanonWriter) {
        w.u64(map.entries().len() as u64);
        for (key, value) in map.entries() {
            prechange_name_body(key, w);
            match value {
                DataValue::OfString(value) => {
                    w.u8(DV_STRING);
                    w.str(value);
                }
                DataValue::OfBool(value) => {
                    w.u8(DV_BOOL);
                    w.bool(*value);
                }
                DataValue::OfName(value) => {
                    w.u8(DV_NAME);
                    prechange_name_body(value, w);
                }
                DataValue::OfNat(value) => {
                    w.u8(DV_NAT);
                    w.u64(*value);
                }
                DataValue::OfInt(value) => {
                    w.u8(DV_INT);
                    w.i64(*value);
                }
                DataValue::OfSyntax(value) => {
                    w.u8(DV_SYNTAX);
                    w.u64(value.0);
                }
            }
        }
    }

    fn prechange_expr_body(expr: &Expr, w: &mut CanonWriter) {
        match expr.node() {
            ExprNode::BVar { idx } => {
                w.u8(EXPR_BVAR);
                w.u32(*idx);
            }
            ExprNode::FVar { id } => {
                w.u8(EXPR_FVAR);
                prechange_name_body(&id.0, w);
            }
            ExprNode::MVar { id } => {
                w.u8(EXPR_MVAR);
                prechange_name_body(&id.0, w);
            }
            ExprNode::Sort { level } => {
                w.u8(EXPR_SORT);
                prechange_level_body(level, w);
            }
            ExprNode::Const { name, levels } => {
                w.u8(EXPR_CONST);
                prechange_name_body(name, w);
                w.u64(levels.len() as u64);
                for level in levels {
                    prechange_level_body(level, w);
                }
            }
            ExprNode::App { f, a } => {
                w.u8(EXPR_APP);
                prechange_expr_body(f, w);
                prechange_expr_body(a, w);
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                w.u8(EXPR_LAM);
                prechange_name_body(binder_name, w);
                prechange_expr_body(binder_type, w);
                prechange_expr_body(body, w);
                w.u8(binder_info_tag(*binder_info));
            }
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                w.u8(EXPR_FORALL);
                prechange_name_body(binder_name, w);
                prechange_expr_body(binder_type, w);
                prechange_expr_body(body, w);
                w.u8(binder_info_tag(*binder_info));
            }
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => {
                w.u8(EXPR_LET);
                prechange_name_body(decl_name, w);
                prechange_expr_body(type_, w);
                prechange_expr_body(value, w);
                prechange_expr_body(body, w);
                w.bool(*non_dep);
            }
            ExprNode::Lit { literal } => match literal {
                Literal::Nat(value) => {
                    w.u8(EXPR_LIT_NAT);
                    w.u64(value.limbs_le().len() as u64);
                    for limb in value.limbs_le() {
                        w.u64(*limb);
                    }
                }
                Literal::Str(value) => {
                    w.u8(EXPR_LIT_STR);
                    w.str(value);
                }
            },
            ExprNode::MData { data, expr } => {
                w.u8(EXPR_MDATA);
                prechange_kvmap_body(data, w);
                prechange_expr_body(expr, w);
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => {
                w.u8(EXPR_PROJ);
                prechange_name_body(struct_name, w);
                w.u64(*idx);
                prechange_expr_body(expr, w);
            }
        }
    }

    fn prechange_bytes(schema: SchemaId, write: impl FnOnce(&mut CanonWriter)) -> Vec<u8> {
        let mut writer = CanonWriter::new();
        writer.schema(schema);
        write(&mut writer);
        writer.into_bytes()
    }

    fn drop_pair_concurrently<T: Send + 'static>(left: T, right: T) {
        let barrier = std::sync::Arc::new(std::sync::Barrier::new(3));
        let spawn = |value, barrier: std::sync::Arc<std::sync::Barrier>| {
            std::thread::Builder::new()
                .stack_size(1024 * 1024)
                .spawn(move || {
                    barrier.wait();
                    drop(value);
                })
                .expect("spawn concurrent dropper")
        };
        let left_thread = spawn(left, barrier.clone());
        let right_thread = spawn(right, barrier.clone());
        barrier.wait();
        left_thread.join().expect("left dropper completes");
        right_thread.join().expect("right dropper completes");
    }

    /// Deterministic value generator (LCG — no external randomness, D1).
    struct Gen(u64);

    impl Gen {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0
        }

        fn range(&mut self, bound: u64) -> u64 {
            self.next() % bound
        }

        fn name(&mut self, depth: u32) -> Name {
            if depth == 0 || self.range(4) == 0 {
                return Name::anonymous();
            }
            let pre = self.name(depth - 1);
            if self.range(2) == 0 {
                Name::str(pre, format!("c{}", self.range(20)))
            } else {
                Name::num(pre, self.range(1000))
            }
        }

        fn level(&mut self, depth: u32) -> Level {
            if depth == 0 {
                return match self.range(3) {
                    0 => Level::zero(),
                    1 => Level::param(self.name(2)),
                    _ => Level::mvar(LMVarId(self.name(2))),
                };
            }
            match self.range(4) {
                0 => self.level(depth - 1).succ().expect("shallow"),
                1 => Level::max(self.level(depth - 1), self.level(depth - 1)).expect("shallow"),
                2 => Level::imax(self.level(depth - 1), self.level(depth - 1)).expect("shallow"),
                _ => self.level(0),
            }
        }

        fn expr(&mut self, depth: u32) -> Expr {
            if depth == 0 {
                return match self.range(5) {
                    0 => Expr::bvar(self.range(64) as u32).expect("small"),
                    1 => Expr::fvar(FVarId(self.name(2))),
                    2 => Expr::sort(self.level(1)),
                    3 => Expr::lit(Literal::Nat(NatLit::from_u64(self.next()))),
                    _ => Expr::const_(self.name(2), vec![self.level(1)]),
                };
            }
            match self.range(6) {
                0 => Expr::app(self.expr(depth - 1), self.expr(depth - 1)),
                1 => Expr::lam(
                    self.name(1),
                    self.expr(depth - 1),
                    self.expr(depth - 1),
                    BinderInfo::Implicit,
                ),
                2 => Expr::forall_e(
                    self.name(1),
                    self.expr(depth - 1),
                    self.expr(depth - 1),
                    BinderInfo::Default,
                ),
                3 => Expr::let_e(
                    self.name(1),
                    self.expr(depth - 1),
                    self.expr(depth - 1),
                    self.expr(depth - 1),
                    self.range(2) == 0,
                ),
                4 => Expr::proj(self.name(2), self.range(8), self.expr(depth - 1)),
                _ => Expr::mdata(KVMap::new(), self.expr(depth - 1)),
            }
        }
    }

    #[test]
    fn name_round_trip_property() {
        let mut generator = Gen(1);
        for _ in 0..200 {
            let name = generator.name(6);
            let bytes = name.to_canonical_bytes();
            assert_eq!(
                Name::from_canonical_bytes(&bytes).expect("round-trip"),
                name
            );
        }
    }

    #[test]
    fn level_round_trip_property() {
        let mut generator = Gen(2);
        for _ in 0..200 {
            let level = generator.level(4);
            let bytes = level.to_canonical_bytes();
            assert_eq!(
                Level::from_canonical_bytes(&bytes).expect("round-trip"),
                level
            );
        }
    }

    #[test]
    fn expr_round_trip_property() {
        let mut generator = Gen(3);
        for _ in 0..100 {
            let expr = generator.expr(4);
            let bytes = expr.to_canonical_bytes();
            let back = Expr::from_canonical_bytes(&bytes).expect("round-trip");
            assert_eq!(back, expr);
            assert_eq!(back.data(), expr.data(), "observables survive the trip");
        }
    }

    #[test]
    fn iterative_encoders_cover_every_level_and_expr_constructor() {
        let n = Name::str(Name::anonymous(), "n");
        let zero = Level::zero();
        let param = Level::param(n.clone());
        let mvar_level = Level::mvar(LMVarId(n.clone()));
        let levels = vec![
            zero.clone(),
            zero.clone().succ().expect("packs"),
            Level::max(param.clone(), zero.clone()).expect("packs"),
            Level::imax(mvar_level.clone(), param.clone()).expect("packs"),
            param.clone(),
            mvar_level.clone(),
        ];
        for level in levels {
            let bytes = level.to_canonical_bytes();
            let decoded = Level::from_canonical_bytes(&bytes).expect("level round-trip");
            assert_eq!(decoded.to_canonical_bytes(), bytes);
        }

        let leaf = Expr::bvar(0).expect("small");
        let mut metadata = KVMap::new();
        metadata.insert(n.clone(), DataValue::OfBool(true));
        let mut expressions = vec![
            leaf.clone(),
            Expr::fvar(FVarId(n.clone())),
            Expr::mvar(MVarId(n.clone())),
            Expr::sort(param.clone()),
            Expr::const_(n.clone(), vec![param.clone(), mvar_level]),
            Expr::app(leaf.clone(), leaf.clone()),
            Expr::let_e(n.clone(), leaf.clone(), leaf.clone(), leaf.clone(), true),
            Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![1, 2]))),
            Expr::lit(Literal::Str("value".to_string())),
            Expr::mdata(metadata, leaf.clone()),
            Expr::proj(n.clone(), 3, leaf.clone()),
        ];
        for info in [
            BinderInfo::Default,
            BinderInfo::Implicit,
            BinderInfo::StrictImplicit,
            BinderInfo::InstImplicit,
        ] {
            expressions.push(Expr::lam(n.clone(), leaf.clone(), leaf.clone(), info));
            expressions.push(Expr::forall_e(n.clone(), leaf.clone(), leaf.clone(), info));
        }
        for expr in expressions {
            let bytes = expr.to_canonical_bytes();
            let decoded = Expr::from_canonical_bytes(&bytes).expect("expr round-trip");
            assert_eq!(decoded.to_canonical_bytes(), bytes);
            assert_eq!(decoded.data(), expr.data());
        }
    }

    #[test]
    fn iterative_encoders_match_the_prechange_recursive_grammar() {
        let base = Name::str(Name::anonymous(), "Lean");
        let names = [
            Name::anonymous(),
            base.clone(),
            Name::num(base.clone(), 17),
            Name::num_overflowing(base.clone(), u64::MAX),
        ];
        for name in &names {
            assert_eq!(
                name.to_canonical_bytes(),
                prechange_bytes(SCHEMA_NAME, |writer| prechange_name_body(name, writer))
            );
        }

        let zero = Level::zero();
        let param = Level::param(base.clone());
        let mvar_level = Level::mvar(LMVarId(Name::num(base.clone(), 3)));
        let levels = [
            zero.clone(),
            zero.clone().succ().expect("shallow level"),
            Level::max(param.clone(), mvar_level.clone()).expect("shallow level"),
            Level::imax(mvar_level.clone(), param.clone()).expect("shallow level"),
            param.clone(),
            mvar_level.clone(),
        ];
        for level in &levels {
            assert_eq!(
                level.to_canonical_bytes(),
                prechange_bytes(SCHEMA_LEVEL, |writer| prechange_level_body(level, writer))
            );
        }

        let leaf = Expr::bvar(7).expect("small bvar");
        let mut metadata = KVMap::new();
        metadata.insert(base.clone(), DataValue::OfString("value".to_string()));
        metadata.insert(Name::num(base.clone(), 1), DataValue::OfBool(true));
        metadata.insert(
            Name::num(base.clone(), 2),
            DataValue::OfName(Name::str(base.clone(), "Meta")),
        );
        metadata.insert(Name::num(base.clone(), 3), DataValue::OfNat(42));
        metadata.insert(Name::num(base.clone(), 4), DataValue::OfInt(-7));
        metadata.insert(
            Name::num(base.clone(), 5),
            DataValue::OfSyntax(SyntaxHandle(9)),
        );

        let mut expressions = vec![
            leaf.clone(),
            Expr::fvar(FVarId(base.clone())),
            Expr::mvar(MVarId(Name::num(base.clone(), 6))),
            Expr::sort(param.clone()),
            Expr::const_(base.clone(), vec![param.clone(), mvar_level]),
            Expr::app(leaf.clone(), Expr::sort(zero)),
            Expr::let_e(base.clone(), leaf.clone(), leaf.clone(), leaf.clone(), true),
            Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![1, 2]))),
            Expr::lit(Literal::Str("text".to_string())),
            Expr::mdata(metadata, leaf.clone()),
            Expr::proj(base.clone(), 3, leaf.clone()),
        ];
        for binder_info in [
            BinderInfo::Default,
            BinderInfo::Implicit,
            BinderInfo::StrictImplicit,
            BinderInfo::InstImplicit,
        ] {
            expressions.push(Expr::lam(
                base.clone(),
                leaf.clone(),
                leaf.clone(),
                binder_info,
            ));
            expressions.push(Expr::forall_e(
                base.clone(),
                leaf.clone(),
                leaf.clone(),
                binder_info,
            ));
        }
        for expr in &expressions {
            assert_eq!(
                expr.to_canonical_bytes(),
                prechange_bytes(SCHEMA_EXPR, |writer| prechange_expr_body(expr, writer))
            );
        }

        let mut generator = Gen(0x6a09_e667_f3bc_c909);
        for sample in 0..256 {
            let name = generator.name(6);
            assert_eq!(
                name.to_canonical_bytes(),
                prechange_bytes(SCHEMA_NAME, |writer| prechange_name_body(&name, writer)),
                "Name sample {sample}"
            );

            let level = generator.level(5);
            assert_eq!(
                level.to_canonical_bytes(),
                prechange_bytes(SCHEMA_LEVEL, |writer| prechange_level_body(&level, writer)),
                "Level sample {sample}"
            );

            let expr = generator.expr(4);
            assert_eq!(
                expr.to_canonical_bytes(),
                prechange_bytes(SCHEMA_EXPR, |writer| prechange_expr_body(&expr, writer)),
                "Expr sample {sample}"
            );
        }
    }

    #[test]
    fn kvmap_round_trip_preserves_order() {
        let mut map = KVMap::new();
        map.insert(Name::str(Name::anonymous(), "b"), DataValue::OfNat(2));
        map.insert(Name::str(Name::anonymous(), "a"), DataValue::OfBool(true));
        map.insert(
            Name::str(Name::anonymous(), "s"),
            DataValue::OfSyntax(SyntaxHandle(7)),
        );
        let bytes = map.to_canonical_bytes();
        let back = KVMap::from_canonical_bytes(&bytes).expect("round-trip");
        assert_eq!(back, map);
        assert_eq!(back.entries()[0].0, map.entries()[0].0);
    }

    #[test]
    fn encoding_is_injective_on_a_corpus() {
        // One encoding per value, one value per encoding: no two distinct generated
        // values share bytes.
        let mut generator = Gen(4);
        let mut seen = std::collections::BTreeMap::new();
        for _ in 0..200 {
            let expr = generator.expr(3);
            let bytes = expr.to_canonical_bytes();
            if let Some(previous) = seen.insert(bytes, expr.clone()) {
                assert_eq!(previous, expr, "distinct values shared an encoding");
            }
        }
    }

    #[test]
    fn malformed_inputs_are_typed_errors_never_panics() {
        let cases: [&[u8]; 5] = [
            b"",
            b"\x01",
            b"\xff\xff\xff\xff\xff\xff\xff\xff",
            // Valid schema header for Name, then garbage.
            &{
                let mut w = CanonWriter::new();
                w.schema(SCHEMA_NAME);
                w.u64(1);
                w.u8(9); // unknown component tag
                w.into_bytes()
            },
            // Huge declared length with no bytes behind it.
            &{
                let mut w = CanonWriter::new();
                w.schema(SCHEMA_NAME);
                w.u64(u64::MAX);
                w.into_bytes()
            },
        ];
        for bytes in cases {
            assert!(Name::from_canonical_bytes(bytes).is_err());
            assert!(Expr::from_canonical_bytes(bytes).is_err());
        }
        // Trailing garbage after a valid value is non-canonical.
        let mut bytes = Name::anonymous().to_canonical_bytes();
        bytes.push(0);
        assert!(matches!(
            Name::from_canonical_bytes(&bytes),
            Err(CanonError {
                what: "trailing bytes after value",
                ..
            })
        ));
        // Non-normalized nat limbs are rejected (two encodings of one value).
        let mut w = CanonWriter::new();
        w.schema(SCHEMA_EXPR);
        w.u8(super::EXPR_LIT_NAT);
        w.u64(2);
        w.u64(5);
        w.u64(0); // trailing zero limb
        assert!(Expr::from_canonical_bytes(&w.into_bytes()).is_err());
    }

    #[test]
    fn schema_headers_are_checked() {
        let name_bytes = Name::anonymous().to_canonical_bytes();
        assert!(Level::from_canonical_bytes(&name_bytes).is_err());
    }

    /// franken_lean-fnj: a deeply nested hostile encoding must decode to a TYPED
    /// error, never a stack-overflow abort. Run on a deliberately small (1 MiB)
    /// stack — a recursive decoder would `SIGABRT` here; the iterative one returns
    /// `Err`. Two properties in one safe check: (a) `.join()` returning `Ok` proves
    /// no abort occurred; (b) the error is `input truncated`, not a depth cap,
    /// proving the decoder walked all 2,000,000 tags rather than bailing at some
    /// artificial limit that would false-reject a legitimately deep olean. The tag
    /// chains carry no operands, so no deep tree is ever built (that would recurse
    /// on `Drop` — a separate concern tracked in franken_lean-fnj).
    #[test]
    fn deeply_nested_input_is_a_typed_error_not_a_stack_overflow() {
        let outcome = std::thread::Builder::new()
            .stack_size(1024 * 1024)
            .spawn(|| {
                let mut expr_bytes = CanonWriter::new();
                expr_bytes.schema(SCHEMA_EXPR);
                let mut expr_bytes = expr_bytes.into_bytes();
                expr_bytes.extend(std::iter::repeat_n(super::EXPR_APP, 2_000_000));
                let expr_err = Expr::from_canonical_bytes(&expr_bytes)
                    .expect_err("truncated deep App chain must be a typed error");
                assert_eq!(expr_err.what, "input truncated", "no artificial depth cap");

                let mut level_bytes = CanonWriter::new();
                level_bytes.schema(SCHEMA_LEVEL);
                let mut level_bytes = level_bytes.into_bytes();
                level_bytes.extend(std::iter::repeat_n(super::LEVEL_MAX, 2_000_000));
                let level_err = Level::from_canonical_bytes(&level_bytes)
                    .expect_err("truncated deep Max chain must be a typed error");
                assert_eq!(level_err.what, "input truncated", "no artificial depth cap");
            })
            .expect("spawn decoder thread")
            .join();
        assert!(
            outcome.is_ok(),
            "decoding deep hostile input aborted the thread (stack overflow) instead of erroring"
        );
    }

    /// franken_lean-canon-stack-safe-drop-6gy: exercise valid deep decode,
    /// byte-identical re-encoding, shared-root release, and partial-error cleanup
    /// in a sacrificial process whose worker has a 1 MiB stack.  The outer test
    /// remains alive if a recursive mutation aborts the child.
    #[test]
    fn deep_valid_lifecycle_is_stack_safe_in_subprocess() {
        const CHILD: &str = "FLN_CANON_LIFECYCLE_CHILD";
        const DEPTH: &str = "FLN_CANON_LIFECYCLE_DEPTH";
        const RUNS: &str = "FLN_CANON_LIFECYCLE_RUNS";
        const ITERATION: &str = "FLN_CANON_LIFECYCLE_ITERATION";
        const MUTANT: &str = "FLN_CANON_LIFECYCLE_MUTANT";
        const NAME_DEPTH: &str = "FLN_CANON_LIFECYCLE_NAME_DEPTH";

        if std::env::var_os(CHILD).is_some() {
            let depth = std::env::var(DEPTH)
                .ok()
                .and_then(|value| value.parse::<usize>().ok())
                .unwrap_or(100_000);
            let iteration = std::env::var(ITERATION).unwrap_or_else(|_| "0".to_string());
            let mutant = std::env::var(MUTANT).ok();
            let name_depth = std::env::var(NAME_DEPTH)
                .ok()
                .and_then(|value| value.parse::<usize>().ok())
                .unwrap_or(depth.min(100_000));
            let outcome = std::thread::Builder::new()
                .name("canon-lifecycle-probe".to_string())
                .stack_size(1024 * 1024)
                .spawn(move || {
                    let mut level = Level::zero();
                    for _ in 0..depth {
                        level = level.succ().expect("depth is below the level covenant");
                    }
                    if mutant.as_deref() == Some("recursive-level-encoder") {
                        recursive_level_encoder_mutant(&level, &mut CanonWriter::new());
                        panic!("recursive Level encoder mutation unexpectedly survived");
                    }
                    let level_bytes = level.to_canonical_bytes();
                    let decoded_level = Level::from_canonical_bytes(&level_bytes)
                        .expect("deep valid level decodes");
                    assert_eq!(decoded_level.to_canonical_bytes(), level_bytes);

                    let level_clone = decoded_level.clone();
                    drop_pair_concurrently(decoded_level, level_clone);

                    let leaf = Expr::bvar(0).expect("small bvar");
                    let mut expr = leaf.clone();
                    for _ in 0..depth {
                        expr = Expr::app(expr, leaf.clone());
                    }
                    if mutant.as_deref() == Some("recursive-expr-encoder") {
                        recursive_expr_encoder_mutant(&expr, &mut CanonWriter::new());
                        panic!("recursive Expr encoder mutation unexpectedly survived");
                    }
                    let expr_bytes = expr.to_canonical_bytes();
                    let decoded_expr = Expr::from_canonical_bytes(&expr_bytes)
                        .expect("deep valid expression decodes");
                    assert_eq!(decoded_expr.to_canonical_bytes(), expr_bytes);

                    let expr_clone = decoded_expr.clone();
                    drop_pair_concurrently(decoded_expr, expr_clone);

                    // Deep names are recursive payloads of multiple Expr/Level
                    // constructors. Their encoding and final Arc release must not
                    // punch a hidden recursive hole through the outer lifecycle.
                    let mut deep_name = Name::anonymous();
                    for _ in 0..name_depth {
                        deep_name = Name::str(deep_name, "n");
                    }
                    let name_bytes = deep_name.to_canonical_bytes();
                    let decoded_name = Name::from_canonical_bytes(&name_bytes)
                        .expect("deep valid name decodes");
                    assert_eq!(decoded_name.to_canonical_bytes(), name_bytes);
                    let named_expr = Expr::const_(deep_name.clone(), Vec::new());
                    let named_expr_bytes = named_expr.to_canonical_bytes();
                    assert_eq!(
                        Expr::from_canonical_bytes(&named_expr_bytes)
                            .expect("deep name in Expr decodes")
                            .to_canonical_bytes(),
                        named_expr_bytes
                    );
                    let named_level = Level::param(deep_name.clone());
                    let named_level_bytes = named_level.to_canonical_bytes();
                    assert_eq!(
                        Level::from_canonical_bytes(&named_level_bytes)
                            .expect("deep name in Level decodes")
                            .to_canonical_bytes(),
                        named_level_bytes
                    );
                    drop(named_expr);
                    drop(named_level);
                    let decoded_name_clone = decoded_name.clone();
                    drop_pair_concurrently(decoded_name, decoded_name_clone);
                    drop(deep_name);

                    // A later missing child must clean up the already-built deep
                    // first child without recursively unwinding its Arc chain.
                    let mut partial_level = CanonWriter::new();
                    partial_level.schema(SCHEMA_LEVEL);
                    partial_level.u8(LEVEL_MAX);
                    level.write_body(&mut partial_level);
                    assert_eq!(
                        Level::from_canonical_bytes(&partial_level.into_bytes())
                            .expect_err("second Max child is absent")
                            .what,
                        "input truncated"
                    );

                    let mut partial_expr = CanonWriter::new();
                    partial_expr.schema(SCHEMA_EXPR);
                    partial_expr.u8(EXPR_APP);
                    expr.write_body(&mut partial_expr);
                    assert_eq!(
                        Expr::from_canonical_bytes(&partial_expr.into_bytes())
                            .expect_err("second App child is absent")
                            .what,
                        "input truncated"
                    );

                    let level_hash = crate::domain::hash(
                        crate::domain::Domain::Fixture,
                        &level_bytes,
                    );
                    let expr_hash =
                        crate::domain::hash(crate::domain::Domain::Fixture, &expr_bytes);
                    drop(expr);
                    drop(level);
                    drop(leaf);

                    // Recovery after both partial failures uses the same real codec.
                    let recovery = Expr::bvar(7).expect("small").to_canonical_bytes();
                    Expr::from_canonical_bytes(&recovery).expect("shallow recovery decode");

                    println!(
                        "{{\"schema\":\"fln.e2e.canon-lifecycle\",\"version\":1,\"bead\":\"franken_lean-canon-stack-safe-drop-6gy\",\"invariant\":\"FL-INV-07\",\"scenario\":\"deep-valid-lifecycle\",\"iteration\":{iteration},\"depth\":{depth},\"name_depth\":{name_depth},\"stack_bytes\":1048576,\"level_bytes\":{},\"expr_bytes\":{},\"level_hash\":\"{}\",\"expr_hash\":\"{}\",\"expected\":\"pass\",\"actual\":\"pass\",\"cleanup\":\"complete\",\"final_state\":\"recovery-decoded\"}}",
                        level_bytes.len(),
                        expr_bytes.len(),
                        level_hash,
                        expr_hash,
                    );
                })
                .expect("spawn bounded-stack probe")
                .join();
            assert!(outcome.is_ok(), "bounded-stack lifecycle worker panicked");
            return;
        }

        let runs = std::env::var(RUNS)
            .ok()
            .and_then(|value| value.parse::<usize>().ok())
            .unwrap_or(1);
        let executable = std::env::current_exe().expect("locate current test binary");
        for iteration in 0..runs {
            let output = std::process::Command::new(&executable)
                .arg("--exact")
                .arg("canon::tests::deep_valid_lifecycle_is_stack_safe_in_subprocess")
                .arg("--nocapture")
                .env(CHILD, "1")
                .env(ITERATION, iteration.to_string())
                .output()
                .expect("launch sacrificial lifecycle process");
            assert!(
                output.status.success(),
                "lifecycle child {iteration} failed: status={:?}\nstdout={}\nstderr={}",
                output.status,
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
            );
            print!("{}", String::from_utf8_lossy(&output.stdout));
        }
    }
}
