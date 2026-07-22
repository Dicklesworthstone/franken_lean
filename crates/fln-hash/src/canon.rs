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

use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::{DataValue, KVMap, SyntaxHandle};

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
        fn components(name: &Name, out: &mut Vec<Name>) {
            if name.is_anonymous() {
                return;
            }
            components(&name.parent(), out);
            out.push(name.clone());
        }
        let mut chain = Vec::new();
        components(self, &mut chain);
        w.u64(chain.len() as u64);
        for link in chain {
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
        match self.view() {
            LevelView::Zero => w.u8(LEVEL_ZERO),
            LevelView::Succ(inner) => {
                w.u8(LEVEL_SUCC);
                inner.write_body(w);
            }
            LevelView::Max(a, b) => {
                w.u8(LEVEL_MAX);
                a.write_body(w);
                b.write_body(w);
            }
            LevelView::IMax(a, b) => {
                w.u8(LEVEL_IMAX);
                a.write_body(w);
                b.write_body(w);
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

    fn read_body(r: &mut CanonReader<'_>) -> Result<Level, CanonError> {
        Ok(match r.u8()? {
            LEVEL_ZERO => Level::zero(),
            LEVEL_SUCC => Level::read_body(r)?
                .succ()
                .map_err(|_| r.err_public("level depth exceeds the 24-bit covenant"))?,
            LEVEL_MAX => {
                let a = Level::read_body(r)?;
                let b = Level::read_body(r)?;
                Level::max(a, b)
                    .map_err(|_| r.err_public("level depth exceeds the 24-bit covenant"))?
            }
            LEVEL_IMAX => {
                let a = Level::read_body(r)?;
                let b = Level::read_body(r)?;
                Level::imax(a, b)
                    .map_err(|_| r.err_public("level depth exceeds the 24-bit covenant"))?
            }
            LEVEL_PARAM => Level::param(Name::read_body(r)?),
            LEVEL_MVAR => Level::mvar(LMVarId(Name::read_body(r)?)),
            _ => return Err(r.err_public("unknown level tag")),
        })
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
        match self.node() {
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
                f.write_body(w);
                a.write_body(w);
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                w.u8(EXPR_LAM);
                binder_name.write_body(w);
                binder_type.write_body(w);
                body.write_body(w);
                w.u8(binder_info_tag(*binder_info));
            }
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                w.u8(EXPR_FORALL);
                binder_name.write_body(w);
                binder_type.write_body(w);
                body.write_body(w);
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
                decl_name.write_body(w);
                type_.write_body(w);
                value.write_body(w);
                body.write_body(w);
                w.bool(*non_dep);
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
                expr.write_body(w);
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => {
                w.u8(EXPR_PROJ);
                struct_name.write_body(w);
                w.u64(*idx);
                expr.write_body(w);
            }
        }
    }

    fn read_body(r: &mut CanonReader<'_>) -> Result<Expr, CanonError> {
        Ok(match r.u8()? {
            EXPR_BVAR => Expr::bvar(r.u32()?)
                .map_err(|_| r.err_public("bvar exceeds the 20-bit range covenant"))?,
            EXPR_FVAR => Expr::fvar(FVarId(Name::read_body(r)?)),
            EXPR_MVAR => Expr::mvar(MVarId(Name::read_body(r)?)),
            EXPR_SORT => Expr::sort(Level::read_body(r)?),
            EXPR_CONST => {
                let name = Name::read_body(r)?;
                let count = r.u64()?;
                let mut levels = Vec::new();
                for _ in 0..count {
                    levels.push(Level::read_body(r)?);
                }
                Expr::const_(name, levels)
            }
            EXPR_APP => {
                let f = Expr::read_body(r)?;
                let a = Expr::read_body(r)?;
                Expr::app(f, a)
            }
            EXPR_LAM => {
                let binder_name = Name::read_body(r)?;
                let binder_type = Expr::read_body(r)?;
                let body = Expr::read_body(r)?;
                let bi = binder_info_from_tag(r.u8()?)
                    .ok_or_else(|| r.err_public("unknown binder-info tag"))?;
                Expr::lam(binder_name, binder_type, body, bi)
            }
            EXPR_FORALL => {
                let binder_name = Name::read_body(r)?;
                let binder_type = Expr::read_body(r)?;
                let body = Expr::read_body(r)?;
                let bi = binder_info_from_tag(r.u8()?)
                    .ok_or_else(|| r.err_public("unknown binder-info tag"))?;
                Expr::forall_e(binder_name, binder_type, body, bi)
            }
            EXPR_LET => {
                let decl_name = Name::read_body(r)?;
                let type_ = Expr::read_body(r)?;
                let value = Expr::read_body(r)?;
                let body = Expr::read_body(r)?;
                let non_dep = r.bool()?;
                Expr::let_e(decl_name, type_, value, body, non_dep)
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
                Expr::lit(Literal::Nat(lit))
            }
            EXPR_LIT_STR => Expr::lit(Literal::Str(r.str()?.to_string())),
            EXPR_MDATA => {
                let data = KVMap::read_body(r)?;
                let expr = Expr::read_body(r)?;
                Expr::mdata(data, expr)
            }
            EXPR_PROJ => {
                let struct_name = Name::read_body(r)?;
                let idx = r.u64()?;
                let expr = Expr::read_body(r)?;
                Expr::proj(struct_name, idx, expr)
            }
            _ => return Err(r.err_public("unknown expr tag")),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::level::Level;

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
}
