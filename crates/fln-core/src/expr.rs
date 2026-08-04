//! The kernel expression inventory with Reference-observable cached data
//! (plan §1.1, §21): hash, approxDepth, loose-bvar range, has-fvar/has-mvar/
//! has-level-mvar/has-level-param flags — these are API, not internals.
//!
//! Semantics anchors (vendor/lean4-src at the SUITE.lock pin):
//! * `Expr.Data` packing — src/Lean/Expr.lean:119-159: bits 0-31 hash, 32-39
//!   approxDepth, 40 hasFVar, 41 hasExprMVar, 42 hasLevelMVar, 43 hasLevelParam,
//!   44-63 looseBVarRange (20 bits);
//! * `lean_expr_mk_data` — src/kernel/expr.cpp:105-115: hash truncated to 32 bits,
//!   approxDepth saturated at 255, looseBVarRange limited to 1048575 (upstream
//!   panics above; we return a typed error — malformed input must not panic);
//! * `lean_expr_mk_app_data` — src/kernel/expr.cpp:120-126: flags = OR of children
//!   masked to bits 40-43; hash = mix of the two FULL 64-bit data words, truncated;
//!   depth = max+1 capped; range = max;
//! * the `@[computed_field] data` per-constructor formulas — src/Lean/Expr.lean:471-514
//!   (seeds: lit=3, const=5, bvar=7, sort=11, fvar=13, mvar=17);
//! * `Literal` — Expr.lean:18-39; `BinderInfo` — Expr.lean:71-86 (hash constants
//!   947/1019/1087/1153; toUInt64 encodings 0-3);
//! * `FVarId`/`MVarId` — Expr.lean:257-259, 604-612 class of wrappers: derived
//!   `Hashable` = ctor-index 0 mixed with the field hash;
//! * `Nat` hash = the value mod 2^64 (src/Init/Data/Hashable.lean:15-16); `List` hash
//!   = left fold of `mixHash` from seed 7 (Hashable.lean:37-38).

use std::sync::Arc;

use crate::lean_hash::{mix_hash, string_hash};
use crate::level::Level;
use crate::name::Name;
use crate::options::KVMap;

/// Maximum representable loose-bvar range (2^20 - 1); expr.cpp:109.
pub const MAX_LOOSE_BVAR_RANGE: u32 = 1_048_575;

/// Free-variable identity: a `Name` wrapper with the derived hash.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FVarId(pub Name);

impl FVarId {
    pub fn hash(&self) -> u64 {
        mix_hash(0, self.0.hash())
    }
}

/// Expression-metavariable identity: a `Name` wrapper with the derived hash.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MVarId(pub Name);

impl MVarId {
    pub fn hash(&self) -> u64 {
        mix_hash(0, self.0.hash())
    }
}

/// `BinderInfo` (Expr.lean:71-86).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum BinderInfo {
    #[default]
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

impl BinderInfo {
    /// `BinderInfo.toUInt64` (Expr.lean:163-168).
    pub fn to_u64(self) -> u64 {
        match self {
            BinderInfo::Default => 0,
            BinderInfo::Implicit => 1,
            BinderInfo::StrictImplicit => 2,
            BinderInfo::InstImplicit => 3,
        }
    }

    /// `BinderInfo.hash` (Expr.lean:82-86). NOT mixed into `Expr` data — a separate
    /// observable.
    pub fn hash(self) -> u64 {
        match self {
            BinderInfo::Default => 947,
            BinderInfo::Implicit => 1019,
            BinderInfo::StrictImplicit => 1087,
            BinderInfo::InstImplicit => 1153,
        }
    }
}

/// An unbounded natural-number literal value: little-endian 64-bit limbs, normalized
/// (no trailing zero limbs; empty = 0). Value identity only — arithmetic is
/// fln-bignum's charter; fln-core stores, compares, and hashes.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NatLit {
    limbs: Vec<u64>,
}

impl NatLit {
    pub fn from_u64(value: u64) -> NatLit {
        NatLit {
            limbs: if value == 0 { Vec::new() } else { vec![value] },
        }
    }

    /// Construct from little-endian limbs; trailing zeros are normalized away.
    pub fn from_limbs_le(mut limbs: Vec<u64>) -> NatLit {
        while limbs.last() == Some(&0) {
            limbs.pop();
        }
        NatLit { limbs }
    }

    pub fn limbs_le(&self) -> &[u64] {
        &self.limbs
    }

    /// The `Hashable Nat` observable: the value mod 2^64, i.e. the low limb.
    pub fn hash(&self) -> u64 {
        self.limbs.first().copied().unwrap_or(0)
    }

    pub fn to_u64(&self) -> Option<u64> {
        match self.limbs.len() {
            0 => Some(0),
            1 => Some(self.limbs[0]),
            _ => None,
        }
    }
}

impl PartialOrd for NatLit {
    fn partial_cmp(&self, other: &NatLit) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for NatLit {
    fn cmp(&self, other: &NatLit) -> std::cmp::Ordering {
        self.limbs
            .len()
            .cmp(&other.limbs.len())
            .then_with(|| self.limbs.iter().rev().cmp(other.limbs.iter().rev()))
    }
}

/// `Literal` (Expr.lean:18-39).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    Nat(NatLit),
    Str(String),
}

impl Literal {
    /// `Literal.hash` (Expr.lean:25-27): the payload hash, no constructor tag.
    pub fn hash(&self) -> u64 {
        match self {
            Literal::Nat(n) => n.hash(),
            Literal::Str(s) => string_hash(s),
        }
    }

    /// `Literal.lt` (Expr.lean:35-39): `natVal < strVal`; payload order within.
    pub fn lt(&self, other: &Literal) -> bool {
        match (self, other) {
            (Literal::Nat(a), Literal::Nat(b)) => a < b,
            (Literal::Nat(_), Literal::Str(_)) => true,
            (Literal::Str(_), Literal::Nat(_)) => false,
            (Literal::Str(a), Literal::Str(b)) => a < b,
        }
    }
}

/// The packed observable word (`Expr.Data`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExprData(pub u64);

impl ExprData {
    /// `lean_expr_mk_data` with the range panic replaced by a typed refusal. The hash
    /// argument is the full 64-bit mix; only its low 32 bits are stored. approxDepth
    /// saturates at 255.
    fn pack(
        hash: u64,
        loose_bvar_range: u32,
        approx_depth: u32,
        has_fvar: bool,
        has_expr_mvar: bool,
        has_level_mvar: bool,
        has_level_param: bool,
    ) -> Result<ExprData, TooManyBoundVars> {
        if loose_bvar_range > MAX_LOOSE_BVAR_RANGE {
            return Err(TooManyBoundVars {
                range: loose_bvar_range,
            });
        }
        let depth = approx_depth.min(255);
        Ok(ExprData(
            u64::from(hash as u32)
                + (u64::from(depth) << 32)
                + (u64::from(has_fvar) << 40)
                + (u64::from(has_expr_mvar) << 41)
                + (u64::from(has_level_mvar) << 42)
                + (u64::from(has_level_param) << 43)
                + (u64::from(loose_bvar_range) << 44),
        ))
    }

    /// `lean_expr_mk_app_data` (expr.cpp:120-126): note the hash mixes the two FULL
    /// 64-bit data words, not the extracted 32-bit hashes.
    fn pack_app(f: ExprData, a: ExprData) -> ExprData {
        let depth = (f.approx_depth_u32().max(a.approx_depth_u32()) + 1).min(255);
        let range = f.loose_bvar_range().max(a.loose_bvar_range());
        let hash = mix_hash(f.0, a.0) as u32;
        ExprData(
            ((f.0 | a.0) & (15u64 << 40))
                | u64::from(hash)
                | (u64::from(depth) << 32)
                | (u64::from(range) << 44),
        )
    }

    /// `Expr.Data.hash` — the low 32 bits, zero-extended.
    pub fn hash(self) -> u64 {
        u64::from(self.0 as u32)
    }

    /// `Expr.Data.approxDepth` (8 bits, saturated at 255).
    pub fn approx_depth(self) -> u8 {
        ((self.0 >> 32) & 255) as u8
    }

    fn approx_depth_u32(self) -> u32 {
        u32::from(self.approx_depth())
    }

    /// `Expr.Data.looseBVarRange` (bits 44-63).
    pub fn loose_bvar_range(self) -> u32 {
        (self.0 >> 44) as u32
    }

    pub fn has_fvar(self) -> bool {
        (self.0 >> 40) & 1 == 1
    }

    pub fn has_expr_mvar(self) -> bool {
        (self.0 >> 41) & 1 == 1
    }

    pub fn has_level_mvar(self) -> bool {
        (self.0 >> 42) & 1 == 1
    }

    pub fn has_level_param(self) -> bool {
        (self.0 >> 43) & 1 == 1
    }
}

/// Typed refusal for a loose-bvar range beyond the 20-bit packing (upstream: internal
/// panic "too many bound variables").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TooManyBoundVars {
    pub range: u32,
}

impl std::fmt::Display for TooManyBoundVars {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "loose bound-variable range {} exceeds the 20-bit packing",
            self.range
        )
    }
}

/// The constructor inventory (plan §1.1). Field order follows the pin.
#[derive(Debug, PartialEq, Eq)]
pub enum ExprNode {
    /// de Bruijn bound variable.
    BVar {
        idx: u32,
    },
    FVar {
        id: FVarId,
    },
    MVar {
        id: MVarId,
    },
    Sort {
        level: Level,
    },
    Const {
        name: Name,
        levels: Vec<Level>,
    },
    App {
        f: Expr,
        a: Expr,
    },
    Lam {
        binder_name: Name,
        binder_type: Expr,
        body: Expr,
        binder_info: BinderInfo,
    },
    ForallE {
        binder_name: Name,
        binder_type: Expr,
        body: Expr,
        binder_info: BinderInfo,
    },
    LetE {
        decl_name: Name,
        type_: Expr,
        value: Expr,
        body: Expr,
        non_dep: bool,
    },
    Lit {
        literal: Literal,
    },
    MData {
        data: KVMap,
        expr: Expr,
    },
    Proj {
        struct_name: Name,
        idx: u64,
        expr: Expr,
    },
}

/// A kernel expression carrying its computed observable data word.
#[derive(Clone)]
pub struct Expr {
    // `Option` is a drop-state marker, not a semantic state: live values always
    // contain `Some`.  It lets `Drop` take ownership of the root `Arc` in safe
    // Rust and drain uniquely owned descendants with an explicit heap worklist.
    // `Option<Arc<_>>` has the same pointer-sized representation as `Arc<_>`.
    node: Option<Arc<ExprNode>>,
    data: ExprData,
}

impl std::fmt::Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Expr")
            .field("node", self.node())
            .field("data", &self.data)
            .finish()
    }
}

impl PartialEq for Expr {
    fn eq(&self, other: &Expr) -> bool {
        self.data == other.data
            && (Arc::ptr_eq(self.node_arc(), other.node_arc()) || self.node() == other.node())
    }
}
impl Eq for Expr {}

impl std::hash::Hash for Expr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&self.data.0, state);
    }
}

const SEED_LIT: u64 = 3;
const SEED_CONST: u64 = 5;
const SEED_BVAR: u64 = 7;
const SEED_SORT: u64 = 11;
const SEED_FVAR: u64 = 13;
const SEED_MVAR: u64 = 17;
/// `Hashable (List α)` fold seed (Hashable.lean:37-38).
const LIST_HASH_SEED: u64 = 7;

fn list_level_hash(levels: &[Level]) -> u64 {
    levels
        .iter()
        .fold(LIST_HASH_SEED, |r, l| mix_hash(r, l.hash()))
}

impl Expr {
    fn with(node: ExprNode, data: ExprData) -> Expr {
        Expr {
            node: Some(Arc::new(node)),
            data,
        }
    }

    fn node_arc(&self) -> &Arc<ExprNode> {
        self.node.as_ref().expect("a live Expr always owns a node")
    }

    fn take_node_for_drop(&mut self) -> Option<Arc<ExprNode>> {
        self.node.take()
    }

    /// `.bvar idx`. The only constructor that can exceed the 20-bit range covenant
    /// (every other range is a max/decrement over child ranges).
    pub fn bvar(idx: u32) -> Result<Expr, TooManyBoundVars> {
        let data = ExprData::pack(
            mix_hash(SEED_BVAR, u64::from(idx)),
            idx.saturating_add(1),
            0,
            false,
            false,
            false,
            false,
        )?;
        Ok(Expr::with(ExprNode::BVar { idx }, data))
    }

    /// `.fvar id`.
    pub fn fvar(id: FVarId) -> Expr {
        let data = ExprData::pack(
            mix_hash(SEED_FVAR, id.hash()),
            0,
            0,
            true,
            false,
            false,
            false,
        )
        .expect("range 0 packs");
        Expr::with(ExprNode::FVar { id }, data)
    }

    /// `.mvar id`.
    pub fn mvar(id: MVarId) -> Expr {
        let data = ExprData::pack(
            mix_hash(SEED_MVAR, id.hash()),
            0,
            0,
            false,
            true,
            false,
            false,
        )
        .expect("range 0 packs");
        Expr::with(ExprNode::MVar { id }, data)
    }

    /// `.sort level`.
    pub fn sort(level: Level) -> Expr {
        let data = ExprData::pack(
            mix_hash(SEED_SORT, level.hash()),
            0,
            0,
            false,
            false,
            level.has_mvar(),
            level.has_param(),
        )
        .expect("range 0 packs");
        Expr::with(ExprNode::Sort { level }, data)
    }

    /// `.const name levels`.
    pub fn const_(name: Name, levels: Vec<Level>) -> Expr {
        let data = ExprData::pack(
            mix_hash(SEED_CONST, mix_hash(name.hash(), list_level_hash(&levels))),
            0,
            0,
            false,
            false,
            levels.iter().any(Level::has_mvar),
            levels.iter().any(Level::has_param),
        )
        .expect("range 0 packs");
        Expr::with(ExprNode::Const { name, levels }, data)
    }

    /// `.app f a`.
    pub fn app(f: Expr, a: Expr) -> Expr {
        let data = ExprData::pack_app(f.data, a.data);
        Expr::with(ExprNode::App { f, a }, data)
    }

    fn binder_data(t: &Expr, b: &Expr) -> ExprData {
        let d = t.data.approx_depth_u32().max(b.data.approx_depth_u32()) + 1;
        ExprData::pack(
            // The hash uses the UNCAPPED d (it can be 256); only the stored depth caps.
            mix_hash(u64::from(d), mix_hash(t.data.hash(), b.data.hash())),
            t.data
                .loose_bvar_range()
                .max(b.data.loose_bvar_range().saturating_sub(1)),
            d,
            t.data.has_fvar() || b.data.has_fvar(),
            t.data.has_expr_mvar() || b.data.has_expr_mvar(),
            t.data.has_level_mvar() || b.data.has_level_mvar(),
            t.data.has_level_param() || b.data.has_level_param(),
        )
        .expect("max of child ranges packs")
    }

    /// `.lam binderName binderType body binderInfo`. The binder name and info are NOT
    /// part of the data hash (pin matches them as `_`).
    pub fn lam(binder_name: Name, binder_type: Expr, body: Expr, binder_info: BinderInfo) -> Expr {
        let data = Expr::binder_data(&binder_type, &body);
        Expr::with(
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            },
            data,
        )
    }

    /// `.forallE binderName binderType body binderInfo`.
    pub fn forall_e(
        binder_name: Name,
        binder_type: Expr,
        body: Expr,
        binder_info: BinderInfo,
    ) -> Expr {
        let data = Expr::binder_data(&binder_type, &body);
        Expr::with(
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            },
            data,
        )
    }

    /// `.letE declName type value body nonDep`.
    pub fn let_e(decl_name: Name, type_: Expr, value: Expr, body: Expr, non_dep: bool) -> Expr {
        let d = type_
            .data
            .approx_depth_u32()
            .max(value.data.approx_depth_u32())
            .max(body.data.approx_depth_u32())
            + 1;
        let data = ExprData::pack(
            mix_hash(
                u64::from(d),
                mix_hash(
                    type_.data.hash(),
                    mix_hash(value.data.hash(), body.data.hash()),
                ),
            ),
            type_
                .data
                .loose_bvar_range()
                .max(value.data.loose_bvar_range())
                .max(body.data.loose_bvar_range().saturating_sub(1)),
            d,
            type_.data.has_fvar() || value.data.has_fvar() || body.data.has_fvar(),
            type_.data.has_expr_mvar() || value.data.has_expr_mvar() || body.data.has_expr_mvar(),
            type_.data.has_level_mvar()
                || value.data.has_level_mvar()
                || body.data.has_level_mvar(),
            type_.data.has_level_param()
                || value.data.has_level_param()
                || body.data.has_level_param(),
        )
        .expect("max of child ranges packs");
        Expr::with(
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            },
            data,
        )
    }

    /// `.lit literal`.
    pub fn lit(literal: Literal) -> Expr {
        let data = ExprData::pack(
            mix_hash(SEED_LIT, literal.hash()),
            0,
            0,
            false,
            false,
            false,
            false,
        )
        .expect("range 0 packs");
        Expr::with(ExprNode::Lit { literal }, data)
    }

    /// `.mdata data expr`.
    pub fn mdata(data: KVMap, expr: Expr) -> Expr {
        let d = expr.data.approx_depth_u32() + 1;
        let word = ExprData::pack(
            mix_hash(u64::from(d), expr.data.hash()),
            expr.data.loose_bvar_range(),
            d,
            expr.data.has_fvar(),
            expr.data.has_expr_mvar(),
            expr.data.has_level_mvar(),
            expr.data.has_level_param(),
        )
        .expect("child range packs");
        Expr::with(ExprNode::MData { data, expr }, word)
    }

    /// `.proj structName idx expr`.
    pub fn proj(struct_name: Name, idx: u64, expr: Expr) -> Expr {
        let d = expr.data.approx_depth_u32() + 1;
        let word = ExprData::pack(
            mix_hash(
                u64::from(d),
                mix_hash(struct_name.hash(), mix_hash(idx, expr.data.hash())),
            ),
            expr.data.loose_bvar_range(),
            d,
            expr.data.has_fvar(),
            expr.data.has_expr_mvar(),
            expr.data.has_level_mvar(),
            expr.data.has_level_param(),
        )
        .expect("child range packs");
        Expr::with(
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            },
            word,
        )
    }

    // ---- observables -------------------------------------------------------------------

    /// `Expr.hash` — the stored 32-bit hash, zero-extended.
    pub fn hash(&self) -> u64 {
        self.data.hash()
    }

    /// The packed data word.
    pub fn data(&self) -> ExprData {
        self.data
    }

    /// `Expr.looseBVarRange`: bvars with de Bruijn index below this are loose.
    pub fn loose_bvar_range(&self) -> u32 {
        self.data.loose_bvar_range()
    }

    pub fn approx_depth(&self) -> u8 {
        self.data.approx_depth()
    }

    pub fn has_fvar(&self) -> bool {
        self.data.has_fvar()
    }

    pub fn has_expr_mvar(&self) -> bool {
        self.data.has_expr_mvar()
    }

    pub fn has_level_mvar(&self) -> bool {
        self.data.has_level_mvar()
    }

    pub fn has_level_param(&self) -> bool {
        self.data.has_level_param()
    }

    /// `Expr.hasLooseBVars`.
    pub fn has_loose_bvars(&self) -> bool {
        self.loose_bvar_range() > 0
    }

    /// The structural node (metaprograms pattern-match on the inventory).
    pub fn node(&self) -> &ExprNode {
        self.node_arc()
    }
}

impl Drop for Expr {
    fn drop(&mut self) {
        let Some(root) = self.take_node_for_drop() else {
            return;
        };

        // A last-reference cascade through `Arc<ExprNode>` would normally recurse
        // through one Rust destructor frame per input node.  Drain unique nodes on
        // this explicit heap stack instead.  A shared node is only decremented;
        // whichever `Expr` later owns its final reference will perform the drain.
        let mut pending = vec![root];
        let mut drained = 0usize;
        while let Some(node) = pending.pop() {
            let Some(node) = Arc::into_inner(node) else {
                continue;
            };
            drained += 1;
            if drained.is_multiple_of(4096) {
                std::thread::yield_now();
            }
            match node {
                ExprNode::App { mut f, mut a } => {
                    pending.extend(f.take_node_for_drop());
                    pending.extend(a.take_node_for_drop());
                }
                ExprNode::Lam {
                    mut binder_type,
                    mut body,
                    ..
                }
                | ExprNode::ForallE {
                    mut binder_type,
                    mut body,
                    ..
                } => {
                    pending.extend(binder_type.take_node_for_drop());
                    pending.extend(body.take_node_for_drop());
                }
                ExprNode::LetE {
                    mut type_,
                    mut value,
                    mut body,
                    ..
                } => {
                    pending.extend(type_.take_node_for_drop());
                    pending.extend(value.take_node_for_drop());
                    pending.extend(body.take_node_for_drop());
                }
                ExprNode::MData { mut expr, .. } | ExprNode::Proj { mut expr, .. } => {
                    pending.extend(expr.take_node_for_drop());
                }
                // `Level` has its own stack-safe last-reference drain.  All other
                // payloads are non-recursive with respect to `Expr`.
                ExprNode::BVar { .. }
                | ExprNode::FVar { .. }
                | ExprNode::MVar { .. }
                | ExprNode::Sort { .. }
                | ExprNode::Const { .. }
                | ExprNode::Lit { .. } => {}
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name(s: &str) -> Name {
        Name::str(Name::anonymous(), s)
    }

    fn u() -> Level {
        Level::param(name("u"))
    }

    #[test]
    fn leaf_data_formulas_match_the_pin() {
        let b = Expr::bvar(3).expect("packs");
        assert_eq!(b.hash(), u64::from(mix_hash(7, 3) as u32));
        assert_eq!(b.loose_bvar_range(), 4);
        assert_eq!(b.approx_depth(), 0);
        assert!(!b.has_fvar() && !b.has_expr_mvar());

        let f = Expr::fvar(FVarId(name("x")));
        assert_eq!(
            f.hash(),
            u64::from(mix_hash(13, mix_hash(0, name("x").hash())) as u32)
        );
        assert!(f.has_fvar() && !f.has_expr_mvar());
        assert_eq!(f.loose_bvar_range(), 0);

        let m = Expr::mvar(MVarId(name("m")));
        assert_eq!(
            m.hash(),
            u64::from(mix_hash(17, mix_hash(0, name("m").hash())) as u32)
        );
        assert!(m.has_expr_mvar() && !m.has_fvar());

        let s = Expr::sort(u());
        assert_eq!(s.hash(), u64::from(mix_hash(11, u().hash()) as u32));
        assert!(s.has_level_param() && !s.has_level_mvar());

        let lit = Expr::lit(Literal::Nat(NatLit::from_u64(42)));
        assert_eq!(lit.hash(), u64::from(mix_hash(3, 42) as u32));

        let slit = Expr::lit(Literal::Str("hi".to_string()));
        assert_eq!(
            slit.hash(),
            u64::from(mix_hash(3, crate::lean_hash::string_hash("hi")) as u32)
        );
    }

    #[test]
    fn const_hash_uses_the_list_fold_and_level_flags() {
        let levels = vec![Level::zero(), u()];
        let expected_list = mix_hash(mix_hash(7, Level::zero().hash()), u().hash());
        let c = Expr::const_(name("Foo"), levels);
        assert_eq!(
            c.hash(),
            u64::from(mix_hash(5, mix_hash(name("Foo").hash(), expected_list)) as u32)
        );
        assert!(c.has_level_param() && !c.has_level_mvar());
        let plain = Expr::const_(name("Nat"), Vec::new());
        assert_eq!(
            plain.hash(),
            u64::from(mix_hash(5, mix_hash(name("Nat").hash(), 7)) as u32)
        );
        assert!(!plain.has_level_param());
    }

    #[test]
    fn app_data_mixes_full_words_and_ors_flags() {
        let f = Expr::fvar(FVarId(name("f")));
        let a = Expr::mvar(MVarId(name("a")));
        let app = Expr::app(f.clone(), a.clone());
        assert_eq!(
            app.hash(),
            u64::from(mix_hash(f.data().0, a.data().0) as u32)
        );
        assert!(app.has_fvar() && app.has_expr_mvar());
        assert_eq!(app.approx_depth(), 1);
        assert_eq!(app.loose_bvar_range(), 0);

        let b = Expr::bvar(9).expect("packs");
        let app2 = Expr::app(app.clone(), b);
        assert_eq!(app2.loose_bvar_range(), 10);
        assert_eq!(app2.approx_depth(), 2);
    }

    #[test]
    fn binders_decrement_the_body_range_with_nat_truncation() {
        // fun (x : A) => bvar 0 — body range 1, bound by the lambda → range 0.
        let a = Expr::const_(name("A"), Vec::new());
        let lam = Expr::lam(
            name("x"),
            a.clone(),
            Expr::bvar(0).expect("packs"),
            BinderInfo::Default,
        );
        assert_eq!(lam.loose_bvar_range(), 0);
        assert!(!lam.has_loose_bvars());

        // fun (x : A) => bvar 1 — body range 2 → 1 loose remains.
        let lam2 = Expr::lam(
            name("x"),
            a.clone(),
            Expr::bvar(1).expect("packs"),
            BinderInfo::Default,
        );
        assert_eq!(lam2.loose_bvar_range(), 1);

        // The domain range is NOT decremented: ∀ (x : bvar 0), A has range 1.
        let pi = Expr::forall_e(
            name("x"),
            Expr::bvar(0).expect("packs"),
            a.clone(),
            BinderInfo::Implicit,
        );
        assert_eq!(pi.loose_bvar_range(), 1);

        // let: type and value ranges kept, body decremented.
        let lete = Expr::let_e(
            name("y"),
            a.clone(),
            Expr::bvar(2).expect("packs"),
            Expr::bvar(0).expect("packs"),
            false,
        );
        assert_eq!(lete.loose_bvar_range(), 3);
    }

    #[test]
    fn binder_hash_uses_uncapped_depth_and_ignores_binder_name_and_info() {
        let a = Expr::const_(name("A"), Vec::new());
        let body = Expr::bvar(0).expect("packs");
        let d = u64::from(a.data().approx_depth().max(body.data().approx_depth()) as u32 + 1);
        let expected = mix_hash(d, mix_hash(a.data().hash(), body.data().hash()));
        let l1 = Expr::lam(name("x"), a.clone(), body.clone(), BinderInfo::Default);
        let l2 = Expr::lam(name("y"), a.clone(), body.clone(), BinderInfo::InstImplicit);
        assert_eq!(l1.hash(), u64::from(expected as u32));
        assert_eq!(l1.hash(), l2.hash(), "name and binder info are not hashed");
        assert_ne!(l1, l2, "but they still distinguish structurally");
    }

    #[test]
    fn mdata_and_proj_wrap_with_depth_bump() {
        let inner = Expr::fvar(FVarId(name("x")));
        let w = Expr::mdata(KVMap::default(), inner.clone());
        let d = u64::from(inner.data().approx_depth() as u32 + 1);
        assert_eq!(w.hash(), u64::from(mix_hash(d, inner.data().hash()) as u32));
        assert_eq!(w.approx_depth(), 1);
        assert!(w.has_fvar());

        let p = Expr::proj(name("Prod"), 1, inner.clone());
        assert_eq!(
            p.hash(),
            u64::from(mix_hash(
                d,
                mix_hash(name("Prod").hash(), mix_hash(1, inner.data().hash()))
            ) as u32)
        );
        assert_eq!(p.approx_depth(), 1);
    }

    #[test]
    fn approx_depth_saturates_at_255_but_the_hash_keeps_moving() {
        let mut e = Expr::lit(Literal::Nat(NatLit::from_u64(0)));
        for _ in 0..300 {
            e = Expr::mdata(KVMap::default(), e);
        }
        assert_eq!(e.approx_depth(), 255);
        // Two expressions at the cap still differ by hash (d in the hash is capped+1
        // uniformly, but the child hashes differ).
        let deeper = Expr::mdata(KVMap::default(), e.clone());
        assert_eq!(deeper.approx_depth(), 255);
        assert_ne!(deeper.hash(), e.hash());
    }

    #[test]
    fn bvar_range_covenant_is_a_typed_error() {
        assert!(Expr::bvar(MAX_LOOSE_BVAR_RANGE - 1).is_ok());
        assert_eq!(
            Expr::bvar(MAX_LOOSE_BVAR_RANGE),
            Err(TooManyBoundVars {
                range: MAX_LOOSE_BVAR_RANGE + 1
            })
        );
    }

    #[test]
    fn literal_order_and_natlit_semantics() {
        let two = Literal::Nat(NatLit::from_u64(2));
        let three = Literal::Nat(NatLit::from_u64(3));
        let s = Literal::Str("a".to_string());
        assert!(two.lt(&three));
        assert!(two.lt(&s));
        assert!(!s.lt(&two));
        assert!(s.lt(&Literal::Str("b".to_string())));

        // NatLit: normalization, ordering across limb counts, mod-2^64 hash.
        let big = NatLit::from_limbs_le(vec![5, 9]);
        assert_eq!(big.hash(), 5, "hash is the value mod 2^64");
        assert_eq!(big.to_u64(), None);
        assert!(NatLit::from_u64(u64::MAX) < big);
        assert_eq!(NatLit::from_limbs_le(vec![7, 0, 0]), NatLit::from_u64(7));
        assert_eq!(NatLit::from_u64(0).limbs_le(), &[] as &[u64]);
    }

    #[test]
    fn structural_equality_rides_the_data_word_fast_path() {
        let a = Expr::app(
            Expr::const_(name("f"), Vec::new()),
            Expr::bvar(0).expect("packs"),
        );
        let b = Expr::app(
            Expr::const_(name("f"), Vec::new()),
            Expr::bvar(0).expect("packs"),
        );
        assert_eq!(a, b);
        let c = Expr::app(
            Expr::const_(name("g"), Vec::new()),
            Expr::bvar(0).expect("packs"),
        );
        assert_ne!(a, c);
    }

    #[test]
    fn iterative_drop_preserves_shared_expr_arcs() {
        let leaf = Expr::bvar(0).expect("small");
        assert_eq!(Arc::strong_count(leaf.node_arc()), 1);

        let root = Expr::app(leaf.clone(), leaf.clone());
        assert_eq!(Arc::strong_count(leaf.node_arc()), 3);
        let retained_root = root.clone();
        assert_eq!(Arc::strong_count(root.node_arc()), 2);

        // The first root drop must only decrement the shared root.  The final root
        // drop unwraps it iteratively and releases exactly its two leaf references.
        drop(root);
        assert_eq!(Arc::strong_count(retained_root.node_arc()), 1);
        drop(retained_root);
        assert_eq!(Arc::strong_count(leaf.node_arc()), 1);
    }

    #[test]
    fn iterative_drop_releases_every_recursive_expr_constructor_reference() {
        let leaf = Expr::bvar(0).expect("small");
        let mut roots = vec![
            Expr::app(leaf.clone(), leaf.clone()),
            Expr::lam(name("x"), leaf.clone(), leaf.clone(), BinderInfo::Default),
            Expr::forall_e(name("x"), leaf.clone(), leaf.clone(), BinderInfo::Implicit),
            Expr::let_e(name("x"), leaf.clone(), leaf.clone(), leaf.clone(), false),
            Expr::mdata(KVMap::new(), leaf.clone()),
            Expr::proj(name("S"), 0, leaf.clone()),
        ];
        assert_eq!(
            Arc::strong_count(leaf.node_arc()),
            12,
            "every recursive field owns exactly one Arc"
        );

        // A deterministic permutation exercises last-owner release in an order
        // unrelated to construction order.
        let mut state = 0x243f_6a88_85a3_08d3_u64;
        while !roots.is_empty() {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let index = (state as usize) % roots.len();
            drop(roots.swap_remove(index));
        }
        assert_eq!(Arc::strong_count(leaf.node_arc()), 1);
    }

    #[test]
    fn iterative_drop_drains_maximally_shared_expr_dag_after_clone_permutations() {
        let leaf = Expr::bvar(0).expect("small");
        let mut dag = leaf.clone();
        let mut retained_roots = Vec::new();
        for depth in 0_usize..64 {
            dag = Expr::app(dag.clone(), dag.clone());
            if depth.is_multiple_of(5) {
                retained_roots.push(dag.clone());
            }
        }
        retained_roots.push(dag);
        assert_eq!(
            Arc::strong_count(leaf.node_arc()),
            3,
            "the maximally shared bottom node has two DAG edges"
        );

        let mut state = 0x1319_8a2e_0370_7344_u64;
        while !retained_roots.is_empty() {
            state = state
                .wrapping_mul(2862933555777941757)
                .wrapping_add(3037000493);
            let index = (state as usize) % retained_roots.len();
            drop(retained_roots.swap_remove(index));
        }
        assert_eq!(
            Arc::strong_count(leaf.node_arc()),
            1,
            "no shared internal node may retain either leaf edge"
        );
    }
}
