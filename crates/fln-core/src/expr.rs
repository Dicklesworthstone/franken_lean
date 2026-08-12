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

use crate::debug_walk::FlatDebug;
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
///
/// Deliberately **not** `PartialEq`/`Eq`: a derived node comparison descends one
/// stack frame per child and overflows on deep input.  Structural equality is a
/// property of [`Expr`], whose `PartialEq` walks a heap worklist instead.
#[derive(Debug)]
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
    /// Byte-identical to the derived rendering, walked on an explicit task stack:
    /// `debug_struct` would descend one frame per node and overflow on deep input
    /// (bead franken_lean-canon-stack-safe-drop-6gy).
    ///
    /// Only child `Expr`s become tasks. Every other payload — `Name`, `Level`,
    /// `Vec<Level>`, `KVMap`, `Literal`, the scalars — is a leaf, because none of
    /// them re-enters this walk and each is depth-independent in its own right.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        enum Task<'a> {
            Expr(&'a Expr),
            Node(&'a ExprNode),
            Field(&'static str),
            Leaf(&'a dyn std::fmt::Debug),
            Close,
        }

        let mut out = FlatDebug::new(f);
        let mut tasks = vec![Task::Expr(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Expr(expr) => {
                    out.open_struct("Expr")?;
                    tasks.push(Task::Close);
                    tasks.push(Task::Leaf(&expr.data));
                    tasks.push(Task::Field("data"));
                    tasks.push(Task::Node(expr.node()));
                    tasks.push(Task::Field("node"));
                }
                Task::Node(node) => {
                    // Field order follows the declaration order the derived
                    // implementation used; tasks are pushed in reverse.
                    match node {
                        ExprNode::BVar { idx } => {
                            out.open_struct("BVar")?;
                            tasks.push(Task::Close);
                            tasks.push(Task::Leaf(idx));
                            tasks.push(Task::Field("idx"));
                        }
                        ExprNode::FVar { id } => {
                            out.open_struct("FVar")?;
                            tasks.push(Task::Close);
                            tasks.push(Task::Leaf(id));
                            tasks.push(Task::Field("id"));
                        }
                        ExprNode::MVar { id } => {
                            out.open_struct("MVar")?;
                            tasks.push(Task::Close);
                            tasks.push(Task::Leaf(id));
                            tasks.push(Task::Field("id"));
                        }
                        ExprNode::Sort { level } => {
                            out.open_struct("Sort")?;
                            tasks.push(Task::Close);
                            tasks.push(Task::Leaf(level));
                            tasks.push(Task::Field("level"));
                        }
                        ExprNode::Const { name, levels } => {
                            out.open_struct("Const")?;
                            tasks.push(Task::Close);
                            tasks.push(Task::Leaf(levels));
                            tasks.push(Task::Field("levels"));
                            tasks.push(Task::Leaf(name));
                            tasks.push(Task::Field("name"));
                        }
                        ExprNode::App { f, a } => {
                            out.open_struct("App")?;
                            tasks.push(Task::Close);
                            tasks.push(Task::Expr(a));
                            tasks.push(Task::Field("a"));
                            tasks.push(Task::Expr(f));
                            tasks.push(Task::Field("f"));
                        }
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => {
                            out.open_struct("Lam")?;
                            tasks.push(Task::Close);
                            tasks.push(Task::Leaf(binder_info));
                            tasks.push(Task::Field("binder_info"));
                            tasks.push(Task::Expr(body));
                            tasks.push(Task::Field("body"));
                            tasks.push(Task::Expr(binder_type));
                            tasks.push(Task::Field("binder_type"));
                            tasks.push(Task::Leaf(binder_name));
                            tasks.push(Task::Field("binder_name"));
                        }
                        ExprNode::ForallE {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => {
                            out.open_struct("ForallE")?;
                            tasks.push(Task::Close);
                            tasks.push(Task::Leaf(binder_info));
                            tasks.push(Task::Field("binder_info"));
                            tasks.push(Task::Expr(body));
                            tasks.push(Task::Field("body"));
                            tasks.push(Task::Expr(binder_type));
                            tasks.push(Task::Field("binder_type"));
                            tasks.push(Task::Leaf(binder_name));
                            tasks.push(Task::Field("binder_name"));
                        }
                        ExprNode::LetE {
                            decl_name,
                            type_,
                            value,
                            body,
                            non_dep,
                        } => {
                            out.open_struct("LetE")?;
                            tasks.push(Task::Close);
                            tasks.push(Task::Leaf(non_dep));
                            tasks.push(Task::Field("non_dep"));
                            tasks.push(Task::Expr(body));
                            tasks.push(Task::Field("body"));
                            tasks.push(Task::Expr(value));
                            tasks.push(Task::Field("value"));
                            tasks.push(Task::Expr(type_));
                            tasks.push(Task::Field("type_"));
                            tasks.push(Task::Leaf(decl_name));
                            tasks.push(Task::Field("decl_name"));
                        }
                        ExprNode::Lit { literal } => {
                            out.open_struct("Lit")?;
                            tasks.push(Task::Close);
                            tasks.push(Task::Leaf(literal));
                            tasks.push(Task::Field("literal"));
                        }
                        ExprNode::MData { data, expr } => {
                            out.open_struct("MData")?;
                            tasks.push(Task::Close);
                            tasks.push(Task::Expr(expr));
                            tasks.push(Task::Field("expr"));
                            tasks.push(Task::Leaf(data));
                            tasks.push(Task::Field("data"));
                        }
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => {
                            out.open_struct("Proj")?;
                            tasks.push(Task::Close);
                            tasks.push(Task::Expr(expr));
                            tasks.push(Task::Field("expr"));
                            tasks.push(Task::Leaf(idx));
                            tasks.push(Task::Field("idx"));
                            tasks.push(Task::Leaf(struct_name));
                            tasks.push(Task::Field("struct_name"));
                        }
                    }
                }
                Task::Field(name) => out.field(name)?,
                Task::Leaf(value) => out.leaf(value)?,
                Task::Close => out.close()?,
            }
        }
        Ok(())
    }
}

impl PartialEq for Expr {
    fn eq(&self, other: &Expr) -> bool {
        // Data word first (hash and packed flags reject fast), then structure.
        //
        // The structural arm walks an explicit heap worklist instead of recursing
        // through one `Expr::eq` frame per constructor: two independently built
        // deep-but-equal terms agree on every data word, so the fast rejections
        // never fire and a recursive comparison would consume the stack in
        // proportion to input depth (the term-plane analogue of the `Name` fix in
        // bead franken_lean-p8a.1).  Equality is a pure predicate, so the order in
        // which pending pairs are visited does not change the verdict.
        let mut pending: Vec<(&Expr, &Expr)> = vec![(self, other)];
        while let Some((left, right)) = pending.pop() {
            if left.data != right.data {
                return false;
            }
            if Arc::ptr_eq(left.node_arc(), right.node_arc()) {
                continue;
            }
            match (left.node(), right.node()) {
                (ExprNode::BVar { idx: a }, ExprNode::BVar { idx: b }) => {
                    if a != b {
                        return false;
                    }
                }
                (ExprNode::FVar { id: a }, ExprNode::FVar { id: b }) => {
                    if a != b {
                        return false;
                    }
                }
                (ExprNode::MVar { id: a }, ExprNode::MVar { id: b }) => {
                    if a != b {
                        return false;
                    }
                }
                // `Level`, `Name`, `Literal` and `KVMap` payloads all compare without
                // recursion over *this* term's depth: the first two are iterative in
                // their own right and the last two are flat.
                (ExprNode::Sort { level: a }, ExprNode::Sort { level: b }) => {
                    if a != b {
                        return false;
                    }
                }
                (
                    ExprNode::Const {
                        name: a,
                        levels: a_levels,
                    },
                    ExprNode::Const {
                        name: b,
                        levels: b_levels,
                    },
                ) => {
                    if a != b || a_levels != b_levels {
                        return false;
                    }
                }
                (ExprNode::App { f: af, a: aa }, ExprNode::App { f: bf, a: ba }) => {
                    pending.push((aa, ba));
                    pending.push((af, bf));
                }
                // `Lam` and `ForallE` share a shape but are distinct constructors, so
                // each needs its own arm: an or-pattern here would equate them.
                (
                    ExprNode::Lam {
                        binder_name: a_name,
                        binder_type: a_type,
                        body: a_body,
                        binder_info: a_info,
                    },
                    ExprNode::Lam {
                        binder_name: b_name,
                        binder_type: b_type,
                        body: b_body,
                        binder_info: b_info,
                    },
                )
                | (
                    ExprNode::ForallE {
                        binder_name: a_name,
                        binder_type: a_type,
                        body: a_body,
                        binder_info: a_info,
                    },
                    ExprNode::ForallE {
                        binder_name: b_name,
                        binder_type: b_type,
                        body: b_body,
                        binder_info: b_info,
                    },
                ) => {
                    if a_name != b_name || a_info != b_info {
                        return false;
                    }
                    pending.push((a_body, b_body));
                    pending.push((a_type, b_type));
                }
                (
                    ExprNode::LetE {
                        decl_name: a_name,
                        type_: a_type,
                        value: a_value,
                        body: a_body,
                        non_dep: a_non_dep,
                    },
                    ExprNode::LetE {
                        decl_name: b_name,
                        type_: b_type,
                        value: b_value,
                        body: b_body,
                        non_dep: b_non_dep,
                    },
                ) => {
                    if a_name != b_name || a_non_dep != b_non_dep {
                        return false;
                    }
                    pending.push((a_body, b_body));
                    pending.push((a_value, b_value));
                    pending.push((a_type, b_type));
                }
                (ExprNode::Lit { literal: a }, ExprNode::Lit { literal: b }) => {
                    if a != b {
                        return false;
                    }
                }
                (
                    ExprNode::MData {
                        data: a_data,
                        expr: a_expr,
                    },
                    ExprNode::MData {
                        data: b_data,
                        expr: b_expr,
                    },
                ) => {
                    if a_data != b_data {
                        return false;
                    }
                    pending.push((a_expr, b_expr));
                }
                (
                    ExprNode::Proj {
                        struct_name: a_name,
                        idx: a_idx,
                        expr: a_expr,
                    },
                    ExprNode::Proj {
                        struct_name: b_name,
                        idx: b_idx,
                        expr: b_expr,
                    },
                ) => {
                    if a_name != b_name || a_idx != b_idx {
                        return false;
                    }
                    pending.push((a_expr, b_expr));
                }
                _ => return false,
            }
        }
        true
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

    /// Process-local identity of this immutable node allocation.
    ///
    /// This is deliberately not a semantic hash and must never enter an
    /// artifact, diagnostic, cache key, or deterministic ordering. It exists
    /// only so bounded in-process graph walks can avoid expanding shared DAGs
    /// as trees. Equal independently allocated expressions may have different
    /// identities; clones of one expression retain the same identity. The
    /// number is unique only while both allocations being compared remain
    /// alive and must not be retained as a cross-lifetime identifier.
    #[doc(hidden)]
    pub fn allocation_identity(&self) -> usize {
        Arc::as_ptr(self.node_arc()) as usize
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
    fn allocation_identity_distinguishes_sharing_from_structural_equality() {
        let shared = Expr::sort(Level::zero());
        let cloned = shared.clone();
        let independent = Expr::sort(Level::zero());

        assert_eq!(shared, independent);
        assert_eq!(shared.allocation_identity(), cloned.allocation_identity());
        assert_ne!(
            shared.allocation_identity(),
            independent.allocation_identity(),
            "independently allocated structural twins are not one DAG node"
        );
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

    /// The recursive comparison this type deliberately no longer derives. Kept as a
    /// test-only oracle: on shallow terms recursion is safe, so it pins the exact
    /// verdict the iterative predicate must reproduce.
    fn recursive_expr_eq(left: &Expr, right: &Expr) -> bool {
        if left.data != right.data {
            return false;
        }
        if Arc::ptr_eq(left.node_arc(), right.node_arc()) {
            return true;
        }
        match (left.node(), right.node()) {
            (ExprNode::BVar { idx: a }, ExprNode::BVar { idx: b }) => a == b,
            (ExprNode::FVar { id: a }, ExprNode::FVar { id: b }) => a == b,
            (ExprNode::MVar { id: a }, ExprNode::MVar { id: b }) => a == b,
            (ExprNode::Sort { level: a }, ExprNode::Sort { level: b }) => a == b,
            (
                ExprNode::Const {
                    name: a,
                    levels: a_levels,
                },
                ExprNode::Const {
                    name: b,
                    levels: b_levels,
                },
            ) => a == b && a_levels == b_levels,
            (ExprNode::App { f: af, a: aa }, ExprNode::App { f: bf, a: ba }) => {
                recursive_expr_eq(af, bf) && recursive_expr_eq(aa, ba)
            }
            (
                ExprNode::Lam {
                    binder_name: a_name,
                    binder_type: a_type,
                    body: a_body,
                    binder_info: a_info,
                },
                ExprNode::Lam {
                    binder_name: b_name,
                    binder_type: b_type,
                    body: b_body,
                    binder_info: b_info,
                },
            )
            | (
                ExprNode::ForallE {
                    binder_name: a_name,
                    binder_type: a_type,
                    body: a_body,
                    binder_info: a_info,
                },
                ExprNode::ForallE {
                    binder_name: b_name,
                    binder_type: b_type,
                    body: b_body,
                    binder_info: b_info,
                },
            ) => {
                a_name == b_name
                    && a_info == b_info
                    && recursive_expr_eq(a_type, b_type)
                    && recursive_expr_eq(a_body, b_body)
            }
            (
                ExprNode::LetE {
                    decl_name: a_name,
                    type_: a_type,
                    value: a_value,
                    body: a_body,
                    non_dep: a_non_dep,
                },
                ExprNode::LetE {
                    decl_name: b_name,
                    type_: b_type,
                    value: b_value,
                    body: b_body,
                    non_dep: b_non_dep,
                },
            ) => {
                a_name == b_name
                    && a_non_dep == b_non_dep
                    && recursive_expr_eq(a_type, b_type)
                    && recursive_expr_eq(a_value, b_value)
                    && recursive_expr_eq(a_body, b_body)
            }
            (ExprNode::Lit { literal: a }, ExprNode::Lit { literal: b }) => a == b,
            (
                ExprNode::MData {
                    data: a_data,
                    expr: a_expr,
                },
                ExprNode::MData {
                    data: b_data,
                    expr: b_expr,
                },
            ) => a_data == b_data && recursive_expr_eq(a_expr, b_expr),
            (
                ExprNode::Proj {
                    struct_name: a_name,
                    idx: a_idx,
                    expr: a_expr,
                },
                ExprNode::Proj {
                    struct_name: b_name,
                    idx: b_idx,
                    expr: b_expr,
                },
            ) => a_name == b_name && a_idx == b_idx && recursive_expr_eq(a_expr, b_expr),
            _ => false,
        }
    }

    /// One value per constructor, plus the pairs that must NOT collapse: same shape
    /// under a different constructor (`Lam` vs `ForallE`), differing binder metadata,
    /// differing literals, and a shared node reached two ways.
    fn shallow_equality_matrix() -> Vec<Expr> {
        let x = Name::str(Name::anonymous(), "x");
        let y = Name::str(Name::anonymous(), "y");
        let bvar = Expr::bvar(0).expect("small");
        let sort = Expr::sort(Level::zero());
        let shared = Expr::app(bvar.clone(), sort.clone());
        vec![
            bvar.clone(),
            Expr::bvar(1).expect("small"),
            Expr::fvar(FVarId(x.clone())),
            Expr::fvar(FVarId(y.clone())),
            Expr::mvar(MVarId(x.clone())),
            sort.clone(),
            Expr::sort(Level::zero().add_offset(1).expect("small")),
            Expr::const_(x.clone(), Vec::new()),
            Expr::const_(x.clone(), vec![Level::zero()]),
            Expr::const_(y.clone(), Vec::new()),
            Expr::app(bvar.clone(), sort.clone()),
            Expr::app(sort.clone(), bvar.clone()),
            shared.clone(),
            shared,
            Expr::lam(x.clone(), sort.clone(), bvar.clone(), BinderInfo::Default),
            Expr::lam(x.clone(), sort.clone(), bvar.clone(), BinderInfo::Implicit),
            Expr::lam(y.clone(), sort.clone(), bvar.clone(), BinderInfo::Default),
            Expr::forall_e(x.clone(), sort.clone(), bvar.clone(), BinderInfo::Default),
            Expr::let_e(x.clone(), sort.clone(), bvar.clone(), bvar.clone(), false),
            Expr::let_e(x.clone(), sort.clone(), bvar.clone(), bvar.clone(), true),
            Expr::lit(Literal::Nat(NatLit::from_u64(0))),
            Expr::lit(Literal::Nat(NatLit::from_u64(1))),
            Expr::lit(Literal::Str("s".to_string())),
            Expr::mdata(KVMap::default(), bvar.clone()),
            Expr::proj(x.clone(), 0, bvar.clone()),
            Expr::proj(x, 1, bvar.clone()),
            Expr::proj(y, 0, bvar),
        ]
    }

    #[test]
    fn iterative_equality_matches_the_recursive_oracle_on_every_constructor() {
        let values = shallow_equality_matrix();
        for (left_index, left) in values.iter().enumerate() {
            for (right_index, right) in values.iter().enumerate() {
                assert_eq!(
                    left == right,
                    recursive_expr_eq(left, right),
                    "verdict changed at ({left_index}, {right_index})"
                );
                assert_eq!(
                    left == right,
                    right == left,
                    "equality is symmetric at ({left_index}, {right_index})"
                );
            }
            assert!(left == left, "equality is reflexive at {left_index}");
            assert!(
                *left == left.clone(),
                "a clone shares its node and stays equal at {left_index}"
            );
        }
    }

    /// A `Lam` and a `ForallE` with identical payloads are distinct terms. The data
    /// word already separates them, but the structural arms must not merge either.
    #[test]
    fn binder_constructors_never_compare_equal() {
        let name = Name::str(Name::anonymous(), "x");
        let body = Expr::bvar(0).expect("small");
        let type_ = Expr::sort(Level::zero());
        let lam = Expr::lam(
            name.clone(),
            type_.clone(),
            body.clone(),
            BinderInfo::Default,
        );
        let forall = Expr::forall_e(name, type_, body, BinderInfo::Default);
        assert!(lam != forall);
        assert!(!recursive_expr_eq(&lam, &forall));
    }

    /// Independently built deep-but-equal terms agree on every data word, so the
    /// structural arm is reached at every node — the exact shape that overflowed
    /// while the comparison recursed. A 1 MiB worker is far below what one frame
    /// per node would need at this depth.
    #[test]
    fn deep_structural_equality_is_stack_bounded() {
        const DEPTH: usize = 100_000;

        fn deep_app_spine(leaf: Expr, depth: usize) -> Expr {
            let mut expr = leaf;
            for _ in 0..depth {
                expr = Expr::app(expr, Expr::bvar(0).expect("small"));
            }
            expr
        }

        fn deep_binder_spine(leaf: Expr, depth: usize) -> Expr {
            let name = Name::str(Name::anonymous(), "x");
            let type_ = Expr::sort(Level::zero());
            let mut expr = leaf;
            for index in 0..depth {
                expr = if index.is_multiple_of(2) {
                    Expr::lam(name.clone(), type_.clone(), expr, BinderInfo::Default)
                } else {
                    Expr::forall_e(name.clone(), type_.clone(), expr, BinderInfo::Default)
                };
            }
            expr
        }

        let outcome = std::thread::Builder::new()
            .stack_size(1024 * 1024)
            .spawn(|| {
                let leaf = || Expr::sort(Level::zero());
                let left = deep_app_spine(leaf(), DEPTH);
                let right = deep_app_spine(leaf(), DEPTH);
                assert!(
                    left == right,
                    "independently built deep terms must compare equal"
                );

                // A mismatch buried under the whole spine: the walk must reach it
                // rather than stop at the roots' data words.
                let other = deep_app_spine(Expr::bvar(0).expect("small"), DEPTH);
                assert!(left != other, "a deep leaf mismatch must be observed");

                let left_binders = deep_binder_spine(leaf(), DEPTH);
                let right_binders = deep_binder_spine(leaf(), DEPTH);
                assert!(
                    left_binders == right_binders,
                    "deep alternating binder spines must agree"
                );
            })
            .expect("spawn bounded-stack Expr comparison worker")
            .join();
        assert!(
            outcome.is_ok(),
            "deep Expr equality exhausted the bounded worker stack"
        );
    }
    /// Byte-for-byte `Debug` vectors captured from the recursive implementation
    /// this walk replaces (bead franken_lean-canon-stack-safe-drop-6gy). Rendering
    /// is a compatibility surface: consumers, goldens, and diagnostics read it, so
    /// the stack-safety fix must be invisible in both `{:?}` and `{:#?}`.
    #[test]
    fn debug_rendering_is_byte_identical_to_the_recursive_goldens() {
        let x = || Name::str(Name::anonymous(), "x");
        let bvar = Expr::bvar(0).expect("small");
        let sort = Expr::sort(Level::zero());
        let levels = vec![Level::zero(), Level::param(x())];
        let values: Vec<(&str, Expr)> = vec![
            ("bvar", bvar.clone()),
            ("fvar", Expr::fvar(FVarId(x()))),
            ("mvar", Expr::mvar(MVarId(x()))),
            ("sort", sort.clone()),
            ("const", Expr::const_(x(), levels)),
            ("app", Expr::app(bvar.clone(), sort.clone())),
            (
                "lam",
                Expr::lam(x(), sort.clone(), bvar.clone(), BinderInfo::Implicit),
            ),
            (
                "forall",
                Expr::forall_e(x(), sort.clone(), bvar.clone(), BinderInfo::StrictImplicit),
            ),
            (
                "let",
                Expr::let_e(x(), sort.clone(), bvar.clone(), bvar.clone(), true),
            ),
            ("lit_nat", Expr::lit(Literal::Nat(NatLit::from_u64(7)))),
            ("lit_str", Expr::lit(Literal::Str("s".to_string()))),
            ("mdata", Expr::mdata(KVMap::default(), bvar.clone())),
            ("proj", Expr::proj(x(), 3, bvar.clone())),
            ("nested", Expr::app(Expr::app(bvar.clone(), sort), bvar)),
        ];
        const GOLDENS: [(&str, &str, &str); 14] = [
            (
                "bvar",
                "Expr { node: BVar { idx: 0 }, data: ExprData(17592537633786) }",
                concat!(
                    "Expr {\n",
                    "    node: BVar {\n",
                    "        idx: 0,\n",
                    "    },\n",
                    "    data: ExprData(\n",
                    "        17592537633786,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "fvar",
                "Expr { node: FVar { id: FVarId(Name(Str(StrNode { pre: Name(Anonymous), component: \"x\", hash: 13655884332201764339 }))) }, data: ExprData(1101888168254) }",
                concat!(
                    "Expr {\n",
                    "    node: FVar {\n",
                    "        id: FVarId(\n",
                    "            Name(\n",
                    "                Str(\n",
                    "                    StrNode {\n",
                    "                        pre: Name(\n",
                    "                            Anonymous,\n",
                    "                        ),\n",
                    "                        component: \"x\",\n",
                    "                        hash: 13655884332201764339,\n",
                    "                    },\n",
                    "                ),\n",
                    "            ),\n",
                    "        ),\n",
                    "    },\n",
                    "    data: ExprData(\n",
                    "        1101888168254,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "mvar",
                "Expr { node: MVar { id: MVarId(Name(Str(StrNode { pre: Name(Anonymous), component: \"x\", hash: 13655884332201764339 }))) }, data: ExprData(2202144694498) }",
                concat!(
                    "Expr {\n",
                    "    node: MVar {\n",
                    "        id: MVarId(\n",
                    "            Name(\n",
                    "                Str(\n",
                    "                    StrNode {\n",
                    "                        pre: Name(\n",
                    "                            Anonymous,\n",
                    "                        ),\n",
                    "                        component: \"x\",\n",
                    "                        hash: 13655884332201764339,\n",
                    "                    },\n",
                    "                ),\n",
                    "            ),\n",
                    "        ),\n",
                    "    },\n",
                    "    data: ExprData(\n",
                    "        2202144694498,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "sort",
                "Expr { node: Sort { level: Level { node: Zero, data: LevelData(2221) } }, data: ExprData(3944470172) }",
                concat!(
                    "Expr {\n",
                    "    node: Sort {\n",
                    "        level: Level {\n",
                    "            node: Zero,\n",
                    "            data: LevelData(\n",
                    "                2221,\n",
                    "            ),\n",
                    "        },\n",
                    "    },\n",
                    "    data: ExprData(\n",
                    "        3944470172,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "const",
                "Expr { node: Const { name: Name(Str(StrNode { pre: Name(Anonymous), component: \"x\", hash: 13655884332201764339 })), levels: [Level { node: Zero, data: LevelData(2221) }, Level { node: Param(Name(Str(StrNode { pre: Name(Anonymous), component: \"x\", hash: 13655884332201764339 }))), data: LevelData(10400061217) }] }, data: ExprData(8796919455285) }",
                concat!(
                    "Expr {\n",
                    "    node: Const {\n",
                    "        name: Name(\n",
                    "            Str(\n",
                    "                StrNode {\n",
                    "                    pre: Name(\n",
                    "                        Anonymous,\n",
                    "                    ),\n",
                    "                    component: \"x\",\n",
                    "                    hash: 13655884332201764339,\n",
                    "                },\n",
                    "            ),\n",
                    "        ),\n",
                    "        levels: [\n",
                    "            Level {\n",
                    "                node: Zero,\n",
                    "                data: LevelData(\n",
                    "                    2221,\n",
                    "                ),\n",
                    "            },\n",
                    "            Level {\n",
                    "                node: Param(\n",
                    "                    Name(\n",
                    "                        Str(\n",
                    "                            StrNode {\n",
                    "                                pre: Name(\n",
                    "                                    Anonymous,\n",
                    "                                ),\n",
                    "                                component: \"x\",\n",
                    "                                hash: 13655884332201764339,\n",
                    "                            },\n",
                    "                        ),\n",
                    "                    ),\n",
                    "                ),\n",
                    "                data: LevelData(\n",
                    "                    10400061217,\n",
                    "                ),\n",
                    "            },\n",
                    "        ],\n",
                    "    },\n",
                    "    data: ExprData(\n",
                    "        8796919455285,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "app",
                "Expr { node: App { f: Expr { node: BVar { idx: 0 }, data: ExprData(17592537633786) }, a: Expr { node: Sort { level: Level { node: Zero, data: LevelData(2221) } }, data: ExprData(3944470172) } }, data: ExprData(17599949397516) }",
                concat!(
                    "Expr {\n",
                    "    node: App {\n",
                    "        f: Expr {\n",
                    "            node: BVar {\n",
                    "                idx: 0,\n",
                    "            },\n",
                    "            data: ExprData(\n",
                    "                17592537633786,\n",
                    "            ),\n",
                    "        },\n",
                    "        a: Expr {\n",
                    "            node: Sort {\n",
                    "                level: Level {\n",
                    "                    node: Zero,\n",
                    "                    data: LevelData(\n",
                    "                        2221,\n",
                    "                    ),\n",
                    "                },\n",
                    "            },\n",
                    "            data: ExprData(\n",
                    "                3944470172,\n",
                    "            ),\n",
                    "        },\n",
                    "    },\n",
                    "    data: ExprData(\n",
                    "        17599949397516,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "lam",
                "Expr { node: Lam { binder_name: Name(Str(StrNode { pre: Name(Anonymous), component: \"x\", hash: 13655884332201764339 })), binder_type: Expr { node: Sort { level: Level { node: Zero, data: LevelData(2221) } }, data: ExprData(3944470172) }, body: Expr { node: BVar { idx: 0 }, data: ExprData(17592537633786) }, binder_info: Implicit }, data: ExprData(8115984807) }",
                concat!(
                    "Expr {\n",
                    "    node: Lam {\n",
                    "        binder_name: Name(\n",
                    "            Str(\n",
                    "                StrNode {\n",
                    "                    pre: Name(\n",
                    "                        Anonymous,\n",
                    "                    ),\n",
                    "                    component: \"x\",\n",
                    "                    hash: 13655884332201764339,\n",
                    "                },\n",
                    "            ),\n",
                    "        ),\n",
                    "        binder_type: Expr {\n",
                    "            node: Sort {\n",
                    "                level: Level {\n",
                    "                    node: Zero,\n",
                    "                    data: LevelData(\n",
                    "                        2221,\n",
                    "                    ),\n",
                    "                },\n",
                    "            },\n",
                    "            data: ExprData(\n",
                    "                3944470172,\n",
                    "            ),\n",
                    "        },\n",
                    "        body: Expr {\n",
                    "            node: BVar {\n",
                    "                idx: 0,\n",
                    "            },\n",
                    "            data: ExprData(\n",
                    "                17592537633786,\n",
                    "            ),\n",
                    "        },\n",
                    "        binder_info: Implicit,\n",
                    "    },\n",
                    "    data: ExprData(\n",
                    "        8115984807,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "forall",
                "Expr { node: ForallE { binder_name: Name(Str(StrNode { pre: Name(Anonymous), component: \"x\", hash: 13655884332201764339 })), binder_type: Expr { node: Sort { level: Level { node: Zero, data: LevelData(2221) } }, data: ExprData(3944470172) }, body: Expr { node: BVar { idx: 0 }, data: ExprData(17592537633786) }, binder_info: StrictImplicit }, data: ExprData(8115984807) }",
                concat!(
                    "Expr {\n",
                    "    node: ForallE {\n",
                    "        binder_name: Name(\n",
                    "            Str(\n",
                    "                StrNode {\n",
                    "                    pre: Name(\n",
                    "                        Anonymous,\n",
                    "                    ),\n",
                    "                    component: \"x\",\n",
                    "                    hash: 13655884332201764339,\n",
                    "                },\n",
                    "            ),\n",
                    "        ),\n",
                    "        binder_type: Expr {\n",
                    "            node: Sort {\n",
                    "                level: Level {\n",
                    "                    node: Zero,\n",
                    "                    data: LevelData(\n",
                    "                        2221,\n",
                    "                    ),\n",
                    "                },\n",
                    "            },\n",
                    "            data: ExprData(\n",
                    "                3944470172,\n",
                    "            ),\n",
                    "        },\n",
                    "        body: Expr {\n",
                    "            node: BVar {\n",
                    "                idx: 0,\n",
                    "            },\n",
                    "            data: ExprData(\n",
                    "                17592537633786,\n",
                    "            ),\n",
                    "        },\n",
                    "        binder_info: StrictImplicit,\n",
                    "    },\n",
                    "    data: ExprData(\n",
                    "        8115984807,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "let",
                "Expr { node: LetE { decl_name: Name(Str(StrNode { pre: Name(Anonymous), component: \"x\", hash: 13655884332201764339 })), type_: Expr { node: Sort { level: Level { node: Zero, data: LevelData(2221) } }, data: ExprData(3944470172) }, value: Expr { node: BVar { idx: 0 }, data: ExprData(17592537633786) }, body: Expr { node: BVar { idx: 0 }, data: ExprData(17592537633786) }, non_dep: true }, data: ExprData(17600335613723) }",
                concat!(
                    "Expr {\n",
                    "    node: LetE {\n",
                    "        decl_name: Name(\n",
                    "            Str(\n",
                    "                StrNode {\n",
                    "                    pre: Name(\n",
                    "                        Anonymous,\n",
                    "                    ),\n",
                    "                    component: \"x\",\n",
                    "                    hash: 13655884332201764339,\n",
                    "                },\n",
                    "            ),\n",
                    "        ),\n",
                    "        type_: Expr {\n",
                    "            node: Sort {\n",
                    "                level: Level {\n",
                    "                    node: Zero,\n",
                    "                    data: LevelData(\n",
                    "                        2221,\n",
                    "                    ),\n",
                    "                },\n",
                    "            },\n",
                    "            data: ExprData(\n",
                    "                3944470172,\n",
                    "            ),\n",
                    "        },\n",
                    "        value: Expr {\n",
                    "            node: BVar {\n",
                    "                idx: 0,\n",
                    "            },\n",
                    "            data: ExprData(\n",
                    "                17592537633786,\n",
                    "            ),\n",
                    "        },\n",
                    "        body: Expr {\n",
                    "            node: BVar {\n",
                    "                idx: 0,\n",
                    "            },\n",
                    "            data: ExprData(\n",
                    "                17592537633786,\n",
                    "            ),\n",
                    "        },\n",
                    "        non_dep: true,\n",
                    "    },\n",
                    "    data: ExprData(\n",
                    "        17600335613723,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "lit_nat",
                "Expr { node: Lit { literal: Nat(NatLit { limbs: [7] }) }, data: ExprData(2256147412) }",
                concat!(
                    "Expr {\n",
                    "    node: Lit {\n",
                    "        literal: Nat(\n",
                    "            NatLit {\n",
                    "                limbs: [\n",
                    "                    7,\n",
                    "                ],\n",
                    "            },\n",
                    "        ),\n",
                    "    },\n",
                    "    data: ExprData(\n",
                    "        2256147412,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "lit_str",
                "Expr { node: Lit { literal: Str(\"s\") }, data: ExprData(357756915) }",
                concat!(
                    "Expr {\n",
                    "    node: Lit {\n",
                    "        literal: Str(\n",
                    "            \"s\",\n",
                    "        ),\n",
                    "    },\n",
                    "    data: ExprData(\n",
                    "        357756915,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "mdata",
                "Expr { node: MData { data: KVMap { entries: [] }, expr: Expr { node: BVar { idx: 0 }, data: ExprData(17592537633786) } }, data: ExprData(17600722897194) }",
                concat!(
                    "Expr {\n",
                    "    node: MData {\n",
                    "        data: KVMap {\n",
                    "            entries: [],\n",
                    "        },\n",
                    "        expr: Expr {\n",
                    "            node: BVar {\n",
                    "                idx: 0,\n",
                    "            },\n",
                    "            data: ExprData(\n",
                    "                17592537633786,\n",
                    "            ),\n",
                    "        },\n",
                    "    },\n",
                    "    data: ExprData(\n",
                    "        17600722897194,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "proj",
                "Expr { node: Proj { struct_name: Name(Str(StrNode { pre: Name(Anonymous), component: \"x\", hash: 13655884332201764339 })), idx: 3, expr: Expr { node: BVar { idx: 0 }, data: ExprData(17592537633786) } }, data: ExprData(17599591845530) }",
                concat!(
                    "Expr {\n",
                    "    node: Proj {\n",
                    "        struct_name: Name(\n",
                    "            Str(\n",
                    "                StrNode {\n",
                    "                    pre: Name(\n",
                    "                        Anonymous,\n",
                    "                    ),\n",
                    "                    component: \"x\",\n",
                    "                    hash: 13655884332201764339,\n",
                    "                },\n",
                    "            ),\n",
                    "        ),\n",
                    "        idx: 3,\n",
                    "        expr: Expr {\n",
                    "            node: BVar {\n",
                    "                idx: 0,\n",
                    "            },\n",
                    "            data: ExprData(\n",
                    "                17592537633786,\n",
                    "            ),\n",
                    "        },\n",
                    "    },\n",
                    "    data: ExprData(\n",
                    "        17599591845530,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "nested",
                "Expr { node: App { f: Expr { node: App { f: Expr { node: BVar { idx: 0 }, data: ExprData(17592537633786) }, a: Expr { node: Sort { level: Level { node: Zero, data: LevelData(2221) } }, data: ExprData(3944470172) } }, data: ExprData(17599949397516) }, a: Expr { node: BVar { idx: 0 }, data: ExprData(17592537633786) } }, data: ExprData(17601966845473) }",
                concat!(
                    "Expr {\n",
                    "    node: App {\n",
                    "        f: Expr {\n",
                    "            node: App {\n",
                    "                f: Expr {\n",
                    "                    node: BVar {\n",
                    "                        idx: 0,\n",
                    "                    },\n",
                    "                    data: ExprData(\n",
                    "                        17592537633786,\n",
                    "                    ),\n",
                    "                },\n",
                    "                a: Expr {\n",
                    "                    node: Sort {\n",
                    "                        level: Level {\n",
                    "                            node: Zero,\n",
                    "                            data: LevelData(\n",
                    "                                2221,\n",
                    "                            ),\n",
                    "                        },\n",
                    "                    },\n",
                    "                    data: ExprData(\n",
                    "                        3944470172,\n",
                    "                    ),\n",
                    "                },\n",
                    "            },\n",
                    "            data: ExprData(\n",
                    "                17599949397516,\n",
                    "            ),\n",
                    "        },\n",
                    "        a: Expr {\n",
                    "            node: BVar {\n",
                    "                idx: 0,\n",
                    "            },\n",
                    "            data: ExprData(\n",
                    "                17592537633786,\n",
                    "            ),\n",
                    "        },\n",
                    "    },\n",
                    "    data: ExprData(\n",
                    "        17601966845473,\n",
                    "    ),\n",
                    "}",
                ),
            ),
        ];
        assert_eq!(values.len(), GOLDENS.len());
        for ((label, value), (golden_label, plain, alternate)) in values.iter().zip(GOLDENS) {
            assert_eq!(*label, golden_label, "vector order drifted");
            assert_eq!(
                format!("{value:?}"),
                plain,
                "plain Debug changed for `{label}`"
            );
            assert_eq!(
                format!("{value:#?}"),
                alternate,
                "pretty Debug changed for `{label}`"
            );
        }
    }

    /// Formatting is the other structural traversal: it must be depth-independent
    /// in both modes, and every node must still appear in the output.
    ///
    /// The two modes run at different depths on purpose. Plain rendering is linear
    /// in the input, so it runs deep. Pretty rendering indents each nesting level
    /// by four spaces, which makes its *output* quadratic in depth — a property of
    /// `{:#?}` itself, unchanged by this walk — so it runs at a depth whose output
    /// stays a few megabytes. Both are far past the recursion threshold: the
    /// recursive renderer this replaces aborted at depth 2000 on this stack.
    #[test]
    fn deep_debug_rendering_is_stack_bounded() {
        const PLAIN_DEPTH: usize = 100_000;
        const PRETTY_DEPTH: usize = 1_000;

        fn app_spine(depth: usize) -> Expr {
            let mut expr = Expr::sort(Level::zero());
            for _ in 0..depth {
                expr = Expr::app(expr, Expr::bvar(0).expect("small"));
            }
            expr
        }

        let outcome = std::thread::Builder::new()
            .stack_size(1024 * 1024)
            .spawn(|| {
                let deep = app_spine(PLAIN_DEPTH);
                let plain = format!("{deep:?}");
                assert_eq!(plain.matches("App {").count(), PLAIN_DEPTH);

                let shallower = app_spine(PRETTY_DEPTH);
                let pretty = format!("{shallower:#?}");
                assert_eq!(pretty.matches("App {").count(), PRETTY_DEPTH);
            })
            .expect("spawn bounded-stack Expr formatter")
            .join();
        assert!(
            outcome.is_ok(),
            "deep Expr formatting exhausted the bounded worker stack"
        );
    }
}
