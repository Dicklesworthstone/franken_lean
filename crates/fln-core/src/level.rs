//! Universe levels with the Reference-observable data word and normalization
//! (plan §1.1, §21).
//!
//! Semantics anchors (vendor/lean4-src at the SUITE.lock pin):
//! * inductive + `@[computed_field] data` — src/Lean/Level.lean:89-107
//!   (seeds: zero=2221, mvar=2237, param=2239, succ=2243, max=2251, imax=2267);
//! * `Level.Data` packing — Level.lean:22-49: bits 0-31 hash, bit 32 hasMVar,
//!   bit 33 hasParam, bits 40-63 depth (24 bits);
//! * `lean_level_mk_data` — src/kernel/level.cpp:44-52: hash truncated to 32 bits,
//!   depth limited to 16777215 (upstream panics above; we return a typed error —
//!   malformed input must not panic, D8 taxonomy);
//! * normalization — Level.lean:266-401 (ctorToNat, normLtAux, getMaxArgsAux,
//!   accMax/mkMaxAux, skipExplicit/isExplicitSubsumed, mkIMaxAux, normalize);
//! * cheap smart constructors — Level.lean:516-551 (mkLevelMax', mkLevelIMax');
//! * `isEquiv` = `u == v || u.normalize == v.normalize` — Level.lean:403-408.
//!
//! `LMVarId` is a `Name` wrapper whose derived hash is `mixHash 0 name.hash`
//! (deriving-handler semantics, src/Lean/Elab/Deriving/Hashable.lean).

use std::sync::Arc;

use crate::lean_hash::mix_hash;
use crate::name::Name;

/// Maximum representable level depth (2^24 - 1); level.cpp:48.
pub const MAX_LEVEL_DEPTH: u32 = 16_777_215;

/// Universe metavariable identity (`LevelMVarId`): a `Name` with the derived hash.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LMVarId(pub Name);

impl LMVarId {
    /// Derived `Hashable LevelMVarId`: ctor index 0 mixed with the field hash.
    pub fn hash(&self) -> u64 {
        mix_hash(0, self.0.hash())
    }
}

/// The packed observable word (`Level.Data`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LevelData(pub u64);

impl LevelData {
    /// `lean_level_mk_data` with the panic replaced by a typed refusal.
    fn pack(
        hash: u64,
        depth: u32,
        has_mvar: bool,
        has_param: bool,
    ) -> Result<LevelData, LevelTooDeep> {
        if depth > MAX_LEVEL_DEPTH {
            return Err(LevelTooDeep { depth });
        }
        Ok(LevelData(
            u64::from(hash as u32)
                + (u64::from(has_mvar) << 32)
                + (u64::from(has_param) << 33)
                + (u64::from(depth) << 40),
        ))
    }

    /// `Level.Data.hash` — the low 32 bits, zero-extended.
    pub fn hash(self) -> u64 {
        u64::from(self.0 as u32)
    }

    /// `Level.Data.depth`.
    pub fn depth(self) -> u32 {
        (self.0 >> 40) as u32
    }

    /// `Level.Data.hasMVar`.
    pub fn has_mvar(self) -> bool {
        (self.0 >> 32) & 1 == 1
    }

    /// `Level.Data.hasParam`.
    pub fn has_param(self) -> bool {
        (self.0 >> 33) & 1 == 1
    }
}

/// Typed refusal for a depth beyond the 24-bit packing (upstream: internal panic
/// "universe level depth is too big"; FrankenLean: a value, never a panic).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LevelTooDeep {
    pub depth: u32,
}

impl std::fmt::Display for LevelTooDeep {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "universe level depth {} exceeds the 24-bit packing",
            self.depth
        )
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
enum Node {
    Zero,
    Succ(Level),
    Max(Level, Level),
    IMax(Level, Level),
    Param(Name),
    MVar(LMVarId),
}

/// A universe level. Immutable, cheaply clonable, carrying its computed data word.
#[derive(Clone)]
pub struct Level {
    // Live values are always `Some`; `None` exists only while `Drop` drains a
    // last-reference cascade iteratively in safe Rust. `Option<Arc<_>>` uses the
    // null-pointer niche, so this does not enlarge `Level`.
    node: Option<Arc<Node>>,
    data: LevelData,
}

impl std::fmt::Debug for Level {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Level")
            .field("node", self.node())
            .field("data", &self.data)
            .finish()
    }
}

impl PartialEq for Level {
    fn eq(&self, other: &Level) -> bool {
        // Data word first (hash/depth/flags reject fast), then structure — the same
        // discipline as lean_level_eq (kernel/level.cpp:125-150).
        self.data == other.data
            && (Arc::ptr_eq(self.node_arc(), other.node_arc()) || self.node() == other.node())
    }
}
impl Eq for Level {}

impl std::hash::Hash for Level {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&self.data.0, state);
    }
}

/// Borrowed constructor view (see [`Level::view`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LevelView<'a> {
    Zero,
    Succ(&'a Level),
    Max(&'a Level, &'a Level),
    IMax(&'a Level, &'a Level),
    Param(&'a Name),
    MVar(&'a LMVarId),
}

const SEED_ZERO: u64 = 2221;
const SEED_MVAR: u64 = 2237;
const SEED_PARAM: u64 = 2239;
const SEED_SUCC: u64 = 2243;
const SEED_MAX: u64 = 2251;
const SEED_IMAX: u64 = 2267;

impl Level {
    /// `Level.zero`.
    pub fn zero() -> Level {
        Level {
            node: Some(Arc::new(Node::Zero)),
            data: LevelData::pack(SEED_ZERO, 0, false, false).expect("depth 0 packs"),
        }
    }

    /// `Level.one` = `succ zero`.
    pub fn one() -> Level {
        Level::zero().succ().expect("depth 1 packs")
    }

    /// `Level.param n`.
    pub fn param(name: Name) -> Level {
        let data = LevelData::pack(mix_hash(SEED_PARAM, name.hash()), 0, false, true)
            .expect("depth 0 packs");
        Level {
            node: Some(Arc::new(Node::Param(name))),
            data,
        }
    }

    /// `Level.mvar id`.
    pub fn mvar(id: LMVarId) -> Level {
        let data =
            LevelData::pack(mix_hash(SEED_MVAR, id.hash()), 0, true, false).expect("depth 0 packs");
        Level {
            node: Some(Arc::new(Node::MVar(id))),
            data,
        }
    }

    /// `Level.succ self`. The only failure mode is the 24-bit depth covenant.
    pub fn succ(self) -> Result<Level, LevelTooDeep> {
        let data = LevelData::pack(
            mix_hash(SEED_SUCC, self.data.hash()),
            self.data.depth() + 1,
            self.data.has_mvar(),
            self.data.has_param(),
        )?;
        Ok(Level {
            node: Some(Arc::new(Node::Succ(self))),
            data,
        })
    }

    /// `Level.max u v` (raw constructor `mkLevelMax`, no simplification).
    pub fn max(u: Level, v: Level) -> Result<Level, LevelTooDeep> {
        let data = LevelData::pack(
            mix_hash(SEED_MAX, mix_hash(u.data.hash(), v.data.hash())),
            u.data.depth().max(v.data.depth()) + 1,
            u.data.has_mvar() || v.data.has_mvar(),
            u.data.has_param() || v.data.has_param(),
        )?;
        Ok(Level {
            node: Some(Arc::new(Node::Max(u, v))),
            data,
        })
    }

    /// `Level.imax u v` (raw constructor `mkLevelIMax`, no simplification).
    pub fn imax(u: Level, v: Level) -> Result<Level, LevelTooDeep> {
        let data = LevelData::pack(
            mix_hash(SEED_IMAX, mix_hash(u.data.hash(), v.data.hash())),
            u.data.depth().max(v.data.depth()) + 1,
            u.data.has_mvar() || v.data.has_mvar(),
            u.data.has_param() || v.data.has_param(),
        )?;
        Ok(Level {
            node: Some(Arc::new(Node::IMax(u, v))),
            data,
        })
    }

    fn node_arc(&self) -> &Arc<Node> {
        self.node.as_ref().expect("a live Level always owns a node")
    }

    fn node(&self) -> &Node {
        self.node_arc()
    }

    fn take_node_for_drop(&mut self) -> Option<Arc<Node>> {
        self.node.take()
    }

    // ---- observables -------------------------------------------------------------------

    /// `Level.hash` — the stored 32-bit hash, zero-extended (Level.lean:111-113).
    pub fn hash(&self) -> u64 {
        self.data.hash()
    }

    /// The packed data word itself.
    pub fn data(&self) -> LevelData {
        self.data
    }

    /// `Level.depth`.
    pub fn depth(&self) -> u32 {
        self.data.depth()
    }

    pub fn has_mvar(&self) -> bool {
        self.data.has_mvar()
    }

    pub fn has_param(&self) -> bool {
        self.data.has_param()
    }

    pub fn is_zero(&self) -> bool {
        matches!(self.node(), Node::Zero)
    }

    /// Borrowed structural view — the constructor-inventory access canonical codecs
    /// and pretty-printers need without exposing the internal representation.
    pub fn view(&self) -> LevelView<'_> {
        match self.node() {
            Node::Zero => LevelView::Zero,
            Node::Succ(u) => LevelView::Succ(u),
            Node::Max(u, v) => LevelView::Max(u, v),
            Node::IMax(u, v) => LevelView::IMax(u, v),
            Node::Param(n) => LevelView::Param(n),
            Node::MVar(m) => LevelView::MVar(m),
        }
    }

    // ---- structure ---------------------------------------------------------------------

    /// `Level.isExplicit`: a numeral `succ^k zero` (Level.lean:233-236).
    pub fn is_explicit(&self) -> bool {
        match self.node() {
            Node::Zero => true,
            Node::Succ(u) => !u.has_mvar() && !u.has_param() && u.is_explicit(),
            _ => false,
        }
    }

    /// `Level.getOffset`: the count of outer `succ`s.
    pub fn get_offset(&self) -> u32 {
        let mut level = self;
        let mut offset = 0;
        while let Node::Succ(u) = level.node() {
            offset += 1;
            level = u;
        }
        offset
    }

    /// `Level.getLevelOffset`: the level under all outer `succ`s.
    pub fn get_level_offset(&self) -> &Level {
        let mut level = self;
        while let Node::Succ(u) = level.node() {
            level = u;
        }
        level
    }

    /// `Level.addOffset`.
    pub fn add_offset(&self, offset: u32) -> Result<Level, LevelTooDeep> {
        let mut level = self.clone();
        for _ in 0..offset {
            level = level.succ()?;
        }
        Ok(level)
    }

    /// `Level.toNat`: `some k` iff the level is the numeral `k`.
    pub fn to_nat(&self) -> Option<u32> {
        if self.get_level_offset().is_zero() {
            Some(self.get_offset())
        } else {
            None
        }
    }

    /// `Level.isNeverZero` (Level.lean:210-217).
    pub fn is_never_zero(&self) -> bool {
        match self.node() {
            Node::Zero | Node::Param(_) | Node::MVar(_) => false,
            Node::Succ(_) => true,
            Node::Max(u, v) => u.is_never_zero() || v.is_never_zero(),
            Node::IMax(_, v) => v.is_never_zero(),
        }
    }

    /// `Level.isAlwaysZero` (Level.lean:199-208).
    pub fn is_always_zero(&self) -> bool {
        match self.node() {
            Node::Zero => true,
            Node::Param(_) | Node::MVar(_) | Node::Succ(_) => false,
            Node::Max(u, v) => u.is_always_zero() && v.is_always_zero(),
            Node::IMax(_, v) => v.is_always_zero(),
        }
    }

    /// `Level.occurs u v` — does `self` occur (as a subterm) in `inside`?
    pub fn occurs_in(&self, inside: &Level) -> bool {
        if self == inside {
            return true;
        }
        match inside.node() {
            Node::Succ(u) => self.occurs_in(u),
            Node::Max(u, v) | Node::IMax(u, v) => self.occurs_in(u) || self.occurs_in(v),
            _ => false,
        }
    }

    /// `Level.dec` (Level.lean:411-419). Note the pin maps BOTH `max` and `imax`
    /// through `mkLevelMax` — faithful, not a typo here.
    pub fn dec(&self) -> Option<Level> {
        match self.node() {
            Node::Zero | Node::Param(_) | Node::MVar(_) => None,
            Node::Succ(u) => Some(u.clone()),
            Node::Max(u, v) | Node::IMax(u, v) => {
                let du = u.dec()?;
                let dv = v.dec()?;
                Some(Level::max(du, dv).expect("dec cannot deepen"))
            }
        }
    }

    // ---- normalization -----------------------------------------------------------------

    /// `ctorToNat` (Level.lean:266-272) — note: NOT the declaration order.
    fn ctor_rank(&self) -> u8 {
        match self.node() {
            Node::Zero => 0,
            Node::Param(_) => 1,
            Node::MVar(_) => 2,
            Node::Succ(_) => 3,
            Node::Max(..) => 4,
            Node::IMax(..) => 5,
        }
    }

    /// `normLtAux` (Level.lean:274-293).
    fn norm_lt_aux(l1: &Level, k1: u32, l2: &Level, k2: u32) -> bool {
        if let Node::Succ(u1) = l1.node() {
            return Level::norm_lt_aux(u1, k1 + 1, l2, k2);
        }
        if let Node::Succ(u2) = l2.node() {
            return Level::norm_lt_aux(l1, k1, u2, k2 + 1);
        }
        match (l1.node(), l2.node()) {
            (Node::Max(a1, b1), Node::Max(a2, b2)) | (Node::IMax(a1, b1), Node::IMax(a2, b2)) => {
                if l1 == l2 {
                    k1 < k2
                } else if a1 != a2 {
                    Level::norm_lt_aux(a1, 0, a2, 0)
                } else {
                    Level::norm_lt_aux(b1, 0, b2, 0)
                }
            }
            (Node::Param(n1), Node::Param(n2)) => {
                if n1 == n2 {
                    k1 < k2
                } else {
                    // Name.lt (lexicographical): stable across shifted mvar indexes.
                    n1.lt(n2)
                }
            }
            (Node::MVar(m1), Node::MVar(m2)) => {
                if m1 == m2 {
                    k1 < k2
                } else {
                    m1.0.lt(&m2.0)
                }
            }
            _ => {
                if l1 == l2 {
                    k1 < k2
                } else {
                    l1.ctor_rank() < l2.ctor_rank()
                }
            }
        }
    }

    /// `normLt` — the normalization total order.
    pub fn norm_lt(&self, other: &Level) -> bool {
        Level::norm_lt_aux(self, 0, other, 0)
    }

    /// `isAlreadyNormalizedCheap` (Level.lean:303-308).
    fn is_already_normalized_cheap(&self) -> bool {
        match self.node() {
            Node::Zero | Node::Param(_) | Node::MVar(_) => true,
            Node::Succ(u) => u.is_already_normalized_cheap(),
            _ => false,
        }
    }

    /// `mkIMaxAux` (Level.lean:311-315).
    fn mk_imax_aux(u1: Level, u2: Level) -> Level {
        if u2.is_zero() {
            return u2; // imax _ 0 = 0
        }
        if u1.is_zero() {
            return u2; // imax 0 u = u
        }
        if let Node::Succ(inner) = u1.node()
            && inner.is_zero()
        {
            return u2; // imax 1 u = u
        }
        if u1 == u2 {
            return u1; // imax u u = u
        }
        Level::imax(u1, u2).expect("children already packed")
    }

    /// `getMaxArgsAux` (Level.lean:318-321): flatten nested `max`, normalizing each
    /// non-max leaf once. Left child first.
    fn collect_max_args(level: &Level, already_normalized: bool, out: &mut Vec<Level>) {
        match level.node() {
            Node::Max(a, b) => {
                Level::collect_max_args(a, already_normalized, out);
                Level::collect_max_args(b, already_normalized, out);
            }
            _ if !already_normalized => {
                let normalized = level.normalize();
                Level::collect_max_args(&normalized, true, out);
            }
            _ => out.push(level.clone()),
        }
    }

    /// `accMax` (Level.lean:323-325).
    fn acc_max(result: Level, prev: &Level, offset: u32) -> Level {
        let shifted = prev
            .add_offset(offset)
            .expect("normalization cannot deepen");
        if result.is_zero() {
            shifted
        } else {
            Level::max(result, shifted).expect("children already packed")
        }
    }

    /// `mkMaxAux` (Level.lean:335-345).
    fn mk_max_aux(
        lvls: &[Level],
        extra_k: u32,
        mut i: usize,
        mut prev: Level,
        mut prev_k: u32,
        mut result: Level,
    ) -> Level {
        while i < lvls.len() {
            let lvl = &lvls[i];
            let curr = lvl.get_level_offset().clone();
            let curr_k = lvl.get_offset();
            if curr == prev {
                prev = curr;
                prev_k = curr_k;
            } else {
                result = Level::acc_max(result, &prev, extra_k + prev_k);
                prev = curr;
                prev_k = curr_k;
            }
            i += 1;
        }
        Level::acc_max(result, &prev, extra_k + prev_k)
    }

    /// `skipExplicit` (Level.lean:350-355): index of the first non-numeral entry.
    fn skip_explicit(lvls: &[Level]) -> usize {
        lvls.iter()
            .position(|l| !l.get_level_offset().is_zero())
            .unwrap_or(lvls.len())
    }

    /// `isExplicitSubsumed` (Level.lean:357-377).
    fn is_explicit_subsumed(lvls: &[Level], first_non_explicit: usize) -> bool {
        if first_non_explicit == 0 {
            return false;
        }
        let max_explicit = lvls[first_non_explicit - 1].get_offset();
        lvls[first_non_explicit..]
            .iter()
            .any(|l| l.get_offset() >= max_explicit)
    }

    /// `Level.normalize` (Level.lean:379-401).
    pub fn normalize(&self) -> Level {
        if self.is_already_normalized_cheap() {
            return self.clone();
        }
        let k = self.get_offset();
        let u = self.get_level_offset();
        match u.node() {
            Node::Max(l1, l2) => {
                let mut lvls: Vec<Level> = Vec::new();
                Level::collect_max_args(l1, false, &mut lvls);
                Level::collect_max_args(l2, false, &mut lvls);
                // `Array.qsort normLt` — order by the normalization total order.
                // A stable sort with a strict-weak `normLt` yields the same sequence.
                lvls.sort_by(|a, b| {
                    if a.norm_lt(b) {
                        std::cmp::Ordering::Less
                    } else if b.norm_lt(a) {
                        std::cmp::Ordering::Greater
                    } else {
                        std::cmp::Ordering::Equal
                    }
                });
                let first_non_explicit = Level::skip_explicit(&lvls);
                let i = if Level::is_explicit_subsumed(&lvls, first_non_explicit) {
                    first_non_explicit
                } else {
                    first_non_explicit.saturating_sub(1)
                };
                let lvl1 = &lvls[i];
                let prev = lvl1.get_level_offset().clone();
                let prev_k = lvl1.get_offset();
                Level::mk_max_aux(&lvls, k, i + 1, prev, prev_k, Level::zero())
            }
            Node::IMax(l1, l2) => {
                if l2.is_never_zero() {
                    let as_max = Level::max(l1.clone(), l2.clone()).expect("children packed");
                    as_max
                        .normalize()
                        .add_offset(k)
                        .expect("normalization cannot deepen")
                } else {
                    let n1 = l1.normalize();
                    let n2 = l2.normalize();
                    Level::mk_imax_aux(n1, n2)
                        .add_offset(k)
                        .expect("normalization cannot deepen")
                }
            }
            _ => unreachable!("cheap-normalized levels are handled above"),
        }
    }

    /// `Level.isEquiv` (Level.lean:403-408).
    pub fn is_equiv(&self, other: &Level) -> bool {
        self == other || self.normalize() == other.normalize()
    }

    /// `is_not_zero` (vendor: src/kernel/level.cpp:160): `true` means NO
    /// parameter assignment can make this level zero. Conservatively `false`
    /// for params and mvars.
    pub fn is_not_zero(&self) -> bool {
        match self.view() {
            LevelView::Zero | LevelView::Param(_) | LevelView::MVar(_) => false,
            LevelView::Succ(_) => true,
            LevelView::Max(a, b) => a.is_not_zero() || b.is_not_zero(),
            LevelView::IMax(_, b) => b.is_not_zero(),
        }
    }

    /// `is_geq` (vendor: src/kernel/level.cpp:508-531): a sound approximation
    /// of "`self ≥ other` under every parameter assignment", computed on
    /// normalized forms exactly as the pin does. Used by KR-604 (constructor
    /// field universes) and KR-602/700 machinery.
    pub fn is_geq(&self, other: &Level) -> bool {
        fn to_offset(l: &Level) -> (Level, u32) {
            let mut base = l.clone();
            let mut k = 0u32;
            while let LevelView::Succ(inner) = base.view() {
                let inner = inner.clone();
                base = inner;
                k += 1;
            }
            (base, k)
        }
        fn core(l1: &Level, l2: &Level) -> bool {
            if l1 == l2 || l2.is_zero() {
                return true;
            }
            if let LevelView::Max(a, b) = l2.view() {
                return l1.is_geq(a) && l1.is_geq(b);
            }
            if let LevelView::Max(a, b) = l1.view()
                && (a.is_geq(l2) || b.is_geq(l2))
            {
                return true;
            }
            if let LevelView::IMax(a, b) = l2.view() {
                return l1.is_geq(a) && l1.is_geq(b);
            }
            if let LevelView::IMax(_, b) = l1.view() {
                return b.is_geq(l2);
            }
            let (base1, k1) = to_offset(l1);
            let (base2, k2) = to_offset(l2);
            if base1 == base2 || base2.is_zero() {
                return k1 >= k2;
            }
            if k1 == k2 && k1 > 0 {
                return base1.is_geq(&base2);
            }
            false
        }
        core(&self.normalize(), &other.normalize())
    }

    // ---- cheap smart constructors ------------------------------------------------------

    /// `subsumes` inside `mkLevelMaxCore` (Level.lean:517-522).
    fn subsumes(u: &Level, v: &Level) -> bool {
        if v.is_explicit() && u.get_offset() >= v.get_offset() {
            return true;
        }
        match u.node() {
            Node::Max(a, b) => v == a || v == b,
            _ => false,
        }
    }

    /// `mkLevelMax'` (Level.lean:516-533): the simplifying max builder.
    pub fn smart_max(u: Level, v: Level) -> Level {
        if u == v {
            return u;
        }
        if u.is_zero() {
            return v;
        }
        if v.is_zero() {
            return u;
        }
        if Level::subsumes(&u, &v) {
            return u;
        }
        if Level::subsumes(&v, &u) {
            return v;
        }
        if u.get_level_offset() == v.get_level_offset() {
            if u.get_offset() >= v.get_offset() {
                u
            } else {
                v
            }
        } else {
            Level::max(u, v).expect("children already packed")
        }
    }

    /// `mkLevelIMax'` (Level.lean:541-551): the simplifying imax builder.
    pub fn smart_imax(u: Level, v: Level) -> Level {
        if v.is_never_zero() {
            Level::smart_max(u, v)
        } else if v.is_zero() || u.is_zero() {
            // Distinct upstream arms (`v.isZero` then `u.isZero`) that both yield `v`.
            v
        } else if u == v {
            u
        } else {
            Level::imax(u, v).expect("children already packed")
        }
    }
}

impl Drop for Level {
    fn drop(&mut self) {
        let Some(root) = self.take_node_for_drop() else {
            return;
        };

        // Destruction follows ownership, not syntax depth.  Unwrap unique nodes
        // and move their child roots onto a heap worklist; shared nodes are only
        // decremented.  The holder of the eventual final reference performs the
        // same iterative drain, preserving exact `Arc` sharing without recursion.
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
                Node::Succ(mut level) => pending.extend(level.take_node_for_drop()),
                Node::Max(mut left, mut right) | Node::IMax(mut left, mut right) => {
                    pending.extend(left.take_node_for_drop());
                    pending.extend(right.take_node_for_drop());
                }
                Node::Zero | Node::Param(_) | Node::MVar(_) => {}
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(name: &str) -> Level {
        Level::param(Name::str(Name::anonymous(), name))
    }

    fn nat(k: u32) -> Level {
        Level::zero().add_offset(k).expect("small")
    }

    #[test]
    fn data_words_match_the_pin_formulas() {
        let zero = Level::zero();
        assert_eq!(zero.hash(), u64::from(2221u32));
        assert_eq!(zero.depth(), 0);
        assert!(!zero.has_mvar() && !zero.has_param());

        let u = p("u");
        assert_eq!(
            u.hash(),
            u64::from(mix_hash(2239, Name::str(Name::anonymous(), "u").hash()) as u32)
        );
        assert!(u.has_param() && !u.has_mvar());

        let m = Level::mvar(LMVarId(Name::str(Name::anonymous(), "m")));
        assert_eq!(
            m.hash(),
            u64::from(mix_hash(2237, mix_hash(0, Name::str(Name::anonymous(), "m").hash())) as u32)
        );
        assert!(m.has_mvar() && !m.has_param());

        let one = Level::one();
        assert_eq!(one.hash(), u64::from(mix_hash(2243, zero.hash()) as u32));
        assert_eq!(one.depth(), 1);

        let mx = Level::max(u.clone(), one.clone()).expect("packs");
        assert_eq!(
            mx.hash(),
            u64::from(mix_hash(2251, mix_hash(u.hash(), one.hash())) as u32)
        );
        assert_eq!(mx.depth(), 2);
        assert!(mx.has_param());

        let im = Level::imax(u.clone(), one).expect("packs");
        assert_eq!(im.hash() as u32 as u64, im.hash(), "hash is 32-bit");
        assert_ne!(im.hash(), mx.hash());
    }

    #[test]
    fn depth_covenant_is_a_typed_error_not_a_panic() {
        let mut level = Level::zero();
        // Build to exactly the cap via offsets — cheap because add_offset loops succ.
        level = level.add_offset(1000).expect("shallow");
        assert_eq!(level.depth(), 1000);
        // Constructing beyond 2^24-1 must refuse with LevelTooDeep. Direct unit check
        // on the packer (walking 16M succs in a test is pointless).
        assert_eq!(
            LevelData::pack(0, MAX_LEVEL_DEPTH + 1, false, false),
            Err(LevelTooDeep {
                depth: MAX_LEVEL_DEPTH + 1
            })
        );
        assert!(LevelData::pack(0, MAX_LEVEL_DEPTH, false, false).is_ok());
    }

    #[test]
    fn imax_collapse_laws() {
        let u = p("u");
        // imax u 0 = 0 — Prop impredicativity depends on this.
        let iz = Level::imax(u.clone(), Level::zero()).expect("packs");
        assert!(iz.normalize().is_zero());
        // imax 0 u = u, imax 1 u = u
        let zi = Level::imax(Level::zero(), u.clone()).expect("packs");
        assert_eq!(zi.normalize(), u);
        let oi = Level::imax(Level::one(), u.clone()).expect("packs");
        assert_eq!(oi.normalize(), u);
        // imax u u = u
        let uu = Level::imax(u.clone(), u.clone()).expect("packs");
        assert_eq!(uu.normalize(), u);
        // imax u (succ v) = max u (succ v) (never-zero RHS)
        let sv = p("v").succ().expect("packs");
        let i = Level::imax(u.clone(), sv.clone()).expect("packs");
        let m = Level::max(u.clone(), sv).expect("packs");
        assert_eq!(i.normalize(), m.normalize());
    }

    #[test]
    fn max_normalization_dedups_sorts_and_subsumes() {
        let u = p("u");
        let v = p("v");
        // max u u = u
        let muu = Level::max(u.clone(), u.clone()).expect("packs");
        assert_eq!(muu.normalize(), u);
        // max is ACI up to normalize: max u v == max v u
        let muv = Level::max(u.clone(), v.clone()).expect("packs");
        let mvu = Level::max(v.clone(), u.clone()).expect("packs");
        assert_eq!(muv.normalize(), mvu.normalize());
        // associativity flattening: max (max u v) v == max u v
        let nested = Level::max(muv.clone(), v.clone()).expect("packs");
        assert_eq!(nested.normalize(), muv.normalize());
        // numeral subsumption: max 1 (u+1) has the numeral subsumed (offset 1 >= 1)
        let u1 = u.clone().succ().expect("packs");
        let m = Level::max(nat(1), u1.clone()).expect("packs");
        assert_eq!(m.normalize(), u1);
        // but max 3 u keeps the numeral
        let m3 = Level::max(nat(3), u.clone()).expect("packs");
        let norm = m3.normalize();
        assert_eq!(
            norm,
            Level::max(nat(3), u.clone()).expect("packs").normalize()
        );
        assert!(!norm.is_zero());
        // offset distribution: (max u v) + 1 normalizes equal to max (u+1) (v+1)
        let lifted = muv.clone().succ().expect("packs");
        let distributed = Level::max(
            u.clone().succ().expect("packs"),
            v.clone().succ().expect("packs"),
        )
        .expect("packs");
        assert_eq!(lifted.normalize(), distributed.normalize());
    }

    #[test]
    fn is_equiv_and_norm_lt_are_consistent() {
        let u = p("u");
        let v = p("v");
        assert!(Level::zero().norm_lt(&u));
        assert!(u.norm_lt(&v) ^ v.norm_lt(&u)); // total on distinct params
        assert!(u.norm_lt(&u.clone().succ().expect("packs"))); // succ is immediate successor
        let a = Level::max(u.clone(), v.clone()).expect("packs");
        let b = Level::max(v, u).expect("packs");
        assert!(a.is_equiv(&b));
        assert!(!a.is_equiv(&Level::zero()));
    }

    #[test]
    fn smart_constructors_match_their_specs() {
        let u = p("u");
        let v = p("v");
        // mkLevelMax' identities
        assert_eq!(Level::smart_max(u.clone(), u.clone()), u);
        assert_eq!(Level::smart_max(Level::zero(), u.clone()), u);
        assert_eq!(Level::smart_max(u.clone(), Level::zero()), u);
        // explicit subsumption: max (u+2) 1 = u+2? No — subsumes needs v explicit and
        // offset(u) >= offset(v): u+2 vs numeral 1 → subsumed.
        let u2 = u.clone().add_offset(2).expect("packs");
        assert_eq!(Level::smart_max(u2.clone(), nat(1)), u2);
        // same base, larger offset wins
        let u1 = u.clone().succ().expect("packs");
        assert_eq!(Level::smart_max(u1.clone(), u.clone()), u1);
        // otherwise a raw max
        let m = Level::smart_max(u.clone(), v.clone());
        assert_eq!(m, Level::max(u.clone(), v.clone()).expect("packs"));
        // mkLevelIMax' laws
        assert_eq!(Level::smart_imax(u.clone(), Level::zero()), Level::zero());
        assert_eq!(Level::smart_imax(Level::zero(), v.clone()), v);
        assert_eq!(Level::smart_imax(u.clone(), u.clone()), u);
        let sv = v.clone().succ().expect("packs");
        assert_eq!(
            Level::smart_imax(u.clone(), sv.clone()),
            Level::smart_max(u.clone(), sv)
        );
    }

    #[test]
    fn structural_helpers() {
        let u = p("u");
        let u3 = u.clone().add_offset(3).expect("packs");
        assert_eq!(u3.get_offset(), 3);
        assert_eq!(u3.get_level_offset(), &u);
        assert_eq!(nat(4).to_nat(), Some(4));
        assert_eq!(u3.to_nat(), None);
        assert!(u3.is_never_zero());
        assert!(!u.is_never_zero());
        assert!(Level::zero().is_always_zero());
        assert!(!u.is_always_zero());
        assert!(u.occurs_in(&u3));
        assert!(!p("w").occurs_in(&u3));
        assert_eq!(
            u3.dec().expect("dec"),
            u.clone().add_offset(2).expect("packs")
        );
        assert_eq!(u.dec(), None);
        assert!(nat(2).is_explicit());
        assert!(!u.is_explicit());
    }

    #[test]
    fn iterative_drop_preserves_shared_level_arcs() {
        let leaf = p("u");
        assert_eq!(Arc::strong_count(leaf.node_arc()), 1);

        let root = Level::max(leaf.clone(), leaf.clone()).expect("packs");
        assert_eq!(Arc::strong_count(leaf.node_arc()), 3);
        let retained_root = root.clone();
        assert_eq!(Arc::strong_count(root.node_arc()), 2);

        drop(root);
        assert_eq!(Arc::strong_count(retained_root.node_arc()), 1);
        drop(retained_root);
        assert_eq!(Arc::strong_count(leaf.node_arc()), 1);
    }

    #[test]
    fn iterative_drop_releases_every_recursive_level_constructor_reference() {
        let leaf = p("u");
        let mut roots = vec![
            leaf.clone().succ().expect("shallow"),
            Level::max(leaf.clone(), leaf.clone()).expect("shallow"),
            Level::imax(leaf.clone(), leaf.clone()).expect("shallow"),
        ];
        assert_eq!(
            Arc::strong_count(leaf.node_arc()),
            6,
            "every recursive field owns exactly one Arc"
        );

        let mut state = 0xa409_3822_299f_31d0_u64;
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
    fn iterative_drop_drains_maximally_shared_level_dag_after_clone_permutations() {
        let leaf = p("u");
        let mut dag = leaf.clone();
        let mut retained_roots = Vec::new();
        for depth in 0_usize..64 {
            dag = if depth % 2 == 0 {
                Level::max(dag.clone(), dag.clone()).expect("shallow")
            } else {
                Level::imax(dag.clone(), dag.clone()).expect("shallow")
            };
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

        let mut state = 0x082e_fa98_ec4e_6c89_u64;
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
