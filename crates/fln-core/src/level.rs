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

use crate::debug_walk::FlatDebug;
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

/// Deliberately **not** `PartialEq`/`Eq`/`Hash`: each derived traversal descends
/// one stack frame per child and overflows on deep input.  Equality and hashing
/// are properties of [`Level`] — the former walks a heap worklist, the latter is
/// the O(1) data word.
#[derive(Debug)]
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
    /// Byte-identical to the derived rendering, walked on an explicit task stack:
    /// `debug_struct` would descend one frame per level and overflow on deep input
    /// (bead franken_lean-canon-stack-safe-drop-6gy).
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        enum Task<'a> {
            Level(&'a Level),
            Node(&'a Node),
            Field(&'static str),
            Entry,
            Leaf(&'a dyn std::fmt::Debug),
            Close,
        }

        let mut out = FlatDebug::new(f);
        let mut tasks = vec![Task::Level(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Level(level) => {
                    out.open_struct("Level")?;
                    tasks.push(Task::Close);
                    tasks.push(Task::Leaf(&level.data));
                    tasks.push(Task::Field("data"));
                    tasks.push(Task::Node(level.node()));
                    tasks.push(Task::Field("node"));
                }
                Task::Node(Node::Zero) => out.unit("Zero")?,
                Task::Node(Node::Succ(inner)) => {
                    out.open_tuple("Succ")?;
                    tasks.push(Task::Close);
                    tasks.push(Task::Level(inner));
                    out.entry()?;
                }
                Task::Node(Node::Max(left, right)) => {
                    out.open_tuple("Max")?;
                    tasks.push(Task::Close);
                    tasks.push(Task::Level(right));
                    tasks.push(Task::Entry);
                    tasks.push(Task::Level(left));
                    out.entry()?;
                }
                Task::Node(Node::IMax(left, right)) => {
                    out.open_tuple("IMax")?;
                    tasks.push(Task::Close);
                    tasks.push(Task::Level(right));
                    tasks.push(Task::Entry);
                    tasks.push(Task::Level(left));
                    out.entry()?;
                }
                Task::Node(Node::Param(name)) => {
                    out.open_tuple("Param")?;
                    out.entry()?;
                    out.leaf(name)?;
                    out.close()?;
                }
                Task::Node(Node::MVar(id)) => {
                    out.open_tuple("MVar")?;
                    out.entry()?;
                    out.leaf(id)?;
                    out.close()?;
                }
                Task::Field(name) => out.field(name)?,
                Task::Entry => out.entry()?,
                Task::Leaf(value) => out.leaf(value)?,
                Task::Close => out.close()?,
            }
        }
        Ok(())
    }
}

impl PartialEq for Level {
    fn eq(&self, other: &Level) -> bool {
        // Data word first (hash/depth/flags reject fast), then structure — the same
        // discipline as lean_level_eq (kernel/level.cpp:125-150).
        //
        // The comparison walks an explicit heap worklist rather than descending
        // through one `Level::eq` frame per input level: two independently built
        // deep-but-equal levels agree on every data word, so the structural arm is
        // reached at every node and a recursive comparison would consume the stack
        // in proportion to input depth.  Equality is a pure predicate, so visiting
        // the pending pairs in any order yields the same verdict.
        let mut pending: Vec<(&Level, &Level)> = vec![(self, other)];
        while let Some((left, right)) = pending.pop() {
            if left.data != right.data {
                return false;
            }
            if Arc::ptr_eq(left.node_arc(), right.node_arc()) {
                continue;
            }
            match (left.node(), right.node()) {
                (Node::Zero, Node::Zero) => {}
                (Node::Succ(a), Node::Succ(b)) => pending.push((a, b)),
                // Distinct constructors never compare equal, so `Max`/`IMax` may not
                // share an arm with each other.
                (Node::Max(a1, a2), Node::Max(b1, b2))
                | (Node::IMax(a1, a2), Node::IMax(b1, b2)) => {
                    pending.push((a2, b2));
                    pending.push((a1, b1));
                }
                (Node::Param(a), Node::Param(b)) => {
                    // `Name` compares iteratively (bead franken_lean-p8a.1).
                    if a != b {
                        return false;
                    }
                }
                (Node::MVar(a), Node::MVar(b)) => {
                    if a != b {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
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
    /// Flags are OR'd down the tower, so a param/mvar anywhere is visible
    /// here; `get_level_offset` peels succs iteratively.
    pub fn is_explicit(&self) -> bool {
        !self.has_mvar() && !self.has_param() && self.get_level_offset().is_zero()
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
        let mut stack = vec![self];
        while let Some(current) = stack.pop() {
            match current.node() {
                Node::Succ(_) => return true,
                Node::Max(u, v) => {
                    stack.push(v);
                    stack.push(u);
                }
                Node::IMax(_, v) => stack.push(v),
                Node::Zero | Node::Param(_) | Node::MVar(_) => {}
            }
        }
        false
    }

    /// `Level.isAlwaysZero` (Level.lean:199-208).
    pub fn is_always_zero(&self) -> bool {
        let mut stack = vec![self];
        while let Some(current) = stack.pop() {
            match current.node() {
                Node::Zero => {}
                Node::Max(u, v) => {
                    stack.push(v);
                    stack.push(u);
                }
                Node::IMax(_, v) => stack.push(v),
                Node::Param(_) | Node::MVar(_) | Node::Succ(_) => return false,
            }
        }
        true
    }

    /// `Level.occurs u v` — does `self` occur (as a subterm) in `inside`?
    pub fn occurs_in(&self, inside: &Level) -> bool {
        let mut stack = vec![inside];
        while let Some(current) = stack.pop() {
            if self == current {
                return true;
            }
            match current.node() {
                Node::Succ(u) => stack.push(u),
                Node::Max(u, v) | Node::IMax(u, v) => {
                    stack.push(v);
                    stack.push(u);
                }
                Node::Zero | Node::Param(_) | Node::MVar(_) => {}
            }
        }
        false
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
    fn norm_lt_aux(mut l1: &Level, mut k1: u32, mut l2: &Level, mut k2: u32) -> bool {
        // Peel succ towers on the heap. A 24-bit-legal tower would blow the
        // host stack if this stayed recursive (FL-INV-07).
        loop {
            if let Node::Succ(u1) = l1.node() {
                l1 = u1;
                k1 += 1;
                continue;
            }
            if let Node::Succ(u2) = l2.node() {
                l2 = u2;
                k2 += 1;
                continue;
            }
            break;
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
        matches!(
            self.get_level_offset().node(),
            Node::Zero | Node::Param(_) | Node::MVar(_)
        )
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
        let mut stack = vec![(level.clone(), already_normalized)];
        while let Some((current, already)) = stack.pop() {
            match current.node() {
                Node::Max(a, b) => {
                    stack.push((b.clone(), already));
                    stack.push((a.clone(), already));
                }
                _ if !already => {
                    let normalized = current.normalize();
                    stack.push((normalized, true));
                }
                _ => out.push(current),
            }
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

    /// A normalization fixpoint: apply [`Level::normalize`] until it stops changing.
    ///
    /// **This is not `Lean.Level.normalize` and must never be used where the pin's
    /// output is the observable** — not for `faithful`-mode artifacts, not for the
    /// `core_observables` oracle rows, not for anything a user metaprogram reads.
    /// Upstream's `normalize` is not idempotent and neither is ours (bead fln-0uvk,
    /// and `normalize_is_not_idempotent_and_the_pin_agrees` pins both steps against
    /// the pinned binary), so matching it means reproducing that.
    ///
    /// It exists for the consumers that non-idempotence actually endangers: anything
    /// that **stores, keys, digests, or caches** a normalized level and compares it
    /// later. For those, one-pass output is not canonical — `is_equiv(x, y)` and
    /// `is_equiv(x.normalize(), y)` can disagree (see
    /// `pre_normalization_changes_an_is_equiv_verdict`), which makes a verdict depend
    /// on how many times someone happened to normalize. That is the FL-INV-01 failure
    /// mode: same inputs, different answer, decided by history rather than by content.
    ///
    /// The loop is bounded because a fixpoint that fails to converge must be a typed
    /// outcome rather than a hang (FL-INV-07). Convergence within
    /// [`Level::NORMALIZE_FIXPOINT_PASSES`] is asserted over the generated corpus by
    /// `normalize_fixpoint_converges_and_is_idempotent`; the bound returns the last
    /// form reached rather than looping forever, so the worst case is a value that is
    /// merely normalized rather than canonical.
    pub fn normalize_fixpoint(&self) -> Level {
        let mut current = self.normalize();
        for _ in 1..Level::NORMALIZE_FIXPOINT_PASSES {
            let next = current.normalize();
            if next == current {
                return current;
            }
            current = next;
        }
        current
    }

    /// Passes [`Level::normalize_fixpoint`] will make before returning what it has.
    /// Two suffice for every shape observed so far — the extra headroom is so that a
    /// future normalization rule cannot turn a slow fixpoint into an unbounded loop.
    pub const NORMALIZE_FIXPOINT_PASSES: usize = 8;

    /// `Level.normalize` (Level.lean:379-401).
    ///
    /// Bit-faithful to the pin, **including its non-idempotence**: for
    /// `succ^k(imax a (succ b))` with `k ≥ 1` this collapses the `imax` to a `max`
    /// but leaves the offset outside, and a second pass distributes it. Use
    /// [`Level::normalize_fixpoint`] when a canonical form is what you need.
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
        let mut stack = vec![self];
        while let Some(current) = stack.pop() {
            match current.view() {
                LevelView::Succ(_) => return true,
                LevelView::Max(a, b) => {
                    stack.push(b);
                    stack.push(a);
                }
                LevelView::IMax(_, b) => stack.push(b),
                LevelView::Zero | LevelView::Param(_) | LevelView::MVar(_) => {}
            }
        }
        false
    }

    /// `is_geq` (vendor: src/kernel/level.cpp:508-531): a sound approximation
    /// of "`self ≥ other` under every parameter assignment", computed on
    /// normalized forms exactly as the pin does. Used by KR-604 (constructor
    /// field universes) and KR-602/700 machinery.
    pub fn is_geq(&self, other: &Level) -> bool {
        /// `Level.geq.go` (Level.lean:620-638), transcribed arm for arm.
        ///
        /// Two things here are load-bearing and were wrong in the previous
        /// re-derivation, which disagreed with the pinned binary on 5 of 196
        /// generated pairs (all of them `succ^k(imax _ (succ _))`, caught by
        /// crates/fln-core/tests/pin_ext_observables.rs):
        ///
        /// * the recursion is on `go`, **not** back through `is_geq`. Re-entering
        ///   `is_geq` normalizes again at every step, and `normalize` is not
        ///   idempotent (bead fln-0uvk), so the operands drifted mid-comparison.
        /// * the arm ORDER decides the answer. `imax` on the LEFT is consumed by
        ///   its own arm before `k` ever runs, and `k` is what handles `imax` on
        ///   the right. Testing the right-hand `imax` first — as the old code did —
        ///   answers a different question.
        fn offset_k(u: &Level, v: &Level) -> bool {
            let v_base = v.get_level_offset();
            (u.get_level_offset() == v_base || v_base.is_zero()) && u.get_offset() >= v.get_offset()
        }

        enum Op<'a> {
            Go(&'a Level, &'a Level),
            And,
            Or,
            OffsetK(&'a Level, &'a Level),
        }

        fn push_k<'a>(ops: &mut Vec<Op<'a>>, u: &'a Level, v: &'a Level) {
            match v.view() {
                LevelView::IMax(v1, v2) => {
                    ops.push(Op::And);
                    ops.push(Op::Go(u, v2));
                    ops.push(Op::Go(u, v1));
                }
                _ => ops.push(Op::OffsetK(u, v)),
            }
        }

        // Same arms as recursive `go`, evaluated on an explicit heap stack
        // so a legal max/imax spine cannot blow the host stack (FL-INV-07).
        // Combinators are pure, so evaluating both sides of ∧/∨ is the same
        // answer as short-circuiting.
        let lhs = self.normalize();
        let rhs = other.normalize();
        let mut ops = vec![Op::Go(&lhs, &rhs)];
        let mut vals: Vec<bool> = Vec::new();
        while let Some(op) = ops.pop() {
            match op {
                Op::And => {
                    let right = vals.pop().expect("geq ∧ has a right operand");
                    let left = vals.pop().expect("geq ∧ has a left operand");
                    vals.push(left && right);
                }
                Op::Or => {
                    let right = vals.pop().expect("geq ∨ has a right operand");
                    let left = vals.pop().expect("geq ∨ has a left operand");
                    vals.push(left || right);
                }
                Op::OffsetK(u, v) => vals.push(offset_k(u, v)),
                Op::Go(u, v) => {
                    if u == v {
                        vals.push(true);
                        continue;
                    }
                    match (u.view(), v.view()) {
                        (_, LevelView::Zero) => vals.push(true),
                        (_, LevelView::Max(v1, v2)) => {
                            ops.push(Op::And);
                            ops.push(Op::Go(u, v2));
                            ops.push(Op::Go(u, v1));
                        }
                        (LevelView::Max(u1, u2), _) => {
                            // go(u1, v) || go(u2, v) || k(u, v)
                            ops.push(Op::Or);
                            push_k(&mut ops, u, v);
                            ops.push(Op::Or);
                            ops.push(Op::Go(u2, v));
                            ops.push(Op::Go(u1, v));
                        }
                        (LevelView::IMax(_, u2), _) => ops.push(Op::Go(u2, v)),
                        (LevelView::Succ(_), LevelView::Succ(_)) => {
                            let mut left = u;
                            let mut right = v;
                            while let (LevelView::Succ(u1), LevelView::Succ(v1)) =
                                (left.view(), right.view())
                            {
                                left = u1;
                                right = v1;
                            }
                            ops.push(Op::Go(left, right));
                        }
                        _ => push_k(&mut ops, u, v),
                    }
                }
            }
        }
        vals.pop().expect("geq produces one answer")
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

    /// Fallible `mkLevelMax'` (Level.lean:516-533): the simplifying max builder.
    ///
    /// The Reference constructor panics if the raw fallback would exceed the packed depth.
    /// Authoritative FrankenLean callers use this form to preserve typed exhaustion instead.
    pub fn try_smart_max(u: Level, v: Level) -> Result<Level, LevelTooDeep> {
        if u == v {
            return Ok(u);
        }
        if u.is_zero() {
            return Ok(v);
        }
        if v.is_zero() {
            return Ok(u);
        }
        if Level::subsumes(&u, &v) {
            return Ok(u);
        }
        if Level::subsumes(&v, &u) {
            return Ok(v);
        }
        if u.get_level_offset() == v.get_level_offset() {
            if u.get_offset() >= v.get_offset() {
                Ok(u)
            } else {
                Ok(v)
            }
        } else {
            Level::max(u, v)
        }
    }

    /// `mkLevelMax'` for callers whose inputs are already known to have depth headroom.
    pub fn smart_max(u: Level, v: Level) -> Level {
        Level::try_smart_max(u, v).expect("smart max inputs have packed depth headroom")
    }

    /// Fallible `mkLevelIMax'` (Level.lean:541-551): the simplifying imax builder.
    pub fn try_smart_imax(u: Level, v: Level) -> Result<Level, LevelTooDeep> {
        if v.is_never_zero() {
            Level::try_smart_max(u, v)
        } else if v.is_zero() || u.is_zero() {
            // Distinct upstream arms (`v.isZero` then `u.isZero`) that both yield `v`.
            Ok(v)
        } else if u == v {
            Ok(u)
        } else {
            Level::imax(u, v)
        }
    }

    /// Fallible kernel `mk_imax` (`kernel/level.cpp`), including its additional
    /// `imax 1 u = u` simplification beyond Lean's library-level `mkLevelIMax'`.
    pub fn try_kernel_imax(u: Level, v: Level) -> Result<Level, LevelTooDeep> {
        if v.is_never_zero() {
            Level::try_smart_max(u, v)
        } else if v.is_zero() || u.is_zero() || u == Level::one() {
            Ok(v)
        } else if u == v {
            Ok(u)
        } else {
            Level::imax(u, v)
        }
    }

    /// `mkLevelIMax'` for callers whose inputs are already known to have depth headroom.
    pub fn smart_imax(u: Level, v: Level) -> Level {
        Level::try_smart_imax(u, v).expect("smart imax inputs have packed depth headroom")
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
        assert_eq!(
            Level::try_smart_max(u.clone(), u.clone()).expect("no depth growth"),
            u
        );
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
        assert_eq!(
            Level::try_smart_imax(u.clone(), Level::zero()).expect("no depth growth"),
            Level::zero()
        );
        assert_eq!(Level::smart_imax(Level::zero(), v.clone()), v);
        assert_eq!(Level::smart_imax(u.clone(), u.clone()), u);
        assert_eq!(
            Level::try_kernel_imax(Level::one(), v.clone()).expect("no depth growth"),
            v
        );
        let sv = v.clone().succ().expect("packs");
        assert_eq!(
            Level::smart_imax(u.clone(), sv.clone()),
            Level::smart_max(u.clone(), sv)
        );
    }

    #[test]
    fn fallible_smart_constructors_report_raw_depth_overflow() {
        let deep_name = Name::str(Name::anonymous(), "deep");
        let boundary = Level {
            node: Some(std::sync::Arc::new(Node::Param(deep_name.clone()))),
            data: LevelData::pack(
                mix_hash(SEED_PARAM, deep_name.hash()),
                MAX_LEVEL_DEPTH,
                false,
                true,
            )
            .expect("the boundary depth itself packs"),
        };
        let other = p("other");
        let expected = LevelTooDeep {
            depth: MAX_LEVEL_DEPTH + 1,
        };

        assert_eq!(
            Level::try_smart_max(boundary.clone(), other.clone()),
            Err(expected)
        );
        assert_eq!(
            Level::try_smart_imax(boundary.clone(), other.clone()),
            Err(expected)
        );
        assert_eq!(Level::try_kernel_imax(boundary, other), Err(expected));
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

    /// Seeded property test for the normalization laws (bead franken_lean-p8a).
    ///
    /// These are laws of the universe algebra, written from the algebra and not read
    /// off `normalize`: if the implementation and the law disagree, the law wins and
    /// the failure is a finding. `imax u 0 ≡ 0` is the load-bearing one — Prop
    /// impredicativity depends on it, and it is the reason `imax` cannot simply be
    /// `max`.
    #[test]
    fn normalization_laws_hold_over_generated_levels() {
        struct Gen(u64);
        impl Gen {
            fn next(&mut self) -> u64 {
                self.0 = self
                    .0
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                self.0
            }
            fn level(&mut self, depth: u32) -> Level {
                if depth == 0 {
                    return match self.next() % 4 {
                        0 => Level::zero(),
                        1 => p("u"),
                        2 => p("v"),
                        _ => Level::mvar(LMVarId(Name::str(Name::anonymous(), "m"))),
                    };
                }
                match self.next() % 5 {
                    0 => self.level(depth - 1).succ().expect("shallow"),
                    1 => Level::max(self.level(depth - 1), self.level(depth - 1)).expect("shallow"),
                    2 => {
                        Level::imax(self.level(depth - 1), self.level(depth - 1)).expect("shallow")
                    }
                    3 => self
                        .level(depth - 1)
                        .add_offset(self.next() as u32 % 3)
                        .expect("shallow"),
                    _ => self.level(0),
                }
            }
        }

        let zero = Level::zero();
        let mut generator = Gen(0x9e37_79b9_7f4a_7c15);
        for round in 0..400 {
            let u = generator.level(3);
            let v = generator.level(3);
            let w = generator.level(2);
            let at = |law: &str| format!("round {round}: {law}");

            // NB: `normalize` is NOT idempotent, and the pin's is not either — see
            // `normalize_is_not_idempotent_and_the_pin_agrees`. Asserting idempotence
            // here, the obvious law for anything called a normal form, would assert
            // something upstream does not hold to.

            // isEquiv is an equivalence relation.
            assert!(u.is_equiv(&u), "{}", at("isEquiv is reflexive"));
            assert_eq!(
                u.is_equiv(&v),
                v.is_equiv(&u),
                "{}",
                at("isEquiv is symmetric")
            );
            if u.is_equiv(&v) && v.is_equiv(&w) {
                assert!(u.is_equiv(&w), "{}", at("isEquiv is transitive"));
            }

            // The impredicativity law: `imax u 0` collapses to `0`, whatever `u` is.
            let imax_zero = Level::imax(u.clone(), zero.clone()).expect("shallow");
            assert!(
                imax_zero.is_equiv(&zero),
                "{}",
                at("imax u 0 ≡ 0 — Prop impredicativity")
            );

            // `imax` above a successor is just `max`: the right side cannot be Prop.
            let succ_v = v.clone().succ().expect("shallow");
            assert!(
                Level::imax(u.clone(), succ_v.clone())
                    .expect("shallow")
                    .is_equiv(&Level::max(u.clone(), succ_v.clone()).expect("shallow")),
                "{}",
                at("imax u (succ v) ≡ max u (succ v)")
            );

            // max is idempotent, commutative and associative, with zero as unit.
            assert!(
                Level::max(u.clone(), u.clone())
                    .expect("shallow")
                    .is_equiv(&u),
                "{}",
                at("max u u ≡ u")
            );
            assert!(
                Level::max(u.clone(), v.clone())
                    .expect("shallow")
                    .is_equiv(&Level::max(v.clone(), u.clone()).expect("shallow")),
                "{}",
                at("max is commutative")
            );
            let left = Level::max(
                Level::max(u.clone(), v.clone()).expect("shallow"),
                w.clone(),
            )
            .expect("shallow");
            let right = Level::max(
                u.clone(),
                Level::max(v.clone(), w.clone()).expect("shallow"),
            )
            .expect("shallow");
            assert!(left.is_equiv(&right), "{}", at("max is associative"));
            assert!(
                Level::max(u.clone(), zero.clone())
                    .expect("shallow")
                    .is_equiv(&u),
                "{}",
                at("max u 0 ≡ u")
            );

            // NB: `succ (max u v)` vs `max (succ u) (succ v)` is deliberately NOT
            // asserted here. The two are semantically equal but `isEquiv` compares
            // NORMAL FORMS, and normalization is not complete for semantic equality
            // — see `is_equiv_compares_normal_forms_not_semantic_equality`, whose
            // counterexample was checked against the pinned Reference.

            // An offset is iterated succ, and normalization preserves that.
            let k = (round % 4) as u32;
            let by_offset = u.clone().add_offset(k).expect("shallow");
            let mut by_succ = u.clone();
            for _ in 0..k {
                by_succ = by_succ.succ().expect("shallow");
            }
            assert!(
                by_offset.is_equiv(&by_succ),
                "{}",
                at("addOffset k ≡ succ^k")
            );

            // The smart constructors agree with the plain ones up to equivalence —
            // they exist to avoid building nodes, not to change meaning.
            assert!(
                Level::smart_max(u.clone(), v.clone())
                    .is_equiv(&Level::max(u.clone(), v.clone()).expect("shallow")),
                "{}",
                at("mkLevelMax' agrees with max")
            );
            assert!(
                Level::smart_imax(u.clone(), v.clone())
                    .is_equiv(&Level::imax(u.clone(), v.clone()).expect("shallow")),
                "{}",
                at("mkLevelIMax' agrees with imax")
            );
        }
    }

    /// `Level.isEquiv` is `u == v || u.normalize == v.normalize` — equality of
    /// NORMAL FORMS, not of meanings. Normalization is incomplete for semantic
    /// equality, so two levels that denote the same universe under every assignment
    /// can still compare unequal.
    ///
    /// This is not our approximation: the counterexample below was run through the
    /// PINNED Reference binary (v4.32.0, commit 8c9756b2), which produces the same
    /// two normal forms and the same `false`:
    ///
    /// ```text
    /// lhs.normalize = max (u + 3) (v + 3)
    /// rhs.normalize = max (max (u + 3) (v + 1)) ((max (u + 2) (v + 2)) + 1)
    /// isEquiv       = false
    /// ```
    ///
    /// `faithful` mode means matching that, incompleteness included. The test exists
    /// so a future "improvement" to normalize that closes this gap is caught as the
    /// fidelity change it is, rather than landing silently.
    ///
    /// Found by the property test above, which asserted succ/max distributivity and
    /// was wrong to.
    #[test]
    fn is_equiv_compares_normal_forms_not_semantic_equality() {
        let u = p("u");
        let v = p("v");

        // Distributivity DOES hold for atoms, which is why the general law looked
        // plausible.
        let simple_lhs = Level::max(u.clone(), v.clone())
            .expect("shallow")
            .succ()
            .expect("shallow");
        let simple_rhs = Level::max(
            u.clone().succ().expect("shallow"),
            v.clone().succ().expect("shallow"),
        )
        .expect("shallow");
        assert!(simple_lhs.is_equiv(&simple_rhs), "atoms distribute");

        // The Reference-checked counterexample: both sides denote max(u,v)+3.
        let left = Level::imax(
            u.clone(),
            Level::max(v.clone(), u.clone())
                .expect("shallow")
                .add_offset(2)
                .expect("shallow"),
        )
        .expect("shallow");
        let right = Level::max(
            Level::max(Level::zero(), u.clone().add_offset(2).expect("shallow")).expect("shallow"),
            v.clone(),
        )
        .expect("shallow");

        let lhs = Level::max(left.clone(), right.clone())
            .expect("shallow")
            .succ()
            .expect("shallow");
        let rhs = Level::max(
            left.succ().expect("shallow"),
            right.succ().expect("shallow"),
        )
        .expect("shallow");

        assert!(
            !lhs.is_equiv(&rhs),
            "normalization is incomplete here and the pin agrees; closing this gap \
             would be a deliberate fidelity change, not a bug fix"
        );
    }

    /// The consumer hazard fln-0uvk was filed for, demonstrated with parameters only
    /// — no metavariable, so this shape occurs in ordinary kernel-checked universes,
    /// not just mid-elaboration.
    ///
    /// Two callers holding the same universe get different answers because one of
    /// them normalized first. Nothing in the workspace does this today (the analysis
    /// on the bead maps every caller), which is why this is a latent hazard rather
    /// than a live bug — but it is the reason `normalize_fixpoint` exists and the
    /// reason no cache key may be taken over `normalize` output.
    #[test]
    fn pre_normalization_changes_an_is_equiv_verdict() {
        let u = p("u");
        let v = p("v");
        // succ(imax v (succ u)) — the non-idempotent class.
        let x = Level::imax(v, u.succ().expect("shallow"))
            .expect("shallow")
            .succ()
            .expect("shallow");
        let y = x.normalize().normalize();

        assert!(!x.is_equiv(&y), "one-pass forms differ, so isEquiv says no");
        assert!(
            x.normalize().is_equiv(&y),
            "after a pre-normalization the very same pair says yes"
        );

        // The fixpoint form is stable under exactly that difference.
        assert_eq!(x.normalize_fixpoint(), y.normalize_fixpoint());
        assert_eq!(
            x.normalize_fixpoint(),
            x.normalize().normalize_fixpoint(),
            "a canonical form cannot depend on how many times the caller normalized"
        );
    }

    /// `normalize_fixpoint` is the true normal form the one-pass function is not.
    ///
    /// The generator deliberately emits `succ^k(imax(a, succ b))`, the only shape
    /// class that is non-idempotent. An earlier version of this search covered 80,000
    /// generated pairs and found zero — because it never built that shape. A search
    /// whose zeros are not validated against a known positive is worth nothing, so
    /// the known counterexample is checked first, here, every run.
    #[test]
    fn normalize_fixpoint_converges_and_is_idempotent() {
        struct Gen(u64);
        impl Gen {
            fn next(&mut self) -> u64 {
                self.0 = self
                    .0
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                self.0
            }
            fn atom(&mut self) -> Level {
                match self.next() % 4 {
                    0 => Level::zero(),
                    1 => p("u"),
                    2 => p("v"),
                    _ => Level::mvar(LMVarId(Name::str(Name::anonymous(), "m"))),
                }
            }
            fn level(&mut self, depth: u32) -> Level {
                if depth == 0 {
                    return self.atom();
                }
                match self.next() % 7 {
                    0 => self.level(depth - 1).succ().expect("shallow"),
                    1 => Level::max(self.level(depth - 1), self.level(depth - 1)).expect("shallow"),
                    2 => {
                        Level::imax(self.level(depth - 1), self.level(depth - 1)).expect("shallow")
                    }
                    3 => Level::imax(self.level(depth - 1), Level::zero()).expect("shallow"),
                    // The non-idempotent class, emitted on purpose.
                    4 => Level::imax(
                        self.level(depth - 1),
                        self.level(depth - 1).succ().expect("shallow"),
                    )
                    .expect("shallow")
                    .succ()
                    .expect("shallow"),
                    5 => self
                        .level(depth - 1)
                        .add_offset((self.next() % 3) as u32)
                        .expect("shallow"),
                    _ => self.atom(),
                }
            }
        }

        // Validate the search before trusting it: the known counterexample must be
        // non-idempotent under `normalize` and stable under `normalize_fixpoint`.
        let known = Level::imax(p("v"), p("u").succ().expect("shallow"))
            .expect("shallow")
            .succ()
            .expect("shallow");
        assert_ne!(
            known.normalize(),
            known.normalize().normalize(),
            "the harness cannot see the known non-idempotent case"
        );
        assert_eq!(
            known.normalize_fixpoint(),
            known.normalize_fixpoint().normalize()
        );

        let mut generator = Gen(0x5eed_0a1b_2c3d_4e5f);
        let mut saw_non_idempotent = 0usize;
        for round in 0..600 {
            let x = generator.level(4);
            let fixed = x.normalize_fixpoint();

            if x.normalize() != x.normalize().normalize() {
                saw_non_idempotent += 1;
            }

            // The fixpoint is a fixpoint.
            assert_eq!(
                fixed.normalize(),
                fixed,
                "round {round}: normalize_fixpoint output is not stable"
            );
            assert_eq!(
                fixed.normalize_fixpoint(),
                fixed,
                "round {round}: normalize_fixpoint is not idempotent"
            );

            // And it is reached regardless of how many times the caller normalized
            // first — the property the one-pass function does not have.
            assert_eq!(
                x.normalize().normalize_fixpoint(),
                fixed,
                "round {round}: pre-normalizing changed the canonical form"
            );
            assert_eq!(
                x.normalize().normalize().normalize_fixpoint(),
                fixed,
                "round {round}: pre-normalizing twice changed the canonical form"
            );

            // Two passes are enough for every shape seen so far; if that ever stops
            // holding, the bound is what keeps it from becoming a hang.
            assert_eq!(
                x.normalize().normalize(),
                fixed,
                "round {round}: the fixpoint took more than two passes"
            );

            // isEquiv agreeing implies the canonical forms agree. The converse does
            // not hold, and must not be asserted: canonical comparison is coarser
            // than the pin's isEquiv, which is exactly the difference this bead is
            // about.
            let y = generator.level(3);
            if x.is_equiv(&y) {
                assert_eq!(
                    fixed,
                    y.normalize_fixpoint(),
                    "round {round}: isEquiv said yes but the canonical forms differ"
                );
            }
        }
        assert!(
            saw_non_idempotent > 0,
            "the generator never produced a non-idempotent level, so this search \
             proved nothing — the same false negative an earlier version shipped"
        );
    }

    /// `Level.normalize` is **not** idempotent, and neither is the pin's.
    ///
    /// Found by the property test above, which asserted idempotence — the obvious law
    /// for anything called a normal form — and was wrong to. The counterexample was
    /// run through the PINNED Reference binary (v4.32.0, commit 8c9756b2), which
    /// produces the same two forms and the same verdict:
    ///
    /// ```text
    /// u             = (imax v (m + 1)) + 1
    /// u.normalize   = (max v (m + 1)) + 1
    /// u.normalize^2 = max (v + 1) (m + 2)
    /// idempotent    = false
    /// ```
    ///
    /// The first pass turns `imax` into `max` — the right side is a `succ`, so it
    /// cannot be zero — but leaves the outer offset outside; the second pass then
    /// distributes it. `faithful` mode means reproducing that, so both steps are
    /// pinned here. Making normalization reach its fixpoint in one pass would be a
    /// deliberate fidelity decision with a Behavior Note, not a tidy-up.
    #[test]
    fn normalize_is_not_idempotent_and_the_pin_agrees() {
        let v = p("v");
        let m = Level::mvar(LMVarId(Name::str(Name::anonymous(), "m")));

        let u = Level::imax(v.clone(), m.clone().succ().expect("shallow"))
            .expect("shallow")
            .succ()
            .expect("shallow");

        // First pass: imax collapses to max, the outer succ stays where it was.
        let once = u.normalize();
        let expected_once = Level::max(v.clone(), m.clone().succ().expect("shallow"))
            .expect("shallow")
            .succ()
            .expect("shallow");
        assert_eq!(once, expected_once, "first pass diverged from the pin");

        // Second pass: the offset distributes into the max arguments.
        let twice = once.normalize();
        let expected_twice = Level::max(
            v.succ().expect("shallow"),
            m.succ().expect("shallow").succ().expect("shallow"),
        )
        .expect("shallow");
        assert_eq!(twice, expected_twice, "second pass diverged from the pin");
        assert_ne!(once, twice, "the pin's normalize is not a fixpoint here");

        // Non-idempotence is one step, not an oscillation.
        assert_eq!(
            twice.normalize(),
            twice,
            "normalization settles after the second pass"
        );
    }

    /// `Level.geq` had no test anywhere in the workspace — found while auditing what
    /// ci/PARITY_LEDGER.txt could honestly claim. It decides "≥ under every parameter
    /// assignment" for KR-604 constructor-field universes, so it is load-bearing for
    /// the kernel even though nothing calls it yet.
    ///
    /// The properties below are stated from the relation's meaning, not read off the
    /// implementation: `u ≥ 0` for every `u`, reflexivity, `succ u ≥ u` strictly one
    /// way, `max` above both arms, and the two cases where a parameter cannot be
    /// ordered against another parameter at all.
    #[test]
    fn geq_orders_universes_by_meaning_not_by_syntax() {
        let zero = Level::zero();
        let u = p("u");
        let v = p("v");

        for level in [
            zero.clone(),
            u.clone(),
            nat(3),
            Level::max(u.clone(), v.clone()).expect("shallow"),
        ] {
            assert!(level.is_geq(&zero), "every universe is at least zero");
            assert!(level.is_geq(&level), "geq is reflexive");
        }

        let succ_u = u.clone().succ().expect("shallow");
        assert!(succ_u.is_geq(&u), "succ u ≥ u");
        assert!(!u.is_geq(&succ_u), "u is not ≥ succ u");
        assert!(!zero.is_geq(&u), "zero is not ≥ a parameter");

        // Distinct parameters are incomparable in both directions: neither dominates
        // under every assignment.
        assert!(!u.is_geq(&v));
        assert!(!v.is_geq(&u));

        // max is above both arms, and dominates a parameter only through an arm.
        let max_uv = Level::max(u.clone(), v.clone()).expect("shallow");
        assert!(max_uv.is_geq(&u));
        assert!(max_uv.is_geq(&v));
        assert!(!u.is_geq(&max_uv));

        // Offsets compose with the base: u+2 ≥ u+1, and not the reverse.
        let u1 = u.clone().add_offset(1).expect("shallow");
        let u2 = u.clone().add_offset(2).expect("shallow");
        assert!(u2.is_geq(&u1));
        assert!(!u1.is_geq(&u2));

        // Explicit levels compare by value, and syntax that normalizes to the same
        // level compares equal in both directions.
        assert!(nat(5).is_geq(&nat(5)));
        assert!(nat(5).is_geq(&nat(4)));
        assert!(!nat(4).is_geq(&nat(5)));
        let max_u_u = Level::max(u.clone(), u.clone()).expect("shallow");
        assert!(max_u_u.is_geq(&u) && u.is_geq(&max_u_u), "max u u ≡ u");
    }

    /// The recursive comparison this type deliberately no longer derives. Kept as a
    /// test-only oracle: on shallow values recursion is safe, so it pins the exact
    /// verdict the iterative predicate must reproduce.
    fn recursive_level_eq(left: &Level, right: &Level) -> bool {
        if left.data != right.data {
            return false;
        }
        if Arc::ptr_eq(left.node_arc(), right.node_arc()) {
            return true;
        }
        match (left.node(), right.node()) {
            (Node::Zero, Node::Zero) => true,
            (Node::Succ(a), Node::Succ(b)) => recursive_level_eq(a, b),
            (Node::Max(a1, a2), Node::Max(b1, b2)) | (Node::IMax(a1, a2), Node::IMax(b1, b2)) => {
                recursive_level_eq(a1, b1) && recursive_level_eq(a2, b2)
            }
            (Node::Param(a), Node::Param(b)) => a == b,
            (Node::MVar(a), Node::MVar(b)) => a == b,
            _ => false,
        }
    }

    /// Every constructor, against every other, in both directions: the iterative
    /// predicate agrees with the recursive oracle on shallow values.
    fn shallow_equality_matrix() -> Vec<Level> {
        let mvar = Level::mvar(LMVarId(Name::str(Name::anonymous(), "m")));
        let other_mvar = Level::mvar(LMVarId(Name::str(Name::anonymous(), "n")));
        let shared = Level::max(p("a"), nat(1)).expect("shallow");
        vec![
            Level::zero(),
            nat(1),
            nat(2),
            p("a"),
            p("b"),
            mvar,
            other_mvar,
            Level::succ(p("a")).expect("shallow"),
            Level::max(p("a"), p("b")).expect("shallow"),
            Level::max(p("b"), p("a")).expect("shallow"),
            Level::imax(p("a"), p("b")).expect("shallow"),
            Level::imax(p("b"), p("a")).expect("shallow"),
            Level::max(p("a"), nat(1)).expect("shallow"),
            shared.clone(),
            shared,
            Level::max(Level::max(p("a"), p("b")).expect("shallow"), nat(3)).expect("shallow"),
        ]
    }

    #[test]
    fn iterative_equality_matches_the_recursive_oracle_on_every_constructor() {
        let values = shallow_equality_matrix();
        for (left_index, left) in values.iter().enumerate() {
            for (right_index, right) in values.iter().enumerate() {
                assert_eq!(
                    left == right,
                    recursive_level_eq(left, right),
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

    /// Independently built deep-but-equal levels agree on every data word, so the
    /// structural arm is reached at every node — the exact shape that overflowed
    /// while the comparison recursed. A 1 MiB worker is far below what one frame
    /// per level would need at this depth.
    #[test]
    fn deep_structural_equality_is_stack_bounded() {
        const DEPTH: usize = 100_000;

        fn deep_succ_over(base: Level, depth: usize) -> Level {
            let mut level = base;
            for _ in 0..depth {
                level = Level::succ(level).expect("depth is inside the 24-bit packing");
            }
            level
        }

        let outcome = std::thread::Builder::new()
            .stack_size(1024 * 1024)
            .spawn(|| {
                let left = deep_succ_over(p("a"), DEPTH);
                let right = deep_succ_over(p("a"), DEPTH);
                assert!(
                    left == right,
                    "independently built deep levels must compare equal"
                );

                // A mismatch buried under the whole chain: the walk must reach it
                // rather than stop at the roots' data words.
                let deep_other = deep_succ_over(p("b"), DEPTH);
                assert!(left != deep_other, "a deep leaf mismatch must be observed");

                // Alternating Max/IMax spines exercise the two-child arms.
                let mut left_spine = Level::zero();
                let mut right_spine = Level::zero();
                for index in 0..DEPTH {
                    let (l, r) = (left_spine.clone(), right_spine.clone());
                    if index.is_multiple_of(2) {
                        left_spine = Level::max(l, p("a")).expect("shallow width");
                        right_spine = Level::max(r, p("a")).expect("shallow width");
                    } else {
                        left_spine = Level::imax(l, p("a")).expect("shallow width");
                        right_spine = Level::imax(r, p("a")).expect("shallow width");
                    }
                }
                assert!(left_spine == right_spine, "deep max/imax spines must agree");
            })
            .expect("spawn bounded-stack Level comparison worker")
            .join();
        assert!(
            outcome.is_ok(),
            "deep Level equality exhausted the bounded worker stack"
        );
    }

    /// The remaining Level predicates used to recurse down `succ` towers
    /// and `max`/`imax` spines. Convert now injects a 400-deep tower;
    /// 24-bit depth is 16M. A 1 MiB worker is far below one frame per node.
    #[test]
    fn deep_level_predicates_are_stack_bounded() {
        const DEPTH: usize = 100_000;

        fn succ_chain(depth: usize) -> Level {
            let mut level = Level::zero();
            for _ in 0..depth {
                level = level.succ().expect("depth is inside the 24-bit packing");
            }
            level
        }

        let outcome = std::thread::Builder::new()
            .stack_size(1024 * 1024)
            .spawn(|| {
                let deep = succ_chain(DEPTH);
                let other = succ_chain(DEPTH);
                assert!(deep.is_explicit(), "succ^k 0 is a numeral");
                assert!(deep.is_never_zero());
                assert!(!deep.is_always_zero());
                assert!(deep.is_not_zero());
                assert!(Level::zero().occurs_in(&deep));
                assert!(!p("a").occurs_in(&deep));
                let normalized = deep.normalize();
                assert_eq!(
                    normalized, deep,
                    "a succ tower over zero is already cheap-normalized"
                );
                assert!(deep.is_equiv(&other));
                assert!(deep.is_geq(&other));
                assert!(deep.norm_lt(&succ_chain(DEPTH + 1)));

                // max-only: normalize flattens Max iteratively. An alternating
                // imax spine still recurses inside normalize (separate hole).
                // Distinct params so go cannot exit on identity.
                let mut left_spine = Level::zero();
                let mut right_spine = Level::zero();
                for _ in 0..DEPTH {
                    left_spine = Level::max(left_spine, p("a")).expect("shallow width");
                    right_spine = Level::max(right_spine, p("b")).expect("shallow width");
                }
                assert!(
                    left_spine.is_geq(&left_spine),
                    "geq of a deep max spine with itself"
                );
                let _ = left_spine.is_geq(&right_spine);
            })
            .expect("spawn bounded-stack Level predicate worker")
            .join();
        assert!(
            outcome.is_ok(),
            "deep Level predicates exhausted the bounded worker stack"
        );
    }
    /// Byte-for-byte `Debug` vectors captured from the recursive implementation
    /// this walk replaces (bead franken_lean-canon-stack-safe-drop-6gy). Rendering
    /// is a compatibility surface: consumers, goldens, and diagnostics read it, so
    /// the stack-safety fix must be invisible in both `{:?}` and `{:#?}`.
    #[test]
    fn debug_rendering_is_byte_identical_to_the_recursive_goldens() {
        let x = || Name::str(Name::anonymous(), "x");
        let values: Vec<(&str, Level)> = vec![
            ("zero", Level::zero()),
            ("succ", Level::zero().succ().expect("small")),
            ("param", Level::param(x())),
            (
                "mvar",
                Level::mvar(LMVarId(Name::num(Name::anonymous(), 4))),
            ),
            (
                "max",
                Level::max(Level::zero(), Level::param(x())).expect("small"),
            ),
            (
                "imax",
                Level::imax(Level::param(x()), Level::zero()).expect("small"),
            ),
            (
                "nested",
                Level::max(
                    Level::zero().succ().expect("small"),
                    Level::imax(Level::param(x()), Level::zero()).expect("small"),
                )
                .expect("small"),
            ),
        ];
        const GOLDENS: [(&str, &str, &str); 7] = [
            (
                "zero",
                "Level { node: Zero, data: LevelData(2221) }",
                concat!(
                    "Level {\n",
                    "    node: Zero,\n",
                    "    data: LevelData(\n",
                    "        2221,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "succ",
                "Level { node: Succ(Level { node: Zero, data: LevelData(2221) }), data: LevelData(1101033050548) }",
                concat!(
                    "Level {\n",
                    "    node: Succ(\n",
                    "        Level {\n",
                    "            node: Zero,\n",
                    "            data: LevelData(\n",
                    "                2221,\n",
                    "            ),\n",
                    "        },\n",
                    "    ),\n",
                    "    data: LevelData(\n",
                    "        1101033050548,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "param",
                "Level { node: Param(Name(Str(StrNode { pre: Name(Anonymous), component: \"x\", hash: 13655884332201764339 }))), data: LevelData(10400061217) }",
                concat!(
                    "Level {\n",
                    "    node: Param(\n",
                    "        Name(\n",
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
                    "    ),\n",
                    "    data: LevelData(\n",
                    "        10400061217,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "mvar",
                "Level { node: MVar(LMVarId(Name(Num(NumNode { pre: Name(Anonymous), component: 4, overflowed: false, hash: 5025098885263514187 })))), data: LevelData(6529228386) }",
                concat!(
                    "Level {\n",
                    "    node: MVar(\n",
                    "        LMVarId(\n",
                    "            Name(\n",
                    "                Num(\n",
                    "                    NumNode {\n",
                    "                        pre: Name(\n",
                    "                            Anonymous,\n",
                    "                        ),\n",
                    "                        component: 4,\n",
                    "                        overflowed: false,\n",
                    "                        hash: 5025098885263514187,\n",
                    "                    },\n",
                    "                ),\n",
                    "            ),\n",
                    "        ),\n",
                    "    ),\n",
                    "    data: LevelData(\n",
                    "        6529228386,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "max",
                "Level { node: Max(Level { node: Zero, data: LevelData(2221) }, Level { node: Param(Name(Str(StrNode { pre: Name(Anonymous), component: \"x\", hash: 13655884332201764339 }))), data: LevelData(10400061217) }), data: LevelData(1111868905434) }",
                concat!(
                    "Level {\n",
                    "    node: Max(\n",
                    "        Level {\n",
                    "            node: Zero,\n",
                    "            data: LevelData(\n",
                    "                2221,\n",
                    "            ),\n",
                    "        },\n",
                    "        Level {\n",
                    "            node: Param(\n",
                    "                Name(\n",
                    "                    Str(\n",
                    "                        StrNode {\n",
                    "                            pre: Name(\n",
                    "                                Anonymous,\n",
                    "                            ),\n",
                    "                            component: \"x\",\n",
                    "                            hash: 13655884332201764339,\n",
                    "                        },\n",
                    "                    ),\n",
                    "                ),\n",
                    "            ),\n",
                    "            data: LevelData(\n",
                    "                10400061217,\n",
                    "            ),\n",
                    "        },\n",
                    "    ),\n",
                    "    data: LevelData(\n",
                    "        1111868905434,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "imax",
                "Level { node: IMax(Level { node: Param(Name(Str(StrNode { pre: Name(Anonymous), component: \"x\", hash: 13655884332201764339 }))), data: LevelData(10400061217) }, Level { node: Zero, data: LevelData(2221) }), data: LevelData(1111737256431) }",
                concat!(
                    "Level {\n",
                    "    node: IMax(\n",
                    "        Level {\n",
                    "            node: Param(\n",
                    "                Name(\n",
                    "                    Str(\n",
                    "                        StrNode {\n",
                    "                            pre: Name(\n",
                    "                                Anonymous,\n",
                    "                            ),\n",
                    "                            component: \"x\",\n",
                    "                            hash: 13655884332201764339,\n",
                    "                        },\n",
                    "                    ),\n",
                    "                ),\n",
                    "            ),\n",
                    "            data: LevelData(\n",
                    "                10400061217,\n",
                    "            ),\n",
                    "        },\n",
                    "        Level {\n",
                    "            node: Zero,\n",
                    "            data: LevelData(\n",
                    "                2221,\n",
                    "            ),\n",
                    "        },\n",
                    "    ),\n",
                    "    data: LevelData(\n",
                    "        1111737256431,\n",
                    "    ),\n",
                    "}",
                ),
            ),
            (
                "nested",
                "Level { node: Max(Level { node: Succ(Level { node: Zero, data: LevelData(2221) }), data: LevelData(1101033050548) }, Level { node: IMax(Level { node: Param(Name(Str(StrNode { pre: Name(Anonymous), component: \"x\", hash: 13655884332201764339 }))), data: LevelData(10400061217) }, Level { node: Zero, data: LevelData(2221) }), data: LevelData(1111737256431) }), data: LevelData(2211360343728) }",
                concat!(
                    "Level {\n",
                    "    node: Max(\n",
                    "        Level {\n",
                    "            node: Succ(\n",
                    "                Level {\n",
                    "                    node: Zero,\n",
                    "                    data: LevelData(\n",
                    "                        2221,\n",
                    "                    ),\n",
                    "                },\n",
                    "            ),\n",
                    "            data: LevelData(\n",
                    "                1101033050548,\n",
                    "            ),\n",
                    "        },\n",
                    "        Level {\n",
                    "            node: IMax(\n",
                    "                Level {\n",
                    "                    node: Param(\n",
                    "                        Name(\n",
                    "                            Str(\n",
                    "                                StrNode {\n",
                    "                                    pre: Name(\n",
                    "                                        Anonymous,\n",
                    "                                    ),\n",
                    "                                    component: \"x\",\n",
                    "                                    hash: 13655884332201764339,\n",
                    "                                },\n",
                    "                            ),\n",
                    "                        ),\n",
                    "                    ),\n",
                    "                    data: LevelData(\n",
                    "                        10400061217,\n",
                    "                    ),\n",
                    "                },\n",
                    "                Level {\n",
                    "                    node: Zero,\n",
                    "                    data: LevelData(\n",
                    "                        2221,\n",
                    "                    ),\n",
                    "                },\n",
                    "            ),\n",
                    "            data: LevelData(\n",
                    "                1111737256431,\n",
                    "            ),\n",
                    "        },\n",
                    "    ),\n",
                    "    data: LevelData(\n",
                    "        2211360343728,\n",
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
    /// in both modes, and every level must still appear in the output.
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
        const PRETTY_DEPTH: usize = 2_000;

        fn succ_chain(depth: usize) -> Level {
            let mut level = Level::zero();
            for _ in 0..depth {
                level = level.succ().expect("depth is inside the 24-bit packing");
            }
            level
        }

        let outcome = std::thread::Builder::new()
            .stack_size(1024 * 1024)
            .spawn(|| {
                let deep = succ_chain(PLAIN_DEPTH);
                let plain = format!("{deep:?}");
                assert_eq!(plain.matches("Succ(").count(), PLAIN_DEPTH);

                let shallower = succ_chain(PRETTY_DEPTH);
                let pretty = format!("{shallower:#?}");
                assert_eq!(pretty.matches("Succ(").count(), PRETTY_DEPTH);
            })
            .expect("spawn bounded-stack Level formatter")
            .join();
        assert!(
            outcome.is_ok(),
            "deep Level formatting exhausted the bounded worker stack"
        );
    }
}
