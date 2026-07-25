//! Total contractual interning for the term store (bead `franken_lean-oh1j`, plan §7.1b).
//!
//! ## Contractual, not opportunistic
//!
//! One stored node per **full structural identity**, including `binder_name`, `decl_name` and every
//! `MData` key and value. Metaprograms observe those fields and faithful `Expr` behaviour demands
//! they round-trip exactly, so they are part of identity rather than noise to be normalised away.
//!
//! The trap is next door in this crate. [`crate::terms::alpha_canonical_digest`] deliberately
//! **strips** `Lam.binder_name`, `ForallE.binder_name` and `LetE.decl_name`, because kernel defeq
//! caches want alpha-varied terms to share reduction work. It is the obvious thing to reach for as
//! an intern key and it is exactly wrong: keying on it collapses `fun x => x` and `fun y => y` into
//! one node, and every metaprogram that reads a binder name then sees whichever spelling happened to
//! be interned first. That is the `overmerge` mutant from `fln-49c`, and it is planted and killed
//! below.
//!
//! The two digests therefore coexist on purpose and are different functions with different jobs:
//! alpha-canonical for the *cache* plane, full-fidelity for the *identity* plane.
//!
//! ## Pointer equality IS structural equality
//!
//! After interning, `Arc::ptr_eq` on two stored nodes holds exactly when they are structurally
//! equal. That is what lets `Expr::equal` collapse to a compare and kernel caches key on identity
//! pairs.
//!
//! The soundness argument is worth stating because it is what makes a hash key safe here. A digest
//! bucket is a *hint*: on a hit the candidate is confirmed with full [`Expr`] equality, so no digest
//! collision can merge two different terms. And that confirmation is cheap by induction —
//! interning is post-order, so a candidate's children are already interned, and `Expr`'s `PartialEq`
//! short-circuits on `Arc::ptr_eq`. Comparing two candidates therefore costs their own fields plus
//! a pointer check per child, not a deep walk.
//!
//! ## Total
//!
//! * **Every shape.** The key builder and the rebuilder both match all twelve `ExprNode` variants
//!   with **no wildcard arm**, so a thirteenth variant is a compile error rather than a silent
//!   fallback. That is the whole of "total" as a completeness property: an interner that is
//!   contractual for the constructors its tests happen to call and opportunistic elsewhere is the
//!   failure mode, and the compiler is the only reliable guard against it.
//! * **Every depth.** The traversal is iterative, on a heap worklist. This crate has the discipline
//!   already — `Expr`'s `Drop`, `Debug` and `PartialEq` are all explicitly stack-safe — and a
//!   recursive interner would overflow on the same inputs those were written for.
//! * **Every size.** A store bounded by how many nodes it holds refuses with a typed FL-INV-07
//!   `Inconclusive`, never a rejection, and the refusal is not cacheable. A term too large to
//!   intern is not a malformed term.

use crate::decl_closure::canonical_name_bytes;
use fln_core::diag::{ResourceReason, StructuralUnit};
use fln_core::expr::{Expr, ExprNode};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::{Inconclusive, InternalFault, Outcome, ResourceUsage};
use fln_hash::canon::{CanonWriter, Canonical};
use fln_hash::domain::{Digest, Domain, DomainHasher};
use std::collections::HashMap;

/// Domain tag for the full-fidelity identity digest.
///
/// Distinct from the alpha-canonical tag on purpose: the two digests must never collide in a shared
/// namespace, because one deliberately discards what the other deliberately keeps.
const INTERN_TAG: &[u8] = b"fln.term-store.intern-identity/1";

/// A stored node's identity. Equal ids mean the same stored node, and after interning that means
/// structurally equal.
///
/// # An id is store-local and schedule-dependent. It must never escape.
///
/// Ids are handed out in **assignment order**, so the same term interned by the same program under
/// a different thread count gets a different number. That is fine for what an id is *for* —
/// answering "is this the same stored node" and keying a store-local memo — and it is a determinism
/// defect (FL-INV-01) the moment an id reaches a digest, a cache key that outlives the store, an
/// artifact, or a diagnostic. Same input closure must give the same artifacts at any thread count,
/// and an id does not.
///
/// This is the same boundary [`crate::terms`] already draws for allocation identity, in the same
/// crate and for the same reason: measurement and memoisation only, never a value that is written
/// down. The interner inverts the *direction* of that relationship — here pointer identity BECOMES
/// the identity — but the escape rule is unchanged.
///
/// So the inner `u32` is **private**, and `Ord` is **deliberately not derived**. Sorting by id is
/// the trap: it yields a schedule-dependent order that looks canonical, which is exactly the
/// "semantically free order not pinned by a registered policy" FL-INV-01 forbids. Code that needs a
/// deterministic order over stored terms must derive it from the terms' own structure.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TermId(u32);

/// How much sharing a store achieved.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct SharingStats {
    /// Nodes presented for interning, counting every visit.
    pub presented: u64,
    /// Nodes newly stored.
    pub stored: u64,
    /// Presentations answered by an existing node.
    pub shared: u64,
    /// Digest-bucket hits that full equality then rejected.
    ///
    /// Recorded rather than ignored because it is the only externally visible sign that the digest
    /// is doing worse than expected. A nonzero value is correct behaviour — the confirmation caught
    /// it — but a growing one means the key is losing discrimination.
    pub bucket_misses: u64,
}

impl SharingStats {
    /// Shared presentations as a fraction of all presentations, or 0 for an empty store.
    pub fn sharing_ratio(self) -> f64 {
        if self.presented == 0 {
            0.0
        } else {
            self.shared as f64 / self.presented as f64
        }
    }
}

/// The largest number of nodes any store can hold, whatever budget a caller asks for.
///
/// This is a property of [`TermId`] rather than a policy. Ids are `u32`, so the node after
/// `u32::MAX` would wrap and **alias two structurally different nodes onto one id** — silently, and
/// in the one direction the whole module exists to prevent. Every entry point clamps its budget to
/// this ceiling and refuses beyond it on the same `ProducedNodes` unit, which is what makes
/// `intern_one`'s `as u32` total rather than merely unlikely to be reached.
///
/// Reaching it needs over 4.29e9 stored nodes, so this closes a latent class rather than a live
/// defect. It is closed anyway because a bead whose title is "total" should not carry a size above
/// which the store starts lying, and because the alternative — trusting the caller's budget to be
/// sane — is the same shape of trust that `intern_bounded` exists to withhold.
pub const MAX_STORED_NODES: u64 = u32::MAX as u64;

/// A bound on how many nodes a store may hold.
///
/// Same law as `fln_syntax::run::LexBudget` and `fln_parse::registry::RegistryBudget`: exceeding it
/// is **inconclusive, never a rejection**. `ProducedNodes` is the honest unit — the store is bounded
/// by how much structure it materialises, not by how much the term denotes, which is
/// `ExpandedWeight`'s job in [`crate::terms`].
///
/// A budget above [`MAX_STORED_NODES`] does not raise the ceiling; it is clamped to it. See
/// [`StoreBudget::effective_max_nodes`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StoreBudget {
    pub max_nodes: u64,
}

impl StoreBudget {
    pub const fn generous() -> StoreBudget {
        StoreBudget { max_nodes: 1 << 24 }
    }

    /// The largest budget that means anything: every node the id space can name.
    ///
    /// This is what a caller who wants "as much as the store can hold" should ask for, and it is
    /// the reason there is no unbounded public entry point. An `intern` that could not refuse would
    /// be the unbounded-growth path item 3 of `franken_lean-oh1j` rules out by name.
    pub const fn representable() -> StoreBudget {
        StoreBudget {
            max_nodes: MAX_STORED_NODES,
        }
    }

    /// The budget actually enforced: what was asked for, clamped to what ids can name.
    pub const fn effective_max_nodes(self) -> u64 {
        if self.max_nodes < MAX_STORED_NODES {
            self.max_nodes
        } else {
            MAX_STORED_NODES
        }
    }
}

/// The interning term store.
#[derive(Debug, Default)]
pub struct Interner {
    /// `TermId` -> the canonical `Expr` for that identity.
    nodes: Vec<Expr>,
    /// Full-fidelity digest -> candidate ids. A bucket is a hint, confirmed by equality.
    buckets: HashMap<Digest, Vec<TermId>>,
    stats: SharingStats,
}

impl Interner {
    pub fn new() -> Interner {
        Interner::default()
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    pub fn stats(&self) -> SharingStats {
        self.stats
    }

    /// The canonical `Expr` for an id.
    pub fn get(&self, id: TermId) -> Option<&Expr> {
        self.nodes.get(id.0 as usize)
    }

    /// Intern `root` and every subterm, returning the canonical root.
    ///
    /// Post-order and iterative. **Private on purpose**: it cannot refuse, so it is only ever
    /// reached through [`Interner::intern_bounded`], which has already established that the store
    /// has room. A public infallible entry point would be exactly the unbounded-growth path
    /// item 3 of `franken_lean-oh1j` rules out, and having one next door to the bounded one is how
    /// a caller ends up on it by accident.
    fn intern(&mut self, root: &Expr) -> Expr {
        let order = post_order(root);
        // Original node pointer -> the id it interned to. Keyed by pointer because the input may
        // already share, and re-interning a shared subterm must not re-walk it.
        let mut done: HashMap<*const ExprNode, TermId> = HashMap::with_capacity(order.len());
        let mut last = TermId(0);
        for expr in &order {
            last = self.intern_one(expr, &done);
            done.insert(node_ptr(expr), last);
        }
        self.get(last)
            .cloned()
            // Reached only for an empty order, which `post_order` cannot produce: it always visits
            // the root. Cloning the input is the honest answer rather than a panic.
            .unwrap_or_else(|| root.clone())
    }

    /// Intern under a budget. Exceeding it is `Inconclusive`, never a rejection, and the store is
    /// left **untouched** so a caller can retry with a larger allowance.
    ///
    /// The enforced limit is [`StoreBudget::effective_max_nodes`], not the raw request: a budget
    /// above [`MAX_STORED_NODES`] is clamped, so asking for more than ids can name yields a typed
    /// refusal rather than a truncated id. `allowed` in the reported usage is the limit actually
    /// applied, so a caller that asked for more can see that it was not granted.
    ///
    /// The bound is on the **store**, not on the traversal, and the difference is worth knowing
    /// before treating this as a cheap doorman: `post_order` runs first and materialises one entry
    /// per distinct node, so a hostile input still pays a full distinct-node walk before being
    /// declined. That is the honest reading of `ProducedNodes` — it names what the store holds — and
    /// [`crate::terms::expanded_weight`] is the preflight for the denoted-size axis.
    pub fn intern_bounded(&mut self, root: &Expr, budget: StoreBudget) -> Outcome<Expr> {
        let order = post_order(root);
        // Checked before anything is stored: the point of a size bound is to decline without
        // materialising the structure it is declining.
        let allowed = budget.effective_max_nodes();
        let projected = self.nodes.len() as u64 + order.len() as u64;
        if projected > allowed {
            return Outcome::Inconclusive(Inconclusive::resource(ResourceUsage {
                reason: ResourceReason::StructuralBudget {
                    unit: StructuralUnit::ProducedNodes,
                },
                allowed,
                observed: projected,
            }));
        }
        Outcome::Complete(self.intern(root))
    }

    /// Intern one node whose children are already interned.
    fn intern_one(&mut self, expr: &Expr, done: &HashMap<*const ExprNode, TermId>) -> TermId {
        self.stats.presented += 1;
        let rebuilt = rebuild(expr, done, &self.nodes);
        // Digested from the ORIGINAL node, not from `rebuilt`, and the two are provably the same
        // digest: `rebuild` carries every own field through unchanged, and children contribute only
        // their id, which is the same id whichever of the two you ask. The difference is cost.
        // `done` is keyed by the original child's pointer, so digesting `rebuilt` — whose non-leaf
        // children are freshly allocated canonical forms — missed `done` on every non-leaf child and
        // fell back to a linear scan of the whole store. That made interning an N-node term into an
        // S-node store cost O(N*S) pointer comparisons, so a single 1e6-node term was ~5e11
        // comparisons: a budget that says "yes" at 1<<24 nodes and then appears to hang. Digesting
        // the original makes every child lookup a hash hit.
        let digest = identity_digest(expr, done);

        if let Some(candidates) = self.buckets.get(&digest) {
            for id in candidates {
                if let Some(existing) = self.nodes.get(id.0 as usize) {
                    // Confirmation, not trust: a digest bucket is a hint. `Expr`'s `PartialEq`
                    // short-circuits on `Arc::ptr_eq`, so with children already interned this costs
                    // the node's own fields plus one pointer check per child.
                    if *existing == rebuilt {
                        self.stats.shared += 1;
                        return *id;
                    }
                    self.stats.bucket_misses += 1;
                }
            }
        }

        // Total, not merely lucky: `intern_bounded` has already refused anything that would push
        // `nodes.len()` past `MAX_STORED_NODES`, which is `u32::MAX`, so this cast cannot wrap. The
        // assertion states the precondition rather than trusting the reader to reconstruct it.
        debug_assert!(
            self.nodes.len() as u64 <= MAX_STORED_NODES,
            "intern_bounded must refuse before an id can wrap"
        );
        let id = TermId(self.nodes.len() as u32);
        self.nodes.push(rebuilt);
        self.buckets.entry(digest).or_default().push(id);
        self.stats.stored += 1;
        id
    }
}

/// One term store shared by many threads.
///
/// # The concurrency shape, and why it is this one (bead `franken_lean-oh1j`, item 5)
///
/// The choice was between ONE SHARED STORE behind a lock and PER-THREAD STORES with a deterministic
/// merge. The second is the heavier machine, and its single advantage is that it can assign
/// [`TermId`]s in a registered order, making them stable across thread counts.
///
/// **That advantage buys nothing here, because an id is not allowed to be observed in the first
/// place.** An id is a store-local memo handle that never reaches a digest, an artifact or a
/// diagnostic — the same boundary `terms.rs` already draws for allocation identity, now enforced by
/// a private field rather than by a doc comment. Stabilising a value that must not escape is work
/// spent making an unobservable thing reproducible. So: one shared store, and the id space stays
/// schedule-dependent *by declaration* rather than by accident.
///
/// **What that leaves is a real FL-INV-01 claim, and it is exactly this.** At any thread count, for
/// the same multiset of interned terms:
///
/// * every term's canonical form is the same term, structurally;
/// * the set of stored nodes is the same set;
/// * `presented`, `stored` and `shared` are the same numbers — dedup is by structural identity, so
///   which thread arrives first changes who pays for a node, never how many exist.
///
/// **What is schedule-dependent, stated so nobody builds on it**: [`TermId`] values, the
/// `identity_digest` bytes that are computed from them, and `bucket_misses` — which depends on the
/// order candidates were added to a bucket, and is zero unless the digest genuinely collides.
///
/// This is a correctness-shaped store, not a throughput-shaped one: one lock serialises interning,
/// and sharding it is a later, profile-driven change with these tests already in place to hold it
/// honest. Correctness outranks speed, and a sharded store whose shards intern the same term twice
/// would break the interning invariant this module exists to provide.
#[derive(Debug, Default)]
pub struct SharedInterner {
    inner: std::sync::Mutex<Interner>,
}

impl SharedInterner {
    pub fn new() -> SharedInterner {
        SharedInterner::default()
    }

    /// Intern under a budget, from any thread. See [`Interner::intern_bounded`].
    ///
    /// A poisoned lock is an [`Outcome::InternalFault`], not an `Inconclusive` and not a panic. It
    /// means another thread panicked while holding the store, so an invariant already broke; that is
    /// a different claim from "a budget ran out", and FL-INV-07 says the two must not be spelled the
    /// same. Unwrapping the lock would re-raise the original panic in a thread that did nothing
    /// wrong, and would lose which invariant it was.
    pub fn intern_bounded(&self, root: &Expr, budget: StoreBudget) -> Outcome<Expr> {
        match self.inner.lock() {
            Ok(mut store) => store.intern_bounded(root, budget),
            Err(_) => Outcome::InternalFault(InternalFault::new(
                "FL-INV-07",
                "the shared term store's lock is poisoned: a thread panicked while interning",
            )),
        }
    }

    /// The store's sharing statistics, or `None` if the lock is poisoned.
    ///
    /// `None` rather than a default: a poisoned store has no statistics, and zeroes would read as
    /// "nothing was interned".
    pub fn stats(&self) -> Option<SharingStats> {
        self.inner.lock().ok().map(|store| store.stats())
    }

    /// How many nodes the store holds, or `None` if the lock is poisoned.
    pub fn len(&self) -> Option<usize> {
        self.inner.lock().ok().map(|store| store.len())
    }

    pub fn is_empty(&self) -> Option<bool> {
        self.inner.lock().ok().map(|store| store.is_empty())
    }
}

/// Pointer identity of a node's allocation — the same accessor `terms.rs` uses, since `Expr`'s
/// `Arc` is private to `fln-core`.
fn node_ptr(expr: &Expr) -> *const ExprNode {
    std::ptr::from_ref(expr.node())
}

/// Distinct nodes of `root` in post-order, iteratively.
///
/// Distinct by pointer, so an input that already shares is walked once per stored node rather than
/// once per path — which is what keeps a DAG from being traversed exponentially.
fn post_order(root: &Expr) -> Vec<Expr> {
    enum Step {
        Enter(Expr),
        Exit(Expr),
    }
    let mut order: Vec<Expr> = Vec::new();
    let mut seen: HashMap<*const ExprNode, ()> = HashMap::new();
    let mut stack = vec![Step::Enter(root.clone())];
    while let Some(step) = stack.pop() {
        match step {
            Step::Enter(expr) => {
                if seen.insert(node_ptr(&expr), ()).is_some() {
                    continue;
                }
                let kids = children_of(&expr);
                stack.push(Step::Exit(expr));
                for child in kids.into_iter().rev() {
                    stack.push(Step::Enter(child));
                }
            }
            Step::Exit(expr) => order.push(expr),
        }
    }
    order
}

/// The child `Expr`s of a node.
///
/// **No wildcard arm.** A thirteenth `ExprNode` variant is a compile error here, which is the only
/// reliable guard against an interner that is total for the shapes its author thought of.
fn children_of(expr: &Expr) -> Vec<Expr> {
    match expr.node() {
        ExprNode::BVar { .. }
        | ExprNode::FVar { .. }
        | ExprNode::MVar { .. }
        | ExprNode::Sort { .. }
        | ExprNode::Const { .. }
        | ExprNode::Lit { .. } => Vec::new(),
        ExprNode::App { f, a } => vec![f.clone(), a.clone()],
        ExprNode::Lam {
            binder_type, body, ..
        } => vec![binder_type.clone(), body.clone()],
        ExprNode::ForallE {
            binder_type, body, ..
        } => vec![binder_type.clone(), body.clone()],
        ExprNode::LetE {
            type_, value, body, ..
        } => vec![type_.clone(), value.clone(), body.clone()],
        ExprNode::MData { expr, .. } => vec![expr.clone()],
        ExprNode::Proj { expr, .. } => vec![expr.clone()],
    }
}

/// Rebuild a node with its children replaced by their canonical forms.
///
/// **No wildcard arm**, for the same reason as [`children_of`]. Every own field is carried through
/// unchanged — `binder_name`, `decl_name`, `MData`, `binder_info`, `non_dep`, the literals, the
/// levels, the de Bruijn indices — because they are part of identity here.
fn rebuild(expr: &Expr, done: &HashMap<*const ExprNode, TermId>, nodes: &[Expr]) -> Expr {
    let canonical = |child: &Expr| -> Expr {
        done.get(&node_ptr(child))
            .and_then(|id| nodes.get(id.0 as usize))
            .cloned()
            // A child not yet interned cannot happen in post-order; using the child as-is is the
            // total answer rather than a panic, and the interning invariant test would catch it.
            .unwrap_or_else(|| child.clone())
    };
    match expr.node() {
        ExprNode::BVar { .. }
        | ExprNode::FVar { .. }
        | ExprNode::MVar { .. }
        | ExprNode::Sort { .. }
        | ExprNode::Const { .. }
        | ExprNode::Lit { .. } => expr.clone(),
        ExprNode::App { f, a } => Expr::app(canonical(f), canonical(a)),
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Expr::lam(
            binder_name.clone(),
            canonical(binder_type),
            canonical(body),
            *binder_info,
        ),
        ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Expr::forall_e(
            binder_name.clone(),
            canonical(binder_type),
            canonical(body),
            *binder_info,
        ),
        ExprNode::LetE {
            decl_name,
            type_,
            value,
            body,
            non_dep,
        } => Expr::let_e(
            decl_name.clone(),
            canonical(type_),
            canonical(value),
            canonical(body),
            *non_dep,
        ),
        ExprNode::MData { data, expr: inner } => Expr::mdata(data.clone(), canonical(inner)),
        ExprNode::Proj {
            struct_name,
            idx,
            expr: inner,
        } => Expr::proj(struct_name.clone(), *idx, canonical(inner)),
    }
}

/// The full-fidelity identity digest of one node, over its variant, its own fields, and its
/// children's **ids**.
///
/// Shallow by construction: children contribute their id rather than their structure, so the digest
/// is O(own fields) per node and the whole store is digested in one post-order pass.
///
/// # This is a bucket key, NOT a content address, and the difference is load-bearing
///
/// Because children contribute their **id**, and ids are assignment-ordered ([`TermId`]), this
/// digest is a function of the store's history as well as of the term. The same term digests
/// differently in two stores, and differently under two thread counts. Within one store it is
/// perfectly well defined — structurally equal nodes have structurally equal children, hence the
/// same canonical children, hence the same ids, hence the same digest — which is all a bucket key
/// needs.
///
/// It is private for that reason and must stay private. It is the obvious thing to reach for as a
/// content address for a term, and it would be silently wrong: schedule-dependent bytes in an
/// artifact. `fln_hash`'s declaration digests and [`crate::terms::alpha_canonical_digest`] are
/// content addresses; this is not. That makes three digests in this crate's orbit with three
/// different jobs, which is why each one says which it is.
///
/// **No wildcard arm.** And unlike the alpha-canonical digest, every binder name and every `MData`
/// entry is fed in — that difference is the entire distinction between the identity plane and the
/// cache plane.
///
/// `expr` must be a node from the traversal, not a rebuilt one, so that `done` covers its children:
/// see the note at the call site for why the two produce the same digest and why only one of them
/// is affordable.
/// Feed a [`Name`] into a digest by its **structural** encoding, length-prefixed.
///
/// Not `to_display_string`, and the difference is the one `franken_lean-f6br` was filed over.
/// `Name::to_display_string` joins components with `.` **without escaping** and renders a numeric
/// component and a string component identically, so `Name::num(a, 5)` and `Name::str(a, "5")`
/// produce the same text, and a single component spelled `a.b` is indistinguishable from the two
/// components `a` then `b`. The anonymous name renders as the literal `[anonymous]`, which a string
/// component spelled that way collides with too. That is precisely how the census witness stopped
/// discriminating, and it was fixed there by moving to this encoding.
///
/// Here the consequence was **not** a soundness hole, and that is worth stating so the fix is not
/// mistaken for a bug repair: a digest is a bucket hint confirmed by full [`Expr`] equality, so
/// colliding names cost a `bucket_misses` and can never overmerge. But `bucket_misses` is the one
/// statistic that exists to reveal a key losing discrimination, and feeding it a known-lossy
/// encoding blinds the instrument to the thing it measures. Length-prefixing keeps the stream
/// self-delimiting, so the trailing NUL separators the display form needed are gone.
fn update_name(hasher: &mut DomainHasher, name: &Name) {
    let encoded = canonical_name_bytes(name);
    hasher.update(&(encoded.len() as u64).to_le_bytes());
    hasher.update(&encoded);
}

/// Feed a [`Level`] into a digest by its **canonical** encoding, length-prefixed.
///
/// # Finishing `bf9ef450` in its own function
///
/// That commit replaced `Name::to_display_string` with the structural encoding above, and left
/// three sibling call sites in [`identity_digest`] feeding `format!("{:?}")` — `Sort`'s level,
/// `Const`'s level list, and the `FVar`/`MVar` ids. The correct encoder was already reachable and
/// already used one line away. Keying an identity on a RENDERER is the defect `franken_lean-f6br`
/// and `bf9ef450` were both filed over; it was fixed here for names and not for levels.
///
/// # This one was latent, not active, and the difference is the whole point
///
/// `Level`'s `Debug` is a hand-written stack-safe copy of the DERIVED rendering, so it is
/// structural and tagged, and `Name`'s `Debug` is structural too. No two distinct levels collide
/// today — unlike `to_display_string`, where the collision was real and demonstrable. So nothing
/// was broken and no digest was wrong.
///
/// What was wrong is that the correctness rested on an ACCIDENT nothing pinned, inside a function
/// whose entire subject is identity:
///
/// * `Level`'s own doc says its `Debug` is "byte-identical to the derived rendering". A field
///   added, renamed or reordered in `Level` or its `Node` silently moves every digest preimage.
///   Nothing would catch it: a digest here is a bucket hint confirmed by full [`Expr`] equality, so
///   every test stays green while `bucket_misses` quietly changes meaning.
/// * The rendering includes `Level`'s packed `data` word — a CACHED hash seed, depth and flags —
///   so the identity preimage depended on a cache rather than on the level's structure alone.
///
/// [`Canonical`](fln_hash::canon::Canonical) for `Level` already existed in `fln-hash`, tagged per
/// variant and iterative for stack safety. Using it makes the encoding a contract rather than a
/// coincidence, and drops a per-node `String` allocation on the way.
fn update_level(hasher: &mut DomainHasher, level: &Level) {
    let mut writer = CanonWriter::new();
    level.write_body(&mut writer);
    let encoded = writer.into_bytes();
    hasher.update(&(encoded.len() as u64).to_le_bytes());
    hasher.update(&encoded);
}

fn identity_digest(expr: &Expr, done: &HashMap<*const ExprNode, TermId>) -> Digest {
    let mut hasher = DomainHasher::new(Domain::DeclContent);
    hasher.update(INTERN_TAG);
    hasher.update(&[0]);

    // A child's contribution is the id of its canonical form, in O(1).
    //
    // The lookup is total by construction and the sentinel is unreachable: `post_order` pushes
    // every child before its parent's `Exit`, so by the time a node is digested each of its children
    // has been interned and recorded in `done`. It is a sentinel rather than a panic because an
    // unreachable branch that panics is still a panic (FL-INV-07: panics are invariant failures,
    // never diagnostics), and because the failure mode if it ever did fire is benign in the one
    // direction that matters: two nodes sharing a sentinel collide in a digest BUCKET, and a bucket
    // is a hint confirmed by full `Expr` equality. It could cost a bucket miss. It could never
    // overmerge.
    let child_id = |child: &Expr| {
        done.get(&node_ptr(child))
            .copied()
            .unwrap_or(TermId(u32::MAX))
            .0
    };

    match expr.node() {
        ExprNode::BVar { idx } => {
            hasher.update(&[1]);
            hasher.update(&idx.to_le_bytes());
        }
        // `FVarId`, `MVarId` and `LMVarId` are all newtypes over `Name`, so their identity IS a
        // name's and goes through the same structural encoding rather than through the derived
        // `Debug` of the wrapper.
        ExprNode::FVar { id } => {
            hasher.update(&[2]);
            update_name(&mut hasher, &id.0);
        }
        ExprNode::MVar { id } => {
            hasher.update(&[3]);
            update_name(&mut hasher, &id.0);
        }
        ExprNode::Sort { level } => {
            hasher.update(&[4]);
            update_level(&mut hasher, level);
        }
        ExprNode::Const { name, levels } => {
            hasher.update(&[5]);
            update_name(&mut hasher, name);
            hasher.update(&(levels.len() as u64).to_le_bytes());
            for level in levels {
                // No NUL separator: `update_level` length-prefixes, so the stream is
                // self-delimiting and a separator would be a second, weaker mechanism.
                update_level(&mut hasher, level);
            }
        }
        ExprNode::App { f, a } => {
            hasher.update(&[6]);
            hasher.update(&child_id(f).to_le_bytes());
            hasher.update(&child_id(a).to_le_bytes());
        }
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            hasher.update(&[7]);
            // KEPT, unlike the alpha-canonical digest. These bytes are the difference between
            // contractual interning and overmerge.
            update_name(&mut hasher, binder_name);
            hasher.update(&child_id(binder_type).to_le_bytes());
            hasher.update(&child_id(body).to_le_bytes());
            hasher.update(&[*binder_info as u8]);
        }
        ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            hasher.update(&[8]);
            update_name(&mut hasher, binder_name);
            hasher.update(&child_id(binder_type).to_le_bytes());
            hasher.update(&child_id(body).to_le_bytes());
            hasher.update(&[*binder_info as u8]);
        }
        ExprNode::LetE {
            decl_name,
            type_,
            value,
            body,
            non_dep,
        } => {
            hasher.update(&[9]);
            update_name(&mut hasher, decl_name);
            hasher.update(&child_id(type_).to_le_bytes());
            hasher.update(&child_id(value).to_le_bytes());
            hasher.update(&child_id(body).to_le_bytes());
            hasher.update(&[u8::from(*non_dep)]);
        }
        ExprNode::Lit { literal } => {
            hasher.update(&[10]);
            hasher.update(format!("{literal:?}").as_bytes());
        }
        ExprNode::MData { data, expr: inner } => {
            hasher.update(&[11]);
            // KEPT in full: metaprograms read mdata, so two nodes differing only in it are
            // different identities.
            hasher.update(format!("{data:?}").as_bytes());
            hasher.update(&[0]);
            hasher.update(&child_id(inner).to_le_bytes());
        }
        ExprNode::Proj {
            struct_name,
            idx,
            expr: inner,
        } => {
            hasher.update(&[12]);
            update_name(&mut hasher, struct_name);
            hasher.update(&idx.to_le_bytes());
            hasher.update(&child_id(inner).to_le_bytes());
        }
    }
    hasher.finalize()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::terms::alpha_canonical_digest;
    use fln_core::expr::{BinderInfo, Literal, NatLit};
    use fln_core::level::Level;
    use fln_core::name::Name;
    use fln_core::options::{DataValue, KVMap};

    fn name(text: &str) -> Name {
        Name::str(Name::anonymous(), text)
    }

    fn bvar(idx: u32) -> Expr {
        Expr::bvar(idx).expect("a small index is representable")
    }

    /// One `Expr` of **every** variant, so the invariant tests cover the whole enum rather than the
    /// constructors that happened to come to mind. The count is asserted against `VARIANTS` below,
    /// which is what keeps this list honest when the enum grows.
    fn one_of_each() -> Vec<(&'static str, Expr)> {
        vec![
            ("BVar", bvar(0)),
            ("Sort", Expr::sort(Level::zero())),
            ("Const", Expr::const_(name("Nat"), Vec::new())),
            ("Lit", Expr::lit(Literal::Nat(NatLit::from_u64(7)))),
            ("App", Expr::app(bvar(0), bvar(1))),
            (
                "Lam",
                Expr::lam(
                    name("x"),
                    Expr::sort(Level::zero()),
                    bvar(0),
                    BinderInfo::Default,
                ),
            ),
            (
                "ForallE",
                Expr::forall_e(
                    name("y"),
                    Expr::sort(Level::zero()),
                    bvar(0),
                    BinderInfo::Default,
                ),
            ),
            (
                "LetE",
                Expr::let_e(
                    name("z"),
                    Expr::sort(Level::zero()),
                    bvar(0),
                    bvar(1),
                    false,
                ),
            ),
            ("MData", Expr::mdata(KVMap::default(), bvar(0))),
            ("Proj", Expr::proj(name("S"), 1, bvar(0))),
        ]
    }

    /// The variants `one_of_each` does not build, and why. `FVar` and `MVar` need id types this
    /// module has no constructor for; they are covered by the exhaustive `match` arms rather than by
    /// a fixture, and the compiler is the guard there.
    const UNBUILT_VARIANTS: usize = 2;
    const VARIANTS: usize = 12;

    /// **THE INTERNING INVARIANT: structural equality implies pointer equality.** Over every
    /// variant, and over every construction path — a term built twice independently must intern to
    /// the same stored node.
    #[test]
    fn structural_equality_implies_pointer_equality_for_every_variant() {
        assert_eq!(
            one_of_each().len() + UNBUILT_VARIANTS,
            VARIANTS,
            "the fixture must cover every ExprNode variant it can construct; if the enum grew, this \
             count is the reminder"
        );

        let mut interner = Interner::new();
        for (label, expr) in one_of_each() {
            // Build the SAME term a second time, independently, so nothing is shared by accident.
            let (_, twin) = one_of_each()
                .into_iter()
                .find(|(other, _)| *other == label)
                .expect("the fixture is stable");

            assert_eq!(expr, twin, "{label}: the two builds are structurally equal");

            let first = interner.intern(&expr);
            let second = interner.intern(&twin);

            assert_eq!(first, second, "{label}: interned forms are equal");
            assert_eq!(
                node_ptr(&first),
                node_ptr(&second),
                "{label}: structurally equal terms MUST intern to the same node. Pointer equality \
                 being structural equality is what lets Expr::equal collapse to a compare."
            );
        }
    }

    /// **The identity digest itself distinguishes binder names**, asserted directly rather than
    /// through interning.
    ///
    /// This test exists because two plants taught me my suite had a hole. Dropping the binder name
    /// from the digest did NOT fail any test, and skipping the equality confirmation on a bucket hit
    /// did not either — because the two are independent safety mechanisms and every fixture was
    /// covered by whichever one remained. Weak digest plus present confirmation still separates the
    /// terms; strong digest plus absent confirmation also does. Only removing BOTH merges them, and
    /// no single-mutant plant could see that.
    ///
    /// So the digest's fidelity is now pinned on its own, here.
    #[test]
    fn the_identity_digest_distinguishes_terms_the_alpha_digest_merges() {
        let done = HashMap::new();
        let unit = Expr::sort(Level::zero());
        let fun_x = Expr::lam(name("x"), unit.clone(), bvar(0), BinderInfo::Default);
        let fun_y = Expr::lam(name("y"), unit, bvar(0), BinderInfo::Default);

        // The premise: the CACHE-plane digest deliberately merges them.
        assert_eq!(
            alpha_canonical_digest(&fun_x),
            alpha_canonical_digest(&fun_y),
            "the fixture must be alpha-equivalent"
        );
        // The law: the IDENTITY-plane digest must not.
        assert_ne!(
            identity_digest(&fun_x, &done),
            identity_digest(&fun_y, &done),
            "the identity digest must feed the binder name in. Keying on the alpha-canonical digest \
             is the `overmerge` mutant, and this is the assertion that catches it at the key rather \
             than relying on the equality confirmation to clean up afterwards."
        );

        // The same for LetE's decl_name and for mdata, the other two the alpha digest strips or that
        // an interner might treat as annotations.
        let let_a = Expr::let_e(
            name("a"),
            Expr::sort(Level::zero()),
            bvar(0),
            bvar(1),
            false,
        );
        let let_b = Expr::let_e(
            name("b"),
            Expr::sort(Level::zero()),
            bvar(0),
            bvar(1),
            false,
        );
        assert_ne!(
            identity_digest(&let_a, &done),
            identity_digest(&let_b, &done),
            "LetE.decl_name is part of identity"
        );
        let bare = Expr::mdata(KVMap::default(), bvar(0));
        let tagged = Expr::mdata(
            KVMap::from_entries(vec![(name("k"), DataValue::OfBool(true))]),
            bvar(0),
        );
        assert_ne!(
            identity_digest(&bare, &done),
            identity_digest(&tagged, &done),
            "MData is part of identity"
        );
    }

    /// **What this suite does NOT establish**, recorded because two plants failed to fail and the
    /// reason is not a defect but a limit.
    ///
    /// The equality confirmation on a bucket hit is **defence in depth against a digest collision**.
    /// Its necessity is not observable with a real hash: to show that removing it merges two
    /// different terms, I would need two structurally different terms whose full-fidelity digests
    /// collide, and I cannot manufacture one. So skipping the confirmation passes every test here.
    ///
    /// That is graded honestly rather than presented as covered: the confirmation is justified by
    /// the argument that a digest bucket is a hint, not by a measurement. What IS pinned is the
    /// digest's own fidelity, in the test above — so the mechanism this suite actually verifies is
    /// the key, and the confirmation is belt to its braces.
    ///
    /// The test asserts the shape of that claim so a reader meets it here rather than in a commit
    /// message: a bucket hit that fails confirmation is *counted*, and on every fixture in this
    /// module that count is zero, which is exactly why the confirmation is untested.
    #[test]
    fn the_equality_confirmation_is_defence_in_depth_and_is_not_measured_here() {
        let mut interner = Interner::new();
        for (_, expr) in one_of_each() {
            interner.intern(&expr);
        }
        assert_eq!(
            interner.stats().bucket_misses,
            0,
            "no fixture in this module produces a digest collision, so the confirmation step never \
             fires. Its necessity is therefore argued, not measured — see this test's doc comment."
        );
    }

    /// **MUTANT `overmerge`.** Keying on the alpha-canonical digest collapses terms that differ only
    /// in a binder name — the mistake sitting one module away.
    ///
    /// The two terms have the SAME alpha-canonical digest by design and MUST still intern separately,
    /// because metaprograms read binder names and faithful `Expr` behaviour demands they round-trip.
    #[test]
    fn mutant_overmerge_terms_differing_only_in_a_binder_name_stay_distinct() {
        let unit = Expr::sort(Level::zero());
        let fun_x = Expr::lam(name("x"), unit.clone(), bvar(0), BinderInfo::Default);
        let fun_y = Expr::lam(name("y"), unit, bvar(0), BinderInfo::Default);

        // The premise: they ARE alpha-equivalent, so the cache-plane digest agrees.
        assert_eq!(
            alpha_canonical_digest(&fun_x),
            alpha_canonical_digest(&fun_y),
            "the fixture must be alpha-equivalent, or this proves nothing about overmerge"
        );
        // And they are NOT structurally equal, which is what identity must respect.
        assert_ne!(fun_x, fun_y);

        let mut interner = Interner::new();
        let a = interner.intern(&fun_x);
        let b = interner.intern(&fun_y);
        assert_ne!(
            node_ptr(&a),
            node_ptr(&b),
            "keying on the alpha-canonical digest would merge these. A metaprogram reading the \
             binder name would then see whichever spelling interned first."
        );
        // Both spellings survive intact, which is the round-trip the contract promises.
        assert_eq!(a, fun_x);
        assert_eq!(b, fun_y);
    }

    /// The same law for `MData`, which the alpha digest keeps but which an interner might normalise
    /// away as "just annotations".
    #[test]
    fn mutant_overmerge_terms_differing_only_in_mdata_stay_distinct() {
        let annotated = KVMap::from_entries(vec![(name("k"), DataValue::OfBool(true))]);
        let bare = Expr::mdata(KVMap::default(), bvar(0));
        let with_data = Expr::mdata(annotated, bvar(0));

        assert_ne!(bare, with_data);
        let mut interner = Interner::new();
        let a = interner.intern(&bare);
        let b = interner.intern(&with_data);
        assert_ne!(
            node_ptr(&a),
            node_ptr(&b),
            "mdata is part of identity: metaprograms read it"
        );
    }

    /// **MUTANT `missed-intern`.** Every subterm is interned, not just the root.
    ///
    /// A shallow interner returns a canonical root whose children are the originals, so pointer
    /// equality holds at the top and fails one level down — and every kernel cache keyed on identity
    /// pairs then misses.
    #[test]
    fn mutant_missed_intern_every_subterm_is_canonical() {
        let shared = Expr::app(bvar(0), bvar(1));
        let left = Expr::app(shared.clone(), bvar(2));
        let right = Expr::app(shared.clone(), bvar(3));
        let root = Expr::app(left, right);

        let mut interner = Interner::new();
        let canonical = interner.intern(&root);

        // Walk the interned term and require every node to be one the store holds.
        let mut stack = vec![canonical.clone()];
        let mut checked = 0usize;
        while let Some(expr) = stack.pop() {
            let found = (0..interner.len())
                .filter_map(|index| interner.get(TermId(index as u32)))
                .any(|stored| node_ptr(stored) == node_ptr(&expr));
            assert!(
                found,
                "a subterm of the interned root is not itself a stored node: {expr:?}"
            );
            checked += 1;
            stack.extend(children_of(&expr));
        }
        assert!(checked >= 5, "only {checked} subterms walked");
    }

    /// **MUTANT `sharing-loss`.** Two **independently built** equal subterms collapse to one stored
    /// node.
    ///
    /// Independently built on purpose, and my first fixture got this wrong in a way worth recording:
    /// I cloned one `Expr` into both positions, which shares the same `Arc` already, so `post_order`
    /// deduplicated it by pointer and there was nothing left for interning to share. The statistics
    /// said `shared: 0` and were right. Sharing that the *input* already has is not sharing the
    /// *store* provided, and only the second is what this mutant is about.
    #[test]
    fn mutant_sharing_loss_independently_built_equal_subterms_collapse() {
        // Two separate allocations with identical structure.
        let left = Expr::app(bvar(0), bvar(1));
        let right = Expr::app(bvar(0), bvar(1));
        assert_eq!(left, right, "structurally equal");
        assert_ne!(
            node_ptr(&left),
            node_ptr(&right),
            "but distinct allocations, or the fixture proves nothing"
        );

        let root = Expr::app(left, right);
        let mut interner = Interner::new();
        let canonical = interner.intern(&root);

        // bvar(0), bvar(1), the one shared app, and the root.
        assert_eq!(
            interner.len(),
            4,
            "the two equal subterms must be stored once: {} nodes",
            interner.len()
        );
        let kids = children_of(&canonical);
        assert_eq!(kids.len(), 2);
        assert_eq!(
            node_ptr(&kids[0]),
            node_ptr(&kids[1]),
            "both must be the SAME node — this is the sharing the store exists for"
        );
        assert!(
            interner.stats().shared > 0,
            "and the statistics must record it: {:?}",
            interner.stats()
        );
    }

    /// Input that ALREADY shares is walked once per stored node, not once per path.
    ///
    /// The complement of the mutant above, and the property that keeps a DAG from being traversed
    /// exponentially: a diamond presents four nodes, not five.
    #[test]
    fn an_input_dag_is_walked_once_per_node_not_once_per_path() {
        let shared = Expr::app(bvar(0), bvar(1));
        let root = Expr::app(shared.clone(), shared);
        let mut interner = Interner::new();
        interner.intern(&root);
        assert_eq!(
            interner.stats().presented,
            4,
            "a diamond presents four distinct nodes: {:?}",
            interner.stats()
        );
        assert_eq!(interner.len(), 4);
    }

    /// The seed terms for the thread matrix: distinct shapes with heavy deliberate overlap, so the
    /// schedule has something to get wrong.
    ///
    /// Overlap is the point. If every term were disjoint, every thread would store its own nodes and
    /// no two threads would ever race for the same identity — the test would run at 32 threads and
    /// prove nothing about sharing. These share `common` and share leaves, so the same structural
    /// identity is genuinely presented by several threads at once, and whichever arrives first is
    /// the one that stores it.
    fn matrix_terms(count: usize) -> Vec<Expr> {
        let common = Expr::app(bvar(0), bvar(1));
        (0..count)
            .map(|index| {
                let leaf = bvar((index % 8) as u32);
                let tagged = Expr::lam(
                    name(["p", "q", "r", "s"][index % 4]),
                    Expr::sort(Level::zero()),
                    leaf,
                    BinderInfo::Default,
                );
                Expr::app(common.clone(), tagged)
            })
            .collect()
    }

    /// Every stored term, in an order derived from the terms themselves rather than from their ids.
    ///
    /// Sorting by `TermId` would be the mistake this reduction exists to avoid: ids are assignment
    /// ordered, so an id-sorted list is schedule-dependent and two thread counts would "differ" for
    /// a reason that is not a defect. `Debug` on `Expr` is structural and stack-safe (that is stated
    /// in this module's header and relied on by `Expr` itself), so it is a total structural key.
    fn canonical_reduction(store: &SharedInterner) -> Vec<String> {
        let count = store.len().expect("the store is not poisoned");
        let guard = store.inner.lock().expect("the store is not poisoned");
        let mut rendered: Vec<String> = (0..count)
            .map(|index| {
                let node = guard
                    .get(TermId(index as u32))
                    .expect("every id below len names a node");
                format!("{node:?}")
            })
            .collect();
        rendered.sort();
        rendered
    }

    /// **FL-INV-01 for the term store**: the same terms interned at 1, 8 and 32 threads give the
    /// same store.
    ///
    /// The claim is stated precisely on [`SharedInterner`] and asserted precisely here, because the
    /// weak version of this test — "it did not crash at 32 threads" — is the one that passes while
    /// the property is false. What is asserted is the SET of stored nodes and the presented/stored/
    /// shared counts. What is deliberately NOT asserted is `TermId` values or `identity_digest`
    /// bytes: both are assignment-ordered by design, both are unobservable outside this module, and
    /// pinning them would pin the schedule dependence rather than remove it.
    ///
    /// The counts are the sharper half. `stored` being schedule-independent is the whole interning
    /// invariant restated under concurrency: dedup is by structural identity, so which thread gets
    /// there first decides who pays for a node, never how many nodes exist. A store that raced would
    /// show it here as a `stored` that grows with the thread count.
    ///
    /// **The matrix is discriminating, measured rather than assumed.** A determinism test proves
    /// nothing if the schedule never actually varies — it would report "identical at 32 threads"
    /// about 32 threads that behaved like one. Probed on 2026-07-25 by rendering the store in `TermId`
    /// order instead of structural order: at 8 and 32 workers that order differed from the 1-worker
    /// order on 6 of 6 executions, while the structural reduction and all three counts were
    /// identical every time. So the threads genuinely interleave and genuinely race for the same
    /// identities, and what survives that is a property rather than an artefact of everything
    /// happening to run in sequence.
    ///
    /// That probe is recorded here rather than kept as an assertion on purpose: "the ids differ" is
    /// a statement about a race, so asserting it would be asserting that an unlucky-but-legal
    /// schedule never happens, and a flaky guard is worse than a recorded measurement.
    #[test]
    fn interning_is_identical_at_1_8_and_32_threads() {
        const TERMS: usize = 256;
        let terms = matrix_terms(TERMS);

        let mut baseline: Option<(Vec<String>, SharingStats)> = None;
        for worker_count in [1usize, 8, 32] {
            let store = SharedInterner::new();
            let partition_sizes = std::thread::scope(|scope| {
                let handles: Vec<_> = (0..worker_count)
                    .map(|worker| {
                        let store = &store;
                        let terms = &terms;
                        scope.spawn(move || {
                            let mut mine = 0usize;
                            for (index, term) in terms.iter().enumerate() {
                                if index % worker_count != worker {
                                    continue;
                                }
                                let outcome =
                                    store.intern_bounded(term, StoreBudget::representable());
                                let canonical = match outcome {
                                    Outcome::Complete(canonical) => canonical,
                                    other => {
                                        unreachable!("interning must complete, got {other:?}")
                                    }
                                };
                                assert_eq!(
                                    &canonical, term,
                                    "the canonical form must be structurally the term it came from"
                                );
                                mine += 1;
                            }
                            mine
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|handle| handle.join().expect("worker completes"))
                    .collect::<Vec<_>>()
            });

            // Productive, on the same standard as the declaration-admission matrix: an idle worker
            // means this thread count is a label rather than a schedule, and a test that never ran
            // 32 threads cannot have proved anything about 32 threads.
            assert_eq!(partition_sizes.len(), worker_count);
            assert!(
                partition_sizes.iter().all(|size| *size > 0),
                "an empty partition means this worker count is a label, not a schedule \
                 (sizes {partition_sizes:?})"
            );
            assert_eq!(
                partition_sizes.iter().sum::<usize>(),
                TERMS,
                "the partition must cover every term exactly once"
            );

            let reduction = canonical_reduction(&store);
            let stats = store.stats().expect("the store is not poisoned");

            match &baseline {
                None => baseline = Some((reduction, stats)),
                Some((expected_reduction, expected_stats)) => {
                    assert_eq!(
                        &reduction, expected_reduction,
                        "the set of stored nodes must not depend on the thread count \
                         (at {worker_count} workers)"
                    );
                    assert_eq!(
                        stats.presented, expected_stats.presented,
                        "presentations are a function of the input, not of the schedule"
                    );
                    assert_eq!(
                        stats.stored, expected_stats.stored,
                        "the interning invariant under concurrency: dedup is by structural \
                         identity, so `stored` counts distinct identities and cannot grow with \
                         the thread count (at {worker_count} workers)"
                    );
                    assert_eq!(
                        stats.shared, expected_stats.shared,
                        "shared is presented minus stored, so it inherits both"
                    );
                }
            }
        }

        let (_, stats) = baseline.expect("the matrix ran at least once");
        // The fixture must actually exercise sharing, or `stored` being stable is stable for the
        // uninteresting reason that nothing was ever shared.
        assert!(
            stats.shared > 0 && stats.stored < stats.presented,
            "the seed terms must overlap or this matrix proves nothing about dedup: {stats:?}"
        );
    }

    /// A poisoned store reports an `InternalFault`, not an `Inconclusive` and not a panic.
    ///
    /// The distinction is FL-INV-07's: a poisoned lock means an invariant already broke in another
    /// thread, which is a different claim from "a budget ran out". Collapsing the two would let a
    /// caller retry with a larger budget against a store that is broken rather than full.
    #[test]
    fn a_poisoned_store_is_an_internal_fault_not_a_resource_stop() {
        let store = SharedInterner::new();
        let poisoned = std::thread::scope(|scope| {
            scope
                .spawn(|| {
                    let _guard = store.inner.lock().expect("the store starts healthy");
                    panic!("deliberate: poison the store while holding it");
                })
                .join()
                .is_err()
        });
        assert!(
            poisoned,
            "the helper thread must have panicked to poison it"
        );

        let outcome = store.intern_bounded(&bvar(0), StoreBudget::representable());
        match outcome {
            Outcome::InternalFault(fault) => {
                assert_eq!(fault.invariant, "FL-INV-07");
            }
            other => panic!("a poisoned store must be an internal fault, got {other:?}"),
        }
        assert!(
            store.stats().is_none(),
            "a poisoned store has no statistics; zeroes would read as `nothing was interned`"
        );
    }

    /// Names that `to_display_string` cannot tell apart are distinct in the identity digest.
    ///
    /// These are the exact collisions `franken_lean-f6br` was filed over, and they were live in
    /// this digest until the five name sites moved to the structural encoding. Asserted at the
    /// DIGEST rather than through the store, because the store would pass either way: a colliding
    /// digest is a bucket hint and full `Expr` equality would still separate the two terms. That is
    /// why this was not a soundness bug — and also why only a digest-level assertion can catch it.
    /// A store-level test here would be the test that passes while the property is false.
    /// Interning changes SHARING, and canonical bytes must not notice
    /// (bead `fln-sv7x`).
    ///
    /// # This is the opposite of what `fln-sv7x` asks for, and the opposite is correct
    ///
    /// That bead asks for "serialization preserving sharing exactly in both codecs" and
    /// prescribes asserting it against `fln-hash`'s `Canonical` codec. For THAT codec the
    /// property would be a **defect**, not a feature. `Canonical` is documented as "a value
    /// with exactly one canonical encoding under a frozen schema"; sharing is not part of an
    /// `Expr`'s identity, so a sharing-sensitive encoder would give one value many encodings
    /// depending on how it happened to be built, and every content-addressed digest resting on
    /// it — logical roots, witnesses, intern keys — would move with construction history.
    ///
    /// So the honest canon-side property is the DUAL of the bead's: the encoding must be
    /// sharing-INDEPENDENT. `Expr::write_body` walks a work stack with no memo table and emits
    /// the tree expansion deliberately, which is what makes that true. Sharing preservation is
    /// a real requirement for the *olean* codec, where the artifact is storage rather than an
    /// identity preimage — and no olean expression encoder exists yet.
    ///
    /// What this pins, which nothing else did: the interner is free to rewrite an `Expr`'s
    /// sharing (that is its entire job), and doing so may not move a single canonical byte.
    /// Without this, an interner change could silently move every digest downstream of it.
    #[test]
    fn interning_rewrites_sharing_and_canonical_bytes_do_not_move() {
        let leaf = || Expr::const_(Name::str(Name::anonymous(), "leaf"), Vec::new());

        // Same denotation, deliberately different sharing: `shared` reaches ONE node by two
        // paths; `unshared` builds two independent equal nodes.
        let once = leaf();
        let shared = Expr::app(once.clone(), once.clone());
        let unshared = Expr::app(leaf(), leaf());

        // Premise: the sharing really does differ, or this test proves nothing.
        let (f_shared, a_shared) = match shared.node() {
            ExprNode::App { f, a } => (node_ptr(f), node_ptr(a)),
            other => unreachable!("built an App, got {other:?}"),
        };
        let (f_unshared, a_unshared) = match unshared.node() {
            ExprNode::App { f, a } => (node_ptr(f), node_ptr(a)),
            other => unreachable!("built an App, got {other:?}"),
        };
        assert_eq!(
            f_shared, a_shared,
            "premise: the shared term aliases its children"
        );
        assert_ne!(
            f_unshared, a_unshared,
            "premise: the unshared term does not alias its children"
        );
        assert_eq!(shared, unshared, "premise: the two denote the same value");

        // The property: one value, one encoding, whatever its sharing.
        assert_eq!(
            shared.to_canonical_bytes(),
            unshared.to_canonical_bytes(),
            "canonical bytes must not depend on how the term was built"
        );

        // And interning — which exists precisely to rewrite sharing — moves no byte.
        let mut store = Interner::new();
        let before = unshared.to_canonical_bytes();
        let Outcome::Complete(interned) =
            store.intern_bounded(&unshared, StoreBudget::representable())
        else {
            unreachable!("the largest representable budget interns a two-node term")
        };
        assert_eq!(interned, unshared, "interning preserves the value");
        assert_eq!(
            interned.to_canonical_bytes(),
            before,
            "interning rewrites sharing; canonical bytes must not notice"
        );
    }

    /// The level plane is keyed on the CANONICAL encoding, not on `Debug`.
    ///
    /// This test is written against the ENCODER rather than against discrimination, and that is
    /// deliberate: `Level`'s `Debug` is structural, so distinct levels do not actually collide
    /// under it and a discrimination-only test would pass equally well before and after the fix.
    /// It would prove nothing and would quietly certify the defect.
    ///
    /// So the assertion recomputes the preimage independently — `Domain::DeclContent`, the intern
    /// tag, the `Sort` discriminant, then the length-prefixed `Canonical` bytes — and requires
    /// `identity_digest` to agree. Reverting either level site to `format!("{:?}")` fails it.
    ///
    /// The defect being pinned was LATENT, not active (see `update_level`): nothing was wrong,
    /// but the correctness rested on `Debug` happening to be structural, which no test asserted
    /// and which `Level`'s own doc invites a refactor to change.
    #[test]
    fn the_identity_digest_keys_levels_on_the_canonical_encoding_not_on_debug() {
        let done = HashMap::new();
        let level = Level::param(Name::str(Name::anonymous(), "u"))
            .succ()
            .expect("one successor is within the depth bound");
        let sort = Expr::sort(level.clone());

        let mut writer = CanonWriter::new();
        level.write_body(&mut writer);
        let canonical = writer.into_bytes();

        let mut expected = DomainHasher::new(Domain::DeclContent);
        expected.update(INTERN_TAG);
        expected.update(&[0]);
        expected.update(&[4]);
        expected.update(&(canonical.len() as u64).to_le_bytes());
        expected.update(&canonical);

        assert_eq!(
            identity_digest(&sort, &done),
            expected.finalize(),
            "a Sort's identity preimage must be the canonical level bytes, length-prefixed"
        );

        // And the encoding is not the rendering: if these were equal the fix would be vacuous.
        assert_ne!(
            canonical.as_slice(),
            format!("{level:?}").as_bytes(),
            "premise: the canonical encoding must differ from the Debug rendering"
        );
    }

    #[test]
    fn the_identity_digest_separates_names_the_display_form_collides() {
        let done = HashMap::new();
        let anon = Name::anonymous();

        // A numeric component and a string component that render identically.
        let numeric = Expr::const_(Name::num(anon.clone(), 5), Vec::new());
        let stringy = Expr::const_(Name::str(anon.clone(), "5"), Vec::new());
        assert_eq!(
            Name::num(anon.clone(), 5).to_display_string(),
            Name::str(anon.clone(), "5").to_display_string(),
            "premise: the display form must actually collide, or this test proves nothing"
        );
        assert_ne!(
            identity_digest(&numeric, &done),
            identity_digest(&stringy, &done),
            "a numeric component must not be able to imitate a string one"
        );

        // Two components `a`,`b` versus one component literally spelled `a.b`: the display form
        // joins with `.` and does not escape, so both render as `a.b`.
        let nested = Expr::const_(Name::str(Name::str(anon.clone(), "a"), "b"), Vec::new());
        let flat = Expr::const_(Name::str(anon.clone(), "a.b"), Vec::new());
        assert_eq!(
            Name::str(Name::str(anon.clone(), "a"), "b").to_display_string(),
            Name::str(anon.clone(), "a.b").to_display_string(),
            "premise: the display form must actually collide, or this test proves nothing"
        );
        assert_ne!(
            identity_digest(&nested, &done),
            identity_digest(&flat, &done),
            "a component containing the display separator must not forge a deeper path"
        );
    }

    /// A budget larger than the id space does not raise the ceiling, it is clamped to it.
    ///
    /// The defect this closes — `TermId(self.nodes.len() as u32)` wrapping and aliasing two
    /// structurally different nodes onto one id — needs over 4.29e9 stored nodes to reach, which no
    /// test can build. So the clamp is asserted where it is *decided* rather than by exhausting it,
    /// and the two things a test genuinely can prove are proved: that an over-large budget is not
    /// granted, and that the clamp does not distort an ordinary one. A clamp that quietly rewrote
    /// every reported `allowed` would be its own defect, and it would be invisible from the first
    /// assertion alone.
    #[test]
    fn a_budget_above_the_id_space_is_clamped_to_it() {
        assert_eq!(
            StoreBudget::representable().max_nodes,
            MAX_STORED_NODES,
            "`representable` must name the whole id space and nothing beyond it"
        );
        assert_eq!(
            StoreBudget {
                max_nodes: u64::MAX
            }
            .effective_max_nodes(),
            MAX_STORED_NODES,
            "a budget above the id space must be clamped, not granted: granting it is how an id wraps"
        );
        assert_eq!(
            StoreBudget::generous().effective_max_nodes(),
            StoreBudget::generous().max_nodes,
            "an ordinary budget must pass through untouched"
        );

        // And the refusal reports the limit actually ENFORCED, so a caller who asked for more can
        // see that it was not granted.
        let root = Expr::app(bvar(0), bvar(1));
        let mut interner = Interner::new();
        let outcome = interner.intern_bounded(&root, StoreBudget { max_nodes: 1 });
        let usage = match &outcome {
            Outcome::Inconclusive(inconclusive) => match &inconclusive.cause {
                fln_core::outcome::InconclusiveCause::ResourceExhausted { usage } => Some(usage),
                _ => None,
            },
            _ => None,
        };
        let usage = usage.expect("an exceeded store budget is a resource stop");
        assert_eq!(
            usage.allowed, 1,
            "a budget below the ceiling must report itself, not the ceiling"
        );
    }

    /// **MUTANT `partial-insert`.** A budget refusal leaves the store untouched, so a caller can
    /// retry with a larger allowance rather than inspect a half-built store.
    #[test]
    fn mutant_partial_insert_a_refused_intern_stores_nothing() {
        let root = Expr::app(Expr::app(bvar(0), bvar(1)), Expr::app(bvar(2), bvar(3)));

        let mut interner = Interner::new();
        let before = interner.len();
        let outcome = interner.intern_bounded(&root, StoreBudget { max_nodes: 3 });

        let usage = match &outcome {
            Outcome::Inconclusive(inconclusive) => match &inconclusive.cause {
                fln_core::outcome::InconclusiveCause::ResourceExhausted { usage } => Some(usage),
                _ => None,
            },
            _ => None,
        };
        let usage = usage.expect("an exceeded store budget is a resource stop");
        assert_eq!(
            usage.reason,
            ResourceReason::StructuralBudget {
                unit: StructuralUnit::ProducedNodes
            },
            "the honest unit for a store bounded by how many nodes it holds"
        );
        assert!(usage.is_genuine_exhaustion());
        assert_eq!(
            interner.len(),
            before,
            "a refused intern must store NOTHING — not a prefix of the term"
        );
    }

    /// A budget stop is not a rejection and publishes no diagnostic. The term is impeccable — it
    /// interns cleanly under a larger budget — so a leaked diagnostic here would tell a user their
    /// correct term is malformed.
    #[test]
    fn a_store_budget_stop_is_inconclusive_and_publishes_nothing() {
        let root = Expr::app(bvar(0), bvar(1));
        let mut control = Interner::new();
        assert!(
            matches!(
                control.intern_bounded(&root, StoreBudget::generous()),
                Outcome::Complete(_)
            ),
            "the term interns cleanly under a generous budget, so nothing about it is wrong"
        );

        let mut interner = Interner::new();
        let outcome = interner.intern_bounded(&root, StoreBudget { max_nodes: 1 });
        assert!(
            !matches!(outcome, Outcome::Complete(_)),
            "not an acceptance"
        );
        assert!(
            !matches!(outcome, Outcome::InternalFault(_)),
            "declining is not an internal fault"
        );
        let published = match &outcome {
            Outcome::Inconclusive(inconclusive) => inconclusive.diagnostic.clone(),
            _ => None,
        };
        assert!(published.is_none(), "published a diagnostic: {published:?}");
    }

    /// A generous budget is invisible: the same store as the unbounded path.
    #[test]
    fn a_generous_budget_interns_exactly_as_the_unbounded_path_does() {
        let root = Expr::lam(
            name("x"),
            Expr::sort(Level::zero()),
            Expr::app(bvar(0), bvar(0)),
            BinderInfo::Default,
        );
        let mut unbounded = Interner::new();
        let a = unbounded.intern(&root);

        let mut bounded = Interner::new();
        let b = match bounded.intern_bounded(&root, StoreBudget::generous()) {
            Outcome::Complete(expr) => expr,
            other => panic!("a generous budget must complete: {other:?}"),
        };

        assert_eq!(a, b);
        assert_eq!(unbounded.len(), bounded.len(), "the same node count");
        assert_eq!(
            unbounded.stats(),
            bounded.stats(),
            "and the same statistics"
        );
    }

    /// **Total on depth.** A left-nested chain far deeper than any stack frame budget interns without
    /// overflowing, because the traversal is a heap worklist.
    #[test]
    fn interning_is_total_on_a_deep_term() {
        let mut deep = bvar(0);
        for _ in 0..20_000 {
            deep = Expr::app(deep, bvar(1));
        }
        let mut interner = Interner::new();
        let canonical = interner.intern(&deep);
        assert_eq!(canonical, deep, "the interned term equals the input");
        // bvar(0), bvar(1), and one App per level.
        assert_eq!(interner.len(), 20_002);
    }

    /// Re-interning an already-canonical term is idempotent: no new nodes, and the same pointer.
    #[test]
    fn interning_is_idempotent() {
        let root = Expr::app(bvar(0), Expr::lit(Literal::Nat(NatLit::from_u64(3))));
        let mut interner = Interner::new();
        let once = interner.intern(&root);
        let count = interner.len();
        let twice = interner.intern(&once);
        assert_eq!(
            node_ptr(&once),
            node_ptr(&twice),
            "re-interning a canonical term returns the same node"
        );
        assert_eq!(interner.len(), count, "and stores nothing new");
    }

    /// Sharing statistics account for every presentation, and a nonzero `bucket_misses` would be
    /// correct-but-notable rather than hidden.
    #[test]
    fn sharing_statistics_account_for_every_presentation() {
        // Independently built, so there is sharing for the store to provide — see the note on
        // `mutant_sharing_loss_independently_built_equal_subterms_collapse`.
        let root = Expr::app(Expr::app(bvar(0), bvar(1)), Expr::app(bvar(0), bvar(1)));
        let mut interner = Interner::new();
        interner.intern(&root);
        let stats = interner.stats();
        assert_eq!(
            stats.presented,
            stats.stored + stats.shared,
            "every presentation is either stored or shared: {stats:?}"
        );
        assert_eq!(stats.stored as usize, interner.len());
        assert!(stats.sharing_ratio() > 0.0);
        assert_eq!(
            stats.bucket_misses, 0,
            "no digest collision is expected on this fixture; a nonzero value here would be \
             correct behaviour but worth investigating"
        );
    }

    /// Distinct terms stay distinct — the other direction of the invariant. Without this, an
    /// interner that merged everything would satisfy "structural equality implies pointer equality"
    /// perfectly.
    #[test]
    fn structurally_different_terms_intern_to_different_nodes() {
        let terms = one_of_each();
        let mut interner = Interner::new();
        let interned: Vec<(&str, Expr)> = terms
            .iter()
            .map(|(label, expr)| (*label, interner.intern(expr)))
            .collect();

        for (i, (label_a, a)) in interned.iter().enumerate() {
            for (label_b, b) in interned.iter().skip(i + 1) {
                assert_ne!(
                    node_ptr(a),
                    node_ptr(b),
                    "{label_a} and {label_b} are different terms and must be different nodes. \
                     Without this direction, an interner that merged everything would satisfy the \
                     invariant."
                );
            }
        }
    }
}
