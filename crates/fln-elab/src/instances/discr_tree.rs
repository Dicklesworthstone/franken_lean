//! The pin's discrimination tree over imported instances (bead `fln-52qv`).
//!
//! Before it tries any instance, the pin narrows the global instances of a goal
//! with `globalInstances.getUnify type` (`getInstances`, vendored
//! `src/Lean/Meta/SynthInstance.lean:201-240`). Without that step every
//! instance of the class is tried: under the real `Init`, `if n < 5` on `Nat`
//! made 1,526 candidate trials, 202 `Decidable` instances entered 396 times,
//! and ran out of heartbeats.
//!
//! The insert side is the pin's own data. Every imported instance carries the
//! path the pin computed for its type when the instance was registered
//! (`InstanceEntry.keys`, `mkInstanceKey`, vendored
//! `src/Lean/Meta/Instances.lean`). This module holds the trie, the pin's
//! `getUnify` traversal (vendored `src/Lean/Meta/DiscrTree/Main.lean`), and the
//! one part computed here, the goal's keys (`getUnifyKeyArgs`).
//!
//! # The goal side may lose precision, never a candidate
//!
//! The pin keys a goal subterm after `reduceDT`: `whnfCore`, then unfolding
//! every definition whose `ReducibilityStatus` is `reducible`. A goal key never
//! claims more than is known, and each uncertainty widens the query instead:
//!
//! - A constant that is not a definition is never unfolded: an inductive type,
//!   constructor, axiom, theorem, opaque constant, `Quot` or `Quot.mk`.
//! - A definition with a recorded status (`crate::reducibility`, bead
//!   `fln-gkhu`) is unfolded and keyed by its unfolding alone when it is
//!   `reducible`, and kept folded otherwise. An unreadable status journal makes
//!   it a star.
//! - A definition with no recorded status is known *not* reducible when some
//!   stored path, at a non-root
//!   position, keeps it folded. The pin's `reduce` unfolds every reducible head
//!   it meets, and unfolding a definition that is neither a matcher nor smart
//!   unfolded always succeeds, so a folded occurrence is the pin's own record
//!   that the definition was not reducible when that instance was registered.
//! - Any other definition may or may not be reducible, so both outcomes are
//!   queried: its folded key, and the keys of its delta-beta unfolding.
//! - A recursor, matcher, smart-unfolded definition, `Quot.lift` or `Quot.ind`,
//!   a projection, `let`, unapplied lambda, let-bound or unknown free variable,
//!   and every metavariable is a star, which matches any path.
//!
//! What the second rule assumes: a definition stays not reducible after an
//! instance stored it folded. A later `attribute [reducible]` breaks that. In
//! the pin's own environment for `import Lean`, every definition that a stored
//! instance path keeps folded and that is now `reducible` has a smart-unfolding
//! companion (one, `Std.Do.SVal`), which the rule already excludes.
//!
//! Native registrations use the same bounded path and prerequisite-order model
//! as source-module export. Unsupported native models, paths that name a free
//! variable, and paths whose root is not the goal's are never filtered. A query
//! that exhausts its step allowance filters nothing.
//!
//! # Candidate order (bead `fln-vm35`)
//!
//! The pin takes `getUnify`'s matches in traversal order, sorts them stably by
//! priority ascending, and its generator tries that array from the end
//! (`getInstances`, and `generate` at vendored `SynthInstance.lean:547-582`). So
//! [`InstanceIndex::narrow`] returns candidates in the order they are tried:
//! priority descending, then the later traversal position first. The traversal
//! is the pin's: at a node the star child before the goal's own key, children in
//! `Key.lt` order, and a leaf's values in insertion order, which is the imported
//! instances' registration order. Where the pin's own index has no position for
//! a candidate (FrankenLean's own registrations, and paths rooted elsewhere), the
//! candidate is tried before every indexed candidate of its priority, newest
//! first: the pin inserts a module's own instances after its imports.
//!
//! Two orders are FrankenLean's choice, because the pin has nothing to compare:
//! where a goal key is uncertain and several alternatives are queried, their
//! subtrees are visited in the order the alternatives are listed; and a goal
//! whose root is a star visits the root's children in key order, where the pin
//! folds a hash map.
use super::{
    InstanceEntry, InstanceRegistry, InstanceRegistryError, MAX_ENTRY_BYTES, beta, read_name, take,
    write_name,
};
use crate::lctx::LocalContext;
use fln_core::expr::{Expr, ExprNode, FVarId, Literal, NatLit};
use fln_core::name::{LeafView, Name};
use fln_env::constants::{ConstantInfo, QuotKind};
use fln_env::environment::Environment;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, OnceLock};

/// Keys in one stored path.
const MAX_PATH_KEYS: usize = 4_096;
/// Delta or beta steps explored at one goal position.
const MAX_UNFOLDS: usize = 16;
/// Key computations and trie visits for one query.
const MAX_STEPS: usize = 1 << 18;

/// `DiscrTree.Key` (vendored `src/Lean/Meta/DiscrTree/Types.lean`), in its
/// constructor order. Universe levels are not part of a key.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Key {
    Star,
    Other,
    Lit(Literal),
    FVar(FVarId, u32),
    Const(Name, u32),
    Arrow,
    /// Structure name, field index, argument count.
    Proj(Name, u32, u32),
}

impl Key {
    /// `Key.arity`: how many subterm paths follow this key.
    pub fn arity(&self) -> usize {
        match self {
            Key::Const(_, n) | Key::FVar(_, n) => *n as usize,
            Key::Arrow => 1,
            Key::Proj(_, _, n) => 1 + *n as usize,
            Key::Star | Key::Other | Key::Lit(_) => 0,
        }
    }

    /// The constructor index, which is also this key's journal tag.
    fn index(&self) -> u8 {
        match self {
            Key::Star => 0,
            Key::Other => 1,
            Key::Lit(_) => 2,
            Key::FVar(..) => 3,
            Key::Const(..) => 4,
            Key::Arrow => 5,
            Key::Proj(..) => 6,
        }
    }

    /// `Key.lt` as a total order: constructor index, then `Name.quickLt` and
    /// the numbers within a constructor. `Key.star` is the least key.
    fn order(&self, other: &Key) -> Ordering {
        match (self, other) {
            (Key::Lit(a), Key::Lit(b)) => {
                if a.lt(b) {
                    Ordering::Less
                } else if b.lt(a) {
                    Ordering::Greater
                } else {
                    Ordering::Equal
                }
            }
            (Key::FVar(a, m), Key::FVar(b, n)) => a.0.quick_cmp(&b.0).then(m.cmp(n)),
            (Key::Const(a, m), Key::Const(b, n)) => a.quick_cmp(b).then(m.cmp(n)),
            (Key::Proj(s, i, m), Key::Proj(t, j, n)) => {
                s.quick_cmp(t).then(i.cmp(j)).then(m.cmp(n))
            }
            _ => self.index().cmp(&other.index()),
        }
    }
}

fn put32(value: usize, out: &mut Vec<u8>) -> Result<(), InstanceRegistryError> {
    out.extend(
        u32::try_from(value)
            .map_err(|_| InstanceRegistryError::Limit)?
            .to_le_bytes(),
    );
    Ok(())
}
fn get32(bytes: &mut &[u8]) -> Result<u32, InstanceRegistryError> {
    Ok(u32::from_le_bytes(
        take(bytes, 4)?
            .try_into()
            .map_err(|_| InstanceRegistryError::Malformed)?,
    ))
}

/// The imported-instance journal's encoding of one stored path.
pub(super) fn write_keys(keys: &[Key], out: &mut Vec<u8>) -> Result<(), InstanceRegistryError> {
    if keys.len() > MAX_PATH_KEYS {
        return Err(InstanceRegistryError::Limit);
    }
    put32(keys.len(), out)?;
    for key in keys {
        out.push(key.index());
        match key {
            Key::Star | Key::Other | Key::Arrow => {}
            Key::Lit(Literal::Nat(value)) => {
                out.push(0);
                put32(value.limbs_le().len(), out)?;
                for limb in value.limbs_le() {
                    out.extend(limb.to_le_bytes());
                }
            }
            Key::Lit(Literal::Str(text)) => {
                out.push(1);
                put32(text.len(), out)?;
                out.extend(text.as_bytes());
            }
            Key::FVar(FVarId(name), arity) | Key::Const(name, arity) => {
                write_name(name, out)?;
                out.extend(arity.to_le_bytes());
            }
            Key::Proj(name, field, arity) => {
                write_name(name, out)?;
                out.extend(field.to_le_bytes());
                out.extend(arity.to_le_bytes());
            }
        }
        if out.len() > MAX_ENTRY_BYTES {
            return Err(InstanceRegistryError::Limit);
        }
    }
    Ok(())
}

/// [`write_keys`]'s inverse. A literal must be in its one canonical form.
pub(super) fn read_keys(bytes: &mut &[u8]) -> Result<Vec<Key>, InstanceRegistryError> {
    let count = usize::try_from(get32(bytes)?).map_err(|_| InstanceRegistryError::Malformed)?;
    if count > MAX_PATH_KEYS {
        return Err(InstanceRegistryError::Limit);
    }
    let mut keys = Vec::with_capacity(count);
    for _ in 0..count {
        let key = match take(bytes, 1)?[0] {
            0 => Key::Star,
            1 => Key::Other,
            2 => match take(bytes, 1)?[0] {
                0 => {
                    let limbs = usize::try_from(get32(bytes)?)
                        .map_err(|_| InstanceRegistryError::Malformed)?;
                    let data = take(
                        bytes,
                        limbs
                            .checked_mul(8)
                            .ok_or(InstanceRegistryError::Malformed)?,
                    )?;
                    let limbs: Vec<u64> = data
                        .as_chunks::<8>()
                        .0
                        .iter()
                        .map(|chunk| u64::from_le_bytes(*chunk))
                        .collect();
                    if limbs.last() == Some(&0) {
                        return Err(InstanceRegistryError::Malformed);
                    }
                    Key::Lit(Literal::Nat(NatLit::from_limbs_le(limbs)))
                }
                1 => {
                    let len = usize::try_from(get32(bytes)?)
                        .map_err(|_| InstanceRegistryError::Malformed)?;
                    let text = std::str::from_utf8(take(bytes, len)?)
                        .map_err(|_| InstanceRegistryError::Malformed)?;
                    Key::Lit(Literal::Str(text.to_owned()))
                }
                _ => return Err(InstanceRegistryError::Malformed),
            },
            3 => Key::FVar(FVarId(read_name(bytes)?), get32(bytes)?),
            4 => Key::Const(read_name(bytes)?, get32(bytes)?),
            5 => Key::Arrow,
            6 => Key::Proj(read_name(bytes)?, get32(bytes)?, get32(bytes)?),
            _ => return Err(InstanceRegistryError::Malformed),
        };
        keys.push(key);
    }
    Ok(keys)
}

/// `DiscrTree.Trie`: values stored at this node, and children in key order.
#[derive(Debug, Default)]
struct Node {
    values: Vec<Name>,
    children: Vec<(Key, Node)>,
}

impl Node {
    fn child(&self, key: &Key) -> Option<&Node> {
        self.children
            .binary_search_by(|(k, _)| k.order(key))
            .ok()
            .map(|at| &self.children[at].1)
    }

    /// `insertKeyValue`: one value per declaration and path.
    fn insert(&mut self, keys: &[Key], value: &Name) {
        let mut node = self;
        for key in keys {
            let at = match node.children.binary_search_by(|(k, _)| k.order(key)) {
                Ok(at) => at,
                Err(at) => {
                    node.children.insert(at, (key.clone(), Node::default()));
                    at
                }
            };
            node = &mut node.children[at].1;
        }
        if !node.values.contains(value) {
            node.values.push(value.clone());
        }
    }
}

/// The pin's instance index over one immutable registry view.
#[derive(Debug, Default)]
pub(crate) struct InstanceIndex {
    root: Node,
    /// Definitions some stored path keeps folded at a non-root position.
    folded: BTreeSet<Name>,
    /// The first key of each indexed instance's path.
    roots: BTreeMap<Name, Key>,
    /// Exact prerequisite order for supported native registrations. Imported
    /// orders remain in their original, authoritative metadata journal.
    native_synth_order: BTreeMap<Name, Vec<u32>>,
}

/// A registry's lazy source-search index. It changes neither registry equality
/// nor environment metadata, and is only published after every active native
/// model has completed within its budget.
#[derive(Debug, Clone, Default)]
pub(crate) struct IndexCell(OnceLock<Arc<InstanceIndex>>);

impl PartialEq for IndexCell {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for IndexCell {}

impl IndexCell {
    pub(super) fn get<'a>(
        &'a self,
        registry: &InstanceRegistry,
        env: &Environment,
        work_left: &mut usize,
    ) -> Result<&'a InstanceIndex, InstanceRegistryError> {
        if let Some(index) = self.0.get() {
            return Ok(index.as_ref());
        }
        // A resource failure never leaves a partial index or a cached miss.
        let index = InstanceIndex::build_source(registry, env, work_left)?;
        let _ = self.0.set(Arc::new(index));
        Ok(self
            .0
            .get()
            .expect("complete source index published")
            .as_ref())
    }
}

impl InstanceIndex {
    fn insert(&mut self, keys: &[Key], declaration: &Name) {
        let Some(first) = keys.first() else {
            return;
        };
        if keys.iter().any(|key| matches!(key, Key::FVar(..))) {
            return;
        }
        for key in &keys[1..] {
            if let Key::Const(name, _) = key {
                self.folded.insert(name.clone());
            }
        }
        self.roots.insert(declaration.clone(), first.clone());
        self.root.insert(keys, declaration);
    }

    fn build_source(
        registry: &InstanceRegistry,
        env: &Environment,
        work_left: &mut usize,
    ) -> Result<Self, InstanceRegistryError> {
        let spend = |left: &mut usize| -> Result<(), InstanceRegistryError> {
            *left = left.checked_sub(1).ok_or(InstanceRegistryError::Limit)?;
            Ok(())
        };
        let mut rows = Vec::new();
        // Only the active view participates. read_with_scopes has already
        // interleaved namespace activation and global registration events.
        for row in registry.instances.values().flatten() {
            spend(work_left)?;
            rows.push(row);
        }
        rows.sort_by_key(|row| row.order);
        let mut index = Self::default();
        for row in rows {
            spend(work_left)?;
            if let Some(parameters) = registry.imported.instances.get(&row.declaration) {
                for _ in &parameters.keys {
                    spend(work_left)?;
                }
                index.insert(&parameters.keys, &row.declaration);
            } else if let Some(model) =
                super::export::derive_index(env, registry, &row.declaration, work_left)?
            {
                for _ in &model.keys {
                    spend(work_left)?;
                }
                index.insert(&model.keys, &row.declaration);
                index
                    .native_synth_order
                    .insert(row.declaration.clone(), model.synth_order);
            }
        }
        Ok(index)
    }

    pub(crate) fn native_synth_order(&self, declaration: &Name) -> Option<&[u32]> {
        self.native_synth_order.get(declaration).map(Vec::as_slice)
    }

    /// The rows of `rows` that the pin's `getUnify` may return for `goal`, in
    /// the order the pin tries them (see the module documentation). Unindexed
    /// rows, and rows whose stored root is not the goal's, are kept. When the
    /// query runs out of steps every row is kept, in its given order.
    pub(crate) fn narrow<'r>(
        &self,
        env: &Environment,
        lctx: &LocalContext,
        goal: &Expr,
        rows: &'r [InstanceEntry],
    ) -> Vec<&'r InstanceEntry> {
        let mut query = Query {
            env,
            lctx,
            folded: &self.folded,
            steps: MAX_STEPS,
        };
        let Some(roots) = query.keys(goal, true) else {
            return rows.iter().collect();
        };
        let Some(matched) = self.get_unify(&mut query, &roots) else {
            return rows.iter().collect();
        };
        let position: BTreeMap<&Name, usize> = matched
            .iter()
            .enumerate()
            .map(|(at, name)| (name, at))
            .collect();
        // `None`: no position in the pin's index for this goal.
        let mut kept: Vec<(&'r InstanceEntry, Option<usize>)> = rows
            .iter()
            .filter_map(|row| match self.roots.get(&row.declaration) {
                None => Some((row, None)),
                Some(stored) => match position.get(&row.declaration) {
                    Some(at) => Some((row, Some(*at))),
                    None => (!roots.iter().any(|(key, _)| key == stored)).then_some((row, None)),
                },
            })
            .collect();
        // Stable: unpositioned rows keep their given (newest-first) order.
        kept.sort_by(|(a, at_a), (b, at_b)| {
            b.priority
                .cmp(&a.priority)
                .then_with(|| at_a.is_some().cmp(&at_b.is_some()))
                .then_with(|| at_b.cmp(at_a))
        });
        kept.into_iter().map(|(row, _)| row).collect()
    }

    /// `getUnify`, over the root alternatives of the goal: the matched values
    /// in the pin's traversal order, each once.
    fn get_unify(&self, query: &mut Query<'_>, roots: &[(Key, Vec<Expr>)]) -> Option<Vec<Name>> {
        let mut result = Vec::new();
        let mut seen = BTreeSet::new();
        let mut emit = |values: &[Name], result: &mut Vec<Name>| {
            for value in values {
                if seen.insert(value.clone()) {
                    result.push(value.clone());
                }
            }
        };
        // `process`, depth first with an explicit stack: each node's visits are
        // pushed in reverse, so the first is finished before the second starts.
        let mut work: Vec<(usize, Vec<Expr>, &Node)> = Vec::new();
        if roots.iter().any(|(key, _)| *key == Key::Star) {
            for (key, child) in self.root.children.iter().rev() {
                work.push((key.arity(), Vec::new(), child));
            }
        } else {
            // `getStarResult`: values whose whole path is a star.
            if let Some(star) = self.root.child(&Key::Star) {
                emit(&star.values, &mut result);
            }
            for (key, args) in roots.iter().rev() {
                if let Some(child) = self.root.child(key) {
                    work.push((0, args.clone(), child));
                }
            }
        }
        while let Some((skip, mut todo, node)) = work.pop() {
            query.spend()?;
            if skip > 0 {
                for (key, child) in node.children.iter().rev() {
                    work.push((skip - 1 + key.arity(), todo.clone(), child));
                }
                continue;
            }
            let Some(next) = todo.pop() else {
                emit(&node.values, &mut result);
                continue;
            };
            if node.children.is_empty() {
                continue;
            }
            let alternatives = query.keys(&next, false)?;
            if alternatives.iter().any(|(key, _)| *key == Key::Star) {
                for (key, child) in node.children.iter().rev() {
                    work.push((key.arity(), todo.clone(), child));
                }
                continue;
            }
            // The star child first (`visitStar`), then the goal's own key.
            let mut visits = Vec::new();
            if let Some((Key::Star, child)) = node.children.first() {
                visits.push((0, todo.clone(), child));
            }
            for (key, args) in alternatives {
                if let Some(child) = node.child(&key) {
                    let mut todo = todo.clone();
                    todo.extend(args);
                    visits.push((0, todo, child));
                }
            }
            work.extend(visits.into_iter().rev());
        }
        Some(result)
    }
}

/// What the pin's `reduceDT` may do to a constant head at `reducible`.
enum Head {
    /// Never unfolded.
    Folded,
    /// Always unfolded: a definition whose recorded status is `reducible`.
    Unfold,
    /// Unfolded if reducible, which is not known here.
    Either,
    /// Reduced by rules not modelled here.
    Star,
}

/// One goal query: the environment, the goal's local context, and its steps.
struct Query<'a> {
    env: &'a Environment,
    lctx: &'a LocalContext,
    folded: &'a BTreeSet<Name>,
    steps: usize,
}

impl Query<'_> {
    fn spend(&mut self) -> Option<()> {
        self.steps = self.steps.checked_sub(1)?;
        Some(())
    }

    fn head(&self, name: &Name) -> Head {
        match self.env.find(name) {
            Some(ConstantInfo::Defn(_)) => {
                let smart = Name::str(name.clone(), "_sunfold");
                if is_matcher(name) || self.env.find(&smart).is_some() {
                    return Head::Star;
                }
                // The pin's `reduce` unfolds exactly the `reducible` heads
                // (`withReducible`), so a recorded status decides; an unreadable
                // journal decides nothing and widens to a star.
                match crate::reducibility::known_status(self.env, name) {
                    Ok(Some(crate::reducibility::Reducibility::Reducible)) => Head::Unfold,
                    Ok(Some(_)) => Head::Folded,
                    Ok(None) if self.folded.contains(name) => Head::Folded,
                    Ok(None) => Head::Either,
                    Err(_) => Head::Star,
                }
            }
            Some(ConstantInfo::Rec(_)) | None => Head::Star,
            Some(ConstantInfo::Quot(quot))
                if matches!(quot.kind, QuotKind::Lift | QuotKind::Ind) =>
            {
                Head::Star
            }
            Some(_) => Head::Folded,
        }
    }

    /// `getUnifyKeyArgs`: every key `e` may have after `reduceDT`, each with its
    /// arguments last first. A star alternative is returned alone, since it
    /// subsumes the rest.
    fn keys(&mut self, e: &Expr, root: bool) -> Option<Vec<(Key, Vec<Expr>)>> {
        let star = || Some(vec![(Key::Star, Vec::new())]);
        let mut out: Vec<(Key, Vec<Expr>)> = Vec::new();
        let mut pending = vec![(e.clone(), 0usize)];
        while let Some((e, unfolds)) = pending.pop() {
            self.spend()?;
            let (head, args) = spine(&e);
            let arity = u32::try_from(args.len()).ok()?;
            match head.node() {
                ExprNode::Lit { literal } => out.push((Key::Lit(literal.clone()), Vec::new())),
                ExprNode::Const { name, .. } => {
                    let (folded, mut unfold) = match self.head(name) {
                        Head::Star => return star(),
                        Head::Folded => (true, false),
                        Head::Unfold => (false, true),
                        Head::Either => (true, true),
                    };
                    if folded {
                        // `toNatLit?` reads the term `whnfCore` left, whose head
                        // carries no metadata; its arguments keep theirs.
                        let numeral = if root {
                            None
                        } else {
                            numeral(&args.iter().rev().cloned().fold(head.clone(), Expr::app))
                        };
                        // A numeral's heads (`OfNat.ofNat`, `Nat.succ`) are
                        // semireducible in the pin, so its `reduce` leaves a numeral
                        // whole and keys it as a literal. Only a recorded `reducible`
                        // status (`Head::Unfold`, never here) would unfold one; an
                        // unrecorded status queries the literal alone (bead fln-eeew).
                        if numeral.is_some() {
                            unfold = false;
                        }
                        out.push(match numeral {
                            Some(value) => (Key::Lit(Literal::Nat(value)), Vec::new()),
                            None => (Key::Const(name.clone(), arity), args.clone()),
                        });
                    }
                    if unfold {
                        // At the root `reduceUntilBadKey` may stop short of an
                        // unfolding; never filter on a root that may move.
                        if root || unfolds >= MAX_UNFOLDS {
                            return star();
                        }
                        let Some(ConstantInfo::Defn(definition)) = self.env.find(name) else {
                            return star();
                        };
                        let forward: Vec<Expr> = args.iter().rev().cloned().collect();
                        let Some(unfolded) = beta(&definition.value, &forward) else {
                            return star();
                        };
                        pending.push((unfolded, unfolds + 1));
                    }
                }
                ExprNode::FVar { id } => {
                    if !self.lctx.find(id).is_some_and(|decl| decl.value.is_none()) {
                        return star();
                    }
                    out.push((Key::FVar(id.clone(), arity), args));
                }
                ExprNode::ForallE { binder_type, .. } if args.is_empty() => {
                    out.push((Key::Arrow, vec![binder_type.clone()]));
                }
                ExprNode::Sort { .. } if args.is_empty() => out.push((Key::Other, Vec::new())),
                // `whnfCore` beta-reduces an applied lambda.
                ExprNode::Lam { .. } if !args.is_empty() => {
                    if unfolds >= MAX_UNFOLDS {
                        return star();
                    }
                    let forward: Vec<Expr> = args.iter().rev().cloned().collect();
                    let Some(reduced) = beta(&head, &forward) else {
                        return star();
                    };
                    pending.push((reduced, unfolds + 1));
                }
                _ => return star(),
            }
        }
        let mut unique: Vec<(Key, Vec<Expr>)> = Vec::with_capacity(out.len());
        for alternative in out {
            if !unique.contains(&alternative) {
                unique.push(alternative);
            }
        }
        Some(unique)
    }
}

/// The head of `e` and its arguments, last first (`getAppRevArgs`), looking
/// through metadata on the head as `whnfCore` does.
fn spine(e: &Expr) -> (Expr, Vec<Expr>) {
    let mut args = Vec::new();
    let mut head = e.clone();
    loop {
        let next = match head.node() {
            ExprNode::App { f, a } => {
                args.push(a.clone());
                f.clone()
            }
            ExprNode::MData { expr, .. } => expr.clone(),
            _ => return (head, args),
        };
        head = next;
    }
}

/// A matcher's name ends in `match_<n>` (`mkMatcherAuxDefinition`).
fn is_matcher(name: &Name) -> bool {
    match name.leaf_view() {
        LeafView::Str(text) => text
            .strip_prefix("match_")
            .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit())),
        _ => false,
    }
}

/// `toNatLit?`: the value of a numeral (`isNumeral`): a raw natural literal,
/// `Nat.zero`, `Nat.succ` of a numeral, or `OfNat.ofNat _ n _` of a numeral.
/// Syntactic, as the pin's: metadata is not looked through.
fn numeral(e: &Expr) -> Option<NatLit> {
    let succ = Name::from_components(["Nat", "succ"]);
    let zero = Name::from_components(["Nat", "zero"]);
    let of_nat = Name::from_components(["OfNat", "ofNat"]);
    let mut successors = 0u64;
    let mut current = e.clone();
    let base = loop {
        if let ExprNode::Lit {
            literal: Literal::Nat(value),
        } = current.node()
        {
            break value.clone();
        }
        let mut args = Vec::new();
        let mut head = &current;
        while let ExprNode::App { f, a } = head.node() {
            args.push(a);
            head = f;
        }
        let ExprNode::Const { name, .. } = head.node() else {
            return None;
        };
        current = match args.len() {
            1 if name == &succ => {
                successors = successors.checked_add(1)?;
                args[0].clone()
            }
            // Arguments are last first: `OfNat.ofNat α n inst` holds `n` at 1.
            3 if name == &of_nat => args[1].clone(),
            0 if name == &zero => break NatLit::from_u64(0),
            _ => return None,
        };
    };
    if successors == 0 {
        return Some(base);
    }
    let sum = fln_bignum::nat::BigNatView::from_limbs_le(base.limbs_le())
        .add(fln_bignum::nat::BigNatView::from_limbs_le(&[successors]));
    Some(fln_bignum::interop::literal_from_bignat(&sum))
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::BinderInfo;
    use fln_core::level::Level;

    fn n(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }
    fn c(text: &str) -> Expr {
        Expr::const_(n(text), Vec::new())
    }
    fn app(f: Expr, args: &[Expr]) -> Expr {
        args.iter().cloned().fold(f, Expr::app)
    }
    fn lit(value: u64) -> Expr {
        Expr::lit(Literal::Nat(NatLit::from_u64(value)))
    }
    fn k(text: &str, arity: u32) -> Key {
        Key::Const(n(text), arity)
    }

    #[test]
    fn keys_order_as_the_pins_key_lt_with_star_least() {
        let mut keys = [
            Key::Proj(n("S"), 0, 0),
            Key::Arrow,
            k("Nat", 0),
            Key::FVar(FVarId(n("x")), 0),
            Key::Lit(Literal::Str("a".into())),
            Key::Lit(Literal::Nat(NatLit::from_u64(3))),
            Key::Other,
            Key::Star,
        ];
        keys.sort_by(|a, b| a.order(b));
        assert_eq!(keys[0], Key::Star);
        assert_eq!(keys[1], Key::Other);
        assert_eq!(keys[2], Key::Lit(Literal::Nat(NatLit::from_u64(3))));
        assert_eq!(keys[3], Key::Lit(Literal::Str("a".into())));
        assert_eq!(keys[7], Key::Proj(n("S"), 0, 0));
        assert_eq!(k("Nat", 0).order(&k("Nat", 1)), Ordering::Less);
        assert_eq!(k("Nat", 1).order(&k("Nat", 1)), Ordering::Equal);
    }

    #[test]
    fn the_journal_encoding_round_trips_and_refuses_noncanonical_literals() {
        let keys = vec![
            k("Decidable", 1),
            Key::Proj(n("Subtype"), 0, 0),
            Key::Lit(Literal::Nat(NatLit::from_limbs_le(vec![7, 9]))),
            Key::Lit(Literal::Nat(NatLit::from_u64(0))),
            Key::Lit(Literal::Str("é".into())),
            Key::FVar(FVarId(n("h")), 2),
            Key::Arrow,
            Key::Other,
            Key::Star,
        ];
        let mut bytes = Vec::new();
        write_keys(&keys, &mut bytes).unwrap();
        let mut cursor: &[u8] = &bytes;
        assert_eq!(read_keys(&mut cursor).unwrap(), keys);
        assert!(cursor.is_empty());
        // A natural with a trailing zero limb is not canonical.
        let mut forged = Vec::new();
        put32(1, &mut forged).unwrap();
        forged.extend([2, 0]);
        put32(1, &mut forged).unwrap();
        forged.extend(0u64.to_le_bytes());
        assert!(read_keys(&mut forged.as_slice()).is_err());
        for tag in [7u8, 200] {
            let mut unknown = Vec::new();
            put32(1, &mut unknown).unwrap();
            unknown.push(tag);
            assert!(read_keys(&mut unknown.as_slice()).is_err());
        }
        assert!(read_keys(&mut &bytes[..bytes.len() - 1]).is_err());
    }

    #[test]
    fn numerals_are_the_pins_four_shapes_and_nothing_else() {
        let of_nat = |value: Expr| app(c("OfNat.ofNat"), &[c("Nat"), value, c("instOfNatNat")]);
        assert_eq!(numeral(&lit(5)), Some(NatLit::from_u64(5)));
        assert_eq!(numeral(&of_nat(lit(5))), Some(NatLit::from_u64(5)));
        assert_eq!(numeral(&c("Nat.zero")), Some(NatLit::from_u64(0)));
        let succ = |e: Expr| app(c("Nat.succ"), &[e]);
        assert_eq!(
            numeral(&succ(succ(of_nat(lit(2))))),
            Some(NatLit::from_u64(4))
        );
        let big = Expr::lit(Literal::Nat(NatLit::from_u64(u64::MAX)));
        assert_eq!(numeral(&succ(big)), Some(NatLit::from_limbs_le(vec![0, 1])));
        assert_eq!(numeral(&succ(Expr::fvar(FVarId(n("x"))))), None);
        assert_eq!(numeral(&app(c("OfNat.ofNat"), &[c("Nat"), lit(5)])), None);
        assert_eq!(numeral(&Expr::lit(Literal::Str("5".into()))), None);
        assert_eq!(numeral(&Expr::mdata(Default::default(), lit(5))), None);
    }

    #[test]
    fn matcher_names_are_recognized_by_their_last_component() {
        assert!(is_matcher(&n("List.foo.match_1")));
        assert!(is_matcher(&n("match_12")));
        assert!(!is_matcher(&n("List.match_")));
        assert!(!is_matcher(&n("List.match_x")));
        assert!(!is_matcher(&n("matcher_1")));
    }

    fn index(paths: &[(&str, Vec<Key>)]) -> InstanceIndex {
        let mut index = InstanceIndex::default();
        for (name, keys) in paths {
            for key in &keys[1..] {
                if let Key::Const(name, _) = key {
                    index.folded.insert(name.clone());
                }
            }
            index.roots.insert(n(name), keys[0].clone());
            index.root.insert(keys, &n(name));
        }
        index
    }

    fn matched(
        index: &InstanceIndex,
        env: &Environment,
        lctx: &LocalContext,
        goal: &Expr,
    ) -> Vec<String> {
        let mut query = Query {
            env,
            lctx,
            folded: &index.folded,
            steps: MAX_STEPS,
        };
        let roots = query.keys(goal, true).unwrap();
        let mut names: Vec<String> = index
            .get_unify(&mut query, &roots)
            .unwrap()
            .into_iter()
            .map(|name| name.to_display_string())
            .collect();
        names.sort();
        names
    }

    fn base(name: &str) -> fln_env::constants::ConstantVal {
        fln_env::constants::ConstantVal {
            name: n(name),
            level_params: Vec::new(),
            type_: Expr::sort(Level::one()),
        }
    }
    fn axiom(name: &str) -> ConstantInfo {
        ConstantInfo::Axiom(fln_env::constants::AxiomVal {
            base: base(name),
            is_unsafe: false,
        })
    }
    fn definition(name: &str, value: Expr) -> ConstantInfo {
        ConstantInfo::Defn(fln_env::constants::DefinitionVal {
            base: base(name),
            value,
            hints: fln_env::constants::ReducibilityHints::Regular(1),
            safety: fln_env::constants::DefinitionSafety::Safe,
            all: vec![n(name)],
        })
    }
    fn lam(body: Expr) -> Expr {
        Expr::lam(n("a"), Expr::sort(Level::zero()), body, BinderInfo::Default)
    }
    fn bvar(index: u32) -> Expr {
        Expr::bvar(index).unwrap()
    }

    /// Hand-built paths in the pin's shape, and an environment in which `LT.lt`
    /// is a definition that the stored paths keep folded, `GT.gt` a definition
    /// they never mention (so possibly reducible), `Nat.lt` one with a
    /// smart-unfolding companion, and `f.match_1` a matcher.
    fn fixture() -> (InstanceIndex, Environment, LocalContext, FVarId, FVarId) {
        let zero = Key::Lit(Literal::Nat(NatLit::from_u64(0)));
        let index = index(&[
            (
                "decLt",
                vec![
                    k("Decidable", 1),
                    k("LT.lt", 4),
                    k("Nat", 0),
                    Key::Star,
                    Key::Star,
                    Key::Star,
                ],
            ),
            (
                "decLtAny",
                vec![
                    k("Decidable", 1),
                    k("LT.lt", 4),
                    Key::Star,
                    Key::Star,
                    Key::Star,
                    Key::Star,
                ],
            ),
            (
                "decLtFin",
                vec![
                    k("Decidable", 1),
                    k("LT.lt", 4),
                    k("Fin", 1),
                    Key::Star,
                    Key::Star,
                    Key::Star,
                    Key::Star,
                ],
            ),
            (
                "decLtZero",
                vec![
                    k("Decidable", 1),
                    k("LT.lt", 4),
                    k("Nat", 0),
                    Key::Star,
                    Key::Star,
                    zero,
                ],
            ),
            (
                "decEq",
                vec![
                    k("Decidable", 1),
                    k("Eq", 3),
                    k("Nat", 0),
                    Key::Star,
                    Key::Star,
                ],
            ),
            ("decAny", vec![k("Decidable", 1), Key::Star]),
            ("inhabited", vec![k("Inhabited", 1), Key::Star]),
        ]);
        let mut env = Environment::new();
        for name in ["Decidable", "Nat", "Fin", "Eq", "instLTNat", "Inhabited"] {
            env = env.add_decl(axiom(name)).unwrap();
        }
        // `fun α inst a b => LT.lt α inst b a`, and `LT.lt` itself, folded.
        let flip = lam(lam(lam(lam(app(
            c("LT.lt"),
            &[bvar(3), bvar(2), bvar(0), bvar(1)],
        )))));
        let opaque_body = lam(lam(lam(lam(c("Nat")))));
        for decl in [
            definition("LT.lt", opaque_body.clone()),
            definition("GT.gt", flip),
            definition("Nat.lt", opaque_body.clone()),
            definition("Nat.lt._sunfold", opaque_body.clone()),
            definition("f.match_1", opaque_body),
        ] {
            env = env.add_decl(decl).unwrap();
        }
        let (x, y) = (FVarId(n("x")), FVarId(n("y")));
        let mut lctx = LocalContext::new();
        lctx.add_param(x.clone(), n("x"), c("Nat"), BinderInfo::Default);
        lctx.add_let(y.clone(), n("y"), c("Nat"), lit(0));
        (index, env, lctx, x, y)
    }

    #[test]
    fn get_unify_follows_stars_on_both_sides_and_skips_by_arity() {
        let (index, env, lctx, x, y) = fixture();
        let lt = |a: Expr, b: Expr| app(c("LT.lt"), &[c("Nat"), c("instLTNat"), a, b]);
        let decidable = |p: Expr| app(c("Decidable"), &[p]);
        let goal = decidable(lt(Expr::fvar(x.clone()), lit(5)));
        assert_eq!(
            matched(&index, &env, &lctx, &goal),
            ["decAny", "decLt", "decLtAny"]
        );
        // A literal meets an equal stored literal.
        let goal = decidable(lt(Expr::fvar(x.clone()), lit(0)));
        assert_eq!(
            matched(&index, &env, &lctx, &goal),
            ["decAny", "decLt", "decLtAny", "decLtZero"]
        );
        // A metavariable is a star, which crosses each stored subterm by arity.
        let hole = Expr::mvar(fln_core::expr::MVarId(n("m")));
        let goal = decidable(app(
            c("LT.lt"),
            &[hole.clone(), c("instLTNat"), lit(1), lit(2)],
        ));
        assert_eq!(
            matched(&index, &env, &lctx, &goal),
            ["decAny", "decLt", "decLtAny", "decLtFin"]
        );
        assert_eq!(
            matched(&index, &env, &lctx, &decidable(hole)),
            [
                "decAny",
                "decEq",
                "decLt",
                "decLtAny",
                "decLtFin",
                "decLtZero"
            ]
        );
        // A let-bound variable may reduce, so it is a star.
        let goal = decidable(lt(Expr::fvar(x.clone()), Expr::fvar(y)));
        assert_eq!(
            matched(&index, &env, &lctx, &goal),
            ["decAny", "decLt", "decLtAny", "decLtZero"]
        );
        // `GT.gt` is never kept folded, so its unfolding is queried too:
        // `x > 0` is `0 < x`, which `decLtZero` (`_ < 0`) cannot match.
        let gt = app(
            c("GT.gt"),
            &[c("Nat"), c("instLTNat"), Expr::fvar(x.clone()), lit(0)],
        );
        assert_eq!(
            matched(&index, &env, &lctx, &decidable(gt)),
            ["decAny", "decLt", "decLtAny"]
        );
        // A smart-unfolded definition and a matcher are stars.
        for head in ["Nat.lt", "f.match_1"] {
            let goal = decidable(app(c(head), &[c("Nat"), c("instLTNat"), lit(1), lit(2)]));
            assert_eq!(matched(&index, &env, &lctx, &goal).len(), 6, "{head}");
        }
        // An unknown constant, an unknown free variable and a projection too.
        for p in [
            c("Unknown"),
            Expr::fvar(FVarId(n("z"))),
            Expr::proj(n("S"), 0, Expr::fvar(x.clone())),
        ] {
            assert_eq!(matched(&index, &env, &lctx, &decidable(p)).len(), 6);
        }
        // A sort is `other`, which only a star stores.
        let goal = decidable(Expr::sort(Level::zero()));
        assert_eq!(matched(&index, &env, &lctx, &goal), ["decAny"]);
    }

    /// `OfNat.ofNat Nat 5 inst` in argument position is the literal `5`, as the
    /// pin's `toNatLit?` keys it, even though `OfNat.ofNat` has no recorded status
    /// here. Its unfolding (a projection, so a star) is not queried: the pin's
    /// `OfNat.ofNat` is semireducible, so its `reduce` never unfolds a numeral
    /// (bead fln-eeew). `decLtZero` (`_ < 0`) is therefore not a match.
    #[test]
    fn an_ofnat_numeral_is_its_literal_whatever_its_unrecorded_status() {
        let (index, env, lctx, x, _) = fixture();
        let projection = lam(lam(lam(Expr::proj(n("OfNat"), 0, bvar(0)))));
        let env = env
            .add_decl(definition("OfNat.ofNat", projection))
            .unwrap()
            .add_decl(axiom("instOfNatNat"))
            .unwrap();
        let numeral = |value: u64| {
            app(
                c("OfNat.ofNat"),
                &[c("Nat"), lit(value), app(c("instOfNatNat"), &[lit(value)])],
            )
        };
        let goal = |value: u64| {
            app(
                c("Decidable"),
                &[app(
                    c("LT.lt"),
                    &[
                        c("Nat"),
                        c("instLTNat"),
                        Expr::fvar(x.clone()),
                        numeral(value),
                    ],
                )],
            )
        };
        assert_eq!(
            matched(&index, &env, &lctx, &goal(5)),
            ["decAny", "decLt", "decLtAny"]
        );
        assert_eq!(
            matched(&index, &env, &lctx, &goal(0)),
            ["decAny", "decLt", "decLtAny", "decLtZero"]
        );
    }

    /// `getUnify`'s matches in the pin's traversal order, unsorted.
    fn traversal(
        index: &InstanceIndex,
        env: &Environment,
        lctx: &LocalContext,
        goal: &Expr,
    ) -> Vec<String> {
        let mut query = Query {
            env,
            lctx,
            folded: &index.folded,
            steps: MAX_STEPS,
        };
        let roots = query.keys(goal, true).unwrap();
        index
            .get_unify(&mut query, &roots)
            .unwrap()
            .iter()
            .map(Name::to_display_string)
            .collect()
    }

    #[test]
    fn get_unify_visits_the_star_child_first_and_a_leaf_in_insertion_order() {
        // Values sharing a leaf stay in the order they were inserted.
        let path = vec![k("Inhabited", 1), k("Nat", 0)];
        let shared = index(&[("second", path.clone()), ("first", path)]);
        let (index, env, lctx, x, _) = fixture();
        let lt = |a: Expr, b: Expr| app(c("LT.lt"), &[c("Nat"), c("instLTNat"), a, b]);
        let decidable = |p: Expr| app(c("Decidable"), &[p]);
        // `decAny` is the `Decidable` node's star child; `decLtAny` the star
        // child at the `Nat` position, ahead of `decLt` under `Nat` itself.
        assert_eq!(
            traversal(
                &index,
                &env,
                &lctx,
                &decidable(lt(Expr::fvar(x.clone()), lit(5)))
            ),
            ["decAny", "decLtAny", "decLt"]
        );
        // At the last argument the star (`decLt`) precedes the literal `0`.
        assert_eq!(
            traversal(&index, &env, &lctx, &decidable(lt(Expr::fvar(x), lit(0)))),
            ["decAny", "decLtAny", "decLt", "decLtZero"]
        );
        assert_eq!(
            traversal(&shared, &env, &lctx, &app(c("Inhabited"), &[c("Nat")])),
            ["second", "first"]
        );
    }

    #[test]
    fn narrow_returns_the_pins_try_order_with_unindexed_rows_first_in_their_priority() {
        let (index, env, lctx, x, _) = fixture();
        let row = |name: &str, priority: u32, order: usize| InstanceEntry {
            declaration: n(name),
            priority,
            order,
        };
        let goal = app(
            c("Decidable"),
            &[app(
                c("LT.lt"),
                &[c("Nat"), c("instLTNat"), Expr::fvar(x), lit(5)],
            )],
        );
        let kept = |rows: &[InstanceEntry]| -> Vec<String> {
            index
                .narrow(&env, &lctx, &goal, rows)
                .into_iter()
                .map(|row| row.declaration.to_display_string())
                .collect()
        };
        // Equal priorities: the rows the index cannot place (`native` has no
        // path, `inhabited` is rooted elsewhere) in their given order, then the
        // traversal `decAny`, `decLt` from its end.
        let rows = [
            row("decLtFin", 1000, 0),
            row("native", 1000, 1),
            row("decLt", 1000, 2),
            row("inhabited", 1000, 3),
            row("decEq", 1000, 4),
            row("decAny", 1000, 5),
        ];
        assert_eq!(kept(&rows), ["native", "inhabited", "decLt", "decAny"]);
        // Priority comes first, placed or not.
        let rows = [
            row("decAny", 2000, 0),
            row("native", 1000, 1),
            row("decLt", 1000, 2),
            row("low", 10, 3),
        ];
        assert_eq!(kept(&rows), ["decAny", "native", "decLt", "low"]);
        // Out of steps, nothing is filtered.
        let mut query = Query {
            env: &env,
            lctx: &lctx,
            folded: &index.folded,
            steps: 3,
        };
        let roots = query.keys(&goal, true).unwrap();
        assert!(index.get_unify(&mut query, &roots).is_none());
    }
}
