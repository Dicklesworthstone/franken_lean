//! Universe metavariable store (`UniverseStore`) for Athanor (plan §10.1).
//!
//! Assignment maps are untrusted elaboration input. Instantiation checks their
//! reachable graph for cycles, preserves typed resource stops, and traverses
//! levels and complete expression DAGs without recursive host-stack growth.

pub mod parameters;

#[cfg(test)]
mod simplification_tests;

use fln_core::expr::{Expr, ExprNode};
use fln_core::level::{LMVarId, Level, LevelTooDeep, LevelView};
use std::collections::{HashMap, HashSet};

/// Default work bound for one universe-instantiation request. Callers with a
/// different elaboration budget can use the explicit-limit entry points.
pub const DEFAULT_UNIVERSE_VISIT_LIMIT: usize = 1_000_000;

/// A malformed assignment graph or a typed resource stop, not a typing verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UniverseInstantiationError {
    CyclicAssignment { uvar: LMVarId },
    VisitLimit { limit: usize },
    LevelTooDeep(LevelTooDeep),
}

/// `(base, k)` with `level = succ^k base` and `base` not a successor.
/// Inspecting an assigned, otherwise skipped successor chain spends the same
/// request budget as instantiating it would; there is no unmetered peel loop.
fn level_offset<'a>(
    level: &'a Level,
    remaining: &mut usize,
    limit: usize,
) -> Result<(&'a Level, u32), UniverseInstantiationError> {
    let mut base = level;
    let mut offset = 0u32;
    loop {
        visit(remaining, limit)?;
        match base.view() {
            LevelView::Succ(inner) => {
                base = inner;
                offset = offset.saturating_add(1);
            }
            _ => return Ok((base, offset)),
        }
    }
}

/// Cheap identity through the public borrowed view. A clone of a compound
/// level returns the very same child references; leaves expose their stored
/// name/id by reference. No structural walk or allocation is needed here.
fn shared_level_root(left: &Level, right: &Level) -> bool {
    if std::ptr::eq(left, right) {
        return true;
    }
    match (left.view(), right.view()) {
        (LevelView::Zero, LevelView::Zero) => true,
        (LevelView::Succ(a), LevelView::Succ(b)) => std::ptr::eq(a, b),
        (LevelView::Max(a1, a2), LevelView::Max(b1, b2))
        | (LevelView::IMax(a1, a2), LevelView::IMax(b1, b2)) => {
            std::ptr::eq(a1, b1) && std::ptr::eq(a2, b2)
        }
        (LevelView::Param(a), LevelView::Param(b)) => std::ptr::eq(a, b),
        (LevelView::MVar(a), LevelView::MVar(b)) => std::ptr::eq(a, b),
        _ => false,
    }
}

/// Structural equality for smart-constructor decisions, not definitional
/// equality or normalization. Core's `Level::eq` is DAG-aware and stack-safe,
/// but it has no caller budget. Invoking it on skipped, mvar-free assignments
/// here would let their entire graphs be compared outside the request limit.
///
/// Only allocation PAIRS are memoized, never hashes or one side alone. The
/// immutable roots pin both graphs throughout this call. Child-reference
/// identity preserves constant-time comparison of cloned compound levels
/// without exposing the core's private `Arc` representation.
fn equal_levels(
    left: &Level,
    right: &Level,
    remaining: &mut usize,
    limit: usize,
) -> Result<bool, UniverseInstantiationError> {
    // The overwhelmingly common unchanged/obviously different cases must
    // not allocate a worklist or memo table just to charge a single pair.
    if left.data() != right.data() {
        visit(remaining, limit)?;
        return Ok(false);
    }
    if shared_level_root(left, right) {
        visit(remaining, limit)?;
        return Ok(true);
    }
    let mut visited = HashSet::new();
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        let pair = (std::ptr::from_ref(left), std::ptr::from_ref(right));
        if visited.contains(&pair) {
            continue;
        }
        visit(remaining, limit)?;
        visited.insert(pair);
        if left.data() != right.data() {
            return Ok(false);
        }
        if std::ptr::eq(left, right) {
            continue;
        }
        match (left.view(), right.view()) {
            (LevelView::Zero, LevelView::Zero) => {}
            (LevelView::Succ(a), LevelView::Succ(b)) => {
                if !std::ptr::eq(a, b) {
                    pending.push((a, b));
                }
            }
            (LevelView::Max(a1, a2), LevelView::Max(b1, b2))
            | (LevelView::IMax(a1, a2), LevelView::IMax(b1, b2)) => {
                if !std::ptr::eq(a2, b2) {
                    pending.push((a2, b2));
                }
                if !std::ptr::eq(a1, b1) {
                    pending.push((a1, b1));
                }
            }
            (LevelView::Param(a), LevelView::Param(b)) if a == b => {}
            (LevelView::MVar(a), LevelView::MVar(b)) if a == b => {}
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn is_zero_level(level: &Level) -> bool {
    matches!(level.view(), LevelView::Zero)
}

/// The pin's `is_not_zero` (kernel/level.cpp), under the caller's work budget.
///
/// A mvar-free branch was deliberately not expanded by instantiation. Looking
/// inside it here must not bypass that operation's resource limit or turn its
/// shared DAG into a recursive, exponentially large tree walk. The borrowed
/// root pins every address until this call returns; no memo key escapes it.
fn is_never_zero(
    level: &Level,
    remaining: &mut usize,
    limit: usize,
) -> Result<bool, UniverseInstantiationError> {
    let mut visited = HashSet::new();
    let mut pending = vec![level];
    while let Some(current) = pending.pop() {
        let key = std::ptr::from_ref(current);
        if visited.contains(&key) {
            continue;
        }
        visit(remaining, limit)?;
        visited.insert(key);
        match current.view() {
            LevelView::Succ(_) => return Ok(true),
            LevelView::Max(left, right) => {
                // Match the pin's left-to-right short circuit.
                pending.push(right);
                pending.push(left);
            }
            LevelView::IMax(_, right) => pending.push(right),
            LevelView::Zero | LevelView::Param(_) | LevelView::MVar(_) => {}
        }
    }
    Ok(false)
}

/// The pin's `mk_max` (kernel/level.cpp:81): cheap simplifications only.
fn pin_mk_max(
    l1: Level,
    l2: Level,
    remaining: &mut usize,
    limit: usize,
) -> Result<Level, UniverseInstantiationError> {
    let (base1, k1) = level_offset(&l1, remaining, limit)?;
    let (base2, k2) = level_offset(&l2, remaining, limit)?;
    if is_zero_level(base1) && is_zero_level(base2) {
        return Ok(if k1 >= k2 { l1 } else { l2 });
    }
    if equal_levels(&l1, &l2, remaining, limit)? || is_zero_level(&l2) {
        return Ok(l1);
    }
    if is_zero_level(&l1) {
        return Ok(l2);
    }
    if let LevelView::Max(left, right) = l2.view()
        && (equal_levels(left, &l1, remaining, limit)?
            || equal_levels(right, &l1, remaining, limit)?)
    {
        return Ok(l2);
    }
    if let LevelView::Max(left, right) = l1.view()
        && (equal_levels(left, &l2, remaining, limit)?
            || equal_levels(right, &l2, remaining, limit)?)
    {
        return Ok(l1);
    }
    if equal_levels(base1, base2, remaining, limit)? {
        return Ok(if k1 > k2 { l1 } else { l2 });
    }
    Ok(Level::max(l1, l2)?)
}

/// The pin's `mk_imax` (kernel/level.cpp:112).
fn pin_mk_imax(
    l1: Level,
    l2: Level,
    remaining: &mut usize,
    limit: usize,
) -> Result<Level, UniverseInstantiationError> {
    if is_never_zero(&l2, remaining, limit)? {
        return pin_mk_max(l1, l2, remaining, limit);
    }
    let one = matches!(l1.view(), LevelView::Succ(inner) if is_zero_level(inner));
    if is_zero_level(&l2) || is_zero_level(&l1) || one {
        return Ok(l2);
    }
    if equal_levels(&l1, &l2, remaining, limit)? {
        return Ok(l1);
    }
    Ok(Level::imax(l1, l2)?)
}

impl std::fmt::Display for UniverseInstantiationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CyclicAssignment { uvar } => write!(
                f,
                "cyclic universe assignment at ?{}",
                uvar.0.to_display_string()
            ),
            Self::VisitLimit { limit } => {
                write!(f, "universe instantiation exceeded {limit} visited nodes")
            }
            Self::LevelTooDeep(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for UniverseInstantiationError {}

impl From<LevelTooDeep> for UniverseInstantiationError {
    fn from(error: LevelTooDeep) -> Self {
        Self::LevelTooDeep(error)
    }
}

fn visit(remaining: &mut usize, limit: usize) -> Result<(), UniverseInstantiationError> {
    *remaining = remaining
        .checked_sub(1)
        .ok_or(UniverseInstantiationError::VisitLimit { limit })?;
    Ok(())
}

/// Tracks universe metavariable assignments and instantiation.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct UniverseStore {
    assignments: HashMap<LMVarId, Level>,
}

impl UniverseStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.assignments.is_empty()
    }

    pub fn len(&self) -> usize {
        self.assignments.len()
    }

    pub fn is_assigned(&self, uvar: &LMVarId) -> bool {
        self.assignments.contains_key(uvar)
    }

    pub fn get_assignment(&self, uvar: &LMVarId) -> Option<&Level> {
        self.assignments.get(uvar)
    }

    /// Replace one raw assignment, returning its old value. This is a mutable
    /// candidate store, not an admission gate: instantiation validates the
    /// reachable assignment graph and reports cycles explicitly.
    pub fn assign(&mut self, uvar: LMVarId, level: Level) -> Option<Level> {
        self.assignments.insert(uvar, level)
    }

    pub fn remove(&mut self, uvar: &LMVarId) -> Option<Level> {
        self.assignments.remove(uvar)
    }

    pub fn assignments(&self) -> &HashMap<LMVarId, Level> {
        &self.assignments
    }

    pub fn instantiate(&self, level: &Level) -> Result<Level, UniverseInstantiationError> {
        self.instantiate_with_limit(level, DEFAULT_UNIVERSE_VISIT_LIMIT)
    }

    /// Expand the reachable graph under an explicit work budget. It covers
    /// instantiation visits and smart-constructor inspections: successor peeling,
    /// nonzero queries, and structural comparison pairs. These can inspect
    /// mvar-free branches that instantiation itself skips. Each helper charges
    /// its own work, including repeated inspections across helper calls.
    ///
    /// Cycles and exhaustion are different errors; neither changes any stored
    /// assignment. Cheap returns for an empty store or mvar-free root remain free.
    pub fn instantiate_with_limit(
        &self,
        level: &Level,
        max_nodes: usize,
    ) -> Result<Level, UniverseInstantiationError> {
        let mut remaining = max_nodes;
        self.instantiate_level(level, &mut HashMap::new(), &mut remaining, max_nodes)
    }

    fn instantiate_level(
        &self,
        level: &Level,
        done: &mut HashMap<*const Level, Level>,
        remaining: &mut usize,
        limit: usize,
    ) -> Result<Level, UniverseInstantiationError> {
        if self.assignments.is_empty() || !level.has_mvar() {
            return Ok(level.clone());
        }
        let mut active = HashSet::new();
        let mut pending = vec![(level, false)];
        while let Some((current, exit)) = pending.pop() {
            let key = std::ptr::from_ref(current);
            if done.contains_key(&key) {
                continue;
            }
            if !exit {
                visit(remaining, limit)?;
                if !current.has_mvar() {
                    done.insert(key, current.clone());
                    continue;
                }
                pending.push((current, true));
                match current.view() {
                    LevelView::MVar(id) => {
                        if let Some(assigned) = self.assignments.get(id) {
                            if !active.insert(id.clone()) {
                                return Err(UniverseInstantiationError::CyclicAssignment {
                                    uvar: id.clone(),
                                });
                            }
                            pending.push((assigned, false));
                        }
                    }
                    LevelView::Succ(inner) => pending.push((inner, false)),
                    LevelView::Max(left, right) | LevelView::IMax(left, right) => {
                        pending.push((right, false));
                        pending.push((left, false));
                    }
                    LevelView::Zero | LevelView::Param(_) => {}
                }
                continue;
            }
            let child = |input: &Level| {
                done.get(&std::ptr::from_ref(input))
                    .expect("universe postorder finishes children first")
                    .clone()
            };
            let result = match current.view() {
                LevelView::MVar(id) => {
                    if let Some(assigned) = self.assignments.get(id) {
                        active.remove(id);
                        child(assigned)
                    } else {
                        current.clone()
                    }
                }
                LevelView::Succ(inner) => child(inner).succ()?,
                // The pin's `instantiate_mvars` rebuilds a changed `max`/`imax`
                // with `update_max` (kernel/level.cpp:293), which simplifies.
                LevelView::Max(left, right) | LevelView::IMax(left, right) => {
                    let (new_left, new_right) = (child(left), child(right));
                    if equal_levels(&new_left, left, remaining, limit)?
                        && equal_levels(&new_right, right, remaining, limit)?
                    {
                        current.clone()
                    } else if matches!(current.view(), LevelView::Max(..)) {
                        pin_mk_max(new_left, new_right, remaining, limit)?
                    } else {
                        pin_mk_imax(new_left, new_right, remaining, limit)?
                    }
                }
                LevelView::Zero | LevelView::Param(_) => current.clone(),
            };
            done.insert(key, result);
        }
        Ok(done
            .get(&std::ptr::from_ref(level))
            .expect("universe postorder finishes the root")
            .clone())
    }

    /// Instantiate universe metavariables in every Sort and Const in an
    /// expression. Expression metavariables are deliberately not assigned here;
    /// compose with `MetavarStore::instantiate` when both stores are in play.
    pub fn instantiate_expr(&self, expr: &Expr) -> Result<Expr, UniverseInstantiationError> {
        self.instantiate_expr_with_limit(expr, DEFAULT_UNIVERSE_VISIT_LIMIT)
    }

    /// The shared budget covers expression and level visits, including the
    /// level smart-constructor work described by [`Self::instantiate_with_limit`].
    /// Memo keys are request-local allocation identities, never semantic or
    /// serialized identities. The borrowed input and store pin all key owners.
    #[allow(clippy::too_many_lines)]
    pub fn instantiate_expr_with_limit(
        &self,
        expr: &Expr,
        max_nodes: usize,
    ) -> Result<Expr, UniverseInstantiationError> {
        if self.assignments.is_empty() || !expr.has_level_mvar() {
            return Ok(expr.clone());
        }
        let mut done: HashMap<*const ExprNode, Expr> = HashMap::new();
        let mut level_done = HashMap::new();
        let mut remaining = max_nodes;
        let mut pending = vec![(expr, false)];
        while let Some((current, exit)) = pending.pop() {
            let key = std::ptr::from_ref(current.node());
            if done.contains_key(&key) {
                continue;
            }
            if !exit {
                visit(&mut remaining, max_nodes)?;
                if !current.has_level_mvar() {
                    done.insert(key, current.clone());
                    continue;
                }
                pending.push((current, true));
                match current.node() {
                    ExprNode::App { f, a } => {
                        pending.push((a, false));
                        pending.push((f, false));
                    }
                    ExprNode::Lam {
                        binder_type, body, ..
                    }
                    | ExprNode::ForallE {
                        binder_type, body, ..
                    } => {
                        pending.push((body, false));
                        pending.push((binder_type, false));
                    }
                    ExprNode::LetE {
                        type_, value, body, ..
                    } => {
                        pending.push((body, false));
                        pending.push((value, false));
                        pending.push((type_, false));
                    }
                    ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                        pending.push((expr, false));
                    }
                    ExprNode::BVar { .. }
                    | ExprNode::FVar { .. }
                    | ExprNode::MVar { .. }
                    | ExprNode::Sort { .. }
                    | ExprNode::Const { .. }
                    | ExprNode::Lit { .. } => {}
                }
                continue;
            }
            let child = |input: &Expr| {
                done.get(&std::ptr::from_ref(input.node()))
                    .expect("expression postorder finishes children first")
                    .clone()
            };
            let result = match current.node() {
                ExprNode::Sort { level } => Expr::sort(self.instantiate_level(
                    level,
                    &mut level_done,
                    &mut remaining,
                    max_nodes,
                )?),
                ExprNode::Const { name, levels } => {
                    let levels = levels
                        .iter()
                        .map(|level| {
                            self.instantiate_level(
                                level,
                                &mut level_done,
                                &mut remaining,
                                max_nodes,
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    Expr::const_(name.clone(), levels)
                }
                ExprNode::App { f, a } => Expr::app(child(f), child(a)),
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::lam(
                    binder_name.clone(),
                    child(binder_type),
                    child(body),
                    *binder_info,
                ),
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::forall_e(
                    binder_name.clone(),
                    child(binder_type),
                    child(body),
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
                    child(type_),
                    child(value),
                    child(body),
                    *non_dep,
                ),
                ExprNode::MData { data, expr } => Expr::mdata(data.clone(), child(expr)),
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => Expr::proj(struct_name.clone(), *idx, child(expr)),
                ExprNode::BVar { .. }
                | ExprNode::FVar { .. }
                | ExprNode::MVar { .. }
                | ExprNode::Lit { .. } => current.clone(),
            };
            done.insert(key, result);
        }
        Ok(done
            .remove(&std::ptr::from_ref(expr.node()))
            .expect("expression postorder finishes the root"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::{BinderInfo, MVarId};
    use fln_core::name::Name;
    use fln_core::options::KVMap;

    fn uvar(name: &str) -> LMVarId {
        LMVarId(Name::from_components([name]))
    }

    #[test]
    fn a_direct_cycle_is_a_typed_error_not_recursive_expansion() {
        let u = uvar("u");
        let mut store = UniverseStore::new();
        store.assign(u.clone(), Level::mvar(u.clone()));
        assert_eq!(
            store.instantiate(&Level::mvar(u.clone())),
            Err(UniverseInstantiationError::CyclicAssignment { uvar: u }),
        );
    }

    #[test]
    fn indirect_cycles_are_reported_and_removal_restores_instantiation() {
        let u = uvar("u");
        let v = uvar("v");
        let mut store = UniverseStore::new();
        store.assign(u.clone(), Level::mvar(v.clone()).succ().unwrap());
        store.assign(v.clone(), Level::mvar(u.clone()));
        let before = store.clone();
        assert!(matches!(
            store.instantiate(&Level::mvar(u.clone())),
            Err(UniverseInstantiationError::CyclicAssignment { .. }),
        ));
        assert_eq!(store, before);
        store.remove(&v);
        assert_eq!(
            store.instantiate(&Level::mvar(u)).unwrap(),
            Level::mvar(v).succ().unwrap(),
        );
    }

    #[test]
    fn an_unreachable_cycle_does_not_poison_an_unrelated_level() {
        let bad = uvar("bad");
        let good = uvar("good");
        let mut store = UniverseStore::new();
        store.assign(bad.clone(), Level::mvar(bad));
        store.assign(good.clone(), Level::one());
        assert_eq!(store.instantiate(&Level::mvar(good)).unwrap(), Level::one());
        assert_eq!(
            store.instantiate_with_limit(&Level::zero(), 0).unwrap(),
            Level::zero()
        );
    }

    #[test]
    fn visit_exhaustion_is_distinct_and_does_not_mutate_assignments() {
        let u = uvar("u");
        let mut store = UniverseStore::new();
        store.assign(u.clone(), Level::one());
        let input = Level::mvar(u).succ().unwrap();
        let before = store.clone();
        assert_eq!(
            store.instantiate_with_limit(&input, 1),
            Err(UniverseInstantiationError::VisitLimit { limit: 1 }),
        );
        assert_eq!(store, before);
        assert_eq!(
            store.instantiate_with_limit(&input, 8).unwrap(),
            Level::one().succ().unwrap()
        );
    }

    #[test]
    fn expression_instantiation_covers_levels_in_every_container() {
        let u = uvar("u");
        let name = Name::from_components(["x"]);
        let build = |level: Level| {
            let sort = Expr::sort(level.clone());
            Expr::let_e(
                name.clone(),
                sort.clone(),
                Expr::lam(
                    name.clone(),
                    sort.clone(),
                    Expr::app(
                        Expr::const_(name.clone(), vec![level]),
                        Expr::bvar(0).unwrap(),
                    ),
                    BinderInfo::Implicit,
                ),
                Expr::forall_e(
                    name.clone(),
                    sort.clone(),
                    Expr::proj(name.clone(), 1, Expr::mdata(KVMap::new(), sort)),
                    BinderInfo::InstImplicit,
                ),
                false,
            )
        };
        let mut store = UniverseStore::new();
        store.assign(u.clone(), Level::one());
        assert_eq!(
            store.instantiate_expr(&build(Level::mvar(u))).unwrap(),
            build(Level::one())
        );
    }

    #[test]
    fn expression_metavariables_are_not_universe_assignments() {
        let u = uvar("u");
        let mut store = UniverseStore::new();
        store.assign(u.clone(), Level::one());
        let expr_mvar = Expr::mvar(MVarId(u.0.clone()));
        let input = Expr::app(Expr::sort(Level::mvar(u)), expr_mvar.clone());
        assert_eq!(
            store.instantiate_expr(&input).unwrap(),
            Expr::app(Expr::sort(Level::one()), expr_mvar),
        );
    }

    #[test]
    fn expression_and_level_work_share_the_same_budget() {
        let u = uvar("u");
        let mut store = UniverseStore::new();
        store.assign(u.clone(), Level::one());
        let input = Expr::sort(Level::mvar(u));
        assert_eq!(
            store.instantiate_expr_with_limit(&input, 1),
            Err(UniverseInstantiationError::VisitLimit { limit: 1 }),
        );
        assert_eq!(
            store.instantiate_expr_with_limit(&input, 8).unwrap(),
            Expr::sort(Level::one())
        );
    }

    #[test]
    fn long_alias_chains_fit_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let mut store = UniverseStore::new();
                let mut previous = uvar("root");
                let root = Level::mvar(previous.clone());
                for i in 0..20_000 {
                    let next = uvar(&format!("u{i}"));
                    store.assign(previous, Level::mvar(next.clone()));
                    previous = next;
                }
                store.assign(previous, Level::one());
                assert_eq!(store.instantiate(&root).unwrap(), Level::one());
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
