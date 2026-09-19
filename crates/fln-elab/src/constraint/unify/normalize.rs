//! Budgeted universe normalization for native constraint solving.
//!
//! Normalize max/successor expressions as a sorted maximum of atoms plus
//! offsets. Equal atoms keep their largest offset; an explicit numeral drops
//! only when another atom's offset dominates it. IMax distributes over maxima
//! on either side and nested right guards, retaining the zero case rather than
//! assuming an unknown universe is positive. Remaining IMax atoms have a
//! parameter or metavariable as their right guard. This is
//! a sufficient conversion procedure, not complete universe constraint solving
//! and not the Reference-observable `Level.normalize` API.
//!
//! Every input walk, comparison, generated cell and successor is metered.
//! Shared input DAGs and normal forms retain sharing; neither comparison nor
//! normalization recurses on the host stack. No expression/universe assignment
//! is made here, including when an IMax condition is still unknown.
use super::*;
use fln_core::name::LeafView;
use std::cmp::Ordering;
use std::sync::Arc;

#[derive(Clone)]
struct Term {
    atom: Level,
    offset: u32,
}
type Form = Arc<[Term]>;

fn rank(level: &Level) -> u8 {
    match level.view() {
        LevelView::Zero => 0,
        LevelView::Param(_) => 1,
        LevelView::MVar(_) => 2,
        LevelView::IMax(..) => 3,
        LevelView::Succ(_) => 4,
        LevelView::Max(..) => 5,
    }
}

/// A stable structural order, independent of allocation and hash-map iteration.
/// Cached hashes are only ordering accelerators: collisions compare structure.
fn compare_names(a: &Name, b: &Name, meter: &mut Meter<'_>) -> Result<Ordering, UnificationError> {
    let (mut a, mut b) = (a.clone(), b.clone());
    loop {
        meter.node()?;
        let order = a.hash().cmp(&b.hash());
        if order != Ordering::Equal {
            return Ok(order);
        }
        let leaf_rank = |leaf| -> u8 { match leaf {
            LeafView::Anonymous => 0,
            LeafView::Str(_) => 1,
            LeafView::Num(_) => 2,
        }};
        let order = leaf_rank(a.leaf_view()).cmp(&leaf_rank(b.leaf_view()));
        if order != Ordering::Equal {
            return Ok(order);
        }
        match (a.leaf_view(), b.leaf_view()) {
            (LeafView::Anonymous, LeafView::Anonymous) => return Ok(Ordering::Equal),
            (LeafView::Str(x), LeafView::Str(y)) => {
                // Length-first order avoids an unmetered library string walk.
                let order = x.len().cmp(&y.len());
                if order != Ordering::Equal {
                    return Ok(order);
                }
                for (x, y) in x.bytes().zip(y.bytes()) {
                    meter.node()?;
                    let order = x.cmp(&y);
                    if order != Ordering::Equal {
                        return Ok(order);
                    }
                }
            }
            (LeafView::Num(x), LeafView::Num(y)) => {
                let order = (x, a.component_overflowed()).cmp(&(y, b.component_overflowed()));
                if order != Ordering::Equal {
                    return Ok(order);
                }
            }
            _ => unreachable!("equal leaf ranks have the same constructor"),
        }
        a = a.parent();
        b = b.parent();
    }
}

fn compare_atoms(a: &Level, b: &Level, meter: &mut Meter<'_>) -> Result<Ordering, UnificationError> {
    let mut pending = vec![(a, b)];
    let mut seen = HashSet::new();
    while let Some((a, b)) = pending.pop() {
        if !seen.insert((std::ptr::from_ref(a), std::ptr::from_ref(b))) {
            continue;
        }
        meter.node()?;
        let order = (rank(a), a.hash()).cmp(&(rank(b), b.hash()));
        if order != Ordering::Equal {
            return Ok(order);
        }
        match (a.view(), b.view()) {
            (LevelView::Zero, LevelView::Zero) => {}
            (LevelView::Param(a), LevelView::Param(b)) => {
                let order = compare_names(a, b, meter)?;
                if order != Ordering::Equal {
                    return Ok(order);
                }
            }
            (LevelView::MVar(a), LevelView::MVar(b)) => {
                let order = compare_names(&a.0, &b.0, meter)?;
                if order != Ordering::Equal {
                    return Ok(order);
                }
            }
            (LevelView::Succ(a), LevelView::Succ(b)) => pending.push((a, b)),
            (LevelView::Max(a, b), LevelView::Max(c, d))
            | (LevelView::IMax(a, b), LevelView::IMax(c, d)) => {
                pending.push((b, d));
                pending.push((a, c));
            }
            _ => unreachable!("equal ranks have the same level constructor"),
        }
    }
    Ok(Ordering::Equal)
}

fn singleton(atom: Level, offset: u32, meter: &mut Meter<'_>) -> Result<Form, UnificationError> {
    meter.node()?;
    Ok(Arc::from([Term { atom, offset }]))
}

fn equal_forms(a: &Form, b: &Form, meter: &mut Meter<'_>) -> Result<bool, UnificationError> {
    if Arc::ptr_eq(a, b) {
        return Ok(true);
    }
    if a.len() != b.len() {
        return Ok(false);
    }
    for (a, b) in a.iter().zip(b.iter()) {
        meter.node()?;
        if a.offset != b.offset || compare_atoms(&a.atom, &b.atom, meter)? != Ordering::Equal {
            return Ok(false);
        }
    }
    Ok(true)
}

fn maximum(a: &Form, b: &Form, meter: &mut Meter<'_>) -> Result<Form, UnificationError> {
    if a.is_empty() || Arc::ptr_eq(a, b) {
        return Ok(Arc::clone(b));
    }
    if b.is_empty() {
        return Ok(Arc::clone(a));
    }
    let mut out = Vec::new();
    let (mut i, mut j) = (0, 0);
    let mut largest_nonconstant_offset: Option<u32> = None;
    while i < a.len() || j < b.len() {
        meter.node()?;
        let next = if i == a.len() {
            let next = b[j].clone();
            j += 1;
            next
        } else if j == b.len() {
            let next = a[i].clone();
            i += 1;
            next
        } else {
            match compare_atoms(&a[i].atom, &b[j].atom, meter)? {
                Ordering::Less => {
                    let next = a[i].clone();
                    i += 1;
                    next
                }
                Ordering::Greater => {
                    let next = b[j].clone();
                    j += 1;
                    next
                }
                Ordering::Equal => {
                    let next = Term {
                        atom: a[i].atom.clone(),
                        offset: a[i].offset.max(b[j].offset),
                    };
                    i += 1;
                    j += 1;
                    next
                }
            }
        };
        if !next.atom.is_zero() {
            largest_nonconstant_offset = Some(largest_nonconstant_offset.unwrap_or(0).max(next.offset));
        }
        out.push(next);
    }
    // Zero is first in the structural order. Keep a positive explicit bound
    // unless one of the nonconstant terms is guaranteed to exceed that bound.
    if out[0].atom.is_zero()
        && largest_nonconstant_offset.is_some_and(|offset| offset >= out[0].offset)
    {
        meter.node()?;
        out.remove(0);
    }
    remove_covered_guards(out, meter)
}

/// `imax a u >= u`, including at `u = 0`. An offset on the guarded atom
/// therefore covers a no-larger offset on its guard. Never use the left
/// operand for this test: it disappears when the guard is zero.
fn remove_covered_guards(
    terms: Vec<Term>,
    meter: &mut Meter<'_>,
) -> Result<Form, UnificationError> {
    let mut guards = Vec::new();
    for term in &terms {
        meter.node()?;
        if let LevelView::IMax(_, guard) = term.atom.view() {
            guards.push((guard, term.offset));
        }
    }
    if guards.is_empty() {
        return Ok(Arc::from(terms));
    }
    let mut retained = Vec::new();
    for term in &terms {
        meter.node()?;
        let mut covered = false;
        if matches!(term.atom.view(), LevelView::Param(_) | LevelView::MVar(_)) {
            for (guard, offset) in &guards {
                meter.node()?;
                if term.offset <= *offset
                    && compare_atoms(&term.atom, guard, meter)? == Ordering::Equal
                {
                    covered = true;
                    break;
                }
            }
        }
        if !covered {
            retained.push(term.clone());
        }
    }
    Ok(Arc::from(retained))
}

/// Apply a single, still-unknown guard to one atom plus its offset.
/// Offsets stay INSIDE the guard: `imax (u+1) v` is zero at `v = 0`.
fn guarded_term(
    term: &Term,
    guard: &Level,
    meter: &mut Meter<'_>,
) -> Result<Form, UnificationError> {
    meter.node()?;
    if (term.atom.is_zero() && term.offset <= 1)
        || (term.offset == 0 && compare_atoms(&term.atom, guard, meter)? == Ordering::Equal)
    {
        return singleton(guard.clone(), 0, meter);
    }
    if term.offset == 0
        && let LevelView::IMax(_, inner_guard) = term.atom.view()
        && compare_atoms(inner_guard, guard, meter)? == Ordering::Equal
    {
        // imax (imax a u) u = imax a u, without choosing u's value.
        return singleton(term.atom.clone(), 0, meter);
    }
    let mut left = term.atom.clone();
    for _ in 0..term.offset {
        meter.node()?;
        left = left.succ().map_err(|error| UnificationError::Universe(error.into()))?;
    }
    meter.node()?;
    let atom = Level::imax(left, guard.clone())
        .map_err(|error| UnificationError::Universe(error.into()))?;
    singleton(atom, 0, meter)
}

fn impredicative_maximum(
    a: &Form,
    b: &Form,
    meter: &mut Meter<'_>,
) -> Result<Form, UnificationError> {
    if b.is_empty() || a.is_empty()
        || (a.len() == 1 && a[0].atom.is_zero() && a[0].offset == 1)
        || equal_forms(a, b, meter)?
    {
        return Ok(Arc::clone(b));
    }
    for term in b.iter() {
        meter.node()?;
        if term.offset > 0 {
            return maximum(a, b, meter);
        }
    }
    // imax distributes over max on both sides. Child forms are already
    // normalized, so a right IMax's guard is atomic; no recursive helper or
    // repeated normalization of generated levels is necessary.
    let mut result: Form = Arc::from([]);
    for right in b.iter() {
        meter.node()?;
        let guard = match right.atom.view() {
            LevelView::Param(_) | LevelView::MVar(_) => &right.atom,
            LevelView::IMax(_, guard) => {
                // imax a (imax c u) = max (imax a u) (imax c u).
                let inner = singleton(right.atom.clone(), 0, meter)?;
                result = maximum(&result, &inner, meter)?;
                guard
            }
            _ => unreachable!("a normalized zero-offset right atom is a universe or an IMax"),
        };
        for left in a.iter() {
            meter.node()?;
            let guarded = guarded_term(left, guard, meter)?;
            result = maximum(&result, &guarded, meter)?;
        }
    }
    Ok(result)
}

fn rebuild(form: &Form, meter: &mut Meter<'_>) -> Result<Level, UnificationError> {
    let mut result = None;
    for term in form.iter() {
        meter.node()?;
        let mut level = term.atom.clone();
        for _ in 0..term.offset {
            meter.node()?;
            level = level.succ().map_err(|error| UnificationError::Universe(error.into()))?;
        }
        result = Some(match result {
            None => level,
            Some(previous) => {
                meter.node()?;
                Level::max(previous, level)
                    .map_err(|error| UnificationError::Universe(error.into()))?
            }
        });
    }
    Ok(result.unwrap_or_else(Level::zero))
}

pub(super) fn simplify(level: &Level, meter: &mut Meter<'_>) -> Result<Level, UnificationError> {
    let mut done = HashMap::<*const Level, Form>::new();
    let mut pending = vec![(level, false)];
    while let Some((current, exit)) = pending.pop() {
        let key = std::ptr::from_ref(current);
        if done.contains_key(&key) {
            continue;
        }
        if !exit {
            meter.node()?;
            pending.push((current, true));
            match current.view() {
                LevelView::Succ(child) => pending.push((child, false)),
                LevelView::Max(a, b) | LevelView::IMax(a, b) => {
                    pending.push((b, false));
                    pending.push((a, false));
                }
                _ => {}
            }
            continue;
        }
        let child = |level: &Level| {
            Arc::clone(done.get(&std::ptr::from_ref(level)).expect("normalization postorder"))
        };
        let form = match current.view() {
            LevelView::Zero => Arc::from([]),
            LevelView::Param(_) | LevelView::MVar(_) => singleton(current.clone(), 0, meter)?,
            LevelView::Succ(inner) => {
                let inner = child(inner);
                if inner.is_empty() {
                    singleton(Level::zero(), 1, meter)?
                } else {
                    let mut shifted = Vec::new();
                    for term in inner.iter() {
                        meter.node()?;
                        shifted.push(Term {
                            atom: term.atom.clone(),
                            offset: term.offset.checked_add(1).ok_or(UnificationError::ExpressionScope)?,
                        });
                    }
                    Arc::from(shifted)
                }
            }
            LevelView::Max(a, b) => maximum(&child(a), &child(b), meter)?,
            LevelView::IMax(a, b) => impredicative_maximum(&child(a), &child(b), meter)?,
        };
        done.insert(key, form);
    }
    rebuild(done.get(&std::ptr::from_ref(level)).expect("normalized root"), meter)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn meter() -> Meter<'static> {
        Meter {
            steps: 0, nodes: 0, max_steps: 1_000_000, max_nodes: 1_000_000,
            heartbeat_bound: false, cancelled: &|| false,
        }
    }
    fn param(text: &str) -> Level { Level::param(Name::from_components([text])) }
    fn max(a: Level, b: Level) -> Level { Level::max(a, b).unwrap() }
    fn imax(a: Level, b: Level) -> Level { Level::imax(a, b).unwrap() }
    fn norm(level: &Level) -> Level { simplify(level, &mut meter()).unwrap() }
    fn evaluate(level: &Level, u: u32, v: u32, m: u32) -> u32 {
        match level.view() {
            LevelView::Zero => 0,
            LevelView::Param(name) if name == &Name::from_components(["u"]) => u,
            LevelView::Param(_) => v,
            LevelView::MVar(_) => m,
            LevelView::Succ(inner) => evaluate(inner, u, v, m) + 1,
            LevelView::Max(a, b) => evaluate(a, u, v, m).max(evaluate(b, u, v, m)),
            LevelView::IMax(a, b) => {
                let right = evaluate(b, u, v, m);
                if right == 0 { 0 } else { evaluate(a, u, v, m).max(right) }
            }
        }
    }

    #[test]
    fn generated_levels_preserve_semantics_and_reach_a_fixpoint() {
        let mut levels = vec![Level::zero(), Level::one(), param("u"), param("v"),
            Level::mvar(LMVarId(Name::from_components(["m"])) )];
        // Deterministically generated DAGs; no external property-testing crate.
        for i in 0..240 {
            let n = levels.len();
            let a = levels[(i * 17 + 3) % n].clone();
            let b = levels[(i * 29 + 1) % n].clone();
            levels.push(match i % 3 { 0 => a.succ().unwrap(), 1 => max(a, b), _ => imax(a, b) });
        }
        for level in &levels {
            let normalized = norm(level);
            assert_eq!(norm(&normalized), normalized);
            for u in 0..=3 { for v in 0..=3 { for m in 0..=3 {
                assert_eq!(evaluate(level, u, v, m), evaluate(&normalized, u, v, m));
            }}}
        }
    }

    #[test]
    fn all_max_permutations_and_parenthesizations_have_one_form() {
        let terms = [param("u"), param("v"), param("u").succ().unwrap(), Level::one()];
        let expected = norm(&max(terms[2].clone(), terms[1].clone()));
        for a in 0..4 { for b in 0..4 { for c in 0..4 { for d in 0..4 {
            if a == b || a == c || a == d || b == c || b == d || c == d { continue; }
            let [a,b,c,d] = [a,b,c,d].map(|i| terms[i].clone());
            assert_eq!(norm(&max(max(a.clone(),b.clone()),max(c.clone(),d.clone()))), expected);
            assert_eq!(norm(&max(a,max(b,max(c,d)))), expected);
        }}}}
    }

    #[test]
    fn explicit_bounds_drop_only_when_an_offset_dominates_them() {
        let three = Level::one().succ().unwrap().succ().unwrap();
        let two = param("u").succ().unwrap().succ().unwrap();
        let not_dominated = norm(&max(three.clone(), two));
        assert_eq!(evaluate(&not_dominated, 0, 0, 0), 3);
        assert_eq!(evaluate(&not_dominated, 9, 0, 0), 11);
        let dominated = param("u").succ().unwrap().succ().unwrap().succ().unwrap();
        assert_eq!(norm(&max(three, dominated.clone())), dominated);
    }

    #[test]
    fn name_and_level_hash_collisions_do_not_merge_atoms() {
        // Overflowing numeric names intentionally share the Reference hash 17.
        let root = Name::from_components(["u"]);
        let a = Level::param(Name::num_overflowing(root.clone(), 1));
        let b = Level::param(Name::num_overflowing(root, 2));
        assert_eq!(a.hash(), b.hash());
        assert_ne!(a, b);
        let merged = norm(&max(a.clone(), b.clone()));
        assert_eq!(merged, norm(&max(b, a)));
        assert!(matches!(merged.view(), LevelView::Max(..)));
    }

    #[test]
    fn imax_guard_is_preserved_when_its_right_side_can_be_zero() {
        let level = imax(param("u"), param("v"));
        assert_eq!(norm(&level), level);
        assert_eq!(evaluate(&norm(&level), 8, 0, 0), 0);
        assert_ne!(norm(&level), norm(&max(param("u"), param("v"))));
    }

    fn guarded_equations() -> Vec<(Level, Level)> {
        let (u, v) = (param("u"), param("v"));
        let w = Level::mvar(LMVarId(Name::from_components(["guard"])));
        vec![
            (imax(max(u.clone(), v.clone()), w.clone()),
                max(imax(u.clone(), w.clone()), imax(v.clone(), w.clone()))),
            (imax(u.clone(), max(v.clone(), w.clone())),
                max(imax(u.clone(), v.clone()), imax(u.clone(), w.clone()))),
            (imax(u.clone(), imax(v.clone(), w.clone())),
                max(imax(u.clone(), w.clone()), imax(v.clone(), w.clone()))),
            (imax(imax(u.clone(), v.clone()), v.clone()), imax(u.clone(), v.clone())),
            (imax(max(u.clone().succ().unwrap(), v.clone()), w.clone()),
                max(imax(u.clone().succ().unwrap(), w.clone()), imax(v.clone(), w))),
            (max(v.clone(), imax(u.clone(), v.clone())), imax(u, v)),
        ]
    }

    #[test]
    fn guarded_distributivity_is_used_by_the_transactional_solver() {
        use fln_core::options::KVMap;
        use fln_env::environment::Environment;
        let mut txn = ElabTxn::new(Environment::new(), KVMap::new(), 79);
        let before = txn.clone();
        let equations: Vec<_> = guarded_equations().into_iter()
            .map(|(a, b)| (Expr::sort(a), Expr::sort(b))).collect();
        let report = txn.unify_many_with(
            &equations,
            UnificationBudget::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
            &|| false,
        ).unwrap();
        assert!(report.expression_assignments.is_empty());
        assert!(report.universe_assignments.is_empty());
        assert_eq!(report.kernel_checks, 0);
        assert_eq!(txn.mvars, before.mvars);
        assert_eq!(txn.universes, before.universes);
        assert_eq!(txn.constraints, before.constraints);
        assert_eq!(txn.env, before.env);
    }

    #[test]
    fn guarded_laws_preserve_zero_cases_and_are_idempotent() {
        for (left, right) in guarded_equations() {
            let normalized = norm(&left);
            assert_eq!(normalized, norm(&right));
            assert_eq!(norm(&normalized), normalized);
            for u in 0..=4 { for v in 0..=4 { for m in 0..=4 {
                assert_eq!(evaluate(&left, u, v, m), evaluate(&normalized, u, v, m));
                assert_eq!(evaluate(&right, u, v, m), evaluate(&normalized, u, v, m));
            }}}
        }
    }

    #[test]
    fn offsets_do_not_escape_a_guard_and_left_operands_are_not_absorbed() {
        let guarded = imax(param("u").succ().unwrap(), param("v"));
        let wrong = imax(param("u"), param("v")).succ().unwrap();
        assert_ne!(norm(&guarded), norm(&wrong));
        assert_eq!(evaluate(&norm(&guarded), 7, 0, 0), 0);
        assert_eq!(evaluate(&norm(&wrong), 7, 0, 0), 1);
        let retained = max(param("u"), imax(param("u"), param("v")));
        assert_eq!(evaluate(&norm(&retained), 7, 0, 0), 7);
        let covered = max(param("v").succ().unwrap(), guarded.clone().succ().unwrap());
        assert_eq!(norm(&covered), norm(&guarded.clone().succ().unwrap()));
        let not_covered = max(param("v").succ().unwrap(), guarded);
        assert_eq!(evaluate(&norm(&not_covered), 0, 0, 0), 1);
    }

    #[test]
    fn colliding_guard_hashes_do_not_authorize_absorption() {
        let root = Name::from_components(["guard"]);
        let a = Level::param(Name::num_overflowing(root.clone(), 1));
        let b = Level::param(Name::num_overflowing(root, 2));
        assert_eq!(a.hash(), b.hash());
        let guarded = imax(param("u"), a);
        assert_ne!(norm(&max(b, guarded.clone())), norm(&guarded));
    }

    fn expansion() -> Level {
        let mut a = param("a0");
        let mut b = param("b0");
        for i in 1..6 {
            a = max(a, param(&format!("a{i}")));
            b = max(b, param(&format!("b{i}")));
        }
        imax(a, b)
    }

    #[test]
    fn distributive_expansion_remains_metered_and_cancellable() {
        use std::cell::Cell;
        let input = expansion();
        let mut control = meter();
        let expected = simplify(&input, &mut control).unwrap();
        assert!(control.nodes > 100);
        let mut limited = meter();
        limited.max_nodes = control.nodes / 2;
        assert!(matches!(simplify(&input, &mut limited), Err(UnificationError::NodeLimit { .. })));
        let polls = Cell::new(0);
        let stop = || { polls.set(polls.get() + 1); polls.get() > control.steps / 2 };
        let mut cancelled = Meter { cancelled: &stop, ..meter() };
        assert!(matches!(simplify(&input, &mut cancelled), Err(UnificationError::Cancelled)));
        assert_eq!(norm(&input), expected);
    }

    #[test]
    fn later_invalid_guard_conversion_rolls_back_tentative_assignments() {
        use fln_core::options::KVMap;
        use fln_env::environment::Environment;
        let mut txn = ElabTxn::new(Environment::new(), KVMap::new(), 80);
        let before = txn.clone();
        let tentative = LMVarId(Name::from_components(["tentative"]));
        let mut equations = vec![(Expr::sort(Level::mvar(tentative)), Expr::sort(Level::one()))];
        equations.extend(guarded_equations().into_iter().map(|(a, b)| (Expr::sort(a), Expr::sort(b))));
        equations.push((
            Expr::sort(imax(param("u"), param("v"))),
            Expr::sort(max(param("u"), param("v"))),
        ));
        let result = txn.unify_many_with(
            &equations,
            UnificationBudget::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
            &|| false,
        );
        assert!(matches!(result, Err(UnificationError::Deferred(_))));
        assert_eq!(txn.mvars, before.mvars);
        assert_eq!(txn.universes, before.universes);
        assert_eq!(txn.constraints, before.constraints);
        assert_eq!(txn.env, before.env);
    }
}
