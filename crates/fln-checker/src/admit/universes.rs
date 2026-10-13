//! Universe comparison for independently reconstructed inductive interfaces.
//!
//! A source-inferred family may spell `max (max 1 (u+1)) (v+1)` where the
//! reconstructed interface spells `max (u+1) (v+1)`. Keep the expression shape
//! check, but compare level roots using this checker's one-pass KR-501 relation.
//! The fixed quotient initializer still requires raw structural level identity.
use super::*;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum ReconstructionMode {
    Inductive,
    Quotient,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn reconstruction_level_equal(
    left: &WireExpr,
    left_root: LevelId,
    right: &WireExpr,
    right_root: LevelId,
    control: &mut StructuralComparisonControl,
    seen: &mut BTreeSet<(LevelId, LevelId)>,
    mode: ReconstructionMode,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<Result<bool, QuickDefEqStop>, QuickDefEqFault> {
    if mode == ReconstructionMode::Quotient {
        return structural_level_equal(
            left, left_root, right, right_root, control, seen, cancelled,
        );
    }
    if seen.contains(&(left_root, right_root)) {
        return Ok(Ok(true));
    }
    // A failed raw comparison records tentative child pairs. They must never
    // enter the successful root cache: equivalence of the enclosing maxima
    // does not establish equivalence of their ordered children. Nor can cached
    // one-pass equivalences replace children before normalizing another root.
    let mut raw_pairs = BTreeSet::new();
    match structural_level_equal(
        left,
        left_root,
        right,
        right_root,
        control,
        &mut raw_pairs,
        cancelled,
    )? {
        Ok(true) => {
            seen.insert((left_root, right_root));
            return Ok(Ok(true));
        }
        Ok(false) => {}
        Err(stop) => return Ok(Err(stop)),
    }
    // The enclosing expression comparison has charged both complete input
    // level arenas against max_level_arena_nodes. Use the same independent,
    // heap-based one-pass relation as quick defeq, with no primary-kernel
    // helpers, assignment, expression reduction, or normalization fixpoint.
    if let Err(stop) = control.comparison(cancelled) {
        return Ok(Err(stop));
    }
    let equal =
        crate::universe::level_roots_equal(left.levels(), left_root, right.levels(), right_root)
            .map_err(|error| QuickDefEqFault::Universe {
                left: left_root.index(),
                right: right_root.index(),
                error,
            })?;
    // Cancellation after normalization must remain a nonanswer and may not
    // publish a cached equality, even when both normal forms already agree.
    if let Err(stop) = control.poll(cancelled) {
        return Ok(Err(stop));
    }
    if equal {
        seen.insert((left_root, right_root));
    }
    Ok(Ok(equal))
}

#[cfg(test)]
mod tests;
