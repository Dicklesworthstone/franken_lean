//! Captured locals may also be explicit pattern arguments. The two roles are
//! distinct: abstracting an argument must not abstract a dependency that the
//! declared function type intended to capture. This extension admits the
//! dependency-independent fragment and leaves the ambiguous cases deferred.
use super::*;

impl Engine<'_> {
    /// Run before allocating a residual or assigning either parent. Existing
    /// noncaptured patterns retain their conversion behavior; the new captured
    /// lane checks the local argument types of both recognized pattern spines
    /// before erasing arguments. It is not a general input-expression checker.
    pub(super) fn captured_pruning_compatible(
        &mut self,
        left: &PruningPattern,
        right: &PruningPattern,
        locals: &LocalContext,
    ) -> Result<bool, UnificationError> {
        let left_captured = self.captured_pruning_arguments(left, locals)?;
        let right_captured = self.captured_pruning_arguments(right, locals)?;
        let (Some(left_captured), Some(right_captured)) = (left_captured, right_captured) else {
            return Ok(false);
        };
        if left_captured.is_empty() && right_captured.is_empty() {
            return Ok(true);
        }
        if !self.captured_pruning_signature_independent(left, &left_captured)?
            || !self.captured_pruning_signature_independent(right, &right_captured)?
        {
            return Ok(false);
        }
        Ok(self.pruning_arguments_typed(left, locals)?
            && self.pruning_arguments_typed(right, locals)?)
    }

    fn captured_pruning_arguments(
        &mut self,
        pattern: &PruningPattern,
        locals: &LocalContext,
    ) -> Result<Option<HashSet<FVarId>>, UnificationError> {
        let mut captured = HashSet::new();
        for (id, _, _) in &pattern.binders {
            self.meter.node()?;
            if let Some(declaration) = pattern.declaration.lctx.find(id) {
                // An equal identifier from a rebound or stale local context
                // is not the lexical binding captured by the parent hole.
                if locals.find(id) != Some(declaration) {
                    return Ok(None);
                }
                captured.insert(id.clone());
            }
        }
        Ok(Some(captured))
    }

    /// Check the transitive local dependency closure of the ORIGINAL type,
    /// before substituting its formal arguments with the actual locals. A
    /// result `P captured_x` must not become `P formal_x` merely because x was
    /// also passed explicitly. A local alias can hide that same dependency.
    /// Expression holes can hide arbitrary captured dependencies; leave those
    /// cases for a later retry rather than guessing at their eventual types.
    fn captured_pruning_signature_independent(
        &mut self,
        pattern: &PruningPattern,
        captured: &HashSet<FVarId>,
    ) -> Result<bool, UnificationError> {
        if captured.is_empty() {
            return Ok(true);
        }
        let mut pending = vec![pattern.declaration.type_.clone()];
        let mut visited = HashSet::new();
        while let Some(expr) = pending.pop() {
            self.meter.node()?;
            // Resolve already assigned holes without applying this pattern's
            // actual arguments. A completed type inference must unblock retry;
            // any capture exposed by the assignment is still checked below.
            let expr = self.instantiate(&expr)?;
            if expr.has_expr_mvar() {
                return Ok(false);
            }
            // Hash-set iteration must not choose traversal order, including
            // the first resource/cancellation stop. Names have a stable order.
            let mut dependencies: Vec<_> = self.scan(&expr)?.fvars.into_iter().collect();
            dependencies.sort_by(|left, right| left.0.cmp(&right.0));
            for id in dependencies {
                self.meter.node()?;
                if captured.contains(&id) {
                    return Ok(false);
                }
                if !visited.insert(id.clone()) {
                    continue;
                }
                let Some(local) = pattern.declaration.lctx.find(&id) else {
                    // A malformed signature is not repaired by introducing a
                    // residual whose context happens to contain the escape.
                    return Ok(false);
                };
                pending.push(local.type_.clone());
                if let Some(value) = &local.value {
                    pending.push(value.clone());
                }
            }
        }
        Ok(true)
    }
}
