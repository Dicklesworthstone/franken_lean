//! A finite rolling window of lazy callbacks for a checked Nat history.
//!
//! Projection depth is only a candidate bound. Specialization must eliminate
//! an opaque older-history marker in every boundary case and in the symbolic
//! successor case before the window is executable. No source result is guessed.
//! Slots are thunks, so an unused predecessor cannot run a callback or diverge.
//! Captured older windows may remain live; this is not a constant-memory claim.
use super::*;

impl Preparation<'_> {
    fn history_window_width(&mut self, functional: &Expr) -> Result<usize, IngressError> {
        let mut width = 1usize;
        let mut pending = vec![functional];
        let mut seen = std::collections::HashSet::new();
        while let Some(expr) = pending.pop() {
            self.tick()?;
            if !seen.insert(expr.allocation_identity()) {
                continue;
            }
            if let ExprNode::Proj {
                struct_name,
                idx: 0,
                expr: inner,
            } = expr.node()
                && struct_name == &named("PProd")
            {
                let mut depth = 1usize;
                let mut tail = inner;
                while let ExprNode::Proj {
                    struct_name,
                    idx: 1,
                    expr,
                } = tail.node()
                {
                    self.tick()?;
                    if struct_name != &named("PProd") {
                        break;
                    }
                    depth = depth
                        .checked_add(1)
                        .ok_or_else(|| unsupported("Nat history width"))?;
                    if depth > self.limits.max_context_depth {
                        return Err(IngressError::ResourceLimit {
                            resource: IngressResource::ContextDepth,
                            limit: self.limits.max_context_depth,
                            observed: depth,
                        });
                    }
                    tail = expr;
                }
                width = width.max(depth);
            }
            for child in history_children(expr).into_iter().flatten() {
                reserve(&mut pending, self.limits.max_nodes)?;
                pending.push(child);
            }
        }
        Ok(width)
    }

    fn history_uses_marker(
        &mut self,
        expression: &Expr,
        marker: &FVarId,
    ) -> Result<bool, IngressError> {
        let mut pending = vec![expression];
        let mut seen = std::collections::HashSet::new();
        while let Some(expr) = pending.pop() {
            self.tick()?;
            if !expr.has_fvar() || !seen.insert(expr.allocation_identity()) {
                continue;
            }
            if matches!(expr.node(), ExprNode::FVar { id } if id == marker) {
                return Ok(true);
            }
            for child in history_children(expr).into_iter().flatten() {
                reserve(&mut pending, self.limits.max_nodes)?;
                pending.push(child);
            }
        }
        Ok(false)
    }

    fn history_bind(&mut self, id: &FVarId, type_: Expr, body: Expr) -> Result<Expr, IngressError> {
        let body = self
            .lift(&body, 1)?
            .abstract_fvar(id, 0)
            .map_err(|_| unsupported("Nat window binder scope"))?;
        Ok(Expr::lam(id.0.clone(), type_, body, BinderInfo::Default))
    }

    fn history_slots(&mut self, state: Expr, width: usize) -> Result<Vec<Expr>, IngressError> {
        let mut tail = state;
        let mut slots = Vec::new();
        for index in 0..width {
            self.tick()?;
            reserve(&mut slots, self.limits.max_context_depth)?;
            if index + 1 == width {
                slots.push(tail.clone());
            } else {
                slots.push(Expr::proj(named("PProd"), 0, tail.clone()));
                tail = Expr::proj(named("PProd"), 1, tail);
            }
        }
        Ok(slots)
    }

    fn history_pack(
        &mut self,
        types: &[(Expr, Level)],
        slots: &[Expr],
    ) -> Result<Expr, IngressError> {
        let mut value = slots
            .last()
            .cloned()
            .ok_or_else(|| unsupported("empty Nat window"))?;
        for index in (0..slots.len() - 1).rev() {
            self.tick()?;
            let tail = &types[slots.len() - index - 2];
            value = application(
                constant("PProd.mk", vec![types[0].1.clone(), tail.1.clone()]),
                [
                    types[0].0.clone(),
                    tail.0.clone(),
                    slots[index].clone(),
                    value,
                ],
            );
        }
        Ok(value)
    }

    /// Build exactly the visible prefix. The older suffix remains an opaque
    /// marker except at zero, where the real dictionary is PUnit.unit.
    fn history_prefix(
        &mut self,
        motive: &Expr,
        universe: &Level,
        mut major: Expr,
        slots: &[Expr],
        mut tail: Expr,
    ) -> Result<(Expr, Expr), IngressError> {
        let storage = Level::max(Level::one(), universe.clone())
            .map_err(|_| unsupported("Nat window universe"))?;
        for slot in slots.iter().rev() {
            self.tick()?;
            let previous_type = application(
                constant("Nat.below", vec![universe.clone()]),
                [motive.clone(), major.clone()],
            );
            tail = application(
                constant("PProd.mk", vec![universe.clone(), storage.clone()]),
                [
                    Expr::app(motive.clone(), major.clone()),
                    previous_type,
                    slot.clone(),
                    tail,
                ],
            );
            major = Expr::app(constant("Nat.succ", vec![]), major);
        }
        Ok((major, tail))
    }

    pub(super) fn nat_history_window(
        &mut self,
        args: &[Expr],
        levels: &[Level],
        result_type: Expr,
        functional: Expr,
        first: Expr,
        marker: &FVarId,
    ) -> Result<Expr, IngressError> {
        let refusal = || unsupported("Nat course-of-values history escapes");
        if first.has_fvar() || !closed(&result_type) {
            return Err(refusal());
        }
        let width = self.history_window_width(&functional)?;
        if width < 2 {
            return Err(refusal());
        }
        let storage = Level::max(Level::one(), levels[0].clone())
            .map_err(|_| unsupported("Nat window universe"))?;
        let thunk_type = Expr::forall_e(
            Name::anonymous(),
            constant("Nat", vec![]),
            result_type.clone(),
            BinderInfo::Default,
        );
        let thunk_level = Level::imax(Level::one(), levels[0].clone())
            .map_err(|_| unsupported("Nat window thunk universe"))?;
        let mut types = vec![(thunk_type.clone(), thunk_level.clone())];
        for _ in 1..width {
            self.tick()?;
            let (tail, level) = types.last().expect("nonempty window types");
            let next = application(
                constant("PProd", vec![thunk_level.clone(), level.clone()]),
                [thunk_type.clone(), tail.clone()],
            );
            reserve(&mut types, self.limits.max_context_depth)?;
            types.push((next, storage.clone()));
        }
        let state_type = types.last().expect("nonempty window types").0.clone();
        let n = FVarId(named("_fln_runtime_window_major"));
        let state = FVarId(named("_fln_runtime_window_state"));
        let stored = self.history_slots(Expr::fvar(state.clone()), width)?;
        let mut entries = Vec::new();
        let mut slots = Vec::new();
        for index in 0..width {
            self.tick()?;
            let id = FVarId(Name::num(named("_fln_runtime_window_entry"), index as u64));
            reserve(&mut entries, self.limits.max_context_depth)?;
            reserve(&mut slots, self.limits.max_context_depth)?;
            slots.push(Expr::fvar(id.clone()));
            entries.push(id);
        }
        let (major, history) = self.history_prefix(
            &args[0],
            &levels[0],
            Expr::fvar(n.clone()),
            &slots,
            Expr::fvar(marker.clone()),
        )?;
        let mut next =
            self.nat_history_reduce(&application(functional.clone(), [major, history]), marker)?;
        if self.history_uses_marker(&next, marker)? {
            return Err(refusal());
        }
        // For n < width-1 the history has fewer entries. Derive each of these
        // cases from the real functional; padded slots are never read there.
        let case_motive = Expr::lam(
            Name::anonymous(),
            constant("Nat", vec![]),
            result_type.clone(),
            BinderInfo::Default,
        );
        for boundary in (1..width).rev() {
            self.tick()?;
            let (major, history) = self.history_prefix(
                &args[0],
                &levels[0],
                constant("Nat.zero", vec![]),
                &slots[..boundary],
                constant("PUnit.unit", vec![storage.clone()]),
            )?;
            let first_case = self
                .nat_history_reduce(&application(functional.clone(), [major, history]), marker)?;
            if self.history_uses_marker(&first_case, marker)? {
                return Err(refusal());
            }
            let lifted = self.lift(&next, 1)?;
            let unused_ih = Expr::lam(
                Name::anonymous(),
                result_type.clone(),
                lifted,
                BinderInfo::Default,
            );
            let successor = self.history_bind(&n, constant("Nat", vec![]), unused_ih)?;
            next = application(
                constant("Nat.rec", levels.to_vec()),
                [
                    case_motive.clone(),
                    first_case,
                    successor,
                    Expr::fvar(n.clone()),
                ],
            );
        }
        // The symbolic dictionary is reduced before inserting forces. Every
        // surviving entry occurrence is a call, never an eagerly evaluated
        // predecessor value. Unchosen source branches must not run callbacks.
        for (entry, thunk) in entries.iter().zip(&stored) {
            self.tick()?;
            let body = self
                .lift(&next, 1)?
                .abstract_fvar(entry, 0)
                .map_err(|_| unsupported("Nat window entry scope"))?;
            let force = Expr::app(thunk.clone(), constant("Nat.zero", vec![]));
            next = self.substitution(&body, &force)?;
        }
        let next = Expr::lam(
            Name::anonymous(),
            constant("Nat", vec![]),
            self.lift(&next, 1)?,
            BinderInfo::Default,
        );
        let thunk_value = self
            .value_type(&thunk_type)?
            .ok_or_else(|| unsupported("Nat history thunk representation"))?;
        let next = self.typed_callable_result(next, thunk_type.clone(), thunk_value)?;
        let mut updated = vec![next];
        for slot in stored.iter().take(width - 1) {
            reserve(&mut updated, self.limits.max_context_depth)?;
            updated.push(slot.clone());
        }
        let next_state = self.history_pack(&types, &updated)?;
        let step = self.history_bind(&state, state_type.clone(), next_state)?;
        let step = self.history_bind(&n, constant("Nat", vec![]), step)?;
        // Padding shares an inert thunk, not an evaluated zero callback. Even
        // the zero result may be unused by a later source branch.
        let initial = FVarId(named("_fln_runtime_window_initial"));
        let mut padding = Vec::new();
        for _ in 0..width {
            reserve(&mut padding, self.limits.max_context_depth)?;
            padding.push(Expr::fvar(initial.clone()));
        }
        let packed = self.history_pack(&types, &padding)?;
        let packed = self
            .lift(&packed, 1)?
            .abstract_fvar(&initial, 0)
            .map_err(|_| unsupported("Nat initial window scope"))?;
        let first = Expr::lam(
            Name::anonymous(),
            constant("Nat", vec![]),
            self.lift(&first, 1)?,
            BinderInfo::Default,
        );
        let initial = Expr::let_e(initial.0, thunk_type, first, packed, false);
        let motive = Expr::lam(
            Name::anonymous(),
            constant("Nat", vec![]),
            state_type,
            BinderInfo::Default,
        );
        let fold = application(
            constant("Nat.rec", vec![storage]),
            [motive, initial, step, args[1].clone()],
        );
        let result = Expr::app(
            Expr::proj(named("PProd"), 0, fold),
            constant("Nat.zero", vec![]),
        );
        if result.has_fvar() {
            return Err(refusal());
        }
        // The new pair layouts did not exist during the source projection
        // pass. Bind their selectors while the window telescope is intact.
        self.lower_projections(&application(result, args[3..].iter().cloned()))
    }
}

fn history_children(expr: &Expr) -> [Option<&Expr>; 3] {
    match expr.node() {
        ExprNode::App { f, a } => [Some(f), Some(a), None],
        ExprNode::Lam {
            binder_type, body, ..
        }
        | ExprNode::ForallE {
            binder_type, body, ..
        } => [Some(binder_type), Some(body), None],
        ExprNode::LetE {
            type_, value, body, ..
        } => [Some(type_), Some(value), Some(body)],
        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => [Some(expr), None, None],
        _ => [None, None, None],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn projected_entry(depth: usize) -> Expr {
        let mut value = Expr::fvar(FVarId(named("history")));
        for _ in 1..depth {
            value = Expr::proj(named("PProd"), 1, value);
        }
        Expr::proj(named("PProd"), 0, value)
    }

    #[test]
    fn window_discovery_obeys_node_and_context_limits() {
        let environment = Environment::new();
        let value = projected_entry(4);
        let mut normal = Preparation::new(&environment, IngressLimits::default());
        assert_eq!(normal.history_window_width(&value).unwrap(), 4);
        let mut bounded = Preparation::new(
            &environment,
            IngressLimits {
                max_context_depth: 2,
                ..IngressLimits::default()
            },
        );
        assert!(matches!(
            bounded.history_window_width(&value),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::ContextDepth,
                limit: 2,
                observed: 3
            })
        ));
        let mut exhausted = Preparation::new(
            &environment,
            IngressLimits {
                max_nodes: 0,
                ..IngressLimits::default()
            },
        );
        assert!(matches!(
            exhausted.history_window_width(&value),
            Err(IngressError::ResourceLimit { .. })
        ));
    }

    #[test]
    fn opaque_tail_checks_include_unused_values_and_type_annotations() {
        let environment = Environment::new();
        let marker = FVarId(named("older_tail"));
        let nat = constant("Nat", vec![]);
        let zero = constant("Nat.zero", vec![]);
        let values = [
            Expr::fvar(marker.clone()),
            Expr::let_e(
                Name::anonymous(),
                nat.clone(),
                Expr::fvar(marker.clone()),
                zero.clone(),
                false,
            ),
            Expr::lam(
                Name::anonymous(),
                Expr::fvar(marker.clone()),
                zero.clone(),
                BinderInfo::Default,
            ),
            Expr::proj(named("PProd"), 0, Expr::fvar(marker.clone())),
        ];
        let mut preparation = Preparation::new(&environment, IngressLimits::default());
        for value in values {
            assert!(preparation.history_uses_marker(&value, &marker).unwrap());
        }
        assert!(!preparation.history_uses_marker(&zero, &marker).unwrap());
        assert!(
            !preparation
                .history_uses_marker(&Expr::fvar(FVarId(named("another"))), &marker)
                .unwrap()
        );
    }
}
