//! Finite-depth List histories retain lazy, typed results for earlier tails.
//!
//! Projection depth proposes a window; it never proves one sufficient. Every
//! boundary and symbolic cons case must eliminate the opaque older suffix.
//! Delayed entries preserve skipped callbacks and strict work inside live ones.
//! Older windows can remain captured: this is not a constant-memory promise.
use super::*;

struct Shape {
    element: Expr,
    motive: Expr,
    levels: Vec<Level>,
    storage: Level,
}

fn children(value: &Expr) -> [Option<&Expr>; 3] {
    match value.node() {
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

impl Preparation<'_> {
    fn list_window_width(&mut self, expression: &Expr) -> Result<usize, IngressError> {
        let mut width = 1usize;
        let mut pending = vec![expression];
        let mut seen = std::collections::HashSet::new();
        while let Some(value) = pending.pop() {
            self.tick()?;
            if !seen.insert(value.allocation_identity()) {
                continue;
            }
            if let ExprNode::Proj {
                struct_name,
                idx: 0,
                expr,
            } = value.node()
                && struct_name == &named("PProd")
            {
                let mut depth = 1usize;
                let mut tail = expr;
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
                        .ok_or_else(|| unsupported("List history width"))?;
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
            for child in children(value).into_iter().flatten() {
                reserve(&mut pending, self.limits.max_nodes)?;
                pending.push(child);
            }
        }
        Ok(width)
    }

    fn list_window_uses(
        &mut self,
        expression: &Expr,
        marker: &FVarId,
    ) -> Result<bool, IngressError> {
        let mut pending = vec![expression];
        let mut seen = std::collections::HashSet::new();
        while let Some(value) = pending.pop() {
            self.tick()?;
            if !value.has_fvar() || !seen.insert(value.allocation_identity()) {
                continue;
            }
            if matches!(value.node(), ExprNode::FVar { id } if id == marker) {
                return Ok(true);
            }
            for child in children(value).into_iter().flatten() {
                reserve(&mut pending, self.limits.max_nodes)?;
                pending.push(child);
            }
        }
        Ok(false)
    }

    fn list_window_bind(
        &mut self,
        id: &FVarId,
        type_: Expr,
        body: Expr,
    ) -> Result<Expr, IngressError> {
        let body = self
            .lift(&body, 1)?
            .abstract_fvar(id, 0)
            .map_err(|_| unsupported("List window binder scope"))?;
        Ok(Expr::lam(id.0.clone(), type_, body, BinderInfo::Default))
    }

    fn list_window_slots(
        &mut self,
        mut tail: Expr,
        width: usize,
    ) -> Result<Vec<Expr>, IngressError> {
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

    fn list_window_pack(
        &mut self,
        types: &[(Expr, Level)],
        slots: &[Expr],
    ) -> Result<Expr, IngressError> {
        let mut result = slots
            .last()
            .cloned()
            .ok_or_else(|| unsupported("empty List window"))?;
        for index in (0..slots.len() - 1).rev() {
            self.tick()?;
            let tail = &types[slots.len() - index - 2];
            result = application(
                constant("PProd.mk", vec![types[0].1.clone(), tail.1.clone()]),
                [
                    types[0].0.clone(),
                    tail.0.clone(),
                    slots[index].clone(),
                    result,
                ],
            );
        }
        Ok(result)
    }

    fn list_window_prefix(
        &mut self,
        shape: &Shape,
        heads: &[FVarId],
        mut major: Expr,
        slots: &[Expr],
        mut history: Expr,
    ) -> Result<(Expr, Expr), IngressError> {
        if heads.len() != slots.len() {
            return Err(unsupported("List window prefix arity"));
        }
        for (head, slot) in heads.iter().zip(slots).rev() {
            self.tick()?;
            let previous = application(
                constant("List.below", shape.levels.clone()),
                [shape.element.clone(), shape.motive.clone(), major.clone()],
            );
            history = application(
                constant(
                    "PProd.mk",
                    vec![shape.levels[0].clone(), shape.storage.clone()],
                ),
                [
                    Expr::app(shape.motive.clone(), major.clone()),
                    previous,
                    slot.clone(),
                    history,
                ],
            );
            major = application(
                constant("List.cons", vec![shape.levels[1].clone()]),
                [shape.element.clone(), Expr::fvar(head.clone()), major],
            );
        }
        Ok((major, history))
    }

    pub(super) fn list_history_window(
        &mut self,
        args: &[Expr],
        levels: &[Level],
        result_type: Expr,
        functional: Expr,
        first: Expr,
        marker: &FVarId,
    ) -> Result<Expr, IngressError> {
        let refusal = || unsupported("List course-of-values history escapes");
        if first.has_fvar() || !closed(&result_type) {
            return Err(refusal());
        }
        let width = self.list_window_width(&functional)?;
        if width < 2 {
            return Err(refusal());
        }
        let storage = Level::max(
            levels[1].clone().succ().map_err(|_| refusal())?,
            levels[0].clone(),
        )
        .map_err(|_| refusal())?;
        let shape = Shape {
            element: args[0].clone(),
            motive: args[1].clone(),
            levels: levels.to_vec(),
            storage,
        };
        let family = Expr::app(constant("List", vec![levels[1].clone()]), args[0].clone());
        let empty = Expr::app(
            constant("List.nil", vec![levels[1].clone()]),
            args[0].clone(),
        );
        let unit_type = constant("PUnit", vec![Level::one()]);
        let unit = constant("PUnit.unit", vec![Level::one()]);
        let thunk_type = Expr::forall_e(
            Name::anonymous(),
            unit_type.clone(),
            result_type.clone(),
            BinderInfo::Default,
        );
        let thunk_level = Level::imax(Level::one(), levels[0].clone()).map_err(|_| refusal())?;
        let mut types = vec![(thunk_type.clone(), thunk_level.clone())];
        for _ in 1..width {
            self.tick()?;
            let (tail, level) = types.last().expect("nonempty window");
            let next = application(
                constant("PProd", vec![thunk_level.clone(), level.clone()]),
                [thunk_type.clone(), tail.clone()],
            );
            let next_level = Level::max(
                Level::one(),
                Level::max(thunk_level.clone(), level.clone()).map_err(|_| refusal())?,
            )
            .map_err(|_| refusal())?;
            reserve(&mut types, self.limits.max_context_depth)?;
            types.push((next, next_level));
        }
        let (state_type, state_level) = types.last().expect("nonempty window").clone();
        let state = FVarId(named("_fln_runtime_list_window_state"));
        let stored = self.list_window_slots(Expr::fvar(state.clone()), width)?;
        let mut heads = Vec::new();
        let mut tails = Vec::new();
        let mut entries = Vec::new();
        let mut slots = Vec::new();
        for index in 0..width {
            self.tick()?;
            for values in [&mut heads, &mut tails, &mut entries] {
                reserve(values, self.limits.max_context_depth)?;
            }
            heads.push(FVarId(Name::num(
                named("_fln_runtime_list_window_head"),
                index as u64,
            )));
            tails.push(FVarId(Name::num(
                named("_fln_runtime_list_window_tail"),
                index as u64,
            )));
            let entry = FVarId(Name::num(
                named("_fln_runtime_list_window_entry"),
                index as u64,
            ));
            reserve(&mut slots, self.limits.max_context_depth)?;
            slots.push(Expr::fvar(entry.clone()));
            entries.push(entry);
        }
        let (major, history) = self.list_window_prefix(
            &shape,
            &heads,
            Expr::fvar(tails[width - 1].clone()),
            &slots,
            Expr::fvar(marker.clone()),
        )?;
        let mut next =
            self.list_history_reduce(&application(functional.clone(), [major, history]), marker)?;
        if self.list_window_uses(&next, marker)? {
            return Err(refusal());
        }
        let case_motive = Expr::lam(
            Name::anonymous(),
            family.clone(),
            result_type.clone(),
            BinderInfo::Default,
        );
        // Each shorter tail chooses its real nil boundary. The cons branch
        // introduces the next actual head and tail, never fabricated payloads.
        for boundary in (1..width).rev() {
            self.tick()?;
            let (major, history) = self.list_window_prefix(
                &shape,
                &heads[..boundary],
                empty.clone(),
                &slots[..boundary],
                constant("PUnit.unit", vec![shape.storage.clone()]),
            )?;
            let first_case = self
                .list_history_reduce(&application(functional.clone(), [major, history]), marker)?;
            if self.list_window_uses(&first_case, marker)? {
                return Err(refusal());
            }
            let unused = Expr::lam(
                Name::anonymous(),
                result_type.clone(),
                self.lift(&next, 1)?,
                BinderInfo::Default,
            );
            let step = self.list_window_bind(&tails[boundary], family.clone(), unused)?;
            let step = self.list_window_bind(&heads[boundary], args[0].clone(), step)?;
            next = application(
                constant("List.rec", levels.to_vec()),
                [
                    args[0].clone(),
                    case_motive.clone(),
                    first_case,
                    step,
                    Expr::fvar(tails[boundary - 1].clone()),
                ],
            );
        }
        // Substitute forces only after reducing the symbolic dictionary.
        // A selected callback still executes every strict occurrence it uses.
        for (entry, thunk) in entries.iter().zip(&stored) {
            self.tick()?;
            let body = self
                .lift(&next, 1)?
                .abstract_fvar(entry, 0)
                .map_err(|_| refusal())?;
            next = self.substitution(&body, &Expr::app(thunk.clone(), unit.clone()))?;
        }
        let next = Expr::lam(
            Name::anonymous(),
            unit_type.clone(),
            self.lift(&next, 1)?,
            BinderInfo::Default,
        );
        let value_type = self.value_type(&thunk_type)?.ok_or_else(refusal)?;
        let next = self.typed_callable_result(next, thunk_type.clone(), value_type)?;
        let mut updated = vec![next];
        for slot in stored.iter().take(width - 1) {
            reserve(&mut updated, self.limits.max_context_depth)?;
            updated.push(slot.clone());
        }
        let next_state = self.list_window_pack(&types, &updated)?;
        let step = self.list_window_bind(&state, state_type.clone(), next_state)?;
        let step = self.list_window_bind(&tails[0], family.clone(), step)?;
        let step = self.list_window_bind(&heads[0], args[0].clone(), step)?;
        let initial = FVarId(named("_fln_runtime_list_window_initial"));
        let mut padding = Vec::new();
        for _ in 0..width {
            reserve(&mut padding, self.limits.max_context_depth)?;
            padding.push(Expr::fvar(initial.clone()));
        }
        let packed = self.list_window_pack(&types, &padding)?;
        let packed = self
            .lift(&packed, 1)?
            .abstract_fvar(&initial, 0)
            .map_err(|_| refusal())?;
        let first = Expr::lam(
            Name::anonymous(),
            unit_type,
            self.lift(&first, 1)?,
            BinderInfo::Default,
        );
        let initial = Expr::let_e(initial.0, thunk_type, first, packed, false);
        let motive = Expr::lam(Name::anonymous(), family, state_type, BinderInfo::Default);
        let fold = application(
            constant("List.rec", vec![state_level, levels[1].clone()]),
            [args[0].clone(), motive, initial, step, args[2].clone()],
        );
        let result = Expr::app(Expr::proj(named("PProd"), 0, fold), unit);
        if result.has_fvar() {
            return Err(refusal());
        }
        self.lower_projections(&application(result, args[4..].iter().cloned()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(depth: usize) -> Expr {
        let mut value = Expr::fvar(FVarId(named("history")));
        for _ in 1..depth {
            value = Expr::proj(named("PProd"), 1, value);
        }
        Expr::proj(named("PProd"), 0, value)
    }

    #[test]
    fn projection_discovery_is_metered_and_bounds_window_storage() {
        let environment = Environment::new();
        let expression = entry(4);
        let mut normal = Preparation::new(&environment, IngressLimits::default());
        assert_eq!(normal.list_window_width(&expression).unwrap(), 4);
        let visits = normal.visited;
        for allowed in [0, visits / 2, visits - 1] {
            let mut stopped = Preparation::new(
                &environment,
                IngressLimits {
                    max_nodes: allowed,
                    ..IngressLimits::default()
                },
            );
            assert!(matches!(
                stopped.list_window_width(&expression),
                Err(IngressError::ResourceLimit { .. })
            ));
        }
        let mut narrow = Preparation::new(
            &environment,
            IngressLimits {
                max_context_depth: 2,
                ..IngressLimits::default()
            },
        );
        assert!(matches!(
            narrow.list_window_width(&expression),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::ContextDepth,
                limit: 2,
                observed: 3
            })
        ));
        let mut retry = Preparation::new(&environment, IngressLimits::default());
        assert_eq!(retry.list_window_width(&expression).unwrap(), 4);
        assert_eq!(retry.visited, visits);
    }

    #[test]
    fn opaque_history_checks_include_unused_values_and_dependent_annotations() {
        let environment = Environment::new();
        let marker = FVarId(named("older"));
        let hole = Expr::fvar(marker.clone());
        let unit = constant("PUnit.unit", vec![Level::one()]);
        let forms = [
            hole.clone(),
            Expr::let_e(
                Name::anonymous(),
                constant("PUnit", vec![Level::one()]),
                hole.clone(),
                unit.clone(),
                false,
            ),
            Expr::lam(
                Name::anonymous(),
                hole.clone(),
                unit.clone(),
                BinderInfo::Default,
            ),
            Expr::proj(named("PProd"), 0, hole),
        ];
        let mut preparation = Preparation::new(&environment, IngressLimits::default());
        for expression in forms {
            assert!(preparation.list_window_uses(&expression, &marker).unwrap());
        }
        assert!(!preparation.list_window_uses(&unit, &marker).unwrap());
        assert!(
            !preparation
                .list_window_uses(&Expr::fvar(FVarId(named("different"))), &marker)
                .unwrap()
        );
    }

    #[test]
    fn shared_projection_graphs_are_not_expanded_as_trees() {
        let environment = Environment::new();
        let expression = (0..24).fold(entry(3), |value, _| Expr::app(value.clone(), value));
        let mut preparation = Preparation::new(&environment, IngressLimits::default());
        assert_eq!(preparation.list_window_width(&expression).unwrap(), 3);
        assert!(preparation.visited < 100);
        let marker = FVarId(named("missing"));
        assert!(!preparation.list_window_uses(&expression, &marker).unwrap());
        assert!(preparation.visited < 200);
    }
}
