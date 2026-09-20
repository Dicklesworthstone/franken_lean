//! Scope-aware output templates. Loose variables are private key placeholders,
//! raised under each binder; templates never enter the unifier or the kernel.
use super::*;

#[derive(Default)]
pub(super) struct Templates {
    holes: HashMap<MVarId, u32>,
    pub types: Vec<Expr>,
    done: HashMap<(Expr, u32), Expr>,
}

impl Templates {
    pub fn units(&self) -> usize {
        self.done.len()
    }

    fn hole(&mut self, frame: &Frame, id: &MVarId, depth: u32) -> Option<Expr> {
        let position = if let Some(position) = self.holes.get(id) {
            *position
        } else {
            let decl = frame.base.txn.mvars.get_decl(id)?;
            if decl.kind != MetavarKind::Natural
                || decl.depth != 0
                || decl.delayed.is_some()
                || frame.base.txn.mvars.is_assigned(id)
                || decl.lctx != frame.base.txn.lctx
                || !ground(&decl.type_)
                || decl.type_.has_loose_bvars()
            {
                return None;
            }
            let position = u32::try_from(self.types.len() + 1).ok()?;
            self.types.push(decl.type_.clone());
            self.holes.insert(id.clone(), position);
            position
        };
        Expr::bvar(depth.checked_add(position)?).ok()
    }

    /// Every expression container is traversed by heap continuation. Memoization
    /// is scoped by binder depth, so shared open syntax cannot capture a binder.
    /// A full key budget disables reuse rather than terminating instance search.
    pub fn rewrite(
        &mut self,
        context: &mut Context,
        frame: &Frame,
        root: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let mut pending = vec![(root.clone(), 0u32, false)];
        while let Some((expr, depth, finish)) = pending.pop() {
            context.tick()?;
            let key = (expr.clone(), depth);
            if self.done.contains_key(&key) {
                continue;
            }
            if self.done.len() + pending.len() >= MAX_KEY_UNITS {
                return Ok(None);
            }
            if ground(&expr) {
                self.done.insert(key, expr);
                continue;
            }
            if let ExprNode::MVar { id } = expr.node() {
                let Some(value) = self.hole(frame, id, depth) else {
                    return Ok(None);
                };
                self.done.insert(key, value);
                continue;
            }
            if !finish {
                pending.push((expr.clone(), depth, true));
                match expr.node() {
                    ExprNode::App { f, a } => {
                        pending.push((a.clone(), depth, false));
                        pending.push((f.clone(), depth, false));
                    }
                    ExprNode::Lam {
                        binder_type, body, ..
                    }
                    | ExprNode::ForallE {
                        binder_type, body, ..
                    } => {
                        pending.push((body.clone(), depth + 1, false));
                        pending.push((binder_type.clone(), depth, false));
                    }
                    ExprNode::LetE {
                        type_, value, body, ..
                    } => {
                        pending.push((body.clone(), depth + 1, false));
                        pending.push((value.clone(), depth, false));
                        pending.push((type_.clone(), depth, false));
                    }
                    ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                        pending.push((expr.clone(), depth, false));
                    }
                    _ => return Ok(None),
                }
                continue;
            }
            let child = |expr: &Expr, depth: u32| {
                self.done
                    .get(&(expr.clone(), depth))
                    .expect("planned output child")
                    .clone()
            };
            let value = match expr.node() {
                ExprNode::App { f, a } => Expr::app(child(f, depth), child(a, depth)),
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::lam(
                    binder_name.clone(),
                    child(binder_type, depth),
                    child(body, depth + 1),
                    *binder_info,
                ),
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::forall_e(
                    binder_name.clone(),
                    child(binder_type, depth),
                    child(body, depth + 1),
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
                    child(type_, depth),
                    child(value, depth),
                    child(body, depth + 1),
                    *non_dep,
                ),
                ExprNode::MData { data, expr } => Expr::mdata(data.clone(), child(expr, depth)),
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => Expr::proj(struct_name.clone(), *idx, child(expr, depth)),
                _ => return Ok(None),
            };
            self.done.insert(key, value);
        }
        Ok(self.done.get(&(root.clone(), 0)).cloned())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn context() -> Context {
        Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        )
    }
    fn constant(name: &str) -> Expr {
        Expr::const_(Name::from_components([name]), vec![])
    }
    fn frame(pattern: Expr) -> Frame {
        let mut base = context();
        let id = MVarId(Name::from_components(["x"]));
        base.txn.mvars.declare(
            id.clone(),
            id.0.clone(),
            Expr::sort(Level::one()),
            LocalContext::new(),
            MetavarKind::Natural,
            0,
            None,
        );
        Frame {
            goal: MVarId(Name::from_components(["goal"])),
            target: Expr::app(constant("C"), Expr::mvar(id)),
            expected: Expr::app(constant("C"), pattern),
            key: Expr::app(constant("C"), Expr::bvar(0).unwrap()),
            binders: Vec::new(),
            base,
            candidates: Vec::new(),
            cursor: 0,
            chosen: None,
            children: Vec::new(),
            resumable: true,
            replay_first: false,
            returned: false,
        }
    }
    fn hole() -> Expr {
        Expr::mvar(MVarId(Name::from_components(["x"])))
    }

    #[test]
    fn every_container_preserves_its_data_and_raises_only_key_placeholders() {
        let nat = constant("Nat");
        let name = Name::from_components(["n"]);
        let x = hole();
        let marker = Expr::bvar(1).unwrap();
        let raised = Expr::bvar(2).unwrap();
        let identity = Expr::lam(
            name.clone(),
            nat.clone(),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        );
        let pairs = [
            (
                Expr::app(identity.clone(), x.clone()),
                Expr::app(identity, marker.clone()),
            ),
            (
                Expr::lam(name.clone(), nat.clone(), x.clone(), BinderInfo::Implicit),
                Expr::lam(
                    name.clone(),
                    nat.clone(),
                    raised.clone(),
                    BinderInfo::Implicit,
                ),
            ),
            (
                Expr::forall_e(
                    name.clone(),
                    nat.clone(),
                    x.clone(),
                    BinderInfo::InstImplicit,
                ),
                Expr::forall_e(
                    name.clone(),
                    nat.clone(),
                    raised.clone(),
                    BinderInfo::InstImplicit,
                ),
            ),
            (
                Expr::let_e(name.clone(), x.clone(), x.clone(), x.clone(), true),
                Expr::let_e(name.clone(), marker.clone(), marker.clone(), raised, true),
            ),
            (
                Expr::mdata(KVMap::new(), x.clone()),
                Expr::mdata(KVMap::new(), marker.clone()),
            ),
            (Expr::proj(name.clone(), 5, x), Expr::proj(name, 5, marker)),
        ];
        let mut context = context();
        for (pattern, expected) in pairs {
            let input = frame(pattern);
            let before = input.base.txn.mvars.clone();
            let output = canonical(&mut context, &input).unwrap().unwrap();
            assert_eq!(output.expected, Expr::app(constant("C"), expected));
            assert_eq!(output.types, vec![Expr::sort(Level::one())]);
            assert!(output.units > 1);
            assert_eq!(input.base.txn.mvars, before);
        }
    }

    #[test]
    fn shared_holes_under_distinct_binder_depths_do_not_capture_locals() {
        let name = Name::from_components(["n"]);
        let pattern = Expr::app(
            hole(),
            Expr::lam(name.clone(), constant("Nat"), hole(), BinderInfo::Default),
        );
        let output = canonical(&mut context(), &frame(pattern)).unwrap().unwrap();
        let expected = Expr::app(
            Expr::bvar(1).unwrap(),
            Expr::lam(
                name,
                constant("Nat"),
                Expr::bvar(2).unwrap(),
                BinderInfo::Default,
            ),
        );
        assert_eq!(output.expected, Expr::app(constant("C"), expected));
        assert_eq!(output.types.len(), 1);
    }

    #[test]
    fn shared_output_dags_are_linear_and_deep_binders_use_the_heap() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut pattern = hole();
                for _ in 0..40 {
                    pattern = Expr::app(Expr::app(constant("Pair"), pattern.clone()), pattern);
                }
                let mut context = context();
                context.txn.budget.max_heartbeats = 1000;
                let result = canonical(&mut context, &frame(pattern)).unwrap().unwrap();
                assert!(result.units < 200);
                assert!(!result.expected.has_expr_mvar());
                assert_eq!(result.types.len(), 1);
                let mut pattern = hole();
                for _ in 0..2000 {
                    pattern = Expr::forall_e(
                        Name::anonymous(),
                        constant("Nat"),
                        pattern,
                        BinderInfo::Default,
                    );
                }
                context.txn.budget.max_heartbeats = 20_000;
                let result = canonical(&mut context, &frame(pattern)).unwrap().unwrap();
                assert!(result.units < 5000);
                assert_eq!(result.types.len(), 1);
                assert!(result.expected.has_loose_bvars());
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn key_resources_never_mutate_the_live_or_original_hole_stores() {
        let mut pattern = hole();
        for _ in 0..30 {
            pattern = Expr::app(constant("Box"), pattern);
        }
        let input = frame(pattern);
        let before = input.base.txn.mvars.clone();
        let mut context = context();
        context.txn.budget.max_heartbeats = 10;
        assert!(canonical(&mut context, &input).is_err());
        assert_eq!(input.base.txn.mvars, before);
        assert!(context.txn.mvars.is_empty());
        context.txn.budget.max_heartbeats = 0;
        let mut table = GroundTable {
            key_units: MAX_KEY_UNITS - 5,
            ..GroundTable::default()
        };
        table
            .exhausted(&mut context, &input, &[frame(constant("Root"))])
            .unwrap();
        assert_eq!(table.entries, 0);
        assert!(table.answers.is_empty());
    }

    #[test]
    fn preexisting_loose_variables_cannot_impersonate_template_holes() {
        let mut context = context();
        for pattern in [
            Expr::bvar(1).unwrap(),
            Expr::app(hole(), Expr::bvar(0).unwrap()),
        ] {
            assert!(canonical(&mut context, &frame(pattern)).unwrap().is_none());
        }
        let input = frame(Expr::app(
            constant("Box"),
            Expr::mvar(MVarId(Name::from_components(["foreign"]))),
        ));
        assert!(canonical(&mut context, &input).unwrap().is_none());
    }
}
