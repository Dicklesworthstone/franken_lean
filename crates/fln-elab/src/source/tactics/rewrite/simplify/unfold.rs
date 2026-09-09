//! Selected-definition expansion and beta/zeta normalization on a shared DAG.
//! Only the named safe definition or local let is unfolded. Its actual body is
//! instantiated at each occurrence's universe arguments, never at guessed levels.

use super::*;
use fln_env::constants::{ConstantInfo, DefinitionVal};

enum Selection {
    Global(DefinitionVal),
    Local(FVarId, Expr),
}

pub(super) enum UnfoldResult {
    NotDefinition,
    Unchanged,
    Changed(Expr),
}

impl Context {
    /// Selection respects local shadowing. A local proof/parameter with this
    /// name must not accidentally request expansion of a same-named global.
    pub(super) fn unfold_simp_term(
        &mut self,
        syntax: &Syntax,
        reverse: bool,
        target: &Expr,
    ) -> Result<UnfoldResult, NatDefinitionElabError> {
        let Syntax::Ident { val: name, .. } = syntax else {
            return Ok(UnfoldResult::NotDefinition);
        };
        let selection = if let Some(local) = self
            .txn
            .lctx
            .decls()
            .iter()
            .rev()
            .find(|l| &l.user_name == name)
        {
            match &local.value {
                Some(value) => Selection::Local(local.id.clone(), value.clone()),
                None => return Ok(UnfoldResult::NotDefinition),
            }
        } else {
            match self.txn.env.find(name) {
                Some(ConstantInfo::Defn(definition))
                    if definition.safety == DefinitionSafety::Safe =>
                {
                    Selection::Global(definition.clone())
                }
                _ => return Ok(UnfoldResult::NotDefinition),
            }
        };
        if reverse {
            return Err(error(TacticError::MalformedScript));
        }
        let result = self.simp_unfold_selected(target, &selection)?;
        if self.rewrite_same(&result, target)? {
            Ok(UnfoldResult::Unchanged)
        } else {
            Ok(UnfoldResult::Changed(result))
        }
    }

    fn simp_unfold_selected(
        &mut self,
        root: &Expr,
        selection: &Selection,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut done: HashMap<usize, Expr> = HashMap::new();
        let mut work = vec![(root, false)];
        while let Some((term, exit)) = work.pop() {
            self.tick()?;
            let key = term.allocation_identity();
            if done.contains_key(&key) {
                continue;
            }
            if !exit {
                work.push((term, true));
                work.extend(
                    children(term)
                        .into_iter()
                        .rev()
                        .flatten()
                        .map(|child| (child, false)),
                );
                continue;
            }
            let child = |term: &Expr| done[&term.allocation_identity()].clone();
            let rebuilt = match term.node() {
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
                ExprNode::Const { name, levels } => match selection {
                    Selection::Global(definition) if name == &definition.base.name => self
                        .instantiate_params(
                            &definition.value,
                            &definition.base.level_params,
                            levels,
                        )?,
                    _ => term.clone(),
                },
                ExprNode::FVar { id } => match selection {
                    Selection::Local(selected, value) if selected == id => value.clone(),
                    _ => term.clone(),
                },
                _ => term.clone(),
            };
            let normalized = self.simp_beta_zeta(&rebuilt)?;
            done.insert(key, normalized);
        }
        Ok(done
            .remove(&root.allocation_identity())
            .expect("selected unfolding finishes the root"))
    }

    /// No delta or local-context lookup here. In particular, calling the source
    /// elaborator's general whnf would unfold definitions absent from the list.
    fn simp_beta_zeta(&mut self, root: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let mut head = root.clone();
        let mut arguments = Vec::new();
        let mut reduced = false;
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    arguments.push(a.clone());
                    head = f.clone();
                }
                ExprNode::LetE { body, value, .. } => {
                    reduced = true;
                    head = self.substitute(body, value)?;
                }
                ExprNode::Lam { body, .. } if !arguments.is_empty() => {
                    reduced = true;
                    let argument = arguments.pop().expect("nonempty beta application");
                    head = self.substitute(body, &argument)?;
                }
                ExprNode::MData { expr, .. } if !arguments.is_empty() => head = expr.clone(),
                _ => break,
            }
        }
        if !reduced {
            return Ok(root.clone());
        }
        for argument in arguments.into_iter().rev() {
            self.tick()?;
            head = Expr::app(head, argument);
        }
        Ok(head)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unfolding_selects_only_the_requested_global_even_below_binders() {
        let name = Name::from_components(["selected"]);
        let other = Name::from_components(["unselected"]);
        let ty = Expr::sort(Level::one());
        let body = Expr::lam(
            Name::anonymous(),
            ty.clone(),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        );
        let definition = DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: Vec::new(),
                type_: Expr::forall_e(
                    Name::anonymous(),
                    ty.clone(),
                    ty.clone(),
                    BinderInfo::Default,
                ),
            },
            value: body,
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![name.clone()],
        };
        let selected = Expr::const_(name, Vec::new());
        let untouched = Expr::const_(other, Vec::new());
        let input = Expr::lam(
            Name::anonymous(),
            ty.clone(),
            Expr::app(
                untouched.clone(),
                Expr::app(selected, Expr::bvar(0).unwrap()),
            ),
            BinderInfo::Default,
        );
        let expected = Expr::lam(
            Name::anonymous(),
            ty,
            Expr::app(untouched, Expr::bvar(0).unwrap()),
            BinderInfo::Default,
        );
        let mut ctx = Context::new(&Environment::new(), Budget::for_stack_bytes(1024 * 1024));
        assert_eq!(
            ctx.simp_unfold_selected(&input, &Selection::Global(definition))
                .unwrap(),
            expected
        );
    }

    #[test]
    fn selected_local_unfolding_preserves_shared_dags_and_respects_work_limits() {
        let id = FVarId(Name::from_components(["selected"]));
        let value = Expr::sort(Level::zero());
        let mut input = Expr::fvar(id.clone());
        for _ in 0..40 {
            input = Expr::app(input.clone(), input);
        }
        let selection = Selection::Local(id, value);
        let mut ctx = Context::new(&Environment::new(), Budget::for_stack_bytes(1024 * 1024));
        let mut output = ctx.simp_unfold_selected(&input, &selection).unwrap();
        for _ in 0..40 {
            let ExprNode::App { f, a } = output.node() else {
                panic!("application retained");
            };
            assert_eq!(f.allocation_identity(), a.allocation_identity());
            output = f.clone();
        }
        ctx.txn.budget.max_heartbeats = 1;
        assert!(matches!(
            ctx.simp_unfold_selected(&input, &selection),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
    }
}
