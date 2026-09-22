//! Checked, lexical section parameters. Their types are resolved at the
//! variable command, not reinterpreted after a later `open` or declaration.
//! They become ordinary Pi/lambda binders; no section state reaches admission.
use super::*;
use std::collections::HashSet;

pub const MAX_SECTION_VARIABLES: usize = 4096;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SectionVariables {
    locals: LocalContext,
    next: u64,
    levels: Vec<Name>,
}

impl SectionVariables {
    pub fn len(&self) -> usize {
        self.locals.len()
    }

    pub fn is_empty(&self) -> bool {
        self.locals.is_empty()
    }

    pub(in crate::source) fn locals(&self) -> &LocalContext {
        &self.locals
    }

    pub(in crate::source) fn next(&self) -> u64 {
        self.next
    }

    pub(in crate::source) fn levels(&self) -> &[Name] {
        &self.levels
    }
}

/// Return a successor only after the entire telescope is elaborated, all holes
/// are resolved, and its closed type passes the ordinary kernel. This check
/// publishes no axiom or other declaration, even for unused section variables.
pub fn declare(
    syntax: &Syntax,
    env: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<SectionVariables, NatDefinitionElabError> {
    let mut context = Context::scoped(env, kernel, scope);
    context.declare_levels(&Syntax::node(Name::from_components(["null"]), vec![]))?;
    context.infer_level_params = true;
    context.bind_parameters(syntax)?;
    if context.txn.lctx.len() > MAX_SECTION_VARIABLES {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    let mut names = HashSet::new();
    let mut locals = context.txn.lctx.decls().to_vec();
    for local in &locals {
        context.tick()?;
        if !names.insert(local.user_name.clone()) {
            return Err(error(ScopeError::InvalidName));
        }
    }
    let types: Vec<_> = locals.iter().map(|local| local.type_.clone()).collect();
    context.generalize_declaration_universes(&types)?;
    for local in &mut locals {
        local.type_ = context.instantiate(&local.type_)?;
        context.require_resolved(std::slice::from_ref(&local.type_))?;
    }
    let mut closed = Expr::sort(Level::zero());
    for local in locals.iter().rev() {
        context.tick()?;
        closed = closed
            .abstract_fvar(&local.id, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        closed = Expr::forall_e(
            local.user_name.clone(),
            local.type_.clone(),
            closed,
            local.binder_info,
        );
    }
    let name = loop {
        let name = context.fresh_name()?;
        if !env.contains(&name) {
            break name;
        }
    };
    let declaration = Declaration::Axiom(fln_env::constants::AxiomVal {
        base: ConstantVal {
            name,
            level_params: context.declaration_levels(std::slice::from_ref(&closed))?,
            type_: closed,
        },
        is_unsafe: false,
    });
    match check(env, &declaration, kernel) {
        Outcome::Complete(Verdict::Accepted { .. }) => {}
        outcome => {
            return Err(failure(SourceInferenceError::TypeObligation(Box::new(
                outcome,
            ))));
        }
    }
    let mut lctx = LocalContext::new();
    for local in locals {
        lctx.add_param(local.id, local.user_name, local.type_, local.binder_info);
    }
    Ok(SectionVariables {
        locals: lctx,
        next: context.next,
        levels: context.level_params,
    })
}

impl Context {
    /// Metered DAG traversal, including annotation and let domains. This must
    /// inspect instantiated terms so dictionary/unification assignments cannot
    /// hide a dependency from generalization or theorem-header filtering.
    fn section_dependencies(
        &mut self,
        roots: &[Expr],
    ) -> Result<HashSet<FVarId>, NatDefinitionElabError> {
        let mut pending = Vec::new();
        for root in roots {
            pending.push(self.instantiate(root)?);
        }
        let mut seen = HashSet::new();
        let mut used = HashSet::new();
        while let Some(expr) = pending.pop() {
            self.tick()?;
            if !seen.insert(expr.allocation_identity()) {
                continue;
            }
            match expr.node() {
                ExprNode::FVar { id } => {
                    used.insert(id.clone());
                }
                ExprNode::App { f, a } => pending.extend([f.clone(), a.clone()]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    pending.extend([binder_type.clone(), body.clone()]);
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => pending.extend([type_.clone(), value.clone(), body.clone()]),
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    pending.push(expr.clone())
                }
                _ => {}
            }
        }
        Ok(used)
    }

    /// Dependencies close in reverse declaration order; instance parameters are
    /// then included only when every variable in their type is already included.
    /// The theorem caller runs this before elaborating the proof and removes all
    /// other section locals, so a proof cannot silently strengthen its statement.
    pub(in crate::source) fn section_parameters(
        &mut self,
        roots: &[Expr],
        include_instances: bool,
    ) -> Result<Vec<LocalDecl>, NatDefinitionElabError> {
        let locals = self.source_scope.variables.locals.decls().to_vec();
        let mut used = self.section_dependencies(roots)?;
        for local in locals.iter().rev() {
            self.tick()?;
            if used.contains(&local.id) {
                used.extend(self.section_dependencies(std::slice::from_ref(&local.type_))?);
            }
        }
        if include_instances {
            for local in &locals {
                self.tick()?;
                if local.binder_info == BinderInfo::InstImplicit
                    && self
                        .section_dependencies(std::slice::from_ref(&local.type_))?
                        .iter()
                        .all(|id| used.contains(id))
                {
                    used.insert(local.id.clone());
                }
            }
        }
        Ok(locals
            .into_iter()
            .filter(|local| used.contains(&local.id))
            .collect())
    }

    pub(in crate::source) fn restrict_section_locals(&mut self, selected: &[LocalDecl]) {
        let all: HashSet<_> = self
            .source_scope
            .variables
            .locals
            .decls()
            .iter()
            .map(|local| &local.id)
            .collect();
        let keep: HashSet<_> = selected.iter().map(|local| &local.id).collect();
        let mut lctx = LocalContext::new();
        for local in self.txn.lctx.decls() {
            if !all.contains(&local.id) || keep.contains(&local.id) {
                lctx.add_param(
                    local.id.clone(),
                    local.user_name.clone(),
                    local.type_.clone(),
                    local.binder_info,
                );
            }
        }
        self.txn.lctx = lctx;
    }
}
