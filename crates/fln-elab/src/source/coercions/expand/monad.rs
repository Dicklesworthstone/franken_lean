//! The two `@[coe_decl] abbrev` monadic bridges in pinned Init/Coe.lean.
//! Unfold only their admitted bodies, under instances transparency, followed
//! by head beta. A general WHNF here would also execute untagged user heads.
use super::*;

impl Context {
    pub(super) fn expand_monadic_helper(
        &mut self,
        name: &Name,
        levels: &[Level],
        args: &[Expr],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        if !matches!(name.leaf_view(), LeafView::Str("coeM" | "liftCoeM")) {
            return Ok(None);
        }
        let internal = name.parent();
        let lean = internal.parent();
        if !matches!(internal.leaf_view(), LeafView::Str("Internal"))
            || !matches!(lean.leaf_view(), LeafView::Str("Lean"))
            || !lean.parent().is_anonymous()
        {
            return Ok(None);
        }
        let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned() else {
            return Ok(None);
        };
        let statuses = crate::reducibility::table(&self.txn.env).map_err(|error| {
            failure(SourceInferenceError::Unification(Box::new(
                UnificationError::Reducibility(error),
            )))
        })?;
        // A recorded status overrides the default, including an explicitly
        // irreducible abbreviation. Missing metadata falls back to the
        // abbreviation hint, as it does in the native source reducer.
        let unfold = match statuses.get(name) {
            Some(status) => status.unfolds_at_instances(),
            None => definition.hints == ReducibilityHints::Abbrev,
        };
        if !unfold
            || definition.safety != DefinitionSafety::Safe
            || definition.base.level_params.len() != levels.len()
        {
            return Ok(None);
        }
        let mut value =
            self.instantiate_params(&definition.value, &definition.base.level_params, levels)?;
        let mut arguments: Vec<_> = args.iter().rev().cloned().collect();
        loop {
            self.tick()?;
            match value.node() {
                ExprNode::App { f, a } => {
                    arguments.push(a.clone());
                    value = f.clone();
                }
                ExprNode::Lam { body, .. } if !arguments.is_empty() => {
                    let argument = arguments.pop().expect("guarded helper head beta");
                    value = self.substitute(body, &argument)?;
                }
                _ => break,
            }
        }
        for argument in arguments.into_iter().rev() {
            self.tick()?;
            value = Expr::app(value, argument);
        }
        Ok(Some(value))
    }
}
