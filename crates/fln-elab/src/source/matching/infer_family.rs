//! Constructor patterns can constrain a previously unknown discriminant type.
//!
//! A local function defined by equations may have neither written parameters
//! nor a result annotation. Its generated lambda domains are ordinary holes.
//! Resolve an actual constructor before selecting an eliminator, then let the
//! ordinary unifier check the family application. This is only a type hint:
//! every pattern, branch, recursive call and final declaration is still checked.
use super::*;

impl Context {
    pub(super) fn infer_match_family(
        &mut self,
        parts: &MatchParts<'_>,
        discriminant_type: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        if !discriminant_type.has_expr_mvar() {
            return Ok(());
        }
        let type_ = self.whnf(discriminant_type)?;
        let ExprNode::MVar { id } = type_.node() else {
            return Ok(());
        };
        let Some(declaration) = self.txn.mvars.get_decl(id) else {
            return Ok(());
        };
        let inference_context = declaration.lctx.clone();
        for alternative in parts.alternatives {
            self.tick()?;
            let alternative = expect_node(
                alternative,
                &parser_kind(&["Term", "matchAlt"]),
                4,
                "match alternative",
            )?;
            let [sequence] = expect_null_args(&alternative[1], "single pattern sequence")? else {
                continue;
            };
            let [pattern] = expect_null_args(sequence, "single pattern")? else {
                continue;
            };
            let mut pattern = pattern;
            while let Some(inner) = parenthesized_inner(pattern)? {
                self.tick()?;
                pattern = inner;
            }
            let head = match pattern {
                Syntax::Node { kind, args, .. }
                    if kind == &parser_kind(&["Term", "app"])
                        || (parts.generated
                            && kind == &parser_kind(&["Term", "matrixCtorPattern"])) =>
                {
                    let [head, _] = args.as_slice() else {
                        return Err(error(MatchError::InvalidPattern));
                    };
                    head
                }
                pattern => pattern,
            };
            // Relative constructors and anonymous constructor notation need a
            // known expected family. Do not search unrelated declarations or
            // turn an ordinary pattern binder into a type annotation.
            let Syntax::Ident { .. } = head else {
                continue;
            };
            let (Some(resolved), explicit_target) =
                self.resolve_unambiguous_identifier_name(head)?
            else {
                continue;
            };
            if !explicit_target && self.txn.lctx.find_by_user_name(&resolved).is_some() {
                continue;
            }
            let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(&resolved) else {
                continue;
            };
            let Some(ConstantInfo::Induct(family)) = self.txn.env.find(&constructor.induct) else {
                return Err(error(MatchError::UnsupportedFamily));
            };
            // Inferring constrained indices needs the full pattern telescope;
            // this hint covers only unindexed families. Its fresh parameters
            // remain available for the constructor fields and later arguments.
            if constructor.is_unsafe
                || family.is_unsafe
                || family.num_indices != 0
                || family.all.len() != 1
                || !family.ctors.contains(&resolved)
            {
                return Ok(());
            }
            let name = family.base.name.clone();
            let parameters = family.num_params;
            let mut application = self.constant(&name)?;
            for _ in 0..parameters {
                self.tick()?;
                let type_ = self.whnf(&application.type_)?;
                let ExprNode::ForallE {
                    binder_type, body, ..
                } = type_.node()
                else {
                    return Err(error(MatchError::UnsupportedFamily));
                };
                // This domain hole predates its discriminant binder. A fresh
                // family parameter must have that same scope, rather than
                // capture the discriminant or later equation arguments. The
                // assignment checker deliberately refuses such residuals.
                let saved = std::mem::replace(&mut self.txn.lctx, inference_context.clone());
                let parameter = self.hole(binder_type.clone());
                self.txn.lctx = saved;
                let parameter = parameter?;
                application.value = Expr::app(application.value, parameter.clone());
                application.type_ = self.substitute(body, &parameter)?;
            }
            self.sort_level(&application)?;
            self.constrain_type(discriminant_type, &application.value)?;
            self.flush(false)?;
            return Ok(());
        }
        Ok(())
    }
}
