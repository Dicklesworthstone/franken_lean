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
        let mut head = &type_;
        let mut arguments = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            arguments.push(a.clone());
            head = f;
        }
        let ExprNode::MVar { id } = head.node() else {
            return Ok(());
        };
        let Some(declaration) = self.txn.mvars.get_decl(id).cloned() else {
            return Ok(());
        };
        let mut inference_context = declaration.lctx.clone();
        let mut captures = Vec::new();
        if !arguments.is_empty() {
            // A deferred field's type is a closed hole applied to its original
            // lexical scope. Use only that declared scope, never the later
            // discriminant or branch locals present at this match. Other
            // higher-order applications remain ordinary unification problems.
            if declaration.kind != MetavarKind::Natural
                || declaration.scope_args != Some(arguments.len())
            {
                return Ok(());
            }
            let mut distinct = HashSet::new();
            let mut telescope = declaration.type_.clone();
            for argument in arguments.iter().rev() {
                self.tick()?;
                let ExprNode::FVar { id } = argument.node() else {
                    return Ok(());
                };
                if inference_context.contains(id) || !distinct.insert(id.clone()) {
                    return Ok(());
                }
                let Some(mut local) = self.txn.lctx.find(id).cloned() else {
                    return Ok(());
                };
                if local.is_let() {
                    return Ok(());
                }
                let type_ = self.whnf(&telescope)?;
                let ExprNode::ForallE {
                    binder_type,
                    body,
                    binder_info,
                    ..
                } = type_.node()
                else {
                    return Ok(());
                };
                local.type_ = binder_type.clone();
                local.binder_info = *binder_info;
                telescope = self.substitute(body, argument)?;
                tactics::eliminate::add_local(&mut inference_context, &local);
                captures.push(local);
            }
        }
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
                // Fresh parameters have only the type hole's original scope.
                // An applied scope hole can legitimately depend on a captured
                // carrier, e.g. Option A, but not on later pattern variables.
                let saved = std::mem::replace(&mut self.txn.lctx, inference_context.clone());
                let parameter = self.hole(binder_type.clone());
                self.txn.lctx = saved;
                let mut parameter = Typed {
                    value: parameter?,
                    type_: binder_type.clone(),
                };
                // Close the parameter holes through the same explicit spine
                // before placing them in a solution of the closed type hole.
                // Otherwise their latent local context could escape even
                // though their visible type contains no free variables.
                self.capture_bound_metavars(&captures, &declaration.lctx, &mut parameter)?;
                let parameter = parameter.value;
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
