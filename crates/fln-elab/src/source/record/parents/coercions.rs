//! Parent conversions are ordinary Coe/CoeDep instances, not special trusted
//! casts. The existing coercion search therefore retains its selection policy.
use super::*;
use crate::records::{Builder, app, fresh, fv};

impl Context {
    pub(in crate::source::record) fn record_parent_coercions(
        &mut self,
        spec: &RecordSpec,
        parents: &[RecordParent],
        budget: RecordBudget,
    ) -> Result<Vec<DefinitionVal>, NatDefinitionElabError> {
        let registry = InstanceRegistry::read(&self.txn.env)
            .map_err(|e| failure(SourceInferenceError::InstanceRegistry(e)))?;
        let mut output = Vec::new();
        let mut builder = Builder {
            remaining: budget.max_nodes,
        };
        let source = app(
            Expr::const_(
                spec.name.clone(),
                spec.level_params
                    .iter()
                    .cloned()
                    .map(Level::param)
                    .collect(),
            ),
            spec.parameters.iter().map(fv),
        );
        let parameters: HashSet<_> = spec.parameters.iter().map(|p| p.id.clone()).collect();
        let mut used: HashSet<_> = self.txn.lctx.decls().iter().map(|l| l.id.clone()).collect();
        let receiver = fresh(&mut used, "self", source.clone(), BinderInfo::Default);
        for parent in parents {
            self.tick()?;
            if parent.record != spec.name {
                return Err(failure(SourceInferenceError::Scope));
            }
            let field = spec
                .fields
                .get(parent.field as usize)
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            let dependent = self
                .elimination_reads(&field.type_)?
                .iter()
                .any(|id| !parameters.contains(id));
            let class = if dependent { "CoeDep" } else { "Coe" };
            if !registry.is_class(&Name::from_components([class])) {
                // The minimal source seed intentionally has no coercion library.
                continue;
            }
            let sort = self
                .known_type(&field.type_)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            let sort = self.whnf(&sort)?;
            let ExprNode::Sort { level } = sort.node() else {
                return Err(failure(SourceInferenceError::ExpectedType));
            };
            let levels = vec![spec.result_level.clone(), level.clone()];
            let mut target = field.type_.clone();
            for (index, earlier) in spec.fields[..parent.field as usize].iter().enumerate() {
                self.tick()?;
                target = target
                    .abstract_fvar(&earlier.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                target = self.substitute(
                    &target,
                    &Expr::proj(spec.name.clone(), index as u64, fv(&receiver)),
                )?;
            }
            let projection = Expr::proj(spec.name.clone(), u64::from(parent.field), fv(&receiver));
            let mut args = vec![source.clone()];
            if dependent {
                args.push(fv(&receiver));
            }
            args.push(target);
            let mut type_ = app(
                Expr::const_(Name::from_components([class]), levels.clone()),
                args.clone(),
            );
            let value = if dependent {
                projection
            } else {
                builder
                    .close(std::slice::from_ref(&receiver), projection, true, false)
                    .map_err(record_error)?
            };
            let mut value = app(
                Expr::const_(Name::from_components([class, "mk"]), levels),
                args.into_iter().chain([value]),
            );
            if dependent {
                type_ = builder
                    .close(std::slice::from_ref(&receiver), type_, false, false)
                    .map_err(record_error)?;
                value = builder
                    .close(std::slice::from_ref(&receiver), value, true, false)
                    .map_err(record_error)?;
            }
            let name = Name::num(
                Name::str(spec.name.clone(), "_parentCoe"),
                u64::from(parent.field),
            );
            output.push(DefinitionVal {
                base: ConstantVal {
                    name: name.clone(),
                    level_params: spec.level_params.clone(),
                    type_: builder
                        .close(&spec.parameters, type_, false, true)
                        .map_err(record_error)?,
                },
                value: builder
                    .close(&spec.parameters, value, true, true)
                    .map_err(record_error)?,
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![name],
            });
        }
        Ok(output)
    }
}
