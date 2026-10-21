//! Only class parent projections are registered as instances by `extends`.
//!
//! Pinned `Lean/Elab/Structure.lean::addParentInstances` registers the existing
//! projection from a child class to its parent class. It does not synthesize
//! `Coe` or `CoeDep` dictionaries for values of structures or classes. Those
//! conversions require ordinary user instances, just like other coercions.
use super::*;

impl Context {
    pub(in crate::source::record) fn record_parent_instances(
        &mut self,
        spec: &RecordSpec,
        parents: &[RecordParent],
    ) -> Result<Vec<Name>, NatDefinitionElabError> {
        let mut output = Vec::new();
        if !spec.is_class {
            return Ok(output);
        }
        let registry = self.instance_registry()?;
        for parent in parents {
            self.tick()?;
            if parent.record != spec.name {
                return Err(failure(SourceInferenceError::Scope));
            }
            let field = spec
                .fields
                .get(parent.field as usize)
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            if registry.is_class(&parent.parent) {
                output.push(spec.name.append_core(&field.user_name));
            }
        }
        Ok(output)
    }

    /// Each copied parent's projection `D.toC` (the pin's `mkCoercionToCopiedParent`, vendored
    /// `Lean/Elab/Structure.lean:1409-1440`): `fun {params} (self : D params) => C.mk params …`,
    /// each field of the record read through its projection, an abbreviation. Between classes
    /// it is an instance (`addParentInstances`), and its receiver an instance binder; the
    /// names of those are returned too.
    pub(in crate::source::record) fn copied_parent_projections(
        &mut self,
        spec: &RecordSpec,
        copied: Vec<CopiedParent>,
        aliases: &[LocalDecl],
        budget: RecordBudget,
    ) -> Result<(Vec<Declaration>, Vec<Name>), NatDefinitionElabError> {
        let mut declarations = Vec::new();
        let mut instances = Vec::new();
        if copied.is_empty() {
            return Ok((declarations, instances));
        }
        let classes = self.instance_registry()?;
        let levels: Vec<Level> = spec
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect();
        let applied = |head: Name| {
            spec.parameters
                .iter()
                .fold(Expr::const_(head, levels.clone()), |f, parameter| {
                    Expr::app(f, Expr::fvar(parameter.id.clone()))
                })
        };
        let receiver_type = applied(spec.name.clone());
        let mut closer = crate::records::Builder {
            remaining: budget.max_nodes,
        };
        for copy in copied {
            self.tick()?;
            let instance = spec.is_class && classes.is_class(&copy.parent);
            let receiver = LocalDecl {
                id: FVarId(self.fresh_name()?),
                user_name: Name::from_components(["self"]),
                type_: receiver_type.clone(),
                value: None,
                binder_info: if instance {
                    BinderInfo::InstImplicit
                } else {
                    BinderInfo::Default
                },
                index: 0,
            };
            let mut value = self.expand_record_aliases(copy.value, aliases)?;
            let mut type_ = self.expand_record_aliases(copy.type_, aliases)?;
            value = self.instantiate(&value)?;
            type_ = self.instantiate(&type_)?;
            for field in &spec.fields {
                self.tick()?;
                let projection = Expr::app(
                    applied(spec.name.append_core(&field.user_name)),
                    Expr::fvar(receiver.id.clone()),
                );
                for expr in [&mut value, &mut type_] {
                    *expr = expr
                        .abstract_fvar(&field.id, 0)
                        .map_err(|_| failure(SourceInferenceError::Scope))?;
                    *expr = self.substitute(expr, &projection)?;
                }
            }
            let record_error = |error| failure(SourceInferenceError::Record(error));
            let value = closer
                .close(std::slice::from_ref(&receiver), value, true, false)
                .and_then(|value| closer.close(&spec.parameters, value, true, true))
                .map_err(record_error)?;
            let type_ = closer
                .close(std::slice::from_ref(&receiver), type_, false, false)
                .and_then(|type_| closer.close(&spec.parameters, type_, false, true))
                .map_err(record_error)?;
            let name = spec.name.append_core(&copy.label);
            declarations.push(Declaration::Defn(DefinitionVal {
                base: ConstantVal {
                    name: name.clone(),
                    level_params: spec.level_params.clone(),
                    type_,
                },
                value,
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![name.clone()],
            }));
            if instance {
                instances.push(name);
            }
        }
        Ok((declarations, instances))
    }
}
