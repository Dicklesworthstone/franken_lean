//! The pin's `_flat_ctor`: ordinary checked definitions whose arguments are the
//! non-parent fields in constructor order. Parent subobjects are rebuilt by
//! applying their admitted constructors, including dependent parent telescopes.
use super::*;
use crate::records::inheritance::RecordParents;
use fln_env::constants::ConstantInfo;
use std::collections::HashSet;

struct Frame {
    record: Name,
    value: Expr,
    type_: Expr,
    index: u32,
    fields: u32,
}

fn problem(error: crate::records::RecordError) -> NatDefinitionElabError {
    failure(SourceInferenceError::Record(error))
}

impl Context {
    fn flat_parent_frame(&mut self, type_: Expr) -> Result<Frame, NatDefinitionElabError> {
        let type_ = self.whnf(&type_)?;
        let mut head = &type_;
        let mut arguments = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            arguments.push(a.clone());
            head = f;
        }
        arguments.reverse();
        let ExprNode::Const { name, levels } = head.node() else {
            return Err(problem(crate::records::RecordError::InvalidTelescope));
        };
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(name).cloned() else {
            return Err(problem(crate::records::RecordError::InvalidTelescope));
        };
        if family.is_unsafe
            || family.is_rec
            || family.num_indices != 0
            || family.ctors.len() != 1
            || arguments.len() != family.num_params as usize
            || levels.len() != family.base.level_params.len()
        {
            return Err(problem(crate::records::RecordError::InvalidTelescope));
        }
        let Some(ConstantInfo::Ctor(ctor)) = self.txn.env.find(&family.ctors[0]).cloned() else {
            return Err(problem(crate::records::RecordError::InvalidTelescope));
        };
        let mut frame = Frame {
            record: name.clone(),
            value: Expr::const_(ctor.base.name.clone(), levels.clone()),
            type_: self.instantiate_params(&ctor.base.type_, &ctor.base.level_params, levels)?,
            index: 0,
            fields: ctor.num_fields,
        };
        for argument in arguments {
            self.tick()?;
            let ExprNode::ForallE { body, .. } = frame.type_.node() else {
                return Err(problem(crate::records::RecordError::InvalidTelescope));
            };
            frame.type_ = self.substitute(body, &argument)?;
            frame.value = Expr::app(frame.value, argument);
        }
        Ok(frame)
    }

    pub(super) fn record_flat_constructor(
        &mut self,
        spec: &RecordSpec,
        parents: &[RecordParent],
        budget: RecordBudget,
    ) -> Result<Declaration, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let registry = RecordParents::read(&self.txn.env).map_err(problem)?;
            let mut closer = crate::records::Builder {
                remaining: budget.max_nodes,
            };
            let levels: Vec<_> = spec
                .level_params
                .iter()
                .cloned()
                .map(Level::param)
                .collect();
            let parameters: Vec<_> = spec
                .parameters
                .iter()
                .map(|p| Expr::fvar(p.id.clone()))
                .collect();
            let target = parameters
                .iter()
                .cloned()
                .fold(Expr::const_(spec.name.clone(), levels.clone()), Expr::app);
            let ctor_name = Name::str(spec.name.clone(), "mk");
            let value = parameters
                .into_iter()
                .fold(Expr::const_(ctor_name.clone(), levels), Expr::app);
            let type_ = closer
                .close(&spec.fields, target.clone(), false, false)
                .map_err(problem)?;
            let mut frames = vec![Frame {
                record: spec.name.clone(),
                value,
                type_,
                index: 0,
                fields: u32::try_from(spec.fields.len())
                    .map_err(|_| problem(crate::records::RecordError::ResourceLimit))?,
            }];
            let mut fields = Vec::new();
            let mut labels = HashSet::new();
            let value = loop {
                self.tick()?;
                closer.tick().map_err(problem)?;
                let frame = frames
                    .last_mut()
                    .ok_or_else(|| problem(crate::records::RecordError::InvalidTelescope))?;
                if frame.index == frame.fields {
                    let value = frames.pop().expect("nonempty frame stack").value;
                    let Some(parent) = frames.last_mut() else {
                        break value;
                    };
                    let ExprNode::ForallE { body, .. } = parent.type_.node() else {
                        return Err(problem(crate::records::RecordError::InvalidTelescope));
                    };
                    parent.type_ = self.substitute(body, &value)?;
                    parent.value = Expr::app(parent.value.clone(), value);
                    parent.index += 1;
                    continue;
                }
                let ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    binder_info,
                    body,
                } = frame.type_.node()
                else {
                    return Err(problem(crate::records::RecordError::InvalidTelescope));
                };
                let rows = if frame.record == spec.name {
                    parents
                } else {
                    registry.parents(&frame.record)
                };
                if let Some(parent) = rows.iter().find(|parent| parent.field == frame.index) {
                    let nested = self.flat_parent_frame(binder_type.clone())?;
                    if nested.record != parent.parent {
                        return Err(problem(crate::records::RecordError::InvalidTelescope));
                    }
                    if frames.len() >= budget.max_binders {
                        return Err(problem(crate::records::RecordError::ResourceLimit));
                    }
                    frames.push(nested);
                    continue;
                }
                if !labels.insert(binder_name.clone()) {
                    return Err(problem(crate::records::RecordError::DuplicateField));
                }
                if spec
                    .parameters
                    .len()
                    .saturating_add(fields.len())
                    .saturating_add(1)
                    > budget.max_binders
                {
                    return Err(problem(crate::records::RecordError::ResourceLimit));
                }
                let id = FVarId(self.fresh_name()?);
                let local = self
                    .txn
                    .lctx
                    .add_param(
                        id.clone(),
                        binder_name.clone(),
                        binder_type.clone(),
                        *binder_info,
                    )
                    .clone();
                let value = Expr::fvar(id);
                frame.type_ = self.substitute(body, &value)?;
                frame.value = Expr::app(frame.value.clone(), value);
                frame.index += 1;
                fields.push(local);
            };
            let type_ = closer
                .close(&fields, target, false, false)
                .map_err(problem)?;
            let type_ = closer
                .close(&spec.parameters, type_, false, true)
                .map_err(problem)?;
            let value = closer.close(&fields, value, true, false).map_err(problem)?;
            let value = closer
                .close(&spec.parameters, value, true, true)
                .map_err(problem)?;
            let name = Name::str(ctor_name, "_flat_ctor");
            Ok(Declaration::Defn(DefinitionVal {
                base: ConstantVal {
                    name: name.clone(),
                    level_params: spec.level_params.clone(),
                    type_,
                },
                value,
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![name],
            }))
        })();
        self.txn.lctx = saved;
        result
    }
}
