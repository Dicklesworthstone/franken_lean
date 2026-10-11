//! Identify admitted class field projections without trusting their spelling.
//!
//! The caller separately checks class registration and reducibility. This
//! descriptor requires the generated constructor field, instance receiver,
//! and exact projection body; an ordinary function that returns a field does
//! not acquire the Reference's `unfoldProjInst?` behavior.

use fln_core::expr::{BinderInfo, ExprNode};
use fln_core::name::Name;
use fln_env::constants::{ConstantInfo, DefinitionSafety, DefinitionVal};
use fln_env::environment::Environment;

pub(crate) struct ClassProjection {
    pub structure: Name,
    pub index: u64,
    pub parameters: usize,
}

pub(crate) fn class_projection<E>(
    environment: &Environment,
    definition: &DefinitionVal,
    mut tick: impl FnMut() -> Result<(), E>,
) -> Result<Option<ClassProjection>, E> {
    if definition.safety != DefinitionSafety::Safe
        || !matches!(
            environment.find(&definition.base.name.parent()),
            Some(ConstantInfo::Induct(_))
        )
    {
        return Ok(None);
    }
    let mut body = &definition.value;
    let mut binders = 0usize;
    let mut receiver = BinderInfo::Default;
    while let ExprNode::Lam {
        body: next,
        binder_info,
        ..
    } = body.node()
    {
        tick()?;
        let Some(count) = binders.checked_add(1) else {
            return Ok(None);
        };
        binders = count;
        receiver = *binder_info;
        body = next;
    }
    tick()?;
    let ExprNode::Proj {
        struct_name,
        idx,
        expr,
    } = body.node()
    else {
        return Ok(None);
    };
    if receiver != BinderInfo::InstImplicit || !matches!(expr.node(), ExprNode::BVar { idx: 0 }) {
        return Ok(None);
    }
    let Some(ConstantInfo::Induct(family)) = environment.find(struct_name) else {
        return Ok(None);
    };
    let Ok(parameters) = usize::try_from(family.num_params) else {
        return Ok(None);
    };
    if family.is_unsafe
        || family.num_indices != 0
        || family.ctors.len() != 1
        || parameters.checked_add(1) != Some(binders)
        || definition.base.level_params != family.base.level_params
    {
        return Ok(None);
    }
    let Some(ConstantInfo::Ctor(constructor)) = environment.find(&family.ctors[0]) else {
        return Ok(None);
    };
    if constructor.is_unsafe
        || &constructor.induct != struct_name
        || constructor.num_params != family.num_params
        || constructor.base.level_params != family.base.level_params
        || *idx >= u64::from(constructor.num_fields)
    {
        return Ok(None);
    }
    // Only the generated field name receives projection behavior. Reusing the
    // same lambda/proj body under an unrelated definition name is insufficient.
    let mut field = &constructor.base.type_;
    for _ in 0..u64::from(family.num_params) + *idx {
        tick()?;
        let ExprNode::ForallE { body, .. } = field.node() else {
            return Ok(None);
        };
        field = body;
    }
    tick()?;
    let ExprNode::ForallE { binder_name, .. } = field.node() else {
        return Ok(None);
    };
    if definition.base.name != struct_name.append_core(binder_name) {
        return Ok(None);
    }
    Ok(Some(ClassProjection {
        structure: struct_name.clone(),
        index: *idx,
        parameters,
    }))
}
