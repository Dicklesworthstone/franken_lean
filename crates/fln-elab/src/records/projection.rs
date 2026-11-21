//! Identify admitted class field projections without trusting their spelling.
//!
//! The caller separately checks class registration and reducibility. This
//! descriptor requires the generated constructor field, instance receiver,
//! and exact projection body; an ordinary function that returns a field does
//! not acquire the Reference's `unfoldProjInst?` behavior.

use crate::records::imported::ImportedStructures;
use fln_core::expr::{BinderInfo, ExprNode};
use fln_core::name::Name;
use fln_env::constants::{ConstantInfo, DefinitionSafety, DefinitionVal};
use fln_env::environment::Environment;

pub(crate) struct ClassProjection {
    pub structure: Name,
    pub index: u64,
    pub parameters: usize,
}

/// Non-subobject (copied) parent projection between classes (`mkCoercionToCopiedParent` +
/// `addAuxParentProjectionInfo`, vendored `Lean/Elab/Structure.lean:1439`).
pub(crate) struct AuxParentProjection {
    pub structure: Name,
    pub parent: Name,
    pub parameters: usize,
}

/// Identify an admitted auxiliary parent projection for diamond inheritance so
/// `reduction_blocker` (`getStuckMVar?`, vendored `Lean/Meta/WHNF.lean:367-372`)
/// can look through copied parent coercions to find a stuck class metavariable.
pub(crate) fn aux_parent_projection<E>(
    environment: &Environment,
    definition: &DefinitionVal,
    mut tick: impl FnMut() -> Result<(), E>,
) -> Result<Option<AuxParentProjection>, E> {
    if definition.safety != DefinitionSafety::Safe {
        return Ok(None);
    }
    let struct_name = definition.base.name.parent();
    let Some(ConstantInfo::Induct(family)) = environment.find(&struct_name) else {
        return Ok(None);
    };
    let Ok(parameters) = usize::try_from(family.num_params) else {
        return Ok(None);
    };
    if family.is_unsafe
        || family.num_indices != 0
        || family.ctors.len() != 1
        || definition.base.level_params != family.base.level_params
    {
        return Ok(None);
    }
    // Cheap shape guard before consulting the structure journal: the type must
    // bind `num_params` parameters followed by an instance-implicit receiver.
    let mut cursor = &definition.base.type_;
    for _ in 0..parameters {
        tick()?;
        let ExprNode::ForallE { body, .. } = cursor.node() else {
            return Ok(None);
        };
        cursor = body;
    }
    tick()?;
    let ExprNode::ForallE { binder_info, .. } = cursor.node() else {
        return Ok(None);
    };
    if *binder_info != BinderInfo::InstImplicit {
        return Ok(None);
    }
    let Ok(structures) = ImportedStructures::read(environment) else {
        return Ok(None);
    };
    let Some(entry) = structures.get(&struct_name) else {
        return Ok(None);
    };
    let Some(parent) = entry
        .parents
        .iter()
        .find(|parent| !parent.subobject && parent.projection == definition.base.name)
    else {
        return Ok(None);
    };
    Ok(Some(AuxParentProjection {
        structure: struct_name,
        parent: parent.name.clone(),
        parameters,
    }))
}

pub(crate) fn class_projection<E>(
    environment: &Environment,
    definition: &DefinitionVal,
    tick: impl FnMut() -> Result<(), E>,
) -> Result<Option<ClassProjection>, E> {
    field_projection(environment, definition, true, tick)
}

/// The generated projection law also applies to non-class record fields during
/// definitional simplification. Ordinary lookalike functions are still refused.
pub(crate) fn generated_projection<E>(
    environment: &Environment,
    definition: &DefinitionVal,
    tick: impl FnMut() -> Result<(), E>,
) -> Result<Option<ClassProjection>, E> {
    field_projection(environment, definition, false, tick)
}

fn field_projection<E>(
    environment: &Environment,
    definition: &DefinitionVal,
    require_instance: bool,
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
    if (require_instance && receiver != BinderInfo::InstImplicit)
        || !matches!(expr.node(), ExprNode::BVar { idx: 0 })
    {
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
