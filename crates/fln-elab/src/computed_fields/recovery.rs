//! Recover native representation authority from a physical module's checked
//! declarations. Persistent computed_field tags remain inert unless this exact
//! inventory can be regenerated. Imported tags alone never authorize casts or
//! cached runtime layouts, even when the family has familiar primitive names.
use super::*;
use std::collections::HashMap;

/// One bounded order-recovery pass followed by the complete validation and
/// journal append passes. Callers can reserve this aggregate allowance before
/// asking for recovery; resource failures never mean an absent native model.
pub const RECOVERY_PHASES: usize = VALIDATION_PHASES + 1;

/// Tags are a NameSet at the pin, so their serialized order cannot describe
/// cache positions. Generated constructors retain the short getter names as
/// their cache binder labels. Those labels select an order to validate; only
/// regeneration of every declaration and replacement edge authorizes it.
pub fn recover_imported(
    env: &Environment,
    family: &Name,
    fields: &[Name],
    inline_fields: &[Name],
    kernel: Budget,
    budget: RecordBudget,
) -> Result<Option<Environment>, ComputedFieldError> {
    let mut build = Build::new(env, kernel, budget);
    build.charge(
        fields
            .len()
            .saturating_add(inline_fields.len())
            .saturating_add(1),
    )?;
    if fields.len() > budget.max_binders || inline_fields.len() > budget.max_binders {
        return Err(ComputedFieldError::ResourceLimit);
    }
    let mut tagged = HashSet::new();
    if fields.is_empty()
        || fields
            .iter()
            .any(|field| field.parent() != *family || !tagged.insert(field.clone()))
    {
        return Err(ComputedFieldError::InvalidInventory);
    }
    let mut labels = HashMap::new();
    for field in fields {
        build.work.tick()?;
        if labels
            .insert(cache_binder_name(field)?, field.clone())
            .is_some()
        {
            return Err(ComputedFieldError::InvalidInventory);
        }
    }
    let mut inlines = HashSet::new();
    if inline_fields
        .iter()
        .any(|field| !tagged.contains(field) || !inlines.insert(field.clone()))
    {
        return Err(ComputedFieldError::InvalidInventory);
    }
    let Some(ConstantInfo::Induct(inductive)) = env.find(family) else {
        return Ok(None);
    };
    if !env.contains(&Name::str(family.clone(), "_impl")) {
        return Ok(None);
    }
    let mut order = None;
    for constructor in &inductive.ctors {
        build.work.tick()?;
        let Some(ConstantInfo::Ctor(original)) = env.find(constructor) else {
            return Ok(None);
        };
        if original.num_fields == 0 {
            continue;
        }
        let Some(ConstantInfo::Ctor(implementation)) =
            env.find(&Name::str(constructor.clone(), "_impl"))
        else {
            return Ok(None);
        };
        let mut current = &implementation.base.type_;
        let mut names = Vec::new();
        let mut seen = HashSet::new();
        for _ in fields {
            build.work.tick()?;
            let ExprNode::ForallE {
                binder_name, body, ..
            } = current.node()
            else {
                return Ok(None);
            };
            let Some(field) = labels.get(binder_name) else {
                return Ok(None);
            };
            if !seen.insert(field.clone()) {
                return Ok(None);
            }
            names.push(field.clone());
            current = body;
        }
        order = Some(names);
        break;
    }
    // All-nullary families have no cache slots, so tag order has no physical
    // meaning. Deterministic order is still checked against every generated
    // body before the row can authorize an executable override.
    let fields = order.unwrap_or_else(|| {
        let mut fields = fields.to_vec();
        fields.sort_unstable();
        fields
    });
    match validate_inventory(env, family, &fields, kernel, budget) {
        Ok(_) => {}
        Err(error @ (ComputedFieldError::ResourceLimit | ComputedFieldError::Reduction(_))) => {
            return Err(error);
        }
        Err(_) => return Ok(None),
    }
    let inline_fields = fields
        .iter()
        .filter(|field| inlines.contains(*field))
        .cloned()
        .collect();
    journal::append(
        env,
        ComputedFieldEntry {
            family: family.clone(),
            fields,
            inline_fields,
        },
        budget,
    )
    .map(Some)
}
