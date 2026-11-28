//! Complete declaration metadata for validated computed-field families.
//! The private checked world supplies generation evidence once; public getter
//! headers reuse that immutable evidence without pretending to contain bodies.
use super::*;
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal, NatLit};
use fln_elab::computed_fields::{self, ComputedFamily, ComputedFieldError};
use fln_elab::constraint::unify::{UnificationBudget, UnificationError, UnificationTransparency};
use fln_elab::records::RecordBudget;

pub(super) struct Family {
    model: ComputedFamily,
    data: [CompilerData; 2],
}

#[derive(Default)]
pub(super) struct Captured {
    pub(super) owned: Vec<Family>,
    /// Includes imported native families: until the executable artifact ABI
    /// supports cache-bearing data, a consuming module must refuse it too.
    pub(super) visible_family: Option<Name>,
}

fn error(module: &Name, reason: &'static str) -> SourceModuleCheckError {
    SourceModuleCheckError::Extension {
        module: module.clone(),
        extension: computed_fields::journal_name(),
        reason,
    }
}

fn failed(module: &Name, meter: &Meter, failure: ComputedFieldError) -> SourceModuleCheckError {
    match failure {
        ComputedFieldError::ResourceLimit => SourceModuleCheckError::Limit {
            resource: "module work",
            limit: meter.limits.max_work,
        },
        ComputedFieldError::Reduction(error) => reduction_failed(module, error),
        _ => error(module, "invalid computed-field generation provenance"),
    }
}

fn reduction_failed(module: &Name, error: Box<UnificationError>) -> SourceModuleCheckError {
    SourceModuleCheckError::Replay {
        module: module.clone(),
        error: Box::new(EngineExecutionError::Frontend(
            fln_elab::NatDefinitionFrontendError::Elaborate(
                fln_elab::NatDefinitionElabError::Inference(
                    fln_elab::source::SourceInferenceError::Unification(error),
                ),
            ),
        )),
    }
}

// Keep the existing phase ceilings and allocation policy. The metered helpers
// below additionally enforce the aggregate remaining allowance, then report
// the work performed instead of charging every unused phase ceiling.
fn budget(meter: &Meter, phases: usize, remaining_models: usize) -> RecordBudget {
    let remaining = meter.limits.max_work.saturating_sub(meter.work);
    let divisor = phases.saturating_mul(remaining_models).saturating_add(1);
    let allowance = (remaining / divisor).min(100_000);
    RecordBudget {
        max_binders: allowance,
        max_nodes: allowance,
    }
}

pub(super) fn models(
    module: &Name,
    base: &Environment,
    private: &Environment,
    meter: &mut Meter,
) -> Result<Captured, SourceModuleCheckError> {
    let Some(journal) = private.extension(&computed_fields::journal_name()) else {
        return Ok(Captured::default());
    };
    let inherited = base.extension(&computed_fields::journal_name());
    let mut unchanged = inherited.is_some_and(|previous| previous.len() == journal.len());
    let mut prior = inherited
        .into_iter()
        .flat_map(|previous| previous.entries());
    for entry in journal.entries() {
        meter.work(1)?;
        meter.bytes(entry.payload.len())?;
        unchanged &= prior.next() == Some(entry);
    }
    let (claims, work) = computed_fields::families_with_work(private, budget(meter, 1, 1))
        .map_err(|failure| failed(module, meter, failure))?;
    meter.work(work)?;
    let visible_family = claims.first().cloned();
    if unchanged {
        return Ok(Captured {
            owned: Vec::new(),
            visible_family,
        });
    }
    let mut owned = Vec::new();
    for family in claims {
        meter.work(1)?;
        let implementation = Name::str(family.clone(), "_impl");
        match (base.contains(&family), base.contains(&implementation)) {
            (true, true) => {}
            (false, false) => owned.push(family),
            _ => {
                return Err(error(
                    module,
                    "computed-field implementation and logical family must have the same module owner",
                ));
            }
        }
    }
    let mut models = Vec::with_capacity(owned.len());
    let mut words_checked = BTreeSet::new();
    for (index, family) in owned.iter().enumerate() {
        let budget = budget(
            meter,
            computed_fields::VALIDATION_PHASES,
            owned.len() - index,
        );
        let remaining = meter.limits.max_work.saturating_sub(meter.work);
        let (model, work) = computed_fields::validated_family_with_work(
            private,
            family,
            meter.limits.source.admission.kernel,
            budget,
            remaining,
        )
        .map_err(|failure| failed(module, meter, failure))?;
        meter.work(work)?;
        let model = model
            .ok_or_else(|| error(module, "computed-field generation provenance disappeared"))?;
        let Some(ConstantInfo::Induct(original)) = private.find(&model.family) else {
            return Err(error(
                module,
                "computed-field logical compiler interface is absent",
            ));
        };
        let Some(ConstantInfo::Induct(implementation)) = private.find(&model.implementation) else {
            return Err(error(
                module,
                "computed-field implementation compiler interface is absent",
            ));
        };
        let data = CompilerData::from_computed_family(
            original,
            implementation,
            |name| private.find(name),
            |work| meter.work(work),
        )?
        .ok_or_else(|| error(module, "computed-field artifacts require supported logical and implementation compiler layouts"))?;
        let words: Vec<_> = word_widths(module, private, &model, meter)?
            .into_iter()
            .filter(|width| !words_checked.contains(width))
            .collect();
        for (index, width) in words.iter().copied().enumerate() {
            if !CompilerData::validate_unsigned_word_model(
                width,
                |name| private.find(name),
                |work| meter.work(work),
            )? {
                return Err(error(
                    module,
                    "unsigned word compiler layout requires its checked word/bitvector/finite model",
                ));
            }
            word_bound(module, private, width, words.len() - index, meter)?;
            words_checked.insert(width);
        }
        models.push(Family { model, data });
    }
    Ok(Captured {
        owned: models,
        visible_family,
    })
}

fn word_widths(
    module: &Name,
    private: &Environment,
    model: &ComputedFamily,
    meter: &mut Meter,
) -> Result<BTreeSet<u32>, SourceModuleCheckError> {
    let mut widths = BTreeSet::new();
    for constructor in &model.constructors {
        meter.work(1)?;
        let Some(ConstantInfo::Ctor(info)) = private.find(&constructor.implementation) else {
            return Err(error(
                module,
                "computed-field implementation constructor is absent",
            ));
        };
        let mut type_ = &info.base.type_;
        while let ExprNode::ForallE {
            binder_type, body, ..
        } = without_metadata(type_, meter)?.node()
        {
            meter.work(1)?;
            if let ExprNode::Const { name, levels } = binder_type.node()
                && levels.is_empty()
            {
                for (word, width) in [
                    ("UInt8", 8_u32),
                    ("UInt16", 16),
                    ("UInt32", 32),
                    ("UInt64", 64),
                ] {
                    meter.work(1)?;
                    if name == &Name::from_components([word]) {
                        widths.insert(width);
                    }
                }
            }
            type_ = body;
        }
    }
    Ok(widths)
}

fn without_metadata<'a>(
    mut expression: &'a Expr,
    meter: &mut Meter,
) -> Result<&'a Expr, SourceModuleCheckError> {
    while let ExprNode::MData { expr, .. } = expression.node() {
        meter.work(1)?;
        expression = expr;
    }
    Ok(expression)
}

fn instantiate_word_model(
    module: &Name,
    expression: &Expr,
    arguments: &[Expr],
    meter: &mut Meter,
) -> Result<Expr, SourceModuleCheckError> {
    let invalid = || {
        error(
            module,
            "unsigned word compiler layout has an invalid finite telescope",
        )
    };
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        // Cover both this scan and the core's immutable substitution.
        meter.work(2)?;
        match expression.node() {
            ExprNode::App { f, a } => {
                pending.push(f);
                pending.push(a);
            }
            ExprNode::MData { expr, .. } => pending.push(expr),
            ExprNode::BVar { idx } if (*idx as usize) < arguments.len() => {}
            ExprNode::Const { .. } | ExprNode::Lit { .. } => {}
            _ => return Err(invalid()),
        }
    }
    expression.subst_loose(0, arguments).map_err(|_| invalid())
}

/// Constructor spelling alone cannot establish a numeric range: the actual
/// safe power dictionaries must reduce the BitVec N bound to precisely 2^N.
/// The existing checked reducer handles their real bodies under the caller's
/// calibrated kernel budget; this adds no name-based evaluation primitive.
fn word_bound(
    module: &Name,
    private: &Environment,
    width: u32,
    remaining_words: usize,
    meter: &mut Meter,
) -> Result<(), SourceModuleCheckError> {
    let invalid = || {
        error(
            module,
            "unsigned word compiler layout requires its checked finite bound",
        )
    };
    let Some(ConstantInfo::Ctor(bits)) = private.find(&Name::from_components(["BitVec", "ofFin"]))
    else {
        return Err(invalid());
    };
    let ExprNode::ForallE { body, .. } = without_metadata(&bits.base.type_, meter)?.node() else {
        return Err(invalid());
    };
    let ExprNode::ForallE { binder_type, .. } = without_metadata(body, meter)?.node() else {
        return Err(invalid());
    };
    let ExprNode::App { f, a: bound } = without_metadata(binder_type, meter)?.node() else {
        return Err(invalid());
    };
    if !matches!(without_metadata(f, meter)?.node(), ExprNode::Const { name, levels }
        if name == &Name::from_components(["Fin"]) && levels.is_empty())
    {
        return Err(invalid());
    }
    let bound = instantiate_word_model(
        module,
        bound,
        &[Expr::lit(Literal::Nat(NatLit::from_u64(u64::from(width))))],
        meter,
    )?;
    let expected_bound = match width {
        8 | 16 | 32 => NatLit::from_u64(1_u64 << width),
        64 => NatLit::from_limbs_le(vec![0, 1]),
        _ => return Err(invalid()),
    };
    let allowance = budget(meter, 2, remaining_words.saturating_add(1)).max_nodes;
    let mut transaction = fln_elab::ElabTxn::new(private.clone(), KVMap::new(), 0);
    let reduce = |transaction: &mut fln_elab::ElabTxn, expression: &Expr, meter: &mut Meter| {
        let allowance = allowance.min(meter.limits.max_work.saturating_sub(meter.work));
        let mut reduction = UnificationBudget::new(meter.limits.source.admission.kernel);
        reduction.transparency = UnificationTransparency::SafeDefinitions;
        reduction.max_steps = reduction.max_steps.min(allowance as u64);
        reduction.max_visited_nodes = reduction.max_visited_nodes.min(allowance);
        let before = transaction.budget.heartbeats_consumed;
        transaction.budget.max_heartbeats = transaction
            .budget
            .heartbeats_consumed
            .saturating_add(allowance as u64);
        let locals = transaction.lctx.clone();
        let result = transaction.whnf_with(expression, &locals, reduction);
        let used = transaction
            .budget
            .heartbeats_consumed
            .saturating_sub(before);
        // The reducer charges every visited node through its step counter.
        // Retain the old step/node ceilings, and charge the actual work before
        // inspecting success or continuing with the second checked reduction.
        meter.work(
            usize::try_from(used).map_err(|_| SourceModuleCheckError::Limit {
                resource: "module work",
                limit: meter.limits.max_work,
            })?,
        )?;
        result.map_err(|failure| match failure {
            UnificationError::StepLimit { .. }
            | UnificationError::NodeLimit { .. }
            | UnificationError::AssignmentLimit { .. }
            | UnificationError::HeartbeatLimit => SourceModuleCheckError::Limit {
                resource: "module work",
                limit: meter.limits.max_work,
            },
            other => reduction_failed(module, Box::new(other)),
        })
    };
    let reduced = reduce(&mut transaction, &bound, meter)?;
    if !matches!(without_metadata(&reduced, meter)?.node(), ExprNode::Lit { literal: Literal::Nat(value) }
        if value == &expected_bound)
    {
        return Err(invalid());
    }

    // Fin's proof must constrain the numeric payload, not just inhabit an
    // arbitrary proposition selected by a same-named comparison dictionary.
    let Some(ConstantInfo::Ctor(finite)) = private.find(&Name::from_components(["Fin", "mk"]))
    else {
        return Err(invalid());
    };
    let mut telescope = &finite.base.type_;
    for _ in 0..2 {
        let ExprNode::ForallE { body, .. } = without_metadata(telescope, meter)?.node() else {
            return Err(invalid());
        };
        telescope = body;
    }
    let ExprNode::ForallE {
        binder_type: proof, ..
    } = without_metadata(telescope, meter)?.node()
    else {
        return Err(invalid());
    };
    let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
    let scope = Name::from_components(["_fln_computed_word_range"]);
    let bound_id = FVarId(Name::num(scope.clone(), 0));
    let value_id = FVarId(Name::num(scope, 1));
    transaction.lctx.add_param(
        bound_id.clone(),
        Name::from_components(["bound"]),
        nat.clone(),
        BinderInfo::Default,
    );
    transaction.lctx.add_param(
        value_id.clone(),
        Name::from_components(["value"]),
        nat,
        BinderInfo::Default,
    );
    let bound = Expr::fvar(bound_id);
    let value = Expr::fvar(value_id);
    let proof = instantiate_word_model(module, proof, &[bound.clone(), value.clone()], meter)?;
    let reduced = reduce(&mut transaction, &proof, meter)?;
    let expected = Expr::app(
        Expr::app(
            Expr::const_(Name::from_components(["Nat", "le"]), Vec::new()),
            Expr::app(
                Expr::const_(Name::from_components(["Nat", "succ"]), Vec::new()),
                value,
            ),
        ),
        bound,
    );
    if without_metadata(&reduced, meter)? != &expected {
        return Err(error(
            module,
            "unsigned word compiler layout requires the canonical finite comparison",
        ));
    }
    Ok(())
}

pub(super) fn inert_tags(
    module: &Name,
    env: &Environment,
    meter: &mut Meter,
) -> Result<BTreeSet<Name>, SourceModuleCheckError> {
    meter.work(1)?;
    let mut allowance = 1_usize;
    if let Some(journal) = env.extension(&computed_fields::tags::journal_name()) {
        for entry in journal.entries() {
            // Reserve the codec's exact byte/entry allowance before reading,
            // including inherited owner snapshots.
            let work = entry.payload.len().saturating_add(1);
            meter.work(work)?;
            meter.bytes(entry.payload.len())?;
            allowance = allowance.saturating_add(work);
        }
    }
    computed_fields::tags::read(
        env,
        RecordBudget {
            max_binders: allowance,
            max_nodes: allowance,
        },
    )
    .map(|names| names.into_iter().collect())
    .map_err(|failure| match failure {
        failure @ (ComputedFieldError::ResourceLimit | ComputedFieldError::Reduction(_)) => {
            failed(module, meter, failure)
        }
        _ => SourceModuleCheckError::Extension {
            module: module.clone(),
            extension: computed_fields::tags::journal_name(),
            reason: "invalid computed-field journal",
        },
    })
}

fn owned(
    module: &Name,
    base: &Environment,
    checked: &Environment,
    declaration: &Name,
    meter: &mut Meter,
) -> Result<(), SourceModuleCheckError> {
    meter.work(1)?;
    if base.contains(declaration) || !checked.contains(declaration) {
        return Err(error(
            module,
            "computed-field artifact metadata must belong to declarations defined in this module",
        ));
    }
    Ok(())
}

pub(super) fn entries(
    families: &[Family],
    meter: &mut Meter,
) -> Result<Vec<computed_fields::ComputedFieldEntry>, SourceModuleCheckError> {
    let mut entries = Vec::with_capacity(families.len());
    for family in families {
        meter.work(
            family
                .model
                .fields
                .len()
                .saturating_add(family.model.inline_fields.len())
                .saturating_add(1),
        )?;
        entries.push(computed_fields::ComputedFieldEntry {
            family: family.model.family.clone(),
            fields: family
                .model
                .fields
                .iter()
                .map(|field| field.name.clone())
                .collect(),
            inline_fields: family.model.inline_fields.clone(),
        });
    }
    Ok(entries)
}

/// Add the two precomputed compiler-data interfaces.
/// Return the families already projected so the ordinary writer cannot emit
/// duplicate maps or substitute the original telescope for the cached one.
pub(super) fn append(
    module: &Name,
    base: &Environment,
    checked: &Environment,
    models: &[Family],
    metadata: &mut SourceMetadata,
    meter: &mut Meter,
) -> Result<BTreeSet<Name>, SourceModuleCheckError> {
    let mut projected = BTreeSet::new();
    for family in models {
        let model = &family.model;
        for declaration in [&model.family, &model.implementation] {
            owned(module, base, checked, declaration, meter)?;
            if !projected.insert(declaration.clone()) {
                return Err(error(module, "duplicate computed-field compiler interface"));
            }
        }
        for field in &model.fields {
            owned(module, base, checked, &field.name, meter)?;
        }
        // Public projection already checked that every generated family and
        // constructor equals the private inventory. Reuse those immutable rows;
        // public primitive/getter headers need not contain implementation bodies.
        metadata.compiler_data.extend(family.data.iter().cloned());
    }
    Ok(projected)
}
