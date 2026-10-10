//! Native deriving handlers produce ordinary, untrusted declarations. The source
//! command caller admits the entire family and handler batch before publication.
//! Inhabited follows the pin's two passes over constructors: first without new
//! hypotheses, then assuming inhabited parameters and retaining only used ones.
use super::*;
use fln_env::constants::{ConstantInfo, InductiveVal};
mod beq;
mod repr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DerivingError {
    UnsupportedHandler(Name),
    UnsupportedFamily(Name),
    CannotDerive(Name),
    CannotDeriveBEq(Name),
    CannotDeriveRepr(Name),
}

impl std::fmt::Display for DerivingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsupportedHandler(name) => write!(
                f,
                "unsupported deriving handler `{}`",
                name.to_display_string()
            ),
            Self::UnsupportedFamily(name) => {
                write!(
                    f,
                    "unsupported deriving telescope for `{}`",
                    name.to_display_string()
                )
            }
            Self::CannotDerive(name) => {
                write!(
                    f,
                    "failed to generate `Inhabited` instance for `{}`",
                    name.to_display_string()
                )
            }
            Self::CannotDeriveRepr(name) => write!(
                f,
                "failed to generate Repr instance for {}",
                name.to_display_string()
            ),
            Self::CannotDeriveBEq(name) => write!(
                f,
                "failed to generate BEq instance for {}",
                name.to_display_string()
            ),
        }
    }
}

impl std::error::Error for DerivingError {}

/// The family syntax with its suffix consumed by a caller that owns derivation.
/// The low-level single-declaration elaborators still refuse an unconsumed suffix.
#[derive(Debug)]
pub struct DerivingRequest {
    pub syntax: Syntax,
    pub type_name: Name,
    pub handlers: Vec<Name>,
    pub is_record: bool,
}

pub fn prepare(syntax: &Syntax) -> Result<Option<DerivingRequest>, NatDefinitionElabError> {
    let is_record = super::is_record(syntax);
    if !is_record && !super::is_inductive(syntax) {
        return Ok(None);
    }
    let root = expect_node(
        syntax,
        &parser_kind(&["Command", "declaration"]),
        2,
        "derived declaration",
    )?;
    let parts = expect_node(
        &root[1],
        &parser_kind(&["Command", if is_record { "structure" } else { "inductive" }]),
        if is_record { 6 } else { 7 },
        "derived family",
    )?;
    let id = expect_node(
        &parts[1],
        &parser_kind(&["Command", "declId"]),
        2,
        "family name",
    )?;
    let Syntax::Ident { val: type_name, .. } = &id[0] else {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    };
    let suffix_index = parts.len() - 1;
    let suffix = expect_node(
        &parts[suffix_index],
        &parser_kind(&["Command", "optDeriving"]),
        1,
        "deriving suffix",
    )?;
    let mut handlers = Vec::new();
    match expect_null_args(&suffix[0], "deriving clause")? {
        [] => {}
        [keyword, classes] => {
            expect_atom(keyword, "deriving", "deriving keyword")?;
            let classes = expect_null_args(classes, "deriving handlers")?;
            if classes.is_empty() || classes.len() % 2 == 0 {
                return Err(failure(SourceInferenceError::Scope));
            }
            for (index, class) in classes.iter().enumerate() {
                if index % 2 == 1 {
                    expect_atom(class, ",", "deriving separator")?;
                    continue;
                }
                let class = expect_node(
                    class,
                    &parser_kind(&["Command", "derivingClass"]),
                    2,
                    "deriving handler",
                )?;
                expect_empty_null(&class[0], "unsupported deriving attributes")?;
                let Syntax::Ident { val, .. } = &class[1] else {
                    return Err(failure(SourceInferenceError::Scope));
                };
                handlers.push(val.clone());
            }
        }
        _ => return Err(failure(SourceInferenceError::Scope)),
    }
    let mut stripped = syntax.clone();
    let Syntax::Node { args: root, .. } = &mut stripped else {
        unreachable!("validated declaration node")
    };
    let Syntax::Node { args: parts, .. } = &mut root[1] else {
        unreachable!("validated family node")
    };
    parts[suffix_index] = Syntax::node(
        parser_kind(&["Command", "optDeriving"]),
        vec![Syntax::node(Name::from_components(["null"]), Vec::new())],
    );
    Ok(Some(DerivingRequest {
        syntax: stripped,
        type_name: type_name.clone(),
        handlers,
        is_record,
    }))
}

#[derive(Debug)]
pub struct DerivedInstance {
    /// The generated helper precedes its dictionary. Both still require checking.
    pub declarations: Vec<Declaration>,
    pub instance: Name,
}

fn named(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn unsupported(name: &Name) -> NatDefinitionElabError {
    failure(SourceInferenceError::Deriving(
        DerivingError::UnsupportedFamily(name.clone()),
    ))
}

fn normal_failure(error: &NatDefinitionElabError) -> bool {
    matches!(
        error,
        NatDefinitionElabError::Inference(SourceInferenceError::InstanceSynthesisRequired)
    ) || instances::nonmatch(error)
}

fn apply(
    context: &mut Context,
    mut f: Typed,
    arguments: &[Expr],
) -> Result<Typed, NatDefinitionElabError> {
    for argument in arguments {
        context.tick()?;
        let type_ = context.whnf(&f.type_)?;
        let ExprNode::ForallE { body, .. } = type_.node() else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        f.type_ = context.substitute(body, argument)?;
        f.value = Expr::app(f.value, argument.clone());
    }
    Ok(f)
}

fn inhabited_type(
    context: &mut Context,
    type_: &Expr,
) -> Result<(Expr, Level), NatDefinitionElabError> {
    let sort = context
        .known_type(type_)?
        .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
    let sort = context.whnf(&sort)?;
    let ExprNode::Sort { level } = sort.node() else {
        return Err(failure(SourceInferenceError::ExpectedType));
    };
    // AppBuilder's universe inference simplifies the level assigned to the
    // class parameter; keep the resulting instance statement canonical too.
    let level = level.normalize();
    Ok((
        Expr::app(
            Expr::const_(named("Inhabited"), vec![level.clone()]),
            type_.clone(),
        ),
        level,
    ))
}

fn default_value(context: &mut Context, type_: &Expr) -> Result<Expr, NatDefinitionElabError> {
    let (goal, level) = inhabited_type(context, type_)?;
    let dictionary = context.instance_hole(goal)?;
    context.resolve_instances(true)?;
    let dictionary = context.instantiate(&dictionary)?;
    Ok(Expr::app(
        Expr::app(
            Expr::const_(named("Inhabited.default"), vec![level]),
            type_.clone(),
        ),
        dictionary,
    ))
}

fn close(
    context: &mut Context,
    mut term: Typed,
    parameters: &[LocalDecl],
) -> Result<Typed, NatDefinitionElabError> {
    for local in parameters.iter().rev() {
        context.tick()?;
        let domain = context.instantiate(&local.type_)?;
        term.type_ = Expr::forall_e(
            local.user_name.clone(),
            domain.clone(),
            term.type_
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            local.binder_info,
        );
        term.value = Expr::lam(
            local.user_name.clone(),
            domain,
            term.value
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            local.binder_info,
        );
    }
    let term = context.finish(term)?;
    if term.type_.has_fvar()
        || term.value.has_fvar()
        || term.type_.has_loose_bvars()
        || term.value.has_loose_bvars()
    {
        return Err(failure(SourceInferenceError::Scope));
    }
    Ok(term)
}

fn candidate(
    context: &mut Context,
    family: &InductiveVal,
    constructor: &Name,
    parameters: &[LocalDecl],
    target: &Expr,
    is_record: bool,
    add_hypotheses: bool,
) -> Result<DerivedInstance, NatDefinitionElabError> {
    let mut trial = context.clone();
    let result = candidate_in_context(
        &mut trial,
        family,
        constructor,
        parameters,
        target,
        is_record,
        add_hypotheses,
    );
    // Backtracking restores goals and local hypotheses, never spent work.
    context.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
    result
}

fn candidate_in_context(
    context: &mut Context,
    family: &InductiveVal,
    constructor: &Name,
    parameters: &[LocalDecl],
    target: &Expr,
    is_record: bool,
    add_hypotheses: bool,
) -> Result<DerivedInstance, NatDefinitionElabError> {
    let levels: Vec<_> = family
        .base
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    let (instance_type, result_level) = inhabited_type(context, target)?;
    // The pin chooses the base name before discovering parameter hypotheses.
    let instance = context.generated_instance_name(parameters, &instance_type)?;
    let helper = Name::str(instance.clone(), "default");
    let mut hypotheses = Vec::new();
    if add_hypotheses {
        for (index, parameter) in parameters.iter().enumerate() {
            let domain = context.whnf(&parameter.type_)?;
            let ExprNode::Sort { level } = domain.node() else {
                continue;
            };
            let type_ = Expr::app(
                Expr::const_(named("Inhabited"), vec![level.clone()]),
                Expr::fvar(parameter.id.clone()),
            );
            let id = FVarId(context.fresh_name()?);
            context.txn.lctx.add_param(
                id.clone(),
                named(&format!("inst{index}")),
                type_,
                BinderInfo::InstImplicit,
            );
            hypotheses.push((
                index,
                context
                    .txn
                    .lctx
                    .find(&id)
                    .expect("inserted hypothesis")
                    .clone(),
            ));
        }
    }
    let Some(ConstantInfo::Ctor(ctor)) = context.txn.env.find(constructor).cloned() else {
        return Err(unsupported(&family.base.name));
    };
    if ctor.num_fields as usize > crate::records::RecordBudget::default().max_binders {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    let parameter_values: Vec<_> = parameters
        .iter()
        .map(|p| Expr::fvar(p.id.clone()))
        .collect();
    let ctor_type =
        context.instantiate_params(&ctor.base.type_, &ctor.base.level_params, &levels)?;
    let mut value = apply(
        context,
        Typed {
            value: Expr::const_(constructor.clone(), levels.clone()),
            type_: ctor_type,
        },
        &parameter_values,
    )?;
    let mut fields = Vec::new();
    for _ in 0..ctor.num_fields {
        let type_ = context.whnf(&value.type_)?;
        let ExprNode::ForallE {
            binder_type, body, ..
        } = type_.node()
        else {
            return Err(unsupported(&family.base.name));
        };
        let hole = context.hole(binder_type.clone())?;
        fields.push((hole.clone(), binder_type.clone()));
        value.value = Expr::app(value.value, hole.clone());
        value.type_ = context.substitute(body, &hole)?;
    }
    context.equations.push(SourceEquation::selection(
        value.type_.clone(),
        target.clone(),
    ));
    context.flush(true)?;
    let defaults = if is_record {
        Some(
            crate::records::defaults::RecordDefaults::read(&context.txn.env)
                .map_err(|error| failure(SourceInferenceError::Record(error)))?,
        )
    } else {
        None
    };
    let mut values = Vec::new();
    // StructInst.synthDefaultFields selects every default before it assigns any
    // pending field. In particular an earlier default must not manufacture an
    // Inhabited instance for a still-unknown dependent field type.
    for (index, (_, type_)) in fields.iter().enumerate() {
        let default = if let Some(helper) = defaults
            .as_ref()
            .and_then(|d| d.helper(&family.base.name, index as u32))
        {
            let Some(ConstantInfo::Defn(definition)) = context.txn.env.find(helper).cloned() else {
                return Err(unsupported(&family.base.name));
            };
            let helper_type = context.instantiate_params(
                &definition.base.type_,
                &definition.base.level_params,
                &levels,
            )?;
            let mut arguments = parameter_values.clone();
            arguments.extend(fields[..index].iter().map(|(hole, _)| hole.clone()));
            apply(
                context,
                Typed {
                    value: Expr::const_(helper.clone(), levels.clone()),
                    type_: helper_type,
                },
                &arguments,
            )?
            .value
        } else {
            default_value(context, type_)?
        };
        values.push(default);
    }
    for ((hole, _), default) in fields.iter().zip(values) {
        context
            .equations
            .push(SourceEquation::inference(hole.clone(), default));
    }
    let value = context.finish(value)?;
    let mut used = Vec::new();
    for (index, local) in hypotheses {
        context.tick()?;
        let abstracted = value
            .value
            .abstract_fvar(&local.id, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        if abstracted != value.value {
            used.push((index, local));
        }
    }
    let mut helper_parameters = parameters.to_vec();
    helper_parameters.extend(used.iter().map(|(_, local)| local.clone()));
    let helper_term = close(context, value, &helper_parameters)?;
    let helper_call = helper_parameters
        .iter()
        .fold(Expr::const_(helper.clone(), levels), |f, p| {
            Expr::app(f, Expr::fvar(p.id.clone()))
        });
    let instance_value = Expr::app(
        Expr::app(
            Expr::const_(named("Inhabited.mk"), vec![result_level]),
            target.clone(),
        ),
        helper_call,
    );
    let mut instance_parameters = Vec::new();
    for (index, parameter) in parameters.iter().enumerate() {
        instance_parameters.push(parameter.clone());
        if let Some((_, hypothesis)) = used.iter().find(|(at, _)| *at == index) {
            instance_parameters.push(hypothesis.clone());
        }
    }
    let instance_term = close(
        context,
        Typed {
            value: instance_value,
            type_: instance_type,
        },
        &instance_parameters,
    )?;
    let definition = |name: Name, term: Typed| {
        Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: family.base.level_params.clone(),
                type_: term.type_,
            },
            value: term.value,
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![name],
        })
    };
    Ok(DerivedInstance {
        declarations: vec![
            definition(helper, helper_term),
            definition(instance.clone(), instance_term),
        ],
        instance,
    })
}

pub fn elaborate_handler(
    handler: &Name,
    type_name: &Name,
    is_record: bool,
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<DerivedInstance, NatDefinitionElabError> {
    let mut context = Context::scoped(environment, kernel, scope);
    let handler_name = context.resolve_source_name(handler)?;
    let is_repr = handler_name.as_ref() == Some(&named("Repr"));
    let is_beq = handler_name.as_ref() == Some(&named("BEq"));
    if !is_repr && !is_beq && handler_name.as_ref() != Some(&named("Inhabited")) {
        return Err(failure(SourceInferenceError::Deriving(
            DerivingError::UnsupportedHandler(handler.clone()),
        )));
    }
    // The generated telescope contains the family's own parameters, including
    // captured section parameters. Ambient section locals must not escape it.
    context.txn.lctx = LocalContext::new();
    let Some(ConstantInfo::Induct(family)) = environment.find(type_name) else {
        return Err(unsupported(type_name));
    };
    if family.num_indices != 0 || family.is_unsafe {
        return Err(unsupported(type_name));
    }
    let budget = crate::records::RecordBudget::default();
    if family.num_params as usize > budget.max_binders || family.ctors.len() > budget.max_binders {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    context.level_params = family.base.level_params.clone();
    let levels: Vec<_> = family
        .base
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    let mut cursor = family.base.type_.clone();
    let mut target = Expr::const_(type_name.clone(), levels);
    let mut parameters = Vec::new();
    for _ in 0..family.num_params {
        let type_ = context.whnf(&cursor)?;
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            ..
        } = type_.node()
        else {
            return Err(unsupported(type_name));
        };
        let id = FVarId(context.fresh_name()?);
        context.txn.lctx.add_param(
            id.clone(),
            binder_name.clone(),
            binder_type.clone(),
            BinderInfo::Implicit,
        );
        let argument = Expr::fvar(id.clone());
        cursor = context.substitute(body, &argument)?;
        target = Expr::app(target, argument);
        parameters.push(
            context
                .txn
                .lctx
                .find(&id)
                .expect("inserted parameter")
                .clone(),
        );
    }
    if is_beq {
        return match beq::elaborate(&mut context, family, &parameters, &target) {
            Err(error) if normal_failure(&error) => Err(failure(SourceInferenceError::Deriving(
                DerivingError::CannotDeriveBEq(type_name.clone()),
            ))),
            result => result,
        };
    }
    if is_repr {
        return match repr::elaborate(&mut context, family, &parameters, &target, is_record) {
            Err(error) if normal_failure(&error) => Err(failure(SourceInferenceError::Deriving(
                DerivingError::CannotDeriveRepr(type_name.clone()),
            ))),
            result => result,
        };
    }
    for add_hypotheses in [false, true] {
        for constructor in &family.ctors {
            context.tick()?;
            match candidate(
                &mut context,
                family,
                constructor,
                &parameters,
                &target,
                is_record,
                add_hypotheses,
            ) {
                Ok(derived) => return Ok(derived),
                Err(error) if normal_failure(&error) => {}
                Err(error) => return Err(error),
            }
        }
    }
    Err(failure(SourceInferenceError::Deriving(
        DerivingError::CannotDerive(type_name.clone()),
    )))
}
