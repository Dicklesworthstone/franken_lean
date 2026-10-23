//! Source record signatures elaborate through the same bidirectional context as
//! ordinary definitions. Result universes follow field domains unless explicit.
use super::*;
mod flat;
mod parents;
use crate::records::defaults::{RecordDefault, helper_name};
use crate::records::imported::{StructureEntry, StructureField, StructureParent};
use crate::records::inheritance::RecordParent;
use crate::records::{RecordBudget, RecordSpec, record_declarations};

#[derive(Debug)]
pub struct SourceRecord {
    pub name: Name,
    pub is_class: bool,
    /// The inductive block followed by each projection, all still untrusted.
    pub declarations: Vec<Declaration>,
    /// References only: the caller registers these after admitting the full batch.
    pub defaults: Vec<RecordDefault>,
    /// Parent metadata and instance registrations are published only after checking.
    pub parents: Vec<RecordParent>,
    pub parent_instances: Vec<Name>,
    /// The generated, checked flat constructor used by pinned record notation.
    pub flat_constructor: Name,
    /// Authored structure identity, never inferred from a one-constructor inductive.
    /// The caller registers it only after admitting the complete declaration batch.
    pub structure: StructureEntry,
}

pub fn is_record(syntax: &Syntax) -> bool {
    matches!(syntax, Syntax::Node { kind, args, .. }
        if kind == &parser_kind(&["Command", "declaration"])
        && matches!(args.as_slice(), [_, Syntax::Node { kind, .. }]
            if kind == &parser_kind(&["Command", "structure"])))
}

fn empty_modifiers(syntax: &Syntax) -> Result<(), NatDefinitionElabError> {
    let parts = expect_node(
        syntax,
        &parser_kind(&["Command", "declModifiers"]),
        7,
        "record modifiers",
    )?;
    super::doc_comment_slot(&parts[0])?;
    for part in &parts[1..] {
        expect_empty_null(part, "absent record modifiers")?;
    }
    Ok(())
}

/// `(x y : T := d)` (`structExplicitBinder`) declares each name as the field `x : T := d`, as the
/// pin's `expandFields` reads it: one `structSimpleBinder` per name, sharing the modifiers, the
/// signature and the default. The implicit and instance binder forms stay refused.
fn simple_fields(fields: &[Syntax]) -> Result<Vec<Syntax>, NatDefinitionElabError> {
    let mut output = Vec::with_capacity(fields.len());
    for field in fields {
        if field.kind() != Some(&parser_kind(&["Command", "structExplicitBinder"])) {
            output.push(field.clone());
            continue;
        }
        let parts = expect_node(
            field,
            &parser_kind(&["Command", "structExplicitBinder"]),
            6,
            "explicit structure field",
        )?;
        expect_atom(&parts[1], "(", "explicit structure field bracket")?;
        expect_atom(&parts[5], ")", "explicit structure field bracket")?;
        for name in expect_null_args(&parts[2], "explicit structure field names")? {
            output.push(Syntax::node(
                parser_kind(&["Command", "structSimpleBinder"]),
                vec![
                    parts[0].clone(),
                    name.clone(),
                    parts[3].clone(),
                    parts[4].clone(),
                ],
            ));
        }
    }
    Ok(output)
}

/// Elaborate a nonrecursive structure/class with named fields. Prop-valued
/// records require proof fields, as in the pin's projection generator.
/// Registration is intentionally absent here: only checked successors can own it.
pub fn elaborate_record(
    syntax: &Syntax,
    environment: &Environment,
    kernel: Budget,
    budget: RecordBudget,
) -> Result<SourceRecord, NatDefinitionElabError> {
    elaborate_record_scoped(syntax, environment, kernel, budget, &SourceScope::default())
}

pub(super) fn elaborate_record_scoped(
    syntax: &Syntax,
    environment: &Environment,
    kernel: Budget,
    budget: RecordBudget,
    scope: &SourceScope,
) -> Result<SourceRecord, NatDefinitionElabError> {
    let root = expect_node(
        syntax,
        &parser_kind(&["Command", "declaration"]),
        2,
        "record declaration",
    )?;
    scope::visibility::data_modifiers(&root[0])?;
    let scope = scope.for_declaration(syntax)?;
    let parts = expect_node(
        &root[1],
        &parser_kind(&["Command", "structure"]),
        6,
        "structure command",
    )?;
    let is_class = matches!(&parts[0], Syntax::Node { kind, .. } if kind == &parser_kind(&["Command", "classTk"]));
    let keyword = expect_node(
        &parts[0],
        &parser_kind(&["Command", if is_class { "classTk" } else { "structureTk" }]),
        1,
        "record keyword",
    )?;
    expect_atom(
        &keyword[0],
        if is_class { "class" } else { "structure" },
        "record keyword",
    )?;
    let id = expect_node(
        &parts[1],
        &parser_kind(&["Command", "declId"]),
        2,
        "record name",
    )?;
    // The source declaration retains its explicit universe scope.
    let Syntax::Ident { val: name, .. } = &id[0] else {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    };
    if name.is_anonymous() {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    }
    let deriving = expect_node(
        &parts[5],
        &parser_kind(&["Command", "optDeriving"]),
        1,
        "deriving suffix",
    )?;
    expect_empty_null(&deriving[0], "unsupported deriving")?;
    let signature = expect_node(
        &parts[2],
        &parser_kind(&["Command", "optDeclSig"]),
        2,
        "record signature",
    )?;
    let own = super::own_short_name(name);
    let mut context = Context::scoped(environment, kernel, &scope);
    let name = &context.enter_declaration(name)?;
    context.declare_levels(&id[1])?;
    context.infer_level_params = true;
    // Auto-bound implicits become leading parameters, as at the pin (`@Box : {α : Sort u_1} → α →
    // Type` for `structure Box (x : α)`, 2026-10-11). A field never auto-binds: the pin refuses one.
    let (autos, (mut parameters, explicit)) =
        context.with_auto_bound_implicits(&own, |context| {
            let parameters = context.bind_parameters(&signature[0])?;
            let explicit = optional_type_syntax(&signature[1])?
                .map(|syntax| {
                    let term = context.term(syntax, None)?;
                    // Inspecting only the reduced Sort would discard invalid ascriptions
                    // or unused let initializers. Check the original type before any
                    // record-field locals enter the telescope. This publishes nothing.
                    inductive::checked_type(context, term.value, budget)
                })
                .transpose()?;
            Ok((parameters, explicit))
        })?;
    context.refuse_auto_bound_dependencies(&autos, &parameters)?;
    parameters.splice(0..0, autos);
    let inheritance = context.record_parents(&parts[3], name, is_class, budget)?;
    let mut labels = inheritance.labels;
    let mut inferred = inheritance.level;
    let fields = match expect_null_args(&parts[4], "record body")? {
        [] => &[][..],
        [keyword, ctor, fields] => {
            // `where`, or the pin's older `:=` (`" := " <|> " where "`), for which the pin's
            // `expandFields` only logs a deprecation lint, a warning.
            if expect_atom(keyword, ":=", "record body keyword").is_err() {
                expect_atom(keyword, "where", "record body keyword")?;
            }
            expect_empty_null(ctor, "unsupported custom constructor")?;
            let fields = expect_node(
                fields,
                &parser_kind(&["Command", "structFields"]),
                1,
                "record fields",
            )?;
            expect_null_args(&fields[0], "record field array")?
        }
        _ => return Err(failure(SourceInferenceError::Scope)),
    };
    let fields = &simple_fields(fields)?;
    if parameters.len().saturating_add(fields.len()) > budget.max_binders {
        return Err(failure(SourceInferenceError::Record(
            crate::records::RecordError::ResourceLimit,
        )));
    }
    let mut output = inheritance.fields;
    let parent_count = output.len();
    let mut defaults = Vec::new();
    let mut helpers = Vec::new();
    for field in fields {
        context.tick()?;
        let parts = expect_node(
            field,
            &parser_kind(&["Command", "structSimpleBinder"]),
            4,
            "named structure field",
        )?;
        empty_modifiers(&parts[0])?;
        // `h : P := by tac` is the pin's `binderTactic`, an `autoParam` field: an omitted field
        // is filled by running its tactic. It is read as a default proved by that tactic, as the
        // checker read the field before its tree was the pin's: the constructor then takes `P`,
        // where the pin's takes `autoParam P _` (`autoParam` is a reducible `P`).
        let tactic_default;
        let default = match expect_null_args(&parts[3], "field default")? {
            [] => None,
            [syntax] if syntax.kind() == Some(&parser_kind(&["Term", "binderTactic"])) => {
                let tactic = expect_node(
                    syntax,
                    &parser_kind(&["Term", "binderTactic"]),
                    3,
                    "field tactic",
                )?;
                expect_atom(&tactic[0], ":=", "field tactic assignment")?;
                tactic_default = Syntax::node(
                    parser_kind(&["Term", "byTactic"]),
                    vec![tactic[1].clone(), tactic[2].clone()],
                );
                Some(&tactic_default)
            }
            [syntax] => {
                let parts = expect_node(
                    syntax,
                    &parser_kind(&["Term", "binderDefault"]),
                    2,
                    "field default value",
                )?;
                expect_atom(&parts[0], ":=", "field default assignment")?;
                Some(&parts[1])
            }
            _ => return Err(failure(SourceInferenceError::Scope)),
        };
        let Syntax::Ident { val: user_name, .. } = &parts[1] else {
            return Err(failure(SourceInferenceError::Scope));
        };
        if !labels.insert(user_name.clone()) {
            return Err(failure(SourceInferenceError::Record(
                crate::records::RecordError::DuplicateField,
            )));
        }
        if parameters
            .len()
            .saturating_add(output.len())
            .saturating_add(1)
            > budget.max_binders
        {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let sig = expect_node(
            &parts[2],
            &parser_kind(&["Command", "optDeclSig"]),
            2,
            "field signature",
        )?;
        let saved = context.txn.lctx.clone();
        let arguments = context.bind_parameters(&sig[0])?;
        let annotation = optional_type_syntax(&sig[1])?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let domain = context.type_term(annotation)?;
        let mut domain = context.expand_record_aliases(domain, &inheritance.aliases)?;
        if let Some(syntax) = default {
            context.infer_level_params = false;
            let term = context.term(syntax, Some(domain.clone()))?;
            context.infer_level_params = true;
            // Preserve the declared type even when the default is never selected.
            // Its ordinary helper declaration must still pass kernel checking.
            let mut term = context.finish(Typed {
                value: term.value,
                type_: domain.clone(),
            })?;
            term.value = context.expand_record_aliases(term.value, &inheritance.aliases)?;
            term.type_ = context.expand_record_aliases(term.type_, &inheritance.aliases)?;
            // Close only the written record parameters, physical fields and
            // method arguments now. Section dependencies are selected across
            // the whole record (including every default) before closing them.
            // Closing the whole lctx here would capture unused section locals
            // and put helpers out of agreement with the constructor telescope.
            let locals = parameters
                .iter()
                .chain(&output)
                .chain(&arguments)
                .cloned()
                .collect::<Vec<_>>();
            for (index, local) in locals.iter().enumerate().rev() {
                context.tick()?;
                let local_type = context.instantiate(&local.type_)?;
                let local_type = context.expand_record_aliases(local_type, &inheritance.aliases)?;
                let style = if index < parameters.len() && local.binder_info == BinderInfo::Default
                {
                    BinderInfo::Implicit
                } else {
                    local.binder_info
                };
                term.value = term
                    .value
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                term.type_ = term
                    .type_
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                term.value = Expr::lam(
                    local.user_name.clone(),
                    local_type.clone(),
                    term.value,
                    style,
                );
                term.type_ = Expr::forall_e(local.user_name.clone(), local_type, term.type_, style);
            }
            let helper = helper_name(name, user_name);
            helpers.push(Declaration::Defn(DefinitionVal {
                base: ConstantVal {
                    name: helper.clone(),
                    level_params: Vec::new(),
                    type_: term.type_,
                },
                value: term.value,
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![helper.clone()],
            }));
            defaults.push(RecordDefault {
                record: name.clone(),
                field: u32::try_from(output.len())
                    .map_err(|_| failure(SourceInferenceError::ResourceLimit))?,
                helper,
            });
        }
        for arg in arguments.iter().rev() {
            context.tick()?;
            domain = domain
                .abstract_fvar(&arg.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            domain = Expr::forall_e(
                arg.user_name.clone(),
                context.expand_record_aliases(arg.type_.clone(), &inheritance.aliases)?,
                domain,
                arg.binder_info,
            );
        }
        context.txn.lctx = saved;
        let type_ = context
            .known_type(&domain)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        // Universe holes are generalized once the whole record is elaborated (below).
        let completed = context.finish_open_universes(Typed {
            value: domain,
            type_,
        })?;
        let universe = context.sort_level(&completed)?;
        inferred =
            Level::max(inferred, universe).map_err(|_| failure(SourceInferenceError::Scope))?;
        let id = FVarId(context.fresh_name()?);
        context.txn.lctx.add_param(
            id.clone(),
            user_name.clone(),
            completed.value,
            BinderInfo::Default,
        );
        output.push(
            context
                .txn
                .lctx
                .find(&id)
                .expect("inserted record field")
                .clone(),
        );
    }
    let result_level = match explicit {
        Some(value) => {
            let sort = context.whnf(&value)?;
            let ExprNode::Sort { level } = sort.node() else {
                return Err(failure(SourceInferenceError::ExpectedType));
            };
            level.clone()
        }
        None => inferred,
    };
    if result_level.normalize_fixpoint().is_zero() {
        for field in &output {
            context.tick()?;
            let domain = context.instantiate(&field.type_)?;
            let sort = context
                .known_type(&domain)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            if !matches!(context.whnf(&sort)?.node(), ExprNode::Sort { level }
                if level.normalize_fixpoint().is_zero())
            {
                return Err(failure(SourceInferenceError::Record(
                    crate::records::RecordError::NonProofField,
                )));
            }
        }
    }
    let mut parameters = parameters;
    for param in &mut parameters {
        param.type_ = context.instantiate(&param.type_)?;
    }
    let mut roots: Vec<_> = parameters
        .iter()
        .chain(&output)
        .map(|p| p.type_.clone())
        .collect();
    roots.push(Expr::sort(result_level.clone()));
    for helper in &helpers {
        if let Declaration::Defn(definition) = helper {
            roots.extend([definition.base.type_.clone(), definition.value.clone()]);
        }
    }
    // Defaults may mention section parameters absent from the field types.
    // Compute one dependency-closed telescope for the family and all helpers,
    // rather than giving each helper a different (and unusable) interface.
    let mut section = context.section_parameters(&roots, false)?;
    for param in &mut section {
        context.tick()?;
        param.type_ = context.instantiate(&param.type_)?;
        context.require_resolved(std::slice::from_ref(&param.type_))?;
        roots.push(param.type_.clone());
    }
    if section
        .len()
        .saturating_add(parameters.len())
        .saturating_add(output.len())
        > budget.max_binders
    {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    // An auto-bound implicit (or a written `Sort _`) leaves a universe hole in the telescope:
    // generalize it into a level parameter as a definition does (the pin's
    // `@Box : {α : Sort u_1} → α → Type` for `structure Box (x : α)`, 2026-10-11). Only the
    // header's holes, in the parameters and the parents, become parameters, as at the pin
    // (`collectExtraHeaderLMVars`; `levelMVarToParamAtInductives` skips a constructor hole no
    // header mentions). A hole only a field mentions is fitted or defaulted there, never
    // generalized: generalizing it accepted `structure S where β : Type _` with `⟨Type⟩`,
    // which the pin rejects. It stays refused here.
    let header: Vec<Expr> = parameters
        .iter()
        .chain(&section)
        .chain(&output[..parent_count])
        .map(|local| local.type_.clone())
        .collect();
    context.generalize_declaration_universes(&header)?;
    for root in &roots {
        context.tick()?;
        if context.instantiate(root)?.has_level_mvar() {
            return Err(failure(SourceInferenceError::UnresolvedUniverses));
        }
    }
    for local in parameters
        .iter_mut()
        .chain(section.iter_mut())
        .chain(output.iter_mut())
    {
        context.tick()?;
        local.type_ = context.instantiate(&local.type_)?;
    }
    let result_level = match context.instantiate(&Expr::sort(result_level))?.node() {
        ExprNode::Sort { level } => level.clone(),
        _ => return Err(failure(SourceInferenceError::ExpectedType)),
    };
    for helper in &mut helpers {
        if let Declaration::Defn(definition) = helper {
            definition.base.type_ = context.instantiate(&definition.base.type_)?;
            definition.value = context.instantiate(&definition.value)?;
        }
    }
    let mut roots: Vec<_> = parameters
        .iter()
        .chain(&section)
        .chain(&output)
        .map(|p| p.type_.clone())
        .collect();
    roots.push(Expr::sort(result_level.clone()));
    for helper in &helpers {
        if let Declaration::Defn(definition) = helper {
            roots.extend([definition.base.type_.clone(), definition.value.clone()]);
        }
    }
    let level_params = context.declaration_levels(&roots)?;
    let mut closer = crate::records::Builder {
        remaining: budget.max_nodes,
    };
    // Helpers are instantiated at the record's levels by the default registry.
    // Constructor parameters, including explicit section variables, are implicit
    // in its helpers too; retain strict/instance binder styles unchanged.
    for helper in &mut helpers {
        if let Declaration::Defn(definition) = helper {
            definition.base.level_params = level_params.clone();
            definition.base.type_ = closer
                .close(&section, definition.base.type_.clone(), false, true)
                .map_err(|e| failure(SourceInferenceError::Record(e)))?;
            definition.value = closer
                .close(&section, definition.value.clone(), true, true)
                .map_err(|e| failure(SourceInferenceError::Record(e)))?;
        }
    }
    parameters.splice(0..0, section);
    let spec = RecordSpec {
        name: name.clone(),
        level_params,
        parameters,
        fields: output,
        result_level,
        is_class,
    };
    let mut declarations =
        record_declarations(&spec, budget).map_err(|e| failure(SourceInferenceError::Record(e)))?;
    declarations.push(context.record_flat_constructor(&spec, &inheritance.parents, budget)?);
    declarations.extend(helpers);
    let parent_instances = context.record_parent_instances(&spec, &inheritance.parents)?;
    let subobjects: std::collections::BTreeMap<_, _> = inheritance
        .parents
        .iter()
        .map(|parent| (parent.field as usize, &parent.parent))
        .collect();
    let mut fields = Vec::with_capacity(spec.fields.len());
    for (index, field) in spec.fields.iter().enumerate() {
        context.tick()?;
        fields.push(StructureField {
            name: field.user_name.clone(),
            projection: spec.name.append_core(&field.user_name),
            subobject: subobjects.get(&index).copied().cloned(),
            binder_info: field.binder_info,
        });
    }
    let mut parents = Vec::with_capacity(inheritance.parents.len());
    for parent in &inheritance.parents {
        context.tick()?;
        let field = fields.get(parent.field as usize).ok_or_else(|| {
            failure(SourceInferenceError::Record(
                crate::records::RecordError::InvalidTelescope,
            ))
        })?;
        parents.push(StructureParent {
            name: parent.parent.clone(),
            subobject: true,
            projection: field.projection.clone(),
        });
    }
    let structure = StructureEntry {
        name: name.clone(),
        fields,
        parents,
    };
    Ok(SourceRecord {
        name: name.clone(),
        is_class,
        declarations,
        defaults,
        parents: inheritance.parents,
        parent_instances,
        flat_constructor: Name::str(Name::str(name.clone(), "mk"), "_flat_ctor"),
        structure,
    })
}
