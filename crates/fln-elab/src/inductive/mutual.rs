//! Native construction of one complete mutual inductive block.
//!
//! Sibling occurrences are allowed only as uniform strictly-positive children.
//! Each child uses its destination's motive, indices and recursor. The result
//! is a candidate, never an environment update or a checking certificate.
use super::*;

struct Child {
    family: usize,
    telescope: RecursiveField,
}
struct Minor<'a> {
    family: usize,
    constructor: &'a ConstructorSpec,
    children: Vec<Option<Child>>,
}

fn scan(
    builder: &mut Builder,
    term: &Expr,
    scope: &HashSet<FVarId>,
    specs: &[InductiveSpec],
) -> Result<(), InductiveError> {
    for spec in specs {
        builder.scan(term, scope, &spec.name)?;
    }
    Ok(())
}

fn child(
    builder: &mut Builder,
    term: &Expr,
    scope: &HashSet<FVarId>,
    specs: &[InductiveSpec],
    levels: &[Level],
    used: &mut HashSet<FVarId>,
) -> Result<Option<Child>, InductiveError> {
    let mut body = term.clone();
    let mut scope = scope.clone();
    let mut arguments = Vec::new();
    loop {
        builder.tick()?;
        match body.node() {
            ExprNode::MData { expr, .. } => body = expr.clone(),
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body: result,
                binder_info,
            } => {
                // Negative cross-family occurrences are as invalid as negative
                // self occurrences, including in dependent function domains.
                scan(builder, binder_type, &scope, specs)?;
                let mut argument = fresh(used, "arg", binder_type.clone(), *binder_info);
                argument.user_name = binder_name.clone();
                body = result
                    .subst_loose(0, &[fv(&argument)])
                    .map_err(|_| InductiveError::InvalidTelescope)?;
                scope.insert(argument.id.clone());
                arguments.push(argument);
            }
            _ => break,
        }
    }
    for (family, spec) in specs.iter().enumerate() {
        if let Some(indices) = recursive_indices(builder, &body, spec, levels, &scope)? {
            for index in &indices {
                scan(builder, index, &scope, specs)?;
            }
            return Ok(Some(Child {
                family,
                telescope: RecursiveField { arguments, indices },
            }));
        }
    }
    // This includes nonuniform and nested occurrences: none may be silently
    // classified as an ordinary field and bypass positivity reconstruction.
    scan(builder, &body, &scope, specs)?;
    Ok(None)
}

/// Construct two to eight safe families with one shared parameter and
/// universe telescope. Parameter identities and types must agree across specs;
/// each index/constructor telescope is otherwise scoped independently. Both
/// admission engines still check all signatures, universes, types and rules.
pub fn mutual_inductive_declaration(
    specs: &[InductiveSpec],
    budget: RecordBudget,
) -> Result<Declaration, InductiveError> {
    build_mutual(specs, budget, None)
}

/// [`mutual_inductive_declaration`] for a block whose trailing parameters were
/// written as indices and promoted (the Reference's `fixedIndicesToParams`).
/// `promoted[f][c]` holds constructor `c` of family `f`'s own binders for those
/// parameters, as in `inductive_with_promoted_parameters`: only the constructor
/// types read them; each family type binds the promoted parameters by its own
/// index binders, and the recursors by the first family's.
pub(crate) fn mutual_inductive_with_promoted_parameters(
    specs: &[InductiveSpec],
    budget: RecordBudget,
    promoted: &[Vec<Vec<LocalDecl>>],
) -> Result<Declaration, InductiveError> {
    build_mutual(specs, budget, Some(promoted))
}

fn build_mutual(
    specs: &[InductiveSpec],
    budget: RecordBudget,
    promoted: Option<&[Vec<Vec<LocalDecl>>]>,
) -> Result<Declaration, InductiveError> {
    if !(2..=8).contains(&specs.len()) {
        return Err(InductiveError::InvalidTelescope);
    }
    let first = &specs[0];
    if let Some(promoted) = promoted
        && (promoted.len() != specs.len()
            || promoted.iter().zip(specs).any(|(family, spec)| {
                family.len() != spec.constructors.len()
                    || family.iter().any(|own| {
                        own.len() > first.parameters.len()
                            || own
                                .iter()
                                .zip(&first.parameters[first.parameters.len() - own.len()..])
                                .any(|(binder, parameter)| {
                                    binder.id != parameter.id || binder.is_let()
                                })
                    })
            }))
    {
        return Err(InductiveError::InvalidTelescope);
    }
    let mut builder = Builder {
        remaining: budget.max_nodes,
    };
    let mut count = 0usize;
    let mut names = HashSet::new();
    let mut used = HashSet::new();
    let mut universe_names = HashSet::new();
    if first.level_params.len() > budget.max_binders {
        return Err(InductiveError::ResourceLimit);
    }
    for name in &first.level_params {
        builder.tick()?;
        if name.is_anonymous() || !universe_names.insert(name.clone()) {
            return Err(InductiveError::InvalidTelescope);
        }
    }
    if first.result_level.has_mvar() {
        return Err(InductiveError::UnsupportedSort);
    }
    let result_level = first.result_level.normalize_fixpoint();
    for spec in specs {
        builder.tick()?;
        if spec.name.is_anonymous() || !names.insert(spec.name.clone()) {
            return Err(InductiveError::InvalidName);
        }
        if spec.level_params != first.level_params
            || spec.parameters.len() != first.parameters.len()
            || spec
                .parameters
                .iter()
                .zip(&first.parameters)
                .any(|(a, b)| a.id != b.id || a.type_ != b.type_ || a.binder_info != b.binder_info)
        {
            return Err(InductiveError::InvalidTelescope);
        }
        if spec.result_level.has_mvar() || spec.result_level.normalize_fixpoint() != result_level {
            return Err(InductiveError::UnsupportedSort);
        }
        count = count
            .checked_add(spec.parameters.len())
            .and_then(|n| n.checked_add(spec.indices.len()))
            .and_then(|n| n.checked_add(spec.constructors.len()))
            .ok_or(InductiveError::ResourceLimit)?;
        for ctor in &spec.constructors {
            count = count
                .checked_add(ctor.fields.len())
                .and_then(|n| n.checked_add(ctor.result_indices.len()))
                .ok_or(InductiveError::ResourceLimit)?;
        }
        if count > budget.max_binders {
            return Err(InductiveError::ResourceLimit);
        }
        let mut scope = HashSet::new();
        for local in spec.parameters.iter().chain(&spec.indices) {
            builder.tick()?;
            if local.is_let() || scope.contains(&local.id) {
                return Err(InductiveError::InvalidTelescope);
            }
            scan(&mut builder, &local.type_, &scope, specs)?;
            scope.insert(local.id.clone());
        }
        used.extend(scope);
        used.extend(
            spec.constructors
                .iter()
                .flat_map(|c| c.fields.iter().map(|f| f.id.clone())),
        );
    }
    let all: Vec<_> = specs.iter().map(|s| s.name.clone()).collect();
    let rec_names: Vec<_> = all.iter().map(|n| Name::str(n.clone(), "rec")).collect();
    for name in &rec_names {
        if !names.insert(name.clone()) {
            return Err(InductiveError::InvalidName);
        }
    }
    let levels: Vec<_> = first
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    let mut entries = Vec::new();
    let mut constructor_names = Vec::new();
    let mut family_constructors = vec![Vec::new(); specs.len()];
    for (family, spec) in specs.iter().enumerate() {
        for (position, ctor) in spec.constructors.iter().enumerate() {
            builder.tick()?;
            if !matches!(ctor.name.leaf_view(), LeafView::Str(s) if !s.is_empty())
                || !ctor.name.parent().is_anonymous()
            {
                return Err(InductiveError::InvalidName);
            }
            if let Some(promoted) = promoted {
                let own = &promoted[family][position];
                let shared = first.parameters.len() - own.len();
                for (offset, binder) in own.iter().enumerate() {
                    let scope: HashSet<_> = first.parameters[..shared + offset]
                        .iter()
                        .map(|p| p.id.clone())
                        .collect();
                    scan(&mut builder, &binder.type_, &scope, specs)?;
                }
            }
            let name = spec.name.append_core(&ctor.name);
            if !names.insert(name.clone()) {
                return Err(InductiveError::DuplicateConstructor);
            }
            family_constructors[family].push(name.clone());
            constructor_names.push(name);
            let mut scope: HashSet<_> = first.parameters.iter().map(|p| p.id.clone()).collect();
            let mut children = Vec::new();
            for field in &ctor.fields {
                builder.tick()?;
                if field.is_let() || scope.contains(&field.id) {
                    return Err(InductiveError::InvalidTelescope);
                }
                children.push(child(
                    &mut builder,
                    &field.type_,
                    &scope,
                    specs,
                    &levels,
                    &mut used,
                )?);
                scope.insert(field.id.clone());
            }
            if ctor.result_indices.len() != spec.indices.len() {
                return Err(InductiveError::InvalidTelescope);
            }
            for index in &ctor.result_indices {
                scan(&mut builder, index, &scope, specs)?;
            }
            entries.push(Minor {
                family,
                constructor: ctor,
                children,
            });
        }
    }
    // The pin's `elim_only_at_universe_zero` (kernel/inductive.cpp) restricts
    // every mutual family whose result universe may be zero to Prop. This
    // includes a universe parameter, even at its nonzero instantiations. Such
    // recursors have no fresh elimination-universe parameter, including in
    // the recursive calls stored in their computation rules.
    let elim = if result_level.is_never_zero() {
        let mut name = Name::from_components(["u"]);
        let mut ordinal = 0usize;
        while universe_names.contains(&name) {
            builder.tick()?;
            ordinal += 1;
            name = Name::from_components([format!("u_{ordinal}").as_str()]);
        }
        Some(name)
    } else {
        None
    };
    let elim_level = elim
        .as_ref()
        .map_or_else(Level::zero, |name| Level::param(name.clone()));
    let rec_params: Vec<_> = elim.iter().chain(&first.level_params).cloned().collect();
    let mut majors = Vec::new();
    let mut motives = Vec::new();
    let prefixes: Vec<_> = specs
        .iter()
        .map(|s| {
            app(
                Expr::const_(s.name.clone(), levels.clone()),
                first.parameters.iter().map(fv),
            )
        })
        .collect();
    for (family, spec) in specs.iter().enumerate() {
        let major = fresh(
            &mut used,
            "t",
            app(prefixes[family].clone(), spec.indices.iter().map(fv)),
            BinderInfo::Default,
        );
        let ty = builder.close(
            std::slice::from_ref(&major),
            Expr::sort(elim_level.clone()),
            false,
            false,
        )?;
        let ty = builder.close(&spec.indices, ty, false, false)?;
        motives.push(fresh(
            &mut used,
            &format!("motive_{}", family + 1),
            ty,
            BinderInfo::Default,
        ));
        majors.push(major);
    }
    let mut minors = Vec::new();
    let mut constructors = Vec::new();
    let params =
        u32::try_from(first.parameters.len()).map_err(|_| InductiveError::ResourceLimit)?;
    let mut cidx = vec![0u32; specs.len()];
    for (index, entry) in entries.iter().enumerate() {
        let ctor = entry.constructor;
        let mut hypotheses = Vec::new();
        for (field, child) in ctor.fields.iter().zip(&entry.children) {
            if let Some(child) = child {
                let target = &child.telescope;
                let value = app(fv(field), target.arguments.iter().map(fv));
                let ty = Expr::app(
                    app(fv(&motives[child.family]), target.indices.iter().cloned()),
                    value,
                );
                let ty = builder.close(&target.arguments, ty, false, false)?;
                let mut ih = fresh(&mut used, "ih", ty, BinderInfo::Default);
                ih.user_name = append_ih(&field.user_name);
                hypotheses.push(ih);
            }
        }
        let constructed = app(
            Expr::const_(constructor_names[index].clone(), levels.clone()),
            first.parameters.iter().chain(&ctor.fields).map(fv),
        );
        let ty = Expr::app(
            app(
                fv(&motives[entry.family]),
                ctor.result_indices.iter().cloned(),
            ),
            constructed,
        );
        let ty = builder.close(&hypotheses, ty, false, false)?;
        let ty = builder.close(&ctor.fields, ty, false, false)?;
        let mut minor = fresh(&mut used, "minor", ty, BinderInfo::Default);
        minor.user_name = ctor.name.clone();
        minors.push(minor);
        let ty = app(
            prefixes[entry.family].clone(),
            ctor.result_indices.iter().cloned(),
        );
        let ty = builder.close(&ctor.fields, ty, false, false)?;
        let own = promoted.map_or(&[][..], |promoted| {
            promoted[entry.family][cidx[entry.family] as usize].as_slice()
        });
        let ty = builder.close(own, ty, false, false)?;
        let shared = &first.parameters[..first.parameters.len() - own.len()];
        let ty = builder.close(shared, ty, false, true)?;
        constructors.push(ConstructorVal {
            base: ConstantVal {
                name: constructor_names[index].clone(),
                level_params: first.level_params.clone(),
                type_: ty,
            },
            induct: all[entry.family].clone(),
            cidx: cidx[entry.family],
            num_params: params,
            num_fields: u32::try_from(ctor.fields.len())
                .map_err(|_| InductiveError::ResourceLimit)?,
            is_unsafe: false,
        });
        cidx[entry.family] += 1;
    }
    let rec_levels: Vec<_> = rec_params.iter().cloned().map(Level::param).collect();
    let rec_prefixes: Vec<_> = rec_names
        .iter()
        .map(|n| {
            app(
                Expr::const_(n.clone(), rec_levels.clone()),
                first
                    .parameters
                    .iter()
                    .chain(&motives)
                    .chain(&minors)
                    .map(fv),
            )
        })
        .collect();
    let mut rules = vec![Vec::new(); specs.len()];
    for (index, entry) in entries.iter().enumerate() {
        let ctor = entry.constructor;
        let mut rhs = app(fv(&minors[index]), ctor.fields.iter().map(fv));
        for (field, child) in ctor.fields.iter().zip(&entry.children) {
            if let Some(child) = child {
                let target = &child.telescope;
                let value = app(fv(field), target.arguments.iter().map(fv));
                let call = Expr::app(
                    app(
                        rec_prefixes[child.family].clone(),
                        target.indices.iter().cloned(),
                    ),
                    value,
                );
                let call = builder.close(&target.arguments, call, true, false)?;
                rhs = Expr::app(rhs, call);
            }
        }
        rhs = builder.close(&ctor.fields, rhs, true, false)?;
        rhs = builder.close(&minors, rhs, true, false)?;
        rhs = builder.close(&motives, rhs, true, false)?;
        rhs = builder.close(&first.parameters, rhs, true, false)?;
        rules[entry.family].push(RecursorRule {
            ctor: constructor_names[index].clone(),
            nfields: constructors[index].num_fields,
            rhs,
        });
    }
    // A motive with no occurrence in a minor is explicit. In particular an
    // empty sibling must not gain an uninferable implicit motive.
    let mut typed_motives = motives.clone();
    for motive in &mut typed_motives {
        for minor in &minors {
            builder.tick()?;
            let closed = minor
                .type_
                .abstract_fvar(&motive.id, 0)
                .map_err(|_| InductiveError::InvalidTelescope)?;
            if closed.has_loose_bvars() {
                motive.binder_info = BinderInfo::Implicit;
                break;
            }
        }
    }
    let recursive = entries
        .iter()
        .any(|m| m.children.iter().any(Option::is_some));
    let reflexive = entries
        .iter()
        .flat_map(|m| &m.children)
        .flatten()
        .any(|c| !c.telescope.arguments.is_empty());
    let mut types = Vec::new();
    let mut recursors = Vec::new();
    for (family, spec) in specs.iter().enumerate() {
        let ty = builder.close(
            &spec.indices,
            Expr::sort(spec.result_level.clone()),
            false,
            false,
        )?;
        // A family type keeps its own parameter binder names (they differ only
        // for promoted indices; identities, domains and styles are checked equal).
        let ty = builder.close(&spec.parameters, ty, false, false)?;
        let indices =
            u32::try_from(spec.indices.len()).map_err(|_| InductiveError::ResourceLimit)?;
        types.push(InductiveVal {
            base: ConstantVal {
                name: spec.name.clone(),
                level_params: first.level_params.clone(),
                type_: ty,
            },
            num_params: params,
            num_indices: indices,
            all: all.clone(),
            ctors: family_constructors[family].clone(),
            num_nested: 0,
            is_rec: recursive,
            is_unsafe: false,
            is_reflexive: reflexive,
        });
        let major = &majors[family];
        let ty = Expr::app(
            app(fv(&motives[family]), spec.indices.iter().map(fv)),
            fv(major),
        );
        let ty = builder.close(std::slice::from_ref(major), ty, false, false)?;
        let ty = builder.close(&spec.indices, ty, false, true)?;
        let ty = builder.close(&minors, ty, false, false)?;
        let ty = builder.close(&typed_motives, ty, false, false)?;
        let ty = builder.close(&first.parameters, ty, false, true)?;
        recursors.push(RecursorVal {
            base: ConstantVal {
                name: rec_names[family].clone(),
                level_params: rec_params.clone(),
                type_: ty,
            },
            all: all.clone(),
            num_params: params,
            num_indices: indices,
            num_motives: u32::try_from(specs.len()).map_err(|_| InductiveError::ResourceLimit)?,
            num_minors: u32::try_from(minors.len()).map_err(|_| InductiveError::ResourceLimit)?,
            rules: std::mem::take(&mut rules[family]),
            k: false,
            is_unsafe: false,
        });
    }
    Ok(Declaration::Inductive(InductiveBlock {
        types,
        ctors: constructors,
        recursors,
    }))
}
