//! Nested occurrences, eliminated as the pin's kernel eliminates them before it generates
//! recursors (`elim_nested_inductive_fn` and `restore_nested`, vendored
//! `src/kernel/inductive.cpp:828-1182`; `fln-kernel`'s `check_nested_full` regenerates the
//! same block on admission). A field `List T` of a family `T` stands for an auxiliary family
//! `_nested.List_1` with `List`'s constructors at `T`. The block is built as an ordinary mutual
//! block, and the auxiliary recursors come back as `T.rec_1, …` over the original occurrences.
//!
//! The builder never calls the kernel. Both translate the block independently and admission
//! compares the recursors byte for byte, so a difference here is refused, never admitted.
use super::*;
use fln_env::constants::ConstantInfo;
use fln_env::environment::Environment;
use std::collections::HashMap;

/// How deep a field type may nest before translation stops (a typed resource limit, not a
/// host stack fault).
const MAX_DEPTH: usize = 512;

/// One auxiliary family: the occurrence `head.{levels} arguments` it stands for, over the
/// block's parameters, and its constructors with the originals they stand for.
struct Auxiliary {
    name: Name,
    head: Name,
    levels: Vec<Level>,
    arguments: Vec<Expr>,
    constructors: Vec<(Name, Name)>,
}

struct Translation<'a> {
    env: &'a Environment,
    families: Vec<Name>,
    level_params: Vec<Name>,
    levels: Vec<Level>,
    parameters: Vec<LocalDecl>,
    auxiliaries: Vec<Auxiliary>,
    specs: Vec<InductiveSpec>,
    used: HashSet<FVarId>,
    builder: Builder,
}

impl Translation<'_> {
    fn block_member(&self, name: &Name) -> bool {
        self.families.contains(name) || self.auxiliaries.iter().any(|aux| &aux.name == name)
    }

    /// Whether `term` names a family of the block, an auxiliary included.
    fn mentions_block(&mut self, term: &Expr) -> Result<bool, InductiveError> {
        let mut work = vec![term.clone()];
        let mut seen = HashSet::new();
        while let Some(term) = work.pop() {
            if !seen.insert(term.allocation_identity()) {
                continue;
            }
            self.builder.tick()?;
            match term.node() {
                ExprNode::Const { name, .. } if self.block_member(name) => return Ok(true),
                ExprNode::App { f, a } => {
                    work.push(a.clone());
                    work.push(f.clone());
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    work.push(body.clone());
                    work.push(binder_type.clone());
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    work.push(body.clone());
                    work.push(value.clone());
                    work.push(type_.clone());
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    work.push(expr.clone());
                }
                _ => {}
            }
        }
        Ok(false)
    }

    /// The pin's `replace_if_nested`: the auxiliary standing for `name.{levels} args`, minted
    /// with its whole mutual block on first sight, and the number of parameters it consumes.
    fn occurrence(
        &mut self,
        name: &Name,
        levels: &[Level],
        args: &[Expr],
    ) -> Result<Option<(Name, usize)>, InductiveError> {
        if args.is_empty() || self.block_member(name) {
            return Ok(None);
        }
        let env = self.env;
        let Some(ConstantInfo::Induct(head)) = env.find(name) else {
            return Ok(None);
        };
        let parameters = head.num_params as usize;
        let mut mentions = false;
        for arg in args.iter().take(parameters) {
            if self.mentions_block(arg)? {
                mentions = true;
                break;
            }
        }
        if !mentions {
            return Ok(None);
        }
        // An under-applied occurrence, or a parameter reading a variable bound inside the
        // field, is refused as the pin refuses it (`inductive.cpp:949`).
        if args.len() < parameters
            || args[..parameters]
                .iter()
                .any(|arg| arg.has_loose_bvars() || arg.has_expr_mvar())
        {
            return Err(InductiveError::InvalidTelescope);
        }
        let arguments = &args[..parameters];
        if let Some(aux) = self
            .auxiliaries
            .iter()
            .find(|aux| &aux.head == name && aux.levels == levels && aux.arguments == arguments)
        {
            return Ok(Some((aux.name.clone(), parameters)));
        }
        let all = head.all.clone();
        let auxiliary = self.mint(&all, name, levels, arguments)?;
        Ok(Some((auxiliary, parameters)))
    }

    /// Copy every member of the nested head's mutual block at this occurrence's levels and
    /// parameters (`inductive.cpp:993-1027`). Names and dedup keys are registered first, so
    /// sibling occurrences inside the copies resolve to them.
    fn mint(
        &mut self,
        all: &[Name],
        head: &Name,
        levels: &[Level],
        arguments: &[Expr],
    ) -> Result<Name, InductiveError> {
        let base = self.auxiliaries.len();
        for (offset, member) in all.iter().enumerate() {
            self.builder.tick()?;
            let name = Name::num(
                Name::str(
                    Name::str(Name::anonymous(), "_nested"),
                    member.to_display_string(),
                ),
                u64::try_from(base + offset + 1).map_err(|_| InductiveError::ResourceLimit)?,
            );
            self.auxiliaries.push(Auxiliary {
                name,
                head: member.clone(),
                levels: levels.to_vec(),
                arguments: arguments.to_vec(),
                constructors: Vec::new(),
            });
        }
        let mut result = None;
        for (offset, member) in all.iter().enumerate() {
            let aux_name = self.auxiliaries[base + offset].name.clone();
            if member == head {
                result = Some(aux_name.clone());
            }
            let env = self.env;
            let Some(ConstantInfo::Induct(family)) = env.find(member) else {
                return Err(InductiveError::InvalidTelescope);
            };
            let family = family.clone();
            if family.num_params as usize != arguments.len()
                || family.base.level_params.len() != levels.len()
            {
                return Err(InductiveError::InvalidTelescope);
            }
            let type_ = self.at_site(
                &family.base.type_,
                &family.base.level_params,
                levels,
                arguments,
            )?;
            let (indices, sort) = self.telescope(type_, None)?;
            let ExprNode::Sort { level } = sort.node() else {
                return Err(InductiveError::InvalidTelescope);
            };
            let result_level = level.clone();
            let mut constructors = Vec::new();
            for constructor in &family.ctors {
                self.builder.tick()?;
                let Some(ConstantInfo::Ctor(info)) = env.find(constructor) else {
                    return Err(InductiveError::InvalidTelescope);
                };
                let info = info.clone();
                let type_ =
                    self.at_site(&info.base.type_, &info.base.level_params, levels, arguments)?;
                let (fields, result) = self.telescope(type_, Some(info.num_fields as usize))?;
                let mut result_args = Vec::new();
                let mut spine = &result;
                while let ExprNode::App { f, a } = spine.node() {
                    result_args.push(a.clone());
                    spine = f;
                }
                result_args.reverse();
                if result_args.len() != arguments.len() + indices.len() {
                    return Err(InductiveError::InvalidTelescope);
                }
                let label = strip_family(constructor, member)?;
                self.auxiliaries[base + offset]
                    .constructors
                    .push((aux_name.append_core(&label), constructor.clone()));
                constructors.push(ConstructorSpec {
                    name: label,
                    fields,
                    result_indices: result_args.split_off(arguments.len()),
                });
            }
            self.specs.push(InductiveSpec {
                name: aux_name,
                level_params: self.level_params.clone(),
                parameters: self.parameters.clone(),
                indices,
                constructors,
                result_level,
            });
        }
        result.ok_or(InductiveError::InvalidTelescope)
    }

    /// A constant's type at the occurrence: its universes at the site's levels, its
    /// parameters at the occurrence's arguments.
    fn at_site(
        &mut self,
        type_: &Expr,
        params: &[Name],
        levels: &[Level],
        arguments: &[Expr],
    ) -> Result<Expr, InductiveError> {
        let mut remaining = self.builder.remaining;
        let mut current = crate::universe::parameters::instantiate(
            || {
                remaining = remaining
                    .checked_sub(1)
                    .ok_or(InductiveError::ResourceLimit)?;
                Ok(())
            },
            || InductiveError::InvalidTelescope,
            type_,
            params,
            levels,
        )?;
        self.builder.remaining = remaining;
        for argument in arguments {
            self.builder.tick()?;
            let ExprNode::ForallE { body, .. } = current.node() else {
                return Err(InductiveError::InvalidTelescope);
            };
            current = body
                .subst_loose(0, std::slice::from_ref(argument))
                .map_err(|_| InductiveError::InvalidTelescope)?;
        }
        Ok(current)
    }

    /// Open `count` binders (all of them without a count) as fresh locals named as written.
    fn telescope(
        &mut self,
        mut current: Expr,
        count: Option<usize>,
    ) -> Result<(Vec<LocalDecl>, Expr), InductiveError> {
        let mut locals = Vec::new();
        while count.is_none_or(|count| locals.len() < count) {
            self.builder.tick()?;
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = current.node()
            else {
                if count.is_some() {
                    return Err(InductiveError::InvalidTelescope);
                }
                break;
            };
            let mut local = fresh(&mut self.used, "field", binder_type.clone(), *binder_info);
            local.user_name = binder_name.clone();
            current = body
                .subst_loose(0, &[fv(&local)])
                .map_err(|_| InductiveError::InvalidTelescope)?;
            locals.push(local);
        }
        Ok((locals, current))
    }

    /// The pin's `replace_all_nested` over one field type: every nested occurrence becomes
    /// its auxiliary applied to the block's parameters and the occurrence's remaining
    /// arguments. Occurrences are minted in the pin's visiting order: a node before its
    /// children, a function before its arguments, a binder's domain before its body.
    fn replace(&mut self, term: &Expr) -> Result<Expr, InductiveError> {
        enum Op {
            Enter(Expr, usize),
            Nested(Expr, Name, usize),
            Rebuild(Expr),
        }
        let mut done: HashMap<usize, Expr> = HashMap::new();
        let mut stack = vec![Op::Enter(term.clone(), 0)];
        let get = |done: &HashMap<usize, Expr>, e: &Expr| {
            done.get(&e.allocation_identity())
                .cloned()
                .ok_or(InductiveError::InvalidTelescope)
        };
        while let Some(op) = stack.pop() {
            self.builder.tick()?;
            match op {
                Op::Enter(current, depth) => {
                    if done.contains_key(&current.allocation_identity()) {
                        continue;
                    }
                    if depth > MAX_DEPTH {
                        return Err(InductiveError::ResourceLimit);
                    }
                    let mut args = Vec::new();
                    let mut head = &current;
                    while let ExprNode::App { f, a } = head.node() {
                        args.push(a.clone());
                        head = f;
                    }
                    args.reverse();
                    if let ExprNode::Const { name, levels } = head.node()
                        && let Some((aux, parameters)) =
                            self.occurrence(&name.clone(), &levels.clone(), &args)?
                    {
                        stack.push(Op::Nested(current.clone(), aux, parameters));
                        for arg in args[parameters..].iter().rev() {
                            stack.push(Op::Enter(arg.clone(), depth + 1));
                        }
                        continue;
                    }
                    let children: Vec<Expr> = match current.node() {
                        ExprNode::App { .. } => std::iter::once(head.clone()).chain(args).collect(),
                        ExprNode::Lam {
                            binder_type, body, ..
                        }
                        | ExprNode::ForallE {
                            binder_type, body, ..
                        } => vec![binder_type.clone(), body.clone()],
                        ExprNode::LetE {
                            type_, value, body, ..
                        } => vec![type_.clone(), value.clone(), body.clone()],
                        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                            vec![expr.clone()]
                        }
                        _ => {
                            done.insert(current.allocation_identity(), current.clone());
                            continue;
                        }
                    };
                    stack.push(Op::Rebuild(current.clone()));
                    for child in children.into_iter().rev() {
                        stack.push(Op::Enter(child, depth + 1));
                    }
                }
                Op::Nested(current, aux, parameters) => {
                    let mut args = Vec::new();
                    let mut head = &current;
                    while let ExprNode::App { f, a } = head.node() {
                        args.push(a.clone());
                        head = f;
                    }
                    args.reverse();
                    let mut rebuilt = app(
                        Expr::const_(aux, self.levels.clone()),
                        self.parameters.iter().map(fv),
                    );
                    for arg in &args[parameters..] {
                        rebuilt = Expr::app(rebuilt, get(&done, arg)?);
                    }
                    done.insert(current.allocation_identity(), rebuilt);
                }
                Op::Rebuild(current) => {
                    let rebuilt = match current.node() {
                        ExprNode::App { .. } => {
                            let mut args = Vec::new();
                            let mut head = &current;
                            while let ExprNode::App { f, a } = head.node() {
                                args.push(a.clone());
                                head = f;
                            }
                            args.reverse();
                            let mut rebuilt = get(&done, head)?;
                            for arg in &args {
                                rebuilt = Expr::app(rebuilt, get(&done, arg)?);
                            }
                            rebuilt
                        }
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => Expr::lam(
                            binder_name.clone(),
                            get(&done, binder_type)?,
                            get(&done, body)?,
                            *binder_info,
                        ),
                        ExprNode::ForallE {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => Expr::forall_e(
                            binder_name.clone(),
                            get(&done, binder_type)?,
                            get(&done, body)?,
                            *binder_info,
                        ),
                        ExprNode::LetE {
                            decl_name,
                            type_,
                            value,
                            body,
                            non_dep,
                        } => Expr::let_e(
                            decl_name.clone(),
                            get(&done, type_)?,
                            get(&done, value)?,
                            get(&done, body)?,
                            *non_dep,
                        ),
                        ExprNode::MData { data, expr } => {
                            Expr::mdata(data.clone(), get(&done, expr)?)
                        }
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => Expr::proj(struct_name.clone(), *idx, get(&done, expr)?),
                        _ => current.clone(),
                    };
                    done.insert(current.allocation_identity(), rebuilt);
                }
            }
        }
        get(&done, term)
    }
}

/// `List.cons` relative to `List`: one string component, as the pin names an auxiliary's
/// constructor (`_nested.List_1.cons`).
fn strip_family(constructor: &Name, family: &Name) -> Result<Name, InductiveError> {
    let mut components = Vec::new();
    let mut cursor = constructor.clone();
    while &cursor != family {
        if cursor.is_anonymous() {
            return Err(InductiveError::InvalidName);
        }
        components.push(cursor.clone());
        cursor = cursor.parent();
    }
    let mut relative = Name::anonymous();
    for component in components.iter().rev() {
        relative = match component.leaf_view() {
            LeafView::Str(text) => Name::str(relative, text),
            LeafView::Num(value) => Name::num(relative, value),
            LeafView::Anonymous => relative,
        };
    }
    if relative.is_anonymous() {
        return Err(InductiveError::InvalidName);
    }
    Ok(Name::str(Name::anonymous(), relative.to_display_string()))
}

/// The pin's `restore_nested` (`inductive.cpp:828-872`) on a closed term: an auxiliary
/// recursor renamed, an auxiliary family applied to the block's parameters mapped back to its
/// occurrence, and an auxiliary constructor to the original constructor at that occurrence.
struct Restore {
    parameters: usize,
    renamed: HashMap<Name, Name>,
    /// Auxiliary family or constructor → the original head applied to the occurrence's
    /// arguments, with the block's parameters as the outermost loose bound variables.
    templates: HashMap<Name, Expr>,
}

impl Restore {
    fn new(translation: &Translation<'_>, base: &Name) -> Result<Self, InductiveError> {
        let mut renamed = HashMap::new();
        let mut templates = HashMap::new();
        let close = |term: Expr| -> Result<Expr, InductiveError> {
            let count = translation.parameters.len();
            let mut term = term;
            for (position, parameter) in translation.parameters.iter().enumerate() {
                term = term
                    .abstract_fvar(&parameter.id, (count - 1 - position) as u32)
                    .map_err(|_| InductiveError::InvalidTelescope)?;
            }
            Ok(term)
        };
        for (ordinal, aux) in translation.auxiliaries.iter().enumerate() {
            renamed.insert(
                Name::str(aux.name.clone(), "rec"),
                Name::str(base.clone(), format!("rec_{}", ordinal + 1)),
            );
            templates.insert(
                aux.name.clone(),
                close(app(
                    Expr::const_(aux.head.clone(), aux.levels.clone()),
                    aux.arguments.iter().cloned(),
                ))?,
            );
            for (auxiliary, original) in &aux.constructors {
                templates.insert(
                    auxiliary.clone(),
                    close(app(
                        Expr::const_(original.clone(), aux.levels.clone()),
                        aux.arguments.iter().cloned(),
                    ))?,
                );
            }
        }
        Ok(Self {
            parameters: translation.parameters.len(),
            renamed,
            templates,
        })
    }

    fn constant(&self, name: &Name) -> Name {
        self.renamed
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.clone())
    }

    fn expr(&self, builder: &mut Builder, term: &Expr) -> Result<Expr, InductiveError> {
        enum Op {
            Enter(Expr),
            Rebuild(Expr),
        }
        let mut done: HashMap<usize, Expr> = HashMap::new();
        let mut stack = vec![Op::Enter(term.clone())];
        let get = |done: &HashMap<usize, Expr>, e: &Expr| {
            done.get(&e.allocation_identity())
                .cloned()
                .ok_or(InductiveError::InvalidTelescope)
        };
        while let Some(op) = stack.pop() {
            builder.tick()?;
            match op {
                Op::Enter(current) => {
                    if done.contains_key(&current.allocation_identity()) {
                        continue;
                    }
                    let mut args = Vec::new();
                    let mut head = &current;
                    while let ExprNode::App { f, a } = head.node() {
                        args.push(a.clone());
                        head = f;
                    }
                    let children: Vec<Expr> = match current.node() {
                        ExprNode::App { .. } => {
                            args.reverse();
                            std::iter::once(head.clone()).chain(args).collect()
                        }
                        ExprNode::Lam {
                            binder_type, body, ..
                        }
                        | ExprNode::ForallE {
                            binder_type, body, ..
                        } => vec![binder_type.clone(), body.clone()],
                        ExprNode::LetE {
                            type_, value, body, ..
                        } => vec![type_.clone(), value.clone(), body.clone()],
                        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                            vec![expr.clone()]
                        }
                        ExprNode::Const { name, levels } => {
                            let restored = match self.templates.get(name) {
                                // A block without parameters applies an auxiliary to none.
                                Some(template) if self.parameters == 0 => template.clone(),
                                // Otherwise only an application to the parameters restores.
                                Some(_) => return Err(InductiveError::InvalidTelescope),
                                None => Expr::const_(self.constant(name), levels.clone()),
                            };
                            done.insert(current.allocation_identity(), restored);
                            continue;
                        }
                        _ => {
                            done.insert(current.allocation_identity(), current.clone());
                            continue;
                        }
                    };
                    // An application's template head is restored with its arguments, never
                    // alone; anywhere else a template is a constant of its own.
                    let template_head = matches!(current.node(), ExprNode::App { .. })
                        && matches!(head.node(), ExprNode::Const { name, .. }
                            if self.templates.contains_key(name));
                    stack.push(Op::Rebuild(current.clone()));
                    for (position, child) in children.into_iter().enumerate().rev() {
                        if position == 0 && template_head {
                            continue;
                        }
                        stack.push(Op::Enter(child));
                    }
                }
                Op::Rebuild(current) => {
                    let rebuilt = match current.node() {
                        ExprNode::App { .. } => {
                            let mut args = Vec::new();
                            let mut head = &current;
                            while let ExprNode::App { f, a } = head.node() {
                                args.push(a.clone());
                                head = f;
                            }
                            args.reverse();
                            let mut restored = Vec::with_capacity(args.len());
                            for arg in &args {
                                restored.push(get(&done, arg)?);
                            }
                            match head.node() {
                                ExprNode::Const { name, .. }
                                    if self.templates.contains_key(name) =>
                                {
                                    if restored.len() < self.parameters {
                                        return Err(InductiveError::InvalidTelescope);
                                    }
                                    let template = &self.templates[name];
                                    let site = template
                                        .subst_loose(0, &restored[..self.parameters])
                                        .map_err(|_| InductiveError::InvalidTelescope)?;
                                    app(site, restored.split_off(self.parameters))
                                }
                                _ => app(get(&done, head)?, restored),
                            }
                        }
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => Expr::lam(
                            binder_name.clone(),
                            get(&done, binder_type)?,
                            get(&done, body)?,
                            *binder_info,
                        ),
                        ExprNode::ForallE {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => Expr::forall_e(
                            binder_name.clone(),
                            get(&done, binder_type)?,
                            get(&done, body)?,
                            *binder_info,
                        ),
                        ExprNode::LetE {
                            decl_name,
                            type_,
                            value,
                            body,
                            non_dep,
                        } => Expr::let_e(
                            decl_name.clone(),
                            get(&done, type_)?,
                            get(&done, value)?,
                            get(&done, body)?,
                            *non_dep,
                        ),
                        ExprNode::MData { data, expr } => {
                            Expr::mdata(data.clone(), get(&done, expr)?)
                        }
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => Expr::proj(struct_name.clone(), *idx, get(&done, expr)?),
                        _ => current.clone(),
                    };
                    done.insert(current.allocation_identity(), rebuilt);
                }
            }
        }
        get(&done, term)
    }
}

/// Build a block whose constructor fields hold nested occurrences, or `None` when none does
/// (the ordinary builders then apply). `promoted[f][c]` is as for the mutual builder.
pub(crate) fn nested_inductive_declaration(
    env: &Environment,
    specs: &[InductiveSpec],
    budget: RecordBudget,
    promoted: &[Vec<Vec<LocalDecl>>],
) -> Result<Option<Declaration>, InductiveError> {
    let Some(first) = specs.first() else {
        return Err(InductiveError::InvalidTelescope);
    };
    if promoted.len() != specs.len() {
        return Err(InductiveError::InvalidTelescope);
    }
    let mut used = HashSet::new();
    for spec in specs {
        for local in spec.parameters.iter().chain(&spec.indices) {
            used.insert(local.id.clone());
        }
        for ctor in &spec.constructors {
            for field in &ctor.fields {
                used.insert(field.id.clone());
            }
        }
    }
    for binder in promoted.iter().flatten().flatten() {
        used.insert(binder.id.clone());
    }
    let mut translation = Translation {
        env,
        families: specs.iter().map(|spec| spec.name.clone()).collect(),
        level_params: first.level_params.clone(),
        levels: first
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect(),
        parameters: first.parameters.clone(),
        auxiliaries: Vec::new(),
        specs: Vec::new(),
        used,
        builder: Builder {
            remaining: budget.max_nodes,
        },
    };
    // The main constructors first, then each auxiliary's in creation order: the worklist
    // order fixes the auxiliaries' numbering and so the recursors' (`inductive.cpp:1036`).
    let mut main = specs.to_vec();
    for spec in &mut main {
        for ctor in &mut spec.constructors {
            for field in &mut ctor.fields {
                field.type_ = translation.replace(&field.type_)?;
            }
        }
    }
    if translation.auxiliaries.is_empty() {
        return Ok(None);
    }
    let mut next = 0;
    while next < translation.specs.len() {
        let mut spec = translation.specs[next].clone();
        for ctor in &mut spec.constructors {
            for field in &mut ctor.fields {
                field.type_ = translation.replace(&field.type_)?;
            }
        }
        translation.specs[next] = spec;
        next += 1;
    }
    let main_count = main.len();
    let auxiliary_count = translation.specs.len();
    let mut all_specs = main;
    all_specs.extend(translation.specs.iter().cloned());
    let mut all_promoted = promoted.to_vec();
    all_promoted.extend(
        translation
            .specs
            .iter()
            .map(|spec| vec![Vec::new(); spec.constructors.len()]),
    );
    let Declaration::Inductive(block) =
        mutual::build_nested_block(&all_specs, budget, &all_promoted)?
    else {
        return Err(InductiveError::InvalidTelescope);
    };
    let restore = Restore::new(&translation, &first.name)?;
    let mut builder = Builder {
        remaining: budget.max_nodes,
    };
    let main_names: Vec<Name> = specs.iter().map(|spec| spec.name.clone()).collect();
    let nested = u32::try_from(auxiliary_count).map_err(|_| InductiveError::ResourceLimit)?;
    let mut types = Vec::with_capacity(main_count);
    for mut family in block.types.into_iter().take(main_count) {
        family.all = main_names.clone();
        family.num_nested = nested;
        types.push(family);
    }
    let mut ctors = Vec::new();
    for mut ctor in block.ctors {
        if !main_names.contains(&ctor.induct) {
            continue;
        }
        ctor.base.type_ = restore.expr(&mut builder, &ctor.base.type_)?;
        ctors.push(ctor);
    }
    let mut recursors = Vec::with_capacity(block.recursors.len());
    for mut recursor in block.recursors {
        recursor.base.name = restore.constant(&recursor.base.name);
        recursor.base.type_ = restore.expr(&mut builder, &recursor.base.type_)?;
        recursor.all = main_names.clone();
        for rule in &mut recursor.rules {
            if let Some((_, original)) = translation
                .auxiliaries
                .iter()
                .flat_map(|aux| &aux.constructors)
                .find(|(auxiliary, _)| auxiliary == &rule.ctor)
            {
                rule.ctor = original.clone();
            }
            rule.rhs = restore.expr(&mut builder, &rule.rhs)?;
        }
        recursors.push(recursor);
    }
    Ok(Some(Declaration::Inductive(InductiveBlock {
        types,
        ctors,
        recursors,
    })))
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::outcome::Outcome;
    use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};
    use fln_kernel::verdict::{Budget, Verdict};

    fn name(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    fn publish(env: &Environment, declaration: Declaration) -> Environment {
        let Outcome::Complete(admitted) = admit(env, declaration, Budget::DEFAULT) else {
            panic!("the test declaration must reach a kernel verdict");
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("the kernel-accepted test declaration must pass the empty council");
        };
        match checked.publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        ) {
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(
                publication,
            ))) => publication.environment,
            Outcome::Complete(Published::BlockCommitted(publication)) => publication.environment,
            other => panic!("the test declaration must publish once: {other:?}"),
        }
    }

    /// `List.{u} (α : Type u)` with `nil` and `cons (head : α) (tail : List α)`.
    fn list_environment() -> Environment {
        let mut used = HashSet::new();
        let universe = Level::param(name("u")).succ().unwrap();
        let alpha = fresh(
            &mut used,
            "α",
            Expr::sort(universe.clone()),
            BinderInfo::Default,
        );
        let list = |alpha: &LocalDecl| {
            Expr::app(
                Expr::const_(name("List"), vec![Level::param(name("u"))]),
                fv(alpha),
            )
        };
        let head = fresh(&mut used, "head", fv(&alpha), BinderInfo::Default);
        let tail = fresh(&mut used, "tail", list(&alpha), BinderInfo::Default);
        let declaration = inductive_declaration(
            &InductiveSpec {
                name: name("List"),
                level_params: vec![name("u")],
                parameters: vec![alpha],
                indices: Vec::new(),
                constructors: vec![
                    ConstructorSpec {
                        name: name("nil"),
                        fields: Vec::new(),
                        result_indices: Vec::new(),
                    },
                    ConstructorSpec {
                        name: name("cons"),
                        fields: vec![head, tail],
                        result_indices: Vec::new(),
                    },
                ],
                result_level: universe,
            },
            RecordBudget::default(),
        )
        .expect("List is an ordinary family");
        publish(&Environment::new(), declaration)
    }

    fn list_of(element: Expr) -> Expr {
        Expr::app(Expr::const_(name("List"), vec![Level::zero()]), element)
    }

    /// `inductive T | mk (f : field) …`, with `T` as a constant in each field.
    fn family(field: impl Fn(Expr) -> Expr) -> InductiveSpec {
        family_of(&[&field])
    }

    fn family_of(fields: &[&dyn Fn(Expr) -> Expr]) -> InductiveSpec {
        let mut used = HashSet::new();
        let t = Expr::const_(name("T"), Vec::new());
        let fields = fields
            .iter()
            .map(|field| fresh(&mut used, "f", field(t.clone()), BinderInfo::Default))
            .collect();
        InductiveSpec {
            name: name("T"),
            level_params: Vec::new(),
            parameters: Vec::new(),
            indices: Vec::new(),
            constructors: vec![ConstructorSpec {
                name: name("mk"),
                fields,
                result_indices: Vec::new(),
            }],
            result_level: Level::one(),
        }
    }

    fn build(
        env: &Environment,
        spec: &InductiveSpec,
    ) -> Result<Option<Declaration>, InductiveError> {
        nested_inductive_declaration(
            env,
            std::slice::from_ref(spec),
            RecordBudget::default(),
            &[vec![Vec::new(); spec.constructors.len()]],
        )
    }

    fn verdict(env: &Environment, declaration: &Declaration) -> Verdict {
        let Outcome::Complete(verdict) = fln_kernel::check(env, declaration, Budget::DEFAULT)
        else {
            panic!("the bounded test block must reach a verdict");
        };
        verdict
    }

    /// Two auxiliaries, in the pin's worklist order: `List T` and `List (List T)` from the main
    /// constructor's fields; the second's own `cons` reads `List T` again.
    fn two_level() -> InductiveSpec {
        family_of(&[&list_of, &|t| list_of(list_of(t))])
    }

    #[test]
    fn nested_blocks_are_the_blocks_the_kernel_regenerates() {
        let env = list_environment();
        for spec in [family(list_of), two_level()] {
            let declaration = build(&env, &spec)
                .expect("a positive nested occurrence builds")
                .expect("a nested occurrence is translated");
            assert!(verdict(&env, &declaration).is_accepted(), "{declaration:?}");
            let Declaration::Inductive(block) = &declaration else {
                panic!("a nested family is an inductive block");
            };
            assert_eq!(block.types.len(), 1);
            assert_eq!(block.types[0].all, vec![name("T")]);
            let names: Vec<_> = block
                .recursors
                .iter()
                .map(|r| r.base.name.to_display_string())
                .collect();
            let expected: &[&str] = if block.types[0].num_nested == 1 {
                &["T.rec", "T.rec_1"]
            } else {
                &["T.rec", "T.rec_1", "T.rec_2"]
            };
            assert_eq!(names, expected);
        }
    }

    #[test]
    fn a_misnumbered_or_undeclared_auxiliary_is_refused_by_admission() {
        let env = list_environment();
        let Some(Declaration::Inductive(block)) = build(&env, &two_level()).unwrap() else {
            panic!("two auxiliaries");
        };
        assert_eq!(block.types[0].num_nested, 2);
        // The auxiliaries' recursors exchanged: each name now holds the other's motive order.
        let mut swapped = block.clone();
        let first = swapped.recursors[1].base.name.clone();
        swapped.recursors[1].base.name = swapped.recursors[2].base.name.clone();
        swapped.recursors[2].base.name = first;
        let mut undeclared = block.clone();
        undeclared.types[0].num_nested = 1;
        for mutant in [swapped, undeclared] {
            assert!(
                verdict(&env, &Declaration::Inductive(mutant)).is_rejected(),
                "admission must refuse a planted block"
            );
        }
    }

    #[test]
    fn negative_and_local_capturing_occurrences_are_refused() {
        let env = list_environment();
        let negative =
            family(|t| list_of(Expr::forall_e(name("x"), t.clone(), t, BinderInfo::Default)));
        assert!(build(&env, &negative).is_err());
        // `∀ (α : Type), List (α → T)`: the occurrence's parameter reads the bound `α`.
        let capturing = family(|t| {
            Expr::forall_e(
                name("α"),
                Expr::sort(Level::one()),
                list_of(Expr::forall_e(
                    name("x"),
                    Expr::bvar(0).unwrap(),
                    t,
                    BinderInfo::Default,
                )),
                BinderInfo::Default,
            )
        });
        assert_eq!(
            build(&env, &capturing).unwrap_err(),
            InductiveError::InvalidTelescope
        );
        // A family without nested occurrences is left to the ordinary builders.
        let plain = family(|_| Expr::sort(Level::zero()));
        assert!(build(&env, &plain).unwrap().is_none());
    }
}
