//! Exact, bounded indexing for immutable direct instance type telescopes.
//!
//! Telescope variables represent the pin's fresh assignable metavariables and
//! index as Star. Definition, recursor, projection, eta and nonempty annotation
//! normalization are explicit unsupported results, never guessed paths. This
//! keeps an exported path independent of later reducibility changes.
use super::*;
use fln_core::expr::{FVarId, Literal};

enum Error {
    Unsupported,
    Registry(InstanceRegistryError),
}
impl From<InstanceRegistryError> for Error {
    fn from(error: InstanceRegistryError) -> Self {
        Self::Registry(error)
    }
}
type Result<T> = std::result::Result<T, Error>;

struct Local {
    id: FVarId,
    type_: Expr,
    binder: BinderInfo,
}
struct Indexer<'a> {
    env: &'a Environment,
    classes: &'a BTreeSet<Name>,
    imported_classes: &'a BTreeMap<Name, imported::ClassParameters>,
    remaining: &'a mut usize,
    locals: Vec<Local>,
}

pub(super) fn derive(
    env: &Environment,
    classes: &BTreeSet<Name>,
    imported_classes: &BTreeMap<Name, imported::ClassParameters>,
    expected_class: Option<&Name>,
    declaration: &Name,
    remaining: &mut usize,
) -> std::result::Result<Option<DerivedIndex>, InstanceRegistryError> {
    let mut indexer = Indexer {
        env,
        classes,
        imported_classes,
        remaining,
        locals: Vec::new(),
    };
    match indexer.instance(expected_class, declaration) {
        Ok(result) => Ok(Some(result)),
        Err(Error::Unsupported) => Ok(None),
        Err(Error::Registry(error)) => Err(error),
    }
}

impl Indexer<'_> {
    fn tick(&mut self) -> Result<()> {
        tick(self.remaining).map_err(Error::from)
    }

    fn instance(
        &mut self,
        expected_class: Option<&Name>,
        declaration: &Name,
    ) -> Result<DerivedIndex> {
        self.tick()?;
        let info = self
            .env
            .find(declaration)
            .ok_or_else(|| InstanceRegistryError::UnknownDeclaration(declaration.clone()))?;
        let safe = match info {
            ConstantInfo::Defn(value) => value.safety == DefinitionSafety::Safe,
            ConstantInfo::Thm(_) => true,
            ConstantInfo::Opaque(value) => !value.is_unsafe,
            ConstantInfo::Axiom(value) => !value.is_unsafe,
            ConstantInfo::Ctor(value) => !value.is_unsafe,
            _ => false,
        };
        if !safe {
            return Err(InstanceRegistryError::InvalidInstance(declaration.clone()).into());
        }
        let mut target = info.constant_val().type_.clone();
        let definition_value = match info {
            ConstantInfo::Defn(definition) => Some(definition.value.clone()),
            _ => None,
        };
        if let Some(definition_value) = definition_value {
            // The native record builder closes a projection by wrapping its
            // Expr::Proj value in lambdas. Projection-function synthesis has a
            // special self-binder readiness rule; an ordinary schedule that
            // happens to succeed is not evidence that its order is the same.
            let mut value = &definition_value;
            loop {
                self.tick()?;
                match value.node() {
                    ExprNode::Lam { body, .. } => value = body,
                    ExprNode::MData { data, expr } if data.is_empty() => value = expr,
                    ExprNode::App { f, .. } => value = f,
                    ExprNode::Proj { .. } => return Err(Error::Unsupported),
                    _ => break,
                }
            }
        }
        loop {
            self.tick()?;
            match target.node() {
                ExprNode::ForallE {
                    binder_type,
                    binder_info,
                    body,
                    ..
                } => {
                    let id = FVarId(Name::num(
                        Name::from_components(["FrankenLean", "exportInstanceIndex"]),
                        self.locals.len() as u64,
                    ));
                    let argument = Expr::fvar(id.clone());
                    let body = body.clone();
                    self.locals.push(Local {
                        id,
                        type_: binder_type.clone(),
                        binder: *binder_info,
                    });
                    target = self.substitute(&body, &argument)?;
                }
                ExprNode::MData { data, expr } if data.is_empty() => target = expr.clone(),
                _ => break,
            }
        }
        let (class, _) = self.class_application(&target)?;
        if expected_class.is_some_and(|expected| expected != &class) {
            return Err(InstanceRegistryError::InvalidInstance(declaration.clone()).into());
        }
        let synth_order = self.synth_order(&target)?;
        let keys = self.path(&target)?;
        Ok(DerivedIndex { keys, synth_order })
    }

    // Meter the DAG before core capture-preserving substitution allocates it.
    fn walk(&mut self, root: &Expr) -> Result<()> {
        let mut todo = vec![root];
        let mut seen = HashSet::new();
        while let Some(expr) = todo.pop() {
            self.tick()?;
            if !seen.insert(expr.allocation_identity()) {
                continue;
            }
            match expr.node() {
                ExprNode::App { f, a } => todo.extend([f, a]),
                ExprNode::ForallE {
                    binder_type, body, ..
                }
                | ExprNode::Lam {
                    binder_type, body, ..
                } => todo.extend([binder_type, body]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => todo.extend([type_, value, body]),
                ExprNode::Proj { expr, .. } | ExprNode::MData { expr, .. } => todo.push(expr),
                _ => {}
            }
        }
        Ok(())
    }

    fn substitute(&mut self, body: &Expr, argument: &Expr) -> Result<Expr> {
        self.walk(body)?;
        body.subst_loose(0, std::slice::from_ref(argument))
            .map_err(|_| Error::Registry(InstanceRegistryError::Limit))
    }

    fn spine(&mut self, expr: &Expr) -> Result<(Expr, Vec<Expr>)> {
        let mut args = Vec::new();
        let mut head = expr;
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    args.push(a.clone());
                    head = f;
                }
                ExprNode::MData { data, expr } if data.is_empty() => head = expr,
                ExprNode::MData { .. } => return Err(Error::Unsupported),
                _ => {
                    args.reverse();
                    return Ok((head.clone(), args));
                }
            }
        }
    }

    fn class_application(&mut self, expr: &Expr) -> Result<(Name, Vec<Expr>)> {
        let (head, args) = self.spine(expr)?;
        let ExprNode::Const { name, .. } = head.node() else {
            return Err(Error::Unsupported);
        };
        if !self.classes.contains(name) {
            return Err(Error::Unsupported);
        }
        validate_class(self.env, name)?;
        Ok((name.clone(), args))
    }

    fn local_index(&self, id: &FVarId) -> Result<usize> {
        let LeafView::Num(index) = id.0.leaf_view() else {
            return Err(Error::Unsupported);
        };
        let index = usize::try_from(index).map_err(|_| Error::Unsupported)?;
        self.locals
            .get(index)
            .filter(|local| &local.id == id)
            .map(|_| index)
            .ok_or(Error::Unsupported)
    }

    fn dependencies(&mut self, root: &Expr) -> Result<BTreeSet<usize>> {
        let mut result = BTreeSet::new();
        let mut todo = vec![root];
        let mut seen = HashSet::new();
        while let Some(expr) = todo.pop() {
            self.tick()?;
            if !seen.insert(expr.allocation_identity()) {
                continue;
            }
            match expr.node() {
                ExprNode::FVar { id } => {
                    result.insert(self.local_index(id)?);
                }
                ExprNode::App { f, a } => todo.extend([f, a]),
                ExprNode::ForallE {
                    binder_type, body, ..
                }
                | ExprNode::Lam {
                    binder_type, body, ..
                } => todo.extend([binder_type, body]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => todo.extend([type_, value, body]),
                ExprNode::Proj { expr, .. } | ExprNode::MData { expr, .. } => todo.push(expr),
                ExprNode::MVar { .. } => return Err(Error::Unsupported),
                _ => {}
            }
        }
        Ok(result)
    }

    // The pin's assignMVarsAt also assigns variables in a variable's type.
    fn assign(&mut self, initial: BTreeSet<usize>, assigned: &mut BTreeSet<usize>) -> Result<()> {
        let mut todo: Vec<_> = initial.into_iter().collect();
        while let Some(index) = todo.pop() {
            self.tick()?;
            if assigned.insert(index) {
                let type_ = self.locals[index].type_.clone();
                todo.extend(self.dependencies(&type_)?);
            }
        }
        Ok(())
    }

    fn input_dependencies(&mut self, type_: &Expr) -> Result<BTreeSet<usize>> {
        let (class, args) = self.class_application(type_)?;
        let class_type = self
            .env
            .find(&class)
            .ok_or(Error::Unsupported)?
            .constant_val()
            .type_
            .clone();
        let mut domains = vec![&class_type];
        while let Some(expr) = domains.pop() {
            self.tick()?;
            match expr.node() {
                ExprNode::Const { name, .. }
                    if *name == Name::from_components(["semiOutParam"]) =>
                {
                    // Semi-output metadata has its own contract; never pretend
                    // that it is an ordinary input or an outParam.
                    return Err(Error::Unsupported);
                }
                ExprNode::App { f, a } => domains.extend([f, a]),
                ExprNode::ForallE {
                    binder_type, body, ..
                } => domains.extend([binder_type, body]),
                ExprNode::MData { expr, .. } => domains.push(expr),
                _ => {}
            }
        }
        let params = match self.imported_classes.get(&class) {
            Some(parameters) => {
                *self.remaining = self
                    .remaining
                    .checked_sub(parameters.out_params.len() + parameters.out_level_params.len())
                    .ok_or(InstanceRegistryError::Limit)?;
                parameters.clone()
            }
            None => parameters_with_budget(self.env, &class, self.remaining)?,
        };
        let mut outputs = BTreeSet::new();
        for index in params.out_params {
            self.tick()?;
            outputs.insert(index);
        }
        let mut input = BTreeSet::new();
        for (index, arg) in args.iter().enumerate() {
            self.tick()?;
            if !outputs.contains(&(index as u32)) {
                input.extend(self.dependencies(arg)?);
            }
        }
        Ok(input)
    }

    fn synth_order(&mut self, target: &Expr) -> Result<Vec<u32>> {
        // checkImpossibleInstance: every ordinary argument must be reachable
        // from the result or a prerequisite, transitively through their types.
        let mut possible = self.dependencies(target)?;
        possible.extend(self.locals.iter().enumerate().filter_map(|(index, local)| {
            (local.binder == BinderInfo::InstImplicit).then_some(index)
        }));
        let mut reachable = BTreeSet::new();
        self.assign(possible, &mut reachable)?;
        if reachable.len() != self.locals.len() {
            return Err(Error::Unsupported);
        }
        let mut assigned = BTreeSet::new();
        let input = self.input_dependencies(target)?;
        self.assign(input, &mut assigned)?;
        let mut pending: BTreeSet<_> = self
            .locals
            .iter()
            .enumerate()
            .filter_map(|(index, local)| {
                (local.binder == BinderInfo::InstImplicit).then_some(index)
            })
            .collect();
        let mut order = Vec::new();
        while !pending.is_empty() {
            self.tick()?;
            let mut ready = None;
            for &index in &pending {
                self.tick()?;
                let type_ = self.locals[index].type_.clone();
                if self.input_dependencies(&type_)?.is_subset(&assigned) {
                    ready = Some((index, type_));
                    break;
                }
            }
            let Some((index, type_)) = ready else {
                // No guessing of projection exceptions or option-disabled
                // fallback order when this direct-class schedule stalls.
                return Err(Error::Unsupported);
            };
            pending.remove(&index);
            let mut values = self.dependencies(&type_)?;
            values.insert(index);
            self.assign(values, &mut assigned)?;
            order.push(u32::try_from(index).map_err(|_| InstanceRegistryError::Limit)?);
        }
        if !self.dependencies(target)?.is_subset(&assigned) {
            return Err(Error::Unsupported);
        }
        Ok(order)
    }

    // Inference of admitted type fragments only, for the pin's ignoreArg.
    // This is metadata construction and makes no declaration-admission claim.
    fn infer(&mut self, expr: &Expr, depth: usize) -> Result<Expr> {
        self.tick()?;
        if depth >= 128 {
            return Err(Error::Unsupported);
        }
        match expr.node() {
            ExprNode::Sort { level } => Ok(Expr::sort(
                level
                    .clone()
                    .succ()
                    .map_err(|_| InstanceRegistryError::Limit)?,
            )),
            ExprNode::FVar { id } => Ok(self.locals[self.local_index(id)?].type_.clone()),
            ExprNode::Const { name, levels } => {
                let base = self
                    .env
                    .find(name)
                    .ok_or(Error::Unsupported)?
                    .constant_val();
                *self.remaining = self
                    .remaining
                    .checked_sub(base.level_params.len())
                    .ok_or(InstanceRegistryError::Limit)?;
                let type_ = base.type_.clone();
                let parameters = base.level_params.clone();
                crate::universe::parameters::instantiate(
                    || tick(self.remaining).map_err(Error::from),
                    || Error::Unsupported,
                    &type_,
                    &parameters,
                    levels,
                )
            }
            ExprNode::App { f, a } => {
                let type_ = self.infer(f, depth + 1)?;
                let ExprNode::ForallE { body, .. } = type_.node() else {
                    return Err(Error::Unsupported);
                };
                self.substitute(body, a)
            }
            ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } => {
                let domain_sort = self.infer(binder_type, depth + 1)?;
                let ExprNode::Sort {
                    level: domain_level,
                } = domain_sort.node()
                else {
                    return Err(Error::Unsupported);
                };
                let id = FVarId(Name::num(
                    Name::from_components(["FrankenLean", "exportInstanceIndex"]),
                    self.locals.len() as u64,
                ));
                let opened = self.substitute(body, &Expr::fvar(id.clone()))?;
                self.locals.push(Local {
                    id,
                    type_: binder_type.clone(),
                    binder: *binder_info,
                });
                let range_sort = self.infer(&opened, depth + 1);
                self.locals.pop();
                let range_sort = range_sort?;
                let ExprNode::Sort { level: range_level } = range_sort.node() else {
                    return Err(Error::Unsupported);
                };
                Ok(Expr::sort(
                    fln_core::level::Level::try_kernel_imax(
                        domain_level.clone(),
                        range_level.clone(),
                    )
                    .map_err(|_| InstanceRegistryError::Limit)?,
                ))
            }
            ExprNode::Lit { literal } => Ok(Expr::const_(
                Name::from_components([match literal {
                    Literal::Nat(_) => "Nat",
                    Literal::Str(_) => "String",
                }]),
                Vec::new(),
            )),
            ExprNode::MData { data, expr } if data.is_empty() => self.infer(expr, depth + 1),
            _ => Err(Error::Unsupported),
        }
    }

    fn ignored_arguments(&mut self, head: &Expr, args: &[Expr]) -> Result<Vec<bool>> {
        let mut type_ = self.infer(head, 0)?;
        let mut ignored = Vec::with_capacity(args.len());
        for arg in args {
            self.tick()?;
            let ExprNode::ForallE {
                binder_type,
                binder_info,
                body,
                ..
            } = type_.node()
            else {
                return Err(Error::Unsupported);
            };
            let binder = *binder_info;
            let body = body.clone();
            let mut instance = false;
            if binder != BinderInfo::Default {
                let (domain, _) = self.spine(binder_type)?;
                match domain.node() {
                    ExprNode::Const { name, .. } => {
                        if matches!(self.env.find(name), Some(ConstantInfo::Defn(_))) {
                            return Err(Error::Unsupported);
                        }
                        instance = self.classes.contains(name);
                    }
                    ExprNode::Sort { .. } | ExprNode::FVar { .. } | ExprNode::BVar { .. } => {}
                    _ => return Err(Error::Unsupported),
                }
            }
            let ignore = if instance {
                true
            } else {
                let arg_type = self.infer(arg, 0)?;
                if matches!(binder, BinderInfo::Implicit | BinderInfo::StrictImplicit) {
                    match arg_type.node() {
                        ExprNode::Sort { .. } => false,
                        ExprNode::Const { name, .. }
                            if matches!(self.env.find(name), Some(ConstantInfo::Defn(_))) =>
                        {
                            return Err(Error::Unsupported);
                        }
                        ExprNode::App { .. } | ExprNode::LetE { .. } | ExprNode::MData { .. } => {
                            return Err(Error::Unsupported);
                        }
                        _ => true,
                    }
                } else if matches!(arg_type.node(), ExprNode::Sort { .. }) {
                    false
                } else {
                    let sort = self.infer(&arg_type, 0)?;
                    let ExprNode::Sort { level } = sort.node() else {
                        return Err(Error::Unsupported);
                    };
                    level.is_zero()
                }
            };
            ignored.push(ignore);
            // FunInfo classifies the original telescope opened with fresh
            // variables, not with the actual earlier application arguments.
            // Keeping its bound-variable spine prevents an actual class type
            // from turning a polymorphic implicit parameter into an instance.
            type_ = body;
        }
        Ok(ignored)
    }

    fn path(&mut self, target: &Expr) -> Result<Vec<discr_tree::Key>> {
        use discr_tree::Key;
        let mut keys = Vec::new();
        let mut todo = vec![(Some(target.clone()), true)];
        while let Some((expr, root)) = todo.pop() {
            self.tick()?;
            let Some(expr) = expr else {
                keys.push(Key::Star);
                continue;
            };
            let (head, args) = self.spine(&expr)?;
            let arity = u32::try_from(args.len()).map_err(|_| InstanceRegistryError::Limit)?;
            let key = match head.node() {
                ExprNode::FVar { id } => {
                    self.local_index(id)?;
                    Key::Star
                }
                ExprNode::Sort { .. } if args.is_empty() => Key::Other,
                ExprNode::Lit { literal } if args.is_empty() => Key::Lit(literal.clone()),
                ExprNode::ForallE { binder_type, .. } if args.is_empty() => {
                    todo.push((Some(binder_type.clone()), false));
                    Key::Arrow
                }
                ExprNode::Const { name, .. } => {
                    // These constructors become a numeral or offset Star in
                    // the pin, never the naive nested constructor keys.
                    if !root
                        && (*name == Name::from_components(["Nat", "zero"])
                            || *name == Name::from_components(["Nat", "succ"]))
                    {
                        return Err(Error::Unsupported);
                    }
                    match self.env.find(name) {
                        Some(ConstantInfo::Axiom(value)) if !value.is_unsafe => {}
                        Some(ConstantInfo::Induct(value)) if !value.is_unsafe => {}
                        Some(ConstantInfo::Ctor(value)) if !value.is_unsafe => {}
                        _ => return Err(Error::Unsupported),
                    }
                    let ignored = self.ignored_arguments(&head, &args)?;
                    for (arg, ignore) in args.into_iter().zip(ignored).rev() {
                        todo.push(((!ignore).then_some(arg), false));
                    }
                    Key::Const(name.clone(), arity)
                }
                _ => return Err(Error::Unsupported),
            };
            keys.push(key);
        }
        Ok(keys)
    }
}
