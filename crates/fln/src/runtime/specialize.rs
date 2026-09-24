//! Post-admission monomorphization of type arguments and concrete dictionaries.
//!
//! Derived names never enter the logical environment. Dictionary selection is
//! permitted only for closed constructor values with inert fields, and runtime
//! beta reduction introduces strict lets: it never duplicates or drops an
//! action. Both the original theorem checking and FIR validation remain intact.
mod scope;

use super::*;
use fln_core::level::Level;
use fln_env::constants::DefinitionSafety;
use std::collections::HashMap;

#[derive(Default)]
pub(super) struct Store {
    definitions: BTreeMap<Name, DefinitionVal>,
    instances: HashMap<(Name, Vec<Level>, Vec<Expr>), Name>,
    types: HashMap<Expr, Expr>,
    constructor_types: HashMap<Name, Expr>,
}
fn closed(expr: &Expr) -> bool {
    !expr.has_loose_bvars()
        && !expr.has_fvar()
        && !expr.has_expr_mvar()
        && !expr.has_level_mvar()
        && !expr.has_level_param()
}
fn application(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}
impl Preparation<'_> {
    pub(super) fn forget_constructor_type(&mut self, name: &Name) {
        self.specializations.constructor_types.remove(name);
    }

    pub(super) fn remember_constructor_type(
        &mut self,
        name: Name,
        type_: Expr,
    ) -> Result<(), IngressError> {
        self.specializations
            .constructor_types
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: self
                    .specializations
                    .constructor_types
                    .len()
                    .saturating_add(1),
            })?;
        self.specializations.constructor_types.insert(name, type_);
        Ok(())
    }
    pub(crate) fn specialized_definition(&self, name: &Name) -> Option<DefinitionVal> {
        self.specializations.definitions.get(name).cloned()
    }
    fn definition(&self, name: &Name) -> Option<DefinitionVal> {
        match self.environment.find(name) {
            Some(ConstantInfo::Defn(definition)) if definition.safety == DefinitionSafety::Safe => {
                Some(definition.clone())
            }
            _ => self.specialized_definition(name),
        }
    }
    pub(super) fn universe_instance(
        &mut self,
        source: &Expr,
        params: &[Name],
        levels: &[Level],
    ) -> Result<Expr, IngressError> {
        fln_elab::universe::parameters::instantiate(
            || self.tick(),
            || unsupported("runtime universe substitution"),
            source,
            params,
            levels,
        )
    }
    pub(super) fn substitution(&mut self, body: &Expr, value: &Expr) -> Result<Expr, IngressError> {
        scope::charge(self, body, scope::Operation::Substitute(value))?;
        body.subst_loose(0, std::slice::from_ref(value))
            .map_err(|_| unsupported("runtime substitution scope"))
    }
    pub(super) fn lift(&mut self, expr: &Expr, amount: u32) -> Result<Expr, IngressError> {
        scope::charge(self, expr, scope::Operation::Lift(amount))?;
        expr.lift_loose(0, amount)
            .map_err(|_| unsupported("runtime specialization scope"))
    }
    pub(super) fn type_head(&mut self, source: &Expr) -> Result<Expr, IngressError> {
        let (mut head, mut args) = self.spine(source)?;
        args.reverse();
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    reserve(&mut args, self.limits.max_application_args)?;
                    args.push(a.clone());
                    head = f.clone();
                }
                ExprNode::MData { expr, .. } => head = expr.clone(),
                ExprNode::LetE { body, value, .. } => head = self.substitution(body, value)?,
                ExprNode::Lam { body, .. } if !args.is_empty() => {
                    head = self.substitution(body, &args.pop().expect("type argument"))?
                }
                ExprNode::Const { name, levels } => {
                    let Some(definition) = self.definition(name) else {
                        break;
                    };
                    if definition.base.level_params.len() != levels.len() {
                        break;
                    }
                    head = self.universe_instance(
                        &definition.value,
                        &definition.base.level_params,
                        levels,
                    )?;
                }
                _ => break,
            }
        }
        Ok(application(head, args.into_iter().rev()))
    }
    pub(super) fn type_parameter(&mut self, type_: &Expr) -> Result<bool, IngressError> {
        let mut type_ = self.type_head(type_)?;
        loop {
            self.tick()?;
            match type_.node() {
                ExprNode::Sort { .. } => return Ok(true),
                ExprNode::ForallE { body, .. } => type_ = self.type_head(body)?,
                _ => return Ok(false),
            }
        }
    }
    /// Normalize only type expressions; executable values do not pass through
    /// this delta/beta/zeta reducer. The memo table owns its expression keys.
    pub(crate) fn normalize_type(&mut self, input: &Expr) -> Result<Expr, IngressError> {
        enum Work {
            Enter(Expr),
            Finish(Expr, Expr),
        }
        let mut work = vec![Work::Enter(input.clone())];
        while let Some(item) = work.pop() {
            self.tick()?;
            match item {
                Work::Enter(source) => {
                    if self.specializations.types.contains_key(&source) {
                        continue;
                    }
                    let head = self.type_head(&source)?;
                    reserve(&mut work, self.limits.max_nodes)?;
                    work.push(Work::Finish(source, head.clone()));
                    let mut push = |child: &Expr| -> Result<(), IngressError> {
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Enter(child.clone()));
                        Ok(())
                    };
                    match head.node() {
                        ExprNode::App { f, a } => {
                            push(a)?;
                            push(f)?;
                        }
                        ExprNode::Lam {
                            binder_type, body, ..
                        }
                        | ExprNode::ForallE {
                            binder_type, body, ..
                        } => {
                            push(body)?;
                            push(binder_type)?;
                        }
                        _ => {}
                    }
                }
                Work::Finish(source, head) => {
                    let child = |expr: &Expr| {
                        self.specializations
                            .types
                            .get(expr)
                            .cloned()
                            .ok_or_else(|| unsupported("runtime type postorder"))
                    };
                    let value = match head.node() {
                        ExprNode::App { f, a } => Expr::app(child(f)?, child(a)?),
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => Expr::lam(
                            binder_name.clone(),
                            child(binder_type)?,
                            child(body)?,
                            *binder_info,
                        ),
                        ExprNode::ForallE {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => Expr::forall_e(
                            binder_name.clone(),
                            child(binder_type)?,
                            child(body)?,
                            *binder_info,
                        ),
                        _ => head,
                    };
                    self.specializations.types.try_reserve(1).map_err(|_| {
                        IngressError::AllocationFailure {
                            resource: IngressResource::Nodes,
                            requested: self.specializations.types.len() + 1,
                        }
                    })?;
                    self.specializations.types.insert(source, value);
                }
            }
        }
        self.specializations
            .types
            .get(input)
            .cloned()
            .ok_or_else(|| unsupported("runtime type result"))
    }
    pub(super) fn normalize_definition_signature(
        &mut self,
        definition: &DefinitionVal,
    ) -> Result<DefinitionVal, IngressError> {
        let mut result = definition.clone();
        result.base.type_ = self.erase_runtime_type(&definition.base.type_)?;
        let mut body = self.erase_proofs(&definition.value, Some(definition.base.type_.clone()))?;
        let mut binders = Vec::new();
        while let ExprNode::Lam {
            binder_name,
            binder_type,
            body: inner,
            binder_info,
        } = body.node()
        {
            self.tick()?;
            let depth = binders.len().saturating_add(1);
            if depth > self.limits.max_context_depth {
                return Err(IngressError::ResourceLimit {
                    resource: IngressResource::ContextDepth,
                    limit: self.limits.max_context_depth,
                    observed: depth,
                });
            }
            reserve(&mut binders, self.limits.max_context_depth)?;
            binders.push((
                binder_name.clone(),
                self.normalize_type(binder_type)?,
                *binder_info,
            ));
            body = inner.clone();
        }
        for (name, type_, info) in binders.into_iter().rev() {
            body = Expr::lam(name, type_, body, info);
        }
        result.value = self.lower_projections(&body)?;
        Ok(result)
    }
    /// Recognize inert closed values without running arbitrary functions.
    /// Lambda bodies are not evaluated. Every constructor field must be inert,
    /// including fields a projection would otherwise discard.
    fn static_value(&mut self, input: &Expr) -> Result<bool, IngressError> {
        if !closed(input) {
            return Ok(false);
        }
        let mut work = vec![input.clone()];
        while let Some(expr) = work.pop() {
            self.tick()?;
            let (head, args) = self.spine(&expr)?;
            match head.node() {
                ExprNode::Lam { .. }
                | ExprNode::ForallE { .. }
                | ExprNode::Sort { .. }
                | ExprNode::Lit { .. }
                    if args.is_empty() => {}
                ExprNode::Const { name, levels } => match self.environment.find(name) {
                    Some(ConstantInfo::Ctor(ctor))
                        if !ctor.is_unsafe
                            && args.len()
                                == ctor.num_params as usize + ctor.num_fields as usize =>
                    {
                        for field in args.into_iter().skip(ctor.num_params as usize) {
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(field);
                        }
                    }
                    Some(ConstantInfo::Induct(_)) => {} // checked type value
                    Some(ConstantInfo::Defn(definition))
                        if args.is_empty()
                            && definition.safety == DefinitionSafety::Safe
                            && definition.base.level_params.len() == levels.len() =>
                    {
                        let value = self.universe_instance(
                            &definition.value,
                            &definition.base.level_params,
                            levels,
                        )?;
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(value);
                    }
                    _ => return Ok(false),
                },
                _ => return Ok(false),
            }
        }
        Ok(true)
    }
    pub(super) fn static_projection(
        &mut self,
        family: &Name,
        index: u64,
        value: &Expr,
    ) -> Result<Option<Expr>, IngressError> {
        if !self.static_value(value)? {
            return Ok(None);
        }
        let mut value = value.clone();
        loop {
            self.tick()?;
            let (head, args) = self.spine(&value)?;
            let ExprNode::Const { name, levels } = head.node() else {
                return Ok(None);
            };
            match self.environment.find(name) {
                Some(ConstantInfo::Ctor(ctor))
                    if !ctor.is_unsafe
                        && ctor.induct == *family
                        && args.len() == ctor.num_params as usize + ctor.num_fields as usize =>
                {
                    let Ok(index) = usize::try_from(index) else {
                        return Ok(None);
                    };
                    if index >= ctor.num_fields as usize {
                        return Ok(None);
                    }
                    return Ok(Some(args[ctor.num_params as usize + index].clone()));
                }
                Some(ConstantInfo::Defn(definition))
                    if args.is_empty() && definition.safety == DefinitionSafety::Safe =>
                {
                    value = self.universe_instance(
                        &definition.value,
                        &definition.base.level_params,
                        levels,
                    )?
                }
                _ => return Ok(None),
            }
        }
    }
    fn static_head(&mut self, input: &Expr) -> Result<Expr, IngressError> {
        let mut value = input.clone();
        loop {
            self.tick()?;
            match value.node() {
                ExprNode::MData { expr, .. } => value = expr.clone(),
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => {
                    let Some(field) = self.static_projection(struct_name, *idx, expr)? else {
                        break;
                    };
                    value = field;
                }
                ExprNode::Const { name, levels } => {
                    if !self.static_value(&value)? {
                        break;
                    }
                    let Some(definition) = self.definition(name) else {
                        break;
                    };
                    value = self.universe_instance(
                        &definition.value,
                        &definition.base.level_params,
                        levels,
                    )?;
                }
                _ => break,
            }
        }
        Ok(value)
    }
    /// Consume a prefix of erased type arguments and inert instance arguments.
    /// Remaining arguments stay in the runtime call. A cache permits ordinary
    /// recursion and shares each concrete body across all its call sites.
    pub(super) fn specialize_call(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const {
            name: original,
            levels,
        } = head.node()
        else {
            return Ok(None);
        };
        if self.specializations.definitions.contains_key(original) {
            return Ok(None);
        }
        let Some(mut definition) = self.definition(original) else {
            return Ok(None);
        };
        if definition.base.level_params.len() != levels.len()
            || levels.iter().any(|l| l.has_mvar() || l.has_param())
        {
            return Ok(None);
        }
        let mut type_ = self.universe_instance(
            &definition.base.type_,
            &definition.base.level_params,
            levels,
        )?;
        let mut value =
            self.universe_instance(&definition.value, &definition.base.level_params, levels)?;
        let mut consumed = 0;
        for argument in args {
            self.tick()?;
            let domain = self.type_head(&type_)?;
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = domain.node()
            else {
                break;
            };
            if !closed(argument) {
                break;
            }
            if !self.type_parameter(binder_type)?
                && (*binder_info != BinderInfo::InstImplicit || !self.static_value(argument)?)
            {
                break;
            }
            // The source's lambda telescope must actually bind this argument.
            // No eta or callback invocation is used to invent an erased body.
            value = self.static_head(&value)?;
            let ExprNode::Lam {
                body: body_value, ..
            } = value.node()
            else {
                break;
            };
            value = self.substitution(body_value, argument)?;
            type_ = self.substitution(body, argument)?;
            consumed += 1;
        }
        if consumed == 0 && levels.is_empty() {
            return Ok(None);
        }
        let key = (original.clone(), levels.clone(), args[..consumed].to_vec());
        let name = if let Some(name) = self.specializations.instances.get(&key) {
            name.clone()
        } else {
            let count = self.specializations.definitions.len();
            if count >= self.limits.fir.max_functions {
                return Err(IngressError::ResourceLimit {
                    resource: IngressResource::ProgramTables,
                    limit: self.limits.fir.max_functions,
                    observed: count.saturating_add(1),
                });
            }
            let serial =
                u64::try_from(count).map_err(|_| unsupported("specialization identity"))?;
            let name = Name::num(
                Name::from_components(["_fln_runtime_specialization"]),
                serial,
            );
            if self.environment.contains(&name) {
                return Err(unsupported("runtime specialization name collision"));
            }
            definition.base.name = name.clone();
            definition.base.level_params.clear();
            definition.base.type_ = type_;
            definition.value = value;
            definition.all.clear();
            self.specializations.instances.try_reserve(1).map_err(|_| {
                IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: count.saturating_add(1),
                }
            })?;
            self.specializations.instances.insert(key, name.clone());
            self.specializations
                .definitions
                .insert(name.clone(), definition);
            name
        };
        Ok(Some(application(
            Expr::const_(name, vec![]),
            args[consumed..].iter().cloned(),
        )))
    }
    /// Expose a concrete dictionary field and eliminate its type lambdas. For
    /// runtime lambdas, retain strict evaluation and sharing with a let binder.
    pub(super) fn static_apply(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        if args.is_empty() {
            return Ok(None);
        }
        // A let in function position must finish its strict initializer before
        // evaluating any application argument. Reassociate without substituting
        // the initializer, preserving sharing and exposing literal lambda tails.
        if let ExprNode::LetE {
            decl_name,
            type_,
            value,
            body,
            non_dep,
        } = head.node()
        {
            let mut lifted = Vec::new();
            for argument in args {
                reserve(&mut lifted, self.limits.max_application_args)?;
                lifted.push(self.lift(argument, 1)?);
            }
            return Ok(Some(Expr::let_e(
                decl_name.clone(),
                type_.clone(),
                value.clone(),
                application(body.clone(), lifted),
                *non_dep,
            )));
        }
        let original = head.clone();
        let mut head = head.clone();
        if let ExprNode::Proj {
            struct_name,
            idx,
            expr,
        } = head.node()
        {
            let Some(field) = self.static_projection(struct_name, *idx, expr)? else {
                return Ok(None);
            };
            head = field;
        }
        let mut consumed = 0;
        loop {
            self.tick()?;
            let ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                ..
            } = head.node()
            else {
                break;
            };
            let Some(argument) = args.get(consumed) else {
                break;
            };
            // Constructing a syntactic lambda executes none of its body. It
            // can be substituted capture-avoidantly without duplicating or
            // dropping an action. This also exposes mutual-match minor
            // premises hidden behind the elaborator's local helper lambdas.
            // A call that *returns* a function must still use the strict let.
            if matches!(argument.node(), ExprNode::Lam { .. })
                || self.type_parameter(binder_type)? && closed(argument)
            {
                head = self.substitution(body, argument)?;
                consumed += 1;
                continue;
            }
            let mut remaining = Vec::new();
            for argument in &args[consumed + 1..] {
                reserve(&mut remaining, self.limits.max_application_args)?;
                remaining.push(self.lift(argument, 1)?);
            }
            return Ok(Some(Expr::let_e(
                binder_name.clone(),
                self.normalize_type(binder_type)?,
                argument.clone(),
                application(body.clone(), remaining),
                false,
            )));
        }
        if consumed == 0 && head == original {
            return Ok(None);
        }
        Ok(Some(application(head, args[consumed..].iter().cloned())))
    }
    /// Only admitted executable entries can become callable values. A familiar
    /// axiom name is insufficient: intrinsics require the exact seed contract.
    /// Ground constructors use the same telescope that produced their layout.
    pub(super) fn callable_type(&mut self, head: &Expr) -> Result<Option<Expr>, IngressError> {
        self.original_callable_type(head)?
            .map(|type_| self.erase_runtime_type(&type_))
            .transpose()
    }

    fn original_callable_type(&mut self, head: &Expr) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        self.tick()?;
        if let Some(definition) = self.definition(name) {
            return self
                .universe_instance(
                    &definition.base.type_,
                    &definition.base.level_params,
                    levels,
                )
                .map(Some);
        }
        if !levels.is_empty() {
            return Ok(None);
        }
        if let Some(type_) = self.specializations.constructor_types.get(name) {
            return Ok(Some(type_.clone()));
        }
        if source_intrinsic_binding(self.environment, name).is_some() {
            return Ok(self
                .environment
                .find(name)
                .map(|info| info.constant_val().type_.clone()));
        }
        if let Some(ConstantInfo::Ctor(constructor)) = self.environment.find(name) {
            if name == &super::name("Nat.succ") {
                self.check_nat_family()?;
                return Ok(Some(constructor.base.type_.clone()));
            }
            let family = Expr::const_(constructor.induct.clone(), vec![]);
            self.value_type(&family)?;
            return Ok(self.specializations.constructor_types.get(name).cloned());
        }
        Ok(None)
    }

    /// Global partial applications retain supplied arguments in strict lets and
    /// return a closure over them. The inner call is saturated; neither the
    /// function nor an argument is executed during this transformation.
    pub(super) fn partial_call(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let Some(mut type_) = self.callable_type(head)? else {
            return Ok(None);
        };
        let mut supplied = Vec::new();
        for argument in args {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                ..
            } = normal.node()
            else {
                return Ok(None);
            };
            let domain = self.normalize_type(binder_type)?;
            if self.value_type(&domain)?.is_none() {
                return Ok(None);
            }
            reserve(&mut supplied, self.limits.max_context_depth)?;
            supplied.push((binder_name.clone(), domain, argument.clone()));
            type_ = self.substitution(body, argument)?;
        }
        let remaining_type = self.normalize_type(&type_)?;
        if !matches!(remaining_type.node(), ExprNode::ForallE { .. }) {
            return Ok(None);
        }
        if self.value_type(&remaining_type)?.is_none() {
            return Ok(None);
        }
        let mut remaining = Vec::new();
        let mut type_ = &remaining_type;
        while let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = type_.node()
        {
            self.tick()?;
            // Runtime interfaces are nondependent; an index may not become a
            // guessed field or a callback type when the binder is erased.
            if body.has_loose_bvars() {
                return Ok(None);
            }
            reserve(&mut remaining, self.limits.max_context_depth)?;
            remaining.push((binder_name.clone(), binder_type.clone(), *binder_info));
            type_ = body;
        }
        let depth =
            u32::try_from(supplied.len()).map_err(|_| unsupported("partial application depth"))?;
        let total = supplied
            .len()
            .checked_add(remaining.len())
            .ok_or_else(|| unsupported("partial application depth"))?;
        let mut value = head.clone();
        for index in (0..total).rev() {
            self.tick()?;
            value = Expr::app(
                value,
                Expr::bvar(
                    u32::try_from(index).map_err(|_| unsupported("partial application index"))?,
                )
                .map_err(|_| unsupported("partial application index"))?,
            );
        }
        for (index, (name, domain, info)) in remaining.into_iter().enumerate().rev() {
            let offset = depth
                .checked_add(
                    u32::try_from(index).map_err(|_| unsupported("partial application depth"))?,
                )
                .ok_or_else(|| unsupported("partial application depth"))?;
            value = Expr::lam(name, self.lift(&domain, offset)?, value, info);
        }
        let mut result = Expr::let_e(
            Name::anonymous(),
            self.lift(&remaining_type, depth)?,
            value,
            Expr::bvar(0).map_err(|_| unsupported("partial result"))?,
            false,
        );
        for (index, (name, domain, argument)) in supplied.into_iter().enumerate().rev() {
            let offset =
                u32::try_from(index).map_err(|_| unsupported("partial application depth"))?;
            result = Expr::let_e(
                name,
                self.lift(&domain, offset)?,
                self.lift(&argument, offset)?,
                result,
                false,
            );
        }
        Ok(Some(result))
    }
    /// Give literal callback arguments a checked type by sharing all arguments
    /// in left-to-right lets. The ordinary closure converter then derives their
    /// interfaces, captures and ownership; no body is executed to infer a type.
    pub(super) fn annotate_call(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        if !args
            .iter()
            .any(|a| matches!(a.node(), ExprNode::Lam { .. }))
        {
            return Ok(None);
        }
        let Some(mut type_) = self.callable_type(head)? else {
            return Ok(None);
        };
        let mut bindings = Vec::new();
        for argument in args {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                ..
            } = normal.node()
            else {
                return Ok(None);
            };
            reserve(&mut bindings, self.limits.max_context_depth)?;
            bindings.push((
                binder_name.clone(),
                self.normalize_type(binder_type)?,
                argument.clone(),
            ));
            type_ = self.substitution(body, argument)?;
        }
        let mut result = head.clone();
        for index in (0..bindings.len()).rev() {
            result = Expr::app(
                result,
                Expr::bvar(
                    u32::try_from(index).map_err(|_| unsupported("runtime callback scope"))?,
                )
                .map_err(|_| unsupported("runtime callback scope"))?,
            );
        }
        for (index, (name, type_, argument)) in bindings.into_iter().enumerate().rev() {
            let depth = u32::try_from(index).map_err(|_| unsupported("runtime callback depth"))?;
            result = Expr::let_e(
                name,
                self.lift(&type_, depth)?,
                self.lift(&argument, depth)?,
                result,
                false,
            );
        }
        Ok(Some(result))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn first_class_intrinsics_require_the_exact_admitted_seed_contract() {
        let name = name("Nat.sub");
        let Declaration::Axiom(mut axiom) =
            fln_elab::seed::source_intrinsic_seed_declaration(&name).unwrap()
        else {
            panic!("intrinsic axiom");
        };
        // Imported metadata alone is untrusted. A familiar name with a
        // different telescope cannot gain code merely by becoming a callback.
        axiom.base.type_ = Expr::forall_e(
            Name::anonymous(),
            Expr::const_(super::name("String"), vec![]),
            Expr::const_(super::name("Nat"), vec![]),
            BinderInfo::Default,
        );
        let environment = Environment::new()
            .add_decl(ConstantInfo::Axiom(axiom))
            .unwrap();
        let head = Expr::const_(name, vec![]);
        assert!(
            Preparation::new(&environment, IngressLimits::default())
                .partial_call(&head, &[])
                .unwrap()
                .is_none()
        );
        assert!(
            Preparation::new(&Environment::new(), IngressLimits::default())
                .partial_call(&head, &[])
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn private_constructor_callback_names_do_not_create_layout_authority() {
        let environment = Environment::new();
        let name = Name::num(Name::num(super::name("_fln_runtime_data"), 0), 1);
        assert!(
            Preparation::new(&environment, IngressLimits::default())
                .partial_call(&Expr::const_(name, vec![]), &[])
                .unwrap()
                .is_none()
        );
        assert!(
            Preparation::new(&environment, IngressLimits::default())
                .partial_call(&Expr::const_(super::name("Nat.succ"), vec![]), &[])
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn deeply_nested_type_normalization_uses_heap_frames_and_a_real_work_limit() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let scalar = Expr::const_(name("Nat"), vec![]);
                let mut type_ = scalar.clone();
                for _ in 0..600 {
                    type_ = Expr::forall_e(
                        Name::anonymous(),
                        scalar.clone(),
                        type_,
                        BinderInfo::Default,
                    );
                }
                let environment = Environment::new();
                let mut limits = IngressLimits {
                    max_nodes: 20_000,
                    ..IngressLimits::default()
                };
                let mut preparation = Preparation::new(&environment, limits);
                assert_eq!(preparation.normalize_type(&type_).unwrap(), type_);
                limits.max_nodes = 10;
                assert!(matches!(
                    Preparation::new(&environment, limits).normalize_type(&type_),
                    Err(IngressError::ResourceLimit {
                        resource: IngressResource::Nodes,
                        ..
                    })
                ));
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn expanding_substitutions_are_charged_before_calling_core_substitution() {
        let scalar = Expr::const_(name("Nat"), vec![]);
        let mut replacement = scalar.clone();
        for _ in 0..30 {
            replacement = Expr::app(replacement, scalar.clone());
        }
        let mut body = Expr::bvar(0).unwrap();
        for _ in 0..30 {
            body = Expr::app(body, Expr::bvar(0).unwrap());
        }
        let environment = Environment::new();
        let limits = IngressLimits {
            max_nodes: 200,
            ..IngressLimits::default()
        };
        // A closed replacement at depth zero is cloned, not copied into a new
        // tree per occurrence. Keep this original fixture as the positive
        // control: its former product-of-tree-sizes rejection was spurious.
        let mut expected = replacement.clone();
        for _ in 0..30 {
            expected = Expr::app(expected, replacement.clone());
        }
        assert_eq!(
            Preparation::new(&environment, limits)
                .substitution(&body, &replacement)
                .unwrap(),
            expected
        );
        // An open replacement under a binder genuinely must be lifted. Its
        // work is still charged before invoking the core transform.
        let mut open = Expr::bvar(0).unwrap();
        for _ in 0..30 {
            open = Expr::app(open, scalar.clone());
        }
        let under_binder = Expr::lam(
            Name::anonymous(),
            scalar,
            body.lift_loose(0, 1).unwrap(),
            BinderInfo::Default,
        );
        assert!(matches!(
            Preparation::new(&environment, limits).substitution(&under_binder, &open),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                ..
            })
        ));
    }
}
