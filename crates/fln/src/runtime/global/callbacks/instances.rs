//! Expose a checked dictionary without treating its computations as metadata.
//! Ordinary operands remain typed runtime lets. The constructor and its generic
//! method literals are substituted only in the current consumer's scope.
use super::*;

pub(super) struct InstancePrefix {
    pub(super) bindings: Vec<Binder>,
    pub(super) value: Expr,
}

struct Scoped {
    value: Expr,
    depth: usize,
}

impl Scoped {
    fn new(value: Expr, depth: usize) -> Self {
        Self { value, depth }
    }

    fn reopen(
        &self,
        preparation: &mut Preparation<'_>,
        depth: usize,
    ) -> Result<Expr, IngressError> {
        let added = depth
            .checked_sub(self.depth)
            .ok_or_else(|| unsupported("instance prefix scope"))?;
        if added == 0 {
            return Ok(self.value.clone());
        }
        let added = preparation.producer_depth(added)?;
        preparation.lift(&self.value, added)
    }
}

enum Work {
    Value(Scoped, Option<Scoped>),
    Apply(Scoped),
    Substitute(Scoped),
    Constructor(Scoped),
    Projection(Name, u64),
}

fn push(work: &mut Vec<Work>, task: Work, limit: usize) -> Result<(), IngressError> {
    reserve(work, limit)?;
    work.push(task);
    Ok(())
}

impl Preparation<'_> {
    /// This is a local compiler transform, not the inert factory evaluator.
    /// Every new binding denotes one original operand, in evaluation order;
    /// pending syntax remembers its scope before those bindings were added.
    /// A dynamic generic producer still has no executable representation.
    pub(super) fn residual_instance_constructor(
        &mut self,
        input: &Expr,
    ) -> Result<Option<InstancePrefix>, IngressError> {
        let mut work = vec![Work::Value(Scoped::new(input.clone(), 0), None)];
        let mut values: Vec<Scoped> = Vec::new();
        let mut bindings = Vec::new();
        while let Some(task) = work.pop() {
            self.tick()?;
            let depth = bindings.len();
            match task {
                Work::Value(source, expected) => {
                    let source = source.reopen(self, depth)?;
                    if let Some(value) = self.scoped_instance_factory_value(&source)? {
                        reserve(&mut values, self.limits.max_nodes)?;
                        values.push(Scoped::new(value, depth));
                        continue;
                    }
                    if let Some(expected) = expected {
                        let domain = expected.reopen(self, depth)?;
                        // Never execute a type argument or guess a generic
                        // closure interface. Representable computations keep
                        // their original checked annotation and runtime body.
                        if !self.type_parameter(&domain)? && self.value_type(&domain)?.is_some() {
                            self.producer_depth(depth.saturating_add(1))?;
                            reserve(&mut bindings, self.limits.max_context_depth)?;
                            bindings.push(Binder {
                                name: Name::anonymous(),
                                domain,
                                value: source,
                            });
                            reserve(&mut values, self.limits.max_nodes)?;
                            values.push(Scoped::new(variable(0)?, bindings.len()));
                            continue;
                        }
                    }
                    match source.node() {
                        ExprNode::MData { expr, .. } => push(
                            &mut work,
                            Work::Value(Scoped::new(expr.clone(), depth), None),
                            self.limits.max_nodes,
                        )?,
                        ExprNode::App { f, a } => {
                            push(
                                &mut work,
                                Work::Apply(Scoped::new(a.clone(), depth)),
                                self.limits.max_nodes,
                            )?;
                            push(
                                &mut work,
                                Work::Value(Scoped::new(f.clone(), depth), None),
                                self.limits.max_nodes,
                            )?;
                        }
                        ExprNode::LetE {
                            decl_name,
                            type_,
                            value,
                            body,
                            ..
                        } => {
                            // Keep the placeholder binder while later prefix
                            // slots lift its outer captures. Substitution then
                            // removes only this original administrative slot.
                            let template = Expr::lam(
                                decl_name.clone(),
                                type_.clone(),
                                body.clone(),
                                BinderInfo::Default,
                            );
                            push(
                                &mut work,
                                Work::Substitute(Scoped::new(template, depth)),
                                self.limits.max_nodes,
                            )?;
                            push(
                                &mut work,
                                Work::Value(
                                    Scoped::new(value.clone(), depth),
                                    Some(Scoped::new(type_.clone(), depth)),
                                ),
                                self.limits.max_nodes,
                            )?;
                        }
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => {
                            if self.st_ref_record_forbidden(struct_name)?
                                || self.array_record_forbidden(struct_name)?
                                || self.thunk_record_forbidden(struct_name)?
                                || self.task_record_forbidden(struct_name)?
                            {
                                return Ok(None);
                            }
                            push(
                                &mut work,
                                Work::Projection(struct_name.clone(), *idx),
                                self.limits.max_nodes,
                            )?;
                            push(
                                &mut work,
                                Work::Value(Scoped::new(expr.clone(), depth), None),
                                self.limits.max_nodes,
                            )?;
                        }
                        ExprNode::Const { name, levels } => {
                            if self.has_implementation(name)? || self.has_extern_attribute(name)? {
                                return Ok(None);
                            }
                            self.check_noncomputable_head(&source)?;
                            let definition = match self.environment.find(name) {
                                Some(ConstantInfo::Defn(definition)) => Some(definition.clone()),
                                Some(_) => None,
                                None => self.specialized_definition(name),
                            };
                            let Some(definition) = definition else {
                                return Ok(None);
                            };
                            if definition.safety != DefinitionSafety::Safe
                                || definition.base.level_params.len() != levels.len()
                                || levels
                                    .iter()
                                    .any(|level| level.has_mvar() || level.has_param())
                            {
                                return Ok(None);
                            }
                            let body = self.universe_instance(
                                &definition.value,
                                &definition.base.level_params,
                                levels,
                            )?;
                            push(
                                &mut work,
                                Work::Value(Scoped::new(body, depth), None),
                                self.limits.max_nodes,
                            )?;
                        }
                        _ => return Ok(None),
                    }
                }
                Work::Apply(argument) => {
                    let function = values
                        .pop()
                        .ok_or_else(|| unsupported("instance prefix function"))?
                        .reopen(self, depth)?;
                    let domain = if let ExprNode::Lam { binder_type, .. } = function.node() {
                        let domain = binder_type.clone();
                        push(
                            &mut work,
                            Work::Substitute(Scoped::new(function, depth)),
                            self.limits.max_nodes,
                        )?;
                        domain
                    } else {
                        let Some(domain) = self.instance_constructor_domain(&function)? else {
                            return Ok(None);
                        };
                        push(
                            &mut work,
                            Work::Constructor(Scoped::new(function, depth)),
                            self.limits.max_nodes,
                        )?;
                        domain
                    };
                    push(
                        &mut work,
                        Work::Value(argument, Some(Scoped::new(domain, depth))),
                        self.limits.max_nodes,
                    )?;
                }
                Work::Substitute(template) => {
                    let argument = values
                        .pop()
                        .ok_or_else(|| unsupported("instance prefix argument"))?
                        .reopen(self, depth)?;
                    let template = template.reopen(self, depth)?;
                    let ExprNode::Lam { body, .. } = template.node() else {
                        return Err(unsupported("instance prefix binder"));
                    };
                    let value = self.substitution(body, &argument)?;
                    push(
                        &mut work,
                        Work::Value(Scoped::new(value, depth), None),
                        self.limits.max_nodes,
                    )?;
                }
                Work::Constructor(function) => {
                    let argument = values
                        .pop()
                        .ok_or_else(|| unsupported("instance prefix field"))?
                        .reopen(self, depth)?;
                    let function = function.reopen(self, depth)?;
                    reserve(&mut values, self.limits.max_nodes)?;
                    values.push(Scoped::new(Expr::app(function, argument), depth));
                }
                Work::Projection(family, index) => {
                    let receiver = values
                        .pop()
                        .ok_or_else(|| unsupported("instance prefix receiver"))?
                        .reopen(self, depth)?;
                    let Some(value) = self.instance_factory_field(&family, index, &receiver)?
                    else {
                        return Ok(None);
                    };
                    reserve(&mut values, self.limits.max_nodes)?;
                    values.push(Scoped::new(value, depth));
                }
            }
        }
        if values.len() != 1 {
            return Err(unsupported("instance prefix result"));
        }
        let value = values
            .pop()
            .ok_or_else(|| unsupported("instance prefix result"))?
            .reopen(self, bindings.len())?;
        let (head, arguments) = self.spine(&value)?;
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Ctor(constructor)) = self.environment.find(name) else {
            return Ok(None);
        };
        if arguments.len()
            != (constructor.num_params as usize).saturating_add(constructor.num_fields as usize)
            || self.inert_instance_constructor(&value)?.is_none()
        {
            return Ok(None);
        }
        Ok(Some(InstancePrefix { bindings, value }))
    }

    fn instance_constructor_domain(&mut self, value: &Expr) -> Result<Option<Expr>, IngressError> {
        let (head, arguments) = self.spine(value)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Ctor(constructor)) = self.environment.find(name) else {
            return Ok(None);
        };
        let constructor = constructor.clone();
        if constructor.is_unsafe
            || constructor.base.level_params.len() != levels.len()
            || arguments.len()
                >= (constructor.num_params as usize).saturating_add(constructor.num_fields as usize)
            || self.has_implementation(name)?
            || self.has_extern_attribute(name)?
            || self.st_ref_record_forbidden(&constructor.induct)?
            || self.array_record_forbidden(&constructor.induct)?
            || self.thunk_record_forbidden(&constructor.induct)?
            || self.task_record_forbidden(&constructor.induct)?
        {
            return Ok(None);
        }
        let mut type_ = self.universe_instance(
            &constructor.base.type_,
            &constructor.base.level_params,
            levels,
        )?;
        for argument in arguments {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE { body, .. } = normal.node() else {
                return Ok(None);
            };
            type_ = self.substitution(body, &argument)?;
        }
        let normal = self.type_head(&type_)?;
        Ok(match normal.node() {
            ExprNode::ForallE { binder_type, .. } => Some(binder_type.clone()),
            _ => None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn c(label: &str) -> Expr {
        Expr::const_(name(label), Vec::new())
    }

    #[test]
    fn constructor_prefixes_keep_the_original_scope_and_never_enter_the_global_factory_cache() {
        let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
        let engine = Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap()
            .check_source_files(
                &[br#"
class PrefixAmount (n : Nat) where
  amount : {A : Type} -> A -> Nat
  unused : Nat
def prefixWork (n : Nat) : Nat := match n with | 0 => 0 | k + 1 => prefixWork k + 1
instance prefixAmount (n : Nat) : PrefixAmount n :=
  let paid : Nat := prefixWork n
  { amount := fun _ => paid, unused := prefixWork n }
"#],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
        let input = Expr::app(c("prefixAmount"), variable(0).unwrap());
        let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
        let exposed = preparation
            .residual_instance_constructor(&input)
            .unwrap()
            .unwrap();
        let needed = preparation.visited;
        assert_eq!(exposed.bindings.len(), 2);
        assert_eq!(
            exposed.bindings[0].value,
            Expr::app(c("prefixWork"), variable(0).unwrap())
        );
        assert_eq!(
            exposed.bindings[1].value,
            Expr::app(c("prefixWork"), variable(1).unwrap())
        );
        let method = preparation
            .instance_factory_field(&name("PrefixAmount"), 0, &exposed.value)
            .unwrap()
            .unwrap();
        assert_eq!(
            preparation
                .static_apply(&method, &[c("Nat"), nat::literal(0)])
                .unwrap(),
            Some(variable(1).unwrap())
        );
        assert!(preparation.specializations.factory_values.is_empty());
        let mut limited = Preparation::new(
            &engine.environment,
            IngressLimits {
                max_nodes: needed - 1,
                ..IngressLimits::default()
            },
        );
        assert!(matches!(
            limited.residual_instance_constructor(&input),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                limit,
                observed,
            }) if limit == needed - 1 && observed == needed
        ));
        assert!(limited.specializations.factory_values.is_empty());
        limited.limits.max_nodes = needed * 2 + 16;
        let retried = limited
            .residual_instance_constructor(&input)
            .unwrap()
            .unwrap();
        assert_eq!(retried.bindings.len(), exposed.bindings.len());
        assert_eq!(retried.value, exposed.value);
    }
}
