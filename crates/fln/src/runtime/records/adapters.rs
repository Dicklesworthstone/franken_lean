//! Structural conversion between verified hidden-carrier representations.
//! A conversion body is scoped under exactly one strict, typed value binder.
//! Functions get real contravariant/covariant adapters; containers are rebuilt
//! by their admitted recursor, whose IHs convert recursive children once.
use super::*;
use std::collections::HashMap;

type Pair = (Expr, Expr);
type Adapters = HashMap<Pair, Option<Expr>>;

struct Field {
    source: usize,
    conversion: Pair,
    erased: bool,
}

struct Minor {
    constructor: Name,
    domains: Vec<Expr>,
    fields: Vec<Field>,
}

struct Container {
    recursor: Expr,
    minors: Vec<Minor>,
}

enum Work {
    Visit(Pair),
    Function {
        pair: Pair,
        parameters: Vec<Pair>,
        result: Pair,
    },
    Container {
        pair: Pair,
        container: Container,
    },
}

fn variable(index: usize) -> Result<Expr, IngressError> {
    Expr::bvar(u32::try_from(index).map_err(|_| unsupported("hidden adapter scope"))?)
        .map_err(|_| unsupported("hidden adapter scope"))
}

fn converted(adapters: &Adapters, pair: &Pair, value: Expr) -> Result<Expr, IngressError> {
    Ok(match adapters.get(pair) {
        Some(None) => value,
        Some(Some(body)) => Expr::let_e(
            Name::anonymous(),
            pair.0.clone(),
            value,
            body.clone(),
            false,
        ),
        None => return Err(unsupported("hidden adapter dependency")),
    })
}

impl Preparation<'_> {
    /// No recursive Rust calls follow a source type. The worklist and the
    /// memo table are bounded by the ordinary ingress quotas. Recursive data
    /// edges are represented by the admitted recursor's IHs, not expanded.
    pub(super) fn erased_adapter(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<Option<Expr>, IngressError> {
        let root = (actual.clone(), expected.clone());
        let mut work = vec![Work::Visit(root.clone())];
        let mut adapters = Adapters::new();
        let mut active = HashSet::new();
        while let Some(task) = work.pop() {
            self.tick()?;
            let (pair, body) = match task {
                Work::Visit(pair) => {
                    if adapters.contains_key(&pair) {
                        continue;
                    }
                    if self.shared_erased_storage(&pair.0, &pair.1)? {
                        (pair, None)
                    } else {
                        if active.contains(&pair) {
                            return Err(unsupported("cyclic hidden adapter dependency"));
                        }
                        active
                            .try_reserve(1)
                            .map_err(|_| IngressError::AllocationFailure {
                                resource: IngressResource::ProgramTables,
                                requested: active.len().saturating_add(1),
                            })?;
                        active.insert(pair.clone());
                        let mut dependencies = Vec::new();
                        let task = match (self.value_type(&pair.0)?, self.value_type(&pair.1)?) {
                            (Some(ValueType::Closure(_)), Some(ValueType::Closure(_))) => {
                                let mut actual = pair.0.clone();
                                let mut expected = pair.1.clone();
                                let mut parameters = Vec::new();
                                while let (
                                    ExprNode::ForallE {
                                        binder_type: ad,
                                        body: ab,
                                        ..
                                    },
                                    ExprNode::ForallE {
                                        binder_type: ed,
                                        body: eb,
                                        ..
                                    },
                                ) = (actual.node(), expected.node())
                                {
                                    self.tick()?;
                                    if ab.has_loose_bvars() || eb.has_loose_bvars() {
                                        return Err(unsupported(
                                            "dependent hidden callback interface",
                                        ));
                                    }
                                    reserve(&mut parameters, self.limits.max_context_depth)?;
                                    parameters.push((ed.clone(), ad.clone()));
                                    reserve(&mut dependencies, self.limits.max_nodes)?;
                                    dependencies.push((ed.clone(), ad.clone()));
                                    actual = ab.clone();
                                    expected = eb.clone();
                                }
                                if parameters.is_empty()
                                    || matches!(actual.node(), ExprNode::ForallE { .. })
                                    || matches!(expected.node(), ExprNode::ForallE { .. })
                                {
                                    return Err(unsupported("hidden callback arity mismatch"));
                                }
                                let result = (actual, expected);
                                reserve(&mut dependencies, self.limits.max_nodes)?;
                                dependencies.push(result.clone());
                                Work::Function {
                                    pair,
                                    parameters,
                                    result,
                                }
                            }
                            (Some(ValueType::Constructor), Some(ValueType::Constructor)) => {
                                let container = self.hidden_container(&pair)?;
                                for minor in &container.minors {
                                    for field in &minor.fields {
                                        self.tick()?;
                                        if !field.erased {
                                            reserve(&mut dependencies, self.limits.max_nodes)?;
                                            dependencies.push(field.conversion.clone());
                                        }
                                    }
                                }
                                Work::Container { pair, container }
                            }
                            _ => return Err(unsupported("nonuniform hidden field representation")),
                        };
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(task);
                        for dependency in dependencies.into_iter().rev() {
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Work::Visit(dependency));
                        }
                        continue;
                    }
                }
                Work::Function {
                    pair,
                    parameters,
                    result,
                } => {
                    let mut body = variable(parameters.len())?;
                    for (index, parameter) in parameters.iter().enumerate() {
                        self.tick()?;
                        body = Expr::app(
                            body,
                            converted(
                                &adapters,
                                parameter,
                                variable(parameters.len() - 1 - index)?,
                            )?,
                        );
                    }
                    body = converted(&adapters, &result, body)?;
                    for (domain, _) in parameters.into_iter().rev() {
                        self.tick()?;
                        body = Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default);
                    }
                    // Both interfaces stay explicit; ordinary ingress inserts
                    // Box/Unbox and checks capture and result ownership.
                    body =
                        Expr::let_e(Name::anonymous(), pair.1.clone(), body, variable(0)?, false);
                    (pair, Some(body))
                }
                Work::Container { pair, container } => {
                    let mut body = container.recursor;
                    for minor in container.minors {
                        self.tick()?;
                        let mut branch = Expr::const_(minor.constructor, vec![]);
                        for field in minor.fields {
                            self.tick()?;
                            let value = if field.erased {
                                proofs::erased_value()
                            } else {
                                converted(
                                    &adapters,
                                    &field.conversion,
                                    variable(minor.domains.len() - 1 - field.source)?,
                                )?
                            };
                            branch = Expr::app(branch, value);
                        }
                        for domain in minor.domains.into_iter().rev() {
                            self.tick()?;
                            branch =
                                Expr::lam(Name::anonymous(), domain, branch, BinderInfo::Default);
                        }
                        body = Expr::app(body, branch);
                    }
                    (pair, Some(Expr::app(body, variable(0)?)))
                }
            };
            active.remove(&pair);
            adapters
                .try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: adapters.len().saturating_add(1),
                })?;
            adapters.insert(pair, body);
        }
        adapters
            .remove(&root)
            .ok_or_else(|| unsupported("hidden adapter result"))
    }

    /// Derive a map from the actual admitted family and its exact constructor
    /// correspondence. This does not recognize List/Option by spelling and
    /// does not change existing object or callable metadata.
    fn hidden_container(&mut self, pair: &Pair) -> Result<Container, IngressError> {
        let actual = self
            .record_shape(&pair.0)?
            .ok_or_else(|| unsupported("hidden source layout"))?;
        let expected = self
            .record_shape(&pair.1)?
            .ok_or_else(|| unsupported("hidden target layout"))?;
        let (head, parameters) = self.spine(&actual.source)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Err(unsupported("hidden container family"));
        };
        let Some(ConstantInfo::Induct(family)) = self.environment.find(name) else {
            return Err(unsupported("hidden container family metadata"));
        };
        if family.num_indices != 0 || family.num_nested != 0 || family.all.len() != 1 {
            return Err(unsupported("hidden container recursive profile"));
        }
        let recursor_name = Name::str(name.clone(), "rec");
        let Some(ConstantInfo::Rec(rec)) = self.environment.find(&recursor_name) else {
            return Err(unsupported("hidden container recursor"));
        };
        if rec.is_unsafe
            || rec.all != family.all
            || rec.num_indices != 0
            || rec.num_motives != 1
            || rec.num_params != family.num_params
            || rec.num_minors as usize != actual.constructors.len()
            || rec.rules.len() != actual.constructors.len()
            || actual.constructors.len() != expected.constructors.len()
        {
            return Err(unsupported("hidden container recursor metadata"));
        }
        let (target_head, target_parameters) = self.spine(&expected.source)?;
        let ExprNode::Const {
            name: target_name,
            levels: target_levels,
        } = target_head.node()
        else {
            return Err(unsupported("hidden target family"));
        };
        if target_name != name || target_parameters.len() != parameters.len() {
            return Err(unsupported("hidden container family mismatch"));
        }
        let mut target_sort =
            self.universe_instance(&family.base.type_, &family.base.level_params, target_levels)?;
        for parameter in &target_parameters {
            self.tick()?;
            let normal = self.type_head(&target_sort)?;
            let ExprNode::ForallE { body, .. } = normal.node() else {
                return Err(unsupported("hidden target parameter telescope"));
            };
            target_sort = self.substitution(body, parameter)?;
        }
        let target_sort = self.type_head(&target_sort)?;
        let ExprNode::Sort {
            level: result_level,
        } = target_sort.node()
        else {
            return Err(unsupported("hidden target universe"));
        };
        let mut recursor_levels = Vec::new();
        let mut motive_levels = 0usize;
        for parameter in &rec.base.level_params {
            self.tick()?;
            let level = match family
                .base
                .level_params
                .iter()
                .position(|name| name == parameter)
            {
                Some(index) => levels
                    .get(index)
                    .ok_or_else(|| unsupported("hidden family universe"))?
                    .clone(),
                None => {
                    motive_levels += 1;
                    result_level.clone()
                }
            };
            reserve(&mut recursor_levels, self.limits.max_context_depth)?;
            recursor_levels.push(level);
        }
        if motive_levels != 1 {
            return Err(unsupported("hidden recursor motive universe"));
        }
        let mut recursor = Expr::const_(recursor_name, recursor_levels);
        for parameter in parameters {
            self.tick()?;
            recursor = Expr::app(recursor, parameter);
        }
        recursor = Expr::app(
            recursor,
            Expr::lam(
                Name::anonymous(),
                actual.source.clone(),
                expected.source.clone(),
                BinderInfo::Default,
            ),
        );
        let mut minors = Vec::new();
        for ((actual_ctor, expected_ctor), rule) in actual
            .constructors
            .iter()
            .zip(&expected.constructors)
            .zip(&rec.rules)
        {
            self.tick()?;
            if actual_ctor.original != expected_ctor.original
                || actual_ctor.tag != expected_ctor.tag
                || actual_ctor.type_fields != expected_ctor.type_fields
                || actual_ctor.fields.len() != expected_ctor.fields.len()
                || rule.ctor != actual_ctor.original
                || rule.nfields as usize != actual_ctor.fields.len()
            {
                return Err(unsupported("hidden constructor correspondence"));
            }
            let mut domains = Vec::new();
            for field in &actual_ctor.fields {
                self.tick()?;
                reserve(&mut domains, self.limits.max_context_depth)?;
                domains.push(field.clone());
            }
            let mut fields = Vec::new();
            for (index, (a, e)) in actual_ctor
                .fields
                .iter()
                .zip(&expected_ctor.fields)
                .enumerate()
            {
                self.tick()?;
                let (source, source_type) = if self
                    .recursive_field(a, std::slice::from_ref(&actual.source))?
                    .is_some()
                {
                    let mut domains_ = Vec::new();
                    let mut result = a;
                    while let ExprNode::ForallE {
                        binder_type, body, ..
                    } = result.node()
                    {
                        self.tick()?;
                        reserve(&mut domains_, self.limits.max_context_depth)?;
                        domains_.push(binder_type.clone());
                        result = body;
                    }
                    let mut ih_type = expected.source.clone();
                    for domain in domains_.into_iter().rev() {
                        self.tick()?;
                        ih_type =
                            Expr::forall_e(Name::anonymous(), domain, ih_type, BinderInfo::Default);
                    }
                    let source = domains.len();
                    reserve(&mut domains, self.limits.max_context_depth)?;
                    domains.push(ih_type.clone());
                    (source, ih_type)
                } else {
                    (index, a.clone())
                };
                reserve(&mut fields, self.limits.max_context_depth)?;
                fields.push(Field {
                    source,
                    conversion: (source_type, e.clone()),
                    erased: actual_ctor.type_fields.get(index) == Some(&true),
                });
            }
            reserve(&mut minors, self.limits.fir.max_constructors)?;
            minors.push(Minor {
                constructor: expected_ctor.name.clone(),
                domains,
                fields,
            });
        }
        Ok(Container { recursor, minors })
    }
}
