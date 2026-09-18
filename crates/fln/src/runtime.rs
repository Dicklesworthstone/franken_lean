//! Bounded post-admission erasure into executable scalar control flow.
//!
//! This never changes the declaration sent to either checker. Special forms
//! are recognized only against exact admitted seed declarations, not by name
//! alone. Unsupported dependent result representations remain typed refusals.
mod nat;
mod records;
mod variants;

use super::*;
use fln_comp::ingress::{BoolCaseBinding, CallableBindings, ConstructorCaseBinding};
use std::collections::HashSet;

pub(super) struct Preparation<'a> {
    environment: &'a Environment,
    limits: IngressLimits,
    visited: usize,
    pub(super) lambdas: Vec<LambdaBinding>,
    pub(super) cases: Vec<BoolCaseBinding>,
    variant_cases: Vec<ConstructorCaseBinding>,
    next_variant: u64,
    lambda_keys: HashSet<Expr>,
    bool_recursor_checked: bool,
    next_branch: usize,
    next_local: u64,
    next_nat: u64,
    nat_family_checked: bool,
    value_types: ExecutableValueTypes,
    pub(super) constructors: Vec<fln_comp::ingress::ConstructorBinding>,
}

enum Task {
    ConstructorCase {
        name: Name,
        result: ValueType,
        branches: usize,
    },
    RecursiveLambda {
        parameters: Vec<ValueType>,
        result: ValueType,
    },
    Visit(Expr),
    Apply(usize),
    Lam {
        name: Name,
        type_: Expr,
        info: BinderInfo,
    },
    Let {
        name: Name,
        type_: Expr,
        nondep: bool,
    },
    Proj {
        name: Name,
        index: u64,
    },
    Case {
        name: Name,
        result: ValueType,
    },
}

impl<'a> Preparation<'a> {
    pub(super) fn new(environment: &'a Environment, limits: IngressLimits) -> Self {
        Self {
            environment,
            limits,
            visited: 0,
            lambdas: Vec::new(),
            cases: Vec::new(),
            variant_cases: Vec::new(),
            next_variant: 0,
            lambda_keys: HashSet::new(),
            bool_recursor_checked: false,
            next_branch: 0,
            next_local: 0,
            next_nat: 0,
            nat_family_checked: false,
            value_types: ExecutableValueTypes::bounded_source(),
            constructors: Vec::new(),
        }
    }

    fn tick(&mut self) -> Result<(), IngressError> {
        charge_catalog_node(&mut self.visited, self.limits)
    }

    fn thunk(&mut self, body: &Expr) -> Result<Expr, IngressError> {
        let observed = self.next_branch.saturating_add(1);
        if observed > self.limits.max_lambda_bindings {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::LambdaBindings,
                limit: self.limits.max_lambda_bindings,
                observed,
            });
        }
        let id = u64::try_from(self.next_branch).map_err(|_| unsupported("branch identity"))?;
        self.next_branch = observed;
        let lifted = body
            .lift_loose(0, 1)
            .map_err(|_| unsupported("branch capture scope"))?;
        // The compiler keys annotations by exact lambda syntax. Identical
        // relative bodies can close over different types at different sites;
        // deterministic site identities keep those annotations separate.
        Ok(Expr::lam(
            Name::num(name("_fln_runtime_branch"), id),
            Expr::const_(name("Bool"), vec![]),
            lifted,
            BinderInfo::Default,
        ))
    }

    fn check_bool_recursor(&mut self) -> Result<(), IngressError> {
        if self.bool_recursor_checked {
            return Ok(());
        }
        let Declaration::Inductive(block) = fln_elab::seed::bool_seed_declaration() else {
            return Err(unsupported("Boolean recursor seed"));
        };
        let expected = block
            .recursors
            .iter()
            .find(|r| r.base.name == name("Bool.rec"))
            .ok_or_else(|| unsupported("Boolean recursor seed"))?;
        if !matches!(self.environment.find(&expected.base.name),
            Some(ConstantInfo::Rec(actual)) if actual == expected)
        {
            return Err(unsupported("noncanonical Boolean recursor"));
        }
        self.bool_recursor_checked = true;
        Ok(())
    }

    fn branch_name(&mut self, result: ValueType) -> Result<Name, IngressError> {
        let index = match result {
            ValueType::Nat => 0,
            ValueType::String => 1,
            ValueType::Bool => 2,
            ValueType::Constructor => 3,
            _ => return Err(unsupported("conditional result representation")),
        };
        let name = Name::num(Name::from_components(["_fln_runtime_bool_case"]), index);
        if self.environment.contains(&name) {
            return Err(unsupported("runtime case name collision"));
        }
        if !self.cases.iter().any(|case| case.name == name) {
            reserve(&mut self.cases, self.limits.fir.max_functions)?;
            self.cases.push(BoolCaseBinding {
                name: name.clone(),
                result,
            });
        }
        Ok(name)
    }

    fn register_branch(&mut self, lambda: &Expr, result: ValueType) -> Result<(), IngressError> {
        if self.lambda_keys.contains(lambda) {
            return Ok(());
        }
        reserve(&mut self.lambdas, self.limits.max_lambda_bindings)?;
        self.lambda_keys
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::LambdaBindings,
                requested: self.lambda_keys.len() + 1,
            })?;
        self.lambda_keys.insert(lambda.clone());
        self.lambdas.push(LambdaBinding {
            lambda: lambda.clone(),
            parameters: vec![ValueType::Bool],
            parameter_ownership: borrowed_runtime_parameters(1)?,
            result,
            result_ownership: result_ownership(result),
            recursion: LambdaRecursion::NonRecursive,
        });
        Ok(())
    }

    /// Derive the compiler's local-closure metadata from a checked let type.
    /// This runs after admission, and the ordinary FIR ingress still validates
    /// captures, calls and ownership. Unsupported erasures remain refusals.
    fn local_function(&mut self, value: &Expr, type_: &Expr) -> Result<Expr, IngressError> {
        let ExprNode::Lam {
            binder_type,
            body,
            binder_info,
            ..
        } = value.node()
        else {
            return Ok(value.clone());
        };
        let definition = DefinitionVal {
            base: fln_env::constants::ConstantVal {
                name: Name::anonymous(),
                level_params: Vec::new(),
                type_: type_.clone(),
            },
            value: value.clone(),
            hints: fln_env::constants::ReducibilityHints::Abbrev,
            safety: fln_env::constants::DefinitionSafety::Safe,
            all: Vec::new(),
        };
        let Some(signature) = self.signature(&definition, false)? else {
            return Ok(value.clone());
        };
        if signature.parameters.is_empty() {
            return Ok(value.clone());
        }
        reserve(&mut self.lambdas, self.limits.max_lambda_bindings)?;
        let id = self.next_local;
        self.next_local = id
            .checked_add(1)
            .ok_or_else(|| unsupported("local closure identity"))?;
        // Equal relative bodies at different sites may capture values of
        // different types. Give metadata keys distinct deterministic identities
        // without changing de Bruijn indices or lifting already prepared bodies.
        let lambda = Expr::lam(
            Name::num(name("_fln_runtime_local"), id),
            binder_type.clone(),
            body.clone(),
            *binder_info,
        );
        let parameter_ownership = borrowed_runtime_parameters(signature.parameters.len())?;
        self.lambdas.push(LambdaBinding {
            lambda: lambda.clone(),
            parameters: signature.parameters,
            parameter_ownership,
            result: signature.result,
            result_ownership: signature.result_ownership,
            recursion: LambdaRecursion::NonRecursive,
        });
        Ok(lambda)
    }

    /// Explicit work frames preserve lexical scope, including branches nested
    /// in let values and functions. Branch binders are inserted *before* their
    /// bodies are transformed so nested closure annotations cannot go stale
    /// under a later de Bruijn lift.
    pub(super) fn expression(&mut self, input: &Expr) -> Result<Expr, IngressError> {
        let mut tasks = vec![Task::Visit(input.clone())];
        let mut values = Vec::<Expr>::new();
        let limit = self.limits.max_nodes.saturating_mul(3).saturating_add(1);
        while let Some(task) = tasks.pop() {
            self.tick()?;
            tasks
                .try_reserve(4)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::PendingTasks,
                    requested: tasks.len().saturating_add(4),
                })?;
            if tasks.len().saturating_add(4) > limit {
                return Err(IngressError::ResourceLimit {
                    resource: IngressResource::PendingTasks,
                    limit,
                    observed: tasks.len().saturating_add(4),
                });
            }
            reserve(&mut values, self.limits.max_nodes.saturating_add(1))?;
            match task {
                Task::Visit(expr) => {
                    if matches!(expr.node(), ExprNode::App { .. }) {
                        let (head, args) = self.spine(&expr)?;
                        if matches!(head.node(), ExprNode::Const { name: n, levels }
                            if n == &name("Bool.rec") && levels.len() == 1)
                            && args.len() == 4
                        {
                            self.check_bool_recursor()?;
                            let ExprNode::Lam { body: motive, .. } = args[0].node() else {
                                return Err(unsupported("Boolean motive"));
                            };
                            let result = self
                                .value_type(motive)?
                                .ok_or_else(|| unsupported("dependent Boolean motive"))?;
                            let case = self.branch_name(result)?;
                            tasks.push(Task::Case { name: case, result });
                            tasks.push(Task::Visit(self.thunk(&args[2])?));
                            tasks.push(Task::Visit(self.thunk(&args[1])?));
                            tasks.push(Task::Visit(args[3].clone()));
                            continue;
                        }
                        if matches!(head.node(), ExprNode::Const { name: n, levels }
                            if n == &name("Nat.rec") && levels.len() == 1)
                            && args.len() >= 4
                        {
                            let recursion = self.nat_recursion(&args)?;
                            let required = args.len().saturating_add(1);
                            if tasks.len().saturating_add(required) > limit {
                                return Err(IngressError::ResourceLimit {
                                    resource: IngressResource::PendingTasks,
                                    limit,
                                    observed: tasks.len().saturating_add(required),
                                });
                            }
                            tasks.try_reserve(required).map_err(|_| {
                                IngressError::AllocationFailure {
                                    resource: IngressResource::PendingTasks,
                                    requested: tasks.len().saturating_add(required),
                                }
                            })?;
                            tasks.push(Task::Apply(args.len() - 3));
                            tasks.extend(args[3..].iter().rev().cloned().map(Task::Visit));
                            tasks.push(Task::RecursiveLambda {
                                parameters: recursion.parameters,
                                result: recursion.result,
                            });
                            tasks.push(Task::Visit(recursion.lambda));
                            continue;
                        }
                        if matches!(head.node(), ExprNode::Const { name: n, levels }
                            if n == &name("Nat.succ") && levels.is_empty())
                            && args.len() == 1
                        {
                            self.check_nat_family()?;
                            tasks.push(Task::Visit(Expr::app(
                                Expr::app(Expr::const_(name("Nat.add"), vec![]), args[0].clone()),
                                nat::literal(1),
                            )));
                            continue;
                        }
                        if let ExprNode::Const { name, levels } = head.node()
                            && let Some(case) = self.variant_recursor(name, levels, &args)?
                        {
                            let required = case.branches.len().saturating_add(2);
                            if tasks.len().saturating_add(required) > limit {
                                return Err(IngressError::ResourceLimit {
                                    resource: IngressResource::PendingTasks,
                                    limit,
                                    observed: tasks.len().saturating_add(required),
                                });
                            }
                            tasks.try_reserve(required).map_err(|_| {
                                IngressError::AllocationFailure {
                                    resource: IngressResource::PendingTasks,
                                    requested: tasks.len().saturating_add(required),
                                }
                            })?;
                            tasks.push(Task::ConstructorCase {
                                name: case.name,
                                result: case.result,
                                branches: case.branches.len(),
                            });
                            tasks.extend(case.branches.into_iter().rev().map(Task::Visit));
                            tasks.push(Task::Visit(case.major));
                            continue;
                        }
                        if let ExprNode::Const { name, levels } = head.node()
                            && let Some(eliminated) = self.record_recursor(name, levels, &args)?
                        {
                            tasks.push(Task::Visit(eliminated));
                            continue;
                        }
                        let required = args.len().saturating_add(2);
                        if tasks.len().saturating_add(required) > limit {
                            return Err(IngressError::ResourceLimit {
                                resource: IngressResource::PendingTasks,
                                limit,
                                observed: tasks.len().saturating_add(required),
                            });
                        }
                        tasks.try_reserve(required).map_err(|_| {
                            IngressError::AllocationFailure {
                                resource: IngressResource::PendingTasks,
                                requested: tasks.len().saturating_add(required),
                            }
                        })?;
                        tasks.push(Task::Apply(args.len()));
                        tasks.extend(args.into_iter().rev().map(Task::Visit));
                        tasks.push(Task::Visit(head));
                        continue;
                    }
                    match expr.node() {
                        ExprNode::Const { name: n, levels }
                            if n == &name("Nat.zero") && levels.is_empty() =>
                        {
                            self.check_nat_family()?;
                            values.push(nat::literal(0));
                        }
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => {
                            tasks.push(Task::Lam {
                                name: binder_name.clone(),
                                type_: binder_type.clone(),
                                info: *binder_info,
                            });
                            tasks.push(Task::Visit(body.clone()));
                        }
                        ExprNode::LetE {
                            decl_name: name,
                            type_,
                            value,
                            body,
                            non_dep: nondep,
                        } => {
                            tasks.push(Task::Let {
                                name: name.clone(),
                                type_: type_.clone(),
                                nondep: *nondep,
                            });
                            tasks.push(Task::Visit(body.clone()));
                            tasks.push(Task::Visit(value.clone()));
                        }
                        ExprNode::MData { expr, .. } => tasks.push(Task::Visit(expr.clone())),
                        ExprNode::Proj {
                            struct_name: type_name,
                            idx,
                            expr,
                        } => {
                            self.value_type(&Expr::const_(type_name.clone(), vec![]))?;
                            tasks.push(Task::Proj {
                                name: type_name.clone(),
                                index: *idx,
                            });
                            tasks.push(Task::Visit(expr.clone()));
                        }
                        ExprNode::Const { name, .. } => {
                            self.constructor(name)?;
                            values.push(expr.clone());
                        }
                        _ => values.push(expr.clone()),
                    }
                }
                Task::ConstructorCase {
                    name,
                    result,
                    branches,
                } => {
                    let start = values
                        .len()
                        .checked_sub(branches.saturating_add(1))
                        .ok_or_else(|| unsupported("constructor case stack"))?;
                    for branch in &values[start + 1..] {
                        self.register_constructor_branch(branch, result)?;
                    }
                    let term = values
                        .drain(start..)
                        .fold(Expr::const_(name, vec![]), Expr::app);
                    values.push(term);
                }
                Task::RecursiveLambda { parameters, result } => {
                    let lambda = pop(&mut values)?;
                    values.push(self.register_recursion(lambda, parameters, result)?);
                }
                Task::Apply(count) => {
                    let start = values
                        .len()
                        .checked_sub(count.saturating_add(1))
                        .ok_or_else(|| unsupported("runtime application stack"))?;
                    let mut parts = values.drain(start..);
                    let function = parts
                        .next()
                        .ok_or_else(|| unsupported("runtime application head"))?;
                    let value = parts.fold(function, Expr::app);
                    values.push(value);
                }
                Task::Lam { name, type_, info } => {
                    let body = pop(&mut values)?;
                    values.push(Expr::lam(name, type_, body, info));
                }
                Task::Let {
                    name,
                    type_,
                    nondep,
                } => {
                    let body = pop(&mut values)?;
                    let value = pop(&mut values)?;
                    let value = self.local_function(&value, &type_)?;
                    values.push(Expr::let_e(name, type_, value, body, nondep));
                }
                Task::Proj { name, index } => {
                    let value = pop(&mut values)?;
                    values.push(Expr::proj(name, index, value));
                }
                Task::Case { name, result } => {
                    let yes = pop(&mut values)?;
                    let no = pop(&mut values)?;
                    let condition = pop(&mut values)?;
                    self.register_branch(&no, result)?;
                    self.register_branch(&yes, result)?;
                    values.push(
                        [condition, no, yes]
                            .into_iter()
                            .fold(Expr::const_(name, vec![]), Expr::app),
                    );
                }
            }
        }
        if values.len() != 1 {
            return Err(unsupported("runtime preparation result"));
        }
        pop(&mut values)
    }

    fn spine(&mut self, expr: &Expr) -> Result<(Expr, Vec<Expr>), IngressError> {
        let mut head = expr.clone();
        let mut args = Vec::new();
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    let observed = args.len().saturating_add(1);
                    if observed > self.limits.max_application_args {
                        return Err(IngressError::ResourceLimit {
                            resource: IngressResource::ApplicationArguments,
                            limit: self.limits.max_application_args,
                            observed,
                        });
                    }
                    args.try_reserve(1)
                        .map_err(|_| IngressError::AllocationFailure {
                            resource: IngressResource::ApplicationArguments,
                            requested: observed,
                        })?;
                    args.push(a.clone());
                    head = f.clone();
                }
                ExprNode::MData { expr, .. } => head = expr.clone(),
                _ => break,
            }
        }
        args.reverse();
        Ok((head, args))
    }

    pub(super) fn callables<'b>(
        &'b self,
        functions: &'b [FunctionBinding],
    ) -> CallableBindings<'b> {
        CallableBindings {
            functions,
            lambdas: &self.lambdas,
            bool_cases: &self.cases,
            constructor_cases: &self.variant_cases,
        }
    }
}
fn reserve<T>(v: &mut Vec<T>, limit: usize) -> Result<(), IngressError> {
    let observed = v.len().saturating_add(1);
    if observed > limit {
        return Err(IngressError::ResourceLimit {
            resource: IngressResource::ProgramTables,
            limit,
            observed,
        });
    }
    v.try_reserve(1)
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: observed,
        })
}
fn pop(values: &mut Vec<Expr>) -> Result<Expr, IngressError> {
    values
        .pop()
        .ok_or_else(|| unsupported("runtime preparation stack"))
}
fn unsupported(kind: &'static str) -> IngressError {
    IngressError::UnsupportedNode { kind }
}
fn name(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn scalar_type(expr: &Expr) -> Option<ValueType> {
    match expr.node() {
        ExprNode::Const { name: n, levels } if levels.is_empty() => {
            if n == &name("Nat") {
                Some(ValueType::Nat)
            } else if n == &name("String") {
                Some(ValueType::String)
            } else if n == &name("Bool") {
                Some(ValueType::Bool)
            } else {
                None
            }
        }
        _ => None,
    }
}
fn result_ownership(result: ValueType) -> CallableResultOwnership {
    match result {
        ValueType::Bool => CallableResultOwnership::Scalar,
        ValueType::Nat => CallableResultOwnership::OwnedOrScalar,
        _ => CallableResultOwnership::Owned,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn long_application_spines_are_prepared_once_and_remain_bounded() {
        let environment = Environment::new();
        let mut limits = IngressLimits {
            max_nodes: 15_000,
            max_application_args: 4_000,
            ..IngressLimits::default()
        };
        let expression = (0..3_000).fold(Expr::const_(name("f"), vec![]), |f, _| {
            Expr::app(f, Expr::const_(name("x"), vec![]))
        });
        let mut preparation = Preparation::new(&environment, limits);
        assert_eq!(preparation.expression(&expression).unwrap(), expression);
        assert!(
            preparation.visited < 10_000,
            "no quadratic rewalk of the application spine"
        );
        limits.max_nodes = 50;
        assert!(matches!(
            Preparation::new(&environment, limits).expression(&expression),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                ..
            })
        ));
    }
    #[test]
    fn a_familiar_recursor_name_does_not_supply_admission_authority() {
        let environment = Environment::new();
        let motive = Expr::lam(
            name("b"),
            Expr::const_(name("Bool"), vec![]),
            Expr::const_(name("Nat"), vec![]),
            BinderInfo::Default,
        );
        let expression = [
            motive,
            Expr::const_(name("x"), vec![]),
            Expr::const_(name("y"), vec![]),
            Expr::const_(name("Bool.true"), vec![]),
        ]
        .into_iter()
        .fold(
            Expr::const_(name("Bool.rec"), vec![Level::one()]),
            Expr::app,
        );
        assert!(matches!(
            Preparation::new(&environment, IngressLimits::default()).expression(&expression),
            Err(IngressError::UnsupportedNode {
                kind: "noncanonical Boolean recursor"
            })
        ));
    }
}
