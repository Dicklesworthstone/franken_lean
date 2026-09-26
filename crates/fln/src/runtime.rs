//! Bounded post-admission erasure into executable scalar control flow.
//!
//! This never changes the declaration sent to either checker. Special forms
//! are recognized only against exact admitted seed declarations, not by name
//! alone. Unsupported dependent result representations remain typed refusals.
mod callables;
mod data_recursion;
mod empty;
mod global;
mod indexed;
mod mutual;
mod nat;
mod projections;
mod proofs;
mod records;
mod specialize;
mod transport;
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
    empty_cases: Vec<fln_comp::ingress::EmptyCaseBinding>,
    false_family_checked: bool,
    next_variant: u64,
    next_mutual: u32,
    lambda_keys: HashSet<Expr>,
    bool_recursor_checked: bool,
    equality_family_checked: bool,
    next_branch: usize,
    next_local: u64,
    next_nat: u64,
    nat_family_checked: bool,
    value_types: ExecutableValueTypes,
    interfaces: Vec<fln_comp::ingress::ClosureSignature>,
    specializations: specialize::Store,
    data_shapes: std::collections::HashMap<Expr, records::Shape>,
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
    MutualLambdas {
        group: u32,
        selected: usize,
        signatures: Vec<(Vec<ValueType>, ValueType)>,
    },
    Visit(Expr),
    Callee(Expr),
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
            empty_cases: Vec::new(),
            false_family_checked: false,
            next_variant: 0,
            next_mutual: 0,
            lambda_keys: HashSet::new(),
            bool_recursor_checked: false,
            equality_family_checked: false,
            next_branch: 0,
            next_local: 0,
            next_nat: 0,
            nat_family_checked: false,
            value_types: ExecutableValueTypes::bounded_source(),
            interfaces: Vec::new(),
            specializations: specialize::Store::default(),
            data_shapes: std::collections::HashMap::new(),
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
            ValueType::Closure(id) => 4 + u64::from(id.get()),
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
        let Some(mut signature) = self.signature(&definition, false)? else {
            return Ok(value.clone());
        };
        if signature.parameters.is_empty() {
            return Ok(value.clone());
        }
        self.refine_local_result(&mut signature)?;
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
        self.expression_at_type(input, None)
    }

    pub(super) fn expression_at_type(
        &mut self,
        input: &Expr,
        expected: Option<Expr>,
    ) -> Result<Expr, IngressError> {
        // Catalog bodies have already had their original binder telescope
        // removed. Their projections are selected by signature normalization;
        // closed roots still carry the source context needed for selection.
        let input = if input.has_loose_bvars() {
            input.clone()
        } else {
            let runtime_expected = expected
                .as_ref()
                .map(|type_| self.erase_runtime_type(type_))
                .transpose()?;
            let erased = self.erase_proofs(input, expected)?;
            let erased = if let Some(type_) = runtime_expected {
                self.annotate_execution_value(erased, type_)?
            } else {
                erased
            };
            self.lower_projections(&erased)?
        };
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
                        if let Some(empty) = self.empty_recursor(&head, &args)? {
                            tasks.push(Task::Visit(empty));
                            continue;
                        }
                        if let Some(transported) = self.equality_transport(&head, &args)? {
                            tasks.push(Task::Visit(transported));
                            continue;
                        }
                        if let Some(constructor) = self.specialize_constructor(&head, &args)? {
                            tasks.push(Task::Visit(constructor));
                            continue;
                        }
                        if let Some(specialized) = self.specialize_call(&head, &args)? {
                            tasks.push(Task::Visit(specialized));
                            continue;
                        }
                        if let Some(reduced) = self.static_apply(&head, &args)? {
                            tasks.push(Task::Visit(reduced));
                            continue;
                        }
                        if let Some(producer) = self.global_producer(&head, &args)? {
                            tasks.push(Task::Visit(producer));
                            continue;
                        }
                        if let Some(partial) = self.partial_call(&head, &args)? {
                            tasks.push(Task::Visit(partial));
                            continue;
                        }
                        if let Some(annotated) = self.annotate_call(&head, &args)? {
                            tasks.push(Task::Visit(annotated));
                            continue;
                        }
                        if let Some(applied) = self.overapplied_data_recursor(&head, &args)? {
                            tasks.push(Task::Visit(applied));
                            continue;
                        }
                        if matches!(head.node(), ExprNode::Const { name: n, levels }
                            if n == &name("Bool.rec") && levels.len() == 1)
                            && args.len() == 4
                        {
                            self.check_bool_recursor()?;
                            let motive = self
                                .indexed_motive(&args[0], &[], &Expr::const_(name("Bool"), vec![]))?
                                .ok_or_else(|| unsupported("dependent Boolean motive"))?;
                            let result = self
                                .value_type(&motive)?
                                .ok_or_else(|| unsupported("dependent Boolean motive"))?;
                            let case = self.branch_name(result)?;
                            let yes = self.typed_callable_result(
                                args[2].clone(),
                                motive.clone(),
                                result,
                            )?;
                            let no = self.typed_callable_result(
                                args[1].clone(),
                                motive.clone(),
                                result,
                            )?;
                            tasks.push(Task::Case { name: case, result });
                            tasks.push(Task::Visit(self.thunk(&yes)?));
                            tasks.push(Task::Visit(self.thunk(&no)?));
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
                            && let Some(case) = self.mutual_case(name, levels, &args)?
                        {
                            self.schedule_constructor_case(case, &mut tasks, limit)?;
                            continue;
                        }
                        if let ExprNode::Const { name, levels } = head.node()
                            && let Some(fold) = self.mutual_fold(name, levels, &args)?
                        {
                            self.schedule_mutual_fold(fold, &mut tasks, limit)?;
                            continue;
                        }
                        if let ExprNode::Const { name, levels } = head.node()
                            && let Some(recursion) = self.data_recursion(name, levels, &args)?
                        {
                            let required = recursion
                                .arguments
                                .len()
                                .saturating_add(recursion.domains.len())
                                .saturating_add(4);
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
                            tasks.push(Task::Apply(recursion.arguments.len()));
                            tasks.extend(recursion.arguments.into_iter().rev().map(Task::Visit));
                            tasks.push(Task::RecursiveLambda {
                                parameters: recursion.parameters,
                                result: recursion.case.result,
                            });
                            tasks.push(Task::Lam {
                                name: recursion.name,
                                type_: recursion.self_type,
                                info: BinderInfo::Default,
                            });
                            for domain in recursion.domains {
                                tasks.push(Task::Lam {
                                    name: Name::anonymous(),
                                    type_: domain,
                                    info: BinderInfo::Default,
                                });
                            }
                            self.schedule_constructor_case(recursion.case, &mut tasks, limit)?;
                            continue;
                        }
                        if let ExprNode::Const { name, levels } = head.node()
                            && let Some(case) = self.variant_recursor(name, levels, &args)?
                        {
                            self.schedule_constructor_case(case, &mut tasks, limit)?;
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
                        tasks.push(if matches!(head.node(), ExprNode::Const { .. }) {
                            Task::Callee(head)
                        } else {
                            Task::Visit(head)
                        });
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
                                type_: self.normalize_type(binder_type)?,
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
                                type_: self.normalize_type(type_)?,
                                nondep: *nondep,
                            });
                            tasks.push(Task::Visit(body.clone()));
                            tasks.push(Task::Visit(self.annotate_callable_tail(value, type_)?));
                        }
                        ExprNode::MData { expr, .. } => tasks.push(Task::Visit(expr.clone())),
                        ExprNode::Proj {
                            struct_name: type_name,
                            idx,
                            expr,
                        } => {
                            if let Some(selected) = self.static_projection(type_name, *idx, expr)? {
                                tasks.push(Task::Visit(selected));
                                continue;
                            }
                            self.value_type(&Expr::const_(type_name.clone(), vec![]))?;
                            tasks.push(Task::Proj {
                                name: type_name.clone(),
                                index: *idx,
                            });
                            tasks.push(Task::Visit(expr.clone()));
                        }
                        ExprNode::Const { name, .. } => {
                            if let Some(constructor) = self.specialize_constructor(&expr, &[])? {
                                tasks.push(Task::Visit(constructor));
                                continue;
                            }
                            if let Some(producer) = self.global_producer(&expr, &[])? {
                                tasks.push(Task::Visit(producer));
                                continue;
                            }
                            if let Some(partial) = self.partial_call(&expr, &[])? {
                                tasks.push(Task::Visit(partial));
                                continue;
                            }
                            self.constructor(name)?;
                            values.push(expr.clone());
                        }
                        _ => values.push(expr.clone()),
                    }
                }
                Task::Callee(expr) => {
                    if let ExprNode::Const { name, .. } = expr.node() {
                        self.constructor(name)?;
                    }
                    values.push(expr);
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
                Task::MutualLambdas {
                    group,
                    selected,
                    signatures,
                } => {
                    let count = signatures.len();
                    let start = values
                        .len()
                        .checked_sub(count)
                        .ok_or_else(|| unsupported("mutual lambda result stack"))?;
                    let selected = values
                        .get(start + selected)
                        .ok_or_else(|| unsupported("mutual selected result"))?
                        .clone();
                    let members =
                        u16::try_from(count).map_err(|_| unsupported("mutual member count"))?;
                    for (index, (lambda, (parameters, result))) in
                        values.drain(start..).zip(signatures).enumerate()
                    {
                        self.tick()?;
                        reserve(&mut self.lambdas, self.limits.max_lambda_bindings)?;
                        self.lambdas.push(LambdaBinding {
                            lambda,
                            parameter_ownership: borrowed_runtime_parameters(parameters.len())?,
                            parameters,
                            result,
                            result_ownership: result_ownership(result),
                            recursion: LambdaRecursion::MutualMember {
                                group,
                                member: u16::try_from(index)
                                    .map_err(|_| unsupported("mutual member index"))?,
                                members,
                            },
                        });
                    }
                    values.push(selected);
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

    /// All members are prepared under their complete peer/argument telescopes
    /// before registration. The compiler creates their shared acyclic capture
    /// environment; preparation never recurses on the Rust stack for a fold.
    fn schedule_mutual_fold(
        &mut self,
        fold: mutual::Fold,
        tasks: &mut Vec<Task>,
        limit: usize,
    ) -> Result<(), IngressError> {
        let mut required = fold.arguments.len().saturating_add(2);
        let mut peers = Vec::new();
        let mut signatures = Vec::new();
        for member in &fold.members {
            self.tick()?;
            required = required
                .saturating_add(fold.members.len())
                .saturating_add(member.domains.len())
                .saturating_add(member.case.branches.len())
                .saturating_add(2);
            reserve(&mut peers, self.limits.max_context_depth)?;
            peers.push((member.name.clone(), member.self_type.clone()));
            reserve(&mut signatures, self.limits.max_lambda_bindings)?;
            signatures.push((member.parameters.clone(), member.case.result));
        }
        if tasks.len().saturating_add(required) > limit {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::PendingTasks,
                limit,
                observed: tasks.len().saturating_add(required),
            });
        }
        tasks
            .try_reserve(required)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::PendingTasks,
                requested: tasks.len().saturating_add(required),
            })?;
        tasks.push(Task::Apply(fold.arguments.len()));
        tasks.extend(fold.arguments.into_iter().rev().map(Task::Visit));
        tasks.push(Task::MutualLambdas {
            group: fold.group,
            selected: fold.selected,
            signatures,
        });
        for member in fold.members.into_iter().rev() {
            for (name, type_) in &peers {
                tasks.push(Task::Lam {
                    name: name.clone(),
                    type_: type_.clone(),
                    info: BinderInfo::Default,
                });
            }
            for domain in member.domains {
                tasks.push(Task::Lam {
                    name: Name::anonymous(),
                    type_: domain,
                    info: BinderInfo::Default,
                });
            }
            self.schedule_constructor_case(member.case, tasks, limit)?;
        }
        Ok(())
    }

    fn schedule_constructor_case(
        &mut self,
        case: variants::Case,
        tasks: &mut Vec<Task>,
        limit: usize,
    ) -> Result<(), IngressError> {
        let required = case.branches.len().saturating_add(2);
        if tasks.len().saturating_add(required) > limit {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::PendingTasks,
                limit,
                observed: tasks.len().saturating_add(required),
            });
        }
        tasks
            .try_reserve(required)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::PendingTasks,
                requested: tasks.len().saturating_add(required),
            })?;
        tasks.push(Task::ConstructorCase {
            name: case.name,
            result: case.result,
            branches: case.branches.len(),
        });
        tasks.extend(case.branches.into_iter().rev().map(Task::Visit));
        tasks.push(Task::Visit(case.major));
        Ok(())
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
            empty_cases: &self.empty_cases,
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

/// Purely syntactic template classification. Inspect the whole parameter
/// telescope: a static type/dictionary argument need not be its first binder.
/// This does not turn a compilation refusal into success. Every template is
/// still admitted, and each concrete evaluation must compile and execute.
pub(super) fn is_template(definition: &DefinitionVal) -> bool {
    if !definition.base.level_params.is_empty() {
        return true;
    }
    let mut type_ = &definition.base.type_;
    loop {
        match type_.node() {
            ExprNode::MData { expr, .. } => type_ = expr,
            ExprNode::Sort { .. } => return true,
            ExprNode::ForallE {
                binder_type,
                binder_info,
                body,
                ..
            } => {
                if *binder_info == BinderInfo::InstImplicit || type_constructor_kind(binder_type) {
                    return true;
                }
                type_ = body;
            }
            _ => return false,
        }
    }
}
fn type_constructor_kind(mut type_: &Expr) -> bool {
    loop {
        match type_.node() {
            ExprNode::MData { expr, .. } => type_ = expr,
            ExprNode::ForallE { body, .. } => type_ = body,
            ExprNode::Sort { .. } => return true,
            _ => return false,
        }
    }
}

#[cfg(test)]
mod templates;

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
            preparation.visited < 13_000,
            "projection discovery adds one linear pass, not a quadratic spine rewalk"
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
