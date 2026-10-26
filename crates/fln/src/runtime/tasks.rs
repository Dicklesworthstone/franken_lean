//! Checked source Tasks share Golem's existing native task representation.
//!
//! The VM currently runs task callbacks through its managerless continuation
//! path: an invoked asTask action completes its callback synchronously and
//! produces a finished task. Waiting preserves the existing refusal of other
//! task states. This bridge adds no scheduler or background execution.
//! Constructing an ordinary BaseIO action performs no task operation.

use super::*;
use crate::source_intrinsics::tasks::{self, Operation};
use fln_comp::fir::EffectClass;
use fln_comp::flbc::{ArgumentOwnership, ResultOwnership};

const HANDLE: &str = "_fln_runtime_task_handle";
const PAYLOAD: &str = "_fln_runtime_task_payload";
const PRIMITIVES: [&str; 6] = [
    "_fln_runtime_task_pure",
    "_fln_runtime_task_get",
    "_fln_runtime_task_as_task",
    "_fln_runtime_task_wait",
    "_fln_runtime_task_map_task",
    "_fln_runtime_task_bind_task",
];

#[derive(Default)]
pub(super) struct Store {
    family: Option<bool>,
    operations: [bool; 6],
    next: u64,
    bindings: [Option<(IntrinsicBinding, Expr)>; 6],
    payloads: std::collections::HashMap<Expr, Name>,
    recoveries: BTreeMap<Name, (Expr, ValueType)>,
}

fn c(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}

fn b(index: u32) -> Result<Expr, IngressError> {
    Expr::bvar(index).map_err(|_| unsupported("Task adapter binder scope"))
}

fn function(domain: Expr, result: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, result, BinderInfo::Default)
}

fn apply(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

fn out_type(payload: Expr) -> Expr {
    apply(c("ST.Out"), [c("IO.RealWorld"), payload])
}

fn out(payload: Expr, value: Expr, world: Expr) -> Expr {
    apply(c("ST.Out.mk"), [c("IO.RealWorld"), payload, value, world])
}

impl Preparation<'_> {
    pub(super) fn task_function_type(&self, requested: &Name) -> Option<Expr> {
        self.tasks
            .recoveries
            .get(requested)
            .map(|(type_, _)| type_.clone())
    }

    pub(crate) fn task_function_signature(
        &self,
        requested: &Name,
    ) -> Result<Option<ExecutableSignature>, IngressError> {
        let Some((_, result)) = self.tasks.recoveries.get(requested) else {
            return Ok(None);
        };
        // This private function is the checked ABI boundary that recovers an
        // owned payload's concrete value class before projection or application.
        Ok(Some(ExecutableSignature {
            parameters: vec![ValueType::Abi],
            result: *result,
            result_ownership: result_ownership(*result),
            body: b(0)?,
        }))
    }

    pub(crate) fn task_intrinsic_binding(&self, requested: &Name) -> Option<IntrinsicBinding> {
        self.tasks
            .bindings
            .iter()
            .flatten()
            .find(|(binding, _)| &binding.name == requested)
            .map(|(binding, _)| binding.clone())
    }

    pub(super) fn task_intrinsic_type(&self, requested: &Name) -> Option<Expr> {
        self.tasks
            .bindings
            .iter()
            .flatten()
            .find(|(binding, _)| &binding.name == requested)
            .map(|(_, type_)| type_.clone())
    }

    fn task_name(&mut self) -> Result<Name, IngressError> {
        self.tick()?;
        let id = self.tasks.next;
        self.tasks.next = id
            .checked_add(1)
            .ok_or_else(|| unsupported("Task adapter identity"))?;
        let private = Name::num(name("_fln_runtime_task_scope"), id);
        if self.environment.contains(&private) {
            return Err(unsupported("Task adapter name collision"));
        }
        Ok(private)
    }

    fn task_family(&mut self) -> Result<bool, IngressError> {
        self.tick()?;
        if let Some(checked) = self.tasks.family {
            return Ok(checked);
        }
        let checked = tasks::family_matches(
            self.environment,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        self.tasks.family = Some(checked);
        Ok(checked)
    }

    pub(super) fn task_record_forbidden(&mut self, family: &Name) -> Result<bool, IngressError> {
        Ok(family == &name("Task") && self.task_family()?)
    }

    fn task_representation(
        &mut self,
        type_: Expr,
        value: ValueType,
        ownership: CallableResultOwnership,
    ) -> Result<(), IngressError> {
        self.tick()?;
        let expected = (value, ownership);
        if let Some(existing) = self.value_types.native.get(&type_) {
            if *existing != expected {
                return Err(unsupported("Task runtime representation conflict"));
            }
            return Ok(());
        }
        let observed = self.value_types.native.len().saturating_add(1);
        if observed > self.limits.max_nodes {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ProgramTables,
                limit: self.limits.max_nodes,
                observed,
            });
        }
        self.value_types
            .native
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: observed,
            })?;
        self.value_types.native.insert(type_, expected);
        Ok(())
    }

    pub(super) fn task_value_type(&mut self, source: &Expr) -> Result<bool, IngressError> {
        let (head, arguments) = self.spine(source)?;
        if !matches!(head.node(), ExprNode::Const { name: family, levels }
            if family == &name("Task") && levels.len() == 1)
            || arguments.len() != 1
            || !specialize::closed(source)
            || !self.task_family()?
        {
            return Ok(false);
        }
        // Retain the logical type as the key so projection inference can
        // recover its payload, while the physical object remains a Task.
        self.task_representation(
            source.clone(),
            ValueType::Task,
            CallableResultOwnership::Owned,
        )?;
        Ok(true)
    }

    fn task_primitive(&mut self, operation: Operation) -> Result<Option<Expr>, IngressError> {
        let index = operation as usize;
        if let Some((binding, _)) = &self.tasks.bindings[index] {
            return Ok(Some(Expr::const_(binding.name.clone(), vec![])));
        }
        if !self.tasks.operations[index] {
            if !tasks::operation_matches(
                self.environment,
                operation,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )? {
                return Ok(None);
            }
            self.tasks.operations[index] = true;
            self.tasks.family = Some(true);
        }
        for label in [HANDLE, PAYLOAD, PRIMITIVES[index]] {
            if self.environment.contains(&name(label)) {
                return Err(unsupported("Task private name collision"));
            }
        }
        self.task_representation(c(HANDLE), ValueType::Task, CallableResultOwnership::Owned)?;
        self.task_representation(c(PAYLOAD), ValueType::Abi, CallableResultOwnership::Erased)?;
        let (kind, module, levels, arity, symbol, effect) = match operation {
            Operation::Pure => ("ctor", "Init.Core", 1, 2, "lean_task_pure", "task"),
            Operation::Get => ("defn", "Init.Core", 1, 2, "lean_task_get_own", "pure"),
            Operation::AsTask => ("opaque", "Init.System.IO", 0, 3, "lean_io_as_task", "io"),
            Operation::Wait => ("opaque", "Init.System.IO", 0, 2, "lean_io_wait", "io"),
            Operation::MapTask => ("opaque", "Init.System.IO", 1, 6, "lean_io_map_task", "io"),
            Operation::BindTask => ("opaque", "Init.System.IO", 1, 6, "lean_io_bind_task", "io"),
        };
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.name == operation.label())
            .ok_or_else(|| unsupported("generated Task extern row"))?;
        if row.kind != kind
            || row.module != module
            || row.levels != levels
            || row.arity != arity
            || row.symbol != symbol
            || row.effect != effect
            || row.safety != "safe"
        {
            return Err(unsupported("generated Task ABI contract"));
        }
        let (domains, result_type, result) = match operation {
            Operation::Pure => (vec![c(PAYLOAD)], c(HANDLE), ValueType::Task),
            Operation::Get | Operation::Wait => (vec![c(HANDLE)], c(PAYLOAD), ValueType::Abi),
            Operation::AsTask => (vec![c(PAYLOAD), c("Nat")], c(HANDLE), ValueType::Task),
            Operation::MapTask => (
                vec![c(PAYLOAD), c(HANDLE), c("Nat"), c("Bool")],
                c(HANDLE),
                ValueType::Task,
            ),
            Operation::BindTask => (
                vec![c(HANDLE), c(PAYLOAD), c("Nat"), c("Bool")],
                c(HANDLE),
                ValueType::Task,
            ),
        };
        let mut arguments = Vec::new();
        for domain in &domains {
            arguments.push(
                self.value_type(domain)?
                    .ok_or_else(|| unsupported("Task ABI argument representation"))?,
            );
        }
        let ownership = fln_vm::extern_row::Ownership::parse(row.ownership)
            .map_err(|_| unsupported("generated Task ownership contract"))?;
        let argument_ownership = ownership
            .argument_ownership(arguments.len())
            .map_err(|_| unsupported("generated Task argument ownership"))?
            .into_iter()
            .map(|ownership| match ownership {
                fln_vm::extern_row::ArgumentOwnership::Borrowed => ArgumentOwnership::Borrowed,
                fln_vm::extern_row::ArgumentOwnership::Owned => ArgumentOwnership::Owned,
                fln_vm::extern_row::ArgumentOwnership::Unique => ArgumentOwnership::Unique,
                fln_vm::extern_row::ArgumentOwnership::Scalar => ArgumentOwnership::Scalar,
            })
            .collect();
        if ownership
            .result_ownership()
            .map_err(|_| unsupported("generated Task result ownership"))?
            != fln_vm::extern_row::ResultOwnership::Owned
        {
            return Err(unsupported("generated Task result ownership"));
        }
        let type_ = domains
            .into_iter()
            .rev()
            .fold(result_type, |body, domain| function(domain, body));
        let private = name(PRIMITIVES[index]);
        self.tasks.bindings[index] = Some((
            IntrinsicBinding {
                name: private.clone(),
                universe_arity: 0,
                row: row.id.to_owned(),
                arguments,
                argument_ownership,
                result,
                result_ownership: ResultOwnership::Owned,
                effect: if matches!(
                    operation,
                    Operation::AsTask | Operation::Wait | Operation::MapTask | Operation::BindTask
                ) {
                    EffectClass::Io
                } else {
                    EffectClass::Task
                },
            },
            type_,
        ));
        Ok(Some(Expr::const_(private, vec![])))
    }

    fn task_typed(&mut self, value: Expr, type_: Expr) -> Result<Expr, IngressError> {
        Ok(Expr::let_e(self.task_name()?, type_, value, b(0)?, false))
    }

    fn task_payload(&mut self, source: &Expr) -> Result<Expr, IngressError> {
        let payload = self.erase_runtime_type(source)?;
        if !specialize::closed(&payload) || self.value_type(&payload)?.is_none() {
            return Err(unsupported("Task payload representation"));
        }
        Ok(payload)
    }

    fn task_recover(&mut self, value: Expr, payload: &Expr) -> Result<Expr, IngressError> {
        self.tick()?;
        let private = if let Some(known) = self.tasks.payloads.get(payload) {
            known.clone()
        } else {
            let result = self
                .value_type(payload)?
                .ok_or_else(|| unsupported("Task recovered payload representation"))?;
            let observed = self.tasks.payloads.len().saturating_add(1);
            let limit = self.limits.fir.max_functions.saturating_sub(1);
            if observed > limit {
                return Err(IngressError::ResourceLimit {
                    resource: IngressResource::ProgramTables,
                    limit,
                    observed,
                });
            }
            self.tasks
                .payloads
                .try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: observed,
                })?;
            let private = self.task_name()?;
            self.tasks.recoveries.insert(
                private.clone(),
                (function(c(PAYLOAD), payload.clone()), result),
            );
            self.tasks.payloads.insert(payload.clone(), private.clone());
            private
        };
        self.task_typed(
            Expr::app(Expr::const_(private, vec![]), value),
            payload.clone(),
        )
    }

    fn task_getter(&mut self, family: Expr, payload: Expr) -> Result<Option<Expr>, IngressError> {
        let Some(get) = self.task_primitive(Operation::Get)? else {
            return Ok(None);
        };
        let value = self.task_recover(Expr::app(get, b(0)?), &payload)?;
        let getter = Expr::lam(
            self.task_name()?,
            family.clone(),
            value,
            BinderInfo::Default,
        );
        self.task_typed(getter, function(family, payload)).map(Some)
    }

    pub(super) fn task_projection_factory(
        &mut self,
        receiver_type: &Expr,
        structure: &Name,
        index: u64,
    ) -> Result<Option<Expr>, IngressError> {
        if structure != &name("Task") || !self.task_family()? {
            return Ok(None);
        }
        if index != 0 {
            return Err(unsupported("Task projection field index"));
        }
        let family = self.normalize_type(receiver_type)?;
        let (head, arguments) = self.spine(&family)?;
        if !matches!(head.node(), ExprNode::Const { name: family, levels }
            if family == &name("Task") && levels.len() == 1)
            || arguments.len() != 1
            || !self.task_value_type(&family)?
        {
            return Err(unsupported("Task projection receiver type"));
        }
        let payload = self.task_payload(&arguments[0])?;
        self.task_getter(family, payload)
    }

    fn task_io_wrapper(
        &mut self,
        operation: Operation,
        primitive: Expr,
        family: Expr,
        payload: Expr,
    ) -> Result<Expr, IngressError> {
        let world = self
            .st_evaluation_world()?
            .ok_or_else(|| unsupported("Task checked IO world"))?;
        let input_out = out_type(payload.clone());
        if self.value_type(&input_out)? != Some(ValueType::Constructor) {
            return Err(unsupported("Task checked action result representation"));
        }
        let (domains, body, result_type) = match operation {
            Operation::AsTask => {
                let shape = self
                    .record_shape(&input_out)?
                    .ok_or_else(|| unsupported("Task checked action result"))?;
                let [constructor] = shape.constructors.as_slice() else {
                    return Err(unsupported("Task checked action result constructor"));
                };
                if constructor.tag != 0
                    || constructor.fields.len() != 2
                    || constructor.type_fields != [false, false]
                {
                    return Err(unsupported("Task checked action result layout"));
                }
                // Within act/prio/world/token, use the checked captured world.
                // The VM token is a raw Nat and is not a source world value.
                let evaluated = Expr::app(b(3)?, b(1)?);
                let value = Expr::proj(shape.projection(constructor), 0, evaluated);
                let callback = Expr::lam(self.task_name()?, c("Nat"), value, BinderInfo::Default);
                // An ABI result keeps this callback unary even when the payload
                // is callable. Eta-expanding its payload would defer the IO
                // action until the returned function's arguments were supplied.
                let callback = self.task_typed(callback, function(c("Nat"), c(PAYLOAD)))?;
                let task = apply(primitive, [callback, b(1)?]);
                let body = out(family.clone(), task, b(0)?);
                (
                    vec![function(world.clone(), input_out), c("Nat"), world],
                    body,
                    out_type(family),
                )
            }
            Operation::Wait => {
                let value = self.task_recover(Expr::app(primitive, b(1)?), &payload)?;
                let body = out(payload.clone(), value, b(0)?);
                (vec![family, world], body, out_type(payload))
            }
            Operation::Pure | Operation::Get | Operation::MapTask | Operation::BindTask => {
                unreachable!("unary Task IO wrapper")
            }
        };
        if self.value_type(&result_type)? != Some(ValueType::Constructor) {
            return Err(unsupported("Task checked IO result representation"));
        }
        let mut wrapper = body;
        let mut type_ = result_type;
        for domain in domains.into_iter().rev() {
            self.tick()?;
            wrapper = Expr::lam(
                self.task_name()?,
                domain.clone(),
                wrapper,
                BinderInfo::Default,
            );
            type_ = function(domain, type_);
        }
        self.task_typed(wrapper, type_)
    }

    fn task_composition_wrapper(
        &mut self,
        operation: Operation,
        primitive: Expr,
        input_family: Expr,
        output_family: Expr,
        input: Expr,
        output: Expr,
    ) -> Result<Expr, IngressError> {
        let world = self
            .st_evaluation_world()?
            .ok_or_else(|| unsupported("Task checked IO world"))?;
        let callback_payload = if operation == Operation::MapTask {
            output
        } else {
            output_family.clone()
        };
        let callback_result = out_type(callback_payload);
        if self.value_type(&callback_result)? != Some(ValueType::Constructor) {
            return Err(unsupported("Task composition action result representation"));
        }
        let shape = self
            .record_shape(&callback_result)?
            .ok_or_else(|| unsupported("Task composition action result"))?;
        let [constructor] = shape.constructors.as_slice() else {
            return Err(unsupported("Task composition action result constructor"));
        };
        if constructor.tag != 0
            || constructor.fields.len() != 2
            || constructor.type_fields != [false, false]
        {
            return Err(unsupported("Task composition action result layout"));
        }
        // Within the five source arguments followed by rawValue/token, keep
        // the captured source world. The VM's token is a raw Nat.
        let callback_index = if operation == Operation::MapTask {
            6
        } else {
            5
        };
        let recovered = self.task_recover(b(1)?, &input)?;
        let evaluated = apply(b(callback_index)?, [recovered, b(2)?]);
        let value = Expr::proj(shape.projection(constructor), 0, evaluated);
        let callback = Expr::lam(
            self.task_name()?,
            c(PAYLOAD),
            Expr::lam(self.task_name()?, c("Nat"), value, BinderInfo::Default),
            BinderInfo::Default,
        );
        // The result remains boxed so a callable payload cannot add arguments
        // to the VM continuation or delay the IO action until application.
        let callback = self.task_typed(
            callback,
            function(c(PAYLOAD), function(c("Nat"), c(PAYLOAD))),
        )?;
        let (source_domains, primitive_arguments) = if operation == Operation::MapTask {
            (
                vec![
                    function(input, function(world.clone(), callback_result)),
                    input_family,
                    c("Nat"),
                    c("Bool"),
                    world,
                ],
                vec![callback, b(3)?, b(2)?, b(1)?],
            )
        } else {
            (
                vec![
                    input_family,
                    function(input, function(world.clone(), callback_result)),
                    c("Nat"),
                    c("Bool"),
                    world,
                ],
                vec![b(4)?, callback, b(2)?, b(1)?],
            )
        };
        let task = apply(primitive, primitive_arguments);
        let mut wrapper = out(output_family.clone(), task, b(0)?);
        let mut type_ = out_type(output_family);
        if self.value_type(&type_)? != Some(ValueType::Constructor) {
            return Err(unsupported("Task composition IO result representation"));
        }
        for domain in source_domains.into_iter().rev() {
            self.tick()?;
            wrapper = Expr::lam(
                self.task_name()?,
                domain.clone(),
                wrapper,
                BinderInfo::Default,
            );
            type_ = function(domain, type_);
        }
        self.task_typed(wrapper, type_)
    }

    fn task_composition_call(
        &mut self,
        operation: Operation,
        levels: &[Level],
        arguments: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ([input_level], [alpha, beta, rest @ ..]) = (levels, arguments) else {
            return Ok(None);
        };
        let Some(primitive) = self.task_primitive(operation)? else {
            return Ok(None);
        };
        let input = self.task_payload(alpha)?;
        let output = self.task_payload(beta)?;
        let input_family = Expr::app(
            Expr::const_(name("Task"), vec![input_level.clone()]),
            input.clone(),
        );
        let output_family = Expr::app(
            Expr::const_(name("Task"), vec![Level::zero()]),
            output.clone(),
        );
        if !self.task_value_type(&input_family)? || !self.task_value_type(&output_family)? {
            return Err(unsupported("Task composition runtime family"));
        }
        let wrapper = self.task_composition_wrapper(
            operation,
            primitive,
            input_family,
            output_family,
            input,
            output,
        )?;
        Ok(Some(rest.iter().cloned().fold(wrapper, Expr::app)))
    }

    pub(super) fn task_call(
        &mut self,
        head: &Expr,
        arguments: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const {
            name: requested,
            levels,
        } = head.node()
        else {
            return Ok(None);
        };
        if arguments.len() > 1
            && levels.is_empty()
            && let Some((type_, _)) = self.tasks.recoveries.get(requested)
        {
            let ExprNode::ForallE { body: payload, .. } = type_.node() else {
                return Err(unsupported("Task recovery signature"));
            };
            let payload = payload.clone();
            let mut body = b(0)?;
            for argument in &arguments[1..] {
                self.tick()?;
                body = Expr::app(body, self.lift(argument, 1)?);
            }
            return Ok(Some(Expr::let_e(
                self.task_name()?,
                payload,
                Expr::app(head.clone(), arguments[0].clone()),
                body,
                false,
            )));
        }
        if requested == &name("Task.rec") {
            return self.task_recursor(levels, arguments);
        }
        let Some(operation) = Operation::from_name(requested) else {
            return Ok(None);
        };
        if matches!(operation, Operation::MapTask | Operation::BindTask) {
            return self.task_composition_call(operation, levels, arguments);
        }
        let expected_levels = usize::from(matches!(operation, Operation::Pure | Operation::Get));
        let [alpha, rest @ ..] = arguments else {
            return Ok(None);
        };
        if levels.len() != expected_levels {
            return Ok(None);
        }
        let Some(primitive) = self.task_primitive(operation)? else {
            return Ok(None);
        };
        let payload = self.task_payload(alpha)?;
        let universe = levels.first().cloned().unwrap_or_else(Level::zero);
        let family = Expr::app(Expr::const_(name("Task"), vec![universe]), payload.clone());
        if !self.task_value_type(&family)? {
            return Err(unsupported("Task runtime family"));
        }
        let wrapper = match operation {
            Operation::AsTask | Operation::Wait => {
                self.task_io_wrapper(operation, primitive, family, payload)?
            }
            Operation::Pure | Operation::Get => {
                let (domain, result, body) = if operation == Operation::Pure {
                    (payload, family, Expr::app(primitive, b(0)?))
                } else {
                    let value = self.task_recover(Expr::app(primitive, b(0)?), &payload)?;
                    (family, payload, value)
                };
                let wrapper =
                    Expr::lam(self.task_name()?, domain.clone(), body, BinderInfo::Default);
                self.task_typed(wrapper, function(domain, result))?
            }
            Operation::MapTask | Operation::BindTask => unreachable!("Task composition dispatched"),
        };
        Ok(Some(rest.iter().cloned().fold(wrapper, Expr::app)))
    }

    fn task_recursor(
        &mut self,
        levels: &[Level],
        arguments: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ([_, payload_level], [alpha, motive, minor, major]) = (levels, arguments) else {
            return Ok(None);
        };
        if !self.task_family()? {
            return Ok(None);
        }
        source_intrinsics::check_selected_extern_attribute(
            self.environment,
            &name("Task.rec"),
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        let payload = self.task_payload(alpha)?;
        let family = Expr::app(
            Expr::const_(name("Task"), vec![payload_level.clone()]),
            payload.clone(),
        );
        if !self.task_value_type(&family)? {
            return Err(unsupported("Task recursor family"));
        }
        let motive = self.erase_type_argument(motive, &[])?;
        let motive = self
            .indexed_motive(&motive, &[], &family)?
            .ok_or_else(|| unsupported("dependent Task recursor result"))?;
        let result = self
            .value_type(&motive)?
            .ok_or_else(|| unsupported("Task recursor result representation"))?;
        let Some(getter) = self.task_getter(family.clone(), payload.clone())? else {
            return Err(unsupported("Task recursor getter"));
        };
        let body = Expr::app(b(1)?, Expr::app(getter, b(0)?));
        let body = self.typed_callable_result(body, motive.clone(), result)?;
        let body = Expr::let_e(self.task_name()?, family, self.lift(major, 1)?, body, false);
        // Evaluate a computed minor and major once, in their source order.
        Ok(Some(Expr::let_e(
            self.task_name()?,
            function(payload, motive),
            minor.clone(),
            body,
            false,
        )))
    }
}
