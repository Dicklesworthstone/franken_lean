//! Checked source Thunks use the VM's existing memoized object representation.
//!
//! One raw ABI row serves each operation. Explicit typed adapters box stored
//! values and unbox forced results; closures retain their real interfaces.
use super::*;
use crate::source_intrinsics::thunks::{self, Operation};
use fln_comp::fir::EffectClass;
use fln_comp::flbc::{ArgumentOwnership, ResultOwnership};

const HANDLE: &str = "_fln_runtime_thunk_handle";
const PAYLOAD: &str = "_fln_runtime_thunk_payload";
const PRIMITIVES: [&str; 3] = [
    "_fln_runtime_thunk_mk",
    "_fln_runtime_thunk_pure",
    "_fln_runtime_thunk_get",
];

#[derive(Default)]
pub(super) struct Store {
    family: Option<bool>,
    operations: [bool; 3],
    projection: bool,
    next: u64,
    bindings: [Option<(IntrinsicBinding, Expr)>; 3],
    payloads: std::collections::HashMap<Expr, Name>,
    recoveries: BTreeMap<Name, (Expr, ValueType)>,
}

fn c(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}

fn b(index: u32) -> Result<Expr, IngressError> {
    Expr::bvar(index).map_err(|_| unsupported("Thunk adapter binder scope"))
}

fn function(domain: Expr, result: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, result, BinderInfo::Default)
}

impl Preparation<'_> {
    pub(super) fn thunk_function_type(&self, requested: &Name) -> Option<Expr> {
        self.thunks
            .recoveries
            .get(requested)
            .map(|(type_, _)| type_.clone())
    }

    pub(crate) fn thunk_function_signature(
        &self,
        requested: &Name,
    ) -> Result<Option<ExecutableSignature>, IngressError> {
        let Some((_, result)) = self.thunks.recoveries.get(requested) else {
            return Ok(None);
        };
        // A compiler-private function result is a real ABI boundary. A source
        // let annotation alone is not one: ingress intentionally derives its
        // value class from the initializer. Keep the proved payload class here
        // so ordinary ingress emits its checked Unbox before any field read or
        // closure application. The logical environment receives no declaration.
        Ok(Some(ExecutableSignature {
            parameters: vec![ValueType::Abi],
            result: *result,
            result_ownership: result_ownership(*result),
            body: b(0)?,
        }))
    }

    pub(crate) fn thunk_intrinsic_binding(&self, requested: &Name) -> Option<IntrinsicBinding> {
        self.thunks
            .bindings
            .iter()
            .flatten()
            .find(|(binding, _)| &binding.name == requested)
            .map(|(binding, _)| binding.clone())
    }

    pub(super) fn thunk_intrinsic_type(&self, requested: &Name) -> Option<Expr> {
        self.thunks
            .bindings
            .iter()
            .flatten()
            .find(|(binding, _)| &binding.name == requested)
            .map(|(_, type_)| type_.clone())
    }

    fn thunk_name(&mut self) -> Result<Name, IngressError> {
        self.tick()?;
        let id = self.thunks.next;
        self.thunks.next = id
            .checked_add(1)
            .ok_or_else(|| unsupported("Thunk adapter identity"))?;
        let private = Name::num(name("_fln_runtime_thunk_scope"), id);
        if self.environment.contains(&private) {
            return Err(unsupported("Thunk adapter name collision"));
        }
        Ok(private)
    }

    fn thunk_family(&mut self) -> Result<bool, IngressError> {
        self.tick()?;
        if let Some(checked) = self.thunks.family {
            return Ok(checked);
        }
        let checked = thunks::family_matches(
            self.environment,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        self.thunks.family = Some(checked);
        Ok(checked)
    }

    pub(super) fn thunk_record_forbidden(&mut self, family: &Name) -> Result<bool, IngressError> {
        Ok(family == &name("Thunk") && self.thunk_family()?)
    }

    fn thunk_representation(
        &mut self,
        type_: Expr,
        value: ValueType,
        ownership: CallableResultOwnership,
    ) -> Result<(), IngressError> {
        self.tick()?;
        let expected = (value, ownership);
        if let Some(existing) = self.value_types.native.get(&type_) {
            if *existing != expected {
                return Err(unsupported("Thunk runtime representation conflict"));
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

    /// Keep the logical type as the key so source projection inference still
    /// knows its payload. The native object has no ordinary record field.
    /// Payload layout is proved separately before constructing or forcing it.
    pub(super) fn thunk_value_type(&mut self, source: &Expr) -> Result<bool, IngressError> {
        let (head, arguments) = self.spine(source)?;
        if !matches!(head.node(), ExprNode::Const { name: family, levels }
            if family == &name("Thunk") && levels.len() == 1)
            || arguments.len() != 1
            || !specialize::closed(source)
            || !self.thunk_family()?
        {
            return Ok(false);
        }
        self.thunk_representation(
            source.clone(),
            ValueType::Thunk,
            CallableResultOwnership::Owned,
        )?;
        Ok(true)
    }

    fn thunk_primitive(&mut self, operation: Operation) -> Result<Option<Expr>, IngressError> {
        let index = operation as usize;
        if let Some((binding, _)) = &self.thunks.bindings[index] {
            return Ok(Some(Expr::const_(binding.name.clone(), vec![])));
        }
        if !self.thunks.operations[index] {
            if !thunks::operation_matches(
                self.environment,
                operation,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )? {
                return Ok(None);
            }
            self.thunks.operations[index] = true;
            self.thunks.family = Some(true);
        }
        for label in [HANDLE, PAYLOAD, PRIMITIVES[index]] {
            if self.environment.contains(&name(label)) {
                return Err(unsupported("Thunk private name collision"));
            }
        }
        self.thunk_representation(c(HANDLE), ValueType::Thunk, CallableResultOwnership::Owned)?;
        self.thunk_representation(c(PAYLOAD), ValueType::Abi, CallableResultOwnership::Erased)?;
        let (source_kind, symbol) = match operation {
            Operation::New => ("ctor", "lean_mk_thunk"),
            Operation::Pure => ("defn", "lean_thunk_pure"),
            Operation::Get => ("defn", "lean_thunk_get_own"),
        };
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.name == operation.label())
            .ok_or_else(|| unsupported("generated Thunk extern row"))?;
        if row.kind != source_kind
            || row.module != "Init.Core"
            || row.levels != 1
            || row.arity != 2
            || row.symbol != symbol
            || row.effect != "pure"
            || row.safety != "safe"
        {
            return Err(unsupported("generated Thunk ABI contract"));
        }
        let ownership = fln_vm::extern_row::Ownership::parse(row.ownership)
            .map_err(|_| unsupported("generated Thunk ownership contract"))?;
        let expected_argument = if operation == Operation::Get {
            fln_vm::extern_row::ArgumentOwnership::Borrowed
        } else {
            fln_vm::extern_row::ArgumentOwnership::Owned
        };
        if ownership
            .argument_ownership(1)
            .map_err(|_| unsupported("generated Thunk argument ownership"))?
            != [expected_argument]
            || ownership
                .result_ownership()
                .map_err(|_| unsupported("generated Thunk result ownership"))?
                != fln_vm::extern_row::ResultOwnership::Owned
        {
            return Err(unsupported("generated Thunk ownership contract"));
        }
        let (domain, result_type, result) = match operation {
            // The callback's real telescope includes the payload arguments.
            // A single raw object row accepts these independently validated
            // closure interfaces; the VM still requires a Golem closure shell.
            Operation::New => (c(PAYLOAD), c(HANDLE), ValueType::Thunk),
            Operation::Pure => (c(PAYLOAD), c(HANDLE), ValueType::Thunk),
            Operation::Get => (c(HANDLE), c(PAYLOAD), ValueType::Abi),
        };
        let argument = self
            .value_type(&domain)?
            .ok_or_else(|| unsupported("Thunk ABI argument representation"))?;
        let private = name(PRIMITIVES[index]);
        self.thunks.bindings[index] = Some((
            IntrinsicBinding {
                name: private.clone(),
                universe_arity: 0,
                row: row.id.to_owned(),
                arguments: vec![argument],
                argument_ownership: vec![if operation == Operation::Get {
                    ArgumentOwnership::Borrowed
                } else {
                    ArgumentOwnership::Owned
                }],
                result,
                result_ownership: ResultOwnership::Owned,
                effect: EffectClass::State,
            },
            function(domain, result_type),
        ));
        Ok(Some(Expr::const_(private, vec![])))
    }

    fn thunk_typed(&mut self, value: Expr, type_: Expr) -> Result<Expr, IngressError> {
        Ok(Expr::let_e(self.thunk_name()?, type_, value, b(0)?, false))
    }

    fn thunk_payload(&mut self, source: &Expr) -> Result<Expr, IngressError> {
        let payload = self.erase_runtime_type(source)?;
        if !specialize::closed(&payload) || self.value_type(&payload)?.is_none() {
            return Err(unsupported("Thunk payload representation"));
        }
        Ok(payload)
    }

    fn thunk_recover(&mut self, value: Expr, payload: &Expr) -> Result<Expr, IngressError> {
        self.tick()?;
        let private = if let Some(known) = self.thunks.payloads.get(payload) {
            known.clone()
        } else {
            let result = self
                .value_type(payload)?
                .ok_or_else(|| unsupported("Thunk recovered payload representation"))?;
            let observed = self.thunks.payloads.len().saturating_add(1);
            let limit = self.limits.fir.max_functions.saturating_sub(1);
            if observed > limit {
                return Err(IngressError::ResourceLimit {
                    resource: IngressResource::ProgramTables,
                    limit,
                    observed,
                });
            }
            self.thunks
                .payloads
                .try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: observed,
                })?;
            let private = self.thunk_name()?;
            self.thunks.recoveries.insert(
                private.clone(),
                (function(c(PAYLOAD), payload.clone()), result),
            );
            self.thunks
                .payloads
                .insert(payload.clone(), private.clone());
            private
        };
        self.thunk_typed(
            Expr::app(Expr::const_(private, vec![]), value),
            payload.clone(),
        )
    }

    fn thunk_delayed_callback(&mut self, unit: Expr, payload: &Expr) -> Result<Expr, IngressError> {
        let mut remaining = self.normalize_type(payload)?;
        let mut parameters = Vec::new();
        while let ExprNode::ForallE {
            binder_type, body, ..
        } = remaining.node()
        {
            self.tick()?;
            if !specialize::closed(binder_type) || !specialize::closed(body) {
                return Err(unsupported("dependent Thunk callable payload"));
            }
            reserve(&mut parameters, self.limits.max_context_depth)?;
            parameters.push(binder_type.clone());
            remaining = body.clone();
        }
        // The pinned compiler eta-expands a callback to its checked arrow
        // telescope, even when its source lambda first computes a function.
        // Keep that convention: forcing supplies only Unit and caches the
        // resulting partial application. Its body runs when the remaining
        // payload arguments arrive. The callback expression itself is still
        // captured strictly once by the outer mk wrapper.
        let depth = u32::try_from(parameters.len())
            .ok()
            .and_then(|n| n.checked_add(1))
            .ok_or_else(|| unsupported("Thunk callback parameter scope"))?;
        let mut delayed = Expr::app(b(depth)?, unit);
        for index in (0..parameters.len()).rev() {
            self.tick()?;
            delayed = Expr::app(delayed, b(index as u32)?);
        }
        for parameter in parameters.into_iter().rev() {
            self.tick()?;
            delayed = Expr::lam(self.thunk_name()?, parameter, delayed, BinderInfo::Default);
        }
        delayed = Expr::lam(self.thunk_name()?, c("Nat"), delayed, BinderInfo::Default);
        // Preserve the concrete terminal result, including callable ownership;
        // an erased result would give the cached partial application a different
        // interface from the payload recovered by get.
        self.thunk_typed(delayed, function(c("Nat"), payload.clone()))
    }

    fn thunk_getter(&mut self, family: Expr, payload: Expr) -> Result<Option<Expr>, IngressError> {
        let Some(get) = self.thunk_primitive(Operation::Get)? else {
            return Ok(None);
        };
        let unit = self.erase_runtime_type(&c("Unit"))?;
        self.value_type(&unit)?
            .ok_or_else(|| unsupported("Thunk Unit representation"))?;
        // The Unit argument is a real strict call argument. Ignore its value,
        // then force the captured Thunk. A cached callable remains a value;
        // forcing itself supplies none of the payload's arguments.
        let value = self.thunk_recover(Expr::app(get, b(1)?), &payload)?;
        let getter_type = function(unit.clone(), payload);
        let getter = Expr::lam(self.thunk_name()?, unit, value, BinderInfo::Default);
        let getter = self.thunk_typed(getter, getter_type.clone())?;
        let factory = Expr::lam(
            self.thunk_name()?,
            family.clone(),
            getter,
            BinderInfo::Default,
        );
        self.thunk_typed(factory, function(family, getter_type))
            .map(Some)
    }

    /// Return a typed factory to apply once to the original receiver. This
    /// permits lexical projection lowering to transform the receiver first,
    /// without duplicating it or visiting a synthetic binder in the old scope.
    pub(super) fn thunk_projection_factory(
        &mut self,
        receiver_type: &Expr,
        structure: &Name,
        index: u64,
    ) -> Result<Option<Expr>, IngressError> {
        if structure != &name("Thunk") || !self.thunk_family()? {
            return Ok(None);
        }
        if index != 0 {
            return Err(unsupported("Thunk projection field index"));
        }
        if !self.thunks.projection {
            if !thunks::projection_matches(
                self.environment,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )? {
                return Ok(None);
            }
            self.thunks.projection = true;
        }
        let family = self.normalize_type(receiver_type)?;
        let (head, args) = self.spine(&family)?;
        if !matches!(head.node(), ExprNode::Const { name: family, levels }
            if family == &name("Thunk") && levels.len() == 1)
            || args.len() != 1
            || !self.thunk_value_type(&family)?
        {
            return Err(unsupported("Thunk projection receiver type"));
        }
        let payload = self.thunk_payload(&args[0])?;
        self.thunk_getter(family, payload)
    }

    pub(super) fn thunk_call(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const {
            name: requested,
            levels,
        } = head.node()
        else {
            return Ok(None);
        };
        if args.len() > 1
            && levels.is_empty()
            && let Some((type_, _)) = self.thunks.recoveries.get(requested)
        {
            let ExprNode::ForallE { body: payload, .. } = type_.node() else {
                return Err(unsupported("Thunk recovery signature"));
            };
            let payload = payload.clone();
            let mut body = b(0)?;
            for argument in &args[1..] {
                self.tick()?;
                body = Expr::app(body, self.lift(argument, 1)?);
            }
            // This identity consumes one raw value and returns its recovered
            // callable. Preserve that prefix before applying source operands;
            // flattening them into the private call loses its ABI boundary.
            return Ok(Some(Expr::let_e(
                self.thunk_name()?,
                payload,
                Expr::app(head.clone(), args[0].clone()),
                body,
                false,
            )));
        }
        if requested == &name("Thunk.rec") {
            return self.thunk_recursor(levels, args);
        }
        if requested == &name("Thunk.fn") {
            let ([_], [alpha, rest @ ..]) = (levels.as_slice(), args) else {
                return Ok(None);
            };
            let family = Expr::app(Expr::const_(name("Thunk"), levels.clone()), alpha.clone());
            let Some(factory) = self.thunk_projection_factory(&family, &name("Thunk"), 0)? else {
                return Ok(None);
            };
            return Ok(Some(rest.iter().cloned().fold(factory, Expr::app)));
        }
        let Some(operation) = Operation::from_name(requested) else {
            return Ok(None);
        };
        let Some(primitive) = self.thunk_primitive(operation)? else {
            return Ok(None);
        };
        let ([_], [alpha, rest @ ..]) = (levels.as_slice(), args) else {
            return Ok(None);
        };
        let payload = self.thunk_payload(alpha)?;
        let family = Expr::app(Expr::const_(name("Thunk"), levels.clone()), payload.clone());
        if !self.thunk_value_type(&family)? {
            return Err(unsupported("Thunk runtime family"));
        }
        let (domain, result, body) = match operation {
            Operation::New => {
                let unit = self.erase_runtime_type(&c("Unit"))?;
                let shape = self
                    .record_shape(&unit)?
                    .ok_or_else(|| unsupported("Thunk Unit record"))?;
                let [constructor] = shape.constructors.as_slice() else {
                    return Err(unsupported("Thunk Unit constructor"));
                };
                if constructor.tag != 0
                    || !constructor.fields.is_empty()
                    || !constructor.type_fields.is_empty()
                {
                    return Err(unsupported("Thunk Unit representation"));
                }
                // Native forcing supplies the raw Unit value. Calling its
                // source alias could execute an unrelated implemented_by
                // replacement. The checked private layout supplies the same
                // zero-field value without selecting another source body.
                let unit_value = Expr::const_(constructor.name.clone(), vec![]);
                let callback = function(unit, payload.clone());
                self.value_type(&callback)?
                    .ok_or_else(|| unsupported("Thunk callback representation"))?;
                let delayed = self.thunk_delayed_callback(unit_value, &payload)?;
                (callback, family, Expr::app(primitive, delayed))
            }
            Operation::Pure => (payload, family, Expr::app(primitive, b(0)?)),
            Operation::Get => {
                let body = self.thunk_recover(Expr::app(primitive, b(0)?), &payload)?;
                (family, payload, body)
            }
        };
        let wrapper = Expr::lam(
            self.thunk_name()?,
            domain.clone(),
            body,
            BinderInfo::Default,
        );
        let wrapper = self.thunk_typed(wrapper, function(domain, result))?;
        Ok(Some(rest.iter().cloned().fold(wrapper, Expr::app)))
    }

    fn thunk_recursor(
        &mut self,
        levels: &[Level],
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ([_, payload_level], [alpha, motive, minor, major]) = (levels, args) else {
            return Ok(None);
        };
        if !self.thunk_family()? {
            return Ok(None);
        }
        source_intrinsics::check_selected_extern_attribute(
            self.environment,
            &name("Thunk.rec"),
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        let payload = self.thunk_payload(alpha)?;
        let family = Expr::app(
            Expr::const_(name("Thunk"), vec![payload_level.clone()]),
            payload.clone(),
        );
        if !self.thunk_value_type(&family)? {
            return Err(unsupported("Thunk recursor family"));
        }
        let motive = self.erase_type_argument(motive, &[])?;
        let motive = self
            .indexed_motive(&motive, &[], &family)?
            .ok_or_else(|| unsupported("dependent Thunk recursor result"))?;
        let result = self
            .value_type(&motive)?
            .ok_or_else(|| unsupported("Thunk recursor result representation"))?;
        let unit = self.erase_runtime_type(&c("Unit"))?;
        let field_type = function(unit, payload.clone());
        let Some(getter) = self.thunk_getter(family.clone(), payload)? else {
            return Err(unsupported("Thunk recursor cached getter"));
        };
        let body = Expr::app(b(1)?, Expr::app(getter, b(0)?));
        let body = self.typed_callable_result(body, motive.clone(), result)?;
        let body = Expr::let_e(
            self.thunk_name()?,
            family,
            self.lift(major, 1)?,
            body,
            false,
        );
        // Preserve strict evaluation order of computed minor and major
        // arguments, including a minor that ignores its cached getter.
        Ok(Some(Expr::let_e(
            self.thunk_name()?,
            function(field_type, motive),
            minor.clone(),
            body,
            false,
        )))
    }
}
