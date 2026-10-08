//! Logical ST actions over the VM's existing reference objects.
//!
//! The generated extern contracts describe bare VM cell operations. Their
//! results are wrapped in the admitted `ST.Out` data family here; they are not
//! interpreted as the Reference's packed `lean_io_result`. All bridges are
//! selected only after checking the complete imported logical model.
use super::*;
use fln_comp::fir::EffectClass;
use fln_comp::flbc::{ArgumentOwnership, ResultOwnership};
use fln_vm::extern_row::{
    ArgumentOwnership as ContractArgument, EffectClass as ContractEffect,
    Ownership as ContractOwnership, ResultOwnership as ContractResult,
};
use std::collections::BTreeMap;

#[derive(Default)]
pub(super) struct Store {
    world_checked: bool,
    ref_checked: bool,
    void_checked: bool,
    runners_checked: [bool; 2],
    next_adapter: u64,
    bindings: BTreeMap<Name, (IntrinsicBinding, Expr)>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Operation {
    New,
    Get,
    Set,
    Swap,
}

impl Operation {
    fn from_name(name: &Name) -> Option<Self> {
        [Self::New, Self::Get, Self::Set, Self::Swap]
            .into_iter()
            .find(|operation| name == &operation.source_name())
    }

    fn source_name(self) -> Name {
        name(match self {
            Self::New => "ST.Prim.mkRef",
            Self::Get => "ST.Prim.Ref.get",
            Self::Set => "ST.Prim.Ref.set",
            Self::Swap => "ST.Prim.Ref.swap",
        })
    }

    fn private_name(self) -> Name {
        Name::num(name("_fln_runtime_st_primitive"), self as u64)
    }

    fn argument_types(self) -> Vec<Expr> {
        match self {
            Self::New => vec![payload_type()],
            Self::Get => vec![ref_type()],
            Self::Set | Self::Swap => vec![ref_type(), payload_type()],
        }
    }

    fn capture_types(self, payload: &Expr) -> Vec<Expr> {
        match self {
            Self::New => vec![payload.clone()],
            Self::Get => vec![ref_type()],
            Self::Set | Self::Swap => vec![ref_type(), payload.clone()],
        }
    }

    fn argument_values(self) -> Vec<ValueType> {
        match self {
            Self::New => vec![ValueType::Abi],
            Self::Get => vec![ValueType::Ref],
            Self::Set | Self::Swap => vec![ValueType::Ref, ValueType::Abi],
        }
    }

    fn raw_result(self) -> (Expr, ValueType) {
        match self {
            Self::New => (ref_type(), ValueType::Ref),
            Self::Get | Self::Swap => (payload_type(), ValueType::Abi),
            Self::Set => (unit_type(), ValueType::Unit),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primitive_cache_never_accepts_display_equal_structural_names() {
        let environment = Environment::new();
        let mut preparation = Preparation::new(&environment, IngressLimits::default());
        for operation in [
            Operation::New,
            Operation::Get,
            Operation::Set,
            Operation::Swap,
        ] {
            let canonical = operation.source_name();
            assert_eq!(Operation::from_name(&canonical), Some(operation));
            // The contract owner installs one binding per actual structural
            // source name. A later similarly rendered name must never bypass
            // recognition merely because that binding is already cached.
            preparation.st_bind_primitive(operation).unwrap();
            let label = canonical.to_display_string();
            let parts: Vec<_> = label.split('.').collect();
            for boundary in 1..parts.len() {
                let left = parts[..boundary].join(".");
                let right = parts[boundary..].join(".");
                let alternate = Name::from_components([left.as_str(), right.as_str()]);
                if alternate == canonical {
                    continue;
                }
                assert_eq!(alternate.to_display_string(), label);
                assert_eq!(Operation::from_name(&alternate), None);
                assert!(
                    preparation
                        .st_call(&Expr::const_(alternate, vec![]), &[])
                        .unwrap()
                        .is_none()
                );
            }
            let alternate = Name::from_components([label.as_str()]);
            assert_ne!(alternate, canonical);
            assert_eq!(alternate.to_display_string(), label);
            assert_eq!(Operation::from_name(&alternate), None);
            assert!(
                preparation
                    .st_call(&Expr::const_(alternate, vec![]), &[])
                    .unwrap()
                    .is_none()
            );
        }
    }
}

fn world_type() -> Expr {
    Expr::const_(name("_fln_runtime_st_world"), vec![])
}

fn ref_type() -> Expr {
    Expr::const_(name("_fln_runtime_st_ref"), vec![])
}

fn payload_type() -> Expr {
    Expr::const_(name("_fln_runtime_st_payload"), vec![])
}

fn unit_type() -> Expr {
    Expr::const_(name("_fln_runtime_st_unit"), vec![])
}

fn apply(label: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter()
        .fold(Expr::const_(name(label), vec![]), Expr::app)
}

fn local(index: u32) -> Result<Expr, IngressError> {
    Expr::bvar(index).map_err(|_| unsupported("ST adapter binder scope"))
}

impl Preparation<'_> {
    pub(crate) fn st_intrinsic_binding(&self, name: &Name) -> Option<IntrinsicBinding> {
        self.st
            .bindings
            .get(name)
            .map(|(binding, _)| binding.clone())
    }

    pub(super) fn st_intrinsic_type(&self, name: &Name) -> Option<Expr> {
        self.st.bindings.get(name).map(|(_, type_)| type_.clone())
    }

    fn st_carrier(
        &mut self,
        type_: Expr,
        value: ValueType,
        ownership: CallableResultOwnership,
    ) -> Result<Expr, IngressError> {
        self.tick()?;
        let ExprNode::Const { name, .. } = type_.node() else {
            return Err(unsupported("ST runtime carrier"));
        };
        if self.environment.contains(name) {
            return Err(unsupported("ST runtime carrier name collision"));
        }
        if !self.value_types.native.contains_key(&type_) {
            self.value_types.native.try_reserve(1).map_err(|_| {
                IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: self.value_types.native.len().saturating_add(1),
                }
            })?;
            self.value_types
                .native
                .insert(type_.clone(), (value, ownership));
        }
        Ok(type_)
    }

    fn st_world(&mut self) -> Result<Option<Expr>, IngressError> {
        if source_scalar_constructor_binding(self.environment, &name("Bool.false")).is_none() {
            return Ok(None);
        }
        if !self.st.world_checked {
            if !source_intrinsics::st::st_world_contract_matches(
                self.environment,
                &mut self.visited,
                self.limits,
            )? {
                return Ok(None);
            }
            self.st.world_checked = true;
        }
        self.st_carrier(
            world_type(),
            ValueType::Bool,
            CallableResultOwnership::Scalar,
        )
        .map(Some)
    }

    fn st_ref(&mut self) -> Result<Option<Expr>, IngressError> {
        if !self.st.ref_checked {
            if !source_intrinsics::st::st_ref_contract_matches(
                self.environment,
                &mut self.visited,
                self.limits,
            )? {
                return Ok(None);
            }
            self.st.ref_checked = true;
        }
        self.st_carrier(ref_type(), ValueType::Ref, CallableResultOwnership::Owned)
            .map(Some)
    }

    pub(super) fn st_ref_record_forbidden(&mut self, family: &Name) -> Result<bool, IngressError> {
        Ok(family == &name("ST.Ref") && self.st_ref()?.is_some())
    }

    /// Called before delta reduction hides Void's opaque carrier projection.
    /// `arguments` is the type reducer's reversed application spine. A closed
    /// handle has no ordinary record fields, independently of its payload.
    /// Primitive selection separately proves the payload's complete runtime
    /// representation; doing that here would recursively reenter type_head.
    pub(super) fn st_type_head(
        &mut self,
        head: &Expr,
        arguments: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const {
            name: head_name,
            levels,
        } = head.node()
        else {
            return Ok(None);
        };
        if !levels.is_empty() {
            return Ok(None);
        }
        // The exact Void family makes sigma a phantom type index. Preserve
        // its uniform world representation even while a checked polymorphic
        // dictionary still binds sigma: unfolding it first would expose the
        // opaque NonemptyType field and incorrectly select a generic ABI slot.
        // This grants no primitive implementation for an open action; those
        // calls retain their separate ground-argument and extern checks.
        if head_name == &name("Void") && arguments.len() == 1 {
            return self.st_world();
        }
        if head_name == &name("ST.Ref")
            && arguments.len() == 2
            && arguments.iter().all(specialize::closed)
        {
            return self.st_ref();
        }
        Ok(None)
    }

    fn st_adapter_name(&mut self, label: &str) -> Result<Name, IngressError> {
        self.tick()?;
        let next = self.st.next_adapter;
        self.st.next_adapter = next
            .checked_add(1)
            .ok_or_else(|| unsupported("ST adapter identity"))?;
        let name = Name::num(name(label), next);
        if self.environment.contains(&name) {
            return Err(unsupported("ST adapter name collision"));
        }
        Ok(name)
    }

    fn st_bind_primitive(&mut self, operation: Operation) -> Result<Name, IngressError> {
        let private = operation.private_name();
        if self.st.bindings.contains_key(&private) {
            return Ok(private);
        }
        if self.environment.contains(&private) {
            return Err(unsupported("ST primitive name collision"));
        }
        let source = operation.source_name().to_display_string();
        let arguments = operation.argument_values();
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| {
                row.name == source && row.levels == 0 && row.arity as usize == arguments.len() + 2
            })
            .ok_or_else(|| unsupported("ST generated primitive row"))?;
        if ContractEffect::parse(row.effect).ok() != Some(ContractEffect::State) {
            return Err(unsupported("ST primitive effect contract"));
        }
        let ownership = ContractOwnership::parse(row.ownership)
            .map_err(|_| unsupported("ST primitive ownership contract"))?;
        let argument_ownership = ownership
            .argument_ownership(arguments.len())
            .map_err(|_| unsupported("ST primitive argument ownership"))?
            .into_iter()
            .map(|ownership| match ownership {
                ContractArgument::Borrowed => ArgumentOwnership::Borrowed,
                ContractArgument::Owned => ArgumentOwnership::Owned,
                ContractArgument::Unique => ArgumentOwnership::Unique,
                ContractArgument::Scalar => ArgumentOwnership::Scalar,
            })
            .collect();
        let result_ownership = match ownership
            .result_ownership()
            .map_err(|_| unsupported("ST primitive result ownership"))?
        {
            ContractResult::Owned => ResultOwnership::Owned,
            ContractResult::Borrowed => ResultOwnership::Borrowed,
            ContractResult::Scalar => ResultOwnership::Scalar,
            ContractResult::RawObject => ResultOwnership::RawObject,
        };
        let (mut type_, result) = operation.raw_result();
        for domain in operation.argument_types().into_iter().rev() {
            self.tick()?;
            type_ = Expr::forall_e(name("_st_arg"), domain, type_, BinderInfo::Default);
        }
        let binding = IntrinsicBinding {
            name: private.clone(),
            universe_arity: 0,
            row: row.id.to_owned(),
            arguments,
            argument_ownership,
            result,
            result_ownership,
            effect: EffectClass::State,
        };
        self.st.bindings.insert(private.clone(), (binding, type_));
        Ok(private)
    }

    /// Keep value arguments strict at action construction, and world strict at
    /// invocation. The native cell operation occurs inside the action, once
    /// per invocation; constructing or reusing the closure performs no effect.
    pub(super) fn st_call(
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
        if !levels.is_empty() {
            return Ok(None);
        }
        let runner = if requested == &name("runST") {
            Some(0)
        } else if requested == &name("runEST") {
            Some(1)
        } else {
            None
        };
        if let Some(runner) = runner {
            if !self.st.runners_checked[runner] {
                if !source_intrinsics::st::st_runner_matches(
                    self.environment,
                    requested,
                    &mut self.visited,
                    self.limits,
                )? {
                    return Ok(None);
                }
                // Body exposure must not bypass an explicitly attached
                // implementation contract merely by removing the source name
                // before ordinary executable dependency discovery.
                source_intrinsics::check_selected_extern_attribute(
                    self.environment,
                    requested,
                    &mut self.externs,
                    &mut self.visited,
                    self.limits,
                )?;
                self.st.runners_checked[runner] = true;
            }
            let Some(ConstantInfo::Defn(definition)) = self.environment.find(requested) else {
                return Ok(None);
            };
            // Expose the checked body to ordinary strict beta preparation.
            // Its literal polymorphic callback can then specialize at Unit;
            // computed callbacks retain lets and their usual refusal boundary.
            let mut body = definition.value.clone();
            for argument in args {
                self.tick()?;
                body = Expr::app(body, argument.clone());
            }
            return Ok(Some(body));
        }
        if requested == &name("Void.mk") {
            if !self.st.void_checked
                && !source_intrinsics::st::st_primitive_matches(
                    self.environment,
                    requested,
                    &mut self.externs,
                    &mut self.visited,
                    self.limits,
                )?
            {
                return Ok(None);
            }
            self.st.void_checked = true;
            if args.len() != 2 || !specialize::closed(&args[0]) || self.st_world()?.is_none() {
                return Ok(None);
            }
            let binder = self.st_adapter_name("_fln_runtime_st_world_argument")?;
            return Ok(Some(Expr::let_e(
                binder,
                self.normalize_type(&args[0])?,
                args[1].clone(),
                proofs::erased_value(),
                false,
            )));
        }
        let Some(operation) = Operation::from_name(requested) else {
            return Ok(None);
        };
        // A canonical extern on an unrelated same-named declaration is a
        // contract refusal even when its arity is outside this adapter slice.
        if !self.st.bindings.contains_key(&operation.private_name())
            && !source_intrinsics::st::st_primitive_matches(
                self.environment,
                requested,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )?
        {
            return Ok(None);
        }
        let arity = operation.argument_values().len();
        let saturated = arity + 2;
        if !(args.len() == saturated || args.len() == saturated + 1)
            || !specialize::closed(&args[0])
            || !specialize::closed(&args[1])
        {
            return Ok(None);
        }
        if self.st_world()?.is_none() || self.st_ref()?.is_none() {
            return Ok(None);
        }
        let payload = self.erase_runtime_type(&args[1])?;
        if !specialize::closed(&payload)
            || !matches!(
                self.value_type(&payload)?,
                Some(ValueType::Nat | ValueType::String | ValueType::Constructor)
            )
        {
            return Ok(None);
        }
        // One canonical generated row serves every proved payload layout.
        // Ingress inserts explicit Box/Unbox operations between this ABI word
        // and the concrete argument/Out field; no layout or callable is cast.
        self.st_carrier(
            payload_type(),
            ValueType::Abi,
            CallableResultOwnership::Erased,
        )?;
        let domains = operation.capture_types(&payload);
        if operation == Operation::Set {
            self.st_carrier(
                unit_type(),
                ValueType::Unit,
                CallableResultOwnership::Scalar,
            )?;
        }
        let primitive = self.st_bind_primitive(operation)?;
        let mut call = Expr::const_(primitive, vec![]);
        for index in 0..arity {
            self.tick()?;
            call = Expr::app(call, local((arity - index) as u32)?);
        }
        let sigma = args[0].clone();
        let result_type = match operation {
            Operation::New => apply("ST.Ref", [sigma.clone(), args[1].clone()]),
            Operation::Set => Expr::const_(name("Unit"), vec![]),
            Operation::Get | Operation::Swap => args[1].clone(),
        };
        let action_type = Expr::forall_e(
            Name::anonymous(),
            world_type(),
            apply("ST.Out", [sigma.clone(), result_type.clone()]),
            BinderInfo::Default,
        );
        let mut body = if operation == Operation::Set {
            let binder = self.st_adapter_name("_fln_runtime_st_set_result")?;
            Expr::let_e(
                binder,
                unit_type(),
                call,
                apply(
                    "ST.Out.mk",
                    [
                        sigma.clone(),
                        result_type,
                        Expr::const_(name("Unit.unit"), vec![]),
                        local(1)?,
                    ],
                ),
                false,
            )
        } else {
            apply("ST.Out.mk", [sigma.clone(), result_type, call, local(0)?])
        };
        let world = self.st_adapter_name("_fln_runtime_st_world_argument")?;
        body = if let Some(argument) = args.get(saturated) {
            Expr::let_e(
                world,
                world_type(),
                self.lift(argument, arity as u32)?,
                body,
                false,
            )
        } else {
            // This lambda is introduced after the ordinary argument-annotation
            // pass. Retain its ground interface in a typed let so the normal
            // closure converter registers its captures and each invocation.
            let action = self.st_adapter_name("_fln_runtime_st_action")?;
            Expr::let_e(
                action,
                action_type,
                Expr::lam(world, world_type(), body, BinderInfo::Default),
                local(0)?,
                false,
            )
        };
        for index in (0..arity).rev() {
            let binder = self.st_adapter_name("_fln_runtime_st_argument")?;
            body = Expr::let_e(
                binder,
                domains[index].clone(),
                self.lift(&args[index + 2], index as u32)?,
                body,
                false,
            );
        }
        Ok(Some(body))
    }
}
