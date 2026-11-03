//! Deferred logical BaseIO adapters for the VM's existing observations.
//!
//! Native observations return bare Bool values or a checked private transport.
//! Only invocation of a world action wraps that payload in its admitted ST.Out
//! constructor. Ordinary definitions keep their action closures, and no opaque
//! logical default is ever executed.

use super::*;
use crate::source_intrinsics::io::primitives::{self, Operation};
use fln_comp::fir::EffectClass;
use fln_comp::flbc::{ArgumentOwnership, ResultOwnership};
use fln_vm::extern_row::{
    ArgumentOwnership as ContractArgument, EffectClass as ContractEffect,
    Ownership as ContractOwnership, ResultOwnership as ContractResult,
};
use std::collections::BTreeMap;

#[derive(Default)]
pub(super) struct Store {
    next_adapter: u64,
    bindings: BTreeMap<Name, (IntrinsicBinding, Expr)>,
    environment_layout: Option<Expr>,
}

fn bool_type() -> Expr {
    Expr::const_(name("Bool"), vec![])
}

fn apply(label: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments
        .into_iter()
        .fold(Expr::const_(name(label), vec![]), Expr::app)
}

fn world_argument() -> Result<Expr, IngressError> {
    Expr::bvar(0).map_err(|_| unsupported("BaseIO adapter binder scope"))
}

impl Preparation<'_> {
    pub(crate) fn io_intrinsic_binding(&self, name: &Name) -> Option<IntrinsicBinding> {
        self.io
            .bindings
            .get(name)
            .map(|(binding, _)| binding.clone())
    }

    pub(super) fn io_intrinsic_type(&self, name: &Name) -> Option<Expr> {
        self.io.bindings.get(name).map(|(_, type_)| type_.clone())
    }

    fn io_adapter_name(&mut self, label: &str) -> Result<Name, IngressError> {
        self.tick()?;
        let next = self.io.next_adapter;
        self.io.next_adapter = next
            .checked_add(1)
            .ok_or_else(|| unsupported("BaseIO adapter identity"))?;
        let name = Name::num(name(label), next);
        if self.environment.contains(&name) {
            return Err(unsupported("BaseIO adapter name collision"));
        }
        Ok(name)
    }

    fn io_bind_primitive(&mut self, operation: Operation) -> Result<Name, IngressError> {
        let private = operation.private_name();
        if self.io.bindings.contains_key(&private) {
            return Ok(private);
        }
        if self.environment.contains(&private) {
            return Err(unsupported("BaseIO primitive name collision"));
        }
        let source = operation.source_name().to_display_string();
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| {
                row.name == source
                    && row.kind == "opaque"
                    && row.levels == 0
                    && row.arity as usize == operation.source_arity()
            })
            .ok_or_else(|| unsupported("BaseIO generated primitive row"))?;
        if ContractEffect::parse(row.effect).ok() != Some(ContractEffect::Io) {
            return Err(unsupported("BaseIO primitive effect contract"));
        }
        let ownership = ContractOwnership::parse(row.ownership)
            .map_err(|_| unsupported("BaseIO primitive ownership contract"))?;
        let argument_ownership = ownership
            .argument_ownership(operation.source_arity())
            .map_err(|_| unsupported("BaseIO primitive argument ownership"))?
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
            .map_err(|_| unsupported("BaseIO primitive result ownership"))?
        {
            ContractResult::Owned => ResultOwnership::Owned,
            ContractResult::Borrowed => ResultOwnership::Borrowed,
            ContractResult::Scalar => ResultOwnership::Scalar,
            ContractResult::RawObject => ResultOwnership::RawObject,
        };
        let (arguments, result, type_) = if operation == Operation::GetEnv {
            let layout = self.io_environment_layout()?;
            (
                vec![ValueType::String],
                ValueType::Constructor,
                Expr::forall_e(
                    Name::anonymous(),
                    apply("String", []),
                    layout,
                    BinderInfo::Default,
                ),
            )
        } else {
            (vec![], ValueType::Bool, bool_type())
        };
        let binding = IntrinsicBinding {
            name: private.clone(),
            universe_arity: 0,
            row: row.id.to_owned(),
            arguments,
            argument_ownership,
            result,
            result_ownership,
            effect: EffectClass::Io,
        };
        self.io.bindings.insert(private.clone(), (binding, type_));
        Ok(private)
    }

    fn io_environment_layout(&mut self) -> Result<Expr, IngressError> {
        if let Some(layout) = &self.io.environment_layout {
            return Ok(layout.clone());
        }
        let layout = self.io_private_record(
            "_fln_runtime_environment_result",
            vec![bool_type(), apply("String", [])],
        )?;
        self.io.environment_layout = Some(layout.clone());
        Ok(layout)
    }

    fn io_getenv_call(&mut self, arguments: &[Expr]) -> Result<Option<Expr>, IngressError> {
        if arguments.len() > 2 {
            return Ok(None);
        }
        let Some(world_type) = self.st_evaluation_world()? else {
            return Ok(None);
        };
        let option = self.io_checked_shape(Operation::GetEnv.result_type())?;
        if option.constructors.len() != 2
            || option.constructors[0].tag != 0
            || !option.constructors[0].fields.is_empty()
            || option.constructors[1].tag != 1
            || option.constructors[1].fields != [apply("String", [])]
        {
            return Err(unsupported("environment checked Option String layout"));
        }
        let primitive = self.io_bind_primitive(Operation::GetEnv)?;
        let transport = self.io_environment_layout()?;
        let variable =
            |index| Expr::bvar(index).map_err(|_| unsupported("environment adapter scope"));
        let field = |index| {
            Ok::<_, IngressError>(Expr::proj(
                name("_fln_runtime_environment_result"),
                index,
                variable(0)?,
            ))
        };
        let absent = Expr::const_(option.constructors[0].name.clone(), vec![]);
        let present = Expr::app(
            Expr::const_(option.constructors[1].name.clone(), vec![]),
            field(1)?,
        );
        let payload = io_result::choose(option.source.clone(), field(0)?, absent, present);
        let state = apply("IO.RealWorld", []);
        let result_type = apply("ST.Out", [state.clone(), option.source.clone()]);
        let returned = apply("ST.Out.mk", [state, option.source, payload, variable(1)?]);
        let body = Expr::let_e(
            self.io_adapter_name("_fln_runtime_environment_packet")?,
            transport,
            Expr::app(Expr::const_(primitive, vec![]), variable(1)?),
            returned,
            false,
        );
        let action_type = Expr::forall_e(
            Name::anonymous(),
            world_type.clone(),
            result_type,
            BinderInfo::Default,
        );
        let action = Expr::lam(Name::anonymous(), world_type, body, BinderInfo::Default);
        let wrapper_type = Expr::forall_e(
            Name::anonymous(),
            apply("String", []),
            action_type,
            BinderInfo::Default,
        );
        let wrapper = Expr::let_e(
            self.io_adapter_name("_fln_runtime_environment_action")?,
            wrapper_type,
            Expr::lam(
                Name::anonymous(),
                apply("String", []),
                action,
                BinderInfo::Default,
            ),
            variable(0)?,
            false,
        );
        Ok(Some(arguments.iter().cloned().fold(wrapper, Expr::app)))
    }

    /// Both bare action constants and explicit world applications enter here.
    /// Native work remains inside the world binder; merely constructing an
    /// action cannot sample initialization or task-cancellation state early.
    pub(super) fn io_call(
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
        let Some(operation) = Operation::from_name(requested) else {
            return Ok(None);
        };
        self.tick()?;
        if !levels.is_empty() {
            return Ok(None);
        }
        // A foreign explicit extern remains a refusal before deciding whether
        // this invocation's argument count belongs to the supported slice.
        if !self.io.bindings.contains_key(&operation.private_name())
            && !primitives::primitive_matches(
                self.environment,
                operation,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )?
        {
            return Ok(None);
        }
        if operation == Operation::GetEnv {
            return self.io_getenv_call(arguments);
        }
        if arguments.len() > 1 {
            return Ok(None);
        }
        let Some(world_type) = self.st_evaluation_world()? else {
            return Ok(None);
        };
        if self.value_type(&bool_type())? != Some(ValueType::Bool) {
            return Ok(None);
        }
        let primitive = self.io_bind_primitive(operation)?;
        let state = Expr::const_(name("IO.RealWorld"), vec![]);
        let result_type = apply("ST.Out", [state.clone(), bool_type()]);
        let body = apply(
            "ST.Out.mk",
            [
                state,
                bool_type(),
                Expr::const_(primitive, vec![]),
                world_argument()?,
            ],
        );
        let world = self.io_adapter_name("_fln_runtime_base_io_world_argument")?;
        if let Some(argument) = arguments.first() {
            return Ok(Some(Expr::let_e(
                world,
                world_type,
                argument.clone(),
                body,
                false,
            )));
        }
        let action = self.io_adapter_name("_fln_runtime_base_io_action")?;
        let action_type = Expr::forall_e(
            Name::anonymous(),
            world_type.clone(),
            result_type,
            BinderInfo::Default,
        );
        Ok(Some(Expr::let_e(
            action,
            action_type,
            Expr::lam(world, world_type, body, BinderInfo::Default),
            world_argument()?,
            false,
        )))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn base_io_observations_use_structural_names_even_after_binding() {
        let environment = Environment::new();
        let mut preparation = Preparation::new(&environment, IngressLimits::default());
        for operation in [Operation::CheckCanceled, Operation::Initializing] {
            let canonical = operation.source_name();
            assert_eq!(Operation::from_name(&canonical), Some(operation));
            // This tests cache addressing only. It grants no source admission
            // or native authority to the display-equivalent alternate name.
            preparation.io_bind_primitive(operation).unwrap();
            let alternate = Name::from_components([canonical.to_display_string().as_str()]);
            assert_ne!(alternate, canonical);
            assert_eq!(alternate.to_display_string(), canonical.to_display_string());
            assert_eq!(Operation::from_name(&alternate), None);
            assert!(
                preparation
                    .io_call(&Expr::const_(alternate, vec![]), &[])
                    .unwrap()
                    .is_none()
            );
        }
    }
}
