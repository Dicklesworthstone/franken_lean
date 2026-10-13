//! Deferred logical BaseIO adapters for the VM's existing observations.
//!
//! These rows return bare ABI Bool values. Only an invoked world action wraps
//! that payload in its admitted ST.Out constructor. Ordinary definitions keep
//! their action closures, and no opaque logical default is ever executed.

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
                row.name == source && row.kind == "opaque" && row.levels == 0 && row.arity == 0
            })
            .ok_or_else(|| unsupported("BaseIO generated primitive row"))?;
        if ContractEffect::parse(row.effect).ok() != Some(ContractEffect::Io) {
            return Err(unsupported("BaseIO primitive effect contract"));
        }
        let ownership = ContractOwnership::parse(row.ownership)
            .map_err(|_| unsupported("BaseIO primitive ownership contract"))?;
        let argument_ownership = ownership
            .argument_ownership(0)
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
        let binding = IntrinsicBinding {
            name: private.clone(),
            universe_arity: 0,
            row: row.id.to_owned(),
            arguments: Vec::new(),
            argument_ownership,
            result: ValueType::Bool,
            result_ownership,
            effect: EffectClass::Io,
        };
        self.io
            .bindings
            .insert(private.clone(), (binding, bool_type()));
        Ok(private)
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
