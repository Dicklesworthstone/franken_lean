//! Execute the checked String.ofList operation over logical character lists.
//!
//! The pin's native constructor traverses Unicode scalar values in source
//! order. List.rec builds the same traversal using the existing checked
//! String.push ABI bridge. Neither List nor Char acquires a packed native
//! representation, and the source list stays outside the closed typed wrapper.

use super::*;
use crate::source_intrinsics::string_from_list;

#[derive(Default)]
pub(super) struct Store {
    next_adapter: u64,
    verified: bool,
}

fn c(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}

fn b(index: u32) -> Result<Expr, IngressError> {
    Expr::bvar(index).map_err(|_| unsupported("String.ofList adapter binder scope"))
}

fn lambda(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn arrow(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default)
}

impl Preparation<'_> {
    fn string_from_list_adapter_name(&mut self) -> Result<Name, IngressError> {
        self.tick()?;
        let serial = self.string_from_list.next_adapter;
        self.string_from_list.next_adapter = serial
            .checked_add(1)
            .ok_or_else(|| unsupported("String.ofList adapter identity"))?;
        let name = Name::num(name("_fln_runtime_string_from_list_scope"), serial);
        if self.environment.contains(&name) {
            return Err(unsupported("String.ofList adapter name collision"));
        }
        Ok(name)
    }

    pub(super) fn string_from_list_call(
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
        if requested != &string_from_list::source_name()
            || !levels.is_empty()
            || arguments.len() > 1
        {
            return Ok(None);
        }
        // Bare function constants reach this adapter before generic executable
        // head selection. Preserve the root's explicit checked replacement in
        // both first-class and applied uses before choosing its native contract.
        if let Some(replacement) = self.implemented_by_call(head, arguments)? {
            return Ok(Some(replacement));
        }
        self.tick()?;
        if !self.string_from_list.verified
            && !string_from_list::contract_matches(
                self.environment,
                requested,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )?
        {
            return Ok(None);
        }

        // The cons minor has #0=String accumulator, #1=IH, #2=tail,
        // #3=Char head. Preparing this helper directly selects the checked
        // primitive used to implement String.ofList; it is not a call to a
        // separately replaceable logical helper from the original definition.
        let pushed = self
            .string_push_call(&c("String.push"), &[b(0)?, b(3)?])?
            .ok_or_else(|| {
                unsupported("String.ofList requires the checked String.push primitive")
            })?;
        self.string_from_list.verified = true;

        let list = Expr::app(Expr::const_(name("List"), vec![Level::zero()]), c("Char"));
        let accumulator = arrow(c("String"), c("String"));
        let cons = lambda(
            c("Char"),
            lambda(
                list.clone(),
                lambda(
                    accumulator.clone(),
                    lambda(c("String"), Expr::app(b(1)?, pushed)),
                ),
            ),
        );
        let body = [
            c("Char"),
            lambda(list.clone(), accumulator),
            lambda(c("String"), b(0)?),
            cons,
            b(0)?,
            Expr::lit(Literal::Str(String::new())),
        ]
        .into_iter()
        .fold(
            Expr::const_(name("List.rec"), vec![Level::one(), Level::zero()]),
            Expr::app,
        );
        let wrapper = Expr::let_e(
            self.string_from_list_adapter_name()?,
            arrow(list.clone(), c("String")),
            lambda(list, body),
            b(0)?,
            false,
        );
        Ok(Some(arguments.iter().cloned().fold(wrapper, Expr::app)))
    }
}

#[cfg(test)]
mod tests;
