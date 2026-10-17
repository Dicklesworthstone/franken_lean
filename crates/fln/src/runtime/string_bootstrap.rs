//! Convert checked Char and Pos.Raw records at the private native String ABI.
//!
//! Strings retain their dedicated VM representation. Char remains the ordinary
//! UInt32/BitVec/Fin constructor chain and Pos.Raw remains a one-field record.
//! Only these closed, typed adapters expose scalar payloads to the pinned pure
//! native rows; position results are reconstructed with the checked constructor.
//! Source operands stay outside the wrapper binding, preserving strict argument
//! evaluation and first-class/partially applied functions.

use super::*;
use crate::source_intrinsics::string_bootstrap::{self, Domain, Operation};
use fln_comp::fir::EffectClass;
use fln_comp::flbc::{ArgumentOwnership, ResultOwnership};

#[derive(Default)]
pub(super) struct Store {
    next_adapter: u64,
    primitives: [Option<(IntrinsicBinding, Expr)>; 8],
    position: Option<(Name, Name)>,
    verified: string_bootstrap::VerifiedDependencies,
}

fn c(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}

fn function(domains: &[Expr], result: Expr) -> Expr {
    domains.iter().rev().fold(result, |body, domain| {
        Expr::forall_e(Name::anonymous(), domain.clone(), body, BinderInfo::Default)
    })
}

fn b(index: u32) -> Result<Expr, IngressError> {
    Expr::bvar(index).map_err(|_| unsupported("String bootstrap adapter binder scope"))
}

fn native_type(domain: Domain) -> Expr {
    match domain {
        Domain::String => c("String"),
        Domain::Bool => c("Bool"),
        Domain::StringCallback => function(&[c("String"), c("Nat")], c("String")),
        Domain::Char | Domain::Position | Domain::Nat => c("Nat"),
    }
}

impl Preparation<'_> {
    pub(crate) fn string_bootstrap_intrinsic_binding(
        &self,
        requested: &Name,
    ) -> Option<IntrinsicBinding> {
        self.string_bootstrap
            .primitives
            .iter()
            .flatten()
            .find(|(binding, _)| &binding.name == requested)
            .map(|(binding, _)| binding.clone())
    }

    pub(super) fn string_bootstrap_intrinsic_type(&self, requested: &Name) -> Option<Expr> {
        self.string_bootstrap
            .primitives
            .iter()
            .flatten()
            .find(|(binding, _)| &binding.name == requested)
            .map(|(_, type_)| type_.clone())
    }

    fn string_bootstrap_adapter_name(&mut self) -> Result<Name, IngressError> {
        self.tick()?;
        let serial = self.string_bootstrap.next_adapter;
        self.string_bootstrap.next_adapter = serial
            .checked_add(1)
            .ok_or_else(|| unsupported("String bootstrap adapter identity"))?;
        let name = Name::num(name("_fln_runtime_string_bootstrap_scope"), serial);
        if self.environment.contains(&name) {
            return Err(unsupported("String bootstrap adapter name collision"));
        }
        Ok(name)
    }

    fn string_bootstrap_position(&mut self) -> Result<(Name, Name), IngressError> {
        if let Some(layout) = &self.string_bootstrap.position {
            return Ok(layout.clone());
        }
        let source = self.erase_runtime_type(&c("String.Pos.Raw"))?;
        if self.value_type(&source)? != Some(ValueType::Constructor) {
            return Err(unsupported(
                "String bootstrap requires the checked position record",
            ));
        }
        let shape = self
            .record_shape(&source)?
            .ok_or_else(|| unsupported("String bootstrap position layout"))?;
        let [constructor] = shape.constructors.as_slice() else {
            return Err(unsupported("String bootstrap position structure"));
        };
        if constructor.tag != 0
            || constructor.fields != [c("Nat")]
            || constructor.type_fields != [false]
        {
            return Err(unsupported("String bootstrap position fields"));
        }
        let layout = (shape.projection(constructor), constructor.name.clone());
        self.string_bootstrap.position = Some(layout.clone());
        Ok(layout)
    }

    fn string_bootstrap_bind(&mut self, operation: Operation) -> Result<(), IngressError> {
        if self.string_bootstrap.primitives[operation.index()].is_some() {
            return Ok(());
        }
        self.tick()?;
        let primitive = operation.primitive();
        if self.environment.contains(&primitive) {
            return Err(unsupported("String bootstrap primitive name collision"));
        }
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.name == operation.label())
            .ok_or_else(|| unsupported("String bootstrap generated primitive row"))?;
        let domains = operation.domains();
        let kind = if operation == Operation::ByteSize {
            "defn"
        } else {
            "opaque"
        };
        let module = if operation == Operation::ByteSize {
            "Init.Prelude"
        } else {
            "Init.Data.String.Bootstrap"
        };
        if row.id != format!("extern:{}", operation.label())
            || row.kind != kind
            || row.module != module
            || row.levels != 0
            || row.arity as usize != domains.len()
            || row.effect != "pure"
            || row.safety != "safe"
        {
            return Err(unsupported("String bootstrap generated primitive contract"));
        }
        use fln_vm::extern_row::{
            ArgumentOwnership as ContractArgument, Ownership, ResultOwnership as ContractResult,
        };
        let ownership = Ownership::parse(row.ownership)
            .map_err(|_| unsupported("String bootstrap generated ownership"))?;
        if ownership.argument_ownership(domains.len()).ok()
            != Some(vec![ContractArgument::Borrowed; domains.len()])
            || ownership.result_ownership().ok() != Some(ContractResult::Owned)
        {
            return Err(unsupported("String bootstrap generated ownership contract"));
        }
        let native_domains: Vec<_> = domains.iter().copied().map(native_type).collect();
        let mut arguments = Vec::new();
        for (domain, type_) in domains.iter().zip(&native_domains) {
            self.tick()?;
            arguments.push(match domain {
                Domain::String => ValueType::String,
                Domain::Char | Domain::Position | Domain::Nat => ValueType::Nat,
                Domain::Bool => ValueType::Bool,
                Domain::StringCallback => {
                    let Some(callback @ ValueType::Closure(_)) = self.value_type(type_)? else {
                        return Err(unsupported("String bootstrap native callback type"));
                    };
                    callback
                }
            });
        }
        let result = match operation.result() {
            Domain::String => ValueType::String,
            Domain::Nat | Domain::Position => ValueType::Nat,
            Domain::Bool => {
                if self.value_type(&c("Bool"))? != Some(ValueType::Bool) {
                    return Err(unsupported("String bootstrap checked Boolean result"));
                }
                ValueType::Bool
            }
            Domain::Char | Domain::StringCallback => unreachable!("fixed String bootstrap result"),
        };
        self.string_bootstrap.primitives[operation.index()] = Some((
            IntrinsicBinding {
                name: primitive,
                universe_arity: 0,
                row: row.id.to_owned(),
                arguments,
                argument_ownership: vec![ArgumentOwnership::Borrowed; domains.len()],
                result,
                result_ownership: ResultOwnership::Owned,
                effect: EffectClass::Pure,
            },
            function(&native_domains, native_type(operation.result())),
        ));
        Ok(())
    }

    pub(super) fn string_bootstrap_call(
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
        if !levels.is_empty() {
            return Ok(None);
        }
        self.tick()?;
        // Keep the existing exact source-seed intrinsic route, including its
        // separate extern check. Only the actual imported Prelude definition
        // needs the new record-to-native bridge.
        if operation == Operation::ByteSize
            && source_intrinsic_binding(self.environment, requested).is_some()
        {
            return Ok(None);
        }
        if self.string_bootstrap.primitives[operation.index()].is_none()
            && !string_bootstrap::contract_matches(
                self.environment,
                operation,
                &mut self.string_bootstrap.verified,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )?
        {
            return Ok(None);
        }
        let domains = operation.domains();
        if arguments.len() > domains.len() {
            return Ok(None);
        }
        self.string_bootstrap_bind(operation)?;
        let mut body = Expr::const_(operation.primitive(), Vec::new());
        for (index, domain) in domains.iter().enumerate() {
            self.tick()?;
            let mut argument = b(u32::try_from(domains.len() - index - 1)
                .map_err(|_| unsupported("String bootstrap adapter arity"))?)?;
            match domain {
                Domain::Char => {
                    for projection in self.native_character_projections()? {
                        self.tick()?;
                        argument = Expr::proj(projection, 0, argument);
                    }
                }
                Domain::Position => {
                    argument = Expr::proj(self.string_bootstrap_position()?.0, 0, argument);
                }
                Domain::StringCallback => {
                    // The native fold supplies scalar codepoints, while the
                    // source function keeps its checked Char parameter. This
                    // closed wrapper captures that function exactly once;
                    // accumulator and character remain ordered runtime inputs.
                    let callback = self.lift(&argument, 2)?;
                    let character = self.native_character_from_scalar(b(0)?)?;
                    argument = Expr::app(Expr::app(callback, b(1)?), character);
                    for type_ in [c("Nat"), c("String")] {
                        argument = Expr::lam(
                            self.string_bootstrap_adapter_name()?,
                            type_,
                            argument,
                            BinderInfo::Default,
                        );
                    }
                }
                Domain::String | Domain::Nat | Domain::Bool => {}
            }
            body = Expr::app(body, argument);
        }
        if operation.result() == Domain::Position {
            body = Expr::app(
                Expr::const_(self.string_bootstrap_position()?.1, Vec::new()),
                body,
            );
        }
        for domain in domains.iter().rev() {
            body = Expr::lam(
                self.string_bootstrap_adapter_name()?,
                domain.source_type(),
                body,
                BinderInfo::Default,
            );
        }
        let type_ = function(
            &domains
                .iter()
                .map(|domain| domain.source_type())
                .collect::<Vec<_>>(),
            operation.result().source_type(),
        );
        let wrapper = Expr::let_e(
            self.string_bootstrap_adapter_name()?,
            type_,
            body,
            b(0)?,
            false,
        );
        Ok(Some(arguments.iter().cloned().fold(wrapper, Expr::app)))
    }
}
