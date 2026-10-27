//! Convert checked Char and Pos.Raw records at the private native String ABI.
//!
//! Strings retain their dedicated VM representation. Char remains the ordinary
//! UInt32/BitVec/Fin constructor chain and Pos.Raw remains a one-field record;
//! `String.Pos s` is the checked record around a `Pos.Raw` and UInt8 the
//! ordinary BitVec/Fin chain. Only these closed, typed adapters expose scalar
//! payloads to the pinned pure native rows; Char, UInt8, position and
//! `String.Pos` results are reconstructed with their checked constructors, and
//! proofs keep their usual inert slots without reaching the native call.
//! Source operands stay outside the wrapper binding, preserving strict argument
//! evaluation and first-class/partially applied functions. Each native operand
//! and result carries the ownership its generated census row declares.

use super::*;
use crate::source_intrinsics::string_bootstrap::{self, Domain, Operation};
use fln_comp::fir::EffectClass;
use fln_comp::flbc::{ArgumentOwnership, ResultOwnership};

#[derive(Default)]
pub(super) struct Store {
    next_adapter: u64,
    /// One slot per operation, on the heap like the verified-row table: the
    /// Store is part of every Preparation, and deep tests and recursive
    /// callers keep Preparations on small host stacks.
    primitives: Box<[Option<(IntrinsicBinding, Expr)>; Operation::ALL.len()]>,
    position: Option<(Name, Name)>,
    string_position: Option<(Name, Name)>,
    byte: Option<[Name; 3]>,
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

fn nat_list() -> Expr {
    Expr::app(Expr::const_(name("List"), vec![Level::zero()]), c("Nat"))
}

fn native_type(domain: Domain) -> Expr {
    match domain {
        Domain::String => c("String"),
        // The native traversal returns its scalars; the adapter rebuilds Chars.
        Domain::CharList => nat_list(),
        Domain::Bool => c("Bool"),
        Domain::StringCallback => function(&[c("String"), c("Nat")], c("String")),
        Domain::Char
        | Domain::Position
        | Domain::Nat
        | Domain::StringPosition
        | Domain::Byte
        | Domain::Proof => c("Nat"),
    }
}

fn runtime_argument(
    ownership: fln_vm::extern_row::ArgumentOwnership,
) -> Result<ArgumentOwnership, IngressError> {
    use fln_vm::extern_row::ArgumentOwnership as Contract;
    Ok(match ownership {
        Contract::Borrowed => ArgumentOwnership::Borrowed,
        Contract::Owned => ArgumentOwnership::Owned,
        Contract::Scalar => ArgumentOwnership::Scalar,
        Contract::Unique => {
            return Err(unsupported("String bootstrap unique argument ownership"));
        }
    })
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

    /// `String.Pos s` is one checked `Pos.Raw` field and an erased validity
    /// proof, for every `s`. Read its layout at the closed instance `""`.
    fn string_bootstrap_string_position(&mut self) -> Result<(Name, Name), IngressError> {
        if let Some(layout) = &self.string_bootstrap.string_position {
            return Ok(layout.clone());
        }
        let source = self.erase_runtime_type(&Expr::app(
            c("String.Pos"),
            Expr::lit(Literal::Str(String::new())),
        ))?;
        if self.value_type(&source)? != Some(ValueType::Constructor) {
            return Err(unsupported(
                "String bootstrap requires the checked String.Pos record",
            ));
        }
        let shape = self
            .record_shape(&source)?
            .ok_or_else(|| unsupported("String bootstrap String.Pos layout"))?;
        let [constructor] = shape.constructors.as_slice() else {
            return Err(unsupported("String bootstrap String.Pos structure"));
        };
        if constructor.tag != 0
            || constructor.fields != [c("String.Pos.Raw"), proofs::erased_type()]
            || constructor.type_fields != [false, false]
        {
            return Err(unsupported("String bootstrap String.Pos fields"));
        }
        let layout = (shape.projection(constructor), constructor.name.clone());
        self.string_bootstrap.string_position = Some(layout.clone());
        Ok(layout)
    }

    fn string_bootstrap_record(
        &mut self,
        source: Expr,
        fields: usize,
    ) -> Result<(Name, Vec<Expr>), IngressError> {
        let source = self.erase_runtime_type(&source)?;
        if self.value_type(&source)? != Some(ValueType::Constructor) {
            return Err(unsupported(
                "String bootstrap requires the checked UInt8 record",
            ));
        }
        let shape = self
            .record_shape(&source)?
            .ok_or_else(|| unsupported("String bootstrap UInt8 layout"))?;
        let [constructor] = shape.constructors.as_slice() else {
            return Err(unsupported("String bootstrap UInt8 structure"));
        };
        if constructor.tag != 0 || constructor.fields.len() != fields {
            return Err(unsupported("String bootstrap UInt8 field count"));
        }
        Ok((constructor.name.clone(), constructor.fields.clone()))
    }

    /// The native byte is a scalar. Rebuild the ordinary checked UInt8 chain
    /// around it with the registered constructors, as Char results are.
    fn string_bootstrap_byte_from_scalar(&mut self, scalar: Expr) -> Result<Expr, IngressError> {
        let [byte, bits, finite] = match &self.string_bootstrap.byte {
            Some(constructors) => constructors.clone(),
            None => {
                let (byte, byte_fields) = self.string_bootstrap_record(c("UInt8"), 1)?;
                let (bits, bits_fields) =
                    self.string_bootstrap_record(byte_fields[0].clone(), 1)?;
                let (finite, finite_fields) =
                    self.string_bootstrap_record(bits_fields[0].clone(), 2)?;
                if finite_fields != [c("Nat"), proofs::erased_type()] {
                    return Err(unsupported("String bootstrap UInt8 finite-word fields"));
                }
                let constructors = [byte, bits, finite];
                self.string_bootstrap.byte = Some(constructors.clone());
                constructors
            }
        };
        let mut result = Expr::app(
            Expr::app(Expr::const_(finite, vec![]), scalar),
            proofs::erased_value(),
        );
        for constructor in [bits, byte] {
            self.tick()?;
            result = Expr::app(Expr::const_(constructor, vec![]), result);
        }
        Ok(result)
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
        // The census arity counts the logical telescope, proofs included;
        // the executable ABI receives only the runtime operands.
        let runtime: Vec<Domain> = domains
            .iter()
            .copied()
            .filter(|domain| *domain != Domain::Proof)
            .collect();
        let (kind, module) = operation.declaration();
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
        use fln_vm::extern_row::{Ownership, ResultOwnership as ContractResult};
        let ownership = Ownership::parse(row.ownership)
            .map_err(|_| unsupported("String bootstrap generated ownership"))?;
        let argument_ownership = ownership
            .argument_ownership(runtime.len())
            .map_err(|_| unsupported("String bootstrap generated ownership contract"))?
            .into_iter()
            .map(runtime_argument)
            .collect::<Result<Vec<_>, _>>()?;
        let result_ownership = match ownership.result_ownership() {
            Ok(ContractResult::Owned) => ResultOwnership::Owned,
            Ok(ContractResult::Scalar) => ResultOwnership::Scalar,
            _ => return Err(unsupported("String bootstrap generated result ownership")),
        };
        // Only the native character may cross as an unboxed `value`; String,
        // callback and Nat-valued operands are objects. Char and UInt8 results
        // are the row's `value` scalar, every other result an owned object.
        for (domain, disposition) in runtime.iter().zip(&argument_ownership) {
            if *disposition == ArgumentOwnership::Scalar && *domain != Domain::Char {
                return Err(unsupported("String bootstrap scalar operand ownership"));
            }
        }
        let scalar_result = matches!(operation.result(), Domain::Char | Domain::Byte);
        if scalar_result != (result_ownership == ResultOwnership::Scalar) {
            return Err(unsupported("String bootstrap scalar result ownership"));
        }
        let native_domains: Vec<_> = runtime.iter().copied().map(native_type).collect();
        let mut arguments = Vec::new();
        for (domain, type_) in runtime.iter().zip(&native_domains) {
            self.tick()?;
            arguments.push(match domain {
                Domain::String => ValueType::String,
                Domain::Char | Domain::Position | Domain::Nat | Domain::StringPosition => {
                    ValueType::Nat
                }
                Domain::Bool => ValueType::Bool,
                Domain::StringCallback => {
                    let Some(callback @ ValueType::Closure(_)) = self.value_type(type_)? else {
                        return Err(unsupported("String bootstrap native callback type"));
                    };
                    callback
                }
                Domain::Proof | Domain::Byte | Domain::CharList => {
                    unreachable!("fixed String bootstrap runtime operand")
                }
            });
        }
        let result = match operation.result() {
            Domain::String => ValueType::String,
            Domain::Nat
            | Domain::Position
            | Domain::StringPosition
            | Domain::Char
            | Domain::Byte => ValueType::Nat,
            Domain::Bool => {
                if self.value_type(&c("Bool"))? != Some(ValueType::Bool) {
                    return Err(unsupported("String bootstrap checked Boolean result"));
                }
                ValueType::Bool
            }
            Domain::CharList => {
                // The VM builds `List.cons` (tag 1, head and tail) and the
                // fieldless tag-0 `List.nil`, as Golem's own code does.
                let list = self.io_checked_shape(nat_list())?;
                if list.constructors.len() != 2
                    || list.constructors[0].tag != 0
                    || !list.constructors[0].fields.is_empty()
                    || list.constructors[1].tag != 1
                    || list.constructors[1].fields != [c("Nat"), list.source.clone()]
                {
                    return Err(unsupported("String bootstrap checked scalar list layout"));
                }
                ValueType::Constructor
            }
            Domain::StringCallback | Domain::Proof => {
                unreachable!("fixed String bootstrap result")
            }
        };
        self.string_bootstrap.primitives[operation.index()] = Some((
            IntrinsicBinding {
                name: primitive,
                universe_arity: 0,
                row: row.id.to_owned(),
                arguments,
                argument_ownership,
                result,
                result_ownership,
                effect: EffectClass::Pure,
            },
            function(&native_domains, native_type(operation.result())),
        ));
        Ok(())
    }

    /// Rebuild the checked `List Char` from the native scalar list in order:
    /// `List.rec` maps each head through the ordinary Char constructors.
    fn string_bootstrap_characters(&mut self, scalars: Expr) -> Result<Expr, IngressError> {
        let characters = Expr::app(Expr::const_(name("List"), vec![Level::zero()]), c("Char"));
        // Under the cons minor: #0 = rebuilt tail, #1 = scalar tail, #2 = head.
        let head = self.native_character_from_scalar(b(2)?)?;
        let cons = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(name("List.cons"), vec![Level::zero()]),
                    c("Char"),
                ),
                head,
            ),
            b(0)?,
        );
        let cons = Expr::lam(
            Name::anonymous(),
            c("Nat"),
            Expr::lam(
                Name::anonymous(),
                nat_list(),
                Expr::lam(
                    Name::anonymous(),
                    characters.clone(),
                    cons,
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let nil = Expr::app(
            Expr::const_(name("List.nil"), vec![Level::zero()]),
            c("Char"),
        );
        let motive = Expr::lam(
            Name::anonymous(),
            nat_list(),
            characters,
            BinderInfo::Default,
        );
        Ok([c("Nat"), motive, nil, cons, scalars].into_iter().fold(
            Expr::const_(name("List.rec"), vec![Level::one(), Level::zero()]),
            Expr::app,
        ))
    }

    /// The binder types of a dependent adapter, and its own type, follow the
    /// checked declaration's telescope: a `String.Pos` mentions the earlier
    /// String. Indices line up because the adapter's lambdas bind the
    /// telescope's arguments in the same order. A proof binder takes the inert
    /// erased-proof slot instead of its proposition, exactly as post-admission
    /// proof erasure gives every other proof: the proposition is never
    /// normalized, and the native row never receives the slot.
    fn string_bootstrap_telescope(
        &mut self,
        operation: Operation,
    ) -> Result<(Vec<Expr>, Expr), IngressError> {
        let declared = self
            .environment
            .find(&operation.source_name())
            .ok_or_else(|| unsupported("String bootstrap checked declaration"))?
            .constant_val()
            .type_
            .clone();
        let mut binders = Vec::new();
        let mut telescope = &declared;
        for domain in operation.domains() {
            self.tick()?;
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = telescope.node()
            else {
                return Err(unsupported("String bootstrap checked telescope"));
            };
            let binder_type = if *domain == Domain::Proof {
                proofs::erased_type()
            } else {
                binder_type.clone()
            };
            binders.push((binder_name.clone(), binder_type, *binder_info));
            telescope = body;
        }
        let mut type_ = telescope.clone();
        for (binder_name, binder_type, binder_info) in binders.iter().rev() {
            self.tick()?;
            type_ = Expr::forall_e(
                binder_name.clone(),
                binder_type.clone(),
                type_,
                *binder_info,
            );
        }
        Ok((
            binders
                .into_iter()
                .map(|(_, binder_type, _)| binder_type)
                .collect(),
            type_,
        ))
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
                Domain::StringPosition => {
                    argument = Expr::proj(self.string_bootstrap_string_position()?.0, 0, argument);
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
                // A proof is a logical argument the native row never receives.
                Domain::Proof => continue,
                Domain::String | Domain::Nat | Domain::Bool => {}
                Domain::Byte | Domain::CharList => {
                    unreachable!("fixed String bootstrap result-only domain")
                }
            }
            body = Expr::app(body, argument);
        }
        body = match operation.result() {
            Domain::Position => Expr::app(
                Expr::const_(self.string_bootstrap_position()?.1, Vec::new()),
                body,
            ),
            // `String.Pos s` over the argument String: the raw position and the
            // validity proof's inert slot, as post-admission erasure leaves it.
            Domain::StringPosition => {
                let raw = Expr::app(
                    Expr::const_(self.string_bootstrap_position()?.1, Vec::new()),
                    body,
                );
                Expr::app(
                    Expr::app(
                        Expr::const_(self.string_bootstrap_string_position()?.1, Vec::new()),
                        raw,
                    ),
                    proofs::erased_value(),
                )
            }
            Domain::Char => self.native_character_from_scalar(body)?,
            Domain::Byte => self.string_bootstrap_byte_from_scalar(body)?,
            Domain::CharList => self.string_bootstrap_characters(body)?,
            _ => body,
        };
        let (binders, type_) = if operation.dependent() {
            self.string_bootstrap_telescope(operation)?
        } else {
            let binders: Vec<_> = domains.iter().map(|domain| domain.source_type()).collect();
            let type_ = function(&binders, operation.result().source_type());
            (binders, type_)
        };
        for binder in binders.into_iter().rev() {
            body = Expr::lam(
                self.string_bootstrap_adapter_name()?,
                binder,
                body,
                BinderInfo::Default,
            );
        }
        let wrapper = Expr::let_e(
            self.string_bootstrap_adapter_name()?,
            type_,
            body,
            b(0)?,
            false,
        );
        // A supplied proof is never evaluated and never reaches the native row.
        // Pass the inert placeholder instead of the elaborated proof term, so no
        // transform lifts or visits a proof the wrapper discards anyway.
        Ok(Some(arguments.iter().zip(domains).fold(
            wrapper,
            |applied, (argument, domain)| {
                Expr::app(
                    applied,
                    if *domain == Domain::Proof {
                        proofs::erased_value()
                    } else {
                        argument.clone()
                    },
                )
            },
        )))
    }
}
