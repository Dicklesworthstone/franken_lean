//! Convert checked characters, words, positions and slices at the String ABI.
//!
//! Strings retain their dedicated VM representation. Char remains the ordinary
//! UInt32/BitVec/Fin constructor chain and Pos.Raw remains a one-field record;
//! `String.Pos s` is the checked record around a `Pos.Raw`, and UInt8/UInt64
//! keep their ordinary BitVec/Fin chains. Slice proofs remain in logical data;
//! only its String and byte offsets cross the native boundary. These closed,
//! typed adapters expose scalar payloads to the pinned pure rows; word and
//! character results, optional characters, native decisions, position and
//! `String.Pos` results are reconstructed with their checked constructors, and
//! proofs keep their usual inert slots without reaching the native call.
//! Source operands stay outside the wrapper binding, preserving strict argument
//! evaluation and first-class/partially applied functions. Each native operand
//! and result carries the ownership its generated census row declares.

use super::*;
use crate::source_intrinsics::string_bootstrap::{self, Domain, Operation};
use fln_comp::fir::EffectClass;
use fln_comp::flbc::{ArgumentOwnership, ResultOwnership};

pub(super) struct Store {
    next_adapter: u64,
    /// One slot per operation, on the heap like the verified-row table: the
    /// Store is part of every Preparation, and deep tests and recursive
    /// callers keep Preparations on small host stacks.
    primitives: Box<[Option<(IntrinsicBinding, Expr)>; Operation::ALL.len()]>,
    position: Option<(Name, Name)>,
    string_position: Option<(Name, Name)>,
    substring: Option<(Name, Name)>,
    slice: Option<Name>,
    byte: Option<[Name; 3]>,
    word64: Option<[Name; 3]>,
    word_to_nat: Option<(IntrinsicBinding, Expr)>,
    byte_view: Option<Expr>,
    verified: string_bootstrap::VerifiedDependencies,
}

impl Default for Store {
    fn default() -> Self {
        Self {
            next_adapter: 0,
            primitives: Box::new(std::array::from_fn(|_| None)),
            position: None,
            string_position: None,
            substring: None,
            slice: None,
            byte: None,
            word64: None,
            word_to_nat: None,
            byte_view: None,
            verified: string_bootstrap::VerifiedDependencies::default(),
        }
    }
}

const NATIVE_SUBSTRING: &str = "_fln_runtime_string_substring";
const NATIVE_SLICE: &str = "_fln_runtime_string_slice";
const NATIVE_WORD64: &str = "_fln_runtime_string_word64";
const NATIVE_WORD_TO_NAT: &str = "_fln_runtime_string_word_to_nat";

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

fn nat_option() -> Expr {
    Expr::app(Expr::const_(name("Option"), vec![Level::zero()]), c("Nat"))
}

fn native_type(domain: Domain) -> Expr {
    match domain {
        Domain::String => c("String"),
        Domain::Substring => c(NATIVE_SUBSTRING),
        Domain::Slice => c(NATIVE_SLICE),
        // The native traversal returns its scalars; the adapter rebuilds Chars.
        Domain::CharList => nat_list(),
        Domain::OptionalChar => nat_option(),
        Domain::Word64 => c(NATIVE_WORD64),
        Domain::Bool | Domain::Decision => c("Bool"),
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
            .chain(self.string_bootstrap.word_to_nat.iter())
            .find(|(binding, _)| &binding.name == requested)
            .map(|(binding, _)| binding.clone())
    }

    pub(super) fn string_bootstrap_intrinsic_type(&self, requested: &Name) -> Option<Expr> {
        self.string_bootstrap
            .primitives
            .iter()
            .flatten()
            .chain(self.string_bootstrap.word_to_nat.iter())
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

    /// Keep the logical String and Pos.Raw fields intact outside the adapter.
    /// The native VM consumes a private three-field record with Nat offsets;
    /// its shape is never installed in the checked logical environment.
    fn string_bootstrap_substring(&mut self) -> Result<(Name, Name), IngressError> {
        if let Some(layout) = &self.string_bootstrap.substring {
            return Ok(layout.clone());
        }
        let source = self.erase_runtime_type(&c("Substring.Raw"))?;
        if self.value_type(&source)? != Some(ValueType::Constructor) {
            return Err(unsupported(
                "String bootstrap requires the checked Substring.Raw record",
            ));
        }
        let shape = self
            .record_shape(&source)?
            .ok_or_else(|| unsupported("String bootstrap Substring.Raw layout"))?;
        let [constructor] = shape.constructors.as_slice() else {
            return Err(unsupported("String bootstrap Substring.Raw structure"));
        };
        if constructor.tag != 0
            || constructor.fields != [c("String"), c("String.Pos.Raw"), c("String.Pos.Raw")]
            || constructor.type_fields != [false, false, false]
        {
            return Err(unsupported("String bootstrap Substring.Raw fields"));
        }
        let layout = (shape.projection(constructor), constructor.name.clone());
        self.string_bootstrap_position()?;
        self.io_private_record(NATIVE_SUBSTRING, vec![c("String"), c("Nat"), c("Nat")])?;
        self.string_bootstrap.substring = Some(layout.clone());
        Ok(layout)
    }

    fn string_bootstrap_pack_substring(&mut self, value: Expr) -> Result<Expr, IngressError> {
        let (projection, _) = self.string_bootstrap_substring()?;
        let (position, _) = self.string_bootstrap_position()?;
        let mut result = Expr::const_(Name::str(name(NATIVE_SUBSTRING), "mk"), Vec::new());
        for index in 0..3 {
            self.tick()?;
            let mut field = Expr::proj(projection.clone(), index, value.clone());
            if index > 0 {
                field = Expr::proj(position.clone(), 0, field);
            }
            result = Expr::app(result, field);
        }
        Ok(result)
    }

    fn string_bootstrap_unpack_substring(&mut self, value: Expr) -> Result<Expr, IngressError> {
        let (_, constructor) = self.string_bootstrap_substring()?;
        let (_, position) = self.string_bootstrap_position()?;
        let mut result = Expr::const_(constructor, Vec::new());
        for index in 0..3 {
            self.tick()?;
            let mut field = Expr::proj(name(NATIVE_SUBSTRING), index, b(0)?);
            if index > 0 {
                field = Expr::app(Expr::const_(position.clone(), Vec::new()), field);
            }
            result = Expr::app(result, field);
        }
        // All three projections share the one evaluated native result. Moving
        // `value` into each projection would execute drop/extract three times.
        Ok(Expr::let_e(
            self.string_bootstrap_adapter_name()?,
            c(NATIVE_SUBSTRING),
            value,
            result,
            false,
        ))
    }

    fn string_bootstrap_slice(&mut self) -> Result<Name, IngressError> {
        if let Some(projection) = &self.string_bootstrap.slice {
            return Ok(projection.clone());
        }
        let shape = self.io_checked_shape(c("String.Slice"))?;
        let [constructor] = shape.constructors.as_slice() else {
            return Err(unsupported("String bootstrap Slice structure"));
        };
        let position = self.erase_runtime_type(&Expr::app(
            c("String.Pos"),
            Expr::lit(Literal::Str(String::new())),
        ))?;
        if constructor.tag != 0
            || constructor.fields
                != [
                    c("String"),
                    position.clone(),
                    position,
                    proofs::erased_type(),
                ]
            || constructor.type_fields != [false, false, false, false]
        {
            return Err(unsupported("String bootstrap Slice fields"));
        }
        self.string_bootstrap_position()?;
        self.string_bootstrap_string_position()?;
        self.io_private_record(NATIVE_SLICE, vec![c("String"), c("Nat"), c("Nat")])?;
        let projection = shape.projection(constructor);
        self.string_bootstrap.slice = Some(projection.clone());
        Ok(projection)
    }

    fn string_bootstrap_pack_slice(&mut self, value: Expr) -> Result<Expr, IngressError> {
        let projection = self.string_bootstrap_slice()?;
        let (position, _) = self.string_bootstrap_string_position()?;
        let (raw, _) = self.string_bootstrap_position()?;
        let mut result = Expr::const_(Name::str(name(NATIVE_SLICE), "mk"), Vec::new());
        for index in 0..3 {
            self.tick()?;
            let mut field = Expr::proj(projection.clone(), index, value.clone());
            if index > 0 {
                field = Expr::proj(position.clone(), 0, field);
                field = Expr::proj(raw.clone(), 0, field);
            }
            result = Expr::app(result, field);
        }
        Ok(result)
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

    /// Hashes return all 64 bits. A private scalar carrier and the existing
    /// native UInt64-to-Nat adapter preserve the public UInt64/BitVec/Fin
    /// records, including in Prelude-only environments. This helper is
    /// compiler-owned representation code, not a call to a user declaration
    /// named UInt64.toNat or a dependency on the unrelated Float model.
    fn string_bootstrap_word64(&mut self) -> Result<(), IngressError> {
        if self.string_bootstrap.word64.is_some() {
            return Ok(());
        }
        let (word, word_fields) = self.string_bootstrap_record(c("UInt64"), 1)?;
        let (bits, bits_fields) = self.string_bootstrap_record(word_fields[0].clone(), 1)?;
        let (finite, finite_fields) = self.string_bootstrap_record(bits_fields[0].clone(), 2)?;
        if finite_fields != [c("Nat"), proofs::erased_type()] {
            return Err(unsupported("String hash checked UInt64 fields"));
        }
        if self.environment.contains(&name(NATIVE_WORD64))
            || self.environment.contains(&name(NATIVE_WORD_TO_NAT))
        {
            return Err(unsupported("String hash private carrier name collision"));
        }
        let mut binding = generated_source_intrinsic_binding(&name("UInt64.toNat"))
            .ok_or_else(|| unsupported("String hash native word conversion"))?;
        if binding.row != "extern:UInt64.toNat"
            || binding.arguments != [ValueType::UInt64]
            || binding.argument_ownership != [ArgumentOwnership::Scalar]
            || binding.result != ValueType::Nat
            || binding.result_ownership != ResultOwnership::Owned
            || binding.effect != EffectClass::Pure
        {
            return Err(unsupported(
                "String hash generated word conversion contract",
            ));
        }
        self.value_types
            .native
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: self.value_types.native.len().saturating_add(1),
            })?;
        self.value_types.native.insert(
            c(NATIVE_WORD64),
            (ValueType::UInt64, CallableResultOwnership::Owned),
        );
        binding.name = name(NATIVE_WORD_TO_NAT);
        self.string_bootstrap.word_to_nat =
            Some((binding, function(&[c(NATIVE_WORD64)], c("Nat"))));
        self.string_bootstrap.word64 = Some([word, bits, finite]);
        Ok(())
    }

    fn string_bootstrap_word64_from_native(&mut self, value: Expr) -> Result<Expr, IngressError> {
        self.string_bootstrap_word64()?;
        let [word, bits, finite] = self
            .string_bootstrap
            .word64
            .clone()
            .expect("checked word layout");
        let natural = Expr::app(c(NATIVE_WORD_TO_NAT), value);
        let mut result = Expr::app(
            Expr::app(Expr::const_(finite, vec![]), natural),
            proofs::erased_value(),
        );
        for constructor in [bits, word] {
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
        if runtime.contains(&Domain::Substring) || operation.result() == Domain::Substring {
            self.string_bootstrap_substring()?;
        }
        if runtime.contains(&Domain::Slice) {
            self.string_bootstrap_slice()?;
        }
        if operation.result() == Domain::Word64 {
            self.string_bootstrap_word64()?;
        }
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
        // callback and Nat-valued operands are objects. C character/byte reads
        // return `value` scalars; Bootstrap's exported Lean helpers return
        // owned objects, including their boxed character results.
        for (domain, disposition) in runtime.iter().zip(&argument_ownership) {
            if *disposition == ArgumentOwnership::Scalar && *domain != Domain::Char {
                return Err(unsupported("String bootstrap scalar operand ownership"));
            }
        }
        let scalar_result = operation.scalar_result();
        if scalar_result != (result_ownership == ResultOwnership::Scalar) {
            return Err(unsupported("String bootstrap scalar result ownership"));
        }
        let native_domains: Vec<_> = runtime.iter().copied().map(native_type).collect();
        let mut arguments = Vec::new();
        for (domain, type_) in runtime.iter().zip(&native_domains) {
            self.tick()?;
            arguments.push(match domain {
                Domain::String => ValueType::String,
                Domain::Substring | Domain::Slice => ValueType::Constructor,
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
                Domain::Proof
                | Domain::Byte
                | Domain::CharList
                | Domain::OptionalChar
                | Domain::Word64
                | Domain::Decision => {
                    unreachable!("fixed String bootstrap runtime operand")
                }
            });
        }
        let result = match operation.result() {
            Domain::String => ValueType::String,
            Domain::Substring => ValueType::Constructor,
            Domain::Word64 => ValueType::UInt64,
            Domain::Nat
            | Domain::Position
            | Domain::StringPosition
            | Domain::Char
            | Domain::Byte => ValueType::Nat,
            Domain::Bool | Domain::Decision => {
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
            Domain::OptionalChar => {
                let option = self.io_checked_shape(nat_option())?;
                if option.constructors.len() != 2
                    || option.constructors[0].tag != 0
                    || !option.constructors[0].fields.is_empty()
                    || option.constructors[1].tag != 1
                    || option.constructors[1].fields != [c("Nat")]
                {
                    return Err(unsupported(
                        "String bootstrap checked optional scalar layout",
                    ));
                }
                ValueType::Constructor
            }
            Domain::StringCallback | Domain::Proof | Domain::Slice => {
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

    fn string_bootstrap_optional_character(&mut self, value: Expr) -> Result<Expr, IngressError> {
        let character = self.native_character_from_scalar(b(0)?)?;
        let some = Expr::app(
            Expr::app(
                Expr::const_(name("Option.some"), vec![Level::zero()]),
                c("Char"),
            ),
            character,
        );
        let some = Expr::lam(Name::anonymous(), c("Nat"), some, BinderInfo::Default);
        let none = Expr::app(
            Expr::const_(name("Option.none"), vec![Level::zero()]),
            c("Char"),
        );
        let motive = Expr::lam(
            Name::anonymous(),
            nat_option(),
            Domain::OptionalChar.source_type(),
            BinderInfo::Default,
        );
        Ok([c("Nat"), motive, none, some, value].into_iter().fold(
            Expr::const_(name("Option.rec"), vec![Level::one(), Level::zero()]),
            Expr::app,
        ))
    }

    fn string_bootstrap_decision(&mut self, value: Expr) -> Result<Expr, IngressError> {
        let shape = self.io_checked_shape(Domain::Decision.source_type())?;
        let [no, yes] = shape.constructors.as_slice() else {
            return Err(unsupported("String slice checked decision constructors"));
        };
        if no.original != name("Decidable.isFalse")
            || no.tag != 0
            || no.fields != [proofs::erased_type()]
            || yes.original != name("Decidable.isTrue")
            || yes.tag != 1
            || yes.fields != [proofs::erased_type()]
        {
            return Err(unsupported("String slice checked decision fields"));
        }
        let constructor = |name: &Name| {
            Expr::app(
                Expr::const_(name.clone(), Vec::new()),
                proofs::erased_value(),
            )
        };
        Ok(io_result::choose(
            shape.source,
            value,
            constructor(&no.name),
            constructor(&yes.name),
        ))
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

    /// A native String has no logical constructor fields. Materialize its
    /// byte view with the verified byte-size and byte-read rows, then rebuild
    /// ByteArray and UInt8 records around the checked Array representation. The String
    /// and its size are each evaluated once. The recursive continuation
    /// visits n-1 .. 0 and prepends, preserving byte order without a second
    /// buffer or quadratic list append.
    fn string_byte_view(&mut self) -> Result<Option<Expr>, IngressError> {
        self.tick()?;
        if let Some(adapter) = &self.string_bootstrap.byte_view {
            return Ok(Some(adapter.clone()));
        }
        for operation in [Operation::ByteSize, Operation::InternalGetUtf8Byte] {
            // ByteSize's exact dependency closure includes String.toByteArray
            // and its selected extern. The byte reader also binds the actual
            // UInt8 representation; a foreign root or helper never acquires
            // authority merely because its name resembles this projection.
            if !string_bootstrap::contract_matches(
                self.environment,
                operation,
                &mut self.string_bootstrap.verified,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )? {
                return Ok(None);
            }
            self.string_bootstrap_bind(operation)?;
        }
        let bytes = self.io_checked_shape(c("ByteArray"))?;
        let [bytes_ctor] = bytes.constructors.as_slice() else {
            return Err(unsupported("String byte view ByteArray constructor"));
        };
        if bytes_ctor.tag != 0 || bytes_ctor.fields.len() != 1 {
            return Err(unsupported("String byte view ByteArray fields"));
        }
        let storage = self.byte_array_storage(bytes_ctor.fields[0].clone())?;
        let list = &storage.list;
        // Inside the successor: #0=accumulator, #1=IH, #2=index,
        // #3=size, #4=String. Every index is below the captured byte size,
        // so the proof-erased native read cannot reach the trailing NUL.
        let read = Expr::app(
            Expr::app(
                Expr::const_(Operation::InternalGetUtf8Byte.primitive(), vec![]),
                b(4)?,
            ),
            b(2)?,
        );
        let byte = self.string_bootstrap_byte_from_scalar(read)?;
        let cons = Expr::app(
            Expr::app(
                Expr::const_(list.constructors[1].name.clone(), vec![]),
                byte,
            ),
            b(0)?,
        );
        let accumulator = function(std::slice::from_ref(&list.source), list.source.clone());
        let lambda = |domain, body| Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default);
        let step = lambda(
            c("Nat"),
            lambda(
                accumulator.clone(),
                lambda(list.source.clone(), Expr::app(b(1)?, cons)),
            ),
        );
        let values = [
            lambda(c("Nat"), accumulator),
            lambda(list.source.clone(), b(0)?),
            step,
            b(0)?,
            Expr::const_(list.constructors[0].name.clone(), vec![]),
        ]
        .into_iter()
        .fold(Expr::const_(name("Nat.rec"), vec![Level::one()]), Expr::app);
        let result = Expr::app(
            Expr::const_(bytes_ctor.name.clone(), vec![]),
            Expr::app(storage.from_list, values),
        );
        let body = Expr::let_e(
            self.string_bootstrap_adapter_name()?,
            c("Nat"),
            Expr::app(Expr::const_(Operation::ByteSize.primitive(), vec![]), b(0)?),
            result,
            false,
        );
        let adapter = Expr::let_e(
            self.string_bootstrap_adapter_name()?,
            function(&[c("String")], c("ByteArray")),
            lambda(c("String"), body),
            b(0)?,
            false,
        );
        self.string_bootstrap.byte_view = Some(adapter.clone());
        Ok(Some(adapter))
    }

    pub(super) fn string_byte_projection_factory(
        &mut self,
        receiver_type: &Expr,
        family: &Name,
        index: u64,
    ) -> Result<Option<Expr>, IngressError> {
        if family != &name("String") || index != 0 || receiver_type != &c("String") {
            return Ok(None);
        }
        // Keep the ordinary family/telescope validation before replacing a
        // field access, including for unchecked direct ingress callers.
        let Some((_, field)) = self.projection_slot(receiver_type, family, index)? else {
            return Ok(None);
        };
        if field != c("ByteArray") {
            return Err(unsupported("String byte view projection result"));
        }
        self.string_byte_view()
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
        if requested == &name("String.toByteArray") && levels.is_empty() && arguments.len() <= 1 {
            if let Some(replacement) = self.implemented_by_call(head, arguments)? {
                return Ok(Some(replacement));
            }
            return Ok(self
                .string_byte_view()?
                .map(|adapter| arguments.iter().cloned().fold(adapter, Expr::app)));
        }
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
                Domain::Substring => {
                    argument = self.string_bootstrap_pack_substring(argument)?;
                }
                Domain::Slice => {
                    argument = self.string_bootstrap_pack_slice(argument)?;
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
                Domain::Byte
                | Domain::CharList
                | Domain::OptionalChar
                | Domain::Word64
                | Domain::Decision => {
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
            Domain::OptionalChar => self.string_bootstrap_optional_character(body)?,
            Domain::Word64 => self.string_bootstrap_word64_from_native(body)?,
            Domain::Decision => self.string_bootstrap_decision(body)?,
            Domain::Substring => self.string_bootstrap_unpack_substring(body)?,
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
