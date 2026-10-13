//! The checked String constructor consumes logical bytes, while its native
//! extern consumes a packed buffer. Keep those representations separate:
//! fold the exact ByteArray/Array/List/UInt8 records into private native bytes,
//! then invoke the selected UTF-8 constructor. Source operands remain strict
//! and shared; the checked validity proof occupies only its usual inert slot.
use super::*;
use crate::source_intrinsics::string_bytes;
use fln_comp::fir::EffectClass;
use fln_comp::flbc::{ArgumentOwnership, ResultOwnership};
use fln_core::level::Level;

const PACKED: &str = "_fln_runtime_string_packed_bytes";
const BYTE: &str = "_fln_runtime_string_native_byte";

#[derive(Default)]
pub(super) struct Store {
    next_adapter: u64,
    verified: bool,
    primitives: [Option<(IntrinsicBinding, Expr)>; 4],
    layout: Option<Layout>,
}

#[derive(Clone)]
struct Layout {
    packed: Expr,
    list: Expr,
    // ByteArray -> Array -> List; UInt8 -> BitVec -> Fin -> Nat.
    projections: [Name; 5],
}

#[derive(Clone, Copy)]
enum Helper {
    Empty,
    Push,
    Byte,
    String,
}

impl Helper {
    fn contract(self) -> (&'static str, &'static str, u32, &'static str) {
        match self {
            Self::Empty => (
                "ByteArray.emptyWithCapacity",
                "defn",
                1,
                "abi((capacity: borrowed_arg) -> owned_res)",
            ),
            Self::Push => (
                "ByteArray.push",
                "defn",
                2,
                "abi((a: owned_arg, b: value) -> owned_res)",
            ),
            Self::Byte => ("UInt8.ofBitVec", "ctor", 1, "abi((a: owned_arg) -> value)"),
            Self::String => (
                "String.ofByteArray",
                "ctor",
                2,
                "rule(borrowed-args,owned-result)",
            ),
        }
    }
    fn name(self) -> Name {
        Name::num(name("_fln_runtime_string_bytes_helper"), self as u64)
    }
}

fn c(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}

fn b(index: u32) -> Result<Expr, IngressError> {
    Expr::bvar(index).map_err(|_| unsupported("String byte adapter binder scope"))
}

fn apply(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

fn function(domains: &[Expr], result: Expr) -> Expr {
    domains.iter().rev().fold(result, |body, domain| {
        Expr::forall_e(Name::anonymous(), domain.clone(), body, BinderInfo::Default)
    })
}

fn lambda(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}

impl Preparation<'_> {
    pub(crate) fn string_bytes_intrinsic_binding(
        &self,
        requested: &Name,
    ) -> Option<IntrinsicBinding> {
        self.string_bytes
            .primitives
            .iter()
            .flatten()
            .find(|(binding, _)| &binding.name == requested)
            .map(|(binding, _)| binding.clone())
    }

    pub(super) fn string_bytes_intrinsic_type(&self, requested: &Name) -> Option<Expr> {
        self.string_bytes
            .primitives
            .iter()
            .flatten()
            .find(|(binding, _)| &binding.name == requested)
            .map(|(_, type_)| type_.clone())
    }

    /// String construction and binary IO may pack bytes in the same program.
    /// Both adapters have independently checked their logical layouts and use
    /// the same native byte operations. Keep one intrinsic declaration per row
    /// and retain the second callable name as an ordinary checked function.
    pub(crate) fn string_bytes_intrinsic_alias(
        &mut self,
        binding: &IntrinsicBinding,
        intrinsics: &[IntrinsicBinding],
        functions: &mut Vec<FunctionBinding>,
    ) -> Result<bool, IngressError> {
        let Some((private, _)) = self
            .string_bytes
            .primitives
            .iter()
            .flatten()
            .find(|(private, _)| private.row == binding.row)
        else {
            return Ok(false);
        };
        let private_name = private.name.clone();
        for known in intrinsics {
            self.tick()?;
            if known.row != binding.row
                || (known.name != private_name && binding.name != private_name)
            {
                continue;
            }
            let mut renamed = binding.clone();
            renamed.name = known.name.clone();
            if &renamed != known {
                return Err(unsupported("String byte helper aliases disagree"));
            }
            // An ABI carrier is deliberately private to each adapter. Its
            // exact row still determines whether the forwarded value owns a
            // packed buffer or is a scalar byte; do not erase that distinction.
            let result_ownership = match (binding.result, binding.result_ownership) {
                (ValueType::Abi | ValueType::String, ResultOwnership::Owned) => {
                    CallableResultOwnership::Owned
                }
                (ValueType::Abi, ResultOwnership::Scalar) => CallableResultOwnership::Scalar,
                _ => return Err(unsupported("String byte alias result ownership")),
            };
            reserve(functions, self.limits.fir.max_functions.saturating_sub(1))?;
            let mut body = Expr::const_(known.name.clone(), Vec::new());
            for index in (0..binding.arguments.len()).rev() {
                self.tick()?;
                let index = u32::try_from(index)
                    .map_err(|_| unsupported("String byte alias binder scope"))?;
                body = Expr::app(body, b(index)?);
            }
            functions.push(FunctionBinding {
                name: binding.name.clone(),
                universe_arity: binding.universe_arity,
                parameters: binding.arguments.clone(),
                parameter_ownership: binding.argument_ownership.clone(),
                result: binding.result,
                result_ownership,
                body,
            });
            return Ok(true);
        }
        Ok(false)
    }

    fn string_bytes_adapter_name(&mut self) -> Result<Name, IngressError> {
        self.tick()?;
        let serial = self.string_bytes.next_adapter;
        self.string_bytes.next_adapter = serial
            .checked_add(1)
            .ok_or_else(|| unsupported("String byte adapter identity"))?;
        let name = Name::num(name("_fln_runtime_string_bytes_scope"), serial);
        if self.environment.contains(&name) {
            return Err(unsupported("String byte adapter name collision"));
        }
        Ok(name)
    }

    fn string_bytes_carrier(
        &mut self,
        label: &str,
        ownership: CallableResultOwnership,
    ) -> Result<Expr, IngressError> {
        self.tick()?;
        if self.environment.contains(&name(label)) {
            return Err(unsupported("String byte private carrier name collision"));
        }
        let type_ = c(label);
        if let Some(known) = self.value_types.native.get(&type_) {
            if *known != (ValueType::Abi, ownership) {
                return Err(unsupported("String byte private carrier ownership"));
            }
            return Ok(type_);
        }
        self.value_types
            .native
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: self.value_types.native.len().saturating_add(1),
            })?;
        self.value_types
            .native
            .insert(type_.clone(), (ValueType::Abi, ownership));
        Ok(type_)
    }

    fn string_bytes_bind(
        &mut self,
        helper: Helper,
        packed: &Expr,
        byte: &Expr,
    ) -> Result<(), IngressError> {
        self.tick()?;
        let private = helper.name();
        if self.environment.contains(&private) {
            return Err(unsupported("String byte helper name collision"));
        }
        if self.string_bytes.primitives[helper as usize].is_some() {
            return Ok(());
        }
        let (label, kind, arity, ownership) = helper.contract();
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.name == label)
            .ok_or_else(|| unsupported("String byte helper extern row"))?;
        if row.kind != kind
            || row.module != "Init.Prelude"
            || row.levels != 0
            || row.arity != arity
            || row.safety != "safe"
            || row.effect != "pure"
            || row.ownership != ownership
        {
            return Err(unsupported("String byte helper ABI contract"));
        }
        let (domains, arguments, argument_ownership, result_type, result, result_ownership) =
            match helper {
                Helper::Empty => (
                    vec![c("Nat")],
                    vec![ValueType::Nat],
                    vec![ArgumentOwnership::Borrowed],
                    packed.clone(),
                    ValueType::Abi,
                    ResultOwnership::Owned,
                ),
                Helper::Push => (
                    vec![packed.clone(), byte.clone()],
                    vec![ValueType::Abi, ValueType::Abi],
                    vec![ArgumentOwnership::Owned, ArgumentOwnership::Scalar],
                    packed.clone(),
                    ValueType::Abi,
                    ResultOwnership::Owned,
                ),
                Helper::Byte => (
                    vec![c("Nat")],
                    vec![ValueType::Nat],
                    vec![ArgumentOwnership::Owned],
                    byte.clone(),
                    ValueType::Abi,
                    ResultOwnership::Scalar,
                ),
                Helper::String => (
                    // The logical second argument is a checked proof. The
                    // genuine C row receives only its packed-byte argument.
                    vec![packed.clone()],
                    vec![ValueType::Abi],
                    vec![ArgumentOwnership::Borrowed],
                    c("String"),
                    ValueType::String,
                    ResultOwnership::Owned,
                ),
            };
        self.string_bytes.primitives[helper as usize] = Some((
            IntrinsicBinding {
                name: private,
                universe_arity: 0,
                row: row.id.to_owned(),
                arguments,
                argument_ownership,
                result,
                result_ownership,
                effect: EffectClass::Pure,
            },
            function(&domains, result_type),
        ));
        Ok(())
    }

    fn string_bytes_record(
        &mut self,
        source: Expr,
        count: usize,
    ) -> Result<(Name, Vec<Expr>), IngressError> {
        let source = self.erase_runtime_type(&source)?;
        if self.value_type(&source)? != Some(ValueType::Constructor) {
            return Err(unsupported(
                "String byte conversion requires checked logical records",
            ));
        }
        let shape = self
            .record_shape(&source)?
            .ok_or_else(|| unsupported("String byte checked record layout"))?;
        let [constructor] = shape.constructors.as_slice() else {
            return Err(unsupported("String byte checked record constructor"));
        };
        if constructor.tag != 0 || constructor.fields.len() != count {
            return Err(unsupported("String byte checked record fields"));
        }
        Ok((shape.projection(constructor), constructor.fields.clone()))
    }

    fn string_bytes_layout(&mut self) -> Result<Layout, IngressError> {
        if let Some(layout) = &self.string_bytes.layout {
            return Ok(layout.clone());
        }
        let (bytes_projection, bytes_fields) = self.string_bytes_record(c("ByteArray"), 1)?;
        let (array_projection, array_fields) =
            self.string_bytes_record(bytes_fields[0].clone(), 1)?;
        let list = self.io_checked_shape(array_fields[0].clone())?;
        if list.constructors.len() != 2
            || list.constructors[0].tag != 0
            || !list.constructors[0].fields.is_empty()
            || list.constructors[1].tag != 1
            || list.constructors[1].fields != [c("UInt8"), list.source.clone()]
        {
            return Err(unsupported("String byte checked list layout"));
        }
        let (byte_projection, byte_fields) = self.string_bytes_record(c("UInt8"), 1)?;
        let (bits_projection, bits_fields) = self.string_bytes_record(byte_fields[0].clone(), 1)?;
        let (fin_projection, fin_fields) = self.string_bytes_record(bits_fields[0].clone(), 2)?;
        if fin_fields != [c("Nat"), proofs::erased_type()] {
            return Err(unsupported("String byte checked finite word"));
        }
        let packed = self.string_bytes_carrier(PACKED, CallableResultOwnership::Owned)?;
        let byte = self.string_bytes_carrier(BYTE, CallableResultOwnership::Scalar)?;
        for helper in [Helper::Empty, Helper::Push, Helper::Byte, Helper::String] {
            self.string_bytes_bind(helper, &packed, &byte)?;
        }
        let layout = Layout {
            packed,
            list: list.source,
            projections: [
                bytes_projection,
                array_projection,
                byte_projection,
                bits_projection,
                fin_projection,
            ],
        };
        self.string_bytes.layout = Some(layout.clone());
        Ok(layout)
    }

    fn string_bytes_pack(&mut self, layout: &Layout, value: Expr) -> Result<Expr, IngressError> {
        self.tick()?;
        let accumulator = function(std::slice::from_ref(&layout.packed), layout.packed.clone());
        // Under the cons minor: #0=packed accumulator, #1=IH, #2=tail,
        // #3=head. Only the exact checked Fin.val reaches native byte boxing.
        let mut natural = b(3)?;
        for projection in &layout.projections[2..] {
            self.tick()?;
            natural = Expr::proj(projection.clone(), 0, natural);
        }
        let byte = Expr::app(Expr::const_(Helper::Byte.name(), Vec::new()), natural);
        let pushed = apply(Expr::const_(Helper::Push.name(), Vec::new()), [b(0)?, byte]);
        let cons = lambda(
            c("UInt8"),
            lambda(
                layout.list.clone(),
                lambda(
                    accumulator.clone(),
                    lambda(layout.packed.clone(), Expr::app(b(1)?, pushed)),
                ),
            ),
        );
        let array = Expr::proj(layout.projections[0].clone(), 0, value);
        let list = Expr::proj(layout.projections[1].clone(), 0, array);
        let empty = Expr::app(
            Expr::const_(Helper::Empty.name(), Vec::new()),
            nat::literal(0),
        );
        // The accumulator fold visits the original logical list in source
        // order. Every recursion and native push obeys ordinary VM limits.
        Ok(apply(
            Expr::const_(name("List.rec"), vec![Level::one(), Level::zero()]),
            [
                c("UInt8"),
                lambda(layout.list.clone(), accumulator),
                lambda(layout.packed.clone(), b(0)?),
                cons,
                list,
                empty,
            ],
        ))
    }

    pub(super) fn string_bytes_call(
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
        if requested != &name("String.ofByteArray") || !levels.is_empty() || arguments.len() > 2 {
            return Ok(None);
        }
        // Applied heads resolve replacements in the main dispatcher. A bare
        // constructor reaches this adapter first and retains the same priority.
        if let Some(replacement) = self.implemented_by_call(head, arguments)? {
            return Ok(Some(replacement));
        }
        if !self.string_bytes.verified {
            if !string_bytes::matches(
                self.environment,
                requested,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )? {
                return Ok(None);
            }
            let Some(ConstantInfo::Ctor(ctor)) = self.environment.find(requested) else {
                return Err(unsupported("String byte checked constructor"));
            };
            let type_ = self.erase_runtime_type(&ctor.base.type_)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = type_.node()
            else {
                return Err(unsupported("String byte checked constructor telescope"));
            };
            let ExprNode::ForallE {
                binder_type: proof_type,
                body: result,
                ..
            } = body.node()
            else {
                return Err(unsupported("String byte checked proof telescope"));
            };
            if binder_type != &c("ByteArray")
                || proof_type != &proofs::erased_type()
                || result != &c("String")
            {
                return Err(unsupported(
                    "String byte requires the checked erased validity proof",
                ));
            }
            self.string_bytes.verified = true;
        }
        let layout = self.string_bytes_layout()?;
        let packed = self.string_bytes_pack(&layout, b(1)?)?;
        let body = Expr::app(Expr::const_(Helper::String.name(), Vec::new()), packed);
        let wrapper = Expr::let_e(
            self.string_bytes_adapter_name()?,
            function(&[c("ByteArray"), proofs::erased_type()], c("String")),
            lambda(c("ByteArray"), lambda(proofs::erased_type(), body)),
            b(0)?,
            false,
        );
        Ok(Some(apply(wrapper, arguments.iter().cloned())))
    }
}
