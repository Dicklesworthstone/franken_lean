//! Convert between native file buffers and checked logical byte records.
//!
//! Packed bytes and native arrays never acquire the source ByteArray/Array
//! representation. A single native ByteArray.data conversion supplies a
//! private array, then metered Nat recursion builds exact logical constructors.
//! The native counted read refuses more than 64 KiB before touching the file;
//! the conversion additionally obeys the caller's instruction/stack budgets.
//! Writes fold the logical List in source order into a private packed buffer;
//! packing stays inside the deferred world action and obeys those same budgets.
use super::*;
use fln_vm::extern_row::{
    ArgumentOwnership as ContractArgumentOwnership, Ownership,
    ResultOwnership as ContractResultOwnership,
};

const PACKED: &str = "_fln_runtime_fs_packed_bytes";
const NATIVE_ARRAY: &str = "_fln_runtime_fs_native_byte_array";
const NATIVE_BYTE: &str = "_fln_runtime_fs_native_byte";
const NATIVE_WORD: &str = "_fln_runtime_fs_native_word";

#[derive(Clone)]
pub(super) struct WordLayout {
    pub(super) native: Expr,
    pub(super) logical: records::Shape,
    bits: records::Shape,
    finite: records::Shape,
    to_word: Name,
    of_nat: Name,
    to_nat: Name,
}

#[derive(Clone)]
pub(super) struct Layout {
    pub(super) word: WordLayout,
    pub(super) packed: Expr,
    native_array: Expr,
    byte_array: records::ShapeConstructor,
    array: records::ShapeConstructor,
    list: records::Shape,
    byte: records::ShapeConstructor,
    bits: records::ShapeConstructor,
    fin: records::ShapeConstructor,
    to_array: Name,
    size: Name,
    get: Name,
    to_nat: Name,
}

fn lambda(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn constructor(shape: &records::ShapeConstructor, fields: impl IntoIterator<Item = Expr>) -> Expr {
    apply(Expr::const_(shape.name.clone(), Vec::new()), fields)
}

#[derive(Clone, Copy)]
enum Helper {
    ToArray,
    Size,
    Get,
    ToNat,
    ToWord,
    WordOfNat,
    WordToNat,
    EmptyBytes,
    PushByte,
    FromNat,
    WordRepr,
    PlatformNumBits,
}

impl Helper {
    fn contract(self) -> (&'static str, &'static str, u32, u32, &'static str) {
        match self {
            Self::ToArray => (
                "ByteArray.data",
                "defn",
                0,
                1,
                "abi((a: owned_arg) -> owned_res)",
            ),
            Self::Size => (
                "Array.size",
                "defn",
                1,
                2,
                "abi((a: borrowed_arg) -> raw_object)",
            ),
            Self::Get => (
                "Array.getInternal",
                "defn",
                1,
                4,
                "abi((a: borrowed_arg, i: borrowed_arg) -> owned_res)",
            ),
            Self::ToNat => ("UInt8.toNat", "defn", 0, 1, "abi((a: value) -> owned_res)"),
            Self::ToWord => (
                "USize.ofBitVec",
                "ctor",
                0,
                1,
                "abi((a: owned_arg) -> value)",
            ),
            Self::WordOfNat => (
                "USize.ofNat",
                "defn",
                0,
                1,
                "abi((a: borrowed_arg) -> value)",
            ),
            Self::WordToNat => ("USize.toNat", "defn", 0, 1, "abi((n: value) -> owned_res)"),
            Self::WordRepr => ("USize.repr", "defn", 0, 1, "abi((value) -> owned_res)"),
            Self::PlatformNumBits => (
                "System.Platform.getNumBits",
                "opaque",
                0,
                1,
                "rule(borrowed-args,owned-result)",
            ),
            Self::EmptyBytes => (
                "ByteArray.emptyWithCapacity",
                "defn",
                0,
                1,
                "abi((capacity: borrowed_arg) -> owned_res)",
            ),
            Self::PushByte => (
                "ByteArray.push",
                "defn",
                0,
                2,
                "abi((a: owned_arg, b: value) -> owned_res)",
            ),
            Self::FromNat => (
                "UInt8.ofBitVec",
                "ctor",
                0,
                1,
                "abi((a: owned_arg) -> value)",
            ),
        }
    }
}

#[derive(Clone)]
pub(super) struct WriteLayout {
    empty: Name,
    push: Name,
    from_nat: Name,
}

impl Preparation<'_> {
    fn fs_bytes_helper(
        &mut self,
        helper: Helper,
        domains: Vec<Expr>,
        argument_types: Vec<ValueType>,
        result_type: Expr,
        result: ValueType,
    ) -> Result<Name, IngressError> {
        self.tick()?;
        let private = Name::num(name("_fln_runtime_fs_bytes_helper"), helper as u64);
        if self.environment.contains(&private) {
            return Err(unsupported("filesystem byte helper name collision"));
        }
        if self.fs.bindings.contains_key(&private) {
            return Ok(private);
        }
        let (source, kind, levels, arity, expected_ownership) = helper.contract();
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.name == source)
            .ok_or_else(|| unsupported("filesystem byte helper row"))?;
        if row.kind != kind
            || row.levels != levels
            || row.arity != arity
            || row.effect != "pure"
            || row.ownership != expected_ownership
        {
            return Err(unsupported("filesystem byte helper ABI contract"));
        }
        let ownership = Ownership::parse(row.ownership)
            .map_err(|_| unsupported("filesystem byte helper ownership"))?;
        let argument_ownership = ownership
            .argument_ownership(domains.len())
            .map_err(|_| unsupported("filesystem byte helper parameter ownership"))?
            .into_iter()
            .map(|value| match value {
                ContractArgumentOwnership::Borrowed => ArgumentOwnership::Borrowed,
                ContractArgumentOwnership::Owned => ArgumentOwnership::Owned,
                ContractArgumentOwnership::Unique => ArgumentOwnership::Unique,
                ContractArgumentOwnership::Scalar => ArgumentOwnership::Scalar,
            })
            .collect();
        let result_ownership = match ownership
            .result_ownership()
            .map_err(|_| unsupported("filesystem byte helper result ownership"))?
        {
            ContractResultOwnership::Owned => ResultOwnership::Owned,
            ContractResultOwnership::Borrowed => ResultOwnership::Borrowed,
            ContractResultOwnership::Scalar => ResultOwnership::Scalar,
            ContractResultOwnership::RawObject => ResultOwnership::RawObject,
        };
        self.fs.bindings.insert(
            private.clone(),
            (
                IntrinsicBinding {
                    name: private.clone(),
                    universe_arity: 0,
                    row: row.id.to_owned(),
                    arguments: argument_types,
                    argument_ownership,
                    result,
                    result_ownership,
                    effect: EffectClass::Pure,
                },
                function(&domains, result_type),
            ),
        );
        Ok(private)
    }

    fn fs_word_layout(&mut self) -> Result<WordLayout, IngressError> {
        if let Some(layout) = &self.fs.word {
            return Ok(layout.clone());
        }
        // The caller has matched either the complete filesystem contract or
        // the independent pure-word contract, including every native helper.
        // Logical USize/BitVec/Fin records never become native-word aliases.
        let word = self.io_checked_shape(c("USize"))?;
        let word_constructor = self.io_checked_single_constructor(c("USize"), 1)?;
        let word_bits = self.io_checked_shape(word_constructor.fields[0].clone())?;
        let word_bits_constructor =
            self.io_checked_single_constructor(word_constructor.fields[0].clone(), 1)?;
        let word_fin = self.io_checked_shape(word_bits_constructor.fields[0].clone())?;
        let word_fin_constructor =
            self.io_checked_single_constructor(word_bits_constructor.fields[0].clone(), 2)?;
        if word_fin_constructor.fields != [c("Nat"), proofs::erased_type()] {
            return Err(unsupported("checked USize finite word layout"));
        }
        let native_word = self.fs_abi_carrier(NATIVE_WORD, CallableResultOwnership::Owned)?;
        let to_word = self.fs_bytes_helper(
            Helper::ToWord,
            vec![c("Nat")],
            vec![ValueType::Nat],
            native_word.clone(),
            ValueType::Abi,
        )?;
        let word_of_nat = self.fs_bytes_helper(
            Helper::WordOfNat,
            vec![c("Nat")],
            vec![ValueType::Nat],
            native_word.clone(),
            ValueType::Abi,
        )?;
        let word_to_nat = self.fs_bytes_helper(
            Helper::WordToNat,
            vec![native_word.clone()],
            vec![ValueType::Abi],
            c("Nat"),
            ValueType::Nat,
        )?;
        let layout = WordLayout {
            native: native_word,
            logical: word,
            bits: word_bits,
            finite: word_fin,
            to_word,
            of_nat: word_of_nat,
            to_nat: word_to_nat,
        };
        self.fs.word = Some(layout.clone());
        Ok(layout)
    }

    pub(super) fn fs_bytes_layout(&mut self) -> Result<Layout, IngressError> {
        if let Some(layout) = &self.fs.bytes {
            return Ok(layout.clone());
        }
        // File reads and writes still establish their complete byte, word and
        // IO contracts before this cache is created. A pure word cache does
        // not grant authority to enter this separate file-buffer path.
        let word = self.fs_word_layout()?;
        let byte_array = self.io_checked_single_constructor(c("ByteArray"), 1)?;
        let array = self.io_checked_single_constructor(byte_array.fields[0].clone(), 1)?;
        let list = self.io_checked_shape(array.fields[0].clone())?;
        if list.constructors.len() != 2
            || list.constructors[0].tag != 0
            || !list.constructors[0].fields.is_empty()
            || list.constructors[1].tag != 1
            || list.constructors[1].fields != [c("UInt8"), list.source.clone()]
        {
            return Err(unsupported("filesystem checked byte list layout"));
        }
        let byte = self.io_checked_single_constructor(c("UInt8"), 1)?;
        let bits = self.io_checked_single_constructor(byte.fields[0].clone(), 1)?;
        let fin = self.io_checked_single_constructor(bits.fields[0].clone(), 2)?;
        if fin.fields != [c("Nat"), proofs::erased_type()] {
            return Err(unsupported("filesystem checked UInt8 finite word"));
        }
        let packed = self.fs_abi_carrier(PACKED, CallableResultOwnership::Owned)?;
        let native_array = self.fs_abi_carrier(NATIVE_ARRAY, CallableResultOwnership::Owned)?;
        let native_byte = self.fs_abi_carrier(NATIVE_BYTE, CallableResultOwnership::Scalar)?;
        let to_array = self.fs_bytes_helper(
            Helper::ToArray,
            vec![packed.clone()],
            vec![ValueType::Abi],
            native_array.clone(),
            ValueType::Abi,
        )?;
        let size = self.fs_bytes_helper(
            Helper::Size,
            vec![native_array.clone()],
            vec![ValueType::Abi],
            c("Nat"),
            ValueType::Nat,
        )?;
        let get = self.fs_bytes_helper(
            Helper::Get,
            vec![native_array.clone(), c("Nat")],
            vec![ValueType::Abi, ValueType::Nat],
            native_byte.clone(),
            ValueType::Abi,
        )?;
        let to_nat = self.fs_bytes_helper(
            Helper::ToNat,
            vec![native_byte],
            vec![ValueType::Abi],
            c("Nat"),
            ValueType::Nat,
        )?;
        let layout = Layout {
            word,
            packed,
            native_array,
            byte_array,
            array,
            list,
            byte,
            bits,
            fin,
            to_array,
            size,
            get,
            to_nat,
        };
        self.fs.bytes = Some(layout.clone());
        Ok(layout)
    }

    pub(super) fn fs_native_read_count(&mut self, value: Expr) -> Result<Expr, IngressError> {
        let layout = self.fs_bytes_layout()?.word;
        self.fs_native_word(&layout, value)
    }

    fn fs_word_natural(&mut self, layout: &WordLayout, value: Expr) -> Result<Expr, IngressError> {
        self.tick()?;
        let bits = Expr::proj(
            layout.logical.projection(&layout.logical.constructors[0]),
            0,
            value,
        );
        let fin = Expr::proj(
            layout.bits.projection(&layout.bits.constructors[0]),
            0,
            bits,
        );
        Ok(Expr::proj(
            layout.finite.projection(&layout.finite.constructors[0]),
            0,
            fin,
        ))
    }

    fn fs_native_word(&mut self, layout: &WordLayout, value: Expr) -> Result<Expr, IngressError> {
        self.tick()?;
        let natural = self.fs_word_natural(layout, value)?;
        // The admitted USize/BitVec/Fin bound proves this projection fits the
        // exact platform word. The genuine constructor row performs the ABI
        // boxing; a tagged Nat is never passed to Handle.read as USize.
        Ok(Expr::app(
            Expr::const_(layout.to_word.clone(), Vec::new()),
            natural,
        ))
    }

    fn fs_platform_bits_call(
        &mut self,
        requested: &Name,
        arguments: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        if !self.fs.word_platform_checked
            && !fs::word_matches(
                self.environment,
                requested,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )?
        {
            return Ok(None);
        }
        self.tick()?;
        let Some(ConstantInfo::Opaque(info)) = self.environment.find(requested) else {
            return Err(unsupported("checked platform width producer"));
        };
        let ExprNode::ForallE {
            binder_type, body, ..
        } = info.base.type_.node()
        else {
            return Err(unsupported("checked platform width telescope"));
        };
        if binder_type != &c("Unit") || !specialize::closed(body) {
            return Err(unsupported("closed platform width telescope"));
        }
        let unit = self.io_checked_shape(binder_type.clone())?;
        if unit.constructors.len() != 1
            || unit.constructors[0].tag != 0
            || !unit.constructors[0].fields.is_empty()
        {
            return Err(unsupported("checked platform unit argument"));
        }
        let result = self.io_checked_shape(body.clone())?;
        if result.constructors.len() != 1
            || result.constructors[0].tag != 0
            || result.constructors[0].fields != [c("Nat"), proofs::erased_type()]
        {
            return Err(unsupported("checked platform width subtype"));
        }
        // The genuine row ignores its one Unit argument and returns native
        // Nat after erasing the subtype proof. Retain the strict logical Unit
        // receiver, then rebuild the actual checked Subtype constructor. Its
        // native Nat never aliases the two-field logical subtype, and the
        // opaque declaration's default inhabitant is never executed.
        let producer = self.fs_bytes_helper(
            Helper::PlatformNumBits,
            vec![unit.source.clone()],
            vec![ValueType::Constructor],
            c("Nat"),
            ValueType::Nat,
        )?;
        let value = Expr::app(Expr::const_(producer, Vec::new()), b(0)?);
        let rebuilt = constructor(&result.constructors[0], [value, proofs::erased_value()]);
        let wrapper = Expr::let_e(
            self.fs_adapter_name()?,
            function(std::slice::from_ref(&unit.source), result.source),
            lambda(unit.source, rebuilt),
            b(0)?,
            false,
        );
        self.fs.word_platform_checked = true;
        Ok(Some(apply(wrapper, arguments.iter().cloned())))
    }

    /// The pin's USize.ofNat requires an opaque platform width. Invoke its
    /// exact genuine row, then rebuild logical records from the corresponding
    /// native toNat result; public USize never becomes a boxed-word alias.
    /// Its public toNat projection keeps a strict logical-word binder so
    /// administrative projection discovery cannot unfold an ofNat argument
    /// into the opaque platform width before the argument is prepared.
    pub(super) fn fs_word_call(
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
        if ![
            name("USize.ofNat"),
            name("USize.toNat"),
            name("USize.repr"),
            name("System.Platform.getNumBits"),
        ]
        .contains(requested)
            || !levels.is_empty()
            || arguments.len() > 1
        {
            return Ok(None);
        }
        // Application heads have already visited this selector; bare callable
        // constants reach us first. Both forms preserve an explicit checked
        // replacement before selecting the root's native word contract.
        if let Some(replacement) = self.implemented_by_call(head, arguments)? {
            return Ok(Some(replacement));
        }
        if requested == &name("System.Platform.getNumBits") {
            return self.fs_platform_bits_call(requested, arguments);
        }
        let repr = requested == &name("USize.repr");
        if (self.fs.word.is_none() || (repr && !self.fs.word_repr_checked))
            && !fs::word_matches(
                self.environment,
                requested,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )?
        {
            return Ok(None);
        }
        let layout = self.fs_word_layout()?;
        if repr {
            self.fs.word_repr_checked = true;
        }
        if requested == &name("USize.toNat") || repr {
            // This is the ordinary checked logical projection, not the
            // native-word row: its receiver is a USize/BitVec/Fin record.
            // Keeping it under a lambda also preserves strict evaluation and
            // sharing of arbitrary checked receiver expressions.
            let (result_type, result) = if repr {
                let printer = self.fs_bytes_helper(
                    Helper::WordRepr,
                    vec![layout.native.clone()],
                    vec![ValueType::Abi],
                    c("String"),
                    ValueType::String,
                )?;
                let native = self.fs_native_word(&layout, b(0)?)?;
                (
                    c("String"),
                    Expr::app(Expr::const_(printer, Vec::new()), native),
                )
            } else {
                (c("Nat"), self.fs_word_natural(&layout, b(0)?)?)
            };
            let wrapper = Expr::let_e(
                self.fs_adapter_name()?,
                function(std::slice::from_ref(&layout.logical.source), result_type),
                lambda(layout.logical.source, result),
                b(0)?,
                false,
            );
            return Ok(Some(apply(wrapper, arguments.iter().cloned())));
        }
        let boxed = Expr::app(Expr::const_(layout.of_nat, Vec::new()), b(0)?);
        let natural = Expr::app(Expr::const_(layout.to_nat, Vec::new()), boxed);
        let finite = constructor(
            &layout.finite.constructors[0],
            [natural, proofs::erased_value()],
        );
        let bits = constructor(&layout.bits.constructors[0], [finite]);
        let result = constructor(&layout.logical.constructors[0], [bits]);
        let wrapper = Expr::let_e(
            self.fs_adapter_name()?,
            function(&[c("Nat")], layout.logical.source),
            lambda(c("Nat"), result),
            b(0)?,
            false,
        );
        Ok(Some(apply(wrapper, arguments.iter().cloned())))
    }

    pub(super) fn fs_materialize_bytes(&mut self, packed: Expr) -> Result<Expr, IngressError> {
        let layout = self.fs_bytes_layout()?;
        let array_name = self.fs_adapter_name()?;
        // After the two strict bindings: #0=size, #1=native Array. The Nat.rec
        // step has #0=accumulator, #1=IH, #2=index, #3=size, #4=native Array.
        let raw = apply(Expr::const_(layout.get.clone(), Vec::new()), [b(4)?, b(2)?]);
        let natural = Expr::app(Expr::const_(layout.to_nat.clone(), Vec::new()), raw);
        let byte = constructor(
            &layout.byte,
            [constructor(
                &layout.bits,
                [constructor(&layout.fin, [natural, proofs::erased_value()])],
            )],
        );
        let cons = constructor(&layout.list.constructors[1], [byte, b(0)?]);
        let step = lambda(
            c("Nat"),
            lambda(
                function(
                    std::slice::from_ref(&layout.list.source),
                    layout.list.source.clone(),
                ),
                lambda(layout.list.source.clone(), Expr::app(b(1)?, cons)),
            ),
        );
        let motive = lambda(
            c("Nat"),
            function(
                std::slice::from_ref(&layout.list.source),
                layout.list.source.clone(),
            ),
        );
        let zero = lambda(layout.list.source.clone(), b(0)?);
        let nil = constructor(&layout.list.constructors[0], []);
        let values = apply(
            Expr::const_(name("Nat.rec"), vec![Level::one()]),
            [motive, zero, step, b(0)?, nil],
        );
        // Descending k=n-1..0, prepended to the accumulator, preserves byte
        // order. Every k is below the one immutable native Array.size, and
        // Array.getInternal additionally performs its normal runtime check.
        let result = constructor(&layout.byte_array, [constructor(&layout.array, [values])]);
        let size_binding = Expr::let_e(
            self.fs_adapter_name()?,
            c("Nat"),
            Expr::app(Expr::const_(layout.size.clone(), Vec::new()), b(0)?),
            result,
            false,
        );
        // The success-only payload refinement and conversion each occur once.
        // The error transport's scalar placeholder never reaches either.
        let packed_binding = Expr::let_e(
            self.fs_adapter_name()?,
            layout.packed,
            packed,
            Expr::let_e(
                array_name,
                layout.native_array,
                Expr::app(Expr::const_(layout.to_array, Vec::new()), b(0)?),
                size_binding,
                false,
            ),
            false,
        );
        Ok(packed_binding)
    }

    /// Convert a checked ByteArray/Array/List/UInt8 value before the native
    /// write. The source value stays logical; only this private result has
    /// the packed byte-array representation expected by Handle.write.
    pub(super) fn fs_native_write_bytes(&mut self, value: Expr) -> Result<Expr, IngressError> {
        let layout = self.fs_bytes_layout()?;
        let write = if let Some(write) = self.fs.write_bytes.clone() {
            write
        } else {
            let byte = self.fs_abi_carrier(NATIVE_BYTE, CallableResultOwnership::Scalar)?;
            let empty = self.fs_bytes_helper(
                Helper::EmptyBytes,
                vec![c("Nat")],
                vec![ValueType::Nat],
                layout.packed.clone(),
                ValueType::Abi,
            )?;
            let push = self.fs_bytes_helper(
                Helper::PushByte,
                vec![layout.packed.clone(), byte.clone()],
                vec![ValueType::Abi, ValueType::Abi],
                layout.packed.clone(),
                ValueType::Abi,
            )?;
            let from_nat = self.fs_bytes_helper(
                Helper::FromNat,
                vec![c("Nat")],
                vec![ValueType::Nat],
                byte,
                ValueType::Abi,
            )?;
            let write = WriteLayout {
                empty,
                push,
                from_nat,
            };
            self.fs.write_bytes = Some(write.clone());
            write
        };
        let accumulator = function(std::slice::from_ref(&layout.packed), layout.packed.clone());
        // Under the cons minor's four binders: #0=packed accumulator, #1=IH,
        // #2=tail, #3=head. The admitted Fin proof establishes the byte bound;
        // only its natural-number field reaches the genuine UInt8 constructor.
        let byte_projection = self.io_checked_shape(c("UInt8"))?.projection(&layout.byte);
        let bits_projection = self
            .io_checked_shape(layout.byte.fields[0].clone())?
            .projection(&layout.bits);
        let fin_projection = self
            .io_checked_shape(layout.bits.fields[0].clone())?
            .projection(&layout.fin);
        let bits = Expr::proj(byte_projection, 0, b(3)?);
        let finite = Expr::proj(bits_projection, 0, bits);
        let natural = Expr::proj(fin_projection, 0, finite);
        let byte = Expr::app(Expr::const_(write.from_nat, Vec::new()), natural);
        let pushed = apply(Expr::const_(write.push, Vec::new()), [b(0)?, byte]);
        let cons = lambda(
            c("UInt8"),
            lambda(
                layout.list.source.clone(),
                lambda(
                    accumulator.clone(),
                    lambda(layout.packed.clone(), Expr::app(b(1)?, pushed)),
                ),
            ),
        );
        let bytes_projection = self
            .io_checked_shape(c("ByteArray"))?
            .projection(&layout.byte_array);
        let array_projection = self
            .io_checked_shape(layout.byte_array.fields[0].clone())?
            .projection(&layout.array);
        let logical_array = Expr::proj(bytes_projection, 0, value);
        let list = Expr::proj(array_projection, 0, logical_array);
        let empty = Expr::app(Expr::const_(write.empty, Vec::new()), nat::literal(0));
        Ok(apply(
            Expr::const_(name("List.rec"), vec![Level::one(), Level::zero()]),
            [
                c("UInt8"),
                lambda(layout.list.source, accumulator),
                lambda(layout.packed, b(0)?),
                cons,
                list,
                empty,
            ],
        ))
    }
}
