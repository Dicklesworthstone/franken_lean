//! Private native scalar calls preserve the imported UInt/BitVec/Fin records.
//! Only complete pinned models authorize these post-admission adapters.
use super::*;
use std::collections::BTreeMap;

#[derive(Default)]
pub(in crate::runtime) struct Store {
    checked: bool,
    next_adapter: u64,
    bindings: BTreeMap<Name, (IntrinsicBinding, Expr)>,
    words: [Option<WordLayout>; 2],
}

#[derive(Clone)]
struct WordLayout {
    logical: records::Shape,
    bits: records::Shape,
    finite: records::Shape,
    of_nat: Name,
    to_nat: Name,
}

fn c(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}

fn apply(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

fn constructor(shape: &records::ShapeConstructor, fields: impl IntoIterator<Item = Expr>) -> Expr {
    apply(Expr::const_(shape.name.clone(), Vec::new()), fields)
}

fn function(domains: &[Expr], result: Expr) -> Expr {
    domains.iter().rev().fold(result, |body, domain| {
        Expr::forall_e(Name::anonymous(), domain.clone(), body, BinderInfo::Default)
    })
}

fn source_type(value: ValueType) -> Result<Expr, IngressError> {
    Ok(c(match value {
        ValueType::Nat => "Nat",
        ValueType::Bool => "Bool",
        ValueType::String => "String",
        ValueType::Float => "Float",
        ValueType::Float32 => "Float32",
        ValueType::UInt32 => "UInt32",
        ValueType::UInt64 => "UInt64",
        _ => return Err(unsupported("Float primitive scalar interface")),
    }))
}

impl Preparation<'_> {
    pub(crate) fn float_intrinsic_binding(&self, requested: &Name) -> Option<IntrinsicBinding> {
        self.floats
            .bindings
            .get(requested)
            .map(|(binding, _)| binding.clone())
    }

    pub(in crate::runtime) fn float_intrinsic_type(&self, requested: &Name) -> Option<Expr> {
        self.floats
            .bindings
            .get(requested)
            .map(|(_, type_)| type_.clone())
    }

    pub(super) fn imported_float_model(&mut self) -> Result<bool, IngressError> {
        self.tick()?;
        if !self.floats.checked {
            if !source_intrinsics::float::matches(
                self.environment,
                &mut self.externs,
                &mut self.implementations,
                &mut self.visited,
                self.limits,
            )? {
                return Ok(false);
            }
            self.floats.checked = true;
        }
        Ok(true)
    }

    fn float_native_type(&mut self, value: ValueType) -> Result<Expr, IngressError> {
        let label = match value {
            ValueType::UInt32 => "_fln_runtime_float_word32",
            ValueType::UInt64 => "_fln_runtime_float_word64",
            _ => return source_type(value),
        };
        self.tick()?;
        if self.environment.contains(&name(label)) {
            return Err(unsupported("Float private word carrier name collision"));
        }
        let type_ = c(label);
        let representation = (value, result_ownership(value));
        if let Some(known) = self.value_types.native.get(&type_) {
            if *known != representation {
                return Err(unsupported("Float private word carrier representation"));
            }
        } else {
            self.value_types.native.try_reserve(1).map_err(|_| {
                IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: self.value_types.native.len().saturating_add(1),
                }
            })?;
            self.value_types
                .native
                .insert(type_.clone(), representation);
        }
        Ok(type_)
    }

    pub(super) fn float_bind_primitive(&mut self, requested: &Name) -> Result<Name, IngressError> {
        self.tick()?;
        if !self.floats.checked || !source_intrinsics::float::is_primitive(requested) {
            return Err(unsupported(
                "Float primitive requires its complete admitted model",
            ));
        }
        let private = Name::str(
            name("_fln_runtime_float_native"),
            requested.to_display_string(),
        );
        if self.floats.bindings.contains_key(&private) {
            return Ok(private);
        }
        if self.environment.contains(&private) {
            return Err(unsupported("Float private primitive name collision"));
        }
        let mut binding = generated_source_intrinsic_binding(requested)
            .ok_or_else(|| unsupported("Float generated primitive contract"))?;
        let mut domains = Vec::new();
        for &argument in &binding.arguments {
            reserve(&mut domains, self.limits.max_application_args)?;
            domains.push(self.float_native_type(argument)?);
        }
        let result = self.float_native_type(binding.result)?;
        binding.name = private.clone();
        self.floats
            .bindings
            .insert(private.clone(), (binding, function(&domains, result)));
        Ok(private)
    }

    fn float_word_layout(&mut self, value: ValueType) -> Result<WordLayout, IngressError> {
        let (index, label) = match value {
            ValueType::UInt32 => (0, "UInt32"),
            ValueType::UInt64 => (1, "UInt64"),
            _ => return Err(unsupported("Float logical word width")),
        };
        if let Some(layout) = &self.floats.words[index] {
            return Ok(layout.clone());
        }
        let logical = self.io_checked_shape(c(label))?;
        let [word] = logical.constructors.as_slice() else {
            return Err(unsupported("Float logical word constructor"));
        };
        if word.tag != 0 || word.fields.len() != 1 {
            return Err(unsupported("Float logical word field"));
        }
        let bits = self.io_checked_shape(word.fields[0].clone())?;
        let [bit_constructor] = bits.constructors.as_slice() else {
            return Err(unsupported("Float logical BitVec constructor"));
        };
        if bit_constructor.tag != 0 || bit_constructor.fields.len() != 1 {
            return Err(unsupported("Float logical BitVec field"));
        }
        let finite = self.io_checked_shape(bit_constructor.fields[0].clone())?;
        let [fin_constructor] = finite.constructors.as_slice() else {
            return Err(unsupported("Float logical Fin constructor"));
        };
        if fin_constructor.tag != 0 || fin_constructor.fields != [c("Nat"), proofs::erased_type()] {
            return Err(unsupported("Float checked finite word bound"));
        }
        let of_nat = self.float_bind_primitive(&Name::str(name(label), "ofNat"))?;
        let to_nat = self.float_bind_primitive(&Name::str(name(label), "toNat"))?;
        let layout = WordLayout {
            logical,
            bits,
            finite,
            of_nat,
            to_nat,
        };
        self.floats.words[index] = Some(layout.clone());
        Ok(layout)
    }

    fn float_pack_word(&mut self, type_: ValueType, value: Expr) -> Result<Expr, IngressError> {
        let layout = self.float_word_layout(type_)?;
        let bits = Expr::proj(
            layout.logical.projection(&layout.logical.constructors[0]),
            0,
            value,
        );
        let finite = Expr::proj(
            layout.bits.projection(&layout.bits.constructors[0]),
            0,
            bits,
        );
        let natural = Expr::proj(
            layout.finite.projection(&layout.finite.constructors[0]),
            0,
            finite,
        );
        // The checked Fin bound supplies the range. The real ofNat extern
        // performs native boxing; no logical record is passed as a scalar.
        Ok(Expr::app(Expr::const_(layout.of_nat, Vec::new()), natural))
    }

    fn float_unpack_word(&mut self, type_: ValueType, value: Expr) -> Result<Expr, IngressError> {
        let layout = self.float_word_layout(type_)?;
        let natural = Expr::app(Expr::const_(layout.to_nat, Vec::new()), value);
        let finite = constructor(
            &layout.finite.constructors[0],
            [natural, proofs::erased_value()],
        );
        let bits = constructor(&layout.bits.constructors[0], [finite]);
        Ok(constructor(&layout.logical.constructors[0], [bits]))
    }

    pub(in crate::runtime) fn imported_float_call(
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
        if !levels.is_empty()
            || !source_intrinsics::float::is_primitive(requested)
            || source_intrinsic_binding(self.environment, requested).is_some()
        {
            return Ok(None);
        }
        if let Some(replacement) = self.implemented_by_call(head, arguments)? {
            return Ok(Some(replacement));
        }
        if !self.imported_float_model()? {
            return Ok(None);
        }
        let binding = generated_source_intrinsic_binding(requested)
            .ok_or_else(|| unsupported("Float generated source interface"))?;
        if arguments.len() > binding.arguments.len() {
            return Ok(None);
        }
        let primitive = self.float_bind_primitive(requested)?;
        let has_words = binding
            .arguments
            .iter()
            .chain(std::iter::once(&binding.result))
            .any(|value| matches!(value, ValueType::UInt32 | ValueType::UInt64));
        if !has_words {
            return Ok(Some(apply(
                Expr::const_(primitive, Vec::new()),
                arguments.iter().cloned(),
            )));
        }
        let mut domains = Vec::new();
        let mut operands = Vec::new();
        for (index, &type_) in binding.arguments.iter().enumerate() {
            reserve(&mut domains, self.limits.max_application_args)?;
            reserve(&mut operands, self.limits.max_application_args)?;
            domains.push(source_type(type_)?);
            let index = u32::try_from(binding.arguments.len() - index - 1)
                .map_err(|_| unsupported("Float adapter binder scope"))?;
            let argument =
                Expr::bvar(index).map_err(|_| unsupported("Float adapter binder scope"))?;
            operands.push(if matches!(type_, ValueType::UInt32 | ValueType::UInt64) {
                self.float_pack_word(type_, argument)?
            } else {
                argument
            });
        }
        let mut body = apply(Expr::const_(primitive, Vec::new()), operands);
        if matches!(binding.result, ValueType::UInt32 | ValueType::UInt64) {
            body = self.float_unpack_word(binding.result, body)?;
        }
        let type_ = function(&domains, source_type(binding.result)?);
        for domain in domains.into_iter().rev() {
            body = Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default);
        }
        self.tick()?;
        let serial = self.floats.next_adapter;
        self.floats.next_adapter = serial
            .checked_add(1)
            .ok_or_else(|| unsupported("Float adapter identity"))?;
        let label = Name::num(name("_fln_runtime_float_scope"), serial);
        if self.environment.contains(&label) {
            return Err(unsupported("Float adapter name collision"));
        }
        // Keep strict public arguments outside projection discovery, including
        // partially applied and first-class word conversions.
        let wrapper = Expr::let_e(
            label,
            type_,
            body,
            Expr::bvar(0).map_err(|_| unsupported("Float adapter binder scope"))?,
            false,
        );
        Ok(Some(apply(wrapper, arguments.iter().cloned())))
    }
}
