//! Shared reconstruction of checked logical IO data from private transports.
//!
//! Callers first validate the complete IO/world, error and finite-word models.
//! These helpers only register post-admission runtime layouts; they never add
//! declarations to the environment or accept native packed fields as logical
//! values. Each native producer separately proves its transport's shape.

use super::*;
use crate::source_intrinsics::io::results::{self, ErrorFields};
use fln_comp::ingress::ConstructorBinding;

#[derive(Clone)]
pub(super) struct ErrorLayout {
    pub(super) error: records::Shape,
    option: records::Shape,
    pub(super) unit_constructor: Name,
    word_constructor: Name,
    bits_constructor: Name,
    fin_constructor: Name,
}

fn c(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}

fn apply(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

fn function(domains: &[Expr], result: Expr) -> Expr {
    domains.iter().rev().fold(result, |body, domain| {
        Expr::forall_e(Name::anonymous(), domain.clone(), body, BinderInfo::Default)
    })
}

pub(super) fn choose(type_: Expr, condition: Expr, no: Expr, yes: Expr) -> Expr {
    // All adapter result types are closed. Ordinary Boolean recursor lowering
    // keeps these branches lazy, including the error payload's unused fields.
    apply(
        Expr::const_(name("Bool.rec"), vec![Level::one()]),
        [
            Expr::lam(Name::anonymous(), c("Bool"), type_, BinderInfo::Default),
            no,
            yes,
            condition,
        ],
    )
}

impl Preparation<'_> {
    pub(super) fn io_checked_shape(
        &mut self,
        source: Expr,
    ) -> Result<records::Shape, IngressError> {
        let source = self.erase_runtime_type(&source)?;
        if self.value_type(&source)? != Some(ValueType::Constructor) {
            return Err(unsupported(
                "native IO requires a checked logical data layout",
            ));
        }
        self.record_shape(&source)?
            .ok_or_else(|| unsupported("native IO checked data layout"))
    }

    pub(super) fn io_checked_single_constructor(
        &mut self,
        source: Expr,
        fields: usize,
    ) -> Result<records::ShapeConstructor, IngressError> {
        let shape = self.io_checked_shape(source)?;
        let [constructor] = shape.constructors.as_slice() else {
            return Err(unsupported("native IO logical structure constructor"));
        };
        if constructor.tag != 0 || constructor.fields.len() != fields {
            return Err(unsupported("native IO logical structure field count"));
        }
        Ok(constructor.clone())
    }

    /// Validate the runtime layout after the source model has matched. No
    /// stdout getter or filesystem extern authority is implied by these data.
    pub(super) fn io_error_layout(&mut self) -> Result<ErrorLayout, IngressError> {
        let error = self.io_checked_shape(c("IO.Error"))?;
        if error.constructors.len() != results::error_cases().len() {
            return Err(unsupported("native IO logical error variants"));
        }
        let option = self.io_checked_shape(Expr::app(
            Expr::const_(name("Option"), vec![Level::zero()]),
            c("String"),
        ))?;
        if option.constructors.len() != 2
            || !option.constructors[0].fields.is_empty()
            || option.constructors[1].fields != [c("String")]
        {
            return Err(unsupported("native IO optional filename layout"));
        }
        let unit = self.io_checked_single_constructor(c("Unit"), 0)?;
        let word = self.io_checked_single_constructor(c("UInt32"), 1)?;
        let bits = self.io_checked_single_constructor(word.fields[0].clone(), 1)?;
        let fin = self.io_checked_single_constructor(bits.fields[0].clone(), 2)?;
        if fin.fields != [c("Nat"), proofs::erased_type()] {
            return Err(unsupported("native IO erased finite-word layout"));
        }
        Ok(ErrorLayout {
            error,
            option,
            unit_constructor: unit.name,
            word_constructor: word.name,
            bits_constructor: bits.name,
            fin_constructor: fin.name,
        })
    }

    /// The native producer/consumer contract is the authority for each private
    /// carrier. These names never enter either checker or logical environment.
    pub(super) fn io_private_record(
        &mut self,
        label: &str,
        fields: Vec<Expr>,
    ) -> Result<Expr, IngressError> {
        let family = name(label);
        let constructor = Name::str(family.clone(), "mk");
        let source = Expr::const_(family.clone(), Vec::new());
        if self.environment.contains(&family) || self.environment.contains(&constructor) {
            return Err(unsupported("native IO private carrier name collision"));
        }
        if self.data_shapes.contains_key(&source) {
            return Ok(source);
        }
        let mut values = Vec::new();
        for field in &fields {
            self.tick()?;
            let value = self
                .value_type(field)?
                .ok_or_else(|| unsupported("native IO private field representation"))?;
            reserve(&mut values, self.limits.max_context_depth)?;
            values.push(value);
        }
        reserve(&mut self.constructors, self.limits.fir.max_constructors)?;
        self.constructors.push(ConstructorBinding {
            name: constructor.clone(),
            projection_structure: Some(family.clone()),
            universe_arity: 0,
            tag: 0,
            fields: values,
            static_scalar_bytes: Vec::new(),
        });
        self.remember_constructor_type(constructor.clone(), function(&fields, source.clone()))?;
        self.value_types
            .records
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: self.value_types.records.len().saturating_add(1),
            })?;
        self.value_types.records.insert(source.clone());
        self.data_shapes
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: self.data_shapes.len().saturating_add(1),
            })?;
        self.data_shapes.insert(
            source.clone(),
            records::Shape {
                source: source.clone(),
                name: family,
                recursive: false,
                constructors: vec![records::ShapeConstructor {
                    original: constructor.clone(),
                    name: constructor,
                    tag: 0,
                    type_fields: vec![false; fields.len()],
                    fields,
                }],
            },
        );
        Ok(source)
    }

    /// The input fields are (error tag, u32 code, has filename, filename,
    /// details). The safe native producer has already checked their ranges and
    /// shape. Only admitted logical constructors build the resulting IO.Error.
    pub(super) fn io_transport_error(
        &mut self,
        layout: &ErrorLayout,
        fields: [Expr; 5],
    ) -> Result<Expr, IngressError> {
        let [tag, code, has_file, filename, details] = fields;
        self.tick()?;
        let fin = apply(
            Expr::const_(layout.fin_constructor.clone(), Vec::new()),
            [code, proofs::erased_value()],
        );
        let code = Expr::app(
            Expr::const_(layout.word_constructor.clone(), Vec::new()),
            Expr::app(
                Expr::const_(layout.bits_constructor.clone(), Vec::new()),
                fin,
            ),
        );
        let optional_file = choose(
            layout.option.source.clone(),
            has_file,
            Expr::const_(layout.option.constructors[0].name.clone(), Vec::new()),
            Expr::app(
                Expr::const_(layout.option.constructors[1].name.clone(), Vec::new()),
                filename.clone(),
            ),
        );
        let mut branches = Vec::new();
        for ((_, shape), constructor) in results::error_cases()
            .into_iter()
            .zip(&layout.error.constructors)
        {
            self.tick()?;
            let fields = match shape {
                ErrorFields::OptionalFileCodeDetails => {
                    vec![optional_file.clone(), code.clone(), details.clone()]
                }
                ErrorFields::CodeDetails => vec![code.clone(), details.clone()],
                ErrorFields::FileCodeDetails => {
                    vec![filename.clone(), code.clone(), details.clone()]
                }
                ErrorFields::Empty => Vec::new(),
                ErrorFields::Message => vec![details.clone()],
            };
            reserve(&mut branches, self.limits.max_context_depth)?;
            branches.push(apply(
                Expr::const_(constructor.name.clone(), Vec::new()),
                fields,
            ));
        }
        // Native transports accept only 0..18. The final branch is tag 18;
        // there is no fallback meaning for an unknown native error tag.
        let mut result = branches
            .pop()
            .ok_or_else(|| unsupported("native IO error cases"))?;
        for (index, branch) in branches.into_iter().enumerate().rev() {
            self.tick()?;
            let condition = apply(c("Nat.beq"), [tag.clone(), nat::literal(index as u64)]);
            result = choose(layout.error.source.clone(), condition, result, branch);
        }
        Ok(result)
    }
}
