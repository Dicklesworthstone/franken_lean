//! Checked Array source values use Golem's native copy-on-write arrays.
//!
//! The logical Array remains a List wrapper in both checkers. Only the
//! post-admission runtime translation changes its representation. One erased
//! ABI binding per operation serves every element type; typed recovery
//! functions restore data and callable payloads at ordinary checked boundaries.
use super::*;
use crate::source_intrinsics::arrays::{self, Operation};
use fln_comp::fir::EffectClass;
use fln_comp::flbc::{ArgumentOwnership, ResultOwnership};

const HANDLE: &str = "_fln_runtime_array_handle";
const PAYLOAD: &str = "_fln_runtime_array_payload";

#[derive(Default)]
pub(super) struct Store {
    family: Option<bool>,
    operations: [bool; Operation::ALL.len()],
    bindings: [Option<(IntrinsicBinding, Expr)>; Operation::ALL.len()],
    next: u64,
    payloads: std::collections::HashMap<Expr, Name>,
    recoveries: BTreeMap<Name, (Expr, ValueType)>,
    modify: Option<Name>,
}

fn c(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}

fn b(index: u32) -> Result<Expr, IngressError> {
    Expr::bvar(index).map_err(|_| unsupported("Array adapter binder scope"))
}

fn function(domains: &[Expr], result: Expr) -> Expr {
    domains.iter().rev().fold(result, |body, domain| {
        Expr::forall_e(Name::anonymous(), domain.clone(), body, BinderInfo::Default)
    })
}

fn application(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

fn family(level: &Level, payload: &Expr) -> Expr {
    Expr::app(
        Expr::const_(name("Array"), vec![level.clone()]),
        payload.clone(),
    )
}

fn list(level: &Level, payload: &Expr) -> Expr {
    Expr::app(
        Expr::const_(name("List"), vec![level.clone()]),
        payload.clone(),
    )
}

pub(super) fn canonical_modify_pair(source: &Name, selected: &Name) -> bool {
    source == &name("Array.modifyM") && selected == &name("Array.modifyMUnsafe")
}

impl Preparation<'_> {
    /// The pin's unsafe implementation clears a slot with `unsafeCast ()` to
    /// improve element uniqueness. Its checked logical body preserves callback
    /// order and bounds without putting an untyped value into native storage.
    /// Only the complete canonical pair authorizes this private executable copy.
    pub(super) fn array_modify_target(&mut self) -> Result<Name, IngressError> {
        self.tick()?;
        if let Some(adapter) = &self.arrays.modify {
            return Ok(adapter.clone());
        }
        arrays::modify_matches(
            self.environment,
            self.implementations
                .as_ref()
                .expect("Array modify implementation edge was already validated"),
            self.runtime_initializers,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        let Some(ConstantInfo::Defn(original)) = self.environment.find(&name("Array.modifyM"))
        else {
            return Err(unsupported(
                "Array modify requires its safe logical interface",
            ));
        };
        if original.safety != DefinitionSafety::Safe {
            return Err(unsupported(
                "Array modify requires its safe logical interface",
            ));
        }
        let mut definition = original.clone();
        let private = name("_fln_runtime_array_modifyM");
        definition.base.name = private.clone();
        definition.hints = ReducibilityHints::Abbrev;
        definition.all.clear();
        self.remember_array_definition(definition)?;
        self.arrays.modify = Some(private.clone());
        Ok(private)
    }

    pub(crate) fn array_intrinsic_binding(&self, requested: &Name) -> Option<IntrinsicBinding> {
        self.arrays
            .bindings
            .iter()
            .flatten()
            .find(|(binding, _)| &binding.name == requested)
            .map(|(binding, _)| binding.clone())
    }

    pub(super) fn array_intrinsic_type(&self, requested: &Name) -> Option<Expr> {
        self.arrays
            .bindings
            .iter()
            .flatten()
            .find(|(binding, _)| &binding.name == requested)
            .map(|(_, type_)| type_.clone())
    }

    /// Binary IO and directory enumeration carry private native arrays through
    /// erased types. Keep the generic Array primitive as the one row authority;
    /// ordinary typed forwarding functions recover each adapter's payload.
    /// This also makes discovery order immaterial: a concrete directory entry
    /// getter must never become the primitive used to read an Array Nat.
    pub(crate) fn array_intrinsic_alias(
        &mut self,
        binding: &IntrinsicBinding,
        intrinsics: &mut Vec<IntrinsicBinding>,
        functions: &mut Vec<FunctionBinding>,
    ) -> Result<bool, IngressError> {
        let Some(native) = self
            .arrays
            .bindings
            .iter()
            .flatten()
            .map(|(binding, _)| binding)
            .find(|native| native.row == binding.row)
            .cloned()
        else {
            return Ok(false);
        };
        if !self.array_alias_matches(binding, &native)? {
            return Ok(false);
        }
        if let Some(index) = intrinsics.iter().position(|known| known.row == native.row) {
            let known = intrinsics[index].clone();
            if !self.array_alias_matches(&known, &native)? {
                return Err(unsupported("Array helper aliases disagree"));
            }
            if known.name != native.name {
                self.array_alias_function(&known, &native.name, functions)?;
                intrinsics[index] = native.clone();
            }
        } else {
            intrinsics
                .try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: intrinsics.len().saturating_add(1),
                })?;
            intrinsics.push(native.clone());
        }
        if binding.name != native.name {
            self.array_alias_function(binding, &native.name, functions)?;
        }
        Ok(true)
    }

    fn array_alias_matches(
        &mut self,
        binding: &IntrinsicBinding,
        native: &IntrinsicBinding,
    ) -> Result<bool, IngressError> {
        self.tick()?;
        if binding == native {
            return Ok(true);
        }
        if self.fs_intrinsic_binding(&binding.name).as_ref() != Some(binding) {
            return Ok(false);
        }
        let mut normalized = binding.clone();
        normalized.name = native.name.clone();
        if normalized.arguments.first() == Some(&ValueType::Abi)
            && native.arguments.first() == Some(&ValueType::Array)
        {
            normalized.arguments[0] = ValueType::Array;
        }
        if normalized.result == ValueType::Constructor && native.result == ValueType::Abi {
            normalized.result = ValueType::Abi;
        }
        if &normalized != native {
            return Err(unsupported("Array helper aliases disagree"));
        }
        Ok(true)
    }

    fn array_alias_function(
        &mut self,
        binding: &IntrinsicBinding,
        target: &Name,
        functions: &mut Vec<FunctionBinding>,
    ) -> Result<(), IngressError> {
        reserve(functions, self.limits.fir.max_functions.saturating_sub(1))?;
        let mut body = Expr::const_(target.clone(), vec![]);
        for index in (0..binding.arguments.len()).rev() {
            self.tick()?;
            body = Expr::app(
                body,
                b(u32::try_from(index).map_err(|_| unsupported("Array alias binder scope"))?)?,
            );
        }
        functions.push(FunctionBinding {
            name: binding.name.clone(),
            universe_arity: binding.universe_arity,
            parameters: binding.arguments.clone(),
            parameter_ownership: binding.argument_ownership.clone(),
            result: binding.result,
            result_ownership: result_ownership(binding.result),
            body,
        });
        Ok(())
    }

    pub(super) fn array_function_type(&self, requested: &Name) -> Option<Expr> {
        self.arrays
            .recoveries
            .get(requested)
            .map(|(type_, _)| type_.clone())
    }

    pub(crate) fn array_function_signature(
        &self,
        requested: &Name,
    ) -> Result<Option<ExecutableSignature>, IngressError> {
        let Some((_, result)) = self.arrays.recoveries.get(requested) else {
            return Ok(None);
        };
        Ok(Some(ExecutableSignature {
            parameters: vec![ValueType::Abi],
            result: *result,
            result_ownership: result_ownership(*result),
            body: b(0)?,
        }))
    }

    fn array_name(&mut self) -> Result<Name, IngressError> {
        self.tick()?;
        let serial = self.arrays.next;
        self.arrays.next = serial
            .checked_add(1)
            .ok_or_else(|| unsupported("Array adapter identity"))?;
        let private = Name::num(name("_fln_runtime_array_scope"), serial);
        if self.environment.contains(&private) || self.has_private_callable(&private) {
            return Err(unsupported("Array adapter name collision"));
        }
        Ok(private)
    }

    pub(super) fn native_arrays_enabled(&mut self) -> Result<bool, IngressError> {
        self.tick()?;
        if let Some(checked) = self.arrays.family {
            return Ok(checked);
        }
        self.implementations()?;
        let checked = arrays::family_matches(
            self.environment,
            self.implementations
                .as_ref()
                .expect("checked implementation journal"),
            self.runtime_initializers,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        self.arrays.family = Some(checked);
        Ok(checked)
    }

    pub(super) fn array_record_forbidden(&mut self, family: &Name) -> Result<bool, IngressError> {
        Ok(family == &name("Array") && self.native_arrays_enabled()?)
    }

    /// A selected implementation may target an Array primitive directly. It
    /// receives the same complete contract as a source call before its extern
    /// can count as executable authority.
    pub(super) fn native_array_operation(
        &mut self,
        requested: &Name,
    ) -> Result<bool, IngressError> {
        let Some(operation) = Operation::from_name(requested) else {
            return Ok(false);
        };
        Ok(self.array_primitive(operation)?.is_some())
    }

    fn array_representation(
        &mut self,
        type_: Expr,
        value: ValueType,
        ownership: CallableResultOwnership,
    ) -> Result<(), IngressError> {
        self.tick()?;
        let expected = (value, ownership);
        if let Some(existing) = self.value_types.native.get(&type_) {
            if *existing != expected {
                return Err(unsupported("Array runtime representation conflict"));
            }
            return Ok(());
        }
        let observed = self.value_types.native.len().saturating_add(1);
        if observed > self.limits.max_nodes {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ProgramTables,
                limit: self.limits.max_nodes,
                observed,
            });
        }
        self.value_types
            .native
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: observed,
            })?;
        self.value_types.native.insert(type_, expected);
        Ok(())
    }

    /// Keep the source type as a key so projection/type inference can recover
    /// the element type. An authenticated native array has no constructor slot.
    pub(super) fn array_value_type(&mut self, source: &Expr) -> Result<bool, IngressError> {
        let (head, arguments) = self.spine(source)?;
        if !matches!(head.node(), ExprNode::Const { name: family, levels }
            if family == &name("Array") && levels.len() == 1)
            || arguments.len() != 1
            || !specialize::closed(source)
            || !self.native_arrays_enabled()?
        {
            return Ok(false);
        }
        self.array_representation(
            source.clone(),
            ValueType::Array,
            CallableResultOwnership::Owned,
        )?;
        Ok(true)
    }

    pub(super) fn array_element_type(
        &mut self,
        source: &Expr,
    ) -> Result<Option<(Level, Expr)>, IngressError> {
        // Element types can contain erased value parameters. Discover only
        // the Array head; the payload's layout owns their later erasure.
        let source = self.type_head(source)?;
        if !self.array_value_type(&source)? {
            return Ok(None);
        }
        let (head, arguments) = self.spine(&source)?;
        let ExprNode::Const { levels, .. } = head.node() else {
            return Err(unsupported("native Array source family"));
        };
        let ([level], [payload]) = (levels.as_slice(), arguments.as_slice()) else {
            return Err(unsupported("native Array source parameters"));
        };
        Ok(Some((level.clone(), payload.clone())))
    }

    fn array_primitive(&mut self, operation: Operation) -> Result<Option<Expr>, IngressError> {
        let index = operation.index();
        if let Some(private) = self.arrays.bindings[index]
            .as_ref()
            .map(|(binding, _)| binding.name.clone())
        {
            self.tick()?;
            return Ok(Some(Expr::const_(private, vec![])));
        }
        if !self.native_arrays_enabled()? {
            return Ok(None);
        }
        if !self.arrays.operations[index] {
            if !arrays::operation_matches(
                self.environment,
                operation,
                self.implementations
                    .as_ref()
                    .expect("checked implementation journal"),
                self.runtime_initializers,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )? {
                return Ok(None);
            }
            self.arrays.operations[index] = true;
        }
        let primitive = Name::num(name("_fln_runtime_array_abi"), index as u64);
        for label in [name(HANDLE), name(PAYLOAD), primitive.clone()] {
            if self.environment.contains(&label) || self.has_private_callable(&label) {
                return Err(unsupported("Array private name collision"));
            }
        }
        self.array_representation(c(HANDLE), ValueType::Array, CallableResultOwnership::Owned)?;
        self.array_representation(c(PAYLOAD), ValueType::Abi, CallableResultOwnership::Erased)?;
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.name == operation.label())
            .ok_or_else(|| unsupported("generated Array extern row"))?;
        if row.levels != 1
            || row.arity as usize != operation.source_arity()
            || row.kind
                != if operation == Operation::FromList {
                    "ctor"
                } else {
                    "defn"
                }
            || row.effect != "pure"
            || row.safety != "safe"
            || row.entry_class != "standard"
            || row.entry_scope != "all"
        {
            return Err(unsupported("generated Array ABI contract"));
        }
        let (domains, result_type, result) = match operation {
            Operation::FromList => (vec![c(PAYLOAD)], c(HANDLE), ValueType::Array),
            Operation::ToList => (vec![c(HANDLE)], c(PAYLOAD), ValueType::Abi),
            Operation::Empty | Operation::MkEmpty => (vec![c("Nat")], c(HANDLE), ValueType::Array),
            Operation::Push => (vec![c(HANDLE), c(PAYLOAD)], c(HANDLE), ValueType::Array),
            Operation::Size => (vec![c(HANDLE)], c("Nat"), ValueType::Nat),
            Operation::Get => (vec![c(HANDLE), c("Nat")], c(PAYLOAD), ValueType::Abi),
            Operation::Set => (
                vec![c(HANDLE), c("Nat"), c(PAYLOAD)],
                c(HANDLE),
                ValueType::Array,
            ),
            Operation::Pop => (vec![c(HANDLE)], c(HANDLE), ValueType::Array),
        };
        let ownership = fln_vm::extern_row::Ownership::parse(row.ownership)
            .map_err(|_| unsupported("generated Array ownership contract"))?;
        let mut argument_ownership = Vec::new();
        for disposition in ownership
            .argument_ownership(domains.len())
            .map_err(|_| unsupported("generated Array argument ownership"))?
        {
            use fln_vm::extern_row::ArgumentOwnership as Contract;
            argument_ownership.push(match disposition {
                Contract::Borrowed => ArgumentOwnership::Borrowed,
                Contract::Owned => ArgumentOwnership::Owned,
                Contract::Scalar => ArgumentOwnership::Scalar,
                Contract::Unique => return Err(unsupported("Array primitive requires uniqueness")),
            });
        }
        let result_ownership = match ownership
            .result_ownership()
            .map_err(|_| unsupported("generated Array result ownership"))?
        {
            fln_vm::extern_row::ResultOwnership::Owned => ResultOwnership::Owned,
            fln_vm::extern_row::ResultOwnership::RawObject => ResultOwnership::RawObject,
            _ => return Err(unsupported("generated Array result ownership")),
        };
        let arguments = domains
            .iter()
            .map(|domain| {
                executable_value_type(domain, &self.value_types)
                    .map(|(value, _)| value)
                    .ok_or_else(|| unsupported("Array primitive representation"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        self.arrays.bindings[index] = Some((
            IntrinsicBinding {
                name: primitive.clone(),
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
        Ok(Some(Expr::const_(primitive, vec![])))
    }

    fn array_typed(&mut self, value: Expr, type_: Expr) -> Result<Expr, IngressError> {
        Ok(Expr::let_e(self.array_name()?, type_, value, b(0)?, false))
    }

    fn array_payload(&mut self, source: &Expr) -> Result<Expr, IngressError> {
        if self.type_parameter(source)? {
            return Ok(proofs::erased_type());
        }
        let payload = self.erase_runtime_type(source)?;
        if !specialize::closed(&payload) || self.value_type(&payload)?.is_none() {
            return Err(unsupported("Array element representation"));
        }
        Ok(payload)
    }

    fn array_recover(&mut self, value: Expr, payload: &Expr) -> Result<Expr, IngressError> {
        self.tick()?;
        let private = if let Some(known) = self.arrays.payloads.get(payload) {
            known.clone()
        } else {
            let result = self
                .value_type(payload)?
                .ok_or_else(|| unsupported("Array recovered payload representation"))?;
            let observed = self.arrays.payloads.len().saturating_add(1);
            let limit = self.limits.fir.max_functions.saturating_sub(1);
            if observed > limit {
                return Err(IngressError::ResourceLimit {
                    resource: IngressResource::ProgramTables,
                    limit,
                    observed,
                });
            }
            self.arrays
                .payloads
                .try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: observed,
                })?;
            let private = self.array_name()?;
            self.arrays.recoveries.insert(
                private.clone(),
                (function(&[c(PAYLOAD)], payload.clone()), result),
            );
            self.arrays
                .payloads
                .insert(payload.clone(), private.clone());
            private
        };
        self.array_typed(
            Expr::app(Expr::const_(private, vec![]), value),
            payload.clone(),
        )
    }

    fn array_wrapper(
        &mut self,
        operation: Operation,
        level: &Level,
        alpha: &Expr,
    ) -> Result<Option<Expr>, IngressError> {
        let Some(primitive) = self.array_primitive(operation)? else {
            return Ok(None);
        };
        let payload = self.array_payload(alpha)?;
        let family = family(level, alpha);
        if !self.array_value_type(&family)? {
            return Err(unsupported("native Array runtime family"));
        }
        let (domains, result, body) = match operation {
            Operation::FromList => {
                let list = list(level, alpha);
                self.value_type(&list)?
                    .ok_or_else(|| unsupported("Array source list layout"))?;
                (vec![list], family, Expr::app(primitive, b(0)?))
            }
            Operation::ToList => {
                let list = list(level, alpha);
                let body = self.array_recover(Expr::app(primitive, b(0)?), &list)?;
                (vec![family], list, body)
            }
            Operation::Empty | Operation::MkEmpty => {
                (vec![c("Nat")], family, Expr::app(primitive, b(0)?))
            }
            Operation::Push => (
                vec![family.clone(), payload],
                family,
                application(primitive, [b(1)?, b(0)?]),
            ),
            Operation::Size => (vec![family], c("Nat"), Expr::app(primitive, b(0)?)),
            Operation::Get => {
                let value = application(primitive, [b(2)?, b(1)?]);
                let body = self.array_recover(value, &payload)?;
                (vec![family, c("Nat"), proofs::erased_type()], payload, body)
            }
            Operation::Set => {
                let value = application(primitive, [b(3)?, b(2)?, b(1)?]);
                (
                    vec![family.clone(), c("Nat"), payload, proofs::erased_type()],
                    family,
                    value,
                )
            }
            Operation::Pop => (vec![family.clone()], family, Expr::app(primitive, b(0)?)),
        };
        let type_ = function(&domains, result);
        let mut wrapper = body;
        for domain in domains.into_iter().rev() {
            self.tick()?;
            wrapper = Expr::lam(self.array_name()?, domain, wrapper, BinderInfo::Default);
        }
        self.array_typed(wrapper, type_).map(Some)
    }

    /// A field access evaluates its original receiver once, then converts the
    /// native storage into the same ordered List the logical projection denotes.
    pub(super) fn array_projection_factory(
        &mut self,
        receiver_type: &Expr,
        structure: &Name,
        index: u64,
    ) -> Result<Option<Expr>, IngressError> {
        if structure != &name("Array") || !self.native_arrays_enabled()? {
            return Ok(None);
        }
        if index != 0 {
            return Err(unsupported("Array projection field index"));
        }
        // Preserve element parameters until checked payload/list discovery
        // erases them; normalizing the whole receiver would visit them first.
        let source = self.type_head(receiver_type)?;
        let (head, args) = self.spine(&source)?;
        let ExprNode::Const {
            name: family,
            levels,
        } = head.node()
        else {
            return Err(unsupported("Array projection receiver type"));
        };
        let ([level], [alpha]) = (levels.as_slice(), args.as_slice()) else {
            return Err(unsupported("Array projection receiver type"));
        };
        if family != &name("Array") || !self.array_value_type(&source)? {
            return Err(unsupported("Array projection receiver type"));
        }
        self.array_wrapper(Operation::ToList, level, alpha)
    }

    pub(super) fn array_call(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const {
            name: requested,
            levels,
        } = head.node()
        else {
            return Ok(None);
        };
        if args.len() > 1
            && levels.is_empty()
            && let Some((type_, _)) = self.arrays.recoveries.get(requested)
        {
            let ExprNode::ForallE { body: payload, .. } = type_.node() else {
                return Err(unsupported("Array recovery signature"));
            };
            let payload = payload.clone();
            let mut body = b(0)?;
            for argument in &args[1..] {
                self.tick()?;
                body = Expr::app(body, self.lift(argument, 1)?);
            }
            return Ok(Some(Expr::let_e(
                self.array_name()?,
                payload,
                Expr::app(head.clone(), args[0].clone()),
                body,
                false,
            )));
        }
        if requested == &name("Array.rec") {
            return self.array_recursor(levels, args);
        }
        let Some(operation) = Operation::from_name(requested) else {
            return Ok(None);
        };
        let ([level], [alpha, rest @ ..]) = (levels.as_slice(), args) else {
            return Ok(None);
        };
        let Some(wrapper) = self.array_wrapper(operation, level, alpha)? else {
            return Ok(None);
        };
        let erased_element = if self.type_parameter(alpha)? {
            match operation {
                Operation::Push => Some(1),
                Operation::Set => Some(2),
                _ => None,
            }
        } else {
            None
        };
        Ok(Some(application(
            wrapper,
            rest.iter().enumerate().map(|(index, argument)| {
                if erased_element == Some(index) {
                    // As with a type-valued List field, the supplied type itself
                    // is static metadata. Never execute it as an array element.
                    proofs::erased_value()
                } else {
                    argument.clone()
                }
            }),
        )))
    }

    fn array_recursor(
        &mut self,
        levels: &[Level],
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ([_, level], [alpha, motive, minor, major, rest @ ..]) = (levels, args) else {
            return Ok(None);
        };
        if !self.native_arrays_enabled()? {
            return Ok(None);
        }
        source_intrinsics::check_selected_extern_attribute(
            self.environment,
            &name("Array.rec"),
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        let family = family(level, alpha);
        self.array_value_type(&family)?;
        let motive = self.erase_type_argument(motive, &[])?;
        let motive = self
            .indexed_motive(&motive, &[], &family)?
            .ok_or_else(|| unsupported("dependent Array recursor result"))?;
        let result = self
            .value_type(&motive)?
            .ok_or_else(|| unsupported("Array recursor result representation"))?;
        let Some(to_list) = self.array_wrapper(Operation::ToList, level, alpha)? else {
            return Err(unsupported("Array recursor list conversion"));
        };
        let field = list(level, alpha);
        let body = Expr::app(b(1)?, Expr::app(to_list, b(0)?));
        let body = self.typed_callable_result(body, motive.clone(), result)?;
        let body = Expr::let_e(
            self.array_name()?,
            family,
            self.lift(major, 1)?,
            body,
            false,
        );
        let body = Expr::let_e(
            self.array_name()?,
            function(&[field], motive),
            minor.clone(),
            body,
            false,
        );
        Ok(Some(application(body, rest.iter().cloned())))
    }
}

#[cfg(test)]
mod extraction;
#[cfg(test)]
mod tests;
