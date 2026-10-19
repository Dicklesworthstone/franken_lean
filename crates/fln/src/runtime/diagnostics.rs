//! Typed bridges from admitted diagnostic functions to the shared native ABI.
//! A single raw-object row serves every result representation. Ordinary FIR
//! box/unbox boundaries retain its concrete class, and diagnostics are marked
//! effectful so logical purity cannot delete, hoist or coalesce their output.
use super::*;
use fln_comp::fir::EffectClass;
use fln_comp::flbc::{ArgumentOwnership, ResultOwnership};

const PAYLOAD: &str = "_fln_runtime_diagnostic_object";
const PANIC: &str = "_fln_runtime_panic_core";
const TRACE: &str = "_fln_runtime_debug_trace";

#[derive(Default)]
pub(super) struct Store {
    next: u64,
    panic: Option<(IntrinsicBinding, Expr)>,
    trace: Option<(IntrinsicBinding, Expr)>,
    trace_unit: Option<Expr>,
}
fn c(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}
fn b(index: u32) -> Result<Expr, IngressError> {
    Expr::bvar(index).map_err(|_| unsupported("diagnostic adapter binder"))
}
fn function(domains: &[Expr], result: Expr) -> Expr {
    domains.iter().rev().fold(result, |body, domain| {
        Expr::forall_e(Name::anonymous(), domain.clone(), body, BinderInfo::Default)
    })
}
impl Preparation<'_> {
    pub(crate) fn diagnostic_intrinsic_binding(
        &self,
        requested: &Name,
    ) -> Option<IntrinsicBinding> {
        self.diagnostics
            .panic
            .iter()
            .chain(self.diagnostics.trace.iter())
            .find(|(binding, _)| &binding.name == requested)
            .map(|(binding, _)| binding.clone())
    }
    pub(super) fn diagnostic_intrinsic_type(&self, requested: &Name) -> Option<Expr> {
        self.diagnostics
            .panic
            .iter()
            .chain(self.diagnostics.trace.iter())
            .find(|(binding, _)| &binding.name == requested)
            .map(|(_, type_)| type_.clone())
    }
    fn diagnostic_name(&mut self) -> Result<Name, IngressError> {
        self.tick()?;
        let serial = self.diagnostics.next;
        self.diagnostics.next = serial
            .checked_add(1)
            .ok_or_else(|| unsupported("diagnostic adapter identity"))?;
        let private = Name::num(name("_fln_runtime_diagnostic_scope"), serial);
        if self.environment.contains(&private) {
            return Err(unsupported("diagnostic adapter name collision"));
        }
        Ok(private)
    }
    fn diagnostic_payload(&mut self) -> Result<(), IngressError> {
        let payload = c(PAYLOAD);
        if self.environment.contains(&name(PAYLOAD)) {
            return Err(unsupported("diagnostic private name collision"));
        }
        let expected = (ValueType::Abi, CallableResultOwnership::Erased);
        if let Some(actual) = self.value_types.native.get(&payload) {
            if *actual != expected {
                return Err(unsupported("diagnostic payload representation"));
            }
            return Ok(());
        }
        self.value_types
            .native
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: self.value_types.native.len().saturating_add(1),
            })?;
        self.value_types.native.insert(payload, expected);
        Ok(())
    }
    fn bind_trace(&mut self) -> Result<Option<Expr>, IngressError> {
        if self.diagnostics.trace.is_some() {
            return self
                .diagnostics
                .trace_unit
                .clone()
                .map(Some)
                .ok_or_else(|| unsupported("diagnostic trace Unit contract"));
        }
        let Some(unit) = crate::source_intrinsics::diagnostics::trace_matches(
            self.environment,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?
        else {
            return Ok(None);
        };
        if self.environment.contains(&name(TRACE)) {
            return Err(unsupported("diagnostic private name collision"));
        }
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.id == "extern:dbgTrace")
            .ok_or_else(|| unsupported("generated dbgTrace row"))?;
        if row.name != "dbgTrace"
            || row.kind != "defn"
            || row.levels != 1
            || row.arity != 3
            || row.module != "Init.Util"
            || row.safety != "safe"
            || row.symbol != "lean_dbg_trace"
            || row.effect != "pure"
        {
            return Err(unsupported("generated dbgTrace ABI contract"));
        }
        let ownership = fln_vm::extern_row::Ownership::parse(row.ownership)
            .map_err(|_| unsupported("generated dbgTrace ownership contract"))?;
        if ownership
            .argument_ownership(2)
            .map_err(|_| unsupported("generated dbgTrace argument ownership"))?
            != [
                fln_vm::extern_row::ArgumentOwnership::Owned,
                fln_vm::extern_row::ArgumentOwnership::Owned,
            ]
            || ownership
                .result_ownership()
                .map_err(|_| unsupported("generated dbgTrace result ownership"))?
                != fln_vm::extern_row::ResultOwnership::RawObject
        {
            return Err(unsupported("generated dbgTrace ownership contract"));
        }
        self.diagnostic_payload()?;
        let reporter = function(&[c("Nat")], c("Nat"));
        let callback = self
            .value_type(&reporter)?
            .ok_or_else(|| unsupported("dbgTrace reporter representation"))?;
        if !matches!(callback, ValueType::Closure(_)) {
            return Err(unsupported("dbgTrace reporter closure"));
        }
        self.diagnostics.trace = Some((
            IntrinsicBinding {
                name: name(TRACE),
                universe_arity: 0,
                row: row.id.to_owned(),
                arguments: vec![ValueType::String, callback],
                argument_ownership: vec![ArgumentOwnership::Owned, ArgumentOwnership::Owned],
                result: ValueType::Abi,
                result_ownership: ResultOwnership::RawObject,
                effect: EffectClass::Io,
            },
            function(&[c("String"), reporter], c(PAYLOAD)),
        ));
        self.diagnostics.trace_unit = Some(unit.clone());
        Ok(Some(unit))
    }
    fn trace_call(
        &mut self,
        levels: &[Level],
        arguments: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let Some(unit) = self.bind_trace()? else {
            return Ok(None);
        };
        let ([_], [source_result, rest @ ..]) = (levels, arguments) else {
            return Err(unsupported("dbgTrace needs a concrete result type"));
        };
        let result = self.erase_runtime_type(source_result)?;
        self.value_type(&result)?
            .ok_or_else(|| unsupported("dbgTrace result representation"))?;
        let unit = self.erase_runtime_type(&unit)?;
        let shape = self
            .record_shape(&unit)?
            .ok_or_else(|| unsupported("dbgTrace Unit record"))?;
        let [constructor] = shape.constructors.as_slice() else {
            return Err(unsupported("dbgTrace Unit constructor"));
        };
        if constructor.tag != 0
            || !constructor.fields.is_empty()
            || !constructor.type_fields.is_empty()
        {
            return Err(unsupported("dbgTrace Unit representation"));
        }
        let unit_value = Expr::const_(constructor.name.clone(), Vec::new());
        let callback = function(&[unit], result.clone());
        // The private ABI thunk only reports the message. Keep the original
        // continuation typed and call it once on the ordinary VM stack after
        // reporting, so callable and constructor results retain their interface.
        let reporter = Expr::lam(
            self.diagnostic_name()?,
            c("Nat"),
            nat::literal(0),
            BinderInfo::Default,
        );
        let reported = Expr::app(Expr::app(c(TRACE), b(1)?), reporter);
        let mut body = Expr::let_e(
            self.diagnostic_name()?,
            c(PAYLOAD),
            reported,
            Expr::app(b(1)?, unit_value),
            false,
        );
        let domains = [c("String"), callback];
        for domain in domains.iter().rev() {
            body = Expr::lam(
                self.diagnostic_name()?,
                domain.clone(),
                body,
                BinderInfo::Default,
            );
        }
        let wrapper = Expr::let_e(
            self.diagnostic_name()?,
            function(&domains, result),
            body,
            b(0)?,
            false,
        );
        Ok(Some(rest.iter().cloned().fold(wrapper, Expr::app)))
    }
    fn bind_panic(&mut self) -> Result<bool, IngressError> {
        if self.diagnostics.panic.is_some() {
            return Ok(true);
        }
        if !crate::source_intrinsics::diagnostics::panic_matches(
            self.environment,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )? {
            return Ok(false);
        }
        for label in [PAYLOAD, PANIC] {
            if self.environment.contains(&name(label)) {
                return Err(unsupported("diagnostic private name collision"));
            }
        }
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.id == "extern:panicCore")
            .ok_or_else(|| unsupported("generated panicCore row"))?;
        if row.name != "panicCore"
            || row.kind != "defn"
            || row.levels != 1
            || row.arity != 3
            || row.module != "Init.Prelude"
            || row.safety != "safe"
            || row.symbol != "lean_panic_fn_borrowed"
            || row.effect != "pure"
            || row.ownership != "abi((default_val: borrowed_arg, msg: raw_object) -> raw_object)"
        {
            return Err(unsupported("generated panicCore ABI contract"));
        }
        self.diagnostic_payload()?;
        self.diagnostics.panic = Some((
            IntrinsicBinding {
                name: name(PANIC),
                universe_arity: 0,
                row: row.id.to_owned(),
                arguments: vec![ValueType::Abi, ValueType::String],
                argument_ownership: vec![ArgumentOwnership::Borrowed, ArgumentOwnership::Owned],
                result: ValueType::Abi,
                result_ownership: ResultOwnership::RawObject,
                effect: EffectClass::Io,
            },
            function(&[c(PAYLOAD), c("String")], c(PAYLOAD)),
        ));
        Ok(true)
    }
    pub(super) fn diagnostic_call(
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
        if requested == &name("dbgTrace") {
            self.tick()?;
            return self.trace_call(levels, arguments);
        }
        if requested != &name("panicCore") {
            return Ok(None);
        }
        self.tick()?;
        // Validate before specialization can copy the logical default and lose
        // the observable implementation. The type parameter is compile-time.
        if !self.bind_panic()? {
            return Ok(None);
        }
        let ([level], [source_result, rest @ ..]) = (levels.as_slice(), arguments) else {
            return Err(unsupported("panicCore needs a concrete result type"));
        };
        let result = self.erase_runtime_type(source_result)?;
        self.value_type(&result)?
            .ok_or_else(|| unsupported("panicCore result representation"))?;
        let instance = Expr::app(
            Expr::const_(name("Inhabited"), vec![level.clone()]),
            source_result.clone(),
        );
        let instance = self.erase_runtime_type(&instance)?;
        let shape = self
            .record_shape(&instance)?
            .ok_or_else(|| unsupported("panicCore instance record"))?;
        let [constructor] = shape.constructors.as_slice() else {
            return Err(unsupported("panicCore instance constructor"));
        };
        if constructor.tag != 0
            || constructor.fields != [result.clone()]
            || constructor.type_fields != [false]
        {
            return Err(unsupported("panicCore instance payload"));
        }
        let payload = Expr::proj(shape.projection(constructor), 0, b(1)?);
        // Keep the admitted payload's concrete type across the raw-object
        // boundary. The native call reports (or follows the fatal policy),
        // and returns another reference to this exact borrowed default. Its
        // redundant raw result is released; the typed, shared original is
        // returned. This also handles function-valued defaults without
        // flattening their callback interface into an untyped application.
        let reported = Expr::app(Expr::app(c(PANIC), b(0)?), b(1)?);
        let mut body = Expr::let_e(
            self.diagnostic_name()?,
            result.clone(),
            payload,
            Expr::let_e(self.diagnostic_name()?, c(PAYLOAD), reported, b(1)?, false),
            false,
        );
        let domains = [instance, c("String")];
        for domain in domains.iter().rev() {
            body = Expr::lam(
                self.diagnostic_name()?,
                domain.clone(),
                body,
                BinderInfo::Default,
            );
        }
        let wrapper = Expr::let_e(
            self.diagnostic_name()?,
            function(&domains, result),
            body,
            b(0)?,
            false,
        );
        Ok(Some(rest.iter().cloned().fold(wrapper, Expr::app)))
    }
}
