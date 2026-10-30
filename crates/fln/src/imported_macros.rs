//! Execute explicitly selected imported user/library macros on Golem.
//!
//! This first native Mirror slice runs actual Reference-compiled `MacroM`
//! functions, including their branches and exceptions. It supplies immutable
//! Syntax, context and state objects and returns the complete resulting state.
//! It does not enable expansion-less parser registrations, interpret Lean's
//! toolchain implementation, or pretend that the five environment-dependent
//! Macro.Methods have been implemented. A macro demanding those methods is
//! refused by the ordinary native-call selection boundary.

use crate::imported_ir::{
    self, CompiledCallableIr, IrExecutionError, IrExecutionLimits, ReferenceFunction,
    VerifiedPartition,
};
use fln_core::diag::{ResourceReason, StructuralUnit};
use fln_core::name::{LeafView, Name};
use fln_core::outcome::{Inconclusive, Outcome, ResourceUsage};
use fln_olean::ir::{IrArg, IrBody, IrDecl, IrExpr, IrModule, IrStmt, IrTerminal};
use fln_rt::convert::{Conversion, inject_name};
use fln_rt::obj::Obj;
use fln_rt::syntax_abi_generated as layout;
use fln_syntax::source::SourceText;
use fln_syntax::tree::Syntax;
use fln_vm::interpreter::{CancellationProbe, ExecutionLimits, ExecutionUsage, VmExit, VmRefusal};
use std::collections::{BTreeSet, HashSet};

pub mod registrations;
mod syntax;
pub use syntax::{SyntaxConversionError, SyntaxLimits};

/// The read-only shape of the pin's Macro.Context.
///
/// The first execution slice requires the compiled entry's context argument to
/// be unused. Contextual name lookup, fresh-name generation and the five
/// Macro.Methods remain unavailable; state-counter updates are supported.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroContext {
    pub quotation_context: Name,
    pub current_macro_scope: u64,
    pub current_recursion_depth: u64,
    pub max_recursion_depth: u64,
}

/// All three fields of the pin's Macro.State, in their original order.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MacroState {
    pub macro_scope: u64,
    pub trace_messages: Vec<(Name, String)>,
    pub expanded_macro_declarations: Vec<Name>,
}

#[derive(Debug, Clone, Copy)]
pub struct MacroLimits {
    pub syntax: SyntaxLimits,
    pub vm: ExecutionLimits,
}

impl Default for MacroLimits {
    fn default() -> Self {
        Self {
            syntax: SyntaxLimits::default(),
            vm: ExecutionLimits::default(),
        }
    }
}

/// Exceptions remain distinct: unsupported syntax may try another registered
/// macro, whereas a diagnostic error stops expansion at its own reference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MacroResult {
    Expanded {
        syntax: Syntax,
        state: MacroState,
    },
    Unsupported {
        state: MacroState,
    },
    Error {
        reference: Syntax,
        message: String,
        state: MacroState,
    },
}

#[derive(Debug)]
pub enum MacroExecutionError {
    Compile(IrExecutionError),
    Conversion(SyntaxConversionError),
    Signature { arity: usize },
    Runtime(VmRefusal),
    RuntimePanic(String),
}

impl std::fmt::Display for MacroExecutionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Compile(error) => write!(f, "macro compilation: {error}"),
            Self::Conversion(error) => write!(f, "{error}"),
            Self::Signature { arity } => {
                write!(f, "MacroM entry requires 3 object arguments, found {arity}")
            }
            Self::Runtime(error) => write!(f, "macro runtime: {error}"),
            Self::RuntimePanic(message) => write!(f, "macro panic: {message}"),
        }
    }
}

impl std::error::Error for MacroExecutionError {}

#[derive(Debug)]
pub struct MacroExecution {
    pub outcome: Outcome<Result<MacroResult, MacroExecutionError>>,
    /// Actual usage when the VM reached a terminal return, panic or refusal.
    /// A registry subtracts these steps before trying another candidate.
    /// Conversion failures before invocation and nonterminal stops have none.
    pub vm_usage: Option<ExecutionUsage>,
    pub reference_functions: Vec<ReferenceFunction>,
    pub native_functions: Vec<String>,
}

/// A verified linked macro closure, reusable with fresh syntax and state.
#[derive(Debug)]
pub struct CompiledMacro {
    callable: CompiledCallableIr,
}

pub fn compile(
    modules: &[IrModule],
    entry: &Name,
    partition: &VerifiedPartition,
    user_declarations: &BTreeSet<Name>,
    limits: IrExecutionLimits,
) -> Result<CompiledMacro, MacroExecutionError> {
    let callable =
        imported_ir::compile_callable(modules, entry, partition, user_declarations, limits)
            .map_err(MacroExecutionError::Compile)?;
    if callable.arity() != 3 {
        return Err(MacroExecutionError::Signature {
            arity: callable.arity(),
        });
    }
    let Some(IrDecl::Function { params, body, .. }) = modules
        .iter()
        .flat_map(|module| &module.decls)
        .find(|declaration| declaration.name() == entry)
    else {
        return Err(MacroExecutionError::Compile(
            IrExecutionError::MissingDeclaration(entry.clone()),
        ));
    };
    // The initial MethodsRef token must be unobservable. Merely refusing
    // getMethods calls would miss a direct untrusted-IR projection or an
    // unsafe cast in user code. Validate the original, already checked body
    // before executing anything; passing context to another function also
    // counts as observing it in this deliberately bounded first slice.
    if observes_context(body, params[1].x) {
        return Err(MacroExecutionError::Compile(
            IrExecutionError::Unsupported {
                declaration: entry.clone(),
                form: "Macro.Context observation requires native Macro.Methods support",
            },
        ));
    }
    // MacroM has no ambient IO or mutable reference capabilities. Even the
    // explicit ST allowance of the general library executor is unavailable.
    for id in callable.native_externs() {
        if let Some(row) = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.id == id)
            && (row.effect != "pure" || matches!(row.id, "extern:dbgTrace" | "extern:panicCore"))
        {
            return Err(MacroExecutionError::Compile(
                IrExecutionError::Unsupported {
                    declaration: Name::from_components(row.name.split('.')),
                    form: "effectful native call in MacroM",
                },
            ));
        }
    }
    Ok(CompiledMacro { callable })
}

fn observes_context(body: &IrBody, context: u64) -> bool {
    let argument = |value: &IrArg| *value == IrArg::Var(context);
    let expression = |value: &IrExpr| match value {
        IrExpr::Ctor { args, .. } | IrExpr::Fap { args, .. } | IrExpr::Pap { args, .. } => {
            args.iter().any(argument)
        }
        IrExpr::Ap { x, args } | IrExpr::Reuse { x, args, .. } => {
            *x == context || args.iter().any(argument)
        }
        IrExpr::Reset { x, .. }
        | IrExpr::Proj { x, .. }
        | IrExpr::UProj { x, .. }
        | IrExpr::SProj { x, .. }
        | IrExpr::Box { x, .. }
        | IrExpr::Unbox { x }
        | IrExpr::IsShared { x } => *x == context,
        IrExpr::Lit(_) => false,
    };
    body.bodies().into_iter().any(|body| {
        body.stmts.iter().any(|statement| match statement {
            IrStmt::VDecl { expr, .. } => expression(expr),
            IrStmt::Set { x, y, .. } => *x == context || argument(y),
            IrStmt::USet { x, y, .. } | IrStmt::SSet { x, y, .. } => *x == context || *y == context,
            IrStmt::SetTag { x, .. } => *x == context,
            IrStmt::JDecl { .. } | IrStmt::Inc { .. } | IrStmt::Dec { .. } | IrStmt::Del { .. } => {
                false
            }
        }) || match body.terminal.as_ref() {
            IrTerminal::Case { x, .. } => *x == context,
            IrTerminal::Ret(value) => argument(value),
            IrTerminal::Jmp { args, .. } => args.iter().any(argument),
            IrTerminal::Unreachable => false,
        }
    })
}

impl CompiledMacro {
    pub fn callable(&self) -> &CompiledCallableIr {
        &self.callable
    }

    /// No result or successor state is exposed until the whole EStateM value
    /// and syntax tree have passed the bounded native projection.
    pub fn execute(
        &self,
        input: &Syntax,
        source: &SourceText,
        context: &MacroContext,
        state: &MacroState,
        limits: MacroLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> MacroExecution {
        let prepared = (|| {
            let syntax = syntax::inject(input, source, limits.syntax)?;
            let mut budget = StateBudget::new(limits.syntax);
            let context = make_ctor(
                layout::MACRO_CONTEXT,
                vec![
                    // Opaque MethodsRef: no native method can inspect this token.
                    // Selecting getMethods/any environment method is a compile
                    // refusal until its explicit capability is implemented.
                    Obj::mk_nat(0),
                    budget.inject_name(&context.quotation_context)?,
                    nat(context.current_macro_scope),
                    nat(context.current_recursion_depth),
                    nat(context.max_recursion_depth),
                    syntax.clone_ref(),
                ],
            );
            let state = inject_state(state, &mut budget)?;
            Ok::<_, SyntaxConversionError>(vec![syntax, context, state])
        })();
        let mut vm_usage = None;
        let outcome = match prepared {
            Err(error) => conversion_outcome(error),
            Ok(arguments) => {
                let report = self.callable.execute(arguments, limits.vm, cancellation);
                match report.outcome {
                    Outcome::Complete(VmExit::Returned(result)) => {
                        vm_usage = Some(result.usage);
                        match project_result(&result.value, source, limits.syntax) {
                            Ok(result) => Outcome::Complete(Ok(result)),
                            Err(error) => conversion_outcome(error),
                        }
                    }
                    Outcome::Complete(VmExit::Refused { refusal, usage }) => {
                        vm_usage = Some(usage);
                        Outcome::Complete(Err(MacroExecutionError::Runtime(refusal)))
                    }
                    Outcome::Complete(VmExit::Panicked { message, usage }) => {
                        vm_usage = Some(usage);
                        Outcome::Complete(Err(MacroExecutionError::RuntimePanic(message)))
                    }
                    Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                    Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
                }
            }
        };
        MacroExecution {
            outcome,
            vm_usage,
            reference_functions: self.callable.reference_functions().to_vec(),
            native_functions: self.callable.native_externs().to_vec(),
        }
    }
}

fn conversion_outcome(
    error: SyntaxConversionError,
) -> Outcome<Result<MacroResult, MacroExecutionError>> {
    match error {
        SyntaxConversionError::Limit {
            resource,
            limit,
            observed,
        } => Outcome::Inconclusive(
            Inconclusive::resource(ResourceUsage {
                reason: if resource.contains("bytes") {
                    ResourceReason::Memory {
                        limit_bytes: limit as u64,
                    }
                } else {
                    ResourceReason::StructuralBudget {
                        unit: StructuralUnit::ProducedNodes,
                    }
                },
                allowed: limit as u64,
                observed: observed as u64,
            })
            .with_progress(format!("macro {resource}")),
        ),
        SyntaxConversionError::Name(fln_rt::convert::ConvertError::NodeBudgetExhausted {
            visited,
            budget,
            ..
        }) => Outcome::Inconclusive(
            Inconclusive::resource(ResourceUsage {
                reason: ResourceReason::StructuralBudget {
                    unit: StructuralUnit::ProducedNodes,
                },
                allowed: budget as u64,
                observed: visited as u64,
            })
            .with_progress("macro Name conversion"),
        ),
        SyntaxConversionError::Allocation => Outcome::Inconclusive(
            Inconclusive::dependency_unavailable("host allocation for macro value conversion"),
        ),
        error => Outcome::Complete(Err(MacroExecutionError::Conversion(error))),
    }
}

fn nat(value: u64) -> Obj {
    if value <= (usize::MAX >> 1) as u64 {
        Obj::mk_nat(value as usize)
    } else {
        Obj::mk_mpz(&[value], false)
    }
}

fn make_ctor(layout: layout::CtorLayout, fields: Vec<Obj>) -> Obj {
    debug_assert_eq!(fields.len(), layout.object_fields);
    debug_assert_eq!(layout.scalar_bytes, 0);
    Obj::mk_ctor(layout.tag, fields, &[])
}

fn check_ctor(value: &Obj, layout: layout::CtorLayout) -> Result<(), SyntaxConversionError> {
    let word = std::mem::size_of::<usize>();
    let bytes = (word + layout.object_fields * word + layout.scalar_bytes).div_ceil(word) * word;
    if value.is_scalar()
        || value.obj_tag() != usize::from(layout.tag)
        || usize::from(value.header().other) != layout.object_fields
        || value.byte_size() != bytes
    {
        return Err(SyntaxConversionError::Malformed(
            "macro result constructor layout",
        ));
    }
    Ok(())
}

fn child(value: &Obj, index: usize) -> Result<Obj, SyntaxConversionError> {
    value
        .try_ctor_child(index)
        .ok_or(SyntaxConversionError::Malformed("macro field missing"))
}

fn text(value: &Obj) -> Result<&str, SyntaxConversionError> {
    let (_, _, chars, bytes) =
        value
            .try_borrow_string_view()
            .ok_or(SyntaxConversionError::Malformed(
                "macro message is not a String",
            ))?;
    let text = bytes
        .strip_suffix(&[0])
        .and_then(|bytes| std::str::from_utf8(bytes).ok())
        .ok_or(SyntaxConversionError::Malformed(
            "macro message is not valid UTF-8",
        ))?;
    if text.chars().count() != chars {
        return Err(SyntaxConversionError::Malformed(
            "macro message character count",
        ));
    }
    Ok(text)
}

struct StateBudget {
    limits: SyntaxLimits,
    nodes: usize,
    bytes: usize,
}

impl StateBudget {
    fn new(limits: SyntaxLimits) -> Self {
        Self {
            limits,
            nodes: 0,
            bytes: 0,
        }
    }
    fn charge(&mut self, nodes: usize, bytes: usize) -> Result<(), SyntaxConversionError> {
        self.nodes = self.nodes.saturating_add(nodes);
        self.bytes = self.bytes.saturating_add(bytes);
        if self.nodes > self.limits.max_nodes {
            return Err(SyntaxConversionError::Limit {
                resource: "state nodes",
                limit: self.limits.max_nodes,
                observed: self.nodes,
            });
        }
        if self.bytes > self.limits.max_bytes {
            return Err(SyntaxConversionError::Limit {
                resource: "state bytes",
                limit: self.limits.max_bytes,
                observed: self.bytes,
            });
        }
        Ok(())
    }
    fn inject_name(&mut self, name: &Name) -> Result<Obj, SyntaxConversionError> {
        let mut cursor = name.clone();
        loop {
            self.charge(
                1,
                match cursor.leaf_view() {
                    LeafView::Str(text) => text.len(),
                    _ => 0,
                },
            )?;
            if cursor.is_anonymous() {
                break;
            }
            cursor = cursor.parent();
        }
        Ok(inject_name(name))
    }
    fn project_name(&mut self, name: &Obj) -> Result<Name, SyntaxConversionError> {
        // Charge the complete Name chain before the shared converter allocates
        // its native string/numeric components. Cycles exhaust this same bound.
        let mut cursor = name.clone_ref();
        loop {
            self.charge(
                1,
                if cursor.is_scalar() {
                    0
                } else {
                    cursor.byte_size()
                },
            )?;
            if cursor.is_scalar() || cursor.obj_tag() == 0 {
                break;
            }
            let component = child(&cursor, 1)?;
            self.charge(
                1,
                if component.is_scalar() {
                    0
                } else {
                    component.byte_size()
                },
            )?;
            cursor = child(&cursor, 0)?;
        }
        Conversion::new()
            .project_name(name)
            .map_err(SyntaxConversionError::Name)
    }
}

fn list(values: Vec<Obj>) -> Obj {
    values
        .into_iter()
        .rev()
        .fold(Obj::mk_nat(layout::LIST_NIL_TAG), |tail, head| {
            make_ctor(layout::LIST_CONS, vec![head, tail])
        })
}

fn inject_state(
    state: &MacroState,
    budget: &mut StateBudget,
) -> Result<Obj, SyntaxConversionError> {
    // Bound all list cells before reserving their output vectors. Names and
    // message bytes are charged before each corresponding object is built.
    budget.charge(
        1usize
            .saturating_add(state.trace_messages.len().saturating_mul(2))
            .saturating_add(state.expanded_macro_declarations.len()),
        0,
    )?;
    let mut traces = Vec::new();
    traces
        .try_reserve_exact(state.trace_messages.len())
        .map_err(|_| SyntaxConversionError::Allocation)?;
    for (class, message) in &state.trace_messages {
        budget.charge(0, message.len())?;
        traces.push(make_ctor(
            layout::PROD,
            vec![budget.inject_name(class)?, Obj::mk_string(message)],
        ));
    }
    let mut declarations = Vec::new();
    declarations
        .try_reserve_exact(state.expanded_macro_declarations.len())
        .map_err(|_| SyntaxConversionError::Allocation)?;
    for name in &state.expanded_macro_declarations {
        declarations.push(budget.inject_name(name)?);
    }
    Ok(make_ctor(
        layout::MACRO_STATE,
        vec![nat(state.macro_scope), list(traces), list(declarations)],
    ))
}

fn read_list<T>(
    value: Obj,
    budget: &mut StateBudget,
    mut item: impl FnMut(&Obj, &mut StateBudget) -> Result<T, SyntaxConversionError>,
) -> Result<Vec<T>, SyntaxConversionError> {
    let mut cursor = value;
    let mut seen = HashSet::new();
    let mut values = Vec::new();
    loop {
        budget.charge(1, 0)?;
        if cursor.is_scalar() && cursor.unbox() == layout::LIST_NIL_TAG {
            return Ok(values);
        }
        check_ctor(&cursor, layout::LIST_CONS)?;
        if !seen.insert(cursor.identity_token()) {
            return Err(SyntaxConversionError::Malformed("cyclic macro state list"));
        }
        values
            .try_reserve(1)
            .map_err(|_| SyntaxConversionError::Allocation)?;
        values.push(item(&child(&cursor, 0)?, budget)?);
        cursor = child(&cursor, 1)?;
    }
}

fn project_state(
    value: &Obj,
    budget: &mut StateBudget,
) -> Result<MacroState, SyntaxConversionError> {
    budget.charge(1, 0)?;
    check_ctor(value, layout::MACRO_STATE)?;
    let scope = child(value, 0)?;
    let macro_scope = if scope.is_scalar() {
        scope.unbox() as u64
    } else {
        let (_, size, limbs) = scope
            .try_mpz_view()
            .ok_or(SyntaxConversionError::Malformed("macro scope is not a Nat"))?;
        if size < 0 || limbs.len() > 1 {
            return Err(SyntaxConversionError::Malformed(
                "macro scope exceeds the native scope range",
            ));
        }
        limbs.first().copied().unwrap_or(0)
    };
    let trace_messages = read_list(child(value, 1)?, budget, |trace, budget| {
        budget.charge(1, 0)?;
        check_ctor(trace, layout::PROD)?;
        let name = budget.project_name(&child(trace, 0)?)?;
        let message = child(trace, 1)?;
        let message = text(&message)?;
        budget.charge(0, message.len())?;
        Ok((name, message.to_owned()))
    })?;
    let expanded_macro_declarations = read_list(child(value, 2)?, budget, |name, budget| {
        budget.project_name(name)
    })?;
    Ok(MacroState {
        macro_scope,
        trace_messages,
        expanded_macro_declarations,
    })
}

fn project_result(
    value: &Obj,
    source: &SourceText,
    limits: SyntaxLimits,
) -> Result<MacroResult, SyntaxConversionError> {
    let ok = !value.is_scalar() && value.obj_tag() == usize::from(layout::RESULT_OK.tag);
    check_ctor(
        value,
        if ok {
            layout::RESULT_OK
        } else {
            layout::RESULT_ERROR
        },
    )?;
    let state = project_state(&child(value, 1)?, &mut StateBudget::new(limits))?;
    let payload = child(value, 0)?;
    if ok {
        return Ok(MacroResult::Expanded {
            syntax: syntax::project(&payload, source, limits)?,
            state,
        });
    }
    if payload.is_scalar() && payload.unbox() == layout::EXCEPTION_UNSUPPORTED_TAG {
        return Ok(MacroResult::Unsupported { state });
    }
    check_ctor(&payload, layout::EXCEPTION_ERROR)?;
    let reference = syntax::project(&child(&payload, 0)?, source, limits)?;
    let message = child(&payload, 1)?;
    let message = text(&message)?;
    if message.len() > limits.max_bytes {
        return Err(SyntaxConversionError::Limit {
            resource: "diagnostic bytes",
            limit: limits.max_bytes,
            observed: message.len(),
        });
    }
    Ok(MacroResult::Error {
        reference,
        message: message.to_owned(),
        state,
    })
}

#[cfg(test)]
mod tests;
