//! Confine the native Macro.Context capability through selected Reference code.
//!
//! IR validation has already established lexical scope and declaration-wide
//! unique variable/join indices. A monotone local dataflow pass propagates
//! context carriers through joins; an iterative, signature-keyed worklist
//! checks every selected function receiving one. Known partial applications
//! retain their target and captures, without recursive host data structures.
//! A carrier may only be projected at a public context field, forwarded to
//! checked code, or consumed by an explicitly supported native context method.
//! It may never be stored, returned, reinterpreted, mutated or handed to an
//! unresolved closure. All visits share the caller's IR work ceiling.

use super::{IrExecutionError, Name, ReferenceFunction, layout};
use fln_olean::ir::{IrArg, IrBody, IrDecl, IrExpr, IrModule, IrParam, IrStmt, IrTerminal};
use std::collections::{BTreeMap, BTreeSet};

const OBSERVATION: &str = "Macro.Context observation requires native Macro.Methods support";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Value {
    Plain,
    Context,
    Closure(usize),
    /// A join merged incompatible values, at least one containing context.
    Mixed,
}

#[derive(Clone)]
struct Closure {
    function: Name,
    arguments: Vec<Value>,
    arity: usize,
    confined: bool,
}

struct Analyzer<'a> {
    declarations: BTreeMap<Name, &'a IrDecl>,
    closures: Vec<Closure>,
    closure_ids: BTreeMap<(Name, Vec<Value>), usize>,
    pending: Vec<(Name, Vec<Value>)>,
    seen: BTreeSet<(Name, Vec<Value>)>,
    remaining: u64,
}

pub(super) fn check(
    modules: &[IrModule],
    entry: &Name,
    selected: &[ReferenceFunction],
    max_work: u64,
) -> Result<(), IrExecutionError> {
    let mut analyzer = Analyzer {
        declarations: BTreeMap::new(),
        closures: Vec::new(),
        closure_ids: BTreeMap::new(),
        pending: Vec::new(),
        seen: BTreeSet::new(),
        remaining: max_work,
    };
    analyzer.charge(selected.len())?;
    let selected: BTreeSet<_> = selected.iter().map(|item| item.name.clone()).collect();
    for module in modules {
        analyzer.charge(1)?;
        for declaration in &module.decls {
            analyzer.charge(1)?;
            if selected.contains(declaration.name())
                && matches!(declaration, IrDecl::Function { .. })
            {
                analyzer
                    .declarations
                    .insert(declaration.name().clone(), declaration);
            }
        }
    }
    analyzer.enqueue(entry, vec![Value::Plain, Value::Context, Value::Plain])?;
    while let Some((name, arguments)) = analyzer.pending.pop() {
        analyzer.charge(1)?;
        let declaration = analyzer
            .declarations
            .get(&name)
            .copied()
            .ok_or_else(|| IrExecutionError::MissingDeclaration(name.clone()))?;
        let IrDecl::Function { params, body, .. } = declaration else {
            return Err(IrExecutionError::MissingDeclaration(name));
        };
        if params.len() != arguments.len() {
            return Err(refusal(&name));
        }
        analyzer.function(&name, params, body, arguments)?;
    }
    Ok(())
}

fn refusal(declaration: &Name) -> IrExecutionError {
    IrExecutionError::Unsupported {
        declaration: declaration.clone(),
        form: OBSERVATION,
    }
}

/// These native rows consume a context carrier without exposing MethodsRef.
/// Their arities still come from the mechanically extracted Mirror contract.
fn accepted_native_context_argument(function: &Name, index: usize) -> bool {
    (index == 0 && *function == Name::from_components(["Lean", "Macro", "getCurrNamespace"]))
        || (index == 1 && *function == Name::from_components(["Lean", "Macro", "hasDecl"]))
}

impl Analyzer<'_> {
    fn charge(&mut self, amount: usize) -> Result<(), IrExecutionError> {
        self.remaining = self
            .remaining
            .checked_sub(amount as u64)
            .ok_or(IrExecutionError::Limit("macro context confinement work"))?;
        Ok(())
    }

    fn confined(&self, value: Value) -> bool {
        match value {
            Value::Plain => false,
            Value::Context | Value::Mixed => true,
            Value::Closure(index) => self.closures[index].confined,
        }
    }

    fn reject_confined(
        &self,
        owner: &Name,
        values: impl IntoIterator<Item = Value>,
    ) -> Result<(), IrExecutionError> {
        if values.into_iter().any(|value| self.confined(value)) {
            Err(refusal(owner))
        } else {
            Ok(())
        }
    }

    fn enqueue(&mut self, name: &Name, arguments: Vec<Value>) -> Result<(), IrExecutionError> {
        self.charge(1)?;
        self.charge(arguments.len())?;
        let signature = (name.clone(), arguments);
        if self.seen.insert(signature.clone()) {
            self.pending.push(signature);
        }
        Ok(())
    }

    fn arity(&self, function: &Name) -> Option<usize> {
        match self.declarations.get(function) {
            Some(IrDecl::Function { params, .. }) => Some(params.len()),
            _ => fln_vm::macro_native::row_for_name(function).map(|row| row.parameters.len()),
        }
    }

    fn native_arguments(
        &self,
        owner: &Name,
        function: &Name,
        arguments: &[Value],
    ) -> Result<(), IrExecutionError> {
        for (index, &value) in arguments.iter().enumerate() {
            if self.confined(value)
                && !(value == Value::Context && accepted_native_context_argument(function, index))
            {
                return Err(refusal(owner));
            }
        }
        Ok(())
    }

    fn call(
        &mut self,
        owner: &Name,
        function: &Name,
        arguments: Vec<Value>,
    ) -> Result<Value, IrExecutionError> {
        if !arguments.iter().any(|&value| self.confined(value)) {
            return Ok(Value::Plain);
        }
        if self.arity(function) != Some(arguments.len()) {
            return Err(refusal(owner));
        }
        if self.declarations.contains_key(function) {
            self.enqueue(function, arguments)?;
        } else {
            self.native_arguments(owner, function, &arguments)?;
        }
        // Every analyzed return must be free of confined values. This includes
        // recursive callees: all pending signatures must pass before admission.
        Ok(Value::Plain)
    }

    fn partial(
        &mut self,
        owner: &Name,
        function: &Name,
        arguments: Vec<Value>,
    ) -> Result<Value, IrExecutionError> {
        let Some(arity) = self.arity(function) else {
            self.reject_confined(owner, arguments)?;
            return Ok(Value::Plain);
        };
        if arguments.len() >= arity {
            return Err(refusal(owner));
        }
        if !self.declarations.contains_key(function) {
            self.native_arguments(owner, function, &arguments)?;
        }
        self.charge(arguments.len())?;
        let key = (function.clone(), arguments);
        if let Some(&index) = self.closure_ids.get(&key) {
            return Ok(Value::Closure(index));
        }
        let index = self.closures.len();
        self.closures.push(Closure {
            function: function.clone(),
            confined: key.1.iter().any(|&value| self.confined(value)),
            arguments: key.1.clone(),
            arity,
        });
        self.closure_ids.insert(key, index);
        Ok(Value::Closure(index))
    }

    fn apply(
        &mut self,
        owner: &Name,
        callable: Value,
        arguments: Vec<Value>,
    ) -> Result<Value, IrExecutionError> {
        let Value::Closure(index) = callable else {
            self.reject_confined(owner, std::iter::once(callable).chain(arguments))?;
            return Ok(Value::Plain);
        };
        self.charge(self.closures[index].arguments.len())?;
        let closure = self.closures[index].clone();
        let mut all = closure.arguments;
        all.extend(arguments);
        match all.len().cmp(&closure.arity) {
            std::cmp::Ordering::Less => self.partial(owner, &closure.function, all),
            std::cmp::Ordering::Equal => self.call(owner, &closure.function, all),
            std::cmp::Ordering::Greater => {
                // The excess arguments would call an unknown returned closure.
                self.reject_confined(owner, all)?;
                Ok(Value::Plain)
            }
        }
    }

    fn arguments(
        &mut self,
        variables: &BTreeMap<u64, Value>,
        arguments: &[IrArg],
    ) -> Result<Option<Vec<Value>>, IrExecutionError> {
        self.charge(arguments.len())?;
        Ok(arguments
            .iter()
            .map(|arg| argument(variables, arg))
            .collect())
    }

    fn expression(
        &mut self,
        owner: &Name,
        variables: &BTreeMap<u64, Value>,
        expression: &IrExpr,
    ) -> Result<Option<Value>, IrExecutionError> {
        match expression {
            IrExpr::Lit(_) => Ok(Some(Value::Plain)),
            IrExpr::Fap { function, args } | IrExpr::Pap { function, args } => {
                let Some(arguments) = self.arguments(variables, args)? else {
                    return Ok(None);
                };
                if matches!(expression, IrExpr::Fap { .. }) {
                    self.call(owner, function, arguments).map(Some)
                } else {
                    self.partial(owner, function, arguments).map(Some)
                }
            }
            IrExpr::Ap { x, args } => {
                let Some(&callable) = variables.get(x) else {
                    return Ok(None);
                };
                let Some(arguments) = self.arguments(variables, args)? else {
                    return Ok(None);
                };
                self.apply(owner, callable, arguments).map(Some)
            }
            IrExpr::Proj { i, x } => {
                let Some(&value) = variables.get(x) else {
                    return Ok(None);
                };
                if value == Value::Context
                    && *i != layout::MACRO_CONTEXT_METHODS_FIELD
                    && *i < layout::MACRO_CONTEXT.object_fields as u64
                {
                    return Ok(Some(Value::Plain));
                }
                self.reject_confined(owner, [value])?;
                Ok(Some(Value::Plain))
            }
            IrExpr::Ctor { args, .. } | IrExpr::Reuse { args, .. } => {
                let Some(arguments) = self.arguments(variables, args)? else {
                    return Ok(None);
                };
                self.reject_confined(owner, arguments)?;
                if let IrExpr::Reuse { x, .. } = expression {
                    let Some(&value) = variables.get(x) else {
                        return Ok(None);
                    };
                    self.reject_confined(owner, [value])?;
                }
                Ok(Some(Value::Plain))
            }
            IrExpr::Reset { x, .. }
            | IrExpr::UProj { x, .. }
            | IrExpr::SProj { x, .. }
            | IrExpr::Box { x, .. }
            | IrExpr::Unbox { x }
            | IrExpr::IsShared { x } => {
                let Some(&value) = variables.get(x) else {
                    return Ok(None);
                };
                self.reject_confined(owner, [value])?;
                Ok(Some(Value::Plain))
            }
        }
    }

    fn merge(&self, variables: &mut BTreeMap<u64, Value>, index: u64, value: Value) -> bool {
        let merged = match variables.get(&index).copied() {
            None => value,
            Some(old) if old == value => return false,
            Some(old) if self.confined(old) || self.confined(value) => Value::Mixed,
            Some(_) => Value::Plain,
        };
        if variables.get(&index) == Some(&merged) {
            false
        } else {
            variables.insert(index, merged);
            true
        }
    }

    fn function(
        &mut self,
        owner: &Name,
        params: &[IrParam],
        root: &IrBody,
        arguments: Vec<Value>,
    ) -> Result<(), IrExecutionError> {
        self.charge(params.len())?;
        let mut variables: BTreeMap<_, _> =
            params.iter().map(|param| param.x).zip(arguments).collect();
        let bodies = root.bodies();
        self.charge(bodies.len())?;
        let mut joins = BTreeMap::new();
        for body in &bodies {
            for statement in &body.stmts {
                self.charge(1)?;
                if let IrStmt::JDecl { j, params, .. } = statement {
                    joins.insert(*j, params.as_slice());
                }
            }
        }
        loop {
            let mut changed = false;
            for body in &bodies {
                self.charge(1)?;
                for statement in &body.stmts {
                    self.charge(1)?;
                    match statement {
                        IrStmt::VDecl { x, expr, .. } => {
                            if let Some(value) = self.expression(owner, &variables, expr)? {
                                changed |= self.merge(&mut variables, *x, value);
                            }
                        }
                        IrStmt::Set { x, y, .. } => {
                            self.reject_confined(
                                owner,
                                variables
                                    .get(x)
                                    .copied()
                                    .into_iter()
                                    .chain(argument(&variables, y)),
                            )?;
                        }
                        IrStmt::USet { x, y, .. } | IrStmt::SSet { x, y, .. } => {
                            self.reject_confined(
                                owner,
                                variables
                                    .get(x)
                                    .copied()
                                    .into_iter()
                                    .chain(variables.get(y).copied()),
                            )?;
                        }
                        IrStmt::SetTag { x, .. } => {
                            self.reject_confined(owner, variables.get(x).copied())?;
                        }
                        IrStmt::JDecl { .. }
                        | IrStmt::Inc { .. }
                        | IrStmt::Dec { .. }
                        | IrStmt::Del { .. } => {}
                    }
                }
                self.charge(1)?;
                match body.terminal.as_ref() {
                    IrTerminal::Ret(arg) => {
                        self.reject_confined(owner, argument(&variables, arg))?;
                    }
                    IrTerminal::Case { x, .. } => {
                        self.reject_confined(owner, variables.get(x).copied())?;
                    }
                    IrTerminal::Jmp { j, args } => {
                        if let Some(arguments) = self.arguments(&variables, args)? {
                            let params = joins.get(j).ok_or_else(|| refusal(owner))?;
                            if params.len() != arguments.len() {
                                return Err(refusal(owner));
                            }
                            self.charge(params.len())?;
                            for (param, value) in params.iter().zip(arguments) {
                                changed |= self.merge(&mut variables, param.x, value);
                            }
                        }
                    }
                    IrTerminal::Unreachable => {}
                }
            }
            if !changed {
                return Ok(());
            }
        }
    }
}

fn argument(variables: &BTreeMap<u64, Value>, argument: &IrArg) -> Option<Value> {
    match argument {
        IrArg::Var(index) => variables.get(index).copied(),
        IrArg::Erased => Some(Value::Plain),
    }
}

#[cfg(test)]
mod tests;
