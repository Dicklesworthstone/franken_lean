//! Budgeted structural validation of decoded IR (bead
//! `fln-ir-decoder-call-graph-sjzl`).
//!
//! Decoding checks representation; this pass checks definition-before-use,
//! lexical scope, declaration-wide index uniqueness, static callee closure and
//! call/jump arities. Join-point scope follows the pin's IR checker: the join
//! point is visible in the continuation, NOT in its own value. Parameters and
//! locals of its value, and locals of a case arm, do not escape that body.
//!
//! This is NOT a type checker, ownership verifier, execution permit or kernel
//! admission token. In particular, a successful result does not authorize
//! executing Reference-produced code. A caller supplying census externs must
//! obtain both names AND arities from its reviewed contract; a name-only
//! allowlist cannot establish an arity. The census/IR population reconciliation
//! remains the caller's responsibility.

use crate::ir::{
    IrAlt, IrArg, IrBody, IrDecl, IrExpr, IrIndex, IrModule, IrParam, IrStmt, IrTerminal,
};
use fln_core::name::Name;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy)]
pub struct IrValidationLimits {
    /// Declaration entries plus supplied census-signature entries, including
    /// overlaps between an IR extern and the census. Checked before indexing.
    pub max_declarations: usize,
    /// Structural visits: modules, entries, bodies, instructions, expressions,
    /// parameters, bindings, operands and case arms. Not a wall-clock budget.
    pub max_work: u64,
    /// Body nesting including the function body (depth one).
    pub max_depth: usize,
}

impl Default for IrValidationLimits {
    fn default() -> Self {
        Self {
            max_declarations: 1 << 20,
            max_work: 64_000_000,
            max_depth: 512,
        }
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct IrValidationSummary {
    pub modules: u64,
    pub declarations: u64,
    pub extern_declarations: u64,
    pub census_signatures: u64,
    pub bodies: u64,
    pub statements: u64,
    pub parameters: u64,
    pub arguments: u64,
    /// Closure-value applications (`ap`); static closure checking cannot resolve
    /// their targets. A nonzero count must not be reported as a complete graph.
    pub dynamic_calls: u64,
    pub work: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrCallTarget {
    Declaration(Name),
    JoinPoint(IrIndex),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrValidationErrorKind {
    Limit {
        resource: &'static str,
    },
    DuplicateDeclaration {
        name: Name,
    },
    ExternalShadowsFunction {
        name: Name,
    },
    ConflictingExternalArity {
        name: Name,
        ir: usize,
        census: usize,
    },
    DuplicateIndex {
        index: IrIndex,
    },
    UnknownVariable {
        index: IrIndex,
    },
    UnknownJoinPoint {
        index: IrIndex,
    },
    UnknownCallee {
        name: Name,
    },
    Arity {
        target: IrCallTarget,
        provided: usize,
        expected: usize,
        /// A partial application requires STRICTLY fewer than `expected`.
        partial: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrValidationError {
    /// Absent only when a module-level budget is exhausted before an entry.
    pub declaration: Option<Name>,
    pub kind: IrValidationErrorKind,
}

impl IrValidationError {
    pub fn is_resource(&self) -> bool {
        matches!(&self.kind, IrValidationErrorKind::Limit { .. })
    }
}

impl std::fmt::Display for IrValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "IR structural validation at {:?}: {:?}",
            self.declaration, self.kind
        )
    }
}

impl std::error::Error for IrValidationError {}

fn error(declaration: Option<&Name>, kind: IrValidationErrorKind) -> IrValidationError {
    IrValidationError {
        declaration: declaration.cloned(),
        kind,
    }
}

struct Budget {
    limits: IrValidationLimits,
    indexed: usize,
    summary: IrValidationSummary,
}

impl Budget {
    fn charge(&mut self, declaration: Option<&Name>) -> Result<(), IrValidationError> {
        let next = self
            .summary
            .work
            .checked_add(1)
            .filter(|n| *n <= self.limits.max_work);
        match next {
            Some(next) => {
                self.summary.work = next;
                Ok(())
            }
            None => Err(error(
                declaration,
                IrValidationErrorKind::Limit { resource: "work" },
            )),
        }
    }

    fn reserve_entry(&mut self, name: &Name) -> Result<(), IrValidationError> {
        self.charge(Some(name))?;
        if self.indexed >= self.limits.max_declarations {
            return Err(error(
                Some(name),
                IrValidationErrorKind::Limit {
                    resource: "declarations",
                },
            ));
        }
        self.indexed += 1;
        Ok(())
    }
}

#[derive(Clone, Copy)]
struct Signature {
    arity: usize,
    is_extern: bool,
}

/// Validate a module closure without mutating or executing it.
///
/// All declarations are indexed before any body is checked, so recursive and
/// mutually recursive *functions* may refer forward. Duplicate declarations
/// are refused, even when their signatures happen to agree. Census entries may
/// overlap IR externs only with matching arities; they cannot shadow functions.
/// Bodies are checked in name order, independent of module enumeration order.
///
/// The pass is iterative, including case arms and join-point values. Scope
/// restoration uses an undo log, not a clone of the entire environment at each
/// nested body. Every index is declaration-wide unique, including across arms
/// and between the variable and join-point namespaces, as in the pin.
pub fn validate_ir(
    modules: &[IrModule],
    census_externs: &BTreeMap<Name, usize>,
    limits: IrValidationLimits,
) -> Result<IrValidationSummary, IrValidationError> {
    validate_modules(modules.iter(), census_externs, limits)
}

fn validate_modules<'a>(
    modules: impl IntoIterator<Item = &'a IrModule>,
    census_externs: &BTreeMap<Name, usize>,
    limits: IrValidationLimits,
) -> Result<IrValidationSummary, IrValidationError> {
    let mut budget = Budget {
        limits,
        indexed: 0,
        summary: IrValidationSummary::default(),
    };
    let mut declarations = BTreeMap::new();
    let mut signatures = BTreeMap::new();
    for module in modules {
        budget.charge(None)?;
        budget.summary.modules += 1;
        for declaration in &module.decls {
            let name = declaration.name();
            budget.reserve_entry(name)?;
            if declarations.insert(name, declaration).is_some() {
                return Err(error(
                    Some(name),
                    IrValidationErrorKind::DuplicateDeclaration { name: name.clone() },
                ));
            }
            let (params, is_extern) = match declaration {
                IrDecl::Function { params, .. } => (params, false),
                IrDecl::Extern { params, .. } => (params, true),
            };
            signatures.insert(
                name.clone(),
                Signature {
                    arity: params.len(),
                    is_extern,
                },
            );
            budget.summary.declarations += 1;
            budget.summary.extern_declarations += u64::from(is_extern);
        }
    }
    for (name, &arity) in census_externs {
        budget.reserve_entry(name)?;
        match signatures.get(name) {
            Some(Signature {
                is_extern: false, ..
            }) => {
                return Err(error(
                    Some(name),
                    IrValidationErrorKind::ExternalShadowsFunction { name: name.clone() },
                ));
            }
            Some(signature) if signature.arity != arity => {
                return Err(error(
                    Some(name),
                    IrValidationErrorKind::ConflictingExternalArity {
                        name: name.clone(),
                        ir: signature.arity,
                        census: arity,
                    },
                ));
            }
            Some(_) => {}
            None => {
                signatures.insert(
                    name.clone(),
                    Signature {
                        arity,
                        is_extern: true,
                    },
                );
            }
        }
        budget.summary.census_signatures += 1;
    }
    for declaration in declarations.into_values() {
        let params = match declaration {
            IrDecl::Function { params, .. } | IrDecl::Extern { params, .. } => params,
        };
        let mut checker = Checker {
            signatures: &signatures,
            declaration: declaration.name(),
            budget: &mut budget,
            seen: BTreeSet::new(),
            variables: BTreeSet::new(),
            joins: BTreeMap::new(),
            bindings: Vec::new(),
        };
        checker.params(params)?;
        if let IrDecl::Function { body, .. } = declaration {
            checker.body(body)?;
        }
    }
    Ok(budget.summary)
}

enum Binding {
    Variable(IrIndex),
    Join(IrIndex),
}

/// Suspended continuations, not recursive calls. `Case` advances one arm at a
/// time, so a wide case does not allocate a pending frame for every arm.
enum Step<'a> {
    Body {
        body: &'a IrBody,
        next: usize,
        checkpoint: usize,
        depth: usize,
    },
    Case {
        alts: &'a [IrAlt],
        next: usize,
        checkpoint: usize,
        depth: usize,
    },
    PublishJoin {
        j: IrIndex,
        arity: usize,
    },
}

struct Checker<'a> {
    signatures: &'a BTreeMap<Name, Signature>,
    declaration: &'a Name,
    budget: &'a mut Budget,
    /// Never rolled back: indices are unique across the entire declaration.
    seen: BTreeSet<IrIndex>,
    variables: BTreeSet<IrIndex>,
    joins: BTreeMap<IrIndex, usize>,
    bindings: Vec<Binding>,
}

impl Checker<'_> {
    fn fail(&self, kind: IrValidationErrorKind) -> IrValidationError {
        error(Some(self.declaration), kind)
    }

    fn charge(&mut self) -> Result<(), IrValidationError> {
        self.budget.charge(Some(self.declaration))
    }

    fn mark(&mut self, index: IrIndex) -> Result<(), IrValidationError> {
        self.charge()?;
        if !self.seen.insert(index) {
            return Err(self.fail(IrValidationErrorKind::DuplicateIndex { index }));
        }
        Ok(())
    }

    fn bind_variable(&mut self, index: IrIndex) -> Result<(), IrValidationError> {
        self.mark(index)?;
        self.variables.insert(index);
        self.bindings.push(Binding::Variable(index));
        Ok(())
    }

    fn params(&mut self, params: &[IrParam]) -> Result<(), IrValidationError> {
        for param in params {
            self.charge()?;
            self.budget.summary.parameters += 1;
            self.bind_variable(param.x)?;
        }
        Ok(())
    }

    fn variable(&mut self, index: IrIndex) -> Result<(), IrValidationError> {
        self.charge()?;
        if !self.variables.contains(&index) {
            return Err(self.fail(IrValidationErrorKind::UnknownVariable { index }));
        }
        Ok(())
    }

    fn arg(&mut self, arg: &IrArg) -> Result<(), IrValidationError> {
        self.charge()?;
        self.budget.summary.arguments += 1;
        if let IrArg::Var(index) = arg {
            self.variable(*index)?;
        }
        Ok(())
    }

    fn args(&mut self, args: &[IrArg]) -> Result<(), IrValidationError> {
        for arg in args {
            self.arg(arg)?;
        }
        Ok(())
    }

    fn call(&mut self, name: &Name, args: &[IrArg], partial: bool) -> Result<(), IrValidationError> {
        self.charge()?;
        let Some(signature) = self.signatures.get(name).copied() else {
            return Err(self.fail(IrValidationErrorKind::UnknownCallee { name: name.clone() }));
        };
        if (partial && args.len() >= signature.arity) || (!partial && args.len() != signature.arity) {
            return Err(self.fail(IrValidationErrorKind::Arity {
                target: IrCallTarget::Declaration(name.clone()),
                provided: args.len(),
                expected: signature.arity,
                partial,
            }));
        }
        self.args(args)
    }

    fn expr(&mut self, expr: &IrExpr) -> Result<(), IrValidationError> {
        self.charge()?;
        match expr {
            IrExpr::Ctor { args, .. } => self.args(args),
            IrExpr::Reuse { x, args, .. } | IrExpr::Ap { x, args } => {
                self.variable(*x)?;
                if matches!(expr, IrExpr::Ap { .. }) {
                    self.budget.summary.dynamic_calls += 1;
                }
                self.args(args)
            }
            IrExpr::Fap { function, args } => self.call(function, args, false),
            IrExpr::Pap { function, args } => self.call(function, args, true),
            IrExpr::Reset { x, .. }
            | IrExpr::Proj { x, .. }
            | IrExpr::UProj { x, .. }
            | IrExpr::SProj { x, .. }
            | IrExpr::Box { x, .. }
            | IrExpr::Unbox { x }
            | IrExpr::IsShared { x } => self.variable(*x),
            IrExpr::Lit(_) => Ok(()),
        }
    }

    fn restore(&mut self, checkpoint: usize) {
        while self.bindings.len() > checkpoint {
            match self.bindings.pop() {
                Some(Binding::Variable(index)) => {
                    self.variables.remove(&index);
                }
                Some(Binding::Join(index)) => {
                    self.joins.remove(&index);
                }
                None => break,
            }
        }
    }

    fn enter<'a>(
        &mut self,
        pending: &mut Vec<Step<'a>>,
        body: &'a IrBody,
        checkpoint: usize,
        depth: usize,
    ) -> Result<(), IrValidationError> {
        if depth > self.budget.limits.max_depth {
            return Err(self.fail(IrValidationErrorKind::Limit { resource: "depth" }));
        }
        self.charge()?;
        self.budget.summary.bodies += 1;
        pending.push(Step::Body {
            body,
            next: 0,
            checkpoint,
            depth,
        });
        Ok(())
    }

    fn child_depth(&self, depth: usize) -> Result<usize, IrValidationError> {
        depth
            .checked_add(1)
            .filter(|d| *d <= self.budget.limits.max_depth)
            .ok_or_else(|| self.fail(IrValidationErrorKind::Limit { resource: "depth" }))
    }

    fn body(&mut self, root: &IrBody) -> Result<(), IrValidationError> {
        let mut pending = Vec::new();
        self.enter(&mut pending, root, self.bindings.len(), 1)?;
        while let Some(step) = pending.pop() {
            match step {
                Step::PublishJoin { j, arity } => {
                    self.joins.insert(j, arity);
                    self.bindings.push(Binding::Join(j));
                }
                Step::Case {
                    alts,
                    next,
                    checkpoint,
                    depth,
                } => {
                    if let Some(alt) = alts.get(next) {
                        self.charge()?;
                        let child_depth = self.child_depth(depth)?;
                        pending.push(Step::Case {
                            alts,
                            next: next + 1,
                            checkpoint,
                            depth,
                        });
                        let body = match alt {
                            IrAlt::Ctor { body, .. } | IrAlt::Default { body } => body,
                        };
                        self.enter(&mut pending, body, self.bindings.len(), child_depth)?;
                    } else {
                        self.restore(checkpoint);
                    }
                }
                Step::Body {
                    body,
                    next,
                    checkpoint,
                    depth,
                } => {
                    self.charge()?;
                    if let Some(stmt) = body.stmts.get(next) {
                        self.budget.summary.statements += 1;
                        pending.push(Step::Body {
                            body,
                            next: next + 1,
                            checkpoint,
                            depth,
                        });
                        match stmt {
                            IrStmt::VDecl { x, expr, .. } => {
                                // The initializer cannot see the variable it defines.
                                self.expr(expr)?;
                                self.bind_variable(*x)?;
                            }
                            IrStmt::JDecl { j, params, value } => {
                                self.mark(*j)?;
                                let child_depth = self.child_depth(depth)?;
                                let checkpoint = self.bindings.len();
                                // Publish AFTER the value has left its parameter scope.
                                pending.push(Step::PublishJoin {
                                    j: *j,
                                    arity: params.len(),
                                });
                                self.params(params)?;
                                self.enter(&mut pending, value, checkpoint, child_depth)?;
                            }
                            IrStmt::Set { x, y, .. } => {
                                self.variable(*x)?;
                                self.arg(y)?;
                            }
                            IrStmt::USet { x, y, .. } | IrStmt::SSet { x, y, .. } => {
                                self.variable(*x)?;
                                self.variable(*y)?;
                            }
                            IrStmt::SetTag { x, .. }
                            | IrStmt::Inc { x, .. }
                            | IrStmt::Dec { x, .. }
                            | IrStmt::Del { x } => self.variable(*x)?,
                        }
                    } else {
                        match body.terminal.as_ref() {
                            IrTerminal::Case { x, alts, .. } => {
                                self.variable(*x)?;
                                pending.push(Step::Case {
                                    alts,
                                    next: 0,
                                    checkpoint,
                                    depth,
                                });
                            }
                            IrTerminal::Ret(arg) => {
                                self.arg(arg)?;
                                self.restore(checkpoint);
                            }
                            IrTerminal::Jmp { j, args } => {
                                self.charge()?;
                                let Some(&arity) = self.joins.get(j) else {
                                    return Err(self.fail(IrValidationErrorKind::UnknownJoinPoint {
                                        index: *j,
                                    }));
                                };
                                if args.len() != arity {
                                    return Err(self.fail(IrValidationErrorKind::Arity {
                                        target: IrCallTarget::JoinPoint(*j),
                                        provided: args.len(),
                                        expected: arity,
                                        partial: false,
                                    }));
                                }
                                self.args(args)?;
                                self.restore(checkpoint);
                            }
                            IrTerminal::Unreachable => self.restore(checkpoint),
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

/// Structural validation succeeded for the supplied inputs, not a proof that
/// they are typed, ownership-safe or executable. The graph is the existing IR
/// graph implementation, not a second graph engine.
#[derive(Debug, Clone)]
pub struct ValidatedIrCallGraph {
    graph: crate::ir::graph::IrCallGraph,
    summary: IrValidationSummary,
}

impl ValidatedIrCallGraph {
    pub fn graph(&self) -> &crate::ir::graph::IrCallGraph {
        &self.graph
    }

    pub fn summary(&self) -> &IrValidationSummary {
        &self.summary
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrValidatedGraphError {
    Validation(IrValidationError),
    Graph(crate::ir::graph::IrGraphError),
}

impl IrValidatedGraphError {
    pub fn is_resource(&self) -> bool {
        match self {
            Self::Validation(error) => error.is_resource(),
            Self::Graph(crate::ir::graph::IrGraphError::TooManyNodes) => true,
        }
    }
}

impl std::fmt::Display for IrValidatedGraphError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Validation(error) => write!(f, "{error}"),
            Self::Graph(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for IrValidatedGraphError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Validation(error) => Some(error),
            Self::Graph(error) => Some(error),
        }
    }
}

/// Validate the entire closure before building the existing call graph.
///
/// Unlike the graph's permissive measurement-oriented `add_module`, this entry
/// point rejects duplicate declarations, unknown static callees and malformed
/// bodies, including unreachable declarations. It returns no partial graph on
/// failure and does not mutate the caller's modules. The validator's structural
/// work budget bounds the IR traversed by the subsequent graph construction;
/// this is not a separate graph-byte or wall-clock quota.
///
/// Module labels and node numbering retain the existing graph's semantics.
/// Census-only callees stay `Undeclared` in that graph: a known external signature
/// is not an IR body. Dynamic `ap` calls stay absent from its named edges, and
/// `summary().dynamic_calls` reports their count. Neither successful validation
/// nor static reachability establishes complete runtime closure.
pub fn build_validated_ir_call_graph(
    modules: &[(&str, &IrModule)],
    census_externs: &BTreeMap<Name, usize>,
    limits: IrValidationLimits,
) -> Result<ValidatedIrCallGraph, IrValidatedGraphError> {
    let summary = validate_modules(
        modules.iter().map(|(_, module)| *module),
        census_externs,
        limits,
    )
    .map_err(IrValidatedGraphError::Validation)?;
    let mut graph = crate::ir::graph::IrCallGraph::new();
    for (label, module) in modules {
        graph
            .add_module(label, module)
            .map_err(IrValidatedGraphError::Graph)?;
    }
    Ok(ValidatedIrCallGraph { graph, summary })
}
