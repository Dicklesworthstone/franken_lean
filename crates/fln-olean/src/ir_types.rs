//! Representation-type checks for decoded IR, after structural validation.
//!
//! Semantic anchors: the pin's `Lean/Compiler/IR/Basic.lean` (`isObj`,
//! `isScalar`) and `IR/Checker.lean` (`checkExpr`). This is native Rust; the
//! Reference is neither loaded nor executed. In particular `void` belongs to
//! the pin's object category, but is NOT a permitted `proj` source.
//!
//! These are the pin's expression representation rules, not a complete IR
//! soundness or ownership proof. As in that checker, full applications do not
//! compare argument/result types, numeric literals have no result-type rule,
//! and returns and mutation/RC instructions retain structural checks only.
//! Constructor layout bounds, linear aggregate use and runtime-tag/RC balance
//! are separate obligations. Successful checking grants no execution authority.

use crate::ir::{
    IrAlt, IrBody, IrDecl, IrExpr, IrIndex, IrLit, IrModule, IrParam, IrStmt, IrTerminal,
    IrType,
};
use crate::ir_validate::{
    IrValidationError, IrValidationLimits, IrValidationSummary, validate_ir,
};
use fln_core::name::Name;
use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IrTypeValidationSummary {
    pub structural: IrValidationSummary,
    pub expressions: u64,
    /// Type nodes visited, including structural type-equality comparisons.
    pub type_nodes: u64,
    /// Cumulative structural PLUS representation work, under one allowance.
    pub work: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrTypeValidationError {
    Structural(IrValidationError),
    Limit {
        declaration: Option<Name>,
        resource: &'static str,
    },
    Rule {
        declaration: Name,
        binding: IrIndex,
        operation: &'static str,
        expected: &'static str,
        found: &'static str,
    },
    Projection {
        declaration: Name,
        binding: IrIndex,
        index: u64,
        fields: usize,
    },
    /// Defensive: the preceding structural pass normally prevents this.
    UnknownVariable {
        declaration: Name,
        index: IrIndex,
    },
}

impl IrTypeValidationError {
    pub fn is_resource(&self) -> bool {
        match self {
            Self::Structural(error) => error.is_resource(),
            Self::Limit { .. } => true,
            _ => false,
        }
    }
}

impl std::fmt::Display for IrTypeValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Never clone or recursively print an attacker-controlled type tree.
        write!(f, "IR representation validation: {self:?}")
    }
}

impl std::error::Error for IrTypeValidationError {}

type Result<T> = std::result::Result<T, IrTypeValidationError>;

/// Check scopes, callee closure and arities first, then the expression
/// representation rules. Census entries provide arities only: neither this
/// pass nor the pin's expression checker proves their ABI signatures.
/// The supplied modules remain unchanged on success and every failure.
pub fn validate_ir_types(
    modules: &[IrModule],
    census_externs: &BTreeMap<Name, usize>,
    limits: IrValidationLimits,
) -> Result<IrTypeValidationSummary> {
    let structural = validate_ir(modules, census_externs, limits)
        .map_err(IrTypeValidationError::Structural)?;
    check_after_structure(modules, structural, limits)
}

/// Internal composition point for the file/graph path. The summary MUST come
/// from structural validation of these same immutable modules and signatures.
/// Keeping it crate-private prevents callers from forging a structural pass.
pub(crate) fn check_after_structure(
    modules: &[IrModule],
    structural: IrValidationSummary,
    limits: IrValidationLimits,
) -> Result<IrTypeValidationSummary> {
    let mut meter = Meter {
        limits,
        summary: IrTypeValidationSummary {
            structural,
            expressions: 0,
            type_nodes: 0,
            work: structural.work,
        },
        declaration: None,
        binding: 0,
    };
    let mut declarations = BTreeMap::new();
    for module in modules {
        meter.charge()?;
        for declaration in &module.decls {
            meter.charge()?;
            declarations.insert(declaration.name(), declaration);
        }
    }
    for declaration in declarations.into_values() {
        meter.declaration = Some(declaration.name().clone());
        check_declaration(declaration, &mut meter)?;
    }
    Ok(meter.summary)
}

struct Meter {
    limits: IrValidationLimits,
    summary: IrTypeValidationSummary,
    declaration: Option<Name>,
    binding: IrIndex,
}

impl Meter {
    fn limit(&self, resource: &'static str) -> IrTypeValidationError {
        IrTypeValidationError::Limit {
            declaration: self.declaration.clone(),
            resource,
        }
    }

    fn name(&self) -> Name {
        self.declaration.clone().unwrap_or_else(Name::anonymous)
    }

    fn charge(&mut self) -> Result<()> {
        self.summary.work = self.summary.work.checked_add(1)
            .filter(|work| *work <= self.limits.max_work)
            .ok_or_else(|| self.limit("work"))?;
        Ok(())
    }

    fn rule(&self, operation: &'static str, expected: &'static str, ty: &IrType) -> IrTypeValidationError {
        IrTypeValidationError::Rule {
            declaration: self.name(),
            binding: self.binding,
            operation,
            expected,
            found: category(ty),
        }
    }

    fn require(&mut self, operation: &'static str, expected: &'static str, ty: &IrType, valid: bool) -> Result<()> {
        self.charge()?;
        if valid { Ok(()) } else { Err(self.rule(operation, expected, ty)) }
    }

    fn object(&mut self, operation: &'static str, ty: &IrType) -> Result<()> {
        self.require(operation, "object, tagged, tobject or void", ty, is_object(ty))
    }

    fn scalar(&mut self, operation: &'static str, ty: &IrType) -> Result<()> {
        self.require(operation, "scalar", ty, is_scalar(ty))
    }

    /// No recursive clone/equality/formatting of aggregate types, even for
    /// callers constructing models directly rather than using the decoder.
    fn visit_type(&mut self, root: &IrType) -> Result<()> {
        let mut pending = vec![(root, 1usize)];
        while let Some((ty, depth)) = pending.pop() {
            self.charge()?;
            if depth > self.limits.max_depth {
                return Err(self.limit("type depth"));
            }
            self.summary.type_nodes += 1;
            if let IrType::Struct { types, .. } | IrType::Union { types, .. } = ty {
                for child in types.iter().rev() {
                    self.charge()?;
                    let child_depth = depth.checked_add(1).ok_or_else(|| self.limit("type depth"))?;
                    pending.push((child, child_depth));
                }
            }
        }
        Ok(())
    }

    fn same_type(&mut self, operation: &'static str, expected: &IrType, actual: &IrType) -> Result<()> {
        let mut pending = vec![(expected, actual)];
        while let Some((left, right)) = pending.pop() {
            self.charge()?;
            self.summary.type_nodes += 1;
            let members = match (left, right) {
                (
                    IrType::Struct { lean_type: a, types: xs },
                    IrType::Struct { lean_type: b, types: ys },
                ) if a == b => Some((xs, ys)),
                (
                    IrType::Union { lean_type: a, types: xs },
                    IrType::Union { lean_type: b, types: ys },
                ) if a == b => Some((xs, ys)),
                (IrType::Struct { .. } | IrType::Union { .. }, _)
                | (_, IrType::Struct { .. } | IrType::Union { .. }) => {
                    return Err(self.rule(operation, category(left), right));
                }
                _ if std::mem::discriminant(left) == std::mem::discriminant(right) => None,
                _ => return Err(self.rule(operation, category(left), right)),
            };
            if let Some((xs, ys)) = members {
                if xs.len() != ys.len() {
                    return Err(self.rule(operation, "matching aggregate fields", right));
                }
                for pair in xs.iter().zip(ys).rev() {
                    self.charge()?;
                    pending.push(pair);
                }
            }
        }
        Ok(())
    }
}

fn category(ty: &IrType) -> &'static str {
    match ty {
        IrType::Float => "float", IrType::Float32 => "float32",
        IrType::UInt8 => "uint8", IrType::UInt16 => "uint16",
        IrType::UInt32 => "uint32", IrType::UInt64 => "uint64",
        IrType::USize => "usize", IrType::Object => "object",
        IrType::TObject => "tobject", IrType::Tagged => "tagged",
        IrType::Void => "void", IrType::Erased => "erased",
        IrType::Struct { .. } => "struct", IrType::Union { .. } => "union",
    }
}

fn is_object(ty: &IrType) -> bool {
    matches!(ty, IrType::Object | IrType::TObject | IrType::Tagged | IrType::Void)
}

fn is_scalar(ty: &IrType) -> bool {
    matches!(ty, IrType::Float | IrType::Float32 | IrType::UInt8 | IrType::UInt16
        | IrType::UInt32 | IrType::UInt64 | IrType::USize)
}

fn add_params<'a>(params: &'a [IrParam], locals: &mut BTreeMap<IrIndex, &'a IrType>, meter: &mut Meter) -> Result<()> {
    for param in params {
        meter.charge()?;
        meter.visit_type(&param.ty)?;
        locals.insert(param.x, &param.ty);
    }
    Ok(())
}

fn check_declaration(declaration: &IrDecl, meter: &mut Meter) -> Result<()> {
    let (params, result, body) = match declaration {
        IrDecl::Function { params, result, body, .. } => (params, result, Some(body)),
        IrDecl::Extern { params, result, .. } => (params, result, None),
    };
    let mut locals = BTreeMap::new();
    meter.visit_type(result)?;
    add_params(params, &mut locals, meter)?;
    let Some(body) = body else { return Ok(()); };
    let mut pending: Vec<&IrBody> = vec![body];
    let mut expressions = Vec::new();
    // Structural validation already proved scopes and declaration-wide index
    // uniqueness. A borrowed index of types is therefore sufficient here; this
    // does not replace lexical scoping with a second, global-scope checker.
    while let Some(body) = pending.pop() {
        meter.charge()?;
        for stmt in &body.stmts {
            meter.charge()?;
            match stmt {
                IrStmt::VDecl { x, ty, expr } => {
                    meter.visit_type(ty)?;
                    if let IrExpr::Box { ty, .. } = expr { meter.visit_type(ty)?; }
                    locals.insert(*x, ty);
                    expressions.push((*x, ty, expr));
                }
                IrStmt::JDecl { params, value, .. } => {
                    add_params(params, &mut locals, meter)?;
                    pending.push(value);
                }
                IrStmt::SSet { ty, .. } => meter.visit_type(ty)?,
                _ => {}
            }
        }
        if let IrTerminal::Case { x_type, alts, .. } = body.terminal.as_ref() {
            meter.visit_type(x_type)?;
            for alt in alts.iter().rev() {
                meter.charge()?;
                let (IrAlt::Ctor { body, .. } | IrAlt::Default { body }) = alt;
                pending.push(body);
            }
        }
    }
    for (binding, result, expr) in expressions {
        meter.binding = binding;
        meter.charge()?;
        meter.summary.expressions += 1;
        check_expr(result, expr, &locals, meter)?;
    }
    Ok(())
}

fn check_expr(result: &IrType, expr: &IrExpr, locals: &BTreeMap<IrIndex, &IrType>, meter: &mut Meter) -> Result<()> {
    // Returning a borrow from locals does not borrow the mutable meter.
    let get = |index: IrIndex| locals.get(&index).copied();
    let source = |index: IrIndex, meter: &Meter| {
        get(index).ok_or_else(|| IrTypeValidationError::UnknownVariable {
            declaration: meter.name(), index,
        })
    };
    match expr {
        IrExpr::Pap { .. } => meter.object("pap result", result),
        IrExpr::Ap { x, .. } => {
            meter.object("ap source", source(*x, meter)?)?;
            meter.object("ap result", result)
        }
        IrExpr::Ctor { info, .. } => {
            if info.size != 0 || info.usize != 0 || info.ssize != 0 {
                meter.object("reference constructor result", result)?;
            }
            Ok(())
        }
        IrExpr::Reset { x, .. } | IrExpr::Reuse { x, .. } => {
            meter.object("reset/reuse source", source(*x, meter)?)?;
            meter.object("reset/reuse result", result)
        }
        IrExpr::Box { ty, x } => {
            meter.object("box result", result)?;
            let actual = source(*x, meter)?;
            meter.scalar("box source", actual)?;
            meter.same_type("box annotation", ty, actual)
        }
        IrExpr::Unbox { x } => {
            meter.object("unbox source", source(*x, meter)?)?;
            meter.scalar("unbox result", result)
        }
        IrExpr::Proj { i, x } => match source(*x, meter)? {
            IrType::Object | IrType::TObject => meter.object("proj result", result),
            IrType::Tagged => Ok(()),
            IrType::Struct { types, .. } | IrType::Union { types, .. } => {
                let field = usize::try_from(*i).ok().and_then(|i| types.get(i))
                    .ok_or_else(|| IrTypeValidationError::Projection {
                        declaration: meter.name(), binding: meter.binding, index: *i, fields: types.len(),
                    })?;
                meter.same_type("proj aggregate field", field, result)
            }
            ty => Err(meter.rule("proj source", "object, tobject, tagged, struct or union", ty)),
        },
        IrExpr::UProj { x, .. } => {
            meter.object("uproj source", source(*x, meter)?)?;
            meter.require("uproj result", "usize", result, matches!(result, IrType::USize))
        }
        IrExpr::SProj { x, .. } => {
            meter.object("sproj source", source(*x, meter)?)?;
            meter.scalar("sproj result", result)
        }
        IrExpr::IsShared { x } => {
            meter.object("isShared source", source(*x, meter)?)?;
            meter.require("isShared result", "uint8", result, matches!(result, IrType::UInt8))
        }
        IrExpr::Lit(IrLit::Str(_)) => meter.object("string literal result", result),
        IrExpr::Fap { .. } | IrExpr::Lit(IrLit::Num(_)) => Ok(()),
    }
}
