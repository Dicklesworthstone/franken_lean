//! Native expression construction and binder operations for imported Lean IR.
//!
//! The checked converter is the only object/native membrane. Cached data is
//! validated before it can prune a walk, and substitution uses the core's
//! binder-aware algorithms. The pin's two array substitution orders are
//! deliberately distinct. Reference implementation bodies are never executed.

use std::collections::{HashMap, HashSet};

use super::{
    IntrinsicFailure, IntrinsicResult, Obj, VmRefusal, bool_value, expect_arity, floats,
    level_native, nat_as_usize, type_mismatch, uint32_argument,
};
use fln_core::expr::{
    BinderInfo, Expr, ExprData, ExprNode, MAX_LOOSE_BVAR_RANGE, TooManyBoundVars,
};
use fln_core::level::{Level, MAX_LEVEL_DEPTH};
use fln_core::name::Name;
use fln_rt::convert::{CheckedExpr, Conversion, ConvertError, ExprConstructor, inject_expr};
use fln_rt::native_heap::NativeHeap;

const MAX_EXPR_NODES: usize = 1_000_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Intrinsic {
    Data,
    MkData,
    MkAppData,
    Equal,
    Eqv,
    HasLooseBVar,
    LiftLooseBVars,
    LowerLooseBVars,
    Instantiate1,
    Instantiate,
    InstantiateRev,
    InstantiateRange,
    InstantiateRevRange,
    Abstract,
    AbstractRange,
    BVar,
    App,
    Lam,
    Forall,
    Let,
    FVar,
    MVar,
    Sort,
    Const,
    Lit,
    MData,
    Proj,
}

impl Intrinsic {
    pub(super) fn for_row(row: &str) -> Option<Self> {
        Some(match row {
            "extern:Lean.Expr.data" => Self::Data,
            "extern:Lean.Expr.mkData" => Self::MkData,
            "extern:Lean.Expr.mkAppData" => Self::MkAppData,
            "extern:Lean.Expr.equal" => Self::Equal,
            "extern:Lean.Expr.eqv" => Self::Eqv,
            "extern:Lean.Expr.hasLooseBVar" => Self::HasLooseBVar,
            "extern:Lean.Expr.liftLooseBVars" => Self::LiftLooseBVars,
            "extern:Lean.Expr.lowerLooseBVars" => Self::LowerLooseBVars,
            "extern:Lean.Expr.instantiate1" => Self::Instantiate1,
            "extern:Lean.Expr.instantiate" => Self::Instantiate,
            "extern:Lean.Expr.instantiateRev" => Self::InstantiateRev,
            "extern:Lean.Expr.instantiateRange" => Self::InstantiateRange,
            "extern:Lean.Expr.instantiateRevRange" => Self::InstantiateRevRange,
            "extern:Lean.Expr.abstract" => Self::Abstract,
            "extern:Lean.Expr.abstractRange" => Self::AbstractRange,
            "mirror:Lean.Expr.bvar._override" => Self::BVar,
            "mirror:Lean.Expr.app._override" => Self::App,
            "mirror:Lean.Expr.lam._override" => Self::Lam,
            "mirror:Lean.Expr.forallE._override" => Self::Forall,
            "mirror:Lean.Expr.letE._override" => Self::Let,
            "mirror:Lean.Expr.fvar._override" => Self::FVar,
            "mirror:Lean.Expr.mvar._override" => Self::MVar,
            "mirror:Lean.Expr.sort._override" => Self::Sort,
            "mirror:Lean.Expr.const._override" => Self::Const,
            "mirror:Lean.Expr.lit._override" => Self::Lit,
            "mirror:Lean.Expr.mdata._override" => Self::MData,
            "mirror:Lean.Expr.proj._override" => Self::Proj,
            _ => return None,
        })
    }

    pub(super) fn invoke(
        self,
        row: &str,
        args: &[Obj],
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        self.invoke_bounded(row, args, MAX_EXPR_NODES)
    }

    fn invoke_bounded(
        self,
        row: &str,
        args: &[Obj],
        node_budget: usize,
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        let arity = match self {
            Self::Data | Self::BVar | Self::FVar | Self::MVar | Self::Sort | Self::Lit => 1,
            Self::MkData => 7,
            Self::LiftLooseBVars | Self::LowerLooseBVars | Self::AbstractRange | Self::Proj => 3,
            Self::Lam | Self::Forall | Self::InstantiateRange | Self::InstantiateRevRange => 4,
            Self::Let => 5,
            _ => 2,
        };
        expect_arity(row, args, arity)?;
        let mut operands = Operands {
            conversion: Conversion::with_node_budget(node_budget),
            heap: NativeHeap::new(),
        };
        let mut work = WorkBudget {
            allowed: node_budget.min(MAX_EXPR_NODES),
            visited: 0,
        };
        match self {
            Self::FVar
            | Self::MVar
            | Self::Sort
            | Self::Const
            | Self::Lit
            | Self::MData
            | Self::Proj => {
                let constructor = match self {
                    Self::FVar => ExprConstructor::FVar,
                    Self::MVar => ExprConstructor::MVar,
                    Self::Sort => ExprConstructor::Sort,
                    Self::Const => ExprConstructor::Const,
                    Self::Lit => ExprConstructor::Lit,
                    Self::MData => ExprConstructor::MData,
                    Self::Proj => ExprConstructor::Proj,
                    _ => unreachable!("only the selected native constructors enter this arm"),
                };
                operands.constructed(constructor, args)
            }
            Self::BVar => {
                let index = nat_as_usize(&args[0], "Expr.bvar", 0)?;
                if index
                    .filter(|index| *index < MAX_LOOSE_BVAR_RANGE as usize)
                    .is_none()
                {
                    return Err(range_exhausted(
                        index.map_or(u64::MAX, |index| (index as u64).saturating_add(1)),
                    ));
                }
                operands.constructed(ExprConstructor::BVar, args)
            }
            Self::App => operands.constructed(ExprConstructor::App, args),
            Self::Lam | Self::Forall => {
                let info = binder_info(&args[3])?;
                operands.constructed(
                    if self == Self::Lam {
                        ExprConstructor::Lam(info)
                    } else {
                        ExprConstructor::Forall(info)
                    },
                    &args[..3],
                )
            }
            Self::Let => {
                let non_dep = bool_value(&args[4], "Expr.letE", 4)?;
                operands.constructed(ExprConstructor::Let(non_dep), &args[..4])
            }
            Self::MkData => {
                let hash = floats::wide_argument(&args[0], "Expr.mkData", 0)?;
                let range = nat_as_usize(&args[1], "Expr.mkData", 1)?;
                // The pinned extern refuses a heap-sized range before packing;
                // it never truncates this Nat to the 20-bit stored field.
                let range = match range {
                    Some(range)
                        if args[1].is_scalar() && range <= MAX_LOOSE_BVAR_RANGE as usize =>
                    {
                        range as u32
                    }
                    other => {
                        return Err(range_exhausted(
                            other.map_or(u64::MAX, |value| value as u64),
                        ));
                    }
                };
                let depth = uint32_argument(&args[2], "Expr.mkData", 2)?;
                let data = ExprData::pack(
                    hash,
                    range,
                    depth,
                    boolean(&args[3], 3)?,
                    boolean(&args[4], 4)?,
                    boolean(&args[5], 5)?,
                    boolean(&args[6], 6)?,
                )
                .map_err(bound_vars)?;
                Ok(IntrinsicResult::owned(wide(data.0)))
            }
            Self::MkAppData => {
                let f = ExprData(floats::wide_argument(&args[0], "Expr.mkAppData", 0)?);
                let a = ExprData(floats::wide_argument(&args[1], "Expr.mkAppData", 1)?);
                Ok(IntrinsicResult::owned(wide(ExprData::pack_app(f, a).0)))
            }
            Self::Data => {
                let expr = operands.expr(&args[0])?;
                // This one row has a generated value result, rather than the
                // borrowed-arguments/owned-result rule of the other Expr rows.
                Ok(IntrinsicResult::scalar(wide(expr.data().0)))
            }
            Self::Equal | Self::Eqv => {
                let left = operands.expr(&args[0])?;
                let right = operands.expr(&args[1])?;
                check_equality_pairs(&left, &right, &mut work)?;
                let equal = if self == Self::Eqv {
                    left.is_alpha_equiv(&right)
                } else {
                    left == right
                };
                Ok(IntrinsicResult::owned(Obj::mk_nat(usize::from(equal))))
            }
            Self::HasLooseBVar => {
                let expr = operands.expr(&args[0])?;
                let index = small_nat_u32(&args[1], "Expr.hasLooseBVar", 1)?;
                let found = if let Some(index) = index {
                    check_transform(&expr, index, None, &mut work)?;
                    expr.has_loose_bvar(index)
                } else {
                    false
                };
                Ok(IntrinsicResult::owned(Obj::mk_nat(usize::from(found))))
            }
            Self::LiftLooseBVars => {
                let expr = operands.expr(&args[0])?;
                let cutoff = small_nat_u32(&args[1], "Expr.liftLooseBVars", 1)?;
                let amount = small_nat_u32(&args[2], "Expr.liftLooseBVars", 2)?;
                let (Some(cutoff), Some(amount)) = (cutoff, amount) else {
                    return Ok(IntrinsicResult::owned(args[0].clone_ref()));
                };
                if amount != 0 {
                    check_transform(&expr, cutoff, None, &mut work)?;
                }
                let result = expr.lift_loose(cutoff, amount).map_err(bound_vars)?;
                operands.result(&expr, &args[0], result)
            }
            Self::LowerLooseBVars => {
                let root = operands
                    .conversion
                    .check_expr(&args[0])
                    .map_err(conversion_error)?;
                let cutoff = small_nat_u32(&args[1], "Expr.lowerLooseBVars", 1)?;
                let amount = small_nat_u32(&args[2], "Expr.lowerLooseBVars", 2)?;
                let (Some(cutoff), Some(amount)) = (cutoff, amount) else {
                    return Ok(IntrinsicResult::owned(args[0].clone_ref()));
                };
                // The C boundary compares the full tagged Nat words before
                // narrowing to unsigned. Moving this guard after narrowing
                // changes valid large-scalar calls at the pinned boundary.
                if args[1].unbox() < args[2].unbox() {
                    return Ok(IntrinsicResult::owned(args[0].clone_ref()));
                }
                lower_loose_bvars(&root, cutoff, amount, &mut operands.conversion, &mut work)
                    .map(IntrinsicResult::owned)
            }
            Self::Instantiate1
            | Self::Instantiate
            | Self::InstantiateRev
            | Self::InstantiateRange
            | Self::InstantiateRevRange => {
                let expr = operands.expr(&args[0])?;
                let mut replacements = if self == Self::Instantiate1 {
                    vec![operands.expr(&args[1])?]
                } else {
                    let (array, range) =
                        if matches!(self, Self::InstantiateRange | Self::InstantiateRevRange) {
                            let operation = if self == Self::InstantiateRange {
                                "Expr.instantiateRange"
                            } else {
                                "Expr.instantiateRevRange"
                            };
                            let range = substitution_range(operation, args)?;
                            (&args[3], range)
                        } else {
                            (&args[1], 0..array_len(&args[1])?)
                        };
                    operands.expr_slice(array, range, work.allowed)?
                };
                // Core subst_loose indexes replacements from the end, as the
                // pin's instantiateRev does. instantiate uses the other order.
                if matches!(self, Self::Instantiate | Self::InstantiateRange) {
                    replacements.reverse();
                }
                if !replacements.is_empty() {
                    check_transform(&expr, 0, Some(&replacements), &mut work)?;
                }
                let result = expr.subst_loose(0, &replacements).map_err(bound_vars)?;
                operands.result(&expr, &args[0], result)
            }
            Self::Abstract | Self::AbstractRange => {
                let root = operands
                    .conversion
                    .check_expr(&args[0])
                    .map_err(conversion_error)?;
                let (array, len) = if self == Self::AbstractRange {
                    let len = array_len(&args[2])?;
                    nat_as_usize(&args[1], "Expr.abstractRange", 1)?;
                    // The pin clips a scalar count and uses the entire array
                    // for a heap-sized Nat. Neither case narrows to u32.
                    let count = if args[1].is_scalar() {
                        args[1].unbox().min(len)
                    } else {
                        len
                    };
                    (&args[2], count)
                } else {
                    (&args[1], array_len(&args[1])?)
                };
                let variables = operands.expr_slice(array, 0..len, work.allowed)?;
                abstract_variables(&root, &variables, &mut operands.conversion, &mut work)
                    .map(IntrinsicResult::owned)
            }
        }
    }
}

struct Operands {
    conversion: Conversion,
    heap: NativeHeap,
}

impl Operands {
    fn expr_slice(
        &mut self,
        array: &Obj,
        range: std::ops::Range<usize>,
        allowed: usize,
    ) -> Result<Vec<Expr>, IntrinsicFailure> {
        if range.len() > allowed {
            return Err(IntrinsicFailure::MirrorResource {
                resource: "expression substitution entries",
                allowed: allowed as u64,
                observed: range.len() as u64,
            });
        }
        range.map(|i| self.expr(&array.array_child(i))).collect()
    }

    fn constructed(
        &mut self,
        constructor: ExprConstructor,
        fields: &[Obj],
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        let checked = self
            .conversion
            .construct_expr(constructor, fields.iter().map(Obj::clone_ref).collect())
            .map_err(conversion_error)?;
        Ok(IntrinsicResult::raw_object(checked.object().clone_ref()))
    }

    fn expr(&mut self, value: &Obj) -> Result<Expr, IntrinsicFailure> {
        // Interning two operands in one heap could compare them structurally
        // before the equality pair budget is checked. Each input therefore
        // gets its own temporary heap, while this Conversion retains aggregate
        // node/byte accounting across every operand in the native invocation.
        let mut heap = NativeHeap::new();
        let handle = self
            .conversion
            .project_expr(&mut heap, value)
            .map_err(conversion_error)?;
        heap.get(handle)
            .cloned()
            .map_err(|_| VmRefusal::InvalidCtorObject.into())
    }

    fn result(
        &mut self,
        original: &Expr,
        carrier: &Obj,
        result: Expr,
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        if original.allocation_identity() == result.allocation_identity() {
            return Ok(IntrinsicResult::owned(carrier.clone_ref()));
        }
        let handle = self.heap.alloc(result);
        inject_expr(&self.heap, handle)
            .map(IntrinsicResult::owned)
            .map_err(conversion_error)
    }
}

fn wide(value: u64) -> Obj {
    Obj::mk_ctor(0, Vec::new(), &value.to_ne_bytes())
}

fn boolean(value: &Obj, argument: usize) -> Result<bool, VmRefusal> {
    if value.is_scalar() && value.unbox() <= 1 {
        Ok(value.unbox() != 0)
    } else {
        Err(type_mismatch("Expr.mkData", argument, "Bool", value))
    }
}

fn binder_info(value: &Obj) -> Result<BinderInfo, VmRefusal> {
    if value.is_scalar() {
        match value.unbox() {
            0 => return Ok(BinderInfo::Default),
            1 => return Ok(BinderInfo::Implicit),
            2 => return Ok(BinderInfo::StrictImplicit),
            3 => return Ok(BinderInfo::InstImplicit),
            _ => {}
        }
    }
    Err(type_mismatch(
        "Expr binder constructor",
        3,
        "BinderInfo",
        value,
    ))
}

fn small_nat_u32(
    value: &Obj,
    operation: &'static str,
    argument: usize,
) -> Result<Option<u32>, VmRefusal> {
    // Validate heap Nat carriers even on the extern's heap-sized fast path.
    nat_as_usize(value, operation, argument)?;
    // The pinned C interface first tests the tagged representation and then
    // narrows the small Nat's word to C unsigned, including its low-word wrap.
    Ok(value.is_scalar().then(|| value.unbox() as u32))
}

fn array_len(array: &Obj) -> Result<usize, VmRefusal> {
    array
        .try_array_view()
        .map(|(len, _)| len)
        .ok_or(VmRefusal::InvalidArrayObject)
}

fn substitution_range(
    operation: &'static str,
    args: &[Obj],
) -> Result<std::ops::Range<usize>, VmRefusal> {
    let size = array_len(&args[3])?;
    // These externs require scalar endpoints and begin <= end <= size. The
    // Reference aborts on invalid ranges; refuse them without a host panic or
    // silently clipping them to a different, executable substitution.
    let begin = nat_as_usize(&args[1], operation, 1)?;
    let end = nat_as_usize(&args[2], operation, 2)?;
    let begin = begin
        .filter(|_| args[1].is_scalar())
        .ok_or(VmRefusal::ArrayIndexOutOfBounds {
            index: usize::MAX,
            size,
        })?;
    let end = end
        .filter(|_| args[2].is_scalar())
        .ok_or(VmRefusal::ArrayIndexOutOfBounds {
            index: usize::MAX,
            size,
        })?;
    if end > size {
        return Err(VmRefusal::ArrayIndexOutOfBounds { index: end, size });
    }
    if begin > end {
        return Err(VmRefusal::ArrayIndexOutOfBounds {
            index: begin,
            size: end,
        });
    }
    Ok(begin..end)
}

fn lower_loose_bvars(
    root: &CheckedExpr,
    cutoff: u32,
    amount: u32,
    conversion: &mut Conversion,
    budget: &mut WorkBudget,
) -> Result<Obj, IntrinsicFailure> {
    if amount == 0 || cutoff >= root.expression().loose_bvar_range() {
        return Ok(root.object().clone_ref());
    }
    replace_binders(root, conversion, budget, |current, depth, conversion| {
        let Some(cutoff) = cutoff.checked_add(depth) else {
            return Ok(Some(current.clone()));
        };
        if cutoff >= current.expression().loose_bvar_range() {
            return Ok(Some(current.clone()));
        }
        if let ExprNode::BVar { idx } = current.expression().node() {
            // After the pin's scalar-word guard, narrowing to C unsigned can
            // wrap cutoff below amount. Its Nat subtraction still saturates.
            let index = idx.saturating_sub(amount);
            return conversion
                .construct_expr(ExprConstructor::BVar, vec![Obj::mk_nat(index as usize)])
                .map(Some)
                .map_err(conversion_error);
        }
        Ok(None)
    })
}

/// The pin abstracts both free and meta variables by their ids, with the
/// rightmost duplicate winning. Other array entries still occupy a binder
/// position. Use checked reconstruction to retain unchanged object identity,
/// and memoize by (object, binder depth) so shared bodies remain capture-free.
fn abstract_variables(
    root: &CheckedExpr,
    variables: &[Expr],
    conversion: &mut Conversion,
    budget: &mut WorkBudget,
) -> Result<Obj, IntrinsicFailure> {
    let mut indices: HashMap<(bool, Name), usize> = HashMap::new();
    for (index, variable) in variables.iter().enumerate() {
        budget.visit()?;
        if let Some(key) = variable_key(variable) {
            indices.insert(key, variables.len() - index - 1);
        }
    }
    if indices.is_empty() {
        return Ok(root.object().clone_ref());
    }

    replace_binders(root, conversion, budget, |current, depth, conversion| {
        let expr = current.expression();
        if !expr.has_fvar() && !expr.has_expr_mvar() {
            return Ok(Some(current.clone()));
        }
        if let Some(variable) = variable_key(expr) {
            let result = if let Some(index) = indices.get(&variable) {
                let index = index.saturating_add(depth as usize);
                if index >= MAX_LOOSE_BVAR_RANGE as usize {
                    return Err(range_exhausted((index as u64).saturating_add(1)));
                }
                conversion
                    .construct_expr(ExprConstructor::BVar, vec![Obj::mk_nat(index)])
                    .map_err(conversion_error)?
            } else {
                current.clone()
            };
            return Ok(Some(result));
        }
        Ok(None)
    })
}

/// A checked, iterative replacement walk shared by binder operations. The
/// binder depth is part of each memo key: one carrier may occur both inside
/// and outside a binder, where it has different substitution semantics.
fn replace_binders(
    root: &CheckedExpr,
    conversion: &mut Conversion,
    budget: &mut WorkBudget,
    mut replace: impl FnMut(
        &CheckedExpr,
        u32,
        &mut Conversion,
    ) -> Result<Option<CheckedExpr>, IntrinsicFailure>,
) -> Result<Obj, IntrinsicFailure> {
    // Keep root alive until the traversal finishes: memo keys are identities
    // of its original carriers, never identities of transient replacements.
    let root_key = (root.object().identity_token(), 0);
    let mut done: HashMap<(usize, u32), CheckedExpr> = HashMap::new();
    let mut stack = vec![(root.clone(), 0_u32, false)];
    while let Some((current, depth, exit)) = stack.pop() {
        let key = (current.object().identity_token(), depth);
        if done.contains_key(&key) {
            continue;
        }
        if !exit {
            budget.visit()?;
            if let Some(result) = replace(&current, depth, conversion)? {
                done.insert(key, result);
                continue;
            }
            let children = current.children().map_err(conversion_error)?;
            stack.push((current.clone(), depth, true));
            for (index, child) in children.into_iter().enumerate().rev() {
                stack.push((
                    child,
                    child_depth(current.expression(), index, depth),
                    false,
                ));
            }
        } else {
            let children = current
                .children()
                .map_err(conversion_error)?
                .iter()
                .enumerate()
                .map(|(index, child)| {
                    done.get(&(
                        child.object().identity_token(),
                        child_depth(current.expression(), index, depth),
                    ))
                    .cloned()
                    .ok_or(VmRefusal::InvalidCtorObject)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let result = conversion
                .rebuild_expr(&current, &children)
                .map_err(conversion_error)?;
            done.insert(key, result);
        }
    }
    done.remove(&root_key)
        .map(|result| result.object().clone_ref())
        .ok_or_else(|| VmRefusal::InvalidCtorObject.into())
}

fn variable_key(expr: &Expr) -> Option<(bool, Name)> {
    match expr.node() {
        ExprNode::FVar { id } => Some((false, id.0.clone())),
        ExprNode::MVar { id } => Some((true, id.0.clone())),
        _ => None,
    }
}

fn child_depth(parent: &Expr, index: usize, depth: u32) -> u32 {
    match (parent.node(), index) {
        (ExprNode::Lam { .. } | ExprNode::ForallE { .. }, 1) | (ExprNode::LetE { .. }, 2) => {
            depth.saturating_add(1)
        }
        _ => depth,
    }
}

fn conversion_error(error: ConvertError) -> IntrinsicFailure {
    match error {
        ConvertError::NodeBudgetExhausted {
            visited, budget, ..
        } => IntrinsicFailure::MirrorResource {
            resource: "expression projection nodes",
            allowed: budget as u64,
            observed: visited as u64,
        },
        ConvertError::ByteBudgetExhausted {
            visited, budget, ..
        } => IntrinsicFailure::MirrorResource {
            resource: "expression projection bytes",
            allowed: budget as u64,
            observed: visited as u64,
        },
        ConvertError::NativeOverflow { family: "level" } => IntrinsicFailure::MirrorResource {
            resource: "universe level depth",
            allowed: u64::from(MAX_LEVEL_DEPTH),
            observed: u64::from(MAX_LEVEL_DEPTH) + 1,
        },
        ConvertError::NativeOverflow { .. } => range_exhausted(u64::MAX),
        _ => VmRefusal::InvalidCtorObject.into(),
    }
}

fn range_exhausted(observed: u64) -> IntrinsicFailure {
    IntrinsicFailure::MirrorResource {
        resource: "expression loose bound variable range",
        allowed: u64::from(MAX_LOOSE_BVAR_RANGE),
        observed: observed.max(u64::from(MAX_LOOSE_BVAR_RANGE) + 1),
    }
}

fn bound_vars(error: TooManyBoundVars) -> IntrinsicFailure {
    range_exhausted(u64::from(error.range))
}

struct WorkBudget {
    allowed: usize,
    visited: usize,
}

impl WorkBudget {
    fn level_pairs(&mut self, left: &Level, right: &Level) -> Result<(), IntrinsicFailure> {
        let remaining = self.allowed.saturating_sub(self.visited);
        let visited = level_native::check_equality_pairs(left, right, remaining)?;
        self.visited += visited;
        Ok(())
    }

    fn visit(&mut self) -> Result<(), IntrinsicFailure> {
        self.visited = self.visited.saturating_add(1);
        if self.visited > self.allowed {
            return Err(IntrinsicFailure::MirrorResource {
                resource: "expression traversal nodes",
                allowed: self.allowed as u64,
                observed: self.visited as u64,
            });
        }
        Ok(())
    }
}

/// The same value can be shared differently on each side. Count pairs, not
/// just input nodes, before delegating the equality judgment to fln-core.
fn check_equality_pairs(
    left: &Expr,
    right: &Expr,
    budget: &mut WorkBudget,
) -> Result<(), IntrinsicFailure> {
    let mut visited = HashSet::new();
    let mut stack = vec![(left, right)];
    while let Some((left, right)) = stack.pop() {
        let pair = (left.allocation_identity(), right.allocation_identity());
        if !visited.insert(pair) {
            continue;
        }
        budget.visit()?;
        if pair.0 == pair.1 || left.data() != right.data() {
            continue;
        }
        match (left.node(), right.node()) {
            (ExprNode::Sort { level: left }, ExprNode::Sort { level: right }) => {
                budget.level_pairs(left, right)?;
            }
            (ExprNode::Const { levels: left, .. }, ExprNode::Const { levels: right, .. })
                if left.len() == right.len() =>
            {
                for (left, right) in left.iter().zip(right) {
                    budget.level_pairs(left, right)?;
                }
            }
            (ExprNode::App { f: lf, a: la }, ExprNode::App { f: rf, a: ra }) => {
                stack.push((la, ra));
                stack.push((lf, rf));
            }
            (
                ExprNode::Lam {
                    binder_type: lt,
                    body: lb,
                    ..
                },
                ExprNode::Lam {
                    binder_type: rt,
                    body: rb,
                    ..
                },
            )
            | (
                ExprNode::ForallE {
                    binder_type: lt,
                    body: lb,
                    ..
                },
                ExprNode::ForallE {
                    binder_type: rt,
                    body: rb,
                    ..
                },
            ) => {
                stack.push((lb, rb));
                stack.push((lt, rt));
            }
            (
                ExprNode::LetE {
                    type_: lt,
                    value: lv,
                    body: lb,
                    ..
                },
                ExprNode::LetE {
                    type_: rt,
                    value: rv,
                    body: rb,
                    ..
                },
            ) => {
                stack.push((lb, rb));
                stack.push((lv, rv));
                stack.push((lt, rt));
            }
            (ExprNode::MData { expr: left, .. }, ExprNode::MData { expr: right, .. })
            | (ExprNode::Proj { expr: left, .. }, ExprNode::Proj { expr: right, .. }) => {
                stack.push((left, right));
            }
            _ => {}
        }
    }
    Ok(())
}

/// Account for the core algorithm's distinct binder contexts before allocating
/// transformed nodes. A shared input can appear at many binder depths; merely
/// bounding input allocations would leave that expansion unbounded. Replacement
/// lifting shares this allowance, including repeated lifts at distinct sites.
fn check_transform(
    root: &Expr,
    cutoff: u32,
    replacements: Option<&[Expr]>,
    budget: &mut WorkBudget,
) -> Result<(), IntrinsicFailure> {
    let mut visited = HashSet::new();
    let mut stack = vec![(root, cutoff)];
    while let Some((expr, cut)) = stack.pop() {
        if !visited.insert((expr.allocation_identity(), cut)) {
            continue;
        }
        budget.visit()?;
        if expr.loose_bvar_range() <= cut {
            continue;
        }
        match expr.node() {
            ExprNode::BVar { idx } => {
                if let Some(replacements) = replacements {
                    let offset = (*idx - cut) as usize;
                    if offset < replacements.len() && cut != 0 {
                        check_transform(
                            &replacements[replacements.len() - 1 - offset],
                            0,
                            None,
                            budget,
                        )?;
                    }
                }
            }
            ExprNode::App { f, a } => {
                stack.push((a, cut));
                stack.push((f, cut));
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                stack.push((body, cut.saturating_add(1)));
                stack.push((binder_type, cut));
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                stack.push((body, cut.saturating_add(1)));
                stack.push((value, cut));
                stack.push((type_, cut));
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                stack.push((expr, cut));
            }
            ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Const { .. }
            | ExprNode::Lit { .. } => {}
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
