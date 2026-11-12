//! Native expression construction and binder operations for imported Lean IR.
//!
//! The checked converter is the only object/native membrane. Cached data is
//! validated before it can prune a walk, and substitution uses the core's
//! binder-aware algorithms. The pin's two array substitution orders are
//! deliberately distinct. Reference implementation bodies are never executed.

use std::collections::HashSet;

use super::{
    IntrinsicFailure, IntrinsicResult, Obj, VmRefusal, bool_value, expect_arity, floats,
    level_native, nat_as_usize, type_mismatch, uint32_argument,
};
use fln_core::expr::{
    BinderInfo, Expr, ExprData, ExprNode, MAX_LOOSE_BVAR_RANGE, TooManyBoundVars,
};
use fln_core::level::{Level, MAX_LEVEL_DEPTH};
use fln_rt::convert::{Conversion, ConvertError, ExprConstructor, inject_expr};
use fln_rt::native_heap::NativeHeap;

const MAX_EXPR_NODES: usize = 1_000_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Intrinsic {
    Data,
    MkData,
    MkAppData,
    Equal,
    HasLooseBVar,
    LiftLooseBVars,
    Instantiate1,
    Instantiate,
    InstantiateRev,
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
            "extern:Lean.Expr.hasLooseBVar" => Self::HasLooseBVar,
            "extern:Lean.Expr.liftLooseBVars" => Self::LiftLooseBVars,
            "extern:Lean.Expr.instantiate1" => Self::Instantiate1,
            "extern:Lean.Expr.instantiate" => Self::Instantiate,
            "extern:Lean.Expr.instantiateRev" => Self::InstantiateRev,
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
            Self::LiftLooseBVars | Self::Proj => 3,
            Self::Lam | Self::Forall => 4,
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
            Self::Equal => {
                let left = operands.expr(&args[0])?;
                let right = operands.expr(&args[1])?;
                check_equality_pairs(&left, &right, &mut work)?;
                Ok(IntrinsicResult::owned(Obj::mk_nat(usize::from(
                    left == right,
                ))))
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
            Self::Instantiate1 | Self::Instantiate | Self::InstantiateRev => {
                let expr = operands.expr(&args[0])?;
                let mut replacements = if self == Self::Instantiate1 {
                    vec![operands.expr(&args[1])?]
                } else {
                    let (len, _) = args[1]
                        .try_array_view()
                        .ok_or(VmRefusal::InvalidArrayObject)?;
                    if len > work.allowed {
                        return Err(IntrinsicFailure::MirrorResource {
                            resource: "expression substitution entries",
                            allowed: work.allowed as u64,
                            observed: len as u64,
                        });
                    }
                    let mut replacements = Vec::with_capacity(len);
                    for i in 0..len {
                        replacements.push(operands.expr(&args[1].array_child(i))?);
                    }
                    replacements
                };
                // Core subst_loose indexes replacements from the end, as the
                // pin's instantiateRev does. instantiate uses the other order.
                if self == Self::Instantiate {
                    replacements.reverse();
                }
                if !replacements.is_empty() {
                    check_transform(&expr, 0, Some(&replacements), &mut work)?;
                }
                let result = expr.subst_loose(0, &replacements).map_err(bound_vars)?;
                operands.result(&expr, &args[0], result)
            }
        }
    }
}

struct Operands {
    conversion: Conversion,
    heap: NativeHeap,
}

impl Operands {
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
