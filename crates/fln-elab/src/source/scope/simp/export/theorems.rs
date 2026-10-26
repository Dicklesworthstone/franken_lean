//! Persistent equality rules use the admitted declaration, not a synthesized
//! proof or a guessed discrimination path. Other propositions and reversed
//! rules require the pin's auxiliary-lemma elaboration before artifact capture.
use super::{Meter, SimpSetError, Theorem, keys};
use crate::lctx::LocalContext;
use fln_core::expr::{Expr, ExprNode, FVarId, Literal};
use fln_core::name::Name;
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use fln_env::environment::Environment;
use std::collections::{HashMap, HashSet};

fn unsupported() -> SimpSetError {
    SimpSetError::UnsupportedDeclaration(Name::anonymous())
}

/// Charge a substitution's whole input DAG before constructing any successor.
fn scan(expr: &Expr, meter: &mut Meter) -> Result<(), SimpSetError> {
    let mut pending = vec![expr];
    let mut seen = HashSet::new();
    while let Some(expr) = pending.pop() {
        meter.work(1)?;
        if !seen.insert(expr.allocation_identity()) {
            continue;
        }
        match expr.node() {
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    Ok(())
}

fn derive_inner(
    env: &Environment,
    row: &super::super::SimpEntry,
    meter: &mut Meter,
) -> Result<Theorem, SimpSetError> {
    // The pin creates and admits `_simp` auxiliary declarations for these
    // cases. An artifact projection cannot manufacture that missing authority.
    if row.reverse || row.proof.is_some() {
        return Err(unsupported());
    }
    let info = env
        .find(&row.declaration)
        .ok_or_else(|| SimpSetError::UnknownDeclaration(row.declaration.clone()))?;
    match info {
        ConstantInfo::Thm(_) => {}
        ConstantInfo::Axiom(value) if !value.is_unsafe => {}
        ConstantInfo::Defn(value) if value.safety == DefinitionSafety::Safe => {}
        _ => return Err(unsupported()),
    }
    let mut ty = info.constant_val().type_.clone();
    if ty.has_fvar() || ty.has_expr_mvar() || ty.has_level_mvar() || ty.has_loose_bvars() {
        return Err(SimpSetError::Malformed);
    }
    let mut locals = LocalContext::new();
    loop {
        meter.work(1)?;
        ty = keys::reduce_type(env, &ty, &locals, meter)?;
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = ty.node()
        else {
            break;
        };
        let index = u64::try_from(locals.len()).map_err(|_| SimpSetError::Limit)?;
        let variable = FVarId(Name::num(
            Name::from_components(["_fln_simp_export"]),
            index,
        ));
        meter.bytes(std::mem::size_of::<crate::lctx::LocalDecl>())?;
        locals.add_param(
            variable.clone(),
            binder_name.clone(),
            binder_type.clone(),
            *binder_info,
        );
        scan(body, meter)?;
        ty = body
            .subst_loose(0, &[Expr::fvar(variable)])
            .map_err(|_| SimpSetError::Limit)?;
    }
    let mut args = Vec::new();
    let mut head = &ty;
    loop {
        meter.work(1)?;
        match head.node() {
            ExprNode::App { f, a } => {
                args.push(a);
                head = f;
            }
            ExprNode::MData { expr, .. } => head = expr,
            _ => break,
        }
    }
    if args.len() != 3
        || !matches!(head.node(), ExprNode::Const { name, levels }
            if *name == Name::from_components(["Eq"]) && levels.len() == 1)
    {
        return Err(unsupported());
    }
    // The application was peeled from the outside: rhs, lhs, then its type.
    let lhs = args[1];
    let rhs = args[0];
    let checked_lhs = keys::reduce_lhs_for_check(env, lhs, &locals, meter)?;
    if matches!(checked_lhs.node(), ExprNode::FVar { .. }) && &checked_lhs == rhs {
        return Err(unsupported());
    }
    let keys = keys::keys(env, lhs, &locals, meter)?;
    let permutation = Permutation {
        locals: &locals,
        representatives: HashMap::new(),
        meter,
    }
    .compare(lhs, rhs, true)?;
    let tagged = super::super::defeq::read(env, || {
        meter.work(1).map_err(|error| {
            crate::NatDefinitionElabError::Inference(crate::source::SourceInferenceError::SimpSet(
                error,
            ))
        })
    })
    .map_err(|error| match error {
        crate::NatDefinitionElabError::Inference(crate::source::SourceInferenceError::SimpSet(
            error,
        )) => error,
        _ => SimpSetError::Malformed,
    })?;
    let reflexive = tagged.contains(&row.declaration);
    let backward = super::super::defeq::read_backward(env, || {
        meter.work(1).map_err(|error| {
            crate::NatDefinitionElabError::Inference(crate::source::SourceInferenceError::SimpSet(
                error,
            ))
        })
    })
    .map_err(|error| match error {
        crate::NatDefinitionElabError::Inference(crate::source::SourceInferenceError::SimpSet(
            error,
        )) => error,
        _ => SimpSetError::Malformed,
    })?;
    Ok(Theorem {
        // SimpTheorem.getValue instantiates a global constant's universes from
        // its declaration; storing them here would change that convention.
        proof: Expr::const_(row.declaration.clone(), Vec::new()),
        level_params: Vec::new(),
        origin: row.declaration.clone(),
        origin_reverse: false,
        priority: row.priority,
        post: true,
        permutation,
        reflexive,
        // Generated equation proofs may be reflexive only under default/all
        // transparency. Retain that independent tag rather than promoting it
        // to the stricter dsimp selection merely because the proof is rfl.
        backward_reflexive: backward.contains(&row.declaration),
        keys,
    })
}

pub(super) fn derive(
    env: &Environment,
    row: &super::super::SimpEntry,
    meter: &mut Meter,
) -> Result<Theorem, SimpSetError> {
    derive_inner(env, row, meter).map_err(|error| match error {
        SimpSetError::UnsupportedDeclaration(_) => {
            SimpSetError::UnsupportedDeclaration(row.declaration.clone())
        }
        other => other,
    })
}

/// The pin compares expression shapes, unifying telescope metavariables only
/// when both positions are metavariables. Equality classes preserve repeated
/// variables across the whole traversal. Type comparisons that require more
/// than this exact structural model are a nonanswer, never a guessed flag.
struct Permutation<'a> {
    locals: &'a LocalContext,
    representatives: HashMap<FVarId, FVarId>,
    meter: &'a mut Meter,
}

impl Permutation<'_> {
    fn representative(&mut self, variable: &FVarId) -> Result<FVarId, SimpSetError> {
        let mut current = variable;
        while let Some(next) = self.representatives.get(current) {
            self.meter.work(1)?;
            current = next;
        }
        Ok(current.clone())
    }

    fn compare(&mut self, lhs: &Expr, rhs: &Expr, assign: bool) -> Result<bool, SimpSetError> {
        let mut pending = vec![(lhs.clone(), rhs.clone())];
        while let Some((lhs, rhs)) = pending.pop() {
            self.meter.work(1)?;
            match (lhs.node(), rhs.node()) {
                (ExprNode::MData { expr, .. }, _) => pending.push((expr.clone(), rhs)),
                (_, ExprNode::MData { expr, .. }) => pending.push((lhs, expr.clone())),
                (ExprNode::App { f: a, a: b }, ExprNode::App { f: c, a: d }) => {
                    pending.extend([(b.clone(), d.clone()), (a.clone(), c.clone())]);
                }
                (ExprNode::FVar { id: a }, ExprNode::FVar { id: b }) => {
                    let a = self.representative(a)?;
                    let b = self.representative(b)?;
                    if a == b {
                        continue;
                    }
                    if !assign {
                        return Ok(false);
                    }
                    self.meter.work(self.locals.len().saturating_mul(2))?;
                    let a_type = self.locals.find(&a).ok_or_else(unsupported)?.type_.clone();
                    let b_type = self.locals.find(&b).ok_or_else(unsupported)?.type_.clone();
                    if !self.compare(&a_type, &b_type, false)? {
                        return Err(unsupported());
                    }
                    self.representatives.insert(a, b);
                }
                (
                    ExprNode::ForallE {
                        binder_type: a,
                        body: b,
                        ..
                    },
                    ExprNode::ForallE {
                        binder_type: c,
                        body: d,
                        ..
                    },
                )
                | (
                    ExprNode::Lam {
                        binder_type: a,
                        body: b,
                        ..
                    },
                    ExprNode::Lam {
                        binder_type: c,
                        body: d,
                        ..
                    },
                ) => pending.extend([(b.clone(), d.clone()), (a.clone(), c.clone())]),
                (
                    ExprNode::LetE {
                        type_: a,
                        value: b,
                        body: c,
                        ..
                    },
                    ExprNode::LetE {
                        type_: d,
                        value: e,
                        body: f,
                        ..
                    },
                ) => pending.extend([
                    (c.clone(), f.clone()),
                    (b.clone(), e.clone()),
                    (a.clone(), d.clone()),
                ]),
                (
                    ExprNode::Proj {
                        idx: a, expr: b, ..
                    },
                    ExprNode::Proj {
                        idx: c, expr: d, ..
                    },
                ) if a == c => pending.push((b.clone(), d.clone())),
                (ExprNode::BVar { idx: a }, ExprNode::BVar { idx: b }) if a == b => {}
                (ExprNode::Sort { level: a }, ExprNode::Sort { level: b }) if a == b => {}
                (
                    ExprNode::Const { name: a, levels: b },
                    ExprNode::Const { name: c, levels: d },
                ) => {
                    self.meter.work(b.len().saturating_add(d.len()))?;
                    if a != c || b != d {
                        return Ok(false);
                    }
                }
                (ExprNode::Lit { literal: a }, ExprNode::Lit { literal: b }) => {
                    let payload_work = |literal: &Literal| match literal {
                        Literal::Nat(value) => value.limbs_le().len(),
                        Literal::Str(value) => value.len(),
                    };
                    self.meter
                        .work(payload_work(a).saturating_add(payload_work(b)))?;
                    if a != b {
                        return Ok(false);
                    }
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::BinderInfo;
    use fln_core::level::Level;

    fn n(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    fn local(context: &mut LocalContext, name: &str, ty: Expr) -> Expr {
        let id = FVarId(n(name));
        context.add_param(id.clone(), n(name), ty, BinderInfo::Default);
        Expr::fvar(id)
    }

    fn call(name: &str, args: &[Expr]) -> Expr {
        args.iter().fold(Expr::const_(n(name), vec![]), |f, a| {
            Expr::app(f, a.clone())
        })
    }

    fn compare(
        locals: &LocalContext,
        lhs: &Expr,
        rhs: &Expr,
        work: usize,
    ) -> Result<bool, SimpSetError> {
        Permutation {
            locals,
            representatives: HashMap::new(),
            meter: &mut Meter {
                remaining: work,
                bytes: 0,
            },
        }
        .compare(lhs, rhs, true)
    }

    #[test]
    fn permutation_preserves_shapes_and_shared_telescope_assignments() {
        let mut locals = LocalContext::new();
        let ty = Expr::const_(n("T"), vec![]);
        let x = local(&mut locals, "x", ty.clone());
        let y = local(&mut locals, "y", ty.clone());
        let z = local(&mut locals, "z", ty);
        assert_eq!(
            compare(
                &locals,
                &call("f", &[x.clone(), y.clone()]),
                &call("f", &[y.clone(), x.clone()]),
                1000
            ),
            Ok(true)
        );
        // isPerm uses shared unification, not a bijective renaming: both
        // fresh variables can be assigned to the same variable here.
        assert_eq!(
            compare(
                &locals,
                &call("f", &[x.clone(), x.clone()]),
                &call("f", &[y.clone(), z]),
                1000
            ),
            Ok(true)
        );
        assert_eq!(
            compare(&locals, &call("f", &[x]), &call("g", &[y]), 1000),
            Ok(false)
        );
    }

    #[test]
    fn permutation_types_see_prior_assignments_without_guessing_conversion() {
        let mut locals = LocalContext::new();
        let a = local(&mut locals, "A", Expr::sort(Level::one()));
        let b = local(&mut locals, "B", Expr::sort(Level::one()));
        let x = local(&mut locals, "x", a.clone());
        let y = local(&mut locals, "y", b.clone());
        assert_eq!(
            compare(
                &locals,
                &call("f", &[a, x.clone()]),
                &call("f", &[b, y.clone()]),
                1000
            ),
            Ok(true)
        );
        assert!(matches!(
            compare(&locals, &call("f", &[x]), &call("f", &[y]), 1000),
            Err(SimpSetError::UnsupportedDeclaration(_))
        ));
    }

    #[test]
    fn permutation_ignores_annotations_but_never_conflates_resource_exhaustion() {
        let mut locals = LocalContext::new();
        let x = local(&mut locals, "x", Expr::sort(Level::one()));
        let annotated = Expr::mdata(fln_core::options::KVMap::new(), x.clone());
        assert_eq!(compare(&locals, &annotated, &x, 100), Ok(true));
        assert_eq!(
            compare(&locals, &annotated, &x, 0),
            Err(SimpSetError::Limit)
        );
    }

    #[test]
    fn permutation_charges_literal_payloads_before_comparing_them() {
        let locals = LocalContext::new();
        let lhs = Expr::lit(Literal::Str("a".repeat(4096)));
        let rhs = Expr::lit(Literal::Str("a".repeat(4096)));
        assert_eq!(compare(&locals, &lhs, &rhs, 16), Err(SimpSetError::Limit));
        assert_eq!(compare(&locals, &lhs, &rhs, 8193), Ok(true));
    }
}
