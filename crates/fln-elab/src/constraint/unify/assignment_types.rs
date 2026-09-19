//! Type constraints produced by native pattern assignment (plan §10.2).
//!
//! A term equation can determine its missing type as well as its value. These
//! are ordinary worklist equations, not typing judgments: every assigned value
//! and every inferred type still passes the parent's K1 validation barrier.
//! Neutral synthesis deliberately leaves argument checking to that barrier.
use super::*;
use fln_core::expr::BinderInfo;

/// Heap continuations keep nested binder synthesis off the Rust call stack.
/// The context is private to this hint; no opened local enters the transaction.
enum TypeFrame {
    Lambda {
        id: FVarId,
        name: Name,
        domain: Expr,
        style: BinderInfo,
        checkpoint: usize,
    },
    PiDomain {
        name: Name,
        domain: Expr,
        body: Expr,
        style: BinderInfo,
    },
    PiBody {
        domain_level: Level,
        checkpoint: usize,
    },
}

impl Engine<'_> {
    pub(super) fn assignment_type_equation(
        &mut self,
        expected: &Expr,
        value: &Expr,
        locals: &LocalContext,
    ) -> Result<Option<Equation>, UnificationError> {
        let expected = self.instantiate(expected)?;
        if !expected.has_expr_mvar() && !expected.has_level_mvar() {
            // Preserve the existing K1 verdict for a closed ill-typed value.
            // Do not make every ordinary assignment pay for type synthesis.
            return Ok(None);
        }
        let inferred = match self.assignment_value_type(value, locals) {
            // An unavailable approximation is not a failed typing judgment.
            // Final assignment checking will retain unresolved obligations.
            Err(UnificationError::Deferred(_)) => None,
            result => result?,
        };
        let Some(inferred) = inferred else {
            return Ok(None);
        };
        self.scan(&inferred)?;
        if same_terms(&expected, &inferred, &mut self.meter)? {
            return Ok(None);
        }
        for _ in locals.decls() {
            self.meter.node()?;
        }
        Ok(Some((expected, inferred, locals.clone())))
    }

    /// Infer a necessary type for lambdas, dependent Pis and reducible terms.
    /// This is NOT a typing judgment: neutral application hints do not validate
    /// arguments, and zeta/beta hints may discard subterms. The original assigned
    /// value and the inferred type still pass the ordinary K1 barrier together.
    /// No new declaration, local-context mutation or hole assignment occurs here.
    fn assignment_value_type(
        &mut self,
        value: &Expr,
        locals: &LocalContext,
    ) -> Result<Option<Expr>, UnificationError> {
        for _ in locals.decls() {
            self.meter.node()?;
        }
        let mut context = locals.clone();
        let mut current = value.clone();
        let mut frames = Vec::new();
        'infer: loop {
            self.meter.node()?;
            current = self.instantiate(&current)?;
            current = self.whnf(&current, &context)?;
            let mut inferred = match current.node() {
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    binder_info,
                    body,
                } => {
                    let id = self.fresh()?;
                    let domain = self.instantiate(binder_type)?;
                    let opened = self.substitute(body, &Expr::fvar(id.clone()))?;
                    let checkpoint = context.len();
                    context.add_param(
                        id.clone(),
                        binder_name.clone(),
                        domain.clone(),
                        *binder_info,
                    );
                    frames.push(TypeFrame::Lambda {
                        id,
                        name: binder_name.clone(),
                        domain,
                        style: *binder_info,
                        checkpoint,
                    });
                    current = opened;
                    continue 'infer;
                }
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    binder_info,
                    body,
                } => {
                    frames.push(TypeFrame::PiDomain {
                        name: binder_name.clone(),
                        domain: binder_type.clone(),
                        body: body.clone(),
                        style: *binder_info,
                    });
                    current = binder_type.clone();
                    continue 'infer;
                }
                ExprNode::Sort { level } => Expr::sort(
                    Level::succ(level.clone()).map_err(|_| UnificationError::ExpressionScope)?,
                ),
                ExprNode::Lit {
                    literal: Literal::Nat(_),
                } => Expr::const_(Name::from_components(["Nat"]), Vec::new()),
                _ => {
                    let Some(type_) = self.eta_neutral_type(&current, &context)? else {
                        return Ok(None);
                    };
                    type_
                }
            };
            while let Some(frame) = frames.pop() {
                self.meter.node()?;
                match frame {
                    TypeFrame::Lambda {
                        id,
                        name,
                        domain,
                        style,
                        checkpoint,
                    } => {
                        self.scan(&inferred)?;
                        inferred = inferred
                            .abstract_fvar(&id, 0)
                            .map_err(|_| UnificationError::ExpressionScope)?;
                        inferred = Expr::forall_e(name, domain, inferred, style);
                        context.truncate(checkpoint);
                    }
                    TypeFrame::PiDomain {
                        name,
                        domain,
                        body,
                        style,
                    } => {
                        inferred = self.whnf(&inferred, &context)?;
                        let ExprNode::Sort { level } = inferred.node() else {
                            return Ok(None);
                        };
                        let id = self.fresh()?;
                        let opened = self.substitute(&body, &Expr::fvar(id.clone()))?;
                        let checkpoint = context.len();
                        context.add_param(id, name, domain, style);
                        frames.push(TypeFrame::PiBody {
                            domain_level: level.clone(),
                            checkpoint,
                        });
                        current = opened;
                        continue 'infer;
                    }
                    TypeFrame::PiBody {
                        domain_level,
                        checkpoint,
                    } => {
                        inferred = self.whnf(&inferred, &context)?;
                        let ExprNode::Sort { level } = inferred.node() else {
                            return Ok(None);
                        };
                        // Pi is impredicative in Prop: use imax, not max and
                        // never default an unknown codomain universe to zero.
                        let level = Level::imax(domain_level, level.clone())
                            .map_err(|_| UnificationError::ExpressionScope)?;
                        inferred = Expr::sort(simplify_level(&level, &mut self.meter)?);
                        context.truncate(checkpoint);
                    }
                }
            }
            self.scan(&inferred)?;
            return Ok(Some(inferred));
        }
    }
}
