//! The supported fragment of the pin's NormalizePattern, run at registration.
//! Once stored, patterns are never reselected or normalized in a later world.
use super::*;
use crate::grind_patterns::CapturedPatterns;
use std::collections::HashSet;

const MAX_DEPTH: usize = 128;

#[derive(Clone, Copy, PartialEq, Eq)]
enum ArgKind {
    Relevant,
    TypeFormer,
    Instance,
    Proof,
    OutParameter,
}
impl ArgKind {
    fn support(self) -> bool {
        self != Self::Relevant
    }
}

#[derive(Default)]
struct Capture {
    found: HashSet<u32>,
    symbols: Vec<Name>,
    symbol_set: HashSet<Name>,
}
impl Capture {
    fn symbol(&mut self, name: &Name) -> Result<(), NatDefinitionElabError> {
        if self.symbol_set.insert(name.clone()) {
            if self.symbols.len() >= registry::MAX_SYMBOLS {
                return Err(failure(SourceInferenceError::ResourceLimit));
            }
            self.symbols.push(name.clone());
        }
        Ok(())
    }
}

fn dependencies(
    context: &mut Context,
    expression: &Expr,
    locals: &[FVarId],
    forward: &mut [bool],
) -> Result<(), NatDefinitionElabError> {
    let mut pending = vec![expression];
    let mut seen = HashSet::new();
    while let Some(term) = pending.pop() {
        context.tick()?;
        if !term.has_fvar() || !seen.insert(term.allocation_identity()) {
            continue;
        }
        match term.node() {
            ExprNode::FVar { id } => {
                if let Some(index) = locals.iter().position(|local| local == id) {
                    forward[index] = true;
                }
            }
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

impl Context {
    pub(super) fn capture_grind_patterns(
        &mut self,
        patterns: &[Expr],
    ) -> Result<CapturedPatterns, NatDefinitionElabError> {
        let mut capture = Capture::default();
        let mut normalized = Vec::with_capacity(patterns.len());
        for pattern in patterns {
            normalized.push(self.capture_grind_pattern(pattern, false, &mut capture, 0)?);
        }
        Ok(CapturedPatterns {
            patterns: normalized,
            symbols: capture.symbols,
        })
    }

    /// Open a bounded type telescope only for classifying a formal argument.
    /// The temporary locals never escape the query.
    fn grind_type_tail(
        &mut self,
        type_: &Expr,
        transparency: UnificationTransparency,
    ) -> Result<Expr, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let mut cursor = type_.clone();
            for _ in 0..MAX_DEPTH {
                self.tick()?;
                cursor = self.whnf_with_transparency(&cursor, transparency, true)?;
                let ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } = cursor.node()
                else {
                    return Ok(cursor);
                };
                let id = FVarId(self.fresh_name()?);
                self.txn.lctx.add_param(
                    id.clone(),
                    binder_name.clone(),
                    binder_type.clone(),
                    *binder_info,
                );
                cursor = self.substitute(body, &Expr::fvar(id))?;
            }
            Err(failure(SourceInferenceError::ResourceLimit))
        })();
        self.txn.lctx = saved;
        result
    }

    /// getPatternArgKinds uses the function's formal telescope, not the actual
    /// arguments. Forward dependencies include later domains and the result.
    fn grind_pattern_arg_kinds(
        &mut self,
        head: &Expr,
        num_args: usize,
    ) -> Result<Vec<ArgKind>, NatDefinitionElabError> {
        if num_args > MAX_DEPTH {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let Some(mut cursor) = self.known_type(head)? else {
                return Err(unsupported("a pattern head with unknown type"));
            };
            let mut locals = Vec::new();
            let mut domains = Vec::new();
            let mut styles = Vec::new();
            for _ in 0..num_args {
                self.tick()?;
                // forallBoundedTelescope leaves the residual type unreduced
                // when the requested number of parameters has been reached.
                if !matches!(cursor.node(), ExprNode::ForallE { .. }) {
                    cursor = self.whnf(&cursor)?;
                }
                let ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } = cursor.node()
                else {
                    break;
                };
                let id = FVarId(self.fresh_name()?);
                self.txn.lctx.add_param(
                    id.clone(),
                    binder_name.clone(),
                    binder_type.clone(),
                    *binder_info,
                );
                domains.push(binder_type.clone());
                styles.push(*binder_info);
                cursor = self.substitute(body, &Expr::fvar(id.clone()))?;
                locals.push(id);
            }
            let mut forward = vec![false; locals.len()];
            for domain in &domains {
                dependencies(self, domain, &locals, &mut forward)?;
            }
            dependencies(self, &cursor, &locals, &mut forward)?;
            let mut kinds = Vec::with_capacity(locals.len());
            for (index, domain) in domains.iter().enumerate() {
                self.tick()?;
                let reduced = self.whnf(domain)?;
                let kind = if matches!(reduced.node(), ExprNode::Sort { level }
                    if level.normalize_fixpoint().is_zero())
                {
                    ArgKind::Relevant
                } else if proposition(self, domain)? {
                    ArgKind::Proof
                } else if matches!(
                    self.grind_type_tail(domain, UnificationTransparency::Default)?
                        .node(),
                    ExprNode::Sort { .. }
                ) {
                    if forward[index] {
                        ArgKind::TypeFormer
                    } else {
                        ArgKind::Relevant
                    }
                } else if styles[index] == BinderInfo::InstImplicit {
                    ArgKind::Instance
                } else {
                    let tail =
                        self.grind_type_tail(domain, UnificationTransparency::Abbreviations)?;
                    let mut class_head = &tail;
                    while let ExprNode::App { f, .. } = class_head.node() {
                        self.tick()?;
                        class_head = f;
                    }
                    let is_class = matches!(class_head.node(), ExprNode::Const { name, .. }
                        if self.instance_registry()?.is_class(name));
                    if is_class {
                        ArgKind::Instance
                    } else {
                        let mut domain_head = domain;
                        while let ExprNode::App { f, .. } = domain_head.node() {
                            self.tick()?;
                            domain_head = f;
                        }
                        if matches!(domain_head.node(), ExprNode::Const { name, .. }
                            if *name == Name::from_components(["outParam"]))
                        {
                            ArgKind::OutParameter
                        } else {
                            ArgKind::Relevant
                        }
                    }
                };
                kinds.push(kind);
            }
            Ok(kinds)
        })();
        self.txn.lctx = saved;
        result
    }

    fn grind_ground_symbols(
        &mut self,
        expression: &Expr,
        capture: &mut Capture,
    ) -> Result<(), NatDefinitionElabError> {
        let mut pending = vec![expression];
        let mut seen = HashSet::new();
        while let Some(term) = pending.pop() {
            self.tick()?;
            if !seen.insert(term.allocation_identity()) {
                continue;
            }
            let mut head = term;
            while let ExprNode::App { f, .. } = head.node() {
                self.tick()?;
                head = f;
            }
            if let ExprNode::Const { name, .. } = head.node()
                && [
                    "OfNat.ofNat",
                    "Lean.Grind.nestedProof",
                    "Lean.Grind.eqBwdPattern",
                    "Lean.Grind.nestedDecidable",
                    "ite",
                ]
                .iter()
                .any(|n| *name == Name::from_components(n.split('.')))
            {
                continue;
            }
            match term.node() {
                ExprNode::Const { name, .. } => capture.symbol(name)?,
                ExprNode::App { f, a } => pending.extend([a, f]),
                ExprNode::MData { expr, .. } => pending.push(expr),
                ExprNode::Sort { .. } | ExprNode::Lit { .. } => {}
                _ => return Err(unsupported("a non-first-order ground pattern")),
            }
        }
        Ok(())
    }

    fn capture_grind_pattern(
        &mut self,
        expression: &Expr,
        in_support: bool,
        capture: &mut Capture,
        depth: usize,
    ) -> Result<Expr, NatDefinitionElabError> {
        self.tick()?;
        if depth >= MAX_DEPTH {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        if in_support {
            return Err(unsupported(
                "a compound support argument requiring wildcard preprocessing",
            ));
        }
        let mut head = expression;
        let mut arguments = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            arguments.push(a);
            head = f;
        }
        arguments.reverse();
        let ExprNode::Const { name, .. } = head.node() else {
            return Err(unsupported("a captured pattern without a constant head"));
        };
        if !registry::supported_head(name) {
            return Err(unsupported("an interpreted captured pattern or gadget"));
        }
        capture.symbol(name)?;
        let kinds = self.grind_pattern_arg_kinds(head, arguments.len())?;
        let mut result = head.clone();
        for (index, argument) in arguments.into_iter().enumerate() {
            self.tick()?;
            let kind = kinds.get(index).copied().unwrap_or(ArgKind::Relevant);
            let support = in_support || kind.support();
            let argument = if !argument.has_loose_bvars() {
                if argument.has_fvar() || argument.has_expr_mvar() || argument.has_level_mvar() {
                    return Err(unsupported("an unresolved ground pattern"));
                }
                let Some(type_) = self.known_type(argument)? else {
                    return Err(unsupported("a ground pattern with unknown type"));
                };
                if proposition(self, &type_)? {
                    return Err(unsupported(
                        "a proof argument requiring wildcard preprocessing",
                    ));
                }
                if !support {
                    self.grind_ground_symbols(argument, capture)?;
                }
                registry::mark_ground(argument.clone())
            } else if let ExprNode::BVar { idx } = argument.node() {
                if support && capture.found.contains(idx) {
                    registry::wildcard()
                } else {
                    capture.found.insert(*idx);
                    argument.clone()
                }
            } else {
                self.capture_grind_pattern(argument, support, capture, depth + 1)?
            };
            result = Expr::app(result, argument);
        }
        Ok(result)
    }
}
