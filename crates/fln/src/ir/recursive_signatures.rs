//! The source ABI of a checked recursive companion, before boxing.
//!
//! The pin's ReduceArity ignores a self-call argument only when it is still the
//! corresponding original parameter. ConstantFold runs first: `x + 0` is such
//! a parameter, while `x + 1` is not; `x * 0` no longer reads x at all. Keep a
//! small, normalized expression DAG for these primitive bodies and collect the
//! same uses. This is metadata analysis, never evaluation of a recursive body.
//! Unknown calls, dependent carriers and ambiguous effectful simplifications
//! refuse instead of inventing a reduced calling convention.

use super::*;
use fln_core::expr::{Expr, ExprNode, Literal, NatLit};
use fln_env::constants::{ConstantInfo, DefinitionSafety, DefinitionVal};

struct Analysis<'a, 'b> {
    checks: SourceUses<'a, 'b>,
    companion: &'a Name,
    logical: &'a Name,
    boolean_facts: Vec<(Expr, Expr)>,
    nat_decisions: [bool; 2],
}

fn named(expression: &Expr, label: &str) -> bool {
    matches!(expression.node(), ExprNode::Const { name, levels }
        if levels.is_empty() && name == &Name::from_components(label.split('.')))
}

fn primitive(name: &Name) -> Option<&'static str> {
    [
        "Nat.add",
        "Nat.sub",
        "Nat.mul",
        "Nat.beq",
        "Nat.ble",
        "String.append",
    ]
    .into_iter()
    .find(|label| name == &Name::from_components(label.split('.')))
}

fn natural(value: &Expr) -> Option<&NatLit> {
    match value.node() {
        ExprNode::Lit {
            literal: Literal::Nat(n),
        } => Some(n),
        _ => None,
    }
}

fn text(value: &Expr) -> Option<&str> {
    match value.node() {
        ExprNode::Lit {
            literal: Literal::Str(s),
        } => Some(s),
        _ => None,
    }
}

impl Analysis<'_, '_> {
    fn enum_constructor(&mut self, expression: &Expr) -> Result<bool> {
        let ExprNode::Const { name, levels } = expression.node() else {
            return Ok(false);
        };
        if !levels.is_empty() {
            return Ok(false);
        }
        self.checks.meter.charge(1)?;
        let Some(ConstantInfo::Ctor(constructor)) = self.checks.environment.find(name) else {
            return Ok(false);
        };
        // A constructor literal has no source-slot uses only after its entire
        // family passes the same fieldless layout checks as the exported type.
        if source_enum_constructors(
            &constructor.induct,
            self.checks.environment,
            self.checks.meter,
        )?
        .is_none()
        {
            return Ok(false);
        }
        self.checks.meter.charge(1)?;
        let Some(ConstantInfo::Induct(family)) = self.checks.environment.find(&constructor.induct)
        else {
            return Ok(false);
        };
        if family.ctors.get(constructor.cidx as usize) != Some(name) {
            return Err(unsupported("recursive source enum constructor"));
        }
        self.checks.metadata()?;
        if self.checks.externs.as_ref().unwrap().get(name).is_some()
            || self
                .checks
                .replacements
                .as_ref()
                .unwrap()
                .get(name)
                .is_some()
        {
            return Err(unsupported("recursive source enum constructor replacement"));
        }
        Ok(true)
    }

    fn spine(&mut self, expression: &Expr) -> Result<(Expr, Vec<Expr>)> {
        let mut head = expression;
        let mut arguments = Vec::new();
        loop {
            self.checks.meter.charge(1)?;
            head = source_without_metadata(head, self.checks.meter)?;
            let ExprNode::App { f, a } = head.node() else {
                break;
            };
            arguments
                .try_reserve(1)
                .map_err(|_| CompileError::Allocation)?;
            arguments.push(a.clone());
            head = f;
        }
        arguments.reverse();
        Ok((head.clone(), arguments))
    }

    /// Open only the usual scalar dictionaries, using their admitted bodies.
    /// Parameters in their types are irrelevant to this analysis, but actual
    /// argument substitution and constructor-field selection remain exact.
    fn normalize_head(&mut self, mut expression: Expr, depth: usize) -> Result<Expr> {
        if depth >= 128 {
            return Err(CompileError::Limit);
        }
        loop {
            let (head, mut arguments) = self.spine(&expression)?;
            let next = match head.node() {
                ExprNode::Const { name, .. }
                    if name == self.companion
                        || name == self.logical
                        || primitive(name).is_some()
                        || matches!(
                            self.checks.environment.find(name),
                            Some(ConstantInfo::Ctor(_))
                        ) =>
                {
                    return Ok(expression);
                }
                ExprNode::Const { name, levels }
                    if SourceUses::dictionary_name(name)
                        || [
                            "HSub.hSub",
                            "Sub.sub",
                            "instHSub",
                            "instSubNat",
                            "HMul.hMul",
                            "Mul.mul",
                            "instHMul",
                            "instMulNat",
                            "BEq.beq",
                            "instBEqOfDecidableEq",
                            "instDecidableEqNat",
                            "OfNat.ofNat",
                            "instOfNatNat",
                        ]
                        .iter()
                        .any(|label| name == &Name::from_components(label.split('.'))) =>
                {
                    self.checks.metadata()?;
                    if self.checks.externs.as_ref().unwrap().get(name).is_some()
                        || self
                            .checks
                            .replacements
                            .as_ref()
                            .unwrap()
                            .get(name)
                            .is_some()
                    {
                        return Err(unsupported("recursive source dictionary replacement"));
                    }
                    let Some(ConstantInfo::Defn(definition)) = self.checks.environment.find(name)
                    else {
                        return Err(unsupported("recursive source dictionary definition"));
                    };
                    if definition.safety != DefinitionSafety::Safe
                        || definition.base.level_params.len() != levels.len()
                        || self
                            .checks
                            .environment
                            .contains(&Name::str(name.clone(), "_unsafe_rec"))
                    {
                        return Err(unsupported("recursive source dictionary definition"));
                    }
                    self.checks.expression_work(&definition.value)?;
                    definition.value.clone()
                }
                ExprNode::Lam { body, .. } if !arguments.is_empty() => {
                    self.checks.expression_work(body)?;
                    let argument = arguments.remove(0);
                    body.subst_loose(0, &[argument])
                        .map_err(|_| CompileError::Limit)?
                }
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => {
                    let constructor = self.normalize_head(expr.clone(), depth + 1)?;
                    let (head, fields) = self.spine(&constructor)?;
                    let ExprNode::Const { name, .. } = head.node() else {
                        return Err(unsupported("recursive source dictionary constructor"));
                    };
                    self.checks.metadata()?;
                    let Some(ConstantInfo::Ctor(info)) = self.checks.environment.find(name) else {
                        return Err(unsupported("recursive source dictionary constructor"));
                    };
                    if self.checks.externs.as_ref().unwrap().get(name).is_some()
                        || self
                            .checks
                            .replacements
                            .as_ref()
                            .unwrap()
                            .get(name)
                            .is_some()
                        || &info.induct != struct_name
                        || *idx >= u64::from(info.num_fields)
                        || fields.len() as u64
                            != u64::from(info.num_params) + u64::from(info.num_fields)
                    {
                        return Err(unsupported("recursive source dictionary projection"));
                    }
                    fields[(u64::from(info.num_params) + idx) as usize].clone()
                }
                _ => return Ok(expression),
            };
            expression = arguments.into_iter().fold(next, Expr::app);
        }
    }

    fn has_call(&mut self, value: &Expr) -> Result<bool> {
        let mut pending = vec![value];
        let mut seen = std::collections::HashSet::new();
        while let Some(value) = pending.pop() {
            self.checks.meter.charge(1)?;
            if !seen.insert(value.clone()) {
                continue;
            }
            match value.node() {
                ExprNode::Const { name, .. } if name == self.companion => return Ok(true),
                ExprNode::App { f, a } => pending.extend([f, a]),
                _ => {}
            }
        }
        Ok(false)
    }

    fn discard(&mut self, value: &Expr) -> Result<()> {
        if self.has_call(value)? {
            return Err(unsupported("recursive source effectful simplification"));
        }
        Ok(())
    }

    fn is_case(&mut self, value: &Expr) -> Result<bool> {
        let (head, _) = self.spine(value)?;
        Ok(named(&head, "_fln_recursive_source_case"))
    }

    fn equality(
        &mut self,
        head: &Expr,
        arguments: &[Expr],
        locals: &mut Vec<Expr>,
        depth: usize,
    ) -> Result<Expr> {
        let pinned = named(head, "Decidable.decide");
        let [_, decision] = arguments else {
            return Err(unsupported("recursive source decision arity"));
        };
        let decision = self.normalize_head(decision.clone(), depth + 1)?;
        let (callee, arguments) = self.spine(&decision)?;
        if !named(&callee, "Nat.decEq") {
            return Err(unsupported("recursive source decision operation"));
        }
        let [left, right] = arguments.as_slice() else {
            return Err(unsupported("recursive source natural decision arity"));
        };
        if !self.nat_decisions[usize::from(pinned)] {
            self.checks.metadata()?;
            for expression in [head, &callee] {
                let ExprNode::Const { name, .. } = expression.node() else {
                    return Err(invariant("source decision constant"));
                };
                if self
                    .checks
                    .replacements
                    .as_ref()
                    .unwrap()
                    .get(name)
                    .is_some()
                    || !pinned && self.checks.externs.as_ref().unwrap().get(name).is_some()
                {
                    return Err(unsupported("recursive source decision replacement"));
                }
            }
            let mut limits = self.checks.ingress;
            limits.max_nodes = limits
                .max_nodes
                .min(usize::try_from(self.checks.meter.0).unwrap_or(usize::MAX));
            let (checked, work) = crate::runtime::source_nat_equality_contract(
                self.checks.environment,
                pinned,
                limits,
            );
            self.checks.meter.charge(work)?;
            checked.map_err(SourceUses::ingress_error)?;
            self.nat_decisions[usize::from(pinned)] = true;
        }
        self.checks.native(&Name::from_components(["Nat", "beq"]))?;
        let left = self.value(left, locals, depth + 1)?;
        let right = self.value(right, locals, depth + 1)?;
        if self.is_case(&left)? || self.is_case(&right)? {
            return Err(unsupported(
                "recursive source conditional primitive argument",
            ));
        }
        self.binary("Nat.beq", left, right)
    }

    fn binary(&mut self, operation: &'static str, left: Expr, right: Expr) -> Result<Expr> {
        let a = natural(&left);
        let b = natural(&right);
        let is =
            |number: Option<&NatLit>, expected| number.and_then(NatLit::to_u64) == Some(expected);
        match operation {
            "Nat.add" if is(a, 0) => return Ok(right),
            "Nat.add" | "Nat.sub" if is(b, 0) => return Ok(left),
            "Nat.mul" if is(a, 1) => return Ok(right),
            "Nat.mul" if is(b, 1) => return Ok(left),
            "Nat.sub" | "Nat.mul" if is(a, 0) => {
                self.discard(&right)?;
                return Ok(left);
            }
            "Nat.mul" if is(b, 0) => {
                self.discard(&left)?;
                return Ok(right);
            }
            "String.append" => match (text(&left), text(&right)) {
                (Some(""), _) => return Ok(right),
                (_, Some("")) => return Ok(left),
                (Some(a), Some(b)) => {
                    self.checks.meter.charge(a.len().saturating_add(b.len()))?;
                    let mut joined = String::new();
                    joined
                        .try_reserve(a.len().saturating_add(b.len()))
                        .map_err(|_| CompileError::Allocation)?;
                    joined.push_str(a);
                    joined.push_str(b);
                    return Ok(Expr::lit(Literal::Str(joined)));
                }
                _ => {}
            },
            _ => {}
        }
        if let (Some(a), Some(b)) = (a, b) {
            // The pin folds Nat.decEq/decLe, but not direct Nat.beq/ble.
            // Dictionary elaboration can select the former even when the
            // native source seed selected the latter. Without that provenance
            // neither folding nor keeping both arms proves the source ABI.
            if matches!(operation, "Nat.beq" | "Nat.ble") {
                return Err(unsupported("recursive source literal comparison"));
            }
            let (Some(a), Some(b)) = (a.to_u64(), b.to_u64()) else {
                return Err(unsupported("large recursive source constant arithmetic"));
            };
            let value = match operation {
                "Nat.add" => u128::from(a) + u128::from(b),
                "Nat.sub" => u128::from(a.saturating_sub(b)),
                "Nat.mul" => u128::from(a) * u128::from(b),
                _ => return Err(invariant("recursive scalar operation")),
            };
            return Ok(Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![
                value as u64,
                (value >> 64) as u64,
            ]))));
        }
        Ok(Expr::app(
            Expr::app(
                Expr::const_(Name::from_components(operation.split('.')), Vec::new()),
                left,
            ),
            right,
        ))
    }

    /// Residual bvars name original source slots, not their lexical depth.
    /// Shared Expr nodes keep let expansion a DAG rather than duplicating trees.
    fn value(&mut self, expression: &Expr, locals: &mut Vec<Expr>, depth: usize) -> Result<Expr> {
        let value = self.value_inner(expression, locals, depth)?;
        self.checks.meter.charge(self.boolean_facts.len())?;
        Ok(self
            .boolean_facts
            .iter()
            .rev()
            .find_map(|(condition, known)| (*condition == value).then(|| known.clone()))
            .unwrap_or(value))
    }

    fn value_inner(
        &mut self,
        expression: &Expr,
        locals: &mut Vec<Expr>,
        depth: usize,
    ) -> Result<Expr> {
        if depth >= 128 {
            return Err(CompileError::Limit);
        }
        self.checks.meter.charge(1)?;
        let expression = source_without_metadata(expression, self.checks.meter)?;
        if let Some([condition, no, yes]) =
            source_boolean_case(expression, self.checks.environment, self.checks.meter)?
        {
            let condition = self.value(condition, locals, depth + 1)?;
            if named(&condition, "Bool.false") {
                return self.value(no, locals, depth + 1);
            }
            if named(&condition, "Bool.true") {
                return self.value(yes, locals, depth + 1);
            }
            self.discard(&condition)?;
            if self.is_case(&condition)? {
                return Err(unsupported("recursive source nested Boolean discriminator"));
            }
            // Equal alternatives can disappear before discriminator facts are
            // introduced. Preserve that order, especially for unchanged
            // same-slot recursive arguments in otherwise identical arms.
            if no == yes {
                return self.value(no, locals, depth + 1);
            }
            // Simp.withDiscrCtor substitutes a Boolean parameter in each arm.
            // Composite discriminators require LCNF occurrence/CSE provenance;
            // do not infer that separately computed comparisons share a value.
            let parameter = matches!(condition.node(), ExprNode::BVar { .. });
            let mut branch = |syntax, truth| {
                if parameter {
                    self.boolean_facts
                        .try_reserve(1)
                        .map_err(|_| CompileError::Allocation)?;
                    self.boolean_facts.push((
                        condition.clone(),
                        Expr::const_(
                            Name::from_components(["Bool", if truth { "true" } else { "false" }]),
                            Vec::new(),
                        ),
                    ));
                }
                let value = self.value(syntax, locals, depth + 1);
                if parameter {
                    self.boolean_facts.pop();
                }
                value
            };
            let no = branch(no, false)?;
            let yes = branch(yes, true)?;
            if parameter && (self.has_call(&no)? || self.has_call(&yes)?) {
                return Err(unsupported(
                    "recursive source Boolean recursive alternatives",
                ));
            }
            if !parameter && (self.contains(&no, &condition)? || self.contains(&yes, &condition)?) {
                return Err(unsupported(
                    "recursive source shared comparison discriminator",
                ));
            }
            if no == yes {
                self.discard(&condition)?;
                return Ok(no);
            }
            if named(&no, "Bool.false") && named(&yes, "Bool.true") {
                return Ok(condition);
            }
            let head = Expr::const_(
                Name::from_components(["_fln_recursive_source_case"]),
                Vec::new(),
            );
            return Ok([condition, no, yes].into_iter().fold(head, Expr::app));
        }
        match expression.node() {
            ExprNode::BVar { idx } => locals
                .get(
                    locals
                        .len()
                        .checked_sub(*idx as usize + 1)
                        .ok_or_else(|| unsupported("open recursive source body"))?,
                )
                .cloned()
                .ok_or_else(|| unsupported("open recursive source body")),
            ExprNode::Lit { .. } => Ok(expression.clone()),
            ExprNode::Const { .. }
                if named(expression, "Bool.true")
                    || named(expression, "Bool.false")
                    || self.enum_constructor(expression)? =>
            {
                Ok(expression.clone())
            }
            ExprNode::LetE { value, body, .. } => {
                let value = self.value(value, locals, depth + 1)?;
                // The pin may retain a potentially nonterminating initializer
                // even when its result is unused; do not silently zeta it away.
                self.discard(&value)?;
                locals
                    .try_reserve(1)
                    .map_err(|_| CompileError::Allocation)?;
                locals.push(value);
                let result = self.value(body, locals, depth + 1);
                locals.pop();
                result
            }
            ExprNode::App { .. } | ExprNode::Proj { .. } | ExprNode::Const { .. } => {
                let normalized = self.normalize_head(expression.clone(), depth)?;
                if normalized != *expression {
                    return self.value(&normalized, locals, depth + 1);
                }
                let (head, arguments) = self.spine(expression)?;
                let ExprNode::Const { name, levels } = head.node() else {
                    return Err(unsupported("recursive source operation"));
                };
                if !levels.is_empty() {
                    return Err(unsupported("polymorphic recursive source operation"));
                }
                if named(&head, "decide") || named(&head, "Decidable.decide") {
                    return self.equality(&head, &arguments, locals, depth);
                }
                if name == self.companion || name == self.logical {
                    if arguments.len() != self.checks.arity {
                        return Err(unsupported("partial or over-applied recursive source call"));
                    }
                    let mut value = Expr::const_(self.companion.clone(), Vec::new());
                    for argument in arguments {
                        let argument = self.value(&argument, locals, depth + 1)?;
                        if self.is_case(&argument)? {
                            return Err(unsupported("recursive source conditional argument"));
                        }
                        value = Expr::app(value, argument);
                    }
                    return Ok(value);
                }
                let Some(operation) = primitive(name) else {
                    return Err(unsupported("recursive source operation"));
                };
                let [left, right] = arguments.as_slice() else {
                    return Err(unsupported("recursive source primitive arity"));
                };
                self.checks.native(name)?;
                let left = self.value(left, locals, depth + 1)?;
                let right = self.value(right, locals, depth + 1)?;
                if self.is_case(&left)? || self.is_case(&right)? {
                    return Err(unsupported(
                        "recursive source conditional primitive argument",
                    ));
                }
                self.binary(operation, left, right)
            }
            _ => Err(unsupported("recursive source reduction expression")),
        }
    }

    fn uses(&mut self, value: &Expr) -> Result<Vec<bool>> {
        self.checks.meter.charge(self.checks.arity)?;
        let mut used = vec![false; self.checks.arity];
        let mut pending = vec![value.clone()];
        let mut seen = std::collections::HashSet::new();
        while let Some(value) = pending.pop() {
            self.checks.meter.charge(1)?;
            if !seen.insert(value.clone()) {
                continue;
            }
            if let ExprNode::BVar { idx } = value.node() {
                *used
                    .get_mut(*idx as usize)
                    .ok_or_else(|| invariant("recursive source slot"))? = true;
                continue;
            }
            let (head, arguments) = self.spine(&value)?;
            let recursive =
                matches!(head.node(), ExprNode::Const { name, .. } if name == self.companion);
            for (index, argument) in arguments.into_iter().enumerate() {
                // ReduceArity.FindUsed.visitLetValue: unchanged same-slot
                // parameters are not observations. A permutation is a use.
                if !recursive
                    || !matches!(argument.node(), ExprNode::BVar { idx } if *idx as usize == index)
                {
                    pending.push(argument);
                }
            }
        }
        Ok(used)
    }

    fn contains(&mut self, value: &Expr, searched: &Expr) -> Result<bool> {
        let mut pending = vec![value];
        let mut seen = std::collections::HashSet::new();
        while let Some(value) = pending.pop() {
            self.checks.meter.charge(1)?;
            if value == searched {
                return Ok(true);
            }
            if !seen.insert(value.clone()) {
                continue;
            }
            if let ExprNode::App { f, a } = value.node() {
                pending.extend([f, a]);
            }
        }
        Ok(false)
    }
}

pub(super) fn parameters(
    logical: &Name,
    companion: &DefinitionVal,
    arity: usize,
    environment: &crate::Environment,
    ingress: fln_comp::ingress::IngressLimits,
    meter: &mut Budget,
) -> Result<Vec<bool>> {
    let mut analysis = Analysis {
        checks: SourceUses {
            environment,
            arity,
            ingress,
            meter,
            externs: None,
            replacements: None,
            natives: std::collections::BTreeSet::new(),
        },
        companion: &companion.base.name,
        logical,
        boolean_facts: Vec::new(),
        nat_decisions: [false; 2],
    };
    let mut body = &companion.value;
    let mut locals = Vec::new();
    while locals.len() < arity {
        analysis.checks.meter.charge(1)?;
        body = source_without_metadata(body, analysis.checks.meter)?;
        let ExprNode::Lam { body: next, .. } = body.node() else {
            return Err(unsupported("recursive source lambda telescope"));
        };
        let slot = u32::try_from(locals.len()).map_err(|_| CompileError::Limit)?;
        locals
            .try_reserve(1)
            .map_err(|_| CompileError::Allocation)?;
        locals.push(Expr::bvar(slot).map_err(|_| CompileError::Limit)?);
        body = next;
    }
    let value = analysis.value(body, &mut locals, 0)?;
    analysis.uses(&value)
}
