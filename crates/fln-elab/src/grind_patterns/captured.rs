//! Restricted wire patterns: exact ground annotations and a reserved wildcard.
//! Wildcards exist only in selection metadata. They never enter a proof term.
use super::*;
use fln_core::options::{DataValue, KVMap};

fn ground_name() -> Name {
    Name::from_components(["grind", "ground_pat"])
}
fn wildcard_name() -> Name {
    Name::from_components(["[grind_dontcare]"])
}
pub(crate) fn wildcard() -> Expr {
    Expr::const_(wildcard_name(), Vec::new())
}
pub(crate) fn is_wildcard(expression: &Expr) -> bool {
    matches!(expression.node(), ExprNode::Const { name, levels }
        if *name == wildcard_name() && levels.is_empty())
}
pub(crate) fn mark_ground(expression: Expr) -> Expr {
    Expr::mdata(
        KVMap::from_entries(vec![(ground_name(), DataValue::OfBool(true))]),
        expression,
    )
}
pub(crate) fn ground_pattern(expression: &Expr) -> Option<&Expr> {
    match expression.node() {
        ExprNode::MData { data, expr }
            if data.len() == 1 && data.get_bool(&ground_name(), false) =>
        {
            Some(expr)
        }
        _ => None,
    }
}

fn constant(
    env: &Environment,
    expression: &Expr,
    parameters: &[Name],
    names: &mut HashSet<Name>,
    remaining: &mut usize,
) -> Result<(), Error> {
    let ExprNode::Const { name, levels } = expression.node() else {
        return Err(Error::Malformed);
    };
    if *name == wildcard_name() {
        return Err(Error::Malformed);
    }
    let declaration = env
        .find(name)
        .ok_or_else(|| Error::UnknownDeclaration(name.clone()))?;
    if levels.len() != declaration.constant_val().level_params.len() {
        return Err(Error::Malformed);
    }
    for level in levels {
        validate_level(level, parameters, remaining)?;
    }
    names.insert(name.clone());
    Ok(())
}

pub(super) fn validate_with(
    env: &Environment,
    row: &GrindPattern,
    capture: &CapturedPatterns,
    remaining: &mut usize,
) -> Result<(), Error> {
    if capture.patterns.len() > MAX_PATTERNS || capture.symbols.len() > MAX_SYMBOLS {
        return Err(Error::Limit);
    }
    if capture.patterns.is_empty() || capture.symbols.is_empty() {
        return Err(Error::Malformed);
    }
    let info = env
        .find(&row.declaration)
        .ok_or_else(|| Error::UnknownDeclaration(row.declaration.clone()))?;
    let parameters = &info.constant_val().level_params;
    let mut covered = vec![false; row.data_params as usize];
    let mut names = HashSet::new();
    let mut required = HashSet::new();
    // true denotes an argument; roots and nested non-ground applications share
    // the same first-order shape, but only argument positions admit gadgets.
    let mut pending: Vec<_> = capture.patterns.iter().rev().map(|p| (p, false)).collect();
    while let Some((expression, argument)) = pending.pop() {
        spend(remaining)?;
        if argument && is_wildcard(expression) {
            continue;
        }
        if argument && let Some(ground) = ground_pattern(expression) {
            if ground.has_fvar()
                || ground.has_loose_bvars()
                || ground.has_expr_mvar()
                || ground.has_level_mvar()
            {
                return Err(Error::Malformed);
            }
            let mut ground_terms = vec![ground];
            let mut seen = HashSet::new();
            while let Some(term) = ground_terms.pop() {
                spend(remaining)?;
                if !seen.insert(term.allocation_identity()) {
                    continue;
                }
                match term.node() {
                    ExprNode::Const { .. } => {
                        constant(env, term, parameters, &mut names, remaining)?
                    }
                    ExprNode::App { f, a } => ground_terms.extend([f, a]),
                    ExprNode::Sort { level } => validate_level(level, parameters, remaining)?,
                    ExprNode::Lit { .. } => {}
                    _ => return Err(Error::Unsupported("a non-first-order ground pattern")),
                }
            }
            continue;
        }
        if argument && let ExprNode::BVar { idx } = expression.node() {
            if *idx >= row.num_params || *idx < row.num_params - row.data_params {
                return Err(Error::Malformed);
            }
            covered[(row.num_params - idx - 1) as usize] = true;
            continue;
        }
        // All closed children are explicitly marked by NormalizePattern.goArg.
        if argument && !expression.has_loose_bvars() {
            return Err(Error::Malformed);
        }
        let mut head = expression;
        let mut arguments = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            spend(remaining)?;
            arguments.push(a);
            head = f;
        }
        let ExprNode::Const { name, .. } = head.node() else {
            return Err(Error::Unsupported(
                "a captured pattern without a constant head",
            ));
        };
        if !supported_head(name) {
            return Err(Error::Unsupported(
                "an interpreted captured pattern or gadget",
            ));
        }
        constant(env, head, parameters, &mut names, remaining)?;
        required.insert(name.clone());
        for argument in arguments {
            pending.push((argument, true));
        }
    }
    if !covered.iter().all(|found| *found) {
        return Err(Error::Unsupported(
            "a data parameter not determined by captured patterns",
        ));
    }
    let mut symbols = HashSet::new();
    for symbol in &capture.symbols {
        spend(remaining)?;
        if symbol.is_anonymous() || !symbols.insert(symbol.clone()) || !names.contains(symbol) {
            return Err(Error::Malformed);
        }
        if !env.contains(symbol) {
            return Err(Error::UnknownDeclaration(symbol.clone()));
        }
    }
    if !required.is_subset(&symbols) {
        return Err(Error::Malformed);
    }
    let mut first = &capture.patterns[0];
    while let ExprNode::App { f, .. } = first.node() {
        spend(remaining)?;
        first = f;
    }
    if !matches!(first.node(), ExprNode::Const { name, .. }
        if capture.symbols.first() == Some(name))
    {
        return Err(Error::Malformed);
    }
    Ok(())
}

/// A capture may erase supporting arguments, but may not alter the other
/// expression nodes. This ties serialized metadata to its checked raw witness.
pub(super) fn compatible(
    raw: &[Expr],
    captured: &[Expr],
    remaining: &mut usize,
) -> Result<(), Error> {
    if raw.len() != captured.len() {
        return Err(Error::Malformed);
    }
    let mut pending: Vec<_> = raw.iter().zip(captured).collect();
    while let Some((raw, capture)) = pending.pop() {
        spend(remaining)?;
        if is_wildcard(capture) {
            continue;
        }
        if let Some(ground) = ground_pattern(capture) {
            if raw != ground {
                return Err(Error::Malformed);
            }
            continue;
        }
        match (raw.node(), capture.node()) {
            (ExprNode::App { f, a }, ExprNode::App { f: g, a: b }) => {
                pending.extend([(f, g), (a, b)]);
            }
            _ if raw == capture => {}
            _ => return Err(Error::Malformed),
        }
    }
    Ok(())
}
