//! Re-admit a restricted normalized foreign pattern without re-normalizing it.
//! Wildcards are restored only to type-check a raw witness. Matching and export
//! retain the original captured bytes' expressions and symbol order.
use super::*;
use crate::grind_patterns::CapturedPatterns;
use std::collections::HashSet;

fn malformed() -> NatDefinitionElabError {
    registry_error(GrindPatternError::Malformed)
}

struct Hole {
    value: Expr,
    available: Vec<Expr>,
}
struct Restore {
    data: Vec<Expr>,
    seen: HashSet<FVarId>,
    holes: Vec<Hole>,
}

pub fn import_captured(
    env: &Environment,
    kernel: Budget,
    declaration: &Name,
    proof: &Expr,
    num_params: u32,
    patterns: &[Expr],
    symbols: &[Name],
) -> Result<GrindPattern, NatDefinitionElabError> {
    if num_params > registry::MAX_PARAMETERS
        || patterns.len() > registry::MAX_PATTERNS
        || symbols.len() > registry::MAX_SYMBOLS
    {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    let info = env.find(declaration).ok_or_else(|| {
        registry_error(GrindPatternError::UnknownDeclaration(declaration.clone()))
    })?;
    if !registry::safe_proof_candidate(info) {
        return Err(malformed());
    }
    let level_params = info.constant_val().level_params.clone();
    let expected_levels: Vec<_> = level_params.iter().cloned().map(Level::param).collect();
    if !matches!(proof.node(), ExprNode::Const { name, levels }
        if name == declaration && *levels == expected_levels)
    {
        return Err(malformed());
    }
    let mut context = Context::new(env, kernel);
    // This context validates an existing expression, not a new source term.
    // Later irreducibility attributes cannot invalidate its checked types.
    context.tactic_transparency = Some(UnificationTransparency::SafeDefinitions);
    context.infer_level_params = false;
    context.level_params = level_params.clone();
    let mut cursor = info.constant_val().type_.clone();
    // Check the serialized count before any supported-fragment refusal.
    // The pin uses plain forallTelescope, so this count is purely syntactic.
    let mut telescope = &cursor;
    let mut actual_params = 0u32;
    while let ExprNode::ForallE { body, .. } = telescope.node() {
        context.tick()?;
        if actual_params >= registry::MAX_PARAMETERS {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        actual_params += 1;
        telescope = body;
    }
    if actual_params != num_params {
        return Err(malformed());
    }
    if !proposition(&mut context, &cursor)? {
        return Err(malformed());
    }
    let mut locals = Vec::new();
    let mut data_params = 0u32;
    let mut proof_suffix = false;
    while let ExprNode::ForallE {
        binder_name,
        binder_type,
        body,
        binder_info,
    } = cursor.node()
    {
        context.tick()?;
        if locals.len() >= registry::MAX_PARAMETERS as usize {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let is_proof = proposition(&mut context, binder_type)?;
        if is_proof {
            proof_suffix = true;
            if body.has_loose_bvars() {
                return Err(unsupported("a dependent imported proof parameter"));
            }
        } else if proof_suffix {
            return Err(unsupported(
                "an imported data parameter following a proof parameter",
            ));
        } else {
            data_params += 1;
        }
        let id = FVarId(context.fresh_name()?);
        context.txn.lctx.add_param(
            id.clone(),
            binder_name.clone(),
            binder_type.clone(),
            *binder_info,
        );
        cursor = context.substitute(body, &Expr::fvar(id.clone()))?;
        locals.push(id);
    }
    if locals.len() != num_params as usize {
        return Err(malformed());
    }
    if matches!(context.whnf(&cursor)?.node(), ExprNode::ForallE { .. }) {
        return Err(unsupported(
            "an imported result-type alias exposing another telescope",
        ));
    }
    let capture = CapturedPatterns {
        patterns: patterns.to_vec(),
        symbols: symbols.to_vec(),
    };
    let mut row = GrindPattern {
        declaration: declaration.clone(),
        num_params,
        data_params,
        patterns: Vec::new(),
        captured: Some(capture.clone()),
    };
    registry::validate_capture(env, &row, &capture).map_err(registry_error)?;
    let data: Vec<_> = locals[..data_params as usize]
        .iter()
        .cloned()
        .map(Expr::fvar)
        .collect();
    let mut restore = Restore {
        data: data.clone(),
        seen: HashSet::new(),
        holes: Vec::new(),
    };
    let mut raw = Vec::new();
    for pattern in &capture.patterns {
        let pattern = pattern
            .subst_loose(num_params - data_params, &data)
            .map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
        raw.push(context.restore_grind_pattern(&pattern, &mut restore, 0)?);
    }
    for hole in restore.holes {
        context.tick()?;
        if !matches!(
            context.instantiate(&hole.value)?.node(),
            ExprNode::MVar { .. }
        ) {
            continue;
        }
        let Some(expected) = context.known_type(&hole.value)? else {
            return Err(malformed());
        };
        let mut filled = false;
        for candidate in hole.available {
            context.tick()?;
            let Some(actual) = context.known_type(&candidate)? else {
                return Err(malformed());
            };
            if context.proof_types_match(&actual, &expected)? {
                context.constrain(&hole.value, &candidate)?;
                filled = true;
                break;
            }
        }
        if !filled {
            return Err(unsupported(
                "an imported wildcard not witnessed by an earlier data variable",
            ));
        }
    }
    for term in raw {
        let term = context.finish(term)?;
        context.check_grind_pattern_term(&term, &level_params, false)?;
        let mut expression = term.value;
        for (index, id) in locals.iter().enumerate() {
            context.tick()?;
            expression = expression
                .abstract_fvar(id, num_params - index as u32 - 1)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
        }
        row.patterns.push(expression);
    }
    registry::validate(env, &row).map_err(registry_error)?;
    Ok(row)
}

impl Context {
    fn restore_grind_pattern(
        &mut self,
        expression: &Expr,
        restore: &mut Restore,
        depth: usize,
    ) -> Result<Typed, NatDefinitionElabError> {
        self.tick()?;
        if depth >= 128 {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let mut head = expression;
        let mut arguments = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            arguments.push(a);
            head = f;
        }
        arguments.reverse();
        if !matches!(head.node(), ExprNode::Const { name, .. } if registry::supported_head(name)) {
            return Err(unsupported("an unsupported imported pattern head"));
        }
        let Some(mut type_) = self.known_type(head)? else {
            return Err(malformed());
        };
        let mut value = head.clone();
        for argument in arguments {
            self.tick()?;
            type_ = self.whnf(&type_)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = type_.node()
            else {
                return Err(malformed());
            };
            if proposition(self, binder_type)? {
                return Err(unsupported(
                    "an imported proof argument requiring wildcard preprocessing",
                ));
            }
            // The recorded wildcard is authoritative selection metadata. Do
            // not recompute support classification under later reducibility or
            // class-attribute changes; restore only a checked type witness.
            let argument = if registry::is_wildcard(argument) {
                let available: Vec<_> = restore.data.iter().filter(|value|
                    matches!(value.node(), ExprNode::FVar { id } if restore.seen.contains(id)))
                    .cloned().collect();
                if available.is_empty() {
                    return Err(unsupported(
                        "an imported wildcard without an earlier data variable",
                    ));
                }
                let hole = self.hole(binder_type.clone())?;
                restore.holes.push(Hole {
                    value: hole.clone(),
                    available,
                });
                hole
            } else if let Some(ground) = registry::ground_pattern(argument) {
                ground.clone()
            } else if let ExprNode::FVar { id } = argument.node() {
                if !restore.data.contains(argument) {
                    return Err(malformed());
                }
                restore.seen.insert(id.clone());
                argument.clone()
            } else {
                self.restore_grind_pattern(argument, restore, depth + 1)?
                    .value
            };
            let Some(actual) = self.known_type(&argument)? else {
                return Err(malformed());
            };
            self.constrain(&actual, binder_type)?;
            let result_type = self.substitute(body, &argument)?;
            value = Expr::app(value, argument);
            type_ = result_type;
        }
        Ok(Typed { value, type_ })
    }
}
