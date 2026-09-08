//! Preserve the original bounded-source unknown-constant diagnostic authority.
//!
//! The new resolver cannot infer a type for a missing reference. For syntax the
//! old explicit-only builder understands, we may still reconstruct its exact
//! untrusted candidate so the caller receives the ordinary K1 rejection. This is
//! a negative-only diagnostic path: even a K1-accepted reconstruction is refused,
//! and no inference error, resource stop or unsolved implicit can use this path
//! to obtain a successful declaration. Queries without an inferable type remain
//! frontend errors rather than manufacturing a query type.

use super::*;

fn rejected(candidate: Declaration, env: &Environment, budget: Budget) -> Option<Declaration> {
    match check(env, &candidate, budget) {
        Outcome::Complete(Verdict::Rejected { .. }) => Some(candidate),
        _ => None,
    }
}

pub(super) fn definition(
    syntax: &Syntax,
    env: &Environment,
    budget: Budget,
) -> Option<Declaration> {
    rejected(
        elaborate_definition_with_types(syntax, true, Some(env)).ok()?,
        env,
        budget,
    )
}

pub(super) fn evaluation(
    syntax: &Syntax,
    name: Name,
    env: &Environment,
    budget: Budget,
) -> Option<Declaration> {
    if !name.parent().is_anonymous() || !matches!(name.leaf_view(), LeafView::Num(_)) {
        return None;
    }
    let parts = expect_node(syntax, &parser_kind(&["Command", "eval"]), 2, "evaluation").ok()?;
    expect_atom(&parts[0], "#eval", "evaluation keyword").ok()?;
    let value = elaborate_term(&parts[1], &[], &nat_const(), true, Some(env)).ok()?;
    let type_ = infer_expr_type(&value, &[], Some(env))
        .filter(|ty| acceptable_inferred(ty, true))
        .unwrap_or_else(nat_const);
    let value = eta_expand_nondependent(value, &type_).ok()?;
    rejected(
        Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: Vec::new(),
                type_,
            },
            value,
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![name],
        }),
        env,
        budget,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diagnostic_reconstruction_never_returns_an_accepted_candidate() {
        let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
        let env = seed::bootstrap_nat_environment(budget).unwrap();
        let parsed = parse_definition(b"def answer : Nat := 42").unwrap();
        assert!(definition(parsed.syntax(), &env, budget).is_none());
        let parsed = parse_definition(b"def answer : Nat := missing").unwrap();
        let candidate = definition(parsed.syntax(), &env, budget).unwrap();
        assert!(matches!(
            check(&env, &candidate, budget),
            Outcome::Complete(Verdict::Rejected { .. })
        ));
    }
}
