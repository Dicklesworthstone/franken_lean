//! The pin's reserved declaration names (v4.32.0). A source declaration may not take a name one
//! of the pin's `registerReservedNamePredicate` predicates claims (`checkNotAlreadyDeclared`,
//! Lean/Elab/DeclModifiers.lean:29-55, which asks for both the user-facing and the private form),
//! and a definition may not be declared once one of its equation names is taken
//! (`ensureEqnReservedNamesAvailable`, Lean/Meta/Eqns.lean:89-92).
//!
//! Ported, each a pure function of the environment and the name:
//! - `eq_<n>`, `eq_def`, `eq_unfold` of a safe definition (Meta/Eqns.lean:57-83, 97-104);
//! - `fun_cases`, `fun_cases_unfolding` of a safe definition, and `induct`, `induct_unfolding` of
//!   a structurally recursive one (Meta/Tactic/FunInd.lean:1500-1534);
//! - `hinj` of a constructor (Meta/Injective.lean:288-291);
//! - `hcongr_<n>` and `congr_simp` of any constant (Meta/CongrTheorems.lean:395-406).
//!
//! Not yet ported: `mutual_induct` (the first definition of a mutual recursive block) and the
//! predicates keyed on constants FrankenLean does not declare: matchers
//! (Meta/Match/MatchEqs.lean:341,355), `ctorIdx` (Meta/CtorIdxHInj.lean:58), method specs
//! (Meta/MethodSpecs.lean:221), sparse `casesOn` (Meta/Constructions/SparseCasesOnEq.lean:92)
//! and partial fixpoints (Elab/PreDefinition/PartialFixpoint/Induction.lean:306).
use fln_core::expr::ExprNode;
use fln_core::name::{LeafView, Name};
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use fln_env::environment::Environment;

/// `String.isNat` (Init/Data/String/Slice.lean:976-989): ASCII digits, with an `_` only
/// between two digits.
fn is_nat(text: &str) -> bool {
    let mut last_was_digit = false;
    for character in text.chars() {
        if character == '_' {
            if !last_was_digit {
                return false;
            }
            last_was_digit = false;
        } else if character.is_ascii_digit() {
            last_was_digit = true;
        } else {
            return false;
        }
    }
    last_was_digit
}

fn indexed(suffix: &str, prefix: &str) -> bool {
    suffix.strip_prefix(prefix).is_some_and(is_nat)
}

fn safe_definition(env: &Environment, name: &Name) -> bool {
    matches!(
        env.find(name),
        Some(ConstantInfo::Defn(definition)) if definition.safety == DefinitionSafety::Safe
    )
}

/// Structural recursion leaves its obligation `let` (`recursion::structural_obligation_name`)
/// directly under the definition's lambdas: the pin's `Structural.eqnInfoExt` entry.
pub(in crate::source) fn structurally_recursive(env: &Environment, name: &Name) -> bool {
    let Some(ConstantInfo::Defn(definition)) = env.find(name) else {
        return false;
    };
    let mut body = &definition.value;
    while let ExprNode::Lam { body: inner, .. } = body.node() {
        body = inner;
    }
    matches!(
        body.node(),
        ExprNode::LetE { decl_name, .. }
            if super::super::recursion::structural_obligation_parameters(decl_name).is_some()
    )
}

/// `isReservedName` over the ported predicates. The caller asks for each form of the name, as
/// `checkNotAlreadyDeclared` does; a module's private equation names are found through the
/// private form, so exposure needs no separate case.
pub(super) fn is_reserved(env: &Environment, name: &Name) -> bool {
    let LeafView::Str(suffix) = name.leaf_view() else {
        return false;
    };
    let parent = name.parent();
    match suffix {
        "eq_def" | "eq_unfold" => safe_definition(env, &parent),
        "fun_cases" | "fun_cases_unfolding" => safe_definition(env, &parent),
        "induct" | "induct_unfolding" => {
            safe_definition(env, &parent) && structurally_recursive(env, &parent)
        }
        "hinj" => matches!(env.find(&parent), Some(ConstantInfo::Ctor(_))),
        "congr_simp" => env.contains(&parent),
        _ if indexed(suffix, "eq_") => safe_definition(env, &parent),
        _ if indexed(suffix, "hcongr_") => env.contains(&parent),
        _ => false,
    }
}

/// The auxiliaries the pin declares beside every structurally recursive definition: `f._f` (the
/// `brecOn` functional), `f._sunfold` (smart unfolding) and `f._unsafe_rec` (the compiler's copy),
/// listed from the pin's environment (v4.32.0, 2026-10-11). FrankenLean keeps all three inside `f`,
/// so a source declaration of one is refused here as already declared. The `f.match_<n>` matchers
/// are not: the pin shares a matcher between declarations of the same shape, so their names
/// depend on the whole file.
pub(super) fn is_declared_auxiliary(env: &Environment, name: &Name) -> bool {
    let LeafView::Str(suffix) = name.leaf_view() else {
        return false;
    };
    matches!(suffix, "_f" | "_sunfold" | "_unsafe_rec")
        && safe_definition(env, &name.parent())
        && structurally_recursive(env, &name.parent())
}

/// `ensureEqnReservedNamesAvailable`: the first equation name already declared, if any. The pin
/// checks only `eq_1` of the indexed ones.
pub(super) fn taken_equation_name(env: &Environment, declaration: &Name) -> Option<Name> {
    ["eq_unfold", "eq_def", "eq_1"]
        .into_iter()
        .map(|suffix| Name::str(declaration.clone(), suffix))
        .find(|name| env.contains(name))
}

#[cfg(test)]
mod tests {
    use super::is_nat;

    #[test]
    fn is_nat_matches_the_pins_examples() {
        for (text, expected) in [
            ("0", true),
            ("123", true),
            ("1_000", true),
            ("", false),
            ("_123", false),
            ("123_", false),
            ("12__34", false),
            ("0xff", false),
            ("2+3", false),
        ] {
            assert_eq!(is_nat(text), expected, "{text:?}");
        }
    }
}
