//! The pin's reserved declaration names (v4.32.0). A source declaration may not take a name one
//! of the pin's `registerReservedNamePredicate` predicates claims (`checkNotAlreadyDeclared`,
//! Lean/Elab/DeclModifiers.lean:29-55, which asks for both the user-facing and the private form),
//! and a definition may not be declared once one of its equation names is taken
//! (`ensureEqnReservedNamesAvailable`, Lean/Meta/Eqns.lean:89-92).
//!
//! Ported, each a pure function of the environment and the name:
//! - `eq_<n>`, `eq_def`, `eq_unfold` of a safe definition (Meta/Eqns.lean:57-83, 97-104);
//! - `fun_cases`, `fun_cases_unfolding` of a safe definition, `induct`, `induct_unfolding` of
//!   a structurally or well-founded recursive one (standalone or mutual), and `mutual_induct`,
//!   `mutual_induct_unfolding` of the first member of a mutual recursive block
//!   (Meta/Tactic/FunInd.lean:1500-1534);
//! - `hinj` of a constructor (Meta/Injective.lean:288-291);
//! - `hcongr_<n>` and `congr_simp` of any constant (Meta/CongrTheorems.lean:395-406).
//!
//! Not yet ported: the predicates keyed on constants FrankenLean does not declare: matchers
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

/// The constant at the head of a definition's value under leading lambdas, if any.
fn body_head_const(mut expr: &fln_core::expr::Expr) -> Option<&Name> {
    while let ExprNode::Lam { body: inner, .. } = expr.node() {
        expr = inner;
    }
    while let ExprNode::App { f, .. } = expr.node() {
        expr = f;
    }
    match expr.node() {
        ExprNode::Const { name, .. } => Some(name),
        _ => None,
    }
}

fn is_well_founded_fix_head(name: &Name) -> bool {
    *name == Name::from_components(["WellFounded", "fix"])
        || *name == Name::from_components(["WellFounded", "Nat", "fix"])
}

fn has_partial_unsafe_rec(env: &Environment, name: &Name) -> bool {
    matches!(
        env.find(&Name::str(name.clone(), "_unsafe_rec")),
        Some(ConstantInfo::Defn(definition)) if definition.safety == DefinitionSafety::Partial
    )
}

/// Standalone well-founded recursion lowers to `WellFounded.fix` or `WellFounded.Nat.fix` under
/// leading lambdas and admits a `partial` `<name>._unsafe_rec` executable companion
/// (`recursion/well_founded.rs`). Requiring the companion distinguishes elaborated well-founded
/// definitions from manual `WellFounded.fix` definitions, for which the pin does not reserve
/// `induct`.
fn well_founded_recursive(env: &Environment, name: &Name) -> bool {
    let Some(ConstantInfo::Defn(definition)) = env.find(name) else {
        return false;
    };
    definition.safety == DefinitionSafety::Safe
        && has_partial_unsafe_rec(env, name)
        && body_head_const(&definition.value).is_some_and(is_well_founded_fix_head)
}

/// The first member of a mutual recursive block (structural or well-founded) containing `name`.
/// Both mutual paths record the SCC member list in `definition.all` (`all.len() > 1`) and admit
/// a safe `<first>._mutual` definition (`partial/group/ordinary.rs`).
fn mutual_recursive_first<'a>(env: &'a Environment, name: &Name) -> Option<&'a Name> {
    let Some(ConstantInfo::Defn(definition)) = env.find(name) else {
        return None;
    };
    if definition.safety != DefinitionSafety::Safe
        || definition.all.len() <= 1
        || !definition.all.contains(name)
    {
        return None;
    }
    let first = &definition.all[0];
    safe_definition(env, &Name::str(first.clone(), "_mutual")).then_some(first)
}

/// Whether `name` belongs to a mutual structural recursion block (`partial/group/ordinary.rs`):
/// `<first>._mutual` is assembled with checked body obligations (`LetE`), whereas mutual
/// well-founded `<first>._mutual` is headed by `WellFounded.fix` / `WellFounded.Nat.fix`.
fn mutual_structurally_recursive(env: &Environment, name: &Name) -> bool {
    let Some(first) = mutual_recursive_first(env, name) else {
        return false;
    };
    let Some(ConstantInfo::Defn(mutual)) = env.find(&Name::str(first.clone(), "_mutual")) else {
        return false;
    };
    matches!(mutual.value.node(), ExprNode::LetE { .. })
}

/// `isReservedName` over the ported predicates. The caller asks for each form of the name, as
/// `checkNotAlreadyDeclared` does; a module's private equation names are found through the
/// private form, so exposure needs no separate case.
pub fn is_reserved(env: &Environment, name: &Name) -> bool {
    let LeafView::Str(suffix) = name.leaf_view() else {
        return false;
    };
    let parent = name.parent();
    match suffix {
        "eq_def" | "eq_unfold" => safe_definition(env, &parent),
        "fun_cases" | "fun_cases_unfolding" => safe_definition(env, &parent),
        "induct" | "induct_unfolding" => {
            safe_definition(env, &parent)
                && (structurally_recursive(env, &parent)
                    || well_founded_recursive(env, &parent)
                    || mutual_recursive_first(env, &parent).is_some())
        }
        "mutual_induct" | "mutual_induct_unfolding" => {
            safe_definition(env, &parent)
                && mutual_recursive_first(env, &parent).is_some_and(|first| first == &parent)
        }
        "hinj" => matches!(env.find(&parent), Some(ConstantInfo::Ctor(_))),
        "congr_simp" => env.contains(&parent),
        _ if indexed(suffix, "eq_") => safe_definition(env, &parent),
        _ if indexed(suffix, "hcongr_") => env.contains(&parent),
        _ => false,
    }
}

/// The auxiliaries the pin declares beside every structurally recursive definition (standalone or
/// mutual): `f._f` (the `brecOn` functional), `f._sunfold` (smart unfolding) and `f._unsafe_rec`
/// (the compiler's copy), listed from the pin's environment (v4.32.0, 2026-10-11, re-verified for
/// mutual blocks 2026-11-22). Well-founded definitions do not declare `_f` or `_sunfold` at the
/// pin, and their `_unsafe_rec` is already admitted directly into the environment. FrankenLean
/// keeps `_f` and `_sunfold` inside the checked definition, so a source declaration of one is
/// refused here as already declared. The `f.match_<n>` matchers are not: the pin shares a matcher
/// between declarations of the same shape, so their names depend on the whole file.
pub(super) fn is_declared_auxiliary(env: &Environment, name: &Name) -> bool {
    let LeafView::Str(suffix) = name.leaf_view() else {
        return false;
    };
    let parent = name.parent();
    matches!(suffix, "_f" | "_sunfold" | "_unsafe_rec")
        && safe_definition(env, &parent)
        && (structurally_recursive(env, &parent) || mutual_structurally_recursive(env, &parent))
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
    use super::{is_declared_auxiliary, is_nat, is_reserved};
    use fln_core::expr::{BinderInfo, Expr};
    use fln_core::level::Level;
    use fln_core::name::Name;
    use fln_env::constants::{
        ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
    };
    use fln_env::environment::Environment;

    fn n(path: &str) -> Name {
        Name::from_components(path.split('.'))
    }

    fn defn(name: &str, value: Expr, safety: DefinitionSafety, all: Vec<Name>) -> ConstantInfo {
        ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: n(name),
                level_params: Vec::new(),
                type_: Expr::sort(Level::one()),
            },
            value,
            hints: ReducibilityHints::Regular(1),
            safety,
            all,
        })
    }

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

    #[test]
    fn well_founded_and_mutual_reserved_and_auxiliary_predicates() {
        let sort = Expr::sort(Level::zero());
        let wf_fix = Expr::lam(
            n("x"),
            sort.clone(),
            Expr::app(
                Expr::const_(n("WellFounded.Nat.fix"), Vec::new()),
                sort.clone(),
            ),
            BinderInfo::Default,
        );
        let generic_wf_fix =
            Expr::app(Expr::const_(n("WellFounded.fix"), Vec::new()), sort.clone());
        let structural_mutual = Expr::let_e(
            Name::anonymous(),
            sort.clone(),
            sort.clone(),
            sort.clone(),
            false,
        );

        let env = Environment::new()
            // Standalone well-founded: WellFounded.Nat.fix + partial _unsafe_rec.
            .add_decl(defn(
                "wf",
                wf_fix.clone(),
                DefinitionSafety::Safe,
                vec![n("wf")],
            ))
            .unwrap()
            .add_decl(defn(
                "wf._unsafe_rec",
                sort.clone(),
                DefinitionSafety::Partial,
                vec![n("wf._unsafe_rec")],
            ))
            .unwrap()
            // Manual WellFounded.fix without _unsafe_rec must NOT reserve `induct`.
            .add_decl(defn(
                "manualWf",
                generic_wf_fix,
                DefinitionSafety::Safe,
                vec![n("manualWf")],
            ))
            .unwrap()
            // Mutual structural: all = [meven, modd], meven._mutual starts with LetE.
            .add_decl(defn(
                "meven._mutual",
                structural_mutual,
                DefinitionSafety::Safe,
                vec![n("meven._mutual")],
            ))
            .unwrap()
            .add_decl(defn(
                "meven",
                sort.clone(),
                DefinitionSafety::Safe,
                vec![n("meven"), n("modd")],
            ))
            .unwrap()
            .add_decl(defn(
                "modd",
                sort.clone(),
                DefinitionSafety::Safe,
                vec![n("meven"), n("modd")],
            ))
            .unwrap()
            // Mutual well-founded: all = [mwfA, mwfB], mwfA._mutual is WellFounded.Nat.fix.
            .add_decl(defn(
                "mwfA._mutual",
                wf_fix,
                DefinitionSafety::Safe,
                vec![n("mwfA._mutual")],
            ))
            .unwrap()
            .add_decl(defn(
                "mwfA",
                sort.clone(),
                DefinitionSafety::Safe,
                vec![n("mwfA"), n("mwfB")],
            ))
            .unwrap()
            .add_decl(defn(
                "mwfB",
                sort,
                DefinitionSafety::Safe,
                vec![n("mwfA"), n("mwfB")],
            ))
            .unwrap();

        for reserved in [
            "wf.induct",
            "wf.induct_unfolding",
            "meven.mutual_induct",
            "meven.mutual_induct_unfolding",
            "meven.induct",
            "modd.induct",
            "modd.induct_unfolding",
            "mwfA.mutual_induct",
            "mwfA.mutual_induct_unfolding",
            "mwfA.induct",
            "mwfB.induct",
            "mwfB.induct_unfolding",
        ] {
            assert!(
                is_reserved(&env, &n(reserved)),
                "expected reserved: {reserved}"
            );
        }
        for free in [
            "wf.mutual_induct",
            "manualWf.induct",
            "manualWf.induct_unfolding",
            "modd.mutual_induct",
            "modd.mutual_induct_unfolding",
            "mwfB.mutual_induct",
            "mwfB.mutual_induct_unfolding",
        ] {
            assert!(!is_reserved(&env, &n(free)), "expected free: {free}");
        }
        for aux in [
            "meven._f",
            "meven._sunfold",
            "meven._unsafe_rec",
            "modd._f",
            "modd._sunfold",
            "modd._unsafe_rec",
        ] {
            assert!(
                is_declared_auxiliary(&env, &n(aux)),
                "expected declared auxiliary: {aux}"
            );
        }
        for non_aux in [
            "wf._f",
            "wf._sunfold",
            "manualWf._f",
            "mwfA._f",
            "mwfA._sunfold",
            "mwfB._f",
            "mwfB._sunfold",
        ] {
            assert!(
                !is_declared_auxiliary(&env, &n(non_aux)),
                "expected non-auxiliary: {non_aux}"
            );
        }
    }
}
