//! The Reference's import-time identity rule for a name that more than one
//! module of an import set declares (`Environment.lean`, `finalizeImport` and
//! `subsumesInfo`).
//!
//! Lean regenerates equation and unfolding lemmas (`eq_def`, `induct_unfolding`,
//! ...) in every module that realizes them, so a closed import set routinely
//! carries two copies of one name. The pinned `Init` closure has 16 that are
//! not byte-identical; every one measured has the identical statement, level
//! parameters and `all`, and a different proof term. Import accepts such a
//! pair when one copy subsumes the other and keeps the later subsuming copy.
//! The rule's tolerance of binder names and binder info in the statement is
//! mirrored faithfully but no repeat at this pin exercises it.

use std::collections::HashSet;

use fln_core::expr::{Expr, ExprNode};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_env::constants::ConstantInfo;

/// Lean's `Expr.eqv` (`expr_eq_fn<false>`, `kernel/expr_eq_fn.cpp`): structural
/// equality ignoring binder names and binder info on binders, and let names.
/// `let` non-dependence, metadata, projections, constants with their levels and
/// literals are compared exactly.
///
/// Pairs of nodes already compared are not revisited, so shared subterms cost
/// their DAG size rather than their tree size, as with the C++ pair cache.
pub(crate) fn expr_eqv(left: &Expr, right: &Expr) -> bool {
    let mut pending = vec![(left, right)];
    let mut compared: HashSet<(*const ExprNode, *const ExprNode)> = HashSet::new();
    while let Some((left, right)) = pending.pop() {
        let (a, b) = (left.node(), right.node());
        if std::ptr::eq(a, b) || !compared.insert((std::ptr::from_ref(a), std::ptr::from_ref(b))) {
            continue;
        }
        match (a, b) {
            (ExprNode::BVar { idx: x }, ExprNode::BVar { idx: y }) if x == y => {}
            (ExprNode::FVar { id: x }, ExprNode::FVar { id: y }) if x == y => {}
            (ExprNode::MVar { id: x }, ExprNode::MVar { id: y }) if x == y => {}
            (ExprNode::Sort { level: x }, ExprNode::Sort { level: y }) if x == y => {}
            (ExprNode::Lit { literal: x }, ExprNode::Lit { literal: y }) if x == y => {}
            (
                ExprNode::Const {
                    name: x,
                    levels: xs,
                },
                ExprNode::Const {
                    name: y,
                    levels: ys,
                },
            ) if x == y && xs == ys => {}
            (ExprNode::App { f: xf, a: xa }, ExprNode::App { f: yf, a: ya }) => {
                pending.push((xf, yf));
                pending.push((xa, ya));
            }
            (
                ExprNode::Lam {
                    binder_type: xt,
                    body: xb,
                    ..
                },
                ExprNode::Lam {
                    binder_type: yt,
                    body: yb,
                    ..
                },
            )
            | (
                ExprNode::ForallE {
                    binder_type: xt,
                    body: xb,
                    ..
                },
                ExprNode::ForallE {
                    binder_type: yt,
                    body: yb,
                    ..
                },
            ) => {
                pending.push((xt, yt));
                pending.push((xb, yb));
            }
            (
                ExprNode::LetE {
                    type_: xt,
                    value: xv,
                    body: xb,
                    non_dep: xn,
                    ..
                },
                ExprNode::LetE {
                    type_: yt,
                    value: yv,
                    body: yb,
                    non_dep: yn,
                    ..
                },
            ) if xn == yn => {
                pending.push((xt, yt));
                pending.push((xv, yv));
                pending.push((xb, yb));
            }
            (ExprNode::MData { data: xd, expr: xe }, ExprNode::MData { data: yd, expr: ye })
                if xd == yd =>
            {
                pending.push((xe, ye))
            }
            (
                ExprNode::Proj {
                    struct_name: xs,
                    idx: xi,
                    expr: xe,
                },
                ExprNode::Proj {
                    struct_name: ys,
                    idx: yi,
                    expr: ye,
                },
            ) if xs == ys && xi == yi => pending.push((xe, ye)),
            _ => return false,
        }
    }
    true
}

/// Lean's `subsumesInfo cinfo₁ cinfo₂`: whether importing `later` over
/// `earlier` is coherent. `lookup` answers for constants already imported,
/// which the axiom rule needs to recognise a proposition.
pub(crate) fn subsumes_info<'a>(
    lookup: &dyn Fn(&Name) -> Option<&'a ConstantInfo>,
    first: &ConstantInfo,
    second: &ConstantInfo,
) -> bool {
    let (a, b) = (first.constant_val(), second.constant_val());
    if a.name != b.name || !expr_eqv(&a.type_, &b.type_) || a.level_params != b.level_params {
        return false;
    }
    match (first, second) {
        (ConstantInfo::Thm(x), ConstantInfo::Thm(y)) => x.all == y.all,
        (ConstantInfo::Thm(x), ConstantInfo::Axiom(y)) => {
            x.all.as_slice() == std::slice::from_ref(&y.base.name) && !y.is_unsafe
        }
        (ConstantInfo::Axiom(x), ConstantInfo::Axiom(y)) => {
            x.is_unsafe == y.is_unsafe && is_prop_cheap(lookup, &x.base.type_)
        }
        _ => false,
    }
}

/// Lean's `isPropCheap`: `ty = ∀ ..., p xs...` with `p : ∀ args..., Prop` and
/// as many `args` as `xs`.
fn is_prop_cheap<'a>(lookup: &dyn Fn(&Name) -> Option<&'a ConstantInfo>, ty: &Expr) -> bool {
    let mut ty = ty;
    while let ExprNode::ForallE { body, .. } = ty.node() {
        ty = body;
    }
    let mut head = ty;
    let mut arguments = 0_usize;
    while let ExprNode::App { f, .. } = head.node() {
        head = f;
        arguments += 1;
    }
    let ExprNode::Const { name, .. } = head.node() else {
        return false;
    };
    let Some(declaration) = lookup(name) else {
        return false;
    };
    let mut predicate = &declaration.constant_val().type_;
    for _ in 0..arguments {
        let ExprNode::ForallE { body, .. } = predicate.node() else {
            return false;
        };
        predicate = body;
    }
    matches!(predicate.node(), ExprNode::Sort { level } if *level == Level::zero())
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::BinderInfo;
    use fln_env::constants::{AxiomVal, ConstantVal, TheoremVal};

    fn name(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    fn constant(text: &str) -> Expr {
        Expr::const_(name(text), Vec::new())
    }

    fn forall(binder: &str, info: BinderInfo, domain: Expr, body: Expr) -> Expr {
        Expr::forall_e(name(binder), domain, body, info)
    }

    fn theorem(text: &str, type_: Expr, value: Expr, all: &[&str]) -> ConstantInfo {
        ConstantInfo::Thm(TheoremVal {
            base: ConstantVal {
                name: name(text),
                level_params: Vec::new(),
                type_,
            },
            value,
            all: all.iter().map(|member| name(member)).collect(),
        })
    }

    fn axiom(text: &str, type_: Expr, is_unsafe: bool) -> ConstantInfo {
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: name(text),
                level_params: Vec::new(),
                type_,
            },
            is_unsafe,
        })
    }

    fn bvar(index: u32) -> Expr {
        Expr::bvar(index).expect("small bound index")
    }

    fn pinned_lib() -> Option<std::path::PathBuf> {
        let lib = std::env::var_os("FLN_REFERENCE_LIB")
            .map(std::path::PathBuf::from)
            .or_else(|| {
                std::env::var_os("HOME").map(|home| {
                    std::path::PathBuf::from(home)
                        .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
                })
            })
            .filter(|lib| lib.is_dir());
        assert!(
            lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "FLN_REQUIRE_REFERENCE is set but the pinned Reference lib/lean is absent"
        );
        lib
    }

    fn decode_pinned(lib: &std::path::Path, module: &str) -> Vec<ConstantInfo> {
        let base = module
            .split('.')
            .fold(lib.to_path_buf(), |path, part| path.join(part))
            .with_extension("olean");
        let read = |path: std::path::PathBuf| std::fs::read(&path).expect("pinned olean part");
        let limits = crate::OleanCheckLimits::new(
            256 * 1024 * 1024,
            crate::Budget::for_stack_bytes(64 * 1024 * 1024),
        );
        crate::decode_olean_module_artifacts(
            &read(base.clone()),
            &read(base.with_extension("olean.server")),
            &read(base.with_extension("olean.private")),
            limits.decode,
        )
        .expect("pinned module decodes")
        .constants
    }

    /// The pinned Reference imports these modules together (both pairs are in
    /// `Init`), so its `subsumesInfo` accepts every repeat between them.
    #[test]
    fn every_pinned_repeat_between_co_imported_modules_is_subsumed() {
        let Some(lib) = pinned_lib() else {
            eprintln!(
                "SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)"
            );
            return;
        };
        let pairs = [
            ["Init.Data.List.TakeDrop", "Init.Data.List.Impl"],
            [
                "Init.Data.String.Lemmas.Pattern.Pred",
                "Init.Data.String.Lemmas.Pattern.Char",
            ],
        ];
        let no_lookup = |_: &Name| None;
        let mut repeats = Vec::new();
        for [first, second] in pairs {
            let earlier = decode_pinned(&lib, first);
            let by_name: std::collections::BTreeMap<&Name, &ConstantInfo> =
                earlier.iter().map(|info| (info.name(), info)).collect();
            for later in decode_pinned(&lib, second) {
                if let Some(&previous) = by_name.get(later.name())
                    && *previous != later
                {
                    assert!(
                        subsumes_info(&no_lookup, previous, &later)
                            && subsumes_info(&no_lookup, &later, previous),
                        "{} repeats between {first} and {second} without subsumption",
                        later.name().to_display_string()
                    );
                    repeats.push((previous.clone(), later));
                }
            }
        }
        let mut names: Vec<String> = repeats
            .iter()
            .map(|(previous, _)| previous.name().to_display_string())
            .collect();
        names.sort();
        assert_eq!(
            names,
            [
                "List.take.eq_def",
                "List.takeWhile.eq_def",
                "String.Slice.Pos.revSkipWhile._unary.induct_unfolding",
                "String.Slice.Pos.skipWhile._unary.induct_unfolding",
            ],
            "the measured non-identical repeats between these pinned modules"
        );

        // Control: the same pair with one statement perturbed is refused, so
        // the acceptances above are not a rule that accepts everything.
        let (previous, later) = &repeats[0];
        let ConstantInfo::Thm(mut perturbed) = later.clone() else {
            unreachable!("every measured repeat is a theorem");
        };
        perturbed.base.type_ = Expr::app(perturbed.base.type_.clone(), constant("Nat.zero"));
        let perturbed = ConstantInfo::Thm(perturbed);
        assert!(!subsumes_info(&no_lookup, previous, &perturbed));
        assert!(!subsumes_info(&no_lookup, &perturbed, previous));
    }

    #[test]
    fn eqv_ignores_binder_names_and_info_but_not_structure() {
        let nat = constant("Nat");
        let left = forall("x", BinderInfo::Default, nat.clone(), bvar(0));
        let renamed = forall(
            "y._@.Init.Data.List.Basic._hyg.12",
            BinderInfo::Implicit,
            nat.clone(),
            bvar(0),
        );
        assert!(expr_eqv(&left, &renamed));
        let other_domain = forall("x", BinderInfo::Default, constant("Int"), bvar(0));
        assert!(!expr_eqv(&left, &other_domain));
        let as_lambda = Expr::lam(name("x"), nat, bvar(0), BinderInfo::Default);
        assert!(!expr_eqv(&left, &as_lambda), "a binder's kind is structure");
    }

    #[test]
    fn eqv_compares_let_non_dependence_and_levels() {
        let nat = constant("Nat");
        let one = Expr::let_e(name("a"), nat.clone(), constant("Nat.zero"), bvar(0), false);
        let other = Expr::let_e(name("b"), nat.clone(), constant("Nat.zero"), bvar(0), false);
        let non_dep = Expr::let_e(name("a"), nat, constant("Nat.zero"), bvar(0), true);
        assert!(expr_eqv(&one, &other));
        assert!(!expr_eqv(&one, &non_dep));
        let zero = Expr::sort(Level::zero());
        let one_level = Expr::sort(Level::one());
        assert!(!expr_eqv(&zero, &one_level));
    }

    #[test]
    fn eqv_pays_dag_size_not_tree_size_on_shared_terms() {
        // Two independently built chains doubling a shared subterm 200 times:
        // tree size 2^200, DAG size 201 each.
        let build = |binder: &str| {
            let mut term = constant("Nat.zero");
            for _ in 0..200 {
                term = Expr::app(Expr::app(constant("Nat.add"), term.clone()), term);
            }
            forall(binder, BinderInfo::Default, constant("Nat"), term)
        };
        assert!(expr_eqv(&build("x"), &build("renamed")));
        let mut different = build("x");
        different = Expr::app(different, constant("Nat.zero"));
        assert!(!expr_eqv(&build("x"), &different));
    }

    #[test]
    fn subsumption_follows_the_reference_rule_per_kind() {
        let proposition = constant("P");
        let lookup_p = axiom("P", Expr::sort(Level::zero()), false);
        let lookup = |candidate: &Name| (*candidate == name("P")).then_some(&lookup_p);
        let statement = |binder: &str| {
            forall(
                binder,
                BinderInfo::Default,
                constant("Nat"),
                proposition.clone(),
            )
        };

        let first = theorem("t", statement("x"), constant("h1"), &["t"]);
        let renamed = theorem("t", statement("y"), constant("h2"), &["t"]);
        assert!(subsumes_info(&lookup, &first, &renamed));
        assert!(subsumes_info(&lookup, &renamed, &first));

        let other_block = theorem("t", statement("x"), constant("h1"), &["t", "u"]);
        assert!(!subsumes_info(&lookup, &first, &other_block));

        let renamed_constant = theorem("s", statement("x"), constant("h1"), &["s"]);
        assert!(!subsumes_info(&lookup, &first, &renamed_constant));

        let as_axiom = axiom("t", statement("z"), false);
        assert!(
            subsumes_info(&lookup, &first, &as_axiom),
            "a theorem subsumes its axiom form"
        );
        assert!(
            !subsumes_info(&lookup, &as_axiom, &first),
            "an axiom never subsumes a theorem"
        );
        let unsafe_axiom = axiom("t", statement("z"), true);
        assert!(!subsumes_info(&lookup, &first, &unsafe_axiom));

        let prop_axiom = axiom("t", statement("x"), false);
        assert!(
            subsumes_info(&lookup, &prop_axiom, &as_axiom),
            "two axioms stating a proposition"
        );
        let data = axiom("d", constant("Nat"), false);
        let data_again = axiom("d", constant("Nat"), false);
        assert!(
            !subsumes_info(&lookup, &data, &data_again),
            "an axiom that is not a proposition is never merged"
        );
    }
}
