//! Expansion of the coercion projections tagged by the pinned `Init/Coe.lean`.
//!
//! The projection's admitted body, not its spelling, determines the reduction.
//! Only the dictionary is reduced at instances transparency: reducing the whole
//! application would also unfold an untagged user conversion such as `Nat.cast`
//! and change the term produced by `Lean.Meta.expandCoe`.
//!
//! This covers the twelve builtin projections and the two monadic bridges.
//! Importing arbitrary user `coe_decl` tags and recording extra-module uses
//! remain separate work.
mod monad;

use super::*;
use fln_core::name::LeafView;
use fln_env::constants::ConstantInfo;
use std::collections::HashMap;

/// The `attribute [coe_decl]` projection rows in the pinned `Init/Coe.lean`.
/// Compare structural names: an escaped dot or `User.Coe.coe` is not `Coe.coe`.
fn builtin_projection(name: &Name) -> Option<Name> {
    if !matches!(name.leaf_view(), LeafView::Str("coe")) {
        return None;
    }
    let class = name.parent();
    if !class.parent().is_anonymous() {
        return None;
    }
    matches!(
        class.leaf_view(),
        LeafView::Str(
            "Coe"
                | "CoeTC"
                | "CoeOut"
                | "CoeOTC"
                | "CoeHead"
                | "CoeHTC"
                | "CoeTail"
                | "CoeHTCT"
                | "CoeDep"
                | "CoeT"
                | "CoeFun"
                | "CoeSort"
        )
    )
    .then_some(class)
}

enum Work {
    Visit(Expr),
    Rebuild(Expr),
    Expanded(Expr, Expr),
}

struct ApplicationSpine {
    head: Expr,
    arguments: Vec<Expr>,
    // Outermost first, so stacking continuations rebuilds the inner prefixes
    // before the arguments of the outer ones. Each prefix keeps its memo entry.
    prefixes: Vec<Expr>,
}

impl Context {
    /// The builtin projection part of `expandCoe`, including its recursive
    /// visit of newly exposed terms. Heap continuations and memoization retain
    /// DAG sharing; every visit, spine step and reduction spends heartbeats.
    pub(super) fn expand_coercions(
        &mut self,
        expression: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut work = vec![Work::Visit(expression.clone())];
        let mut memo = HashMap::<_, Expr>::new();
        // Identity keys alone do not keep nodes alive. Retain each input whose
        // address is cached, including intermediate expansion results, so an
        // allocator cannot recycle an address during this traversal.
        let mut retained = Vec::new();
        while let Some(step) = work.pop() {
            self.tick()?;
            match step {
                Work::Visit(term) => {
                    if memo.contains_key(&term.allocation_identity()) {
                        continue;
                    }
                    let spine = self.coercion_spine(&term)?;
                    if let Some(expanded) =
                        self.expand_coercion_projection(&spine.head, &spine.arguments)?
                    {
                        work.push(Work::Expanded(term, expanded.clone()));
                        work.push(Work::Visit(expanded));
                        continue;
                    }
                    if !spine.prefixes.is_empty() {
                        // Pinned Meta.Transform.visitApp visits the head and
                        // arguments, not every application prefix. Peeling each
                        // prefix again would make a long spine quadratic. Keep
                        // per-prefix rebuilding so shared subapplications still
                        // reuse the same transformed node.
                        let mut head = spine.head;
                        for (prefix, argument) in spine
                            .prefixes
                            .into_iter()
                            .zip(spine.arguments.into_iter().rev())
                        {
                            if memo.contains_key(&prefix.allocation_identity()) {
                                head = prefix;
                                break;
                            }
                            work.push(Work::Rebuild(prefix));
                            work.push(Work::Visit(argument));
                        }
                        work.push(Work::Visit(head));
                        continue;
                    }
                    work.push(Work::Rebuild(term.clone()));
                    match term.node() {
                        ExprNode::Lam {
                            binder_type, body, ..
                        }
                        | ExprNode::ForallE {
                            binder_type, body, ..
                        } => {
                            work.push(Work::Visit(body.clone()));
                            work.push(Work::Visit(binder_type.clone()));
                        }
                        ExprNode::LetE {
                            type_, value, body, ..
                        } => {
                            work.push(Work::Visit(body.clone()));
                            work.push(Work::Visit(value.clone()));
                            work.push(Work::Visit(type_.clone()));
                        }
                        ExprNode::Proj { expr, .. } | ExprNode::MData { expr, .. } => {
                            work.push(Work::Visit(expr.clone()));
                        }
                        _ => {}
                    }
                }
                Work::Expanded(original, expanded) => {
                    let result = memo[&expanded.allocation_identity()].clone();
                    memo.insert(original.allocation_identity(), result);
                    retained.push(original);
                }
                Work::Rebuild(original) => {
                    let get = |child: &Expr| memo[&child.allocation_identity()].clone();
                    let changed = |child: &Expr| {
                        memo[&child.allocation_identity()].allocation_identity()
                            != child.allocation_identity()
                    };
                    let result = match original.node() {
                        ExprNode::App { f, a } if changed(f) || changed(a) => {
                            Expr::app(get(f), get(a))
                        }
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } if changed(binder_type) || changed(body) => Expr::lam(
                            binder_name.clone(),
                            get(binder_type),
                            get(body),
                            *binder_info,
                        ),
                        ExprNode::ForallE {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } if changed(binder_type) || changed(body) => Expr::forall_e(
                            binder_name.clone(),
                            get(binder_type),
                            get(body),
                            *binder_info,
                        ),
                        ExprNode::LetE {
                            decl_name,
                            type_,
                            value,
                            body,
                            non_dep,
                        } if changed(type_) || changed(value) || changed(body) => Expr::let_e(
                            decl_name.clone(),
                            get(type_),
                            get(value),
                            get(body),
                            *non_dep,
                        ),
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } if changed(expr) => Expr::proj(struct_name.clone(), *idx, get(expr)),
                        ExprNode::MData { data, expr } if changed(expr) => {
                            Expr::mdata(data.clone(), get(expr))
                        }
                        _ => original.clone(),
                    };
                    memo.insert(original.allocation_identity(), result);
                    retained.push(original);
                }
            }
        }
        memo.remove(&expression.allocation_identity())
            .ok_or_else(|| failure(SourceInferenceError::Scope))
    }

    fn coercion_spine(
        &mut self,
        expression: &Expr,
    ) -> Result<ApplicationSpine, NatDefinitionElabError> {
        let mut head = expression.clone();
        let mut arguments = Vec::new();
        let mut prefixes = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            arguments.push(a.clone());
            prefixes.push(head.clone());
            head = f.clone();
        }
        arguments.reverse();
        Ok(ApplicationSpine {
            head,
            arguments,
            prefixes,
        })
    }

    fn expand_coercion_projection(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        if let Some(value) = self.expand_monadic_helper(name, levels, args)? {
            return Ok(Some(value));
        }
        let Some(class) = builtin_projection(name) else {
            return Ok(None);
        };
        let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned() else {
            return Ok(None);
        };
        // Pinned unfoldProjInst? checks the projection at default transparency
        // before reducing its dictionary at instances transparency. Ordinary
        // semireducible class projections are eligible; irreducible ones are not.
        let irreducible = crate::reducibility::table(&self.txn.env)
            .map_err(|error| {
                failure(SourceInferenceError::Unification(Box::new(
                    UnificationError::Reducibility(error),
                )))
            })?
            .status(name)
            == crate::reducibility::Reducibility::Irreducible;
        if irreducible
            || definition.safety != DefinitionSafety::Safe
            || definition.base.level_params.len() != levels.len()
        {
            return Ok(None);
        }
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(&class) else {
            return Ok(None);
        };
        let parameters = usize::try_from(family.num_params)
            .map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
        let prefix = parameters
            .checked_add(1)
            .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
        if args.len() < prefix {
            return Ok(None);
        }
        // Verify the admitted definition really is this projection. An
        // arbitrary safe definition named `Coe.coe` is not projection metadata.
        let mut body = &definition.value;
        for _ in 0..prefix {
            self.tick()?;
            let ExprNode::Lam { body: next, .. } = body.node() else {
                return Ok(None);
            };
            body = next;
        }
        if !matches!(body.node(), ExprNode::Proj { struct_name, idx: 0, expr }
            if struct_name == &class
                && matches!(expr.node(), ExprNode::BVar { idx: 0 }))
        {
            return Ok(None);
        }
        let dictionary =
            self.reduce_source_head(&args[parameters], UnificationTransparency::Instances, true)?;
        let mut dictionary_spine = self.coercion_spine(&dictionary)?;
        dictionary_spine.arguments.reverse();
        let Some(mut value) = crate::records::constructor_field(
            &self.txn.env,
            &class,
            0,
            &dictionary_spine.head,
            &dictionary_spine.arguments,
        ) else {
            // `unfoldDefinition?` leaves a projection of a stuck dictionary
            // alone; do not replace it with a bare `Expr::Proj`.
            return Ok(None);
        };
        // `headBeta`, not WHNF: untagged conversion functions stay folded.
        for arg in args.iter().skip(prefix) {
            self.tick()?;
            value = Expr::app(value, arg.clone());
        }
        let mut arguments = Vec::new();
        loop {
            self.tick()?;
            match value.node() {
                ExprNode::App { f, a } => {
                    arguments.push(a.clone());
                    value = f.clone();
                }
                ExprNode::Lam { body, .. } if !arguments.is_empty() => {
                    let argument = arguments.pop().expect("guarded head beta");
                    value = self.substitute(body, &argument)?;
                }
                _ => break,
            }
        }
        for argument in arguments.into_iter().rev() {
            self.tick()?;
            value = Expr::app(value, argument);
        }
        Ok(Some(value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lctx::LocalDecl;
    use crate::records::{RecordBudget, RecordSpec, record_declarations};
    use fln_env::constants::{ConstantVal, DefinitionVal};
    use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};

    fn n(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }
    fn c(text: &str) -> Expr {
        Expr::const_(n(text), Vec::new())
    }
    fn app(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
        args.into_iter().fold(head, Expr::app)
    }
    fn budget() -> Budget {
        Budget::for_stack_bytes(2 * 1024 * 1024)
    }
    fn publish(env: &Environment, declaration: Declaration) -> Environment {
        let Outcome::Complete(admitted) = admit(env, declaration, budget()) else {
            panic!("kernel did not complete");
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("fixture was not accepted");
        };
        match checked.publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        ) {
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => {
                result.environment
            }
            Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
            other => panic!("fixture publication failed: {other:?}"),
        }
    }
    fn local(name: &str, type_: Expr, index: usize) -> LocalDecl {
        LocalDecl {
            id: FVarId(n(name)),
            user_name: n(name),
            type_,
            value: None,
            binder_info: BinderInfo::Default,
            index,
        }
    }
    fn environment() -> Environment {
        let mut env = crate::seed::bootstrap_nat_environment(budget()).unwrap();
        let a = local("A", Expr::sort(Level::one()), 0);
        let b = local("B", Expr::sort(Level::one()), 1);
        let function = Expr::forall_e(
            n("x"),
            Expr::fvar(a.id.clone()),
            Expr::fvar(b.id.clone()),
            BinderInfo::Default,
        );
        let declarations = record_declarations(
            &RecordSpec {
                name: n("Coe"),
                level_params: Vec::new(),
                parameters: vec![a, b],
                fields: vec![local("coe", function, 2)],
                result_level: Level::one(),
                is_class: true,
            },
            RecordBudget::default(),
        )
        .unwrap();
        for declaration in declarations {
            env = publish(&env, declaration);
        }
        publish(
            &env,
            Declaration::Defn(DefinitionVal {
                base: ConstantVal {
                    name: n("convert"),
                    level_params: Vec::new(),
                    type_: Expr::forall_e(n("x"), c("Nat"), c("Nat"), BinderInfo::Default),
                },
                value: Expr::lam(
                    n("x"),
                    c("Nat"),
                    Expr::bvar(0).unwrap(),
                    BinderInfo::Default,
                ),
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![n("convert")],
            }),
        )
    }
    fn dictionary(function: Expr) -> Expr {
        app(c("Coe.mk"), [c("Nat"), c("Nat"), function])
    }
    fn coerce(dict: Expr, value: Expr) -> Expr {
        app(c("Coe.coe"), [c("Nat"), c("Nat"), dict, value])
    }

    #[test]
    fn builtin_names_are_exact_not_display_string_prefixes() {
        for class in [
            "Coe", "CoeTC", "CoeOut", "CoeOTC", "CoeHead", "CoeHTC", "CoeTail", "CoeHTCT",
            "CoeDep", "CoeT", "CoeFun", "CoeSort",
        ] {
            assert_eq!(
                builtin_projection(&Name::str(n(class), "coe")),
                Some(n(class))
            );
        }
        for name in [
            n("User.Coe.coe"),
            n("Coe.cast"),
            n("Coe.coe.extra"),
            Name::str(Name::anonymous(), "Coe.coe"),
        ] {
            assert!(builtin_projection(&name).is_none());
        }
    }

    #[test]
    fn expands_under_binders_without_unfolding_the_conversion() {
        let env = environment();
        let mut context = Context::new(&env, budget());
        let variable = Expr::bvar(0).unwrap();
        let original = Expr::lam(
            n("x"),
            c("Nat"),
            coerce(dictionary(c("convert")), variable.clone()),
            BinderInfo::Default,
        );
        let expected = Expr::lam(
            n("x"),
            c("Nat"),
            Expr::app(c("convert"), variable),
            BinderInfo::Default,
        );
        let expanded = context.expand_coercions(&original).unwrap();
        assert_eq!(expanded, expected);
        assert_ne!(expanded, original);
        // Both expressions are checked, not merely compared by a mock reducer.
        assert!(matches!(
            fln_kernel::check_def_eq(&env, &[], &original, &expanded, budget()),
            Outcome::Complete(Verdict::Accepted { .. })
        ));
    }

    #[test]
    fn revisits_chained_coercions_exposed_by_head_beta() {
        let env = environment();
        let mut context = Context::new(&env, budget());
        let variable = Expr::bvar(0).unwrap();
        let inner = Expr::lam(
            n("x"),
            c("Nat"),
            coerce(dictionary(c("convert")), variable.clone()),
            BinderInfo::Default,
        );
        let original = coerce(dictionary(inner), variable.clone());
        assert_eq!(
            context.expand_coercions(&original).unwrap(),
            Expr::app(c("convert"), variable)
        );
    }

    #[test]
    fn head_beta_reduces_redexes_exposed_by_substitution() {
        let env = environment();
        let mut context = Context::new(&env, budget());
        let variable = Expr::bvar(0).unwrap();
        let identity = Expr::lam(n("y"), c("Nat"), variable.clone(), BinderInfo::Default);
        let function = Expr::lam(
            n("x"),
            c("Nat"),
            Expr::app(identity, variable.clone()),
            BinderInfo::Default,
        );
        let original = coerce(dictionary(function), variable.clone());
        assert_eq!(context.expand_coercions(&original).unwrap(), variable);
    }

    #[test]
    fn stuck_dictionary_and_partial_projection_are_preserved() {
        let env = environment();
        let mut context = Context::new(&env, budget());
        let stuck = coerce(Expr::fvar(FVarId(n("dictionary"))), Expr::bvar(0).unwrap());
        assert_eq!(context.expand_coercions(&stuck).unwrap(), stuck);
        let partial = app(c("Coe.coe"), [c("Nat"), c("Nat")]);
        assert_eq!(context.expand_coercions(&partial).unwrap(), partial);
    }

    #[test]
    fn irreducible_builtin_projection_is_preserved() {
        let env = crate::reducibility::register(
            &environment(),
            &n("Coe.coe"),
            crate::reducibility::Reducibility::Irreducible,
        )
        .unwrap();
        let mut context = Context::new(&env, budget());
        let original = coerce(dictionary(c("convert")), Expr::bvar(0).unwrap());
        let expanded = context.expand_coercions(&original).unwrap();
        assert_eq!(
            expanded.allocation_identity(),
            original.allocation_identity()
        );
    }

    #[test]
    fn long_application_spine_expands_with_linear_heartbeats() {
        let env = environment();
        let mut context = Context::new(&env, budget());
        let variable = Expr::bvar(0).unwrap();
        let argument = coerce(dictionary(c("convert")), variable.clone());
        let expanded_argument = Expr::app(c("convert"), variable);
        let original = app(c("combine"), std::iter::repeat_n(argument, 2_000));
        let expected = app(c("combine"), std::iter::repeat_n(expanded_argument, 2_000));
        // Repeatedly peeling every application prefix takes over two million
        // steps. One spine traversal and memoized visits need a linear budget.
        context.txn.budget.max_heartbeats = 20_000;
        let expanded = context.expand_coercions(&original).unwrap();
        assert_eq!(expanded, expected);

        let mut context = Context::new(&env, budget());
        context.txn.budget.max_heartbeats = 20_000;
        let unchanged = context.expand_coercions(&expanded).unwrap();
        assert_eq!(
            unchanged.allocation_identity(),
            expanded.allocation_identity()
        );
    }

    #[test]
    fn shared_application_prefix_keeps_one_expansion() {
        let env = environment();
        let variable = Expr::bvar(0).unwrap();
        let prefix = Expr::app(
            c("combine"),
            coerce(dictionary(c("convert")), variable.clone()),
        );
        let extension = Expr::app(prefix.clone(), c("Nat.zero"));
        let expected_prefix = Expr::app(c("combine"), Expr::app(c("convert"), variable));
        for prefix_first in [true, false] {
            let mut context = Context::new(&env, budget());
            let arguments = if prefix_first {
                [prefix.clone(), extension.clone()]
            } else {
                [extension.clone(), prefix.clone()]
            };
            let expanded = context
                .expand_coercions(&app(c("combine"), arguments))
                .unwrap();
            let ExprNode::App { f, a: second } = expanded.node() else {
                panic!("expected outer application");
            };
            let ExprNode::App { a: first, .. } = f.node() else {
                panic!("expected first argument");
            };
            let (prefix, extension) = if prefix_first {
                (first, second)
            } else {
                (second, first)
            };
            let ExprNode::App { f: shared, .. } = extension.node() else {
                panic!("expected extended prefix");
            };
            assert_eq!(prefix, &expected_prefix);
            assert_eq!(prefix.allocation_identity(), shared.allocation_identity());
        }
    }

    #[test]
    fn shared_dag_is_not_expanded_as_an_exponential_tree() {
        let env = environment();
        let mut context = Context::new(&env, budget());
        let mut original = coerce(dictionary(c("convert")), Expr::bvar(0).unwrap());
        let mut expected = Expr::app(c("convert"), Expr::bvar(0).unwrap());
        for _ in 0..64 {
            original = app(c("combine"), [original.clone(), original]);
            expected = app(c("combine"), [expected.clone(), expected]);
        }
        context.txn.budget.max_heartbeats = 20_000;
        assert_eq!(context.expand_coercions(&original).unwrap(), expected);
    }

    #[test]
    fn exhausted_expansion_is_a_typed_resource_stop() {
        let env = environment();
        let mut context = Context::new(&env, budget());
        context.txn.budget.max_heartbeats = 1;
        let original = coerce(dictionary(c("convert")), Expr::bvar(0).unwrap());
        assert!(matches!(
            context.expand_coercions(&original),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
    }
}
