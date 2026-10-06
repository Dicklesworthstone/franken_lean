//! Expansion of the coercion projections tagged by the pinned `Init/Coe.lean`.
//!
//! The projection's admitted body, not its spelling, determines the reduction.
//! Only the dictionary is reduced at instances transparency: reducing the whole
//! application would also unfold an untagged user conversion such as `Nat.cast`
//! and change the term produced by `Lean.Meta.expandCoe`.
//!
//! This covers the twelve builtin coercion projections. Importing arbitrary
//! user `coe_decl` tags and recording extra-module uses remain separate work.
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
            "Coe" | "CoeTC" | "CoeOut" | "CoeOTC" | "CoeHead" | "CoeHTC"
                | "CoeTail" | "CoeHTCT" | "CoeDep" | "CoeT" | "CoeFun" | "CoeSort"
        )
    )
    .then_some(class)
}

enum Work {
    Visit(Expr),
    Rebuild(Expr),
    Expanded(Expr, Expr),
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
                    if let Some(expanded) = self.expand_coercion_projection(&term)? {
                        work.push(Work::Expanded(term, expanded.clone()));
                        work.push(Work::Visit(expanded));
                        continue;
                    }
                    work.push(Work::Rebuild(term.clone()));
                    match term.node() {
                        ExprNode::App { f, a } => {
                            work.push(Work::Visit(a.clone()));
                            work.push(Work::Visit(f.clone()));
                        }
                        ExprNode::Lam { binder_type, body, .. }
                        | ExprNode::ForallE { binder_type, body, .. } => {
                            work.push(Work::Visit(body.clone()));
                            work.push(Work::Visit(binder_type.clone()));
                        }
                        ExprNode::LetE { type_, value, body, .. } => {
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
                        ExprNode::Lam { binder_name, binder_type, body, binder_info }
                            if changed(binder_type) || changed(body) =>
                        {
                            Expr::lam(binder_name.clone(), get(binder_type), get(body), *binder_info)
                        }
                        ExprNode::ForallE { binder_name, binder_type, body, binder_info }
                            if changed(binder_type) || changed(body) =>
                        {
                            Expr::forall_e(binder_name.clone(), get(binder_type), get(body), *binder_info)
                        }
                        ExprNode::LetE { decl_name, type_, value, body, non_dep }
                            if changed(type_) || changed(value) || changed(body) =>
                        {
                            Expr::let_e(decl_name.clone(), get(type_), get(value), get(body), *non_dep)
                        }
                        ExprNode::Proj { struct_name, idx, expr } if changed(expr) => {
                            Expr::proj(struct_name.clone(), *idx, get(expr))
                        }
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
    ) -> Result<(Expr, Vec<Expr>), NatDefinitionElabError> {
        let mut head = expression.clone();
        let mut args = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            args.push(a.clone());
            head = f.clone();
        }
        args.reverse();
        Ok((head, args))
    }

    fn expand_coercion_projection(
        &mut self,
        expression: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let (head, args) = self.coercion_spine(expression)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(class) = builtin_projection(name) else {
            return Ok(None);
        };
        let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned() else {
            return Ok(None);
        };
        if definition.safety != DefinitionSafety::Safe
            || definition.base.level_params.len() != levels.len()
        {
            return Ok(None);
        }
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(&class) else {
            return Ok(None);
        };
        let parameters = usize::try_from(family.num_params)
            .map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
        let prefix = parameters.checked_add(1)
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
        let dictionary = self.reduce_source_head(
            &args[parameters], UnificationTransparency::Instances, true,
        )?;
        let (constructor, mut fields) = self.coercion_spine(&dictionary)?;
        fields.reverse();
        let Some(mut value) = crate::records::constructor_field(
            &self.txn.env, &class, 0, &constructor, &fields,
        ) else {
            // `unfoldDefinition?` leaves a projection of a stuck dictionary
            // alone; do not replace it with a bare `Expr::Proj`.
            return Ok(None);
        };
        // `headBeta`, not WHNF: untagged conversion functions stay folded.
        for arg in args.into_iter().skip(prefix) {
            self.tick()?;
            value = Expr::app(value, arg);
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
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
            panic!("fixture was not accepted");
        };
        let Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) =
            checked.publish(DeclarationBudget::default(), CollisionBudget::default(), None)
        else {
            panic!("fixture was not published");
        };
        result.environment
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
            n("x"), Expr::fvar(a.id.clone()), Expr::fvar(b.id.clone()), BinderInfo::Default,
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
        ).unwrap();
        for declaration in declarations {
            env = publish(&env, declaration);
        }
        publish(&env, Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: n("convert"),
                level_params: Vec::new(),
                type_: Expr::forall_e(n("x"), c("Nat"), c("Nat"), BinderInfo::Default),
            },
            value: Expr::lam(n("x"), c("Nat"), Expr::bvar(0).unwrap(), BinderInfo::Default),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![n("convert")],
        }))
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
            "Coe", "CoeTC", "CoeOut", "CoeOTC", "CoeHead", "CoeHTC", "CoeTail",
            "CoeHTCT", "CoeDep", "CoeT", "CoeFun", "CoeSort",
        ] {
            assert_eq!(builtin_projection(&Name::str(n(class), "coe")), Some(n(class)));
        }
        for name in [
            n("User.Coe.coe"), n("Coe.cast"), n("Coe.coe.extra"),
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
            n("x"), c("Nat"), coerce(dictionary(c("convert")), variable.clone()),
            BinderInfo::Default,
        );
        let expected = Expr::lam(
            n("x"), c("Nat"), Expr::app(c("convert"), variable), BinderInfo::Default,
        );
        let expanded = context.expand_coercions(&original).unwrap();
        assert_eq!(expanded, expected);
        assert_ne!(expanded, original);
        // Both expressions are checked, not merely compared by a mock reducer.
        assert!(matches!(fln_kernel::check_def_eq(&env, &[], &original, &expanded, budget()),
            Outcome::Complete(Verdict::Accepted { .. })));
    }

    #[test]
    fn revisits_chained_coercions_exposed_by_head_beta() {
        let env = environment();
        let mut context = Context::new(&env, budget());
        let variable = Expr::bvar(0).unwrap();
        let inner = Expr::lam(
            n("x"), c("Nat"), coerce(dictionary(c("convert")), variable.clone()),
            BinderInfo::Default,
        );
        let original = coerce(dictionary(inner), variable.clone());
        assert_eq!(context.expand_coercions(&original).unwrap(), Expr::app(c("convert"), variable));
    }

    #[test]
    fn head_beta_reduces_redexes_exposed_by_substitution() {
        let env = environment();
        let mut context = Context::new(&env, budget());
        let variable = Expr::bvar(0).unwrap();
        let identity = Expr::lam(n("y"), c("Nat"), variable.clone(), BinderInfo::Default);
        let function = Expr::lam(
            n("x"), c("Nat"), Expr::app(identity, variable.clone()), BinderInfo::Default,
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
        assert!(matches!(context.expand_coercions(&original),
            Err(NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit))));
    }
}
