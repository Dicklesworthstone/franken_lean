//! Checked use of imported structural smart-unfolding companions.
//!
//! `_sunfold` and its match annotations locate a candidate, never certify it.
//! The candidate is used only after a closed, metered kernel conversion against
//! the original application. This also enforces the structural-major condition
//! from `Lean/Meta/WHNF.lean` without guessing a recursive argument position.

use super::*;

enum MatchReduction {
    Alternative(Expr),
    Reduced(Expr),
}

fn annotation<'a>(term: &'a Expr, tag: &str) -> Option<&'a Expr> {
    let ExprNode::MData { data, expr } = term.node() else {
        return None;
    };
    (data.len() == 1 && data.get_bool(&Name::from_components([tag]), false)).then_some(expr)
}

impl Context {
    pub(super) fn imported_smart_unfolding(
        &mut self,
        definition: &DefinitionVal,
        levels: &[Level],
        arguments: &[Expr],
    ) -> Result<SmartUnfolding, NatDefinitionElabError> {
        let name = Name::str(definition.base.name.clone(), "_sunfold");
        let Some(ConstantInfo::Defn(companion)) = self.txn.env.find(&name).cloned() else {
            return Ok(SmartUnfolding::Plain);
        };
        if companion.safety != DefinitionSafety::Safe
            || companion.base.level_params.len() != levels.len()
        {
            return Ok(SmartUnfolding::Folded);
        }
        let mut body =
            self.instantiate_params(&companion.value, &companion.base.level_params, levels)?;
        let mut supplied = arguments.iter().rev();
        let mut consumed = 0;
        while let ExprNode::Lam { body: inner, .. } = body.node() {
            self.tick()?;
            let Some(argument) = supplied.next() else {
                return Ok(SmartUnfolding::Folded);
            };
            body = self.substitute(inner, argument)?;
            consumed += 1;
        }
        // A bare name is not the pin's smart-unfolding application path.
        if consumed == 0 || arguments.is_empty() {
            return Ok(SmartUnfolding::Folded);
        }
        let Some(candidate) = self.reduce_imported_smart_body(&body)? else {
            return Ok(SmartUnfolding::Folded);
        };
        let mut original = Expr::const_(definition.base.name.clone(), levels.to_vec());
        for argument in arguments.iter().rev().take(consumed) {
            self.tick()?;
            original = Expr::app(original, argument.clone());
        }
        let original = self.instantiate(&original)?;
        let candidate = self.instantiate(&candidate)?;
        // An open equation is not a completed conversion query. In particular,
        // do not assign a major or universe to justify a speculative unfolding.
        if original.has_expr_mvar()
            || original.has_level_mvar()
            || original.has_loose_bvars()
            || candidate.has_expr_mvar()
            || candidate.has_level_mvar()
            || candidate.has_loose_bvars()
            || !self.coercion_kernel_eq(original, candidate.clone())?
        {
            return Ok(SmartUnfolding::Folded);
        }
        Ok(SmartUnfolding::Alternative {
            value: candidate,
            consumed,
        })
    }

    /// Traverse the companion as the pin's `smartUnfoldingReduce?`: reduce
    /// marked matches, stop at their marked alternatives, and leave ordinary
    /// function bodies and recursive calls folded. Heap tasks bound Rust stack
    /// usage even for imported expression trees.
    fn reduce_imported_smart_body(
        &mut self,
        root: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        enum Task {
            Visit(Expr),
            App,
            Lam(Name, Expr, BinderInfo),
            LetBody(Expr),
            Metadata(KVMap),
            Projection(Name, u64),
        }
        let mut tasks = vec![Task::Visit(root.clone())];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Visit(term) => match term.node() {
                    ExprNode::App { f, a } => {
                        tasks.push(Task::App);
                        tasks.push(Task::Visit(a.clone()));
                        tasks.push(Task::Visit(f.clone()));
                    }
                    ExprNode::Lam {
                        binder_name,
                        binder_type,
                        body,
                        binder_info,
                    } => {
                        tasks.push(Task::Lam(
                            binder_name.clone(),
                            binder_type.clone(),
                            *binder_info,
                        ));
                        tasks.push(Task::Visit(body.clone()));
                    }
                    ExprNode::LetE { value, body, .. } => {
                        tasks.push(Task::LetBody(body.clone()));
                        tasks.push(Task::Visit(value.clone()));
                    }
                    ExprNode::MData { data, expr } => {
                        if let Some(matcher) = annotation(&term, "sunfoldMatch") {
                            match self.reduce_imported_smart_match(matcher)? {
                                Some(MatchReduction::Alternative(value)) => values.push(value),
                                Some(MatchReduction::Reduced(value)) => {
                                    tasks.push(Task::Visit(value));
                                }
                                None => return Ok(None),
                            }
                        } else {
                            tasks.push(Task::Metadata(data.clone()));
                            tasks.push(Task::Visit(expr.clone()));
                        }
                    }
                    ExprNode::Proj {
                        struct_name,
                        idx,
                        expr,
                    } => {
                        tasks.push(Task::Projection(struct_name.clone(), *idx));
                        tasks.push(Task::Visit(expr.clone()));
                    }
                    _ => values.push(term),
                },
                Task::App => {
                    let argument = values.pop().expect("smart application argument");
                    let function = values.pop().expect("smart application function");
                    values.push(Expr::app(function, argument));
                }
                Task::Lam(name, type_, style) => {
                    let body = values.pop().expect("smart lambda body");
                    values.push(Expr::lam(name, type_, body, style));
                }
                Task::LetBody(body) => {
                    let value = values.pop().expect("smart let value");
                    let body = self.substitute(&body, &value)?;
                    tasks.push(Task::Visit(body));
                }
                Task::Metadata(data) => {
                    let body = values.pop().expect("smart metadata body");
                    values.push(Expr::mdata(data, body));
                }
                Task::Projection(name, index) => {
                    let body = values.pop().expect("smart projection body");
                    values.push(Expr::proj(name, index, body));
                }
            }
        }
        Ok(values.pop())
    }

    /// Recognize a safe forwarding body over an admitted auxiliary or recursor.
    /// Imported matchers are not auxRecExt entries, and may be shared by unrelated
    /// declarations (List.map uses instDecidableEqList's matcher). Their actual
    /// body must expose the eliminator; no name suffix grants this permission.
    fn imported_smart_matcher_wrapper(
        &mut self,
        definition: &DefinitionVal,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut body = &definition.value;
        loop {
            self.tick()?;
            match body.node() {
                ExprNode::Lam { body: inner, .. } | ExprNode::MData { expr: inner, .. } => {
                    body = inner
                }
                _ => break,
            }
        }
        while let ExprNode::App { f, .. } = body.node() {
            self.tick()?;
            body = f;
        }
        let ExprNode::Const { name, .. } = body.node() else {
            return Ok(false);
        };
        if self.is_auxiliary_recursor(name)? {
            return Ok(true);
        }
        Ok(matches!(
            self.txn.env.find(name),
            Some(ConstantInfo::Rec(recursor)) if !recursor.is_unsafe
                && !recursor.all.is_empty()
                && recursor.num_motives as usize == recursor.all.len()
        ))
    }

    /// Reduce beta/zeta, admitted auxiliaries/recursors and the safe forwarding
    /// wrappers above, preserving the first alternative marker. The enclosing
    /// conversion query remains necessary after reaching an alternative.
    fn reduce_imported_smart_match(
        &mut self,
        root: &Expr,
    ) -> Result<Option<MatchReduction>, NatDefinitionElabError> {
        let mut head = root.clone();
        let mut arguments = Vec::new();
        let mut matched = false;
        loop {
            self.tick()?;
            if let Some(alternative) = annotation(&head, "sunfoldMatchAlt") {
                let value = self.rebuild_application(alternative.clone(), arguments)?;
                return Ok(Some(MatchReduction::Alternative(value)));
            }
            match head.node() {
                ExprNode::App { f, a } => {
                    arguments.push(a.clone());
                    head = f.clone();
                }
                ExprNode::MData { expr, .. } => head = expr.clone(),
                ExprNode::LetE { value, body, .. } => head = self.substitute(body, value)?,
                ExprNode::Lam { body, .. } if !arguments.is_empty() => {
                    let argument = arguments.pop().expect("smart matcher beta argument");
                    head = self.substitute(body, &argument)?;
                }
                ExprNode::Const { name, levels } => match self.txn.env.find(name).cloned() {
                    Some(ConstantInfo::Defn(auxiliary))
                        if auxiliary.safety == DefinitionSafety::Safe
                            && !arguments.is_empty()
                            && auxiliary.base.level_params.len() == levels.len()
                            && (self.is_auxiliary_recursor(name)?
                                || self.imported_smart_matcher_wrapper(&auxiliary)?) =>
                    {
                        head = self.instantiate_params(
                            &auxiliary.value,
                            &auxiliary.base.level_params,
                            levels,
                        )?;
                    }
                    Some(ConstantInfo::Rec(recursor)) => {
                        let major = recursor_major(&recursor)?;
                        if recursor.is_unsafe
                            || recursor.all.is_empty()
                            || recursor.num_motives as usize != recursor.all.len()
                            || recursor.base.level_params.len() != levels.len()
                            || major >= arguments.len()
                        {
                            return Ok(None);
                        }
                        let position = arguments.len() - major - 1;
                        let mut major_head = self.reduce_source_head(
                            &arguments[position],
                            UnificationTransparency::None,
                            false,
                        )?;
                        let mut major_arguments = Vec::new();
                        while let ExprNode::App { f, a } = major_head.node() {
                            self.tick()?;
                            major_arguments.push(a.clone());
                            major_head = f.clone();
                        }
                        let reduced = match self.source_iota(
                            &head,
                            &recursor,
                            &arguments,
                            &major_head,
                            &major_arguments,
                        )? {
                            Some(value) => Some(value),
                            None => self.source_k_iota(&head, &recursor, &arguments)?,
                        };
                        let Some(reduced) = reduced else {
                            return Ok(None);
                        };
                        arguments.truncate(position);
                        head = reduced;
                        matched = true;
                    }
                    _ => break,
                },
                _ => break,
            }
        }
        if matched {
            self.rebuild_application(head, arguments)
                .map(MatchReduction::Reduced)
                .map(Some)
        } else {
            Ok(None)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::NatLit;
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
    fn literal(value: u64) -> Expr {
        Expr::lit(Literal::Nat(NatLit::from_u64(value)))
    }
    fn app(function: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
        arguments.into_iter().fold(function, Expr::app)
    }
    fn arrow(domain: Expr, range: Expr) -> Expr {
        Expr::forall_e(Name::anonymous(), domain, range, BinderInfo::Default)
    }
    fn mark(tag: &str, value: Expr) -> Expr {
        let mut data = KVMap::new();
        data.insert(n(tag), fln_core::options::DataValue::OfBool(true));
        Expr::mdata(data, value)
    }
    fn choose(flag: Expr, no: Expr, yes: Expr) -> Expr {
        app(
            Expr::const_(n("Bool.rec"), vec![Level::one()]),
            [
                Expr::lam(n("b"), c("Bool"), c("Nat"), BinderInfo::Default),
                no,
                yes,
                flag,
            ],
        )
    }
    fn definition(name: &str, type_: Expr, value: Expr) -> DefinitionVal {
        DefinitionVal {
            base: ConstantVal {
                name: n(name),
                level_params: Vec::new(),
                type_,
            },
            value,
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![n(name)],
        }
    }
    fn budget() -> Budget {
        Budget::for_stack_bytes(2 * 1024 * 1024)
    }
    fn publish(env: &Environment, declaration: Declaration) -> Environment {
        let Outcome::Complete(admitted) = admit(env, declaration, budget()) else {
            panic!("smart fixture admission must answer");
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("smart fixture must be kernel accepted");
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
            result => panic!("smart fixture publication failed: {result:?}"),
        }
    }

    fn environment(companion: Expr, safety: DefinitionSafety) -> (Environment, DefinitionVal) {
        let mut env = Environment::new();
        for declaration in [
            crate::seed::nat_inductive_seed_declaration(),
            crate::seed::bool_seed_declaration(),
        ] {
            env = publish(&env, declaration);
        }
        // No special suffix or auxiliary tag: the checked body is a direct
        // forwarding telescope over the admitted Bool recursor.
        let matcher = definition(
            "ordinaryMatcher",
            arrow(c("Bool"), arrow(c("Nat"), arrow(c("Nat"), c("Nat")))),
            Expr::lam(
                n("b"),
                c("Bool"),
                Expr::lam(
                    n("no"),
                    c("Nat"),
                    Expr::lam(
                        n("yes"),
                        c("Nat"),
                        choose(
                            Expr::bvar(2).unwrap(),
                            Expr::bvar(1).unwrap(),
                            Expr::bvar(0).unwrap(),
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
        );
        env = publish(&env, Declaration::Defn(matcher));
        let original = definition(
            "choose",
            arrow(c("Bool"), c("Nat")),
            Expr::lam(
                n("b"),
                c("Bool"),
                choose(Expr::bvar(0).unwrap(), literal(3), literal(7)),
                BinderInfo::Default,
            ),
        );
        env = publish(&env, Declaration::Defn(original.clone()));
        let mut companion = definition(
            "choose._sunfold",
            original.base.type_.clone(),
            Expr::lam(n("b"), c("Bool"), companion, BinderInfo::Default),
        );
        companion.safety = safety;
        env = publish(&env, Declaration::Defn(companion));
        (env, original)
    }

    fn matching_body(yes: u64) -> Expr {
        mark(
            "sunfoldMatch",
            app(
                c("ordinaryMatcher"),
                [
                    Expr::bvar(0).unwrap(),
                    mark("sunfoldMatchAlt", literal(3)),
                    mark("sunfoldMatchAlt", literal(yes)),
                ],
            ),
        )
    }

    #[test]
    fn checked_smart_matches_keep_general_delta_disabled() {
        let (env, original) = environment(matching_body(7), DefinitionSafety::Safe);
        let mut context = Context::new(&env, budget());
        for (flag, expected) in [("Bool.false", 3), ("Bool.true", 7)] {
            let call = Expr::app(c("choose"), c(flag));
            assert_eq!(
                context
                    .unfold_selected_definition(&call, &original)
                    .unwrap(),
                literal(expected)
            );
        }
        let unselected = app(
            c("ordinaryMatcher"),
            [c("Bool.true"), literal(3), literal(7)],
        );
        assert_eq!(
            context
                .whnf_with_transparency(&unselected, UnificationTransparency::None, false)
                .unwrap(),
            unselected
        );
        assert_eq!(
            context
                .unfold_selected_definition(&c("choose"), &original)
                .unwrap(),
            c("choose")
        );
        let registered =
            crate::aux_recursors::register_module(&env, &[n("ordinaryMatcher")]).unwrap();
        let mut context = Context::new(&registered, budget());
        assert_eq!(
            context
                .whnf_with_transparency(&unselected, UnificationTransparency::None, false)
                .unwrap(),
            literal(7)
        );
    }

    #[test]
    fn false_or_unsafe_companions_and_stuck_majors_do_not_authorize_unfolding() {
        let call = Expr::app(c("choose"), c("Bool.true"));
        for (body, safety) in [
            (matching_body(8), DefinitionSafety::Safe),
            (matching_body(7), DefinitionSafety::Unsafe),
        ] {
            let (env, original) = environment(body, safety);
            let mut context = Context::new(&env, budget());
            assert_eq!(
                context
                    .unfold_selected_definition(&call, &original)
                    .unwrap(),
                call
            );
            assert_eq!(context.txn.env, env);
            assert!(context.txn.mvars.assignments().is_empty());
        }
        // A forged alternative marker bypasses matcher evaluation, but cannot
        // bypass conversion with the blocked original structural application.
        let (env, original) =
            environment(mark("sunfoldMatchAlt", literal(7)), DefinitionSafety::Safe);
        let mut context = Context::new(&env, budget());
        let id = FVarId(n("flag"));
        context
            .txn
            .lctx
            .add_param(id.clone(), n("flag"), c("Bool"), BinderInfo::Default);
        let blocked = Expr::app(c("choose"), Expr::fvar(id));
        let locals = context.txn.lctx.clone();
        assert_eq!(
            context
                .unfold_selected_definition(&blocked, &original)
                .unwrap(),
            blocked
        );
        assert_eq!(context.txn.env, env);
        assert_eq!(context.txn.lctx, locals);
        assert!(context.txn.mvars.assignments().is_empty());
    }

    #[test]
    fn smart_conversion_exhaustion_is_not_a_failed_match() {
        let (env, original) = environment(matching_body(7), DefinitionSafety::Safe);
        let call = Expr::app(c("choose"), c("Bool.true"));
        let mut control = Context::new(&env, budget());
        assert_eq!(
            control
                .unfold_selected_definition(&call, &original)
                .unwrap(),
            literal(7)
        );
        let spent = control.txn.budget.heartbeats_consumed;
        let mut limited = Context::new(&env, budget());
        limited.txn.budget.max_heartbeats = spent - 1;
        let error = limited
            .unfold_selected_definition(&call, &original)
            .unwrap_err();
        assert!(matches!(
            error,
            NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit | SourceInferenceError::TypeObligation(_)
            )
        ));
        assert_eq!(limited.txn.env, env);
        assert!(limited.txn.mvars.assignments().is_empty());
    }
}
