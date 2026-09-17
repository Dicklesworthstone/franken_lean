//! Native equality calculations. Every written step remains an annotated let
//! in the final candidate, even when conversion could ignore its proof. The
//! chain is composed with ordinary Eq.rec; this module grants no admission.
use super::*;

pub(super) struct Build<'a> {
    pub steps: Vec<&'a [Syntax]>,
    pub cursor: usize,
    expected: Option<Expr>,
    saved: LocalContext,
    bindings: Vec<(FVarId, Name, Expr, Expr)>,
    chain: Option<Typed>,
}

fn invalid() -> NatDefinitionElabError {
    failure(SourceInferenceError::Tactic(
        tactics::TacticError::ExpectedEquality,
    ))
}
fn equation(level: Level, alpha: Expr, left: Expr, right: Expr) -> Expr {
    [alpha, left, right].into_iter().fold(
        Expr::const_(Name::from_components(["Eq"]), vec![level]),
        Expr::app,
    )
}

impl Context {
    pub(super) fn start_calculation<'a>(
        &mut self,
        syntax: &'a Syntax,
        expected: Option<Expr>,
    ) -> Result<Build<'a>, NatDefinitionElabError> {
        let parts = expect_node(syntax, &parser_kind(&["Term", "calc"]), 2, "calculation")?;
        expect_atom(&parts[0], "calc", "calculation keyword")?;
        let mut steps = Vec::new();
        for step in expect_null_args(&parts[1], "calculation steps")? {
            self.tick()?;
            let parts = expect_node(
                step,
                &parser_kind(&["Term", "calcStep"]),
                3,
                "calculation step",
            )?;
            expect_atom(&parts[1], ":=", "calculation proof separator")?;
            steps.push(parts);
        }
        if steps.is_empty() {
            return Err(invalid());
        }
        Ok(Build {
            steps,
            cursor: 0,
            expected,
            saved: self.txn.lctx.clone(),
            bindings: Vec::new(),
            chain: None,
        })
    }

    pub(super) fn prepare_calculation_step(
        &mut self,
        build: &mut Build<'_>,
        relation: Typed,
    ) -> Result<Expr, NatDefinitionElabError> {
        let target = self.whnf(&relation.value)?;
        let (_, alpha, left, _) = tactics::equality_target(&target).ok_or_else(invalid)?;
        let predecessor = if let Some(chain) = &build.chain {
            let ty = self.whnf(&chain.type_)?;
            let (_, alpha, _, right) = tactics::equality_target(&ty).ok_or_else(invalid)?;
            Some((alpha, right))
        } else if let Some(expected) = &build.expected {
            let ty = self.whnf(expected)?;
            tactics::equality_target(&ty).map(|(_, alpha, left, _)| (alpha, left))
        } else {
            None
        };
        if let Some((previous_alpha, previous_endpoint)) = predecessor {
            // Solves continuation `_` holes. These are elaboration constraints,
            // not trust: the exact asserted types are retained below and both
            // endpoints are checked again through Eq.rec in the final term.
            self.constrain(&alpha, &previous_alpha)?;
            self.constrain(&left, &previous_endpoint)?;
        }
        self.instantiate(&target)
    }

    pub(super) fn add_calculation_step(
        &mut self,
        build: &mut Build<'_>,
        relation: Expr,
        proof: Typed,
    ) -> Result<(), NatDefinitionElabError> {
        self.tick()?;
        self.constrain_type(&proof.type_, &relation)?;
        let relation = self.instantiate(&relation)?;
        let proof_value = self.instantiate(&proof.value)?;
        let name = self.fresh_name()?;
        let id = FVarId(name.clone());
        // Opaque while elaborating the following steps: long chains do not
        // repeatedly unfold all earlier proofs. Closing emits a real typed let.
        self.txn.lctx.add_param(
            id.clone(),
            name.clone(),
            relation.clone(),
            BinderInfo::Default,
        );
        let current = Typed {
            value: Expr::fvar(id.clone()),
            type_: relation.clone(),
        };
        build.bindings.push((id, name, relation, proof_value));
        build.chain = Some(match build.chain.take() {
            None => current,
            Some(previous) => self.compose_calculation(previous, current)?,
        });
        build.cursor += 1;
        Ok(())
    }

    fn compose_calculation(
        &mut self,
        previous: Typed,
        next: Typed,
    ) -> Result<Typed, NatDefinitionElabError> {
        let previous_type = self.whnf(&previous.type_)?;
        let next_type = self.whnf(&next.type_)?;
        let (level, alpha, first, middle) =
            tactics::equality_target(&previous_type).ok_or_else(invalid)?;
        let (_, _, _, last) = tactics::equality_target(&next_type).ok_or_else(invalid)?;
        let endpoint_name = self.fresh_name()?;
        let endpoint = FVarId(endpoint_name.clone());
        let endpoint_expr = Expr::fvar(endpoint.clone());
        let witness_name = self.fresh_name()?;
        let witness = FVarId(witness_name.clone());
        let witness_type = equation(
            level.clone(),
            alpha.clone(),
            middle.clone(),
            endpoint_expr.clone(),
        );
        let result = equation(level.clone(), alpha.clone(), first.clone(), endpoint_expr);
        let body = result
            .abstract_fvar(&witness, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let motive = Expr::lam(witness_name, witness_type, body, BinderInfo::Default);
        let motive = motive
            .abstract_fvar(&endpoint, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let motive = Expr::lam(endpoint_name, alpha.clone(), motive, BinderInfo::Default);
        let value = [
            alpha.clone(),
            middle,
            motive,
            previous.value,
            last.clone(),
            next.value,
        ]
        .into_iter()
        .fold(
            Expr::const_(
                Name::from_components(["Eq", "rec"]),
                vec![Level::zero(), level.clone()],
            ),
            Expr::app,
        );
        Ok(Typed {
            value,
            type_: equation(level, alpha, first, last),
        })
    }

    pub(super) fn finish_calculation(
        &mut self,
        build: Build<'_>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let mut chain = build.chain.ok_or_else(invalid)?;
        self.flush(false)?;
        chain.value = self.instantiate(&chain.value)?;
        chain.type_ = self.instantiate(&chain.type_)?;
        for (id, name, type_, value) in build.bindings.into_iter().rev() {
            self.tick()?;
            let body = chain
                .value
                .abstract_fvar(&id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            chain.value = Expr::let_e(
                name,
                self.instantiate(&type_)?,
                self.instantiate(&value)?,
                body,
                false,
            );
        }
        self.txn.lctx = build.saved;
        self.finish_term(chain, build.expected.as_ref())
    }
}
