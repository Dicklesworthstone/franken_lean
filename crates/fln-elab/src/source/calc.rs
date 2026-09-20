//! Native calculations over binary relations. Every written step remains an
//! annotated let in the final candidate, even when conversion could ignore its
//! proof. Equality transport uses ordinary Eq.rec and grants no admission.
use super::*;

pub(super) struct Build<'a> {
    pub steps: Vec<&'a [Syntax]>,
    pub cursor: usize,
    expected: Option<Expr>,
    saved: LocalContext,
    bindings: Vec<(FVarId, Name, Expr, Expr)>,
    chain: Option<Typed>,
}

struct Relation {
    head: Expr,
    left: Expr,
    right: Expr,
}

impl Relation {
    fn view(expression: &Expr) -> Option<Self> {
        let ExprNode::App { f, a: right } = expression.node() else {
            return None;
        };
        let ExprNode::App { f: head, a: left } = f.node() else {
            return None;
        };
        Some(Self {
            head: head.clone(),
            left: left.clone(),
            right: right.clone(),
        })
    }

    fn at(&self, left: Expr, right: Expr) -> Expr {
        Expr::app(Expr::app(self.head.clone(), left), right)
    }
}

fn invalid() -> NatDefinitionElabError {
    NatDefinitionElabError::UnexpectedSyntax {
        expected: "a binary relation with two endpoints in a calculation",
    }
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

    // Preserve the written relation head: unfolding it can erase its endpoints
    // or reverse them (for example, a greater-than abbreviation). Reduction is
    // only a fallback for a type hidden behind a let or other non-application.
    fn calculation_relation(
        &mut self,
        expression: &Expr,
    ) -> Result<(Expr, Relation), NatDefinitionElabError> {
        let expression = self.instantiate(expression)?;
        if let Some(relation) = Relation::view(&expression) {
            return Ok((expression, relation));
        }
        let expression = self.whnf(&expression)?;
        let relation = Relation::view(&expression).ok_or_else(invalid)?;
        Ok((expression, relation))
    }

    pub(super) fn prepare_calculation_step(
        &mut self,
        build: &mut Build<'_>,
        relation: Typed,
    ) -> Result<Expr, NatDefinitionElabError> {
        let (target, current) = self.calculation_relation(&relation.value)?;
        if let Some(chain) = &build.chain {
            let (_, previous) = self.calculation_relation(&chain.type_)?;
            // Only adjacent written endpoints constrain continuation holes.
            // The expected result is checked after composition, not mined for
            // endpoints: relations may be heterogeneous or reverse arguments.
            self.equations
                .push(SourceEquation::selection(current.left, previous.right));
            self.flush(true)?;
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

    #[allow(clippy::too_many_lines)]
    fn compose_calculation(
        &mut self,
        previous: Typed,
        next: Typed,
    ) -> Result<Typed, NatDefinitionElabError> {
        let (previous_type, previous_relation) = self.calculation_relation(&previous.type_)?;
        let (next_type, next_relation) = self.calculation_relation(&next.type_)?;
        let (equality, relation, proof, backwards) =
            if let Some(equality) = tactics::equality_target(&next_type) {
                (equality, previous_relation, previous.value.clone(), false)
            } else if let Some(equality) = tactics::equality_target(&previous_type) {
                (equality, next_relation, next.value.clone(), true)
            } else {
                return Err(invalid());
            };
        let (level, alpha, base, end) = equality;
        let endpoint_name = self.fresh_name()?;
        let endpoint = FVarId(endpoint_name.clone());
        let endpoint_expr = Expr::fvar(endpoint.clone());
        let (result, family, minor, equality_proof) = if backwards {
            // a = b, S b c  ==> S a c. Eliminate a = b into
            // (S x c -> S a c), with identity at x = a, then apply S b c.
            // This avoids inventing symmetry axioms or assuming S is injective.
            let result = relation.at(base.clone(), relation.right.clone());
            let domain = relation.at(endpoint_expr.clone(), relation.right.clone());
            let family = Expr::forall_e(
                Name::anonymous(),
                domain,
                result.clone(),
                BinderInfo::Default,
            );
            let minor = Expr::lam(
                Name::anonymous(),
                result.clone(),
                Expr::bvar(0).map_err(|_| failure(SourceInferenceError::Scope))?,
                BinderInfo::Default,
            );
            (result, family, minor, previous.value)
        } else {
            // R a b, b = c  ==> R a c, including equality-only chains.
            let result = relation.at(relation.left.clone(), end.clone());
            let family = relation.at(relation.left.clone(), endpoint_expr.clone());
            (result, family, proof.clone(), next.value)
        };
        let result_sort = self
            .known_type(&result)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let result_sort = self.whnf(&result_sort)?;
        let ExprNode::Sort { level: result_level } = result_sort.node() else {
            return Err(failure(SourceInferenceError::ExpectedType));
        };
        let witness_name = self.fresh_name()?;
        let witness = FVarId(witness_name.clone());
        let witness_type = equation(level.clone(), alpha.clone(), base.clone(), endpoint_expr);
        let body = family
            .abstract_fvar(&witness, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let motive = Expr::lam(witness_name, witness_type, body, BinderInfo::Default);
        let motive = motive
            .abstract_fvar(&endpoint, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let motive = Expr::lam(endpoint_name, alpha.clone(), motive, BinderInfo::Default);
        let value = [alpha, base, motive, minor, end, equality_proof]
            .into_iter()
            .fold(
                Expr::const_(
                    Name::from_components(["Eq", "rec"]),
                    vec![result_level.clone(), level],
                ),
                Expr::app,
            );
        Ok(Typed {
            value: if backwards { Expr::app(value, proof) } else { value },
            type_: result,
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