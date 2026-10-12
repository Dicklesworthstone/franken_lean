//! Explicit measures use the selected checked `WellFoundedRelation` through
//! `invImage` and `WellFounded.fix`. The ordinary Nat relation uses the pin's
//! `WellFounded.Nat.fix` specialization. Recursive calls become a typed
//! continuation and a proof obligation; the source tactics solve every one.
//!
//! Varying parameters use `Meta.ArgsPacker`'s dependent PSigma encoding.
//! Fixed arguments are captured at their actual telescope positions. Missing
//! measures try Nat parameters in the pin's telescope order, with active
//! SizeOf and well-founded instances checked. Missing proofs use native
//! simplification, assumptions and omega. Mutual groups and arbitrary
//! SizeOf/lexicographic measure inference remain separate elaboration work.
mod packing;
mod relation;
mod scopes;

use super::*;
use fln_env::constants::ConstantInfo;

#[derive(Clone)]
pub(in crate::source) struct Hint<'a> {
    aliases: Vec<Option<Name>>,
    measure: Option<&'a Syntax>,
    decreasing: Option<&'a Syntax>,
    /// Retain the original local identity, including inaccessible lambda names.
    inferred: Option<usize>,
}

impl Hint<'_> {
    pub(super) fn automatic() -> Self {
        Self {
            aliases: Vec::new(),
            measure: None,
            decreasing: None,
            inferred: None,
        }
    }
}

#[derive(Clone)]
pub(in crate::source) struct State {
    pub name: Name,
    pub reference: Typed,
    marker: FVarId,
    parameters: Vec<LocalDecl>,
    varying: Vec<usize>,
    fixed: Vec<(usize, LocalDecl)>,
    /// These parameters occur in the selected measure's type or dictionary.
    /// Unlike other fixed parameters, allowing one to vary would change the
    /// relation while descending through a single checked fixpoint.
    measure_captures: HashSet<usize>,
    natural_measure: bool,
    continuation: LocalDecl,
    proof_inaccessible: Vec<FVarId>,
    proof_hidden: HashSet<Name>,
    branch_scopes: Vec<Name>,
    calls: HashMap<Expr, CachedCall>,
    goals: Vec<Obligation>,
    pub proving: bool,
}

/// The source branch closes before `decreasing_by` runs. Its term therefore
/// contains a closed metavariable applied to explicit captures, while the
/// tactic goal retains the original branch context and user names.
#[derive(Clone)]
struct Obligation {
    goal: tactics::ProofGoal,
    /// Cleanup reads the unnormalized inverse-image relation: distinct
    /// arguments can have definitionally equal measures but different locals.
    raw_target: Expr,
    transport: MVarId,
    captures: Vec<LocalDecl>,
    arguments: Vec<Expr>,
}

enum Attempt {
    Complete(Typed),
    Repack(Vec<usize>),
    /// Inference has already selected this measure. A final aggregate proof
    /// failure cannot authorize guessing a later measure.
    SelectedFailure(NatDefinitionElabError),
}

enum MeasureProbe {
    Strict,
    Unusable(NatDefinitionElabError),
    Lexicographic,
}

#[derive(Clone)]
struct CachedCall {
    scope: FVarId,
    branch_scope: Option<Name>,
    value: Expr,
}

impl State {
    pub(in crate::source) fn hides(&self, local: &LocalDecl) -> bool {
        local.id == self.marker
            || local.user_name == self.continuation.user_name
            || self.proof_hidden.contains(&local.user_name)
    }
}

/// Read well-founded hints without elaborating them. The pin ignores a hint
/// when a definition has no surviving recursive reference.
pub(in crate::source) fn hint(syntax: &Syntax) -> Result<Option<Hint<'_>>, NatDefinitionElabError> {
    let parts = expect_node(
        syntax,
        &parser_kind(&["Termination", "suffix"]),
        2,
        "termination suffix",
    )?;
    let decreasing = match expect_null_args(&parts[1], "decreasing clause")? {
        [] => None,
        [clause] => {
            let clause = expect_node(
                clause,
                &parser_kind(&["Termination", "decreasingBy"]),
                2,
                "decreasing proof",
            )?;
            expect_atom(&clause[0], "decreasing_by", "decreasing keyword")?;
            Some(&clause[1])
        }
        _ => return Err(failure(SourceInferenceError::Scope)),
    };
    let clause = match expect_null_args(&parts[0], "termination clause")? {
        [] => {
            return Ok(decreasing.map(|decreasing| Hint {
                aliases: Vec::new(),
                measure: None,
                decreasing: Some(decreasing),
                inferred: None,
            }));
        }
        [clause] => clause,
        _ => return Err(failure(SourceInferenceError::Scope)),
    };
    let clause = expect_node(
        clause,
        &parser_kind(&["Termination", "terminationBy"]),
        4,
        "termination clause",
    )?;
    expect_atom(&clause[0], "termination_by", "termination keyword")?;
    if !expect_null_args(&clause[1], "structural termination marker")?.is_empty() {
        return Ok(None);
    }
    let mut aliases = Vec::new();
    match expect_null_args(&clause[2], "termination parameter aliases")? {
        [] => {}
        [binders, arrow] => {
            expect_atom(arrow, "=>", "termination parameter arrow")?;
            let binders = expect_null_args(binders, "termination parameters")?;
            if binders.is_empty() {
                return Err(failure(SourceInferenceError::Scope));
            }
            for binder in binders {
                if let Syntax::Ident { val, .. } = binder
                    && !val.is_anonymous()
                {
                    aliases.push(Some(val.clone()));
                } else {
                    let [hole] = expect_node(
                        binder,
                        &parser_kind(&["Term", "hole"]),
                        1,
                        "termination parameter or underscore",
                    )?
                    else {
                        return Err(failure(SourceInferenceError::Scope));
                    };
                    expect_atom(hole, "_", "termination parameter underscore")?;
                    aliases.push(None);
                }
            }
        }
        _ => return Err(failure(SourceInferenceError::Scope)),
    }
    Ok(Some(Hint {
        aliases,
        measure: Some(&clause[3]),
        decreasing,
        inferred: None,
    }))
}

/// The pin's lexicographic constructor prefix and Nat base-case fragment of
/// decreasing_tactic after the checked continuation has exposed its measure.
/// This is native syntax expansion; no Reference metaprogram is executed.
fn automatic_decreasing_proof() -> Syntax {
    fn null(args: Vec<Syntax>) -> Syntax {
        Syntax::node(Name::from_components(["null"]), args)
    }
    fn atom(value: &str) -> Syntax {
        Syntax::atom(fln_syntax::source::SourceInfo::None, value)
    }
    fn sequence(tactics: Vec<Syntax>) -> Syntax {
        let mut rows = Vec::new();
        for tactic in tactics {
            if !rows.is_empty() {
                rows.push(null(Vec::new()));
            }
            rows.push(tactic);
        }
        Syntax::node(
            parser_kind(&["Tactic", "tacticSeq"]),
            vec![Syntax::node(
                parser_kind(&["Tactic", "tacticSeq1Indented"]),
                vec![null(rows)],
            )],
        )
    }
    fn first(tactics: Vec<Syntax>) -> Syntax {
        Syntax::node(
            parser_kind(&["Tactic", "first"]),
            vec![
                atom("first"),
                null(
                    tactics
                        .into_iter()
                        .map(|tactic| {
                            Syntax::node(
                                Name::from_components(["group"]),
                                vec![atom("|"), sequence(vec![tactic])],
                            )
                        })
                        .collect(),
                ),
            ],
        )
    }
    fn lexicographic_constructors(family: &str) -> Syntax {
        // Preserve the pin's right-before-left order. A right constructor
        // commits only when the first coordinate is definitionally equal.
        let alternatives = ["right", "left"]
            .into_iter()
            .map(|constructor| {
                let identifier = Syntax::Ident {
                    info: fln_syntax::source::SourceInfo::None,
                    raw_val: fln_syntax::source::ByteSpan::default(),
                    val: Name::from_components(["_root_", family, "Lex", constructor]),
                    preresolved: Vec::new(),
                };
                Syntax::node(
                    parser_kind(&["Tactic", "apply"]),
                    vec![atom("apply"), identifier],
                )
            })
            .collect();
        Syntax::node(
            parser_kind(&["Tactic", "tacticRepeat_"]),
            vec![atom("repeat"), sequence(vec![first(alternatives)])],
        )
    }
    let simp = Syntax::node(
        parser_kind(&["Tactic", "simp"]),
        vec![
            atom("simp"),
            null(Vec::new()),
            null(Vec::new()),
            null(Vec::new()),
            null(Vec::new()),
            null(Vec::new()),
        ],
    );
    let alternatives = ["done", "assumption", "omega"]
        .into_iter()
        .map(|name| {
            let mut args = vec![atom(name)];
            if name == "omega" {
                args.push(null(Vec::new()));
            }
            Syntax::node(parser_kind(&["Tactic", name]), args)
        })
        .collect();
    sequence(vec![
        Syntax::node(
            parser_kind(&["Tactic", "tacticTry_"]),
            vec![atom("try"), sequence(vec![simp])],
        ),
        lexicographic_constructors("Prod"),
        lexicographic_constructors("PSigma"),
        first(alternatives),
    ])
}

impl Context {
    /// Matcher branches may replace the private continuation with a binder
    /// whose domain mentions the constructor. Its private name survives that
    /// telescope, while its FVar identity and type belong to the active branch.
    pub(in crate::source) fn well_founded_continuation(&self) -> Option<LocalDecl> {
        let state = self.well_founded.as_ref().filter(|state| !state.proving)?;
        self.txn
            .lctx
            .find_by_user_name(&state.continuation.user_name)
            .cloned()
    }

    /// Pattern matrices evaluate their inputs in checked, unspellable lets.
    /// Follow those aliases only: matching a genuine `saved := n` must not
    /// identify its branch input with n in a decreasing obligation.
    pub(in crate::source) fn well_founded_match_input(
        &mut self,
        mut input: Typed,
    ) -> Result<Typed, NatDefinitionElabError> {
        let mut visited = HashSet::new();
        while let ExprNode::FVar { id } = input.value.node() {
            self.tick()?;
            if !visited.insert(id.clone()) {
                return Err(failure(SourceInferenceError::Scope));
            }
            let Some(local) = self.txn.lctx.find(id) else {
                break;
            };
            if !local.user_name.parent().is_anonymous()
                || !matches!(
                    local.user_name.leaf_view(),
                    fln_core::name::LeafView::Num(_)
                )
            {
                break;
            }
            let Some(value) = &local.value else {
                break;
            };
            let ExprNode::FVar { id } = value.node() else {
                break;
            };
            let original = self
                .txn
                .lctx
                .find(id)
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            input = Typed {
                value: value.clone(),
                type_: original.type_.clone(),
            };
        }
        Ok(input)
    }

    /// Cached calls may still reference the ambient telescope, but the source
    /// branch sees the specialized hypotheses only. Hide old declarations by
    /// private names while retaining their FVar identities for those captures.
    /// Restoring the match's saved local context restores the original names.
    pub(in crate::source) fn hide_well_founded_match_locals(
        &mut self,
        generalized: &[LocalDecl],
    ) -> Result<bool, NatDefinitionElabError> {
        if self.well_founded_continuation().is_none() {
            return Ok(false);
        }
        let candidates: HashSet<_> = generalized.iter().map(|local| local.id.clone()).collect();
        let mut locals = LocalContext::new();
        let mut hidden = Vec::new();
        for mut local in self.txn.lctx.clone().decls().iter().cloned() {
            self.tick()?;
            if candidates.contains(&local.id) {
                local.user_name = self.fresh_name()?;
                hidden.push(local.user_name.clone());
            }
            tactics::eliminate::add_local(&mut locals, &local);
        }
        self.txn.lctx = locals;
        self.well_founded
            .as_mut()
            .expect("active match continuation")
            .proof_hidden
            .extend(hidden);
        Ok(true)
    }

    fn well_founded_measure(
        &mut self,
        hint: &Hint<'_>,
        parameters: &[LocalDecl],
        header_parameters: usize,
    ) -> Result<Typed, NatDefinitionElabError> {
        if let Some(index) = hint.inferred {
            return parameters
                .get(index)
                .map(|parameter| Typed {
                    value: Expr::fvar(parameter.id.clone()),
                    type_: parameter.type_.clone(),
                })
                .ok_or_else(|| failure(SourceInferenceError::Scope));
        }
        let syntax = hint
            .measure
            .ok_or_else(|| error(RecursionError::WellFoundedMeasureRequired))?;
        let extra = parameters
            .get(header_parameters..)
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        if hint.aliases.len() > extra.len() {
            return Err(error(RecursionError::TerminationBinderCount {
                bound: hint.aliases.len(),
                available: extra.len(),
            }));
        }
        let saved = self.txn.lctx.clone();
        let defining = self.defining.take();
        let mut locals = LocalContext::new();
        for local in saved.decls() {
            self.tick()?;
            let mut local = local.clone();
            if let Some(index) = extra.iter().position(|extra| extra.id == local.id) {
                let Some(alias) = hint.aliases.get(index) else {
                    continue;
                };
                local.user_name = alias.clone().unwrap_or_else(Name::anonymous);
            }
            tactics::eliminate::add_local(&mut locals, &local);
        }
        self.txn.lctx = locals;
        let result = (|| {
            let term = self.term(syntax, None)?;
            self.resolve_instances_with_defaults()?;
            let term = self.finish_open_universes(term)?;
            // An arbitrary measure is checked as source, including unused let
            // initializers and annotations; it is also retained in the final
            // fixpoint application for both admission engines to validate.
            Ok(term)
        })();
        self.txn.lctx = saved;
        self.defining = defining;
        result
    }

    pub(in crate::source) fn well_founded_body(
        &mut self,
        name: &Name,
        parameters: &[LocalDecl],
        syntax: &Syntax,
        expected: Option<Expr>,
        hint: &Hint<'_>,
        header_parameters: usize,
    ) -> Result<Typed, NatDefinitionElabError> {
        if hint.measure.is_some() {
            return match self.well_founded_selected_body(
                name,
                parameters,
                syntax,
                expected,
                hint,
                header_parameters,
            )? {
                Attempt::Complete(value) => Ok(value),
                Attempt::SelectedFailure(problem) => Err(problem),
                Attempt::Repack(_) => Err(failure(SourceInferenceError::Scope)),
            };
        }
        // Automatic inference remains the direct-Nat slice. Explicit measures
        // select their own dictionary after their actual type is elaborated.
        if !self.native_nat_well_founded_relation()? {
            return Err(error(RecursionError::WellFoundedRelationUnsupported));
        }
        // GuessLex walks the varying parameter telescope in order. This slice
        // supports direct Nat measures; fixed positions are discarded after
        // typed call analysis, before any decreasing proof is attempted.
        let mut candidates = Vec::new();
        for (index, parameter) in parameters.iter().enumerate() {
            self.tick()?;
            let type_ = self.reduce_source_head(
                &parameter.type_,
                UnificationTransparency::Abbreviations,
                true,
            )?;
            if matches!(type_.node(), ExprNode::Const { name, levels }
                if name == &Name::from_components(["Nat"]) && levels.is_empty())
                && self.native_nat_size_measure(parameter)?
            {
                candidates.push(index);
            }
        }
        if candidates.is_empty() {
            return Err(error(RecursionError::WellFoundedMeasureRequired));
        }
        let snapshot = self.clone();
        let mut first_error = None;
        for index in candidates {
            self.tick()?;
            let selected = Hint {
                aliases: Vec::new(),
                measure: None,
                decreasing: hint.decreasing,
                inferred: Some(index),
            };
            let result = self.well_founded_selected_body(
                name,
                parameters,
                syntax,
                expected.clone(),
                &selected,
                header_parameters,
            );
            let problem = match result {
                Ok(Attempt::Complete(value)) => return Ok(value),
                Ok(Attempt::SelectedFailure(problem)) => return Err(problem),
                Ok(Attempt::Repack(_)) => return Err(failure(SourceInferenceError::Scope)),
                Err(problem) => problem,
            };
            let spent = self.txn.budget.heartbeats_consumed;
            *self = snapshot.clone();
            self.txn.budget.heartbeats_consumed = spent;
            if !tactics::backtrack::recoverable(&problem) {
                return Err(problem);
            }
            if !matches!(
                &problem,
                NatDefinitionElabError::Inference(SourceInferenceError::Recursion(
                    RecursionError::WellFoundedMeasureSearchFailed
                ))
            ) {
                first_error.get_or_insert(problem);
            }
        }
        Err(first_error.unwrap_or_else(|| error(RecursionError::WellFoundedMeasureSearchFailed)))
    }

    /// Ordinary scoped instance search honors local dictionaries and user
    /// instances. These probes retain consumed work but publish no assignments.
    fn native_nat_well_founded_relation(&mut self) -> Result<bool, NatDefinitionElabError> {
        let mut trial = self.clone();
        let result = (|| {
            let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
            let target = Expr::app(
                Expr::const_(
                    Name::from_components(["WellFoundedRelation"]),
                    vec![Level::one()],
                ),
                nat.clone(),
            );
            let Some(dictionary) = trial.coercion_instance(target)? else {
                return Ok(false);
            };
            let mut actual = Expr::proj(
                Name::from_components(["WellFoundedRelation"]),
                0,
                dictionary,
            );
            let mut expected = Expr::const_(Name::from_components(["Nat", "lt"]), Vec::new());
            for _ in 0..2 {
                trial.tick()?;
                let id = FVarId(trial.fresh_name()?);
                trial.txn.lctx.add_param(
                    id.clone(),
                    Name::anonymous(),
                    nat.clone(),
                    BinderInfo::Default,
                );
                let argument = Expr::fvar(id);
                actual = Expr::app(actual, argument.clone());
                expected = Expr::app(expected, argument);
            }
            let actual =
                trial.reduce_source_head(&actual, UnificationTransparency::Default, true)?;
            let expected =
                trial.reduce_source_head(&expected, UnificationTransparency::Default, true)?;
            trial.well_founded_default_conversion(&actual, &expected)
        })();
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        result
    }

    fn native_nat_size_measure(
        &mut self,
        parameter: &LocalDecl,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut trial = self.clone();
        let result = (|| {
            let target = Expr::app(
                Expr::const_(Name::from_components(["SizeOf"]), vec![Level::one()]),
                Expr::const_(Name::from_components(["Nat"]), Vec::new()),
            );
            let Some(dictionary) = trial.coercion_instance(target)? else {
                return Ok(false);
            };
            let parameter = Expr::fvar(parameter.id.clone());
            let size = Expr::app(
                Expr::proj(Name::from_components(["SizeOf"]), 0, dictionary),
                parameter.clone(),
            );
            let size = trial.reduce_source_head(&size, UnificationTransparency::Default, true)?;
            trial.well_founded_default_conversion(&size, &parameter)
        })();
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        result
    }

    fn well_founded_selected_body(
        &mut self,
        name: &Name,
        parameters: &[LocalDecl],
        syntax: &Syntax,
        expected: Option<Expr>,
        hint: &Hint<'_>,
        header_parameters: usize,
    ) -> Result<Attempt, NatDefinitionElabError> {
        let measure = self.well_founded_measure(hint, parameters, header_parameters)?;
        let measure = self.select_well_founded_relation(measure, parameters)?;
        let snapshot = self.clone();
        let mut varying: Vec<_> = (0..parameters.len())
            .filter(|index| !measure.captures.contains(index))
            .collect();
        loop {
            let result = self.well_founded_attempt(
                name,
                parameters,
                &varying,
                (syntax, expected.clone()),
                (hint, &measure),
                header_parameters,
            )?;
            match result {
                result @ (Attempt::Complete(_) | Attempt::SelectedFailure(_)) => return Ok(result),
                Attempt::Repack(next) => {
                    // A typed call analysis can only remove fixed positions.
                    // Retry from the complete checkpoint without refunding
                    // the work spent discovering this smaller telescope.
                    if next.len() >= varying.len()
                        || next.iter().any(|index| !varying.contains(index))
                    {
                        return Err(failure(SourceInferenceError::Scope));
                    }
                    let spent = self.txn.budget.heartbeats_consumed;
                    *self = snapshot.clone();
                    self.txn.budget.heartbeats_consumed = spent;
                    varying = next;
                }
            }
        }
    }

    fn well_founded_attempt(
        &mut self,
        name: &Name,
        parameters: &[LocalDecl],
        varying: &[usize],
        (syntax, expected): (&Syntax, Option<Expr>),
        (hint, measure): (&Hint<'_>, &relation::Measure),
        header_parameters: usize,
    ) -> Result<Attempt, NatDefinitionElabError> {
        let expected = expected.ok_or_else(|| error(RecursionError::ResultTypeRequired))?;
        if varying.is_empty() {
            return Err(error(RecursionError::WellFoundedArgumentRequired));
        }
        let varying_parameters: Vec<_> = varying
            .iter()
            .map(|index| parameters[*index].clone())
            .collect();
        if self.well_founded.is_some() {
            return Err(error(RecursionError::WellFoundedArgumentRequired));
        }
        let saved = self.txn.lctx.clone();
        let domain = self.well_founded_domain(&varying_parameters)?;
        let motive = self.well_founded_motive(&varying_parameters, &domain, &expected)?;
        let measure_fn =
            self.uncurry_well_founded_value(&varying_parameters, measure.value.clone())?;
        let current_arguments: Vec<_> = varying_parameters
            .iter()
            .map(|parameter| Expr::fvar(parameter.id.clone()))
            .collect();
        let current = self.pack_well_founded_arguments(&domain, &current_arguments)?;
        let fix = self.well_founded_fix(domain, motive, measure_fn.value, measure)?;
        let fix_type = self.whnf(&fix.type_)?;
        let ExprNode::ForallE {
            binder_type: functional_type,
            ..
        } = fix_type.node()
        else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        let functional_type = self.whnf(functional_type)?;
        let ExprNode::ForallE { body, .. } = functional_type.node() else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        let at_major = self.substitute(body, &current.value)?;
        let at_major = self.whnf(&at_major)?;
        let ExprNode::ForallE {
            binder_type: continuation_type,
            ..
        } = at_major.node()
        else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        let continuation_name = self.fresh_name()?;
        let continuation_id = FVarId(continuation_name.clone());
        self.txn.lctx.add_param(
            continuation_id.clone(),
            continuation_name,
            continuation_type.clone(),
            BinderInfo::Default,
        );
        let continuation = self
            .txn
            .lctx
            .find(&continuation_id)
            .expect("inserted well-founded continuation")
            .clone();
        let mut reference_type = expected.clone();
        for local in parameters.iter().rev() {
            self.tick()?;
            reference_type = Expr::forall_e(
                local.user_name.clone(),
                self.instantiate(&local.type_)?,
                reference_type
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                local.binder_info,
            );
        }
        let marker = FVarId(self.fresh_name()?);
        self.txn.lctx.add_param(
            marker.clone(),
            Name::anonymous(),
            reference_type.clone(),
            BinderInfo::Default,
        );
        self.well_founded = Some(State {
            name: name.clone(),
            reference: Typed {
                value: Expr::fvar(marker.clone()),
                type_: reference_type,
            },
            marker: marker.clone(),
            parameters: parameters.to_vec(),
            varying: varying.to_vec(),
            fixed: parameters
                .iter()
                .enumerate()
                .filter(|(index, _)| !varying.contains(index))
                .map(|(index, parameter)| (index, parameter.clone()))
                .collect(),
            measure_captures: measure.captures.clone(),
            natural_measure: measure.natural,
            continuation: continuation.clone(),
            proof_inaccessible: parameters[header_parameters..]
                .iter()
                .map(|parameter| parameter.id.clone())
                .collect(),
            proof_hidden: HashSet::new(),
            branch_scopes: Vec::new(),
            calls: HashMap::new(),
            goals: Vec::new(),
            proving: false,
        });
        let result = (|| {
            let term = self.term(syntax, Some(expected.clone()))?;
            self.resolve_instances_with_defaults()?;
            self.resume_postponed_eliminators(true)?;
            self.flush(true)?;
            self.complete_local_functions()?;
            let value = self.instantiate(&term.value)?;
            if self.elimination_reads(&value)?.contains(&marker) {
                return Err(error(RecursionError::PartialApplication));
            }
            let live = self.txn.mvars.collect_mvars(&value);
            let obligations: Vec<_> = self
                .well_founded
                .as_ref()
                .expect("active well-founded definition")
                .goals
                .iter()
                .filter(|obligation| live.contains(&obligation.transport))
                .cloned()
                .collect();
            let actual_varying = self.well_founded_varying_parameters(parameters, &obligations)?;
            if actual_varying.is_empty() {
                return Err(error(RecursionError::WellFoundedArgumentRequired));
            }
            if actual_varying != varying {
                return Ok(Attempt::Repack(actual_varying));
            }
            if let Some(index) = hint.inferred {
                if !varying.contains(&index) {
                    return Err(error(RecursionError::WellFoundedMeasureSearchFailed));
                }
                if hint.decreasing.is_some() {
                    // A supplied script can behave differently during single
                    // call inference and its final aggregate run. Do not skip
                    // an earlier unsupported SizeOf candidate which the pin
                    // might select before this Nat measure.
                    for &prior in varying.iter().filter(|prior| **prior < index) {
                        self.tick()?;
                        let type_ = self.reduce_source_head(
                            &parameters[prior].type_,
                            UnificationTransparency::Abbreviations,
                            true,
                        )?;
                        if !matches!(type_.node(), ExprNode::Const { name, levels }
                            if name == &Name::from_components(["Nat"]) && levels.is_empty())
                        {
                            return Ok(Attempt::SelectedFailure(error(
                                RecursionError::WellFoundedMeasureOrderUnsupported,
                            )));
                        }
                    }
                }
            }
            if !obligations.is_empty() {
                self.well_founded
                    .as_mut()
                    .expect("active well-founded proof")
                    .proving = true;
                let goals = self.prepare_decreasing_goals(&obligations)?;
                let automatic;
                let proof = match hint.decreasing {
                    Some(proof) => proof,
                    None => {
                        automatic = automatic_decreasing_proof();
                        &automatic
                    }
                };
                let prepared = self.lower_pattern_matrices(proof)?;
                if hint.inferred.is_some()
                    && !self.single_direct_measure(parameters, varying, &obligations)?
                {
                    match self.check_inferred_measure(&prepared, &goals)? {
                        MeasureProbe::Strict => {}
                        MeasureProbe::Unusable(problem) => return Err(problem),
                        MeasureProbe::Lexicographic => {
                            return Ok(Attempt::SelectedFailure(error(
                                RecursionError::WellFoundedMeasureOrderUnsupported,
                            )));
                        }
                    }
                }
                let proof_result = (|| {
                    // Final cleanup has already inspected the raw InvImage.
                    // Only now expose measure operands and local let values.
                    let goals = self.normalize_decreasing_goals(goals)?;
                    if hint.decreasing.is_some() {
                        // The user's final script sees all obligations in the
                        // original order, after inference has selected a measure.
                        let state = self.start_decreasing_proof(&prepared, goals)?;
                        self.run_decreasing_proof(&prepared, state)?;
                    } else {
                        for goal in goals {
                            self.tick()?;
                            let state = self.start_decreasing_proof(&prepared, vec![goal])?;
                            self.run_decreasing_proof(&prepared, state)?;
                        }
                    }
                    Ok::<_, NatDefinitionElabError>(())
                })();
                if let Err(problem) = proof_result {
                    return Ok(Attempt::SelectedFailure(problem));
                }
                for obligation in obligations {
                    self.tick()?;
                    let proof = self.instantiate(&Expr::mvar(obligation.goal.id))?;
                    self.require_resolved_terms(std::slice::from_ref(&proof))?;
                    let closed =
                        self.close_decreasing_capture(proof, &obligation.captures, true)?;
                    self.txn
                        .mvars
                        .assign(
                            obligation.transport,
                            closed,
                            AssignmentJustification::UserGiven,
                        )
                        .map_err(|_| failure(SourceInferenceError::Scope))?;
                }
            }
            let mut value = self.instantiate(&value)?;
            self.require_resolved_terms(std::slice::from_ref(&value))?;
            value = Expr::lam(
                continuation.user_name.clone(),
                self.instantiate(&continuation.type_)?,
                value
                    .abstract_fvar(&continuation.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                BinderInfo::Default,
            );
            let type_ = self
                .known_type(&value)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            let functional =
                self.uncurry_well_founded_value(&varying_parameters, Typed { value, type_ })?;
            let fixed = self.match_apply(fix, functional)?;
            self.match_apply(fixed, current).map(Attempt::Complete)
        })();
        self.well_founded = None;
        self.txn.lctx = saved;
        if matches!(&result, Ok(Attempt::Complete(_))) {
            self.well_founded_definition = true;
        }
        result
    }

    /// GuessLex's singleton shortcut counts every SizeOf and complex measure.
    /// Prove that precondition only for one varying Nat, with positive Nat
    /// comparisons whose left sides are fixed and right sides are parameters.
    /// Other contexts conservatively require per-call inference. Inspect the
    /// original call contexts: cleanup may discard a fixed-parameter comparison
    /// that still contributes a complex measure to the pin's candidate set.
    fn single_direct_measure(
        &mut self,
        parameters: &[LocalDecl],
        varying: &[usize],
        obligations: &[Obligation],
    ) -> Result<bool, NatDefinitionElabError> {
        if varying.len() != 1 {
            return Ok(false);
        }
        let original: HashSet<_> = parameters
            .iter()
            .map(|parameter| parameter.id.clone())
            .collect();
        let varying = &parameters[varying[0]].id;
        let saved = self.txn.lctx.clone();
        let result = (|| {
            for obligation in obligations {
                let goal = &obligation.goal;
                self.txn.lctx = goal.lctx.clone();
                for local in goal.lctx.decls() {
                    self.tick()?;
                    let Some(sort) = self.known_type(&local.type_)? else {
                        return Ok(false);
                    };
                    let sort = self.whnf(&sort)?;
                    if !matches!(sort.node(), ExprNode::Sort { level } if level == &Level::zero()) {
                        continue;
                    }
                    let type_ = self.instantiate(&local.type_)?;
                    let (head, arguments) = operators::spine(&type_);
                    let ExprNode::Const { name, .. } = head.node() else {
                        return Ok(false);
                    };
                    let (left, right) = if (name == &Name::from_components(["Nat", "lt"])
                        || name == &Name::from_components(["Nat", "le"]))
                        && arguments.len() == 2
                    {
                        (&arguments[0], &arguments[1])
                    } else if (name == &Name::from_components(["LT", "lt"])
                        || name == &Name::from_components(["LE", "le"]))
                        && arguments.len() == 4
                    {
                        let domain = self.reduce_source_head(
                            &arguments[0],
                            UnificationTransparency::Abbreviations,
                            true,
                        )?;
                        if !matches!(domain.node(), ExprNode::Const { name, levels }
                            if name == &Name::from_components(["Nat"]) && levels.is_empty())
                        {
                            return Ok(false);
                        }
                        (&arguments[2], &arguments[3])
                    } else {
                        return Ok(false);
                    };
                    let ExprNode::FVar { id } = right.node() else {
                        return Ok(false);
                    };
                    let reads = self.elimination_reads(left)?;
                    if !original.contains(id)
                        || reads.contains(varying)
                        || !reads.is_subset(&original)
                    {
                        return Ok(false);
                    }
                }
            }
            Ok(true)
        })();
        self.txn.lctx = saved;
        result
    }

    /// The pin tries equality, then the supplied/default proof for < and <=.
    /// A candidate with some strict and some weak calls is an earlier viable
    /// lexicographic prefix. Do not silently skip it for a later Nat measure.
    fn check_inferred_measure(
        &mut self,
        proof: &Syntax,
        goals: &[tactics::ProofGoal],
    ) -> Result<MeasureProbe, NatDefinitionElabError> {
        let mut strict = 0usize;
        for goal in goals {
            self.tick()?;
            let mut trial = self.clone();
            trial.txn.lctx = goal.lctx.clone();
            // BasicMeasure.beta has already removed the argument pack before
            // the pin creates this comparison. Keep user let identities until
            // cleanup, but remove our equivalent beta/iota/projection redexes.
            let target = trial.reduce_decreasing_comparison(&goal.target, false);
            self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
            let target = target?;
            let (head, arguments) = operators::spine(&target);
            if !matches!(head.node(), ExprNode::Const { name, .. }
                if name == &Name::from_components(["Nat", "lt"]))
                || arguments.len() != 2
            {
                return Err(failure(SourceInferenceError::Scope));
            }
            let equal = trial.well_founded_default_conversion(&arguments[0], &arguments[1]);
            self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
            if equal? {
                continue;
            }
            let problem = match self.probe_inferred_goal(proof, goal, target) {
                Ok(()) => {
                    strict += 1;
                    continue;
                }
                Err(problem) if !tactics::backtrack::recoverable(&problem) => return Err(problem),
                Err(problem) => problem,
            };
            let le = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_components(["Nat", "le"]), Vec::new()),
                    arguments[0].clone(),
                ),
                arguments[1].clone(),
            );
            match self.probe_inferred_goal(proof, goal, le) {
                Ok(()) => {}
                Err(stopped) if !tactics::backtrack::recoverable(&stopped) => return Err(stopped),
                Err(_) => return Ok(MeasureProbe::Unusable(problem)),
            }
        }
        if strict == goals.len() {
            Ok(MeasureProbe::Strict)
        } else if strict > 0 {
            Ok(MeasureProbe::Lexicographic)
        } else {
            Ok(MeasureProbe::Unusable(error(
                RecursionError::WellFoundedMeasureSearchFailed,
            )))
        }
    }

    /// GuessLex cleans a direct Nat comparison, not the later packed InvImage.
    /// Fresh goals prevent a <= probe from retyping the existing < metavariable.
    /// Every probe restores all semantic state while retaining spent work.
    fn probe_inferred_goal(
        &mut self,
        proof: &Syntax,
        goal: &tactics::ProofGoal,
        target: Expr,
    ) -> Result<(), NatDefinitionElabError> {
        let snapshot = self.clone();
        let result = (|| {
            let locals = self.clean_decreasing_context(&goal.lctx, &target)?;
            self.txn.lctx = locals.clone();
            let target = self.reduce_decreasing_comparison(&target, true)?;
            let name = self.fresh_name()?;
            let id = MVarId(name.clone());
            self.txn.mvars.declare(
                id.clone(),
                name,
                target.clone(),
                locals.clone(),
                MetavarKind::SyntheticOpaque,
                0,
                None,
            );
            let fresh = tactics::ProofGoal {
                id,
                target,
                lctx: locals,
                introduced: Vec::new(),
            };
            let state = self.start_decreasing_proof(proof, vec![fresh])?;
            self.run_decreasing_proof(proof, state).map(|_| ())
        })();
        let spent = self.txn.budget.heartbeats_consumed;
        *self = snapshot;
        self.txn.budget.heartbeats_consumed = spent;
        result
    }

    /// Expose the checked argument-pack redexes without unfolding ordinary
    /// arithmetic definitions. Inference retains local let identities until
    /// cleanup; the subsequent clean_wf stage can unfold their head values.
    fn reduce_decreasing_comparison(
        &mut self,
        target: &Expr,
        zeta_delta: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        let (head, arguments) = operators::spine(target);
        let Some((current, prefix)) = arguments.split_last() else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let Some((smaller, relation_arguments)) = prefix.split_last() else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let mut relation = head;
        for argument in relation_arguments {
            self.tick()?;
            relation = Expr::app(relation, argument.clone());
        }
        if zeta_delta {
            relation = self.clean_decreasing_relation(&relation)?;
        }
        let smaller = self.reduce_decreasing_operand(smaller, zeta_delta)?;
        let current = self.reduce_decreasing_operand(current, zeta_delta)?;
        Ok(Expr::app(Expr::app(relation, smaller), current))
    }

    fn reduce_decreasing_operand(
        &mut self,
        operand: &Expr,
        clean: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut value = self.reduce_source_head(operand, UnificationTransparency::None, clean)?;
        // The pin's simp-based clean_wf reduces ordinary structure projections
        // only when their receiver exposes a constructor. This comes after
        // cleanup: inference's beta reduction must retain source dependencies.
        if clean {
            while let Some(field) = self.clean_decreasing_projection(&value)? {
                value = self.reduce_source_head(&field, UnificationTransparency::None, true)?;
            }
        }
        Ok(value)
    }

    /// A generated, reducible non-class field on an actual constructor. Keep
    /// stuck projections in their original spelling, so e.g. Prod.fst p remains
    /// the same arithmetic atom in the goal and an existing hypothesis.
    fn clean_decreasing_projection(
        &mut self,
        value: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        self.tick()?;
        let (head, arguments) = operators::spine(value);
        let ExprNode::Const { name, levels } = head.node() else {
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
        let reducible = crate::reducibility::table(&self.txn.env)
            .map_err(|problem| {
                failure(SourceInferenceError::Unification(Box::new(
                    UnificationError::Reducibility(problem),
                )))
            })?
            .get(name)
            .map_or(definition.hints == ReducibilityHints::Abbrev, |status| {
                status == crate::reducibility::Reducibility::Reducible
            });
        if !reducible {
            return Ok(None);
        }
        let mut body = &definition.value;
        let mut binders = 0usize;
        let mut receiver = BinderInfo::Default;
        while let ExprNode::Lam {
            body: next,
            binder_info,
            ..
        } = body.node()
        {
            self.tick()?;
            binders = binders
                .checked_add(1)
                .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
            receiver = *binder_info;
            body = next;
        }
        let ExprNode::Proj {
            struct_name,
            idx,
            expr,
        } = body.node()
        else {
            return Ok(None);
        };
        if receiver != BinderInfo::Default || !matches!(expr.node(), ExprNode::BVar { idx: 0 }) {
            return Ok(None);
        }
        let env = self.txn.env.clone();
        let Some(ConstantInfo::Induct(family)) = env.find(struct_name) else {
            return Ok(None);
        };
        let Ok(parameters) = usize::try_from(family.num_params) else {
            return Ok(None);
        };
        if family.is_unsafe
            || family.num_indices != 0
            || family.ctors.len() != 1
            || parameters.checked_add(1) != Some(binders)
            || arguments.len() < binders
            || definition.base.level_params != family.base.level_params
        {
            return Ok(None);
        }
        let Some(ConstantInfo::Ctor(constructor)) = env.find(&family.ctors[0]) else {
            return Ok(None);
        };
        if constructor.is_unsafe
            || &constructor.induct != struct_name
            || constructor.num_params != family.num_params
            || constructor.base.level_params != family.base.level_params
            || *idx >= u64::from(constructor.num_fields)
        {
            return Ok(None);
        }
        let mut field_type = &constructor.base.type_;
        for _ in 0..u64::from(family.num_params) + *idx {
            self.tick()?;
            let ExprNode::ForallE { body, .. } = field_type.node() else {
                return Ok(None);
            };
            field_type = body;
        }
        let ExprNode::ForallE { binder_name, .. } = field_type.node() else {
            return Ok(None);
        };
        if definition.base.name != struct_name.append_core(binder_name) {
            return Ok(None);
        }
        let receiver =
            self.reduce_source_head(&arguments[parameters], UnificationTransparency::None, true)?;
        let (constructor, mut fields) = operators::spine(&receiver);
        fields.reverse();
        let Some(mut field) =
            crate::records::constructor_field(&env, struct_name, *idx, &constructor, &fields)
        else {
            return Ok(None);
        };
        for argument in arguments.into_iter().skip(binders) {
            self.tick()?;
            field = Expr::app(field, argument);
        }
        Ok(Some(field))
    }

    /// Final goals retain the context selected from raw InvImage dependencies.
    /// Normalization changes only the displayed comparison; assignment checks
    /// and final admission still validate the original obligation and captures.
    fn normalize_decreasing_goals(
        &mut self,
        mut goals: Vec<tactics::ProofGoal>,
    ) -> Result<Vec<tactics::ProofGoal>, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = (|| {
            for goal in &mut goals {
                self.tick()?;
                self.txn.lctx = goal.lctx.clone();
                goal.target = self.reduce_decreasing_comparison(&goal.target, true)?;
            }
            Ok(goals)
        })();
        self.txn.lctx = saved;
        result
    }

    /// GuessLex compares instances and tries reflexivity at default transparency.
    /// A conversion failure is a negative answer; internal/resource stops are not.
    fn well_founded_default_conversion(
        &mut self,
        left: &Expr,
        right: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        self.flush(false)?;
        let mut budget = UnificationBudget::new(self.kernel);
        budget.transparency = UnificationTransparency::Default;
        match self.txn.unify(left, right, budget) {
            Ok(report) => {
                assert!(report.awakened.is_empty(), "private source queue");
                Ok(true)
            }
            Err(UnificationError::Deferred(reason))
                if !matches!(
                    reason,
                    crate::constraint::unify::UnificationDeferred::InvalidLocalContext
                        | crate::constraint::unify::UnificationDeferred::UnknownMetavariable(_)
                ) =>
            {
                Ok(false)
            }
            Err(UnificationError::AssignmentCheck { outcome, .. })
                if matches!(*outcome, Outcome::Complete(Verdict::Rejected { .. })) =>
            {
                Ok(false)
            }
            Err(problem) => Err(failure(SourceInferenceError::Unification(Box::new(
                problem,
            )))),
        }
    }

    fn fixed_argument_conversion(
        &mut self,
        left: &Expr,
        right: &Expr,
        proof_irrelevance: bool,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut budget = UnificationBudget::new(self.kernel);
        budget.proof_irrelevance = proof_irrelevance;
        match self.txn.unify(left, right, budget) {
            Ok(report) => {
                assert!(report.awakened.is_empty(), "private source queue");
                Ok(true)
            }
            Err(UnificationError::Deferred(_)) => Ok(false),
            Err(UnificationError::AssignmentCheck { outcome, .. })
                if matches!(
                    *outcome,
                    Outcome::Complete(fln_kernel::verdict::Verdict::Rejected { .. })
                ) =>
            {
                Ok(false)
            }
            Err(problem) => Err(failure(SourceInferenceError::Unification(Box::new(
                problem,
            )))),
        }
    }

    /// The pin retains unitlike eta even under `withoutProofIrrelevance`.
    /// The admitted family must have exactly one nullary constructor, and the
    /// actual parameterized types must still compare at reducible transparency.
    fn fixed_unitlike_argument(
        &mut self,
        argument: &Expr,
        parameter: &LocalDecl,
    ) -> Result<bool, NatDefinitionElabError> {
        let domain = self.reduce_source_head(
            &parameter.type_,
            UnificationTransparency::Abbreviations,
            true,
        )?;
        let (head, arguments) = operators::spine(&domain);
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(false);
        };
        self.tick()?;
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(name) else {
            return Ok(false);
        };
        if family.is_unsafe
            || family.is_rec
            || family.is_reflexive
            || family.num_indices != 0
            || family.num_nested != 0
            || family.all.len() != 1
            || family.all.first() != Some(name)
            || family.ctors.len() != 1
            || levels.len() != family.base.level_params.len()
            || u32::try_from(arguments.len()).ok() != Some(family.num_params)
        {
            return Ok(false);
        }
        let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(&family.ctors[0]) else {
            return Ok(false);
        };
        if constructor.is_unsafe
            || constructor.cidx != 0
            || &constructor.induct != name
            || constructor.num_params != family.num_params
            || constructor.num_fields != 0
            || constructor.base.level_params != family.base.level_params
        {
            return Ok(false);
        }
        let type_ = self
            .known_type(argument)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        if self.fixed_argument_conversion(&domain, &type_, false)? {
            return Ok(true);
        }
        if self.fixed_argument_conversion(&domain, &type_, true)? {
            return Err(error(RecursionError::FixedArgumentConversionUnsupported));
        }
        Ok(false)
    }

    fn fixed_well_founded_argument(
        &mut self,
        argument: &Expr,
        parameter: &LocalDecl,
    ) -> Result<bool, NatDefinitionElabError> {
        self.flush(false)?;
        let argument =
            self.reduce_source_head(argument, UnificationTransparency::Abbreviations, true)?;
        let original = Expr::fvar(parameter.id.clone());
        if self.fixed_recursive_argument(&argument, parameter)?
            || self.fixed_argument_conversion(&original, &argument, false)?
            || self.fixed_unitlike_argument(&argument, parameter)?
        {
            return Ok(true);
        }
        // The pin has additional proof-field and implicit-proof-argument
        // rules even with direct proof irrelevance disabled. Until those
        // rungs are available, do not mistake a missing conversion for a
        // varying argument and expose extra locals to decreasing_by.
        if self.fixed_argument_conversion(&original, &argument, true)? {
            return Err(error(RecursionError::FixedArgumentConversionUnsupported));
        }
        Ok(false)
    }

    /// Single-function `FixedParams`: inspect the typed recursive arguments,
    /// then propagate variation through parameter-type dependencies. Analysis
    /// precedes decreasing tactics, so packing cannot change their local scope.
    fn well_founded_varying_parameters(
        &mut self,
        parameters: &[LocalDecl],
        obligations: &[Obligation],
    ) -> Result<Vec<usize>, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let mut varying = vec![false; parameters.len()];
            for obligation in obligations {
                self.txn.lctx = obligation.goal.lctx.clone();
                for (index, parameter) in parameters.iter().enumerate() {
                    self.tick()?;
                    if varying[index] {
                        continue;
                    }
                    varying[index] = !self
                        .fixed_well_founded_argument(&obligation.arguments[index], parameter)?;
                }
            }
            self.txn.lctx = saved.clone();
            let mut changed = true;
            while changed {
                changed = false;
                for (index, parameter) in parameters.iter().enumerate() {
                    self.tick()?;
                    if varying[index] {
                        continue;
                    }
                    let dependencies = self.elimination_reads(&parameter.type_)?;
                    if parameters.iter().enumerate().any(|(earlier, parameter)| {
                        varying[earlier] && dependencies.contains(&parameter.id)
                    }) {
                        varying[index] = true;
                        changed = true;
                    }
                }
            }
            Ok(varying
                .into_iter()
                .enumerate()
                .filter_map(|(index, changes)| changes.then_some(index))
                .collect())
        })();
        self.txn.lctx = saved;
        result
    }

    fn add_decreasing_dependencies(
        &mut self,
        locals: &LocalContext,
        used: &mut HashSet<FVarId>,
        roots: impl IntoIterator<Item = FVarId>,
    ) -> Result<(), NatDefinitionElabError> {
        let mut pending: Vec<_> = roots.into_iter().collect();
        while let Some(id) = pending.pop() {
            self.tick()?;
            if !used.insert(id.clone()) {
                continue;
            }
            let local = locals
                .find(&id)
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            pending.extend(self.elimination_reads(&local.type_)?);
            if let Some(value) = &local.value {
                pending.extend(self.elimination_reads(value)?);
            }
        }
        Ok(())
    }

    /// `MVarId.cleanup` runs before `clean_wf`: preserve the raw relation's
    /// dependencies, then the propositions and let values depending on them.
    /// In particular, unrelated hypotheses are not proof-script parameters.
    fn clean_decreasing_context(
        &mut self,
        locals: &LocalContext,
        raw_target: &Expr,
    ) -> Result<LocalContext, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        self.txn.lctx = locals.clone();
        let result = (|| {
            let mut used = HashSet::new();
            let roots = self.elimination_reads(raw_target)?;
            self.add_decreasing_dependencies(locals, &mut used, roots)?;
            loop {
                let before = used.len();
                for local in locals.decls() {
                    self.tick()?;
                    if used.contains(&local.id) {
                        continue;
                    }
                    let mut retain = if let Some(value) = &local.value {
                        !self.elimination_reads(value)?.is_disjoint(&used)
                    } else {
                        false
                    };
                    if !retain && !self.elimination_reads(&local.type_)?.is_disjoint(&used) {
                        let type_type = self
                            .known_type(&local.type_)?
                            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
                        retain = matches!(
                            self.whnf(&type_type)?.node(),
                            ExprNode::Sort { level } if level == &Level::zero()
                        );
                    }
                    if retain {
                        self.add_decreasing_dependencies(
                            locals,
                            &mut used,
                            std::iter::once(local.id.clone()),
                        )?;
                    }
                }
                if used.len() == before {
                    break;
                }
            }
            let mut cleaned = LocalContext::new();
            for local in locals.decls() {
                self.tick()?;
                if used.contains(&local.id) {
                    tactics::eliminate::add_local(&mut cleaned, local);
                }
            }
            Ok(cleaned)
        })();
        self.txn.lctx = saved;
        result
    }

    /// Clean the surviving proof contexts before running the user's single
    /// script. Cache misses remain distinct call sites: the pin's raw targets
    /// also include `_recAppPos`, so equal bare relations do not justify merging
    /// them after a call has escaped its original local scope.
    fn prepare_decreasing_goals(
        &mut self,
        obligations: &[Obligation],
    ) -> Result<Vec<tactics::ProofGoal>, NatDefinitionElabError> {
        let mut goals = Vec::new();
        for obligation in obligations {
            self.tick()?;
            let raw_target = self.instantiate(&obligation.raw_target)?;
            let mut goal = obligation.goal.clone();
            goal.target = self.instantiate(&goal.target)?;
            goal.lctx = self.clean_decreasing_context(&goal.lctx, &raw_target)?;
            goals.push(goal);
        }
        Ok(goals)
    }

    /// `clean_wf` exposes the measure at the actual branch input. Read it
    /// from the checked fixpoint continuation, so a match refines the current
    /// argument without rewriting unrelated captured source variables.
    fn decreasing_target(&mut self, raw_target: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let (relation, measure, next, current) = self.decreasing_relation_parts(raw_target)?;
        let measure = self.whnf(&measure)?;
        let ExprNode::Lam { body, .. } = measure.node() else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        let smaller = self.substitute(body, &next)?;
        let current = self.substitute(body, &current)?;
        Ok(Expr::app(Expr::app(relation, smaller), current))
    }

    /// Let values remain let values in both telescopes. Making an arbitrary
    /// parameter out of a source let would invalidate proofs that used its
    /// definitional equality. Parameters alone become explicit applications.
    fn close_decreasing_capture(
        &mut self,
        mut body: Expr,
        captures: &[LocalDecl],
        value: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        for local in captures.iter().rev() {
            self.tick()?;
            body = body
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            let type_ = self.instantiate(&local.type_)?;
            body = if let Some(initializer) = &local.value {
                Expr::let_e(
                    local.user_name.clone(),
                    type_,
                    self.instantiate(initializer)?,
                    body,
                    false,
                )
            } else if value {
                Expr::lam(local.user_name.clone(), type_, body, local.binder_info)
            } else {
                Expr::forall_e(local.user_name.clone(), type_, body, local.binder_info)
            };
        }
        Ok(body)
    }

    /// Lower only saturated applications. A bare self reference must remain
    /// visible to the final escape check, including in unused source values.
    pub(in crate::source) fn lower_well_founded_call(
        &mut self,
        value: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let Some(state) = &self.well_founded else {
            return Ok(value.clone());
        };
        if !value.has_fvar() {
            return Ok(value.clone());
        }
        let marker = state.marker.clone();
        let arity = state.parameters.len();
        let mut head = value;
        let mut arguments = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            arguments.push(a.clone());
            head = f;
        }
        if !matches!(head.node(), ExprNode::FVar { id } if id == &marker) || arguments.len() < arity
        {
            return Ok(value.clone());
        }
        let state = self.well_founded.as_ref().expect("active recursive call");
        if state.proving {
            return Err(error(RecursionError::RecursionInDecreasingProof));
        }
        // Do not copy the growing obligation list on each source application.
        // Only an actual saturated self call needs these small snapshots.
        let fixed = state.fixed.clone();
        let measure_captures = state.measure_captures.clone();
        let varying = state.varying.clone();
        let proof_inaccessible = state.proof_inaccessible.clone();
        arguments.reverse();
        for (index, parameter) in &fixed {
            self.tick()?;
            if !self.fixed_well_founded_argument(&arguments[*index], parameter)? {
                if measure_captures.contains(index) {
                    return Err(error(
                        RecursionError::WellFoundedMeasureDependsOnVaryingParameter,
                    ));
                }
                return Err(error(RecursionError::ChangedParameter));
            }
        }
        // PackMutual preserves the original expression only for a unary
        // varying suffix after fixed parameters. All other encodings remove
        // fixed arguments before the complete-call cache sees the expression.
        // Validate those arguments above before a cache hit can discard them.
        let call = if varying.len() == 1 && varying[0] + 1 == arity {
            self.instantiate(value)?
        } else {
            let mut call = Expr::fvar(marker.clone());
            for index in varying.iter().copied().chain(arity..arguments.len()) {
                self.tick()?;
                call = Expr::app(call, self.instantiate(&arguments[index])?);
            }
            call
        };
        // Reuse remains directional: the cached original scope's last local
        // must still be present. Sibling/expired contexts keep distinct goals.
        if let Some(cached) = self
            .well_founded
            .as_ref()
            .expect("active recursive call")
            .calls
            .get(&call)
            .cloned()
            && self.txn.lctx.find(&cached.scope).is_some()
            && self.well_founded_cached_scope(cached.branch_scope.as_ref())?
        {
            return Ok(cached.value);
        }
        let continuation = self
            .well_founded_continuation()
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        let continuation_type = self.whnf(&continuation.type_)?;
        let ExprNode::ForallE {
            binder_type: domain,
            body,
            ..
        } = continuation_type.node()
        else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        let mut next_arguments = Vec::new();
        for index in varying {
            self.tick()?;
            next_arguments.push(self.instantiate(&arguments[index])?);
        }
        let next = self
            .pack_well_founded_arguments(domain, &next_arguments)?
            .value;
        let at_next = self.substitute(body, &next)?;
        let at_next = self.whnf(&at_next)?;
        let ExprNode::ForallE {
            binder_type: raw_target,
            ..
        } = at_next.node()
        else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        let raw_target = self.instantiate(raw_target)?;
        let target = self.decreasing_target(&raw_target)?;
        // The pin cleans InvImage and its measure before presenting goals to
        // decreasing_by. The final continuation application still carries the
        // original fixpoint domain, so the kernel checks that conversion.
        let name = self.fresh_name()?;
        let id = MVarId(name.clone());
        self.txn.mvars.declare(
            id.clone(),
            name,
            target.clone(),
            self.txn.lctx.clone(),
            MetavarKind::SyntheticOpaque,
            0,
            None,
        );
        // The pin introduces arguments after the declaration colon as
        // inaccessible names in its decreasing goals. Termination aliases
        // name the measure's telescope only, not this later proof context.
        let mut proof_lctx = LocalContext::new();
        let locals = self.txn.lctx.decls().to_vec();
        let mut hidden = Vec::new();
        for local in &locals {
            self.tick()?;
            if self.is_matrix_hypothesis(local) && !local.user_name.is_anonymous() {
                hidden.push(local.user_name.clone());
            }
            let mut local = local.clone();
            if proof_inaccessible.contains(&local.id) {
                local.user_name = Name::anonymous();
            }
            tactics::eliminate::add_local(&mut proof_lctx, &local);
        }
        let goal = tactics::ProofGoal {
            id: id.clone(),
            target,
            lctx: proof_lctx,
            introduced: Vec::new(),
        };
        // Retain full captures even when proof-context cleanup later removes
        // an unrelated local. Let values can still depend on the hidden
        // continuation. The recursive marker is never captured and remains
        // subject to the ordinary escape check.
        let captures: Vec<_> = locals
            .into_iter()
            .filter(|local| local.id != marker)
            .collect();
        let closed_type = self.close_decreasing_capture(goal.target.clone(), &captures, false)?;
        if self.elimination_reads(&closed_type)?.contains(&marker) {
            return Err(error(RecursionError::PartialApplication));
        }
        let transport_name = self.fresh_name()?;
        let transport = MVarId(transport_name.clone());
        self.txn.mvars.declare(
            transport.clone(),
            transport_name,
            closed_type,
            LocalContext::new(),
            MetavarKind::SyntheticOpaque,
            0,
            None,
        );
        let mut transported = Expr::mvar(transport.clone());
        for local in &captures {
            self.tick()?;
            if local.value.is_none() {
                transported = Expr::app(transported, Expr::fvar(local.id.clone()));
            }
        }
        let mut result = Expr::app(Expr::app(Expr::fvar(continuation.id), next), transported);
        let call_arguments = arguments[..arity].to_vec();
        for argument in arguments.into_iter().skip(arity) {
            self.tick()?;
            result = Expr::app(result, argument);
        }
        let scope = self
            .txn
            .lctx
            .decls()
            .last()
            .ok_or_else(|| failure(SourceInferenceError::Scope))?
            .id
            .clone();
        let active = self
            .well_founded
            .as_mut()
            .expect("active well-founded call");
        active.proof_hidden.extend(hidden);
        active.goals.push(Obligation {
            goal,
            raw_target,
            transport,
            captures,
            arguments: call_arguments,
        });
        let branch_scope = active.branch_scopes.last().cloned();
        active.calls.insert(
            call,
            CachedCall {
                scope,
                branch_scope,
                value: result.clone(),
            },
        );
        Ok(result)
    }
}
