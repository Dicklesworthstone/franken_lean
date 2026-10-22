//! Native proof-state execution. Tactics construct candidate terms, not verdicts.
//!
//! `intro` records binders and closes them only after descendant goals are
//! solved. Abstracting a lambda around an unassigned child hole would hide its
//! context variables from substitution and leak free variables. Both tactic
//! sequences and application continuations use heap worklists instead.

use super::*;
pub(in crate::source) mod backtrack;
mod change;
mod congruence;
mod construct;
mod constructor_transport;
mod constructors;
mod context;
mod control;
mod decision;
pub(in crate::source) mod eliminate;
mod empty;
mod equality;
mod extensionality;
mod false_or_by_contra;
mod guard;
mod guard_hyp;
mod index_equations;
mod introductions;
mod omega;
mod rcases;
mod refine;
mod relations;
mod rewrite;
mod search;
mod trace;
mod trivial;
mod unfold;
pub(in crate::source) use refine::RefinementFrame;
pub(in crate::source) use rewrite::SimpKeyCache;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TacticError {
    ExplicitFailure,
    /// The tactic given to `fail_if_success` succeeded (`evalFailIfSuccess`).
    FailIfSuccessSucceeded,
    /// A tactic this engine does not run, named by its syntax kind. Like a malformed script it
    /// is never caught by `first`/`try`: the pin would run it, and could succeed.
    UnsupportedTactic(Name),
    /// `guard_target`'s comparison failed (`evalGuardTarget`: "The main goal is … but was
    /// expected to be …").
    GuardTargetMismatch,
    /// `guard_hyp` must refer to a local, not a constant or computed expression.
    GuardHypExpectedLocal,
    GuardHypTypeMismatch(Name),
    GuardHypValueMismatch(Name),
    GuardHypNotLet(Name),
    GuardHypMissingValue(Name),
    ExpectedGoal,
    ExpectedProposition,
    /// A non-identifier simp argument whose type does not conclude in a proposition (the
    /// pin's `checkTypeIsProp`).
    InvalidSimpTheorem,
    DecisionNotTrue,
    /// `decide` on a goal that still mentions a local after its let-bound locals are unfolded
    /// (the pin's `preprocessPropToDecide`; `decide +revert` is not read).
    DecideFreeVariables,
    NoGoals,
    UnsolvedGoals {
        count: usize,
    },
    NoMatchingAssumption,
    InvalidSearchArguments(&'static str),
    SyntheticHoleOutsideRefine,
    IncompatibleSyntheticHole,
    NoConstructor,
    ExpectedTwoConstructors,
    ApplyMismatch,
    ChangeMismatch,
    MalformedScript,
    ExpectedEquality,
    RewriteNoMatch,
    UnfoldFailed(Name),
    RewriteLocation,
    RewriteMetavariablePattern,
    SimplificationNoProgress,
    DefinitionalSimplificationNoProgress,
    SimplificationCycle,
    EliminationLocal,
    EliminationCoverage,
    EliminationArity,
    /// `induction` on a major whose type has an index that is not a local
    /// variable: the pin's `checkInductionTargets` (vendored
    /// Lean/Elab/Tactic/Induction.lean:947-954) refuses it and suggests `cases`.
    InductionIndexNotVariable,
    /// `induction` on a major whose type repeats one index local.
    InductionIndexRepeated,
    /// `induction` on a major whose parameters mention one of its index
    /// locals: the pin's motive, abstracted over the index, cannot be typed.
    InductionMotiveMismatch,
    UnsupportedEliminator,
    InvalidGeneralization,
    SubstitutionLocal,
    /// `subst h` on `h : HEq a b` whose two types are not definitionally equal. The pin's
    /// `subst` (vendored src/Lean/Meta/Tactic/Subst.lean) turns an `HEq` into an `Eq` only
    /// when they are (`heqToEq`); otherwise it reads `h` as a variable to eliminate and finds
    /// no equation for it.
    SubstitutionNoEquation {
        local: Name,
    },
    /// `injection h with …` gave more names than it made equations. The pin's `noConfusion`
    /// makes none for a proof field, so those take no name (`checkUnusedIds`, vendored
    /// src/Lean/Elab/Tactic/Injection.lean).
    InjectionUnusedNames {
        unused: Vec<Name>,
    },
    /// `rename_i` named more hypotheses than are inaccessible or shadowed
    /// (`renameInaccessibles`, vendored src/Lean/Elab/Tactic/RenameInaccessibles.lean).
    RenameTooManyNames,
    /// `clear` of a local that a later local, or the target, still reads (`MVarId.clear`,
    /// vendored src/Lean/Meta/Tactic/Clear.lean); `dependent: None` is the target.
    ClearDependency {
        local: Name,
        dependent: Option<Name>,
    },
    /// `specialize e` whose head is not a local hypothesis (`evalSpecialize`, vendored
    /// src/Lean/Elab/Tactic/ElabTerm.lean).
    SpecializeRequiresLocal,
    /// `case t => …` with no goal tagged `t` (`getCaseGoals`, vendored
    /// src/Lean/Elab/Tactic/BuiltinTactic.lean).
    CaseTagNotFound(Name),
    ConstructorEquality,
    NoContradiction,
    ArithmeticUnsupported,
    ArithmeticNoContradiction,
    ArithmeticInvalidCertificate,
}
impl std::fmt::Display for TacticError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ExplicitFailure => write!(f, "explicit tactic failure"),
            Self::UnsupportedTactic(kind) => {
                write!(f, "unsupported tactic `{}`", kind.to_display_string())
            }
            Self::FailIfSuccessSucceeded => write!(
                f,
                "the tactic provided to `fail_if_success` succeeded but was expected to fail"
            ),
            Self::GuardTargetMismatch => write!(
                f,
                "guard_target: the main goal is not what it was expected to be"
            ),
            Self::GuardHypExpectedLocal => {
                write!(f, "guard_hyp: expected a local hypothesis")
            }
            Self::GuardHypTypeMismatch(name) => write!(
                f,
                "guard_hyp: hypothesis `{}` has a different type",
                name.to_display_string()
            ),
            Self::GuardHypValueMismatch(name) => write!(
                f,
                "guard_hyp: hypothesis `{}` has a different value",
                name.to_display_string()
            ),
            Self::GuardHypNotLet(name) => {
                write!(f, "`{}` is not a let binding", name.to_display_string())
            }
            Self::GuardHypMissingValue(name) => {
                write!(f, "`{}` is a let binding", name.to_display_string())
            }
            Self::ExpectedGoal => write!(f, "by proof requires an expected type"),
            Self::ExpectedProposition => write!(f, "decision requires a proposition"),
            Self::InvalidSimpTheorem => {
                write!(f, "Invalid simp theorem: Expected a proposition")
            }
            Self::DecisionNotTrue => write!(f, "decision did not reduce to a proof of the goal"),
            // The pin's words.
            Self::DecideFreeVariables => {
                write!(f, "Expected type must not contain free variables")
            }
            Self::NoGoals => write!(f, "tactic has no remaining goal"),
            Self::UnsolvedGoals { count } => write!(f, "proof script left {count} unsolved goals"),
            Self::SyntheticHoleOutsideRefine => write!(f, "synthetic proof holes require refine"),
            Self::IncompatibleSyntheticHole => {
                write!(f, "named synthetic hole used at incompatible type or scope")
            }
            Self::NoConstructor => write!(f, "no constructor applies to the current goal"),
            Self::ExpectedTwoConstructors => write!(
                f,
                "left/right require an inductive type with two constructors"
            ),
            Self::NoMatchingAssumption => write!(f, "no local assumption matches the goal"),
            Self::InvalidSearchArguments(reason) => write!(f, "solve_by_elim: {reason}"),
            Self::ApplyMismatch => write!(f, "apply conclusion does not match the goal"),
            Self::ChangeMismatch => {
                write!(f, "change target is not definitionally equal to the goal")
            }
            Self::ExpectedEquality => write!(f, "rewrite requires an instantiated equality proof"),
            Self::RewriteLocation => write!(
                f,
                "rewrite location must name an available local hypothesis"
            ),
            Self::RewriteNoMatch => write!(f, "rewrite found no matching occurrence in the goal"),
            Self::UnfoldFailed(name) => write!(
                f,
                "unfold failed for `{}` in the selected location",
                name.to_display_string()
            ),
            Self::RewriteMetavariablePattern => {
                write!(f, "rewrite pattern has an unresolved metavariable head")
            }
            Self::DefinitionalSimplificationNoProgress => {
                write!(f, "`dsimp` made no progress")
            }
            Self::SimplificationNoProgress => write!(f, "simp only made no progress"),
            Self::SimplificationCycle => write!(f, "simp only encountered a rewrite cycle"),
            Self::EliminationLocal => write!(f, "elimination requires a local variable"),
            Self::EliminationCoverage => write!(
                f,
                "elimination alternatives must cover each constructor exactly once"
            ),
            Self::EliminationArity => {
                write!(f, "elimination has duplicate or excessive binder names")
            }
            Self::InductionIndexNotVariable => write!(
                f,
                "Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)"
            ),
            Self::InductionIndexRepeated => write!(
                f,
                "Invalid target: Target (or one of its indices) occurs more than once"
            ),
            Self::InductionMotiveMismatch => write!(f, "Type mismatch when assigning motive"),
            Self::UnsupportedEliminator => write!(
                f,
                "elimination requires a supported admitted single-family recursor"
            ),
            Self::InvalidGeneralization => {
                write!(f, "invalid or dependent elimination generalization")
            }
            Self::SubstitutionLocal => {
                write!(f, "subst requires an acyclic local-variable equality")
            }
            // The pin's words.
            Self::InjectionUnusedNames { unused } => write!(
                f,
                "Tactic `injection` failed: too many identifiers provided, unused: [{}]",
                unused
                    .iter()
                    .map(Name::to_display_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            // The pin's words.
            Self::SubstitutionNoEquation { local } => write!(
                f,
                "Tactic `subst` failed: did not find equation for eliminating '{}'",
                local.to_display_string()
            ),
            // The pin's words.
            Self::RenameTooManyNames => write!(f, "too many variable names provided"),
            Self::ClearDependency {
                local,
                dependent: Some(dependent),
            } => write!(
                f,
                "Tactic `clear` failed: variable '{}' depends on '{}'",
                dependent.to_display_string(),
                local.to_display_string()
            ),
            Self::ClearDependency {
                local,
                dependent: None,
            } => write!(
                f,
                "Tactic `clear` failed: target depends on '{}'",
                local.to_display_string()
            ),
            Self::CaseTagNotFound(tag) => {
                write!(f, "Case tag `{}` not found.", tag.to_display_string())
            }
            Self::SpecializeRequiresLocal => write!(
                f,
                "'specialize' requires a term of the form `h x_1 .. x_n` where `h` appears in the local context"
            ),
            Self::ConstructorEquality => write!(
                f,
                "constructor equality has no supported injective fields or contradiction"
            ),
            Self::NoContradiction => write!(f, "no supported contradictory evidence was found"),
            Self::ArithmeticUnsupported => write!(
                f,
                "omega requires its native provider and checked Init.Omega declarations"
            ),
            Self::ArithmeticNoContradiction => write!(f, "omega could not prove the goal"),
            Self::ArithmeticInvalidCertificate => {
                write!(f, "native arithmetic returned an invalid certificate")
            }
            Self::MalformedScript => write!(f, "unsupported or malformed native proof script"),
        }
    }
}
fn error(reason: TacticError) -> NatDefinitionElabError {
    failure(SourceInferenceError::Tactic(reason))
}

/// Application callers select the order of their *real* pending obligations.
/// Manual tactics prefer nondependent goals; search's constructor discharger
/// follows the original telescope, so a witness choice can be backtracked.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum ApplyGoalOrder {
    NonDependentFirst,
    Telescope,
}

#[derive(Clone)]
pub(super) struct ProofGoal {
    pub(in crate::source) id: MVarId,
    pub(super) target: Expr,
    pub(super) lctx: LocalContext,
    pub(in crate::source) introduced: Vec<LocalDecl>,
}
#[derive(Clone)]
enum Work<'a> {
    EndAttempt(usize),
    EndControl(usize),
    EndOptions(Box<OptionScope<'a>>),
    Rewrite(ProofGoal, std::collections::VecDeque<RewriteRule<'a>>, bool),
    Goal(ProofGoal),
    Close(ProofGoal, Expr),
    Script(ProofGoal, Vec<&'a Syntax>),
    Term(ProofGoal, &'a Syntax),
    EndScript(Vec<&'a Syntax>, usize),
}
#[derive(Clone)]
// The lexical barrier restores both options and tactic-local instances.
struct OptionScope<'a> {
    options: KVMap,
    instance_scopes: crate::instances::scoped::ActiveScopes,
    instructions: Vec<&'a Syntax>,
    cursor: usize,
}
#[derive(Clone)]
pub(super) struct ProofState<'a> {
    extent: Option<Box<std::ops::Range<usize>>>,
    saved: LocalContext,
    target: Expr,
    root: Expr,
    instructions: Vec<&'a Syntax>,
    cursor: usize,
    work: Vec<Work<'a>>,
    controls: Vec<control::Frame<'a>>,
}
/// A local a tactic adds: a hypothesis (`have`) or a definition with its value (`let`).
/// `replaces` is the hypothesis `replace` supersedes, cleared once the new one is in place
/// unless something still reads it.
#[derive(Clone)]
pub(super) struct LocalBinding {
    pub(super) name: Name,
    pub(super) opaque: bool,
    pub(super) replaces: Option<FVarId>,
}

/// A `have`/`let`/`replace` declaration's single `letIdDecl`, with no binders: its name
/// (`this` for an anonymous `have`), its optional type and its value.
fn local_declaration(
    declaration: &Syntax,
    opaque: bool,
) -> Result<(Name, Option<&Syntax>, &Syntax), NatDefinitionElabError> {
    let [declaration] = expect_node(
        declaration,
        &parser_kind(&["Term", "letDecl"]),
        1,
        "local tactic declaration",
    )?
    else {
        return Err(error(TacticError::MalformedScript));
    };
    let [id, binders, annotation, assign, value] = expect_node(
        declaration,
        &parser_kind(&["Term", "letIdDecl"]),
        5,
        "local tactic declaration",
    )?
    else {
        return Err(error(TacticError::MalformedScript));
    };
    expect_empty_null(binders, "local tactic without binders")?;
    expect_atom(assign, ":=", "local tactic assignment")?;
    let [id] = expect_node(id, &parser_kind(&["Term", "letId"]), 1, "local tactic name")? else {
        return Err(error(TacticError::MalformedScript));
    };
    let name = match id {
        Syntax::Node { kind, .. } if opaque && kind == &Name::from_components(["hygieneInfo"]) => {
            Name::from_components(["this"])
        }
        Syntax::Ident { val, .. } if !val.is_anonymous() && val.parent().is_anonymous() => {
            val.clone()
        }
        _ => return Err(error(TacticError::MalformedScript)),
    };
    Ok((name, optional_type_syntax(annotation)?, value))
}

#[derive(Clone)]
pub(super) struct RewriteRule<'a> {
    pub(super) syntax: &'a Syntax,
    pub(super) reverse: bool,
}

pub(super) enum ProofAction<'a> {
    Change {
        goal: ProofGoal,
        target: &'a Syntax,
    },
    Simpa {
        goal: ProofGoal,
        args: &'a [Syntax],
        using: &'a Syntax,
    },
    Eliminate {
        goal: ProofGoal,
        args: &'a [Syntax],
        induction: bool,
        equation: Option<Name>,
        expression: &'a Syntax,
    },
    Generalize {
        goal: ProofGoal,
        name: Name,
        equality: Option<Name>,
        expression: &'a Syntax,
    },
    Cases {
        goal: ProofGoal,
        name: Name,
        proposition: &'a Syntax,
    },
    Attempt(backtrack::Spec<'a>),
    AttemptComplete(usize),
    Refine {
        syntax: &'a Syntax,
        goal: ProofGoal,
    },
    Binding {
        goal: ProofGoal,
        binding: LocalBinding,
        annotation: Option<&'a Syntax>,
        value: &'a Syntax,
    },
    /// `specialize e`: `e` is elaborated, then replaces its head hypothesis in place.
    Specialize {
        goal: ProofGoal,
        term: &'a Syntax,
    },
    Rewrite {
        goal: ProofGoal,
        rule: RewriteRule<'a>,
        remaining: std::collections::VecDeque<RewriteRule<'a>>,
        close: bool,
    },
    Term {
        syntax: &'a Syntax,
        goal: ProofGoal,
        apply: bool,
    },
    Complete(Typed),
}

impl Context {
    fn proof_goal(&mut self, target: Expr) -> Result<(Expr, ProofGoal), NatDefinitionElabError> {
        let hole = self.hole(target.clone())?;
        let ExprNode::MVar { id } = hole.node() else {
            unreachable!("fresh hole");
        };
        let goal = ProofGoal {
            id: id.clone(),
            target,
            lctx: self.txn.lctx.clone(),
            introduced: Vec::new(),
        };
        Ok((hole, goal))
    }

    pub(super) fn start_proof<'a>(
        &mut self,
        syntax: &'a Syntax,
        expected: Option<Expr>,
    ) -> Result<ProofState<'a>, NatDefinitionElabError> {
        let mut target = expected.ok_or_else(|| error(TacticError::ExpectedGoal))?;
        // The pin runs a tactic block only after `synthesizeSyntheticMVars` has
        // applied default instances, so `have h : 0 = 0 := by rfl` sees `(0 : Nat)`.
        // This engine starts the block where it is visited, so default the
        // pending instance goals first when the goal is still open.
        if target.has_expr_mvar() {
            self.resolve_instances_with_defaults()?;
            target = self.instantiate(&target)?;
        }
        let kind = if syntax.kind() == Some(&parser_kind(&["Term", "byTactic'"])) {
            parser_kind(&["Term", "byTactic'"])
        } else {
            parser_kind(&["Term", "byTactic"])
        };
        let parts = expect_node(syntax, &kind, 2, "by proof")?;
        expect_atom(&parts[0], "by", "by keyword")?;
        let instructions = self.proof_instructions(&parts[1])?;
        let (root, goal) = self.proof_goal(target.clone())?;
        let extent = self.observation_extent(syntax)?.map(Box::new);
        self.observe_by(&parts[0], &goal)?;
        Ok(ProofState {
            extent,
            saved: self.txn.lctx.clone(),
            target,
            root,
            instructions,
            cursor: 0,
            work: vec![Work::Goal(goal)],
            controls: Vec::new(),
        })
    }

    /// A single user script handles all recursive-call obligations, in source
    /// order, just as the pin's `solveDecreasingGoals` does. Reusing the normal
    /// proof driver preserves tactic controls, alternatives, and resource rules.
    pub(super) fn start_decreasing_proof<'a>(
        &mut self,
        syntax: &'a Syntax,
        goals: Vec<ProofGoal>,
    ) -> Result<ProofState<'a>, NatDefinitionElabError> {
        let first = goals
            .first()
            .ok_or_else(|| error(TacticError::ExpectedGoal))?;
        Ok(ProofState {
            extent: self.observation_extent(syntax)?.map(Box::new),
            saved: self.txn.lctx.clone(),
            target: first.target.clone(),
            root: Expr::mvar(first.id.clone()),
            instructions: self.proof_instructions(syntax)?,
            cursor: 0,
            work: goals.into_iter().rev().map(Work::Goal).collect(),
            controls: Vec::new(),
        })
    }

    fn proof_instructions<'a>(
        &mut self,
        syntax: &'a Syntax,
    ) -> Result<Vec<&'a Syntax>, NatDefinitionElabError> {
        let mut instructions = Vec::new();
        let mut pending = vec![(syntax, true)];
        while let Some((syntax, sequence)) = pending.pop() {
            self.tick()?;
            if !sequence {
                if let Syntax::Node { kind, args, .. } = syntax
                    && kind == &parser_kind(&["Tactic", "paren"])
                {
                    let [open, body, close] = args.as_slice() else {
                        return Err(error(TacticError::MalformedScript));
                    };
                    expect_atom(open, "(", "tactic sequence opening")?;
                    expect_atom(close, ")", "tactic sequence closing")?;
                    pending.push((body, true));
                } else {
                    instructions.push(syntax);
                }
                continue;
            }
            // `{ tacs }` (`tacticSeqBracketed := "{" sepByIndent tactic "; " "}"`) is the body of
            // its own focus here; as a sequence, it is that one focused instruction.
            let rows = if let Syntax::Node { kind, args, .. } = syntax
                && kind == &parser_kind(&["Tactic", "tacticSeqBracketed"])
            {
                let [open, rows, close] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(open, "{", "bracketed tactic sequence opening")?;
                expect_atom(close, "}", "bracketed tactic sequence closing")?;
                rows
            } else {
                let sequence = expect_node(
                    syntax,
                    &parser_kind(&["Tactic", "tacticSeq"]),
                    1,
                    "tactic sequence",
                )?;
                if sequence[0].kind() == Some(&parser_kind(&["Tactic", "tacticSeqBracketed"])) {
                    pending.push((&sequence[0], false));
                    continue;
                }
                &expect_node(
                    &sequence[0],
                    &parser_kind(&["Tactic", "tacticSeq1Indented"]),
                    1,
                    "flat tactic sequence",
                )?[0]
            };
            let rows = expect_null_args(rows, "tactic sequence rows")?;
            for (index, row) in rows.iter().enumerate().rev() {
                self.tick()?;
                if index % 2 == 0 {
                    pending.push((row, false));
                } else if !matches!(row, Syntax::Atom { val, .. } if val == ";") {
                    // Otherwise a line break, which the pin's `sepByIndent` records as `[]`.
                    expect_empty_null(row, "tactic separator")
                        .map_err(|_| error(TacticError::MalformedScript))?;
                }
            }
        }
        Ok(instructions)
    }

    /// A tactic is syntax its declaring module adds, as a `ParserDescr` constant named after its
    /// kind (`Lean.Parser.Tactic.guardTarget`, from `Init/Guard.lean`). In a world built from
    /// Init's `.olean`s, which declare `Lean.ParserDescr`, a world whose imports do not reach that
    /// module lacks the constant, and the pin reads the tactic as unknown ("unknown tactic"). The
    /// seed declares no syntax and stands for the implicit Init, which declares every such tactic.
    pub(super) fn require_declared_tactic(
        &self,
        syntax_constant: &[&str],
    ) -> Result<(), NatDefinitionElabError> {
        let name = Name::from_components(syntax_constant.iter().copied());
        if self
            .txn
            .env
            .contains(&Name::from_components(["Lean", "ParserDescr"]))
            && !self.txn.env.contains(&name)
        {
            return Err(failure(SourceInferenceError::UnknownConstant(name)));
        }
        Ok(())
    }

    /// Try equality transactionally; a failed candidate retains no assignment.
    /// Inconclusive/resource/internal outcomes never mean "try another proof".
    pub(in crate::source) fn proof_types_match(
        &mut self,
        left: &Expr,
        right: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        self.proof_types_match_with_budget(left, right, UnificationBudget::new(self.kernel))
    }

    fn proof_types_match_with_budget(
        &mut self,
        left: &Expr,
        right: &Expr,
        budget: UnificationBudget,
    ) -> Result<bool, NatDefinitionElabError> {
        self.flush(false)?;
        match self.txn.unify(left, right, budget) {
            Ok(report) => {
                assert!(report.awakened.is_empty(), "private source queue");
                Ok(true)
            }
            Err(UnificationError::Deferred(_)) => Ok(false),
            Err(UnificationError::AssignmentCheck { outcome, .. })
                if matches!(*outcome, Outcome::Complete(Verdict::Rejected { .. })) =>
            {
                Ok(false)
            }
            Err(error) => Err(failure(SourceInferenceError::Unification(Box::new(error)))),
        }
    }

    /// The pin's `MVarId.assumptionCore`: the most recent hypothesis whose type matches the
    /// goal, as `assumption` uses it and as `injection` tries it on the goal it leaves.
    pub(super) fn matching_assumption(
        &mut self,
        goal: &ProofGoal,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        self.matching_assumption_except(goal, &std::collections::HashSet::new())
    }

    /// [`Self::matching_assumption`], never answering with a hypothesis in `hidden`.
    pub(super) fn matching_assumption_except(
        &mut self,
        goal: &ProofGoal,
        hidden: &std::collections::HashSet<FVarId>,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        for local in goal.lctx.decls().iter().rev() {
            self.tick()?;
            if self.is_matrix_hypothesis(local) || hidden.contains(&local.id) {
                continue;
            }
            // The pin keeps ordinary conversion during decreasing proofs.
            // Cleanup can expose Nat.lt while a retained hypothesis still
            // names LT.lt through its instance. Both inferred probes and
            // supplied/default WF proofs must recognize that same evidence.
            let mut budget = UnificationBudget::new(self.kernel);
            if self
                .well_founded
                .as_ref()
                .is_some_and(|state| state.proving)
            {
                budget.transparency = UnificationTransparency::Default;
            }
            if self.proof_types_match_with_budget(&local.type_, &goal.target, budget)? {
                return Ok(Some(Expr::fvar(local.id.clone())));
            }
        }
        Ok(None)
    }

    /// `rfl` on an `Eq` or `HEq` goal: both sides, and for `HEq` both types, are unified.
    pub(super) fn rfl_proof_goal(&mut self, goal: ProofGoal) -> Result<(), NatDefinitionElabError> {
        let target = self.whnf(&goal.target)?;
        if let Some((level, alpha, left, beta, right)) = equality::heterogeneous_target(&target) {
            self.constrain(&alpha, &beta)?;
            self.constrain(&left, &right)?;
            let value = [alpha, left].into_iter().fold(
                Expr::const_(Name::from_components(["HEq", "refl"]), vec![level]),
                Expr::app,
            );
            return self.close_proof_goal(goal, value);
        }
        let (level, alpha, left, right) =
            equality_target(&target).ok_or_else(|| error(TacticError::ApplyMismatch))?;
        self.constrain(&left, &right)?;
        let value = Expr::app(
            Expr::app(
                Expr::const_(Name::from_components(["Eq", "refl"]), vec![level]),
                alpha,
            ),
            left,
        );
        self.close_proof_goal(goal, value)
    }

    pub(super) fn close_proof_goal(
        &mut self,
        goal: ProofGoal,
        value: Expr,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx;
        self.resolve_instances(false)?;
        self.flush(false)?;
        let mut value = self.instantiate(&value)?;
        if let Some(plan) = self
            .recursion
            .as_mut()
            .and_then(|recursion| recursion.equation_goals.remove(&goal.id))
        {
            value = self.lower_constrained_recursive_calls(&value, &plan)?;
        }
        for local in goal.introduced.into_iter().rev() {
            self.tick()?;
            let domain = self.instantiate(&local.type_)?;
            let abstracted = value
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            if local.value.is_some()
                && !abstracted.has_loose_bvar(0)
                && self.discarded_lets.contains(&local.id)
            {
                continue;
            }
            value = abstracted;
            value = if let Some(local_value) = local.value {
                Expr::let_e(
                    local.user_name,
                    domain,
                    self.instantiate(&local_value)?,
                    value,
                    false,
                )
            } else {
                Expr::lam(local.user_name, domain, value, local.binder_info)
            };
        }
        // This is candidate construction in a private transaction, not a
        // kernel acceptance. The complete command still goes through K1.
        self.txn
            .assign_mvar(
                goal.id,
                value,
                AssignmentJustification::Tactic {
                    tactic_name: Name::from_components(["native_source_proof"]),
                },
            )
            .map_err(|e| {
                failure(SourceInferenceError::Unification(Box::new(
                    UnificationError::Metavariable(e),
                )))
            })?;
        Ok(())
    }

    pub(super) fn advance_proof<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
    ) -> Result<ProofAction<'a>, NatDefinitionElabError> {
        loop {
            self.tick()?;
            if matches!(
                proof.work.last(),
                None | Some(
                    Work::EndScript(..)
                        | Work::EndControl(_)
                        | Work::EndAttempt(_)
                        | Work::EndOptions(_)
                )
            ) {
                self.skip_empty_goal_controls(proof)?;
                if let Some(&instruction) = proof.instructions.get(proof.cursor) {
                    if instruction.kind() == Some(&parser_kind(&["Tactic", "traceState"]))
                        || instruction.kind() == Some(&parser_kind(&["Tactic", "traceMessage"]))
                    {
                        self.trace_proof_state(proof, instruction)?;
                        proof.cursor += 1;
                        continue;
                    }
                    if extensionality::is_empty(instruction) {
                        self.require_declared_tactic(&["tacticFunext___"])?;
                        proof.cursor += 1;
                        continue;
                    }
                    if let Some(spec) = self.backtrack_instruction(instruction)? {
                        proof.cursor += 1;
                        return Ok(ProofAction::Attempt(spec));
                    }
                    // `done` with no goal left succeeds, as `skip` does (`evalDone`,
                    // `Lean/Elab/Tactic/BuiltinTactic.lean`).
                    if instruction.kind() == Some(&parser_kind(&["Tactic", "skip"]))
                        || instruction.kind() == Some(&parser_kind(&["Tactic", "done"]))
                    {
                        proof.cursor += 1;
                        continue;
                    }
                    if instruction.kind() == Some(&parser_kind(&["Tactic", "fail"])) {
                        return Err(error(TacticError::ExplicitFailure));
                    }
                    if let Syntax::Node { kind, args, .. } = instruction
                        && control::is_scope(kind)
                    {
                        self.start_tactic_scope(proof, kind, args)?;
                        continue;
                    }
                }
            }
            let Some(work) = proof.work.pop() else {
                self.skip_empty_goal_controls(proof)?;
                if proof.cursor != proof.instructions.len() {
                    return Err(error(TacticError::NoGoals));
                }
                self.observe_proof_end(proof.extent.as_deref(), &[])?;
                self.txn.lctx = proof.saved.clone();
                let value = self.instantiate(&proof.root)?;
                return Ok(ProofAction::Complete(Typed {
                    value,
                    type_: proof.target.clone(),
                }));
            };
            let mut goal = match work {
                Work::EndAttempt(index) => {
                    self.skip_empty_goal_controls(proof)?;
                    if proof.cursor != proof.instructions.len() {
                        return Err(error(TacticError::NoGoals));
                    }
                    return Ok(ProofAction::AttemptComplete(index));
                }
                Work::EndControl(index) => {
                    self.finish_goal_control(proof, index, Vec::new())?;
                    continue;
                }
                Work::EndOptions(scope) => {
                    self.finish_tactic_options(proof, *scope)?;
                    continue;
                }
                Work::Term(mut goal, syntax) => {
                    self.txn.lctx = goal.lctx.clone();
                    goal.target = self.instantiate(&goal.target)?;
                    return Ok(ProofAction::Term {
                        syntax,
                        goal,
                        apply: false,
                    });
                }
                Work::Script(goal, instructions) => {
                    let parent = std::mem::replace(&mut proof.instructions, instructions);
                    let cursor = std::mem::replace(&mut proof.cursor, 0);
                    proof.work.push(Work::EndScript(parent, cursor));
                    goal
                }
                Work::EndScript(instructions, cursor) => {
                    self.skip_empty_goal_controls(proof)?;
                    if proof.cursor != proof.instructions.len() {
                        return Err(error(TacticError::NoGoals));
                    }
                    proof.instructions = instructions;
                    proof.cursor = cursor;
                    continue;
                }
                Work::Rewrite(goal, mut remaining, close) => {
                    self.txn.lctx = goal.lctx.clone();
                    if let Some(rule) = remaining.pop_front() {
                        return Ok(ProofAction::Rewrite {
                            goal,
                            rule,
                            remaining,
                            close,
                        });
                    }
                    if close && self.rewrite_reflexivity(&goal)? {
                        continue;
                    }
                    goal
                }
                Work::Close(goal, term) => {
                    self.close_proof_goal(goal, term)?;
                    continue;
                }
                Work::Goal(goal) => goal,
            };
            if self.txn.mvars.is_assigned(&goal.id) {
                continue;
            }
            self.txn.lctx = goal.lctx.clone();
            goal.target = self.instantiate(&goal.target)?;
            let instruction = proof.instructions.get(proof.cursor).copied();
            if self.observes_goal(instruction, proof.extent.as_deref())? {
                let mut visible = vec![goal.clone()];
                for pending in proof.work.iter().rev() {
                    self.tick()?;
                    match pending {
                        Work::EndScript(..)
                        | Work::EndControl(_)
                        | Work::EndAttempt(_)
                        | Work::EndOptions(_) => break,
                        Work::Goal(other) if !self.txn.mvars.is_assigned(&other.id) => {
                            visible.push(other.clone());
                        }
                        _ => {}
                    }
                }
                self.observe_goals(&visible)?;
            }
            let Some(instruction) = instruction else {
                if let Some(index) = self.suspend_attempt(proof, &goal)? {
                    return Ok(ProofAction::AttemptComplete(index));
                }
                if self.suspend_goal_control(proof, &goal)? {
                    continue;
                }
                if self.suspend_tactic_options(proof, &goal)? {
                    continue;
                }
                let count = 1 + proof.work.iter().filter(|row| matches!(row, Work::Goal(goal) if !self.txn.mvars.is_assigned(&goal.id))).count();
                return Err(error(TacticError::UnsolvedGoals { count }));
            };
            if let Syntax::Node { kind, args, .. } = instruction
                && control::is_scope(kind)
            {
                // Finish the preceding tactic's queued branches and close
                // actions before changing lexical state for this instruction.
                proof.work.push(Work::Goal(goal));
                self.start_tactic_scope(proof, kind, args)?;
                continue;
            }
            proof.cursor += 1;
            let Syntax::Node { kind, args, .. } = instruction else {
                return Err(error(TacticError::MalformedScript));
            };
            if let Some(spec) = self.backtrack_instruction(instruction)? {
                proof.work.push(Work::Goal(goal));
                return Ok(ProofAction::Attempt(spec));
            } else if kind == &parser_kind(&["Tactic", "skip"]) {
                proof.work.push(Work::Goal(goal));
            } else if kind == &parser_kind(&["Tactic", "traceState"])
                || kind == &parser_kind(&["Tactic", "traceMessage"])
            {
                proof.work.push(Work::Goal(goal));
                self.trace_proof_state(proof, instruction)?;
            } else if kind == &parser_kind(&["Tactic", "guardTarget"]) {
                let [keyword, relation, expected] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "guard_target", "guard_target keyword")?;
                self.require_declared_tactic(&["Lean", "Parser", "Tactic", "guardTarget"])?;
                let relation = guard::relation(relation)?;
                if !self.guard_target_matches(&goal, relation, expected)? {
                    return Err(error(TacticError::GuardTargetMismatch));
                }
                proof.work.push(Work::Goal(goal));
            } else if kind == &parser_kind(&["Tactic", "guardHyp"]) {
                self.guard_hypothesis(&goal, args)?;
                proof.work.push(Work::Goal(goal));
            } else if kind == &parser_kind(&["Tactic", "fail"]) {
                return Err(error(TacticError::ExplicitFailure));
            } else if kind == &parser_kind(&["Tactic", "done"]) {
                // An unsolved goal reaches `done`: it fails, and `first` may catch that.
                let [keyword] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "done", "done")?;
                let count = 1 + proof.work.iter().filter(|row| matches!(row, Work::Goal(goal) if !self.txn.mvars.is_assigned(&goal.id))).count();
                return Err(error(TacticError::UnsolvedGoals { count }));
            } else if kind == &parser_kind(&["Tactic", "tactic_<;>_"]) {
                let [left, separator, right] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(separator, "<;>", "goal sequencing operator")?;
                self.start_goal_sequence(proof, goal, left, right)?;
            } else if kind == &parser_kind(&["Tactic", "tacticSeqBracketed"]) {
                // The pin's `evalTacticSeqBracketed` runs its tactics under `closeUsingOrAdmit`:
                // on the main goal alone, which they must close, as `·` does.
                self.start_goal_control(proof, goal, instruction, control::Mode::Solve)?;
            } else if let Some(mode) = control::mode(kind) {
                let [keyword, sequence] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                // `·` is its own `cdotTk` node.
                let keyword = if control::is_cdot(kind) {
                    &expect_node(keyword, &Name::from_components(["Lean", "cdotTk"]), 1, "·")?[0]
                } else {
                    keyword
                };
                // `cdotTk := unicode("· ", ". ")`: the ASCII dot is the same focus.
                let ascii_cdot = control::is_cdot(kind)
                    && matches!(keyword, Syntax::Atom { val, .. } if val == ".");
                if !ascii_cdot {
                    expect_atom(keyword, mode.keyword(), "goal control keyword")?;
                }
                self.start_goal_control(proof, goal, sequence, mode)?;
            } else if kind == &parser_kind(&["Tactic", "tacticHave__"])
                || kind == &parser_kind(&["Tactic", "tacticLet__"])
            {
                // `"have" letConfig letDecl` and `"let" letConfig letDecl`: one `letIdDecl`
                // with no binders and the default configuration.
                let opaque = kind == &parser_kind(&["Tactic", "tacticHave__"]);
                let [keyword, config, declaration] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(
                    keyword,
                    if opaque { "have" } else { "let" },
                    "local tactic declaration",
                )?;
                let config = expect_node(
                    config,
                    &parser_kind(&["Term", "letConfig"]),
                    1,
                    "local tactic configuration",
                )?;
                expect_empty_null(&config[0], "default local configuration")?;
                let (name, annotation, value) = local_declaration(declaration, opaque)?;
                return Ok(ProofAction::Binding {
                    goal,
                    binding: LocalBinding {
                        name,
                        opaque,
                        replaces: None,
                    },
                    annotation,
                    value,
                });
            } else if kind == &parser_kind(&["Tactic", "replace"]) {
                // `replace decl` (`evalReplace`, vendored src/Lean/Elab/Tactic/BuiltinTactic.lean)
                // is `have decl`, after which the hypothesis that had the name is cleared when
                // nothing still reads it (`tryClearMany`).
                let [keyword, declaration] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "replace", "replace keyword")?;
                self.require_declared_tactic(&["Lean", "Parser", "Tactic", "replace"])?;
                let (name, annotation, value) = local_declaration(declaration, true)?;
                let replaces = goal
                    .lctx
                    .find_by_user_name(&name)
                    .map(|local| local.id.clone());
                return Ok(ProofAction::Binding {
                    goal,
                    binding: LocalBinding {
                        name,
                        opaque: true,
                        replaces,
                    },
                    annotation,
                    value,
                });
            } else if kind == &parser_kind(&["Tactic", "tacticSuffices_"]) {
                let [keyword, declaration] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "suffices", "suffices keyword")?;
                self.require_declared_tactic(&["Lean", "Parser", "Tactic", "tacticSuffices_"])?;
                self.suffices_proof_goal(proof, goal, keyword, declaration)?;
            } else if kind == &parser_kind(&["Tactic", "specialize"]) {
                let [keyword, term] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "specialize", "specialize keyword")?;
                self.require_declared_tactic(&["Lean", "Parser", "Tactic", "specialize"])?;
                return Ok(ProofAction::Specialize { goal, term });
            } else if kind == &parser_kind(&["Tactic", "rintro"]) {
                self.rintro_proof_goal(proof, goal, args)?;
            } else if kind == &parser_kind(&["Tactic", "obtain"]) {
                self.obtain_proof_goal(proof, goal, args)?;
            } else if kind == &parser_kind(&["Tactic", "rcases"]) {
                self.rcases_proof_goal(proof, goal, args)?;
            } else if kind == &parser_kind(&["Tactic", "refine"]) {
                let [keyword, term] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "refine", "refinement tactic")?;
                return Ok(ProofAction::Refine { syntax: term, goal });
            } else if kind == &Name::from_components(["tacticBy_cases_:_"]) {
                let [keyword, binder, proposition] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "by_cases", "decidable case split")?;
                let name = match expect_null_args(binder, "case evidence name")? {
                    // The pin's unnamed `by_cases p` binds a hygienic `h✝`: usable by
                    // `assumption`, never by a source `h` ("Unknown identifier `h`").
                    [] => self.fresh_inaccessible(&Name::from_components(["h"]))?,
                    [Syntax::Ident { val, .. }, colon]
                        if !val.is_anonymous() && val.parent().is_anonymous() =>
                    {
                        expect_atom(colon, ":", "case evidence annotation")?;
                        val.clone()
                    }
                    _ => return Err(error(TacticError::MalformedScript)),
                };
                return Ok(ProofAction::Cases {
                    goal,
                    name,
                    proposition,
                });
            } else if kind == &parser_kind(&["Tactic", "falseOrByContra"]) {
                let [keyword] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(
                    keyword,
                    "false_or_by_contra",
                    "contradiction preparation tactic",
                )?;
                self.false_or_by_contra_proof_goal(proof, goal)?;
            } else if kind == &parser_kind(&["Tactic", "tacticExfalso"]) {
                let [keyword] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "exfalso", "exfalso tactic")?;
                let instance_start = self.instance_goals.len();
                let term = self.constant(&Name::from_components(["False", "elim"]))?;
                self.apply_proof_term(proof, goal, term, instance_start)?;
            } else if kind == &parser_kind(&["Tactic", "tacticInfer_instance"]) {
                let [keyword] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "infer_instance", "instance synthesis tactic")?;
                self.txn.lctx = goal.lctx.clone();
                if let Err(problem) = self.validate_instance_binder(&goal.target) {
                    if matches!(
                        problem,
                        NatDefinitionElabError::Inference(
                            SourceInferenceError::InvalidInstanceBinder
                        )
                    ) {
                        return Err(error(TacticError::NoMatchingAssumption));
                    }
                    return Err(problem);
                }
                let value = self.instance_hole(goal.target.clone())?;
                self.resolve_instances(true)?;
                let value = self.instantiate(&value)?;
                if value.has_expr_mvar() || value.has_level_mvar() {
                    return Err(failure(SourceInferenceError::InstanceSynthesisRequired));
                }
                self.close_proof_goal(goal, value)?;
            } else if kind == &parser_kind(&["Tactic", "decide"]) {
                let [keyword, config] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "decide", "decision proof tactic")?;
                // Only the empty configuration is supported.
                let config = expect_node(
                    config,
                    &parser_kind(&["Tactic", "optConfig"]),
                    1,
                    "decide config",
                )?;
                if !expect_null_args(&config[0], "decide config items")?.is_empty() {
                    return Err(error(TacticError::MalformedScript));
                }
                self.decide_proof_goal(goal)?;
            } else if kind == &parser_kind(&["Tactic", "constructor"])
                || kind == &parser_kind(&["Tactic", "left"])
                || kind == &parser_kind(&["Tactic", "right"])
            {
                let (keyword, selected) = if kind == &parser_kind(&["Tactic", "left"]) {
                    ("left", Some(0))
                } else if kind == &parser_kind(&["Tactic", "right"]) {
                    ("right", Some(1))
                } else {
                    ("constructor", None)
                };
                let [actual] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(actual, keyword, "constructor tactic")?;
                self.construct_proof_goal(proof, goal, selected)?;
            } else if kind == &parser_kind(&["Tactic", "contradiction"]) {
                let [keyword] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "contradiction", "contradiction tactic")?;
                self.contradict_proof_goal(goal)?;
            } else if kind == &parser_kind(&["Tactic", "injection"]) {
                self.inject_proof_goal(proof, goal, args)?;
            } else if kind == &parser_kind(&["Tactic", "subst"]) {
                let [keyword, names] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "subst", "substitution tactic")?;
                let [Syntax::Ident { val, .. }] = expect_null_args(names, "substituted name")?
                else {
                    return Err(error(TacticError::MalformedScript));
                };
                self.substitute_proof_goal(proof, goal, val)?;
            } else if kind == &parser_kind(&["Tactic", "cases"])
                || kind == &parser_kind(&["Tactic", "induction"])
            {
                let induction = kind == &parser_kind(&["Tactic", "induction"]);
                let (expression, binder) = eliminate::target(args, induction)?;
                let equation = match binder {
                    None => None,
                    Some(Syntax::Ident { val, .. }) => Some(val.clone()),
                    Some(_) => Some(self.fresh_inaccessible(&Name::from_components(["h"]))?),
                };
                return Ok(ProofAction::Eliminate {
                    goal,
                    args,
                    induction,
                    equation,
                    expression,
                });
            } else if kind == &parser_kind(&["Tactic", "simpAll"]) {
                self.simplify_all_proof_goal(proof, goal, args)?;
            } else if kind == &parser_kind(&["Tactic", "dsimp"]) {
                self.dsimplify_proof_goal(proof, goal, args)?;
            } else if kind == &parser_kind(&["Tactic", "simp"]) {
                self.simplify_proof_goal(proof, goal, args)?;
            } else if kind == &parser_kind(&["Tactic", "simpa"]) {
                let [keyword, _, _, rest] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "simpa", "simplifying completion")?;
                let rest = expect_node(
                    rest,
                    &parser_kind(&["Tactic", "simpaArgsRest"]),
                    5,
                    "simpa arguments",
                )?;
                let using = &rest[4];
                match expect_null_args(using, "optional simpa evidence")? {
                    [] => self.simpa_proof_term(proof, goal, args, None)?,
                    [keyword, using] => {
                        expect_atom(keyword, "using", "simpa evidence keyword")?;
                        return Ok(ProofAction::Simpa { goal, args, using });
                    }
                    _ => return Err(error(TacticError::MalformedScript)),
                }
            } else if kind == &parser_kind(&["Tactic", "unfold"]) {
                self.unfold_proof_goal(proof, goal, args)?;
            } else if kind == &parser_kind(&["Tactic", "rwSeq"])
                || kind == &parser_kind(&["Tactic", "rewriteSeq"])
            {
                let close = kind == &parser_kind(&["Tactic", "rwSeq"]);
                if !self.rewrite_at_locations(proof, &goal, args, close)? {
                    let rules = self.rewrite_rules(args, close)?;
                    proof.work.push(Work::Rewrite(goal, rules, close));
                }
            } else if kind == &parser_kind(&["Tactic", "intro"]) {
                let [keyword, names] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "intro", "intro keyword")?;
                let names = expect_null_args(names, "intro names")?;
                self.intro_proof_patterns(proof, goal, names)?;
            } else if kind == &parser_kind(&["Tactic", "intros"]) {
                let [keyword, names] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "intros", "intros keyword")?;
                let names = expect_null_args(names, "intros names")?;
                self.intros_proof_goal(proof, goal, names)?;
            } else if kind == &parser_kind(&["Tactic", "renameI"]) {
                let [keyword, names] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "rename_i", "rename_i keyword")?;
                self.require_declared_tactic(&["Lean", "Parser", "Tactic", "renameI"])?;
                let names = expect_null_args(names, "renamed hypotheses")?;
                if names.is_empty() {
                    return Err(error(TacticError::MalformedScript));
                }
                let goal = self.renamed_proof_goal(proof, goal, names)?;
                proof.work.push(Work::Goal(goal));
            } else if kind == &parser_kind(&["Tactic", "clear"]) {
                self.clear_proof_locals(proof, goal, args)?;
            } else if kind == &parser_kind(&["Tactic", "tacticNext_=>_"]) {
                // `macro "next " args:(ppSpace binderIdent)* " => " tac:tacticSeq : tactic` is
                // `case _ args* => tac` (vendored src/Init/Tactics.lean): the main goal, its
                // inaccessible hypotheses renamed and its tag cleared, must be closed by `tac`
                // (`evalCase`, vendored src/Lean/Elab/Tactic/BuiltinTactic.lean), as `·` does.
                let [keyword, names, arrow, body] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "next", "next keyword")?;
                expect_atom(arrow, "=>", "next arrow")?;
                self.require_declared_tactic(&["Lean", "Parser", "Tactic", "tacticNext_=>_"])?;
                let names = expect_null_args(names, "next names")?;
                let goal = self.renamed_proof_goal(proof, goal, names)?;
                self.goal_tags.remove(&goal.id);
                self.start_goal_control(proof, goal, body, control::Mode::Solve)?;
            } else if kind == &parser_kind(&["Tactic", "case"]) {
                // `"case " sepBy1(caseArg, " | ") " => " tacticSeq` (`evalCase`, vendored
                // src/Lean/Elab/Tactic/BuiltinTactic.lean): the goal the tag selects, renamed and
                // untagged, must be closed by the body; the others keep their order.
                let [keyword, cases, arrow, body] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "case", "case keyword")?;
                expect_atom(arrow, "=>", "case arrow")?;
                self.require_declared_tactic(&["Lean", "Parser", "Tactic", "case"])?;
                // The body runs once per `tag | tag`; only one tag is run here.
                let [case] = expect_null_args(cases, "case arguments")? else {
                    return Err(error(TacticError::UnsupportedTactic(kind.clone())));
                };
                let [tag, names] = expect_node(
                    case,
                    &parser_kind(&["Tactic", "caseArg"]),
                    2,
                    "case argument",
                )?
                else {
                    return Err(error(TacticError::MalformedScript));
                };
                let names = expect_null_args(names, "case names")?;
                let goal = self.case_goal(proof, goal, tag)?;
                let goal = self.renamed_proof_goal(proof, goal, names)?;
                self.goal_tags.remove(&goal.id);
                self.start_goal_control(proof, goal, body, control::Mode::Solve)?;
            } else if kind == &parser_kind(&["Tactic", "revert"]) {
                self.revert_proof_locals(proof, goal, args)?;
            } else if kind == &parser_kind(&["Tactic", "generalize"]) {
                // `"generalize " generalizeArg,+ (location)?`: one argument, at the goal.
                let [keyword, arguments, location] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "generalize", "generalize keyword")?;
                expect_empty_null(location, "goal-only generalize location")?;
                let [argument] = expect_null_args(arguments, "generalize arguments")? else {
                    return Err(error(TacticError::MalformedScript));
                };
                let [
                    witness,
                    expression,
                    equality,
                    Syntax::Ident { val: name, .. },
                ] = expect_node(
                    argument,
                    &parser_kind(&["Tactic", "generalizeArg"]),
                    4,
                    "generalize argument",
                )?
                else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(equality, "=", "generalize equality")?;
                let equality = match expect_null_args(witness, "generalize witness")? {
                    [] => None,
                    [Syntax::Ident { val, .. }, colon] => {
                        expect_atom(colon, ":", "generalize witness colon")?;
                        Some(val.clone())
                    }
                    _ => return Err(error(TacticError::MalformedScript)),
                };
                return Ok(ProofAction::Generalize {
                    goal,
                    name: name.clone(),
                    equality,
                    expression,
                });
            } else if kind == &parser_kind(&["Tactic", "change"]) {
                let [keyword, target, location] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "change", "target replacement tactic")?;
                expect_empty_null(location, "goal-only change location")?;
                return Ok(ProofAction::Change { goal, target });
            } else if kind == &parser_kind(&["Tactic", "show"]) {
                // `syntax (name := «show») "show " term : tactic` (`Init/Tactics.lean`): the first
                // goal whose target unifies with the term becomes the main goal, its target
                // replaced by it (`Lean/Elab/Tactic/Show.lean`). Only the main goal is tried here;
                // a later goal the pin would select is refused, never changed.
                let [keyword, target] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "show", "show tactic")?;
                let syntax = Name::from_components(["Lean", "Parser", "Tactic", "show"]);
                if !self.txn.env.contains(&syntax) {
                    return Err(failure(SourceInferenceError::UnknownConstant(syntax)));
                }
                return Ok(ProofAction::Change { goal, target });
            } else if let Some(tactic) = relations::classify(kind) {
                self.relation_proof_goal(proof, goal, tactic, args)?;
            } else if kind == &parser_kind(&["Tactic", "tacticSorry"])
                || kind == &parser_kind(&["Tactic", "tacticAdmit"])
            {
                // `macro "sorry" : tactic => `(tactic| exact sorry)` (`Init/Tactics.lean:459`),
                // and `macro "admit" : tactic => `(tactic| sorry)` beside it. A world whose
                // imports do not reach `Init.Tactics` lacks the macro, and the pin reads the
                // word there as an unexpected token.
                let admit = kind == &parser_kind(&["Tactic", "tacticAdmit"]);
                let [keyword] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(
                    keyword,
                    if admit { "admit" } else { "sorry" },
                    "sorry tactic",
                )?;
                let macro_syntax = Name::from_components([
                    "Lean",
                    "Parser",
                    "Tactic",
                    if admit { "tacticAdmit" } else { "tacticSorry" },
                ]);
                if !self.txn.env.contains(&macro_syntax) {
                    return Err(failure(SourceInferenceError::UnknownConstant(macro_syntax)));
                }
                let sorry = self.labeled_sorry(instruction, goal.target.clone())?;
                self.close_proof_goal(goal, sorry.value)?;
            } else if kind == &parser_kind(&["Tactic", "tacticRfl"]) {
                let [keyword] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "rfl", "reflexivity tactic")?;
                self.rfl_proof_goal(goal)?;
            } else if kind == &parser_kind(&["Tactic", "tacticTrivial"]) {
                let [keyword] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "trivial", "trivial tactic")?;
                self.trivial_proof_goal(goal)?;
            } else if kind == &Name::from_components(["Lean", "calcTactic"]) {
                // The tactic's steps are read as the term's (`start_calculation`).
                return Ok(ProofAction::Term {
                    syntax: instruction,
                    goal,
                    apply: false,
                });
            } else if kind == &parser_kind(&["Tactic", "omega"]) {
                let [keyword, config] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "omega", "linear arithmetic tactic")?;
                expect_default_config(config, "omega configuration")?;
                self.omega_proof_goal(goal)?;
            } else if kind == &parser_kind(&["Tactic", "solveByElim"]) {
                let selection = search::selection(self, args)?;
                self.solve_by_elim_selected_proof_state(proof, goal, &selection)?;
            } else if kind == &parser_kind(&["Tactic", "applyRules"])
                || kind == &parser_kind(&["Tactic", "applyAssumption"])
            {
                self.apply_rule_proof_goal(
                    proof,
                    goal,
                    args,
                    kind == &parser_kind(&["Tactic", "applyAssumption"]),
                )?;
            } else if kind == &parser_kind(&["Tactic", "assumption"]) {
                let [keyword] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "assumption", "assumption keyword")?;
                let value = self
                    .matching_assumption(&goal)?
                    .ok_or_else(|| error(TacticError::NoMatchingAssumption))?;
                self.close_proof_goal(goal, value)?;
            } else {
                let apply = kind == &parser_kind(&["Tactic", "apply"]);
                if !apply && kind != &parser_kind(&["Tactic", "exact"]) {
                    return Err(error(TacticError::UnsupportedTactic(kind.clone())));
                }
                let [keyword, term] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(
                    keyword,
                    if apply { "apply" } else { "exact" },
                    "tactic keyword",
                )?;
                return Ok(ProofAction::Term {
                    syntax: term,
                    goal,
                    apply,
                });
            }
        }
    }

    /// Introduce only a completed local value. The declaration is not in scope
    /// during its own proof. Have hypotheses stay opaque during elaboration;
    /// let declarations are unfoldable. Both retain checked let bindings in the
    /// final term, including unused values and their written type annotations.
    pub(super) fn bind_proof_value(
        &mut self,
        proof: &mut ProofState<'_>,
        mut goal: ProofGoal,
        binding: LocalBinding,
        value: Typed,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let value = self.completed_local_value(value)?;
        self.add_proof_local(&mut goal, binding.name, value, binding.opaque, None)?;
        match binding.replaces {
            Some(replaced) => self.try_clear_proof_local(proof, goal, replaced),
            None => {
                proof.work.push(Work::Goal(goal));
                Ok(())
            }
        }
    }

    /// `specialize e` (`evalSpecialize`, vendored src/Lean/Elab/Tactic/ElabTerm.lean): `e`'s
    /// head, under its lambdas, must be a local hypothesis `h`. `MVarId.replace` (vendored
    /// src/Lean/Meta/Tactic/Replace.lean) adds `h : type of e`, head-beta reduced, right after
    /// the old `h` or after the latest local that type reads, then clears the old `h` unless
    /// something still reads it.
    pub(in crate::source) fn specialize_proof_term(
        &mut self,
        proof: &mut ProofState<'_>,
        mut goal: ProofGoal,
        term: Typed,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let value = self.completed_local_value(term)?;
        let mut head = &value.value;
        while let ExprNode::Lam { body, .. } = head.node() {
            head = body;
        }
        while let ExprNode::App { f, .. } = head.node() {
            head = f;
        }
        let ExprNode::FVar { id } = head.node() else {
            return Err(error(TacticError::SpecializeRequiresLocal));
        };
        let Some(position) = goal.lctx.decls().iter().position(|local| &local.id == id) else {
            return Err(error(TacticError::SpecializeRequiresLocal));
        };
        let replaced = goal.lctx.decls()[position].clone();
        if self.is_matrix_hypothesis(&replaced) {
            return Err(error(TacticError::SpecializeRequiresLocal));
        }
        let type_ = self.head_beta(value.type_)?;
        let reads = self.elimination_reads(&type_)?;
        let after = goal
            .lctx
            .decls()
            .iter()
            .enumerate()
            .filter(|(_, local)| reads.contains(&local.id))
            .map(|(index, _)| index)
            .fold(position, usize::max);
        let value = Typed {
            value: value.value,
            type_,
        };
        self.add_proof_local(&mut goal, replaced.user_name, value, true, Some(after))?;
        self.try_clear_proof_local(proof, goal, replaced.id)
    }

    /// The pin elaborates a tactic `have`/`let` value with `Tactic.elabTerm`,
    /// whose `synthesizeSyntheticMVars (postpone := .no)` applies default
    /// instances and refuses what stays unsynthesized (`have h : String := 1`
    /// fails there, so `first`/`repeat` move on instead of binding it).
    fn completed_local_value(&mut self, value: Typed) -> Result<Typed, NatDefinitionElabError> {
        self.resolve_instances_with_defaults()?;
        self.flush(false)?;
        let value = Typed {
            value: self.instantiate(&value.value)?,
            type_: self.instantiate(&value.type_)?,
        };
        // Expression holes only: universe variables may still be settled later.
        let mut holes = std::collections::HashSet::new();
        holes.extend(self.txn.mvars.collect_mvars(&value.value));
        holes.extend(self.txn.mvars.collect_mvars(&value.type_));
        if !holes.is_empty() {
            return Err(failure(SourceInferenceError::UnresolvedHoles {
                count: holes.len(),
            }));
        }
        Ok(value)
    }

    /// Add a completed local to `goal`: at the end of its context, or right after the local at
    /// position `after`. Its value stays in the final term either way.
    fn add_proof_local(
        &mut self,
        goal: &mut ProofGoal,
        name: Name,
        value: Typed,
        opaque: bool,
        after: Option<usize>,
    ) -> Result<(), NatDefinitionElabError> {
        let id = FVarId(self.fresh_name()?);
        let add = |context: &mut LocalContext| {
            if opaque {
                context.add_param(
                    id.clone(),
                    name.clone(),
                    value.type_.clone(),
                    BinderInfo::Default,
                );
            } else {
                context.add_let(
                    id.clone(),
                    name.clone(),
                    value.type_.clone(),
                    value.value.clone(),
                );
            }
        };
        let context = match after {
            None => {
                let mut context = self.txn.lctx.clone();
                add(&mut context);
                context
            }
            Some(after) => {
                let mut context = LocalContext::new();
                for (index, local) in self.txn.lctx.clone().decls().iter().enumerate() {
                    self.tick()?;
                    eliminate::add_local(&mut context, local);
                    if index == after {
                        add(&mut context);
                    }
                }
                context
            }
        };
        let mut local = context.find(&id).expect("added local").clone();
        local.value = Some(value.value.clone());
        self.txn.lctx = context;
        goal.introduced.push(local);
        goal.lctx = self.txn.lctx.clone();
        Ok(())
    }

    /// `Expr.headBeta`: `(fun x => b) a …` reduced at the head until it is no such redex.
    fn head_beta(&mut self, mut expr: Expr) -> Result<Expr, NatDefinitionElabError> {
        loop {
            self.tick()?;
            let mut arguments = Vec::new();
            let mut head = expr.clone();
            while let ExprNode::App { f, a } = head.node() {
                let (f, a) = (f.clone(), a.clone());
                arguments.push(a);
                head = f;
            }
            let ExprNode::Lam { body, .. } = head.node() else {
                return Ok(expr);
            };
            let Some(argument) = arguments.pop() else {
                return Ok(expr);
            };
            let reduced = self.substitute(body, &argument)?;
            expr = arguments.into_iter().rev().fold(reduced, Expr::app);
        }
    }

    pub(super) fn apply_proof_term(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        term: Typed,
        instance_start: usize,
    ) -> Result<(), NatDefinitionElabError> {
        self.apply_proof_term_ordered(
            proof,
            goal,
            term,
            instance_start,
            ApplyGoalOrder::NonDependentFirst,
        )
    }

    pub(super) fn apply_proof_term_ordered(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        mut term: Typed,
        instance_start: usize,
        order: ApplyGoalOrder,
    ) -> Result<(), NatDefinitionElabError> {
        let mut arguments = Vec::new();
        let mut binder_infos = Vec::new();
        // The pin's `MVarId.apply` tries only the argument counts from `numArgs` less the
        // target's own (`Lean/Meta/Tactic/Apply.lean`). So a conclusion that is still a `∀` is
        // never compared with a target whose head normal form is neither a `∀` nor headed by
        // a metavariable: no assignment makes such a target a `∀`. Each failed
        // `apply PSigma.Lex.right` of the default `decreasing_by` compared every `∀`-prefix of
        // the lemma with `x < x + 1`, unfolding the target each time.
        let target = self.whnf(&goal.target)?;
        let mut target_head = &target;
        while let ExprNode::App { f, .. } = target_head.node() {
            self.tick()?;
            target_head = f;
        }
        let rigid_target = !matches!(
            target_head.node(),
            ExprNode::ForallE { .. } | ExprNode::MVar { .. }
        );
        loop {
            self.tick()?;
            let mut budget = UnificationBudget::new(self.kernel);
            if self
                .well_founded
                .as_ref()
                .is_some_and(|state| state.proving)
            {
                // WF obligations retain ordinary conversion after clean_wf;
                // selected relation dictionaries must match constructor
                // conclusions without opening irreducible definitions.
                budget.transparency = UnificationTransparency::Default;
            }
            let premise_left =
                rigid_target && matches!(term.type_.node(), ExprNode::ForallE { .. });
            if !premise_left
                && self.proof_types_match_with_budget(&term.type_, &goal.target, budget)?
            {
                break;
            }
            term.type_ = self.whnf(&term.type_)?;
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
                ..
            } = term.type_.node()
            else {
                return Err(error(TacticError::ApplyMismatch));
            };
            let domain = binder_type.clone();
            let body = body.clone();
            let tag = binder_name.clone();
            binder_infos.push(*binder_info);
            let argument = if *binder_info == BinderInfo::InstImplicit {
                self.instance_hole(domain)?
            } else {
                let (argument, subgoal) = self.proof_goal(domain)?;
                // Tags are kept whether or not traces are recorded: `case` selects by them.
                self.goal_tags.insert(subgoal.id.clone(), tag);
                arguments.push(subgoal);
                argument
            };
            term.value = Expr::app(term.value, argument.clone());
            term.type_ = self.substitute(&body, &argument)?;
        }
        self.resolve_instances(false)?;
        // Application must discharge its own instance arguments before it
        // commits. Ordinary fields remain goals, but an unavailable dictionary
        // makes this candidate inapplicable, including when its inputs are
        // still unknown. Surrounding terms may have older deferred instances.
        if self.instance_goals[instance_start..]
            .iter()
            .any(|id| !self.txn.mvars.is_assigned(id))
        {
            return Err(error(TacticError::ApplyMismatch));
        }
        let parent = self
            .goal_tags
            .get(&goal.id)
            .cloned()
            .unwrap_or_else(Name::anonymous);
        // The pin's `appendParentTag` (Lean/Meta/Tactic/Apply.lean) reads only the new
        // goals unification left unassigned: a single one inherits the parent's tag, so
        // `apply Prod.Lex.right` on an untagged goal leaves no `case h`; otherwise, under
        // a tagged parent, each is suffixed. Instance holes are all assigned here (above).
        // The pin indexes the binder infos by position among the unassigned goals, not by
        // each goal's own binder; that is kept.
        let unassigned: Vec<MVarId> = arguments
            .iter()
            .filter(|subgoal| !self.txn.mvars.is_assigned(&subgoal.id))
            .map(|subgoal| subgoal.id.clone())
            .collect();
        if let [only] = unassigned.as_slice() {
            self.goal_tags.insert(only.clone(), parent);
        } else if !parent.is_anonymous() {
            for (index, id) in unassigned.iter().enumerate() {
                if binder_infos.get(index) == Some(&BinderInfo::InstImplicit) {
                    continue;
                }
                let child = self
                    .goal_tags
                    .get(id)
                    .cloned()
                    .unwrap_or_else(Name::anonymous);
                self.goal_tags
                    .insert(id.clone(), super::trace::append_tag(&parent, &child));
            }
        }
        proof.work.push(Work::Close(goal, term.value));
        if order == ApplyGoalOrder::Telescope {
            // SolveByElim.constructorAfter explicitly uses newGoals := .all.
            // Keep even assigned holes in order; the worklist skips them.
            proof
                .work
                .extend(arguments.into_iter().rev().map(Work::Goal));
            return Ok(());
        }
        // The pin's apply returns its new goals non-dependent-first
        // (`ApplyConfig.newGoals := ApplyNewGoals.nonDependentFirst`,
        // Init/Meta/Defs.lean:1706): a goal is dependent exactly when another
        // new goal's type mentions its metavariable (`dependsOnOthers`,
        // Lean/Meta/Tactic/Apply.lean:132), and dependent goals come last with
        // each class keeping its telescope order. `constructor`, `left`/`right`
        // and `exists` reach apply with the default config, so they share this
        // order: after `constructor` on `Witness (fun n => n = 7)` the first
        // goal is `?n = 7`, not `n : Nat`. Types are instantiated first so
        // conclusion-matching assignments are visible to the occurs check;
        // goals whose metavariable was already assigned stay in the list and
        // are skipped by advance, as before.
        let mut instantiated = Vec::with_capacity(arguments.len());
        for subgoal in &arguments {
            instantiated.push(self.instantiate(&subgoal.target)?);
        }
        let mut mentioned = std::collections::HashSet::new();
        for (index, type_) in instantiated.iter().enumerate() {
            for id in self.txn.mvars.collect_mvars(type_) {
                if arguments
                    .iter()
                    .enumerate()
                    .any(|(other, subgoal)| other != index && subgoal.id == id)
                {
                    mentioned.insert(id);
                }
            }
        }
        let (non_dependent, dependent): (Vec<_>, Vec<_>) = arguments
            .into_iter()
            .partition(|subgoal| !mentioned.contains(&subgoal.id));
        proof.work.extend(
            non_dependent
                .into_iter()
                .chain(dependent)
                .rev()
                .map(Work::Goal),
        );
        Ok(())
    }
}

/// Decode only the ordinary homogeneous equality head; no lookalike names or
/// Boolean comparisons count as equality propositions.
pub(super) fn equality_target(target: &Expr) -> Option<(Level, Expr, Expr, Expr)> {
    let ExprNode::App { f, a: right } = target.node() else {
        return None;
    };
    let ExprNode::App { f, a: left } = f.node() else {
        return None;
    };
    let ExprNode::App { f, a: alpha } = f.node() else {
        return None;
    };
    let ExprNode::Const { name, levels } = f.node() else {
        return None;
    };
    if name != &Name::from_components(["Eq"]) {
        return None;
    }
    let [level] = levels.as_slice() else {
        return None;
    };
    Some((level.clone(), alpha.clone(), left.clone(), right.clone()))
}
