//! Bidirectional elaboration of the native source subset.
//!
//! Syntax drives one private elaboration transaction. Applications insert typed
//! implicit metavariables; argument and expected-result types generate ordinary
//! unification equations. Only fully instantiated candidates leave this module.
//! The caller still owns final kernel checking and declaration publication.

mod binders;
mod calc;
mod coercions;
pub mod scope;
use scope::SourceScope;
mod equations;
mod inductive;
mod infer;
mod instance_command;
mod instances;
mod level_syntax;
mod levels;
mod local_functions;
pub use level_syntax::LevelSyntaxError;
mod matching;
mod patterns;
mod record;
mod record_terms;
mod recursion;
mod reduce;
mod tactics;

use super::*;
use crate::constraint::unify::{
    UnificationBudget, UnificationDeferred, UnificationError, UnificationTransparency,
};
use fln_core::expr::{FVarId, MVarId};
use fln_core::level::{LMVarId, Level};
use fln_core::options::KVMap;

#[derive(Debug, Clone, PartialEq)]
pub enum SourceInferenceError {
    NameScope(scope::ScopeError),
    Recursion(recursion::RecursionError),
    Match(matching::MatchError),
    Inductive(crate::inductive::InductiveError),
    UnknownConstant(Name),
    LevelSyntax(LevelSyntaxError),
    ExpectedFunction,
    ExpectedType,
    RecordTerm(record_terms::RecordTermError),
    Record(crate::records::RecordError),
    TypeObligation(Box<Outcome<Verdict>>),
    Tactic(tactics::TacticError),
    UnresolvedHoles { count: usize },
    UnresolvedUniverses,
    InstanceSynthesisRequired,
    InvalidInstanceBinder,
    InstanceRegistry(crate::instances::InstanceRegistryError),
    SimpSet(scope::simp::SimpSetError),
    ResourceLimit,
    Scope,
    Universe(crate::universe::UniverseInstantiationError),
    Unification(Box<UnificationError>),
}

impl std::fmt::Display for SourceInferenceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NameScope(error) => write!(f, "{error}"),
            Self::LevelSyntax(reason) => write!(f, "{reason}"),
            Self::Recursion(reason) => write!(f, "{reason}"),
            Self::Match(reason) => write!(f, "{reason}"),
            Self::Inductive(error) => write!(f, "{error}"),
            Self::UnknownConstant(_) => {
                write!(f, "source reference does not name a known constant")
            }
            Self::ExpectedFunction => write!(f, "source application requires a function type"),
            Self::Tactic(error) => write!(f, "{error}"),
            Self::Record(error) => write!(f, "{error}"),
            Self::TypeObligation(outcome) => {
                write!(f, "source type obligation failed: {outcome:?}")
            }
            Self::RecordTerm(error) => write!(f, "{error}"),
            Self::ExpectedType => write!(f, "source annotation requires a type"),
            Self::UnresolvedHoles { count } => write!(
                f,
                "source elaboration left {count} unresolved metavariables"
            ),
            Self::UnresolvedUniverses => write!(f, "source elaboration left unresolved universes"),
            Self::InstanceSynthesisRequired => write!(
                f,
                "native instance search could not resolve all instance arguments"
            ),
            Self::InvalidInstanceBinder => write!(
                f,
                "instance binder must end in a registered class with inferable parameters"
            ),
            Self::InstanceRegistry(error) => write!(f, "{error}"),
            Self::SimpSet(error) => write!(f, "{error}"),
            Self::ResourceLimit => write!(f, "source elaboration work limit reached"),
            Self::Scope => write!(
                f,
                "source elaboration encountered an invalid expression scope"
            ),
            Self::Universe(error) => write!(f, "{error}"),
            Self::Unification(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for SourceInferenceError {}

#[derive(Clone)]
struct Typed {
    value: Expr,
    type_: Expr,
}

#[derive(Clone, Copy)]
enum ImplicitInsertion<'a> {
    ExplicitArgument,
    Expected(Option<&'a Expr>),
    FieldReceiver,
}

/// Source typing constraints survive in the eventual declaration. Selection
/// constraints are different: an instance or rewrite occurrence may be chosen
/// only after equality has actually been established, even for ground terms.
#[derive(Clone, Copy, PartialEq, Eq)]
enum EquationPolicy {
    FinalAdmission,
    BeforeSelection,
}

#[derive(Clone)]
struct SourceEquation {
    sides: (Expr, Expr),
    policy: EquationPolicy,
}

impl SourceEquation {
    fn inference(left: Expr, right: Expr) -> Self {
        Self {
            sides: (left, right),
            policy: EquationPolicy::FinalAdmission,
        }
    }
    fn selection(left: Expr, right: Expr) -> Self {
        Self {
            sides: (left, right),
            policy: EquationPolicy::BeforeSelection,
        }
    }
}

#[derive(Clone)]
struct Context {
    source_scope: SourceScope,
    // Speculative tactics must observe rigid typing failures before choosing
    // their successful alternative. Outside speculation, ordinary final K1
    // admission retains its existing error boundary.
    attempt_depth: usize,
    txn: ElabTxn,
    kernel: Budget,
    next: u64,
    equations: Vec<SourceEquation>,
    instance_goals: Vec<MVarId>,
    level_params: Vec<Name>,
    explicit_levels: usize,
    infer_level_params: bool,
    // Stable private names link raw IHs to checked specializations. Actual
    // declarations in the local context decide visibility, including rollback.
    induction_specializations: Vec<(Name, Name)>,
    matrix_rows: std::collections::HashSet<Name>,
    // Only compiler-generated aliases may expose their already checked referent.
    matrix_aliases: std::collections::HashMap<FVarId, Expr>,
    refinements: Vec<tactics::RefinementFrame>,
    recursion: Option<recursion::Recursion>,
}

fn failure(reason: SourceInferenceError) -> NatDefinitionElabError {
    NatDefinitionElabError::Inference(reason)
}

impl Context {
    fn new(env: &Environment, kernel: Budget) -> Self {
        let mut txn = ElabTxn::new(env.clone(), KVMap::new(), 0);
        txn.budget.max_heartbeats = 1_000_000;
        Self {
            source_scope: SourceScope::default(),
            attempt_depth: 0,
            txn,
            kernel,
            next: 0,
            equations: Vec::new(),
            instance_goals: Vec::new(),
            level_params: Vec::new(),
            explicit_levels: 0,
            infer_level_params: false,
            induction_specializations: Vec::new(),
            matrix_rows: std::collections::HashSet::new(),
            matrix_aliases: std::collections::HashMap::new(),
            refinements: Vec::new(),
            recursion: None,
        }
    }

    fn tick(&mut self) -> Result<(), NatDefinitionElabError> {
        self.txn
            .budget
            .check_heartbeat()
            .map_err(|_| failure(SourceInferenceError::ResourceLimit))
    }

    fn fresh_name(&mut self) -> Result<Name, NatDefinitionElabError> {
        self.tick()?;
        let id = self.next;
        self.next = self
            .next
            .checked_add(1)
            .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
        Ok(Name::num(Name::from_components(["_fln_source"]), id))
    }

    fn level(&mut self) -> Result<Level, NatDefinitionElabError> {
        Ok(Level::mvar(LMVarId(self.fresh_name()?)))
    }

    fn type_expected(&mut self) -> Result<Expr, NatDefinitionElabError> {
        Ok(Expr::sort(self.level()?))
    }

    fn hole(&mut self, type_: Expr) -> Result<Expr, NatDefinitionElabError> {
        let name = self.fresh_name()?;
        let id = MVarId(name.clone());
        self.txn.mvars.declare(
            id.clone(),
            name,
            type_,
            self.txn.lctx.clone(),
            MetavarKind::Natural,
            0,
            None,
        );
        Ok(Expr::mvar(id))
    }

    fn instantiate(&mut self, value: &Expr) -> Result<Expr, NatDefinitionElabError> {
        self.tick()?;
        self.txn
            .instantiate_expr(value)
            .map_err(|error| failure(SourceInferenceError::Universe(error)))
    }

    fn substitute(&mut self, body: &Expr, argument: &Expr) -> Result<Expr, NatDefinitionElabError> {
        self.tick()?;
        body.subst_loose(0, std::slice::from_ref(argument))
            .map_err(|_| failure(SourceInferenceError::Scope))
    }

    fn constant(&mut self, name: &Name) -> Result<Typed, NatDefinitionElabError> {
        let info = self
            .txn
            .env
            .find(name)
            .cloned()
            .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(name.clone())))?;
        let base = info.constant_val();
        let mut levels = Vec::new();
        for _ in &base.level_params {
            levels.push(self.level()?);
        }
        let type_ = self.instantiate_params(&base.type_, &base.level_params, &levels)?;
        Ok(Typed {
            value: Expr::const_(name.clone(), levels),
            type_,
        })
    }

    fn atom(
        &mut self,
        syntax: &Syntax,
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        if let Syntax::Node { kind, args, .. } = syntax {
            if kind == &parser_kind(&["Term", "syntheticHole"]) {
                let [question, label] = args.as_slice() else {
                    return Err(failure(SourceInferenceError::Scope));
                };
                expect_atom(question, "?", "synthetic hole")?;
                let name = match label {
                    Syntax::Atom { val, .. } if val == "_" => None,
                    Syntax::Ident { val, .. }
                        if !val.is_anonymous() && val.parent().is_anonymous() =>
                    {
                        Some(val.clone())
                    }
                    _ => return Err(failure(SourceInferenceError::Scope)),
                };
                return self.synthetic_proof_hole(name, expected);
            }
            if kind == &parser_kind(&["Term", "hole"]) {
                let [hole] = args.as_slice() else {
                    return Err(failure(SourceInferenceError::Scope));
                };
                expect_atom(hole, "_", "placeholder")?;
                let type_ = match expected {
                    Some(type_) => type_.clone(),
                    None => {
                        let level = self.level()?;
                        self.hole(Expr::sort(level))?
                    }
                };
                return Ok(Typed {
                    value: self.hole(type_.clone())?,
                    type_,
                });
            }
            let level = if kind == &parser_kind(&["Term", "type"]) {
                Some(self.source_sort(args, true)?)
            } else if kind == &parser_kind(&["Term", "sort"]) {
                Some(self.source_sort(args, false)?)
            } else if kind == &parser_kind(&["Term", "explicitUniv"]) {
                return self.explicit_universes(args);
            } else if kind == &parser_kind(&["Term", "prop"]) {
                let [keyword] = args.as_slice() else {
                    return Err(failure(SourceInferenceError::Scope));
                };
                expect_atom(keyword, "Prop", "proposition universe")?;
                Some(Level::zero())
            } else {
                None
            };
            if let Some(level) = level {
                let type_ = Expr::sort(
                    level
                        .clone()
                        .succ()
                        .map_err(|_| failure(SourceInferenceError::Scope))?,
                );
                return Ok(Typed {
                    value: Expr::sort(level),
                    type_,
                });
            }
        }
        if let Syntax::Ident { val: name, .. } = syntax {
            if name.is_anonymous() {
                return Err(NatDefinitionElabError::AnonymousReferenceName);
            }
            if let Some(local) = self
                .txn
                .lctx
                .decls()
                .iter()
                .rev()
                .find(|local| &local.user_name == name)
            {
                return Ok(Typed {
                    value: self
                        .matrix_aliases
                        .get(&local.id)
                        .cloned()
                        .unwrap_or_else(|| Expr::fvar(local.id.clone())),
                    type_: local.type_.clone(),
                });
            }
            let resolved = self
                .resolve_source_name(name)?
                .unwrap_or_else(|| name.clone());
            if let Some(local) = self.txn.lctx.find_by_user_name(&resolved) {
                return Ok(Typed {
                    value: self
                        .matrix_aliases
                        .get(&local.id)
                        .cloned()
                        .unwrap_or_else(|| Expr::fvar(local.id.clone())),
                    type_: local.type_.clone(),
                });
            }
            let name = &resolved;
            if let Some(recursion) = &self.recursion
                && &recursion.name == name
            {
                return Ok(recursion.reference.clone());
            }
            let mut resolved = name.clone();
            if !self.txn.env.contains(name) {
                if let Some(term) = self.qualified_record_field(name)? {
                    return Ok(term);
                }
                if name == &Name::from_components(["true"]) {
                    resolved = Name::from_components(["Bool", "true"]);
                }
                if name == &Name::from_components(["false"]) {
                    resolved = Name::from_components(["Bool", "false"]);
                }
            }
            return self.constant(&resolved);
        }
        let value = elaborate_atom(syntax, &[], true, Some(&self.txn.env))?;
        let type_ = match value.node() {
            ExprNode::Lit {
                literal: Literal::Nat(_),
            } => nat_const(),
            ExprNode::Lit {
                literal: Literal::Str(_),
            } => string_const(),
            _ => return Err(failure(SourceInferenceError::ExpectedType)),
        };
        Ok(Typed { value, type_ })
    }

    fn whnf(&mut self, expr: &Expr) -> Result<Expr, NatDefinitionElabError> {
        self.whnf_with_transparency(expr, UnificationTransparency::SafeDefinitions, true)
    }

    fn whnf_with_transparency(
        &mut self,
        expr: &Expr,
        transparency: UnificationTransparency,
        zeta_delta: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        self.reduce_source_head(expr, transparency, zeta_delta)
    }

    /// Enough type reconstruction to generate the universe side of an implicit
    /// type assignment. This is a constraint producer, not a trusted checker.
    fn leaf_type(&mut self, expression: &Expr) -> Result<Option<Expr>, NatDefinitionElabError> {
        let expression = self.instantiate(expression)?;
        match expression.node() {
            ExprNode::Sort { level } => Ok(Some(Expr::sort(
                level
                    .clone()
                    .succ()
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
            ))),
            ExprNode::MVar { id } => Ok(self.txn.mvars.get_decl(id).map(|decl| decl.type_.clone())),
            ExprNode::FVar { id } => Ok(self.txn.lctx.find(id).map(|local| local.type_.clone())),
            ExprNode::Const { name, levels } => {
                let Some(info) = self.txn.env.find(name).cloned() else {
                    return Ok(None);
                };
                let base = info.constant_val();
                Ok(Some(self.instantiate_params(
                    &base.type_,
                    &base.level_params,
                    levels,
                )?))
            }
            ExprNode::Lit {
                literal: Literal::Nat(_),
            } => Ok(Some(nat_const())),
            ExprNode::Lit {
                literal: Literal::Str(_),
            } => Ok(Some(string_const())),
            _ => Ok(None),
        }
    }

    fn constrain_type(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        // Source type conversion unfolds safe definitions, including dictionary
        // projections. Instance candidate matching retains its narrower policy.
        let actual = self.instantiate(actual)?;
        let expected = self.instantiate(expected)?;
        // Preserve a named type when assigning an unknown expected type; its
        // identity may determine which class instance is eligible.
        let actual = if matches!(expected.node(), ExprNode::MVar { .. })
            && matches!(
                actual.node(),
                ExprNode::Const { .. } | ExprNode::FVar { .. }
            ) {
            actual
        } else {
            self.whnf(&actual)?
        };
        // An unknown type must retain the named target it is assigned. Unfolding
        // Alias here would make inferInstance accept a non-reducible class head.
        let expected = if matches!(actual.node(), ExprNode::MVar { .. }) {
            expected
        } else {
            self.whnf(&expected)?
        };
        self.constrain(&actual, &expected)
    }

    fn constrain(&mut self, actual: &Expr, expected: &Expr) -> Result<(), NatDefinitionElabError> {
        let actual = self.instantiate(actual)?;
        let expected = self.instantiate(expected)?;
        if !actual.has_expr_mvar()
            && !expected.has_expr_mvar()
            && !actual.has_level_mvar()
            && !expected.has_level_mvar()
        {
            self.check_attempt_equation(&actual, &expected)?;
            // Closed constraints are checked by the declaration's ordinary K1
            // admission. Keeping them there preserves its original verdict.
            return Ok(());
        }
        if let (Some(left), Some(right)) = (self.known_type(&actual)?, self.known_type(&expected)?)
            && (left.has_level_mvar() || right.has_level_mvar())
        {
            self.equations.push(SourceEquation::inference(left, right));
        }
        self.equations
            .push(SourceEquation::inference(actual, expected));
        self.flush(false)
    }

    /// Keep the abbreviation-only solution when it succeeds: eagerly unfolding
    /// named types can change later instance selection. Only ordinary typing
    /// equations that defer receive a second, safe-definition conversion pass.
    /// Both attempts use the transactional solver and retain their spent work;
    /// resource failures and selection queries never take this fallback.
    fn unify_source_batch(
        &mut self,
        pairs: &[(Expr, Expr)],
        allow_delta: bool,
    ) -> Result<(), UnificationError> {
        let mut result =
            self.txn
                .unify_many_with(pairs, UnificationBudget::new(self.kernel), &|| false);
        if allow_delta
            && matches!(
                &result,
                Err(UnificationError::Deferred(
                    UnificationDeferred::UnsupportedEquation | UnificationDeferred::NotAPattern
                ))
            )
        {
            let mut budget = UnificationBudget::new(self.kernel);
            budget.transparency = UnificationTransparency::SafeDefinitions;
            result = self.txn.unify_many_with(pairs, budget, &|| false);
        }
        result.map(|report| assert!(report.awakened.is_empty(), "private source queue"))
    }

    fn flush(&mut self, final_pass: bool) -> Result<(), NatDefinitionElabError> {
        loop {
            if self.equations.is_empty() {
                return Ok(());
            }
            self.tick()?;
            let mut pairs = Vec::with_capacity(self.equations.len());
            for index in 0..self.equations.len() {
                self.tick()?;
                pairs.push(self.equations[index].sides.clone());
            }
            let allow_delta = self
                .equations
                .iter()
                .all(|equation| equation.policy == EquationPolicy::FinalAdmission);
            let deferred = match self.unify_source_batch(&pairs, allow_delta) {
                Ok(()) => {
                    self.equations.clear();
                    return Ok(());
                }
                Err(error @ UnificationError::Deferred(_)) => error,
                Err(error) => {
                    return Err(failure(SourceInferenceError::Unification(Box::new(error))));
                }
            };
            // A failed selection query is a nonmatch, not a reason to replay
            // all of its rigid subequations. Keep the original atomic matcher
            // and its work cost; only ordinary source inference is resumed.
            if self
                .equations
                .iter()
                .any(|equation| equation.policy == EquationPolicy::BeforeSelection)
            {
                return if final_pass {
                    Err(failure(SourceInferenceError::Unification(Box::new(
                        deferred,
                    ))))
                } else {
                    Ok(())
                };
            }
            // An explicit opaque proof hole can postpone an entire batch, even
            // when an independent equation determines its argument type. Keep
            // the joint solver first (it handles interdependent assignments),
            // then publish individually K1-checked progress only inside this
            // private source transaction and retry the blocked obligations.
            let generation = self.txn.mvars.assignments().len() + self.txn.universes.len();
            let pending = std::mem::take(&mut self.equations);
            for mut equation in pending {
                self.tick()?;
                let left = self.instantiate(&equation.sides.0)?;
                let right = self.instantiate(&equation.sides.1)?;
                if equation.policy == EquationPolicy::FinalAdmission
                    && !left.has_expr_mvar()
                    && !right.has_expr_mvar()
                    && !left.has_level_mvar()
                    && !right.has_level_mvar()
                {
                    self.check_attempt_equation(&left, &right)?;
                    // Exactly the same policy as `constrain`: once inference
                    // has finished, the retained source terms and annotations
                    // are obligations of the final ordinary K1 declaration.
                    continue;
                }
                match self.unify_source_batch(
                    &[(left.clone(), right.clone())],
                    equation.policy == EquationPolicy::FinalAdmission,
                ) {
                    Ok(()) => {}
                    Err(UnificationError::Deferred(_)) => {
                        equation.sides = (left, right);
                        self.equations.push(equation);
                    }
                    Err(error) => {
                        return Err(failure(SourceInferenceError::Unification(Box::new(error))));
                    }
                }
            }
            if self.equations.is_empty() {
                return Ok(());
            }
            if generation == self.txn.mvars.assignments().len() + self.txn.universes.len() {
                return if final_pass {
                    Err(failure(SourceInferenceError::Unification(Box::new(
                        deferred,
                    ))))
                } else {
                    Ok(())
                };
            }
        }
    }

    fn insert_implicits(
        &mut self,
        mut term: Typed,
        insertion: ImplicitInsertion<'_>,
    ) -> Result<Typed, NatDefinitionElabError> {
        loop {
            self.tick()?;
            let reduced = self.whnf(&term.type_)?;
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = reduced.node()
            else {
                break;
            };
            let insert = match binder_info {
                BinderInfo::Default => false,
                BinderInfo::Implicit | BinderInfo::InstImplicit => {
                    !matches!(insertion, ImplicitInsertion::Expected(None))
                }
                BinderInfo::StrictImplicit => {
                    matches!(insertion, ImplicitInsertion::ExplicitArgument)
                }
            };
            if !insert {
                term.type_ = reduced;
                break;
            }
            if let ImplicitInsertion::Expected(Some(expected)) = insertion {
                let expected = self.whnf(expected)?;
                if matches!(expected.node(), ExprNode::ForallE { binder_info: style, .. } if style == binder_info)
                {
                    term.type_ = reduced;
                    break;
                }
            }
            let body = body.clone();
            let argument = if *binder_info == BinderInfo::InstImplicit {
                self.instance_hole(binder_type.clone())?
            } else {
                self.hole(binder_type.clone())?
            };
            term.value = Expr::app(term.value, argument.clone());
            term.type_ = self.substitute(&body, &argument)?;
        }
        Ok(term)
    }

    fn finish_term(
        &mut self,
        term: Typed,
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let term = self.insert_implicits(term, ImplicitInsertion::Expected(expected))?;
        self.finish_explicit_term(term, expected)
    }

    fn finish_explicit_term(
        &mut self,
        mut term: Typed,
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        // Resolve known dictionaries before their dependent result types enter
        // unification. Unknown class inputs still wait for the expected type.
        self.resolve_instances(false)?;
        if let Some(expected) = expected {
            term = self.coerce_expected(term, expected)?;
        }
        self.resolve_instances(false)?;
        term.value = self.lower_matrix_call(&term.value)?;
        Ok(term)
    }

    /// Explicit application is a property of this syntactic head, not of a
    /// value or its binder types. It must not leak into argument elaboration.
    fn explicit_application_head<'a>(
        &mut self,
        mut syntax: &'a Syntax,
    ) -> Result<(&'a Syntax, bool), NatDefinitionElabError> {
        loop {
            self.tick()?;
            if let Some(inner) = parenthesized_inner(syntax)? {
                syntax = inner;
                continue;
            }
            let kind = parser_kind(&["Term", "explicit"]);
            if syntax.kind() != Some(&kind) {
                return Ok((syntax, false));
            }
            let parts = expect_node(syntax, &kind, 2, "explicit application")?;
            expect_atom(&parts[0], "@", "explicit application prefix")?;
            let head = &parts[1];
            if !matches!(head, Syntax::Ident { .. })
                && head.kind() != Some(&parser_kind(&["Term", "explicitUniv"]))
                && head.kind() != Some(&parser_kind(&["Term", "proj"]))
            {
                return Err(failure(SourceInferenceError::ExpectedFunction));
            }
            return Ok((head, true));
        }
    }

    fn term(
        &mut self,
        syntax: &Syntax,
        expected: Option<Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let syntax = self.lower_pattern_matrices(syntax)?;
        self.term_prepared(&syntax, expected)
    }

    fn term_prepared(
        &mut self,
        syntax: &Syntax,
        expected: Option<Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        enum Task<'a> {
            CalcNext(calc::Build<'a>),
            CalcRelation(calc::Build<'a>),
            CalcProof(calc::Build<'a>, Expr),
            MatrixScope(Vec<Name>),
            MatchDiscriminant(matching::MatchParts<'a>, Option<Expr>),
            MatchNext(matching::MatchBuild<'a>),
            MatchBranch(matching::MatchBuild<'a>, matching::BranchBinders),
            Ascription(&'a Syntax, Option<Expr>),
            AscribedValue(Expr, Option<Expr>),
            Projection(Name, Option<Expr>, bool),
            RecordType(record_terms::RecordParts<'a>, Option<Expr>),
            RecordPrepare(record_terms::RecordParts<'a>, Option<Expr>, Vec<Typed>),
            RecordSource(record_terms::RecordParts<'a>, Option<Expr>, Vec<Typed>),
            RecordNext(record_terms::RecordBuild<'a>),
            RecordField(record_terms::RecordBuild<'a>, Expr),
            Visit(&'a Syntax, Option<Expr>, bool),
            Function(&'a [Syntax], Option<Expr>, bool),
            Argument(Typed, Expr, &'a [Syntax], Option<Expr>, bool),
            Apply(Typed, &'a [Syntax], Option<Expr>, bool),
            Infix(BoundedInfixIntrinsic, Option<Expr>),
            Arrow(Option<Expr>),
            BinderNext(binders::Telescope<'a>),
            BinderDomain(binders::Telescope<'a>),
            BinderBody(binders::Telescope<'a>),
            LocalFunctionAnnotation(local_functions::Build<'a>),
            LocalFunctionValue(local_functions::Build<'a>),
            LetAnnotation(Name, &'a Syntax, &'a Syntax, Option<Expr>),
            LetValue(Name, Option<Expr>, &'a Syntax, Option<Expr>),
            LetBody(LocalContext, FVarId, Name, Typed),
            RewriteTerm(
                tactics::ProofState<'a>,
                tactics::ProofGoal,
                bool,
                std::collections::VecDeque<tactics::RewriteRule<'a>>,
                bool,
            ),
            Proof(tactics::ProofState<'a>),
            ProofEliminate(
                tactics::ProofState<'a>,
                tactics::ProofGoal,
                &'a [Syntax],
                bool,
                Option<Name>,
            ),
            ProofCases(tactics::ProofState<'a>, tactics::ProofGoal, Name),
            ProofGeneralize(
                tactics::ProofState<'a>,
                tactics::ProofGoal,
                Name,
                Option<Name>,
            ),
            ProofBindingType(
                tactics::ProofState<'a>,
                tactics::ProofGoal,
                Name,
                &'a Syntax,
                bool,
            ),
            ProofBindingValue(
                tactics::ProofState<'a>,
                tactics::ProofGoal,
                Name,
                Option<Expr>,
                bool,
            ),
            ProofTerm(tactics::ProofState<'a>, tactics::ProofGoal, Option<usize>),
            RefineTerm(tactics::ProofState<'a>, tactics::ProofGoal, usize),
        }
        let mut tasks = vec![Task::Visit(syntax, expected, true)];
        let mut values: Vec<Typed> = Vec::new();
        let mut attempts: Vec<tactics::backtrack::Checkpoint<'_>> = Vec::new();
        loop {
            let result = (|| {
                while let Some(task) = tasks.pop() {
                    self.tick()?;
                    match task {
                        Task::CalcNext(build) => {
                            if let Some(step) = build.steps.get(build.cursor) {
                                let relation = &step[0];
                                tasks.push(Task::CalcRelation(build));
                                tasks.push(Task::Visit(
                                    relation,
                                    Some(Expr::sort(Level::zero())),
                                    true,
                                ));
                            } else {
                                values.push(self.finish_calculation(build)?);
                            }
                        }
                        Task::CalcRelation(mut build) => {
                            let relation = values.pop().expect("calculation relation visit");
                            let relation = self.prepare_calculation_step(&mut build, relation)?;
                            let proof = &build.steps[build.cursor][2];
                            tasks.push(Task::CalcProof(build, relation.clone()));
                            tasks.push(Task::Visit(proof, Some(relation), true));
                        }
                        Task::CalcProof(mut build, relation) => {
                            let proof = values.pop().expect("calculation step proof visit");
                            self.add_calculation_step(&mut build, relation, proof)?;
                            tasks.push(Task::CalcNext(build));
                        }
                        Task::MatrixScope(rows) => {
                            for row in rows {
                                self.tick()?;
                                if !self.matrix_rows.remove(&row) {
                                    return Err(failure(SourceInferenceError::Match(
                                        matching::MatchError::UnreachableRow,
                                    )));
                                }
                            }
                        }
                        Task::Visit(syntax, expected, finish) => {
                            if let Some(inner) = parenthesized_inner(syntax)? {
                                tasks.push(Task::Visit(inner, expected, finish));
                                continue;
                            }
                            let (head, explicit) = self.explicit_application_head(syntax)?;
                            if explicit {
                                tasks.push(Task::Function(&[], expected, true));
                                tasks.push(Task::Visit(head, None, false));
                                continue;
                            }
                            if let Syntax::Node { kind, args, .. } = syntax {
                                if kind == &parser_kind(&["Term", "matrixScope"]) {
                                    let [rows, body] = args.as_slice() else {
                                        return Err(failure(SourceInferenceError::Scope));
                                    };
                                    let mut names = Vec::new();
                                    for row in expect_null_args(rows, "pattern coverage witnesses")?
                                    {
                                        self.tick()?;
                                        let Syntax::Ident { val, .. } = row else {
                                            return Err(failure(SourceInferenceError::Scope));
                                        };
                                        names.push(val.clone());
                                    }
                                    tasks.push(Task::MatrixScope(names));
                                    tasks.push(Task::Visit(body, expected, finish));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "matrixAlias"]) {
                                    let [Syntax::Ident { val: name, .. }, subject, body] =
                                        args.as_slice()
                                    else {
                                        return Err(failure(SourceInferenceError::Scope));
                                    };
                                    let value = self.atom(subject, None)?;
                                    if !matches!(value.value.node(), ExprNode::FVar { .. }) {
                                        return Err(failure(SourceInferenceError::Scope));
                                    }
                                    let saved = self.txn.lctx.clone();
                                    let id = FVarId(self.fresh_name()?);
                                    self.txn.lctx.add_let(
                                        id.clone(),
                                        name.clone(),
                                        value.type_.clone(),
                                        value.value.clone(),
                                    );
                                    self.matrix_aliases.insert(id.clone(), value.value.clone());
                                    tasks.push(Task::LetBody(saved, id, name.clone(), value));
                                    tasks.push(Task::Visit(body, expected, finish));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "matrixBranch"]) {
                                    let [Syntax::Ident { val, .. }, body] = args.as_slice() else {
                                        return Err(failure(SourceInferenceError::Scope));
                                    };
                                    self.matrix_rows.insert(val.clone());
                                    tasks.push(Task::Visit(body, expected, finish));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "forall"])
                                    || kind == &parser_kind(&["Term", "fun"])
                                    || kind == &parser_kind(&["Term", "depArrow"])
                                {
                                    let lambda = kind == &parser_kind(&["Term", "fun"]);
                                    tasks.push(Task::BinderNext(
                                        self.start_telescope(syntax, expected, lambda)?,
                                    ));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "match"])
                                    || kind == &parser_kind(&["Term", "matchMatrix"])
                                    || kind == &parser_kind(&["Term", "ifThenElse"])
                                {
                                    let parts = self.match_parts(syntax)?;
                                    let discriminant = parts.discriminant;
                                    tasks.push(Task::MatchDiscriminant(parts, expected));
                                    tasks.push(Task::Visit(discriminant, None, true));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "proj"]) {
                                    let parts = expect_node(syntax, kind, 3, "field projection")?;
                                    expect_atom(&parts[1], ".", "field dot")?;
                                    let Syntax::Ident { val: field, .. } = &parts[2] else {
                                        return Err(failure(SourceInferenceError::Scope));
                                    };
                                    tasks.push(Task::Projection(field.clone(), expected, finish));
                                    tasks.push(Task::Visit(&parts[0], None, true));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "typeAscription"]) {
                                    let parts = expect_node(syntax, kind, 5, "term ascription")?;
                                    expect_atom(&parts[2], ":", "ascription colon")?;
                                    let [annotation] =
                                        expect_null_args(&parts[3], "ascribed type")?
                                    else {
                                        return Err(failure(SourceInferenceError::Scope));
                                    };
                                    tasks.push(Task::Ascription(&parts[1], expected));
                                    tasks.push(Task::Visit(
                                        annotation,
                                        Some(self.type_expected()?),
                                        true,
                                    ));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "structInst"]) {
                                    let parts = self.record_parts(syntax)?;
                                    if let Some(annotation) = parts.annotation {
                                        tasks.push(Task::RecordType(parts, expected));
                                        tasks.push(Task::Visit(
                                            annotation,
                                            Some(self.type_expected()?),
                                            true,
                                        ));
                                    } else {
                                        tasks.push(Task::RecordPrepare(
                                            parts,
                                            expected,
                                            Vec::new(),
                                        ));
                                    }
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "calc"]) {
                                    tasks.push(Task::CalcNext(
                                        self.start_calculation(syntax, expected)?,
                                    ));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "byTactic"]) {
                                    tasks.push(Task::Proof(self.start_proof(syntax, expected)?));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "let"]) {
                                    let binding = self.let_parts(args)?;
                                    if !expect_null_args(
                                        binding.parameters,
                                        "local function parameters",
                                    )?
                                    .is_empty()
                                    {
                                        let build = self.start_local_function(binding, expected)?;
                                        if let Some(annotation) = build.binding.annotation {
                                            tasks.push(Task::LocalFunctionAnnotation(build));
                                            tasks.push(Task::Visit(
                                                annotation,
                                                Some(self.type_expected()?),
                                                true,
                                            ));
                                        } else {
                                            let value = build.binding.value;
                                            tasks.push(Task::LocalFunctionValue(build));
                                            tasks.push(Task::Visit(value, None, true));
                                        }
                                        continue;
                                    }
                                    let local_functions::Binding {
                                        name,
                                        annotation,
                                        value,
                                        body,
                                        ..
                                    } = binding;
                                    if let Some(annotation) = annotation {
                                        tasks
                                            .push(Task::LetAnnotation(name, value, body, expected));
                                        tasks.push(Task::Visit(
                                            annotation,
                                            Some(self.type_expected()?),
                                            true,
                                        ));
                                    } else {
                                        tasks.push(Task::LetValue(name, None, body, expected));
                                        tasks.push(Task::Visit(value, None, true));
                                    }
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "arrow"]) {
                                    let [domain, arrow, codomain] = args.as_slice() else {
                                        return Err(failure(SourceInferenceError::Scope));
                                    };
                                    if !matches!(arrow, Syntax::Atom { val, .. } if val == "->" || val == "→")
                                    {
                                        return Err(failure(SourceInferenceError::Scope));
                                    }
                                    tasks.push(Task::Arrow(expected));
                                    tasks.push(Task::Visit(
                                        codomain,
                                        Some(self.type_expected()?),
                                        true,
                                    ));
                                    tasks.push(Task::Visit(
                                        domain,
                                        Some(self.type_expected()?),
                                        true,
                                    ));
                                    continue;
                                }
                                if kind == &Name::str(Name::anonymous(), "term¬_") {
                                    let parts =
                                        expect_node(syntax, kind, 2, "propositional negation")?;
                                    expect_atom(&parts[0], "¬", "negation prefix")?;
                                    let function =
                                        self.constant(&Name::from_components(["Not"]))?;
                                    tasks.push(Task::Apply(function, &parts[1..], expected, false));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "app"]) {
                                    let parts = expect_node(syntax, kind, 2, "application")?;
                                    let arguments =
                                        expect_null_args(&parts[1], "application arguments")?;
                                    if arguments.is_empty() {
                                        return Err(failure(
                                            SourceInferenceError::ExpectedFunction,
                                        ));
                                    }
                                    let (head, explicit) =
                                        self.explicit_application_head(&parts[0])?;
                                    tasks.push(Task::Function(arguments, expected, explicit));
                                    tasks.push(Task::Visit(head, None, false));
                                    continue;
                                }
                                if let Some(intrinsic) = bounded_infix_intrinsic(kind, true) {
                                    let parts = expect_node(syntax, kind, 3, "scalar infix")?;
                                    expect_atom(
                                        &parts[1],
                                        intrinsic.spelling(),
                                        "scalar operator",
                                    )?;
                                    tasks.push(Task::Infix(intrinsic, expected));
                                    tasks.push(Task::Visit(&parts[2], None, true));
                                    tasks.push(Task::Visit(&parts[0], None, true));
                                    continue;
                                }
                            }
                            let term = self.atom(syntax, expected.as_ref())?;
                            values.push(if finish {
                                // Numerals in this bounded frontend are Nat terms,
                                // not an excuse to bypass OfNat by coercing them.
                                // An explicitly ascribed Nat can still be coerced.
                                if matches!(
                                    term.value.node(),
                                    ExprNode::Lit {
                                        literal: Literal::Nat(_)
                                    }
                                ) {
                                    if let Some(expected) = &expected {
                                        self.constrain_type(&term.type_, expected)?;
                                    }
                                    self.resolve_instances(false)?;
                                    term
                                } else {
                                    self.finish_term(term, expected.as_ref())?
                                }
                            } else {
                                term
                            });
                        }
                        Task::Projection(field, expected, finish) => {
                            let receiver = values.pop().expect("receiver precedes projection");
                            let term = self.record_field_path(receiver, &field)?;
                            values.push(if finish {
                                self.finish_term(term, expected.as_ref())?
                            } else {
                                term
                            });
                        }
                        Task::MatchDiscriminant(parts, expected) => {
                            let major = values.pop().expect("match discriminant visit");
                            tasks.push(match self.start_match(parts, major, expected)? {
                                matching::MatchStart::Regular(state) => Task::MatchNext(*state),
                                matching::MatchStart::Refined(proof) => Task::Proof(proof),
                            });
                        }
                        Task::MatchNext(mut state) => match self.next_match_branch(&mut state)? {
                            matching::MatchStep::Branch {
                                syntax,
                                expected,
                                binders,
                            } => {
                                tasks.push(Task::MatchBranch(state, binders));
                                tasks.push(Task::Visit(syntax, Some(expected), true));
                            }
                            matching::MatchStep::Complete(term) => values.push(term),
                        },
                        Task::MatchBranch(mut state, binders) => {
                            let branch = values.pop().expect("match branch visit");
                            self.accept_match_branch(&mut state, binders, branch)?;
                            tasks.push(Task::MatchNext(state));
                        }
                        Task::Ascription(syntax, expected) => {
                            let type_ = values.pop().expect("ascription type visit");
                            self.sort_level(&type_)?;
                            tasks.push(Task::AscribedValue(type_.value.clone(), expected));
                            tasks.push(Task::Visit(syntax, Some(type_.value), true));
                        }
                        Task::AscribedValue(annotation, expected) => {
                            let term = values.pop().expect("ascribed term follows its annotation");
                            // The value's actual type guides surrounding inference.
                            // The written annotation still constrains the inner value
                            // and remains in the checked term even when ignored later.
                            // Expected types guide inference but closed constraints are
                            // left to K1. Retain this assertion in the checked term,
                            // including when the surrounding program ignores its value.
                            let ascribed = Typed {
                                value: Expr::let_e(
                                    Name::anonymous(),
                                    annotation.clone(),
                                    term.value,
                                    Expr::bvar(0).expect("fixed ascription identity binder"),
                                    false,
                                ),
                                type_: term.type_,
                            };
                            // Coerce outside the assertion: its inner annotation
                            // must remain checked even if a conversion discards it.
                            values.push(self.finish_term(ascribed, expected.as_ref())?);
                        }
                        Task::RecordType(parts, expected) => {
                            let type_ = values.pop().expect("record type visit");
                            self.sort_level(&type_)?;
                            if let Some(expected) = expected {
                                self.constrain_type(&type_.value, &expected)?;
                            }
                            tasks.push(Task::RecordPrepare(parts, Some(type_.value), Vec::new()));
                        }
                        Task::RecordPrepare(parts, expected, sources) => {
                            if let Some(syntax) = parts.sources.get(sources.len()).copied() {
                                tasks.push(Task::RecordSource(parts, expected, sources));
                                tasks.push(Task::Visit(syntax, None, true));
                            } else {
                                tasks.push(Task::RecordNext(
                                    self.start_record(parts, expected, sources)?,
                                ));
                            }
                        }
                        Task::RecordSource(parts, expected, mut sources) => {
                            sources.push(values.pop().expect("record update source visit"));
                            tasks.push(Task::RecordPrepare(parts, expected, sources));
                        }
                        Task::RecordNext(mut state) => match self.next_record_field(&mut state)? {
                            record_terms::RecordStep::Field {
                                syntax,
                                domain,
                                codomain,
                            } => {
                                tasks.push(Task::RecordField(state, codomain));
                                tasks.push(Task::Visit(syntax, Some(domain), true));
                            }
                            record_terms::RecordStep::Copy { value, codomain } => {
                                self.accept_record_field(&mut state, &codomain, value)?;
                                tasks.push(Task::RecordNext(state));
                            }
                            record_terms::RecordStep::Complete(term) => values.push(term),
                        },
                        Task::RecordField(mut state, codomain) => {
                            let value = values.pop().expect("record field visit");
                            self.accept_record_field(&mut state, &codomain, value)?;
                            tasks.push(Task::RecordNext(state));
                        }
                        Task::Proof(mut proof) => match self.advance_proof(&mut proof)? {
                            tactics::ProofAction::Eliminate {
                                goal,
                                args,
                                induction,
                                equation,
                                expression,
                            } => {
                                self.txn.lctx = goal.lctx.clone();
                                tasks.push(Task::ProofEliminate(
                                    proof, goal, args, induction, equation,
                                ));
                                tasks.push(Task::Visit(expression, None, true));
                            }
                            tactics::ProofAction::Cases {
                                goal,
                                name,
                                proposition,
                            } => {
                                self.txn.lctx = goal.lctx.clone();
                                tasks.push(Task::ProofCases(proof, goal, name));
                                tasks.push(Task::Visit(
                                    proposition,
                                    Some(Expr::sort(Level::zero())),
                                    true,
                                ));
                            }
                            tactics::ProofAction::Attempt(spec) => {
                                let mut checkpoint = tactics::backtrack::Checkpoint::new(
                                    self,
                                    &proof,
                                    spec,
                                    tasks.len(),
                                    values.len(),
                                );
                                let branch = checkpoint.begin(self, attempts.len())?;
                                attempts.push(checkpoint);
                                tasks.push(Task::Proof(branch));
                            }
                            tactics::ProofAction::AttemptComplete(index) => {
                                if index + 1 != attempts.len() {
                                    return Err(failure(SourceInferenceError::Scope));
                                }
                                let checkpoint = attempts.pop().expect("checked attempt index");
                                if checkpoint.tasks != tasks.len()
                                    || checkpoint.values != values.len()
                                {
                                    return Err(failure(SourceInferenceError::Scope));
                                }
                                checkpoint.finish(self, &mut proof);
                                if let Some(mut next) = checkpoint.next_iteration(self, &proof) {
                                    proof = next.begin(self, attempts.len())?;
                                    attempts.push(next);
                                }
                                tasks.push(Task::Proof(proof));
                            }
                            tactics::ProofAction::Refine { syntax, goal } => {
                                self.txn.lctx = goal.lctx.clone();
                                let expected = goal.target.clone();
                                let depth = self.begin_refinement();
                                tasks.push(Task::RefineTerm(proof, goal, depth));
                                tasks.push(Task::Visit(syntax, Some(expected), true));
                            }
                            tactics::ProofAction::Binding {
                                goal,
                                name,
                                annotation,
                                value,
                                opaque,
                            } => {
                                self.txn.lctx = goal.lctx.clone();
                                if let Some(annotation) = annotation {
                                    tasks.push(Task::ProofBindingType(
                                        proof, goal, name, value, opaque,
                                    ));
                                    tasks.push(Task::Visit(
                                        annotation,
                                        Some(self.type_expected()?),
                                        true,
                                    ));
                                } else {
                                    tasks.push(Task::ProofBindingValue(
                                        proof, goal, name, None, opaque,
                                    ));
                                    tasks.push(Task::Visit(value, None, true));
                                }
                            }
                            tactics::ProofAction::Generalize {
                                goal,
                                name,
                                equality,
                                expression,
                            } => {
                                self.txn.lctx = goal.lctx.clone();
                                tasks.push(Task::ProofGeneralize(proof, goal, name, equality));
                                tasks.push(Task::Visit(expression, None, true));
                            }
                            tactics::ProofAction::Rewrite {
                                goal,
                                rule,
                                remaining,
                                close,
                            } => {
                                self.txn.lctx = goal.lctx.clone();
                                tasks.push(Task::RewriteTerm(
                                    proof,
                                    goal,
                                    rule.reverse,
                                    remaining,
                                    close,
                                ));
                                tasks.push(Task::Visit(rule.syntax, None, true));
                            }
                            tactics::ProofAction::Term {
                                syntax,
                                goal,
                                apply,
                            } => {
                                let expected = if apply {
                                    None
                                } else {
                                    Some(goal.target.clone())
                                };
                                self.txn.lctx = goal.lctx.clone();
                                // Written arguments can insert implicit dictionaries
                                // before apply starts opening the remaining telescope.
                                let instance_start = apply.then_some(self.instance_goals.len());
                                tasks.push(Task::ProofTerm(proof, goal, instance_start));
                                tasks.push(Task::Visit(syntax, expected, true));
                            }
                            tactics::ProofAction::Complete(term) => values.push(term),
                        },
                        Task::ProofEliminate(mut proof, goal, args, induction, equation) => {
                            let term = values.pop().expect("elimination expression visit");
                            self.eliminate_proof_term(
                                &mut proof, goal, args, induction, equation, term,
                            )?;
                            tasks.push(Task::Proof(proof));
                        }
                        Task::ProofCases(mut proof, goal, name) => {
                            let proposition = values.pop().expect("case proposition visit");
                            self.split_decision_goal(&mut proof, goal, name, proposition)?;
                            tasks.push(Task::Proof(proof));
                        }
                        Task::ProofGeneralize(mut proof, goal, name, equality) => {
                            let term = values.pop().expect("generalized expression visit");
                            self.generalize_proof_term(&mut proof, goal, name, equality, term)?;
                            tasks.push(Task::Proof(proof));
                        }
                        Task::ProofBindingType(proof, goal, name, value, opaque) => {
                            let annotation = values.pop().expect("local proof annotation visit");
                            self.sort_level(&annotation)?;
                            tasks.push(Task::ProofBindingValue(
                                proof,
                                goal,
                                name,
                                Some(annotation.value.clone()),
                                opaque,
                            ));
                            tasks.push(Task::Visit(value, Some(annotation.value), true));
                        }
                        Task::ProofBindingValue(mut proof, goal, name, annotation, opaque) => {
                            let mut value = values.pop().expect("local proof value visit");
                            if let Some(annotation) = annotation {
                                value.type_ = annotation;
                            }
                            self.bind_proof_value(&mut proof, goal, name, value, opaque)?;
                            tasks.push(Task::Proof(proof));
                        }
                        Task::RewriteTerm(mut proof, goal, reverse, remaining, close) => {
                            let term = values.pop().expect("rewrite rule visit");
                            self.rewrite_proof_term(
                                &mut proof, goal, term, reverse, remaining, close,
                            )?;
                            tasks.push(Task::Proof(proof));
                        }
                        Task::RefineTerm(mut proof, goal, depth) => {
                            let term = values.pop().expect("refinement term visit");
                            self.finish_refinement(&mut proof, goal, term, depth)?;
                            tasks.push(Task::Proof(proof));
                        }
                        Task::ProofTerm(mut proof, goal, instance_start) => {
                            let term = values.pop().expect("tactic term visit");
                            if let Some(instance_start) = instance_start {
                                self.apply_proof_term(&mut proof, goal, term, instance_start)?;
                            } else {
                                // A speculative `exact` must not select an alternative
                                // merely because its implicit arguments deferred. On
                                // a fixed goal, validate its candidate before dropping
                                // the checkpoint so a bad `exact rfl` can fall back.
                                let target = self.instantiate(&goal.target)?;
                                if self.attempt_depth != 0
                                    && !target.has_expr_mvar()
                                    && !target.has_level_mvar()
                                {
                                    let check = self.hole(target)?;
                                    let value = self.instantiate(&term.value)?;
                                    let mut budget = UnificationBudget::new(self.kernel);
                                    budget.transparency = UnificationTransparency::SafeDefinitions;
                                    let report = self.txn.unify(&check, &value, budget).map_err(
                                        |reason| {
                                            failure(SourceInferenceError::Unification(Box::new(
                                                reason,
                                            )))
                                        },
                                    )?;
                                    assert!(report.awakened.is_empty(), "private source queue");
                                }
                                self.close_proof_goal(goal, term.value)?;
                            }
                            tasks.push(Task::Proof(proof));
                        }
                        Task::Function(arguments, expected, explicit) => {
                            let function = values.pop().expect("function task follows its visit");
                            tasks.push(Task::Apply(function, arguments, expected, explicit));
                        }
                        Task::Apply(function, arguments, expected, explicit) => {
                            if let Some((first, rest)) = arguments.split_first() {
                                let function = if explicit {
                                    function
                                } else {
                                    self.insert_implicits(
                                        function,
                                        ImplicitInsertion::ExplicitArgument,
                                    )?
                                };
                                let function = self.coerce_function(function)?;
                                let ExprNode::ForallE {
                                    binder_type, body, ..
                                } = function.type_.node()
                                else {
                                    return Err(failure(SourceInferenceError::ExpectedFunction));
                                };
                                let domain = binder_type.clone();
                                let codomain = body.clone();
                                // Propagate a known result before checking the last
                                // explicit argument when the codomain does not depend
                                // on that argument (e.g. Inhabited.mk (fun x => ...)).
                                if rest.is_empty()
                                    && !codomain.has_loose_bvar(0)
                                    && let Some(expected) = &expected
                                {
                                    self.constrain_result_hint(&codomain, expected)?;
                                }
                                tasks.push(Task::Argument(
                                    function, codomain, rest, expected, explicit,
                                ));
                                tasks.push(Task::Visit(first, Some(domain), true));
                            } else {
                                values.push(if explicit {
                                    self.finish_explicit_term(function, expected.as_ref())?
                                } else {
                                    self.finish_term(function, expected.as_ref())?
                                });
                            }
                        }
                        Task::Argument(function, codomain, rest, expected, explicit) => {
                            let argument = values.pop().expect("argument task follows its visit");
                            let type_ = self.substitute(&codomain, &argument.value)?;
                            tasks.push(Task::Apply(
                                Typed {
                                    value: Expr::app(function.value, argument.value),
                                    type_,
                                },
                                rest,
                                expected,
                                explicit,
                            ));
                        }
                        Task::Infix(intrinsic, expected) => {
                            let right = values.pop().expect("infix right visit");
                            let left = values.pop().expect("infix left visit");
                            self.flush(false)?;
                            let name = match intrinsic {
                                BoundedInfixIntrinsic::Fixed { intrinsic, .. } => intrinsic,
                                BoundedInfixIntrinsic::ScalarBeq => {
                                    if self.instantiate(&left.type_)? == string_const()
                                        && self.instantiate(&right.type_)? == string_const()
                                    {
                                        Name::from_components(["String", "decEq"])
                                    } else {
                                        Name::from_components(["Nat", "beq"])
                                    }
                                }
                            };
                            let mut function = self.constant(&name)?;
                            for argument in [left, right] {
                                function = self.insert_implicits(
                                    function,
                                    ImplicitInsertion::ExplicitArgument,
                                )?;
                                let ExprNode::ForallE {
                                    binder_type, body, ..
                                } = function.type_.node()
                                else {
                                    return Err(failure(SourceInferenceError::ExpectedFunction));
                                };
                                let domain = binder_type.clone();
                                let body = body.clone();
                                let argument = self.finish_term(argument, Some(&domain))?;
                                self.constrain_type(&argument.type_, &domain)?;
                                function.type_ = self.substitute(&body, &argument.value)?;
                                function.value = Expr::app(function.value, argument.value);
                            }
                            values.push(self.finish_term(function, expected.as_ref())?);
                        }
                        Task::BinderNext(mut state) => {
                            if let Some(syntax) = self.next_telescope_domain(&mut state)? {
                                tasks.push(Task::BinderDomain(state));
                                tasks.push(Task::Visit(syntax, Some(self.type_expected()?), true));
                            } else {
                                let expected = self.telescope_body_expected(&state)?;
                                let syntax = state.body;
                                tasks.push(Task::BinderBody(state));
                                tasks.push(Task::Visit(syntax, expected, true));
                            }
                        }
                        Task::BinderDomain(mut state) => {
                            let domain = values.pop().expect("telescope domain visit");
                            self.open_telescope_group(&mut state, Some(domain))?;
                            tasks.push(Task::BinderNext(state));
                        }
                        Task::BinderBody(state) => {
                            let body = values.pop().expect("telescope body visit");
                            values.push(self.finish_telescope(state, body)?);
                        }
                        Task::Arrow(expected) => {
                            let right = values.pop().expect("arrow codomain visit");
                            let left = values.pop().expect("arrow domain visit");
                            let u = self.sort_level(&left)?;
                            let v = self.sort_level(&right)?;
                            let level = Level::imax(u, v)
                                .map_err(|_| failure(SourceInferenceError::Scope))?;
                            let body = right
                                .value
                                .lift_loose(0, 1)
                                .map_err(|_| failure(SourceInferenceError::Scope))?;
                            let term = Typed {
                                value: Expr::forall_e(
                                    Name::anonymous(),
                                    left.value,
                                    body,
                                    BinderInfo::Default,
                                ),
                                type_: Expr::sort(level),
                            };
                            values.push(self.finish_term(term, expected.as_ref())?);
                        }
                        Task::LocalFunctionAnnotation(mut build) => {
                            let annotation = values.pop().expect("local function annotation visit");
                            self.sort_level(&annotation)?;
                            build.result_type = Some(annotation.value.clone());
                            let value = build.binding.value;
                            tasks.push(Task::LocalFunctionValue(build));
                            tasks.push(Task::Visit(value, Some(annotation.value), true));
                        }
                        Task::LocalFunctionValue(build) => {
                            let value = values.pop().expect("local function value visit");
                            let value = self.close_local_function(&build, value)?;
                            values.push(value);
                            tasks.push(Task::LetValue(
                                build.binding.name,
                                None,
                                build.binding.body,
                                build.expected,
                            ));
                        }
                        Task::LetAnnotation(name, value, body, expected) => {
                            let annotation = values.pop().expect("let annotation visit");
                            self.sort_level(&annotation)?;
                            tasks.push(Task::LetValue(
                                name,
                                Some(annotation.value.clone()),
                                body,
                                expected,
                            ));
                            tasks.push(Task::Visit(value, Some(annotation.value), true));
                        }
                        Task::LetValue(name, annotation, body, expected) => {
                            let mut value = values.pop().expect("let value visit");
                            if let Some(annotation) = annotation {
                                value.type_ = annotation;
                            }
                            let saved = self.txn.lctx.clone();
                            let id = FVarId(self.fresh_name()?);
                            self.txn.lctx.add_let(
                                id.clone(),
                                name.clone(),
                                value.type_.clone(),
                                value.value.clone(),
                            );
                            tasks.push(Task::LetBody(saved, id, name, value));
                            tasks.push(Task::Visit(body, expected, true));
                        }
                        Task::LetBody(saved, id, name, value) => {
                            self.matrix_aliases.remove(&id);
                            let mut body = values.pop().expect("let body visit");
                            body.value = self.instantiate(&body.value)?;
                            body.type_ = self.instantiate(&body.type_)?;
                            let abstract_body = body
                                .value
                                .abstract_fvar(&id, 0)
                                .map_err(|_| failure(SourceInferenceError::Scope))?;
                            let abstract_type = body
                                .type_
                                .abstract_fvar(&id, 0)
                                .map_err(|_| failure(SourceInferenceError::Scope))?;
                            let type_ = self.substitute(&abstract_type, &value.value)?;
                            values.push(Typed {
                                value: Expr::let_e(
                                    name,
                                    value.type_,
                                    value.value,
                                    abstract_body,
                                    false,
                                ),
                                type_,
                            });
                            self.txn.lctx = saved;
                        }
                    }
                }
                let [result] = values.as_slice() else {
                    return Err(failure(SourceInferenceError::Scope));
                };
                Ok(result.clone())
            })();
            match result {
                Ok(value) => return Ok(value),
                Err(problem) => {
                    if !tactics::backtrack::recoverable(&problem) {
                        return Err(problem);
                    }
                    loop {
                        let Some(mut checkpoint) = attempts.pop() else {
                            return Err(problem);
                        };
                        tasks.truncate(checkpoint.tasks);
                        values.truncate(checkpoint.values);
                        checkpoint.restore(self);
                        self.tick()?;
                        if checkpoint.retry() {
                            let proof = checkpoint.begin(self, attempts.len())?;
                            attempts.push(checkpoint);
                            tasks.push(Task::Proof(proof));
                            break;
                        }
                        if checkpoint.optional() {
                            tasks.push(Task::Proof(checkpoint.original()));
                            break;
                        }
                    }
                }
            }
        }
    }

    fn let_parts<'a>(
        &mut self,
        parts: &'a [Syntax],
    ) -> Result<local_functions::Binding<'a>, NatDefinitionElabError> {
        let [keyword, config, declaration, separator, body] = parts else {
            return Err(failure(SourceInferenceError::Scope));
        };
        expect_atom(keyword, "let", "let keyword")?;
        let config = expect_node(
            config,
            &parser_kind(&["Term", "letConfig"]),
            1,
            "let config",
        )?;
        expect_empty_null(&config[0], "empty let config")?;
        let wrapper = expect_node(
            declaration,
            &parser_kind(&["Term", "letDecl"]),
            1,
            "let declaration",
        )?;
        let declaration = expect_node(
            &wrapper[0],
            &parser_kind(&["Term", "letIdDecl"]),
            5,
            "let binding",
        )?;
        let id = expect_node(
            &declaration[0],
            &parser_kind(&["Term", "letId"]),
            1,
            "let identifier",
        )?;
        let Syntax::Ident { val: name, .. } = &id[0] else {
            return Err(failure(SourceInferenceError::Scope));
        };
        if name.is_anonymous() {
            return Err(NatDefinitionElabError::AnonymousReferenceName);
        }
        expect_null_args(&declaration[1], "local function parameters")?;
        let annotation = optional_type_syntax(&declaration[2])?;
        expect_atom(&declaration[3], ":=", "let assignment")?;
        expect_atom(separator, ";", "let separator")?;
        Ok(local_functions::Binding {
            name: name.clone(),
            parameters: &declaration[1],
            annotation,
            value: &declaration[4],
            body,
        })
    }

    fn sort_level(&mut self, term: &Typed) -> Result<Level, NatDefinitionElabError> {
        let type_ = self.whnf(&term.type_)?;
        let ExprNode::Sort { level } = type_.node() else {
            return Err(failure(SourceInferenceError::ExpectedType));
        };
        Ok(level.clone())
    }

    fn type_term(&mut self, syntax: &Syntax) -> Result<Expr, NatDefinitionElabError> {
        // Carry the sort into the term so implicit insertion happens while
        // annotation-local lets and their instance dictionaries remain in scope.
        let expected = self.type_expected()?;
        let term = self.term(syntax, Some(expected))?;
        self.sort_level(&term)?;
        Ok(term.value)
    }

    fn require_resolved(&self, terms: &[Expr]) -> Result<(), NatDefinitionElabError> {
        let mut holes = std::collections::HashSet::new();
        for term in terms {
            holes.extend(self.txn.mvars.collect_mvars(term));
        }
        if !holes.is_empty() {
            return Err(failure(SourceInferenceError::UnresolvedHoles {
                count: holes.len(),
            }));
        }
        if terms.iter().any(Expr::has_level_mvar) {
            return Err(failure(SourceInferenceError::UnresolvedUniverses));
        }
        Ok(())
    }

    fn finish(&mut self, term: Typed) -> Result<Typed, NatDefinitionElabError> {
        self.resolve_instances(true)?;
        self.flush(true)?;
        let value = self.instantiate(&term.value)?;
        let type_ = self.instantiate(&term.type_)?;
        self.require_resolved(&[value.clone(), type_.clone()])?;
        Ok(Typed { value, type_ })
    }
}

fn optional_type_syntax(syntax: &Syntax) -> Result<Option<&Syntax>, NatDefinitionElabError> {
    let parts = expect_null_args(syntax, "optional type")?;
    if parts.is_empty() {
        return Ok(None);
    }
    let [annotation] = parts else {
        return Err(failure(SourceInferenceError::Scope));
    };
    let parts = expect_node(
        annotation,
        &parser_kind(&["Term", "typeSpec"]),
        2,
        "type ascription",
    )?;
    expect_atom(&parts[0], ":", "type ascription colon")?;
    Ok(Some(&parts[1]))
}

impl Context {
    fn bind_parameters(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Vec<LocalDecl>, NatDefinitionElabError> {
        let mut parameters = Vec::new();
        for syntax in expect_null_args(syntax, "declaration binders")? {
            let Syntax::Node { kind, .. } = syntax else {
                return Err(failure(SourceInferenceError::Scope));
            };
            if kind == &parser_kind(&["Term", "instBinder"]) {
                let parts = expect_node(syntax, kind, 4, "instance binder")?;
                expect_atom(&parts[0], "[", "instance binder opener")?;
                expect_atom(&parts[3], "]", "instance binder closer")?;
                let optional = expect_null_args(&parts[1], "optional instance name")?;
                let user_name = match optional {
                    [] => self.fresh_name()?,
                    [Syntax::Ident { val, .. }, colon] => {
                        expect_atom(colon, ":", "instance name colon")?;
                        val.clone()
                    }
                    _ => return Err(failure(SourceInferenceError::Scope)),
                };
                let domain = self.type_term(&parts[2])?;
                self.validate_instance_binder(&domain)?;
                let id = FVarId(self.fresh_name()?);
                self.txn.lctx.add_param(
                    id.clone(),
                    user_name.clone(),
                    domain.clone(),
                    BinderInfo::InstImplicit,
                );
                parameters.push(self.txn.lctx.find(&id).expect("inserted parameter").clone());
                continue;
            }
            let (style, open, close, arity) = if kind == &parser_kind(&["Term", "implicitBinder"]) {
                (BinderInfo::Implicit, "{", "}", 4)
            } else if kind == &parser_kind(&["Term", "strictImplicitBinder"]) {
                (BinderInfo::StrictImplicit, "⦃", "⦄", 4)
            } else if kind == &parser_kind(&["Term", "explicitBinder"]) {
                (BinderInfo::Default, "(", ")", 5)
            } else {
                return Err(failure(SourceInferenceError::Scope));
            };
            let parts = expect_node(syntax, kind, arity, "typed binder")?;
            expect_atom(&parts[0], open, "binder opener")?;
            expect_atom(&parts[arity - 1], close, "binder closer")?;
            if style == BinderInfo::Default {
                expect_empty_null(&parts[3], "absent binder default")?;
            }
            let names = expect_null_args(&parts[1], "binder names")?;
            if names.is_empty() {
                return Err(failure(SourceInferenceError::Scope));
            }
            let type_parts = expect_null_args(&parts[2], "binder type")?;
            let [colon, type_syntax] = type_parts else {
                return Err(failure(SourceInferenceError::ExpectedType));
            };
            expect_atom(colon, ":", "binder type ascription")?;
            let domain = self.type_term(type_syntax)?;
            for name in names {
                let Syntax::Ident { val: name, .. } = name else {
                    return Err(failure(SourceInferenceError::Scope));
                };
                let id = FVarId(self.fresh_name()?);
                self.txn
                    .lctx
                    .add_param(id.clone(), name.clone(), domain.clone(), style);
                parameters.push(self.txn.lctx.find(&id).expect("inserted parameter").clone());
            }
        }
        Ok(parameters)
    }
}

pub(super) fn definition(
    syntax: &Syntax,
    environment: &Environment,
    kernel: Budget,
) -> Result<Declaration, NatDefinitionElabError> {
    definition_scoped(syntax, environment, kernel, &SourceScope::default())
}

fn definition_scoped(
    syntax: &Syntax,
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<Declaration, NatDefinitionElabError> {
    let mut context = Context::scoped(environment, kernel, scope);
    let declaration = expect_node(
        syntax,
        &parser_kind(&["Command", "declaration"]),
        2,
        "declaration",
    )?;
    let modifiers = expect_node(
        &declaration[0],
        &parser_kind(&["Command", "declModifiers"]),
        7,
        "declaration modifiers",
    )?;
    scope::simp::registration(syntax)?;
    for (index, modifier) in modifiers.iter().enumerate() {
        if index != 1 {
            expect_empty_null(modifier, "empty declaration modifier")?;
        }
    }
    let is_instance = matches!(&declaration[1], Syntax::Node { kind,.. } if kind==&parser_kind(&["Command","instance"]));
    let is_theorem = matches!(&declaration[1], Syntax::Node { kind,.. } if kind==&parser_kind(&["Command","theorem"]));
    let instance_parts;
    let definition = if is_instance {
        let parts = instance_command::parts(&declaration[1])?;
        instance_parts = [
            parts.keyword.clone(),
            parts.id.clone(),
            parts.signature.clone(),
            parts.value.clone(),
        ];
        &instance_parts[..]
    } else {
        let parts = expect_node(
            &declaration[1],
            &parser_kind(&["Command", if is_theorem { "theorem" } else { "definition" }]),
            if is_theorem { 4 } else { 5 },
            "named declaration",
        )?;
        expect_atom(
            &parts[0],
            if is_theorem { "theorem" } else { "def" },
            "declaration keyword",
        )?;
        parts
    };
    let id = expect_node(
        &definition[1],
        &parser_kind(&["Command", "declId"]),
        2,
        "declaration id",
    )?;
    let Syntax::Ident { val: name, .. } = &id[0] else {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    };
    if name.is_anonymous() {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    }
    let name = &context.enter_declaration(name)?;
    context.declare_levels(&id[1])?;
    context.infer_level_params = true;
    let signature = expect_node(
        &definition[2],
        &parser_kind(&[
            "Command",
            if is_theorem || is_instance {
                "declSig"
            } else {
                "optDeclSig"
            },
        ]),
        2,
        "declaration signature",
    )?;
    let mut parameters = context.bind_parameters(&signature[0])?;
    let mut expected = if is_theorem || is_instance {
        let parts = expect_node(
            &signature[1],
            &parser_kind(&["Term", "typeSpec"]),
            2,
            "theorem type",
        )?;
        expect_atom(&parts[0], ":", "theorem type colon")?;
        Some(context.type_term(&parts[1])?)
    } else {
        optional_type_syntax(&signature[1])?
            .map(|syntax| context.type_term(syntax))
            .transpose()?
    };
    context.infer_level_params = false;
    // Later binders may determine earlier class inputs, but the body may not
    // rescue a stuck header instance. An explicit result also closes ordinary
    // header holes; inferred results may still constrain ordinary parameters.
    context.resolve_instances(true)?;
    if let Some(expected) = &expected {
        context.flush(true)?;
        let mut types = Vec::with_capacity(parameters.len() + 1);
        for parameter in &parameters {
            types.push(context.instantiate(&parameter.type_)?);
        }
        types.push(context.instantiate(expected)?);
        // Universe holes may still be constrained by the body. Ordinary term
        // holes and unresolved header instances must not cross this boundary.
        context.require_resolved_terms(&types)?;
    }
    let equations = definition[3].kind() == Some(&parser_kind(&["Command", "declValEqns"]));
    let (body, termination, where_clause) = if equations {
        let parts = expect_node(
            &definition[3],
            &parser_kind(&["Command", "declValEqns"]),
            3,
            "equation value",
        )?;
        (&parts[0], &parts[1], &parts[2])
    } else {
        let parts = expect_node(
            &definition[3],
            &parser_kind(&["Command", "declValSimple"]),
            4,
            "definition value",
        )?;
        expect_atom(&parts[0], ":=", "definition assignment")?;
        (&parts[1], &parts[2], &parts[3])
    };
    let termination = expect_node(
        termination,
        &parser_kind(&["Termination", "suffix"]),
        2,
        "termination suffix",
    )?;
    for part in termination {
        expect_empty_null(part, "absent termination clause")?;
    }
    expect_empty_null(where_clause, "absent where clause")?;
    if !is_theorem && !is_instance {
        expect_empty_null(&definition[4], "absent definition clauses")?;
    }
    if is_instance {
        context.validate_instance_binder(
            expected
                .as_ref()
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?,
        )?;
    }
    let generated;
    let body = if equations {
        let declared_type = expected
            .as_ref()
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let (syntax, result_type) =
            context.equation_function(body, declared_type, &mut parameters)?;
        generated = syntax;
        expected = Some(result_type);
        &generated
    } else {
        body
    };
    let mut term = context.definition_body(name, &parameters, body, expected.clone())?;
    if let Some(expected) = expected {
        term.type_ = expected;
    }
    let mut universe_roots: Vec<_> = parameters
        .iter()
        .map(|parameter| parameter.type_.clone())
        .collect();
    universe_roots.extend([term.type_.clone(), term.value.clone()]);
    context.generalize_declaration_universes(&universe_roots)?;
    let mut term = context.finish(term)?;
    term.value = eta_expand_nondependent(term.value, &term.type_)?;
    for local in parameters.into_iter().rev() {
        let LocalDecl {
            id,
            user_name: name,
            type_: domain,
            binder_info: style,
            ..
        } = local;
        let domain = context.instantiate(&domain)?;
        term.value = term
            .value
            .abstract_fvar(&id, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        term.type_ = term
            .type_
            .abstract_fvar(&id, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        term.value = Expr::lam(name.clone(), domain.clone(), term.value, style);
        term.type_ = Expr::forall_e(name, domain, term.type_, style);
    }
    let term = context.finish(term)?;
    if term.value.has_fvar()
        || term.type_.has_fvar()
        || term.value.has_loose_bvars()
        || term.type_.has_loose_bvars()
    {
        return Err(failure(SourceInferenceError::Scope));
    }
    let level_params = context.declaration_levels(&[term.type_.clone(), term.value.clone()])?;
    let base = ConstantVal {
        name: name.clone(),
        level_params,
        type_: term.type_,
    };
    if is_theorem {
        Ok(Declaration::Thm(fln_env::constants::TheoremVal {
            base,
            value: term.value,
            all: vec![name.clone()],
        }))
    } else {
        Ok(Declaration::Defn(DefinitionVal {
            base,
            value: term.value,
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![name.clone()],
        }))
    }
}

pub(super) fn query(
    syntax: &Syntax,
    name: Name,
    environment: &Environment,
    kernel: Budget,
    evaluate: bool,
) -> Result<Declaration, NatDefinitionElabError> {
    if !name.parent().is_anonymous() || !matches!(name.leaf_view(), LeafView::Num(_)) {
        return Err(if evaluate {
            NatDefinitionElabError::InvalidGeneratedEvaluationName
        } else {
            NatDefinitionElabError::InvalidGeneratedCheckName
        });
    }
    let parts = expect_node(
        syntax,
        &parser_kind(&["Command", if evaluate { "eval" } else { "check" }]),
        2,
        if evaluate {
            "Lean.Parser.Command.eval"
        } else {
            "Lean.Parser.Command.check"
        },
    )?;
    expect_atom(
        &parts[0],
        if evaluate { "#eval" } else { "#check" },
        "query keyword",
    )?;
    let mut context = Context::new(environment, kernel);
    let term = context.term(&parts[1], None)?;
    let mut term = context.finish(term)?;
    if evaluate {
        term.value = eta_expand_nondependent(term.value, &term.type_)?;
    }
    Ok(Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name.clone(),
            level_params: Vec::new(),
            type_: term.type_,
        },
        value: term.value,
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![name],
    }))
}

/// Registration requested by a canonical named source instance. The caller must
/// still obtain ordinary declaration admission before installing this metadata.
pub fn instance_registration(
    syntax: &Syntax,
) -> Result<Option<(Name, u32)>, NatDefinitionElabError> {
    instance_command::registration(syntax)
}

pub use inductive::{elaborate_inductive, is_inductive};
/// A source record/class expands to a block and projections, not one definition.
/// These are untrusted candidates. The caller must admit the whole sequence
/// before registering the class or exposing any successor.
pub use record::{SourceRecord, elaborate_record, is_record};
