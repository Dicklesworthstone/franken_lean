//! Bidirectional elaboration of the native source subset.
//!
//! Syntax drives one private elaboration transaction. Applications insert typed
//! implicit metavariables; argument and expected-result types generate ordinary
//! unification equations. Only fully instantiated candidates leave this module.
//! The caller still owns final kernel checking and declaration publication.

mod inductive;
mod infer;
mod instance_command;
mod instances;
mod levels;
mod matching;
mod patterns;
mod record;
mod record_terms;
mod recursion;
mod reduce;
mod tactics;

use super::*;
use crate::constraint::unify::{UnificationBudget, UnificationError, UnificationTransparency};
use fln_core::expr::{FVarId, MVarId};
use fln_core::level::{LMVarId, Level};
use fln_core::options::KVMap;

#[derive(Debug, Clone, PartialEq)]
pub enum SourceInferenceError {
    Recursion(recursion::RecursionError),
    Match(matching::MatchError),
    Inductive(crate::inductive::InductiveError),
    UnknownConstant(Name),
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
    ResourceLimit,
    Scope,
    Universe(crate::universe::UniverseInstantiationError),
    Unification(Box<UnificationError>),
}

impl std::fmt::Display for SourceInferenceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
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

#[derive(Clone)]
struct Context {
    txn: ElabTxn,
    kernel: Budget,
    next: u64,
    equations: Vec<(Expr, Expr)>,
    instance_goals: Vec<MVarId>,
    // Stable private names link raw IHs to checked specializations. Actual
    // declarations in the local context decide visibility, including rollback.
    induction_specializations: Vec<(Name, Name)>,
    matrix_rows: std::collections::HashSet<Name>,
    // Only compiler-generated aliases may expose their already checked referent.
    matrix_aliases: std::collections::HashMap<FVarId, Expr>,
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
            txn,
            kernel,
            next: 0,
            equations: Vec::new(),
            instance_goals: Vec::new(),
            induction_specializations: Vec::new(),
            matrix_rows: std::collections::HashSet::new(),
            matrix_aliases: std::collections::HashMap::new(),
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
                let [keyword, level] = args.as_slice() else {
                    return Err(failure(SourceInferenceError::Scope));
                };
                expect_atom(keyword, "Type", "type universe")?;
                expect_empty_null(level, "absent universe level")?;
                Some(Level::one())
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
            // Closed constraints are checked by the declaration's ordinary K1
            // admission. Keeping them there preserves its original verdict.
            return Ok(());
        }
        if let (Some(left), Some(right)) = (self.known_type(&actual)?, self.known_type(&expected)?)
            && (left.has_level_mvar() || right.has_level_mvar())
        {
            self.equations.push((left, right));
        }
        self.equations.push((actual, expected));
        self.flush(false)
    }

    fn flush(&mut self, final_pass: bool) -> Result<(), NatDefinitionElabError> {
        if self.equations.is_empty() {
            return Ok(());
        }
        self.tick()?;
        match self.txn.unify_many_with(
            &self.equations,
            UnificationBudget::new(self.kernel),
            &|| false,
        ) {
            Ok(report) => {
                assert!(
                    report.awakened.is_empty(),
                    "this private source transaction has no queued consumer work"
                );
                self.equations.clear();
                Ok(())
            }
            Err(UnificationError::Deferred(_)) if !final_pass => Ok(()),
            Err(error) => Err(failure(SourceInferenceError::Unification(Box::new(error)))),
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
        let mut term = self.insert_implicits(term, ImplicitInsertion::Expected(expected))?;
        // Resolve known dictionaries before their dependent result types enter
        // unification. Unknown class inputs still wait for the expected type.
        self.resolve_instances(false)?;
        if let Some(expected) = expected {
            self.constrain_type(&term.type_, expected)?;
        }
        self.resolve_instances(false)?;
        term.value = self.lower_matrix_call(&term.value)?;
        Ok(term)
    }

    fn term(
        &mut self,
        syntax: &Syntax,
        expected: Option<Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let (syntax, required) = self.lower_pattern_matrices(syntax)?;
        let result = self.term_prepared(&syntax, expected)?;
        for row in required {
            if !self.matrix_rows.remove(&row) {
                return Err(failure(SourceInferenceError::Match(
                    matching::MatchError::UnreachableRow,
                )));
            }
        }
        Ok(result)
    }

    fn term_prepared(
        &mut self,
        syntax: &Syntax,
        expected: Option<Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        enum Task<'a> {
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
            Function(&'a [Syntax], Option<Expr>),
            Argument(Typed, Expr, &'a [Syntax], Option<Expr>),
            Apply(Typed, &'a [Syntax], Option<Expr>),
            Infix(BoundedInfixIntrinsic, Option<Expr>),
            Arrow(Option<Expr>),
            ForallDomain(&'a [Syntax], &'a Syntax, Option<Expr>),
            ForallBody(LocalContext, Vec<LocalDecl>, Level, Option<Expr>),
            LetAnnotation(Name, &'a Syntax, &'a Syntax, Option<Expr>),
            LetValue(Name, Option<Expr>, &'a Syntax, Option<Expr>),
            LetBody(LocalContext, FVarId, Name, Typed),
            Lambda(LocalContext, Vec<LocalDecl>, Option<Expr>),
            RewriteTerm(
                tactics::ProofState<'a>,
                tactics::ProofGoal,
                bool,
                std::collections::VecDeque<tactics::RewriteRule<'a>>,
                bool,
            ),
            Proof(tactics::ProofState<'a>),
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
            ProofTerm(tactics::ProofState<'a>, tactics::ProofGoal, bool),
        }
        let mut tasks = vec![Task::Visit(syntax, expected, true)];
        let mut values: Vec<Typed> = Vec::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Visit(syntax, expected, finish) => {
                    if let Some(inner) = parenthesized_inner(syntax)? {
                        tasks.push(Task::Visit(inner, expected, finish));
                        continue;
                    }
                    if let Syntax::Node { kind, args, .. } = syntax {
                        if kind == &parser_kind(&["Term", "matrixAlias"]) {
                            let [Syntax::Ident { val: name, .. }, subject, body] = args.as_slice()
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
                        if kind == &parser_kind(&["Term", "forall"]) {
                            let parts = expect_node(syntax, kind, 5, "universal quantifier")?;
                            if !matches!(&parts[0], Syntax::Atom { val, .. } if val == "forall" || val == "∀")
                            {
                                return Err(failure(SourceInferenceError::Scope));
                            }
                            let names = expect_null_args(&parts[1], "quantified names")?;
                            if names.is_empty() {
                                return Err(failure(SourceInferenceError::Scope));
                            }
                            let annotation = optional_type_syntax(&parts[2])?
                                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                            expect_atom(&parts[3], ",", "quantifier separator")?;
                            tasks.push(Task::ForallDomain(names, &parts[4], expected));
                            tasks.push(Task::Visit(annotation, Some(self.type_expected()?), true));
                            continue;
                        }
                        if kind == &parser_kind(&["Term", "match"])
                            || kind == &parser_kind(&["Term", "matchMatrix"])
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
                            let [annotation] = expect_null_args(&parts[3], "ascribed type")? else {
                                return Err(failure(SourceInferenceError::Scope));
                            };
                            tasks.push(Task::Ascription(&parts[1], expected));
                            tasks.push(Task::Visit(annotation, Some(self.type_expected()?), true));
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
                                tasks.push(Task::RecordPrepare(parts, expected, Vec::new()));
                            }
                            continue;
                        }
                        if kind == &parser_kind(&["Term", "byTactic"]) {
                            tasks.push(Task::Proof(self.start_proof(syntax, expected)?));
                            continue;
                        }
                        if kind == &parser_kind(&["Term", "fun"]) {
                            let parts = expect_node(syntax, kind, 2, "Lean.Parser.Term.fun")?;
                            if !matches!(&parts[0], Syntax::Atom { val, .. } if val == "fun" || val == "λ")
                            {
                                return Err(failure(SourceInferenceError::Scope));
                            }
                            let basic = expect_node(
                                &parts[1],
                                &parser_kind(&["Term", "basicFun"]),
                                4,
                                "Lean.Parser.Term.basicFun",
                            )?;
                            let names = expect_null_args(&basic[0], "lambda binders")?;
                            if names.is_empty() {
                                return Err(failure(SourceInferenceError::Scope));
                            }
                            expect_empty_null(&basic[1], "absent lambda result ascription")?;
                            if !matches!(&basic[2], Syntax::Atom { val, .. } if val == "=>" || val == "↦")
                            {
                                return Err(failure(SourceInferenceError::Scope));
                            }
                            let saved = self.txn.lctx.clone();
                            let mut binders = Vec::new();
                            let mut expected_body = expected.clone();
                            for name in names {
                                self.tick()?;
                                let Syntax::Ident { val: name, .. } = name else {
                                    return Err(failure(SourceInferenceError::Scope));
                                };
                                if name.is_anonymous() {
                                    return Err(NatDefinitionElabError::AnonymousReferenceName);
                                }
                                let (domain, codomain) = if let Some(expected) = &expected_body {
                                    let expected = self.whnf(expected)?;
                                    match expected.node() {
                                        ExprNode::ForallE {
                                            binder_type,
                                            body,
                                            binder_info: BinderInfo::Default,
                                            ..
                                        } => (binder_type.clone(), Some(body.clone())),
                                        ExprNode::MVar { .. } => {
                                            let universe = self.level()?;
                                            (self.hole(Expr::sort(universe))?, None)
                                        }
                                        _ => {
                                            return Err(failure(
                                                SourceInferenceError::ExpectedFunction,
                                            ));
                                        }
                                    }
                                } else {
                                    let universe = self.level()?;
                                    (self.hole(Expr::sort(universe))?, None)
                                };
                                let id = FVarId(self.fresh_name()?);
                                expected_body = codomain
                                    .map(|body| self.substitute(&body, &Expr::fvar(id.clone())))
                                    .transpose()?;
                                self.txn.lctx.add_param(
                                    id.clone(),
                                    name.clone(),
                                    domain,
                                    BinderInfo::Default,
                                );
                                binders.push(
                                    self.txn.lctx.find(&id).expect("new lambda binder").clone(),
                                );
                            }
                            tasks.push(Task::Lambda(saved, binders, expected));
                            tasks.push(Task::Visit(&basic[3], expected_body, true));
                            continue;
                        }
                        if kind == &parser_kind(&["Term", "let"]) {
                            let (name, annotation, value, body) = self.let_parts(args)?;
                            if let Some(annotation) = annotation {
                                tasks.push(Task::LetAnnotation(name, value, body, expected));
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
                            tasks.push(Task::Visit(codomain, Some(self.type_expected()?), true));
                            tasks.push(Task::Visit(domain, Some(self.type_expected()?), true));
                            continue;
                        }
                        if kind == &parser_kind(&["Term", "app"]) {
                            let parts = expect_node(syntax, kind, 2, "application")?;
                            let arguments = expect_null_args(&parts[1], "application arguments")?;
                            if arguments.is_empty() {
                                return Err(failure(SourceInferenceError::ExpectedFunction));
                            }
                            tasks.push(Task::Function(arguments, expected));
                            tasks.push(Task::Visit(&parts[0], None, false));
                            continue;
                        }
                        if let Some(intrinsic) = bounded_infix_intrinsic(kind, true) {
                            let parts = expect_node(syntax, kind, 3, "scalar infix")?;
                            expect_atom(&parts[1], intrinsic.spelling(), "scalar operator")?;
                            tasks.push(Task::Infix(intrinsic, expected));
                            tasks.push(Task::Visit(&parts[2], None, true));
                            tasks.push(Task::Visit(&parts[0], None, true));
                            continue;
                        }
                    }
                    let term = self.atom(syntax, expected.as_ref())?;
                    values.push(if finish {
                        self.finish_term(term, expected.as_ref())?
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
                    if let Some(expected) = expected {
                        self.constrain_type(&term.type_, &expected)?;
                        self.resolve_instances(false)?;
                    }
                    // Expected types guide inference but closed constraints are
                    // left to K1. Retain this assertion in the checked term,
                    // including when the surrounding program ignores its value.
                    values.push(Typed {
                        value: Expr::let_e(
                            Name::anonymous(),
                            annotation.clone(),
                            term.value,
                            Expr::bvar(0).expect("fixed ascription identity binder"),
                            false,
                        ),
                        type_: term.type_,
                    });
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
                    tactics::ProofAction::Binding {
                        goal,
                        name,
                        annotation,
                        value,
                        opaque,
                    } => {
                        self.txn.lctx = goal.lctx.clone();
                        if let Some(annotation) = annotation {
                            tasks.push(Task::ProofBindingType(proof, goal, name, value, opaque));
                            tasks.push(Task::Visit(annotation, Some(self.type_expected()?), true));
                        } else {
                            tasks.push(Task::ProofBindingValue(proof, goal, name, None, opaque));
                            tasks.push(Task::Visit(value, None, true));
                        }
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
                        tasks.push(Task::ProofTerm(proof, goal, apply));
                        tasks.push(Task::Visit(syntax, expected, true));
                    }
                    tactics::ProofAction::Complete(term) => values.push(term),
                },
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
                    self.rewrite_proof_term(&mut proof, goal, term, reverse, remaining, close)?;
                    tasks.push(Task::Proof(proof));
                }
                Task::ProofTerm(mut proof, goal, apply) => {
                    let term = values.pop().expect("tactic term visit");
                    if apply {
                        self.apply_proof_term(&mut proof, goal, term)?;
                    } else {
                        self.close_proof_goal(goal, term.value)?;
                    }
                    tasks.push(Task::Proof(proof));
                }
                Task::Lambda(saved, binders, expected) => {
                    let mut body = values.pop().expect("lambda body visit");
                    self.flush(false)?;
                    body.value = self.instantiate(&body.value)?;
                    body.type_ = self.instantiate(&body.type_)?;
                    for local in binders.into_iter().rev() {
                        self.tick()?;
                        let domain = self.instantiate(&local.type_)?;
                        body.value = body
                            .value
                            .abstract_fvar(&local.id, 0)
                            .map_err(|_| failure(SourceInferenceError::Scope))?;
                        body.type_ = body
                            .type_
                            .abstract_fvar(&local.id, 0)
                            .map_err(|_| failure(SourceInferenceError::Scope))?;
                        body.value = Expr::lam(
                            local.user_name.clone(),
                            domain.clone(),
                            body.value,
                            local.binder_info,
                        );
                        body.type_ =
                            Expr::forall_e(local.user_name, domain, body.type_, local.binder_info);
                    }
                    self.txn.lctx = saved;
                    values.push(self.finish_term(body, expected.as_ref())?);
                }
                Task::Function(arguments, expected) => {
                    let function = values.pop().expect("function task follows its visit");
                    tasks.push(Task::Apply(function, arguments, expected));
                }
                Task::Apply(function, arguments, expected) => {
                    if let Some((first, rest)) = arguments.split_first() {
                        let function =
                            self.insert_implicits(function, ImplicitInsertion::ExplicitArgument)?;
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
                            self.constrain_type(&codomain, expected)?;
                        }
                        tasks.push(Task::Argument(function, codomain, rest, expected));
                        tasks.push(Task::Visit(first, Some(domain), true));
                    } else {
                        values.push(self.finish_term(function, expected.as_ref())?);
                    }
                }
                Task::Argument(function, codomain, rest, expected) => {
                    let argument = values.pop().expect("argument task follows its visit");
                    let type_ = self.substitute(&codomain, &argument.value)?;
                    tasks.push(Task::Apply(
                        Typed {
                            value: Expr::app(function.value, argument.value),
                            type_,
                        },
                        rest,
                        expected,
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
                        function =
                            self.insert_implicits(function, ImplicitInsertion::ExplicitArgument)?;
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
                Task::ForallDomain(names, body, expected) => {
                    let domain = values.pop().expect("quantifier domain visit");
                    let universe = self.sort_level(&domain)?;
                    let saved = self.txn.lctx.clone();
                    let mut locals = Vec::new();
                    for name in names {
                        self.tick()?;
                        let Syntax::Ident { val, .. } = name else {
                            return Err(failure(SourceInferenceError::Scope));
                        };
                        if val.is_anonymous() {
                            return Err(failure(SourceInferenceError::Scope));
                        }
                        let id = FVarId(self.fresh_name()?);
                        self.txn.lctx.add_param(
                            id.clone(),
                            val.clone(),
                            domain.value.clone(),
                            BinderInfo::Default,
                        );
                        locals.push(self.txn.lctx.find(&id).expect("quantified local").clone());
                    }
                    tasks.push(Task::ForallBody(saved, locals, universe, expected));
                    tasks.push(Task::Visit(body, Some(self.type_expected()?), true));
                }
                Task::ForallBody(saved, locals, domain_universe, expected) => {
                    let body = values.pop().expect("quantifier body visit");
                    let mut universe = self.sort_level(&body)?;
                    let mut value = body.value;
                    for local in locals.iter().rev() {
                        self.tick()?;
                        value = value
                            .abstract_fvar(&local.id, 0)
                            .map_err(|_| failure(SourceInferenceError::Scope))?;
                        value = Expr::forall_e(
                            local.user_name.clone(),
                            local.type_.clone(),
                            value,
                            local.binder_info,
                        );
                        universe = Level::imax(domain_universe.clone(), universe)
                            .map_err(|_| failure(SourceInferenceError::Scope))?;
                    }
                    self.txn.lctx = saved;
                    values.push(self.finish_term(
                        Typed {
                            value,
                            type_: Expr::sort(universe),
                        },
                        expected.as_ref(),
                    )?);
                }
                Task::Arrow(expected) => {
                    let right = values.pop().expect("arrow codomain visit");
                    let left = values.pop().expect("arrow domain visit");
                    let u = self.sort_level(&left)?;
                    let v = self.sort_level(&right)?;
                    let level =
                        Level::imax(u, v).map_err(|_| failure(SourceInferenceError::Scope))?;
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
                        value: Expr::let_e(name, value.type_, value.value, abstract_body, false),
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
    }

    fn let_parts<'a>(
        &mut self,
        parts: &'a [Syntax],
    ) -> Result<(Name, Option<&'a Syntax>, &'a Syntax, &'a Syntax), NatDefinitionElabError> {
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
        expect_empty_null(&declaration[1], "empty let parameters")?;
        let annotation = optional_type_syntax(&declaration[2])?;
        expect_atom(&declaration[3], ":=", "let assignment")?;
        expect_atom(separator, ";", "let separator")?;
        Ok((name.clone(), annotation, &declaration[4], body))
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
    let mut context = Context::new(environment, kernel);
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
    for modifier in modifiers {
        expect_empty_null(modifier, "empty declaration modifier")?;
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
    expect_empty_null(&id[1], "absent declaration pre-parser")?;
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
    let parameters = context.bind_parameters(&signature[0])?;
    let expected = if is_theorem || is_instance {
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
        context.require_resolved(&types)?;
    }
    let parts = expect_node(
        &definition[3],
        &parser_kind(&["Command", "declValSimple"]),
        4,
        "definition value",
    )?;
    expect_atom(&parts[0], ":=", "definition assignment")?;
    let termination = expect_node(
        &parts[2],
        &parser_kind(&["Termination", "suffix"]),
        2,
        "termination suffix",
    )?;
    for part in termination {
        expect_empty_null(part, "absent termination clause")?;
    }
    expect_empty_null(&parts[3], "absent where clause")?;
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
    let mut term = context.definition_body(name, &parameters, &parts[1], expected.clone())?;
    if let Some(expected) = expected {
        term.type_ = expected;
    }
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
    let base = ConstantVal {
        name: name.clone(),
        level_params: Vec::new(),
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
