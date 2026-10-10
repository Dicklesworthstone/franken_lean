//! Bidirectional elaboration of the native source subset.
//!
//! Syntax drives one private elaboration transaction. Applications insert typed
//! implicit metavariables; argument and expected-result types generate ordinary
//! unification equations. Only fully instantiated candidates leave this module.
//! The caller still owns final kernel checking and declaration publication.

mod anonymous_ctor;
pub use anonymous_ctor::AnonymousCtorError;
mod application;
mod binders;
mod calc;
mod cdot;
mod character;
mod codegen;
mod coercions;
mod collections;
pub mod deriving;
mod do_notation;
mod dotted_ident;
pub use dotted_ident::DottedIdentError;
mod eliminator;
mod subst;
pub use subst::SubstError;
pub mod scope;
use scope::SourceScope;
mod equations;
mod inductive;
mod infer;
mod instance_command;
mod instance_name;
mod instances;
mod level_syntax;
mod levels;
mod local_functions;
pub use level_syntax::LevelSyntaxError;
pub mod inspect;
mod matching;
mod numeric;
mod operators;
mod overload;
mod patterns;
mod record;
mod record_terms;
mod recursion;
mod reduce;
mod tactics;

use super::*;
use crate::constraint::unify::{
    UnificationBudget, UnificationDeferred, UnificationError, UnificationReport,
    UnificationTransparency,
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
    Deriving(deriving::DerivingError),
    UnknownConstant(Name),
    /// More than one interpretation of an overloaded identifier elaborates against
    /// the expected type (the pin's `elabAppAux`), listed in the order it tries them.
    AmbiguousTerm {
        name: Name,
        interpretations: Vec<Name>,
    },
    /// Every interpretation of an overloaded identifier definitely fails.
    OverloadFailed {
        name: Name,
        failures: Vec<(Name, String)>,
    },
    /// An interpretation of an overloaded identifier could be neither established nor
    /// ruled out here, so none is chosen (`overload.rs`).
    OverloadUndetermined {
        name: Name,
        candidate: Name,
    },
    /// An unknown name with a proper prefix that is itself a constant (`Nat.nope` when `Nat`
    /// exists). The pin reads the rest as a member of that constant and words it
    /// `Unknown constant`, not `Unknown identifier`. Produced only where an error leaves the
    /// elaborator (`crate::with_pin_unknown_name_wording`); inside it every unknown name is
    /// [`Self::UnknownConstant`].
    UnknownMemberConstant(Name),
    InvalidNamedArgument(Name),
    DuplicateNamedArgument(Name),
    InvalidFieldReceiver(Name),
    LevelSyntax(LevelSyntaxError),
    ExpectedFunction,
    ExpectedType,
    RecordTerm(record_terms::RecordTermError),
    Record(crate::records::RecordError),
    TypeObligation(Box<Outcome<Verdict>>),
    /// A completed conversion query refused at elaboration's transparency.
    /// This is not a kernel rejection of the declaration: ordinary admission
    /// may unfold definitions that this query must keep opaque.
    ConversionRefused(Box<Verdict>),
    Tactic(tactics::TacticError),
    UnresolvedHoles {
        count: usize,
    },
    UnresolvedUniverses,
    InstanceSynthesisRequired,
    /// An operator tree needs a coercion at a leaf. The pin inserts the
    /// `expandCoe`-unfolded coercion; the native coercion search does not
    /// produce that term, so this is refused rather than approximated.
    OperatorCoercion,
    /// The pin's eliminator elaboration (`elabAsElim`) could not finish; the
    /// text is the pin's own message after "failed to elaborate eliminator, ".
    Eliminator(&'static str),
    /// A compiled declaration applies a recursor the pin's code generator does not
    /// support (`codegen.rs`, bead `franken_lean-z8j.1.6.6`).
    UnsupportedRecursor(Name),
    InvalidInstanceBinder,
    InstanceRegistry(crate::instances::InstanceRegistryError),
    SimpSet(scope::simp::SimpSetError),
    /// The protected-declaration journal refused a tag.
    ProtectedJournal(crate::protected_names::ProtectedError),
    ResourceLimit,
    /// Private inspection stopped at a source boundary; never an admitted declaration.
    ObservationComplete,
    Scope,
    Universe(crate::universe::UniverseInstantiationError),
    Unification(Box<UnificationError>),
    /// `⟨…⟩` could not be expanded (`elabAnonymousCtor`).
    AnonymousCtor(AnonymousCtorError),
    /// `h ▸ e` could not be elaborated (`elabSubst`).
    Subst(SubstError),
    /// `.c` could not be resolved against its expected type (`resolveDottedIdentFn`).
    DottedIdent(DottedIdentError),
    /// A `·` that no parentheses, tuple or ascription scopes (the pin's `elabCDot`).
    CdotOutsideParentheses,
    /// A term whose type is rigidly not its expected type, with no coercion between them: the
    /// pin's `Type mismatch` (`throwTypeMismatchError`). Only rigid mismatches are reported
    /// here; an undecided one still reaches the kernel (`coercions::rigid_type_mismatch`).
    TypeMismatch {
        actual: String,
        expected: String,
    },
    /// A `mutual` block whose members' headers the pin refuses to combine.
    MutualHeader(MutualHeaderError),
}

/// The pin's header checks across the members of a `mutual` inductive block
/// (`Lean.Elab.Command`'s `withElaboratedHeaders` and `elabHeaders`, vendored
/// `src/Lean/Elab/MutualInductive.lean`; parameters by `forallTelescopeCompatibleAux`,
/// `src/Lean/Elab/DeclUtil.lean`). Each later member is compared with the first. A
/// member is named as it was written, without its namespace (`shortDeclName`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MutualHeaderError {
    /// `InductiveElabStep1.checkLevelNames`. Each list is the member's universe names as
    /// the pin prints them: its declared `.{…}` names, then the section's `universe`
    /// names, each reversed, because `expandDeclId` conses them on.
    UniverseParameters {
        declaration: Name,
        names: Vec<Name>,
        first: Name,
        first_names: Vec<Name>,
    },
    /// `checkNumParams`, which runs over every member before any parameter is compared.
    ParameterCount {
        declaration: Name,
        count: usize,
        first: Name,
        first_count: usize,
    },
    /// The same parameter carries a different binder annotation.
    BinderAnnotation { parameter: Name },
    /// The same parameter is spelled differently. Exception: two anonymous instance
    /// binders, whose names the pin generates with macro scopes (lean4#4310).
    ParameterNames { found: Name, expected: Name },
}

impl std::fmt::Display for MutualHeaderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let list = |names: &[Name]| {
            names
                .iter()
                .map(|name| format!("`{}`", name.to_display_string()))
                .collect::<Vec<_>>()
                .join(", ")
        };
        // The pin's words, including its trailing notes.
        match self {
            Self::UniverseParameters {
                declaration,
                names,
                first,
                first_names,
            } => write!(
                f,
                "Universe parameter mismatch in mutually inductive types: `{}` has universe \
                 parameters\n  {}\nbut the preceding declaration `{}` has\n  {}\n\nNote: All \
                 inductive declarations in the same `mutual` block must have the same universe \
                 level parameters",
                declaration.to_display_string(),
                list(names),
                first.to_display_string(),
                list(first_names)
            ),
            Self::ParameterCount {
                declaration,
                count,
                first,
                first_count,
            } => write!(
                f,
                "Invalid mutually inductive types: `{}` has {count} parameter(s), but the \
                 preceding type `{}` has {first_count}\n\nNote: All inductive types declared in \
                 the same `mutual` block must have the same parameters",
                declaration.to_display_string(),
                first.to_display_string()
            ),
            Self::BinderAnnotation { parameter } => write!(
                f,
                "Invalid mutually inductive types: Binder annotations for parameter `{}` must \
                 match",
                parameter.to_display_string()
            ),
            Self::ParameterNames { found, expected } => write!(
                f,
                "Invalid mutually inductive types: Parameter names `{}` and `{}` differ but \
                 were expected to match",
                found.to_display_string(),
                expected.to_display_string()
            ),
        }
    }
}

/// An interpretation as the pin's message names it: a root declaration as `_root_.x`.
fn interpretation_name(name: &Name) -> String {
    if name.parent().is_anonymous() {
        format!("_root_.{}", name.to_display_string())
    } else {
        name.to_display_string()
    }
}

impl std::fmt::Display for SourceInferenceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NameScope(error) => write!(f, "{error}"),
            Self::LevelSyntax(reason) => write!(f, "{reason}"),
            Self::Recursion(reason) => write!(f, "{reason}"),
            Self::Match(reason) => write!(f, "{reason}"),
            Self::Inductive(error) => write!(f, "{error}"),
            Self::Deriving(error) => write!(f, "{error}"),
            // The pin's two wordings for `lean.unknownIdentifier`, verbatim.
            Self::UnknownConstant(name) => {
                write!(f, "Unknown identifier `{}`", name.to_display_string())
            }
            Self::UnknownMemberConstant(name) => {
                write!(f, "Unknown constant `{}`", name.to_display_string())
            }
            // The pin's wording (`elabAppAux`), with each interpretation named as it
            // names it: a root declaration as `_root_.x`.
            Self::AmbiguousTerm {
                name,
                interpretations,
            } => {
                write!(
                    f,
                    "Ambiguous term `{}`; Possible interpretations:",
                    name.to_display_string()
                )?;
                for (index, interpretation) in interpretations.iter().enumerate() {
                    let separator = if index == 0 { " " } else { ", " };
                    write!(f, "{separator}`{}`", interpretation_name(interpretation))?;
                }
                Ok(())
            }
            Self::OverloadFailed { name, failures } => {
                write!(f, "overloaded `{}`, errors:", name.to_display_string())?;
                for (index, (candidate, reason)) in failures.iter().enumerate() {
                    let separator = if index == 0 { " " } else { "; " };
                    write!(
                        f,
                        "{separator}`{}`: {reason}",
                        interpretation_name(candidate)
                    )?;
                }
                Ok(())
            }
            Self::OverloadUndetermined { name, candidate } => write!(
                f,
                "overloaded `{}`: the interpretation `{}` can be neither established nor \
                 ruled out here, so none is chosen",
                name.to_display_string(),
                interpretation_name(candidate)
            ),
            Self::InvalidNamedArgument(name) => write!(
                f,
                "invalid argument name `{}` for this application",
                name.to_display_string()
            ),
            Self::DuplicateNamedArgument(name) => {
                write!(f, "duplicate named argument `{}`", name.to_display_string())
            }
            Self::InvalidFieldReceiver(name) => write!(
                f,
                "field notation requires a usable parameter with type head `{}`",
                name.to_display_string()
            ),
            Self::ExpectedFunction => write!(f, "source application requires a function type"),
            Self::Tactic(error) => write!(f, "{error}"),
            Self::Record(error) => write!(f, "{error}"),
            Self::TypeObligation(outcome) => {
                write!(f, "source type obligation failed: {outcome:?}")
            }
            Self::ConversionRefused(verdict) => {
                write!(f, "source conversion refused: {verdict:?}")
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
            Self::OperatorCoercion => write!(
                f,
                "operator elaboration needs a coercion to the tree's maximal type, and expanded coercion insertion is not implemented"
            ),
            Self::Eliminator(reason) => write!(f, "failed to elaborate eliminator, {reason}"),
            Self::UnsupportedRecursor(name) => write!(
                f,
                "code generator does not support recursor `{}` yet, consider using 'match ... with' and/or structural recursion",
                name.to_display_string()
            ),
            Self::InvalidInstanceBinder => write!(
                f,
                "instance binder must end in a registered class with inferable parameters"
            ),
            Self::InstanceRegistry(error) => write!(f, "{error}"),
            Self::SimpSet(error) => write!(f, "{error}"),
            Self::ProtectedJournal(error) => write!(f, "{error}"),
            Self::ObservationComplete => {
                write!(f, "source observation completed without admission")
            }
            Self::ResourceLimit => write!(f, "source elaboration work limit reached"),
            Self::Scope => write!(
                f,
                "source elaboration encountered an invalid expression scope"
            ),
            Self::Universe(error) => write!(f, "{error}"),
            Self::Unification(error) => write!(f, "{error}"),
            Self::AnonymousCtor(error) => write!(f, "{error}"),
            Self::Subst(error) => write!(f, "{error}"),
            Self::DottedIdent(error) => write!(f, "{error}"),
            // The pin's words.
            Self::CdotOutsideParentheses => f.write_str(
                "invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)",
            ),
            Self::TypeMismatch { actual, expected } => write!(
                f,
                "Type mismatch: a term of type `{actual}` is expected to have type `{expected}`"
            ),
            Self::MutualHeader(error) => write!(f, "{error}"),
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
    ApplicationEnd,
    InstanceQuery,
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
    AfterSelection,
    DefaultInstance,
}

#[derive(Clone)]
struct SourceEquation {
    sides: (Expr, Expr),
    policy: EquationPolicy,
}

/// What a non-final flush saw when it last stopped without progress. The
/// solver is deterministic, so a later flush over the same equations, under the
/// same metavariable and universe assignments and in the same local context,
/// defers in exactly the same way; replaying it only spends heartbeats. The
/// assignments are compared, not counted, since one can be replaced in place.
/// Rollback restores this with the rest of the context.
#[derive(Clone)]
struct StalledFlush {
    mvar_assignments: std::collections::HashMap<MVarId, crate::mvar::MetavarAssignment>,
    universe_assignments: std::collections::HashMap<LMVarId, Level>,
    lctx: crate::lctx::LocalContext,
    equations: Vec<((Expr, Expr), EquationPolicy)>,
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
    fn instance_result(left: Expr, right: Expr) -> Self {
        Self {
            sides: (left, right),
            policy: EquationPolicy::AfterSelection,
        }
    }
    fn default_instance(left: Expr, right: Expr) -> Self {
        Self {
            sides: (left, right),
            policy: EquationPolicy::DefaultInstance,
        }
    }
}

#[derive(Clone)]
struct Context {
    inspection: Option<inspect::Probe>,
    source_scope: SourceScope,
    // Speculative tactics must observe rigid typing failures before choosing
    // their successful alternative. Outside speculation, ordinary final K1
    // admission retains its existing error boundary.
    attempt_depth: usize,
    // Opaque assertions remain parameter assumptions until their continuations
    // have been checked. Visibility comes from lctx, including after rollback.
    opaque_locals: std::collections::HashSet<FVarId>,
    txn: ElabTxn,
    kernel: Budget,
    next: u64,
    equations: Vec<SourceEquation>,
    stalled_flush: Option<StalledFlush>,
    instance_goals: Vec<MVarId>,
    // Nesting of pending instance synthesis started by unification, the pin's
    // `synthPendingDepth`. Bounded by `MAX_SYNTH_PENDING_DEPTH`.
    synth_pending_depth: u8,
    // Nesting of overload trials (`overload.rs`). Bounded by `MAX_OVERLOAD_DEPTH`.
    overload_depth: u8,
    level_params: Vec<Name>,
    explicit_levels: usize,
    infer_level_params: bool,
    // Stable private names link raw IHs to checked specializations. Actual
    // declarations in the local context decide visibility, including rollback.
    induction_specializations: Vec<(Name, Name)>,
    matrix_rows: std::collections::HashSet<Name>,
    // Generated pattern columns at a constructor's parameter positions. The pin
    // makes those positions inaccessible, so a match binds nothing there, and a
    // source name the pattern matrix aliased to such a column is refused.
    inaccessible_columns: std::collections::HashSet<Name>,
    // Only compiler-generated aliases may expose their already checked referent.
    matrix_aliases: std::collections::HashMap<FVarId, Expr>,
    // The instance registry, re-read only when it can have changed: every
    // numeric literal, operator and coercion asks it.
    registry_cache: crate::instances::RegistryCache,
    // Imported `export` aliases, re-read only when the journal or the constants
    // change: every unresolved identifier consults them.
    alias_cache: crate::aliases::AliasCache,
    // Imported `protected` declarations, re-read on the same terms: an atomic
    // identifier never reaches one through a namespace or an alias.
    protected_cache: crate::protected_names::ProtectedCache,
    // The declaration being elaborated, when it is `protected`.
    protected_declaration: Option<Name>,
    refinements: Vec<tactics::RefinementFrame>,
    // The declaration whose body is being elaborated (`definition_body`), so that field
    // notation naming it (`l.size` inside `T.size`) is recognized as a recursive reference
    // before the recursion context exists, as a direct `T.size l` already is.
    defining: Option<Name>,
    recursion: Option<recursion::Recursion>,
    // Eliminator applications waiting for their expected type (`elabAsElim`'s
    // postponement), resumed after default instances run.
    postponed_eliminators: Vec<eliminator::PostponedEliminator>,
    // Resumed argument failures are delayed source diagnostics, just like the
    // pin's synthetic metavariable errors. Tactic/recursion rollback restores
    // them; a selected declaration can never discard them or admit its holes.
    postponed_application_errors: Vec<NatDefinitionElabError>,
    // Recursors the source names directly, which a compiled declaration may not apply
    // (`codegen.rs`). Rollback restores them with the rest of the context.
    source_recursors: Vec<Name>,
}

fn failure(reason: SourceInferenceError) -> NatDefinitionElabError {
    NatDefinitionElabError::Inference(reason)
}

/// The refusals after which a source batch gets its one safe-definition retry.
fn retries_with_delta(result: &Result<UnificationReport, UnificationError>) -> bool {
    matches!(
        result,
        Err(UnificationError::Deferred(
            UnificationDeferred::UnsupportedEquation | UnificationDeferred::NotAPattern
        )) | Err(UnificationError::Metavariable(
            MetavarError::OccursCheckFailed { .. }
        ))
    )
}

impl Context {
    fn new(env: &Environment, kernel: Budget) -> Self {
        let mut txn = ElabTxn::new(env.clone(), KVMap::new(), 0);
        txn.budget.max_heartbeats = 1_000_000;
        Self {
            inspection: None,
            source_scope: SourceScope::default(),
            attempt_depth: 0,
            opaque_locals: std::collections::HashSet::new(),
            txn,
            kernel,
            next: 0,
            equations: Vec::new(),
            stalled_flush: None,
            instance_goals: Vec::new(),
            synth_pending_depth: 0,
            overload_depth: 0,
            level_params: Vec::new(),
            explicit_levels: 0,
            infer_level_params: false,
            induction_specializations: Vec::new(),
            matrix_rows: std::collections::HashSet::new(),
            inaccessible_columns: std::collections::HashSet::new(),
            matrix_aliases: std::collections::HashMap::new(),
            registry_cache: crate::instances::RegistryCache::default(),
            alias_cache: crate::aliases::AliasCache::default(),
            protected_cache: crate::protected_names::ProtectedCache::default(),
            protected_declaration: None,
            refinements: Vec::new(),
            defining: None,
            recursion: None,
            postponed_eliminators: Vec::new(),
            postponed_application_errors: Vec::new(),
            source_recursors: Vec::new(),
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
        // Elaboration's own eliminations build their recursor constants directly; one
        // resolved here is the source's.
        if matches!(info, fln_env::constants::ConstantInfo::Rec(_)) {
            self.note_source_recursor(name);
        }
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
        if let Some(literal) = self.character_literal(syntax)? {
            return Ok(literal);
        }
        if let Some(literal) = self.numeric_literal(syntax, expected)? {
            return Ok(literal);
        }
        if let Syntax::Node { kind, args, .. } = syntax {
            if kind == &parser_kind(&["Term", "dotIdent"]) {
                return self.dotted_identifier(args, expected);
            }
            if kind == &parser_kind(&["Term", "cdot"]) {
                return Err(failure(SourceInferenceError::CdotOutsideParentheses));
            }
            // `notation "∅" => EmptyCollection.emptyCollection` (`Init/Core.lean:581`): the
            // constant, whose implicit type and instance the caller inserts.
            if kind == &Name::from_components(["term∅"]) {
                let [symbol] = args.as_slice() else {
                    return Err(failure(SourceInferenceError::Scope));
                };
                expect_atom(symbol, "∅", "empty collection")?;
                return self.constant(&Name::from_components([
                    "EmptyCollection",
                    "emptyCollection",
                ]));
            }
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
            // The fallback to the name as written must not reach a seed constant the pin
            // does not have: resolution already refused it (`source_unreachable`), and the
            // direct lookup below would otherwise find it anyway.
            if crate::seed::protected::source_unreachable(&resolved) {
                return Err(failure(SourceInferenceError::UnknownConstant(
                    resolved.clone(),
                )));
            }
            if !scope::is_root_qualified(name)
                && let Some(local) = self.txn.lctx.find_by_user_name(&resolved)
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
            let name = &resolved;
            if let Some(recursion) = &self.recursion
                && &recursion.name == name
            {
                return Ok(recursion.reference.clone());
            }
            let mut resolved = name.clone();
            if !self.txn.env.contains(name) {
                if let Some(term) = self.qualified_record_field(name, expected)? {
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
        self.whnf_with_transparency(expr, UnificationTransparency::Default, true)
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
        // Ordinary type conversion preserves irreducibility, including beneath
        // dictionary projections. Instance matching keeps its narrower policy.
        let actual = self.instantiate(actual)?;
        let expected = self.instantiate(expected)?;
        // Assign an unknown expected type before reducing the actual carrier.
        // This includes dependent projection applications: unfolding their
        // semireducible receiver here can change later instance selection.
        let actual = if matches!(expected.node(), ExprNode::MVar { .. }) {
            actual
        } else {
            self.whnf(&actual)?
        };
        // Preserve the original target for the reverse assignment as well.
        let expected = if matches!(actual.node(), ExprNode::MVar { .. }) {
            expected
        } else {
            self.whnf(&expected)?
        };
        self.constrain(&actual, &expected)
    }

    fn check_scoped_equation(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        self.check_attempt_equation(actual, expected)?;
        // Kernel admission unfolds definitions that ordinary elaboration must
        // leave opaque. Check closed equations at Default as well; otherwise
        // explicit proof arguments and carrier conversions bypass inference.
        // The restricted fallback also closes opaque locals as parameters.
        match self.coercion_conversion(actual, expected)? {
            coercions::Conversion::Equal => Ok(()),
            coercions::Conversion::Refuted(verdict) => Err(failure(
                SourceInferenceError::ConversionRefused(Box::new(verdict)),
            )),
            coercions::Conversion::Deferred => {
                Err(failure(SourceInferenceError::Unification(Box::new(
                    UnificationError::Deferred(UnificationDeferred::UnsupportedEquation),
                ))))
            }
        }
    }

    fn constrain(&mut self, actual: &Expr, expected: &Expr) -> Result<(), NatDefinitionElabError> {
        let actual = self.instantiate(actual)?;
        let expected = self.instantiate(expected)?;
        if !actual.has_expr_mvar()
            && !expected.has_expr_mvar()
            && !actual.has_level_mvar()
            && !expected.has_level_mvar()
        {
            self.check_scoped_equation(&actual, &expected)?;
            // Final admission still independently checks the declaration under
            // the kernel's ordinary, unrestricted conversion policy.
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
    /// equations that defer or encounter a syntactic occurs check receive one
    /// default-transparency conversion retry. For example, ?A = Id ?A is reflexive
    /// after delta reduction, not a cyclic assignment. A real cycle still fails
    /// the unchanged occurs check on the retry. Both attempts are transactional
    /// and retain spent work; resource failures and selection queries never retry.
    fn unify_source_batch(
        &mut self,
        pairs: &[(Expr, Expr)],
        allow_delta: bool,
    ) -> Result<(), UnificationError> {
        let mut result =
            self.txn
                .unify_many_with(pairs, UnificationBudget::new(self.kernel), &|| false);
        if allow_delta && retries_with_delta(&result) {
            let mut budget = UnificationBudget::new(self.kernel);
            budget.transparency = UnificationTransparency::Default;
            result = self.txn.unify_many_with(pairs, budget, &|| false);
        }
        result.map(|report| assert!(report.awakened.is_empty(), "private source queue"))
    }

    /// `unify_source_batch` for the pending source equations, where a batch
    /// stuck on one of this context's instance holes may synthesize it.
    fn unify_pending_batch(
        &mut self,
        pairs: &[(Expr, Expr)],
        allow_delta: bool,
    ) -> Result<Result<(), UnificationError>, NatDefinitionElabError> {
        let mut budget = UnificationBudget::new(self.kernel);
        if !allow_delta {
            // A selection query (an instance candidate against its goal) is one
            // `isDefEq` at the pin's `instances` transparency (vendored
            // Lean/Meta/SynthInstance.lean `tryResolve`, :356; configured at :879),
            // which also unfolds `implicitReducible` definitions such as
            // `instOfNatNat` (bead fln-gkhu).
            budget.transparency = UnificationTransparency::Instances;
        }
        let mut result = self.unify_pending(pairs, budget)?;
        if allow_delta && retries_with_delta(&result) {
            let mut budget = UnificationBudget::new(self.kernel);
            budget.transparency = UnificationTransparency::Default;
            result = self.unify_pending(pairs, budget)?;
        }
        Ok(result.map(|report| assert!(report.awakened.is_empty(), "private source queue")))
    }

    /// One source unification request. A fixed point blocked on one of this
    /// context's instance holes may synthesize it and continue, as the pin's
    /// `isDefEq` calls `synthPending` (vendored Meta/ExprDefEq.lean
    /// `unstuckMVar`, Meta/SynthInstance.lean `synthPendingImp`), nested at most
    /// `maxSynthPendingDepth` deep. The outer error is the synthesis's own
    /// typed failure, exactly as `resolve_instances` would have returned it.
    fn unify_pending(
        &mut self,
        pairs: &[(Expr, Expr)],
        budget: UnificationBudget,
    ) -> Result<Result<UnificationReport, UnificationError>, NatDefinitionElabError> {
        if self.synth_pending_depth > instances::MAX_SYNTH_PENDING_DEPTH
            || self.instance_goals.is_empty()
        {
            return Ok(self.txn.unify_many_with(pairs, budget, &|| false));
        }
        // The owner reads this context while the solver mutates the
        // transaction; it works on the solver's state, never on this copy.
        let detached = ElabTxn::new(Environment::new(), KVMap::new(), 0);
        let mut txn = std::mem::replace(&mut self.txn, detached);
        let mut owner = instances::PendingInstances::new(self);
        let result = txn.unify_many_with_pending(pairs, budget, &|| false, &mut owner);
        let fault = owner.into_fault();
        self.txn = txn;
        match fault {
            Some(fault) => Err(fault),
            None => Ok(result),
        }
    }

    fn flush(&mut self, final_pass: bool) -> Result<(), NatDefinitionElabError> {
        if !final_pass && self.flush_is_stalled() {
            return Ok(());
        }
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
                .all(|equation| equation.policy != EquationPolicy::BeforeSelection);
            let deferred = match self.unify_pending_batch(&pairs, allow_delta)? {
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
                    self.check_scoped_equation(&left, &right)?;
                    // Exactly the same policy as `constrain`: once inference
                    // has finished, the retained source terms and annotations
                    // are obligations of the final ordinary K1 declaration.
                    continue;
                }
                match self.unify_pending_batch(
                    &[(left.clone(), right.clone())],
                    equation.policy != EquationPolicy::BeforeSelection,
                )? {
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
                    self.stalled_flush = Some(StalledFlush {
                        mvar_assignments: self.txn.mvars.assignments().clone(),
                        universe_assignments: self.txn.universes.assignments().clone(),
                        lctx: self.txn.lctx.clone(),
                        equations: self
                            .equations
                            .iter()
                            .map(|equation| (equation.sides.clone(), equation.policy))
                            .collect(),
                    });
                    Ok(())
                };
            }
        }
    }

    /// Whether the pending equations are exactly those a previous non-final
    /// flush left deferred, with no assignment and no local-context change
    /// since. Each replay re-runs the joint batch and every individual retry,
    /// so without this a stuck equation is re-solved after every later
    /// constraint and drains the transaction's heartbeats.
    fn flush_is_stalled(&self) -> bool {
        let Some(stalled) = &self.stalled_flush else {
            return false;
        };
        stalled.equations.len() == self.equations.len()
            && &stalled.mvar_assignments == self.txn.mvars.assignments()
            && &stalled.universe_assignments == self.txn.universes.assignments()
            && stalled.lctx == self.txn.lctx
            && stalled
                .equations
                .iter()
                .zip(&self.equations)
                .all(|(seen, now)| seen.0 == now.sides && seen.1 == now.policy)
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
                BinderInfo::Implicit => !matches!(
                    insertion,
                    ImplicitInsertion::Expected(None) | ImplicitInsertion::InstanceQuery
                ),
                BinderInfo::InstImplicit => !matches!(insertion, ImplicitInsertion::Expected(None)),
                BinderInfo::StrictImplicit => {
                    matches!(insertion, ImplicitInsertion::ExplicitArgument)
                }
            };
            if !insert {
                // A completed term keeps its named type. Unfolding a
                // function-backed monad here would store an anonymous Pi
                // in inferred action aliases, losing the constructor that
                // later Bind and MonadLiftT instance selection needs.
                // Argument and receiver consumers still need the exposed
                // telescope; conversion checks remain unchanged.
                if matches!(
                    insertion,
                    ImplicitInsertion::ExplicitArgument | ImplicitInsertion::FieldReceiver
                ) {
                    term.type_ = reduced;
                }
                break;
            }
            if let ImplicitInsertion::Expected(Some(expected)) = insertion {
                let expected = self.whnf(expected)?;
                if matches!(expected.node(), ExprNode::ForallE { binder_info: style, .. } if style == binder_info)
                {
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

    fn finish_application(
        &mut self,
        term: Typed,
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        // App.processImplicitArg/processInstImplicitArg continue after the
        // last written argument even without an expected result. Strict
        // implicits still require another argument; explicit `@` bypasses us.
        let insertion = expected.map_or(ImplicitInsertion::ApplicationEnd, |expected| {
            ImplicitInsertion::Expected(Some(expected))
        });
        let term = self.insert_implicits(term, insertion)?;
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
        use application::postponed;
        /// An application's explicit arguments: a plain list (`Term.app`), or the elements of
        /// `⟨a, b, …⟩` interleaved with their `,` separators, which are skipped.
        #[derive(Clone, Copy)]
        enum Arguments<'a> {
            Plain(&'a [Syntax]),
            /// Arguments between separator atoms (`,` in `⟨a, b⟩`, `then`/`else` in `bif`).
            Separated(&'a [Syntax], &'static [&'static str]),
        }
        impl<'a> Arguments<'a> {
            fn split_first(self) -> Option<(&'a Syntax, Self)> {
                match self {
                    Arguments::Plain(items) => items
                        .split_first()
                        .map(|(first, rest)| (first, Arguments::Plain(rest))),
                    Arguments::Separated(items, separators) => {
                        let start = items.iter().position(|item| {
                            !matches!(item, Syntax::Atom { val, .. }
                                if separators.contains(&val.as_str()))
                        })?;
                        items[start..]
                            .split_first()
                            .map(|(first, rest)| (first, Arguments::Separated(rest, separators)))
                    }
                }
            }
            fn is_empty(self) -> bool {
                self.split_first().is_none()
            }
        }
        enum Task<'a> {
            DoJoinValue(Name, &'a Syntax, Option<Expr>),
            DoBindJoinStart(Name, &'a Syntax, &'a Syntax, Expr, bool),
            DoBindJoinBody(LocalContext, FVarId, Name, &'a Syntax, Expr),
            DoBindJoinValue(LocalContext, FVarId, Name, Typed),
            DoNestedAnnotation(&'a Syntax, Option<Expr>, bool),
            DoAction(&'a [Syntax], Option<Expr>),
            CalcNext(calc::Build<'a>),
            CalcRelation(calc::Build<'a>),
            CalcProof(calc::Build<'a>, Expr),
            MatrixScope(Vec<Name>),
            CaptureRecursiveContext,
            MatchDiscriminant(matching::MatchParts<'a>, Option<Expr>),
            MatchNext(matching::MatchBuild<'a>),
            MatchBranch(matching::MatchBuild<'a>, matching::BranchBinders),
            Ascription(&'a Syntax, Option<Expr>, bool),
            AscribedValue(Expr, Option<Expr>, bool),
            Projection(Name, &'a [Syntax], Option<Expr>, bool, bool),
            RecordType(record_terms::RecordParts<'a>, Option<Expr>),
            RecordPrepare(record_terms::RecordParts<'a>, Option<Expr>, Vec<Typed>),
            RecordSource(record_terms::RecordParts<'a>, Option<Expr>, Vec<Typed>),
            RecordNext(record_terms::RecordBuild<'a>),
            RecordField(record_terms::RecordBuild<'a>, Expr),
            Visit(&'a Syntax, Option<Expr>, bool),
            Observe(&'a Syntax, LocalContext),
            Function(&'a [Syntax], Option<Expr>, bool),
            StartApplication(&'a Syntax, &'a [Syntax], Option<Expr>, bool),
            NamedNext(application::NamedApplication<'a>),
            NamedArgument(application::NamedApplication<'a>, Expr),
            CheckArgument(&'a Syntax, Expr, bool),
            InferredExceptionArgument(Expr),
            ArgumentComplete(usize),
            ForCollection(Option<Expr>),
            Argument(Typed, Expr, Arguments<'a>, Option<Expr>, bool),
            Apply(Typed, Arguments<'a>, Option<Expr>, bool),
            Infix(BoundedInfixIntrinsic, Option<Expr>),
            Operator(operators::OperatorTree<'a>, Option<Expr>),
            Arrow(Option<Expr>),
            BinderNext(binders::Telescope<'a>),
            BinderDomain(binders::Telescope<'a>),
            BinderBody(binders::Telescope<'a>),
            LocalFunctionAnnotation(local_functions::Build<'a>),
            LocalFunctionStart(local_functions::Build<'a>, Option<usize>),
            LocalFunctionValue(local_functions::Build<'a>, usize),
            // The last two flags: opaque (`have`), and inline (`letI`/`haveI`, whose
            // value replaces the bound variable instead of becoming a `let`).
            LetAnnotation(Name, &'a Syntax, &'a Syntax, Option<Expr>, bool, bool),
            LetValue(Name, Option<Expr>, &'a Syntax, Option<Expr>, bool, bool),
            LetBody(LocalContext, FVarId, Name, Typed, bool, bool),
            RewriteTerm(
                tactics::ProofState<'a>,
                tactics::ProofGoal,
                bool,
                std::collections::VecDeque<tactics::RewriteRule<'a>>,
                bool,
            ),
            Proof(tactics::ProofState<'a>),
            ChangeTarget(tactics::ProofState<'a>, tactics::ProofGoal),
            SimpaTerm(tactics::ProofState<'a>, tactics::ProofGoal, &'a [Syntax]),
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
        enum Attempt<'a> {
            Proof(tactics::backtrack::Checkpoint<'a>, postponed::Queue<'a>),
            LocalFunction(Box<local_functions::Checkpoint<'a>>, postponed::Queue<'a>),
            Argument(Box<postponed::Checkpoint<'a>>),
        }
        let mut attempts: Vec<Attempt<'_>> = Vec::new();
        let mut pending = postponed::Queue::default();
        loop {
            let mut blocked_application = None;
            let mut containing_argument = None;
            let result = (|| {
                loop {
                    let closes_scope = matches!(
                        tasks.last(),
                        Some(
                            Task::BinderBody(..)
                                | Task::LetBody(..)
                                | Task::LocalFunctionValue(..)
                                | Task::MatchBranch(..)
                                | Task::DoBindJoinBody(..)
                                | Task::DoBindJoinValue(..)
                                | Task::ProofTerm(..)
                                | Task::RefineTerm(..)
                        )
                    );
                    let mut ready = pending.take_ready(self)?;
                    if ready.is_none()
                        && (tasks.is_empty() || closes_scope)
                        && pending.has_current_scope(self)?
                    {
                        // A let/lambda closes before the overall term worklist
                        // is empty. Finish inference while captured locals are
                        // still available, resuming between individual defaults
                        // so the callback can constrain other pending numerals.
                        self.resolve_instances(false)?;
                        self.flush(false)?;
                        ready = pending.take_ready(self)?;
                        if ready.is_none() {
                            let blockers = pending.scope_blockers(self)?;
                            if !blockers.is_empty() {
                                for (index, attempt) in attempts.iter().enumerate().rev() {
                                    self.tick()?;
                                    if let Attempt::Argument(checkpoint) = attempt
                                        && let Some(blocker) =
                                            checkpoint.outer_blocker(self, &blockers)?
                                    {
                                        // Rewind the whole containing argument,
                                        // not an already-closed inner lambda.
                                        // The blocker belongs to that snapshot.
                                        blocked_application = Some(blocker);
                                        containing_argument = Some(index);
                                        return Err(failure(
                                            SourceInferenceError::ExpectedFunction,
                                        ));
                                    }
                                }
                            }
                            if self.resolve_next_default_instance()? {
                                continue;
                            }
                        }
                    }
                    if let Some(argument) = ready {
                        let checkpoint = postponed::Checkpoint::resume(
                            self,
                            &pending,
                            argument,
                            tasks.len(),
                            values.len(),
                        );
                        let syntax = checkpoint.syntax;
                        let expected = checkpoint.expected.clone();
                        let index = attempts.len();
                        attempts.push(Attempt::Argument(Box::new(checkpoint)));
                        tasks.push(Task::ArgumentComplete(index));
                        tasks.push(Task::Visit(syntax, Some(expected), true));
                    }
                    let Some(task) = tasks.pop() else {
                        pending.finish(self)?;
                        break;
                    };
                    self.tick()?;
                    if matches!(
                        &task,
                        Task::BinderBody(..)
                            | Task::LetBody(..)
                            | Task::LocalFunctionValue(..)
                            | Task::MatchBranch(..)
                            | Task::DoBindJoinBody(..)
                            | Task::DoBindJoinValue(..)
                            | Task::ProofTerm(..)
                            | Task::RefineTerm(..)
                    ) {
                        // Every still-unresolved argument keeps its original
                        // scope. A later assignment cannot enter a lambda or
                        // structural branch after that scope has been closed.
                        pending.close_scope(self)?;
                    }
                    match task {
                        Task::CheckArgument(syntax, expected, infer_exception_action) => {
                            if let Some(checkpoint) = postponed::Checkpoint::argument(
                                self,
                                &pending,
                                syntax,
                                expected.clone(),
                                tasks.len(),
                                values.len(),
                            )? {
                                let index = attempts.len();
                                attempts.push(Attempt::Argument(Box::new(checkpoint)));
                                tasks.push(Task::ArgumentComplete(index));
                            }
                            if infer_exception_action {
                                tasks.push(Task::InferredExceptionArgument(expected));
                                tasks.push(Task::Visit(syntax, None, true));
                            } else {
                                tasks.push(Task::Visit(syntax, Some(expected), true));
                            }
                        }
                        Task::InferredExceptionArgument(expected) => {
                            let action = values.pop().expect("inferred protected action visit");
                            values.push(self.finish_do_exception_action(action, &expected)?);
                        }
                        Task::ArgumentComplete(index) => {
                            if index + 1 != attempts.len() {
                                return Err(failure(SourceInferenceError::Scope));
                            }
                            let Some(Attempt::Argument(checkpoint)) = attempts.last() else {
                                return Err(failure(SourceInferenceError::Scope));
                            };
                            if checkpoint.tasks != tasks.len()
                                || checkpoint.values + 1 != values.len()
                            {
                                return Err(failure(SourceInferenceError::Scope));
                            }
                            if let Some(hole) = &checkpoint.hole {
                                let value = values.pop().expect("resumed argument visit");
                                self.constrain(hole, &value.value)?;
                            }
                            attempts.pop();
                        }
                        Task::DoAction(arguments, expected) => {
                            let action = values.pop().expect("do action visit");
                            let function = self.do_action(action)?;
                            tasks.push(Task::Apply(
                                function,
                                Arguments::Plain(arguments),
                                expected,
                                false,
                            ));
                        }
                        Task::CalcNext(build) => {
                            if let Some(step) = build.steps.get(build.cursor) {
                                let relation = step.0;
                                // The pin elaborates a calc relation with
                                // `elabType`; its result may inhabit any Sort.
                                let expected = self.type_expected()?;
                                tasks.push(Task::CalcRelation(build));
                                tasks.push(Task::Visit(relation, Some(expected), true));
                            } else {
                                values.push(self.finish_calculation(build)?);
                            }
                        }
                        Task::CalcRelation(mut build) => {
                            let relation = values.pop().expect("calculation relation visit");
                            let relation = self.prepare_calculation_step(&mut build, relation)?;
                            let proof = build.steps[build.cursor].1;
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
                        Task::Observe(syntax, locals) => {
                            let term = values.last().expect("observed term visit");
                            self.observe_term(syntax, term.clone(), locals)?;
                        }
                        Task::CaptureRecursiveContext => {
                            let value = values.pop().expect("contextual match visit");
                            values.push(self.capture_recursive_context(value)?);
                        }
                        Task::Visit(syntax, expected, finish) => {
                            if self.observes_term(syntax) {
                                tasks.push(Task::Observe(syntax, self.txn.lctx.clone()));
                            }
                            if let Some(inner) = parenthesized_inner(syntax)? {
                                tasks.push(Task::Visit(inner, expected, finish));
                                continue;
                            }
                            let (head, explicit) = self.explicit_application_head(syntax)?;
                            if explicit {
                                tasks.push(Task::StartApplication(head, &[], expected, true));
                                continue;
                            }
                            if let Syntax::Node { kind, args, .. } = syntax {
                                if kind == &parser_kind(&["Term", "recursiveContextCapture"]) {
                                    let [body] = args.as_slice() else {
                                        return Err(failure(SourceInferenceError::Scope));
                                    };
                                    tasks.push(Task::CaptureRecursiveContext);
                                    tasks.push(Task::Visit(body, expected, finish));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "nativeDoForCollection"]) {
                                    let [collection] = args.as_slice() else {
                                        return Err(failure(SourceInferenceError::Scope));
                                    };
                                    tasks.push(Task::ForCollection(expected));
                                    tasks.push(Task::Visit(collection, None, true));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "nativeDoJoin"]) {
                                    let (name, suffix, body) = do_notation::join_parts(args)?;
                                    tasks.push(Task::DoJoinValue(name, body, expected.clone()));
                                    tasks.push(Task::Visit(suffix, expected, true));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "nativeDoBindJoin"]) {
                                    let (name, continuation, body) = do_notation::join_parts(args)?;
                                    let result_type = match expected {
                                        Some(expected) => expected,
                                        None => {
                                            let sort = self.type_expected()?;
                                            self.hole(sort)?
                                        }
                                    };
                                    let annotation = do_notation::bind_join_domain(continuation)?;
                                    tasks.push(Task::DoBindJoinStart(
                                        name,
                                        continuation,
                                        body,
                                        result_type,
                                        annotation.is_some(),
                                    ));
                                    if let Some(annotation) = annotation {
                                        tasks.push(Task::Visit(
                                            annotation,
                                            Some(self.type_expected()?),
                                            true,
                                        ));
                                    }
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "nativeDoNestedAnnotation"]) {
                                    let [annotation, body] = args.as_slice() else {
                                        return Err(failure(SourceInferenceError::Scope));
                                    };
                                    tasks.push(Task::DoNestedAnnotation(body, expected, finish));
                                    tasks.push(Task::Visit(
                                        annotation,
                                        Some(self.type_expected()?),
                                        true,
                                    ));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "nativeDoBind"])
                                    || kind == &parser_kind(&["Term", "nativeDoPure"])
                                    || kind == &parser_kind(&["Term", "nativeDoNestedAction"])
                                {
                                    let nested =
                                        kind == &parser_kind(&["Term", "nativeDoNestedAction"]);
                                    let bind =
                                        nested || kind == &parser_kind(&["Term", "nativeDoBind"]);
                                    if args.len() != if bind { 2 } else { 1 } {
                                        return Err(failure(SourceInferenceError::Scope));
                                    }
                                    let monad = match &expected {
                                        Some(type_) => self.do_monad(type_)?,
                                        None => None,
                                    };
                                    if bind && monad.is_none() && !nested {
                                        tasks.push(Task::DoAction(&args[1..], expected));
                                        tasks.push(Task::Visit(&args[0], None, true));
                                    } else {
                                        let function = self.do_operation(bind, monad)?;
                                        let function = if nested {
                                            self.do_nested_action_function(function, &args[1])?
                                        } else if bind {
                                            function
                                        } else {
                                            self.do_pure_result(function, expected.as_ref())?
                                        };
                                        tasks.push(Task::Apply(
                                            function,
                                            Arguments::Plain(args),
                                            expected,
                                            false,
                                        ));
                                    }
                                    continue;
                                }
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
                                    // A name written at a promoted parameter position
                                    // (`| .done k, _`): the pin's type mismatch.
                                    if let Syntax::Ident { val: column, .. } = subject
                                        && self.inaccessible_columns.contains(column)
                                    {
                                        return Err(failure(SourceInferenceError::Match(
                                            matching::MatchError::InaccessibleParameter,
                                        )));
                                    }
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
                                    tasks.push(Task::LetBody(
                                        saved,
                                        id,
                                        name.clone(),
                                        value,
                                        false,
                                        false,
                                    ));
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
                                    || kind == &Name::from_components(["termIfThenElse"])
                                    || kind == &Name::from_components(["termDepIfThenElse"])
                                {
                                    let parts = self.match_parts(syntax)?;
                                    let discriminant = parts.discriminant;
                                    tasks.push(Task::MatchDiscriminant(parts, expected));
                                    tasks.push(Task::Visit(discriminant, None, true));
                                    continue;
                                }
                                // `bif c then a else b` is `cond c a b` (`Init/Notation.lean`).
                                if kind == &Name::from_components(["boolIfThenElse"]) {
                                    let parts =
                                        expect_node(syntax, kind, 6, "boolean conditional")?;
                                    expect_atom(&parts[0], "bif", "boolean conditional")?;
                                    expect_atom(&parts[2], "then", "boolean conditional")?;
                                    expect_atom(&parts[4], "else", "boolean conditional")?;
                                    let function =
                                        self.constant(&Name::from_components(["cond"]))?;
                                    tasks.push(Task::Apply(
                                        function,
                                        Arguments::Separated(&parts[1..], &["then", "else"]),
                                        expected,
                                        false,
                                    ));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "subst"]) {
                                    let term = self.substitution(args, expected.as_ref())?;
                                    values.push(if finish {
                                        self.finish_term(term, expected.as_ref())?
                                    } else {
                                        term
                                    });
                                    continue;
                                }
                                // `no_index e` is `e`: it only keeps `e` out of simp's
                                // discrimination-tree keys (`Lean/Elab/BuiltinNotation.lean`).
                                if kind == &parser_kind(&["Term", "noindex"]) {
                                    let parts = expect_node(syntax, kind, 2, "no_index")?;
                                    expect_atom(&parts[0], "no_index", "no_index")?;
                                    tasks.push(Task::Visit(&parts[1], expected, finish));
                                    continue;
                                }
                                // `e |>.f args` is `(e).f args` (`Term.pipeProj`'s macro,
                                // `Lean/Elab/BuiltinNotation.lean`).
                                if kind == &parser_kind(&["Term", "pipeProj"]) {
                                    let parts =
                                        expect_node(syntax, kind, 5, "pipeline projection")?;
                                    expect_atom(&parts[1], "|>.", "pipeline projection")?;
                                    expect_empty_null(&parts[3], "pipeline projection")?;
                                    let field = record_terms::projection_field(&parts[2])?;
                                    let arguments = expect_null_args(
                                        &parts[4],
                                        "pipeline projection arguments",
                                    )?;
                                    tasks.push(Task::Projection(
                                        field, arguments, expected, false, finish,
                                    ));
                                    tasks.push(Task::Visit(&parts[0], None, true));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "proj"]) {
                                    let parts = expect_node(syntax, kind, 3, "field projection")?;
                                    expect_atom(&parts[1], ".", "field dot")?;
                                    let field = record_terms::projection_field(&parts[2])?;
                                    tasks.push(Task::Projection(
                                        field,
                                        &[],
                                        expected,
                                        false,
                                        finish,
                                    ));
                                    tasks.push(Task::Visit(&parts[0], None, true));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "suffices"]) {
                                    let (name, annotation, witness, continuation) =
                                        self.suffices_parts(args)?;
                                    // Backward chaining checks the last source term
                                    // first. The proposed fact is not in its own scope.
                                    tasks.push(Task::LetAnnotation(
                                        name,
                                        witness,
                                        continuation,
                                        expected,
                                        true,
                                        false,
                                    ));
                                    tasks.push(Task::Visit(
                                        annotation,
                                        Some(self.type_expected()?),
                                        true,
                                    ));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "show"]) {
                                    let parts = expect_node(syntax, kind, 3, "show term")?;
                                    expect_atom(&parts[0], "show", "show keyword")?;
                                    let value = if parts[2].kind()
                                        == Some(&parser_kind(&["Term", "byTactic'"]))
                                    {
                                        &parts[2]
                                    } else {
                                        let rhs = expect_node(
                                            &parts[2],
                                            &parser_kind(&["Term", "fromTerm"]),
                                            2,
                                            "show value",
                                        )?;
                                        expect_atom(&rhs[0], "from", "show separator")?;
                                        &rhs[1]
                                    };
                                    tasks.push(Task::Ascription(value, expected, true));
                                    tasks.push(Task::Visit(
                                        &parts[1],
                                        Some(self.type_expected()?),
                                        true,
                                    ));
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
                                    tasks.push(Task::Ascription(&parts[1], expected, false));
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
                                if kind == &Name::from_components(["Lean", "calc"])
                                    || kind == &Name::from_components(["Lean", "calcTactic"])
                                {
                                    tasks.push(Task::CalcNext(
                                        self.start_calculation(syntax, expected)?,
                                    ));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "byTactic"])
                                    || kind == &parser_kind(&["Term", "byTactic'"])
                                {
                                    tasks.push(Task::Proof(self.start_proof(syntax, expected)?));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "let"])
                                    || kind == &parser_kind(&["Term", "have"])
                                    || kind == &parser_kind(&["Term", "letrec"])
                                    || kind == &parser_kind(&["Term", "letI"])
                                    || kind == &parser_kind(&["Term", "haveI"])
                                {
                                    let opaque = kind == &parser_kind(&["Term", "have"])
                                        || kind == &parser_kind(&["Term", "haveI"]);
                                    // `letI`/`haveI` elaborate as `let`/`have` and then inline
                                    // the value (`Lean/Elab/BuiltinNotation.lean`).
                                    let inline = kind == &parser_kind(&["Term", "letI"])
                                        || kind == &parser_kind(&["Term", "haveI"]);
                                    let recursive = kind == &parser_kind(&["Term", "letrec"]);
                                    let binding = self.let_parts(args, opaque, recursive)?;
                                    let parameters = !expect_null_args(
                                        binding.parameters,
                                        "local function parameters",
                                    )?
                                    .is_empty();
                                    if inline && parameters {
                                        return Err(NatDefinitionElabError::UnexpectedSyntax {
                                            expected: "an inlined local without parameters",
                                        });
                                    }
                                    if recursive || parameters {
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
                                            tasks.push(Task::LocalFunctionValue(
                                                build,
                                                self.postponed_application_errors.len(),
                                            ));
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
                                        tasks.push(Task::LetAnnotation(
                                            name, value, body, expected, opaque, inline,
                                        ));
                                        tasks.push(Task::Visit(
                                            annotation,
                                            Some(self.type_expected()?),
                                            true,
                                        ));
                                    } else {
                                        tasks.push(Task::LetValue(
                                            name, None, body, expected, opaque, inline,
                                        ));
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
                                // The pin's `binop%`/`binrel%`/`unop%`/`rightact%`
                                // expression trees. A notation whose function is
                                // absent keeps the seed bridge below.
                                if let Some(notation) = operators::pin_notation(kind)
                                    && self.pin_notation_available(notation)?
                                {
                                    let tree = self.operator_tree(syntax, notation)?;
                                    let leaves = tree.leaves.clone();
                                    tasks.push(Task::Operator(tree, expected));
                                    for leaf in leaves.into_iter().rev() {
                                        tasks.push(Task::Visit(leaf, None, true));
                                    }
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "anonymousCtor"]) {
                                    let parts =
                                        expect_node(syntax, kind, 3, "anonymous constructor")?;
                                    expect_atom(&parts[0], "⟨", "anonymous constructor opener")?;
                                    expect_atom(&parts[2], "⟩", "anonymous constructor closer")?;
                                    let elements = expect_null_args(
                                        &parts[1],
                                        "anonymous constructor fields",
                                    )?;
                                    for (index, element) in elements.iter().enumerate() {
                                        if index % 2 == 1 {
                                            expect_atom(element, ",", "field separator")?;
                                        }
                                    }
                                    let provided = elements.len().div_ceil(2);
                                    let function = match self
                                        .anonymous_constructor(expected.as_ref(), provided)
                                    {
                                        Err(NatDefinitionElabError::Inference(
                                            SourceInferenceError::AnonymousCtor(
                                                anonymous_ctor::AnonymousCtorError::NestedFieldsUnsupported {
                                                    explicit,
                                                    ..
                                                },
                                            ),
                                        )) => {
                                            // The pin's rewrite: the extra arguments become one
                                            // `⟨…⟩` for the last explicit field.
                                            let nested =
                                                anonymous_ctor::nest_fields(elements, explicit);
                                            values.push(self.term_prepared(&nested, expected)?);
                                            continue;
                                        }
                                        other => other?,
                                    };
                                    tasks.push(Task::Apply(
                                        function,
                                        Arguments::Separated(elements, &[","]),
                                        expected,
                                        false,
                                    ));
                                    continue;
                                }
                                if kind == &Name::str(Name::anonymous(), "term¬_") {
                                    let parts =
                                        expect_node(syntax, kind, 2, "propositional negation")?;
                                    expect_atom(&parts[0], "¬", "negation prefix")?;
                                    let function =
                                        self.constant(&Name::from_components(["Not"]))?;
                                    tasks.push(Task::Apply(
                                        function,
                                        Arguments::Plain(&parts[1..]),
                                        expected,
                                        false,
                                    ));
                                    continue;
                                }
                                // `"!" b:40 => not b` and `prefix:100 "~~~" => Complement.complement`
                                // (`Init/Notation.lean`; `not` is `Bool.not`, exported).
                                let prefix = [
                                    ("!", ["Bool", "not"]),
                                    ("~~~", ["Complement", "complement"]),
                                ]
                                .into_iter()
                                .find(|(spelling, _)| {
                                    kind == &Name::str(
                                        Name::anonymous(),
                                        format!("term{spelling}_"),
                                    )
                                });
                                if let Some((spelling, constant)) = prefix {
                                    let parts = expect_node(syntax, kind, 2, "prefix operator")?;
                                    expect_atom(&parts[0], spelling, "prefix operator")?;
                                    let function =
                                        self.constant(&Name::from_components(constant))?;
                                    tasks.push(Task::Apply(
                                        function,
                                        Arguments::Plain(&parts[1..]),
                                        expected,
                                        false,
                                    ));
                                    continue;
                                }
                                // `postfix:max "⁻¹" => Inv.inv` (`Init/Prelude.lean`).
                                if kind == &Name::str(Name::anonymous(), "term_⁻¹") {
                                    let parts = expect_node(syntax, kind, 2, "inverse")?;
                                    expect_atom(&parts[1], "⁻¹", "inverse postfix")?;
                                    let function =
                                        self.constant(&Name::from_components(["Inv", "inv"]))?;
                                    tasks.push(Task::Apply(
                                        function,
                                        Arguments::Plain(&parts[..1]),
                                        expected,
                                        false,
                                    ));
                                    continue;
                                }
                                // The ranges with an unbounded side, in namespace `Std`
                                // (`Init/Data/Range/Polymorphic/PRange.lean`): `macro_rules`
                                // makes `*...b` and `*...<b` `Rio.mk b`, `*...=b` `Ric.mk b`,
                                // `a...*` `Rci.mk a`, `a<...*` `Roi.mk a` and `*...*` `Rii.mk`.
                                let unbounded = [
                                    ("term*..._", "*...", "Rio", 1..2),
                                    ("term*...<_", "*...<", "Rio", 1..2),
                                    ("term*...=_", "*...=", "Ric", 1..2),
                                    ("term_...*", "...*", "Rci", 0..1),
                                    ("term_<...*", "<...*", "Roi", 0..1),
                                    ("term*...*", "*...*", "Rii", 1..1),
                                ]
                                .into_iter()
                                .find(|(label, ..)| kind == &Name::from_components(["Std", label]));
                                if let Some((_, spelling, constant, operands)) = unbounded {
                                    let arity = if operands.is_empty() { 1 } else { 2 };
                                    let parts =
                                        expect_node(syntax, kind, arity, "unbounded range")?;
                                    let symbol = if operands.start == 0 { arity - 1 } else { 0 };
                                    expect_atom(&parts[symbol], spelling, "unbounded range")?;
                                    let function = self.constant(&Name::from_components([
                                        "Std", constant, "mk",
                                    ]))?;
                                    tasks.push(Task::Apply(
                                        function,
                                        Arguments::Plain(&parts[operands]),
                                        expected,
                                        false,
                                    ));
                                    continue;
                                }
                                if kind == &Name::str(Name::anonymous(), "term-_") {
                                    let parts =
                                        expect_node(syntax, kind, 2, "arithmetic negation")?;
                                    expect_atom(&parts[0], "-", "negation prefix")?;
                                    let function =
                                        self.constant(&Name::from_components(["Neg", "neg"]))?;
                                    tasks.push(Task::Apply(
                                        function,
                                        Arguments::Plain(&parts[1..]),
                                        expected,
                                        false,
                                    ));
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
                                    tasks.push(Task::StartApplication(
                                        head, arguments, expected, explicit,
                                    ));
                                    continue;
                                }
                                // `f <| a` and `a |> f` are the application `f a`
                                // (`Init/Notation.lean:522`). The pin's macros also flatten
                                // `f x <| a` and `a |> f x` into `f x a`; that form is refused
                                // here rather than read as `(f x) a`.
                                let pipeline = if kind == &Name::from_components(["term_<|_"]) {
                                    Some(("<|", 0, 2))
                                } else if kind == &Name::from_components(["term_$__"]) {
                                    // `f $ a`, `<|`'s other spelling (`Init/Notation.lean:557`).
                                    Some(("$", 0, 2))
                                } else if kind == &Name::from_components(["term_|>_"]) {
                                    Some(("|>", 2, 0))
                                } else {
                                    None
                                };
                                if let Some((operator, function, argument)) = pipeline {
                                    let parts = expect_node(syntax, kind, 3, "pipeline")?;
                                    expect_atom(&parts[1], operator, "pipeline operator")?;
                                    if matches!(&parts[function], Syntax::Node { kind, .. }
                                        if kind == &parser_kind(&["Term", "app"]))
                                    {
                                        return Err(NatDefinitionElabError::UnexpectedSyntax {
                                            expected: "a pipeline whose function is not an application",
                                        });
                                    }
                                    let (head, explicit) =
                                        self.explicit_application_head(&parts[function])?;
                                    tasks.push(Task::StartApplication(
                                        head,
                                        std::slice::from_ref(&parts[argument]),
                                        expected,
                                        explicit,
                                    ));
                                    continue;
                                }
                                if let Some(intrinsic) = bounded_infix_intrinsic(kind, true) {
                                    let parts = expect_node(syntax, kind, 3, "scalar infix")?;
                                    if !intrinsic.spelled_by(&parts[1]) {
                                        return Err(NatDefinitionElabError::UnexpectedSyntax {
                                            expected: "scalar operator",
                                        });
                                    }
                                    // `(a : α) × β a` is the pin's dependent pair
                                    // (`Init/NotationExtra.lean:93`, `Sigma`/`PSigma`), not
                                    // `Prod` of an ascription.
                                    if matches!(intrinsic.spelling(), "×" | "×'")
                                        && matches!(&parts[0], Syntax::Node { kind, .. }
                                            if kind == &parser_kind(&["Term", "typeAscription"]))
                                    {
                                        return Err(NatDefinitionElabError::UnexpectedSyntax {
                                            expected: "a product of types, not a dependent pair",
                                        });
                                    }
                                    tasks.push(Task::Infix(intrinsic, expected));
                                    tasks.push(Task::Visit(&parts[2], None, true));
                                    tasks.push(Task::Visit(&parts[0], None, true));
                                    continue;
                                }
                            }
                            let term = match self.atom(syntax, expected.as_ref()) {
                                Ok(term) => term,
                                Err(error) => {
                                    // An identifier naming more than one declaration is
                                    // overloaded: the pin's `elabAtom` -> `elabAppAux`.
                                    if finish
                                        && let Some((name, candidates)) =
                                            overload::ambiguous_head(&error, syntax)
                                    {
                                        values.push(self.overloaded(
                                            syntax,
                                            None,
                                            &name,
                                            &candidates,
                                            expected.as_ref(),
                                        )?);
                                        continue;
                                    }
                                    return Err(error);
                                }
                            };
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
                        Task::Projection(field, arguments, expected, explicit, finish) => {
                            let receiver = values.pop().expect("receiver precedes projection");
                            match self.resolve_field_path(
                                receiver,
                                &field,
                                !arguments.is_empty(),
                            )? {
                                record_terms::FieldResolution::Value(term)
                                    if arguments.is_empty() =>
                                {
                                    values.push(if finish {
                                        self.finish_term(term, expected.as_ref())?
                                    } else {
                                        term
                                    });
                                }
                                record_terms::FieldResolution::Value(term) => {
                                    values.push(term);
                                    tasks.push(Task::Function(arguments, expected, explicit));
                                }
                                record_terms::FieldResolution::Method {
                                    function,
                                    receiver,
                                    base,
                                } => {
                                    tasks.push(Task::NamedNext(self.start_field_application(
                                        function, receiver, &base, arguments, expected, explicit,
                                    )?));
                                }
                            }
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
                        Task::Ascription(syntax, expected, show) => {
                            let type_ = values.pop().expect("ascription type visit");
                            self.sort_level(&type_)?;
                            if show && let Some(expected) = &expected {
                                self.constrain_result_hint(&type_.value, expected)?;
                            }
                            tasks.push(Task::AscribedValue(type_.value.clone(), expected, show));
                            tasks.push(Task::Visit(syntax, Some(type_.value), true));
                        }
                        Task::AscribedValue(annotation, expected, show) => {
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
                                    show,
                                ),
                                // `show` pins the structural result type, not merely
                                // a definitionally equal inferred type. Rewriters
                                // consume precisely the equation the user wrote.
                                type_: if show { annotation } else { term.type_ },
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
                        Task::ChangeTarget(mut proof, goal) => {
                            let annotation = values.pop().expect("change target visit");
                            self.change_proof_goal(&mut proof, goal, annotation)?;
                            tasks.push(Task::Proof(proof));
                        }
                        Task::Proof(mut proof) => match self.advance_proof(&mut proof)? {
                            tactics::ProofAction::Change { goal, target } => {
                                self.txn.lctx = goal.lctx.clone();
                                tasks.push(Task::ChangeTarget(proof, goal));
                                tasks.push(Task::Visit(target, Some(self.type_expected()?), true));
                            }
                            tactics::ProofAction::Simpa { goal, args, using } => {
                                self.txn.lctx = goal.lctx.clone();
                                tasks.push(Task::SimpaTerm(proof, goal, args));
                                tasks.push(Task::Visit(using, None, true));
                            }
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
                                attempts.push(Attempt::Proof(checkpoint, pending.clone()));
                                tasks.push(Task::Proof(branch));
                            }
                            tactics::ProofAction::AttemptComplete(index) => {
                                if index + 1 != attempts.len() {
                                    return Err(failure(SourceInferenceError::Scope));
                                }
                                let Some(Attempt::Proof(checkpoint, _)) = attempts.pop() else {
                                    return Err(failure(SourceInferenceError::Scope));
                                };
                                if checkpoint.tasks != tasks.len()
                                    || checkpoint.values != values.len()
                                {
                                    return Err(failure(SourceInferenceError::Scope));
                                }
                                checkpoint.finish(self, &mut proof);
                                if let Some(mut next) = checkpoint.next_iteration(self, &proof) {
                                    proof = next.begin(self, attempts.len())?;
                                    attempts.push(Attempt::Proof(next, pending.clone()));
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
                        Task::SimpaTerm(mut proof, goal, args) => {
                            let term = values.pop().expect("simpa evidence visit");
                            self.simpa_proof_term(&mut proof, goal, args, Some(term))?;
                            tasks.push(Task::Proof(proof));
                        }
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
                                    && self.postponed_application_errors.is_empty()
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
                        Task::StartApplication(head, arguments, expected, explicit) => {
                            let receiver = match self.field_application_receiver(head) {
                                Ok(receiver) => receiver,
                                Err(error) => {
                                    // An overloaded head: every interpretation of the
                                    // whole application (the pin's `elabAppAux`).
                                    if !explicit
                                        && let Some((name, candidates)) =
                                            overload::ambiguous_head(&error, head)
                                    {
                                        values.push(self.overloaded(
                                            head,
                                            Some(arguments),
                                            &name,
                                            &candidates,
                                            expected.as_ref(),
                                        )?);
                                        continue;
                                    }
                                    return Err(error);
                                }
                            };
                            match receiver {
                                Some(record_terms::FieldReceiver::Syntax(receiver, field)) => {
                                    tasks.push(Task::Projection(
                                        field, arguments, expected, explicit, true,
                                    ));
                                    tasks.push(Task::Visit(receiver, None, true));
                                }
                                Some(record_terms::FieldReceiver::Elaborated(receiver, field)) => {
                                    values.push(receiver);
                                    tasks.push(Task::Projection(
                                        field, arguments, expected, explicit, true,
                                    ));
                                }
                                // `.c a b`: the head resolves against the expected type
                                // of the whole application (`elabAppFn`'s dotIdent case).
                                None if head.kind()
                                    == Some(&parser_kind(&["Term", "dotIdent"])) =>
                                {
                                    let Syntax::Node { args, .. } = head else {
                                        return Err(failure(SourceInferenceError::Scope));
                                    };
                                    values.push(self.dotted_identifier(args, expected.as_ref())?);
                                    tasks.push(Task::Function(arguments, expected, explicit));
                                }
                                None => {
                                    tasks.push(Task::Function(arguments, expected, explicit));
                                    tasks.push(Task::Visit(head, None, false));
                                }
                            }
                        }
                        Task::Function(arguments, expected, explicit) => {
                            let function = values.pop().expect("function task follows its visit");
                            if let Some(info) =
                                self.eliminator_info(&function, arguments, explicit)?
                            {
                                let term = self.eliminator_application(
                                    function,
                                    arguments,
                                    info,
                                    expected.clone(),
                                )?;
                                values.push(self.finish_explicit_term(term, expected.as_ref())?);
                            } else if application::has_named(arguments) {
                                tasks.push(Task::NamedNext(self.start_named_application(
                                    function, arguments, expected, explicit,
                                )?));
                            } else {
                                tasks.push(Task::Apply(
                                    function,
                                    Arguments::Plain(arguments),
                                    expected,
                                    explicit,
                                ));
                            }
                        }
                        Task::ForCollection(expected) => {
                            let collection = values.pop().expect("loop collection visit");
                            let collection = self.finish_term(collection, expected.as_ref())?;
                            // Numeric defaults must precede dependent callback
                            // checking, so the admitted ForIn' dictionary can
                            // supply the element and membership proof types.
                            self.resolve_instances_with_defaults()?;
                            values.push(self.finish_term(collection, expected.as_ref())?);
                        }
                        Task::NamedNext(mut state) => {
                            let next = self.next_named_argument(&mut state);
                            if matches!(
                                &next,
                                Err(NatDefinitionElabError::Inference(
                                    SourceInferenceError::ExpectedFunction
                                        | SourceInferenceError::InvalidNamedArgument(_)
                                ))
                            ) {
                                blocked_application =
                                    self.application_type_unavailable(state.function_type())?;
                                if blocked_application.is_some() {
                                    return Err(failure(SourceInferenceError::ExpectedFunction));
                                }
                            }
                            if let Some(argument) = next? {
                                match argument.value {
                                    application::ApplicationValue::Syntax(syntax) => {
                                        tasks.push(Task::NamedArgument(state, argument.codomain));
                                        tasks.push(Task::CheckArgument(
                                            syntax,
                                            argument.domain,
                                            argument.infer_exception_action,
                                        ));
                                    }
                                    application::ApplicationValue::Elaborated(value) => {
                                        let value = if argument.infer_exception_action {
                                            self.finish_do_exception_action(
                                                value,
                                                &argument.domain,
                                            )?
                                        } else {
                                            let value =
                                                self.finish_term(value, Some(&argument.domain))?;
                                            self.constrain_type(&value.type_, &argument.domain)?;
                                            value
                                        };
                                        self.add_named_argument(
                                            &mut state,
                                            &argument.codomain,
                                            value,
                                        )?;
                                        tasks.push(Task::NamedNext(state));
                                    }
                                }
                            } else {
                                values.push(self.finish_named_application(state)?);
                            }
                        }
                        Task::NamedArgument(mut state, codomain) => {
                            let argument = values.pop().expect("named argument follows its value");
                            self.add_named_argument(&mut state, &codomain, argument)?;
                            tasks.push(Task::NamedNext(state));
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
                                let callee_type = function.type_.clone();
                                let coerced = self.coerce_function(function);
                                if matches!(
                                    &coerced,
                                    Err(NatDefinitionElabError::Inference(
                                        SourceInferenceError::ExpectedFunction
                                    ))
                                ) {
                                    blocked_application =
                                        self.application_type_unavailable(&callee_type)?;
                                }
                                let function = coerced?;
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
                                    self.do_operation_result_hint(&function, &codomain, expected)?;
                                    self.constrain_result_hint(&codomain, expected)?;
                                }
                                tasks.push(Task::Argument(
                                    function, codomain, rest, expected, explicit,
                                ));
                                tasks.push(Task::CheckArgument(first, domain, false));
                            } else {
                                values.push(if explicit {
                                    self.finish_explicit_term(function, expected.as_ref())?
                                } else {
                                    self.finish_application(function, expected.as_ref())?
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
                        Task::Operator(tree, expected) => {
                            let start = values
                                .len()
                                .checked_sub(tree.leaves.len())
                                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                            let leaves = values.split_off(start);
                            values.push(self.finish_operator_tree(
                                tree,
                                leaves,
                                expected.as_ref(),
                            )?);
                        }
                        Task::Infix(intrinsic, expected) => {
                            let right = values.pop().expect("infix right visit");
                            let left = values.pop().expect("infix left visit");
                            self.flush(false)?;
                            let notation =
                                match crate::instances::numeric::notation(intrinsic.spelling()) {
                                    Some((class, method)) if self.has_numeric_class(class)? => {
                                        Some(Name::from_components([class, method]))
                                    }
                                    _ => None,
                                };
                            let negated = matches!(
                                intrinsic,
                                BoundedInfixIntrinsic::Membership { negated: true }
                            );
                            let swapped =
                                matches!(intrinsic, BoundedInfixIntrinsic::Membership { .. });
                            let name = if let Some(name) = notation {
                                name
                            } else {
                                match intrinsic {
                                    BoundedInfixIntrinsic::Fixed { intrinsic, .. } => intrinsic,
                                    BoundedInfixIntrinsic::Membership { .. } => {
                                        Name::from_components(["Membership", "mem"])
                                    }
                                    BoundedInfixIntrinsic::ScalarBeq => {
                                        if self.instantiate(&left.type_)? == string_const()
                                            && self.instantiate(&right.type_)? == string_const()
                                        {
                                            Name::from_components(["String", "decEq"])
                                        } else {
                                            Name::from_components(["Nat", "beq"])
                                        }
                                    }
                                }
                            };
                            let mut function = self.constant(&name)?;
                            let operands = if swapped {
                                [right, left]
                            } else {
                                [left, right]
                            };
                            for argument in operands {
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
                            if negated {
                                let mut not = self.constant(&Name::from_components(["Not"]))?;
                                let ExprNode::ForallE {
                                    binder_type, body, ..
                                } = not.type_.node()
                                else {
                                    return Err(failure(SourceInferenceError::ExpectedFunction));
                                };
                                let (domain, body) = (binder_type.clone(), body.clone());
                                let membership = self.finish_term(function, Some(&domain))?;
                                self.constrain_type(&membership.type_, &domain)?;
                                not.type_ = self.substitute(&body, &membership.value)?;
                                not.value = Expr::app(not.value, membership.value);
                                function = not;
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
                            if build.binding.recursive {
                                let mut checkpoint = local_functions::Checkpoint::new(
                                    self,
                                    build,
                                    tasks.len(),
                                    values.len(),
                                )?;
                                let (build, column) = checkpoint.begin(attempts.len());
                                attempts.push(Attempt::LocalFunction(
                                    Box::new(checkpoint),
                                    pending.clone(),
                                ));
                                tasks.push(Task::LocalFunctionStart(build, column));
                            } else {
                                let value = build.binding.value;
                                tasks.push(Task::LocalFunctionValue(
                                    build,
                                    self.postponed_application_errors.len(),
                                ));
                                tasks.push(Task::Visit(value, Some(annotation.value), true));
                            }
                        }
                        Task::LocalFunctionStart(mut build, column) => {
                            self.start_local_function_value(&mut build, column)?;
                            let value = build.value_syntax;
                            let expected = build.result_type.clone();
                            tasks.push(Task::LocalFunctionValue(
                                build,
                                self.postponed_application_errors.len(),
                            ));
                            tasks.push(Task::Visit(value, expected, true));
                        }
                        Task::LocalFunctionValue(build, postponed_start) => {
                            if build.checkpoint.is_some() {
                                // Completed local bodies hand selected errors
                                // to their own structural candidate checkpoint.
                                self.require_no_postponed_recursion_since(postponed_start)?;
                            }
                            let value = values.pop().expect("local function value visit");
                            let value = self.close_local_function(&build, value)?;
                            if let Some(index) = build.checkpoint {
                                if index + 1 != attempts.len() {
                                    return Err(failure(SourceInferenceError::Scope));
                                }
                                let Some(Attempt::LocalFunction(checkpoint, _)) = attempts.pop()
                                else {
                                    return Err(failure(SourceInferenceError::Scope));
                                };
                                if checkpoint.tasks != tasks.len()
                                    || checkpoint.values != values.len()
                                {
                                    return Err(failure(SourceInferenceError::Scope));
                                }
                            }
                            values.push(value);
                            tasks.push(Task::LetValue(
                                build.binding.name,
                                None,
                                build.binding.body,
                                build.expected,
                                build.binding.opaque,
                                false,
                            ));
                        }
                        Task::LetAnnotation(name, value, body, expected, opaque, inline) => {
                            let annotation = values.pop().expect("let annotation visit");
                            self.sort_level(&annotation)?;
                            tasks.push(Task::LetValue(
                                name,
                                Some(annotation.value.clone()),
                                body,
                                expected,
                                opaque,
                                inline,
                            ));
                            tasks.push(Task::Visit(value, Some(annotation.value), true));
                        }
                        Task::DoJoinValue(name, body, expected) => {
                            let value = values.pop().expect("do continuation visit");
                            // The suffix is checked in the OUTER lexical scope
                            // against the original expected monad, before alias
                            // reduction or branch-local binders can obscure it.
                            let result_type = expected.unwrap_or_else(|| value.type_.clone());
                            let value = self.do_join_thunk(value, &result_type)?;
                            // Treat a join as a function parameter while checking
                            // branches. Expanding its body here would duplicate
                            // pending dictionaries into dependent local contexts.
                            // LetBody still emits the actual checked core let.
                            let saved = self.txn.lctx.clone();
                            let id = FVarId(self.fresh_name()?);
                            self.txn.lctx.add_param(
                                id.clone(),
                                name.clone(),
                                value.type_.clone(),
                                BinderInfo::Default,
                            );
                            tasks.push(Task::LetBody(saved, id, name, value, false, false));
                            tasks.push(Task::Visit(body, Some(result_type), true));
                        }
                        Task::DoBindJoinStart(name, continuation, body, result_type, annotated) => {
                            let domain = if annotated {
                                let annotation = values.pop().expect("nested do binder annotation");
                                self.sort_level(&annotation)?;
                                annotation.value
                            } else {
                                let sort = self.type_expected()?;
                                self.hole(sort)?
                            };
                            let continuation_type = Expr::forall_e(
                                Name::anonymous(),
                                domain,
                                result_type
                                    .lift_loose(0, 1)
                                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                                BinderInfo::Default,
                            );
                            // Check normal actions against an opaque parameter
                            // first: their actual results determine its domain.
                            // No suffix expression guesses a record receiver type.
                            let saved = self.txn.lctx.clone();
                            let id = FVarId(self.fresh_name()?);
                            self.txn.lctx.add_param(
                                id.clone(),
                                name.clone(),
                                continuation_type.clone(),
                                BinderInfo::Default,
                            );
                            tasks.push(Task::DoBindJoinBody(
                                saved,
                                id,
                                name,
                                continuation,
                                continuation_type,
                            ));
                            tasks.push(Task::Visit(body, Some(result_type), true));
                        }
                        Task::DoBindJoinBody(saved, id, name, continuation, continuation_type) => {
                            let body = values.pop().expect("nested do body visit");
                            self.flush(false)?;
                            self.txn.lctx = saved.clone();
                            // The suffix sees its original lexical scope and the
                            // domain inferred from normal actions (or annotation).
                            tasks.push(Task::DoBindJoinValue(saved, id, name, body));
                            tasks.push(Task::Visit(continuation, Some(continuation_type), true));
                        }
                        Task::DoBindJoinValue(saved, id, name, body) => {
                            let continuation = values.pop().expect("nested do continuation visit");
                            values.push(body);
                            tasks.push(Task::LetBody(saved, id, name, continuation, false, false));
                        }
                        Task::DoNestedAnnotation(body, expected, finish) => {
                            let annotation =
                                values.pop().expect("dead nested do binder annotation");
                            self.sort_level(&annotation)?;
                            tasks.push(Task::Visit(body, expected, finish));
                        }
                        Task::LetValue(name, annotation, body, expected, opaque, inline) => {
                            let mut value = values.pop().expect("let value visit");
                            if let Some(annotation) = annotation {
                                value.type_ = annotation;
                            }
                            let saved = self.txn.lctx.clone();
                            let id = FVarId(self.fresh_name()?);
                            if opaque {
                                // A `have` witness is checked, but cannot unfold in
                                // the continuation's elaboration context.
                                self.txn.lctx.add_param(
                                    id.clone(),
                                    name.clone(),
                                    value.type_.clone(),
                                    BinderInfo::Default,
                                );
                                self.opaque_locals.insert(id.clone());
                            } else {
                                self.txn.lctx.add_let(
                                    id.clone(),
                                    name.clone(),
                                    value.type_.clone(),
                                    value.value.clone(),
                                );
                            }
                            tasks.push(Task::LetBody(saved, id, name, value, opaque, inline));
                            tasks.push(Task::Visit(body, expected, true));
                        }
                        Task::LetBody(saved, id, name, value, opaque, inline) => {
                            if opaque {
                                // Do not postpone equations past the context that
                                // gives this assertion its opaque interpretation.
                                self.flush(true)?;
                                self.opaque_locals.remove(&id);
                            }
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
                            let value = if inline {
                                // `letI`/`haveI`: the value replaces the variable.
                                self.substitute(&abstract_body, &value.value)?
                            } else {
                                Expr::let_e(name, value.type_, value.value, abstract_body, opaque)
                            };
                            values.push(Typed { value, type_ });
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
                        let Some(attempt) = attempts.pop() else {
                            return Err(problem);
                        };
                        if let Some(target) = containing_argument {
                            if attempts.len() > target {
                                // This is suspension, not a failing tactic.
                                // The target's complete checkpoint restores all
                                // nested choices and work, retaining spent fuel.
                                self.tick()?;
                                continue;
                            }
                            if attempts.len() != target || !matches!(&attempt, Attempt::Argument(_))
                            {
                                return Err(failure(SourceInferenceError::Scope));
                            }
                        }
                        match attempt {
                            Attempt::Argument(checkpoint) => {
                                tasks.truncate(checkpoint.tasks);
                                values.truncate(checkpoint.values);
                                checkpoint.restore(self, &mut pending);
                                self.tick()?;
                                if let Some(blocker) = &blocked_application
                                    && let Some(value) =
                                        checkpoint.postpone(self, &mut pending, blocker)?
                                {
                                    if checkpoint.hole.is_none() {
                                        values.push(value);
                                    }
                                    break;
                                }
                                if containing_argument.is_some() {
                                    return Err(failure(SourceInferenceError::Scope));
                                }
                                if checkpoint.hole.is_some()
                                    && !matches!(
                                        &problem,
                                        NatDefinitionElabError::Inference(
                                            SourceInferenceError::Recursion(
                                                recursion::RecursionError::GeneralizeParameter { .. }
                                            )
                                        )
                                    )
                                {
                                    // Synthetic argument errors belong to the
                                    // selected term. `first` may still roll back
                                    // an explicit later failure, but cannot turn
                                    // a bad postponed `exact` into success.
                                    // Motive generalization is an immediate
                                    // retry signal; other recursion diagnostics
                                    // surface at their completed body boundary.
                                    self.postponed_application_errors.push(problem.clone());
                                    break;
                                }
                            }
                            Attempt::LocalFunction(mut checkpoint, queue) => {
                                tasks.truncate(checkpoint.tasks);
                                values.truncate(checkpoint.values);
                                checkpoint.restore(self);
                                pending = queue;
                                self.tick()?;
                                if checkpoint.retry(&problem) {
                                    let (build, column) = checkpoint.begin(attempts.len());
                                    attempts
                                        .push(Attempt::LocalFunction(checkpoint, pending.clone()));
                                    tasks.push(Task::LocalFunctionStart(build, column));
                                    break;
                                }
                            }
                            Attempt::Proof(mut checkpoint, queue) => {
                                tasks.truncate(checkpoint.tasks);
                                values.truncate(checkpoint.values);
                                checkpoint.restore(self);
                                pending = queue;
                                self.tick()?;
                                // Motive discovery belongs to the enclosing
                                // recursion driver, not a tactic alternative.
                                if matches!(
                                    &problem,
                                    NatDefinitionElabError::Inference(
                                        SourceInferenceError::Recursion(
                                            recursion::RecursionError::GeneralizeParameter { .. }
                                        )
                                    )
                                ) {
                                    continue;
                                }
                                if checkpoint.retry() {
                                    let proof = checkpoint.begin(self, attempts.len())?;
                                    attempts.push(Attempt::Proof(checkpoint, pending.clone()));
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
        }
    }

    fn suffices_parts<'a>(
        &mut self,
        parts: &'a [Syntax],
    ) -> Result<(Name, &'a Syntax, &'a Syntax, &'a Syntax), NatDefinitionElabError> {
        let [keyword, declaration, separator, witness] = parts else {
            return Err(failure(SourceInferenceError::Scope));
        };
        expect_atom(keyword, "suffices", "suffices keyword")?;
        if separator.kind() == Some(&Name::from_components(["null"])) {
            expect_empty_null(separator, "suffices linebreak")?;
        } else {
            expect_atom(separator, ";", "suffices separator")?;
        }
        let parts = expect_node(
            declaration,
            &parser_kind(&["Term", "sufficesDecl"]),
            3,
            "suffices declaration",
        )?;
        // `atomic (group (binderIdent " : ")) <|> hygieneInfo`.
        let name = if parts[0].kind() == Some(&Name::from_components(["group"])) {
            let [id, colon] = expect_node(
                &parts[0],
                &Name::from_components(["group"]),
                2,
                "suffices binder",
            )?
            else {
                return Err(failure(SourceInferenceError::Scope));
            };
            expect_atom(colon, ":", "suffices binder colon")?;
            let Syntax::Ident { val, .. } = id else {
                return Err(failure(SourceInferenceError::Scope));
            };
            if val.is_anonymous() {
                return Err(NatDefinitionElabError::AnonymousReferenceName);
            }
            val.clone()
        } else {
            let hygiene = expect_node(
                &parts[0],
                &Name::from_components(["hygieneInfo"]),
                1,
                "suffices hygiene",
            )?;
            if !matches!(&hygiene[0], Syntax::Ident { val, preresolved, .. } if val.is_anonymous() && preresolved.is_empty())
            {
                return Err(failure(SourceInferenceError::Scope));
            }
            Name::from_components(["this"])
        };
        let continuation = if parts[2].kind() == Some(&parser_kind(&["Term", "byTactic'"])) {
            &parts[2]
        } else {
            let rhs = expect_node(
                &parts[2],
                &parser_kind(&["Term", "fromTerm"]),
                2,
                "suffices continuation",
            )?;
            expect_atom(&rhs[0], "from", "suffices proof introducer")?;
            &rhs[1]
        };
        Ok((name, &parts[1], witness, continuation))
    }

    fn let_parts<'a>(
        &mut self,
        parts: &'a [Syntax],
        opaque: bool,
        recursive: bool,
    ) -> Result<local_functions::Binding<'a>, NatDefinitionElabError> {
        let (declaration, separator, body, termination) = if recursive {
            let [keywords, declarations, separator, body] = parts else {
                return Err(failure(SourceInferenceError::Scope));
            };
            let [keyword, rec] = expect_node(
                keywords,
                &Name::str(Name::anonymous(), "group"),
                2,
                "let rec keywords",
            )?
            else {
                return Err(failure(SourceInferenceError::Scope));
            };
            expect_atom(keyword, "let", "recursive local keyword")?;
            expect_atom(rec, "rec", "recursive local keyword")?;
            let declarations = expect_node(
                declarations,
                &parser_kind(&["Term", "letRecDecls"]),
                1,
                "local recursive group",
            )?;
            let [declaration] =
                expect_null_args(&declarations[0], "single local recursive definition")?
            else {
                return Err(failure(SourceInferenceError::Scope));
            };
            let declaration = expect_node(
                declaration,
                &parser_kind(&["Term", "letRecDecl"]),
                4,
                "local recursive definition",
            )?;
            // A local declaration's doc comment has no meaning the kernel sees.
            match expect_null_args(&declaration[0], "local doc comment")? {
                [] => {}
                [doc] => {
                    let doc = expect_node(
                        doc,
                        &parser_kind(&["Command", "docComment"]),
                        2,
                        "local doc comment",
                    )?;
                    expect_atom(&doc[0], "/--", "local doc comment opener")?;
                }
                _ => {
                    return Err(NatDefinitionElabError::UnexpectedSyntax {
                        expected: "one local doc comment",
                    });
                }
            }
            expect_empty_null(&declaration[1], "absent local attributes")?;
            let termination = recursion::structural_hint(&declaration[3])?;
            (&declaration[2], separator, body, termination)
        } else {
            let [keyword, config, declaration, separator, body] = parts else {
                return Err(failure(SourceInferenceError::Scope));
            };
            // `letI`/`haveI` share the grammar; the caller reads which from the node kind.
            let (plain, inlined) = if opaque {
                ("have", "haveI")
            } else {
                ("let", "letI")
            };
            if !matches!(keyword, Syntax::Atom { val, .. } if val == plain || val == inlined) {
                return Err(NatDefinitionElabError::UnexpectedSyntax {
                    expected: "local binding keyword",
                });
            }
            let config = expect_node(
                config,
                &parser_kind(&["Term", "letConfig"]),
                1,
                "let config",
            )?;
            expect_empty_null(&config[0], "empty let config")?;
            (declaration, separator, body, None)
        };
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
        let name = if let Syntax::Ident { val: name, .. } = &id[0] {
            name.clone()
        } else if opaque {
            let hygiene = expect_node(
                &id[0],
                &Name::from_components(["hygieneInfo"]),
                1,
                "anonymous assertion hygiene",
            )?;
            if !matches!(&hygiene[0], Syntax::Ident { val, preresolved, .. } if val.is_anonymous() && preresolved.is_empty())
            {
                return Err(failure(SourceInferenceError::Scope));
            }
            Name::from_components(["this"])
        } else {
            return Err(failure(SourceInferenceError::Scope));
        };
        if name.is_anonymous() {
            return Err(NatDefinitionElabError::AnonymousReferenceName);
        }
        expect_null_args(&declaration[1], "local function parameters")?;
        let annotation = optional_type_syntax(&declaration[2])?;
        expect_atom(&declaration[3], ":=", "let assignment")?;
        if separator.kind() == Some(&Name::from_components(["null"])) {
            expect_empty_null(separator, "local declaration linebreak")?;
        } else {
            expect_atom(separator, ";", "let separator")?;
        }
        Ok(local_functions::Binding {
            name,
            opaque,
            recursive,
            parameters: &declaration[1],
            annotation,
            value: &declaration[4],
            body,
            termination,
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

    /// Assign every universe metavariable still open in `term` a fresh parameter
    /// `u_1`, `u_2`, … in order of first occurrence (value, then type), returning the
    /// parameters.
    fn generalize_level_mvars(
        &mut self,
        term: &Typed,
    ) -> Result<Vec<Name>, NatDefinitionElabError> {
        self.resolve_instances(true)?;
        self.resume_postponed_eliminators(true)?;
        self.flush(true)?;
        let value = self.instantiate(&term.value)?;
        let type_ = self.instantiate(&term.type_)?;
        let mut order: Vec<LMVarId> = Vec::new();
        let mut exprs = vec![type_, value];
        while let Some(expr) = exprs.pop() {
            self.tick()?;
            if !expr.has_level_mvar() {
                continue;
            }
            let mut levels: Vec<Level> = Vec::new();
            match expr.node() {
                ExprNode::Sort { level } => levels.push(level.clone()),
                // Popped from the end: pushed in reverse so the first is seen first.
                ExprNode::Const { levels: args, .. } => levels.extend(args.iter().rev().cloned()),
                ExprNode::App { f, a } => {
                    exprs.push(a.clone());
                    exprs.push(f.clone());
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    exprs.push(body.clone());
                    exprs.push(binder_type.clone());
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    exprs.push(body.clone());
                    exprs.push(value.clone());
                    exprs.push(type_.clone());
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    exprs.push(expr.clone());
                }
                _ => {}
            }
            while let Some(level) = levels.pop() {
                match level.view() {
                    fln_core::level::LevelView::MVar(id) => {
                        if !order.contains(id) {
                            order.push(id.clone());
                        }
                    }
                    fln_core::level::LevelView::Succ(inner) => levels.push(inner.clone()),
                    fln_core::level::LevelView::Max(a, b)
                    | fln_core::level::LevelView::IMax(a, b) => {
                        levels.push(b.clone());
                        levels.push(a.clone());
                    }
                    _ => {}
                }
            }
        }
        let mut parameters = Vec::with_capacity(order.len());
        for (index, id) in order.into_iter().enumerate() {
            let parameter = Name::str(Name::anonymous(), format!("u_{}", index + 1));
            self.txn
                .universes
                .assign(id, Level::param(parameter.clone()));
            parameters.push(parameter);
        }
        Ok(parameters)
    }

    fn finish(&mut self, term: Typed) -> Result<Typed, NatDefinitionElabError> {
        if let Some(error) = self.postponed_application_errors.first() {
            return Err(error.clone());
        }
        self.resolve_instances(true)?;
        self.resume_postponed_eliminators(true)?;
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
            let domain = match type_parts {
                [colon, type_syntax] => {
                    expect_atom(colon, ":", "binder type ascription")?;
                    self.type_term(type_syntax)?
                }
                // `{α}`: the pin elaborates an omitted binder type as a hole
                // (`Lean/Elab/Binders.lean`, `mkHole`), which unification must fill.
                [] => {
                    let hole = Syntax::node(
                        parser_kind(&["Term", "hole"]),
                        vec![Syntax::atom(fln_syntax::source::SourceInfo::None, "_")],
                    );
                    self.type_term(&hole)?
                }
                _ => return Err(failure(SourceInferenceError::ExpectedType)),
            };
            for name in names {
                let name = match name {
                    Syntax::Ident { val, .. } => val.clone(),
                    // `_` binds a name no source identifier spells, as an unnamed instance
                    // binder does above (the pin's `mkFreshIdent`).
                    Syntax::Node { kind, args, .. }
                        if kind == &parser_kind(&["Term", "hole"])
                            && matches!(args.as_slice(), [Syntax::Atom { val, .. }] if val == "_") =>
                    {
                        self.fresh_name()?
                    }
                    _ => return Err(failure(SourceInferenceError::Scope)),
                };
                let id = FVarId(self.fresh_name()?);
                self.txn
                    .lctx
                    .add_param(id.clone(), name, domain.clone(), style);
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
    definition_in_context(syntax, &mut context)
}

fn definition_in_context(
    syntax: &Syntax,
    context: &mut Context,
) -> Result<Declaration, NatDefinitionElabError> {
    definition_in_context_named(syntax, context, None)
}

fn definition_in_context_named(
    syntax: &Syntax,
    context: &mut Context,
    generated_name: Option<Name>,
) -> Result<Declaration, NatDefinitionElabError> {
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
    let mut is_protected = false;
    for (index, modifier) in modifiers.iter().enumerate() {
        match index {
            0 => doc_comment_slot(modifier)?,
            1 => {}
            PROTECTED_SLOT => is_protected = protected_slot(modifier)?,
            _ => expect_empty_null(modifier, "empty declaration modifier")?,
        }
    }
    if is_protected && generated_name.is_some() {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "a named protected declaration",
        });
    }
    let is_instance = matches!(&declaration[1], Syntax::Node { kind,.. } if kind==&parser_kind(&["Command","instance"]));
    let is_theorem = matches!(&declaration[1], Syntax::Node { kind,.. } if kind==&parser_kind(&["Command","theorem"]));
    let instance_parts;
    let definition = if is_instance {
        let parts = instance_command::parts(&declaration[1])?;
        instance_parts = [
            parts.keyword.clone(),
            match parts.id {
                Some(id) => id.clone(),
                // Anonymous: a placeholder `declId` whose name is generated below,
                // once the signature is elaborated (`mkInstanceName`).
                None => Syntax::node(
                    parser_kind(&["Command", "declId"]),
                    vec![
                        Syntax::Ident {
                            info: fln_syntax::source::SourceInfo::None,
                            raw_val: fln_syntax::source::ByteSpan::default(),
                            val: Name::anonymous(),
                            preresolved: Vec::new(),
                        },
                        Syntax::node(Name::from_components(["null"]), Vec::new()),
                    ],
                ),
            },
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
    let anonymous_instance = is_instance && name.is_anonymous() && generated_name.is_none();
    if name.is_anonymous() && !anonymous_instance {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    }
    if is_protected {
        context.check_protected_declaration_name(name)?;
    }
    // Anonymous examples retain their surrounding lookup scope. Their internal
    // numeric identity is never a source namespace or a recursive source name.
    // An anonymous instance stays in the current namespace; its name is generated
    // after its signature.
    let mut owned_name = match generated_name {
        Some(generated) => generated,
        None if anonymous_instance => Name::anonymous(),
        None => context.enter_declaration(name)?,
    };
    // The pin tags a protected declaration before elaborating its body, and
    // names its recursive local `<last namespace component>.<short name>`, so
    // the body cannot reach it by its atomic name either.
    context.protected_declaration = is_protected.then(|| owned_name.clone());
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
    context.resume_postponed_eliminators(true)?;
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
    if anonymous_instance {
        let expected = expected
            .as_ref()
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        owned_name = context.generated_instance_name(&parameters, expected)?;
    }
    let name = &owned_name;
    let theorem_section_parameters = if is_theorem {
        let mut roots: Vec<_> = parameters.iter().map(|local| local.type_.clone()).collect();
        roots.extend(expected.iter().cloned());
        let selected = context.section_parameters(&roots, true)?;
        context.restrict_section_locals(&selected);
        Some(selected)
    } else {
        None
    };
    let equations = definition[3].kind() == Some(&parser_kind(&["Command", "declValEqns"]));
    let struct_instance;
    let empty_suffix;
    let empty_where;
    // `whereStructInst` is any declaration's value (`declVal`, `Lean/Parser/Command.lean`).
    let (body, termination, where_clause) =
        if definition[3].kind() == Some(&parser_kind(&["Command", "whereStructInst"])) {
            struct_instance = where_struct_instance(&definition[3])?;
            empty_suffix = Syntax::node(
                parser_kind(&["Termination", "suffix"]),
                vec![
                    Syntax::node(Name::from_components(["null"]), Vec::new()),
                    Syntax::node(Name::from_components(["null"]), Vec::new()),
                ],
            );
            empty_where = Syntax::node(Name::from_components(["null"]), Vec::new());
            (&struct_instance, &empty_suffix, &empty_where)
        } else if equations {
            let parts = expect_node(
                &definition[3],
                &parser_kind(&["Command", "declValEqns"]),
                1,
                "equation value",
            )?;
            let parts = expect_node(
                &parts[0],
                &parser_kind(&["Term", "matchAltsWhereDecls"]),
                3,
                "equation alternatives",
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
    let termination = recursion::structural_hint(termination)?;
    // `where` declarations scope over the body as `let rec` declarations, the pin's
    // `expandWhereDecls`; each is its own group here, so a later one may call an
    // earlier one.
    let with_where;
    let body = match expect_null_args(where_clause, "where clause")? {
        [] => body,
        [where_decls] if !equations => {
            with_where = where_body(where_decls, body)?;
            &with_where
        }
        _ => return Err(failure(SourceInferenceError::Scope)),
    };
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
    let header_parameters = parameters.len();
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
    let mut term = context.definition_body(
        name,
        &parameters,
        body,
        expected.clone(),
        termination.as_ref(),
        header_parameters,
    )?;
    if let Some(expected) = expected {
        term.type_ = expected;
    }
    // Section variables are fixed during recursion, not recursive arguments.
    // Only after body elaboration are their used dependencies prepended.
    context.resolve_instances(true)?;
    context.resume_postponed_eliminators(true)?;
    context.flush(true)?;
    let section_parameters = if let Some(selected) = theorem_section_parameters {
        selected
    } else {
        let mut roots: Vec<_> = parameters.iter().map(|local| local.type_.clone()).collect();
        roots.extend([term.type_.clone(), term.value.clone()]);
        context.section_parameters(&roots, false)?
    };
    parameters.splice(0..0, section_parameters);
    let mut universe_roots: Vec<_> = parameters
        .iter()
        .map(|parameter| parameter.type_.clone())
        .collect();
    universe_roots.extend([term.type_.clone(), term.value.clone()]);
    context.generalize_declaration_universes(&universe_roots)?;
    let mut term = context.finish(term)?;
    // Preserve the source's actual lambda stages. Eta-expanding a computed
    // function moves its strict initializer under a new binder and delays it
    // until an argument arrives. Native runtime preparation owns function
    // aliases and computed closures without changing the admitted term.
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
    // The pin compiles every declaration but a theorem (`codegen.rs`).
    if !is_theorem {
        context.check_compiled_recursors(&term.value)?;
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
    query_in(syntax, name, Context::new(environment, kernel), evaluate)
}

/// [`query`] with names resolved in a source scope (namespaces, `open`).
pub(super) fn query_scoped(
    syntax: &Syntax,
    name: Name,
    environment: &Environment,
    kernel: Budget,
    evaluate: bool,
    scope: &scope::SourceScope,
) -> Result<Declaration, NatDefinitionElabError> {
    query_in(
        syntax,
        name,
        Context::scoped(environment, kernel, scope),
        evaluate,
    )
}

fn query_in(
    syntax: &Syntax,
    name: Name,
    mut context: Context,
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
    let mut term = context.term(&parts[1], None)?;
    if evaluate {
        let (head, explicit) = context.explicit_application_head(&parts[1])?;
        if !explicit
            && (matches!(head, Syntax::Ident { .. })
                || head.kind() == Some(&parser_kind(&["Term", "explicitUniv"])))
        {
            // The pin elaborates an identifier through `elabAppArgs`, even
            // with no written arguments, and synthesizes its instance binders
            // (`Lean/Elab/App.lean`, `elabAtom`/`processInstImplicitArg`).
            // A bare `#eval selected` must evaluate the selected dictionary's
            // value. Do not guess ordinary implicit parameters or apply a
            // function's explicit arguments; `@selected` stays explicit.
            term = context.insert_implicits(term, ImplicitInsertion::InstanceQuery)?;
        }
    }
    // `#check` generalizes universe metavariables the term leaves open to fresh
    // parameters `u_1`, `u_2`, … (the pin's `levelMVarToParam`), so `#check @List.map`
    // has a type; `#eval` needs a closed, concrete term and keeps the refusal.
    let level_params = if evaluate {
        Vec::new()
    } else {
        context.generalize_level_mvars(&term)?
    };
    let term = context.finish(term)?;
    // `#eval` compiles its term (`codegen.rs`); `#check` does not.
    if evaluate {
        context.check_compiled_recursors(&term.value)?;
    }
    Ok(Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name.clone(),
            level_params,
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

/// `declModifiers`' `protected` slot: docComment, attributes, visibility, then
/// `protected` (vendored `src/Lean/Parser/Command.lean`, `declModifiers`).
const PROTECTED_SLOT: usize = 3;

/// `declModifiers`' doc comment slot: empty, or the pin's `docComment` node. A docstring adds
/// no declaration and no meaning the kernel sees; the reference-manual links the pin validates
/// were checked when the command was partitioned.
pub(crate) fn doc_comment_slot(slot: &Syntax) -> Result<(), NatDefinitionElabError> {
    match expect_null_args(slot, "doc comment")? {
        [] => Ok(()),
        [doc] => {
            let parts = expect_node(
                doc,
                &parser_kind(&["Command", "docComment"]),
                2,
                "doc comment",
            )?;
            expect_atom(&parts[0], "/--", "doc comment opener")?;
            Ok(())
        }
        _ => Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "one doc comment",
        }),
    }
}

/// Whether a `protected` slot is set: empty, or exactly one
/// `Lean.Parser.Command.protected` node holding the keyword.
fn protected_slot(slot: &Syntax) -> Result<bool, NatDefinitionElabError> {
    match expect_null_args(slot, "protected modifier")? {
        [] => Ok(false),
        [modifier] => {
            let parts = expect_node(
                modifier,
                &parser_kind(&["Command", "protected"]),
                1,
                "protected modifier",
            )?;
            expect_atom(&parts[0], "protected", "protected keyword")?;
            Ok(true)
        }
        _ => Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "one protected modifier",
        }),
    }
}

/// The name a `protected` definition, theorem or instance is written with, if
/// the command is one. The caller derives the full name from the scope, as for
/// [`instance_registration`], and tags it in the protected-declaration journal
/// only once the council has admitted the declaration. The pin tags it in
/// `applyVisibility` (vendored `src/Lean/Elab/DeclModifiers.lean`).
pub fn protected_registration(syntax: &Syntax) -> Result<Option<Name>, NatDefinitionElabError> {
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
    if !protected_slot(&modifiers[PROTECTED_SLOT])? {
        return Ok(None);
    }
    let instance = matches!(&declaration[1], Syntax::Node { kind, .. }
        if kind == &parser_kind(&["Command", "instance"]));
    let id = if instance {
        instance_command::parts(&declaration[1])?
            .id
            .cloned()
            .ok_or(NatDefinitionElabError::AnonymousDeclarationName)?
    } else {
        let Syntax::Node { args, .. } = &declaration[1] else {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "named declaration",
            });
        };
        args.get(1)
            .cloned()
            .ok_or(NatDefinitionElabError::UnexpectedSyntax {
                expected: "declaration id",
            })?
    };
    let id = expect_node(
        &id,
        &parser_kind(&["Command", "declId"]),
        2,
        "declaration id",
    )?;
    match &id[0] {
        Syntax::Ident { val, .. } if !val.is_anonymous() => Ok(Some(val.clone())),
        _ => Err(NatDefinitionElabError::AnonymousDeclarationName),
    }
}

pub use inductive::{elaborate_inductive, is_inductive};
/// A source record/class expands to a block and projections, not one definition.
/// These are untrusted candidates. The caller must admit the whole sequence
/// before registering the class or exposing any successor.
pub use record::{SourceRecord, elaborate_record, is_record};

#[cfg(test)]
mod conversion_tests;

/// `body` under the `let rec` declarations of a `Term.whereDecls` block, first declaration
/// outermost.
fn where_body(where_decls: &Syntax, body: &Syntax) -> Result<Syntax, NatDefinitionElabError> {
    let parts = expect_node(
        where_decls,
        &parser_kind(&["Term", "whereDecls"]),
        3,
        "where declarations",
    )?;
    expect_atom(&parts[0], "where", "where keyword")?;
    expect_empty_null(&parts[2], "where trailing separator")?;
    let items = expect_null_args(&parts[1], "where declaration list")?;
    let mut declarations = Vec::new();
    for (index, item) in items.iter().enumerate() {
        if index % 2 == 1 {
            expect_empty_null(item, "where declaration separator")?;
        } else {
            expect_node(
                item,
                &parser_kind(&["Term", "letRecDecl"]),
                4,
                "where declaration",
            )?;
            declarations.push(item.clone());
        }
    }
    let null = |args: Vec<Syntax>| Syntax::node(Name::from_components(["null"]), args);
    let atom = |text: &str| Syntax::atom(fln_syntax::source::SourceInfo::None, text);
    let mut result = body.clone();
    for declaration in declarations.into_iter().rev() {
        result = Syntax::node(
            parser_kind(&["Term", "letrec"]),
            vec![
                Syntax::node(
                    Name::str(Name::anonymous(), "group"),
                    vec![atom("let"), atom("rec")],
                ),
                Syntax::node(
                    parser_kind(&["Term", "letRecDecls"]),
                    vec![null(vec![declaration])],
                ),
                null(Vec::new()),
                result,
            ],
        );
    }
    Ok(result)
}

/// `instance … where fields` (`Command.whereStructInst`) as the structure instance
/// `{ fields }` it elaborates to. The ordinary field expansion subsequently lowers
/// method binders and result annotations, for both `where` and record literals.
/// A field defined by equations, `f | p => e …` (`structInstFieldEqns`), as the field
/// `f := fun | p => e …`, which the pattern-lambda lowering reads; any other field unchanged.
fn field_equations_as_lambda(field: &Syntax) -> Syntax {
    let Syntax::Node { kind, args, .. } = field else {
        return field.clone();
    };
    let Some(Syntax::Node { args: payload, .. }) = args.get(1) else {
        return field.clone();
    };
    let [
        binders,
        annotation,
        Syntax::Node {
            kind: definition,
            args: equations,
            ..
        },
    ] = payload.as_slice()
    else {
        return field.clone();
    };
    if definition != &parser_kind(&["Term", "structInstFieldEqns"])
        || equations.len() != 2
        || !matches!(&equations[0], Syntax::Node { args, .. } if args.is_empty())
    {
        return field.clone();
    }
    let null = |args: Vec<Syntax>| Syntax::node(Name::from_components(["null"]), args);
    let atom = |text: &str| Syntax::atom(fln_syntax::source::SourceInfo::None, text);
    let lambda = Syntax::node(
        parser_kind(&["Term", "fun"]),
        vec![atom("fun"), equations[1].clone()],
    );
    let value = Syntax::node(
        parser_kind(&["Term", "structInstFieldDef"]),
        vec![atom(":="), null(Vec::new()), lambda],
    );
    Syntax::node(
        kind.clone(),
        vec![
            args[0].clone(),
            null(vec![binders.clone(), annotation.clone(), value]),
        ],
    )
}

fn where_struct_instance(syntax: &Syntax) -> Result<Syntax, NatDefinitionElabError> {
    let parts = expect_node(
        syntax,
        &parser_kind(&["Command", "whereStructInst"]),
        3,
        "instance where block",
    )?;
    expect_atom(&parts[0], "where", "instance where keyword")?;
    expect_empty_null(&parts[2], "instance deriving clause")?;
    let fields = expect_node(
        &parts[1],
        &parser_kind(&["Term", "structInstFields"]),
        1,
        "instance fields",
    )?;
    let items = expect_null_args(&fields[0], "instance field list")?;
    let null = |args: Vec<Syntax>| Syntax::node(Name::from_components(["null"]), args);
    let atom = |text: &str| Syntax::atom(fln_syntax::source::SourceInfo::None, text);
    let mut rows = Vec::with_capacity(items.len());
    for (index, item) in items.iter().enumerate() {
        if index % 2 == 1 {
            expect_empty_null(item, "instance field separator")?;
            rows.push(atom(","));
            continue;
        }
        expect_node(
            item,
            &parser_kind(&["Term", "structInstField"]),
            2,
            "instance field",
        )?;
        rows.push(field_equations_as_lambda(item));
    }
    Ok(Syntax::node(
        parser_kind(&["Term", "structInst"]),
        vec![
            atom("{"),
            null(Vec::new()),
            Syntax::node(parser_kind(&["Term", "structInstFields"]), vec![null(rows)]),
            Syntax::node(
                parser_kind(&["Term", "optEllipsis"]),
                vec![null(Vec::new())],
            ),
            null(Vec::new()),
            atom("}"),
        ],
    ))
}
