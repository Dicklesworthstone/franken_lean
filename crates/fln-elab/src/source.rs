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
pub mod evaluation;
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
mod optional;
mod overload;
pub mod partial;
mod pattern_typing;
mod public_body;
pub use public_body::{
    elaborate_public_definition, is_definition_body, public_definition_header_is_hidden,
};
mod patterns;
mod record;
mod record_terms;
mod recursion;
mod reduce;
mod tactics;
pub mod trace;

use super::*;
use crate::constraint::unify::{
    UnificationBudget, UnificationDeferred, UnificationError, UnificationReport,
    UnificationTransparency,
};
use fln_core::expr::{FVarId, MVarId};
use fln_core::level::{LMVarId, Level};
use fln_core::options::KVMap;

/// What the pin's refusal of a field-notation receiver prints: the head of the
/// selected function, the receiver's type head, and the receiver in the local
/// context it was elaborated in.
#[derive(Debug, Clone, PartialEq)]
pub struct FieldReceiverRefusal {
    pub function: Expr,
    pub base: Name,
    pub receiver: Expr,
    pub locals: crate::lctx::LocalContext,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SourceInferenceError {
    NameScope(scope::ScopeError),
    Recursion(recursion::RecursionError),
    Match(matching::MatchError),
    Inductive(crate::inductive::InductiveError),
    Auxiliary(crate::inductive::auxiliaries::AuxiliaryError),
    Deriving(deriving::DerivingError),
    EvaluationPrinting(evaluation::PrintingError),
    UnknownConstant(Name),
    /// An auto-bound implicit's type mentions a binder written after it (the pin's
    /// `addAutoBoundImplicits`, Lean/Elab/Term/TermElabM.lean:2044-2058).
    AutoBoundDependsOnExplicit {
        auto: Name,
        explicit: Name,
    },
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
    /// Field notation found no parameter whose type has the receiver's head
    /// (vendored `Lean/Elab/App.lean:1786-1794`). The pin's message names the
    /// function, that head and the receiver, so the refusal keeps all three.
    InvalidFieldReceiver(Box<FieldReceiverRefusal>),
    /// Field notation's parameter can be passed neither by position nor by name.
    UnusableFieldParameter(Name),
    LevelSyntax(LevelSyntaxError),
    ExpectedFunction,
    /// Argument processing exhausted a known function telescope, and the
    /// pin's imported `CoeFun` has no active global, scoped or local provider.
    /// Unlike an initially unknown callee, this is the pin's terminal
    /// `synthesizePendingAndNormalizeFunType` refusal, not a postponement.
    FunctionCoercionAbsent,
    ExpectedType,
    RecordTerm(record_terms::RecordTermError),
    Record(crate::records::RecordError),
    TypeObligation(Box<Outcome<Verdict>>),
    /// A completed conversion query refused at elaboration's transparency.
    /// This is not a kernel rejection of the declaration: ordinary admission
    /// may unfold definitions that this query must keep opaque.
    ConversionRefused(Box<Verdict>),
    Tactic(tactics::TacticError),
    ArithmeticInconclusive(Box<fln_core::outcome::Inconclusive>),
    UnresolvedHoles {
        count: usize,
    },
    UnresolvedUniverses,
    InstanceSynthesisRequired,
    /// The pin's eliminator elaboration (`elabAsElim`) could not finish; the
    /// text is the pin's own message after "failed to elaborate eliminator, ".
    Eliminator(&'static str),
    /// A compiled declaration applies a recursor the pin's code generator does not
    /// support (`codegen.rs`, bead `franken_lean-z8j.1.6.6`).
    UnsupportedRecursor(Name),
    /// A generated recOn has no compiled LCNF signature at the pin.
    AuxiliaryNotCompiled(Name),
    /// A surviving executable reference has no compiled implementation.
    NoncomputableDependency(Name),
    /// Invalid dependency metadata cannot become a suppressed compiler failure.
    NoncomputableJournal(crate::noncomputable::NoncomputableError),
    ExternJournal(crate::externs::ExternError),
    ImplementedByJournal(crate::implemented_by::ImplementedByError),
    InvalidInstanceBinder,
    InstanceRegistry(crate::instances::InstanceRegistryError),
    Option(scope::options::OptionRefusal),
    SimpSet(scope::simp::SimpSetError),
    /// The protected-declaration journal refused a tag.
    ProtectedJournal(crate::protected_names::ProtectedError),
    AuxiliaryJournal(crate::aux_recursors::AuxRecursorError),
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
            Self::Auxiliary(error) => write!(f, "{error}"),
            Self::Deriving(error) => write!(f, "{error}"),
            Self::EvaluationPrinting(error) => write!(f, "{error}"),
            Self::Option(error) => write!(f, "{error}"),
            // The pin's two wordings for `lean.unknownIdentifier`, verbatim.
            Self::UnknownConstant(name) => {
                write!(f, "Unknown identifier `{}`", name.to_display_string())
            }
            Self::UnknownMemberConstant(name) => {
                write!(f, "Unknown constant `{}`", name.to_display_string())
            }
            Self::AutoBoundDependsOnExplicit { auto, explicit } => write!(
                f,
                "invalid auto implicit argument `{}`, it depends on explicitly provided argument `{}`",
                auto.to_display_string(),
                explicit.to_display_string()
            ),
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
            Self::InvalidFieldReceiver(refusal) => {
                let function = match refusal.function.node() {
                    ExprNode::Const { name, .. } => format!("`{}`", name.to_display_string()),
                    _ => "the selected function".to_string(),
                };
                write!(
                    f,
                    "Invalid field notation: Function {function} does not have a usable \
                     parameter of type `{}` for which to substitute the receiver",
                    refusal.base.to_display_string()
                )
            }
            Self::UnusableFieldParameter(name) => write!(
                f,
                "field notation requires a usable parameter with type head `{}`",
                name.to_display_string()
            ),
            Self::ExpectedFunction | Self::FunctionCoercionAbsent => {
                write!(f, "source application requires a function type")
            }
            Self::Tactic(error) => write!(f, "{error}"),
            Self::ArithmeticInconclusive(reason) => {
                write!(f, "omega did not complete: {:?}", reason.cause)
            }
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
            Self::Eliminator(reason) => write!(f, "failed to elaborate eliminator, {reason}"),
            Self::UnsupportedRecursor(name) => write!(
                f,
                "code generator does not support recursor `{}` yet, consider using 'match ... with' and/or structural recursion",
                name.to_display_string()
            ),
            Self::AuxiliaryNotCompiled(name) => write!(
                f,
                "Failed to find LCNF signature for {}",
                name.to_display_string()
            ),
            Self::NoncomputableDependency(name) => write!(
                f,
                "failed to compile definition, consider marking it as 'noncomputable' because it depends on '{}', which is 'noncomputable'",
                name.to_display_string()
            ),
            Self::NoncomputableJournal(error) => write!(f, "{error}"),
            Self::ExternJournal(error) => write!(f, "{error}"),
            Self::ImplementedByJournal(error) => write!(f, "{error}"),
            Self::InvalidInstanceBinder => write!(
                f,
                "instance binder must end in a registered class with inferable parameters"
            ),
            Self::InstanceRegistry(error) => write!(f, "{error}"),
            Self::SimpSet(error) => write!(f, "{error}"),
            Self::ProtectedJournal(error) => write!(f, "{error}"),
            Self::AuxiliaryJournal(error) => write!(f, "{error}"),
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
    traces: trace::TraceLog,
    goal_tags: std::collections::HashMap<MVarId, Name>,
    trace_local_names: std::collections::HashMap<FVarId, Name>,
    // Elimination fields no alternative named: the pin's inaccessible `n✝`, which
    // `rename_i`/`next`/`case` may name. Other anonymous locals are this engine's own.
    unnamed_fields: std::collections::HashSet<FVarId>,
    // Public proof declarations fix their signatures in the exported world
    // before their bodies may see private imports. Both environments remain
    // untrusted elaborator inputs; complete bodies require ordinary admission.
    private_proof_body: Option<(Environment, crate::instances::scoped::ActiveScopes)>,
    public_theorem_signature: Option<ConstantVal>,
    private_definition_body: bool,
    public_definition_header: Option<public_body::Header>,
    public_instance_signature: Option<instance_command::PublicHeader>,
    /// A frozen public instance header does not itself imply a private body:
    /// an explicitly exposed proof is checked in the public predecessor.
    private_instance_body: bool,
    // Completion may observe only a resolved declaration header. The value is
    // returned at that boundary; no body or declaration is constructed.
    declaration_header_probe: Option<bool>,
    source_scope: SourceScope,
    // Speculative tactics must observe rigid typing failures before choosing
    // their successful alternative. Outside speculation, ordinary final K1
    // admission retains its existing error boundary.
    attempt_depth: usize,
    // Opaque assertions remain parameter assumptions until their continuations
    // have been checked. Visibility comes from lctx, including after rollback.
    opaque_locals: std::collections::HashSet<FVarId>,
    // Unlike ordinary `have` values, local recursive definitions remain
    // opaque after leaving their lexical scope, until their enclosing
    // declaration has completed all source constraints.
    deferred_local_functions: Vec<local_functions::Deferred>,
    local_function_lifting: local_functions::lifting::Lifting,
    txn: ElabTxn,
    kernel: Budget,
    next: u64,
    equations: Vec<SourceEquation>,
    stalled_flush: Option<StalledFlush>,
    instance_goals: Vec<MVarId>,
    // Instance goals a `fun` or `∀` closed over before they were solved (`instances.rs`).
    bound_instances: Vec<instances::BoundInstance>,
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
    // A written match the pattern-matrix compiler lowered, by its last input's binder: the
    // inputs in order and the alternatives' patterns, typed as the pin types them once that
    // binder is in scope (`pattern_typing`).
    pattern_typing_checks: std::collections::HashMap<Name, (Vec<Name>, Vec<Syntax>)>,
    // The instance registry, re-read only when it can have changed: every
    // numeric literal, operator and coercion asks it.
    registry_cache: crate::instances::RegistryCache,
    // Imported `export` aliases, re-read only when the journal or the constants
    // change: every unresolved identifier consults them.
    alias_cache: crate::aliases::AliasCache,
    // Imported `protected` declarations, re-read on the same terms: an atomic
    // identifier never reaches one through a namespace or an alias.
    protected_cache: crate::protected_names::ProtectedCache,
    // Only explicitly generated/imported auxiliary declarations receive the
    // pin's eliminator elaboration; a declaration's suffix is insufficient.
    auxiliary_cache: crate::aux_recursors::AuxRecursorCache,
    // Registered simp rules' discrimination keys, shared by speculative snapshots.
    simp_key_cache: tactics::SimpKeyCache,
    // The declaration being elaborated, when it is `protected`.
    protected_declaration: Option<Name>,
    refinements: Vec<tactics::RefinementFrame>,
    // The declaration whose body is being elaborated (`definition_body`), so that field
    // notation naming it (`l.size` inside `T.size`) is recognized as a recursive reference
    // before the recursion context exists, as a direct `T.size l` already is.
    defining: Option<Name>,
    // Omitted result types of the recursive definitions being elaborated, innermost last
    // (`recursion::omitted_result_type`): each body is checked against its `body` hole in the
    // parameters' context, while its recursive reference uses `reference`, `?F x₁ … xₙ`.
    omitted_results: Vec<recursion::OmittedResult>,
    recursion: Option<recursion::Recursion>,
    well_founded: Option<recursion::WellFounded>,
    // Set only after a top-level well-founded lowering succeeds. The source
    // declaration result carries this status to post-admission metadata.
    well_founded_definition: bool,
    // Enabled only by the batch-only partial-definition entry point. A recursive
    // body needs its opaque logical interface AND its executable companion.
    partial: Option<partial::State>,
    // A supported compiler refusal suppressed by a noncomputable section.
    // Only the successful declaration result can carry it to post-admission metadata.
    noncomputable_definition: bool,
    // A local recursive helper suspends its parent's structural compiler.
    // Complete parent calls still lower against that parent's hypotheses
    // before the helper closes over them as an opaque value.
    enclosing_recursions: Vec<recursion::Recursion>,
    // Eliminator applications waiting for their expected type (`elabAsElim`'s
    // postponement), resumed after default instances run.
    postponed_eliminators: Vec<eliminator::PostponedEliminator>,
    // Coercions whose value was still open (`mkCoe`'s `.undef`), resumed by
    // instance synthesis and refused, as they were found, on its final pass.
    postponed_coercions: Vec<coercions::PostponedCoercion>,
    // Resumed argument failures are delayed source diagnostics, just like the
    // pin's synthetic metavariable errors. Tactic/recursion rollback restores
    // them; a selected declaration can never discard them or admit its holes.
    postponed_application_errors: Vec<NatDefinitionElabError>,
    // Argument queues borrow syntax from their term worklist. Nested overload
    // trials cannot own those queues, but must know that pending synthetic work
    // may still reveal a function type before establishing terminal failure.
    pending_source_arguments: bool,
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
            traces: trace::TraceLog::default(),
            goal_tags: std::collections::HashMap::new(),
            trace_local_names: std::collections::HashMap::new(),
            unnamed_fields: std::collections::HashSet::new(),
            private_proof_body: None,
            public_theorem_signature: None,
            private_definition_body: false,
            public_definition_header: None,
            public_instance_signature: None,
            private_instance_body: false,
            declaration_header_probe: None,
            source_scope: SourceScope::default(),
            attempt_depth: 0,
            opaque_locals: std::collections::HashSet::new(),
            deferred_local_functions: Vec::new(),
            local_function_lifting: local_functions::lifting::Lifting::default(),
            txn,
            kernel,
            next: 0,
            equations: Vec::new(),
            stalled_flush: None,
            instance_goals: Vec::new(),
            bound_instances: Vec::new(),
            synth_pending_depth: 0,
            overload_depth: 0,
            level_params: Vec::new(),
            explicit_levels: 0,
            infer_level_params: false,
            induction_specializations: Vec::new(),
            matrix_rows: std::collections::HashSet::new(),
            inaccessible_columns: std::collections::HashSet::new(),
            matrix_aliases: std::collections::HashMap::new(),
            pattern_typing_checks: std::collections::HashMap::new(),
            registry_cache: crate::instances::RegistryCache::default(),
            alias_cache: crate::aliases::AliasCache::default(),
            protected_cache: crate::protected_names::ProtectedCache::default(),
            auxiliary_cache: crate::aux_recursors::AuxRecursorCache::default(),
            simp_key_cache: tactics::SimpKeyCache::default(),
            protected_declaration: None,
            refinements: Vec::new(),
            defining: None,
            omitted_results: Vec::new(),
            recursion: None,
            well_founded: None,
            well_founded_definition: false,
            partial: None,
            noncomputable_definition: false,
            enclosing_recursions: Vec::new(),
            postponed_eliminators: Vec::new(),
            postponed_coercions: Vec::new(),
            postponed_application_errors: Vec::new(),
            pending_source_arguments: false,
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

    /// Hygienic binder. Macro scopes keep it out of source lookup (`h` does not
    /// see `h✝`) while `assumption` can still use the local. Anonymous or
    /// `_fln*` stems fall back to `a`, matching Lean's inaccessible-name printer.
    pub(super) fn fresh_inaccessible(
        &mut self,
        stem: &Name,
    ) -> Result<Name, NatDefinitionElabError> {
        self.tick()?;
        let id = self.next;
        self.next = self
            .next
            .checked_add(1)
            .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
        let erased = stem.erase_macro_scopes();
        let base = if erased.is_anonymous() || erased.to_display_string().starts_with("_fln") {
            Name::from_components(["a"])
        } else {
            erased
        };
        let hyg = base.append_core(&Name::from_components(["_@", "_internal", "_hyg"]));
        Ok(Name::num(hyg, id))
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
        if !self.bound_instances.is_empty() {
            self.settle_bound_instances()?;
        }
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
        if let Some(term) = self.partial_group_reference(name)? {
            return Ok(term);
        }
        let info = self
            .txn
            .env
            .find(name)
            .cloned()
            .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(name.clone())))?;
        self.note_resolved_recursor(name, &info)?;
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

    /// `sorry` at `type_`, as the pin elaborates it (`elabSorry`, `Lean/Elab/BuiltinNotation.lean`;
    /// `mkLabeledSorry type (synthetic := false) (unique := true)`, `Lean/Meta/Sorry.lean`):
    /// `sorryAx (Lean.Name → type_) false tag`. The tag makes every `sorry` a different term, so
    /// two of them are never definitionally equal. The pin's tag is the module, the source range
    /// and a fresh macro scope; this one is the source byte range plus a counter, so the term is
    /// the pin's up to that label. Without `Lean.Name` and `sorryAx` the pin aborts the command;
    /// here it is refused, naming the missing constant.
    fn labeled_sorry(
        &mut self,
        syntax: &Syntax,
        type_: Expr,
    ) -> Result<Typed, NatDefinitionElabError> {
        let name = |components: &[&str]| Name::from_components(components.iter().copied());
        for required in [
            name(&["sorryAx"]),
            name(&["Lean", "Name"]),
            name(&["Lean", "Name", "anonymous"]),
            name(&["Lean", "Name", "str"]),
            name(&["Lean", "Name", "num"]),
            name(&["Bool", "false"]),
        ] {
            if !self.txn.env.contains(&required) {
                return Err(failure(SourceInferenceError::UnknownConstant(required)));
            }
        }
        let name_type = Expr::const_(name(&["Lean", "Name"]), Vec::new());
        let labeled = Expr::forall_e(
            Name::str(Name::anonymous(), "tag"),
            name_type,
            type_.clone(),
            BinderInfo::Default,
        );
        let sort = match self.known_type(&labeled)? {
            Some(sort) => self.whnf(&sort)?,
            None => return Err(failure(SourceInferenceError::ExpectedType)),
        };
        let ExprNode::Sort { level } = sort.node() else {
            return Err(failure(SourceInferenceError::ExpectedType));
        };
        let nat = |value: u64| Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(value)));
        let info = match syntax {
            Syntax::Node { args, .. } => args
                .first()
                .map_or(fln_syntax::source::SourceInfo::None, Syntax::info),
            _ => syntax.info(),
        };
        let counter = self.next;
        self.fresh_name()?;
        let mut tag = Expr::app(
            Expr::app(
                Expr::const_(name(&["Lean", "Name", "str"]), Vec::new()),
                Expr::const_(name(&["Lean", "Name", "anonymous"]), Vec::new()),
            ),
            Expr::lit(Literal::Str("_sorry".to_owned())),
        );
        let positions = [
            info.pos(false).map(|pos| pos.0 as u64),
            info.end_pos(false).map(|pos| pos.0 as u64),
        ];
        for component in positions.into_iter().flatten().chain([counter]) {
            tag = Expr::app(
                Expr::app(
                    Expr::const_(name(&["Lean", "Name", "num"]), Vec::new()),
                    tag,
                ),
                nat(component),
            );
        }
        let value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(name(&["sorryAx"]), vec![level.clone()]),
                    labeled,
                ),
                Expr::const_(name(&["Bool", "false"]), Vec::new()),
            ),
            tag,
        );
        Ok(Typed { value, type_ })
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
            if kind == &parser_kind(&["Term", "quotedName"]) {
                return self.quoted_name(args);
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
            if kind == &parser_kind(&["Term", "sorry"]) {
                let [keyword] = args.as_slice() else {
                    return Err(failure(SourceInferenceError::Scope));
                };
                expect_atom(keyword, "sorry", "sorry")?;
                let type_ = match expected {
                    Some(type_) => type_.clone(),
                    None => {
                        let level = self.level()?;
                        self.hole(Expr::sort(level))?
                    }
                };
                return self.labeled_sorry(syntax, type_);
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
            // A template's name (macro-scoped) is a global once its scopes are erased; the
            // exact local scan above was its only local match (`resolve_source_candidates`).
            let hygienic = name.has_macro_scopes();
            let resolved = self
                .resolve_source_name(name)?
                .unwrap_or_else(|| name.erase_macro_scopes());
            // The fallback to the name as written must not reach a seed constant the pin
            // does not have: resolution already refused it (`source_unreachable`), and the
            // direct lookup below would otherwise find it anyway.
            if crate::seed::protected::source_unreachable(&resolved) {
                return Err(failure(SourceInferenceError::UnknownConstant(
                    resolved.clone(),
                )));
            }
            if !scope::is_root_qualified(name)
                && !hygienic
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
            if let Some(reference) = self
                .partial
                .as_ref()
                .and_then(|state| state.reference.as_ref())
                && &reference.name == name
            {
                return Ok(reference.term.clone());
            }
            if let Some(recursion) = &self.recursion
                && &recursion.name == name
            {
                return Ok(recursion.reference.clone());
            }
            if let Some(recursion) = &self.well_founded
                && &recursion.name == name
            {
                if recursion.proving {
                    return Err(failure(SourceInferenceError::Recursion(
                        recursion::RecursionError::RecursionInDecreasingProof,
                    )));
                }
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

    /// `` `a.b `` (`Term.quotedName`): the pin's `elabQuotedName` is `toExpr` of the literal's name
    /// (`Name.toExprAux`, vendored Lean/ToExpr.lean). That is `Lean.Name.mkStrN "a" "b"` for one to
    /// eight components, otherwise `Lean.Name.str` from `Lean.Name.anonymous`. A name literal's
    /// components are all strings (`String.toName`). `«…»` escapes a component. A double backtick
    /// (`doubleQuotedName`, which resolves a constant) is refused here.
    fn quoted_name(&mut self, args: &[Syntax]) -> Result<Typed, NatDefinitionElabError> {
        let [literal] = args else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let parts = expect_node(
            literal,
            &Name::str(Name::anonymous(), "name"),
            1,
            "name literal",
        )?;
        let Syntax::Atom { val, .. } = &parts[0] else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let Some(body) = val.strip_prefix('`').filter(|body| !body.starts_with('`')) else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let mut components = Vec::new();
        let mut current = String::new();
        let mut escaped = false;
        for character in body.chars() {
            match character {
                '«' if !escaped => escaped = true,
                '»' if escaped => escaped = false,
                '.' if !escaped => components.push(std::mem::take(&mut current)),
                _ => current.push(character),
            }
        }
        components.push(current);
        if escaped || components.iter().any(String::is_empty) {
            return Err(failure(SourceInferenceError::Scope));
        }
        let name = |label: &str| Name::from_components(["Lean", "Name", label]);
        let value = if components.len() <= 8 {
            let mut value = self
                .constant(&name(&format!("mkStr{}", components.len())))?
                .value;
            for component in components {
                value = Expr::app(value, Expr::lit(Literal::Str(component)));
            }
            value
        } else {
            let mut value = self.constant(&name("anonymous"))?.value;
            let str_ = self.constant(&name("str"))?.value;
            for component in components {
                value = Expr::app(
                    Expr::app(str_.clone(), value),
                    Expr::lit(Literal::Str(component)),
                );
            }
            value
        };
        Ok(Typed {
            value,
            type_: Expr::const_(Name::from_components(["Lean", "Name"]), Vec::new()),
        })
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
        // The unifier instantiates the equations itself, so a goal solved under a closed binder
        // is put back into place before it reads them.
        if !self.bound_instances.is_empty() {
            self.settle_bound_instances()?;
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
                // Field lookup consumes leading value defaults even when
                // its receiver was written with `@` (pin `consumeImplicits`).
                if matches!(insertion, ImplicitInsertion::FieldReceiver)
                    && let Some(argument) = optional::default_value(binder_type)
                {
                    let argument = argument.clone();
                    term.type_ = self.substitute(body, &argument)?;
                    term.value = Expr::app(term.value, argument);
                    continue;
                }
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
        if self.has_optional_parameter(&term.type_)? {
            return self.finish_optional_application(term, expected);
        }
        self.finish_application_implicits(term, expected)
    }

    fn finish_application_implicits(
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
            // The pin elaborates with first-order approximation on (`foApprox`): a result
            // `?m ?σ` that is no pattern meets `StateM Nat Nat` as `?m := StateM Nat`, `?σ := Nat`
            // (`processAssignmentFOApprox`), so `get`'s instance goal is known. The ordinary
            // unifier suspends such an equation; the hint publishes only a whole solution.
            if self.flexible_non_pattern(&term.type_)? {
                self.first_order_result_hint(&term.type_, expected)?;
            }
            term = self.coerce_expected(term, expected)?;
        }
        self.resolve_instances(false)?;
        term.value = self.lower_matrix_call(&term.value)?;
        term.value = self.lower_well_founded_call(&term.value)?;
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
        // An application whose argument the pin postpones and then refuses (`pattern_typing`,
        // R1 of franken_lean-z8j.1.6.3).
        if let Some(expected) = &expected {
            self.check_application_typing(syntax, expected)?;
        }
        let syntax = self.lower_pattern_matrices(syntax)?;
        self.term_prepared(&syntax, expected)
    }

    fn term_prepared(
        &mut self,
        syntax: &Syntax,
        expected: Option<Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        // Scoped term and tactic options are dynamically restored even when a
        // failed elaboration leaves its worklist before the closing frame.
        // Speculative retries restore their own complete Context checkpoints.
        let options = self.txn.options.clone();
        let pending_source_arguments = self.pending_source_arguments;
        let result = self.term_prepared_scoped(syntax, expected, None);
        self.txn.options = options;
        self.pending_source_arguments = pending_source_arguments;
        result
    }

    fn run_decreasing_proof<'a>(
        &mut self,
        syntax: &'a Syntax,
        proof: tactics::ProofState<'a>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let options = self.txn.options.clone();
        let pending_source_arguments = self.pending_source_arguments;
        let result = self.term_prepared_scoped(syntax, None, Some(proof));
        self.txn.options = options;
        self.pending_source_arguments = pending_source_arguments;
        result
    }

    fn term_prepared_scoped<'a>(
        &mut self,
        syntax: &'a Syntax,
        expected: Option<Expr>,
        initial_proof: Option<tactics::ProofState<'a>>,
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
            RestoreOptions(KVMap),
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
            NomatchDiscriminant(Arguments<'a>, Vec<Typed>, Option<Expr>),
            MatchNext(matching::MatchBuild<'a>),
            MatchBranch(matching::MatchBuild<'a>, matching::BranchBinders),
            Ascription(&'a Syntax, Option<Expr>, bool),
            AscribedValue(Expr, Option<Expr>, bool),
            Projection(Name, &'a [Syntax], Option<Expr>, bool, bool),
            RecordType(record_terms::RecordParts<'a>, Option<Expr>),
            RecordPrepare(record_terms::RecordParts<'a>, Option<Expr>, Vec<Typed>),
            RecordSource(record_terms::RecordParts<'a>, Option<Expr>, Vec<Typed>),
            RecordNext(record_terms::RecordBuild<'a>),
            RecordField(record_terms::RecordBuild<'a>, record_terms::RecordTarget),
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
            ApplyNext(Typed, Arguments<'a>, Option<Expr>, bool),
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
                tactics::LocalBinding,
                &'a Syntax,
            ),
            ProofBindingValue(
                tactics::ProofState<'a>,
                tactics::ProofGoal,
                tactics::LocalBinding,
                Option<Expr>,
            ),
            ProofSpecialize(tactics::ProofState<'a>, tactics::ProofGoal),
            ProofTerm(tactics::ProofState<'a>, tactics::ProofGoal, Option<usize>),
            RefineTerm(tactics::ProofState<'a>, tactics::ProofGoal, usize),
        }
        let mut tasks = vec![match initial_proof {
            Some(proof) => Task::Proof(proof),
            None => Task::Visit(syntax, expected, true),
        }];
        let mut values: Vec<Typed> = Vec::new();
        enum Attempt<'a> {
            Proof(tactics::backtrack::Checkpoint<'a>, postponed::Queue<'a>),
            LocalFunction(Box<local_functions::Checkpoint<'a>>, postponed::Queue<'a>),
            Argument(Box<postponed::Checkpoint<'a>>),
        }
        let mut attempts: Vec<Attempt<'_>> = Vec::new();
        let inherited_pending_arguments = self.pending_source_arguments;
        let mut pending = postponed::Queue::default();
        loop {
            let mut blocked_application = None;
            let mut containing_argument = None;
            let mut blocked_initial_application = None;
            let result = (|| {
                loop {
                    self.pending_source_arguments =
                        inherited_pending_arguments || !pending.is_empty();
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
                                        blocked_application = Some(blocker.id);
                                        containing_argument = Some(index);
                                        return Err(blocker.problem);
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
                        checkpoint.enter_options(self);
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
                        Task::RestoreOptions(options) => self.txn.options = options,
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
                            checkpoint.finish_options(self);
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
                                if kind == &parser_kind(&["Term", "set_option"]) {
                                    let (body, options) = self.enter_source_options(args)?;
                                    tasks.push(Task::RestoreOptions(options));
                                    tasks.push(Task::Visit(body, expected, finish));
                                    continue;
                                }
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
                                // A reassignment's type: the type of the variable it replaces
                                // (`do_notation::mutation`).
                                if kind == &parser_kind(&["Term", "nativeDoTypeOf"]) {
                                    let [Syntax::Ident { val, .. }] = args.as_slice() else {
                                        return Err(failure(SourceInferenceError::Scope));
                                    };
                                    let local = self
                                        .txn
                                        .lctx
                                        .find_by_user_name(val)
                                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                                    let value = self.instantiate(&local.type_.clone())?;
                                    let type_ = self.known_type(&value)?.ok_or_else(|| {
                                        failure(SourceInferenceError::ExpectedType)
                                    })?;
                                    let term = Typed { value, type_ };
                                    values.push(if finish {
                                        self.finish_term(term, expected.as_ref())?
                                    } else {
                                        term
                                    });
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
                                if kind == &parser_kind(&["Term", "nofun"]) {
                                    tasks.push(Task::Proof(
                                        self.start_empty_function(syntax, expected)?,
                                    ));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "nomatch"]) {
                                    let items = self.nomatch_discriminants(syntax)?;
                                    let arguments = Arguments::Separated(items, &[","]);
                                    let (first, remaining) =
                                        arguments.split_first().expect("nonempty discriminants");
                                    tasks.push(Task::NomatchDiscriminant(
                                        remaining,
                                        Vec::new(),
                                        expected,
                                    ));
                                    tasks.push(Task::Visit(first, None, true));
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
                                        } else if let Some(omitted) = build.omitted.clone() {
                                            // The omitted result's hole stands in for the
                                            // annotation the recursive path expects.
                                            values.push(Typed {
                                                value: omitted.body,
                                                type_: omitted.sort,
                                            });
                                            tasks.push(Task::LocalFunctionAnnotation(build));
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
                                // Explicit operator elaborators resolve the authored
                                // identifier, including local functions. Builtin notation
                                // whose function is absent keeps the seed bridge below.
                                let notation = operators::pin_notation(kind);
                                if operators::explicit_operator(kind).is_some()
                                    || match notation {
                                        Some(notation) => self.pin_notation_available(notation)?,
                                        None => false,
                                    }
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
                                        Ok(function) => function,
                                        Err(problem) => {
                                            blocked_application = self.notation_type_unavailable(
                                                &problem,
                                                expected.as_ref(),
                                            )?;
                                            return Err(problem);
                                        }
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
                                    blocked_application =
                                        self.notation_type_unavailable(&error, expected.as_ref())?;
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
                                } else if matches!(syntax, Syntax::Ident { .. })
                                    || syntax.kind()
                                        == Some(&parser_kind(&["Term", "explicitUniv"]))
                                    || syntax.kind() == Some(&parser_kind(&["Term", "dotIdent"]))
                                {
                                    self.finish_optional_term(term, expected.as_ref())?
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
                                        if explicit {
                                            self.finish_explicit_term(term, expected.as_ref())?
                                        } else {
                                            self.finish_optional_term(term, expected.as_ref())?
                                        }
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
                        Task::NomatchDiscriminant(remaining, mut terms, expected) => {
                            terms.push(values.pop().expect("empty match discriminant visit"));
                            if let Some((next, rest)) = remaining.split_first() {
                                tasks.push(Task::NomatchDiscriminant(rest, terms, expected));
                                tasks.push(Task::Visit(next, None, true));
                            } else {
                                tasks.push(Task::Proof(self.start_empty_match(terms, expected)?));
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
                                self.show_result_hint(&type_.value, expected)?;
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
                                let record_expected = expected.clone();
                                match self.start_record(parts, expected, sources) {
                                    Ok(record) => tasks.push(Task::RecordNext(record)),
                                    Err(problem) => {
                                        blocked_application = self.notation_type_unavailable(
                                            &problem,
                                            record_expected.as_ref(),
                                        )?;
                                        return Err(problem);
                                    }
                                }
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
                                target,
                            } => {
                                tasks.push(Task::RecordField(state, target));
                                tasks.push(Task::Visit(syntax, Some(domain), true));
                            }
                            record_terms::RecordStep::Copy { value, target } => {
                                self.accept_record_field(&mut state, &target, value)?;
                                tasks.push(Task::RecordNext(state));
                            }
                            record_terms::RecordStep::Complete(term) => values.push(term),
                            record_terms::RecordStep::Continue => {
                                tasks.push(Task::RecordNext(state))
                            }
                        },
                        Task::RecordField(mut state, target) => {
                            let value = values.pop().expect("record field visit");
                            self.accept_record_field(&mut state, &target, value)?;
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
                                if checkpoint.inverted() {
                                    // `fail_if_success t` and `t` succeeded: undo it and fail, to
                                    // the enclosing attempt (whose own checkpoint restores it).
                                    tasks.truncate(checkpoint.tasks);
                                    values.truncate(checkpoint.values);
                                    checkpoint.restore(self);
                                    return Err(failure(SourceInferenceError::Tactic(
                                        tactics::TacticError::FailIfSuccessSucceeded,
                                    )));
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
                                binding,
                                annotation,
                                value,
                            } => {
                                self.txn.lctx = goal.lctx.clone();
                                if let Some(annotation) = annotation {
                                    tasks.push(Task::ProofBindingType(proof, goal, binding, value));
                                    tasks.push(Task::Visit(
                                        annotation,
                                        Some(self.type_expected()?),
                                        true,
                                    ));
                                } else {
                                    tasks.push(Task::ProofBindingValue(proof, goal, binding, None));
                                    tasks.push(Task::Visit(value, None, true));
                                }
                            }
                            tactics::ProofAction::Specialize { goal, term } => {
                                self.txn.lctx = goal.lctx.clone();
                                tasks.push(Task::ProofSpecialize(proof, goal));
                                tasks.push(Task::Visit(term, None, true));
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
                                // `exact e` elaborates `e` against the goal, as a definition
                                // body against its type (`pattern_typing`, R1).
                                if let Some(target) = &expected {
                                    self.check_application_typing(syntax, target)?;
                                }
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
                        Task::ProofBindingType(proof, goal, binding, value) => {
                            let annotation = values.pop().expect("local proof annotation visit");
                            self.sort_level(&annotation)?;
                            tasks.push(Task::ProofBindingValue(
                                proof,
                                goal,
                                binding,
                                Some(annotation.value.clone()),
                            ));
                            tasks.push(Task::Visit(value, Some(annotation.value), true));
                        }
                        Task::ProofBindingValue(mut proof, goal, binding, annotation) => {
                            let mut value = values.pop().expect("local proof value visit");
                            if let Some(annotation) = annotation {
                                value.type_ = annotation;
                            }
                            self.bind_proof_value(&mut proof, goal, binding, value)?;
                            tasks.push(Task::Proof(proof));
                        }
                        Task::ProofSpecialize(mut proof, goal) => {
                            let term = values.pop().expect("specialized term visit");
                            self.specialize_proof_term(&mut proof, goal, term)?;
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
                                    let function = match self
                                        .dotted_identifier(args, expected.as_ref())
                                    {
                                        Ok(function) => function,
                                        Err(problem) => {
                                            blocked_application = self.notation_type_unavailable(
                                                &problem,
                                                expected.as_ref(),
                                            )?;
                                            return Err(problem);
                                        }
                                    };
                                    values.push(function);
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
                            if state.initial() {
                                if state.has_arguments()
                                    && self
                                        .application_type_unavailable(state.function_type())?
                                        .is_some()
                                {
                                    self.resolve_instances(false)?;
                                    if let Some(blocker) =
                                        self.application_type_unavailable(state.function_type())?
                                    {
                                        blocked_application = Some(blocker);
                                        blocked_initial_application = Some(Task::NamedNext(state));
                                        return Err(failure(
                                            SourceInferenceError::ExpectedFunction,
                                        ));
                                    }
                                }
                                state.start();
                            }
                            let next = self.next_named_argument(&mut state);
                            if matches!(
                                &next,
                                Err(NatDefinitionElabError::Inference(
                                    SourceInferenceError::ExpectedFunction
                                        | SourceInferenceError::InvalidNamedArgument(_)
                                ))
                            ) {
                                if self.function_coercion_is_absent(state.function_type())? {
                                    return Err(failure(
                                        SourceInferenceError::FunctionCoercionAbsent,
                                    ));
                                }
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
                            if !arguments.is_empty()
                                && self
                                    .application_type_unavailable(&function.type_)?
                                    .is_some()
                            {
                                // Known telescopes reach ordinary synthesis in
                                // coerce_function. Only an unavailable initial
                                // callee needs an earlier round here.
                                self.resolve_instances(false)?;
                                if let Some(blocker) =
                                    self.application_type_unavailable(&function.type_)?
                                {
                                    // `elabAppArgs` postpones before consuming
                                    // arguments. Keep this continuation in its
                                    // lexical context; defaults can resume it
                                    // when no containing argument owns the type.
                                    blocked_application = Some(blocker);
                                    blocked_initial_application =
                                        Some(Task::Apply(function, arguments, expected, explicit));
                                    return Err(failure(SourceInferenceError::ExpectedFunction));
                                }
                            }
                            tasks.push(Task::ApplyNext(function, arguments, expected, explicit));
                        }
                        Task::ApplyNext(function, arguments, expected, explicit) => {
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
                                    if self.function_coercion_is_absent(&callee_type)? {
                                        return Err(failure(
                                            SourceInferenceError::FunctionCoercionAbsent,
                                        ));
                                    }
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
                                let domain = self.projection_domain(binder_type.clone())?;
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
                            tasks.push(Task::ApplyNext(
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
                            // The pin's `elabArrow` (vendored Lean/Elab/Binders.lean:299-303)
                            // names the binder `a` under the reserved macro scope:
                            // `a._@._internal._hyg.0`. It shows when an index is promoted to a
                            // parameter (`@F.rec : {a : Nat} → …`).
                            let term = Typed {
                                value: Expr::forall_e(
                                    Name::num(
                                        Name::from_components(["a", "_@", "_internal", "_hyg"]),
                                        0,
                                    ),
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
                            if let Some(omitted) = &build.omitted {
                                self.settle_omitted_result(omitted)?;
                            }
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
                            let value = if build.binding.recursive {
                                self.defer_local_function(value, build.lift_name)?
                            } else {
                                value
                            };
                            values.push(value);
                            // The pin elaborates the rest of the enclosing definition with a
                            // `let rec` (and so a `where` declaration) as a local without a value:
                            // it becomes the auxiliary `f.g` only once `f` is complete
                            // (`elabLetRec`, Lean/Elab/LetRec.lean:140-147: `withAuxLocalDecls`,
                            // then `registerLetRecsToLift`). Inside `f` it cannot unfold, as a
                            // `have` cannot; the admitted term still binds the value.
                            tasks.push(Task::LetValue(
                                build.binding.name,
                                None,
                                build.binding.body,
                                build.expected,
                                build.binding.opaque || build.binding.recursive,
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
                            // Every input of a lowered written match is in scope now.
                            if let Some((inputs, alternatives)) =
                                self.pattern_typing_checks.remove(&name)
                            {
                                let discriminants = inputs
                                    .iter()
                                    .map(|input| {
                                        self.txn.lctx.find_by_user_name(input).and_then(|decl| {
                                            Some((decl.value.clone()?, decl.type_.clone()))
                                        })
                                    })
                                    .collect::<Option<Vec<_>>>();
                                if let Some(discriminants) = discriminants {
                                    self.check_pattern_typing(&discriminants, &alternatives)?;
                                }
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
                    if let Some(blocker) = &blocked_application
                        && containing_argument.is_none()
                    {
                        let blockers = [postponed::Blocker {
                            id: blocker.clone(),
                            problem: problem.clone(),
                        }];
                        for (index, attempt) in attempts.iter().enumerate().rev() {
                            self.tick()?;
                            if let Attempt::Argument(checkpoint) = attempt
                                && let Some(owner) = checkpoint.owned_blocker(self, &blockers)?
                            {
                                blocked_application = Some(owner.id);
                                containing_argument = Some(index);
                                break;
                            }
                        }
                        if containing_argument.is_none() {
                            if let Some(application) = blocked_initial_application
                                && self.resolve_next_default_instance()?
                            {
                                // The pin retries postponed initial applications
                                // between default-instance rounds. Do not close
                                // their locals, drop pending argument work, or
                                // refund the unsuccessful attempt's budget.
                                tasks.push(application);
                                continue;
                            }
                            return Err(problem);
                        }
                    }
                    if blocked_application.is_none() && !tactics::backtrack::recoverable(&problem) {
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
                                    && let Some(value) = checkpoint.postpone(
                                        self,
                                        &mut pending,
                                        blocker,
                                        &problem,
                                    )?
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
        let term = self.finish_open_universes(term)?;
        self.require_resolved(&[term.value.clone(), term.type_.clone()])?;
        Ok(term)
    }

    /// `finish`, but a universe hole may remain for the enclosing declaration to generalize, as
    /// a record field's may under an auto-bound implicit (`α : Sort ?u`). A term hole may not.
    fn finish_open_universes(&mut self, term: Typed) -> Result<Typed, NatDefinitionElabError> {
        if let Some(error) = self.postponed_application_errors.first() {
            return Err(error.clone());
        }
        self.resolve_instances(true)?;
        self.resume_postponed_eliminators(true)?;
        self.flush(true)?;
        let value = self.instantiate(&term.value)?;
        let type_ = self.instantiate(&term.type_)?;
        self.require_resolved_terms(&[value.clone(), type_.clone()])?;
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
            let expanded = self.expand_optional_binder_node(syntax.clone(), false)?;
            let syntax = &expanded;
            let Syntax::Node { kind, .. } = syntax else {
                return Err(failure(SourceInferenceError::Scope));
            };
            if kind == &parser_kind(&["Term", "instBinder"]) {
                let parts = expect_node(syntax, kind, 4, "instance binder")?;
                expect_atom(&parts[0], "[", "instance binder opener")?;
                expect_atom(&parts[3], "]", "instance binder closer")?;
                let optional = expect_null_args(&parts[1], "optional instance name")?;
                let user_name = match optional {
                    [] => self.fresh_inaccessible(&Name::from_components(["inst"]))?,
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
            // `toBinderViews` gives every name its own copy of the type, elaborated after the
            // preceding names are bound: `(A B : Type _)` has two universe holes, and `{α β}`
            // two type holes, not one shared between them.
            let domain_of = |context: &mut Self| match type_parts {
                [colon, type_syntax] => {
                    expect_atom(colon, ":", "binder type ascription")?;
                    context.type_term(type_syntax)
                }
                // `{α}`: the pin elaborates an omitted binder type as a hole
                // (`Lean/Elab/Binders.lean`, `mkHole`), which unification must fill.
                [] => {
                    let hole = Syntax::node(
                        parser_kind(&["Term", "hole"]),
                        vec![Syntax::atom(fln_syntax::source::SourceInfo::None, "_")],
                    );
                    context.type_term(&hole)
                }
                _ => Err(failure(SourceInferenceError::ExpectedType)),
            };
            for name in names {
                let domain = domain_of(self)?;
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
                self.txn.lctx.add_param(id.clone(), name, domain, style);
                parameters.push(self.txn.lctx.find(&id).expect("inserted parameter").clone());
            }
        }
        Ok(parameters)
    }
}

/// The two checked predecessor views used by a module's public declaration. The
/// signature sees `public`; a hidden implementation sees `private`. Scope histories are
/// supplied separately because each anchors a different instance journal.
#[derive(Clone, Copy)]
pub struct TheoremWorlds<'a> {
    pub public: &'a Environment,
    pub private: &'a Environment,
    pub public_scope: &'a SourceScope,
    pub private_scope: &'a SourceScope,
}

/// Whether the parsed command is an ordinary named theorem declaration.
pub fn is_theorem(syntax: &Syntax) -> bool {
    matches!(syntax, Syntax::Node { kind, args, .. }
        if kind == &parser_kind(&["Command", "declaration"])
            && args.len() == 2
            && args[1].kind() == Some(&parser_kind(&["Command", "theorem"])))
}

/// Whether the parsed command is a named or anonymous instance declaration.
pub fn is_instance(syntax: &Syntax) -> bool {
    matches!(syntax, Syntax::Node { kind, args, .. }
        if kind == &parser_kind(&["Command", "declaration"])
            && args.len() == 2
            && args[1].kind() == Some(&parser_kind(&["Command", "instance"])))
}

/// An untrusted instance candidate and the header-selected body visibility.
/// These flags grant no export authority: the module driver checks the actual
/// theorem or definition before constructing and admitting its interface.
#[derive(Debug)]
pub struct PublicInstance {
    pub declaration: Declaration,
    /// Independently checked local helpers, kept in the selected body world.
    pub local_functions: Vec<Declaration>,
    pub proof_valued: bool,
    pub hidden_body: bool,
    pub noncomputable: bool,
}

/// Elaborate a public instance once, choosing its body world from the resolved
/// header. Automatically exposed data and explicitly exposed proofs stay public;
/// `no_expose` selects the private body world for either kind.
/// Proof instances become theorems with frozen public types, as in the pin's
/// `addNonRecAux`; their body exposure does not change their declaration kind.
pub fn elaborate_public_instance(
    syntax: &Syntax,
    worlds: &TheoremWorlds<'_>,
    kernel: Budget,
) -> Result<PublicInstance, NatDefinitionElabError> {
    let mut context = Context::public_instance(syntax, worlds, kernel)?;
    let declaration = definition_in_context(syntax, &mut context)?;
    let local_functions = context.lift_local_functions(&declaration)?;
    Ok(PublicInstance {
        local_functions,
        proof_valued: matches!(&declaration, Declaration::Thm(_)),
        hidden_body: context.private_instance_body,
        noncomputable: context.noncomputable_definition,
        declaration,
    })
}

/// Observe whether a complete public instance header selects a private
/// body. The syntax may contain a placeholder body: it is never elaborated.
/// This bounded query grants no declaration or export authority.
pub fn public_instance_header_is_hidden(
    syntax: &Syntax,
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<bool, NatDefinitionElabError> {
    let scope = scope.for_declaration(syntax)?;
    if !is_instance(syntax) || !scope.exports_declaration() {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "a public instance header in a module file",
        });
    }
    probe_header_visibility(syntax, environment, kernel, &scope)
}

fn probe_header_visibility(
    syntax: &Syntax,
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<bool, NatDefinitionElabError> {
    let mut context = Context::scoped(environment, kernel, scope);
    // There is no final candidate admission after a header-only query. Rigid
    // typing failures must be observed before revealing a private body context.
    context.attempt_depth = 1;
    context.declaration_header_probe = Some(false);
    match definition_in_context(syntax, &mut context) {
        Err(NatDefinitionElabError::Inference(SourceInferenceError::ObservationComplete)) => {
            context
                .declaration_header_probe
                .ok_or_else(|| failure(SourceInferenceError::Scope))
        }
        Err(error) => Err(error),
        Ok(_) => Err(failure(SourceInferenceError::Scope)),
    }
}

/// Elaborate a public theorem's header and proof in their respective worlds.
/// This produces only untrusted candidates, never an exported assumption or
/// an environment successor. The proof and every named local helper must pass
/// separate ordinary admissions in the private world before publication.
pub fn elaborate_public_theorem(
    syntax: &Syntax,
    worlds: &TheoremWorlds<'_>,
    kernel: Budget,
) -> Result<ElaboratedDeclaration, NatDefinitionElabError> {
    let mut context = Context::public_theorem(syntax, worlds, kernel)?;
    let declaration = definition_in_context(syntax, &mut context)?;
    let local_functions = context.lift_local_functions(&declaration)?;
    Ok(ElaboratedDeclaration {
        declaration,
        local_functions,
        irreducible: false,
        noncomputable: context.noncomputable_definition,
    })
}

impl Context {
    fn public_theorem(
        syntax: &Syntax,
        worlds: &TheoremWorlds<'_>,
        kernel: Budget,
    ) -> Result<Self, NatDefinitionElabError> {
        let scope = worlds.public_scope.for_declaration(syntax)?;
        if !is_theorem(syntax) || !scope.exports_declaration() {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "a public theorem in a module file",
            });
        }
        let mut context = Self::scoped(worlds.public, kernel, &scope);
        context.private_proof_body = Some((
            worlds.private.clone(),
            worlds.private_scope.instance_scopes.clone(),
        ));
        Ok(context)
    }

    fn public_instance(
        syntax: &Syntax,
        worlds: &TheoremWorlds<'_>,
        kernel: Budget,
    ) -> Result<Self, NatDefinitionElabError> {
        let scope = worlds.public_scope.for_declaration(syntax)?;
        if !is_instance(syntax) || !scope.exports_declaration() {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "a public instance in a module file",
            });
        }
        let mut context = Self::scoped(worlds.public, kernel, &scope);
        context.private_proof_body = Some((
            worlds.private.clone(),
            worlds.private_scope.instance_scopes.clone(),
        ));
        Ok(context)
    }

    /// Close and retain the exact header before changing either name resolution
    /// or instance search. Header universes become rigid parameters here, as in
    /// the pin's `levelMVarToParamHeaders` / theorem signature publication.
    fn enter_public_theorem_proof(
        &mut self,
        name: &Name,
        parameters: &[LocalDecl],
        section_parameters: &[LocalDecl],
        expected: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        let signature = self.with_closed_local_function_header(|context| {
            let mut roots: Vec<_> = section_parameters
                .iter()
                .chain(parameters)
                .map(|local| local.type_.clone())
                .collect();
            roots.push(expected.clone());
            context.generalize_declaration_universes(&roots)?;
            let mut type_ = context.instantiate(expected)?;
            for local in section_parameters.iter().chain(parameters).rev() {
                context.tick()?;
                type_ = Expr::forall_e(
                    local.user_name.clone(),
                    context.instantiate(&local.type_)?,
                    type_
                        .abstract_fvar(&local.id, 0)
                        .map_err(|_| failure(SourceInferenceError::Scope))?,
                    local.binder_info,
                );
            }
            context.require_resolved(std::slice::from_ref(&type_))?;
            if type_.has_fvar() || type_.has_loose_bvars() {
                return Err(failure(SourceInferenceError::Scope));
            }
            let level_params = context.declaration_levels(std::slice::from_ref(&type_))?;
            Ok(ConstantVal {
                name: name.clone(),
                level_params,
                type_,
            })
        })?;
        self.public_theorem_signature = Some(signature);
        self.enter_private_proof()
    }

    fn enter_private_proof(&mut self) -> Result<(), NatDefinitionElabError> {
        let (environment, instance_scopes) =
            self.private_proof_body
                .take()
                .ok_or(NatDefinitionElabError::UnexpectedSyntax {
                    expected: "separate public and private predecessors for a hidden proof body",
                })?;
        self.txn.env = environment;
        self.source_scope.instance_scopes = instance_scopes;
        self.registry_cache = crate::instances::RegistryCache::default();
        self.alias_cache = crate::aliases::AliasCache::default();
        self.protected_cache = crate::protected_names::ProtectedCache::default();
        self.auxiliary_cache = crate::aux_recursors::AuxRecursorCache::default();
        Ok(())
    }
}

pub(super) fn definition(
    syntax: &Syntax,
    environment: &Environment,
    kernel: Budget,
) -> Result<Declaration, NatDefinitionElabError> {
    definition_scoped(syntax, environment, kernel, &SourceScope::default())
}

/// An untrusted source candidate and the effects selected by its successful
/// elaboration. Effects are installed only after ordinary declaration admission;
/// neither this value nor its flags grant publication authority.
#[derive(Debug, Clone, PartialEq)]
pub struct ElaboratedDeclaration {
    pub declaration: Declaration,
    /// Closed local recursive helpers. They grant no authority: callers must
    /// admit every helper and the owner atomically through both checkers.
    pub local_functions: Vec<Declaration>,
    /// The definition actually used well-founded lowering. A source spelling or
    /// a body mentioning `WellFounded.Nat.fix` does not set this effect.
    pub irreducible: bool,
    /// An actual supported code-generation refusal suppressed by the enclosing
    /// noncomputable section, not merely the presence of that section.
    pub noncomputable: bool,
}

fn definition_scoped(
    syntax: &Syntax,
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<Declaration, NatDefinitionElabError> {
    definition_scoped_with_effects(syntax, environment, kernel, scope)
        .map(|elaborated| elaborated.declaration)
}

fn definition_scoped_with_effects(
    syntax: &Syntax,
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<ElaboratedDeclaration, NatDefinitionElabError> {
    let scope = scope.for_declaration(syntax)?;
    let mut context = Context::scoped(environment, kernel, &scope);
    let declaration = definition_in_context(syntax, &mut context)?;
    let local_functions = context.lift_local_functions(&declaration)?;
    Ok(ElaboratedDeclaration {
        declaration,
        local_functions,
        irreducible: context.well_founded_definition,
        noncomputable: context.noncomputable_definition,
    })
}

/// Whether the pin would auto-bind `name` in a header: `autoImplicit` is on (its default) and
/// `name` is atomic, without macro scopes, and a strict name, one character followed only by
/// digits, subscripts, `_` or `'` (`checkValidAutoBoundImplicitName`,
/// Lean/Elab/AutoBound.lean:31-63; `isSubScriptAlnum`, Init/Meta/Defs.lean:111-118). The pin's
/// default `relaxedAutoImplicit` also binds any other atomic name; this engine does not, because
/// its seed lacks names Init has (`IO`, `Int`, `Unit`), and binding those would make a variable
/// of a constant. Such a name stays an unknown identifier: a refusal where the pin may accept.
fn auto_bound_name(name: &Name, options: &KVMap) -> bool {
    if !options.get_bool(&Name::from_components(["autoImplicit"]), true)
        || name.has_macro_scopes()
        || !name.parent().is_anonymous()
    {
        return false;
    }
    let LeafView::Str(spelled) = name.leaf_view() else {
        return false;
    };
    let subscript = |c: char| {
        let c = u32::from(c);
        (0x2080..=0x2089).contains(&c)
            || (0x2090..=0x209c).contains(&c)
            || (0x1d62..=0x1d6a).contains(&c)
            || c == 0x2c7c
    };
    let mut chars = spelled.chars();
    chars.next().is_some()
        && chars.all(|c| c.is_ascii_digit() || subscript(c) || c == '_' || c == '\'')
}

impl Context {
    /// The pin's `withAutoBoundImplicit` (Lean/Elab/Term/TermElabM.lean:1932-1955) around a header's
    /// binders and type: an unknown name `auto_bound_name` admits, other than `own_names`, restores
    /// the state from before the attempt, becomes an implicit local of a fresh type, and `elaborate`
    /// runs again. Returns those locals, in order (they precede whatever `elaborate` binds), and its
    /// result. The pin's `addAutoBoundImplicits` refusal of an auto whose type mentions a written
    /// binder is `refuse_auto_bound_dependencies`.
    pub(super) fn with_auto_bound_implicits<T>(
        &mut self,
        own_names: &[Name],
        mut elaborate: impl FnMut(&mut Self) -> Result<T, NatDefinitionElabError>,
    ) -> Result<(Vec<LocalDecl>, T), NatDefinitionElabError> {
        let mut state = self.clone();
        let mut autos: Vec<LocalDecl> = Vec::new();
        loop {
            match elaborate(self) {
                Err(NatDefinitionElabError::Inference(SourceInferenceError::UnknownConstant(
                    found,
                ))) if !own_names.contains(&found)
                    && !autos.iter().any(|auto| auto.user_name == found)
                    && auto_bound_name(&found, &self.txn.options) =>
                {
                    let spent = self.txn.budget.heartbeats_consumed;
                    *self = state;
                    self.txn.budget.heartbeats_consumed = spent;
                    self.tick()?;
                    let sort = self.type_expected()?;
                    let type_ = self.hole(sort)?;
                    let id = FVarId(self.fresh_name()?);
                    self.txn
                        .lctx
                        .add_param(id.clone(), found, type_, BinderInfo::Implicit);
                    autos.push(self.txn.lctx.find(&id).expect("auto-bound local").clone());
                    state = self.clone();
                }
                other => return other.map(|value| (autos, value)),
            }
        }
    }

    /// `addAutoBoundImplicits` (Lean/Elab/Term/TermElabM.lean:2044-2058): an auto-bound implicit
    /// precedes the written binders, so its type may not mention one.
    pub(super) fn refuse_auto_bound_dependencies(
        &mut self,
        autos: &[LocalDecl],
        written: &[LocalDecl],
    ) -> Result<(), NatDefinitionElabError> {
        for auto in autos {
            let type_ = self.instantiate(&auto.type_)?;
            for binder in written {
                self.tick()?;
                let abstracted = type_
                    .abstract_fvar(&binder.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                if abstracted.has_loose_bvar(0) {
                    return Err(failure(SourceInferenceError::AutoBoundDependsOnExplicit {
                        auto: auto.user_name.clone(),
                        explicit: binder.user_name.clone(),
                    }));
                }
            }
        }
        Ok(())
    }
}

/// A declaration's own short name, which its header never auto-binds (MutualDef.lean:213).
pub(super) fn own_short_name(name: &Name) -> Vec<Name> {
    match name.leaf_view() {
        LeafView::Str(spelled) => vec![Name::from_components([spelled])],
        _ => Vec::new(),
    }
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
    let expanded = context.expand_match_alternatives(syntax)?;
    let syntax = expanded.as_ref();
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
    let mut is_noncomputable = false;
    let mut is_unsafe = false;
    for (index, modifier) in modifiers.iter().enumerate() {
        match index {
            0 => doc_comment_slot(modifier)?,
            1 => {}
            2 => {
                scope::visibility::modifier(modifier)?;
            }
            PROTECTED_SLOT => is_protected = protected_slot(modifier)?,
            // Validated, with the declaration kind, by `noncomputable_registration` below.
            NONCOMPUTABLE_SLOT => is_noncomputable = noncomputable_slot(modifier)?,
            5 => match expect_null_args(modifier, "unsafe modifier")? {
                [] => {}
                [modifier] => {
                    let [keyword] = expect_node(
                        modifier,
                        &parser_kind(&["Command", "unsafe"]),
                        1,
                        "unsafe modifier",
                    )?
                    else {
                        return Err(failure(SourceInferenceError::Scope));
                    };
                    expect_atom(keyword, "unsafe", "unsafe modifier")?;
                    is_unsafe = true;
                }
                _ => return Err(failure(SourceInferenceError::Scope)),
            },
            6 if context
                .partial
                .as_ref()
                .is_some_and(|state| state.kind == partial::Kind::Partial) =>
            {
                partial::validate_modifier(modifier)?
            }
            _ => expect_empty_null(modifier, "empty declaration modifier")?,
        }
    }
    noncomputable_registration(syntax)?;
    if is_protected && generated_name.is_some() {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "a named protected declaration",
        });
    }
    let is_instance = matches!(&declaration[1], Syntax::Node { kind,.. } if kind==&parser_kind(&["Command","instance"]));
    let is_theorem = matches!(&declaration[1], Syntax::Node { kind,.. } if kind==&parser_kind(&["Command","theorem"]));
    let is_abbrev = matches!(&declaration[1], Syntax::Node { kind,.. } if kind==&parser_kind(&["Command","abbrev"]));
    // `opaque` is an opaque constant whose signature is a `declSig` and whose value is
    // optional (vendored `Lean/Elab/Declaration.lean`, `elabOpaque` via `mkDefViewOfOpaque`).
    let is_opaque = matches!(&declaration[1], Syntax::Node { kind,.. } if kind==&parser_kind(&["Command","opaque"]));
    // `axiom` is `"axiom " declId declSig` (vendored `Lean/Elab/Declaration.lean`,
    // `elabAxiom`): a theorem's header and no value.
    let is_axiom = matches!(&declaration[1], Syntax::Node { kind,.. } if kind==&parser_kind(&["Command","axiom"]));
    if is_unsafe {
        // MutualDef.check at the pin forbids unsafe theorems and unsafe
        // partial declarations. Opaque/axiom forms need a separate source
        // door; do not accidentally give them recursive-definition machinery.
        if is_theorem
            || is_opaque
            || is_axiom
            || context
                .partial
                .as_ref()
                .is_some_and(|state| state.kind != partial::Kind::Unsafe)
        {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "unsafe def, abbrev, or data instance without partial",
            });
        }
        context.partial.get_or_insert(partial::State {
            kind: partial::Kind::Unsafe,
            ..partial::State::default()
        });
    }
    if is_opaque {
        let parts = expect_node(
            &declaration[1],
            &parser_kind(&["Command", "opaque"]),
            4,
            "opaque",
        )?;
        if expect_null_args(&parts[3], "opaque value")?.is_empty() {
            return opaque_without_value(declaration, parts, context, generated_name);
        }
    }
    let instance_parts;
    let opaque_parts;
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
    } else if is_opaque {
        let parts = expect_node(
            &declaration[1],
            &parser_kind(&["Command", "opaque"]),
            4,
            "opaque",
        )?;
        expect_atom(&parts[0], "opaque", "opaque keyword")?;
        let [value] = expect_null_args(&parts[3], "opaque value")? else {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "one opaque value",
            });
        };
        opaque_parts = [
            parts[0].clone(),
            parts[1].clone(),
            parts[2].clone(),
            value.clone(),
        ];
        &opaque_parts[..]
    } else {
        // An abbreviation has the definition's optional signature and value,
        // but no deriving slot (Lean.Parser.Command.abbrev at the pin); an axiom
        // has a theorem's `declId declSig` and no value at all.
        let (kind, keyword, arity) = if is_theorem {
            ("theorem", "theorem", 4)
        } else if is_axiom {
            ("axiom", "axiom", 3)
        } else if is_abbrev {
            ("abbrev", "abbrev", 4)
        } else {
            ("definition", "def", 5)
        };
        let parts = expect_node(
            &declaration[1],
            &parser_kind(&["Command", kind]),
            arity,
            "named declaration",
        )?;
        expect_atom(&parts[0], keyword, "declaration keyword")?;
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
        None => {
            let owned = context.enter_declaration(name)?;
            if !is_axiom {
                context.ensure_equation_names_available(&owned)?;
            }
            owned
        }
    };
    context.local_function_lifting.parent =
        (!owned_name.is_anonymous()).then(|| owned_name.clone());
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
            if is_theorem || is_instance || is_opaque || is_axiom {
                "declSig"
            } else {
                "optDeclSig"
            },
        ]),
        2,
        "declaration signature",
    )?;
    // The pin's `withAutoBoundImplicit` (Lean/Elab/Term/TermElabM.lean:1932-1955): an unknown
    // atomic name in the header restores the header's state, becomes an implicit local of a
    // fresh type, and the header is elaborated again. Never the definition's own name
    // (MutualDef.lean:213). See `auto_bound_name` for which names.
    let mut own_names = own_short_name(name);
    if let Some(group) = context
        .partial
        .as_ref()
        .and_then(|state| state.group.as_ref())
    {
        for name in &group.names {
            own_names.extend(own_short_name(name));
        }
    }
    let (autos, (mut parameters, mut expected)) =
        context.with_auto_bound_implicits(&own_names, |context| {
            let parameters = context.bind_parameters(&signature[0])?;
            let expected = if is_theorem || is_instance || is_opaque || is_axiom {
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
            Ok((parameters, expected))
        })?;
    context.refuse_auto_bound_dependencies(&autos, &parameters)?;
    parameters.splice(0..0, autos);
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
    let (proof_instance, hidden_instance) = if is_instance {
        context.validate_instance_binder(
            expected
                .as_ref()
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?,
        )?;
        instance_command::prepare_header(
            context,
            &parameters,
            expected
                .as_ref()
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?,
            &modifiers[1],
        )?
    } else {
        (false, false)
    };
    if anonymous_instance {
        let expected = expected
            .as_ref()
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        owned_name = context.generated_instance_name(&parameters, expected)?;
        context.local_function_lifting.parent = Some(owned_name.clone());
    }
    if is_instance && !hidden_instance {
        // Naming may consult the private predecessor only for collisions. Once
        // the name is chosen, an exposed body retains only its public world.
        context.private_proof_body = None;
    }
    if let Some(probe) = &mut context.declaration_header_probe {
        *probe = if is_instance {
            hidden_instance
        } else {
            context.source_scope.exports_declaration() && !context.source_scope.expose_definitions
        };
        return Err(failure(SourceInferenceError::ObservationComplete));
    }
    let name = &owned_name;
    if is_axiom
        || context
            .partial
            .as_ref()
            .and_then(|state| state.group.as_ref())
            .is_some_and(|group| group.header_only)
    {
        let expected = expected.ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        return axiom_from_header(context, name, parameters, expected);
    }
    let theorem_section_parameters = if is_theorem {
        let mut roots: Vec<_> = parameters.iter().map(|local| local.type_.clone()).collect();
        roots.extend(expected.iter().cloned());
        let selected = context.section_parameters(&roots, true)?;
        context.restrict_section_locals(&selected);
        Some(selected)
    } else {
        None
    };
    let prop_header = if is_theorem {
        true
    } else if !is_instance
        && let Some(result) = &expected
        && let Some(sort) = context.known_type(result)?
    {
        let sort = context.whnf(&sort)?;
        matches!(sort.node(), ExprNode::Sort { level } if level.normalize().is_zero())
    } else {
        false
    };
    if prop_header {
        // `levelMVarToParamHeaders` (`MutualDef.lean:1148-1161`): eagerly convert
        // universe metavariables occurring in theorem headers or `Prop`-typed
        // headers (including `example ... : Prop`) to universe parameters before
        // elaborating the body.
        let mut roots: Vec<_> = context
            .source_scope
            .variables
            .locals()
            .decls()
            .iter()
            .chain(&parameters)
            .map(|local| local.type_.clone())
            .collect();
        roots.extend(expected.iter().cloned());
        context.generalize_declaration_universes(&roots)?;
    }
    if prop_header || proof_instance {
        for parameter in &mut parameters {
            parameter.type_ = context.instantiate(&parameter.type_)?;
        }
        if let Some(expected) = &mut expected {
            *expected = context.instantiate(expected)?;
        }
        let locals = context.txn.lctx.decls().to_vec();
        let mut lctx = LocalContext::new();
        for mut local in locals {
            local.type_ = context.instantiate(&local.type_)?;
            if let Some(value) = &mut local.value {
                *value = context.instantiate(value)?;
            }
            tactics::eliminate::add_local(&mut lctx, &local);
        }
        context.txn.lctx = lctx;
    }
    if proof_instance && context.source_scope.exports_declaration() {
        context.public_instance_signature = Some(instance_command::PublicHeader::freeze(
            context,
            name,
            &parameters,
            expected
                .as_ref()
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?,
        )?);
        if hidden_instance {
            context.enter_private_proof()?;
            context.private_instance_body = true;
        }
    } else if hidden_instance && context.source_scope.exports_declaration() {
        context.enter_public_definition_body(&parameters, expected.as_ref())?;
        context.private_instance_body = true;
    } else if context.private_definition_body {
        context.enter_public_definition_body(&parameters, expected.as_ref())?;
    } else if context.private_proof_body.is_some() {
        context.enter_public_theorem_proof(
            name,
            &parameters,
            theorem_section_parameters
                .as_deref()
                .ok_or_else(|| failure(SourceInferenceError::Scope))?,
            expected
                .as_ref()
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?,
        )?;
    }
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
    let termination = recursion::termination_hint(
        termination,
        !is_theorem && !is_instance && !is_abbrev && !is_opaque,
    )?;
    if context.partial.is_some()
        && !matches!(
            termination,
            None | Some(recursion::TerminationHint::Automatic)
        )
    {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "no termination_by or decreasing_by on partial def",
        });
    }
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
    if !is_theorem && !is_instance && !is_abbrev && !is_opaque {
        expect_empty_null(&definition[4], "absent definition clauses")?;
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
    context.complete_local_functions()?;
    context.close_partial_group_references(&mut term)?;
    let section_parameters = if let Some(selected) = theorem_section_parameters {
        selected
    } else {
        let mut roots: Vec<_> = parameters.iter().map(|local| local.type_.clone()).collect();
        roots.extend([term.type_.clone(), term.value.clone()]);
        context.section_parameters(&roots, false)?
    };
    let public_definition_type = context
        .public_definition_header
        .clone()
        .map(|header| header.close(context, &section_parameters, &term.type_))
        .transpose()?;
    let partial_captures = section_parameters.clone();
    let instance_type = context
        .public_instance_signature
        .clone()
        .map(|header| header.close(context, name, &section_parameters))
        .transpose()?;
    parameters.splice(0..0, section_parameters);
    let mut universe_roots: Vec<_> = parameters
        .iter()
        .map(|parameter| parameter.type_.clone())
        .collect();
    universe_roots.extend([term.type_.clone(), term.value.clone()]);
    universe_roots.extend(context.local_function_lifting.roots());
    context.generalize_declaration_universes(&universe_roots)?;
    let mut term = context.finish(term)?;
    context.close_partial_reference(&mut term, &parameters, &partial_captures)?;
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
    // `shouldGenCodeFor` at the pin excludes theorems and noncomputable declarations.
    // These still pass ordinary term elaboration and council admission, but a missing
    // runtime recursor implementation is irrelevant when no code may be generated.
    if !is_theorem && !proof_instance && !is_noncomputable {
        context.noncomputable_definition = context.check_definition_codegen(&term)?;
    }
    let type_ = if let Some(header) = public_definition_type {
        context.instantiate(&header)?
    } else {
        instance_type.unwrap_or(term.type_)
    };
    let level_params = context.declaration_levels(&[type_.clone(), term.value.clone()])?;
    let mut base = ConstantVal {
        name: name.clone(),
        level_params,
        type_,
    };
    if is_theorem || proof_instance {
        if let Some(signature) = &context.public_theorem_signature {
            if base.name != signature.name || base.level_params != signature.level_params {
                return Err(NatDefinitionElabError::UnexpectedSyntax {
                    expected: "a public theorem proof preserving its closed signature",
                });
            }
            // Equation elaboration may introduce fresh binder names or unfold
            // a function-valued statement while building its proof. Preserve
            // the exact original statement; ordinary theorem admission checks
            // the produced proof against this frozen header, not that rebuilt
            // body type. No proof can change the public declaration's type.
            base = signature.clone();
        }
        Ok(Declaration::Thm(fln_env::constants::TheoremVal {
            base,
            value: term.value,
            all: vec![name.clone()],
        }))
    } else if is_opaque {
        Ok(Declaration::Opaque(fln_env::constants::OpaqueVal {
            base,
            value: term.value,
            is_unsafe: false,
            all: vec![name.clone()],
        }))
    } else if context
        .partial
        .as_ref()
        .is_some_and(|state| state.kind == partial::Kind::Unsafe)
    {
        // Basic.addAndCompileUnsafe retains direct recursive references and
        // opaque hints. Even a nonrecursive unsafe definition stays Unsafe;
        // it never acquires a safe logical inhabitant or companion.
        let recursive = context
            .partial
            .as_ref()
            .is_some_and(|state| state.reference.is_some());
        let definition = DefinitionVal {
            base,
            value: term.value,
            hints: if recursive {
                ReducibilityHints::Opaque
            } else if is_abbrev {
                ReducibilityHints::Abbrev
            } else {
                ReducibilityHints::Regular(1)
            },
            safety: DefinitionSafety::Unsafe,
            all: vec![name.clone()],
        };
        if context
            .partial
            .as_ref()
            .is_some_and(|state| state.group.is_some())
        {
            Ok(Declaration::Mutual(vec![definition]))
        } else {
            Ok(Declaration::Defn(definition))
        }
    } else if context
        .partial
        .as_ref()
        .is_some_and(|state| state.reference.is_some() || state.group.is_some())
    {
        base.name = Name::str(name.clone(), "_unsafe_rec");
        Ok(Declaration::Mutual(vec![DefinitionVal {
            all: vec![base.name.clone()],
            base,
            value: term.value,
            hints: ReducibilityHints::Opaque,
            safety: DefinitionSafety::Partial,
        }]))
    } else {
        Ok(Declaration::Defn(DefinitionVal {
            base,
            value: term.value,
            hints: if is_abbrev {
                ReducibilityHints::Abbrev
            } else {
                ReducibilityHints::Regular(1)
            },
            safety: DefinitionSafety::Safe,
            all: vec![name.clone()],
        }))
    }
}

/// An axiom from its elaborated header (`elabAxiom`): the type, closed over its binders and
/// the section variables it uses (`mkForallFVars vars type (usedOnly := true)`), with its
/// universe parameters.
fn axiom_from_header(
    context: &mut Context,
    name: &Name,
    mut parameters: Vec<LocalDecl>,
    expected: Expr,
) -> Result<Declaration, NatDefinitionElabError> {
    context.resolve_instances(true)?;
    context.resume_postponed_eliminators(true)?;
    context.flush(true)?;
    let mut roots: Vec<_> = parameters.iter().map(|local| local.type_.clone()).collect();
    roots.push(expected.clone());
    let section = context.section_parameters(&roots, true)?;
    parameters.splice(0..0, section);
    let mut universe_roots: Vec<_> = parameters
        .iter()
        .map(|parameter| parameter.type_.clone())
        .collect();
    universe_roots.push(expected.clone());
    context.generalize_declaration_universes(&universe_roots)?;
    let mut type_ = context.instantiate(&expected)?;
    for local in parameters.into_iter().rev() {
        let LocalDecl {
            id,
            user_name,
            type_: domain,
            binder_info,
            ..
        } = local;
        let domain = context.instantiate(&domain)?;
        type_ = type_
            .abstract_fvar(&id, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        type_ = Expr::forall_e(user_name, domain, type_, binder_info);
    }
    let type_ = context.instantiate(&type_)?;
    context.require_resolved(std::slice::from_ref(&type_))?;
    if type_.has_fvar() || type_.has_loose_bvars() {
        return Err(failure(SourceInferenceError::Scope));
    }
    let level_params = context.declaration_levels(std::slice::from_ref(&type_))?;
    Ok(Declaration::Axiom(fln_env::constants::AxiomVal {
        base: ConstantVal {
            name: name.clone(),
            level_params,
            type_,
        },
        is_unsafe: false,
    }))
}

/// `opaque c : T` with no value takes the pin's `default_or_ofNonempty%` (vendored
/// `Lean/Elab/BuiltinNotation.lean`): `default` through an `Inhabited` instance, elaborated as
/// the written value would be. Its other half, `Classical.ofNonempty` through a `Nonempty`
/// instance, is noncomputable, and the pin's compiler refuses it for an `opaque` that is not
/// `noncomputable`, `@[extern]` or `@[implemented_by]` ("failed to compile definition … depends
/// on 'Classical.ofNonempty'", measured 2026-10-11). None of those is modelled here, so a type
/// without an `Inhabited` instance is refused, as the pin refuses it.
fn opaque_without_value(
    declaration: &[Syntax],
    parts: &[Syntax],
    context: &mut Context,
    generated_name: Option<Name>,
) -> Result<Declaration, NatDefinitionElabError> {
    let value = |term: Syntax| {
        let null = || Syntax::node(Name::from_components(["null"]), Vec::new());
        let declaration_value = Syntax::node(
            parser_kind(&["Command", "declValSimple"]),
            vec![
                Syntax::atom(fln_syntax::source::SourceInfo::None, ":="),
                term,
                Syntax::node(
                    parser_kind(&["Termination", "suffix"]),
                    vec![null(), null()],
                ),
                null(),
            ],
        );
        let opaque = Syntax::node(
            parser_kind(&["Command", "opaque"]),
            vec![
                parts[0].clone(),
                parts[1].clone(),
                parts[2].clone(),
                Syntax::node(Name::from_components(["null"]), vec![declaration_value]),
            ],
        );
        Syntax::node(
            parser_kind(&["Command", "declaration"]),
            vec![declaration[0].clone(), opaque],
        )
    };
    let identifier = |components: &[&str]| Syntax::Ident {
        info: fln_syntax::source::SourceInfo::None,
        raw_val: fln_syntax::source::ByteSpan::default(),
        val: Name::from_components(components.iter().copied()),
        preresolved: Vec::new(),
    };
    definition_in_context_named(&value(identifier(&["default"])), context, generated_name)
}

pub(super) fn query(
    syntax: &Syntax,
    name: Name,
    environment: &Environment,
    kernel: Budget,
    evaluate: bool,
) -> Result<Declaration, NatDefinitionElabError> {
    query_in(syntax, name, Context::new(environment, kernel), evaluate)
        .map(|(declaration, _)| declaration)
}

/// [`query`] with names resolved in a source scope (namespaces, `open`). With the candidate
/// come the positions, in the scope's `variable` list, of the section variables it is closed
/// over, outermost first (see [`Context::close_query_section`]).
pub(super) fn query_scoped(
    syntax: &Syntax,
    name: Name,
    environment: &Environment,
    kernel: Budget,
    evaluate: bool,
    scope: &scope::SourceScope,
) -> Result<(Declaration, Vec<usize>), NatDefinitionElabError> {
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
) -> Result<(Declaration, Vec<usize>), NatDefinitionElabError> {
    let (term, level_params, section) = query_term(syntax, &name, &mut context, evaluate)?;
    Ok((
        query_declaration(
            name,
            term,
            level_params,
            if evaluate {
                DefinitionSafety::Unsafe
            } else {
                DefinitionSafety::Safe
            },
        ),
        section,
    ))
}

fn query_term(
    syntax: &Syntax,
    name: &Name,
    context: &mut Context,
    evaluate: bool,
) -> Result<(Typed, Vec<Name>, Vec<usize>), NatDefinitionElabError> {
    let expanded = context.expand_match_alternatives(syntax)?;
    let syntax = expanded.as_ref();
    if !name.parent().is_anonymous() || !matches!(name.leaf_view(), LeafView::Num(_)) {
        return Err(if evaluate {
            NatDefinitionElabError::InvalidGeneratedEvaluationName
        } else {
            NatDefinitionElabError::InvalidGeneratedCheckName
        });
    }
    // The scope's universes (`universe u`) and those its `variable`s bound name levels in a
    // query, as in a declaration header without explicit universe parameters.
    if !evaluate {
        context.declare_levels(&Syntax::node(Name::from_components(["null"]), vec![]))?;
    }
    // `#synth C` (`elabSynth`, Lean/Elab/BuiltinCommand.lean:506): `C` elaborated with no
    // expected type, its pending instances synthesized, then an instance of `C` synthesized.
    // The candidate is that instance at type `C`; the caller prints the instance alone.
    let synth = parser_kind(&["Command", "synth"]);
    if !evaluate && syntax.kind() == Some(&synth) {
        let parts = expect_node(syntax, &synth, 2, "Lean.Parser.Command.synth")?;
        expect_atom(&parts[0], "#synth", "synth keyword")?;
        let class = context.term(&parts[1], None)?;
        context.resolve_instances(true)?;
        let class = context.instantiate(&class.value)?;
        let hole = context.instance_hole(class.clone())?;
        context.resolve_instances(true)?;
        context.complete_local_functions()?;
        let term = context.finish(Typed {
            value: hole,
            type_: class,
        })?;
        return context.close_query_section(term, Vec::new());
    }
    // `#print` (`Lean/Elab/Print.lean`): its identifier or string is elaborated as `#check`
    // elaborates a term, and the caller prints from the constant or literal the candidate is.
    let printed = (!evaluate)
        .then(|| {
            ["print", "printSig", "printAxioms", "printEqns"]
                .into_iter()
                .find(|form| syntax.kind() == Some(&parser_kind(&["Command", form])))
        })
        .flatten();
    let argument = match printed {
        Some(form) => {
            let arity = if form == "print" { 2 } else { 3 };
            let parts = expect_node(
                syntax,
                &parser_kind(&["Command", form]),
                arity,
                "Lean.Parser.Command.print",
            )?;
            expect_atom(&parts[0], "#print", "print keyword")?;
            &parts[arity - 1]
        }
        None => {
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
            &parts[1]
        }
    };
    let mut term = context.term(argument, None)?;
    if evaluate {
        let (head, explicit) = context.explicit_application_head(argument)?;
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
    context.complete_local_functions()?;
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
        context.check_compiled_recursors(&term)?;
        return Ok((term, level_params, Vec::new()));
    }
    context.close_query_section(term, level_params)
}

impl Context {
    /// The pin elaborates `#check` and `#synth` with every section variable in the local
    /// context (`runTermElabM`, vendored `Lean/Elab/Command.lean`) and prints the term with
    /// those variables as they are named there. The candidate here is closed over the variables
    /// its term uses, outermost first, as a definition's value is, so the kernel can check it;
    /// the caller opens the binders again to print. `level_params` gains the scope universes
    /// (`universe u`) the closed term uses. Returns the closed variables' positions in the
    /// scope's `variable` list.
    fn close_query_section(
        &mut self,
        mut term: Typed,
        mut level_params: Vec<Name>,
    ) -> Result<(Typed, Vec<Name>, Vec<usize>), NatDefinitionElabError> {
        let section = self.section_parameters(&[term.value.clone(), term.type_.clone()], false)?;
        let declared = self.source_scope.variables.locals().decls();
        let positions = section
            .iter()
            .map(|local| {
                declared
                    .iter()
                    .position(|declared| declared.id == local.id)
                    .ok_or_else(|| failure(SourceInferenceError::Scope))
            })
            .collect::<Result<Vec<_>, _>>()?;
        for local in section.into_iter().rev() {
            let LocalDecl {
                id,
                user_name: name,
                type_: domain,
                binder_info: style,
                ..
            } = local;
            let domain = self.instantiate(&domain)?;
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
        let term = self.finish(term)?;
        if term.value.has_fvar() || term.type_.has_fvar() {
            return Err(failure(SourceInferenceError::Scope));
        }
        for level in self.declaration_levels(&[term.type_.clone(), term.value.clone()])? {
            if !level_params.contains(&level) {
                level_params.push(level);
            }
        }
        Ok((term, level_params, positions))
    }
}

fn query_declaration(
    name: Name,
    term: Typed,
    level_params: Vec<Name>,
    safety: DefinitionSafety,
) -> Declaration {
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name.clone(),
            level_params,
            type_: term.type_,
        },
        value: term.value,
        hints: ReducibilityHints::Regular(1),
        safety,
        all: vec![name],
    })
}

/// Registration requested by a canonical named source instance. The caller must
/// still obtain ordinary declaration admission before installing this metadata.
/// Use [`instance_registration_is_scoped`] to select namespace registration.
/// [`instance_registration_is_local`] instead requests a lexical selection;
/// its registration must never enter the persistent environment journal.
pub fn instance_registration(
    syntax: &Syntax,
) -> Result<Option<(Name, u32)>, NatDefinitionElabError> {
    instance_command::registration(syntax)
}

/// Chronological global default-instance priorities requested by a declaration.
/// Apply these only to the actual name returned by ordinary checked admission.
pub fn default_instance_registration(syntax: &Syntax) -> Result<Vec<u32>, NatDefinitionElabError> {
    instance_command::default_registration(syntax)
}

/// Whether an instance command requests namespace-scoped registration. Read
/// alongside [`instance_registration`]; after admission, register in the current
/// source namespace, which need not be the qualified declaration name's parent.
pub fn instance_registration_is_scoped(syntax: &Syntax) -> Result<bool, NatDefinitionElabError> {
    instance_command::is_scoped(syntax)
}

/// Whether an instance command requests registration in its lexical source
/// scope. The checked named declaration itself survives the end of that scope.
pub fn instance_registration_is_local(syntax: &Syntax) -> Result<bool, NatDefinitionElabError> {
    instance_command::is_local(syntax)
}

/// `declModifiers`' `protected` slot: docComment, attributes, visibility, then
/// `protected` (vendored `src/Lean/Parser/Command.lean`, `declModifiers`).
const PROTECTED_SLOT: usize = 3;
pub(super) const NONCOMPUTABLE_SLOT: usize = 4;

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

/// Whether a `noncomputable` slot is set: empty, or exactly one
/// `Lean.Parser.Command.noncomputable` node holding the keyword.
pub(super) fn noncomputable_slot(slot: &Syntax) -> Result<bool, NatDefinitionElabError> {
    match expect_null_args(slot, "noncomputable modifier")? {
        [] => Ok(false),
        [modifier] => {
            let parts = expect_node(
                modifier,
                &parser_kind(&["Command", "noncomputable"]),
                1,
                "noncomputable modifier",
            )?;
            expect_atom(&parts[0], "noncomputable", "noncomputable keyword")?;
            Ok(true)
        }
        _ => Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "one noncomputable modifier",
        }),
    }
}

/// The requested name of a noncomputable definition, abbreviation, instance or opaque.
/// These declarations are checked but never compiled (the pin's `noncomputableExt`,
/// vendored `src/Lean/Compiler/NoncomputableAttr.lean`). As for [`instance_registration`],
/// an anonymous name requests the instance name generated by elaboration: the caller must
/// take that exact name from the completed council admission, never publish the placeholder.
/// A `noncomputable example` declares nothing. An explicit `noncomputable theorem` is the
/// pin's error "'theorem' subsumes 'noncomputable'"; a proof-valued instance is allowed.
pub fn noncomputable_registration(syntax: &Syntax) -> Result<Option<Name>, NatDefinitionElabError> {
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
    if !noncomputable_slot(&modifiers[NONCOMPUTABLE_SLOT])? {
        return Ok(None);
    }
    let kind = |name: &str| declaration[1].kind() == Some(&parser_kind(&["Command", name]));
    if kind("example") {
        return Ok(None);
    }
    if kind("theorem") {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "a computable theorem ('theorem' subsumes 'noncomputable')",
        });
    }
    if kind("instance") {
        return instance_command::registration(syntax)
            .map(|registration| registration.map(|(name, _)| name));
    }
    if !kind("definition") && !kind("abbrev") && !kind("opaque") {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "a noncomputable `def`, `abbrev`, `instance`, `opaque` or `example`",
        });
    }
    let Syntax::Node { args, .. } = &declaration[1] else {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "named declaration",
        });
    };
    let id = expect_node(
        args.get(1)
            .ok_or(NatDefinitionElabError::UnexpectedSyntax {
                expected: "declaration id",
            })?,
        &parser_kind(&["Command", "declId"]),
        2,
        "declaration id",
    )?;
    match &id[0] {
        Syntax::Ident { val, .. } if !val.is_anonymous() => Ok(Some(val.clone())),
        _ => Err(NatDefinitionElabError::AnonymousDeclarationName),
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
