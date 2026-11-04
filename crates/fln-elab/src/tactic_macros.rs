//! Imported macro execution at the native elaborator boundary.
//!
//! The provider only produces Syntax. The elaborator executes tactic candidates
//! in order, restores failed proof states, and submits the resulting declaration
//! to ordinary kernel admission. Macro scopes, traces and consumed work belong
//! to the provider and survive proof backtracking, as Core.SavedState.restore
//! preserves them in the pin.

use std::sync::Arc;

use fln_core::name::Name;
use fln_core::outcome::{Inconclusive, InternalFault};
use fln_env::environment::Environment;
use fln_syntax::tree::Syntax;

use crate::source::scope::SourceScope;

/// An ordinary macro diagnostic is catchable by tactic alternatives. Missing
/// implementation, resource stops and internal faults are never alternatives.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TacticMacroError {
    Diagnostic { declaration: Name, message: String },
    Unsupported(String),
    Inconclusive(Box<Inconclusive>),
    InternalFault(InternalFault),
}

impl std::fmt::Display for TacticMacroError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Diagnostic {
                declaration,
                message,
            } => {
                write!(f, "macro {}: {message}", declaration.to_display_string())
            }
            Self::Unsupported(message) => write!(f, "imported macro capability: {message}"),
            Self::Inconclusive(reason) => write!(f, "imported macro stopped: {reason:?}"),
            Self::InternalFault(fault) => write!(f, "imported macro fault: {fault:?}"),
        }
    }
}

/// One candidate, never an eagerly expanded list. A diagnostic's no-fallback
/// policy is supplied separately because Unsupported always tries the next rule.
pub enum TacticMacroExpansion {
    Expanded {
        syntax: Syntax,
        no_fallback: bool,
    },
    Unsupported,
    Diagnostic {
        error: TacticMacroError,
        no_fallback: bool,
    },
    Exhausted,
}

/// All lookup authority is borrowed from the elaborator's current transaction.
/// An implementation may retain immutable code, but never an ambient environment
/// or an unchecked declaration as authority for name resolution.
pub trait TacticMacroExpander: Send + Sync {
    fn contains(&self, kind: &Name) -> bool;

    /// Allocate the scope shared by all candidates of this evalTactic call.
    fn enter_tactic(&self, depth: usize) -> Result<u64, TacticMacroError>;

    #[allow(clippy::too_many_arguments)]
    fn expand_tactic(
        &self,
        syntax: &Syntax,
        candidate: usize,
        macro_scope: u64,
        depth: usize,
        environment: &Environment,
        scope: &SourceScope,
    ) -> Result<TacticMacroExpansion, TacticMacroError>;

    /// Root expansion for a term visited while a tactic is executing. Children
    /// remain with the native term worklist; by blocks retain tactic dispatch.
    fn expand_term(
        &self,
        syntax: &Syntax,
        depth: usize,
        environment: &Environment,
        scope: &SourceScope,
    ) -> Result<Option<Syntax>, TacticMacroError>;
}

#[derive(Clone)]
pub struct TacticMacroProvider(pub Arc<dyn TacticMacroExpander>);

impl std::fmt::Debug for TacticMacroProvider {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("TacticMacroProvider")
    }
}

impl PartialEq for TacticMacroProvider {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for TacticMacroProvider {}
