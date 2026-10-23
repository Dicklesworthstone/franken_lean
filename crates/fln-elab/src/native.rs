//! The embedding engine's native evaluator: the capability behind `native_decide` and
//! `decide +native`, the pin's `Lean.Meta.nativeEqTrue` (vendored `Lean/Meta/Native.lean`).
//!
//! The elaborator owns the tactic. It builds the closed `Bool` it wants run, names the
//! temporary definition and the axiom as the pin does (`mkAuxDeclName`), and adds the
//! axiom `@Eq Bool e true` that the proof cites. A provider only runs one closed `Bool`
//! value through the engine's own compiler and VM — the machinery `#eval` uses — and
//! reports what it returned. It never admits anything into the elaborated result: the
//! axiom reaches the environment through ordinary admission, before the declaration
//! citing it, and is the record of the trust the pin also extends to its compiler.
//!
//! Linked by the embedding facade and passed explicitly in the source scope, as
//! [`crate::arithmetic::ArithmeticProvider`] is. Absent, the tactic refuses typed.

use std::sync::Arc;

use fln_core::outcome::{Inconclusive, InternalFault};
use fln_env::constants::DefinitionVal;

/// What running one closed `Bool` definition produced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeEvaluation {
    /// The definition ran to completion and returned this Boolean.
    Value(bool),
    /// This engine's compiler or VM does not implement something the evaluation needs,
    /// or the run took a path whose pin behaviour this engine does not reproduce (a
    /// `panic!`, which the pin reports and then continues past with the default value).
    /// A non-answer: never the pin's verdict on the proposition.
    Unsupported(String),
    /// Out of budget or cancelled before an answer (FL-INV-07).
    Inconclusive(Inconclusive),
    /// The engine itself failed.
    InternalFault(InternalFault),
}

/// Runs a closed `Bool` definition the elaborator built. `definition` is named, typed
/// `Bool` and universe-parameterized as the pin's `_native.<tactic>.decl` auxiliary
/// is; an implementation checks it, compiles and runs it, and discards it.
pub trait NativeEvaluator: Send + Sync {
    fn evaluate_bool(&self, definition: &DefinitionVal) -> NativeEvaluation;
}

/// The capability as it travels in a source scope.
#[derive(Clone)]
pub struct NativeProvider(pub Arc<dyn NativeEvaluator>);

impl std::fmt::Debug for NativeProvider {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("NativeProvider")
    }
}

impl PartialEq for NativeProvider {
    fn eq(&self, other: &Self) -> bool {
        // In-process source-scope equality, never an artifact identity.
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for NativeProvider {}

/// Why a native evaluation gave no answer about the proposition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeEvaluationError {
    /// The command's elaboration was not given an evaluator, or its route does not
    /// carry the axiom a successful evaluation adds to admission.
    Unavailable,
    /// [`NativeEvaluation::Unsupported`].
    Unsupported(String),
    /// [`NativeEvaluation::InternalFault`].
    Fault(InternalFault),
}

impl std::fmt::Display for NativeEvaluationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unavailable => write!(f, "native evaluation is not available here"),
            Self::Unsupported(reason) => {
                write!(f, "native evaluation is not supported here: {reason}")
            }
            Self::Fault(fault) => write!(f, "native evaluation failed: {fault:?}"),
        }
    }
}
