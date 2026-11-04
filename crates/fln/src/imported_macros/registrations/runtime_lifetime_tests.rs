//! Per-command authority must not survive a reporting boundary or a borrowed
//! override. An empty registry suffices: these tests exercise the real owned
//! provider and FileSession rather than an invented execution implementation.
use super::*;
use crate::imported_macros::source::{FileSession, SourceMacroInvocation};
use fln_elab::source::scope::SourceScope;
use fln_elab::tactic_macros::TacticMacroError;

fn registry() -> RegisteredMacros {
    let global = Arc::new(BTreeMap::new());
    RegisteredMacros {
        candidates: global.clone(),
        global,
        scoped: Arc::new(BTreeMap::new()),
        active_scopes: BTreeSet::new(),
        modules: Arc::new(BTreeMap::new()),
        owners: Arc::new(BTreeMap::new()),
    }
}

fn context() -> MacroContext {
    MacroContext {
        quotation_context: Name::from_components(["Main"]),
        current_macro_scope: 99,
        current_recursion_depth: 0,
        max_recursion_depth: 32,
    }
}

fn invocation<'a>(
    registry: &'a RegisteredMacros,
    context: &'a MacroContext,
) -> SourceMacroInvocation<'a> {
    SourceMacroInvocation {
        registry,
        context,
        state: MacroState {
            macro_scope: 100,
            ..MacroState::default()
        },
        lookup: None,
        limits: MacroTreeLimits::default(),
        cancellation: None,
    }
}

#[test]
fn completing_a_session_revokes_archived_scope_providers_without_refunding_work() {
    let registry = registry();
    let context = context();
    let mut session = FileSession::new(invocation(&registry, &context));
    let mut scope = SourceScope::default();
    assert!(matches!(
        session.bind_tactics(&registry, b"theorem t : True := by trivial", &mut scope),
        Outcome::Complete(Ok(()))
    ));
    assert_eq!(
        scope,
        SourceScope::default(),
        "runtime authority is not a persisted lexical effect"
    );
    let archived = scope.clone();
    let provider = archived.tactic_macros.as_ref().unwrap();
    assert_eq!(provider.0.enter_tactic(0).unwrap(), 100);
    let (outcome, report) = session.finish();
    assert!(matches!(outcome, Outcome::Complete(())));
    assert_eq!(report.state.macro_scope, 101);
    assert_eq!(report.tree_usage.visits, 1);
    assert!(
        matches!(provider.0.enter_tactic(0), Err(TacticMacroError::Unsupported(reason)) if reason.contains("completed source command"))
    );
}

struct Lookup(Name);
impl MacroLookup for Lookup {
    fn current_namespace(&self) -> &Name {
        &self.0
    }
    fn has_decl(&self, _: &Name) -> bool {
        false
    }
}
struct NotCancelled;
impl CancellationProbe for NotCancelled {
    fn is_cancelled(&self) -> bool {
        false
    }
}

#[test]
fn borrowed_lookup_or_cancellation_clears_preexisting_owned_authority() {
    let registry = registry();
    let context = context();
    let mut owned = FileSession::new(invocation(&registry, &context));
    let mut original = SourceScope::default();
    assert!(matches!(
        owned.bind_tactics(&registry, b"theorem t : True := by trivial", &mut original),
        Outcome::Complete(Ok(()))
    ));
    let lookup = Lookup(Name::anonymous());
    let cancellation = NotCancelled;
    for override_kind in [false, true] {
        let mut input = invocation(&registry, &context);
        if override_kind {
            input.lookup = Some(&lookup);
        } else {
            input.cancellation = Some(&cancellation);
        }
        let mut borrowed = FileSession::new(input);
        let mut reused = original.clone();
        assert!(matches!(
            borrowed.bind_tactics(&registry, b"theorem t : True := by trivial", &mut reused),
            Outcome::Complete(Ok(()))
        ));
        assert!(reused.tactic_macros.is_none());
    }
    assert!(matches!(owned.finish().0, Outcome::Complete(())));
}
