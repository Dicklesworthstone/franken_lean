//! Source reducibility updates over already checked declarations.
//!
//! Validation follows the pin's Lean/ReducibilityAttrs.lean. Global attributes
//! enter the persistent journal; local attributes live only in SourceScope and
//! are projected into a temporary environment for each elaboration.
use super::*;
use fln_elab::reducibility::{Reducibility, ReducibilityError};
use fln_elab::source::scope::SourceScope;
use fln_parse::command_scope::reducibility::{
    AttributeScope, ReducibilityAttribute, ReducibilityStatus,
};

const MAX_DECLARATIONS: usize = 4096;

pub(super) fn registry_error(
    error: ReducibilityError,
    (file, command, offset): (usize, usize, usize),
) -> SourceCheckError {
    SourceCheckError::Command {
        file,
        command,
        offset,
        error: Box::new(EngineExecutionError::Frontend(
            DefinitionFrontendError::Elaborate(fln_elab::NatDefinitionElabError::Inference(
                fln_elab::source::SourceInferenceError::Unification(Box::new(
                    fln_elab::constraint::unify::UnificationError::Reducibility(error),
                )),
            )),
        )),
    }
}

pub(super) fn apply(
    environment: &Environment,
    file_base: &Environment,
    scope: &mut SourceScope,
    attribute: ReducibilityAttribute,
    position @ (file, command, offset): (usize, usize, usize),
) -> Result<Environment, SourceCheckError> {
    if attribute.declarations.len() > MAX_DECLARATIONS {
        return Err(SourceCheckError::Limit {
            resource: "reducibility attribute declarations",
            limit: MAX_DECLARATIONS,
        });
    }
    let refuse = |message| SourceCheckError::Scope {
        file,
        command,
        offset,
        message,
    };
    let allow_unsafe = scope
        .options
        .get_bool(&Name::from_components(["allowUnsafeReducibility"]), false);
    let local = match attribute.scope {
        AttributeScope::Local => true,
        AttributeScope::Scoped => {
            return Err(refuse(if scope.namespace.is_anonymous() {
                "scoped reducibility attributes must be used inside namespaces".into()
            } else if allow_unsafe {
                "scoped reducibility attributes are not supported".into()
            } else {
                "failed to set reducibility status: the scoped modifier is not recommended for this kind of attribute".into()
            }));
        }
        AttributeScope::Global => false,
    };
    let status = match attribute.status {
        ReducibilityStatus::Reducible => Reducibility::Reducible,
        ReducibilityStatus::Semireducible => Reducibility::Semireducible,
        ReducibilityStatus::Irreducible => Reducibility::Irreducible,
        ReducibilityStatus::ImplicitReducible => Reducibility::ImplicitReducible,
    };
    let mut next = environment.clone();
    let mut overrides = scope.local_reducibility.clone();
    for requested in attribute.declarations {
        let name = scope
            .resolve(&requested, |name| next.contains(name))
            .map_err(|error| refuse(error.to_string()))?
            .ok_or_else(|| {
                refuse(format!(
                    "unknown reducibility declaration `{}`",
                    requested.to_display_string(),
                ))
            })?;
        if !allow_unsafe && !matches!(next.find(&name), Some(ConstantInfo::Defn(_))) {
            return Err(refuse(format!(
                "failed to set reducibility status: `{}` is not a definition",
                name.to_display_string(),
            )));
        }
        if !allow_unsafe && !local && file_base.contains(&name) {
            return Err(refuse(format!(
                "failed to set reducibility status: `{}` has not been defined in this file",
                name.to_display_string(),
            )));
        }
        // Local status takes precedence even when validating a global update,
        // as getReducibilityStatusCore reads reducibilityExtra before core.
        let effective = if scope.exports_declaration() {
            overrides.visible_in(&next).environment(&next)
        } else {
            overrides.environment(&next)
        }
        .map_err(|error| registry_error(error, position))?;
        let old = fln_elab::reducibility::table(&effective)
            .map_err(|error| registry_error(error, position))?
            .status(&name);
        let allowed = match status {
            Reducibility::Reducible => !local && old == Reducibility::Semireducible,
            Reducibility::ImplicitReducible => old == Reducibility::Semireducible,
            Reducibility::Irreducible => matches!(
                old,
                Reducibility::Semireducible | Reducibility::ImplicitReducible
            ),
            Reducibility::Semireducible => local && old == Reducibility::Irreducible,
        };
        if !allow_unsafe && !allowed {
            return Err(refuse(format!(
                "failed to set reducibility status for `{}`: transition from {old:?} to {status:?} is not permitted",
                name.to_display_string(),
            )));
        }
        if local {
            overrides = overrides
                .with_status(&next, &name, status)
                .map_err(|error| registry_error(error, position))?;
        } else {
            next = fln_elab::reducibility::register(&next, &name, status)
                .map_err(|error| registry_error(error, position))?;
        }
    }
    // Neither a local prefix nor persistent metadata escapes a failed batch.
    scope.local_reducibility = overrides;
    Ok(next)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    #[test]
    fn failed_attribute_batches_leave_the_active_scope_and_journal_unchanged() {
        let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20));
        let base = Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap();
        let checked = base
            .check_source_files(
                &[b"def first : Nat := 1\ndef second : Nat := 2"],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
        let env = checked.environment();
        let before = fln_elab::reducibility::journal_digest(env);
        let mut scope = SourceScope::default();
        let original = scope.clone();
        let attribute = |status, declarations: &[&str]| ReducibilityAttribute {
            declarations: declarations.iter().map(|text| name(text)).collect(),
            status,
            scope: AttributeScope::Local,
        };
        assert!(
            apply(
                env,
                base.environment(),
                &mut scope,
                attribute(ReducibilityStatus::Irreducible, &["first", "missing"]),
                (0, 0, 0),
            )
            .is_err()
        );
        assert_eq!(scope, original);
        let unchanged = apply(
            env,
            base.environment(),
            &mut scope,
            attribute(ReducibilityStatus::Irreducible, &["first"]),
            (0, 0, 0),
        )
        .unwrap();
        assert_eq!(&unchanged, env);
        let active = scope.clone();
        // The first transition is legal; the second must discard that prefix.
        assert!(
            apply(
                env,
                base.environment(),
                &mut scope,
                attribute(ReducibilityStatus::Semireducible, &["first", "second"]),
                (0, 0, 0),
            )
            .is_err()
        );
        assert_eq!(scope, active);
        assert_eq!(fln_elab::reducibility::journal_digest(env), before);
        let effective = scope.local_reducibility.environment(env).unwrap();
        assert_eq!(
            fln_elab::reducibility::table(&effective)
                .unwrap()
                .status(&name("first")),
            Reducibility::Irreducible
        );
        let repeated = scope.local_reducibility.environment(&effective).unwrap();
        assert_eq!(effective, repeated);
    }
}
