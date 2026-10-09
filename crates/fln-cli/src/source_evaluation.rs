//! Present explicitly evaluated IO payloads without executing deferred values.
use super::*;

#[derive(Debug)]
pub(super) enum Error {
    Value(SourceValueProjectionError),
    Io(fln::IoEvaluationProjectionError),
    InvalidUnit,
    InvalidException,
    Raised {
        message: String,
        steps: u64,
        system_polls: u64,
        peak_stack_depth: u64,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Value(error) => error.fmt(f),
            Self::Io(error) => error.fmt(f),
            Self::InvalidUnit => f.write_str("IO unit result has an invalid representation"),
            Self::InvalidException => {
                f.write_str("IO exception disagrees with its admitted constructor layout")
            }
            Self::Raised {
                message,
                steps,
                system_polls,
                peak_stack_depth,
            } => write!(
                f,
                "IO exception: {message}; execution used {steps} steps, {system_polls} system polls, peak stack {peak_stack_depth}"
            ),
        }
    }
}

impl Error {
    pub(super) fn disposition(&self) -> (&'static str, bool, u8) {
        match self {
            Self::Raised { .. } => ("io-exception", true, 1),
            Self::Value(SourceValueProjectionError::Shaped(
                fln::ClosedShapedValueError::TooLarge { .. },
            )) => ("resource", false, 3),
            _ => ("internal-fault", false, 4),
        }
    }

    pub(super) fn failure(
        &self,
        command: usize,
        presentation: SourcePresentation,
    ) -> MultiplexerOutput {
        let (class, authority, exit) = self.disposition();
        source_failure(
            class,
            &format!("evaluation command {command}: {self}"),
            authority,
            presentation,
            exit,
        )
    }
}

fn constant(type_: &fln::Expr, components: &[&str]) -> bool {
    matches!(type_.node(), fln::ExprNode::Const { name, levels }
        if name == &fln::Name::from_components(components.iter().copied()) && levels.is_empty())
}

fn unit_type(type_: &fln::Expr) -> bool {
    constant(type_, &["Unit"])
        || matches!(type_.node(), fln::ExprNode::Const { name, levels }
            if name == &fln::Name::from_components(["PUnit"])
                && levels.as_slice() == [fln::Level::one()])
}

/// Imported Unit retains the admitted PUnit constructor's logical layout.
/// The native ABI's scalar Unit is not that boxed, zero-field constructor.
fn unit_payload(
    environment: &fln::Environment,
    runtime_type: &fln::Expr,
    exit: &fln::VmExit,
) -> Result<(), Error> {
    if !unit_type(runtime_type) {
        return Err(Error::InvalidUnit);
    }
    let family_name = fln::Name::from_components(["PUnit"]);
    let ctor_name = fln::Name::from_components(["PUnit", "unit"]);
    if constant(runtime_type, &["Unit"]) {
        let Some(fln::ConstantInfo::Defn(alias)) =
            environment.find(&fln::Name::from_components(["Unit"]))
        else {
            return Err(Error::InvalidUnit);
        };
        if alias.safety != fln::DefinitionSafety::Safe
            || !alias.base.level_params.is_empty()
            || alias.base.type_ != fln::Expr::sort(fln::Level::one())
            || alias.value != fln::Expr::const_(family_name.clone(), vec![fln::Level::one()])
        {
            return Err(Error::InvalidUnit);
        }
    }
    let Some(fln::ConstantInfo::Induct(family)) = environment.find(&family_name) else {
        return Err(Error::InvalidUnit);
    };
    let [universe] = family.base.level_params.as_slice() else {
        return Err(Error::InvalidUnit);
    };
    let level = fln::Level::param(universe.clone());
    if family.is_unsafe
        || family.num_params != 0
        || family.num_indices != 0
        || family.num_nested != 0
        || family.is_rec
        || family.is_reflexive
        || family.all.as_slice() != [family_name.clone()]
        || family.ctors.as_slice() != [ctor_name.clone()]
        || family.base.type_ != fln::Expr::sort(level.clone())
    {
        return Err(Error::InvalidUnit);
    }
    let Some(fln::ConstantInfo::Ctor(ctor)) = environment.find(&ctor_name) else {
        return Err(Error::InvalidUnit);
    };
    if ctor.is_unsafe
        || ctor.induct != family_name
        || ctor.cidx != 0
        || ctor.num_params != 0
        || ctor.num_fields != 0
        || ctor.base.level_params != family.base.level_params
        || ctor.base.type_ != fln::Expr::const_(family_name, vec![level])
    {
        return Err(Error::InvalidUnit);
    }
    let fln::VmExit::Returned(returned) = exit else {
        return Err(Error::InvalidUnit);
    };
    if returned.value.is_scalar()
        || u32::from(returned.value.header().tag) != ctor.cidx
        || returned.value.header().other != 0
        // A zero-field logical constructor contains only the pinned ABI header.
        || returned.value.byte_size() != 8
    {
        return Err(Error::InvalidUnit);
    }
    Ok(())
}

/// Read only the admitted exception constructor. The userError tag is taken
/// from the checked family, never from a pinned numeric tag. Other exceptions
/// retain their constructor name rather than guessing IO.Error.toString.
fn exception_message(
    environment: &fln::Environment,
    runtime_type: &fln::Expr,
    exit: fln::VmExit,
) -> Result<String, Error> {
    if !constant(runtime_type, &["IO", "Error"]) {
        return Err(Error::InvalidException);
    }
    let fln::VmExit::Returned(mut returned) = exit else {
        return Err(Error::InvalidException);
    };
    let family_name = fln::Name::from_components(["IO", "Error"]);
    let Some(fln::ConstantInfo::Induct(family)) = environment.find(&family_name) else {
        return Err(Error::InvalidException);
    };
    if family.is_unsafe || family.num_params != 0 || !family.base.level_params.is_empty() {
        return Err(Error::InvalidException);
    }
    let tag = if returned.value.is_scalar() {
        returned.value.unbox()
    } else {
        usize::from(returned.value.header().tag)
    };
    let Some(ctor_name) = family.ctors.get(tag) else {
        return Err(Error::InvalidException);
    };
    let Some(fln::ConstantInfo::Ctor(ctor)) = environment.find(ctor_name) else {
        return Err(Error::InvalidException);
    };
    if ctor.is_unsafe
        || ctor.induct != family_name
        || ctor.cidx as usize != tag
        || ctor.num_params != 0
        || !ctor.base.level_params.is_empty()
        || (returned.value.is_scalar() && ctor.num_fields != 0)
    {
        return Err(Error::InvalidException);
    }
    if ctor_name != &fln::Name::from_components(["IO", "Error", "userError"]) {
        return Ok(ctor_name.to_display_string());
    }
    let fln::ExprNode::ForallE {
        binder_type, body, ..
    } = ctor.base.type_.node()
    else {
        return Err(Error::InvalidException);
    };
    if ctor.num_fields != 1
        || !constant(binder_type, &["String"])
        || !constant(body, &["IO", "Error"])
        || returned.value.is_scalar()
        || returned.value.header().other != 1
    {
        return Err(Error::InvalidException);
    }
    returned.value = returned
        .value
        .try_ctor_child(0)
        .ok_or(Error::InvalidException)?;
    match fln::closed_vm_value(&fln::VmExit::Returned(returned))
        .map_err(|error| Error::Value(SourceValueProjectionError::Runtime(error)))?
    {
        Some(fln::ClosedVmValue::String(message)) => Ok(message),
        _ => Err(Error::InvalidException),
    }
}

fn raised(
    execution: &fln::DefinitionExecution,
    runtime_type: &fln::Expr,
    exit: fln::VmExit,
) -> Error {
    let fln::VmExit::Returned(returned) = &exit else {
        return Error::InvalidException;
    };
    let usage = returned.usage;
    match exception_message(execution.engine.environment(), runtime_type, exit) {
        Ok(message) => Error::Raised {
            message,
            steps: usage.steps,
            system_polls: usage.system_polls,
            peak_stack_depth: usage.peak_stack_depth,
        },
        Err(error) => error,
    }
}

/// Validate every execution before rendering any output, including evaluations
/// in dependencies. A later successful command cannot hide an IO exception.
pub(super) fn check(execution: &fln::DefinitionExecution) -> Result<(), Error> {
    match execution.io_evaluation_outcome().map_err(Error::Io)? {
        Some(fln::IoEvaluationOutcome::Raised { runtime_type, exit }) => {
            Err(raised(execution, &runtime_type, exit))
        }
        _ => Ok(()),
    }
}

pub(super) fn value(
    execution: &fln::DefinitionExecution,
) -> Result<Option<SourceFinalValue>, Error> {
    match execution.io_evaluation_outcome().map_err(Error::Io)? {
        Some(fln::IoEvaluationOutcome::Returned { runtime_type, exit }) => {
            // IO returns Type-valued PUnit (the normalized Unit alias). The
            // pin suppresses that result line; the raw JSON door retains it.
            if unit_type(&runtime_type) {
                unit_payload(execution.engine.environment(), &runtime_type, &exit)?;
                return Ok(Some(SourceFinalValue::IoUnit));
            }
            closed_source_cli_value(&runtime_type, &exit).map_err(Error::Value)
        }
        Some(fln::IoEvaluationOutcome::Raised { runtime_type, exit }) => {
            Err(raised(execution, &runtime_type, exit))
        }
        None => {
            closed_source_cli_value(&execution.runtime_type, &execution.exit).map_err(Error::Value)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_rt::obj::Obj;

    fn execute(source: &str) -> fln::DefinitionExecution {
        let limits = fln::EngineExecutionLimits::new(fln::Budget::for_stack_bytes(
            SOURCE_RUN_KERNEL_STACK_BYTES,
        ));
        let engine = fln::Engine::with_source_seed(limits.admission())
            .unwrap()
            .into_complete()
            .unwrap();
        let mut result = engine
            .execute_source_commands_with_checks(source.as_bytes(), &fln::KVMap::new(), limits)
            .unwrap()
            .into_complete()
            .unwrap();
        result.batch.executions.pop().unwrap()
    }

    fn unit_execution() -> fln::DefinitionExecution {
        execute(
            "def Unit := PUnit.{1}\ndef Unit.unit : Unit := PUnit.unit.{1}\ndef ordinaryUnit : Unit := ()",
        )
    }

    #[test]
    fn checked_unit_payload_is_its_logical_boxed_constructor() {
        let execution = unit_execution();
        assert_eq!(
            execution.checker.ground,
            fln::CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        assert!(execution.io_evaluation_outcome().unwrap().is_none());
        for type_ in [
            execution.runtime_type.clone(),
            fln::Expr::const_(fln::Name::from_components(["Unit"]), vec![]),
        ] {
            unit_payload(execution.engine.environment(), &type_, &execution.exit).unwrap();
        }
        let fln::VmExit::Returned(returned) = &execution.exit else {
            panic!("the checked Unit definition must return");
        };
        assert!(!returned.value.is_scalar());
        assert_eq!(returned.value.header().other, 0);
    }

    #[test]
    fn unit_payload_rejects_scalar_tags_fields_and_scalar_storage() {
        let mut execution = unit_execution();
        for value in [
            Obj::mk_nat(0),
            Obj::mk_ctor(1, vec![], &[]),
            Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &[]),
            Obj::mk_ctor(0, vec![], &[0]),
            Obj::mk_ctor(0, vec![], &[0; 8]),
        ] {
            let fln::VmExit::Returned(returned) = &mut execution.exit else {
                panic!("a returned Unit fixture");
            };
            returned.value = value;
            assert!(matches!(
                unit_payload(
                    execution.engine.environment(),
                    &execution.runtime_type,
                    &execution.exit,
                ),
                Err(Error::InvalidUnit)
            ));
        }
    }

    #[test]
    fn unit_payload_requires_the_exact_type_universe_and_checked_alias() {
        let execution = unit_execution();
        for levels in [
            vec![],
            vec![fln::Level::zero()],
            vec![fln::Level::one().succ().unwrap()],
            vec![fln::Level::one(), fln::Level::one()],
        ] {
            let type_ = fln::Expr::const_(fln::Name::from_components(["PUnit"]), levels);
            assert!(!unit_type(&type_));
            assert!(matches!(
                unit_payload(execution.engine.environment(), &type_, &execution.exit),
                Err(Error::InvalidUnit)
            ));
        }
        let wrong_alias = execute("def Unit := Nat\ndef value : Unit := Nat.zero");
        let unit = fln::Expr::const_(fln::Name::from_components(["Unit"]), vec![]);
        assert!(matches!(
            unit_payload(wrong_alias.engine.environment(), &unit, &execution.exit),
            Err(Error::InvalidUnit)
        ));
    }

    #[test]
    fn a_familiar_unit_constructor_name_does_not_authorize_different_metadata() {
        let execution = unit_execution();
        let family_name = fln::Name::from_components(["PUnit"]);
        let ctor_name = fln::Name::from_components(["PUnit", "unit"]);
        let environment = execution.engine.environment();
        for mutation in 0..4 {
            let family = environment.find(&family_name).unwrap().clone();
            let mut info = environment.find(&ctor_name).unwrap().clone();
            let fln::ConstantInfo::Ctor(ctor) = &mut info else {
                panic!("the checked PUnit constructor");
            };
            match mutation {
                0 => ctor.cidx = 1,
                1 => ctor.num_fields = 1,
                2 => ctor.induct = fln::Name::from_components(["OtherUnit"]),
                3 => ctor.base.type_ = fln::Expr::sort(fln::Level::one()),
                _ => unreachable!(),
            }
            // A forged metadata control is never submitted for execution.
            let changed = fln::Environment::new()
                .add_decl(family)
                .unwrap()
                .add_decl(info)
                .unwrap();
            assert!(matches!(
                unit_payload(&changed, &execution.runtime_type, &execution.exit),
                Err(Error::InvalidUnit)
            ));
        }
    }

    #[test]
    fn user_error_messages_follow_checked_constructor_indices_and_string_fields() {
        let execution = execute(
            "inductive IO.Error where\n  | other (code : Nat)\n  | userError (message : String)\ndef failure : IO.Error := IO.Error.userError \"expected λ failure\"",
        );
        let Some(fln::ConstantInfo::Ctor(ctor)) = execution
            .engine
            .environment()
            .find(&fln::Name::from_components(["IO", "Error", "userError"]))
        else {
            panic!("checked constructor missing");
        };
        assert_eq!(ctor.cidx, 1, "this fixture deliberately uses another tag");
        assert!(execution.io_evaluation_outcome().unwrap().is_none());
        assert_eq!(
            exception_message(
                execution.engine.environment(),
                &execution.runtime_type,
                execution.exit,
            )
            .unwrap(),
            "expected λ failure"
        );
    }

    #[test]
    fn other_exceptions_retain_their_checked_constructor_identity() {
        let execution = execute(
            "inductive IO.Error where\n  | custom\n  | userError (message : String)\ndef failure : IO.Error := IO.Error.custom",
        );
        assert_eq!(
            exception_message(
                execution.engine.environment(),
                &execution.runtime_type,
                execution.exit,
            )
            .unwrap(),
            "IO.Error.custom"
        );
    }

    #[test]
    fn a_familiar_exception_name_does_not_authorize_a_different_payload_layout() {
        let execution = execute(
            "inductive IO.Error where\n  | userError (number : Nat)\ndef failure : IO.Error := IO.Error.userError 42",
        );
        assert!(matches!(
            exception_message(
                execution.engine.environment(),
                &execution.runtime_type,
                execution.exit,
            ),
            Err(Error::InvalidException)
        ));
    }
}
