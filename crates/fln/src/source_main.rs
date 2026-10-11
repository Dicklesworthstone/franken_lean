//! Execute the pinned executable entry point in an already checked environment.
//!
//! `Lean.Compiler.LCNF.isValidMainType` accepts precisely
//! `(List String →)? IO (UInt32 | Unit | PUnit)`. The interpreter resolves the
//! exact root declaration `main`, independently of the file's open namespaces
//! and private aliases. Arguments are ordinary checked expressions, and the
//! existing explicit IO entry supplies its runtime world only after admission.
//! No result printer or logical world inhabitant is introduced here.

use crate::source_check::SourceCheckError;
use crate::source_evaluation::Entry;
use crate::{
    ConstantInfo, ConstantVal, Declaration, DefinitionExecution, DefinitionSafety, DefinitionVal,
    Engine, EngineExecutionError, EngineExecutionLimits, Environment, Expr, ExprNode, IngressError,
    KVMap, Level, Name, Outcome, ReducibilityHints, SourceCommandBatchExecution, VmExit,
};
use fln_core::expr::Literal;
use fln_rt::obj::Obj;
use std::fmt;

#[derive(Clone, Copy, Debug)]
enum ReturnContract {
    Unit,
    UInt32,
}

/// A retained checked main invocation. The generated declaration is a private
/// successor in `execution`; neither the input engine nor its source batch is
/// changed. Inspect `execution.exit` before interpreting an outcome: a VM
/// resource stop is not a user-supplied process exit code.
#[derive(Debug)]
pub struct MainExecution {
    pub execution: DefinitionExecution,
    contract: ReturnContract,
}

/// The logical success or exception returned by one completed main action.
/// The full UInt32 is retained independently of the host OS's process-status
/// encoding. Neither result implies a new environment publication.
#[derive(Debug)]
pub enum MainOutcome {
    Returned { exit_code: u32 },
    Raised { runtime_type: Expr, exit: VmExit },
}

#[derive(Debug)]
pub enum MainExecutionError {
    MissingMain,
    InvalidMainType,
    UnsupportedMain {
        reason: &'static str,
    },
    UnsupportedContract {
        family: &'static str,
    },
    Limit {
        resource: &'static str,
        limit: usize,
        observed: usize,
    },
    AllocationFailure {
        resource: &'static str,
        requested: usize,
    },
    Preparation(IngressError),
    Execution(SourceCheckError),
}

impl MainExecutionError {
    pub fn disposition(&self) -> (&'static str, bool, u8) {
        match self {
            Self::MissingMain | Self::InvalidMainType => ("input", false, 1),
            Self::UnsupportedMain { .. } | Self::UnsupportedContract { .. } => {
                ("capability", false, 5)
            }
            Self::Limit { .. } | Self::AllocationFailure { .. } => ("resource", false, 3),
            Self::Preparation(error) if error.is_resource_exhaustion() => ("resource", false, 3),
            Self::Preparation(_) => ("capability", false, 5),
            Self::Execution(error) => error.disposition(),
        }
    }
}

impl fmt::Display for MainExecutionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingMain => f.write_str("unknown executable declaration `main`"),
            Self::InvalidMainType => f.write_str(
                "`main` function must have type `(List String →)? IO (UInt32 | Unit | PUnit)`",
            ),
            Self::UnsupportedMain { reason } => write!(f, "cannot execute `main`: {reason}"),
            Self::UnsupportedContract { family } => {
                write!(f, "main execution requires the checked {family} contract")
            }
            Self::Limit {
                resource,
                limit,
                observed,
            } => {
                write!(f, "main {resource} limit {limit} exceeded by {observed}")
            }
            Self::AllocationFailure {
                resource,
                requested,
            } => {
                write!(f, "could not allocate main {resource} ({requested})")
            }
            Self::Preparation(error) => error.fmt(f),
            Self::Execution(SourceCheckError::Command { error, .. }) => error.fmt(f),
            Self::Execution(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for MainExecutionError {}

impl From<EngineExecutionError> for MainExecutionError {
    fn from(error: EngineExecutionError) -> Self {
        Self::Execution(SourceCheckError::Command {
            file: 0,
            command: 0,
            offset: 0,
            error: Box::new(error),
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MainProjectionError {
    NonReturningExit,
    MissingIoResult,
    InvalidResultRepresentation,
    InvalidPayload,
    UInt32Range,
}

impl MainProjectionError {
    pub fn disposition(&self) -> (&'static str, bool, u8) {
        ("internal-fault", false, 4)
    }
}

impl fmt::Display for MainProjectionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::NonReturningExit => "main did not return a VM value",
            Self::MissingIoResult => "main did not retain its checked IO result",
            Self::InvalidResultRepresentation => "main returned a malformed logical IO result",
            Self::InvalidPayload => "main result does not have its checked constructor layout",
            Self::UInt32Range => "main UInt32 result lies outside its checked finite range",
        })
    }
}

impl std::error::Error for MainProjectionError {}

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn constant(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}

fn is_constant(expr: &Expr, label: &str, levels: &[Level]) -> bool {
    matches!(expr.node(), ExprNode::Const { name: actual, levels: actual_levels }
        if actual == &name(label) && actual_levels == levels)
}

/// Match the original declaration type, without delta reduction, inferred
/// implicit arguments or source-name resolution. Binder visibility does not
/// alter the pin's executable arity.
fn signature(type_: &Expr) -> Result<(bool, Expr, ReturnContract), MainExecutionError> {
    let (arguments, result) = match type_.node() {
        ExprNode::ForallE {
            binder_type, body, ..
        } => {
            let ExprNode::App { f, a } = binder_type.node() else {
                return Err(MainExecutionError::InvalidMainType);
            };
            if !is_constant(f, "List", &[Level::zero()]) || !is_constant(a, "String", &[]) {
                return Err(MainExecutionError::InvalidMainType);
            }
            (true, body)
        }
        _ => (false, type_),
    };
    let ExprNode::App { f, a } = result.node() else {
        return Err(MainExecutionError::InvalidMainType);
    };
    if !is_constant(f, "IO", &[]) {
        return Err(MainExecutionError::InvalidMainType);
    }
    let contract = if is_constant(a, "UInt32", &[]) {
        ReturnContract::UInt32
    } else if is_constant(a, "Unit", &[]) || is_constant(a, "PUnit", &[Level::one()]) {
        ReturnContract::Unit
    } else {
        return Err(MainExecutionError::InvalidMainType);
    };
    Ok((arguments, result.clone(), contract))
}

fn check_limit(
    resource: &'static str,
    observed: usize,
    limit: usize,
) -> Result<(), MainExecutionError> {
    if observed > limit {
        Err(MainExecutionError::Limit {
            resource,
            limit,
            observed,
        })
    } else {
        Ok(())
    }
}

fn tick(visited: &mut usize, limits: EngineExecutionLimits) -> Result<(), MainExecutionError> {
    crate::charge_catalog_node(visited, limits.ingress).map_err(MainExecutionError::Preparation)
}

fn arguments(
    values: &[String],
    visited: &mut usize,
    limits: EngineExecutionLimits,
) -> Result<Expr, MainExecutionError> {
    // Check the complete request before copying any caller-owned text. The
    // same independent ingress ceilings will apply again to executable code.
    check_limit(
        "argument count",
        values.len(),
        limits.ingress.max_context_depth,
    )?;
    let mut bytes = 0usize;
    for value in values {
        tick(visited, limits)?;
        bytes = bytes
            .checked_add(value.len())
            .ok_or(MainExecutionError::Limit {
                resource: "argument bytes",
                limit: limits.ingress.max_literal_bytes,
                observed: usize::MAX,
            })?;
        check_limit("argument bytes", bytes, limits.ingress.max_literal_bytes)?;
    }
    let string = constant("String");
    let mut result = Expr::app(
        Expr::const_(name("List.nil"), vec![Level::zero()]),
        string.clone(),
    );
    let cons = Expr::app(Expr::const_(name("List.cons"), vec![Level::zero()]), string);
    for value in values.iter().rev() {
        for _ in 0..3 {
            tick(visited, limits)?;
        }
        let mut text = String::new();
        text.try_reserve_exact(value.len())
            .map_err(|_| MainExecutionError::AllocationFailure {
                resource: "argument text",
                requested: value.len(),
            })?;
        text.push_str(value);
        result = Expr::app(
            Expr::app(cons.clone(), Expr::lit(Literal::Str(text))),
            result,
        );
    }
    Ok(result)
}

fn generated_name(
    environment: &Environment,
    visited: &mut usize,
    limits: EngineExecutionLimits,
) -> Result<Name, MainExecutionError> {
    for offset in 0..=environment.len() {
        tick(visited, limits)?;
        let component = u64::try_from(offset).map_err(|_| MainExecutionError::Limit {
            resource: "generated name space",
            limit: usize::MAX,
            observed: offset,
        })?;
        let candidate = Name::num(Name::anonymous(), component);
        if !environment.contains(&candidate) {
            return Ok(candidate);
        }
    }
    Err(MainExecutionError::UnsupportedMain {
        reason: "generated name space is exhausted",
    })
}

fn unit_contract_matches(environment: &Environment, result: &Expr) -> bool {
    let ExprNode::App { a: payload, .. } = result.node() else {
        return false;
    };
    let family_name = name("PUnit");
    let ctor_name = name("PUnit.unit");
    if is_constant(payload, "Unit", &[]) {
        let Some(ConstantInfo::Defn(alias)) = environment.find(&name("Unit")) else {
            return false;
        };
        if alias.safety != DefinitionSafety::Safe
            || !alias.base.level_params.is_empty()
            || alias.base.type_ != Expr::sort(Level::one())
            || alias.value != Expr::const_(family_name.clone(), vec![Level::one()])
        {
            return false;
        }
    }
    let Some(ConstantInfo::Induct(family)) = environment.find(&family_name) else {
        return false;
    };
    let [universe] = family.base.level_params.as_slice() else {
        return false;
    };
    let level = Level::param(universe.clone());
    if family.is_unsafe
        || family.num_params != 0
        || family.num_indices != 0
        || family.num_nested != 0
        || family.is_rec
        || family.is_reflexive
        || family.all.as_slice() != [family_name.clone()]
        || family.ctors.as_slice() != [ctor_name.clone()]
        || family.base.type_ != Expr::sort(level.clone())
    {
        return false;
    }
    matches!(environment.find(&ctor_name), Some(ConstantInfo::Ctor(ctor))
        if !ctor.is_unsafe && ctor.induct == family_name && ctor.cidx == 0
        && ctor.num_params == 0 && ctor.num_fields == 0
        && ctor.base.level_params == family.base.level_params
        && ctor.base.type_ == Expr::const_(family_name, vec![level]))
}

impl Engine {
    /// Execute the exact root `main` after a caller has completed source or
    /// module checking. Its original type must have a pinned main signature;
    /// namespaces, type aliases and private names do not supply another entry.
    /// A checked companion or `implemented_by` still has ordinary compiler
    /// precedence because the candidate calls `main` rather than copying a body.
    pub fn execute_main(
        &self,
        arguments: &[String],
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<MainExecution>, MainExecutionError> {
        let mut visited = 0;
        tick(&mut visited, limits)?;
        let requested = name("main");
        let info = self
            .environment()
            .find(&requested)
            .ok_or(MainExecutionError::MissingMain)?;
        let (takes_arguments, result, contract) = signature(&info.constant_val().type_)?;
        // The compiler's existing resolver validates every recursive sibling
        // and explicit replacement. A forged suffix must not select a body,
        // and an unsupported opaque/unsafe main must not run its logical value.
        let mut preparation = crate::runtime::Preparation::new(self.environment(), limits.ingress)
            .with_executable_opaques(&self.executable_opaques);
        if preparation
            .executable_definition(&requested)
            .map_err(MainExecutionError::Preparation)?
            .is_none()
        {
            return Err(MainExecutionError::UnsupportedMain {
                reason: "no supported checked executable definition or companion",
            });
        }
        if preparation
            .evaluation_presentation_type(&result)
            .map_err(MainExecutionError::Preparation)?
            .is_none()
        {
            return Err(MainExecutionError::UnsupportedContract { family: "IO world" });
        }
        // Establish the result's host interpretation before any action effect.
        // These comparisons install no definitions or runtime native bindings.
        match contract {
            ReturnContract::Unit => {
                tick(&mut visited, limits)?;
                if !unit_contract_matches(self.environment(), &result) {
                    return Err(MainExecutionError::UnsupportedContract {
                        family: "Unit/PUnit",
                    });
                }
                for label in ["PUnit", "PUnit.unit", "Unit"] {
                    crate::source_intrinsics::check_selected_extern_attribute(
                        self.environment(),
                        &name(label),
                        &mut None,
                        &mut visited,
                        limits.ingress,
                    )
                    .map_err(MainExecutionError::Preparation)?;
                }
            }
            ReturnContract::UInt32 => {
                if !crate::source_intrinsics::io::results::word_contract_matches(
                    self.environment(),
                    &mut None,
                    &mut visited,
                    limits.ingress,
                )
                .map_err(MainExecutionError::Preparation)?
                {
                    return Err(MainExecutionError::UnsupportedContract { family: "UInt32" });
                }
            }
        }
        let level_count = info.constant_val().level_params.len();
        check_limit(
            "universe arguments",
            level_count,
            limits.ingress.max_context_depth,
        )?;
        let mut levels = Vec::new();
        levels.try_reserve_exact(level_count).map_err(|_| {
            MainExecutionError::AllocationFailure {
                resource: "universe arguments",
                requested: level_count,
            }
        })?;
        // Main's accepted type has no universe parameter. Any unused universe
        // binders can be instantiated without guessing a value-level argument;
        // the complete candidate still passes both ordinary checkers.
        levels.resize(level_count, Level::zero());
        let mut value = Expr::const_(requested, levels);
        if takes_arguments {
            value = Expr::app(value, self::arguments(arguments, &mut visited, limits)?);
        }
        let candidate = generated_name(self.environment(), &mut visited, limits)?;
        let declaration = Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: candidate.clone(),
                level_params: Vec::new(),
                type_: result,
            },
            value,
            hints: ReducibilityHints::Opaque,
            safety: DefinitionSafety::Safe,
            all: vec![candidate],
        });
        Ok(
            match self.execute_definition_entry(declaration, options, limits, Entry::Evaluation)? {
                Outcome::Complete(execution) => Outcome::Complete(MainExecution {
                    execution,
                    contract,
                }),
                Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
            },
        )
    }
}

impl SourceCommandBatchExecution {
    /// Run main in this completed stream's exact final environment with the
    /// explicit caller options. As in Lean's shell, source-local `set_option`
    /// scopes do not become the runtime options for main. No namespace/private
    /// alias resolution is performed. A graph caller must choose its entry
    /// module's batch, not a sibling's engine.
    pub fn execute_main(
        &self,
        arguments: &[String],
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<MainExecution>, MainExecutionError> {
        self.batch.engine.execute_main(arguments, options, limits)
    }
}

fn constructor(value: &Obj, fields: u8) -> bool {
    !value.is_scalar()
        && value.header().tag == 0
        && value.header().other == fields
        && value.byte_size() == 8 + usize::from(fields) * std::mem::size_of::<usize>()
}

fn uint32(value: Obj) -> Result<u32, MainProjectionError> {
    let invalid = MainProjectionError::InvalidPayload;
    if !constructor(&value, 1) {
        return Err(invalid);
    }
    let bits = value.try_ctor_child(0).ok_or(invalid)?;
    if !constructor(&bits, 1) {
        return Err(invalid);
    }
    let fin = bits.try_ctor_child(0).ok_or(invalid)?;
    if !constructor(&fin, 2) {
        return Err(invalid);
    }
    let proof = fin.try_ctor_child(1).ok_or(invalid)?;
    if !proof.is_scalar() || proof.unbox() != 0 {
        return Err(invalid);
    }
    let natural = fin.try_ctor_child(0).ok_or(invalid)?;
    if natural.is_scalar() {
        return u32::try_from(natural.unbox()).map_err(|_| MainProjectionError::UInt32Range);
    }
    // No decimal conversion or attacker-sized copy is necessary. At most one
    // nonnegative limb can encode a UInt32, including on a 32-bit host.
    let (_, size, limbs) = natural.try_mpz_view().ok_or(invalid)?;
    if size < 0 || limbs.len() > 1 {
        return Err(MainProjectionError::UInt32Range);
    }
    u32::try_from(limbs.first().copied().unwrap_or(0)).map_err(|_| MainProjectionError::UInt32Range)
}

impl MainExecution {
    pub fn outcome(&self) -> Result<MainOutcome, MainProjectionError> {
        self.outcome_for_exit(&self.execution.exit)
    }

    /// Project a replayed exit using this invocation's checked result contract.
    /// This performs no execution, admission, conversion call or printing.
    pub fn outcome_for_exit(&self, exit: &VmExit) -> Result<MainOutcome, MainProjectionError> {
        let types = self
            .execution
            .io_result_types
            .as_ref()
            .ok_or(MainProjectionError::MissingIoResult)?;
        let VmExit::Returned(returned) = exit else {
            return Err(MainProjectionError::NonReturningExit);
        };
        let value = &returned.value;
        let invalid = MainProjectionError::InvalidResultRepresentation;
        if value.is_scalar()
            || value.header().other != 2
            || value.byte_size() != 8 + 2 * std::mem::size_of::<usize>()
        {
            return Err(invalid);
        }
        let world = value.try_ctor_child(1).ok_or(invalid)?;
        if !world.is_scalar() || world.unbox() != 0 {
            return Err(invalid);
        }
        let payload = value.try_ctor_child(0).ok_or(invalid)?;
        match value.header().tag {
            0 => {
                let exit_code = match self.contract {
                    ReturnContract::Unit => {
                        if !is_constant(&types.value, "PUnit", &[Level::one()])
                            || !constructor(&payload, 0)
                        {
                            return Err(MainProjectionError::InvalidPayload);
                        }
                        0
                    }
                    ReturnContract::UInt32 => {
                        if !is_constant(&types.value, "UInt32", &[]) {
                            return Err(MainProjectionError::InvalidPayload);
                        }
                        uint32(payload)?
                    }
                };
                Ok(MainOutcome::Returned { exit_code })
            }
            1 => {
                let runtime_type = types.error.as_ref().ok_or(invalid)?;
                if !is_constant(runtime_type, "IO.Error", &[]) {
                    return Err(invalid);
                }
                Ok(MainOutcome::Raised {
                    runtime_type: runtime_type.clone(),
                    exit: VmExit::Returned(fln_vm::interpreter::CompletedExecution {
                        value: payload,
                        usage: returned.usage,
                    }),
                })
            }
            _ => Err(invalid),
        }
    }
}
