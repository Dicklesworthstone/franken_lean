//! Bounded, stack-safe ingress from closed [`Expr`] values into validated FIR.
//!
//! This is a deliberately narrow post-elaboration bridge. It executes no
//! Reference code, trusts no source text, and does not type-check the `type_`
//! annotation carried by [`ExprNode::LetE`]. The executable subset is Nat and
//! String literals, transparent metadata, let bindings, de Bruijn lookup, and
//! saturated direct applications of caller-supplied intrinsic and constructor
//! bindings, declaration-bound structure projections, saturated direct calls
//! into caller-supplied first-order function bodies, and explicitly typed local
//! lambda closures with under-, exact, closure-result overapplication, and
//! acyclic self- or mutually recursive environments.
//! Concrete semantic classes crossing an explicitly declared [`fir::ValueType::Abi`]
//! parameter or result boundary receive an explicit FIR box or unbox operation.
//! Both preserve the same Marrow object at runtime; no host-value shadow domain
//! or implicit conversion is introduced.
//! Intrinsic declarations retain FIR's pure, state, IO, or task effect identity;
//! source evaluation order remains the execution order.
//! Bindings are untrusted input: this module canonicalizes and checks their
//! shape, while the caller remains responsible for deriving intrinsics from the
//! generated extern contract, deriving constructor layouts from elaborated
//! declarations, stripping top-level lambdas from function bodies, and binding
//! local lambda spines to reviewed runtime signatures. Those signatures may
//! pass and return closures by canonical FIR closure-type id; every such
//! reference is checked against the final deduplicated signature table before
//! lowering. Every other expression constructor is a typed refusal.
//!
//! The traversal uses an explicit heap task stack. A caller receives
//! [`IngressedProgram`] only after the generated program has passed
//! [`fir::validate`]; subsequent FLBC publication remains gated by
//! [`fir::lower_to_flbc`] and FLBC's independent validator.

use crate::fir;
use fln_core::expr::{Expr, ExprNode, Literal};
use fln_core::name::Name;
use std::collections::VecDeque;
use std::fmt;

/// Explicit ceilings for the core-expression ingress.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IngressLimits {
    /// Maximum executable expression nodes visited.
    pub max_nodes: usize,
    /// Maximum source `let` bindings entered.
    pub max_bindings: usize,
    /// Maximum caller-supplied local-lambda annotations inspected.
    pub max_lambda_bindings: usize,
    /// Maximum expression nodes inspected while selecting closure captures.
    pub max_capture_analysis_nodes: usize,
    /// Maximum live de Bruijn context depth.
    pub max_context_depth: usize,
    /// Maximum total bytes copied from executable string literals.
    pub max_literal_bytes: usize,
    /// Maximum arguments in one direct application spine.
    pub max_application_args: usize,
    /// Independent FIR validation ceilings.
    pub fir: fir::ValidationLimits,
}

impl Default for IngressLimits {
    fn default() -> Self {
        Self {
            max_nodes: 1_000_000,
            max_bindings: 1_000_000,
            max_lambda_bindings: 65_536,
            max_capture_analysis_nodes: 1_000_000,
            max_context_depth: 65_536,
            max_literal_bytes: 32 * 1024 * 1024,
            max_application_args: 65_536,
            fir: fir::ValidationLimits::default(),
        }
    }
}

/// Resource dimension named by an ingress refusal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IngressResource {
    Nodes,
    Bindings,
    LambdaBindings,
    CaptureAnalysisNodes,
    ContextDepth,
    LiteralBytes,
    ApplicationArguments,
    PendingTasks,
    ResultValues,
    ProgramTables,
}

impl IngressResource {
    const fn token(self) -> &'static str {
        match self {
            Self::Nodes => "nodes",
            Self::Bindings => "bindings",
            Self::LambdaBindings => "lambda bindings",
            Self::CaptureAnalysisNodes => "capture-analysis nodes",
            Self::ContextDepth => "context depth",
            Self::LiteralBytes => "literal bytes",
            Self::ApplicationArguments => "application arguments",
            Self::PendingTasks => "pending tasks",
            Self::ResultValues => "result values",
            Self::ProgramTables => "program tables",
        }
    }
}

/// Exact reason a core expression did not publish validated FIR.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IngressError {
    ResourceLimit {
        resource: IngressResource,
        limit: usize,
        observed: usize,
    },
    AllocationFailure {
        resource: IngressResource,
        requested: usize,
    },
    OpenFreeVariable,
    UnresolvedMetavariable,
    LooseBoundVariables {
        range: u32,
    },
    UnboundBoundVariable {
        index: u32,
        context_depth: usize,
    },
    MissingCapturedBoundVariable {
        index: u32,
        context_depth: usize,
    },
    UnsupportedNode {
        kind: &'static str,
    },
    UnknownConstant {
        name_hash: u64,
    },
    IntrinsicUniverseArity {
        name_hash: u64,
        expected: usize,
        actual: usize,
    },
    IntrinsicTermArity {
        name_hash: u64,
        expected: usize,
        actual: usize,
    },
    IntrinsicArgumentType {
        name_hash: u64,
        argument: usize,
        expected: fir::ValueType,
        actual: fir::ValueType,
    },
    ConstructorUniverseArity {
        name_hash: u64,
        expected: usize,
        actual: usize,
    },
    ConstructorTermArity {
        name_hash: u64,
        expected: usize,
        actual: usize,
    },
    ConstructorArgumentType {
        name_hash: u64,
        argument: usize,
        expected: fir::ValueType,
        actual: fir::ValueType,
    },
    FunctionUniverseArity {
        name_hash: u64,
        expected: usize,
        actual: usize,
    },
    FunctionTermArity {
        name_hash: u64,
        expected: usize,
        actual: usize,
    },
    FunctionOwnershipArity {
        binding: usize,
        parameters: usize,
        ownership: usize,
    },
    FunctionArgumentType {
        name_hash: u64,
        argument: usize,
        expected: fir::ValueType,
        actual: fir::ValueType,
    },
    FunctionResultType {
        name_hash: u64,
        expected: fir::ValueType,
        actual: fir::ValueType,
    },
    InvalidIntrinsicRow {
        binding: usize,
        row_bytes: usize,
    },
    IntrinsicOwnershipArity {
        binding: usize,
        arguments: usize,
        ownership: usize,
    },
    AnonymousIntrinsicName {
        binding: usize,
    },
    DuplicateIntrinsicRow {
        first: usize,
        second: usize,
    },
    DuplicateIntrinsicName {
        name_hash: u64,
        first: usize,
        second: usize,
    },
    AnonymousConstructorName {
        binding: usize,
    },
    DuplicateConstructorName {
        name_hash: u64,
        first: usize,
        second: usize,
    },
    AnonymousProjectionStructureName {
        binding: usize,
    },
    DuplicateProjectionStructureName {
        name_hash: u64,
        first: usize,
        second: usize,
    },
    UnknownProjection {
        name_hash: u64,
        field: u64,
    },
    ProjectionOperandType {
        name_hash: u64,
        field: u64,
        actual: fir::ValueType,
    },
    ConstructorIntrinsicNameCollision {
        name_hash: u64,
        constructor: usize,
        intrinsic: usize,
    },
    ConstructorFunctionNameCollision {
        name_hash: u64,
        constructor: usize,
        function: usize,
    },
    AnonymousFunctionName {
        binding: usize,
    },
    DuplicateFunctionName {
        name_hash: u64,
        first: usize,
        second: usize,
    },
    CallableNameCollision {
        name_hash: u64,
        intrinsic: usize,
        function: usize,
    },
    FunctionBodyOpenFreeVariable {
        binding: usize,
    },
    FunctionBodyUnresolvedMetavariable {
        binding: usize,
    },
    FunctionBodyLooseBoundVariables {
        binding: usize,
        range: u32,
        parameters: usize,
    },
    LambdaBindingNotLambda {
        binding: usize,
    },
    LambdaParameterCount {
        binding: usize,
        expected: usize,
        actual: usize,
    },
    LambdaOwnershipArity {
        binding: usize,
        parameters: usize,
        ownership: usize,
    },
    LambdaMutualGroupTooSmall {
        binding: usize,
        group: u32,
        members: u16,
    },
    LambdaMutualGroupMemberOutOfRange {
        binding: usize,
        group: u32,
        member: u16,
        members: u16,
    },
    LambdaMutualGroupMemberCountMismatch {
        binding: usize,
        group: u32,
        expected: u16,
        actual: u16,
    },
    DuplicateLambdaMutualGroupMember {
        group: u32,
        member: u16,
        first: usize,
        second: usize,
    },
    MissingLambdaMutualGroupMember {
        group: u32,
        member: u16,
        members: u16,
    },
    DuplicateLambdaBinding {
        lambda_hash: u64,
        first: usize,
        second: usize,
    },
    LambdaClosureTypeOutOfRange {
        binding: usize,
        parameter: Option<usize>,
        closure_type: fir::ClosureTypeId,
        known: usize,
    },
    UnknownLambda {
        lambda_hash: u64,
    },
    UnusedLambdaBinding {
        binding: usize,
        lambda_hash: u64,
    },
    LambdaApplicationOperandType {
        actual: fir::ValueType,
    },
    LambdaApplicationPartialClosureTypeMissing {
        closure_type: fir::ClosureTypeId,
        consumed: usize,
    },
    LambdaApplicationArgumentType {
        closure_type: fir::ClosureTypeId,
        argument: usize,
        expected: fir::ValueType,
        actual: fir::ValueType,
    },
    LambdaApplicationRemainderType {
        closure_type: fir::ClosureTypeId,
        argument: usize,
        actual: fir::ValueType,
    },
    LambdaResultType {
        binding: usize,
        expected: fir::ValueType,
        actual: fir::ValueType,
    },
    NatLiteralTooWide {
        limbs: usize,
    },
    NatLiteralOutOfAbiRange {
        value: u64,
        maximum: u64,
    },
    IdentifierWidth {
        table: &'static str,
        observed: usize,
    },
    MalformedResultState {
        phase: &'static str,
        expected: usize,
        observed: usize,
    },
    FirValidation(fir::ValidationError),
}

impl fmt::Display for IngressError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ResourceLimit {
                resource,
                limit,
                observed,
            } => write!(
                formatter,
                "core Expr ingress {} limit {limit} exceeded by {observed}",
                resource.token()
            ),
            Self::AllocationFailure {
                resource,
                requested,
            } => write!(
                formatter,
                "core Expr ingress could not reserve {requested} {}",
                resource.token()
            ),
            Self::OpenFreeVariable => {
                formatter.write_str("core Expr ingress requires no free variables")
            }
            Self::UnresolvedMetavariable => {
                formatter.write_str("core Expr ingress requires no expression metavariables")
            }
            Self::LooseBoundVariables { range } => write!(
                formatter,
                "core Expr ingress requires a closed de Bruijn term; loose range is {range}"
            ),
            Self::UnboundBoundVariable {
                index,
                context_depth,
            } => write!(
                formatter,
                "bound variable {index} is unavailable at context depth {context_depth}"
            ),
            Self::MissingCapturedBoundVariable {
                index,
                context_depth,
            } => write!(
                formatter,
                "capture analysis omitted bound variable {index} at context depth {context_depth}"
            ),
            Self::UnsupportedNode { kind } => {
                write!(
                    formatter,
                    "core Expr node {kind} is outside the executable subset"
                )
            }
            Self::UnknownConstant { name_hash } => write!(
                formatter,
                "core Expr constant with observable name hash {name_hash} is not in the runtime catalogs"
            ),
            Self::IntrinsicUniverseArity {
                name_hash,
                expected,
                actual,
            } => write!(
                formatter,
                "intrinsic constant with observable name hash {name_hash} expects {expected} universe arguments, observed {actual}"
            ),
            Self::IntrinsicTermArity {
                name_hash,
                expected,
                actual,
            } => write!(
                formatter,
                "intrinsic constant with observable name hash {name_hash} expects {expected} term arguments, observed {actual}"
            ),
            Self::IntrinsicArgumentType {
                name_hash,
                argument,
                expected,
                actual,
            } => write!(
                formatter,
                "intrinsic constant with observable name hash {name_hash} argument {argument} expects {expected:?}, observed {actual:?}"
            ),
            Self::ConstructorUniverseArity {
                name_hash,
                expected,
                actual,
            } => write!(
                formatter,
                "constructor constant with observable name hash {name_hash} expects {expected} universe arguments, observed {actual}"
            ),
            Self::ConstructorTermArity {
                name_hash,
                expected,
                actual,
            } => write!(
                formatter,
                "constructor constant with observable name hash {name_hash} expects {expected} term arguments, observed {actual}"
            ),
            Self::ConstructorArgumentType {
                name_hash,
                argument,
                expected,
                actual,
            } => write!(
                formatter,
                "constructor constant with observable name hash {name_hash} argument {argument} expects {expected:?}, observed {actual:?}"
            ),
            Self::FunctionUniverseArity {
                name_hash,
                expected,
                actual,
            } => write!(
                formatter,
                "function constant with observable name hash {name_hash} expects {expected} universe arguments, observed {actual}"
            ),
            Self::FunctionTermArity {
                name_hash,
                expected,
                actual,
            } => write!(
                formatter,
                "function constant with observable name hash {name_hash} expects {expected} term arguments, observed {actual}"
            ),
            Self::FunctionOwnershipArity {
                binding,
                parameters,
                ownership,
            } => write!(
                formatter,
                "function catalog binding {binding} has {parameters} typed parameters but {ownership} ownership dispositions"
            ),
            Self::FunctionArgumentType {
                name_hash,
                argument,
                expected,
                actual,
            } => write!(
                formatter,
                "function constant with observable name hash {name_hash} argument {argument} expects {expected:?}, observed {actual:?}"
            ),
            Self::FunctionResultType {
                name_hash,
                expected,
                actual,
            } => write!(
                formatter,
                "function constant with observable name hash {name_hash} declares result {expected:?}, observed {actual:?}"
            ),
            Self::InvalidIntrinsicRow { binding, row_bytes } => write!(
                formatter,
                "intrinsic catalog binding {binding} has a noncanonical {row_bytes}-byte row id"
            ),
            Self::IntrinsicOwnershipArity {
                binding,
                arguments,
                ownership,
            } => write!(
                formatter,
                "intrinsic catalog binding {binding} has {arguments} typed arguments but {ownership} ownership dispositions"
            ),
            Self::AnonymousIntrinsicName { binding } => write!(
                formatter,
                "intrinsic catalog binding {binding} has an anonymous source name"
            ),
            Self::DuplicateIntrinsicRow { first, second } => write!(
                formatter,
                "intrinsic catalog bindings {first} and {second} duplicate one row id"
            ),
            Self::DuplicateIntrinsicName {
                name_hash,
                first,
                second,
            } => write!(
                formatter,
                "intrinsic catalog bindings {first} and {second} duplicate source name hash {name_hash}"
            ),
            Self::AnonymousConstructorName { binding } => write!(
                formatter,
                "constructor catalog binding {binding} has an anonymous source name"
            ),
            Self::DuplicateConstructorName {
                name_hash,
                first,
                second,
            } => write!(
                formatter,
                "constructor catalog bindings {first} and {second} duplicate source name hash {name_hash}"
            ),
            Self::AnonymousProjectionStructureName { binding } => write!(
                formatter,
                "constructor catalog binding {binding} has an anonymous projection structure name"
            ),
            Self::DuplicateProjectionStructureName {
                name_hash,
                first,
                second,
            } => write!(
                formatter,
                "constructor catalog bindings {first} and {second} duplicate projection structure name hash {name_hash}"
            ),
            Self::UnknownProjection { name_hash, field } => write!(
                formatter,
                "structure projection with observable name hash {name_hash} and field {field} is absent"
            ),
            Self::ProjectionOperandType {
                name_hash,
                field,
                actual,
            } => write!(
                formatter,
                "structure projection with observable name hash {name_hash} and field {field} expects a constructor, observed {actual:?}"
            ),
            Self::ConstructorIntrinsicNameCollision {
                name_hash,
                constructor,
                intrinsic,
            } => write!(
                formatter,
                "constructor binding {constructor} and intrinsic binding {intrinsic} share source name hash {name_hash}"
            ),
            Self::ConstructorFunctionNameCollision {
                name_hash,
                constructor,
                function,
            } => write!(
                formatter,
                "constructor binding {constructor} and function binding {function} share source name hash {name_hash}"
            ),
            Self::AnonymousFunctionName { binding } => write!(
                formatter,
                "function catalog binding {binding} has an anonymous source name"
            ),
            Self::DuplicateFunctionName {
                name_hash,
                first,
                second,
            } => write!(
                formatter,
                "function catalog bindings {first} and {second} duplicate source name hash {name_hash}"
            ),
            Self::CallableNameCollision {
                name_hash,
                intrinsic,
                function,
            } => write!(
                formatter,
                "intrinsic binding {intrinsic} and function binding {function} share source name hash {name_hash}"
            ),
            Self::FunctionBodyOpenFreeVariable { binding } => write!(
                formatter,
                "function catalog binding {binding} body contains a free variable"
            ),
            Self::FunctionBodyUnresolvedMetavariable { binding } => write!(
                formatter,
                "function catalog binding {binding} body contains an expression metavariable"
            ),
            Self::FunctionBodyLooseBoundVariables {
                binding,
                range,
                parameters,
            } => write!(
                formatter,
                "function catalog binding {binding} body has loose de Bruijn range {range} for {parameters} parameters"
            ),
            Self::LambdaBindingNotLambda { binding } => write!(
                formatter,
                "lambda catalog binding {binding} does not start with a lambda"
            ),
            Self::LambdaParameterCount {
                binding,
                expected,
                actual,
            } => write!(
                formatter,
                "lambda catalog binding {binding} declares {expected} parameters for a {actual}-binder lambda spine"
            ),
            Self::LambdaOwnershipArity {
                binding,
                parameters,
                ownership,
            } => write!(
                formatter,
                "lambda catalog binding {binding} has {parameters} typed parameters but {ownership} ownership dispositions"
            ),
            Self::LambdaMutualGroupTooSmall {
                binding,
                group,
                members,
            } => write!(
                formatter,
                "lambda catalog binding {binding} declares mutual group {group} with {members} members; mutual groups require at least two"
            ),
            Self::LambdaMutualGroupMemberOutOfRange {
                binding,
                group,
                member,
                members,
            } => write!(
                formatter,
                "lambda catalog binding {binding} declares mutual group {group} member {member}, outside its {members}-member range"
            ),
            Self::LambdaMutualGroupMemberCountMismatch {
                binding,
                group,
                expected,
                actual,
            } => write!(
                formatter,
                "lambda catalog binding {binding} declares {actual} members for mutual group {group}; the group declares {expected}"
            ),
            Self::DuplicateLambdaMutualGroupMember {
                group,
                member,
                first,
                second,
            } => write!(
                formatter,
                "lambda catalog bindings {first} and {second} both declare mutual group {group} member {member}"
            ),
            Self::MissingLambdaMutualGroupMember {
                group,
                member,
                members,
            } => write!(
                formatter,
                "mutual lambda group {group} is missing member {member} of {members}"
            ),
            Self::DuplicateLambdaBinding {
                lambda_hash,
                first,
                second,
            } => write!(
                formatter,
                "lambda catalog bindings {first} and {second} duplicate expression hash {lambda_hash}"
            ),
            Self::LambdaClosureTypeOutOfRange {
                binding,
                parameter,
                closure_type,
                known,
            } => match parameter {
                Some(parameter) => write!(
                    formatter,
                    "lambda catalog binding {binding} parameter {parameter} references closure type {}, but the canonical table has {known} entries",
                    closure_type.get()
                ),
                None => write!(
                    formatter,
                    "lambda catalog binding {binding} result references closure type {}, but the canonical table has {known} entries",
                    closure_type.get()
                ),
            },
            Self::UnknownLambda { lambda_hash } => write!(
                formatter,
                "lambda expression hash {lambda_hash} has no exact runtime signature binding"
            ),
            Self::UnusedLambdaBinding {
                binding,
                lambda_hash,
            } => write!(
                formatter,
                "lambda catalog binding {binding} for expression hash {lambda_hash} was not used"
            ),
            Self::LambdaApplicationOperandType { actual } => write!(
                formatter,
                "dynamic core application expects a typed closure, observed {actual:?}"
            ),
            Self::LambdaApplicationPartialClosureTypeMissing {
                closure_type,
                consumed,
            } => write!(
                formatter,
                "closure type {} has no canonical suffix after {consumed} arguments",
                closure_type.get()
            ),
            Self::LambdaApplicationArgumentType {
                closure_type,
                argument,
                expected,
                actual,
            } => write!(
                formatter,
                "closure type {} argument {argument} expects {expected:?}, observed {actual:?}",
                closure_type.get()
            ),
            Self::LambdaApplicationRemainderType {
                closure_type,
                argument,
                actual,
            } => write!(
                formatter,
                "closure type {} returns {actual:?}, so argument {argument} has no closure to apply",
                closure_type.get()
            ),
            Self::LambdaResultType {
                binding,
                expected,
                actual,
            } => write!(
                formatter,
                "lambda catalog binding {binding} declares result {expected:?}, observed {actual:?}"
            ),
            Self::NatLiteralTooWide { limbs } => write!(
                formatter,
                "Nat literal has {limbs} limbs; large-Nat boxing is not implemented"
            ),
            Self::NatLiteralOutOfAbiRange { value, maximum } => write!(
                formatter,
                "Nat literal {value} exceeds the ABI scalar maximum {maximum}"
            ),
            Self::IdentifierWidth { table, observed } => {
                write!(formatter, "{table} index {observed} does not fit u32")
            }
            Self::MalformedResultState {
                phase,
                expected,
                observed,
            } => write!(
                formatter,
                "core Expr ingress result state at {phase} expected {expected}, observed {observed}"
            ),
            Self::FirValidation(error) => {
                write!(formatter, "generated FIR was refused: {error}")
            }
        }
    }
}

impl std::error::Error for IngressError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::FirValidation(error) => Some(error),
            _ => None,
        }
    }
}

impl From<fir::ValidationError> for IngressError {
    fn from(error: fir::ValidationError) -> Self {
        Self::FirValidation(error)
    }
}

/// Measured work facts bound to one successful ingress.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IngressWork {
    pub visited_nodes: usize,
    pub source_bindings: usize,
    pub capture_analysis_nodes: usize,
    pub captured_values: usize,
    pub elided_capture_slots: usize,
    pub intrinsic_calls: usize,
    pub constructor_calls: usize,
    pub projection_calls: usize,
    pub function_calls: usize,
    pub lambda_conversions: usize,
    pub recursive_self_closures: usize,
    pub mutual_group_closures: usize,
    pub closure_applications: usize,
    pub generated_constructors: usize,
    pub generated_projections: usize,
    pub generated_closure_types: usize,
    pub generated_functions: usize,
    pub function_parameters: usize,
    pub generated_values: usize,
    pub literal_bytes: usize,
    pub maximum_context_depth: usize,
}

/// One untrusted source-name binding supplied by the generated-contract owner.
///
/// Construction confers no authority. [`lower_closed_expr_with_intrinsics`]
/// canonicalizes the complete slice, rejects duplicate names and rows, retains
/// every supported effect class, and includes every declaration in FIR identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IntrinsicBinding {
    pub name: Name,
    pub universe_arity: usize,
    pub row: String,
    pub arguments: Vec<fir::ValueType>,
    pub argument_ownership: Vec<crate::flbc::ArgumentOwnership>,
    pub result: fir::ValueType,
    pub result_ownership: crate::flbc::ResultOwnership,
    pub effect: fir::EffectClass,
}

/// One untrusted source constructor and its already-erased runtime layout.
///
/// Every term argument becomes one ABI-valued object field in declaration
/// order. `static_scalar_bytes` is bound once in the FIR layout and applied to
/// every construction; it therefore supports only layouts whose packed scalar
/// payload is declaration static. Type/index erasure and dynamic scalar
/// extraction are intentionally outside this bounded checkpoint.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConstructorBinding {
    pub name: Name,
    /// Optional source structure name whose `ExprNode::Proj` indices address
    /// this constructor's object fields.
    pub projection_structure: Option<Name>,
    pub universe_arity: usize,
    pub tag: u8,
    pub fields: Vec<fir::ValueType>,
    pub static_scalar_bytes: Vec<u8>,
}

/// One untrusted first-order function supplied by the declaration owner.
///
/// `body` is already stripped of its top-level lambdas. Its loose de Bruijn
/// variables address `parameters` in declaration order, so index zero denotes
/// the final parameter. Construction confers no typing or executable authority:
/// [`lower_closed_expr_with_catalogs`] checks the complete catalog, compiles
/// every body, and publishes only FIR accepted by [`fir::validate`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionBinding {
    pub name: Name,
    pub universe_arity: usize,
    pub parameters: Vec<fir::ValueType>,
    pub parameter_ownership: Vec<crate::flbc::ArgumentOwnership>,
    pub result: fir::ValueType,
    pub result_ownership: crate::flbc::CallableResultOwnership,
    pub body: Expr,
}

/// How a local lambda's source spine represents recursion.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LambdaRecursion {
    /// Every source binder is an externally callable parameter.
    NonRecursive,
    /// The first source binder is the lambda's own closure.
    ///
    /// The self binder is not part of [`LambdaBinding::parameters`]. Closure
    /// conversion reconstructs it from the lifted target and that target's
    /// ordinary captures, so the resulting Marrow object graph is acyclic.
    SelfBinder,
    /// One canonical member of a finite mutually recursive closure group.
    ///
    /// Every member source spine begins with `members` synthetic closure
    /// binders in ascending `member` order. The current binding occupies its
    /// declared slot. Group metadata is untrusted and is checked for one
    /// complete, non-singleton slot set before any FIR is published.
    MutualMember {
        group: u32,
        member: u16,
        members: u16,
    },
}

impl LambdaRecursion {
    const fn synthetic_binders(self) -> usize {
        match self {
            Self::NonRecursive => 0,
            Self::SelfBinder => 1,
            Self::MutualMember { members, .. } => members as usize,
        }
    }
}

/// One exact local lambda spine and its reviewed runtime signature.
///
/// The `lambda` expression must begin with exactly `parameters.len()` contiguous
/// [`ExprNode::Lam`] nodes for [`LambdaRecursion::NonRecursive`], or one
/// synthetic self binder followed by those parameters for
/// [`LambdaRecursion::SelfBinder`]. A mutual member begins with the complete
/// ordered group binder set before its callable parameters. Binder-type
/// expressions remain metaprogram-visible source data and are not trusted as
/// runtime types here. `parameter_ownership` carries one reviewed callable
/// disposition per explicit parameter; ingress refuses an arity mismatch
/// instead of deriving ownership from source types. The explicit signature is
/// untrusted input checked against the generated FIR function and every
/// application. A
/// [`fir::ValueType::Closure`] entry names its position in the final
/// structurally sorted, deduplicated closure-type table, independent of
/// `LambdaBinding` input order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LambdaBinding {
    pub lambda: Expr,
    pub parameters: Vec<fir::ValueType>,
    pub parameter_ownership: Vec<crate::flbc::ArgumentOwnership>,
    pub result: fir::ValueType,
    pub result_ownership: crate::flbc::CallableResultOwnership,
    pub recursion: LambdaRecursion,
}

/// A core-expression checkpoint that has already passed FIR validation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IngressedProgram {
    source_expr_hash: u64,
    work: IngressWork,
    fir: fir::ValidatedProgram,
}

impl IngressedProgram {
    /// Reference-observable `Expr.hash`; this is not a cryptographic provenance root.
    pub const fn source_expr_hash(&self) -> u64 {
        self.source_expr_hash
    }

    pub const fn work(&self) -> IngressWork {
        self.work
    }

    pub const fn fir(&self) -> &fir::ValidatedProgram {
        &self.fir
    }

    pub fn into_fir(self) -> fir::ValidatedProgram {
        self.fir
    }
}

#[derive(Clone, Copy)]
struct CompiledValue {
    id: fir::ValueId,
    ty: fir::ValueType,
}

type CompiledContext = Vec<Option<CompiledValue>>;

struct PreparedIntrinsic {
    source_index: usize,
    name: Name,
    universe_arity: usize,
    declaration: fir::IntrinsicDecl,
}

struct PreparedConstructor {
    source_index: usize,
    name: Name,
    projection_structure: Option<Name>,
    universe_arity: usize,
    declaration: fir::ConstructorDecl,
}

struct PreparedProjection {
    structure_name: Name,
    source_field: u64,
    constructor_index: usize,
    declaration: fir::ProjectionDecl,
}

struct PreparedFunction<'a> {
    source_index: usize,
    name: Name,
    universe_arity: usize,
    id: fir::FunctionId,
    parameters: Vec<fir::ValueType>,
    parameter_ownership: Vec<crate::flbc::ArgumentOwnership>,
    result: fir::ValueType,
    result_ownership: crate::flbc::CallableResultOwnership,
    body: &'a Expr,
}

struct PreparedLambda<'a> {
    source_index: usize,
    lambda: &'a Expr,
    closure_type: fir::ClosureTypeId,
    parameters: Vec<fir::ValueType>,
    parameter_ownership: Vec<crate::flbc::ArgumentOwnership>,
    result: fir::ValueType,
    result_ownership: crate::flbc::CallableResultOwnership,
    recursion: LambdaRecursion,
}

struct PreparedMutualGroup {
    group: u32,
    members: Vec<usize>,
}

struct MutualGroupRow {
    group: u32,
    member: u16,
    members: u16,
    lambda: usize,
}

struct PreparedCatalog<'a> {
    constructors: Vec<PreparedConstructor>,
    constructors_by_name: Vec<usize>,
    projections: Vec<PreparedProjection>,
    entries: Vec<PreparedIntrinsic>,
    by_name: Vec<usize>,
    functions: Vec<PreparedFunction<'a>>,
    functions_by_name: Vec<usize>,
    lambdas: Vec<PreparedLambda<'a>>,
    lambdas_by_hash: Vec<usize>,
    mutual_groups: Vec<PreparedMutualGroup>,
    closure_types: Vec<fir::ClosureTypeDecl>,
}

#[derive(Clone, Copy)]
enum CallTarget {
    Constructor(usize),
    Intrinsic(usize),
    Function(usize),
}

enum Task<'a> {
    Eval(&'a Expr),
    EnterLetBody {
        body: &'a Expr,
        context_len: usize,
        result_len: usize,
    },
    LeaveLet {
        context_len: usize,
        result_len: usize,
    },
    FinishCall {
        target: CallTarget,
        argument_count: usize,
        result_len: usize,
    },
    FinishProjection {
        projection: usize,
        result_len: usize,
    },
    FinishApply {
        argument_count: usize,
        result_len: usize,
    },
}

struct LoweredBody {
    bindings: Vec<fir::Binding>,
    result: CompiledValue,
}

struct LowerBodySeed {
    context: CompiledContext,
    parameter_count: usize,
    bindings: Vec<fir::Binding>,
}

struct LambdaSpecialization {
    binding: usize,
    capture_types: Vec<fir::ValueType>,
    function: fir::FunctionId,
}

struct PendingLambda<'a> {
    binding: usize,
    function: fir::FunctionId,
    parameters: Vec<fir::ValueType>,
    parameter_ownership: Vec<crate::flbc::ArgumentOwnership>,
    context: CompiledContext,
    result: fir::ValueType,
    result_ownership: crate::flbc::CallableResultOwnership,
    body: &'a Expr,
    recursive_prologue: Option<RecursivePrologue>,
}

#[derive(Clone, Copy)]
struct RecursiveClosure {
    closure_type: fir::ClosureTypeId,
    function: fir::FunctionId,
}

struct RecursivePrologue {
    closures: Vec<RecursiveClosure>,
    capture_count: usize,
    mutual_group: bool,
}

struct ClosureBuild<'a> {
    used: Vec<bool>,
    specializations: Vec<LambdaSpecialization>,
    pending: VecDeque<PendingLambda<'a>>,
    next_function_index: usize,
}

fn charge(resource: IngressResource, observed: usize, limit: usize) -> Result<(), IngressError> {
    if observed > limit {
        return Err(IngressError::ResourceLimit {
            resource,
            limit,
            observed,
        });
    }
    Ok(())
}

fn increment(
    resource: IngressResource,
    current: usize,
    limit: usize,
) -> Result<usize, IngressError> {
    let observed = current.saturating_add(1);
    charge(resource, observed, limit)?;
    Ok(observed)
}

fn try_push<T>(
    values: &mut Vec<T>,
    value: T,
    resource: IngressResource,
    limit: usize,
) -> Result<(), IngressError> {
    let requested = values.len().saturating_add(1);
    charge(resource, requested, limit)?;
    values
        .try_reserve(1)
        .map_err(|_| IngressError::AllocationFailure {
            resource,
            requested,
        })?;
    values.push(value);
    Ok(())
}

fn charge_fir(
    resource: fir::ValidationResource,
    observed: usize,
    limit: usize,
) -> Result<(), IngressError> {
    if observed > limit {
        return Err(IngressError::FirValidation(
            fir::ValidationError::ResourceLimit {
                resource,
                limit,
                observed,
            },
        ));
    }
    Ok(())
}

fn clone_text(value: &str, resource: IngressResource) -> Result<String, IngressError> {
    let mut clone = String::new();
    clone
        .try_reserve_exact(value.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource,
            requested: value.len(),
        })?;
    clone.push_str(value);
    Ok(clone)
}

fn clone_string(value: &str) -> Result<String, IngressError> {
    clone_text(value, IngressResource::LiteralBytes)
}

fn clone_types(values: &[fir::ValueType]) -> Result<Vec<fir::ValueType>, IngressError> {
    let mut clone = Vec::new();
    clone
        .try_reserve_exact(values.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: values.len(),
        })?;
    clone.extend_from_slice(values);
    Ok(clone)
}

fn clone_argument_ownership(
    values: &[crate::flbc::ArgumentOwnership],
) -> Result<Vec<crate::flbc::ArgumentOwnership>, IngressError> {
    let mut clone = Vec::new();
    clone
        .try_reserve_exact(values.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: values.len(),
        })?;
    clone.extend_from_slice(values);
    Ok(clone)
}

fn borrowed_argument_ownership(
    count: usize,
) -> Result<Vec<crate::flbc::ArgumentOwnership>, IngressError> {
    let mut ownership = Vec::new();
    ownership
        .try_reserve_exact(count)
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: count,
        })?;
    ownership.resize(count, crate::flbc::ArgumentOwnership::Borrowed);
    Ok(ownership)
}

fn clone_bytes(values: &[u8]) -> Result<Vec<u8>, IngressError> {
    let mut clone = Vec::new();
    clone
        .try_reserve_exact(values.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: values.len(),
        })?;
    clone.extend_from_slice(values);
    Ok(clone)
}

fn emit_binding(
    bindings: &mut Vec<fir::Binding>,
    parameter_count: usize,
    ty: fir::ValueType,
    operation: fir::Operation,
    limits: IngressLimits,
) -> Result<CompiledValue, IngressError> {
    let observed = parameter_count
        .saturating_add(bindings.len())
        .saturating_add(1);
    charge_fir(
        fir::ValidationResource::Values,
        observed,
        limits.fir.max_values,
    )?;
    charge_fir(
        fir::ValidationResource::Operations,
        observed,
        limits.fir.max_operations,
    )?;
    let value_index = parameter_count.saturating_add(bindings.len());
    let raw = u32::try_from(value_index).map_err(|_| IngressError::IdentifierWidth {
        table: "FIR value",
        observed: value_index,
    })?;
    bindings
        .try_reserve(1)
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: observed,
        })?;
    let id = fir::ValueId::new(raw);
    bindings.push(fir::Binding { id, ty, operation });
    Ok(CompiledValue { id, ty })
}

fn coerce_abi_boundary(
    value: CompiledValue,
    expected: fir::ValueType,
    bindings: &mut Vec<fir::Binding>,
    parameter_count: usize,
    limits: IngressLimits,
) -> Result<Option<CompiledValue>, IngressError> {
    if value.ty == expected {
        return Ok(Some(value));
    }
    let operation = match (value.ty, expected) {
        (fir::ValueType::Abi, concrete) if concrete != fir::ValueType::Abi => {
            fir::Operation::Unbox {
                value: value.id,
                ty: concrete,
            }
        }
        (concrete, fir::ValueType::Abi) if concrete != fir::ValueType::Abi => {
            fir::Operation::Box(value.id)
        }
        _ => return Ok(None),
    };
    emit_binding(bindings, parameter_count, expected, operation, limits).map(Some)
}

fn emit_literal(
    literal: &Literal,
    bindings: &mut Vec<fir::Binding>,
    parameter_count: usize,
    literal_bytes: &mut usize,
    limits: IngressLimits,
) -> Result<CompiledValue, IngressError> {
    match literal {
        Literal::Nat(value) => {
            let scalar = value.to_u64().ok_or(IngressError::NatLiteralTooWide {
                limbs: value.limbs_le().len(),
            })?;
            let maximum = (usize::MAX >> 1) as u64;
            if scalar > maximum {
                return Err(IngressError::NatLiteralOutOfAbiRange {
                    value: scalar,
                    maximum,
                });
            }
            emit_binding(
                bindings,
                parameter_count,
                fir::ValueType::Nat,
                fir::Operation::Nat(scalar),
                limits,
            )
        }
        Literal::Str(value) => {
            let observed = literal_bytes.checked_add(value.len()).unwrap_or(usize::MAX);
            charge(
                IngressResource::LiteralBytes,
                observed,
                limits.max_literal_bytes,
            )?;
            charge_fir(
                fir::ValidationResource::LiteralBytes,
                observed,
                limits.fir.max_literal_bytes,
            )?;
            let value = clone_string(value)?;
            *literal_bytes = observed;
            emit_binding(
                bindings,
                parameter_count,
                fir::ValueType::String,
                fir::Operation::String(value),
                limits,
            )
        }
    }
}

fn singleton<T>(value: T) -> Result<Vec<T>, IngressError> {
    let mut values = Vec::new();
    values
        .try_reserve_exact(1)
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: 1,
        })?;
    values.push(value);
    Ok(values)
}

fn prepare_intrinsics<'a>(
    bindings: &[IntrinsicBinding],
    limits: IngressLimits,
) -> Result<PreparedCatalog<'a>, IngressError> {
    charge_fir(
        fir::ValidationResource::Intrinsics,
        bindings.len(),
        limits.fir.max_intrinsics,
    )?;

    let mut entries = Vec::new();
    entries
        .try_reserve_exact(bindings.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: bindings.len(),
        })?;
    let mut operands = 0usize;
    let mut row_bytes = 0usize;
    for (source_index, binding) in bindings.iter().enumerate() {
        if !fir::valid_extern_row(&binding.row) {
            return Err(IngressError::InvalidIntrinsicRow {
                binding: source_index,
                row_bytes: binding.row.len(),
            });
        }
        if binding.name.is_anonymous() {
            return Err(IngressError::AnonymousIntrinsicName {
                binding: source_index,
            });
        }
        if binding.arguments.len() != binding.argument_ownership.len() {
            return Err(IngressError::IntrinsicOwnershipArity {
                binding: source_index,
                arguments: binding.arguments.len(),
                ownership: binding.argument_ownership.len(),
            });
        }
        operands = operands.saturating_add(binding.arguments.len());
        charge_fir(
            fir::ValidationResource::Operands,
            operands,
            limits.fir.max_operands,
        )?;
        row_bytes = row_bytes.saturating_add(binding.row.len());
        charge_fir(
            fir::ValidationResource::LiteralBytes,
            row_bytes,
            limits.fir.max_literal_bytes,
        )?;
        entries.push(PreparedIntrinsic {
            source_index,
            name: binding.name.clone(),
            universe_arity: binding.universe_arity,
            declaration: fir::IntrinsicDecl {
                id: fir::IntrinsicId::new(0),
                row: clone_text(&binding.row, IngressResource::ProgramTables)?,
                arguments: clone_types(&binding.arguments)?,
                argument_ownership: clone_argument_ownership(&binding.argument_ownership)?,
                result: binding.result,
                result_ownership: binding.result_ownership,
                effect: binding.effect,
            },
        });
    }

    entries.sort_unstable_by(|left, right| left.declaration.row.cmp(&right.declaration.row));
    for pair in entries.windows(2) {
        if pair[0].declaration.row == pair[1].declaration.row {
            let first = pair[0].source_index.min(pair[1].source_index);
            let second = pair[0].source_index.max(pair[1].source_index);
            return Err(IngressError::DuplicateIntrinsicRow { first, second });
        }
    }
    for (index, entry) in entries.iter_mut().enumerate() {
        let raw = u32::try_from(index).map_err(|_| IngressError::IdentifierWidth {
            table: "FIR intrinsic",
            observed: index,
        })?;
        entry.declaration.id = fir::IntrinsicId::new(raw);
    }

    let mut by_name = Vec::new();
    by_name
        .try_reserve_exact(entries.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: entries.len(),
        })?;
    by_name.extend(0..entries.len());
    by_name.sort_unstable_by(|left, right| entries[*left].name.quick_cmp(&entries[*right].name));
    for pair in by_name.windows(2) {
        let left = &entries[pair[0]].name;
        let right = &entries[pair[1]].name;
        if left == right {
            let first = entries[pair[0]]
                .source_index
                .min(entries[pair[1]].source_index);
            let second = entries[pair[0]]
                .source_index
                .max(entries[pair[1]].source_index);
            return Err(IngressError::DuplicateIntrinsicName {
                name_hash: left.hash(),
                first,
                second,
            });
        }
    }

    Ok(PreparedCatalog {
        constructors: Vec::new(),
        constructors_by_name: Vec::new(),
        projections: Vec::new(),
        entries,
        by_name,
        functions: Vec::new(),
        functions_by_name: Vec::new(),
        lambdas: Vec::new(),
        lambdas_by_hash: Vec::new(),
        mutual_groups: Vec::new(),
        closure_types: Vec::new(),
    })
}

fn prepare_constructors(
    catalog: &mut PreparedCatalog<'_>,
    bindings: &[ConstructorBinding],
    limits: IngressLimits,
) -> Result<(), IngressError> {
    charge_fir(
        fir::ValidationResource::Constructors,
        bindings.len(),
        limits.fir.max_constructors,
    )?;
    catalog
        .constructors
        .try_reserve_exact(bindings.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: bindings.len(),
        })?;

    let mut operands = 0usize;
    let mut scalar_bytes = 0usize;
    for (source_index, binding) in bindings.iter().enumerate() {
        if binding.name.is_anonymous() {
            return Err(IngressError::AnonymousConstructorName {
                binding: source_index,
            });
        }
        if binding
            .projection_structure
            .as_ref()
            .is_some_and(Name::is_anonymous)
        {
            return Err(IngressError::AnonymousProjectionStructureName {
                binding: source_index,
            });
        }
        operands = operands.saturating_add(binding.fields.len());
        charge_fir(
            fir::ValidationResource::Operands,
            operands,
            limits.fir.max_operands,
        )?;
        scalar_bytes = scalar_bytes.saturating_add(binding.static_scalar_bytes.len());
        charge(
            IngressResource::LiteralBytes,
            scalar_bytes,
            limits.max_literal_bytes,
        )?;
        catalog.constructors.push(PreparedConstructor {
            source_index,
            name: binding.name.clone(),
            projection_structure: binding.projection_structure.clone(),
            universe_arity: binding.universe_arity,
            declaration: fir::ConstructorDecl {
                id: fir::ConstructorId::new(0),
                tag: binding.tag,
                fields: clone_types(&binding.fields)?,
                static_scalar_bytes: clone_bytes(&binding.static_scalar_bytes)?,
            },
        });
    }

    catalog
        .constructors
        .sort_unstable_by(|left, right| left.name.quick_cmp(&right.name));
    for pair in catalog.constructors.windows(2) {
        if pair[0].name == pair[1].name {
            let first = pair[0].source_index.min(pair[1].source_index);
            let second = pair[0].source_index.max(pair[1].source_index);
            return Err(IngressError::DuplicateConstructorName {
                name_hash: pair[0].name.hash(),
                first,
                second,
            });
        }
    }
    for (index, constructor) in catalog.constructors.iter_mut().enumerate() {
        let raw = u32::try_from(index).map_err(|_| IngressError::IdentifierWidth {
            table: "FIR constructor",
            observed: index,
        })?;
        constructor.declaration.id = fir::ConstructorId::new(raw);
    }

    let mut projection_constructors = Vec::new();
    projection_constructors
        .try_reserve_exact(catalog.constructors.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: catalog.constructors.len(),
        })?;
    projection_constructors.extend(catalog.constructors.iter().enumerate().filter_map(
        |(index, constructor)| {
            constructor
                .projection_structure
                .as_ref()
                .map(|name| (name.clone(), index))
        },
    ));
    projection_constructors.sort_unstable_by(|left, right| left.0.quick_cmp(&right.0));
    for pair in projection_constructors.windows(2) {
        if pair[0].0 == pair[1].0 {
            let left = &catalog.constructors[pair[0].1];
            let right = &catalog.constructors[pair[1].1];
            let first = left.source_index.min(right.source_index);
            let second = left.source_index.max(right.source_index);
            return Err(IngressError::DuplicateProjectionStructureName {
                name_hash: pair[0].0.hash(),
                first,
                second,
            });
        }
    }
    let projection_count =
        projection_constructors
            .iter()
            .fold(0usize, |total, (_, constructor_index)| {
                total.saturating_add(
                    catalog.constructors[*constructor_index]
                        .declaration
                        .fields
                        .len(),
                )
            });
    charge_fir(
        fir::ValidationResource::Projections,
        projection_count,
        limits.fir.max_projections,
    )?;
    catalog
        .projections
        .try_reserve_exact(projection_count)
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: projection_count,
        })?;
    for (structure_name, constructor_index) in projection_constructors {
        let constructor = &catalog.constructors[constructor_index];
        for field in 0..constructor.declaration.fields.len() {
            let source_field = u64::try_from(field).map_err(|_| IngressError::IdentifierWidth {
                table: "source projection field",
                observed: field,
            })?;
            let field = u16::try_from(field).map_err(|_| IngressError::IdentifierWidth {
                table: "FIR projection field",
                observed: field,
            })?;
            let id = u32::try_from(catalog.projections.len()).map_err(|_| {
                IngressError::IdentifierWidth {
                    table: "FIR projection",
                    observed: catalog.projections.len(),
                }
            })?;
            catalog.projections.push(PreparedProjection {
                structure_name: structure_name.clone(),
                source_field,
                constructor_index,
                declaration: fir::ProjectionDecl {
                    id: fir::ProjectionId::new(id),
                    constructor: constructor.declaration.id,
                    field,
                },
            });
        }
    }

    catalog
        .constructors_by_name
        .try_reserve_exact(catalog.constructors.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: catalog.constructors.len(),
        })?;
    catalog
        .constructors_by_name
        .extend(0..catalog.constructors.len());
    for index in &catalog.constructors_by_name {
        let constructor = &catalog.constructors[*index];
        if let Some(intrinsic_index) = catalog.resolve_intrinsic(&constructor.name) {
            return Err(IngressError::ConstructorIntrinsicNameCollision {
                name_hash: constructor.name.hash(),
                constructor: constructor.source_index,
                intrinsic: catalog.entries[intrinsic_index].source_index,
            });
        }
    }
    Ok(())
}

impl PreparedCatalog<'_> {
    fn resolve_constructor(&self, name: &Name) -> Option<usize> {
        self.constructors_by_name
            .binary_search_by(|index| self.constructors[*index].name.quick_cmp(name))
            .ok()
            .and_then(|position| self.constructors_by_name.get(position).copied())
    }

    fn resolve_projection(&self, structure_name: &Name, field: u64) -> Option<usize> {
        self.projections
            .binary_search_by(|projection| {
                projection
                    .structure_name
                    .quick_cmp(structure_name)
                    .then_with(|| projection.source_field.cmp(&field))
            })
            .ok()
    }

    fn resolve_intrinsic(&self, name: &Name) -> Option<usize> {
        self.by_name
            .binary_search_by(|index| self.entries[*index].name.quick_cmp(name))
            .ok()
            .and_then(|position| self.by_name.get(position).copied())
    }

    fn resolve_function(&self, name: &Name) -> Option<usize> {
        self.functions_by_name
            .binary_search_by(|index| self.functions[*index].name.quick_cmp(name))
            .ok()
            .and_then(|position| self.functions_by_name.get(position).copied())
    }

    fn resolve_lambda(&self, lambda: &Expr) -> Option<usize> {
        let hash = lambda.hash();
        let start = self
            .lambdas_by_hash
            .partition_point(|index| self.lambdas[*index].lambda.hash() < hash);
        self.lambdas_by_hash[start..]
            .iter()
            .copied()
            .take_while(|index| self.lambdas[*index].lambda.hash() == hash)
            .find(|index| self.lambdas[*index].lambda == lambda)
    }

    fn resolve_mutual_group(&self, group: u32) -> Option<&PreparedMutualGroup> {
        self.mutual_groups
            .binary_search_by_key(&group, |candidate| candidate.group)
            .ok()
            .and_then(|index| self.mutual_groups.get(index))
    }
}

fn lambda_spine(lambda: &Expr) -> Option<(usize, &Expr)> {
    let mut binders = 0usize;
    let mut body = lambda;
    while let ExprNode::Lam {
        body: next_body, ..
    } = body.node()
    {
        binders = binders.saturating_add(1);
        body = next_body;
    }
    (binders != 0).then_some((binders, body))
}

fn prepare_lambdas<'a>(
    catalog: &mut PreparedCatalog<'a>,
    bindings: &'a [LambdaBinding],
    limits: IngressLimits,
) -> Result<(), IngressError> {
    charge(
        IngressResource::LambdaBindings,
        bindings.len(),
        limits.max_lambda_bindings,
    )?;
    catalog
        .lambdas
        .try_reserve_exact(bindings.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: bindings.len(),
        })?;
    for (source_index, binding) in bindings.iter().enumerate() {
        let Some((binder_count, _)) = lambda_spine(&binding.lambda) else {
            return Err(IngressError::LambdaBindingNotLambda {
                binding: source_index,
            });
        };
        let expected_binders = binding
            .parameters
            .len()
            .saturating_add(binding.recursion.synthetic_binders());
        if expected_binders != binder_count {
            return Err(IngressError::LambdaParameterCount {
                binding: source_index,
                expected: expected_binders,
                actual: binder_count,
            });
        }
        if binding.parameters.len() != binding.parameter_ownership.len() {
            return Err(IngressError::LambdaOwnershipArity {
                binding: source_index,
                parameters: binding.parameters.len(),
                ownership: binding.parameter_ownership.len(),
            });
        }
        catalog.lambdas.push(PreparedLambda {
            source_index,
            lambda: &binding.lambda,
            closure_type: fir::ClosureTypeId::new(0),
            parameters: clone_types(&binding.parameters)?,
            parameter_ownership: clone_argument_ownership(&binding.parameter_ownership)?,
            result: binding.result,
            result_ownership: binding.result_ownership,
            recursion: binding.recursion,
        });
    }

    let mut mutual_rows = Vec::new();
    mutual_rows
        .try_reserve_exact(catalog.lambdas.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: catalog.lambdas.len(),
        })?;
    for (lambda, binding) in catalog.lambdas.iter().enumerate() {
        let LambdaRecursion::MutualMember {
            group,
            member,
            members,
        } = binding.recursion
        else {
            continue;
        };
        if members < 2 {
            return Err(IngressError::LambdaMutualGroupTooSmall {
                binding: binding.source_index,
                group,
                members,
            });
        }
        if member >= members {
            return Err(IngressError::LambdaMutualGroupMemberOutOfRange {
                binding: binding.source_index,
                group,
                member,
                members,
            });
        }
        mutual_rows.push(MutualGroupRow {
            group,
            member,
            members,
            lambda,
        });
    }
    mutual_rows.sort_unstable_by(|left, right| {
        left.group
            .cmp(&right.group)
            .then_with(|| left.member.cmp(&right.member))
            .then_with(|| {
                catalog.lambdas[left.lambda]
                    .source_index
                    .cmp(&catalog.lambdas[right.lambda].source_index)
            })
    });
    let mut group_start = 0usize;
    while group_start < mutual_rows.len() {
        let group = mutual_rows[group_start].group;
        let group_end = mutual_rows[group_start..]
            .partition_point(|row| row.group == group)
            .saturating_add(group_start);
        let members = mutual_rows[group_start].members;
        for row in &mutual_rows[group_start..group_end] {
            if row.members != members {
                return Err(IngressError::LambdaMutualGroupMemberCountMismatch {
                    binding: catalog.lambdas[row.lambda].source_index,
                    group,
                    expected: members,
                    actual: row.members,
                });
            }
        }
        let mut prepared_members = Vec::new();
        prepared_members
            .try_reserve_exact(usize::from(members))
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: usize::from(members),
            })?;
        let mut cursor = group_start;
        for member in 0..members {
            let Some(row) = mutual_rows
                .get(cursor)
                .filter(|row| cursor < group_end && row.group == group && row.member == member)
            else {
                return Err(IngressError::MissingLambdaMutualGroupMember {
                    group,
                    member,
                    members,
                });
            };
            if let Some(duplicate) = mutual_rows
                .get(cursor.saturating_add(1))
                .filter(|next| cursor.saturating_add(1) < group_end && next.member == member)
            {
                let first = catalog.lambdas[row.lambda].source_index;
                let second = catalog.lambdas[duplicate.lambda].source_index;
                return Err(IngressError::DuplicateLambdaMutualGroupMember {
                    group,
                    member,
                    first: first.min(second),
                    second: first.max(second),
                });
            }
            prepared_members.push(row.lambda);
            cursor = cursor.saturating_add(1);
        }
        if cursor != group_end {
            let row = &mutual_rows[cursor];
            return Err(IngressError::DuplicateLambdaMutualGroupMember {
                group,
                member: row.member,
                first: catalog.lambdas[mutual_rows[cursor.saturating_sub(1)].lambda].source_index,
                second: catalog.lambdas[row.lambda].source_index,
            });
        }
        catalog.mutual_groups.push(PreparedMutualGroup {
            group,
            members: prepared_members,
        });
        group_start = group_end;
    }

    catalog
        .lambdas_by_hash
        .try_reserve_exact(catalog.lambdas.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: catalog.lambdas.len(),
        })?;
    catalog.lambdas_by_hash.extend(0..catalog.lambdas.len());
    catalog.lambdas_by_hash.sort_unstable_by(|left, right| {
        catalog.lambdas[*left]
            .lambda
            .hash()
            .cmp(&catalog.lambdas[*right].lambda.hash())
            .then_with(|| {
                catalog.lambdas[*left]
                    .source_index
                    .cmp(&catalog.lambdas[*right].source_index)
            })
    });
    let mut group_start = 0usize;
    while group_start < catalog.lambdas_by_hash.len() {
        let hash = catalog.lambdas[catalog.lambdas_by_hash[group_start]]
            .lambda
            .hash();
        let group_end = catalog.lambdas_by_hash[group_start..]
            .partition_point(|index| catalog.lambdas[*index].lambda.hash() == hash)
            .saturating_add(group_start);
        for left in group_start..group_end {
            for right in left.saturating_add(1)..group_end {
                let first = catalog.lambdas_by_hash[left];
                let second = catalog.lambdas_by_hash[right];
                if catalog.lambdas[first].lambda == catalog.lambdas[second].lambda {
                    return Err(IngressError::DuplicateLambdaBinding {
                        lambda_hash: hash,
                        first: catalog.lambdas[first].source_index,
                        second: catalog.lambdas[second].source_index,
                    });
                }
            }
        }
        group_start = group_end;
    }

    for lambda in &catalog.lambdas {
        for suffix_start in 0..lambda.parameters.len() {
            let observed = catalog.closure_types.len().saturating_add(1);
            charge_fir(
                fir::ValidationResource::ClosureTypes,
                observed,
                limits.fir.max_closure_types,
            )?;
            catalog
                .closure_types
                .try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: observed,
                })?;
            catalog.closure_types.push(fir::ClosureTypeDecl {
                id: fir::ClosureTypeId::new(0),
                parameters: clone_types(&lambda.parameters[suffix_start..])?,
                parameter_ownership: clone_argument_ownership(
                    &lambda.parameter_ownership[suffix_start..],
                )?,
                result: lambda.result,
                result_ownership: lambda.result_ownership,
            });
        }
    }
    catalog.closure_types.sort_unstable_by(|left, right| {
        left.parameters
            .cmp(&right.parameters)
            .then_with(|| left.parameter_ownership.cmp(&right.parameter_ownership))
            .then_with(|| left.result.cmp(&right.result))
            .then_with(|| left.result_ownership.cmp(&right.result_ownership))
    });
    catalog.closure_types.dedup_by(|left, right| {
        left.parameters == right.parameters
            && left.parameter_ownership == right.parameter_ownership
            && left.result == right.result
            && left.result_ownership == right.result_ownership
    });
    charge_fir(
        fir::ValidationResource::ClosureTypes,
        catalog.closure_types.len(),
        limits.fir.max_closure_types,
    )?;
    let known_closure_types = catalog.closure_types.len();
    for lambda in &catalog.lambdas {
        for (parameter, ty) in lambda.parameters.iter().copied().enumerate() {
            if let fir::ValueType::Closure(closure_type) = ty
                && usize::try_from(closure_type.get())
                    .ok()
                    .is_none_or(|index| index >= known_closure_types)
            {
                return Err(IngressError::LambdaClosureTypeOutOfRange {
                    binding: lambda.source_index,
                    parameter: Some(parameter),
                    closure_type,
                    known: known_closure_types,
                });
            }
        }
        if let fir::ValueType::Closure(closure_type) = lambda.result
            && usize::try_from(closure_type.get())
                .ok()
                .is_none_or(|index| index >= known_closure_types)
        {
            return Err(IngressError::LambdaClosureTypeOutOfRange {
                binding: lambda.source_index,
                parameter: None,
                closure_type,
                known: known_closure_types,
            });
        }
    }
    let mut signature_operands = 0usize;
    for (index, closure_type) in catalog.closure_types.iter_mut().enumerate() {
        let raw = u32::try_from(index).map_err(|_| IngressError::IdentifierWidth {
            table: "FIR closure type",
            observed: index,
        })?;
        closure_type.id = fir::ClosureTypeId::new(raw);
        signature_operands = signature_operands
            .saturating_add(closure_type.parameters.len())
            .saturating_add(closure_type.parameter_ownership.len());
        charge_fir(
            fir::ValidationResource::Operands,
            signature_operands,
            limits.fir.max_operands,
        )?;
    }
    for lambda in &mut catalog.lambdas {
        let position = catalog
            .closure_types
            .binary_search_by(|closure_type| {
                closure_type
                    .parameters
                    .cmp(&lambda.parameters)
                    .then_with(|| {
                        closure_type
                            .parameter_ownership
                            .cmp(&lambda.parameter_ownership)
                    })
                    .then_with(|| closure_type.result.cmp(&lambda.result))
                    .then_with(|| closure_type.result_ownership.cmp(&lambda.result_ownership))
            })
            .map_err(|_| IngressError::MalformedResultState {
                phase: "lambda closure type lookup",
                expected: catalog.closure_types.len(),
                observed: usize::MAX,
            })?;
        lambda.closure_type = catalog.closure_types[position].id;
    }
    Ok(())
}

fn prepare_catalog<'a>(
    intrinsics: &[IntrinsicBinding],
    constructors: &[ConstructorBinding],
    functions: &'a [FunctionBinding],
    lambdas: &'a [LambdaBinding],
    limits: IngressLimits,
) -> Result<PreparedCatalog<'a>, IngressError> {
    let function_count = functions.len().saturating_add(1);
    charge_fir(
        fir::ValidationResource::Functions,
        function_count,
        limits.fir.max_functions,
    )?;
    let mut catalog = prepare_intrinsics(intrinsics, limits)?;
    prepare_constructors(&mut catalog, constructors, limits)?;
    catalog
        .functions
        .try_reserve_exact(functions.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: functions.len(),
        })?;

    let mut parameter_count = 0usize;
    for (source_index, binding) in functions.iter().enumerate() {
        if binding.name.is_anonymous() {
            return Err(IngressError::AnonymousFunctionName {
                binding: source_index,
            });
        }
        if binding.body.has_fvar() {
            return Err(IngressError::FunctionBodyOpenFreeVariable {
                binding: source_index,
            });
        }
        if binding.body.has_expr_mvar() {
            return Err(IngressError::FunctionBodyUnresolvedMetavariable {
                binding: source_index,
            });
        }
        if binding.parameters.len() != binding.parameter_ownership.len() {
            return Err(IngressError::FunctionOwnershipArity {
                binding: source_index,
                parameters: binding.parameters.len(),
                ownership: binding.parameter_ownership.len(),
            });
        }
        let parameter_range =
            u32::try_from(binding.parameters.len()).map_err(|_| IngressError::IdentifierWidth {
                table: "function parameter",
                observed: binding.parameters.len(),
            })?;
        let loose_range = binding.body.loose_bvar_range();
        if loose_range > parameter_range {
            return Err(IngressError::FunctionBodyLooseBoundVariables {
                binding: source_index,
                range: loose_range,
                parameters: binding.parameters.len(),
            });
        }
        charge(
            IngressResource::ContextDepth,
            binding.parameters.len(),
            limits.max_context_depth,
        )?;
        parameter_count = parameter_count.saturating_add(binding.parameters.len());
        charge_fir(
            fir::ValidationResource::Operands,
            parameter_count.saturating_mul(2),
            limits.fir.max_operands,
        )?;
        charge_fir(
            fir::ValidationResource::Values,
            parameter_count,
            limits.fir.max_values,
        )?;
        catalog.functions.push(PreparedFunction {
            source_index,
            name: binding.name.clone(),
            universe_arity: binding.universe_arity,
            id: fir::FunctionId::new(0),
            parameters: clone_types(&binding.parameters)?,
            parameter_ownership: clone_argument_ownership(&binding.parameter_ownership)?,
            result: binding.result,
            result_ownership: binding.result_ownership,
            body: &binding.body,
        });
    }

    catalog
        .functions
        .sort_unstable_by(|left, right| left.name.quick_cmp(&right.name));
    for pair in catalog.functions.windows(2) {
        if pair[0].name == pair[1].name {
            let first = pair[0].source_index.min(pair[1].source_index);
            let second = pair[0].source_index.max(pair[1].source_index);
            return Err(IngressError::DuplicateFunctionName {
                name_hash: pair[0].name.hash(),
                first,
                second,
            });
        }
    }
    for (index, function) in catalog.functions.iter_mut().enumerate() {
        let table_index = index.saturating_add(1);
        let raw = u32::try_from(table_index).map_err(|_| IngressError::IdentifierWidth {
            table: "FIR function",
            observed: table_index,
        })?;
        function.id = fir::FunctionId::new(raw);
    }

    catalog
        .functions_by_name
        .try_reserve_exact(catalog.functions.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: catalog.functions.len(),
        })?;
    catalog.functions_by_name.extend(0..catalog.functions.len());
    for index in &catalog.functions_by_name {
        let function = &catalog.functions[*index];
        if let Some(intrinsic_index) = catalog.resolve_intrinsic(&function.name) {
            return Err(IngressError::CallableNameCollision {
                name_hash: function.name.hash(),
                intrinsic: catalog.entries[intrinsic_index].source_index,
                function: function.source_index,
            });
        }
        if let Some(constructor_index) = catalog.resolve_constructor(&function.name) {
            return Err(IngressError::ConstructorFunctionNameCollision {
                name_hash: function.name.hash(),
                constructor: catalog.constructors[constructor_index].source_index,
                function: function.source_index,
            });
        }
    }
    prepare_lambdas(&mut catalog, lambdas, limits)?;

    Ok(catalog)
}

struct ScheduledCall<'a> {
    target: CallTarget,
    arguments: Vec<&'a Expr>,
}

fn resolve_call<'a>(
    name: &Name,
    universe_arity: usize,
    arguments: Vec<&'a Expr>,
    catalog: &PreparedCatalog<'_>,
) -> Result<ScheduledCall<'a>, IngressError> {
    let name_hash = name.hash();
    if let Some(binding_index) = catalog.resolve_intrinsic(name) {
        let binding = &catalog.entries[binding_index];
        if universe_arity != binding.universe_arity {
            return Err(IngressError::IntrinsicUniverseArity {
                name_hash,
                expected: binding.universe_arity,
                actual: universe_arity,
            });
        }
        if arguments.len() != binding.declaration.arguments.len() {
            return Err(IngressError::IntrinsicTermArity {
                name_hash,
                expected: binding.declaration.arguments.len(),
                actual: arguments.len(),
            });
        }
        return Ok(ScheduledCall {
            target: CallTarget::Intrinsic(binding_index),
            arguments,
        });
    }
    if let Some(binding_index) = catalog.resolve_constructor(name) {
        let binding = &catalog.constructors[binding_index];
        if universe_arity != binding.universe_arity {
            return Err(IngressError::ConstructorUniverseArity {
                name_hash,
                expected: binding.universe_arity,
                actual: universe_arity,
            });
        }
        if arguments.len() != binding.declaration.fields.len() {
            return Err(IngressError::ConstructorTermArity {
                name_hash,
                expected: binding.declaration.fields.len(),
                actual: arguments.len(),
            });
        }
        return Ok(ScheduledCall {
            target: CallTarget::Constructor(binding_index),
            arguments,
        });
    }
    if let Some(binding_index) = catalog.resolve_function(name) {
        let binding = &catalog.functions[binding_index];
        if universe_arity != binding.universe_arity {
            return Err(IngressError::FunctionUniverseArity {
                name_hash,
                expected: binding.universe_arity,
                actual: universe_arity,
            });
        }
        if arguments.len() != binding.parameters.len() {
            return Err(IngressError::FunctionTermArity {
                name_hash,
                expected: binding.parameters.len(),
                actual: arguments.len(),
            });
        }
        return Ok(ScheduledCall {
            target: CallTarget::Function(binding_index),
            arguments,
        });
    }
    Err(IngressError::UnknownConstant { name_hash })
}

fn malformed(phase: &'static str, expected: usize, observed: usize) -> IngressError {
    IngressError::MalformedResultState {
        phase,
        expected,
        observed,
    }
}

fn capture_set(
    body: &Expr,
    binder_count: usize,
    context: &[Option<CompiledValue>],
    limits: IngressLimits,
    work: &mut IngressWork,
) -> Result<Vec<bool>, IngressError> {
    let initial_depth = context.len().saturating_add(binder_count);
    charge(
        IngressResource::ContextDepth,
        initial_depth,
        limits.max_context_depth,
    )?;
    let mut captures = Vec::new();
    captures
        .try_reserve_exact(context.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::CaptureAnalysisNodes,
            requested: context.len(),
        })?;
    captures.resize(context.len(), false);

    let mut pending = Vec::new();
    try_push(
        &mut pending,
        (body, binder_count),
        IngressResource::CaptureAnalysisNodes,
        limits.max_capture_analysis_nodes,
    )?;
    while let Some((expr, local_depth)) = pending.pop() {
        work.capture_analysis_nodes = increment(
            IngressResource::CaptureAnalysisNodes,
            work.capture_analysis_nodes,
            limits.max_capture_analysis_nodes,
        )?;
        match expr.node() {
            ExprNode::BVar { idx } => {
                let index =
                    usize::try_from(*idx).map_err(|_| IngressError::UnboundBoundVariable {
                        index: *idx,
                        context_depth: context.len().saturating_add(local_depth),
                    })?;
                if index < local_depth {
                    continue;
                }
                let outer_index = index.saturating_sub(local_depth);
                let Some(offset) = context.len().checked_sub(outer_index.saturating_add(1)) else {
                    return Err(IngressError::UnboundBoundVariable {
                        index: *idx,
                        context_depth: context.len().saturating_add(local_depth),
                    });
                };
                let capture =
                    captures
                        .get_mut(offset)
                        .ok_or(IngressError::UnboundBoundVariable {
                            index: *idx,
                            context_depth: context.len().saturating_add(local_depth),
                        })?;
                *capture = true;
            }
            ExprNode::App { f, a } => {
                try_push(
                    &mut pending,
                    (f, local_depth),
                    IngressResource::CaptureAnalysisNodes,
                    limits.max_capture_analysis_nodes,
                )?;
                try_push(
                    &mut pending,
                    (a, local_depth),
                    IngressResource::CaptureAnalysisNodes,
                    limits.max_capture_analysis_nodes,
                )?;
            }
            ExprNode::Lam { body, .. } => {
                let nested_depth = local_depth.saturating_add(1);
                charge(
                    IngressResource::ContextDepth,
                    context.len().saturating_add(nested_depth),
                    limits.max_context_depth,
                )?;
                try_push(
                    &mut pending,
                    (body, nested_depth),
                    IngressResource::CaptureAnalysisNodes,
                    limits.max_capture_analysis_nodes,
                )?;
            }
            ExprNode::LetE { value, body, .. } => {
                try_push(
                    &mut pending,
                    (value, local_depth),
                    IngressResource::CaptureAnalysisNodes,
                    limits.max_capture_analysis_nodes,
                )?;
                let nested_depth = local_depth.saturating_add(1);
                charge(
                    IngressResource::ContextDepth,
                    context.len().saturating_add(nested_depth),
                    limits.max_context_depth,
                )?;
                try_push(
                    &mut pending,
                    (body, nested_depth),
                    IngressResource::CaptureAnalysisNodes,
                    limits.max_capture_analysis_nodes,
                )?;
            }
            ExprNode::MData { expr, .. } => {
                try_push(
                    &mut pending,
                    (expr, local_depth),
                    IngressResource::CaptureAnalysisNodes,
                    limits.max_capture_analysis_nodes,
                )?;
            }
            ExprNode::Proj { expr, .. } => {
                try_push(
                    &mut pending,
                    (expr, local_depth),
                    IngressResource::CaptureAnalysisNodes,
                    limits.max_capture_analysis_nodes,
                )?;
            }
            ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Const { .. }
            | ExprNode::ForallE { .. }
            | ExprNode::Lit { .. } => {}
        }
    }
    Ok(captures)
}

impl<'a> ClosureBuild<'a> {
    fn new(catalog: &PreparedCatalog<'a>) -> Result<Self, IngressError> {
        let mut used = Vec::new();
        used.try_reserve_exact(catalog.lambdas.len()).map_err(|_| {
            IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: catalog.lambdas.len(),
            }
        })?;
        used.resize(catalog.lambdas.len(), false);
        Ok(Self {
            used,
            specializations: Vec::new(),
            pending: VecDeque::new(),
            next_function_index: catalog.functions.len().saturating_add(1),
        })
    }

    fn schedule(
        &mut self,
        lambda: &'a Expr,
        context: &[Option<CompiledValue>],
        catalog: &PreparedCatalog<'a>,
        limits: IngressLimits,
        work: &mut IngressWork,
    ) -> Result<(fir::ClosureTypeId, fir::FunctionId, Vec<fir::ValueId>), IngressError> {
        let binding_index = catalog
            .resolve_lambda(lambda)
            .ok_or(IngressError::UnknownLambda {
                lambda_hash: lambda.hash(),
            })?;
        let binding =
            catalog
                .lambdas
                .get(binding_index)
                .ok_or(IngressError::MalformedResultState {
                    phase: "lambda catalog lookup",
                    expected: catalog.lambdas.len(),
                    observed: binding_index,
                })?;
        let Some((binder_count, body)) = lambda_spine(lambda) else {
            return Err(IngressError::MalformedResultState {
                phase: "lambda spine lookup",
                expected: binding
                    .parameters
                    .len()
                    .saturating_add(binding.recursion.synthetic_binders()),
                observed: 0,
            });
        };
        let expected_binders = binding
            .parameters
            .len()
            .saturating_add(binding.recursion.synthetic_binders());
        if binder_count != expected_binders {
            return Err(IngressError::MalformedResultState {
                phase: "lambda spine width",
                expected: expected_binders,
                observed: binder_count,
            });
        }
        if matches!(binding.recursion, LambdaRecursion::MutualMember { .. }) {
            return self.schedule_mutual_group(binding_index, context, catalog, limits, work);
        }
        let used_count = self.used.len();
        let used = self
            .used
            .get_mut(binding_index)
            .ok_or(IngressError::MalformedResultState {
                phase: "lambda use lookup",
                expected: used_count,
                observed: binding_index,
            })?;
        *used = true;

        let selected = capture_set(body, binder_count, context, limits, work)?;
        let available_captures = context.iter().filter(|value| value.is_some()).count();
        let selected_count = selected.iter().filter(|capture| **capture).count();
        let mut capture_types = Vec::new();
        let mut captures = Vec::new();
        capture_types
            .try_reserve_exact(selected_count)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: selected_count,
            })?;
        captures.try_reserve_exact(selected_count).map_err(|_| {
            IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: selected_count,
            }
        })?;
        for (offset, (selected, value)) in selected.iter().zip(context).enumerate() {
            if !selected {
                continue;
            }
            let Some(value) = *value else {
                let outer_index = context.len().saturating_sub(offset.saturating_add(1));
                let source_index = binder_count.saturating_add(outer_index);
                let index =
                    u32::try_from(source_index).map_err(|_| IngressError::IdentifierWidth {
                        table: "captured de Bruijn index",
                        observed: source_index,
                    })?;
                return Err(IngressError::MissingCapturedBoundVariable {
                    index,
                    context_depth: context.len().saturating_add(binder_count),
                });
            };
            capture_types.push(value.ty);
            captures.push(value.id);
        }
        work.captured_values = work.captured_values.saturating_add(captures.len());
        work.elided_capture_slots = work
            .elided_capture_slots
            .saturating_add(available_captures.saturating_sub(captures.len()));

        let function = if let Some(existing) = self.specializations.iter().find(|existing| {
            existing.binding == binding_index && existing.capture_types == capture_types
        }) {
            existing.function
        } else {
            let function_index = self.next_function_index;
            let function_count = function_index.saturating_add(1);
            charge_fir(
                fir::ValidationResource::Functions,
                function_count,
                limits.fir.max_functions,
            )?;
            let raw = u32::try_from(function_index).map_err(|_| IngressError::IdentifierWidth {
                table: "FIR lambda function",
                observed: function_index,
            })?;
            let function = fir::FunctionId::new(raw);
            let parameter_count = capture_types.len().saturating_add(binding.parameters.len());
            charge(
                IngressResource::ContextDepth,
                parameter_count,
                limits.max_context_depth,
            )?;
            work.function_parameters = work.function_parameters.saturating_add(parameter_count);
            charge_fir(
                fir::ValidationResource::Values,
                work.function_parameters
                    .saturating_add(work.generated_values),
                limits.fir.max_values,
            )?;
            let mut parameters = clone_types(&capture_types)?;
            parameters
                .try_reserve_exact(binding.parameters.len())
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: parameter_count,
                })?;
            parameters.extend_from_slice(&binding.parameters);
            let mut parameter_ownership = borrowed_argument_ownership(capture_types.len())?;
            parameter_ownership
                .try_reserve_exact(binding.parameter_ownership.len())
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: parameter_count,
                })?;
            parameter_ownership.extend_from_slice(&binding.parameter_ownership);
            let source_context_len = context
                .len()
                .saturating_add(binding.recursion.synthetic_binders())
                .saturating_add(binding.parameters.len());
            let mut source_context = Vec::new();
            source_context
                .try_reserve_exact(source_context_len)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ContextDepth,
                    requested: source_context_len,
                })?;
            let mut capture_parameter = 0usize;
            for (selected, value) in selected.iter().zip(context) {
                if *selected {
                    let Some(value) = *value else {
                        return Err(IngressError::MalformedResultState {
                            phase: "selected capture context",
                            expected: selected_count,
                            observed: capture_parameter,
                        });
                    };
                    let raw = u32::try_from(capture_parameter).map_err(|_| {
                        IngressError::IdentifierWidth {
                            table: "FIR capture parameter",
                            observed: capture_parameter,
                        }
                    })?;
                    source_context.push(Some(CompiledValue {
                        id: fir::ValueId::new(raw),
                        ty: value.ty,
                    }));
                    capture_parameter = capture_parameter.saturating_add(1);
                } else {
                    source_context.push(None);
                }
            }
            let recursive_prologue = if binding.recursion == LambdaRecursion::SelfBinder {
                let raw =
                    u32::try_from(parameter_count).map_err(|_| IngressError::IdentifierWidth {
                        table: "FIR recursive self closure",
                        observed: parameter_count,
                    })?;
                source_context.push(Some(CompiledValue {
                    id: fir::ValueId::new(raw),
                    ty: fir::ValueType::Closure(binding.closure_type),
                }));
                let mut closures = Vec::new();
                closures
                    .try_reserve_exact(1)
                    .map_err(|_| IngressError::AllocationFailure {
                        resource: IngressResource::ProgramTables,
                        requested: 1,
                    })?;
                closures.push(RecursiveClosure {
                    closure_type: binding.closure_type,
                    function,
                });
                Some(RecursivePrologue {
                    closures,
                    capture_count: captures.len(),
                    mutual_group: false,
                })
            } else {
                None
            };
            for (parameter, ty) in binding.parameters.iter().copied().enumerate() {
                let value_index = captures.len().saturating_add(parameter);
                let raw =
                    u32::try_from(value_index).map_err(|_| IngressError::IdentifierWidth {
                        table: "FIR lambda parameter",
                        observed: value_index,
                    })?;
                source_context.push(Some(CompiledValue {
                    id: fir::ValueId::new(raw),
                    ty,
                }));
            }
            self.specializations
                .try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: self.specializations.len().saturating_add(1),
                })?;
            self.specializations.push(LambdaSpecialization {
                binding: binding_index,
                capture_types,
                function,
            });
            self.pending
                .try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: self.pending.len().saturating_add(1),
                })?;
            self.pending.push_back(PendingLambda {
                binding: binding.source_index,
                function,
                parameters,
                parameter_ownership,
                context: source_context,
                result: binding.result,
                result_ownership: binding.result_ownership,
                body,
                recursive_prologue,
            });
            self.next_function_index = function_count;
            function
        };
        work.generated_functions = self.next_function_index;
        Ok((binding.closure_type, function, captures))
    }

    fn schedule_mutual_group(
        &mut self,
        binding_index: usize,
        context: &[Option<CompiledValue>],
        catalog: &PreparedCatalog<'a>,
        limits: IngressLimits,
        work: &mut IngressWork,
    ) -> Result<(fir::ClosureTypeId, fir::FunctionId, Vec<fir::ValueId>), IngressError> {
        let binding =
            catalog
                .lambdas
                .get(binding_index)
                .ok_or(IngressError::MalformedResultState {
                    phase: "mutual lambda lookup",
                    expected: catalog.lambdas.len(),
                    observed: binding_index,
                })?;
        let LambdaRecursion::MutualMember {
            group: group_id,
            member,
            members,
        } = binding.recursion
        else {
            return Err(IngressError::MalformedResultState {
                phase: "mutual lambda metadata",
                expected: 1,
                observed: 0,
            });
        };
        let group =
            catalog
                .resolve_mutual_group(group_id)
                .ok_or(IngressError::MalformedResultState {
                    phase: "mutual group lookup",
                    expected: catalog.mutual_groups.len(),
                    observed: usize::MAX,
                })?;
        if group.members.len() != usize::from(members)
            || group.members.get(usize::from(member)) != Some(&binding_index)
        {
            return Err(IngressError::MalformedResultState {
                phase: "mutual group member lookup",
                expected: usize::from(members),
                observed: group.members.len(),
            });
        }

        let mut selected = Vec::new();
        selected
            .try_reserve_exact(context.len())
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::CaptureAnalysisNodes,
                requested: context.len(),
            })?;
        selected.resize(context.len(), false);
        let mut binder_counts = Vec::new();
        binder_counts
            .try_reserve_exact(context.len())
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::CaptureAnalysisNodes,
                requested: context.len(),
            })?;
        binder_counts.resize(context.len(), 0usize);
        for member_binding_index in &group.members {
            let member_binding = catalog.lambdas.get(*member_binding_index).ok_or(
                IngressError::MalformedResultState {
                    phase: "mutual group binding",
                    expected: catalog.lambdas.len(),
                    observed: *member_binding_index,
                },
            )?;
            let Some((binder_count, body)) = lambda_spine(member_binding.lambda) else {
                return Err(IngressError::MalformedResultState {
                    phase: "mutual group lambda spine",
                    expected: member_binding
                        .parameters
                        .len()
                        .saturating_add(usize::from(members)),
                    observed: 0,
                });
            };
            let expected_binders = member_binding
                .parameters
                .len()
                .saturating_add(usize::from(members));
            if binder_count != expected_binders {
                return Err(IngressError::MalformedResultState {
                    phase: "mutual group lambda width",
                    expected: expected_binders,
                    observed: binder_count,
                });
            }
            let member_selected = capture_set(body, binder_count, context, limits, work)?;
            for (slot, required) in member_selected.into_iter().enumerate() {
                if required && !selected[slot] {
                    selected[slot] = true;
                    binder_counts[slot] = binder_count;
                }
            }
            let used_count = self.used.len();
            let used = self.used.get_mut(*member_binding_index).ok_or(
                IngressError::MalformedResultState {
                    phase: "mutual lambda use lookup",
                    expected: used_count,
                    observed: *member_binding_index,
                },
            )?;
            *used = true;
        }

        let available_captures = context.iter().filter(|value| value.is_some()).count();
        let selected_count = selected.iter().filter(|capture| **capture).count();
        let mut capture_types = Vec::new();
        let mut captures = Vec::new();
        capture_types
            .try_reserve_exact(selected_count)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: selected_count,
            })?;
        captures.try_reserve_exact(selected_count).map_err(|_| {
            IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: selected_count,
            }
        })?;
        for (offset, (required, value)) in selected.iter().zip(context).enumerate() {
            if !required {
                continue;
            }
            let Some(value) = *value else {
                let outer_index = context.len().saturating_sub(offset.saturating_add(1));
                let binder_count = binder_counts[offset];
                let source_index = binder_count.saturating_add(outer_index);
                let index =
                    u32::try_from(source_index).map_err(|_| IngressError::IdentifierWidth {
                        table: "mutual captured de Bruijn index",
                        observed: source_index,
                    })?;
                return Err(IngressError::MissingCapturedBoundVariable {
                    index,
                    context_depth: context.len().saturating_add(binder_count),
                });
            };
            capture_types.push(value.ty);
            captures.push(value.id);
        }
        work.captured_values = work.captured_values.saturating_add(captures.len());
        work.elided_capture_slots = work
            .elided_capture_slots
            .saturating_add(available_captures.saturating_sub(captures.len()));

        if let Some(existing) = self.specializations.iter().find(|existing| {
            existing.binding == binding_index && existing.capture_types == capture_types
        }) {
            let function = existing.function;
            for member_binding_index in &group.members {
                if !self.specializations.iter().any(|candidate| {
                    candidate.binding == *member_binding_index
                        && candidate.capture_types == capture_types
                }) {
                    return Err(IngressError::MalformedResultState {
                        phase: "mutual group specialization",
                        expected: group.members.len(),
                        observed: 1,
                    });
                }
            }
            work.generated_functions = self.next_function_index;
            return Ok((binding.closure_type, function, captures));
        }

        let function_start = self.next_function_index;
        let function_count = function_start.saturating_add(group.members.len());
        charge_fir(
            fir::ValidationResource::Functions,
            function_count,
            limits.fir.max_functions,
        )?;
        let mut functions = Vec::new();
        functions
            .try_reserve_exact(group.members.len())
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: group.members.len(),
            })?;
        for offset in 0..group.members.len() {
            let function_index = function_start.saturating_add(offset);
            let raw = u32::try_from(function_index).map_err(|_| IngressError::IdentifierWidth {
                table: "FIR mutual lambda function",
                observed: function_index,
            })?;
            functions.push(fir::FunctionId::new(raw));
        }

        let mut added_parameters = 0usize;
        for member_binding_index in &group.members {
            let member_binding = &catalog.lambdas[*member_binding_index];
            let parameter_count = capture_types
                .len()
                .saturating_add(member_binding.parameters.len());
            charge(
                IngressResource::ContextDepth,
                parameter_count,
                limits.max_context_depth,
            )?;
            added_parameters = added_parameters.saturating_add(parameter_count);
        }
        work.function_parameters = work.function_parameters.saturating_add(added_parameters);
        charge_fir(
            fir::ValidationResource::Values,
            work.function_parameters
                .saturating_add(work.generated_values),
            limits.fir.max_values,
        )?;

        let mut recursive_closures = Vec::new();
        recursive_closures
            .try_reserve_exact(group.members.len())
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: group.members.len(),
            })?;
        for (member_binding_index, function) in group.members.iter().zip(&functions) {
            recursive_closures.push(RecursiveClosure {
                closure_type: catalog.lambdas[*member_binding_index].closure_type,
                function: *function,
            });
        }
        self.specializations
            .try_reserve(group.members.len())
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: self
                    .specializations
                    .len()
                    .saturating_add(group.members.len()),
            })?;
        self.pending.try_reserve(group.members.len()).map_err(|_| {
            IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: self.pending.len().saturating_add(group.members.len()),
            }
        })?;

        for (member_binding_index, function) in group.members.iter().zip(&functions) {
            let member_binding = &catalog.lambdas[*member_binding_index];
            let Some((_, body)) = lambda_spine(member_binding.lambda) else {
                return Err(IngressError::MalformedResultState {
                    phase: "mutual pending lambda spine",
                    expected: 1,
                    observed: 0,
                });
            };
            let parameter_count = capture_types
                .len()
                .saturating_add(member_binding.parameters.len());
            let mut parameters = clone_types(&capture_types)?;
            parameters
                .try_reserve_exact(member_binding.parameters.len())
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: parameter_count,
                })?;
            parameters.extend_from_slice(&member_binding.parameters);
            let mut parameter_ownership = borrowed_argument_ownership(capture_types.len())?;
            parameter_ownership
                .try_reserve_exact(member_binding.parameter_ownership.len())
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: parameter_count,
                })?;
            parameter_ownership.extend_from_slice(&member_binding.parameter_ownership);

            let source_context_len = context
                .len()
                .saturating_add(group.members.len())
                .saturating_add(member_binding.parameters.len());
            let mut source_context = Vec::new();
            source_context
                .try_reserve_exact(source_context_len)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ContextDepth,
                    requested: source_context_len,
                })?;
            let mut capture_parameter = 0usize;
            for (required, value) in selected.iter().zip(context) {
                if *required {
                    let Some(value) = *value else {
                        return Err(IngressError::MalformedResultState {
                            phase: "mutual selected capture context",
                            expected: selected_count,
                            observed: capture_parameter,
                        });
                    };
                    let raw = u32::try_from(capture_parameter).map_err(|_| {
                        IngressError::IdentifierWidth {
                            table: "FIR mutual capture parameter",
                            observed: capture_parameter,
                        }
                    })?;
                    source_context.push(Some(CompiledValue {
                        id: fir::ValueId::new(raw),
                        ty: value.ty,
                    }));
                    capture_parameter = capture_parameter.saturating_add(1);
                } else {
                    source_context.push(None);
                }
            }
            for (peer, closure) in recursive_closures.iter().enumerate() {
                let value_index = parameter_count.saturating_add(peer);
                let raw =
                    u32::try_from(value_index).map_err(|_| IngressError::IdentifierWidth {
                        table: "FIR mutual recursive closure",
                        observed: value_index,
                    })?;
                source_context.push(Some(CompiledValue {
                    id: fir::ValueId::new(raw),
                    ty: fir::ValueType::Closure(closure.closure_type),
                }));
            }
            for (parameter, ty) in member_binding.parameters.iter().copied().enumerate() {
                let value_index = capture_types.len().saturating_add(parameter);
                let raw =
                    u32::try_from(value_index).map_err(|_| IngressError::IdentifierWidth {
                        table: "FIR mutual lambda parameter",
                        observed: value_index,
                    })?;
                source_context.push(Some(CompiledValue {
                    id: fir::ValueId::new(raw),
                    ty,
                }));
            }

            let mut prologue_closures = Vec::new();
            prologue_closures
                .try_reserve_exact(recursive_closures.len())
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: recursive_closures.len(),
                })?;
            prologue_closures.extend_from_slice(&recursive_closures);
            self.specializations.push(LambdaSpecialization {
                binding: *member_binding_index,
                capture_types: clone_types(&capture_types)?,
                function: *function,
            });
            self.pending.push_back(PendingLambda {
                binding: member_binding.source_index,
                function: *function,
                parameters,
                parameter_ownership,
                context: source_context,
                result: member_binding.result,
                result_ownership: member_binding.result_ownership,
                body,
                recursive_prologue: Some(RecursivePrologue {
                    closures: prologue_closures,
                    capture_count: captures.len(),
                    mutual_group: true,
                }),
            });
        }
        self.next_function_index = function_count;
        work.generated_functions = function_count;
        let function = functions.get(usize::from(member)).copied().ok_or(
            IngressError::MalformedResultState {
                phase: "mutual member function",
                expected: functions.len(),
                observed: usize::from(member),
            },
        )?;
        Ok((binding.closure_type, function, captures))
    }

    fn refuse_unused(&self, catalog: &PreparedCatalog<'_>) -> Result<(), IngressError> {
        if let Some((index, _)) = self.used.iter().enumerate().find(|(_, used)| !**used) {
            let binding = catalog
                .lambdas
                .get(index)
                .ok_or(IngressError::MalformedResultState {
                    phase: "unused lambda lookup",
                    expected: catalog.lambdas.len(),
                    observed: index,
                })?;
            return Err(IngressError::UnusedLambdaBinding {
                binding: binding.source_index,
                lambda_hash: binding.lambda.hash(),
            });
        }
        Ok(())
    }
}

/// Lower one closed, already elaborated core expression into validated FIR.
///
/// `LetE.type_` is intentionally not traversed as executable input. The root
/// expression's cached free-variable, metavariable, and loose-bound-variable
/// observables are nevertheless checked before any program is constructed, so
/// ignored annotations cannot smuggle an open term through this checkpoint.
pub fn lower_closed_expr(
    source: &Expr,
    limits: IngressLimits,
) -> Result<IngressedProgram, IngressError> {
    lower_closed_expr_with_catalogs(source, &[], &[], &[], limits)
}

/// Lower through an explicit untrusted source-name to intrinsic catalog.
pub fn lower_closed_expr_with_intrinsics(
    source: &Expr,
    intrinsics: &[IntrinsicBinding],
    limits: IngressLimits,
) -> Result<IngressedProgram, IngressError> {
    lower_closed_expr_with_catalogs(source, intrinsics, &[], &[], limits)
}

fn lower_body<'a>(
    source: &'a Expr,
    seed: LowerBodySeed,
    expected_result: Option<fir::ValueType>,
    catalog: &PreparedCatalog<'a>,
    limits: IngressLimits,
    work: &mut IngressWork,
    closure_build: &mut ClosureBuild<'a>,
) -> Result<LoweredBody, IngressError> {
    let LowerBodySeed {
        mut context,
        parameter_count,
        mut bindings,
    } = seed;
    let initial_context_len = context.len();
    if source.has_fvar() {
        return Err(IngressError::OpenFreeVariable);
    }
    if source.has_expr_mvar() {
        return Err(IngressError::UnresolvedMetavariable);
    }
    let allowed_range =
        u32::try_from(context.len()).map_err(|_| IngressError::IdentifierWidth {
            table: "source de Bruijn context",
            observed: context.len(),
        })?;
    if source.loose_bvar_range() > allowed_range {
        return Err(IngressError::LooseBoundVariables {
            range: source.loose_bvar_range(),
        });
    }

    let pending_limit = limits.max_nodes.saturating_mul(2).saturating_add(1);
    let result_limit = limits.max_nodes.saturating_add(1);
    let mut tasks = Vec::new();
    let mut results = Vec::new();
    try_push(
        &mut tasks,
        Task::Eval(source),
        IngressResource::PendingTasks,
        pending_limit,
    )?;

    work.maximum_context_depth = work.maximum_context_depth.max(context.len());

    while let Some(task) = tasks.pop() {
        match task {
            Task::Eval(expr) => {
                work.visited_nodes =
                    increment(IngressResource::Nodes, work.visited_nodes, limits.max_nodes)?;
                match expr.node() {
                    ExprNode::BVar { idx } => {
                        let index = usize::try_from(*idx).map_err(|_| {
                            IngressError::UnboundBoundVariable {
                                index: *idx,
                                context_depth: context.len(),
                            }
                        })?;
                        let Some(offset) = context.len().checked_sub(index.saturating_add(1))
                        else {
                            return Err(IngressError::UnboundBoundVariable {
                                index: *idx,
                                context_depth: context.len(),
                            });
                        };
                        let value = context.get(offset).copied().flatten().ok_or(
                            IngressError::MissingCapturedBoundVariable {
                                index: *idx,
                                context_depth: context.len(),
                            },
                        )?;
                        try_push(
                            &mut results,
                            value,
                            IngressResource::ResultValues,
                            result_limit,
                        )?;
                    }
                    ExprNode::FVar { .. } => return Err(IngressError::OpenFreeVariable),
                    ExprNode::MVar { .. } => {
                        return Err(IngressError::UnresolvedMetavariable);
                    }
                    ExprNode::Lit { literal } => {
                        let value = emit_literal(
                            literal,
                            &mut bindings,
                            parameter_count,
                            &mut work.literal_bytes,
                            limits,
                        )?;
                        try_push(
                            &mut results,
                            value,
                            IngressResource::ResultValues,
                            result_limit,
                        )?;
                    }
                    ExprNode::LetE { value, body, .. } => {
                        work.source_bindings = increment(
                            IngressResource::Bindings,
                            work.source_bindings,
                            limits.max_bindings,
                        )?;
                        let continuation = Task::EnterLetBody {
                            body,
                            context_len: context.len(),
                            result_len: results.len(),
                        };
                        try_push(
                            &mut tasks,
                            continuation,
                            IngressResource::PendingTasks,
                            pending_limit,
                        )?;
                        try_push(
                            &mut tasks,
                            Task::Eval(value),
                            IngressResource::PendingTasks,
                            pending_limit,
                        )?;
                    }
                    ExprNode::MData { expr, .. } => {
                        try_push(
                            &mut tasks,
                            Task::Eval(expr),
                            IngressResource::PendingTasks,
                            pending_limit,
                        )?;
                    }
                    ExprNode::Sort { .. } => {
                        return Err(IngressError::UnsupportedNode { kind: "sort" });
                    }
                    ExprNode::Const { name, levels } => {
                        let scheduled = resolve_call(name, levels.len(), Vec::new(), catalog)?;
                        match scheduled.target {
                            CallTarget::Constructor(_) => {
                                work.constructor_calls = work.constructor_calls.saturating_add(1);
                            }
                            CallTarget::Intrinsic(_) => {
                                work.intrinsic_calls = work.intrinsic_calls.saturating_add(1);
                            }
                            CallTarget::Function(_) => {
                                work.function_calls = work.function_calls.saturating_add(1);
                            }
                        }
                        try_push(
                            &mut tasks,
                            Task::FinishCall {
                                target: scheduled.target,
                                argument_count: 0,
                                result_len: results.len(),
                            },
                            IngressResource::PendingTasks,
                            pending_limit,
                        )?;
                    }
                    ExprNode::App { f, a } => {
                        let mut arguments = Vec::new();
                        try_push(
                            &mut arguments,
                            a,
                            IngressResource::ApplicationArguments,
                            limits.max_application_args,
                        )?;
                        let mut head = f;
                        let direct = loop {
                            match head.node() {
                                ExprNode::App { f, a } => {
                                    work.visited_nodes = increment(
                                        IngressResource::Nodes,
                                        work.visited_nodes,
                                        limits.max_nodes,
                                    )?;
                                    try_push(
                                        &mut arguments,
                                        a,
                                        IngressResource::ApplicationArguments,
                                        limits.max_application_args,
                                    )?;
                                    head = f;
                                }
                                ExprNode::MData { expr, .. } => {
                                    work.visited_nodes = increment(
                                        IngressResource::Nodes,
                                        work.visited_nodes,
                                        limits.max_nodes,
                                    )?;
                                    head = expr;
                                }
                                ExprNode::Const { name, levels } => {
                                    work.visited_nodes = increment(
                                        IngressResource::Nodes,
                                        work.visited_nodes,
                                        limits.max_nodes,
                                    )?;
                                    break Some((name, levels.len()));
                                }
                                _ => break None,
                            }
                        };
                        if let Some((name, universe_arity)) = direct {
                            let scheduled = resolve_call(name, universe_arity, arguments, catalog)?;
                            let argument_count = scheduled.arguments.len();
                            match scheduled.target {
                                CallTarget::Constructor(_) => {
                                    work.constructor_calls =
                                        work.constructor_calls.saturating_add(1);
                                }
                                CallTarget::Intrinsic(_) => {
                                    work.intrinsic_calls = work.intrinsic_calls.saturating_add(1);
                                }
                                CallTarget::Function(_) => {
                                    work.function_calls = work.function_calls.saturating_add(1);
                                }
                            }
                            try_push(
                                &mut tasks,
                                Task::FinishCall {
                                    target: scheduled.target,
                                    argument_count,
                                    result_len: results.len(),
                                },
                                IngressResource::PendingTasks,
                                pending_limit,
                            )?;
                            for argument in scheduled.arguments {
                                try_push(
                                    &mut tasks,
                                    Task::Eval(argument),
                                    IngressResource::PendingTasks,
                                    pending_limit,
                                )?;
                            }
                        } else {
                            let argument_count = arguments.len();
                            work.closure_applications = work.closure_applications.saturating_add(1);
                            try_push(
                                &mut tasks,
                                Task::FinishApply {
                                    argument_count,
                                    result_len: results.len(),
                                },
                                IngressResource::PendingTasks,
                                pending_limit,
                            )?;
                            for argument in arguments {
                                try_push(
                                    &mut tasks,
                                    Task::Eval(argument),
                                    IngressResource::PendingTasks,
                                    pending_limit,
                                )?;
                            }
                            try_push(
                                &mut tasks,
                                Task::Eval(head),
                                IngressResource::PendingTasks,
                                pending_limit,
                            )?;
                        }
                    }
                    ExprNode::Lam { .. } => {
                        let (closure_type, function, captures) =
                            closure_build.schedule(expr, &context, catalog, limits, work)?;
                        let capture_ownership = borrowed_argument_ownership(captures.len())?;
                        let value = emit_binding(
                            &mut bindings,
                            parameter_count,
                            fir::ValueType::Closure(closure_type),
                            fir::Operation::Closure {
                                closure_type,
                                function,
                                captures,
                                capture_ownership,
                            },
                            limits,
                        )?;
                        work.lambda_conversions = work.lambda_conversions.saturating_add(1);
                        try_push(
                            &mut results,
                            value,
                            IngressResource::ResultValues,
                            result_limit,
                        )?;
                    }
                    ExprNode::ForallE { .. } => {
                        return Err(IngressError::UnsupportedNode { kind: "forall" });
                    }
                    ExprNode::Proj {
                        struct_name,
                        idx,
                        expr,
                    } => {
                        let projection = catalog.resolve_projection(struct_name, *idx).ok_or(
                            IngressError::UnknownProjection {
                                name_hash: struct_name.hash(),
                                field: *idx,
                            },
                        )?;
                        work.projection_calls = work.projection_calls.saturating_add(1);
                        try_push(
                            &mut tasks,
                            Task::FinishProjection {
                                projection,
                                result_len: results.len(),
                            },
                            IngressResource::PendingTasks,
                            pending_limit,
                        )?;
                        try_push(
                            &mut tasks,
                            Task::Eval(expr),
                            IngressResource::PendingTasks,
                            pending_limit,
                        )?;
                    }
                }
            }
            Task::EnterLetBody {
                body,
                context_len,
                result_len,
            } => {
                if context.len() != context_len {
                    return Err(malformed("let-value context", context_len, context.len()));
                }
                let expected_results = result_len.saturating_add(1);
                if results.len() != expected_results {
                    return Err(malformed("let value", expected_results, results.len()));
                }
                let value = results
                    .pop()
                    .ok_or_else(|| malformed("let value pop", expected_results, 0))?;
                let observed_depth = context.len().saturating_add(1);
                charge(
                    IngressResource::ContextDepth,
                    observed_depth,
                    limits.max_context_depth,
                )?;
                try_push(
                    &mut context,
                    Some(value),
                    IngressResource::ContextDepth,
                    limits.max_context_depth,
                )?;
                work.maximum_context_depth = work.maximum_context_depth.max(observed_depth);
                try_push(
                    &mut tasks,
                    Task::LeaveLet {
                        context_len,
                        result_len,
                    },
                    IngressResource::PendingTasks,
                    pending_limit,
                )?;
                try_push(
                    &mut tasks,
                    Task::Eval(body),
                    IngressResource::PendingTasks,
                    pending_limit,
                )?;
            }
            Task::LeaveLet {
                context_len,
                result_len,
            } => {
                let expected_context = context_len.saturating_add(1);
                if context.len() != expected_context {
                    return Err(malformed(
                        "let-body context",
                        expected_context,
                        context.len(),
                    ));
                }
                let expected_results = result_len.saturating_add(1);
                if results.len() != expected_results {
                    return Err(malformed("let body", expected_results, results.len()));
                }
                context.truncate(context_len);
            }
            Task::FinishCall {
                target,
                argument_count,
                result_len,
            } => {
                let expected_results = result_len.saturating_add(argument_count);
                if results.len() != expected_results {
                    return Err(malformed("call arguments", expected_results, results.len()));
                }
                let (name_hash, expected_types, result_type) = match target {
                    CallTarget::Constructor(binding_index) => {
                        let binding = catalog.constructors.get(binding_index).ok_or(
                            IngressError::MalformedResultState {
                                phase: "constructor catalog lookup",
                                expected: catalog.constructors.len(),
                                observed: binding_index,
                            },
                        )?;
                        (
                            binding.name.hash(),
                            binding.declaration.fields.as_slice(),
                            fir::ValueType::Constructor,
                        )
                    }
                    CallTarget::Intrinsic(binding_index) => {
                        let binding = catalog.entries.get(binding_index).ok_or(
                            IngressError::MalformedResultState {
                                phase: "intrinsic catalog lookup",
                                expected: catalog.entries.len(),
                                observed: binding_index,
                            },
                        )?;
                        (
                            binding.name.hash(),
                            binding.declaration.arguments.as_slice(),
                            binding.declaration.result,
                        )
                    }
                    CallTarget::Function(binding_index) => {
                        let binding = catalog.functions.get(binding_index).ok_or(
                            IngressError::MalformedResultState {
                                phase: "function catalog lookup",
                                expected: catalog.functions.len(),
                                observed: binding_index,
                            },
                        )?;
                        (
                            binding.name.hash(),
                            binding.parameters.as_slice(),
                            binding.result,
                        )
                    }
                };
                let mut arguments = Vec::new();
                arguments.try_reserve_exact(argument_count).map_err(|_| {
                    IngressError::AllocationFailure {
                        resource: IngressResource::ProgramTables,
                        requested: argument_count,
                    }
                })?;
                arguments.extend_from_slice(&results[result_len..]);
                for (argument, expected) in expected_types.iter().copied().enumerate() {
                    let actual = arguments[argument];
                    let Some(coerced) = coerce_abi_boundary(
                        actual,
                        expected,
                        &mut bindings,
                        parameter_count,
                        limits,
                    )?
                    else {
                        return Err(match target {
                            CallTarget::Constructor(_) => IngressError::ConstructorArgumentType {
                                name_hash,
                                argument,
                                expected,
                                actual: actual.ty,
                            },
                            CallTarget::Intrinsic(_) => IngressError::IntrinsicArgumentType {
                                name_hash,
                                argument,
                                expected,
                                actual: actual.ty,
                            },
                            CallTarget::Function(_) => IngressError::FunctionArgumentType {
                                name_hash,
                                argument,
                                expected,
                                actual: actual.ty,
                            },
                        });
                    };
                    arguments[argument] = coerced;
                }
                let mut argument_ids = Vec::new();
                argument_ids
                    .try_reserve_exact(argument_count)
                    .map_err(|_| IngressError::AllocationFailure {
                        resource: IngressResource::ProgramTables,
                        requested: argument_count,
                    })?;
                argument_ids.extend(arguments.iter().map(|value| value.id));
                let operation = match target {
                    CallTarget::Constructor(binding_index) => {
                        let binding = &catalog.constructors[binding_index];
                        fir::Operation::Ctor {
                            constructor: binding.declaration.id,
                            fields: argument_ids,
                        }
                    }
                    CallTarget::Intrinsic(binding_index) => fir::Operation::Intrinsic {
                        intrinsic: catalog.entries[binding_index].declaration.id,
                        args: argument_ids,
                    },
                    CallTarget::Function(binding_index) => fir::Operation::Call {
                        function: catalog.functions[binding_index].id,
                        args: argument_ids,
                    },
                };
                let value = emit_binding(
                    &mut bindings,
                    parameter_count,
                    result_type,
                    operation,
                    limits,
                )?;
                results.truncate(result_len);
                try_push(
                    &mut results,
                    value,
                    IngressResource::ResultValues,
                    result_limit,
                )?;
            }
            Task::FinishApply {
                argument_count,
                result_len,
            } => {
                let expected_results = result_len.saturating_add(argument_count).saturating_add(1);
                if results.len() != expected_results {
                    return Err(malformed(
                        "closure application values",
                        expected_results,
                        results.len(),
                    ));
                }
                let closure = results.get(result_len).copied().ok_or_else(|| {
                    malformed(
                        "closure application operand",
                        expected_results,
                        results.len(),
                    )
                })?;
                let fir::ValueType::Closure(closure_type) = closure.ty else {
                    return Err(IngressError::LambdaApplicationOperandType { actual: closure.ty });
                };
                let mut arguments = Vec::new();
                arguments.try_reserve_exact(argument_count).map_err(|_| {
                    IngressError::AllocationFailure {
                        resource: IngressResource::ProgramTables,
                        requested: argument_count,
                    }
                })?;
                arguments.extend_from_slice(&results[result_len.saturating_add(1)..]);
                let mut argument_ownership = Vec::new();
                argument_ownership
                    .try_reserve_exact(argument_count)
                    .map_err(|_| IngressError::AllocationFailure {
                        resource: IngressResource::ProgramTables,
                        requested: argument_count,
                    })?;
                let application_result = match fir::infer_application_type(
                    &catalog.closure_types,
                    closure_type,
                    argument_count,
                    |argument, expected, expected_ownership| {
                        argument_ownership.push(expected_ownership);
                        let actual = arguments[argument];
                        let Some(coerced) = coerce_abi_boundary(
                            actual,
                            expected,
                            &mut bindings,
                            parameter_count,
                            limits,
                        )?
                        else {
                            return Ok(actual.ty);
                        };
                        arguments[argument] = coerced;
                        Ok(coerced.ty)
                    },
                ) {
                    Ok(result) => result,
                    Err(fir::ApplicationInferenceError::Argument(error)) => return Err(error),
                    Err(fir::ApplicationInferenceError::Type(
                        fir::ApplicationTypeError::EmptyArguments { .. },
                    )) => {
                        return Err(IngressError::MalformedResultState {
                            phase: "empty closure application",
                            expected: 1,
                            observed: 0,
                        });
                    }
                    Err(fir::ApplicationInferenceError::Type(
                        fir::ApplicationTypeError::MissingClosureType { closure_type },
                    )) => {
                        let observed = usize::try_from(closure_type.get()).unwrap_or(usize::MAX);
                        return Err(IngressError::MalformedResultState {
                            phase: "closure application signature",
                            expected: catalog.closure_types.len(),
                            observed,
                        });
                    }
                    Err(fir::ApplicationInferenceError::Type(
                        fir::ApplicationTypeError::PartialClosureTypeMissing {
                            closure_type,
                            consumed,
                        },
                    )) => {
                        return Err(IngressError::LambdaApplicationPartialClosureTypeMissing {
                            closure_type,
                            consumed,
                        });
                    }
                    Err(fir::ApplicationInferenceError::Type(
                        fir::ApplicationTypeError::ArgumentType {
                            closure_type,
                            argument,
                            expected,
                            actual,
                        },
                    )) => {
                        return Err(IngressError::LambdaApplicationArgumentType {
                            closure_type,
                            argument,
                            expected,
                            actual,
                        });
                    }
                    Err(fir::ApplicationInferenceError::Type(
                        fir::ApplicationTypeError::RemainderType {
                            closure_type,
                            argument,
                            actual,
                        },
                    )) => {
                        return Err(IngressError::LambdaApplicationRemainderType {
                            closure_type,
                            argument,
                            actual,
                        });
                    }
                };
                let mut argument_ids = Vec::new();
                argument_ids
                    .try_reserve_exact(argument_count)
                    .map_err(|_| IngressError::AllocationFailure {
                        resource: IngressResource::ProgramTables,
                        requested: argument_count,
                    })?;
                argument_ids.extend(arguments.iter().map(|value| value.id));
                let value = emit_binding(
                    &mut bindings,
                    parameter_count,
                    application_result.ty,
                    fir::Operation::Apply {
                        closure: closure.id,
                        args: argument_ids,
                        argument_ownership,
                        result_ownership: application_result.ownership,
                    },
                    limits,
                )?;
                results.truncate(result_len);
                try_push(
                    &mut results,
                    value,
                    IngressResource::ResultValues,
                    result_limit,
                )?;
            }
            Task::FinishProjection {
                projection,
                result_len,
            } => {
                let expected_results = result_len.saturating_add(1);
                if results.len() != expected_results {
                    return Err(malformed(
                        "projection operand",
                        expected_results,
                        results.len(),
                    ));
                }
                let operand = results
                    .get(result_len)
                    .copied()
                    .ok_or_else(|| malformed("projection operand lookup", expected_results, 0))?;
                let prepared = catalog.projections.get(projection).ok_or(
                    IngressError::MalformedResultState {
                        phase: "projection catalog lookup",
                        expected: catalog.projections.len(),
                        observed: projection,
                    },
                )?;
                if operand.ty != fir::ValueType::Constructor {
                    return Err(IngressError::ProjectionOperandType {
                        name_hash: prepared.structure_name.hash(),
                        field: prepared.source_field,
                        actual: operand.ty,
                    });
                }
                let constructor = catalog.constructors.get(prepared.constructor_index).ok_or(
                    IngressError::MalformedResultState {
                        phase: "projection constructor lookup",
                        expected: catalog.constructors.len(),
                        observed: prepared.constructor_index,
                    },
                )?;
                let result_type = constructor
                    .declaration
                    .fields
                    .get(usize::from(prepared.declaration.field))
                    .copied()
                    .ok_or(IngressError::MalformedResultState {
                        phase: "projection field lookup",
                        expected: constructor.declaration.fields.len(),
                        observed: usize::from(prepared.declaration.field),
                    })?;
                let value = emit_binding(
                    &mut bindings,
                    parameter_count,
                    result_type,
                    fir::Operation::Project {
                        projection: prepared.declaration.id,
                        value: operand.id,
                    },
                    limits,
                )?;
                results.truncate(result_len);
                try_push(
                    &mut results,
                    value,
                    IngressResource::ResultValues,
                    result_limit,
                )?;
            }
        }
    }

    if context.len() != initial_context_len {
        return Err(malformed(
            "final context",
            initial_context_len,
            context.len(),
        ));
    }
    if results.len() != 1 {
        return Err(malformed("final result", 1, results.len()));
    }
    let mut result = results
        .pop()
        .ok_or_else(|| malformed("final result pop", 1, 0))?;
    if let Some(expected) = expected_result
        && let Some(coerced) =
            coerce_abi_boundary(result, expected, &mut bindings, parameter_count, limits)?
    {
        result = coerced;
    }

    work.generated_values = work.generated_values.saturating_add(bindings.len());
    let total_values = work
        .function_parameters
        .saturating_add(work.generated_values);
    charge_fir(
        fir::ValidationResource::Values,
        total_values,
        limits.fir.max_values,
    )?;
    Ok(LoweredBody { bindings, result })
}

fn parameter_context(
    parameters: &[fir::ValueType],
    limits: IngressLimits,
) -> Result<CompiledContext, IngressError> {
    charge(
        IngressResource::ContextDepth,
        parameters.len(),
        limits.max_context_depth,
    )?;
    let mut context = Vec::new();
    context
        .try_reserve_exact(parameters.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ContextDepth,
            requested: parameters.len(),
        })?;
    for (index, ty) in parameters.iter().copied().enumerate() {
        let raw = u32::try_from(index).map_err(|_| IngressError::IdentifierWidth {
            table: "FIR parameter",
            observed: index,
        })?;
        context.push(Some(CompiledValue {
            id: fir::ValueId::new(raw),
            ty,
        }));
    }
    Ok(context)
}

fn assemble_function(
    id: fir::FunctionId,
    parameters: Vec<fir::ValueType>,
    parameter_ownership: Vec<crate::flbc::ArgumentOwnership>,
    result: fir::ValueType,
    result_ownership: crate::flbc::CallableResultOwnership,
    body: LoweredBody,
) -> Result<fir::Function, IngressError> {
    let block = fir::Block {
        id: fir::BlockId::new(0),
        bindings: body.bindings,
        terminator: fir::Terminator::Return {
            value: body.result.id,
        },
    };
    Ok(fir::Function {
        id,
        parameters,
        parameter_ownership,
        result,
        result_ownership,
        blocks: singleton(block)?,
    })
}

const fn default_callable_result_ownership(
    result: fir::ValueType,
) -> crate::flbc::CallableResultOwnership {
    match result {
        fir::ValueType::Unit | fir::ValueType::Bool | fir::ValueType::Nat => {
            crate::flbc::CallableResultOwnership::Scalar
        }
        fir::ValueType::String
        | fir::ValueType::Constructor
        | fir::ValueType::Array
        | fir::ValueType::Ref
        | fir::ValueType::Thunk
        | fir::ValueType::Task
        | fir::ValueType::Closure(_)
        | fir::ValueType::Abi => crate::flbc::CallableResultOwnership::Owned,
    }
}

/// Lower through explicit untrusted intrinsic, constructor, and first-order
/// function catalogs.
///
/// Intrinsics are canonicalized by contract row. Constructors and functions
/// are canonicalized by structural source name. Every constructor layout and
/// every function body, including currently unreachable entries, participates
/// in FIR identity. Source names are resolution metadata and are erased after
/// canonical ids are fixed.
pub fn lower_closed_expr_with_catalogs(
    source: &Expr,
    intrinsics: &[IntrinsicBinding],
    constructors: &[ConstructorBinding],
    functions: &[FunctionBinding],
    limits: IngressLimits,
) -> Result<IngressedProgram, IngressError> {
    lower_closed_expr_with_lambdas(source, intrinsics, constructors, functions, &[], limits)
}

/// Lower through all declaration catalogs plus exact local-lambda signatures.
///
/// Lambda annotations are resolution metadata. Their deduplicated signatures,
/// every generated target function, and every closure/application operation are
/// part of canonical FIR identity and pass the ordinary independent validator.
/// Closure-valued parameter and result types use ids in that final canonical
/// signature table; dangling ids are refused before any FIR is published. A
/// recursive self binder is rebuilt inside its lifted target from that target's
/// ordinary capture parameters, rather than stored as a cyclic RC edge.
pub fn lower_closed_expr_with_lambdas<'a>(
    source: &'a Expr,
    intrinsics: &[IntrinsicBinding],
    constructors: &[ConstructorBinding],
    functions: &'a [FunctionBinding],
    lambdas: &'a [LambdaBinding],
    limits: IngressLimits,
) -> Result<IngressedProgram, IngressError> {
    if source.has_fvar() {
        return Err(IngressError::OpenFreeVariable);
    }
    if source.has_expr_mvar() {
        return Err(IngressError::UnresolvedMetavariable);
    }
    if source.has_loose_bvars() {
        return Err(IngressError::LooseBoundVariables {
            range: source.loose_bvar_range(),
        });
    }

    let catalog = prepare_catalog(intrinsics, constructors, functions, lambdas, limits)?;
    let mut closure_build = ClosureBuild::new(&catalog)?;
    let generated_functions = catalog.functions.len().saturating_add(1);
    let function_parameters = catalog.functions.iter().fold(0usize, |total, function| {
        total.saturating_add(function.parameters.len())
    });
    let mut work = IngressWork {
        visited_nodes: 0,
        source_bindings: 0,
        capture_analysis_nodes: 0,
        captured_values: 0,
        elided_capture_slots: 0,
        intrinsic_calls: 0,
        constructor_calls: 0,
        projection_calls: 0,
        function_calls: 0,
        lambda_conversions: 0,
        recursive_self_closures: 0,
        mutual_group_closures: 0,
        closure_applications: 0,
        generated_constructors: catalog.constructors.len(),
        generated_projections: catalog.projections.len(),
        generated_closure_types: catalog.closure_types.len(),
        generated_functions,
        function_parameters,
        generated_values: 0,
        literal_bytes: 0,
        maximum_context_depth: 0,
    };

    let mut fir_functions = Vec::new();
    fir_functions
        .try_reserve_exact(generated_functions)
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: generated_functions,
        })?;
    let entry_body = lower_body(
        source,
        LowerBodySeed {
            context: Vec::new(),
            parameter_count: 0,
            bindings: Vec::new(),
        },
        None,
        &catalog,
        limits,
        &mut work,
        &mut closure_build,
    )?;
    fir_functions.push(assemble_function(
        fir::FunctionId::new(0),
        Vec::new(),
        Vec::new(),
        entry_body.result.ty,
        default_callable_result_ownership(entry_body.result.ty),
        entry_body,
    )?);
    for function in &catalog.functions {
        let context = parameter_context(&function.parameters, limits)?;
        let body = lower_body(
            function.body,
            LowerBodySeed {
                context,
                parameter_count: function.parameters.len(),
                bindings: Vec::new(),
            },
            Some(function.result),
            &catalog,
            limits,
            &mut work,
            &mut closure_build,
        )?;
        if body.result.ty != function.result {
            return Err(IngressError::FunctionResultType {
                name_hash: function.name.hash(),
                expected: function.result,
                actual: body.result.ty,
            });
        }
        fir_functions.push(assemble_function(
            function.id,
            clone_types(&function.parameters)?,
            clone_argument_ownership(&function.parameter_ownership)?,
            function.result,
            function.result_ownership,
            body,
        )?);
    }
    while let Some(lambda) = closure_build.pending.pop_front() {
        let parameter_count = lambda.parameters.len();
        let mut prologue = Vec::new();
        if let Some(recursive) = lambda.recursive_prologue {
            for closure in &recursive.closures {
                let mut captures = Vec::new();
                captures
                    .try_reserve_exact(recursive.capture_count)
                    .map_err(|_| IngressError::AllocationFailure {
                        resource: IngressResource::ProgramTables,
                        requested: recursive.capture_count,
                    })?;
                for capture in 0..recursive.capture_count {
                    let raw =
                        u32::try_from(capture).map_err(|_| IngressError::IdentifierWidth {
                            table: "FIR recursive closure capture",
                            observed: capture,
                        })?;
                    captures.push(fir::ValueId::new(raw));
                }
                let capture_ownership = borrowed_argument_ownership(captures.len())?;
                let recursive_value = emit_binding(
                    &mut prologue,
                    parameter_count,
                    fir::ValueType::Closure(closure.closure_type),
                    fir::Operation::Closure {
                        closure_type: closure.closure_type,
                        function: closure.function,
                        captures,
                        capture_ownership,
                    },
                    limits,
                )?;
                let expected =
                    lambda.context.iter().flatten().find(|value| {
                        value.id == recursive_value.id && value.ty == recursive_value.ty
                    });
                if expected.is_none() {
                    return Err(IngressError::MalformedResultState {
                        phase: "recursive closure context",
                        expected: usize::try_from(recursive_value.id.get()).unwrap_or(usize::MAX),
                        observed: usize::MAX,
                    });
                }
            }
            if recursive.mutual_group {
                work.mutual_group_closures = work
                    .mutual_group_closures
                    .saturating_add(recursive.closures.len());
            } else {
                work.recursive_self_closures = work
                    .recursive_self_closures
                    .saturating_add(recursive.closures.len());
            }
        }
        let body = lower_body(
            lambda.body,
            LowerBodySeed {
                context: lambda.context,
                parameter_count,
                bindings: prologue,
            },
            Some(lambda.result),
            &catalog,
            limits,
            &mut work,
            &mut closure_build,
        )?;
        if body.result.ty != lambda.result {
            return Err(IngressError::LambdaResultType {
                binding: lambda.binding,
                expected: lambda.result,
                actual: body.result.ty,
            });
        }
        fir_functions
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: fir_functions.len().saturating_add(1),
            })?;
        fir_functions.push(assemble_function(
            lambda.function,
            lambda.parameters,
            lambda.parameter_ownership,
            lambda.result,
            lambda.result_ownership,
            body,
        )?);
    }
    closure_build.refuse_unused(&catalog)?;

    let mut intrinsic_declarations = Vec::new();
    intrinsic_declarations
        .try_reserve_exact(catalog.entries.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: catalog.entries.len(),
        })?;
    intrinsic_declarations.extend(catalog.entries.into_iter().map(|entry| entry.declaration));
    let mut projection_declarations = Vec::new();
    projection_declarations
        .try_reserve_exact(catalog.projections.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: catalog.projections.len(),
        })?;
    projection_declarations.extend(
        catalog
            .projections
            .into_iter()
            .map(|entry| entry.declaration),
    );
    let mut constructor_declarations = Vec::new();
    constructor_declarations
        .try_reserve_exact(catalog.constructors.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: catalog.constructors.len(),
        })?;
    constructor_declarations.extend(
        catalog
            .constructors
            .into_iter()
            .map(|entry| entry.declaration),
    );
    let program = fir::Program::new_with_closures(
        fir::FunctionId::new(0),
        constructor_declarations,
        projection_declarations,
        catalog.closure_types,
        intrinsic_declarations,
        fir_functions,
    );
    let fir = fir::validate(program, limits.fir)?;
    Ok(IngressedProgram {
        source_expr_hash: source.hash(),
        work,
        fir,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::flbc::{CodecLimits, encode_canonical};
    use fln_core::expr::{BinderInfo, FVarId, MVarId, NatLit};
    use fln_core::level::Level;
    use fln_core::name::Name;
    use fln_core::options::KVMap;
    use fln_rt::abi;

    fn nat(value: u64) -> Expr {
        Expr::lit(Literal::Nat(NatLit::from_u64(value)))
    }

    fn string(value: &str) -> Expr {
        Expr::lit(Literal::Str(value.to_string()))
    }

    fn direct_call(name: &[&str], arguments: impl IntoIterator<Item = Expr>) -> Expr {
        arguments.into_iter().fold(
            Expr::const_(Name::from_components(name.iter().copied()), Vec::new()),
            Expr::app,
        )
    }

    fn lambda(body: Expr) -> Expr {
        named_lambda("x", body)
    }

    fn named_lambda(name: &str, body: Expr) -> Expr {
        Expr::lam(
            Name::from_components([name]),
            Expr::sort(Level::zero()),
            body,
            BinderInfo::Default,
        )
    }

    fn lambda_binding(
        lambda: &Expr,
        parameters: Vec<fir::ValueType>,
        result: fir::ValueType,
    ) -> LambdaBinding {
        let parameter_ownership = vec![crate::flbc::ArgumentOwnership::Borrowed; parameters.len()];
        LambdaBinding {
            lambda: lambda.clone(),
            parameters,
            parameter_ownership,
            result,
            result_ownership: default_callable_result_ownership(result),
            recursion: LambdaRecursion::NonRecursive,
        }
    }

    fn self_recursive_lambda_binding(
        lambda: &Expr,
        parameters: Vec<fir::ValueType>,
        result: fir::ValueType,
    ) -> LambdaBinding {
        let parameter_ownership = vec![crate::flbc::ArgumentOwnership::Borrowed; parameters.len()];
        LambdaBinding {
            lambda: lambda.clone(),
            parameters,
            parameter_ownership,
            result,
            result_ownership: default_callable_result_ownership(result),
            recursion: LambdaRecursion::SelfBinder,
        }
    }

    fn mutual_lambda_binding(
        lambda: &Expr,
        parameters: Vec<fir::ValueType>,
        result: fir::ValueType,
        group: u32,
        member: u16,
        members: u16,
    ) -> LambdaBinding {
        let parameter_ownership = vec![crate::flbc::ArgumentOwnership::Borrowed; parameters.len()];
        LambdaBinding {
            lambda: lambda.clone(),
            parameters,
            parameter_ownership,
            result,
            result_ownership: default_callable_result_ownership(result),
            recursion: LambdaRecursion::MutualMember {
                group,
                member,
                members,
            },
        }
    }

    fn nat_add_binding() -> IntrinsicBinding {
        IntrinsicBinding {
            name: Name::from_components(["Nat", "add"]),
            universe_arity: 0,
            row: "extern:Nat.add".to_string(),
            arguments: vec![fir::ValueType::Nat, fir::ValueType::Nat],
            argument_ownership: vec![
                crate::flbc::ArgumentOwnership::Borrowed,
                crate::flbc::ArgumentOwnership::Borrowed,
            ],
            result_ownership: crate::flbc::ResultOwnership::Owned,
            result: fir::ValueType::Nat,
            effect: fir::EffectClass::Pure,
        }
    }

    fn string_append_binding() -> IntrinsicBinding {
        IntrinsicBinding {
            name: Name::from_components(["String", "append"]),
            universe_arity: 0,
            row: "extern:String.append".to_string(),
            arguments: vec![fir::ValueType::String, fir::ValueType::String],
            argument_ownership: vec![
                crate::flbc::ArgumentOwnership::Owned,
                crate::flbc::ArgumentOwnership::Borrowed,
            ],
            result_ownership: crate::flbc::ResultOwnership::Owned,
            result: fir::ValueType::String,
            effect: fir::EffectClass::Pure,
        }
    }

    fn pure_catalog() -> Vec<IntrinsicBinding> {
        vec![string_append_binding(), nat_add_binding()]
    }

    fn constructor_binding(
        name: &[&str],
        tag: u8,
        fields: Vec<fir::ValueType>,
        static_scalar_bytes: Vec<u8>,
    ) -> ConstructorBinding {
        ConstructorBinding {
            name: Name::from_components(name.iter().copied()),
            projection_structure: None,
            universe_arity: 0,
            tag,
            fields,
            static_scalar_bytes,
        }
    }

    fn pair_constructor_binding() -> ConstructorBinding {
        constructor_binding(
            &["User", "Pair", "mk"],
            7,
            vec![fir::ValueType::Nat, fir::ValueType::String],
            vec![0xAB, 0xCD],
        )
    }

    fn projected_pair_constructor_binding() -> ConstructorBinding {
        let mut pair = pair_constructor_binding();
        pair.projection_structure = Some(Name::from_components(["User", "Pair"]));
        pair
    }

    fn function_binding(
        name: &[&str],
        parameters: Vec<fir::ValueType>,
        result: fir::ValueType,
        body: Expr,
    ) -> FunctionBinding {
        let parameter_ownership = vec![crate::flbc::ArgumentOwnership::Borrowed; parameters.len()];
        FunctionBinding {
            name: Name::from_components(name.iter().copied()),
            universe_arity: 0,
            parameters,
            parameter_ownership,
            result,
            result_ownership: default_callable_result_ownership(result),
            body,
        }
    }

    fn identity_function_binding() -> FunctionBinding {
        function_binding(
            &["User", "identity"],
            vec![fir::ValueType::Nat],
            fir::ValueType::Nat,
            Expr::bvar(0).expect("small bvar"),
        )
    }

    fn inc_function_binding() -> FunctionBinding {
        function_binding(
            &["User", "inc"],
            vec![fir::ValueType::Nat],
            fir::ValueType::Nat,
            direct_call(
                &["Nat", "add"],
                [Expr::bvar(0).expect("small bvar"), nat(1)],
            ),
        )
    }

    fn twice_function_binding() -> FunctionBinding {
        function_binding(
            &["User", "twice"],
            vec![fir::ValueType::Nat],
            fir::ValueType::Nat,
            direct_call(
                &["User", "inc"],
                [direct_call(
                    &["User", "inc"],
                    [Expr::bvar(0).expect("small bvar")],
                )],
            ),
        )
    }

    fn ignored_type() -> Expr {
        Expr::app(nat(0), nat(1))
    }

    fn nested_let() -> Expr {
        Expr::mdata(
            KVMap::new(),
            Expr::let_e(
                Name::anonymous(),
                ignored_type(),
                nat(40),
                Expr::let_e(
                    Name::anonymous(),
                    Expr::sort(Level::zero()),
                    nat(2),
                    Expr::bvar(1).expect("small bvar"),
                    false,
                ),
                false,
            ),
        )
    }

    fn identity(expr: &Expr, limits: IngressLimits) -> (u64, IngressWork, String, Vec<u8>) {
        let ingress = lower_closed_expr(expr, limits).expect("closed subset ingress");
        let text = ingress.fir().canonical_text();
        let flbc = fir::lower_to_flbc(ingress.fir()).expect("validated FIR lowers");
        let bytes =
            encode_canonical(&flbc, CodecLimits::default()).expect("canonical FLBC artifact");
        (ingress.source_expr_hash(), ingress.work(), text, bytes)
    }

    fn intrinsic_identity(
        expr: &Expr,
        catalog: &[IntrinsicBinding],
        limits: IngressLimits,
    ) -> (u64, IngressWork, String, Vec<u8>) {
        let ingress = lower_closed_expr_with_intrinsics(expr, catalog, limits)
            .expect("closed intrinsic subset ingress");
        let text = ingress.fir().canonical_text();
        let flbc = fir::lower_to_flbc(ingress.fir()).expect("validated FIR lowers");
        let bytes =
            encode_canonical(&flbc, CodecLimits::default()).expect("canonical FLBC artifact");
        (ingress.source_expr_hash(), ingress.work(), text, bytes)
    }

    fn function_identity(
        expr: &Expr,
        intrinsics: &[IntrinsicBinding],
        functions: &[FunctionBinding],
        limits: IngressLimits,
    ) -> (u64, IngressWork, String, Vec<u8>) {
        let ingress = lower_closed_expr_with_catalogs(expr, intrinsics, &[], functions, limits)
            .expect("closed first-order subset ingress");
        let text = ingress.fir().canonical_text();
        let flbc = fir::lower_to_flbc(ingress.fir()).expect("validated FIR lowers");
        let bytes =
            encode_canonical(&flbc, CodecLimits::default()).expect("canonical FLBC artifact");
        (ingress.source_expr_hash(), ingress.work(), text, bytes)
    }

    fn constructor_identity(
        expr: &Expr,
        constructors: &[ConstructorBinding],
        limits: IngressLimits,
    ) -> (u64, IngressWork, String, Vec<u8>) {
        let ingress = lower_closed_expr_with_catalogs(expr, &[], constructors, &[], limits)
            .expect("closed constructor subset ingress");
        let text = ingress.fir().canonical_text();
        let flbc = fir::lower_to_flbc(ingress.fir()).expect("validated FIR lowers");
        let bytes =
            encode_canonical(&flbc, CodecLimits::default()).expect("canonical FLBC artifact");
        (ingress.source_expr_hash(), ingress.work(), text, bytes)
    }

    fn closure_identity(
        expr: &Expr,
        intrinsics: &[IntrinsicBinding],
        lambdas: &[LambdaBinding],
        limits: IngressLimits,
    ) -> (u64, IngressWork, String, Vec<u8>) {
        let ingress = lower_closed_expr_with_lambdas(expr, intrinsics, &[], &[], lambdas, limits)
            .expect("closed local-closure subset ingress");
        let text = ingress.fir().canonical_text();
        let flbc = fir::lower_to_flbc(ingress.fir()).expect("validated FIR lowers");
        let bytes =
            encode_canonical(&flbc, CodecLimits::default()).expect("canonical FLBC artifact");
        (ingress.source_expr_hash(), ingress.work(), text, bytes)
    }

    #[test]
    fn literal_metadata_and_nested_let_ingress_preserve_core_semantics() {
        let source = nested_let();
        let ingress =
            lower_closed_expr(&source, IngressLimits::default()).expect("supported expression");
        assert_eq!(ingress.source_expr_hash(), source.hash());
        assert_eq!(
            ingress.work(),
            IngressWork {
                visited_nodes: 6,
                source_bindings: 2,
                capture_analysis_nodes: 0,
                captured_values: 0,
                elided_capture_slots: 0,
                intrinsic_calls: 0,
                constructor_calls: 0,
                projection_calls: 0,
                function_calls: 0,
                lambda_conversions: 0,
                recursive_self_closures: 0,
                mutual_group_closures: 0,
                closure_applications: 0,
                generated_constructors: 0,
                generated_projections: 0,
                generated_closure_types: 0,
                generated_functions: 1,
                function_parameters: 0,
                generated_values: 2,
                literal_bytes: 0,
                maximum_context_depth: 2,
            }
        );
        assert_eq!(
            ingress.fir().canonical_text(),
            concat!(
                "fir/12 entry=f0\n",
                "function f0 params=[] ownership=[] result=nat result_ownership=scalar\n",
                " block b0\n",
                "  v0:nat = nat 40\n",
                "  v1:nat = nat 2\n",
                "  return v0\n",
            )
        );

        let text = lower_closed_expr(&string("hello"), IngressLimits::default())
            .expect("String literal")
            .fir()
            .canonical_text();
        assert!(text.contains("v0:string = string 5:68656c6c6f"));
    }

    #[test]
    fn ten_thousand_metadata_nodes_are_ingressed_without_rust_recursion() {
        let mut source = nat(7);
        for _ in 0..10_000 {
            source = Expr::mdata(KVMap::new(), source);
        }
        let limits = IngressLimits {
            max_nodes: 10_001,
            ..IngressLimits::default()
        };
        let ingress = lower_closed_expr(&source, limits).expect("iterative ingress");
        assert_eq!(ingress.work().visited_nodes, 10_001);
        assert_eq!(ingress.work().generated_values, 1);
        assert_eq!(ingress.work().maximum_context_depth, 0);
    }

    #[test]
    fn open_unresolved_unsupported_and_large_literals_never_publish() {
        assert_eq!(
            lower_closed_expr(
                &Expr::fvar(FVarId(Name::anonymous())),
                IngressLimits::default()
            ),
            Err(IngressError::OpenFreeVariable)
        );
        assert_eq!(
            lower_closed_expr(
                &Expr::mvar(MVarId(Name::anonymous())),
                IngressLimits::default()
            ),
            Err(IngressError::UnresolvedMetavariable)
        );
        assert_eq!(
            lower_closed_expr(
                &Expr::bvar(0).expect("small bvar"),
                IngressLimits::default()
            ),
            Err(IngressError::LooseBoundVariables { range: 1 })
        );
        assert_eq!(
            lower_closed_expr(
                &Expr::const_(Name::anonymous(), Vec::new()),
                IngressLimits::default()
            ),
            Err(IngressError::UnknownConstant { name_hash: 1723 })
        );
        assert_eq!(
            lower_closed_expr(&Expr::app(nat(0), nat(1)), IngressLimits::default()),
            Err(IngressError::LambdaApplicationOperandType {
                actual: fir::ValueType::Nat,
            })
        );
        assert_eq!(
            lower_closed_expr(
                &Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![0, 1]))),
                IngressLimits::default()
            ),
            Err(IngressError::NatLiteralTooWide { limbs: 2 })
        );
        let maximum = (usize::MAX >> 1) as u64;
        assert_eq!(
            lower_closed_expr(
                &Expr::lit(Literal::Nat(NatLit::from_u64(maximum + 1))),
                IngressLimits::default()
            ),
            Err(IngressError::NatLiteralOutOfAbiRange {
                value: maximum + 1,
                maximum,
            })
        );
    }

    #[test]
    fn every_unsupported_executable_constructor_is_a_typed_refusal() {
        let cases = [
            (Expr::sort(Level::zero()), "sort"),
            (
                Expr::forall_e(
                    Name::anonymous(),
                    Expr::sort(Level::zero()),
                    Expr::bvar(0).expect("small bound variable"),
                    BinderInfo::Default,
                ),
                "forall",
            ),
        ];
        for (source, kind) in cases {
            assert_eq!(
                lower_closed_expr(&source, IngressLimits::default()),
                Err(IngressError::UnsupportedNode { kind })
            );
        }
        let lambda = Expr::lam(
            Name::anonymous(),
            Expr::sort(Level::zero()),
            Expr::bvar(0).expect("small bound variable"),
            BinderInfo::Default,
        );
        assert_eq!(
            lower_closed_expr(&lambda, IngressLimits::default()),
            Err(IngressError::UnknownLambda {
                lambda_hash: lambda.hash(),
            })
        );
        let projection = Expr::proj(Name::anonymous(), 0, nat(0));
        assert_eq!(
            lower_closed_expr(&projection, IngressLimits::default()),
            Err(IngressError::UnknownProjection {
                name_hash: Name::anonymous().hash(),
                field: 0,
            })
        );
    }

    #[test]
    fn direct_intrinsic_applications_are_typed_canonical_fir() {
        let source = direct_call(
            &["Nat", "add"],
            [direct_call(&["Nat", "add"], [nat(20), nat(21)]), nat(1)],
        );
        let catalog = pure_catalog();
        let ingress =
            lower_closed_expr_with_intrinsics(&source, &catalog, IngressLimits::default())
                .expect("saturated direct intrinsic calls");
        assert_eq!(
            ingress.work(),
            IngressWork {
                visited_nodes: 9,
                source_bindings: 0,
                capture_analysis_nodes: 0,
                captured_values: 0,
                elided_capture_slots: 0,
                intrinsic_calls: 2,
                constructor_calls: 0,
                projection_calls: 0,
                function_calls: 0,
                lambda_conversions: 0,
                recursive_self_closures: 0,
                mutual_group_closures: 0,
                closure_applications: 0,
                generated_constructors: 0,
                generated_projections: 0,
                generated_closure_types: 0,
                generated_functions: 1,
                function_parameters: 0,
                generated_values: 5,
                literal_bytes: 0,
                maximum_context_depth: 0,
            }
        );
        assert_eq!(
            ingress.fir().canonical_text(),
            concat!(
                "fir/12 entry=f0\n",
                "intrinsic i0 row=14:65787465726e3a4e61742e616464 args=[nat,nat] ownership=[borrowed,borrowed] result=nat result_ownership=owned effect=pure\n",
                "intrinsic i1 row=20:65787465726e3a537472696e672e617070656e64 args=[string,string] ownership=[owned,borrowed] result=string result_ownership=owned effect=pure\n",
                "function f0 params=[] ownership=[] result=nat result_ownership=scalar\n",
                " block b0\n",
                "  v0:nat = nat 20\n",
                "  v1:nat = nat 21\n",
                "  v2:nat = intrinsic i0 [v0,v1]\n",
                "  v3:nat = nat 1\n",
                "  v4:nat = intrinsic i0 [v2,v3]\n",
                "  return v4\n",
            )
        );
    }

    #[test]
    fn constructor_catalog_is_typed_canonical_and_lowers_to_abi_shape() {
        let source = direct_call(&["User", "Pair", "mk"], [nat(42), string("answer")]);
        let unused = constructor_binding(&["User", "Empty", "mk"], 3, Vec::new(), Vec::new());
        let pair = pair_constructor_binding();
        let ingress = lower_closed_expr_with_catalogs(
            &source,
            &[],
            &[pair, unused],
            &[],
            IngressLimits::default(),
        )
        .expect("typed constructor catalog");
        assert_eq!(
            ingress.work(),
            IngressWork {
                visited_nodes: 5,
                source_bindings: 0,
                capture_analysis_nodes: 0,
                captured_values: 0,
                elided_capture_slots: 0,
                intrinsic_calls: 0,
                constructor_calls: 1,
                projection_calls: 0,
                function_calls: 0,
                lambda_conversions: 0,
                recursive_self_closures: 0,
                mutual_group_closures: 0,
                closure_applications: 0,
                generated_constructors: 2,
                generated_projections: 0,
                generated_closure_types: 0,
                generated_functions: 1,
                function_parameters: 0,
                generated_values: 3,
                literal_bytes: 6,
                maximum_context_depth: 0,
            }
        );
        assert_eq!(
            ingress.fir().canonical_text(),
            concat!(
                "fir/12 entry=f0\n",
                "constructor c0 tag=7 fields=[nat,string] scalar_bytes=2:abcd\n",
                "constructor c1 tag=3 fields=[] scalar_bytes=0:\n",
                "function f0 params=[] ownership=[] result=ctor result_ownership=owned\n",
                " block b0\n",
                "  v0:nat = nat 42\n",
                "  v1:string = string 6:616e73776572\n",
                "  v2:ctor = ctor c0 fields=[v0,v1]\n",
                "  return v2\n",
            )
        );
        let lowered = fir::lower_to_flbc(ingress.fir()).expect("constructor FIR lowers");
        assert!(matches!(
            &lowered.functions()[0].code[2],
            crate::flbc::Instruction::Ctor {
                tag: 7,
                fields,
                scalar_bytes,
                ..
            } if fields == &[crate::flbc::Register::new(0), crate::flbc::Register::new(1)]
                && scalar_bytes == &[0xAB, 0xCD]
        ));
    }

    #[test]
    fn constructor_catalog_and_call_refusals_are_exact() {
        let pair = pair_constructor_binding();
        let name_hash = pair.name.hash();

        assert_eq!(
            lower_closed_expr_with_catalogs(
                &Expr::const_(pair.name.clone(), vec![Level::zero()]),
                &[],
                std::slice::from_ref(&pair),
                &[],
                IngressLimits::default(),
            ),
            Err(IngressError::ConstructorUniverseArity {
                name_hash,
                expected: 0,
                actual: 1,
            })
        );
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &Expr::const_(pair.name.clone(), Vec::new()),
                &[],
                std::slice::from_ref(&pair),
                &[],
                IngressLimits::default(),
            ),
            Err(IngressError::ConstructorTermArity {
                name_hash,
                expected: 2,
                actual: 0,
            })
        );
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &direct_call(&["User", "Pair", "mk"], [string("wrong"), string("ok")]),
                &[],
                std::slice::from_ref(&pair),
                &[],
                IngressLimits::default(),
            ),
            Err(IngressError::ConstructorArgumentType {
                name_hash,
                argument: 0,
                expected: fir::ValueType::Nat,
                actual: fir::ValueType::String,
            })
        );

        let mut duplicate = pair.clone();
        duplicate.tag = 8;
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &nat(0),
                &[],
                &[pair.clone(), duplicate],
                &[],
                IngressLimits::default(),
            ),
            Err(IngressError::DuplicateConstructorName {
                name_hash,
                first: 0,
                second: 1,
            })
        );

        let anonymous = ConstructorBinding {
            name: Name::anonymous(),
            projection_structure: None,
            universe_arity: 0,
            tag: 0,
            fields: Vec::new(),
            static_scalar_bytes: Vec::new(),
        };
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &nat(0),
                &[],
                &[anonymous],
                &[],
                IngressLimits::default(),
            ),
            Err(IngressError::AnonymousConstructorName { binding: 0 })
        );

        let intrinsic_collision = constructor_binding(&["Nat", "add"], 0, Vec::new(), Vec::new());
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &nat(0),
                &[nat_add_binding()],
                &[intrinsic_collision],
                &[],
                IngressLimits::default(),
            ),
            Err(IngressError::ConstructorIntrinsicNameCollision {
                name_hash: Name::from_components(["Nat", "add"]).hash(),
                constructor: 0,
                intrinsic: 0,
            })
        );

        let function_collision =
            constructor_binding(&["User", "identity"], 0, Vec::new(), Vec::new());
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &nat(0),
                &[],
                &[function_collision],
                &[identity_function_binding()],
                IngressLimits::default(),
            ),
            Err(IngressError::ConstructorFunctionNameCollision {
                name_hash: Name::from_components(["User", "identity"]).hash(),
                constructor: 0,
                function: 0,
            })
        );

        let bad_tag = constructor_binding(
            &["User", "BadTag"],
            abi::TAG_MAX_CTOR_TAG
                .checked_add(1)
                .expect("one invalid tag fits u8"),
            Vec::new(),
            Vec::new(),
        );
        assert!(matches!(
            lower_closed_expr_with_catalogs(
                &nat(0),
                &[],
                &[bad_tag],
                &[],
                IngressLimits::default(),
            ),
            Err(IngressError::FirValidation(
                fir::ValidationError::ConstructorTagOutOfRange {
                    constructor,
                    ..
                }
            )) if constructor == fir::ConstructorId::new(0)
        ));

        let too_many_fields = constructor_binding(
            &["User", "TooWide"],
            0,
            vec![fir::ValueType::Abi; abi::MAX_CTOR_FIELDS],
            Vec::new(),
        );
        assert!(matches!(
            lower_closed_expr_with_catalogs(
                &nat(0),
                &[],
                &[too_many_fields],
                &[],
                IngressLimits::default(),
            ),
            Err(IngressError::FirValidation(
                fir::ValidationError::TooManyConstructorFields {
                    constructor,
                    count,
                }
            )) if constructor == fir::ConstructorId::new(0) && count == abi::MAX_CTOR_FIELDS
        ));
    }

    #[test]
    fn ten_thousand_nested_constructor_calls_use_the_same_heap_worklist() {
        let empty = constructor_binding(&["User", "Box", "empty"], 0, Vec::new(), Vec::new());
        let wrap = constructor_binding(
            &["User", "Box", "wrap"],
            1,
            vec![fir::ValueType::Constructor],
            Vec::new(),
        );
        let mut source = direct_call(&["User", "Box", "empty"], []);
        for _ in 0..10_000 {
            source = direct_call(&["User", "Box", "wrap"], [source]);
        }
        let limits = IngressLimits {
            max_nodes: 20_001,
            ..IngressLimits::default()
        };
        let ingress = lower_closed_expr_with_catalogs(&source, &[], &[wrap, empty], &[], limits)
            .expect("iterative constructor ingress");
        assert_eq!(ingress.work().visited_nodes, 20_001);
        assert_eq!(ingress.work().constructor_calls, 10_001);
        assert_eq!(ingress.work().generated_values, 10_001);
    }

    #[test]
    fn constructor_catalog_order_is_erased_but_every_unused_layout_is_identity() {
        let alpha = constructor_binding(&["User", "Alpha"], 1, Vec::new(), Vec::new());
        let beta = constructor_binding(&["User", "Beta"], 2, vec![fir::ValueType::Nat], vec![0x11]);
        let left = lower_closed_expr_with_catalogs(
            &nat(0),
            &[],
            &[beta.clone(), alpha.clone()],
            &[],
            IngressLimits::default(),
        )
        .expect("first constructor order");
        let right = lower_closed_expr_with_catalogs(
            &nat(0),
            &[],
            &[alpha, beta.clone()],
            &[],
            IngressLimits::default(),
        )
        .expect("second constructor order");
        assert_eq!(left.fir().canonical_text(), right.fir().canonical_text());

        let mut changed_beta = beta;
        changed_beta.static_scalar_bytes[0] = 0x22;
        let changed = lower_closed_expr_with_catalogs(
            &nat(0),
            &[],
            &[
                constructor_binding(&["User", "Alpha"], 1, Vec::new(), Vec::new()),
                changed_beta,
            ],
            &[],
            IngressLimits::default(),
        )
        .expect("changed unused layout");
        assert_ne!(left.fir().canonical_text(), changed.fir().canonical_text());
        assert_eq!(left.fir().constructors().len(), 2);
        assert_eq!(changed.fir().constructors().len(), 2);
    }

    #[test]
    fn projection_catalog_is_typed_canonical_and_lowers_to_checked_flbc() {
        let structure_name = Name::from_components(["User", "Pair"]);
        let source = Expr::proj(
            structure_name,
            1,
            direct_call(&["User", "Pair", "mk"], [nat(42), string("answer")]),
        );
        let pair = projected_pair_constructor_binding();
        let ingress =
            lower_closed_expr_with_catalogs(&source, &[], &[pair], &[], IngressLimits::default())
                .expect("typed projection catalog");
        assert_eq!(
            ingress.work(),
            IngressWork {
                visited_nodes: 6,
                source_bindings: 0,
                capture_analysis_nodes: 0,
                captured_values: 0,
                elided_capture_slots: 0,
                intrinsic_calls: 0,
                constructor_calls: 1,
                projection_calls: 1,
                function_calls: 0,
                lambda_conversions: 0,
                recursive_self_closures: 0,
                mutual_group_closures: 0,
                closure_applications: 0,
                generated_constructors: 1,
                generated_projections: 2,
                generated_closure_types: 0,
                generated_functions: 1,
                function_parameters: 0,
                generated_values: 4,
                literal_bytes: 6,
                maximum_context_depth: 0,
            }
        );
        assert_eq!(
            ingress.fir().canonical_text(),
            concat!(
                "fir/12 entry=f0\n",
                "constructor c0 tag=7 fields=[nat,string] scalar_bytes=2:abcd\n",
                "projection p0 constructor=c0 field=0\n",
                "projection p1 constructor=c0 field=1\n",
                "function f0 params=[] ownership=[] result=string result_ownership=owned\n",
                " block b0\n",
                "  v0:nat = nat 42\n",
                "  v1:string = string 6:616e73776572\n",
                "  v2:ctor = ctor c0 fields=[v0,v1]\n",
                "  v3:string = project p1 v2\n",
                "  return v3\n",
            )
        );
        let lowered = fir::lower_to_flbc(ingress.fir()).expect("projection FIR lowers");
        assert!(matches!(
            lowered.functions()[0].code[3],
            crate::flbc::Instruction::CtorField {
                expected_tag: 7,
                expected_fields: 2,
                field: 1,
                ..
            }
        ));
    }

    #[test]
    fn projection_binding_and_operand_refusals_are_exact() {
        let mut anonymous = projected_pair_constructor_binding();
        anonymous.projection_structure = Some(Name::anonymous());
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &nat(0),
                &[],
                &[anonymous],
                &[],
                IngressLimits::default(),
            ),
            Err(IngressError::AnonymousProjectionStructureName { binding: 0 })
        );

        let pair = projected_pair_constructor_binding();
        let mut duplicate = constructor_binding(
            &["User", "Other", "mk"],
            9,
            vec![fir::ValueType::Nat],
            Vec::new(),
        );
        duplicate.projection_structure = Some(Name::from_components(["User", "Pair"]));
        let projection_name_hash = Name::from_components(["User", "Pair"]).hash();
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &nat(0),
                &[],
                &[pair.clone(), duplicate],
                &[],
                IngressLimits::default(),
            ),
            Err(IngressError::DuplicateProjectionStructureName {
                name_hash: projection_name_hash,
                first: 0,
                second: 1,
            })
        );

        let unknown_name = Name::from_components(["User", "Missing"]);
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &Expr::proj(unknown_name.clone(), 0, nat(0)),
                &[],
                std::slice::from_ref(&pair),
                &[],
                IngressLimits::default(),
            ),
            Err(IngressError::UnknownProjection {
                name_hash: unknown_name.hash(),
                field: 0,
            })
        );
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &Expr::proj(Name::from_components(["User", "Pair"]), 2, nat(0)),
                &[],
                std::slice::from_ref(&pair),
                &[],
                IngressLimits::default(),
            ),
            Err(IngressError::UnknownProjection {
                name_hash: projection_name_hash,
                field: 2,
            })
        );
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &Expr::proj(Name::from_components(["User", "Pair"]), 0, nat(0)),
                &[],
                std::slice::from_ref(&pair),
                &[],
                IngressLimits::default(),
            ),
            Err(IngressError::ProjectionOperandType {
                name_hash: projection_name_hash,
                field: 0,
                actual: fir::ValueType::Nat,
            })
        );

        let mut limits = IngressLimits::default();
        limits.fir.max_projections = 1;
        assert_eq!(
            lower_closed_expr_with_catalogs(&nat(0), &[], &[pair], &[], limits),
            Err(IngressError::FirValidation(
                fir::ValidationError::ResourceLimit {
                    resource: fir::ValidationResource::Projections,
                    limit: 1,
                    observed: 2,
                }
            ))
        );
    }

    #[test]
    fn ten_thousand_nested_projections_use_the_same_heap_worklist() {
        let empty = constructor_binding(&["User", "Box", "empty"], 0, Vec::new(), Vec::new());
        let mut wrap = constructor_binding(
            &["User", "Box", "wrap"],
            1,
            vec![fir::ValueType::Constructor],
            Vec::new(),
        );
        let structure_name = Name::from_components(["User", "Box"]);
        wrap.projection_structure = Some(structure_name.clone());

        let mut source = direct_call(&["User", "Box", "empty"], []);
        for _ in 0..10_000 {
            source = direct_call(&["User", "Box", "wrap"], [source]);
        }
        for _ in 0..10_000 {
            source = Expr::proj(structure_name.clone(), 0, source);
        }
        let limits = IngressLimits {
            max_nodes: 30_001,
            ..IngressLimits::default()
        };
        let ingress = lower_closed_expr_with_catalogs(&source, &[], &[wrap, empty], &[], limits)
            .expect("iterative projection ingress");
        assert_eq!(ingress.work().visited_nodes, 30_001);
        assert_eq!(ingress.work().constructor_calls, 10_001);
        assert_eq!(ingress.work().projection_calls, 10_000);
        assert_eq!(ingress.work().generated_projections, 1);
        assert_eq!(ingress.work().generated_values, 20_001);
    }

    #[test]
    fn projection_catalog_order_is_erased_but_unused_rows_are_identity() {
        let mut alpha = constructor_binding(
            &["User", "Alpha", "mk"],
            1,
            vec![fir::ValueType::Nat],
            Vec::new(),
        );
        alpha.projection_structure = Some(Name::from_components(["User", "Alpha"]));
        let mut beta = constructor_binding(
            &["User", "Beta", "mk"],
            2,
            vec![fir::ValueType::String],
            Vec::new(),
        );
        beta.projection_structure = Some(Name::from_components(["User", "Beta"]));
        let left = lower_closed_expr_with_catalogs(
            &nat(0),
            &[],
            &[beta.clone(), alpha.clone()],
            &[],
            IngressLimits::default(),
        )
        .expect("first projection catalog order");
        let right = lower_closed_expr_with_catalogs(
            &nat(0),
            &[],
            &[alpha, beta.clone()],
            &[],
            IngressLimits::default(),
        )
        .expect("second projection catalog order");
        assert_eq!(left.fir().canonical_text(), right.fir().canonical_text());
        assert_eq!(left.fir().projections().len(), 2);

        beta.projection_structure = None;
        let changed = lower_closed_expr_with_catalogs(
            &nat(0),
            &[],
            &[
                {
                    let mut alpha = constructor_binding(
                        &["User", "Alpha", "mk"],
                        1,
                        vec![fir::ValueType::Nat],
                        Vec::new(),
                    );
                    alpha.projection_structure = Some(Name::from_components(["User", "Alpha"]));
                    alpha
                },
                beta,
            ],
            &[],
            IngressLimits::default(),
        )
        .expect("changed unused projection binding");
        assert_ne!(left.fir().canonical_text(), changed.fir().canonical_text());
        assert_eq!(changed.fir().projections().len(), 1);
    }

    #[test]
    fn first_order_function_catalog_lowers_every_body_to_typed_calls() {
        let source = direct_call(&["User", "twice"], [nat(40)]);
        let functions = vec![twice_function_binding(), inc_function_binding()];
        let ingress = lower_closed_expr_with_catalogs(
            &source,
            &[nat_add_binding()],
            &[],
            &functions,
            IngressLimits::default(),
        )
        .expect("typed first-order catalog");
        assert_eq!(
            ingress.work(),
            IngressWork {
                visited_nodes: 13,
                source_bindings: 0,
                capture_analysis_nodes: 0,
                captured_values: 0,
                elided_capture_slots: 0,
                intrinsic_calls: 1,
                constructor_calls: 0,
                projection_calls: 0,
                function_calls: 3,
                lambda_conversions: 0,
                recursive_self_closures: 0,
                mutual_group_closures: 0,
                closure_applications: 0,
                generated_constructors: 0,
                generated_projections: 0,
                generated_closure_types: 0,
                generated_functions: 3,
                function_parameters: 2,
                generated_values: 6,
                literal_bytes: 0,
                maximum_context_depth: 1,
            }
        );
        assert_eq!(
            ingress.fir().canonical_text(),
            concat!(
                "fir/12 entry=f0\n",
                "intrinsic i0 row=14:65787465726e3a4e61742e616464 args=[nat,nat] ownership=[borrowed,borrowed] result=nat result_ownership=owned effect=pure\n",
                "function f0 params=[] ownership=[] result=nat result_ownership=scalar\n",
                " block b0\n",
                "  v0:nat = nat 40\n",
                "  v1:nat = call f2 [v0]\n",
                "  return v1\n",
                "function f1 params=[nat] ownership=[borrowed] result=nat result_ownership=scalar\n",
                " block b0\n",
                "  v1:nat = nat 1\n",
                "  v2:nat = intrinsic i0 [v0,v1]\n",
                "  return v2\n",
                "function f2 params=[nat] ownership=[borrowed] result=nat result_ownership=scalar\n",
                " block b0\n",
                "  v1:nat = call f1 [v0]\n",
                "  v2:nat = call f1 [v1]\n",
                "  return v2\n",
            )
        );
    }

    #[test]
    fn abi_boundaries_are_explicit_canonical_and_resource_accounted() {
        let identity = function_binding(
            &["User", "abiIdentity"],
            vec![fir::ValueType::Abi],
            fir::ValueType::Abi,
            Expr::bvar(0).expect("ABI identity parameter"),
        );
        let recover = function_binding(
            &["User", "recoverNat"],
            vec![fir::ValueType::Abi],
            fir::ValueType::Nat,
            Expr::bvar(0).expect("ABI value recovered at the result boundary"),
        );
        let boxed_result = function_binding(
            &["User", "boxedResult"],
            Vec::new(),
            fir::ValueType::Abi,
            nat(1),
        );
        let mut holder = constructor_binding(
            &["User", "Holder", "mk"],
            3,
            vec![fir::ValueType::Abi],
            Vec::new(),
        );
        let holder_name = Name::from_components(["User", "Holder"]);
        holder.projection_structure = Some(holder_name.clone());

        let recovered = direct_call(
            &["User", "recoverNat"],
            [direct_call(&["User", "abiIdentity"], [nat(20)])],
        );
        let projected = Expr::proj(
            holder_name,
            0,
            direct_call(&["User", "Holder", "mk"], [nat(21)]),
        );
        let source = direct_call(
            &["Nat", "add"],
            [
                recovered,
                direct_call(
                    &["Nat", "add"],
                    [projected, direct_call(&["User", "boxedResult"], [])],
                ),
            ],
        );
        let functions = vec![recover.clone(), identity.clone(), boxed_result.clone()];
        let ingress = lower_closed_expr_with_catalogs(
            &source,
            &[nat_add_binding()],
            std::slice::from_ref(&holder),
            &functions,
            IngressLimits::default(),
        )
        .expect("typed ABI boundaries publish validated FIR");

        let mut boxes = 0usize;
        let mut unboxes = 0usize;
        for operation in ingress
            .fir()
            .functions()
            .iter()
            .flat_map(|function| &function.blocks)
            .flat_map(|block| &block.bindings)
            .map(|binding| &binding.operation)
        {
            match operation {
                fir::Operation::Box(_) => boxes += 1,
                fir::Operation::Unbox { .. } => unboxes += 1,
                _ => {}
            }
        }
        assert_eq!((boxes, unboxes), (3, 3));
        assert!(ingress.fir().canonical_text().contains(" = box v"));
        assert!(ingress.fir().canonical_text().contains(" = unbox nat v"));

        let reversed_functions = vec![boxed_result, identity, recover];
        let reversed = lower_closed_expr_with_catalogs(
            &source,
            &[nat_add_binding()],
            std::slice::from_ref(&holder),
            &reversed_functions,
            IngressLimits::default(),
        )
        .expect("catalog reversal preserves the ABI-boundary program");
        assert_eq!(
            ingress.fir().canonical_text(),
            reversed.fir().canonical_text()
        );
        let canonical = encode_canonical(
            &fir::lower_to_flbc(ingress.fir()).expect("ABI boundaries lower"),
            CodecLimits::default(),
        )
        .expect("ABI-boundary FLBC encodes canonically");
        assert_eq!(
            encode_canonical(
                &fir::lower_to_flbc(reversed.fir()).expect("reversed ABI boundaries lower"),
                CodecLimits::default(),
            )
            .expect("reversed ABI-boundary FLBC encodes canonically"),
            canonical
        );

        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    let repeated = lower_closed_expr_with_catalogs(
                        &source,
                        &[nat_add_binding()],
                        std::slice::from_ref(&holder),
                        &functions,
                        IngressLimits::default(),
                    )
                    .expect("threaded ABI-boundary ingress");
                    (
                        repeated.fir().canonical_text(),
                        encode_canonical(
                            &fir::lower_to_flbc(repeated.fir())
                                .expect("threaded ABI boundaries lower"),
                            CodecLimits::default(),
                        )
                        .expect("threaded ABI-boundary FLBC encodes"),
                    )
                }));
            }
            for join in joins {
                let (text, bytes) = join.join().expect("ABI-boundary identity worker");
                assert_eq!(text, ingress.fir().canonical_text());
                assert_eq!(bytes, canonical);
            }
        });

        let observed = ingress
            .work()
            .function_parameters
            .saturating_add(ingress.work().generated_values);
        let mut limits = IngressLimits::default();
        limits.fir.max_values = observed.saturating_sub(1);
        assert!(matches!(
            lower_closed_expr_with_catalogs(
                &source,
                &[nat_add_binding()],
                std::slice::from_ref(&holder),
                &functions,
                limits,
            ),
            Err(IngressError::FirValidation(
                fir::ValidationError::ResourceLimit {
                    resource: fir::ValidationResource::Values,
                    limit,
                    observed: refused,
                }
            )) if limit == observed.saturating_sub(1) && refused == observed
        ));
    }

    #[test]
    fn closure_arguments_and_results_cross_only_explicit_abi_boundaries() {
        let abi_to_nat = lambda(Expr::bvar(0).expect("ABI lambda parameter"));
        let recovered = lower_closed_expr_with_lambdas(
            &Expr::app(abi_to_nat.clone(), nat(42)),
            &[],
            &[],
            &[],
            &[lambda_binding(
                &abi_to_nat,
                vec![fir::ValueType::Abi],
                fir::ValueType::Nat,
            )],
            IngressLimits::default(),
        )
        .expect("closure argument boxes and result unboxes");
        let recovered_text = recovered.fir().canonical_text();
        assert_eq!(recovered_text.matches(" = box v").count(), 1);
        assert_eq!(recovered_text.matches(" = unbox nat v").count(), 1);

        let nat_to_abi = lambda(Expr::bvar(0).expect("concrete lambda parameter"));
        let boxed = lower_closed_expr_with_lambdas(
            &direct_call(
                &["Nat", "add"],
                [Expr::app(nat_to_abi.clone(), nat(41)), nat(1)],
            ),
            &[nat_add_binding()],
            &[],
            &[],
            &[lambda_binding(
                &nat_to_abi,
                vec![fir::ValueType::Nat],
                fir::ValueType::Abi,
            )],
            IngressLimits::default(),
        )
        .expect("closure result boxes and its typed consumer unboxes");
        let boxed_text = boxed.fir().canonical_text();
        assert_eq!(boxed_text.matches(" = box v").count(), 1);
        assert_eq!(boxed_text.matches(" = unbox nat v").count(), 1);

        for program in [recovered.fir(), boxed.fir()] {
            let lowered = fir::lower_to_flbc(program).expect("closure ABI boundaries lower");
            assert_eq!(
                lowered
                    .functions()
                    .iter()
                    .flat_map(|function| &function.code)
                    .filter(|instruction| {
                        matches!(instruction, crate::flbc::Instruction::Copy { .. })
                    })
                    .count(),
                2
            );
        }
    }

    #[test]
    fn function_parameters_preserve_call_order_and_de_bruijn_meaning() {
        let mut join = function_binding(
            &["User", "join"],
            vec![fir::ValueType::String, fir::ValueType::String],
            fir::ValueType::String,
            direct_call(
                &["String", "append"],
                [
                    Expr::bvar(1).expect("first parameter"),
                    Expr::bvar(0).expect("second parameter"),
                ],
            ),
        );
        join.parameter_ownership = vec![
            crate::flbc::ArgumentOwnership::Owned,
            crate::flbc::ArgumentOwnership::Borrowed,
        ];
        let source = direct_call(&["User", "join"], [string("left"), string("-right")]);
        let ingress = lower_closed_expr_with_catalogs(
            &source,
            &[string_append_binding()],
            &[],
            &[join],
            IngressLimits::default(),
        )
        .expect("two-parameter body");
        let text = ingress.fir().canonical_text();
        assert!(text.contains(
            "function f1 params=[string,string] ownership=[owned,borrowed] result=string"
        ));
        assert!(text.contains("v2:string = intrinsic i0 [v0,v1]"));
        assert!(text.contains("v2:string = call f1 [v0,v1]"));
        let lowered = fir::lower_to_flbc(ingress.fir()).expect("owned direct call lowers");
        assert_eq!(
            lowered.functions()[1].parameter_ownership,
            [
                crate::flbc::ArgumentOwnership::Owned,
                crate::flbc::ArgumentOwnership::Borrowed,
            ]
        );
        assert!(matches!(
            &lowered.functions()[0].code[2],
            crate::flbc::Instruction::Call {
                function,
                argument_ownership,
                ..
            } if *function == crate::flbc::FunctionId::new(1)
                && argument_ownership
                    == &[
                        crate::flbc::ArgumentOwnership::Owned,
                        crate::flbc::ArgumentOwnership::Borrowed,
                    ]
        ));
    }

    #[test]
    fn first_order_catalog_and_call_refusals_are_exact() {
        let identity = identity_function_binding();
        let name_hash = identity.name.hash();

        let mut missing_ownership = identity.clone();
        missing_ownership.parameter_ownership.clear();
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &nat(0),
                &[],
                &[],
                &[missing_ownership],
                IngressLimits::default(),
            ),
            Err(IngressError::FunctionOwnershipArity {
                binding: 0,
                parameters: 1,
                ownership: 0,
            })
        );

        assert_eq!(
            lower_closed_expr_with_catalogs(
                &Expr::const_(identity.name.clone(), vec![Level::zero()]),
                &[],
                &[],
                std::slice::from_ref(&identity),
                IngressLimits::default(),
            ),
            Err(IngressError::FunctionUniverseArity {
                name_hash,
                expected: 0,
                actual: 1,
            })
        );
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &Expr::const_(identity.name.clone(), Vec::new()),
                &[],
                &[],
                std::slice::from_ref(&identity),
                IngressLimits::default(),
            ),
            Err(IngressError::FunctionTermArity {
                name_hash,
                expected: 1,
                actual: 0,
            })
        );
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &direct_call(&["User", "identity"], [string("wrong")]),
                &[],
                &[],
                std::slice::from_ref(&identity),
                IngressLimits::default(),
            ),
            Err(IngressError::FunctionArgumentType {
                name_hash,
                argument: 0,
                expected: fir::ValueType::Nat,
                actual: fir::ValueType::String,
            })
        );

        let wrong_result = function_binding(
            &["User", "wrongResult"],
            Vec::new(),
            fir::ValueType::String,
            nat(0),
        );
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &nat(0),
                &[],
                &[],
                std::slice::from_ref(&wrong_result),
                IngressLimits::default(),
            ),
            Err(IngressError::FunctionResultType {
                name_hash: wrong_result.name.hash(),
                expected: fir::ValueType::String,
                actual: fir::ValueType::Nat,
            })
        );

        let mut duplicate = identity.clone();
        duplicate.body = nat(1);
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &nat(0),
                &[],
                &[],
                &[identity.clone(), duplicate],
                IngressLimits::default(),
            ),
            Err(IngressError::DuplicateFunctionName {
                name_hash,
                first: 0,
                second: 1,
            })
        );

        let collision = function_binding(&["Nat", "add"], Vec::new(), fir::ValueType::Nat, nat(0));
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &nat(0),
                &[nat_add_binding()],
                &[],
                &[collision],
                IngressLimits::default(),
            ),
            Err(IngressError::CallableNameCollision {
                name_hash: Name::from_components(["Nat", "add"]).hash(),
                intrinsic: 0,
                function: 0,
            })
        );

        let anonymous = function_binding(&[], Vec::new(), fir::ValueType::Nat, nat(0));
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &nat(0),
                &[],
                &[],
                &[anonymous],
                IngressLimits::default(),
            ),
            Err(IngressError::AnonymousFunctionName { binding: 0 })
        );

        let loose = function_binding(
            &["User", "loose"],
            vec![fir::ValueType::Nat],
            fir::ValueType::Nat,
            Expr::bvar(1).expect("small bvar"),
        );
        assert_eq!(
            lower_closed_expr_with_catalogs(&nat(0), &[], &[], &[loose], IngressLimits::default(),),
            Err(IngressError::FunctionBodyLooseBoundVariables {
                binding: 0,
                range: 2,
                parameters: 1,
            })
        );

        let open = function_binding(
            &["User", "open"],
            Vec::new(),
            fir::ValueType::Nat,
            Expr::fvar(FVarId(Name::anonymous())),
        );
        assert_eq!(
            lower_closed_expr_with_catalogs(&nat(0), &[], &[], &[open], IngressLimits::default(),),
            Err(IngressError::FunctionBodyOpenFreeVariable { binding: 0 })
        );

        let unresolved = function_binding(
            &["User", "unresolved"],
            Vec::new(),
            fir::ValueType::Nat,
            Expr::mvar(MVarId(Name::anonymous())),
        );
        assert_eq!(
            lower_closed_expr_with_catalogs(
                &nat(0),
                &[],
                &[],
                &[unresolved],
                IngressLimits::default(),
            ),
            Err(IngressError::FunctionBodyUnresolvedMetavariable { binding: 0 })
        );
    }

    #[test]
    fn recursive_function_bodies_compile_without_host_recursion() {
        let loop_name = Name::from_components(["User", "loop"]);
        let recursive = FunctionBinding {
            name: loop_name,
            universe_arity: 0,
            parameters: vec![fir::ValueType::Nat],
            parameter_ownership: vec![crate::flbc::ArgumentOwnership::Borrowed],
            result: fir::ValueType::Nat,
            result_ownership: crate::flbc::CallableResultOwnership::Scalar,
            body: direct_call(&["User", "loop"], [Expr::bvar(0).expect("small bvar")]),
        };
        let ingress = lower_closed_expr_with_catalogs(
            &nat(0),
            &[],
            &[],
            &[recursive],
            IngressLimits::default(),
        )
        .expect("recursive edge is an ordinary FIR call");
        assert_eq!(ingress.work().function_calls, 1);
        assert!(
            ingress
                .fir()
                .canonical_text()
                .contains("v1:nat = call f1 [v0]")
        );
    }

    #[test]
    fn ten_thousand_nested_function_calls_use_the_same_heap_worklist() {
        let mut source = nat(0);
        for _ in 0..10_000 {
            source = direct_call(&["User", "identity"], [source]);
        }
        let limits = IngressLimits {
            max_nodes: 20_002,
            ..IngressLimits::default()
        };
        let ingress = lower_closed_expr_with_catalogs(
            &source,
            &[],
            &[],
            &[identity_function_binding()],
            limits,
        )
        .expect("iterative first-order call ingress");
        assert_eq!(ingress.work().visited_nodes, 20_002);
        assert_eq!(ingress.work().function_calls, 10_000);
        assert_eq!(ingress.work().generated_values, 10_001);
    }

    #[test]
    fn local_lambda_capture_is_typed_canonical_and_lowers_to_flbc() {
        let closure = lambda(direct_call(
            &["String", "append"],
            [
                Expr::bvar(0).expect("lambda parameter"),
                Expr::bvar(1).expect("captured suffix"),
            ],
        ));
        let source = Expr::let_e(
            Name::from_components(["suffix"]),
            ignored_type(),
            string("!"),
            Expr::let_e(
                Name::from_components(["appendSuffix"]),
                ignored_type(),
                closure.clone(),
                Expr::app(Expr::bvar(0).expect("bound closure"), string("hello")),
                false,
            ),
            false,
        );
        let annotations = [lambda_binding(
            &closure,
            vec![fir::ValueType::String],
            fir::ValueType::String,
        )];
        let ingress = lower_closed_expr_with_lambdas(
            &source,
            &[string_append_binding()],
            &[],
            &[],
            &annotations,
            IngressLimits::default(),
        )
        .expect("typed captured lambda");
        assert_eq!(
            ingress.work(),
            IngressWork {
                visited_nodes: 12,
                source_bindings: 2,
                capture_analysis_nodes: 5,
                captured_values: 1,
                elided_capture_slots: 0,
                intrinsic_calls: 1,
                constructor_calls: 0,
                projection_calls: 0,
                function_calls: 0,
                lambda_conversions: 1,
                recursive_self_closures: 0,
                mutual_group_closures: 0,
                closure_applications: 1,
                generated_constructors: 0,
                generated_projections: 0,
                generated_closure_types: 1,
                generated_functions: 2,
                function_parameters: 2,
                generated_values: 5,
                literal_bytes: 6,
                maximum_context_depth: 2,
            }
        );
        assert_eq!(
            ingress.fir().canonical_text(),
            concat!(
                "fir/12 entry=f0\n",
                "closure_type s0 params=[string] ownership=[borrowed] result=string result_ownership=owned\n",
                "intrinsic i0 row=20:65787465726e3a537472696e672e617070656e64 args=[string,string] ownership=[owned,borrowed] result=string result_ownership=owned effect=pure\n",
                "function f0 params=[] ownership=[] result=string result_ownership=owned\n",
                " block b0\n",
                "  v0:string = string 1:21\n",
                "  v1:closure:s0 = closure s0 f1 captures=[v0] ownership=[borrowed]\n",
                "  v2:string = string 5:68656c6c6f\n",
                "  v3:string = apply v1 args=[v2] ownership=[borrowed] result_ownership=owned\n",
                "  return v3\n",
                "function f1 params=[string,string] ownership=[borrowed,borrowed] result=string result_ownership=owned\n",
                " block b0\n",
                "  v2:string = intrinsic i0 [v1,v0]\n",
                "  return v2\n",
            )
        );
        let lowered = fir::lower_to_flbc(ingress.fir()).expect("checked closure lowering");
        assert!(matches!(
            &lowered.functions()[0].code[1],
            crate::flbc::Instruction::Closure {
                function,
                captures,
                ..
            } if *function == crate::flbc::FunctionId::new(1) && captures.len() == 1
        ));
        assert!(matches!(
            &lowered.functions()[0].code[3],
            crate::flbc::Instruction::Apply { args, .. } if args.len() == 1
        ));
    }

    #[test]
    fn minimal_capture_keeps_source_slots_and_compacts_runtime_parameters() {
        let closure = lambda(Expr::let_e(
            Name::from_components(["unusedLocal"]),
            ignored_type(),
            string("ignored"),
            direct_call(
                &["String", "append"],
                [
                    Expr::bvar(1).expect("lambda parameter beyond local let"),
                    Expr::bvar(3).expect("captured suffix beyond both unused neighbors"),
                ],
            ),
            false,
        ));
        let source = Expr::let_e(
            Name::from_components(["suffix"]),
            ignored_type(),
            string("!"),
            Expr::let_e(
                Name::from_components(["unused"]),
                ignored_type(),
                nat(99),
                Expr::app(closure.clone(), string("hello")),
                false,
            ),
            false,
        );
        let annotations = [lambda_binding(
            &closure,
            vec![fir::ValueType::String],
            fir::ValueType::String,
        )];
        let ingress = lower_closed_expr_with_lambdas(
            &source,
            &[string_append_binding()],
            &[],
            &[],
            &annotations,
            IngressLimits::default(),
        )
        .expect("unused neighboring binding is not captured");
        assert_eq!(ingress.work().visited_nodes, 14);
        assert_eq!(ingress.work().source_bindings, 3);
        assert_eq!(ingress.work().capture_analysis_nodes, 7);
        assert_eq!(ingress.work().captured_values, 1);
        assert_eq!(ingress.work().elided_capture_slots, 1);
        assert_eq!(ingress.work().function_parameters, 2);
        assert_eq!(ingress.work().maximum_context_depth, 4);
        assert_eq!(ingress.work().generated_values, 7);
        assert!(ingress.fir().canonical_text().contains(
            "function f1 params=[string,string] ownership=[borrowed,borrowed] result=string",
        ));
        assert!(
            ingress
                .fir()
                .canonical_text()
                .contains("v3:string = intrinsic i0 [v1,v0]")
        );

        let lowered = fir::lower_to_flbc(ingress.fir()).expect("checked minimal-capture lowering");
        assert!(matches!(
            &lowered.functions()[0].code[2],
            crate::flbc::Instruction::Closure {
                function,
                captures,
                ..
            } if *function == crate::flbc::FunctionId::new(1) && captures.len() == 1
        ));
    }

    #[test]
    fn nested_lambdas_propagate_transitive_captures_without_capturing_neighbors() {
        let inner = named_lambda(
            "prefix",
            direct_call(
                &["String", "append"],
                [
                    Expr::bvar(0).expect("inner parameter"),
                    Expr::bvar(2).expect("suffix beyond outer parameter"),
                ],
            ),
        );
        let outer = named_lambda(
            "unusedOuterParameter",
            Expr::app(inner.clone(), string("hello")),
        );
        let source = Expr::let_e(
            Name::from_components(["suffix"]),
            ignored_type(),
            string("!"),
            Expr::app(outer.clone(), nat(0)),
            false,
        );
        let outer_binding =
            lambda_binding(&outer, vec![fir::ValueType::Nat], fir::ValueType::String);
        let inner_binding =
            lambda_binding(&inner, vec![fir::ValueType::String], fir::ValueType::String);
        let intrinsics = [string_append_binding()];
        let annotations = [outer_binding.clone(), inner_binding.clone()];
        let ingress = lower_closed_expr_with_lambdas(
            &source,
            &intrinsics,
            &[],
            &[],
            &annotations,
            IngressLimits::default(),
        )
        .expect("nested capture is propagated through the outer closure");
        assert_eq!(ingress.work().visited_nodes, 13);
        assert_eq!(ingress.work().capture_analysis_nodes, 13);
        assert_eq!(ingress.work().captured_values, 2);
        assert_eq!(ingress.work().elided_capture_slots, 1);
        assert_eq!(ingress.work().lambda_conversions, 2);
        assert_eq!(ingress.work().closure_applications, 2);
        assert_eq!(ingress.work().generated_closure_types, 2);
        assert_eq!(ingress.work().generated_functions, 3);
        assert_eq!(ingress.work().function_parameters, 4);
        assert_eq!(ingress.work().generated_values, 8);
        assert_eq!(ingress.work().maximum_context_depth, 3);

        let lowered = fir::lower_to_flbc(ingress.fir()).expect("checked nested-closure lowering");
        assert!(matches!(
            &lowered.functions()[0].code[1],
            crate::flbc::Instruction::Closure {
                function,
                captures,
                ..
            } if *function == crate::flbc::FunctionId::new(1) && captures.len() == 1
        ));
        assert!(matches!(
            &lowered.functions()[1].code[0],
            crate::flbc::Instruction::Closure {
                function,
                captures,
                ..
            } if *function == crate::flbc::FunctionId::new(2) && captures.len() == 1
        ));

        let identity = closure_identity(
            &source,
            &intrinsics,
            &[inner_binding.clone(), outer_binding.clone()],
            IngressLimits::default(),
        );
        assert_eq!(
            identity,
            closure_identity(
                &source,
                &intrinsics,
                &[outer_binding.clone(), inner_binding.clone()],
                IngressLimits::default(),
            )
        );
        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    closure_identity(
                        &source,
                        &intrinsics,
                        &[outer_binding.clone(), inner_binding.clone()],
                        IngressLimits::default(),
                    )
                }));
            }
            for join in joins {
                assert_eq!(
                    join.join().expect("nested capture identity worker"),
                    identity
                );
            }
        });
    }

    #[test]
    fn lambda_catalog_and_dynamic_application_refusals_are_exact() {
        let identity = lambda(Expr::bvar(0).expect("lambda parameter"));
        let annotation = lambda_binding(&identity, vec![fir::ValueType::Nat], fir::ValueType::Nat);

        assert_eq!(
            lower_closed_expr_with_lambdas(
                &nat(0),
                &[],
                &[],
                &[],
                &[LambdaBinding {
                    lambda: nat(1),
                    parameters: vec![fir::ValueType::Nat],
                    parameter_ownership: vec![crate::flbc::ArgumentOwnership::Borrowed],
                    result: fir::ValueType::Nat,
                    result_ownership: crate::flbc::CallableResultOwnership::Scalar,
                    recursion: LambdaRecursion::NonRecursive,
                }],
                IngressLimits::default(),
            ),
            Err(IngressError::LambdaBindingNotLambda { binding: 0 })
        );
        assert_eq!(
            lower_closed_expr_with_lambdas(
                &identity,
                &[],
                &[],
                &[],
                &[lambda_binding(
                    &identity,
                    vec![fir::ValueType::Nat, fir::ValueType::Nat],
                    fir::ValueType::Nat,
                )],
                IngressLimits::default(),
            ),
            Err(IngressError::LambdaParameterCount {
                binding: 0,
                expected: 2,
                actual: 1,
            })
        );
        let mut missing_ownership = annotation.clone();
        missing_ownership.parameter_ownership.clear();
        assert_eq!(
            lower_closed_expr_with_lambdas(
                &identity,
                &[],
                &[],
                &[],
                &[missing_ownership],
                IngressLimits::default(),
            ),
            Err(IngressError::LambdaOwnershipArity {
                binding: 0,
                parameters: 1,
                ownership: 0,
            })
        );
        let recursive = named_lambda(
            "self",
            named_lambda("argument", Expr::bvar(1).expect("recursive self binder")),
        );
        assert_eq!(
            lower_closed_expr_with_lambdas(
                &recursive,
                &[],
                &[],
                &[],
                &[lambda_binding(
                    &recursive,
                    vec![fir::ValueType::Nat],
                    fir::ValueType::Closure(fir::ClosureTypeId::new(0)),
                )],
                IngressLimits::default(),
            ),
            Err(IngressError::LambdaParameterCount {
                binding: 0,
                expected: 1,
                actual: 2,
            })
        );
        assert_eq!(
            lower_closed_expr_with_lambdas(
                &identity,
                &[],
                &[],
                &[],
                &[self_recursive_lambda_binding(
                    &identity,
                    vec![fir::ValueType::Nat],
                    fir::ValueType::Nat,
                )],
                IngressLimits::default(),
            ),
            Err(IngressError::LambdaParameterCount {
                binding: 0,
                expected: 2,
                actual: 1,
            })
        );
        assert_eq!(
            lower_closed_expr_with_lambdas(
                &identity,
                &[],
                &[],
                &[],
                &[annotation.clone(), annotation.clone()],
                IngressLimits::default(),
            ),
            Err(IngressError::DuplicateLambdaBinding {
                lambda_hash: identity.hash(),
                first: 0,
                second: 1,
            })
        );
        assert_eq!(
            lower_closed_expr_with_lambdas(
                &identity,
                &[],
                &[],
                &[],
                &[lambda_binding(
                    &identity,
                    vec![fir::ValueType::Closure(fir::ClosureTypeId::new(99))],
                    fir::ValueType::Nat,
                )],
                IngressLimits::default(),
            ),
            Err(IngressError::LambdaClosureTypeOutOfRange {
                binding: 0,
                parameter: Some(0),
                closure_type: fir::ClosureTypeId::new(99),
                known: 1,
            })
        );
        assert_eq!(
            lower_closed_expr_with_lambdas(
                &identity,
                &[],
                &[],
                &[],
                &[lambda_binding(
                    &identity,
                    vec![fir::ValueType::Nat],
                    fir::ValueType::Closure(fir::ClosureTypeId::new(99)),
                )],
                IngressLimits::default(),
            ),
            Err(IngressError::LambdaClosureTypeOutOfRange {
                binding: 0,
                parameter: None,
                closure_type: fir::ClosureTypeId::new(99),
                known: 1,
            })
        );
        assert_eq!(
            lower_closed_expr_with_lambdas(&identity, &[], &[], &[], &[], IngressLimits::default(),),
            Err(IngressError::UnknownLambda {
                lambda_hash: identity.hash(),
            })
        );
        assert_eq!(
            lower_closed_expr_with_lambdas(
                &nat(0),
                &[],
                &[],
                &[],
                std::slice::from_ref(&annotation),
                IngressLimits::default(),
            ),
            Err(IngressError::UnusedLambdaBinding {
                binding: 0,
                lambda_hash: identity.hash(),
            })
        );

        let overapplied = Expr::app(Expr::app(identity.clone(), nat(1)), nat(2));
        assert_eq!(
            lower_closed_expr_with_lambdas(
                &overapplied,
                &[],
                &[],
                &[],
                std::slice::from_ref(&annotation),
                IngressLimits::default(),
            ),
            Err(IngressError::LambdaApplicationRemainderType {
                closure_type: fir::ClosureTypeId::new(0),
                argument: 1,
                actual: fir::ValueType::Nat,
            })
        );
        assert_eq!(
            lower_closed_expr_with_lambdas(
                &Expr::app(identity.clone(), string("wrong")),
                &[],
                &[],
                &[],
                std::slice::from_ref(&annotation),
                IngressLimits::default(),
            ),
            Err(IngressError::LambdaApplicationArgumentType {
                closure_type: fir::ClosureTypeId::new(0),
                argument: 0,
                expected: fir::ValueType::Nat,
                actual: fir::ValueType::String,
            })
        );
        let wrong_result =
            lambda_binding(&identity, vec![fir::ValueType::Nat], fir::ValueType::String);
        assert_eq!(
            lower_closed_expr_with_lambdas(
                &Expr::app(identity.clone(), nat(1)),
                &[],
                &[],
                &[],
                &[wrong_result],
                IngressLimits::default(),
            ),
            Err(IngressError::LambdaResultType {
                binding: 0,
                expected: fir::ValueType::String,
                actual: fir::ValueType::Nat,
            })
        );
    }

    #[test]
    fn mutual_group_catalog_refusals_are_exact() {
        let singleton = named_lambda(
            "only",
            named_lambda("argument", Expr::bvar(0).expect("singleton parameter")),
        );
        assert_eq!(
            lower_closed_expr_with_lambdas(
                &nat(0),
                &[],
                &[],
                &[],
                &[mutual_lambda_binding(
                    &singleton,
                    vec![fir::ValueType::Nat],
                    fir::ValueType::Nat,
                    7,
                    0,
                    1,
                )],
                IngressLimits::default(),
            ),
            Err(IngressError::LambdaMutualGroupTooSmall {
                binding: 0,
                group: 7,
                members: 1,
            })
        );

        let first = named_lambda(
            "first",
            named_lambda(
                "second",
                named_lambda("argument", Expr::bvar(0).expect("first parameter")),
            ),
        );
        assert_eq!(
            lower_closed_expr_with_lambdas(
                &nat(0),
                &[],
                &[],
                &[],
                &[mutual_lambda_binding(
                    &first,
                    vec![fir::ValueType::Nat],
                    fir::ValueType::Nat,
                    8,
                    2,
                    2,
                )],
                IngressLimits::default(),
            ),
            Err(IngressError::LambdaMutualGroupMemberOutOfRange {
                binding: 0,
                group: 8,
                member: 2,
                members: 2,
            })
        );
        assert_eq!(
            lower_closed_expr_with_lambdas(
                &nat(0),
                &[],
                &[],
                &[],
                &[mutual_lambda_binding(
                    &first,
                    vec![fir::ValueType::Nat],
                    fir::ValueType::Nat,
                    9,
                    0,
                    2,
                )],
                IngressLimits::default(),
            ),
            Err(IngressError::MissingLambdaMutualGroupMember {
                group: 9,
                member: 1,
                members: 2,
            })
        );

        let second = named_lambda(
            "left",
            named_lambda("right", named_lambda("argument", nat(0))),
        );
        assert_eq!(
            lower_closed_expr_with_lambdas(
                &nat(0),
                &[],
                &[],
                &[],
                &[
                    mutual_lambda_binding(
                        &first,
                        vec![fir::ValueType::Nat],
                        fir::ValueType::Nat,
                        10,
                        0,
                        2,
                    ),
                    mutual_lambda_binding(
                        &second,
                        vec![fir::ValueType::Nat],
                        fir::ValueType::Nat,
                        10,
                        0,
                        2,
                    ),
                ],
                IngressLimits::default(),
            ),
            Err(IngressError::DuplicateLambdaMutualGroupMember {
                group: 10,
                member: 0,
                first: 0,
                second: 1,
            })
        );

        let three_member_spine = named_lambda(
            "first",
            named_lambda(
                "second",
                named_lambda("third", named_lambda("argument", nat(0))),
            ),
        );
        assert_eq!(
            lower_closed_expr_with_lambdas(
                &nat(0),
                &[],
                &[],
                &[],
                &[
                    mutual_lambda_binding(
                        &first,
                        vec![fir::ValueType::Nat],
                        fir::ValueType::Nat,
                        11,
                        0,
                        2,
                    ),
                    mutual_lambda_binding(
                        &three_member_spine,
                        vec![fir::ValueType::Nat],
                        fir::ValueType::Nat,
                        11,
                        1,
                        3,
                    ),
                ],
                IngressLimits::default(),
            ),
            Err(IngressError::LambdaMutualGroupMemberCountMismatch {
                binding: 1,
                group: 11,
                expected: 2,
                actual: 3,
            })
        );

        let identity = lambda(Expr::bvar(0).expect("ordinary parameter"));
        assert_eq!(
            lower_closed_expr_with_lambdas(
                &identity,
                &[],
                &[],
                &[],
                &[mutual_lambda_binding(
                    &identity,
                    vec![fir::ValueType::Nat],
                    fir::ValueType::Nat,
                    12,
                    0,
                    2,
                )],
                IngressLimits::default(),
            ),
            Err(IngressError::LambdaParameterCount {
                binding: 0,
                expected: 3,
                actual: 1,
            })
        );
    }

    #[test]
    fn higher_order_lambda_arguments_and_results_have_one_canonical_identity() {
        let nat_to_nat = fir::ValueType::Closure(fir::ClosureTypeId::new(0));
        let identity = named_lambda("identity", Expr::bvar(0).expect("identity parameter"));
        let apply = named_lambda(
            "apply",
            Expr::app(Expr::bvar(0).expect("closure parameter"), nat(41)),
        );
        let pass_source = Expr::app(apply.clone(), identity.clone());
        let identity_binding =
            lambda_binding(&identity, vec![fir::ValueType::Nat], fir::ValueType::Nat);
        let apply_binding = lambda_binding(&apply, vec![nat_to_nat], fir::ValueType::Nat);
        let pass_identity = closure_identity(
            &pass_source,
            &[],
            &[apply_binding.clone(), identity_binding.clone()],
            IngressLimits::default(),
        );
        assert_eq!(
            pass_identity,
            closure_identity(
                &pass_source,
                &[],
                &[identity_binding.clone(), apply_binding.clone()],
                IngressLimits::default(),
            )
        );
        assert_eq!(pass_identity.1.lambda_conversions, 2);
        assert_eq!(pass_identity.1.closure_applications, 2);
        assert_eq!(pass_identity.1.generated_closure_types, 2);
        assert_eq!(pass_identity.1.generated_functions, 3);
        assert!(
            pass_identity
                .2
                .contains("closure_type s1 params=[closure:s0] ownership=[borrowed] result=nat")
        );

        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    closure_identity(
                        &pass_source,
                        &[],
                        &[identity_binding.clone(), apply_binding.clone()],
                        IngressLimits::default(),
                    )
                }));
            }
            for join in joins {
                assert_eq!(
                    join.join().expect("higher-order identity worker"),
                    pass_identity
                );
            }
        });

        let inner = named_lambda(
            "delta",
            direct_call(
                &["Nat", "add"],
                [
                    Expr::bvar(1).expect("captured base"),
                    Expr::bvar(0).expect("delta parameter"),
                ],
            ),
        );
        let outer = named_lambda("base", Expr::mdata(KVMap::new(), inner.clone()));
        let return_source = Expr::let_e(
            Name::from_components(["returnedClosure"]),
            ignored_type(),
            Expr::app(outer.clone(), nat(40)),
            Expr::app(Expr::bvar(0).expect("returned closure binding"), nat(2)),
            false,
        );
        let inner_binding = lambda_binding(&inner, vec![fir::ValueType::Nat], fir::ValueType::Nat);
        let outer_binding = lambda_binding(&outer, vec![fir::ValueType::Nat], nat_to_nat);
        let intrinsics = [nat_add_binding()];
        let return_identity = closure_identity(
            &return_source,
            &intrinsics,
            &[outer_binding.clone(), inner_binding.clone()],
            IngressLimits::default(),
        );
        assert_eq!(
            return_identity,
            closure_identity(
                &return_source,
                &intrinsics,
                &[inner_binding, outer_binding],
                IngressLimits::default(),
            )
        );
        assert_eq!(return_identity.1.captured_values, 1);
        assert_eq!(return_identity.1.lambda_conversions, 2);
        assert_eq!(return_identity.1.closure_applications, 2);
        assert_eq!(return_identity.1.generated_closure_types, 2);
        assert_eq!(return_identity.1.generated_functions, 3);
        assert!(
            return_identity
                .2
                .contains("closure_type s1 params=[nat] ownership=[borrowed] result=closure:s0")
        );
    }

    #[test]
    fn self_recursive_lambdas_rebuild_acyclic_canonical_closures() {
        let self_type = fir::ValueType::Closure(fir::ClosureTypeId::new(0));
        let recursive = named_lambda(
            "self",
            named_lambda("argument", Expr::bvar(1).expect("recursive self binder")),
        );
        let neighbor = named_lambda("text", Expr::bvar(0).expect("ordinary neighbor parameter"));
        let source = Expr::let_e(
            Name::from_components(["ignoredNeighbor"]),
            ignored_type(),
            Expr::app(neighbor.clone(), string("catalog")),
            Expr::app(Expr::app(recursive.clone(), nat(0)), nat(1)),
            false,
        );
        let recursive_binding =
            self_recursive_lambda_binding(&recursive, vec![fir::ValueType::Nat], self_type);
        let neighbor_binding = lambda_binding(
            &neighbor,
            vec![fir::ValueType::String],
            fir::ValueType::String,
        );
        let canonical = closure_identity(
            &source,
            &[],
            &[recursive_binding.clone(), neighbor_binding.clone()],
            IngressLimits::default(),
        );
        assert_eq!(
            canonical,
            closure_identity(
                &source,
                &[],
                &[neighbor_binding.clone(), recursive_binding.clone()],
                IngressLimits::default(),
            )
        );
        assert_eq!(canonical.1.lambda_conversions, 2);
        assert_eq!(canonical.1.recursive_self_closures, 1);
        assert_eq!(canonical.1.closure_applications, 2);
        assert_eq!(canonical.1.captured_values, 0);
        assert_eq!(canonical.1.generated_closure_types, 2);
        assert_eq!(canonical.1.generated_functions, 3);
        assert!(
            canonical
                .2
                .contains("closure_type s0 params=[nat] ownership=[borrowed] result=closure:s0")
        );
        assert!(
            canonical
                .2
                .contains("v1:closure:s0 = closure s0 f2 captures=[]")
        );

        let ingressed = lower_closed_expr_with_lambdas(
            &source,
            &[],
            &[],
            &[],
            &[neighbor_binding.clone(), recursive_binding.clone()],
            IngressLimits::default(),
        )
        .expect("self-recursive closure publishes independently validated FIR");
        let lowered =
            fir::lower_to_flbc(ingressed.fir()).expect("self-recursive FIR lowers to FLBC");
        let recursive_target = lowered
            .functions()
            .get(2)
            .expect("source evaluation assigns the recursive target function 2");
        assert!(matches!(
            recursive_target.code.first(),
            Some(crate::flbc::Instruction::Closure {
                function,
                captures,
                ..
            }) if *function == crate::flbc::FunctionId::new(2) && captures.is_empty()
        ));

        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    closure_identity(
                        &source,
                        &[],
                        &[recursive_binding.clone(), neighbor_binding.clone()],
                        IngressLimits::default(),
                    )
                }));
            }
            for join in joins {
                assert_eq!(
                    join.join().expect("recursive closure identity worker"),
                    canonical
                );
            }
        });
    }

    #[test]
    fn mutual_recursive_groups_share_one_acyclic_canonical_capture_layout() {
        let first = named_lambda(
            "first",
            named_lambda(
                "second",
                named_lambda(
                    "argument",
                    Expr::bvar(1).expect("second mutual closure binder"),
                ),
            ),
        );
        let second = named_lambda(
            "first",
            named_lambda(
                "second",
                named_lambda(
                    "text",
                    Expr::bvar(3).expect("captured string outside the mutual group"),
                ),
            ),
        );
        let source = Expr::let_e(
            Name::from_components(["captured"]),
            ignored_type(),
            string("peer-capture"),
            Expr::app(Expr::app(first.clone(), nat(0)), string("ignored-argument")),
            false,
        );
        let first_binding = mutual_lambda_binding(
            &first,
            vec![fir::ValueType::Nat],
            fir::ValueType::Closure(fir::ClosureTypeId::new(1)),
            17,
            0,
            2,
        );
        let second_binding = mutual_lambda_binding(
            &second,
            vec![fir::ValueType::String],
            fir::ValueType::String,
            17,
            1,
            2,
        );
        let canonical = closure_identity(
            &source,
            &[],
            &[first_binding.clone(), second_binding.clone()],
            IngressLimits::default(),
        );
        assert_eq!(
            canonical,
            closure_identity(
                &source,
                &[],
                &[second_binding.clone(), first_binding.clone()],
                IngressLimits::default(),
            )
        );
        assert_eq!(canonical.1.lambda_conversions, 1);
        assert_eq!(canonical.1.recursive_self_closures, 0);
        assert_eq!(canonical.1.mutual_group_closures, 4);
        assert_eq!(canonical.1.closure_applications, 1);
        assert_eq!(canonical.1.captured_values, 1);
        assert_eq!(canonical.1.generated_closure_types, 2);
        assert_eq!(canonical.1.generated_functions, 3);
        assert!(
            canonical
                .2
                .contains("closure_type s0 params=[nat] ownership=[borrowed] result=closure:s1")
        );
        assert!(
            canonical
                .2
                .contains("closure_type s1 params=[string] ownership=[borrowed] result=string")
        );
        assert!(
            canonical
                .2
                .contains("v2:closure:s0 = closure s0 f1 captures=[v0]")
        );
        assert!(
            canonical
                .2
                .contains("v3:closure:s1 = closure s1 f2 captures=[v0]")
        );

        let second_source = Expr::let_e(
            Name::from_components(["captured"]),
            ignored_type(),
            string("second-entry"),
            Expr::app(second.clone(), string("ignored-argument")),
            false,
        );
        let second_scheduled = closure_identity(
            &second_source,
            &[],
            &[first_binding.clone(), second_binding.clone()],
            IngressLimits::default(),
        );
        assert_eq!(second_scheduled.1.lambda_conversions, 1);
        assert_eq!(second_scheduled.1.mutual_group_closures, 4);
        assert_eq!(second_scheduled.1.captured_values, 1);
        assert_eq!(second_scheduled.1.generated_functions, 3);
        assert!(second_scheduled.2.contains("closure s1 f2 captures=[v0]"));

        let ingressed = lower_closed_expr_with_lambdas(
            &source,
            &[],
            &[],
            &[],
            &[second_binding.clone(), first_binding.clone()],
            IngressLimits::default(),
        )
        .expect("mutual group publishes independently validated FIR");
        let lowered = fir::lower_to_flbc(ingressed.fir())
            .expect("mutual group lowers through the independent FLBC validator");
        for target in &lowered.functions()[1..=2] {
            assert!(matches!(
                target.code.first(),
                Some(crate::flbc::Instruction::Closure {
                    function,
                    captures,
                    ..
                }) if *function == crate::flbc::FunctionId::new(1) && captures.len() == 1
            ));
            assert!(matches!(
                target.code.get(1),
                Some(crate::flbc::Instruction::Closure {
                    function,
                    captures,
                    ..
                }) if *function == crate::flbc::FunctionId::new(2) && captures.len() == 1
            ));
        }

        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    closure_identity(
                        &source,
                        &[],
                        &[first_binding.clone(), second_binding.clone()],
                        IngressLimits::default(),
                    )
                }));
            }
            for join in joins {
                assert_eq!(
                    join.join().expect("mutual closure identity worker"),
                    canonical
                );
            }
        });
    }

    #[test]
    fn partial_repeated_and_overapplication_have_one_typed_identity() {
        let add_pair = named_lambda(
            "left",
            named_lambda(
                "right",
                direct_call(
                    &["Nat", "add"],
                    [
                        Expr::bvar(1).expect("left parameter"),
                        Expr::bvar(0).expect("right parameter"),
                    ],
                ),
            ),
        );
        let add_pair_binding = lambda_binding(
            &add_pair,
            vec![fir::ValueType::Nat, fir::ValueType::Nat],
            fir::ValueType::Nat,
        );
        let partial_source = Expr::let_e(
            Name::from_components(["partial"]),
            ignored_type(),
            Expr::app(add_pair.clone(), nat(20)),
            Expr::app(Expr::bvar(0).expect("partial closure"), nat(22)),
            false,
        );
        let intrinsics = [nat_add_binding()];
        let partial_identity = closure_identity(
            &partial_source,
            &intrinsics,
            std::slice::from_ref(&add_pair_binding),
            IngressLimits::default(),
        );
        assert_eq!(partial_identity.1.lambda_conversions, 1);
        assert_eq!(partial_identity.1.closure_applications, 2);
        assert_eq!(partial_identity.1.generated_closure_types, 2);
        assert_eq!(partial_identity.1.generated_functions, 2);
        assert!(
            partial_identity
                .2
                .contains("closure_type s0 params=[nat] ownership=[borrowed] result=nat")
        );
        assert!(
            partial_identity.2.contains(
                "closure_type s1 params=[nat,nat] ownership=[borrowed,borrowed] result=nat",
            )
        );
        let partial = lower_closed_expr_with_lambdas(
            &partial_source,
            &intrinsics,
            &[],
            &[],
            std::slice::from_ref(&add_pair_binding),
            IngressLimits::default(),
        )
        .expect("partial application publishes typed FIR");
        let partial_flbc =
            fir::lower_to_flbc(partial.fir()).expect("partial application lowers to FLBC");
        let partial_widths = partial_flbc
            .functions()
            .iter()
            .flat_map(|function| &function.code)
            .filter_map(|instruction| match instruction {
                crate::flbc::Instruction::Apply { args, .. } => Some(args.len()),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(partial_widths, [1, 1]);

        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    closure_identity(
                        &partial_source,
                        &intrinsics,
                        std::slice::from_ref(&add_pair_binding),
                        IngressLimits::default(),
                    )
                }));
            }
            for join in joins {
                assert_eq!(
                    join.join().expect("partial application identity worker"),
                    partial_identity
                );
            }
        });

        let inner = named_lambda(
            "rhs",
            direct_call(
                &["Nat", "add"],
                [
                    Expr::bvar(1).expect("captured lhs"),
                    Expr::bvar(0).expect("rhs parameter"),
                ],
            ),
        );
        let outer = named_lambda("lhs", Expr::mdata(KVMap::new(), inner.clone()));
        let nat_to_nat = fir::ValueType::Closure(fir::ClosureTypeId::new(0));
        let outer_binding = lambda_binding(&outer, vec![fir::ValueType::Nat], nat_to_nat);
        let inner_binding = lambda_binding(&inner, vec![fir::ValueType::Nat], fir::ValueType::Nat);
        let over_source = Expr::app(Expr::app(outer.clone(), nat(20)), nat(22));
        let over_identity = closure_identity(
            &over_source,
            &intrinsics,
            &[outer_binding.clone(), inner_binding.clone()],
            IngressLimits::default(),
        );
        assert_eq!(
            over_identity,
            closure_identity(
                &over_source,
                &intrinsics,
                &[inner_binding, outer_binding],
                IngressLimits::default(),
            )
        );
        assert_eq!(over_identity.1.captured_values, 1);
        assert_eq!(over_identity.1.lambda_conversions, 2);
        assert_eq!(over_identity.1.closure_applications, 1);
        let over = lower_closed_expr_with_lambdas(
            &over_source,
            &intrinsics,
            &[],
            &[],
            &[
                lambda_binding(&outer, vec![fir::ValueType::Nat], nat_to_nat),
                lambda_binding(&inner, vec![fir::ValueType::Nat], fir::ValueType::Nat),
            ],
            IngressLimits::default(),
        )
        .expect("closure-result overapplication publishes typed FIR");
        let over_flbc =
            fir::lower_to_flbc(over.fir()).expect("closure-result overapplication lowers");
        let over_widths = over_flbc
            .functions()
            .iter()
            .flat_map(|function| &function.code)
            .filter_map(|instruction| match instruction {
                crate::flbc::Instruction::Apply { args, .. } => Some(args.len()),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(over_widths, [2]);
    }

    #[test]
    fn an_elided_source_slot_is_a_typed_refusal_if_capture_analysis_and_lowering_disagree() {
        let catalog = prepare_catalog(&[], &[], &[], &[], IngressLimits::default())
            .expect("empty catalog is canonical");
        let mut closure_build = ClosureBuild::new(&catalog).expect("empty closure worklist");
        let context = vec![
            None,
            Some(CompiledValue {
                id: fir::ValueId::new(0),
                ty: fir::ValueType::Nat,
            }),
        ];
        let mut work = IngressWork {
            visited_nodes: 0,
            source_bindings: 0,
            capture_analysis_nodes: 0,
            captured_values: 0,
            elided_capture_slots: 0,
            intrinsic_calls: 0,
            constructor_calls: 0,
            projection_calls: 0,
            function_calls: 0,
            lambda_conversions: 0,
            recursive_self_closures: 0,
            mutual_group_closures: 0,
            closure_applications: 0,
            generated_constructors: 0,
            generated_projections: 0,
            generated_closure_types: 0,
            generated_functions: 1,
            function_parameters: 1,
            generated_values: 0,
            literal_bytes: 0,
            maximum_context_depth: 0,
        };
        assert!(matches!(
            lower_body(
                &Expr::bvar(1).expect("source slot within the declared context"),
                LowerBodySeed {
                    context,
                    parameter_count: 1,
                    bindings: Vec::new(),
                },
                None,
                &catalog,
                IngressLimits::default(),
                &mut work,
                &mut closure_build,
            ),
            Err(IngressError::MissingCapturedBoundVariable {
                index: 1,
                context_depth: 2,
            })
        ));
    }

    #[test]
    fn lambda_catalog_order_repetition_and_threads_have_one_identity() {
        let first = named_lambda("first", Expr::bvar(0).expect("first parameter"));
        let second = named_lambda(
            "second",
            direct_call(
                &["Nat", "add"],
                [Expr::bvar(0).expect("second parameter"), nat(1)],
            ),
        );
        let source = direct_call(
            &["Nat", "add"],
            [
                Expr::app(first.clone(), nat(20)),
                Expr::app(second.clone(), nat(20)),
            ],
        );
        let first_binding = lambda_binding(&first, vec![fir::ValueType::Nat], fir::ValueType::Nat);
        let second_binding =
            lambda_binding(&second, vec![fir::ValueType::Nat], fir::ValueType::Nat);
        let intrinsics = [nat_add_binding()];
        let left = closure_identity(
            &source,
            &intrinsics,
            &[second_binding.clone(), first_binding.clone()],
            IngressLimits::default(),
        );
        let right = closure_identity(
            &source,
            &intrinsics,
            &[first_binding.clone(), second_binding.clone()],
            IngressLimits::default(),
        );
        assert_eq!(left, right);
        assert_eq!(left.1.generated_closure_types, 1);
        assert_eq!(left.1.generated_functions, 3);

        let repeated_source = direct_call(
            &["Nat", "add"],
            [
                Expr::app(first.clone(), nat(1)),
                Expr::app(first.clone(), nat(2)),
            ],
        );
        let repeated = closure_identity(
            &repeated_source,
            &intrinsics,
            std::slice::from_ref(&first_binding),
            IngressLimits::default(),
        );
        assert_eq!(repeated.1.lambda_conversions, 2);
        assert_eq!(repeated.1.generated_functions, 2);

        std::thread::scope(|scope| {
            let mut joins = Vec::new();
            for _ in 0..8 {
                joins.push(scope.spawn(|| {
                    closure_identity(
                        &source,
                        &intrinsics,
                        &[first_binding.clone(), second_binding.clone()],
                        IngressLimits::default(),
                    )
                }));
            }
            for join in joins {
                assert_eq!(join.join().expect("closure identity worker"), left);
            }
        });
    }

    #[test]
    fn ten_thousand_nested_lambda_applications_use_the_heap_worklist() {
        let identity = lambda(Expr::bvar(0).expect("lambda parameter"));
        let annotation = lambda_binding(&identity, vec![fir::ValueType::Nat], fir::ValueType::Nat);
        let mut source = nat(7);
        for _ in 0..10_000 {
            source = Expr::app(identity.clone(), source);
        }
        let limits = IngressLimits {
            max_nodes: 20_002,
            ..IngressLimits::default()
        };
        let ingress = lower_closed_expr_with_lambdas(&source, &[], &[], &[], &[annotation], limits)
            .expect("iterative local closure ingress");
        assert_eq!(ingress.work().visited_nodes, 20_002);
        assert_eq!(ingress.work().capture_analysis_nodes, 10_000);
        assert_eq!(ingress.work().captured_values, 0);
        assert_eq!(ingress.work().elided_capture_slots, 0);
        assert_eq!(ingress.work().lambda_conversions, 10_000);
        assert_eq!(ingress.work().closure_applications, 10_000);
        assert_eq!(ingress.work().generated_functions, 2);
        assert_eq!(ingress.work().generated_values, 20_001);
    }

    #[test]
    fn intrinsic_catalog_and_call_refusals_are_exact() {
        let add_name = Name::from_components(["Nat", "add"]);
        let add_hash = add_name.hash();
        let catalog = pure_catalog();

        let unknown_name = Name::from_components(["Unknown", "call"]);
        assert_eq!(
            lower_closed_expr_with_intrinsics(
                &Expr::const_(unknown_name.clone(), Vec::new()),
                &catalog,
                IngressLimits::default(),
            ),
            Err(IngressError::UnknownConstant {
                name_hash: unknown_name.hash(),
            })
        );
        assert_eq!(
            lower_closed_expr_with_intrinsics(
                &Expr::const_(add_name.clone(), Vec::new()),
                &catalog,
                IngressLimits::default(),
            ),
            Err(IngressError::IntrinsicTermArity {
                name_hash: add_hash,
                expected: 2,
                actual: 0,
            })
        );
        assert_eq!(
            lower_closed_expr_with_intrinsics(
                &direct_call(&["Nat", "add"], [nat(1), nat(2), nat(3)]),
                &catalog,
                IngressLimits::default(),
            ),
            Err(IngressError::IntrinsicTermArity {
                name_hash: add_hash,
                expected: 2,
                actual: 3,
            })
        );
        assert_eq!(
            lower_closed_expr_with_intrinsics(
                &Expr::app(
                    Expr::app(Expr::const_(add_name.clone(), vec![Level::zero()]), nat(1),),
                    nat(2),
                ),
                &catalog,
                IngressLimits::default(),
            ),
            Err(IngressError::IntrinsicUniverseArity {
                name_hash: add_hash,
                expected: 0,
                actual: 1,
            })
        );
        assert_eq!(
            lower_closed_expr_with_intrinsics(
                &direct_call(&["Nat", "add"], [string("wrong"), nat(2)]),
                &catalog,
                IngressLimits::default(),
            ),
            Err(IngressError::IntrinsicArgumentType {
                name_hash: add_hash,
                argument: 0,
                expected: fir::ValueType::Nat,
                actual: fir::ValueType::String,
            })
        );

        let mut duplicate_row = string_append_binding();
        duplicate_row.name = Name::from_components(["Other", "append"]);
        duplicate_row.row = "extern:Nat.add".to_string();
        assert_eq!(
            lower_closed_expr_with_intrinsics(
                &nat(0),
                &[nat_add_binding(), duplicate_row],
                IngressLimits::default(),
            ),
            Err(IngressError::DuplicateIntrinsicRow {
                first: 0,
                second: 1,
            })
        );

        let mut duplicate_name = string_append_binding();
        duplicate_name.name = add_name;
        assert_eq!(
            lower_closed_expr_with_intrinsics(
                &nat(0),
                &[nat_add_binding(), duplicate_name],
                IngressLimits::default(),
            ),
            Err(IngressError::DuplicateIntrinsicName {
                name_hash: add_hash,
                first: 0,
                second: 1,
            })
        );

        let mut invalid = nat_add_binding();
        invalid.row = "Nat.add".to_string();
        assert_eq!(
            lower_closed_expr_with_intrinsics(&nat(0), &[invalid], IngressLimits::default()),
            Err(IngressError::InvalidIntrinsicRow {
                binding: 0,
                row_bytes: 7,
            })
        );

        let mut ownership_short = nat_add_binding();
        ownership_short.argument_ownership.pop();
        assert_eq!(
            lower_closed_expr_with_intrinsics(
                &nat(0),
                &[ownership_short],
                IngressLimits::default(),
            ),
            Err(IngressError::IntrinsicOwnershipArity {
                binding: 0,
                arguments: 2,
                ownership: 1,
            })
        );

        let mut anonymous = nat_add_binding();
        anonymous.name = Name::anonymous();
        assert_eq!(
            lower_closed_expr_with_intrinsics(&nat(0), &[anonymous], IngressLimits::default()),
            Err(IngressError::AnonymousIntrinsicName { binding: 0 })
        );

        let mut effectful = nat_add_binding();
        effectful.effect = fir::EffectClass::Io;
        assert_eq!(
            lower_closed_expr_with_intrinsics(
                &direct_call(&["Nat", "add"], [string("wrong"), nat(2)]),
                &[effectful],
                IngressLimits::default(),
            ),
            Err(IngressError::IntrinsicArgumentType {
                name_hash: add_hash,
                argument: 0,
                expected: fir::ValueType::Nat,
                actual: fir::ValueType::String,
            })
        );

        let string_component = FunctionBinding {
            name: Name::str(Name::anonymous(), "1"),
            universe_arity: 0,
            parameters: Vec::new(),
            parameter_ownership: Vec::new(),
            result: fir::ValueType::Nat,
            result_ownership: crate::flbc::CallableResultOwnership::Scalar,
            body: nat(1),
        };
        let numeric_component = FunctionBinding {
            name: Name::num(Name::anonymous(), 1),
            universe_arity: 0,
            parameters: Vec::new(),
            parameter_ownership: Vec::new(),
            result: fir::ValueType::Nat,
            result_ownership: crate::flbc::CallableResultOwnership::Scalar,
            body: nat(2),
        };
        let structurally_distinct = lower_closed_expr_with_catalogs(
            &Expr::const_(numeric_component.name.clone(), Vec::new()),
            &[],
            &[],
            &[string_component, numeric_component],
            IngressLimits::default(),
        )
        .expect("equal display projections remain distinct structural names");
        assert_eq!(structurally_distinct.work().generated_functions, 3);
    }

    #[test]
    fn every_fir_effect_class_retains_identity_and_static_types() {
        let source = direct_call(&["Nat", "add"], [nat(20), nat(22)]);
        let cases = [
            (fir::EffectClass::Pure, "pure"),
            (fir::EffectClass::State, "state"),
            (fir::EffectClass::Io, "io"),
            (fir::EffectClass::Task, "task"),
        ];
        let mut identities = Vec::new();
        for (effect, token) in cases {
            let mut binding = nat_add_binding();
            binding.effect = effect;
            let identity = intrinsic_identity(
                &source,
                std::slice::from_ref(&binding),
                IngressLimits::default(),
            );
            assert!(
                identity.2.contains(&format!("effect={token}")),
                "FIR retains the supplied {token} effect class"
            );
            identities.push(identity);
        }
        for left in 0..identities.len() {
            for right in left.saturating_add(1)..identities.len() {
                assert_ne!(
                    identities[left].2, identities[right].2,
                    "distinct FIR effect classes cannot collapse to one identity"
                );
            }
        }
    }

    #[test]
    fn ten_thousand_nested_intrinsic_calls_use_a_heap_worklist() {
        let mut source = nat(0);
        for _ in 0..10_000 {
            source = direct_call(&["Nat", "add"], [nat(1), source]);
        }
        let limits = IngressLimits {
            max_nodes: 40_001,
            ..IngressLimits::default()
        };
        let ingress = lower_closed_expr_with_intrinsics(&source, &[nat_add_binding()], limits)
            .expect("iterative direct-call ingress");
        assert_eq!(ingress.work().visited_nodes, 40_001);
        assert_eq!(ingress.work().intrinsic_calls, 10_000);
        assert_eq!(ingress.work().generated_values, 20_001);
    }

    #[test]
    fn every_ingress_resource_dimension_is_typed() {
        let nodes = IngressLimits {
            max_nodes: 0,
            ..IngressLimits::default()
        };
        assert!(matches!(
            lower_closed_expr(&nat(0), nodes),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                limit: 0,
                observed: 1,
            })
        ));

        let source = Expr::let_e(
            Name::anonymous(),
            Expr::sort(Level::zero()),
            nat(1),
            Expr::bvar(0).expect("small bvar"),
            false,
        );
        let bindings = IngressLimits {
            max_bindings: 0,
            ..IngressLimits::default()
        };
        assert!(matches!(
            lower_closed_expr(&source, bindings),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::Bindings,
                limit: 0,
                observed: 1,
            })
        ));
        let identity = lambda(Expr::bvar(0).expect("lambda parameter"));
        let lambda_bindings = IngressLimits {
            max_lambda_bindings: 0,
            ..IngressLimits::default()
        };
        assert!(matches!(
            lower_closed_expr_with_lambdas(
                &identity,
                &[],
                &[],
                &[],
                &[lambda_binding(
                    &identity,
                    vec![fir::ValueType::Nat],
                    fir::ValueType::Nat,
                )],
                lambda_bindings,
            ),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::LambdaBindings,
                limit: 0,
                observed: 1,
            })
        ));
        let add_pair = named_lambda(
            "left",
            named_lambda("right", Expr::bvar(0).expect("right parameter")),
        );
        let closure_types = IngressLimits {
            fir: fir::ValidationLimits {
                max_closure_types: 1,
                ..fir::ValidationLimits::default()
            },
            ..IngressLimits::default()
        };
        assert!(matches!(
            lower_closed_expr_with_lambdas(
                &add_pair,
                &[],
                &[],
                &[],
                &[lambda_binding(
                    &add_pair,
                    vec![fir::ValueType::Nat, fir::ValueType::Nat],
                    fir::ValueType::Nat,
                )],
                closure_types,
            ),
            Err(IngressError::FirValidation(
                fir::ValidationError::ResourceLimit {
                    resource: fir::ValidationResource::ClosureTypes,
                    limit: 1,
                    observed: 2,
                }
            ))
        ));
        let capture_analysis = IngressLimits {
            max_capture_analysis_nodes: 0,
            ..IngressLimits::default()
        };
        assert!(matches!(
            lower_closed_expr_with_lambdas(
                &identity,
                &[],
                &[],
                &[],
                &[lambda_binding(
                    &identity,
                    vec![fir::ValueType::Nat],
                    fir::ValueType::Nat,
                )],
                capture_analysis,
            ),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::CaptureAnalysisNodes,
                limit: 0,
                observed: 1,
            })
        ));
        let context = IngressLimits {
            max_context_depth: 0,
            ..IngressLimits::default()
        };
        assert!(matches!(
            lower_closed_expr(&source, context),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::ContextDepth,
                limit: 0,
                observed: 1,
            })
        ));

        let literal = IngressLimits {
            max_literal_bytes: 3,
            ..IngressLimits::default()
        };
        assert!(matches!(
            lower_closed_expr(&string("four"), literal),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::LiteralBytes,
                limit: 3,
                observed: 4,
            })
        ));
        let constructor_literal = IngressLimits {
            max_literal_bytes: 1,
            ..IngressLimits::default()
        };
        assert!(matches!(
            lower_closed_expr_with_catalogs(
                &nat(0),
                &[],
                &[pair_constructor_binding()],
                &[],
                constructor_literal,
            ),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::LiteralBytes,
                limit: 1,
                observed: 2,
            })
        ));

        let application = IngressLimits {
            max_application_args: 1,
            ..IngressLimits::default()
        };
        assert!(matches!(
            lower_closed_expr_with_intrinsics(
                &direct_call(&["Nat", "add"], [nat(1), nat(2)]),
                &[nat_add_binding()],
                application,
            ),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::ApplicationArguments,
                limit: 1,
                observed: 2,
            })
        ));

        let mut fir_limit = IngressLimits::default();
        fir_limit.fir.max_values = 0;
        assert!(matches!(
            lower_closed_expr(&nat(0), fir_limit),
            Err(IngressError::FirValidation(
                fir::ValidationError::ResourceLimit {
                    resource: fir::ValidationResource::Values,
                    limit: 0,
                    observed: 1,
                }
            ))
        ));

        let recursive = named_lambda(
            "self",
            named_lambda("argument", Expr::bvar(1).expect("recursive self binder")),
        );
        let mut recursive_prologue = IngressLimits::default();
        recursive_prologue.fir.max_values = 1;
        assert!(matches!(
            lower_closed_expr_with_lambdas(
                &recursive,
                &[],
                &[],
                &[],
                &[self_recursive_lambda_binding(
                    &recursive,
                    vec![fir::ValueType::Nat],
                    fir::ValueType::Closure(fir::ClosureTypeId::new(0)),
                )],
                recursive_prologue,
            ),
            Err(IngressError::FirValidation(
                fir::ValidationError::ResourceLimit {
                    resource: fir::ValidationResource::Values,
                    limit: 1,
                    observed: 2,
                }
            ))
        ));

        let mutual_first = named_lambda(
            "first",
            named_lambda(
                "second",
                named_lambda("argument", Expr::bvar(1).expect("mutual peer")),
            ),
        );
        let mutual_second = named_lambda(
            "first",
            named_lambda(
                "second",
                named_lambda("argument", Expr::bvar(2).expect("mutual self")),
            ),
        );
        let mut mutual_functions = IngressLimits::default();
        mutual_functions.fir.max_functions = 2;
        assert!(matches!(
            lower_closed_expr_with_lambdas(
                &mutual_first,
                &[],
                &[],
                &[],
                &[
                    mutual_lambda_binding(
                        &mutual_first,
                        vec![fir::ValueType::Nat],
                        fir::ValueType::Closure(fir::ClosureTypeId::new(0)),
                        21,
                        0,
                        2,
                    ),
                    mutual_lambda_binding(
                        &mutual_second,
                        vec![fir::ValueType::Nat],
                        fir::ValueType::Closure(fir::ClosureTypeId::new(0)),
                        21,
                        1,
                        2,
                    ),
                ],
                mutual_functions,
            ),
            Err(IngressError::FirValidation(
                fir::ValidationError::ResourceLimit {
                    resource: fir::ValidationResource::Functions,
                    limit: 2,
                    observed: 3,
                }
            ))
        ));

        let mut functions = IngressLimits::default();
        functions.fir.max_functions = 1;
        assert!(matches!(
            lower_closed_expr_with_catalogs(
                &nat(0),
                &[],
                &[],
                &[identity_function_binding()],
                functions,
            ),
            Err(IngressError::FirValidation(
                fir::ValidationError::ResourceLimit {
                    resource: fir::ValidationResource::Functions,
                    limit: 1,
                    observed: 2,
                }
            ))
        ));

        let mut constructors = IngressLimits::default();
        constructors.fir.max_constructors = 0;
        assert!(matches!(
            lower_closed_expr_with_catalogs(
                &nat(0),
                &[],
                &[pair_constructor_binding()],
                &[],
                constructors,
            ),
            Err(IngressError::FirValidation(
                fir::ValidationError::ResourceLimit {
                    resource: fir::ValidationResource::Constructors,
                    limit: 0,
                    observed: 1,
                }
            ))
        ));
    }

    #[test]
    fn canonical_fir_and_flbc_identity_is_repeated_and_thread_stable() {
        let source = nested_let();
        let limits = IngressLimits::default();
        let expected = identity(&source, limits);
        for _ in 0..8 {
            assert_eq!(identity(&source, limits), expected);
        }
        std::thread::scope(|scope| {
            let mut handles = Vec::new();
            for _ in 0..8 {
                handles.push(scope.spawn(|| identity(&source, limits)));
            }
            for handle in handles {
                assert_eq!(handle.join().expect("ingress thread"), expected);
            }
        });

        let source = direct_call(
            &["String", "append"],
            [string("canonical"), string("-catalog")],
        );
        let catalog = pure_catalog();
        let expected = intrinsic_identity(&source, &catalog, limits);
        let mut reverse = catalog.clone();
        reverse.reverse();
        assert_eq!(intrinsic_identity(&source, &reverse, limits), expected);
        for _ in 0..8 {
            assert_eq!(intrinsic_identity(&source, &catalog, limits), expected);
        }
        std::thread::scope(|scope| {
            let mut handles = Vec::new();
            for _ in 0..8 {
                handles.push(scope.spawn(|| intrinsic_identity(&source, &catalog, limits)));
            }
            for handle in handles {
                assert_eq!(handle.join().expect("intrinsic ingress thread"), expected);
            }
        });

        let source = Expr::proj(
            Name::from_components(["User", "Pair"]),
            0,
            direct_call(&["User", "Pair", "mk"], [nat(42), string("answer")]),
        );
        let constructors = vec![
            projected_pair_constructor_binding(),
            constructor_binding(&["User", "Unused", "mk"], 3, Vec::new(), Vec::new()),
        ];
        let expected = constructor_identity(&source, &constructors, limits);
        let mut reverse = constructors.clone();
        reverse.reverse();
        assert_eq!(constructor_identity(&source, &reverse, limits), expected);
        for _ in 0..8 {
            assert_eq!(
                constructor_identity(&source, &constructors, limits),
                expected
            );
        }
        std::thread::scope(|scope| {
            let mut handles = Vec::new();
            for _ in 0..8 {
                handles.push(scope.spawn(|| constructor_identity(&source, &constructors, limits)));
            }
            for handle in handles {
                assert_eq!(handle.join().expect("projection ingress thread"), expected);
            }
        });

        let source = direct_call(&["User", "twice"], [nat(40)]);
        let intrinsics = vec![nat_add_binding()];
        let functions = vec![twice_function_binding(), inc_function_binding()];
        let expected = function_identity(&source, &intrinsics, &functions, limits);
        let mut reverse = functions.clone();
        reverse.reverse();
        assert_eq!(
            function_identity(&source, &intrinsics, &reverse, limits),
            expected
        );
        for _ in 0..8 {
            assert_eq!(
                function_identity(&source, &intrinsics, &functions, limits),
                expected
            );
        }
        std::thread::scope(|scope| {
            let mut handles = Vec::new();
            for _ in 0..8 {
                handles.push(
                    scope.spawn(|| function_identity(&source, &intrinsics, &functions, limits)),
                );
            }
            for handle in handles {
                assert_eq!(handle.join().expect("function ingress thread"), expected);
            }
        });

        let unused_one =
            function_binding(&["User", "unused"], Vec::new(), fir::ValueType::Nat, nat(1));
        let mut unused_two = unused_one.clone();
        unused_two.body = nat(2);
        assert_ne!(
            function_identity(&nat(0), &[], &[unused_one], limits),
            function_identity(&nat(0), &[], &[unused_two], limits),
            "every supplied function body participates in artifact identity"
        );
    }
}
