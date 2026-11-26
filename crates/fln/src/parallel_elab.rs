//! Production parallel source elaboration wired to [`fln_elab::DeterministicScheduler`]
//! (Bet B4, Plan §10.6, FL-INV-01).
//!
//! Effect-free source definitions are parsed into [`DataflowNode`]s with conservative
//! syntax-level name pre-scans, elaborated and K1-checked speculatively across
//! `worker_threads` via [`DeterministicScheduler::execute`], merged in canonical
//! source order with footprint-validated rebasing, and finally admitted into an
//! immutable [`Engine`] successor through the ordinary dual-checker council
//! (K1 + independent `fln-checker`). Commands with attributes, local helpers,
//! recursive equations, or other source effects use ordinary source admission
//! in source order, so their journals and checked auxiliaries are retained.
//!
//! Schedule independence (FL-INV-01): for any valid source batch, the resulting
//! `Engine` environment, `result_logical_root`, and `committed_order` are
//! identical across `worker_threads = 1, 4, 8, ...`.
#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::fmt;
use std::sync::Arc;

use fln_core::expr::{Expr, ExprNode};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::{Inconclusive, InternalFault, Outcome};
use fln_elab::{
    CommandEffect, CommandId, DataflowGraph, DataflowNode, DeclAspect, DeterministicScheduler,
    EffectSummary, ElabBudget, ElabUnitProduct, ExecutionConfig,
};
use fln_env::constants::ConstantInfo;
use fln_kernel::verdict::Verdict as KernelVerdict;
use fln_kernel::{Declaration, check};
use fln_parse::DefinitionParseError;
use fln_syntax::tree::Syntax;

use crate::{
    Engine, EngineAdmissionError, EngineAdmissionLimits, EngineExecutionError, LogicalRoot,
};

/// Failure returned by [`check_source_definitions_parallel`].
#[derive(Debug)]
pub enum ParallelElabError {
    EmptyBatch,
    Parse {
        index: usize,
        error: DefinitionParseError,
    },
    Scheduler(String),
    Admission(EngineAdmissionError),
    Source {
        index: usize,
        error: Box<EngineExecutionError>,
    },
}

impl fmt::Display for ParallelElabError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyBatch => {
                f.write_str("parallel source elaboration requires at least one command")
            }
            Self::Parse { index, error } => write!(f, "command #{index} parse error: {error:?}"),
            Self::Scheduler(detail) => write!(f, "parallel elaboration failed: {detail}"),
            Self::Admission(error) => write!(f, "dual-checker admission failed: {error:?}"),
            Self::Source { index, error } => write!(f, "command #{index} failed: {error}"),
        }
    }
}

impl std::error::Error for ParallelElabError {}

/// The execution path used for the batch. A requested worker width does not
/// imply that source effects can be applied concurrently.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParallelSourceStrategy {
    /// Definitions use the dependency scheduler; dependencies can still serialize work.
    Dataflow,
    /// Source effects require the ordinary ordered source-admission path.
    SourceOrder,
}

/// Result of checking a batch of source definitions through [`DeterministicScheduler`].
#[derive(Debug, Clone)]
pub struct ParallelSourceCheck {
    /// Immutable successor engine carrying every dual-checked declaration.
    pub engine: Engine,
    /// Logical root of the base engine before this batch.
    pub base_logical_root: LogicalRoot,
    /// Logical root of the successor engine after canonical-order commit.
    pub result_logical_root: LogicalRoot,
    /// Canonical committed command order produced by the scheduler.
    pub committed_order: Vec<CommandId>,
    /// Number of speculative rebases performed by the scheduler.
    pub retry_count: usize,
    /// Worker-thread width requested for this run.
    pub worker_threads: usize,
    /// Whether declarations used the dataflow scheduler or ordered source admission.
    pub strategy: ParallelSourceStrategy,
}

/// The scheduler publishes declarations, not source-extension transactions.
/// Admit only an explicit, effect-free syntax subset through that seam. Every
/// other supported source form still works through ordinary source admission.
/// In particular, an unknown future parser node cannot silently lose an effect.
fn uses_declaration_only_path(syntax: &Syntax) -> bool {
    if fln_elab::source::scope::simp::defeq::direct_rfl(syntax) {
        return false;
    }
    let Syntax::Node { args, .. } = syntax else {
        return false;
    };
    let [modifiers, definition] = args.as_slice() else {
        return false;
    };
    let Syntax::Node {
        args: modifiers, ..
    } = modifiers
    else {
        return false;
    };
    if modifiers
        .iter()
        .any(|modifier| !matches!(modifier, Syntax::Node { args, .. } if args.is_empty()))
    {
        return false;
    }
    if !matches!(
        definition.kind().map(Name::to_display_string).as_deref(),
        Some("Lean.Parser.Command.definition" | "Lean.Parser.Command.theorem")
    ) {
        return false;
    }
    let mut pending = vec![(definition, false)];
    while let Some((node, in_decl_id)) = pending.pop() {
        match node {
            Syntax::Ident {
                val, preresolved, ..
            } if !preresolved.is_empty() || (in_decl_id && !val.parent().is_anonymous()) => {
                return false;
            }
            Syntax::Node { kind, args, .. } => {
                let kind_name = kind.to_display_string();
                if !matches!(
                    kind_name.as_str(),
                    "null"
                        | "num"
                        | "str"
                        | "char"
                        | "scientific"
                        | "Lean.Parser.Command.definition"
                        | "Lean.Parser.Command.theorem"
                        | "Lean.Parser.Command.declId"
                        | "Lean.Parser.Command.declSig"
                        | "Lean.Parser.Command.optDeclSig"
                        | "Lean.Parser.Command.declValSimple"
                        | "Lean.Parser.Term.typeSpec"
                        | "Lean.Parser.Term.explicitBinder"
                        | "Lean.Parser.Term.implicitBinder"
                        | "Lean.Parser.Term.strictImplicitBinder"
                        | "Lean.Parser.Term.app"
                        | "Lean.Parser.Term.paren"
                        | "Lean.Parser.Term.typeAscription"
                        | "Lean.Parser.Term.arrow"
                        | "Lean.Parser.Term.type"
                        | "Lean.Parser.Term.prop"
                        | "Lean.Parser.Term.hole"
                        | "Lean.Parser.Term.explicit"
                        | "Lean.Parser.Termination.suffix"
                        | "term_+_"
                        | "term_-_"
                        | "term_*_"
                        | "term_/_"
                        | "term_%_"
                        | "term_^_"
                        | "term_++_"
                        | "term_=_"
                        | "term_≠_"
                        | "term_↔_"
                        | "term_∧_"
                        | "term_∨_"
                        | "term_¬_"
                        | "term_==_"
                        | "term_!=_"
                        | "term_&&_"
                        | "term_||_"
                        | "term_<_"
                        | "term_≤_"
                        | "term_<=_"
                        | "term_>_"
                        | "term_≥_"
                        | "term_>=_"
                ) {
                    return false;
                }
                let child_in_decl_id = in_decl_id || kind_name == "Lean.Parser.Command.declId";
                pending.extend(args.iter().map(|arg| (arg, child_in_decl_id)));
            }
            Syntax::Missing => return false,
            Syntax::Atom { .. } | Syntax::Ident { .. } => {}
        }
    }
    true
}

/// Keep the source door's typed nonanswers out of the scheduler's semantic
/// error/retry channel. The shared elaboration adapter retains complete kernel,
/// native-evaluation and macro causes. Some older frontend resource errors have
/// no quantitative usage; report that unfinished dependency without inventing
/// an allowance or an observed count.
fn source_outcome<T>(
    result: Result<Outcome<T>, EngineExecutionError>,
) -> Outcome<Result<T, EngineExecutionError>> {
    match result {
        Ok(outcome) => outcome.map_complete(Ok),
        Err(error) => match crate::source_check::classify(&error) {
            ("cancelled", _, _) => {
                Outcome::Inconclusive(Inconclusive::cancelled(error.to_string()))
            }
            (_, _, 3) => Outcome::Inconclusive(Inconclusive::dependency_unavailable(format!(
                "source elaboration did not complete: {error}"
            ))),
            (_, _, 4) => Outcome::InternalFault(InternalFault::new("FL-INV-07", error.to_string())),
            (_, _, 5) => Outcome::Inconclusive(Inconclusive::unsupported(error.to_string())),
            _ => Outcome::Complete(Err(error)),
        },
    }
}

fn check_in_source_order(
    engine: &Engine,
    sources: &[&[u8]],
    options: &KVMap,
    worker_threads: usize,
    limits: EngineAdmissionLimits,
) -> Result<Outcome<ParallelSourceCheck>, ParallelElabError> {
    let base_logical_root = engine.logical_root(options);
    let mut next = engine.clone();
    for (index, source) in sources.iter().enumerate() {
        next = match source_outcome(next.admit_source_declaration(source, options, limits)) {
            Outcome::Complete(Ok(admitted)) => admitted.engine,
            Outcome::Complete(Err(error)) => {
                return Err(ParallelElabError::Source {
                    index,
                    error: Box::new(error),
                });
            }
            Outcome::Inconclusive(stop) => return Ok(Outcome::Inconclusive(stop)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
    }
    Ok(Outcome::Complete(ParallelSourceCheck {
        base_logical_root,
        result_logical_root: next.logical_root(options),
        engine: next,
        committed_order: (0..sources.len()).map(CommandId).collect(),
        retry_count: 0,
        worker_threads: worker_threads.max(1),
        strategy: ParallelSourceStrategy::SourceOrder,
    }))
}

fn collect_syntax_identifiers(root: &Syntax) -> Vec<Name> {
    let mut stack = vec![root];
    let mut names = Vec::new();
    while let Some(node) = stack.pop() {
        match node {
            Syntax::Ident { val, .. } => names.push(val.clone()),
            Syntax::Node { args, .. } => {
                for child in args.iter().rev() {
                    stack.push(child);
                }
            }
            Syntax::Atom { .. } | Syntax::Missing => {}
        }
    }
    names
}

fn collect_expr_constants(expr: &Expr, out: &mut BTreeSet<Name>) {
    let mut stack = vec![expr];
    while let Some(current) = stack.pop() {
        match current.node() {
            ExprNode::Const { name, .. } => {
                out.insert(name.clone());
            }
            ExprNode::App { f, a } => {
                stack.push(f);
                stack.push(a);
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                stack.push(binder_type);
                stack.push(body);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                stack.push(type_);
                stack.push(value);
                stack.push(body);
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                stack.push(expr);
            }
            ExprNode::BVar { .. }
            | ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Lit { .. } => {}
        }
    }
}

fn constant_value(info: &ConstantInfo) -> Option<&Expr> {
    match info {
        ConstantInfo::Defn(v) => Some(&v.value),
        ConstantInfo::Thm(v) => Some(&v.value),
        ConstantInfo::Opaque(v) => Some(&v.value),
        _ => None,
    }
}

fn declaration_to_constants(decl: &Declaration) -> Vec<ConstantInfo> {
    match decl {
        Declaration::Axiom(v) => vec![ConstantInfo::Axiom(v.clone())],
        Declaration::Defn(v) => vec![ConstantInfo::Defn(v.clone())],
        Declaration::Thm(v) => vec![ConstantInfo::Thm(v.clone())],
        Declaration::Opaque(v) => vec![ConstantInfo::Opaque(v.clone())],
        Declaration::Mutual(defs) => defs.iter().cloned().map(ConstantInfo::Defn).collect(),
        Declaration::Inductive(block) => {
            let mut out = Vec::new();
            out.extend(block.types.iter().cloned().map(ConstantInfo::Induct));
            out.extend(block.ctors.iter().cloned().map(ConstantInfo::Ctor));
            out.extend(block.recursors.iter().cloned().map(ConstantInfo::Rec));
            out
        }
        Declaration::Quotient(quots) => quots.iter().cloned().map(ConstantInfo::Quot).collect(),
    }
}

fn constant_to_declaration(info: &ConstantInfo) -> Option<Declaration> {
    match info {
        ConstantInfo::Axiom(v) => Some(Declaration::Axiom(v.clone())),
        ConstantInfo::Defn(v) => Some(Declaration::Defn(v.clone())),
        ConstantInfo::Thm(v) => Some(Declaration::Thm(v.clone())),
        ConstantInfo::Opaque(v) => Some(Declaration::Opaque(v.clone())),
        _ => None,
    }
}

fn effects_for_constants(constants: &[ConstantInfo]) -> EffectSummary {
    let mut effects = EffectSummary::new();
    let mut reads = BTreeSet::new();
    let mut writes = BTreeSet::new();
    for info in constants {
        let name = info.name().clone();
        writes.insert(name.clone());
        effects.record(CommandEffect::WritesDecl { name });
        collect_expr_constants(&info.constant_val().type_, &mut reads);
        if let Some(val) = constant_value(info) {
            collect_expr_constants(val, &mut reads);
        }
    }
    for name in reads {
        if !writes.contains(&name) {
            effects.record(CommandEffect::ReadsDecl {
                name,
                aspect: DeclAspect::All,
            });
        }
    }
    effects
}

/// Elaborate and dual-check a sequence of source declarations, returning an
/// immutable [`Engine`] successor. Simple effect-free definitions use
/// [`DeterministicScheduler`]; richer source uses the same ordered source door
/// as [`Engine::admit_source_declaration`]. Neither route publishes a partial
/// batch or retries an exhausted/faulted elaboration as a semantic failure.
///
/// `options` has the ordinary source-admission meaning: admission/root options,
/// not a replacement for the engine's source scope. Scheduler workers allocate
/// the stack required by `limits.kernel`. Final admission and the ordered route
/// retain the ordinary `Engine` requirement that the caller supplies that stack.
/// Whether `source` is a single effect-free declaration eligible for the
/// [`DeterministicScheduler`] dataflow path, returning its declared name.
pub(crate) fn is_declaration_only_source(source: &[u8]) -> Option<Name> {
    let parsed = fln_parse::parse_definition(source)
        .and_then(fln_parse::ParsedDefinition::expanded)
        .ok()?;
    if !uses_declaration_only_path(parsed.syntax()) {
        return None;
    }
    collect_syntax_identifiers(parsed.syntax())
        .into_iter()
        .next()
}

pub fn check_source_definitions_parallel(
    engine: &Engine,
    sources: &[&[u8]],
    options: &KVMap,
    worker_threads: usize,
    limits: EngineAdmissionLimits,
) -> Result<Outcome<ParallelSourceCheck>, ParallelElabError> {
    check_source_definitions_parallel_with_declarations(
        engine,
        sources,
        options,
        worker_threads,
        limits,
    )
    .map(|outcome| outcome.map_complete(|(checked, _)| checked))
}

pub(crate) fn check_source_definitions_parallel_with_declarations(
    engine: &Engine,
    sources: &[&[u8]],
    options: &KVMap,
    worker_threads: usize,
    limits: EngineAdmissionLimits,
) -> Result<Outcome<(ParallelSourceCheck, Vec<Declaration>)>, ParallelElabError> {
    if sources.is_empty() {
        return Err(ParallelElabError::EmptyBatch);
    }

    let mut graph = DataflowGraph::new();
    let mut ordered_decl_names: Vec<Name> = Vec::with_capacity(sources.len());
    let kernel_budget = limits.kernel;

    let parsed = sources
        .iter()
        .enumerate()
        .map(|(index, source)| {
            fln_parse::parse_definition(source)
                .and_then(fln_parse::ParsedDefinition::expanded)
                .map_err(|error| ParallelElabError::Parse { index, error })
        })
        .collect::<Result<Vec<_>, _>>()?;
    if parsed
        .iter()
        .any(|parsed| !uses_declaration_only_path(parsed.syntax()))
    {
        return check_in_source_order(engine, sources, options, worker_threads, limits)
            .map(|outcome| outcome.map_complete(|checked| (checked, Vec::new())));
    }

    for (index, parsed) in parsed.into_iter().enumerate() {
        let syntax = parsed.syntax().clone();
        let idents = collect_syntax_identifiers(&syntax);
        let declared = idents.first().cloned();
        let declared_names: Vec<Name> = declared.iter().cloned().collect();
        let mut referenced_names: Vec<Name> = Vec::new();
        for name in idents.into_iter().skip(1) {
            let mut prefix = name.parent();
            referenced_names.push(name);
            while !prefix.is_anonymous() {
                referenced_names.push(prefix.clone());
                prefix = prefix.parent();
            }
        }
        if let Some(name) = declared.clone() {
            ordered_decl_names.push(name);
        }
        let scope = engine.base_source_scope();

        let elab_fn = Arc::new(
            move |env: &fln_env::environment::Environment,
                  _budget: &ElabBudget|
                  -> Outcome<Result<ElabUnitProduct, String>> {
                let decl = match source_outcome(crate::source_records::elaboration_outcome(
                    fln_elab::elaborate_definition_in_scope_with_budget(
                        &syntax,
                        env,
                        kernel_budget,
                        &scope,
                    ),
                )) {
                    Outcome::Complete(Ok(decl)) => decl,
                    Outcome::Complete(Err(error)) => {
                        return Outcome::Complete(Err(error.to_string()));
                    }
                    Outcome::Inconclusive(stop) => return Outcome::Inconclusive(stop),
                    Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
                };
                match check(env, &decl, kernel_budget) {
                    Outcome::Complete(KernelVerdict::Accepted { .. }) => {
                        let constants = declaration_to_constants(&decl);
                        let effects = effects_for_constants(&constants);
                        Outcome::Complete(Ok(ElabUnitProduct {
                            admitted_decls: constants,
                            messages: Vec::new(),
                            info_tree: None,
                            effects,
                            decisions: Vec::new(),
                        }))
                    }
                    Outcome::Complete(KernelVerdict::Rejected { class, message, .. }) => {
                        Outcome::Complete(Err(format!("kernel rejected ({class:?}): {message}")))
                    }
                    Outcome::Inconclusive(stop) => Outcome::Inconclusive(stop),
                    Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
                }
            },
        );

        graph.add_node(DataflowNode {
            id: CommandId(index),
            name: declared,
            declared_names,
            referenced_names,
            declared_effects: EffectSummary::new(),
            elab_fn,
        });
    }

    let config = ExecutionConfig {
        worker_threads: worker_threads.max(1),
        worker_stack_bytes: limits.kernel.calibration().stack_bytes(),
        enable_speculation: worker_threads > 1,
        budget: ElabBudget::default(),
    };

    let scheduled = match DeterministicScheduler::execute(&graph, engine.environment(), &config) {
        Outcome::Complete(Ok(output)) => output,
        Outcome::Complete(Err(detail)) => return Err(ParallelElabError::Scheduler(detail)),
        Outcome::Inconclusive(stop) => return Ok(Outcome::Inconclusive(stop)),
        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
    };

    // Re-admit the canonically ordered declarations through the Engine's full
    // dual-checker (K1 + independent fln-checker) council.
    let mut declarations = Vec::with_capacity(ordered_decl_names.len());
    for name in &ordered_decl_names {
        let Some(info) = scheduled.final_environment.find(name) else {
            return Ok(Outcome::InternalFault(
                fln_core::outcome::InternalFault::new(
                    "FL-INV-01",
                    format!(
                        "scheduled environment missing committed declaration `{}`",
                        name.to_display_string()
                    ),
                ),
            ));
        };
        let Some(decl) = constant_to_declaration(info) else {
            return Ok(Outcome::InternalFault(
                fln_core::outcome::InternalFault::new(
                    "FL-INV-01",
                    format!(
                        "unsupported scheduled declaration kind for `{}`",
                        name.to_display_string()
                    ),
                ),
            ));
        };
        declarations.push(decl);
    }

    let batch = match engine
        .admit_declarations(&declarations, options, limits)
        .map_err(ParallelElabError::Admission)?
    {
        Outcome::Complete(batch) => batch,
        Outcome::Inconclusive(stop) => return Ok(Outcome::Inconclusive(stop)),
        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
    };

    // Even a plain definition freezes source equation policy. The scheduler
    // never treats a journal as admission authority: install it only after the
    // entire declaration batch has crossed both checkers.
    let mut result_engine = batch.engine;
    for (index, declaration) in declarations.iter().enumerate() {
        result_engine = match source_outcome(result_engine.freeze_source_equation_policy(
            declaration,
            &engine.base_source_scope(),
            options,
            limits.kernel,
        )) {
            Outcome::Complete(Ok(engine)) => engine,
            Outcome::Complete(Err(error)) => {
                return Err(ParallelElabError::Source {
                    index,
                    error: Box::new(error),
                });
            }
            Outcome::Inconclusive(stop) => return Ok(Outcome::Inconclusive(stop)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
    }

    Ok(Outcome::Complete((
        ParallelSourceCheck {
            result_logical_root: result_engine.logical_root(options),
            engine: result_engine,
            base_logical_root: batch.base_logical_root,
            committed_order: scheduled.committed_order,
            retry_count: scheduled.retry_count,
            worker_threads: config.worker_threads,
            strategy: ParallelSourceStrategy::Dataflow,
        },
        declarations,
    )))
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::diag::ResourceReason;
    use fln_core::outcome::ResourceUsage;
    use fln_elab::{NatDefinitionElabError, source::SourceInferenceError};

    #[test]
    fn elaborator_nonanswers_keep_their_original_causes_before_scheduling() {
        let stopped = Inconclusive::resource(ResourceUsage {
            reason: ResourceReason::ExecutionSteps,
            allowed: 7,
            observed: 8,
        })
        .with_progress("parallel-source-conversion");
        let fault = InternalFault::new("source-conversion", "invalid conversion state");
        for outcome in [
            Outcome::Inconclusive(stopped.clone()),
            Outcome::InternalFault(fault.clone()),
        ] {
            let error = NatDefinitionElabError::Inference(SourceInferenceError::TypeObligation(
                Box::new(outcome.clone()),
            ));
            let actual =
                source_outcome(crate::source_records::elaboration_outcome::<()>(Err(error)));
            match outcome {
                Outcome::Inconclusive(expected) => {
                    assert!(matches!(actual, Outcome::Inconclusive(got) if got == expected))
                }
                Outcome::InternalFault(expected) => {
                    assert!(matches!(actual, Outcome::InternalFault(got) if got == expected))
                }
                Outcome::Complete(_) => unreachable!(),
            }
        }
        let unification_cancel =
            NatDefinitionElabError::Inference(SourceInferenceError::Unification(Box::new(
                fln_elab::constraint::unify::UnificationError::Cancelled,
            )));
        assert!(matches!(
            source_outcome(crate::source_records::elaboration_outcome::<()>(Err(
                unification_cancel
            ))),
            Outcome::Inconclusive(Inconclusive {
                cause: fln_core::outcome::InconclusiveCause::Cancelled { .. },
                ..
            })
        ));
        let frontend_limit = NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit);
        assert!(matches!(
            source_outcome(crate::source_records::elaboration_outcome::<()>(Err(
                frontend_limit
            ))),
            Outcome::Inconclusive(_)
        ));
    }

    #[test]
    fn check_source_files_with_jobs_matches_sequential_across_worker_counts() {
        let limits_1 = crate::SourceCheckLimits::new(EngineAdmissionLimits::new(
            fln_kernel::verdict::Budget::for_stack_bytes(2 * 1024 * 1024),
        ));
        let engine = Engine::with_coercion_seed(limits_1.admission)
            .unwrap()
            .into_complete()
            .unwrap();
        let options = KVMap::new();
        let source = br#"
def a : Nat := 1
def b : Nat := 2
def c : Nat := a + b
def d (x : Nat) : Nat := x + c
theorem t_sum : c = 3 := Eq.refl 3
theorem t_d : d 4 = 7 := Eq.refl 7
namespace Scoped
def inner : Nat := c + 1
end Scoped
def after_ns : Nat := Scoped.inner + b
def after_two : Nat := after_ns + 1
"#;
        let seq = engine
            .check_source_files_with_jobs(&[source.as_slice()], &options, limits_1, 1)
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(seq.commands, 11);
        assert_eq!(seq.theorems, 2);

        for jobs in [2, 4, 8] {
            let par = engine
                .check_source_files_with_jobs(&[source.as_slice()], &options, limits_1, jobs)
                .unwrap()
                .into_complete()
                .unwrap();
            assert_eq!(par.result_logical_root, seq.result_logical_root);
            assert_eq!(par.base_logical_root, seq.base_logical_root);
            assert_eq!(par.commands, seq.commands);
            assert_eq!(par.theorems, seq.theorems);
        }

        // Verify the contiguous theorem + def prefix directly enters Dataflow.
        let batch: [&[u8]; 4] = [
            b"def a : Nat := 1",
            b"def b : Nat := 2",
            b"def c : Nat := a + b",
            b"theorem t_sum : c = 3 := Eq.refl 3",
        ];
        let direct =
            check_source_definitions_parallel(&engine, &batch, &options, 4, limits_1.admission)
                .unwrap()
                .into_complete()
                .unwrap();
        assert_eq!(direct.strategy, ParallelSourceStrategy::Dataflow);

        // Error coordinates stay identical when a parallel batch fails and falls back.
        let broken = b"def ok1 : Nat := 1\ndef ok2 : Nat := 2\ndef bad : Nat := missing_ident\n";
        let err_1 = engine
            .check_source_files_with_jobs(&[broken.as_slice()], &options, limits_1, 1)
            .unwrap_err();
        let err_4 = engine
            .check_source_files_with_jobs(&[broken.as_slice()], &options, limits_1, 4)
            .unwrap_err();
        assert_eq!(err_1.to_string(), err_4.to_string());
    }
}
