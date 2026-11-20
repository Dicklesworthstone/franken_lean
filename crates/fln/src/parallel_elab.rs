//! Production parallel source elaboration wired to [`fln_elab::DeterministicScheduler`]
//! (Bet B4, Plan §10.6, FL-INV-01).
//!
//! Each source definition is parsed into a [`DataflowNode`] with conservative
//! syntax-level name pre-scans, elaborated and K1-checked speculatively across
//! `worker_threads` via [`DeterministicScheduler::execute`], merged in canonical
//! source order with footprint-validated rebasing, and finally admitted into an
//! immutable [`Engine`] successor through the ordinary dual-checker council
//! (K1 + independent `fln-checker`).
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
use fln_core::outcome::Outcome;
use fln_elab::{
    CommandEffect, CommandId, DataflowGraph, DataflowNode, DeclAspect, DeterministicScheduler,
    EffectSummary, ElabBudget, ElabUnitProduct, ExecutionConfig,
};
use fln_env::constants::ConstantInfo;
use fln_kernel::verdict::Verdict as KernelVerdict;
use fln_kernel::{Declaration, check};
use fln_parse::DefinitionParseError;
use fln_syntax::tree::Syntax;

use crate::{Engine, EngineAdmissionError, EngineAdmissionLimits, LogicalRoot};

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
        }
    }
}

impl std::error::Error for ParallelElabError {}

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

/// Elaborate and dual-check a sequence of source definitions through
/// [`DeterministicScheduler`], returning an immutable [`Engine`] successor.
pub fn check_source_definitions_parallel(
    engine: &Engine,
    sources: &[&[u8]],
    options: &KVMap,
    worker_threads: usize,
    limits: EngineAdmissionLimits,
) -> Result<Outcome<ParallelSourceCheck>, ParallelElabError> {
    if sources.is_empty() {
        return Err(ParallelElabError::EmptyBatch);
    }

    let mut graph = DataflowGraph::new();
    let mut ordered_decl_names: Vec<Name> = Vec::with_capacity(sources.len());
    let kernel_budget = limits.kernel;

    for (index, source) in sources.iter().enumerate() {
        let parsed = fln_parse::parse_definition(source)
            .map_err(|error| ParallelElabError::Parse { index, error })?;
        let syntax = parsed.syntax().clone();
        let idents = collect_syntax_identifiers(&syntax);
        let declared = idents.first().cloned();
        let declared_names: Vec<Name> = declared.iter().cloned().collect();
        let referenced_names: Vec<Name> = idents.into_iter().skip(1).collect();
        if let Some(name) = declared.clone() {
            ordered_decl_names.push(name);
        }

        let elab_fn = Arc::new(
            move |env: &fln_env::environment::Environment,
                  _budget: &ElabBudget|
                  -> Outcome<Result<ElabUnitProduct, String>> {
                let decl = match fln_elab::elaborate_definition_in_with_budget(
                    &syntax,
                    env,
                    kernel_budget,
                ) {
                    Ok(decl) => decl,
                    Err(error) => return Outcome::Complete(Err(format!("{error:?}"))),
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

    Ok(Outcome::Complete(ParallelSourceCheck {
        engine: batch.engine,
        base_logical_root: batch.base_logical_root,
        result_logical_root: batch.result_logical_root,
        committed_order: scheduled.committed_order,
        retry_count: scheduled.retry_count,
        worker_threads: config.worker_threads,
    }))
}
