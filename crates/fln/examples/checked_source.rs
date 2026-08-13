//! Minimal embedder over the currently implemented bounded source facade.
//!
//! This example uses source bytes supplied by the caller and explicit resource
//! limits. It does not claim the planned `Cx`, project/import, receipt, or full
//! Lean APIs already exist.

#![forbid(unsafe_code)]

use fln::{
    Budget, ClosedVmValue, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name,
    Outcome, closed_vm_value,
};
use std::error::Error;
use std::fmt;

const KERNEL_STACK_BYTES: usize = 2 * 1024 * 1024;

#[derive(Debug)]
struct ExampleError(String);

impl fmt::Display for ExampleError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl Error for ExampleError {}

#[derive(Debug, PartialEq, Eq)]
struct EmbedderSummary {
    definitions: usize,
    answer: usize,
    answer_is_queryable: bool,
    checker_schema: &'static str,
    artifact_bytes: usize,
    base_root: String,
    result_root: String,
}

fn example_error(message: impl Into<String>) -> Box<dyn Error> {
    Box::new(ExampleError(message.into()))
}

fn seeded_engine() -> Result<Engine, Box<dyn Error>> {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(KERNEL_STACK_BYTES));
    match Engine::with_source_seed(limits)? {
        Outcome::Complete(engine) => Ok(engine),
        Outcome::Inconclusive(reason) => Err(example_error(format!(
            "source seed was inconclusive: {reason:?}"
        ))),
        Outcome::InternalFault(fault) => Err(example_error(format!(
            "source seed hit an internal fault: {fault:?}"
        ))),
    }
}

fn run_embedder() -> Result<EmbedderSummary, Box<dyn Error>> {
    let engine = seeded_engine()?;
    let options = KVMap::new();
    let sources: [&[u8]; 2] = [
        b"def product : Nat := Nat.mul 6 7",
        b"def incremented : Nat := Nat.add product 1",
        b"def answer : Nat := Nat.sub incremented 1",
    ];
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(KERNEL_STACK_BYTES));
    let completed = match engine.execute_source_definitions(&sources, &options, limits)? {
        Outcome::Complete(completed) => completed,
        Outcome::Inconclusive(reason) => {
            return Err(example_error(format!(
                "source execution was inconclusive: {reason:?}"
            )));
        }
        Outcome::InternalFault(fault) => {
            return Err(example_error(format!(
                "source execution hit an internal fault: {fault:?}"
            )));
        }
    };

    let final_execution = completed
        .executions
        .last()
        .ok_or_else(|| example_error("completed source batch contained no executions"))?;
    let Some(ClosedVmValue::Scalar(answer)) = closed_vm_value(&final_execution.exit)? else {
        return Err(example_error(
            "final definition did not return a Nat scalar",
        ));
    };

    let answer_name = Name::from_components(["answer"]);
    Ok(EmbedderSummary {
        definitions: completed.executions.len(),
        answer,
        answer_is_queryable: completed.engine.environment().find(&answer_name).is_some(),
        checker_schema: final_execution.checker.schema,
        artifact_bytes: final_execution.flbc_artifact.len(),
        base_root: completed.base_logical_root.to_string(),
        result_root: completed.result_logical_root.to_string(),
    })
}

fn main() -> Result<(), Box<dyn Error>> {
    let summary = run_embedder()?;
    println!("definitions: {}", summary.definitions);
    println!("answer: {}", summary.answer);
    println!("answer queryable: {}", summary.answer_is_queryable);
    println!("checker schema: {}", summary.checker_schema);
    println!("final FLBC bytes: {}", summary.artifact_bytes);
    println!("base logical root: {}", summary.base_root);
    println!("result logical root: {}", summary.result_root);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn real_embedder_path_returns_and_publishes_a_queryable_answer() {
        let summary = run_embedder().expect("the checked embedder example completes");

        assert_eq!(summary.definitions, 2);
        assert_eq!(summary.answer, 42);
        assert!(summary.answer_is_queryable);
        assert!(!summary.checker_schema.is_empty());
        assert!(summary.artifact_bytes > 0);
        assert_ne!(summary.base_root, summary.result_root);
    }

    #[test]
    fn a_frontend_refusal_leaves_the_original_snapshot_unchanged() {
        let engine = seeded_engine().expect("the bounded source seed completes");
        let options = KVMap::new();
        let original_root = engine.logical_root(&options);
        let sources: [&[u8]; 1] = [b"def broken : Nat := missing"];

        engine
            .execute_source_definitions(
                &sources,
                &options,
                EngineExecutionLimits::new(Budget::for_stack_bytes(KERNEL_STACK_BYTES)),
            )
            .expect_err("an unknown source reference is refused");

        assert_eq!(engine.logical_root(&options), original_root);
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["broken"]))
        );
    }
}
