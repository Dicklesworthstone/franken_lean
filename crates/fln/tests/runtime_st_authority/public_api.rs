//! Public ST/EST source syntax over the already admitted artifact closure.
use super::*;

pub(super) const PROGRAMS: [(&str, &str); 3] = [
    (
        "qualified reference operations",
        r#"
prelude
import Init.System.ST

#eval runST (fun sigma => do
  let reference ← ST.mkRef (σ := sigma) (7 : Nat)
  let alias := reference
  ST.Ref.set reference 20
  let previous ← ST.Ref.swap alias 22
  let current ← ST.Ref.get reference
  return Nat.add previous current)
"#,
    ),
    (
        "reference field notation",
        r#"
prelude
import Init.System.ST

#eval runST (fun sigma => do
  let reference ← ST.mkRef (σ := sigma) (7 : Nat)
  let alias := reference
  reference.set 20
  let previous ← alias.swap 22
  let current ← reference.get
  return Nat.add previous current)
"#,
    ),
    (
        "lifted state and caught exceptions",
        r#"
prelude
import Init.System.ST

def stateResult (result : Except Nat Nat) : Nat :=
  match result with
  | .ok value => value
  | .error code => Nat.add 1000 code

#eval stateResult (runEST (fun sigma => do
  let reference ← ST.mkRef (σ := sigma) (0 : Nat)
  try
    reference.set 37
    throw (5 : Nat)
    reference.set 99
    return 0
  catch code =>
    let current ← reference.get
    return Nat.add current code))
"#,
    ),
];

/// The caller has admitted the complete ST import closure and activated its
/// actual source metadata. The decoded raw fixture must never call this helper.
pub(super) fn check_public_api(engine: &Engine) {
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
    for (label, program) in PROGRAMS {
        // The same sources are Reference-checked import probes. The engine
        // already contains their admitted import and its class/instance data.
        let source = program
            .strip_prefix("\nprelude\nimport Init.System.ST\n")
            .expect("remove only the imported source header");
        let run = || {
            engine
                .execute_source_commands_with_checks(source.as_bytes(), &options, limits)
                .unwrap_or_else(|error| panic!("{label}: {error:?}"))
                .into_complete()
                .unwrap_or_else(|outcome| panic!("{label}: {outcome:?}"))
        };
        let first = run();
        assert_eq!(first.batch.source_evaluation_indices.len(), 1, "{label}");
        let execution = &first.batch.executions[first.batch.source_evaluation_indices[0]];
        assert_scalar(execution, 42);
        let bytecode = execution.flbc_artifact.clone();
        drop(first);
        assert_eq!(engine.logical_root(&options), root, "{label}");

        let repeated = run();
        assert_eq!(repeated.batch.source_evaluation_indices.len(), 1, "{label}");
        let execution = &repeated.batch.executions[repeated.batch.source_evaluation_indices[0]];
        assert_scalar(execution, 42);
        assert_eq!(execution.flbc_artifact, bytecode, "{label}");
        drop(repeated);
        assert_eq!(engine.logical_root(&options), root, "{label}");
    }
}
