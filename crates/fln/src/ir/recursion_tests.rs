//! Source recursion reaches the IR exporter only through an admitted logical
//! interface and its exact checked executable companion. These tests use the
//! ordinary source checker; the installed Lake suite exercises physical `.ir`
//! consumers against the pinned Lean toolchain.
use super::*;
use crate::{Engine, EngineAdmissionLimits, EngineExecutionLimits, SourceCheckLimits};
use fln_comp::ingress::{IngressError, IngressResource};
use fln_core::{options::KVMap, outcome::Outcome};
use fln_env::constants::{ConstantInfo, DefinitionSafety};

const COUNT: &str = "partial def count (n : Nat) : Nat := \
    if n == 0 then 7 else count (n - 1)\n";

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn execution_limits() -> EngineExecutionLimits {
    let mut limits = EngineExecutionLimits::new(crate::Budget::for_stack_bytes(2 * 1024 * 1024));
    // Compilation must work without evaluating even one instruction. In
    // particular, a nonterminating partial body cannot be sampled for a value.
    limits.vm.max_steps = 0;
    limits
}

fn checked(source: &str) -> Engine {
    let admission = EngineAdmissionLimits::new(execution_limits().kernel);
    Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
        .engine
}

fn export(
    engine: &Engine,
    entry: &str,
) -> std::result::Result<Outcome<IrModule>, DefinitionCompileError> {
    compile_checked_source_definition(
        engine,
        &name(entry),
        &KVMap::new(),
        execution_limits(),
        CompileLimits::default(),
    )
}

fn assert_unsupported(engine: &Engine, entry: &str) {
    let error = export(engine, entry).unwrap_err();
    assert!(
        matches!(
            error,
            DefinitionCompileError::Ir(CompileError::Unsupported { .. })
                | DefinitionCompileError::Engine(crate::EngineExecutionError::Ingress(
                    IngressError::UnsupportedNode { .. }
                ))
        ),
        "expected an explicit unsupported refusal for {entry}, got {error:?}"
    );
}

#[test]
fn source_recursion_exports_logical_unary_entries_without_evaluation() {
    let engine = checked(&format!(
        r#"def structural : Nat -> Nat
  | .zero => 7
  | .succ n => structural n
def accumulating : Nat -> Nat
  | .zero => 0
  | .succ n => accumulating n + 2
{COUNT}
partial def spin (n : Nat) : Nat := spin (n + 1)
"#
    ));
    let before = engine.environment().clone();
    for label in ["count", "spin", "structural", "accumulating"] {
        let entry = name(label);
        let companion = Name::str(entry.clone(), "_unsafe_rec");
        if matches!(label, "count" | "spin") || engine.environment().contains(&companion) {
            assert!(matches!(
                engine.environment().find(&companion),
                Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Partial
            ));
            assert!(
                is_checked_recursive_companion(
                    &engine,
                    &companion,
                    execution_limits(),
                    CompileLimits::default(),
                )
                .unwrap()
            );
        }
        let module = export(&engine, label)
            .unwrap_or_else(|error| panic!("{label}: {error:?}"))
            .into_complete()
            .unwrap();
        let Some(IrDecl::Function { params, result, .. }) =
            module.decls.iter().find(|decl| decl.name() == &entry)
        else {
            panic!("missing logical exported function {label}")
        };
        assert_eq!(params.len(), 1);
        assert_eq!(params[0].ty, IrType::TObject);
        assert_eq!(*result, IrType::TObject);
        assert!(module.decls.iter().all(|decl| {
            !decl.name().to_display_string().contains("_unsafe_rec")
                && decl.name() != &Name::str(entry.clone(), "_redArg")
        }));
        assert_eq!(engine.environment(), &before);
    }
    assert!(matches!(
        engine.environment().find(&name("count")),
        Some(ConstantInfo::Opaque(value)) if !value.is_unsafe
    ));
    for source in [
        "theorem leakedComputation : count 0 = 7 := by rfl",
        "def leakedBody : Nat := count._unsafe_rec 0",
    ] {
        assert!(
            engine
                .check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(EngineAdmissionLimits::new(execution_limits().kernel)),
                )
                .is_err(),
            "compilation changed logical opacity: {source}"
        );
    }
    assert_eq!(engine.environment(), &before);
}

#[test]
fn source_recursion_refuses_unsafe_entries_and_unverified_companions() {
    let engine = checked(&format!(
        "{COUNT}\
         unsafe def unsafeEntry (n : Nat) : Nat := n\n\
         def counterfeit (n : Nat) : Nat := n\n\
         def counterfeit._unsafe_rec (n : Nat) : Nat := n\n\
         opaque opaqueCounterfeit : Nat -> Nat := fun n => n\n\
         def opaqueCounterfeit._unsafe_rec (n : Nat) : Nat := n\n"
    ));
    for entry in [
        "count._unsafe_rec",
        "unsafeEntry",
        "counterfeit",
        "opaqueCounterfeit",
    ] {
        assert_unsupported(&engine, entry);
    }
    assert!(
        is_checked_recursive_companion(
            &engine,
            &name("counterfeit._unsafe_rec"),
            execution_limits(),
            CompileLimits::default(),
        )
        .is_err()
    );
}

#[test]
fn source_recursion_refuses_unproved_public_signatures_and_mutual_groups() {
    let engine = checked(
        r#"partial def accumulator (n total : Nat) : Nat :=
  if n == 0 then total else accumulator (n - 1) (total + 2)
partial def text (n : Nat) : String :=
  if n == 0 then "done" else text (n - 1)
mutual
  partial def first (n : Nat) : Nat := second n
  partial def second (n : Nat) : Nat := first n
end
"#,
    );
    for entry in ["accumulator", "text", "first", "second"] {
        assert_unsupported(&engine, entry);
    }
}

#[test]
fn source_recursion_refuses_executable_metadata_on_either_half() {
    use fln_elab::externs::ExternEntry;
    let engine = checked(&format!("{COUNT}def replacement (n : Nat) : Nat := n\n"));
    for target in [name("count"), name("count._unsafe_rec")] {
        let extern_environment = fln_elab::externs::register(
            engine.environment(),
            &target,
            vec![ExternEntry::Standard {
                backend: Name::anonymous(),
                symbol: "unbound_recursive_export".into(),
            }],
        )
        .unwrap();
        assert_unsupported(&Engine::from_environment(extern_environment), "count");

        let replacement_environment =
            fln_elab::implemented_by::register(engine.environment(), &target, &name("replacement"))
                .unwrap();
        assert_unsupported(&Engine::from_environment(replacement_environment), "count");

        let noncomputable_environment =
            fln_elab::noncomputable::register(engine.environment(), &target).unwrap();
        assert_unsupported(
            &Engine::from_environment(noncomputable_environment),
            "count",
        );
    }
}

#[test]
fn source_recursion_refuses_initialized_globals_before_any_stored_body() {
    let engine = checked(&format!("{COUNT}opaque initialized : Nat := 42\n"));
    for target in [
        name("count"),
        name("count._unsafe_rec"),
        name("initialized"),
    ] {
        let mut changed = engine.clone();
        std::sync::Arc::make_mut(&mut changed.runtime_initializers).insert(target.clone());
        let entry = if target == name("initialized") {
            "initialized"
        } else {
            "count"
        };
        assert_unsupported(&changed, entry);
    }
}

#[test]
fn source_recursion_linkage_exhaustion_remains_a_resource_nonanswer() {
    let engine = checked(COUNT);
    let before = engine.environment().clone();
    let mut execution = execution_limits();
    execution.ingress.fir.max_functions = 0;
    let error = compile_checked_source_definition(
        &engine,
        &name("count"),
        &KVMap::new(),
        execution,
        CompileLimits::default(),
    )
    .unwrap_err();
    assert!(
        matches!(
            error,
            DefinitionCompileError::Engine(crate::EngineExecutionError::Ingress(
                IngressError::ResourceLimit {
                    resource: IngressResource::ProgramTables,
                    limit: 0,
                    observed: 1,
                }
            ))
        ),
        "{error:?}"
    );
    assert_eq!(engine.environment(), &before);
}
