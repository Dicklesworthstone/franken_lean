//! Native proof/type erasure must precede the direct-recursor codegen restriction.
//! Model regressions; no claim these cases have run on the pinned Reference.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits, VmExit,
};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
const PREFIX: &str = "inductive T where | a | b (x : T)\ndef sink (_ : True) : Nat := 7\n";
const COUNT: &str = "T.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 1) t";

fn check(body: &str) {
    let source = format!("{PREFIX}{body}").replace("COUNT", COUNT);
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("both native checkers complete");
}

#[test]
fn data_recursors_inside_proof_arguments_are_not_compiled() {
    check("def f (t : T) : Nat := sink ((fun (_ : Nat) => True.intro) (COUNT))\n");
}

#[test]
fn data_recursors_inside_proof_lets_are_not_compiled() {
    check("def f (t : T) : Nat := let h : True := (let n : Nat := COUNT; True.intro); 7\n");
}

#[test]
fn data_recursors_inside_type_arguments_are_not_compiled() {
    check(
        "def keep (A : Type) (n : Nat) : Nat := n\ndef f (t : T) : Nat := keep ((fun (_ : Nat) => Nat) (COUNT)) 7\n",
    );
}

#[test]
fn proof_arguments_to_local_functions_use_the_binder_telescope() {
    check("def f (k : True -> Nat) (t : T) : Nat := k ((fun (_ : Nat) => True.intro) (COUNT))\n");
}

#[test]
fn dependent_proof_lets_do_not_lose_their_local_type_context() {
    check(
        "def f (t : T) : Nat := let n : Nat := 7; let h : n = n := (fun (_ : Nat) => Eq.refl n) (COUNT); n\n",
    );
}

#[test]
fn erased_recursors_are_not_compiled_at_the_execution_door() {
    let source = format!(
        "{PREFIX}def f (t : T) : Nat := sink ((fun (_ : Nat) => True.intro) ({COUNT}))\n#eval f (T.b T.a)\n"
    );
    let run = engine()
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{error:?}"))
        .into_complete()
        .expect("execution completes");
    let VmExit::Returned(result) = &run.executions.last().unwrap().exit else {
        panic!("returned Nat");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some("7")
    );
}

#[test]
fn data_uses_still_refuse_and_failed_checks_preserve_the_predecessor() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    for body in [
        "def keep (n : Nat) : Nat := n\ndef f (t : T) : Nat := keep (COUNT)\n",
        "def f (t : T) : Nat := let n : Nat := COUNT; sink ((fun (_ : Nat) => True.intro) n) + n\n",
        "def f (t : T) : Nat := (fun (_ : True) => COUNT) True.intro\n",
    ] {
        let source = format!("{PREFIX}{body}").replace("COUNT", COUNT);
        let error = engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect_err("the data recursor still requires unsupported codegen");
        assert!(
            error
                .to_string()
                .contains("code generator does not support recursor `T.rec`"),
            "{error:?}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}
