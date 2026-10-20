//! The source compiler must select checked equations before noncomputability.
//! These equations and original bodies are admitted through both checker seats;
//! no mocked declaration or proof is used as executable input.
#![forbid(unsafe_code)]
use fln::{
    Budget, ClosedVmValue, Engine, EngineAdmissionLimits, EngineExecutionLimits,
    KVMap, Name, SourceCheckLimits, closed_vm_value,
};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn seed() -> Engine {
    Engine::with_source_seed(limits()).unwrap().into_complete().unwrap()
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), SourceCheckLimits::new(limits()))
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete().unwrap().engine
}

const SCALAR: &str = r#"
namespace WellFounded
noncomputable def fix : Nat := 7
def fixC : Nat := 7
theorem fix_eq_fixC : fix = fixC := rfl
noncomputable def fixF : Nat := 7
def fixFC : Nat := 7
theorem fixF_eq_fixFC : fixF = fixFC := rfl
end WellFounded
"#;

fn returns(base: &Engine, source: &str, expected: usize) {
    let root = base.logical_root(&KVMap::new());
    let result = base.execute_source_definitions(
        &[source.as_bytes()], &KVMap::new(), EngineExecutionLimits::new(limits().kernel),
    ).unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete().unwrap();
    assert_eq!(result.executions.len(), 1);
    assert_eq!(closed_vm_value(&result.executions[0].exit).unwrap(), Some(ClosedVmValue::Scalar(expected)));
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

fn refuses(base: &Engine, source: &str, expected: &str) {
    let root = base.logical_root(&KVMap::new());
    let error = base.check_source_files(
        &[source.as_bytes()], &KVMap::new(), SourceCheckLimits::new(limits()),
    ).expect_err("a refused compiler dependency must not publish a successor");
    assert!(error.to_string().contains(expected), "{error:?}");
    assert_eq!(error.disposition(), ("elaboration", false, 1));
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&name("rejected")));
}

#[test]
fn admitted_equations_enable_source_definitions_and_native_evaluation() {
    let base = checked(&seed(), SCALAR);
    let logical = base.environment().find(&name("WellFounded.fix")).unwrap().clone();
    let available = checked(&base, "def usable : Nat := WellFounded.fix + WellFounded.fixF");
    returns(&available, "#eval usable", 14);
    returns(&base, "#eval WellFounded.fix", 7);
    returns(&base, "#eval WellFounded.fixF", 7);
    assert_eq!(base.environment().find(&name("WellFounded.fix")), Some(&logical));
    assert!(fln_elab::noncomputable::read(base.environment()).unwrap().contains(&name("WellFounded.fix")));
}

#[test]
fn partial_applications_and_captured_arguments_reach_the_same_checked_target() {
    let base = checked(&seed(), r#"
namespace WellFounded
noncomputable def fix (a b : Nat) : Nat := a + b
def fixC (a b : Nat) : Nat := a + b
theorem fix_eq_fixC : @fix = @fixC := rfl
end WellFounded
def throughLocal (n : Nat) : Nat :=
  let remaining : Nat -> Nat := WellFounded.fix n
  remaining 21
"#);
    returns(&base, "#eval throughLocal 21", 42);
    returns(&base, "#eval (WellFounded.fix 21) 21", 42);
}

#[test]
fn a_missing_or_wrong_equation_never_becomes_an_implicit_noncomputable_exemption() {
    let no_equation = checked(&seed(), r#"
namespace WellFounded
noncomputable def fix : Nat := 7
def fixC : Nat := 7
end WellFounded
"#);
    refuses(&no_equation, "def rejected : Nat := WellFounded.fix", "WellFounded.fix");
    let wrong = checked(&no_equation,
        "theorem WellFounded.fix_eq_fixC : WellFounded.fixC = WellFounded.fixC := rfl");
    refuses(&wrong, "def rejected : Nat := WellFounded.fix", "compiler equation");
    refuses(&wrong, "noncomputable section\ndef rejected : Nat := WellFounded.fix\nend",
        "compiler equation");
    let recovered = checked(&no_equation,
        "theorem WellFounded.fix_eq_fixC : WellFounded.fix = WellFounded.fixC := rfl");
    returns(&recovered, "#eval WellFounded.fix", 7);
}

#[test]
fn selecting_an_equation_does_not_exempt_its_noncomputable_target_or_a_live_argument() {
    let base = checked(&seed(), SCALAR);
    let tagged = fln_elab::noncomputable::register(base.environment(), &name("WellFounded.fixC")).unwrap();
    // Only the tag changed; all logical declarations and proofs came from the
    // ordinary two-seat source admission above. No altered proof is executed.
    let tagged = Engine::from_environment(tagged);
    refuses(&tagged, "def rejected : Nat := WellFounded.fix", "WellFounded.fixC");
    let function = checked(&seed(), r#"
namespace WellFounded
noncomputable def fix (n : Nat) : Nat := n
def fixC (n : Nat) : Nat := n
theorem fix_eq_fixC : @fix = @fixC := rfl
end WellFounded
noncomputable def hiddenArgument : Nat := 42
"#);
    refuses(&function, "def rejected : Nat := WellFounded.fix hiddenArgument", "hiddenArgument");
}

#[test]
fn source_admitted_mixed_chains_execute_but_cycles_are_not_suppressed() {
    let base = checked(&seed(), SCALAR);
    let first = fln_elab::implemented_by::register(
        base.environment(), &name("WellFounded.fixC"), &name("WellFounded.fixF"),
    ).unwrap();
    let executable = Engine::from_environment(first.clone());
    returns(&executable, "#eval WellFounded.fix", 7);
    let cycle = fln_elab::implemented_by::register(
        &first, &name("WellFounded.fixFC"), &name("WellFounded.fix"),
    ).unwrap();
    let cycle = Engine::from_environment(cycle);
    refuses(&cycle, "def rejected : Nat := WellFounded.fix", "cyclic executable replacement chain");
    refuses(&cycle, "noncomputable section\ndef rejected : Nat := WellFounded.fix\nend",
        "cyclic executable replacement chain");
}
