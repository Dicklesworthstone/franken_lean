//! Explicit Nat measures use the pinned, kernel-checked `WellFounded.Nat.fix`
//! on the native VM. Proofs run in the source branch's local context and every
//! surviving recursive obligation must be discharged.
#![forbid(unsafe_code)]
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, ClosedVmValue, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name,
    OleanCheckLimits, OleanDecodeLimits, OleanModuleInput, SourceCheckLimits, olean_module_imports,
};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

#[path = "support/well_founded_opacity.rs"]
mod well_founded_opacity;

const STACK: usize = 256 * 1024 * 1024;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))
}

fn pinned_lib() -> Option<PathBuf> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|lib| lib.is_dir());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "FLN_REQUIRE_REFERENCE is set but the pinned Reference lib/lean is absent"
    );
    lib
}

fn import_closure(lib: &Path) -> Engine {
    let root = n("Init.WFTactics");
    let mut pending = vec![root.clone()];
    let mut seen = BTreeSet::new();
    let mut names = Vec::new();
    let mut parts = Vec::new();
    while let Some(module) = pending.pop() {
        if !seen.insert(module.clone()) {
            continue;
        }
        let base = module
            .to_display_string()
            .split('.')
            .fold(lib.to_path_buf(), |path, part| path.join(part))
            .with_extension("olean");
        let exported = std::fs::read(&base).expect("pinned exported artifact");
        pending.extend(
            olean_module_imports(&exported, OleanDecodeLimits::new(exported.len()))
                .expect("pinned module imports"),
        );
        parts.push([
            exported,
            std::fs::read(base.with_extension("olean.server")).expect("pinned server artifact"),
            std::fs::read(base.with_extension("olean.private")).expect("pinned private artifact"),
        ]);
        names.push(module);
    }
    let inputs: Vec<_> = names
        .iter()
        .zip(&parts)
        .map(|(name, [exported, server, private])| OleanModuleInput {
            name,
            artifact: exported,
            server_artifact: Some(server),
            private_artifact: Some(private),
        })
        .collect();
    Engine::builder()
        .build_empty()
        .import_olean_modules_for_source(
            &inputs,
            &[root],
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(256 * 1024 * 1024, limits().kernel)),
        )
        .expect("the imported library passes both checkers")
        .into_complete()
        .expect("the import finishes")
        .engine
}

const COMPUTING: &str = r#"
def countdown (n : Nat) : Nat :=
  if h : 0 < n then countdown (n - 1) + 1 else 0
termination_by n
decreasing_by exact @Nat.sub_lt n 1 h (Nat.succ_pos 0)

def repeated (step n : Nat) : Nat :=
  if h : 0 < n then repeated step (n - 1) + step else 0
termination_by n
decreasing_by exact @Nat.sub_lt n 1 h (Nat.succ_pos 0)

def aliased : Nat -> Nat := fun n =>
  if h : 0 < n then aliased (n - 1) + 1 else 0
termination_by remaining => remaining
decreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)

def keptLet (n : Nat) : Nat :=
  if h : 0 < n then
    let k := n - 1
    keptLet k + 1
  else 0
termination_by n
decreasing_by exact @Nat.sub_lt n 1 h (Nat.succ_pos 0)

def twice (n : Nat) : Nat :=
  if h : 0 < n then twice 0 + twice 0 + 42 else 0
termination_by n
decreasing_by all_goals exact h

def measured (n : Nat) : Nat :=
  if h : 0 < n then measured 0 + 42 else 0
termination_by (fun x : Nat => x) n
decreasing_by exact h

def pairCount (p : Nat × Nat) : Nat :=
  if h : 0 < p.1 then pairCount (p.1 - 1, p.2) + p.2 else 0
termination_by p.1
decreasing_by exact @Nat.sub_lt p.1 1 h (Nat.succ_pos 0)

def gcdPair (p : Nat × Nat) : Nat :=
  if h : 0 < p.2 then gcdPair (p.2, p.1 % p.2) else p.1
termination_by p.2
decreasing_by exact @Nat.mod_lt p.1 p.2 h

def inferredCountdown (n : Nat) : Nat :=
  if h : 0 < n then inferredCountdown (n - 1) + 1 else 0
termination_by n
decreasing_by exact Nat.sub_lt h (by decide)

def answer1 : Nat := countdown 42
def answer2 : Nat := repeated 2 21
def answer3 : Nat := aliased 42
def answer4 : Nat := keptLet 42
def answer5 : Nat := twice 42
def answer6 : Nat := measured 42
def answer7 : Nat := pairCount (21, 2)
def answer8 : Nat := gcdPair (126, 84)
def answer9 : Nat := inferredCountdown 42
"#;

const SHARING: &str = r#"
def shared (n : Nat) : Nat :=
  if h : 0 < n then shared 0 + shared 0 + 42 else 0
termination_by n
decreasing_by exact h

def distinct (n : Nat) : Nat :=
  if h : 0 < n then distinct 0 + distinct (n - 1) + 1 else 0
termination_by n
decreasing_by
  exact h
  exact Nat.sub_lt h (by decide)

def largerContext (n : Nat) : Nat :=
  if h : 0 < n then largerContext 0 + (let k := n - 1; largerContext 0) + 42 else 0
termination_by n
decreasing_by exact h

def smallerContext (n : Nat) : Nat :=
  if h : 0 < n then (let k := n - 1; smallerContext 0) + smallerContext 0 + 42 else 0
termination_by n
decreasing_by
  exact h
  exact h

def siblingScopes (n : Nat) : Nat :=
  (if h : 0 < n then siblingScopes 0 else 21) +
  (if h : 0 < n then siblingScopes 0 else 0)
termination_by n
decreasing_by
  exact h
  exact h

def sameMeasure (p : Nat × Nat) : Nat :=
  if h : 0 < p.1 then sameMeasure (0, 0) + sameMeasure (0, 1) + 42 else 0
termination_by p.1
decreasing_by
  exact h
  exact h

def retainedLet (n : Nat) : Nat :=
  if h : 0 < n then
    let k := n - 1
    retainedLet k + 1
  else 0
termination_by n
decreasing_by
  have retained : Nat := k
  exact Nat.sub_lt h (by decide)

def sharingAnswer1 : Nat := shared 42
def sharingAnswer2 : Nat := distinct 42
def sharingAnswer3 : Nat := largerContext 42
def sharingAnswer4 : Nat := smallerContext 42
def sharingAnswer5 : Nat := siblingScopes 42
def sharingAnswer6 : Nat := sameMeasure (42, 10)
def sharingAnswer7 : Nat := retainedLet 42
"#;

fn assert_computations(base: &Engine) {
    // Live v4.32.0 evaluates each of these sixteen applications to 42. The
    // non-Nat domain and fixed prefix exercise actual measure lowering rather
    // than a subtraction-specific rewrite or structural recursion shortcut.
    for (source, count) in [(COMPUTING, 9), (SHARING, 7)] {
        let result = base
            .execute_source_definitions(
                &[source.as_bytes()],
                &KVMap::new(),
                EngineExecutionLimits::new(limits().kernel),
            )
            .expect("the source programs elaborate, pass both checkers, and execute")
            .into_complete()
            .expect("the computations finish");
        let values: Vec<_> = result
            .executions
            .iter()
            .filter_map(|execution| fln::closed_vm_value(&execution.exit).expect("normal VM exit"))
            .collect();
        assert_eq!(values, vec![ClosedVmValue::Scalar(42); count]);
    }
}

fn assert_decreasing_refusals(base: &Engine) {
    let root = base.logical_root(&KVMap::new());
    for source in [
        // A proof of positivity is not a proof of n < n.
        "def bad (n : Nat) : Nat := if h : 0 < n then bad n else 0\ntermination_by n\ndecreasing_by exact h",
        // Distinct calls require both proofs, and an extra command cannot pass.
        "def bad (n : Nat) : Nat := if h : 0 < n then bad 0 + bad (n - 1) else 0\ntermination_by n\ndecreasing_by exact h",
        "def bad (n : Nat) : Nat := if h : 0 < n then bad 0 + bad (n - 1) else 0\ntermination_by n\ndecreasing_by\n  exact h\n  exact Nat.sub_lt h (by decide)\n  exact h",
        // Identical calls share only while their original full scope is valid.
        "def bad (n : Nat) : Nat := if h : 0 < n then bad 0 + bad 0 else 0\ntermination_by n\ndecreasing_by\n  exact h\n  exact h",
        "def bad (n : Nat) : Nat := if h : 0 < n then (let k := n - 1; bad 0) + bad 0 else 0\ntermination_by n\ndecreasing_by exact h",
        "def bad (n : Nat) : Nat := (if h : 0 < n then bad 0 else 21) + (if h : 0 < n then bad 0 else 0)\ntermination_by n\ndecreasing_by exact h",
        // Definitional equality of measures does not make different calls identical.
        "def bad (p : Nat × Nat) : Nat := if h : 0 < p.1 then bad (0, 0) + bad (0, 1) else 0\ntermination_by p.1\ndecreasing_by exact h",
        // Cleanup removes unrelated data parameters and independent hypotheses.
        "def bad (step n : Nat) : Nat := if h : 0 < n then bad step 0 else 0\ntermination_by n\ndecreasing_by\n  have unused : Nat := step\n  exact h",
        "def bad (impossible : False) (n : Nat) : Nat := if h : 0 < n then bad impossible 0 else 0\ntermination_by n\ndecreasing_by exact False.elim impossible",
        // Unused recursive source values and their obligations still count.
        "def bad (n : Nat) : Nat := let unused := bad n; 42\ntermination_by n\ndecreasing_by exact Nat.succ_pos n",
        "def bad (n : Nat) : Nat := let unused := bad; 42\ntermination_by n\ndecreasing_by exact Nat.succ_pos n",
        // A proof script must neither call the recursive function nor leave a hole.
        "def bad (n : Nat) : Nat := if h : 0 < n then bad 0 else 0\ntermination_by n\ndecreasing_by exact bad n",
        "def bad (n : Nat) : Nat := if h : 0 < n then bad 0 else 0\ntermination_by n\ndecreasing_by exact _",
        // Hints are checked source terms, including ignored let initializers.
        "def bad (n : Nat) : Nat := if h : 0 < n then bad 0 else 0\ntermination_by let x := missing; n\ndecreasing_by exact h",
        "def bad (n : Nat) : Nat := if h : 0 < n then bad 0 else 0\ntermination_by (n : Bool)\ndecreasing_by exact h",
        // The pin does not expose a leading lambda's original name in this proof.
        "def bad : Nat -> Nat := fun n => if h : 0 < n then bad (n - 1) else 0\ntermination_by size => size\ndecreasing_by exact @Nat.sub_lt n 1 h (Nat.succ_pos 0)",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err(),
            "the invalid definition must be refused: {source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    // The pin ignores hints after successful nonrecursive elaboration. A bad
    // unused measure/proof must not turn the resulting ordinary def irreducible.
    base.check_source_files(
        &[b"def ordinary (n : Nat) : Nat := 42\ntermination_by missing\ndecreasing_by exact absent\ntheorem ordinaryComputes : ordinary 10 = 42 := by rfl"],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .expect("nonrecursive hints are ignored")
    .into_complete()
    .expect("ordinary source checking completes");
}

fn assert_explicit_scope_limits(base: &Engine) {
    for source in [
        // Multi-varying-argument packing is a later extension; a fixed
        // parameter must not silently be frozen at its initial value.
        "def changes (a n : Nat) : Nat := if h : 0 < n then changes (a + 1) (n - 1) else a\ntermination_by n\ndecreasing_by exact @Nat.sub_lt n 1 h (Nat.succ_pos 0)",
        // This slice does not claim measure search or automatic proof synthesis.
        "def absentMeasure (n : Nat) : Nat := if h : 0 < n then absentMeasure 0 else 0\ndecreasing_by exact h",
        "def absentProof (n : Nat) : Nat := if h : 0 < n then absentProof 0 else 0\ntermination_by n",
        // Declaration metadata is attached only by the supported actual-def path.
        "abbrev otherKind (n : Nat) : Nat := if h : 0 < n then otherKind 0 else 0\ntermination_by n\ndecreasing_by exact h",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err(),
            "unsupported well-founded shape must remain an explicit refusal: {source}"
        );
    }
}

#[test]
fn native_well_founded_measures_and_checked_decreasing_proofs() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let base = import_closure(&lib);
            assert_computations(&base);
            assert_decreasing_refusals(&base);
            assert_explicit_scope_limits(&base);
            well_founded_opacity::assert_source_opacity_routes(&base);
        })
        .expect("spawn native checking thread")
        .join()
        .expect("native well-founded checks finish");
}
