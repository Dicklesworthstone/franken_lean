//! AC normalization over the actual pinned classes, with ordinary proof admission.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, Environment, KVMap, Name, OleanCheckLimits,
    OleanDecodeLimits, OleanModuleInput, Outcome, SourceCheckLimits,
};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

const STACK: usize = 256 * 1024 * 1024;
const BYTES: usize = 256 * 1024 * 1024;
const HEADER: &str = "prelude\nimport Init.Data.AC\nimport Init.Guard\n";

struct Fixture {
    compiler: PathBuf,
    library: PathBuf,
    engine: Engine,
}

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)))
}

fn fixture() -> Option<&'static Fixture> {
    static FIXTURE: OnceLock<Option<Fixture>> = OnceLock::new();
    FIXTURE
        .get_or_init(|| {
            let row = include_str!("../../../SUITE.lock")
                .lines()
                .find(|line| line.starts_with("reference leanprover/lean4 "))
                .expect("Reference pin");
            let field = |key: &str| {
                row.split_whitespace()
                    .find_map(|word| word.strip_prefix(key))
                    .expect("Reference field")
            };
            let library = std::env::var_os("FLN_REFERENCE_LIB")
                .map(PathBuf::from)
                .or_else(|| {
                    std::env::var_os("HOME").map(|home| {
                        PathBuf::from(home)
                            .join(".elan/toolchains")
                            .join(format!("leanprover--lean4---{}", field("tag=")))
                            .join("lib/lean")
                    })
                })
                .filter(|path| path.join("Init/Data/AC.olean").is_file());
            let Some(library) = library else {
                assert!(
                    std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                    "the pinned AC library is required"
                );
                eprintln!("SKIP: AC differential requires the pinned Reference library");
                return None;
            };
            let compiler = library
                .parent()
                .and_then(Path::parent)
                .expect("pinned toolchain root")
                .join("bin/lean");
            let output = Command::new(&compiler).arg("--githash").output().unwrap();
            assert!(output.status.success());
            assert_eq!(
                String::from_utf8_lossy(&output.stdout).trim(),
                field("commit="),
                "the oracle and artifacts must use the SUITE.lock pin"
            );
            let engine = import(&library);
            Some(Fixture {
                compiler,
                library,
                engine,
            })
        })
        .as_ref()
}

/// Derive the actual artifact closure instead of fabricating the law classes.
fn import(library: &Path) -> Engine {
    let roots = [name("Init.Data.AC"), name("Init.Guard")];
    let mut pending: Vec<_> = roots.iter().cloned().map(|root| (root, false)).collect();
    let mut seen = BTreeSet::new();
    let mut ordered = Vec::new();
    let mut artifacts = BTreeMap::new();
    while let Some((module, finished)) = pending.pop() {
        if finished {
            ordered.push(module);
            continue;
        }
        if !seen.insert(module.clone()) {
            continue;
        }
        assert!(seen.len() <= 512, "bounded pinned AC import closure");
        let relative = module.to_display_string().replace('.', "/");
        let path = library.join(relative).with_extension("olean");
        let optional = |path: PathBuf| match std::fs::read(path) {
            Ok(bytes) => Some(bytes),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => panic!("reading a pinned companion: {error}"),
        };
        let public = std::fs::read(&path).unwrap();
        let dependencies =
            fln::olean_module_imports(&public, OleanDecodeLimits::new(BYTES)).unwrap();
        artifacts.insert(
            module.clone(),
            (
                public,
                optional(path.with_extension("olean.server")),
                optional(path.with_extension("olean.private")),
            ),
        );
        pending.push((module, true));
        pending.extend(dependencies.into_iter().rev().map(|module| (module, false)));
    }
    let inputs: Vec<_> = ordered
        .iter()
        .map(|module| {
            let (public, server, private) = &artifacts[module];
            OleanModuleInput {
                name: module,
                artifact: public,
                server_artifact: server.as_deref(),
                private_artifact: private.as_deref(),
            }
        })
        .collect();
    Engine::from_environment(Environment::new())
        .import_olean_modules_for_source(
            &inputs,
            &roots,
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                BYTES,
                Budget::for_stack_bytes(STACK),
            )),
        )
        .unwrap_or_else(|error| panic!("the actual AC closure must import: {error:?}"))
        .into_complete()
        .expect("the actual AC closure passes both checkers")
        .engine
}

fn with_fixture(run: impl FnOnce(&Fixture) + Send + 'static) {
    static RUN: Mutex<()> = Mutex::new(());
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let _serial = RUN
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if let Some(fixture) = fixture() {
                run(fixture);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

fn oracle(fixture: &Fixture, source: &str, accepted: bool) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!("fln-ac-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let path = directory.join(format!("{}.lean", NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::write(&path, format!("{HEADER}{source}")).unwrap();
    let output = Command::new(&fixture.compiler)
        .env("LEAN_PATH", &fixture.library)
        .arg("-j1")
        .arg(&path)
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some(if accepted { 0 } else { 1 }),
        "pinned AC verdict: {source}\n{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn check(fixture: &Fixture, source: &str) -> Engine {
    oracle(fixture, source, true);
    fixture
        .engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("AC evidence passes both checkers")
        .engine
}

fn reject(fixture: &Fixture, source: &str) {
    oracle(fixture, source, false);
    let root = fixture.engine.logical_root(&KVMap::new());
    let error = fixture
        .engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .expect_err("the unavailable AC law must not become a proof");
    assert_eq!(error.disposition().2, 1, "ordinary refusal: {error:?}");
    assert_eq!(fixture.engine.logical_root(&KVMap::new()), root);
    assert!(!fixture.engine.environment().contains(&name("bad")));
}

#[test]
fn associative_and_commutative_dictionaries_normalize_generic_operators() {
    with_fixture(|fixture| {
        check(
            fixture,
            r#"
universe u
theorem reassociate {α : Sort u} (op : α → α → α) [Std.Associative op]
    (a b c d : α) : op (op (op a b) c) d = op a (op b (op c d)) := by
  ac_rfl
theorem permute {α : Sort u} (op : α → α → α)
    [Std.Associative op] [Std.Commutative op] (a b c d : α) :
    op (op a b) (op c d) = op d (op b (op a c)) := by ac_rfl
theorem ordinaryLocalLaw {α : Sort u} (op : α → α → α)
    (law : Std.Associative op) (a b c : α) :
    op (op a b) c = op a (op b c) := by ac_rfl
theorem typedAscription {α : Sort u} (op : α → α → α) [Std.Associative op]
    (a b c : α) : (op (op a b) c : α) = op a (op b c) := by ac_rfl
theorem reflexive (a : Nat) : a = a := by ac_rfl
theorem betaReflexive {α : Type} (a : α) : (fun x => x) a = a := by ac_rfl
theorem letReflexive {α : Type} (a : α) : (let x := a; x) = a := by ac_rfl
"#,
        );
    });
}

#[test]
fn mixed_operators_and_prop_carriers_use_their_own_laws() {
    with_fixture(|fixture| {
        check(
            fixture,
            r#"
universe u
theorem mixed {α : Sort u} (op inner : α → α → α)
    [Std.Associative op] [Std.Commutative op]
    [Std.Associative inner] [Std.Commutative inner] (a b c d : α) :
    op (inner a b) (inner c d) = op (inner d c) (inner b a) := by ac_rfl
theorem propositionOperator (op : Prop → Prop → Prop)
    [Std.Associative op] [Std.Commutative op] (p q r : Prop) :
    op (op p q) r = op r (op q p) := by ac_rfl
theorem propositionLaws (p q : Prop) : (p ∨ p ∨ q ∧ True) = (q ∨ p) := by ac_rfl
theorem nestedEquality (x y : Nat) : (x + y = 42) = (y + x = 42) := by ac_rfl
theorem exposeReflexiveEquality (a : Nat) : True ∧ (a = a) := by ac_rfl
theorem exposeAssociativeEquality (a b c : Nat) :
    True ∧ ((a+b)+c = a+(b+c)) := by ac_rfl
theorem sharedOccurrence {α : Type} (op : α → α → α) [Std.Associative op]
    (pack : α → α → α) (a b c d : α) :
    pack (op (op a b) c) (op (op (op a b) c) d) =
      pack (op a (op b c)) (op a (op b (op c d))) := by ac_rfl
"#,
        );
    });
}

#[test]
fn identity_and_idempotence_preserve_the_pins_normal_form() {
    with_fixture(|fixture| {
        check(
            fixture,
            r#"
universe u
theorem neutral {α : Sort u} (op : α → α → α)
    [Std.Associative op] (e : α) [Std.LawfulIdentity op e] (a b : α) :
    op (op e a) (op b e) = op a b := by ac_rfl
theorem allNeutral {α : Sort u} (op : α → α → α)
    [Std.Associative op] (e : α) [Std.LawfulIdentity op e] :
    op (op e e) e = e := by ac_rfl
theorem firstNeutral {α : Sort u} (op : α → α → α)
    [Std.Associative op] (e z : α)
    [Std.LawfulIdentity op e] [Std.LawfulIdentity op z] : op e z = e := by ac_rfl
theorem adjacentDuplicates {α : Sort u} (op : α → α → α)
    [Std.Associative op] [Std.IdempotentOp op] (a b : α) :
    op a (op a b) = op a b := by ac_rfl
theorem separatedDuplicates {α : Sort u} (op : α → α → α)
    [Std.Associative op] [Std.Commutative op] [Std.IdempotentOp op]
    (a b c : α) : op (op a b) (op c a) = op c (op b a) := by ac_rfl
"#,
        );
    });
}

#[test]
fn normalization_lifts_through_binders_and_preserves_dependent_arguments() {
    with_fixture(|fixture| {
        check(
            fixture,
            r#"
universe u
theorem underLambda {α : Sort u} (op : α → α → α)
    [Std.Associative op] [Std.Commutative op] (a : α) :
    (fun x => op a x) = (fun x => op x a) := by ac_rfl
theorem arrowDomain (x y : Nat) (P : Prop) :
    (x + y = 42 → P) = (y + x = 42 → P) := by ac_rfl
inductive VectorAC (α : Type u) : Nat → Type u where
  | nil : VectorAC α 0
  | cons : α → VectorAC α n → VectorAC α (n+1)
def preserveAC (n : Nat) (xs : VectorAC α n) := xs
theorem dependentArguments (n m : Nat) (xs : VectorAC α (n+m))
    (ys : VectorAC α (m+n)) :
    (preserveAC (n+m) xs, preserveAC (m+n) ys, n+m) =
    (preserveAC (n+m) xs, preserveAC (m+n) ys, m+n) := by ac_rfl
"#,
        );
    });
}

#[test]
fn unavailable_laws_and_order_changes_refuse_without_publication() {
    with_fixture(|fixture| {
        for source in [
            r#"
theorem bad {α : Type} (op : α → α → α) [Std.Commutative op]
    (a b : α) : op a b = op b a := by ac_rfl
"#,
            r#"
theorem bad {α : Type} (op : α → α → α) [Std.Associative op]
    (a b : α) : op a b = op b a := by ac_rfl
"#,
            r#"
theorem bad {α : Type} (op : α → α → α)
    [Std.Associative op] [Std.IdempotentOp op] (a b : α) :
    op a (op b a) = op a b := by ac_rfl
"#,
            r#"
theorem bad {α : Type} (op : α → α → α)
    [Std.Associative op] (e z : α)
    [Std.LawfulIdentity op e] [Std.LawfulIdentity op z] : op e z = z := by ac_rfl
"#,
            r#"
theorem bad {α : Type} (op : α → α → α)
    [Std.Associative op] [Std.Commutative op] (a b : α) : op a b = a := by ac_rfl
"#,
            r#"
theorem bad {α : Type} (op : α → α → α) [Std.Associative op] (a b c : α) :
    (fun x => op x c) (op a b) = op a (op b c) := by ac_rfl
"#,
            r#"
theorem bad {α : Type} (op : α → α → α) [Std.Associative op] (a b c : α) :
    (let x := op a b; op x c) = op a (op b c) := by ac_rfl
"#,
            "theorem bad : True := by ac_rfl\n",
            "theorem bad (p : Prop) : p ↔ p := by ac_rfl\n",
            "theorem bad {α : Sort u} (a : α) : HEq a a := by ac_rfl\n",
            "theorem bad : False := by ac_rfl\n",
        ] {
            reject(fixture, source);
        }
    });
}

#[test]
fn failed_ac_attempt_restores_the_goal_and_local_instances() {
    with_fixture(|fixture| {
        let root = fixture.engine.logical_root(&KVMap::new());
        check(
            fixture,
            r#"
theorem recovered {α : Type} (op : α → α → α) [Std.Associative op]
    (a b : α) (h : op a b = op b a) : op a b = op b a := by
  first | ac_rfl | exact h
theorem afterRollback {α : Type} (op : α → α → α)
    [Std.Associative op] [Std.Commutative op] (a b : α) : op a b = op b a := by
  first | (ac_rfl; fail) | ac_rfl
inductive CustomAC (a : Nat) : Nat → Prop where
  | reflexive : CustomAC a a
theorem customAC_refl (a : Nat) : CustomAC a a := CustomAC.reflexive
theorem customFallback (a : Nat) : CustomAC a a := by
  first | ac_rfl | exact CustomAC.reflexive
"#,
        );
        reject(
            fixture,
            r#"
inductive CustomAC (a : Nat) : Nat → Prop where
  | reflexive : CustomAC a a
theorem customAC_refl (a : Nat) : CustomAC a a := CustomAC.reflexive
theorem regular (a : Nat) : CustomAC a a := CustomAC.reflexive
theorem bad (a : Nat) : CustomAC a a := by ac_rfl
"#,
        );
        assert_eq!(fixture.engine.logical_root(&KVMap::new()), root);
    });
}

#[test]
fn ac_nf_distinguishes_normalization_from_optional_goal_closing() {
    with_fixture(|fixture| {
        check(
            fixture,
            r#"
universe u
theorem acOpen {α : Sort u} (op : α → α → α) [Std.Associative op]
    (a b c : α) : op (op a b) c = op a (op b c) := by
  ac_nf0
  guard_target =ₛ op a (op b c) = op a (op b c)
  rfl
theorem acClosed {α : Sort u} (op : α → α → α) [Std.Associative op]
    (a b c : α) : op (op a b) c = op a (op b c) := by ac_nf
theorem acContinues {α : Sort u} (op : α → α → α) [Std.Associative op]
    (a b c : α) (P : α → Prop) (ready : True → P (op a (op b c))) :
    P (op (op a b) c) := by
  ac_nf
  guard_target =ₛ P (op a (op b c))
  exact ready True.intro
theorem acTrue : True := by ac_nf
theorem acTrueOpen : True := by
  ac_nf0
  guard_target =ₛ True
  exact True.intro
"#,
        );
    });
}

#[test]
fn ac_nf_locations_select_only_the_written_target_and_hypotheses() {
    with_fixture(|fixture| {
        check(
            fixture,
            r#"
universe u v
theorem acDefaultOnly {α : Sort u} (op : α → α → α) [Std.Associative op]
    (a b c : α) (P : α → Prop) (h : P (op (op a b) c))
    (ready : True → P (op a (op b c))) : P (op (op a b) c) := by
  ac_nf
  guard_hyp h :ₛ P (op (op a b) c)
  guard_target =ₛ P (op a (op b c))
  exact ready True.intro
theorem acTargetOnly {α : Sort u} (op : α → α → α) [Std.Associative op]
    (a b c : α) (P : α → Prop) (h : P (op (op a b) c)) : P (op (op a b) c) := by
  ac_nf0
  guard_hyp h :ₛ P (op (op a b) c)
  guard_target =ₛ P (op a (op b c))
  ac_nf0 at h
  guard_hyp h :ₛ P (op a (op b c))
  exact h
theorem acNamedTarget {α : Sort u} (op : α → α → α) [Std.Associative op]
    (a b c : α) (P : α → Prop) (h untouched : P (op (op a b) c)) :
    P (op (op a b) c) := by
  ac_nf0 at h ⊢
  guard_hyp h :ₛ P (op a (op b c))
  guard_hyp untouched :ₛ P (op (op a b) c)
  guard_target =ₛ P (op a (op b c))
  exact h
theorem acNamedClosed {α : Sort u} (op : α → α → α) [Std.Associative op]
    (a b c : α) (P : α → Prop) (h : P (op (op a b) c)) :
    P (op a (op b c)) := by ac_nf at h
def dataHypAC {α : Sort u} (op : α → α → α) [Std.Associative op]
    (a b c : α) (D : α → Type v) (d : D (op (op a b) c)) :
    D (op a (op b c)) := by
  ac_nf0 at d
  guard_hyp d :ₛ D (op a (op b c))
  exact d
"#,
        );
    });
}

#[test]
fn ac_explicit_locations_resolve_auxiliary_self_and_preserve_scope() {
    with_fixture(|fixture| {
        let root = fixture.engine.logical_root(&KVMap::new());
        check(
            fixture,
            r#"
def explicitSelfLocation : Nat := by
  first
  | ac_nf0 at explicitSelfLocation
    exact 7
  | exact 42
theorem exactSelfValue : explicitSelfLocation = 7 := by rfl
namespace ScopedAC
def qualified : Nat := by
  first
  | ac_nf0 at ScopedAC.qualified
    exact 7
  | exact 42
def rootQualified : Nat := by
  first
  | ac_nf0 at _root_.ScopedAC.rootQualified
    exact 7
  | exact 42
end ScopedAC
def shadowSelf (shadowSelf : Nat) : Nat := by
  ac_nf0 at shadowSelf
  guard_hyp shadowSelf : Nat
  exact shadowSelf
theorem qualifiedValue : ScopedAC.qualified = 7 := by rfl
theorem rootValue : ScopedAC.rootQualified = 42 := by rfl
theorem shadowValue : shadowSelf 9 = 9 := by rfl
theorem rewritesSelf (a b c : Nat) : (a + b) + c = a + (b + c) := by
  ac_nf0 at rewritesSelf
  guard_hyp rewritesSelf :ₛ ∀ (a b c : Nat), a + (b + c) = a + (b + c)
  ac_rfl
theorem wildcardSelf (a b c : Nat) : (a + b) + c = a + (b + c) := by
  ac_nf0 at *
  guard_hyp wildcardSelf :ₛ ∀ (a b c : Nat), (a + b) + c = a + (b + c)
  rfl
"#,
        );
        reject(
            fixture,
            r#"
theorem bad (a b c : Nat) : (a + b) + c = a + (b + c) := by
  ac_nf0 at bad
  have h := bad a b c
  ac_nf0
  exact h
"#,
        );
        assert_eq!(fixture.engine.logical_root(&KVMap::new()), root);
    });
}

#[test]
fn ac_nf_wildcard_skips_dependencies_data_and_let_bound_proofs() {
    with_fixture(|fixture| {
        check(
            fixture,
            r#"
universe u
theorem acWildcard {α : Type u} (op : α → α → α) [Std.Associative op]
    (a b c : α) (P : α → Prop) (D : α → Type u)
    (data : D (op (op a b) c)) (h : P (op (op a b) c)) (dep : h = h)
    (fromLet : P (op (op a b) c)) (free : P (op (op a b) c)) : True := by
  let held : P (op (op a b) c) := fromLet
  ac_nf0 at *
  guard_hyp data :ₛ D (op (op a b) c)
  guard_hyp h :ₛ P (op (op a b) c)
  guard_hyp fromLet :ₛ P (op (op a b) c)
  guard_hyp held :ₛ P (op (op a b) c) :=ₛ fromLet
  guard_hyp free :ₛ P (op a (op b c))
  exact True.intro
theorem acWildcardTarget {α : Sort u} (op : α → α → α) [Std.Associative op]
    (a b c : α) (P : α → Prop) (h : P (op (op a b) c)) : h = h := by
  ac_nf0 at *
  guard_hyp h :ₛ P (op (op a b) c)
  rfl
theorem acDependent {α : Sort u} (op : α → α → α) [Std.Associative op]
    (a b c : α) (P : α → Prop) (h : P (op (op a b) c)) (dep : h = h) : h = h := by
  ac_nf0 at h
  guard_hyp h :ₛ P (op a (op b c))
  exact dep
"#,
        );
    });
}

#[test]
fn ac_nf_failures_restore_context_and_leave_no_declarations() {
    with_fixture(|fixture| {
        let root = fixture.engine.logical_root(&KVMap::new());
        check(
            fixture,
            r#"
universe u
theorem acRollback {α : Sort u} (op : α → α → α) [Std.Associative op]
    (a b c : α) (P : α → Prop) (h : P (op (op a b) c)) : P (op (op a b) c) := by
  first | (ac_nf0 at h ⊢; fail) | skip
  guard_hyp h :ₛ P (op (op a b) c)
  guard_target =ₛ P (op (op a b) c)
  exact h
"#,
        );
        for source in [
            "theorem bad : True := by ac_nf0\n",
            r#"
theorem bad {α : Type} (op : α → α → α) [Std.Associative op]
    (a b c : α) : op (op a b) c = op a (op b c) := by ac_nf0
"#,
            "theorem bad : True := by ac_nf at missing\n",
            "theorem bad : False := by ac_nf\n",
            r#"
theorem bad {α : Type} (op : α → α → α) [Std.Associative op]
    (a b : α) : op a b = op b a := by ac_nf
"#,
        ] {
            reject(fixture, source);
        }
        assert_eq!(fixture.engine.logical_root(&KVMap::new()), root);
    });
}

#[test]
fn resource_refusal_keeps_the_base_reusable() {
    with_fixture(|fixture| {
        let source = r#"
theorem boundedAC {α : Type} (op : α → α → α)
    [Std.Associative op] [Std.Commutative op] (a b c : α) :
    op (op a b) c = op c (op b a) := by ac_rfl
"#;
        oracle(fixture, source, true);
        let root = fixture.engine.logical_root(&KVMap::new());
        let mut bounded = limits();
        bounded.admission.kernel.steps = 0;
        match fixture
            .engine
            .check_source_files(&[source.as_bytes()], &KVMap::new(), bounded)
        {
            Ok(Outcome::Inconclusive(_)) => {}
            Err(error) => assert_eq!(error.disposition().2, 3, "resource stop: {error:?}"),
            other => panic!("zero admission work cannot prove the declaration: {other:?}"),
        }
        assert_eq!(fixture.engine.logical_root(&KVMap::new()), root);
        assert!(!fixture.engine.environment().contains(&name("boundedAC")));
        // The reflected proof core supports larger inputs within its existing
        // 4096-node allowance. The tail has 127 atoms and each side has 129;
        // this must not inherit the old direct-proof builder's 128-atom cap.
        let mut tail = String::from("a");
        for _ in 1..127 {
            tail = format!("op a ({tail})");
        }
        // The same statement must elaborate and pass ordinary admission with
        // its direct class projection before measuring AC normalization work.
        let direct = format!(
            "theorem largeACControl {{α : Type}} (op : α → α → α) [Std.Associative op]\n\
             (a : α) : op (op a a) ({tail}) = op a (op a ({tail})) :=\n\
             Std.Associative.assoc (op := op) a a ({tail})\n"
        );
        let control = check(fixture, &direct);
        assert!(control.environment().contains(&name("largeACControl")));
        assert_eq!(fixture.engine.logical_root(&KVMap::new()), root);
        assert!(
            !fixture
                .engine
                .environment()
                .contains(&name("largeACControl"))
        );
        let large = format!(
            "theorem largeAC {{α : Type}} (op : α → α → α) [Std.Associative op]\n\
             (a : α) : op (op a a) ({tail}) = op a (op a ({tail})) := by ac_rfl\n"
        );
        let larger = check(fixture, &large);
        assert!(larger.environment().contains(&name("largeAC")));
        assert_eq!(fixture.engine.logical_root(&KVMap::new()), root);
        assert!(!fixture.engine.environment().contains(&name("largeAC")));
        check(fixture, source);
        assert_eq!(fixture.engine.logical_root(&KVMap::new()), root);
    });
}
