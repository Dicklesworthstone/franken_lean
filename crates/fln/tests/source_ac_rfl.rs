//! Generic AC reflection through the real imported class registry and both
//! checker seats. Every positive and negative source row is also judged by
//! the pinned executable; the implementation never asks it for a proof.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, OleanCheckLimits, OleanDecodeLimits,
    OleanModuleInput, Outcome, SourceCheckLimits, olean_module_imports,
};
use fln_env::constants::ConstantInfo;
use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
    process::Command,
};

const STACK: usize = 128 * 1024 * 1024;
const ROOTS: &[&str] = &["Init.Data.AC", "Init.Data.Nat.Basic"];
const HEADER: &str = "prelude\nimport Init.Data.AC\nimport Init.Data.Nat.Basic\n";
const BINDER_BOUNDARY: &str = "theorem binder_boundary (a : Nat) (_h : (fun x : Nat => a + x) = (fun x : Nat => x + a)) : (fun x : Nat => a + x) = (fun x : Nat => x + a) := by first | ac_rfl | exact _h";

const ACCEPT: &[(&str, &str)] = &[
    (
        "generic_assoc",
        "theorem generic_assoc {α : Type} (op : α → α → α) [Std.Associative op] (a b c : α) : op (op a b) c = op a (op b c) := by ac_rfl",
    ),
    (
        "generic_comm",
        "theorem generic_comm {α : Type} (op : α → α → α) [Std.Associative op] [Std.Commutative op] (a b c : α) : op (op a b) c = op c (op b a) := by ac_rfl",
    ),
    (
        "generic_idem",
        "theorem generic_idem {α : Type} (op : α → α → α) [Std.Associative op] [Std.IdempotentOp op] (a b : α) : op (op a a) (op b b) = op a b := by ac_rfl",
    ),
    (
        "generic_neutral",
        "theorem generic_neutral {α : Type} (op : α → α → α) [Std.Associative op] (e : α) [Std.LawfulIdentity op e] (a b : α) : op (op e a) (op b e) = op a b := by ac_rfl",
    ),
    (
        "under_function",
        "theorem under_function {α β : Type} (op : α → α → α) [Std.Associative op] [Std.Commutative op] (f : α → β) (a b : α) : f (op a b) = f (op b a) := by ac_rfl",
    ),
    (
        "under_binder",
        "theorem under_binder (a : Nat) : (fun x : Nat => a + x) = (fun x : Nat => x + a) := by ac_rfl",
    ),
    (
        "sort_universe",
        "theorem sort_universe {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.Commutative op] (a b : α) : op a b = op b a := by ac_rfl",
    ),
    (
        "nat_nested",
        "theorem nat_nested (a b c : Nat) : (a + b) * (0 + c) = 1 * c * (b + 0 + a) := by ac_rfl",
    ),
    (
        "propositions",
        "theorem propositions (p q : Prop) : (p ∨ p ∨ q ∧ True) = (q ∨ p) := by ac_rfl",
    ),
    (
        "reflexive",
        "theorem reflexive (a : Nat) : a = a := by ac_rfl",
    ),
    (
        "backtrack",
        "theorem backtrack {α : Type} (op : α → α → α) [Std.Associative op] (a b : α) (h : op a b = op b a) : op a b = op b a := by first | ac_rfl | exact h",
    ),
    (
        "overlapping_prefix",
        "theorem overlapping_prefix {α : Type} (op : α → α → α) [Std.Associative op] [Std.Commutative op] (F : α → α → α) (G : (α → α) → α → α) (a b c d : α) : F (op b a) (G (F (op b a)) (op d c)) = F (op a b) (G (F (op a b)) (op c d)) := by ac_rfl",
    ),
];

const REFUSE: &[(&str, &str)] = &[
    (
        "without_assoc",
        "example {α : Type} (op : α → α → α) [Std.Commutative op] (a b : α) : op a b = op b a := by ac_rfl",
    ),
    (
        "without_comm",
        "example {α : Type} (op : α → α → α) [Std.Associative op] (a b : α) : op a b = op b a := by ac_rfl",
    ),
    (
        "without_idem",
        "example {α : Type} (op : α → α → α) [Std.Associative op] [Std.Commutative op] (a : α) : op a a = a := by ac_rfl",
    ),
    (
        "different_atom",
        "example (a b : Nat) : a + b = a + a := by ac_rfl",
    ),
    ("non_equality", "example : True := by ac_rfl"),
    (
        "unlawful_identity",
        "example {α : Type} (op : α → α → α) [Std.Associative op] (e : α) [Std.Identity op e] (a : α) : op a e = a := by ac_rfl",
    ),
    (
        "unrelated_laws",
        "example {α : Type} (op other : α → α → α) [Std.Associative other] [Std.Commutative other] (a b : α) : op a b = op b a := by ac_rfl",
    ),
];

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn unsupported_ac(problem: &fln::SourceCheckError) -> bool {
    let fln::SourceCheckError::Command { error, .. } = problem else {
        return false;
    };
    matches!(error.as_ref(), fln::EngineExecutionError::Frontend(
        fln::DefinitionFrontendError::Elaborate(fln_elab::NatDefinitionElabError::Inference(
            fln_elab::source::SourceInferenceError::Tactic(
                fln_elab::source::TacticError::UnsupportedTactic(kind)))))
        if kind == &name("Lean.Parser.Tactic.acRfl"))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))
}

fn reference() -> Option<(PathBuf, PathBuf)> {
    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .filter(|p| p.join("Init/Data/AC.olean").is_file());
    let binary = std::env::var_os("FLN_REFERENCE_LEAN")
        .or_else(|| std::env::var_os("FLN_REFERENCE_BIN"))
        .map(PathBuf::from)
        .or_else(|| {
            library
                .as_ref()?
                .parent()?
                .parent()
                .map(|p| p.join("bin/lean"))
        })
        .filter(|p| p.is_file());
    let reference = library.zip(binary);
    assert!(
        reference.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned AC source differential requires FLN_REFERENCE_LIB and the Reference executable"
    );
    if reference.is_none() {
        eprintln!("SKIP: pinned AC Reference/library unavailable");
    }
    reference
}

fn imported(library: &Path) -> Engine {
    let roots: Vec<_> = ROOTS.iter().map(|root| name(root)).collect();
    let mut pending = roots.clone();
    let mut seen = BTreeSet::new();
    let mut names = Vec::new();
    let mut parts = Vec::new();
    while let Some(module) = pending.pop() {
        if !seen.insert(module.clone()) {
            continue;
        }
        let path = module
            .to_display_string()
            .split('.')
            .fold(library.to_owned(), |path, component| path.join(component))
            .with_extension("olean");
        let artifact = std::fs::read(&path).expect("pinned exported module");
        pending.extend(
            olean_module_imports(&artifact, OleanDecodeLimits::new(artifact.len()))
                .expect("pinned dependency header"),
        );
        parts.push([
            artifact,
            std::fs::read(path.with_extension("olean.server")).expect("server companion"),
            std::fs::read(path.with_extension("olean.private")).expect("private companion"),
        ]);
        names.push(module);
    }
    let artifact_bytes = parts.iter().flatten().map(Vec::len).sum();
    let inputs: Vec<_> = names
        .iter()
        .zip(&parts)
        .map(|(name, [artifact, server, private])| OleanModuleInput {
            name,
            artifact,
            server_artifact: Some(server),
            private_artifact: Some(private),
        })
        .collect();
    let mut budget =
        SourceOleanImportLimits::new(OleanCheckLimits::new(artifact_bytes, limits().kernel));
    // Extension captures are independent encodings of the complete public and
    // private journals, not a fraction of the object-file byte count.
    budget.max_capture_bytes = 256 * 1024 * 1024;
    budget.jobs.worker_stack_bytes = STACK;
    budget.read_jobs = budget.jobs;
    eprintln!(
        "ac_rfl: admitting {} complete modules ({artifact_bytes} bytes)",
        inputs.len()
    );
    let imported = Engine::builder()
        .build_empty()
        .import_olean_modules_for_source(&inputs, &roots, &KVMap::new(), budget)
        .expect("AC library metadata")
        .into_complete()
        .expect("AC library passes both checker seats");
    assert_eq!(imported.checked.modules.len(), inputs.len());
    imported.engine
}

fn oracle(
    binary: &Path,
    library: &Path,
    directory: &Path,
    label: &str,
    body: &str,
    accepted: bool,
) {
    let path = directory.join(format!("{label}.lean"));
    std::fs::write(&path, format!("{HEADER}{body}\n")).expect("oracle input");
    let result = Command::new(binary)
        .arg(&path)
        .env("LEAN_PATH", library)
        .output()
        .expect("run pinned AC tactic");
    assert_eq!(
        result.status.code(),
        Some(if accepted { 0 } else { 1 }),
        "pin {label}: {}\n{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
    if accepted {
        assert!(
            result.stdout.is_empty() && result.stderr.is_empty(),
            "pin {label} emitted diagnostics"
        );
    }
}

#[test]
fn generic_ac_reflection_matches_the_pin_and_checks_every_proof() {
    let Some((library, binary)) = reference() else {
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let directory = std::env::temp_dir().join(format!(
                "fln-ac-rfl-{}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            std::fs::create_dir(&directory).expect("fresh AC oracle directory");
            for (label, source) in ACCEPT {
                oracle(&binary, &library, &directory, label, source, true);
            }
            for (label, source) in REFUSE {
                oracle(&binary, &library, &directory, label, source, false);
            }
            oracle(
                &binary,
                &library,
                &directory,
                "binder_boundary",
                BINDER_BOUNDARY,
                true,
            );
            let base = imported(&library);
            let before = base.logical_root(&KVMap::new());
            let mut failures = Vec::new();
            for (label, source) in ACCEPT {
                eprintln!("ac_rfl accepted: {label}");
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let checked = base
                        .check_source_files(
                            &[source.as_bytes()],
                            &KVMap::new(),
                            SourceCheckLimits::new(limits()),
                        )
                        .unwrap_or_else(|error| panic!("{label}: {error:?}"))
                        .into_complete()
                        .unwrap_or_else(|reason| panic!("{label}: {reason:?}"));
                    assert_eq!(checked.theorems, 1);
                    let Some(ConstantInfo::Thm(theorem)) =
                        checked.engine.environment().find(&name(label))
                    else {
                        panic!("missing theorem {label}")
                    };
                    assert!(
                        !theorem.value.has_expr_mvar()
                            && !theorem.value.has_level_mvar()
                            && !theorem.value.has_fvar()
                    );
                    assert_eq!(base.logical_root(&KVMap::new()), before);
                }));
                if result.is_err() {
                    failures.push(*label);
                }
            }
            for (label, source) in REFUSE {
                eprintln!("ac_rfl refused: {label}");
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let error = base
                        .check_source_files(
                            &[source.as_bytes()],
                            &KVMap::new(),
                            SourceCheckLimits::new(limits()),
                        )
                        .expect_err("the pin-refused equality must not be admitted");
                    assert!(
                        !unsupported_ac(&error),
                        "{label} must be an ordinary failed proof: {error:?}"
                    );
                    assert!(
                        !matches!(
                            error.disposition().0,
                            "resource" | "inconclusive" | "internal-fault"
                        ),
                        "{label}: {error:?}"
                    );
                    assert_eq!(base.logical_root(&KVMap::new()), before);
                }));
                if result.is_err() {
                    failures.push(*label);
                }
            }
            // The scoped traversal now implements this previously unsupported
            // binder case. ACCEPT also checks it directly, without a hypothesis
            // or fallback that could conceal a missing AC implementation.
            let supported = base
                .check_source_files(
                    &[BINDER_BOUNDARY.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits()),
                )
                .expect("the implemented binder traversal accepts the former boundary")
                .into_complete()
                .expect("binder congruence passes both checker seats");
            let Some(ConstantInfo::Thm(theorem)) = supported
                .engine
                .environment()
                .find(&name("binder_boundary"))
            else {
                panic!("missing checked binder capability theorem")
            };
            assert!(
                !theorem.value.has_expr_mvar()
                    && !theorem.value.has_level_mvar()
                    && !theorem.value.has_fvar()
            );
            assert_eq!(supported.theorems, 1);
            assert_eq!(base.logical_root(&KVMap::new()), before);
            let written = BINDER_BOUNDARY.replace("first | ac_rfl | exact _h", "exact _h");
            base.check_source_files(
                &[written.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect("the control statement and its hypothesis are valid")
            .into_complete()
            .expect("the written binder control passes both seats");
            // A checker veto cannot be turned into successful tactic fallback or
            // a published theorem; the unchanged base remains usable afterwards.
            let mut stopped = limits();
            stopped.kernel.steps = 0;
            let result = base.check_source_files(
                &[ACCEPT[1].1.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(stopped),
            );
            assert!(
                matches!(result, Ok(Outcome::Inconclusive(_)))
                    || result.as_ref().is_err_and(|error| matches!(
                        error.disposition().0,
                        "resource" | "inconclusive"
                    )),
                "zero kernel budget: {result:?}"
            );
            assert_eq!(base.logical_root(&KVMap::new()), before);
            assert!(failures.is_empty(), "AC source cases failed: {failures:?}");
        })
        .expect("spawn AC source checking thread")
        .join()
        .expect("AC source gate");
}
