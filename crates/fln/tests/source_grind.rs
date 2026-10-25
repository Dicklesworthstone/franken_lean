//! Real pinned grind programs, admitted natively through both checker seats.
#![forbid(unsafe_code)]
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, OleanCheckLimits, OleanDecodeLimits,
    OleanModuleInput, Outcome, SourceCheckLimits, olean_module_imports,
};
use std::{collections::BTreeSet, path::Path, process::Command};

const STACK: usize = 128 * 1024 * 1024;
const ROOTS: &[&str] = &[
    "Init.Grind.Tactics",
    "Init.Grind.Lemmas",
    "Init.Grind.ToInt",
    "Init.Grind.Norm",
];
const HEADER: &str = "prelude\nimport Init.Grind.Tactics\nimport Init.Grind.Lemmas\nimport Init.Grind.ToInt\nimport Init.Grind.Norm\n";
fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)))
}
fn record_failure(failures: &mut Vec<String>, label: &str, detail: String) {
    eprintln!(
        "grind: failure {label}: {}",
        detail.chars().take(1800).collect::<String>()
    );
    failures.push(label.to_owned());
}
fn base(library: &Path) -> Engine {
    let roots: Vec<_> = ROOTS.iter().map(|text| name(text)).collect();
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
            .fold(library.to_path_buf(), |path, part| path.join(part))
            .with_extension("olean");
        let exported = std::fs::read(&path).unwrap();
        pending.extend(
            olean_module_imports(&exported, OleanDecodeLimits::new(exported.len())).unwrap(),
        );
        parts.push([
            exported,
            std::fs::read(path.with_extension("olean.server")).unwrap(),
            std::fs::read(path.with_extension("olean.private")).unwrap(),
        ]);
        names.push(module);
    }
    // Artifact volume is independent of the kernel's stack allowance. Charge
    // the complete real import closure, including server/private companions.
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
    let mut import_limits = SourceOleanImportLimits::new(OleanCheckLimits::new(
        artifact_bytes,
        limits().admission.kernel,
    ));
    // Captured extension graphs have their own encoding and can exceed the
    // underlying object-file bytes; keep this allowance independent as well.
    import_limits.max_capture_bytes = 1024 * 1024 * 1024;
    import_limits.jobs.threads = std::num::NonZeroUsize::new(4).unwrap();
    import_limits.jobs.worker_stack_bytes = STACK;
    import_limits.read_jobs = import_limits.jobs;
    eprintln!(
        "grind: importing {} modules, {artifact_bytes} artifact bytes, {} capture-byte allowance",
        inputs.len(),
        import_limits.max_capture_bytes,
    );
    let imported = Engine::builder()
        .build_empty()
        .import_olean_modules_for_source(&inputs, &roots, &KVMap::new(), import_limits)
        .unwrap_or_else(|error| panic!("grind import: {error:?}"));
    let imported = match imported {
        Outcome::Complete(imported) => imported,
        Outcome::Inconclusive(reason) => panic!("grind import inconclusive: {reason:?}"),
        Outcome::InternalFault(fault) => panic!("grind import internal fault: {fault:?}"),
    };
    assert_eq!(imported.checked.modules.len(), inputs.len());
    eprintln!(
        "grind: import complete ({} modules)",
        imported.checked.modules.len()
    );
    imported.engine
}

const ACCEPT: &[(&str, &str)] = &[
    (
        "constructor_injection",
        "example (a b : Nat) (h : Nat.succ a = Nat.succ b) : a = b := by grind",
    ),
    (
        "product_injection",
        "example (a b c d : Nat) (h : (a, b) = (c, d)) : a = c ∧ b = d := by grind",
    ),
    (
        "constructor_clash",
        "example (h : true = false) : False := by grind",
    ),
    (
        "nested",
        "example (f g : Nat → Nat) (a b c : Nat) (h : a = b) (h' : b = c) : f (g a) = f (g c) := by grind",
    ),
    (
        "function_and_argument",
        "example (f g : Nat → Nat) (a b : Nat) (hf : f = g) (ha : a = b) : f a = g b := by grind",
    ),
    (
        "curried",
        "example (f : Nat → Nat → Nat) (a b c d : Nat) (h : a = b) (h' : c = d) : f a c = f b d := by grind",
    ),
    (
        "local_partial",
        "example (f g : Nat → Nat → Nat) (a b c : Nat) (h : f a = g b) : f a c = g b c := by grind",
    ),
    (
        "predicate",
        "example (P : Nat → Prop) (a b : Nat) (h : a = b) (hp : P a) : P b := by grind",
    ),
    (
        "disequality",
        "example (f : Nat → Nat) (a b : Nat) (h : a = b) (hn : f a ≠ f b) : False := by grind",
    ),
    (
        "implications",
        "example (P Q R : Prop) (h : P) (h' : P → Q) (h'' : Q → R) : R := by grind",
    ),
    (
        "equation_premise",
        "example (a b c : Nat) (P : Prop) (h : a = b) (h' : b = c) (hp : a = c → P) : P := by grind",
    ),
    (
        "derived_equation",
        "example (P : Prop) (a b : Nat) (f : Nat → Nat) (h : P) (h' : P → a = b) : f a = f b := by grind",
    ),
    (
        "conjunction",
        "example (P Q R : Prop) (h : P ∧ Q) (h' : Q → R) : R ∧ P := by grind",
    ),
    (
        "disjunction_refutation",
        "example (P Q : Prop) (h : P ∨ Q) (hn : ¬ P) : Q := by grind",
    ),
    (
        "disjunction_construction",
        "example (P Q : Prop) (h : Q) : P ∨ Q := by grind only []",
    ),
    (
        "iff",
        "example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by grind",
    ),
    (
        "proposition_equality",
        "example (P Q : Prop) (h : P = Q) (hp : P) : Q := by grind",
    ),
    (
        "forall_goal",
        "example : ∀ (a b : Nat), a = b → b = a := by grind",
    ),
    (
        "negative_goal",
        "example (P Q : Prop) (h : P → Q) (hn : ¬ Q) : ¬ P := by grind",
    ),
    (
        "sort_polymorphic",
        "universe u\nexample {α : Sort u} (a b c : α) (h : a = b) (h' : b = c) : c = a := by grind",
    ),
    (
        "dependent_function",
        "example {α : Type} {β : α → Type} (f g : (a : α) → β a) (a : α) (h : f = g) : f a = g a := by grind",
    ),
    (
        "reducible_alias",
        "abbrev ident (n : Nat) := n\nexample (a b : Nat) (h : a = b) : ident a = b := by grind",
    ),
    (
        "truth",
        "example (P : Prop) (h : P) : P = True := by grind\nexample (P : Prop) (h : False) : P := by grind\nexample (P : Prop) : P → P := by grind",
    ),
    (
        "constant_spine",
        "opaque fixed : Nat → Nat → Nat := fun _ _ => 0\nexample (a b c : Nat) (h : a = b) : fixed a c = fixed b c := by grind",
    ),
    (
        "disjunction_cases",
        "example (P Q R : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R := by grind",
    ),
    (
        "classical",
        "example (P : Prop) : P ∨ ¬ P := by grind\nexample (P : Prop) (h : ¬¬P) : P := by grind",
    ),
];

const REFUSE: &[(&str, &str)] = &[
    ("unrelated", "example (P Q : Prop) (h : P) : Q := by grind"),
    (
        "noninjective",
        "example (f : Nat → Nat) (a b : Nat) (h : f a = f b) : a = b := by grind",
    ),
    (
        "missing_conjunct",
        "example (P Q : Prop) (h : P) : P ∧ Q := by grind",
    ),
    (
        "converse",
        "example (P Q : Prop) (h : P → Q) (hq : Q) : P := by grind",
    ),
    (
        "wrong_argument",
        "example (f g : Nat → Nat) (a b : Nat) (h : f = g) : f a = g b := by grind",
    ),
    (
        "after_success",
        "example (a : Nat) : a = a := by grind; rfl",
    ),
    (
        "try_must_not_skip",
        "example (a : Nat) : a + 0 = a := by try grind; rfl",
    ),
    (
        "constant_partial_function",
        "opaque fixed : Nat → Nat → Nat := fun _ _ => 0\nopaque other : Nat → Nat := fun _ => 0\nexample (a b : Nat) (h : fixed a = other) : fixed a b = other b := by grind",
    ),
    (
        "constant_partial_equality",
        "opaque fixed : Nat → Nat → Nat := fun _ _ => 0\nexample (a b c : Nat) (h : fixed a = fixed b) : fixed a c = fixed b c := by grind",
    ),
];

#[test]
fn ground_grind_proofs_and_refusals_match_the_live_pin() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(std::path::PathBuf::from)
            else {
                assert!(
                    std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                    "Reference required"
                );
                eprintln!("SKIP: locked Reference absent");
                return;
            };
            let compiler = library.parent().unwrap().parent().unwrap().join("bin/lean");
            let version = Command::new(&compiler).arg("--version").output().unwrap();
            assert!(version.status.success());
            assert!(
                String::from_utf8_lossy(&version.stdout)
                    .contains("8c9756b28d64dab099da31a4c09229a9e6a2ef35")
            );
            let directory = std::env::temp_dir().join(format!("fln-grind-{}", std::process::id()));
            std::fs::create_dir_all(&directory).unwrap();
            for (accepted, cases) in [(true, ACCEPT), (false, REFUSE)] {
                for (label, source) in cases {
                    let path = directory.join(format!("{label}.lean"));
                    std::fs::write(&path, format!("{HEADER}{source}\n")).unwrap();
                    let result = Command::new(&compiler).arg(&path).output().unwrap();
                    assert_eq!(
                        result.status.success(),
                        accepted,
                        "pin {label}: {}{}",
                        String::from_utf8_lossy(&result.stdout),
                        String::from_utf8_lossy(&result.stderr)
                    );
                }
            }
            let engine = base(&library);
            let options = KVMap::new();
            let before = engine.logical_root(&options);
            let mut failures = Vec::new();
            for (label, source) in ACCEPT {
                eprintln!("grind: native accept {label}");
                match engine.check_source_files(&[source.as_bytes()], &options, limits()) {
                    Ok(Outcome::Complete(_)) => {}
                    Ok(Outcome::Inconclusive(reason)) => {
                        record_failure(&mut failures, label, format!("inconclusive: {reason:?}"))
                    }
                    Ok(Outcome::InternalFault(fault)) => {
                        record_failure(&mut failures, label, format!("internal fault: {fault:?}"))
                    }
                    Err(error) => record_failure(&mut failures, label, format!("{error:?}")),
                }
                if engine.logical_root(&options) != before {
                    record_failure(&mut failures, label, "input logical root mutated".into());
                }
            }
            for (label, source) in REFUSE {
                eprintln!("grind: native refuse {label}");
                match engine.check_source_files(&[source.as_bytes()], &options, limits()) {
                    Err(error) => {
                        let disposition = error.disposition();
                        if disposition.0 != "elaboration" || disposition.2 != 1 {
                            record_failure(
                                &mut failures,
                                label,
                                format!("semantic elaboration refusal required: {error:?}"),
                            );
                        }
                    }
                    Ok(Outcome::Complete(_)) => {
                        record_failure(&mut failures, label, "false acceptance".into());
                    }
                    Ok(Outcome::Inconclusive(reason)) => record_failure(
                        &mut failures,
                        label,
                        format!("inconclusive instead of refusal: {reason:?}"),
                    ),
                    Ok(Outcome::InternalFault(fault)) => record_failure(
                        &mut failures,
                        label,
                        format!("internal fault instead of refusal: {fault:?}"),
                    ),
                }
                if engine.logical_root(&options) != before {
                    record_failure(
                        &mut failures,
                        label,
                        "refusal mutated input logical root".into(),
                    );
                }
            }
            // The pin closes arithmetic beyond this ground fragment. Refusal must
            // propagate out of try, not turn failure into an acceptance witness.
            let unsupported = "example (a : Nat) : a + 0 = a := by try grind; rfl";
            let label = "unsupported arithmetic propagation";
            eprintln!("grind: native {label}");
            match engine.check_source_files(&[unsupported.as_bytes()], &options, limits()) {
                Err(error) => {
                    if !format!("{error:?}").contains("UnsupportedTactic") {
                        record_failure(&mut failures, label, format!("{error:?}"));
                    }
                }
                Ok(Outcome::Complete(_)) => record_failure(
                    &mut failures,
                    label,
                    "try grind silently skipped an unsupported arithmetic goal".into(),
                ),
                Ok(Outcome::Inconclusive(reason)) => {
                    record_failure(&mut failures, label, format!("inconclusive: {reason:?}"))
                }
                Ok(Outcome::InternalFault(fault)) => {
                    record_failure(&mut failures, label, format!("internal fault: {fault:?}"))
                }
            }
            if engine.logical_root(&options) != before {
                record_failure(&mut failures, label, "input logical root mutated".into());
            }
            assert!(
                failures.is_empty(),
                "grind failed checks: {}",
                failures.join(", ")
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
