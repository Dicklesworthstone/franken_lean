//! Declaration admission and source-module compiler eligibility are distinct.
//! The signature controls target the pinned Reference compiler at
//! 8c9756b28d64dab099da31a4c09229a9e6a2ef35; import and budget tests also
//! verify native authority isolation and resource-error classification.

#![forbid(unsafe_code)]

use fln::source_check::modules::execution::{SourceProgramExecution, SourceProgramLimits};
use fln::source_check::modules::imported::{SourceOleanImport, SourceOleanImportLimits};
use fln::source_check::modules::{SourceModuleCheckError, SourceModuleCheckLimits};
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, EvaluationPresentation, KVMap,
    Name, OleanCheckLimits, OleanModuleInput, OleanWriteBudget, Outcome, SourceCheckLimits,
    SourceModuleInput,
};

const POLY: &str = "universe u\ndef ident (A : Type u) (x : A) : A := x\n";
const ENUM: &str = "inductive E where\n | a\n | b\n";
const MARKERS: &str = "axiom lcAny : Type\naxiom lcErased : Type\n";

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn run(
    source: &str,
    limits: EngineExecutionLimits,
) -> Result<Outcome<SourceProgramExecution>, SourceModuleCheckError> {
    let entry = name("Main");
    SourceOleanImport::empty(&KVMap::new()).execute_lean_source_modules_with_presentation(
        &[SourceModuleInput {
            name: &entry,
            source: source.as_bytes(),
        }],
        &entry,
        &KVMap::new(),
        SourceProgramLimits::new(limits),
        None,
        EvaluationPresentation::Lean,
    )
}

fn accepted(source: &str) {
    let result = run(source, limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap_or_else(|reason| panic!("{source}\n{reason:?}"));
    assert_eq!(result.modules.len(), 1);
    assert!(result.modules[0].commands.batch.executions.is_empty());
}

fn missing(source: &str, marker: &str) {
    let error = run(source, limits()).expect_err("missing compiler prerequisite must fail");
    assert_eq!(error.disposition(), ("compilation", false, 1), "{error:?}");
    assert!(
        error
            .to_string()
            .contains(&format!("Unknown constant `{marker}`")),
        "{source}\n{error:?}",
    );
}

#[test]
fn executable_polymorphism_requires_each_actual_marker() {
    missing(&format!("prelude\n{POLY}"), "lcAny");
    missing(&format!("prelude\naxiom lcAny : Type\n{POLY}"), "lcErased");
    missing(&format!("prelude\naxiom lcErased : Type\n{POLY}"), "lcAny");
    accepted(&format!("prelude\n{MARKERS}{POLY}"));
    missing(
        &format!("prelude\n{ENUM}def f (A : Type) : E := E.a\n"),
        "lcErased",
    );
    missing(
        &format!("prelude\n{ENUM}axiom A : Type\ndef f (a : A) : E := E.a\n"),
        "lcAny",
    );
}

#[test]
fn noncomputable_sections_record_only_actual_compiler_failures() {
    for (header, declaration) in [
        ("prelude\n", "def ident"),
        ("module\nprelude\n", "public def ident"),
    ] {
        let source = format!(
            "{header}universe u\nnoncomputable section\n{declaration} (A : Type u) (x : A) : A := x\nend\n",
        );
        let completed = run(&source, limits()).unwrap().into_complete().unwrap();
        let engine = &completed.modules[0].commands.batch.engine;
        assert!(
            fln_elab::noncomputable::read(engine.environment())
                .unwrap()
                .contains(&name("ident")),
            "{source}",
        );
    }
    for source in [
        format!("prelude\n{MARKERS}noncomputable section\n{POLY}end\n"),
        format!("prelude\n{ENUM}noncomputable section\ndef ident (e : E) : E := e\nend\n"),
    ] {
        let completed = run(&source, limits()).unwrap().into_complete().unwrap();
        assert!(
            !fln_elab::noncomputable::read(
                completed.modules[0].commands.batch.engine.environment()
            )
            .unwrap()
            .contains(&name("ident")),
            "{source}",
        );
    }
    let use_outside =
        format!("prelude\n{ENUM}noncomputable section\n{POLY}end\ndef value : E := ident E E.a\n",);
    let error = run(&use_outside, limits()).expect_err("the retained tag blocks later codegen");
    assert_eq!(error.disposition().2, 1, "{error:?}");
    assert!(error.to_string().contains("noncomputable"), "{error:?}");

    let mut constrained = limits();
    constrained.ingress.max_nodes = 0;
    let source = format!("prelude\nnoncomputable section\n{POLY}end\n");
    let error = run(&source, constrained).expect_err("section cannot suppress resource exhaustion");
    assert_eq!(error.disposition(), ("resource", false, 3), "{error:?}");
}

#[test]
fn public_section_compiler_effects_replay_into_importing_modules() {
    let receipt = SourceOleanImport::empty(&KVMap::new());
    let library = name("Library");
    let main = name("Main");
    let library_source = b"module\nprelude\nuniverse u\nnoncomputable section\npublic def ident (A : Type u) (x : A) : A := x\nend\n";
    let outcome = receipt
        .execute_lean_source_modules_with_presentation(
            &[
                SourceModuleInput {
                    name: &library,
                    source: library_source,
                },
                SourceModuleInput {
                    name: &main,
                    source: b"prelude\nimport Library\n",
                },
            ],
            &main,
            &KVMap::new(),
            SourceProgramLimits::new(limits()),
            None,
            EvaluationPresentation::Lean,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    for module in &outcome.modules {
        let environment = module.commands.batch.engine.environment();
        assert!(environment.contains(&name("ident")), "{module:?}");
        assert!(
            fln_elab::noncomputable::read(environment)
                .unwrap()
                .contains(&name("ident")),
            "{module:?}",
        );
    }
}

#[test]
fn only_extern_axioms_request_compilation_of_their_signature() {
    let external = "universe u\n@[extern \"poly_ext\"] axiom ext (A : Type u) (x : A) : A\n";
    missing(&format!("prelude\n{external}"), "lcErased");
    accepted(&format!("prelude\n{MARKERS}{external}"));
    accepted("prelude\nuniverse u\naxiom ext (A : Type u) (x : A) : A\n");
}

#[test]
fn proof_typeformer_and_ignored_polymorphic_parameters_require_erasure() {
    for declaration in [
        "axiom P : Prop\ndef f (p : P) : E := E.a\n",
        "def f (g : E → Type) : E := E.a\n",
        "universe u\ndef f (A : Type u) (x : A) : E := E.a\n",
    ] {
        missing(&format!("prelude\n{ENUM}{declaration}"), "lcErased");
    }
}

#[test]
fn only_generated_recursor_metadata_exempts_auxiliary_wrappers() {
    accepted(&format!("prelude\n{ENUM}#check E.recOn\n"));
    missing(
        "prelude\nuniverse u\nnamespace User\ndef recOn (A : Type u) (x : A) : A := x\nend User\n",
        "lcAny",
    );
}

#[test]
fn proofs_noncomputable_and_concrete_entries_remain_admissible() {
    for source in [
        "prelude\nuniverse u\nnoncomputable def ident (A : Type u) (x : A) : A := x\n".to_owned(),
        "prelude\ntheorem ident (P : Prop) (x : P) : P := x\n".to_owned(),
        "prelude\ndef ident (A : Type) : Type := A\n".to_owned(),
        format!("prelude\n{ENUM}def ident (e : E) : E := e\n"),
        format!("prelude\n{ENUM}def value : E := E.a\n"),
    ] {
        accepted(&source);
    }
}

#[test]
fn closure_parameters_and_eliminated_body_binders_do_not_require_markers() {
    accepted(&format!(
        "prelude\n{ENUM}axiom A : Type\ndef f (g : E → A) (e : E) : E := e\n"
    ));
    accepted(&format!(
        "prelude\n{ENUM}def f : E := (fun (A : Type) (x : A) => E.a) E E.a\n"
    ));
}

#[test]
fn compiler_type_aliases_preserve_concrete_carriers_and_erased_parameters() {
    for declaration in [
        "@[irreducible] def Data : Type := E\ndef ident (x : Data) : Data := x\n",
        "unsafe def Data : Type := E\nunsafe def ident (x : Data) : Data := x\n",
        "unsafe def Callback : Type := E → E\nunsafe def ignore (f : Callback) : E := E.a\n",
        "unsafe def Callback : Type := E → E\nunsafe def ident (f : Callback) : Callback := f\n",
        "universe u\nunsafe def Carrier (A : Type u) : Type u := A\nunsafe def ident (x : Carrier E) : Carrier E := x\n",
        "axiom Q : Prop\nunsafe def P : Prop := Q\nunsafe def ident (p : P) : P := p\n",
        "axiom Q : Prop\nunsafe def Predicate : E → Prop := fun _ => Q\nunsafe def ident (e : E) (p : Predicate e) : Predicate e := p\n",
    ] {
        accepted(&format!("prelude\n{ENUM}{declaration}"));
    }

    let predicate =
        "unsafe def Predicate : Type 1 := E → Type\nunsafe def ignore (p : Predicate) : E := E.a\n";
    missing(&format!("prelude\n{ENUM}{predicate}"), "lcErased");
    accepted(&format!(
        "prelude\n{ENUM}axiom lcErased : Type\n{predicate}"
    ));

    let abstract_alias =
        "axiom A : Type\nunsafe def Data : Type := A\nunsafe def ident (x : Data) : Data := x\n";
    missing(&format!("prelude\n{ENUM}{abstract_alias}"), "lcAny");
    accepted(&format!(
        "prelude\n{ENUM}axiom lcAny : Type\n{abstract_alias}"
    ));
    missing(
        &format!("prelude\n{ENUM}opaque Data : Type := E\ndef ident (x : Data) : Data := x\n"),
        "lcAny",
    );
}

#[test]
fn macro_inline_bodies_are_checked_when_a_runtime_caller_uses_them() {
    let base = format!("prelude\n{ENUM}axiom value : E\n");
    for declaration in [
        "@[macro_inline] def f : E := value\n",
        "@[noinline, macro_inline] def f : E := value\n",
        "@[macro_inline] def discard (_ : E) : E := E.a\ndef use : E := discard value\n",
    ] {
        accepted(&format!("{base}{declaration}"));
    }
    for declaration in [
        "def f : E := value\n",
        "@[macro_inline] def f : E := value\ndef g : E := f\n",
        "@[macro_inline, noinline] def f : E := value\n",
        "@[macro_inline] def keep (x : E) : E := x\ndef use : E := keep value\n",
    ] {
        let source = format!("{base}{declaration}");
        let error = run(&source, limits()).expect_err("a runtime entry cannot use the axiom");
        assert_eq!(error.disposition().2, 1, "{error:?}");
        assert!(
            error.to_string().contains("noncomputable"),
            "{source}\n{error:?}"
        );
        assert!(error.to_string().contains("value"), "{source}\n{error:?}");
    }
}

#[test]
fn macro_inline_recursors_follow_surviving_runtime_terms() {
    let base = "prelude\ninductive N where | zero | succ (n : N)\n";
    let recursor = "N.rec (motive := fun _ => N) N.zero (fun _ ih => ih) n";
    let fold = format!("@[macro_inline] def fold (n : N) : N := {recursor}\n");
    for declaration in [
        fold.clone(),
        format!(
            "{fold}@[macro_inline] def discard (_ : N) : N := N.zero\ndef use (n : N) : N := discard (fold n)\n"
        ),
        format!(
            "@[macro_inline] def discard (_ : N) : N := N.zero\n@[macro_inline] def fold (n : N) : N := discard ({recursor})\ndef use (n : N) : N := fold n\n"
        ),
        format!("{fold}def Proof (n : N) : Prop := (P : N → Prop) → P (fold n) → P (fold n)\n"),
    ] {
        accepted(&format!("{base}{declaration}"));
    }
    for (declaration, diagnostic) in [
        (
            format!("{fold}def use (n : N) : N := fold n\n"),
            "does not support recursor",
        ),
        (
            format!(
                "@[macro_inline] def keep (x : N) : N := x\n@[macro_inline] def fold (n : N) : N := keep ({recursor})\ndef use (n : N) : N := fold n\n"
            ),
            "does not support recursor",
        ),
        (
            "@[macro_inline] def fold (n : N) : N := N.recOn (motive := fun _ => N) n N.zero (fun _ ih => ih)\ndef use (n : N) : N := fold n\n".to_owned(),
            "Failed to find LCNF signature",
        ),
    ] {
        let source = format!("{base}{declaration}");
        let error = run(&source, limits()).expect_err("the surviving recursor has no native entry");
        assert_eq!(error.disposition().2, 1, "{error:?}");
        assert!(error.to_string().contains(diagnostic), "{source}\n{error:?}");
        assert!(error.to_string().contains("N.rec"), "{source}\n{error:?}");
    }
}

#[test]
fn method_eliminators_preserve_the_direct_recursors_compiler_boundary() {
    let base = "prelude\ninductive UserChain where | nil | more (tail : UserChain)\n";
    for application in [
        "UserChain.rec UserChain.nil (fun _ ih => ih) x",
        "x.rec UserChain.nil (fun _ ih => ih)",
        "x.rec (nil := UserChain.nil) (more := fun _ ih => ih)",
    ] {
        let source = format!("{base}def keep (x : UserChain) : UserChain := {application}\n");
        let error =
            run(&source, limits()).expect_err("method notation cannot hide an explicit recursor");
        assert_eq!(error.disposition().2, 1, "{source}\n{error:?}");
        assert!(
            error.to_string().contains("does not support recursor"),
            "{source}\n{error:?}"
        );
        assert!(
            error.to_string().contains("UserChain.rec"),
            "{source}\n{error:?}"
        );
        accepted(&format!(
            "{base}noncomputable def keep (x : UserChain) : UserChain := {application}\n"
        ));
    }
}

#[test]
fn macro_inline_source_recursors_retain_provenance_across_module_imports() {
    let library = name("Library");
    let main = name("Main");
    let result = SourceOleanImport::empty(&KVMap::new())
        .execute_lean_source_modules_with_presentation(
            &[
                SourceModuleInput {
                    name: &library,
                    source: b"prelude\ninductive N where | zero | succ (n : N)\n@[macro_inline] def fold (n : N) : N := N.rec (motive := fun _ => N) N.zero (fun _ ih => ih) n\n",
                },
                SourceModuleInput {
                    name: &main,
                    source: b"prelude\nimport Library\ndef use (n : N) : N := fold n\n",
                },
            ],
            &main,
            &KVMap::new(),
            SourceProgramLimits::new(limits()),
            None,
            EvaluationPresentation::Lean,
        );
    let error = result.expect_err("an imported macro cannot hide its explicit recursor");
    assert_eq!(error.disposition().2, 1, "{error:?}");
    assert!(
        error.to_string().contains("does not support recursor"),
        "{error:?}",
    );
    assert!(error.to_string().contains("N.rec"), "{error:?}");
    assert!(error.to_string().contains("Main"), "{error:?}");
}

#[test]
fn macro_inline_recursors_survive_physical_olean_import_into_a_fresh_engine() {
    let library = name("Library");
    let main = name("Main");
    let source = b"prelude\ninductive N where | zero | succ (n : N)\n@[macro_inline] def fold (n : N) : N := N.rec (motive := fun _ => N) N.zero (fun _ ih => ih) n\n";
    let artifacts = Engine::builder()
        .build_empty()
        .compile_source_modules(
            &[SourceModuleInput {
                name: &library,
                source,
            }],
            &library,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
                limits().kernel,
            ))),
            OleanWriteBudget::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .artifacts;
    let inputs: Vec<_> = artifacts
        .iter()
        .map(|artifact| OleanModuleInput {
            name: &artifact.name,
            artifact: &artifact.bytes,
            server_artifact: artifact
                .companions
                .as_ref()
                .map(|parts| parts.server.as_slice()),
            private_artifact: artifact
                .companions
                .as_ref()
                .map(|parts| parts.private.as_slice()),
        })
        .collect();
    // The producer engine has been dropped. Only physical module bytes cross
    // this boundary, including the macro tag and the expression's provenance.
    let imported = Engine::builder()
        .build_empty()
        .import_olean_modules_for_source(
            &inputs,
            std::slice::from_ref(&library),
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(4 * 1024 * 1024, limits().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    for (source, rejects) in [
        (
            "prelude\nimport Library\ndef use (n : N) : N := fold n\n",
            true,
        ),
        (
            "prelude\nimport Library\ndef Proof (n : N) : Prop := (P : N → Prop) → P (fold n) → P (fold n)\n",
            false,
        ),
    ] {
        let result = imported.execute_lean_source_modules_with_presentation(
            &[SourceModuleInput {
                name: &main,
                source: source.as_bytes(),
            }],
            &main,
            &KVMap::new(),
            SourceProgramLimits::new(limits()),
            None,
            EvaluationPresentation::Lean,
        );
        if rejects {
            let error =
                result.expect_err("physical import cannot lose explicit recursor provenance");
            assert_eq!(error.disposition().2, 1, "{error:?}");
            assert!(
                error.to_string().contains("does not support recursor"),
                "{error:?}"
            );
            assert!(error.to_string().contains("N.rec"), "{error:?}");
        } else {
            result.unwrap().into_complete().unwrap();
        }
    }
}

#[test]
fn public_module_declarations_observe_the_same_compiler_boundary() {
    missing(
        "module\nprelude\nuniverse u\npublic def ident (A : Type u) (x : A) : A := x\n",
        "lcAny",
    );
}

#[test]
fn logical_checking_and_raw_command_apis_do_not_gain_a_codegen_requirement() {
    let base = Engine::builder().build_empty();
    let checked = base
        .check_source_files(
            &[POLY.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(checked.engine.environment().contains(&name("ident")));
    assert!(!base.environment().contains(&name("ident")));
    let executed = base
        .execute_source_commands_with_presentation(
            POLY.as_bytes(),
            &KVMap::new(),
            limits(),
            EvaluationPresentation::Lean,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(executed.batch.engine.environment().contains(&name("ident")));
    assert!(executed.batch.executions.is_empty());
}

#[test]
fn admitted_marker_imports_are_isolated_from_sibling_modules_and_failed_retries() {
    let receipt = SourceOleanImport::empty(&KVMap::new());
    let markers = name("Markers");
    let consumer = name("Consumer");
    let main = name("Main");
    let marker_source = format!("prelude\n{MARKERS}");
    let entry = b"prelude\nimport Markers\nimport Consumer\n";
    for imports_markers in [false, true, false] {
        let consumer_source = format!(
            "prelude\n{}{POLY}",
            if imports_markers {
                "import Markers\n"
            } else {
                ""
            },
        );
        let outcome = receipt.execute_lean_source_modules_with_presentation(
            &[
                SourceModuleInput {
                    name: &markers,
                    source: marker_source.as_bytes(),
                },
                SourceModuleInput {
                    name: &consumer,
                    source: consumer_source.as_bytes(),
                },
                SourceModuleInput {
                    name: &main,
                    source: entry,
                },
            ],
            &main,
            &KVMap::new(),
            SourceProgramLimits::new(limits()),
            None,
            EvaluationPresentation::Lean,
        );
        if imports_markers {
            let completed = outcome.unwrap().into_complete().unwrap();
            let environment = completed
                .modules
                .last()
                .unwrap()
                .commands
                .batch
                .engine
                .environment();
            assert!(environment.contains(&name("ident")));
            assert!(environment.contains(&name("lcAny")));
            assert!(environment.contains(&name("lcErased")));
        } else {
            let error = outcome.expect_err("a sibling's markers are not imported");
            assert_eq!(error.disposition(), ("compilation", false, 1), "{error:?}");
            assert!(error.to_string().contains("lcAny"), "{error:?}");
            assert!(error.to_string().contains("Consumer"), "{error:?}");
        }
        assert!(!receipt.engine.environment().contains(&name("ident")));
        assert!(!receipt.engine.environment().contains(&name("lcAny")));
    }
}

#[test]
fn resource_exhaustion_during_signature_analysis_is_a_nonanswer() {
    let mut constrained = limits();
    constrained.ingress.max_nodes = 0;
    let source = format!("prelude\n{POLY}");
    let error = run(&source, constrained).expect_err("analysis has no work budget");
    assert_eq!(error.disposition(), ("resource", false, 3), "{error:?}");
    assert!(!error.to_string().contains("Unknown constant"), "{error:?}");
    missing(&source, "lcAny");
    accepted(&format!("prelude\n{MARKERS}{POLY}"));
}

#[test]
fn inductive_constructor_fields_and_trivial_structure_unboxing_require_markers() {
    // Concrete/nullary/arrow constructor fields need neither marker.
    for source in [
        "prelude\ninductive Empty : Type\n",
        "prelude\ninductive True : Prop | intro\n",
        "prelude\nuniverse u\ninductive Phantom (A : Type u) | mk\n",
        "prelude\nuniverse u\ninductive MyEq {α : Sort u} (a : α) : α → Prop | refl : MyEq a a\n",
        "prelude\ninductive E | a\ninductive Wrap | mk (e : E)\n",
        "prelude\ninductive E | a\ninductive Fn | mk (f : E → E)\n",
        "prelude\nuniverse u\ninductive PolyFn (A : Type u) | mk (f : A → A)\n",
        "prelude\nuniverse u\naxiom lcAny : Type\ninductive Box (A : Type u) | mk (val : A)\n",
        "prelude\nuniverse u\naxiom lcAny : Type\nstructure Box (A : Type u) where val : A\n",
        "prelude\nuniverse u\naxiom lcAny : Type\nstructure Pair (A : Type u) (B : Type u) where\n  fst : A\n  snd : B\n",
        "prelude\nuniverse u\naxiom lcAny : Type\nstructure A (T : Type u) where x : T\nstructure B (T : Type u) extends A T where y : T\n",
    ] {
        accepted(source);
    }

    // Polymorphic constructor fields require `lcAny`, even for `Prop` inductives
    // and inside `noncomputable section` (`compileInductives` runs unconditionally).
    for source in [
        "prelude\nuniverse u\ninductive Box (A : Type u) | mk (val : A)\n",
        "prelude\nuniverse u\ninductive BoxP (A : Type u) : Prop | mk (val : A)\n",
        "prelude\nuniverse u\nnoncomputable section\ninductive Box (A : Type u) | mk (val : A)\nend\n",
        "prelude\nuniverse u\nstructure Box (A : Type u) where val : A\n",
        "prelude\nuniverse u\nnoncomputable section\nstructure Box (A : Type u) where val : A\nend\n",
        "prelude\nuniverse u\ninductive Exists {α : Sort u} (p : α → Prop) : Prop | intro (w : α) (h : p w)\n",
        "prelude\nuniverse u\nmutual\ninductive A (T : Type u) | mk (b : B T)\ninductive B (T : Type u) | mk (x : T)\nend\n",
    ] {
        missing(source, "lcAny");
    }

    // Erased constructor fields (`Prop` / `Type`), trivial-structure unboxing
    // (`Wrap Type`), and copied diamond parent projections require `lcErased`.
    for source in [
        "prelude\ninductive P : Prop | intro\ninductive Hold | mk (h : P)\n",
        "prelude\ninductive Hold | mk (A : Type)\n",
        "prelude\ninductive Hold (P : Prop) | mk (h : P)\n",
        "prelude\ninductive E | a\ninductive Dep (P : E → Prop) | mk (h : (e : E) → P e)\n",
        "prelude\nuniverse u\ninductive Exist | mk (A : Type u) (x : A)\n",
        "prelude\nuniverse u\naxiom lcAny : Type\ninductive Exists {α : Sort u} (p : α → Prop) : Prop | intro (w : α) (h : p w)\n",
        "prelude\naxiom lcAny : Type\ninductive Wrap (A : Type 1) | mk (x : A)\ninductive Hold | mk (w : Wrap Type)\n",
        "prelude\naxiom lcAny : Type\ninductive E | a\ninductive Wrap (A : Type 1) | mk (x : A)\ndef f (w : Wrap Type) : E := E.a\n",
        "prelude\nuniverse u\naxiom lcAny : Type\nstructure A (T : Type u) where x : T\nstructure B (T : Type u) extends A T where y : T\nstructure C (T : Type u) extends A T where z : T\nstructure D (T : Type u) extends B T, C T where w : T\n",
    ] {
        missing(source, "lcErased");
    }
}
