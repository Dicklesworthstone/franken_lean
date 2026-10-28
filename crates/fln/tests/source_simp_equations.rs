//! Lazy equation theorems retain ordinary admission evidence at every source door.
#![forbid(unsafe_code)]

use fln::source_check::modules::execution::SourceProgramLimits;
use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
};
use fln::{
    Budget, CheckerAdmissionBudget, DataValue, Declaration, Engine, EngineAdmissionLimits,
    EngineExecutionLimits, KVMap, Name, Outcome, SourceCheckLimits, SourceModuleInput,
};
use fln_elab::source::scope::simp;

fn name(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn checked(base: &Engine, source: &str) -> fln::SourceFileCheck {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .unwrap()
}

#[test]
fn inline_equation_has_its_own_admission_and_can_be_used_as_a_proof() {
    let base = engine();
    let options = KVMap::new();
    let admitted = base
        .admit_source_declaration(
            b"@[simp 700] def wrap.{u} {A : Sort u} (x : A) : A := x",
            &options,
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let [primary, equation] = admitted.admissions.as_slice() else {
        panic!("the definition and its equation require separate council receipts")
    };
    assert!(
        matches!(&primary.declaration, Declaration::Defn(value) if value.base.name == name("wrap"))
    );
    assert!(
        matches!(&equation.declaration, Declaration::Thm(value) if value.base.name == name("wrap.eq_1"))
    );
    assert_eq!(admitted.declaration, primary.declaration);
    assert_eq!(admitted.checker, primary.checker);
    assert_eq!(admitted.base_logical_root, base.logical_root(&options));
    assert_eq!(
        admitted.result_logical_root,
        admitted.engine.logical_root(&options)
    );
    assert_eq!(
        equation.result_logical_root,
        equation.engine.logical_root(&options)
    );
    assert!(!base.environment().contains(&name("wrap.eq_1")));
    let rules = simp::read(admitted.engine.environment()).unwrap();
    assert!(
        rules
            .iter()
            .any(|row| row.declaration == name("wrap.eq_1") && row.priority == 700)
    );
    assert!(rules.iter().any(|row| row.declaration == name("wrap")));
    checked(
        &admitted.engine,
        "theorem explicit.{u} {A : Sort u} (x : A) : wrap x = x := wrap.eq_1 x\n\
         theorem automated (x : Nat) : wrap (wrap x) = x := by simp",
    );
    // The semireducible owner needs backward conversion; the generated proof
    // must not be promoted to the strict rfl theorem extension.
    assert!(
        !simp::defeq::read(admitted.engine.environment(), || Ok(()))
            .unwrap()
            .contains(&name("wrap.eq_1"))
    );
    assert!(
        simp::defeq::read_backward(admitted.engine.environment(), || Ok(()))
            .unwrap()
            .contains(&name("wrap.eq_1"))
    );
}

#[test]
fn delayed_and_repeated_attributes_generate_once_and_erase_the_whole_group() {
    let base = engine();
    assert!(!base.environment().contains(&name("N.wrap.eq_1")));
    let selected = checked(
        &base,
        "namespace N\ndef wrap (n : Nat) : Nat := n\nend N\n\
         open N\nattribute [simp 800] wrap",
    );
    assert_eq!(selected.theorems, 1);
    let repeated = checked(&selected.engine, "attribute [simp 600] N.wrap");
    assert_eq!(
        repeated.theorems, 0,
        "re-registration reuses the actual checked theorem"
    );
    assert!(
        simp::read(repeated.engine.environment())
            .unwrap()
            .iter()
            .filter(|row| row.declaration == name("N.wrap.eq_1"))
            .all(|row| row.priority == 600)
    );
    let erased = checked(&repeated.engine, "attribute [-simp] N.wrap");
    assert!(simp::read(erased.engine.environment()).unwrap().is_empty());
    assert!(erased.engine.environment().contains(&name("N.wrap.eq_1")));
    checked(
        &erased.engine,
        "theorem retained (n : Nat) : N.wrap n = n := N.wrap.eq_1 n",
    );
}

#[test]
fn local_simp_generates_a_checked_equation_without_global_activation() {
    let base = engine();
    let local = checked(
        &base,
        "def wrap (n : Nat) : Nat := n\nsection\nattribute [local simp] wrap\n\
         theorem during (n : Nat) : wrap (wrap n) = n := by simp\nend\n\
         theorem retained (n : Nat) : wrap n = n := wrap.eq_1 n",
    );
    assert_eq!(local.theorems, 3);
    assert!(local.engine.environment().contains(&name("wrap.eq_1")));
    assert!(simp::read(local.engine.environment()).unwrap().is_empty());
    assert!(!base.environment().contains(&name("wrap.eq_1")));
}

#[test]
fn failed_multi_name_registration_and_checker_stops_publish_no_equation() {
    // A nondefault splitting policy freezes provenance across API calls; a
    // split-free body has the same equation with this policy disabled.
    let mut definition_options = KVMap::new();
    definition_options.insert(
        name("backward.eqns.deepRecursiveSplit"),
        DataValue::OfBool(false),
    );
    let base = engine()
        .admit_source_declaration(
            b"def wrap (n : Nat) : Nat := n",
            &definition_options,
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let failed = base.check_source_files(
        &[b"attribute [simp] wrap missing"],
        &options,
        SourceCheckLimits::new(limits()),
    );
    assert!(failed.is_err());
    assert_eq!(base.logical_root(&options), root);
    assert!(!base.environment().contains(&name("wrap.eq_1")));
    assert!(simp::read(base.environment()).unwrap().is_empty());

    // The owner is already admitted. This independent checker veto therefore
    // applies to the lazy generated proof, not the original definition.
    let term = fln_checker::term::TermBudget::new(0, 0).with_max_arena_nodes(0);
    let whnf = fln_checker::whnf::WhnfBudget::new(0, 0, term);
    let inference = fln_checker::infer::InferenceBudget::new(0, 0, term, term).with_whnf(whnf);
    let mut stopped = limits();
    stopped.checker.admission = CheckerAdmissionBudget::new(inference, whnf, inference.defeq);
    let error = base
        .check_source_files(
            &[b"attribute [simp] wrap"],
            &options,
            SourceCheckLimits::new(stopped),
        )
        .expect_err("the equation's independent checker must veto publication");
    assert_eq!(error.disposition().0, "inconclusive");
    assert_eq!(base.logical_root(&options), root);
    assert!(!base.environment().contains(&name("wrap.eq_1")));

    let mut stopped = limits();
    stopped.kernel.steps = 0;
    assert!(matches!(
        base.check_source_files(
            &[b"attribute [simp] wrap"],
            &options,
            SourceCheckLimits::new(stopped),
        ),
        Ok(Outcome::Inconclusive(_))
    ));
    assert_eq!(base.logical_root(&options), root);
    assert!(
        checked(&base, "attribute [simp] wrap")
            .engine
            .environment()
            .contains(&name("wrap.eq_1"))
    );
}

#[test]
fn frozen_options_survive_later_calls_and_untracked_defaults_stay_conservative() {
    let base = engine();
    let mut disabled = KVMap::new();
    disabled.insert(name("backward.eqns.nonrecursive"), DataValue::OfBool(false));
    let unsupported = base
        .admit_source_declaration(b"def frozen (n : Nat) : Nat := n", &disabled, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let selected = checked(&unsupported.engine, "attribute [simp] frozen");
    assert!(!selected.engine.environment().contains(&name("frozen.eq_1")));
    assert_eq!(selected.theorems, 0);
    // Existing source simplification is preserved for the statically
    // unsupported option; artifact export has a separate capability refusal.
    checked(
        &selected.engine,
        "theorem use (n : Nat) : frozen n = n := by simp",
    );

    let supported = checked(&base, "def original (n : Nat) : Nat := n");
    let selected = supported
        .engine
        .check_source_files(
            &[b"attribute [simp] original"],
            &disabled,
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    // An earlier API call's default definition has no portable realization
    // policy. Treating its name as new source ownership would guess provenance.
    assert!(
        !selected
            .engine
            .environment()
            .contains(&name("original.eq_1"))
    );
    assert_eq!(selected.theorems, 0);
}

#[test]
fn an_occupied_equation_name_needs_generated_provenance_even_for_the_same_proof() {
    let mut definition_options = KVMap::new();
    definition_options.insert(
        name("backward.eqns.deepRecursiveSplit"),
        DataValue::OfBool(false),
    );
    let base = engine()
        .admit_source_declaration(
            b"def wrap (n : Nat) : Nat := n",
            &definition_options,
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let generated = checked(&base, "attribute [simp] wrap");
    let Some(fln::ConstantInfo::Thm(theorem)) =
        generated.engine.environment().find(&name("wrap.eq_1"))
    else {
        panic!("a generated equation theorem")
    };
    let occupied = base
        .admit_declaration(Declaration::Thm(theorem.clone()), &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = occupied.logical_root(&KVMap::new());
    let error = occupied
        .check_source_files(
            &[b"attribute [simp] wrap"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .expect_err("a theorem suffix is not equation-generation provenance");
    assert!(!matches!(
        error.disposition().0,
        "resource" | "inconclusive"
    ));
    assert_eq!(occupied.logical_root(&KVMap::new()), root);
    assert!(simp::read(occupied.environment()).unwrap().is_empty());
}

#[test]
fn executable_stream_retains_attribute_equations_as_checked_source_admissions() {
    let base = engine();
    let completed = base
        .execute_source_commands_with_checks(
            b"def answer : Nat := 42\nattribute [simp] answer\n\
              def wrap (n : Nat) : Nat := n\nattribute [simp] wrap",
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    // The two ordinary definitions retain their executable products; their
    // generated theorem proofs belong only to checked source admissions.
    assert_eq!(completed.batch.executions.len(), 2);
    for (command, equation) in [(1, "answer.eq_1"), (3, "wrap.eq_1")] {
        let row = completed
            .batch
            .source_admissions
            .iter()
            .find(|row| row.command_index == command)
            .expect("an attribute's generated declarations must survive artifact collection");
        let [admitted] = row.admission.admissions.as_slice() else {
            panic!("one generated equation")
        };
        assert!(
            matches!(&admitted.declaration, Declaration::Thm(value) if value.base.name == name(equation))
        );
        assert_eq!(
            row.admission.result_logical_root,
            row.admission.engine.logical_root(&KVMap::new())
        );
    }
    checked(
        &completed.batch.engine,
        "theorem answer_correct : answer = 42 := answer.eq_1\n\
         theorem wrap_correct (n : Nat) : wrap n = n := wrap.eq_1 n",
    );
}

#[test]
fn a_public_local_equation_is_exported_and_later_global_registration_reuses_it() {
    let initial = Engine::builder().build_empty();
    let api_name = name("Api");
    let main_name = name("Main");
    let local = "module\nprelude\n\
        public inductive Eq.{u} {A : Sort u} : A -> A -> Prop where | refl (a : A) : Eq a a\n\
        @[expose] public def wrap.{u} {A : Sort u} (x : A) : A := x\n\
        section\nattribute [local simp] wrap\nend\n";
    let main = "prelude\nimport Api\n\
        theorem witness.{u} {A : Sort u} (x : A) : wrap x = x := wrap.eq_1 x";
    let module_limits = SourceModuleCheckLimits::new(SourceCheckLimits::new(limits()));
    for global in [false, true] {
        let api = if global {
            format!("{local}public section\nattribute [simp] wrap\n")
        } else {
            local.to_owned()
        };
        let checked = initial
            .check_source_modules(
                &[
                    SourceModuleInput {
                        name: &api_name,
                        source: api.as_bytes(),
                    },
                    SourceModuleInput {
                        name: &main_name,
                        source: main.as_bytes(),
                    },
                ],
                &main_name,
                &KVMap::new(),
                module_limits,
            )
            .unwrap_or_else(|error| panic!("global={global}: {error:?}"))
            .into_complete()
            .unwrap();
        assert!(
            checked
                .checked
                .engine
                .environment()
                .contains(&name("wrap.eq_1"))
        );
        assert!(
            checked
                .checked
                .engine
                .environment()
                .contains(&name("witness"))
        );
        let rules = simp::read(checked.checked.engine.environment()).unwrap();
        if global {
            assert_eq!(rules.len(), 2);
            assert!(
                rules
                    .iter()
                    .any(|rule| rule.declaration == name("wrap.eq_1"))
            );
        } else {
            assert!(
                rules.is_empty(),
                "local activation must not escape its module scope"
            );
        }
    }
    assert!(initial.environment().is_empty());
}

const PUBLIC_EQUATION_PREFIX: &str = "module\nprelude\n\
    public inductive Eq.{u} {A : Sort u} : A -> A -> Prop where | refl (a : A) : Eq a a\n\
    @[expose] public def wrap.{u} {A : Sort u} (x : A) : A := x\n";

#[test]
fn private_and_hidden_public_proofs_publish_equations_once_before_later_simp() {
    let initial = Engine::builder().build_empty();
    let api_name = name("Api");
    let main_name = name("Main");
    let main = "prelude\nimport Api\n\
        theorem witness.{u} {A : Sort u} (x : A) : wrap x = x := by simp";
    let module_limits = SourceModuleCheckLimits::new(SourceCheckLimits::new(limits()));
    for (visibility, proof) in [
        ("", "wrap.eq_1 x"),
        ("", "by rw [wrap]"),
        ("", "by\n  trace \"equation retained\"\n  exact wrap.eq_1 x"),
        ("public ", "wrap.eq_1 x"),
        ("public ", "by rw [wrap]"),
    ] {
        let api = format!(
            "{PUBLIC_EQUATION_PREFIX}{visibility}theorem first.{{u}} {{A : Sort u}} (x : A) : \
             wrap x = x := {proof}\npublic section\nattribute [simp] wrap\n"
        );
        let modules = [
            SourceModuleInput {
                name: &api_name,
                source: api.as_bytes(),
            },
            SourceModuleInput {
                name: &main_name,
                source: main.as_bytes(),
            },
        ];
        // The plain checking API deliberately refuses a raw trace: it has no
        // observation owner. The command-stream API below retains the trace
        // while checking and publishing the same module declarations.
        let checked = if proof.contains("trace") {
            None
        } else {
            Some(
                initial
                    .check_source_modules(&modules, &main_name, &KVMap::new(), module_limits)
                    .unwrap_or_else(|error| panic!("{api}\n{error:?}"))
                    .into_complete()
                    .unwrap(),
            )
        };
        let executed =
            fln::source_check::modules::imported::SourceOleanImport::empty(&KVMap::new())
                .execute_source_modules(
                    &modules,
                    &main_name,
                    &KVMap::new(),
                    SourceProgramLimits::new(EngineExecutionLimits::new(limits().kernel)),
                    None,
                )
                .unwrap_or_else(|error| panic!("{api}\n{error:?}"))
                .into_complete()
                .unwrap();
        let main = executed
            .modules
            .iter()
            .find(|module| module.module == main_name)
            .unwrap();
        let exported = main.commands.batch.engine.environment();
        assert!(matches!(
            exported.find(&name("wrap.eq_1")),
            Some(fln::ConstantInfo::Thm(_))
        ));
        assert_eq!(exported.contains(&name("first")), !visibility.is_empty());
        if !visibility.is_empty() {
            assert!(matches!(
                exported.find(&name("first")),
                Some(fln::ConstantInfo::Axiom(_))
            ));
        }
        assert_eq!(simp::read(exported).unwrap().len(), 2);
        if let Some(checked) = checked {
            assert_eq!(
                checked.checked.engine.logical_root(&KVMap::new()),
                main.commands.batch.engine.logical_root(&KVMap::new())
            );
        }
        let api = executed
            .modules
            .iter()
            .find(|module| module.module == api_name)
            .unwrap();
        let equation_rows: Vec<_> = api
            .commands
            .batch
            .source_admissions
            .iter()
            .filter(|row| {
                row.admission.admissions.iter().any(|admitted| {
                    matches!(&admitted.declaration, Declaration::Thm(theorem)
                    if theorem.base.name == name("wrap.eq_1"))
                })
            })
            .collect();
        assert_eq!(
            equation_rows.len(),
            1,
            "the first requesting command owns the receipt"
        );
        let [equation, theorem] = equation_rows[0].admission.admissions.as_slice() else {
            panic!("exactly the checked equation and the requesting proof")
        };
        assert!(
            matches!(&equation.declaration, Declaration::Thm(value) if value.base.name == name("wrap.eq_1"))
        );
        assert!(matches!(theorem.declaration, Declaration::Thm(_)));
        if proof.contains("trace") {
            assert_eq!(api.commands.traces.len(), 1);
            assert_eq!(api.commands.traces[0].message, "equation retained");
        }
    }
    assert!(initial.environment().is_empty());
}

#[test]
fn failed_private_or_hidden_public_proof_does_not_publish_staged_equations() {
    let options = KVMap::new();
    let initial = Engine::builder().build_empty();
    let mut session = SourceModuleSession::new(
        initial.clone(),
        options,
        SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        SourceModuleCacheLimits::default(),
    );
    let api_name = name("Api");
    for visibility in ["", "public "] {
        let failed = format!(
            "{PUBLIC_EQUATION_PREFIX}{visibility}theorem bad.{{u}} {{A : Sort u}} (x y : A) : \
             wrap x = y := wrap.eq_1 x\n"
        );
        assert!(
            session
                .check(
                    &[SourceModuleInput {
                        name: &api_name,
                        source: failed.as_bytes(),
                    }],
                    &api_name
                )
                .is_err()
        );
        assert_eq!(session.retained_modules(), 0);
    }
    let recovered = format!(
        "{PUBLIC_EQUATION_PREFIX}theorem first.{{u}} {{A : Sort u}} (x : A) : \
         wrap x = x := wrap.eq_1 x\npublic section\nattribute [simp] wrap\n"
    );
    let files = [SourceModuleInput {
        name: &api_name,
        source: recovered.as_bytes(),
    }];
    let checked = session
        .check(&files, &api_name)
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        checked
            .checked
            .checked
            .engine
            .environment()
            .contains(&name("wrap.eq_1"))
    );
    let reused = session
        .check(&files, &api_name)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(reused.reused_modules, 1);
    assert_eq!(
        checked.checked.checked.result_logical_root,
        reused.checked.checked.result_logical_root
    );
    assert!(initial.environment().is_empty());
}

#[test]
fn an_irreducible_owner_keeps_source_simp_without_a_guessed_rfl_equation() {
    let admitted = engine()
        .admit_source_declaration(
            b"@[irreducible, simp] def wrap (n : Nat) : Nat := n",
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(admitted.admissions.len(), 1);
    assert!(!admitted.engine.environment().contains(&name("wrap.eq_1")));
    assert_eq!(simp::read(admitted.engine.environment()).unwrap().len(), 1);
    checked(
        &admitted.engine,
        "theorem source_use (n : Nat) : wrap n = n := by simp",
    );
}
