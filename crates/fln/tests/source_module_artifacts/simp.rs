//! Real source libraries retain simp behavior through physical `.olean` imports.
#![forbid(unsafe_code)]
use super::*;
use fln_elab::source::scope::simp;
use fln_olean::source_extensions::{DiscrTreeKey, SimpKind};

// Match Init.Prelude's index promotion: the constructor's explicit `a` becomes
// a fixed parameter while keeping Eq.refl's independently checked binder style.
const EQUALITY: &str = "inductive Eq.{u} {A : Sort u} : A -> A -> Prop where | refl (a : A) : Eq a a\n\
    def rfl.{u} {A : Sort u} {a : A} : Eq a a := @Eq.refl A a\n";
const WRAP: &str = "prelude\n\
    inductive Eq.{u} {A : Sort u} : A -> A -> Prop where | refl (a : A) : Eq a a\n\
    def wrap.{u} {A : Sort u} (x : A) : A := x\n\
    attribute [reducible] wrap\n\
    attribute [simp] wrap";

fn accepted(engine: &Engine, source: &str) {
    engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits().source)
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_complete()
        .unwrap();
}

fn refused(engine: &Engine, source: &str) {
    let before = engine.logical_root(&KVMap::new());
    let error = engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits().source)
        .expect_err("an unavailable or false simplification must be refused");
    assert!(
        !matches!(
            error.disposition().0,
            "resource" | "inconclusive" | "internal-fault"
        ),
        "expected a semantic refusal: {error:?}"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn registered_definition_unfolding_survives_physical_import() {
    let built = compiled(&[("Main", WRAP)]);
    let rows = metadata(&built.artifacts[0].bytes).simps;
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].scope, None);
    assert_eq!(rows[0].kind, SimpKind::Unfold(name("wrap")));
    let imported = imported(&built);
    assert_eq!(imported.modules[0].simps, 1);
    assert_eq!(imported.modules[0].activated_simps, 1);
    assert_eq!(imported.modules[0].deferred_simps, 0);
    let rules = simp::read(imported.engine.environment()).unwrap();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].declaration, name("wrap"));
    assert!(rules[0].proof.is_none());
    let use_rule = "theorem use (P : Prop) (h : P) : wrap (wrap P) := by simpa using h";
    accepted(&imported.engine, use_rule);
    refused(
        &imported.engine,
        "theorem falseGoal (P Q : Prop) (h : P) : wrap Q := by simpa using h",
    );

    // A reducible definition also unfolds during conversion, so this control
    // checks metadata absence. Equality-rule tests below prove that actual
    // downstream tactic success depends on a retained theorem registration.
    let unmarked = WRAP.replace("attribute [simp] wrap", "");
    let without_rule = super::imported(&compiled(&[("Main", &unmarked)]));
    assert!(
        simp::read(without_rule.engine.environment())
            .unwrap()
            .is_empty()
    );
}

#[test]
fn inline_reducibility_precedes_simp_regardless_of_attribute_order() {
    for attributes in ["reducible, simp", "simp, reducible"] {
        let source = format!(
            "prelude\n{EQUALITY}\
             @[{attributes}] def wrap.{{u}} {{A : Sort u}} (x : A) : A := x"
        );
        let built = compiled(&[("Main", &source)]);
        let rows = metadata(&built.artifacts[0].bytes).simps;
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].kind, SimpKind::Unfold(name("wrap")));
        let receipt = imported(&built);
        assert_eq!(receipt.modules[0].activated_simps, 1);
        accepted(
            &receipt.engine,
            "theorem use.{u} {A : Sort u} (x : A) : wrap (wrap x) = x := by simp",
        );
    }
}

#[test]
fn ordinary_simp_definitions_wait_for_checked_equation_theorem_export() {
    let initial = Engine::builder().build_empty();
    let body = "@[simp] def wrap.{u} {A : Sort u} (x : A) : A := x";
    accepted(&initial, body);
    let source = format!("prelude\n{body}");
    let error = build(&initial, &[("Main", &source)], OleanWriteBudget::default()).unwrap_err();
    assert!(matches!(error,
        SourceModuleBuildError::Check(SourceModuleCheckError::Extension { extension, .. })
            if extension == simp::export::journal_name()));
    assert!(initial.environment().is_empty());
}

#[test]
fn beta_headed_proofs_keep_theorem_encoding_and_reflexivity_flags() {
    for (kind, proof, reflexive) in [
        ("def", "rfl", true),
        ("def", "by rfl", false),
        ("theorem", "rfl", true),
        ("theorem", "by rfl", false),
    ] {
        let source = format!(
            "prelude\n{EQUALITY}\
             def wrap.{{u}} {{A : Sort u}} (x : A) : A := x\n\
             @[simp] {kind} unwrap.{{u}} {{A : Sort u}} (x : A) : (fun P : Prop => P) (wrap x = x) := {proof}"
        );
        let built = compiled(&[("Main", &source)]);
        let rows = metadata(&built.artifacts[0].bytes).simps;
        let [row] = rows.as_slice() else {
            panic!("one proof registration")
        };
        let SimpKind::Theorem(theorem) = &row.kind else {
            panic!("a beta-headed proposition must never select definition unfolding")
        };
        assert_eq!(theorem.proof, fln::Expr::const_(name("unwrap"), vec![]));
        assert_eq!(theorem.reflexive, reflexive, "{kind} := {proof}");
        assert_eq!(theorem.backward_reflexive, reflexive, "{kind} := {proof}");
        assert_eq!(
            theorem.keys,
            [
                DiscrTreeKey::Const(name("wrap"), 2),
                DiscrTreeKey::Star,
                DiscrTreeKey::Star
            ]
        );
    }
}

#[test]
fn reducible_argument_indexing_preserves_delta_beta_binder_order() {
    let source = format!(
        "prelude\n{EQUALITY}\
         inductive Nat where | zero | succ (n : Nat)\n\
         def choose (x y : Nat) : Nat := x\n\
         attribute [reducible] choose\n\
         def f (x : Nat) : Nat := x\n\
         @[simp] theorem choose_rule : f (choose Nat.zero (Nat.succ Nat.zero)) = f Nat.zero := by rfl"
    );
    let built = compiled(&[("Main", &source)]);
    let rows = metadata(&built.artifacts[0].bytes).simps;
    let [row] = rows.as_slice() else {
        panic!("one indexed theorem")
    };
    let SimpKind::Theorem(theorem) = &row.kind else {
        panic!("a checked equality proof")
    };
    assert_eq!(
        theorem.keys,
        [
            DiscrTreeKey::Const(name("f"), 1),
            DiscrTreeKey::Lit(fln::Literal::Nat(fln::NatLit::from_u64(0))),
        ]
    );
}

#[test]
fn equality_rules_keep_exact_keys_priorities_and_reflexivity_flags() {
    for (proof, reflexive) in [("rfl", true), ("by rfl", false)] {
        let declarations = format!(
            "prelude\n{EQUALITY}\
             def wrap.{{u}} {{A : Sort u}} (x : A) : A := x\n\
             @[simp 1200] theorem unwrap.{{u}} {{A : Sort u}} (x : A) : wrap x = x := {proof}\n\
             attribute [irreducible] wrap"
        );
        let built = compiled(&[("Main", &declarations)]);
        let rows = metadata(&built.artifacts[0].bytes).simps;
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].scope, None);
        let SimpKind::Theorem(theorem) = &rows[0].kind else {
            panic!("an equality theorem must retain its checked proof")
        };
        assert_eq!(theorem.origin, name("unwrap"));
        assert_eq!(theorem.proof, fln::Expr::const_(name("unwrap"), vec![]));
        assert!(theorem.level_params.is_empty());
        assert_eq!(theorem.priority, 1200);
        assert!(theorem.post);
        assert!(!theorem.origin_reverse);
        assert!(!theorem.permutation);
        assert_eq!(theorem.reflexive, reflexive);
        assert_eq!(theorem.backward_reflexive, reflexive);
        assert_eq!(
            theorem.keys,
            [
                DiscrTreeKey::Const(name("wrap"), 2),
                DiscrTreeKey::Star,
                DiscrTreeKey::Star,
            ]
        );
        let receipt = imported(&built);
        assert_eq!(receipt.modules[0].activated_simps, 1);
        assert_eq!(receipt.modules[0].deferred_simps, 0);
        let rules = simp::read(receipt.engine.environment()).unwrap();
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].declaration, name("unwrap"));
        assert_eq!(rules[0].proof, Some(name("unwrap")));
        assert_eq!(rules[0].priority, 1200);
        let use_rule = "theorem use.{u} {A : Sort u} (x : A) : wrap (wrap x) = x := by simp";
        accepted(&receipt.engine, use_rule);
        refused(
            &receipt.engine,
            "theorem falseGoal.{u} {A : Sort u} (x y : A) : wrap x = y := by simp",
        );
        let unmarked = declarations.replace("@[simp 1200] ", "");
        let unmarked = compiled(&[("Main", &unmarked)]);
        assert!(metadata(&unmarked.artifacts[0].bytes).simps.is_empty());
        let without_rule = imported(&unmarked);
        refused(&without_rule.engine, use_rule);
    }
}

#[test]
fn a_false_simp_theorem_never_reaches_an_artifact() {
    let initial = Engine::builder().build_empty();
    let source = format!(
        "prelude\n{EQUALITY}\
         @[simp] theorem falseRule.{{u}} {{A : Sort u}} (x y : A) : x = y := by rfl"
    );
    let error = build(&initial, &[("Main", &source)], OleanWriteBudget::default()).unwrap_err();
    assert!(
        matches!(&error, SourceModuleBuildError::Check(_)),
        "{error:?}"
    );
    assert!(!matches!(
        error.disposition().0,
        "resource" | "inconclusive" | "internal-fault"
    ));
    assert!(initial.environment().is_empty());
    assert!(simp::read(initial.environment()).unwrap().is_empty());
}

#[test]
fn physical_entries_keep_the_registration_snapshot_across_later_reducibility_changes() {
    let source = format!(
        "prelude\n{EQUALITY}\
         def hidden.{{u}} {{A : Sort u}} (x : A) : A := x\n\
         def outer.{{u}} {{A : Sort u}} (x : A) : A := x\n\
         @[simp 700] theorem unwrap.{{u}} {{A : Sort u}} (x : A) : outer (hidden x) = x := by rfl\n\
         attribute [reducible] hidden\n\
         attribute [irreducible] outer"
    );
    for repeat in [false, true] {
        let source = format!(
            "{source}{}",
            if repeat {
                "\nattribute [simp 700] unwrap"
            } else {
                ""
            }
        );
        let built = compiled(&[("Main", &source)]);
        let rows = metadata(&built.artifacts[0].bytes).simps;
        assert_eq!(rows.len(), if repeat { 2 } else { 1 });
        let SimpKind::Theorem(first) = &rows[0].kind else {
            panic!("initial equality")
        };
        assert_eq!(
            first.keys,
            [
                DiscrTreeKey::Const(name("outer"), 2),
                DiscrTreeKey::Star,
                DiscrTreeKey::Const(name("hidden"), 2),
                DiscrTreeKey::Star,
                DiscrTreeKey::Star
            ]
        );
        if repeat {
            let SimpKind::Theorem(second) = &rows[1].kind else {
                panic!("refreshed equality")
            };
            assert_eq!(
                second.keys,
                [
                    DiscrTreeKey::Const(name("outer"), 2),
                    DiscrTreeKey::Star,
                    DiscrTreeKey::Star,
                ]
            );
            assert_eq!(second.priority, 700);
        }
        let receipt = imported(&built);
        assert_eq!(receipt.modules[0].activated_simps, rows.len());
        if repeat {
            accepted(
                &receipt.engine,
                "theorem use.{u} {A : Sort u} (x : A) : outer (hidden x) = x := by simp",
            );
        }
    }
}

#[test]
fn diamond_artifacts_export_only_the_modules_own_simp_additions() {
    let built = compiled(&[
        ("Base", WRAP),
        (
            "Left",
            "prelude\nimport Base\ndef left.{u} {A : Sort u} (x : A) : A := wrap x\nattribute [reducible] left\nattribute [simp] left",
        ),
        ("Right", "prelude\nimport Base"),
        ("Main", "prelude\nimport Left\nimport Right"),
    ]);
    assert_eq!(
        built
            .artifacts
            .iter()
            .map(|artifact| (artifact.name.clone(), metadata(&artifact.bytes).simps.len()))
            .collect::<Vec<_>>(),
        [
            (name("Base"), 1),
            (name("Left"), 1),
            (name("Right"), 0),
            (name("Main"), 0)
        ]
    );
    let receipt = imported(&built);
    assert_eq!(
        receipt
            .modules
            .iter()
            .map(|module| module.simps)
            .sum::<usize>(),
        2
    );
    receipt
        .engine
        .check_source_files(
            &[b"theorem useDiamond (P : Prop) (h : P) : left (wrap P) := by simpa using h"],
            &KVMap::new(),
            limits().source,
        )
        .unwrap()
        .into_complete()
        .unwrap();
}

#[test]
fn erasing_simp_before_export_refuses_without_publishing_partial_artifacts() {
    let initial = Engine::builder().build_empty();
    let source = format!("{WRAP}\nattribute [-simp] wrap");
    for files in [
        vec![("Main", source.as_str())],
        vec![
            ("Base", WRAP),
            ("Main", "prelude\nimport Base\nattribute [-simp] wrap"),
        ],
    ] {
        let error = build(&initial, &files, OleanWriteBudget::default()).unwrap_err();
        assert!(matches!(
            error,
            SourceModuleBuildError::Check(SourceModuleCheckError::Extension { extension, .. })
                if extension == simp::export::journal_name()
        ));
        assert!(initial.environment().is_empty());
    }
}

#[test]
fn simp_metadata_obeys_the_module_writer_budget() {
    let initial = Engine::builder().build_empty();
    let complete = compiled(&[("Main", WRAP)]);
    let file_bytes = complete.artifacts[0].report.file_bytes;
    assert!(
        build(
            &initial,
            &[("Main", WRAP)],
            OleanWriteBudget {
                max_bytes: file_bytes,
                ..OleanWriteBudget::default()
            },
        )
        .unwrap()
        .into_complete()
        .is_ok()
    );
    let error = build(
        &initial,
        &[("Main", WRAP)],
        OleanWriteBudget {
            max_bytes: file_bytes - 1,
            ..OleanWriteBudget::default()
        },
    )
    .unwrap_err();
    assert_eq!(error.disposition(), ("resource", false, 3));
    assert!(initial.environment().is_empty());
}
