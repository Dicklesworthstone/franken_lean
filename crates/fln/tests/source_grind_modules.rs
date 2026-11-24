//! Explicit grind registrations survive native imports without leaking private symbols.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::{SourceOleanImport, SourceOleanImportLimits};
use fln::source_check::modules::{
    SourceModuleBuild, SourceModuleCheck, SourceModuleCheckError, SourceModuleCheckLimits,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, Expr, KVMap, Name, OleanCheckLimits, OleanModuleInput,
    OleanWriteBudget, Outcome, SourceCheckLimits, SourceModuleInput,
};
use fln_elab::grind_patterns::{self, CapturedPatterns, GrindPattern};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 * 1024 * 1024),
    )))
}

fn check(
    base: &Engine,
    files: &[(&str, &str)],
) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
    let names: Vec<_> = files.iter().map(|(name, _)| n(name)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    base.check_source_modules(&inputs, &n("Main"), &KVMap::new(), limits())
}

fn complete(base: &Engine, files: &[(&str, &str)]) -> SourceModuleCheck {
    check(base, files)
        .unwrap_or_else(|error| panic!("{files:?}: {error:?}"))
        .into_complete()
        .unwrap()
}

fn row(declaration: Name, trigger: &str) -> GrindPattern {
    let pattern = Expr::app(Expr::const_(n(trigger), vec![]), Expr::bvar(1).unwrap());
    GrindPattern {
        declaration,
        num_params: 2,
        data_params: 1,
        // The trailing proof occupies index zero in the full theorem telescope.
        patterns: vec![pattern.clone()],
        captured: Some(CapturedPatterns {
            patterns: vec![pattern],
            symbols: vec![n(trigger)],
        }),
    }
}

fn build(base: &Engine, files: &[(&str, &str)]) -> SourceModuleBuild {
    let names: Vec<_> = files.iter().map(|(name, _)| n(name)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    base.compile_source_modules(
        &inputs,
        &n("Main"),
        &KVMap::new(),
        limits(),
        OleanWriteBudget::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap()
}

fn import(base: &Engine, built: &SourceModuleBuild) -> SourceOleanImport {
    let inputs: Vec<_> = built
        .artifacts
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
    base.import_olean_modules_for_source(
        &inputs,
        &[n("Main")],
        &KVMap::new(),
        SourceOleanImportLimits::new(OleanCheckLimits::new(
            4 << 20,
            limits().source.admission.kernel,
        )),
    )
    .unwrap()
    .into_complete()
    .unwrap()
}

const CORE: &str = "prelude\naxiom A : Type\naxiom p : A -> Prop\naxiom trigger : A -> A\naxiom other : A -> A\ntheorem rule (x : A) (h : p x) : p x := h\n";

#[test]
fn global_grind_rows_cross_a_diamond_once_with_their_full_binder_offsets() {
    let base = Engine::builder().build_empty();
    let library = format!("{CORE}grind_pattern rule => trigger x\ngrind_pattern rule => other x\n");
    let result = complete(
        &base,
        &[
            ("Main", "prelude\nimport Left\nimport Right"),
            ("Left", "prelude\nimport Library"),
            ("Right", "prelude\nimport Library"),
            ("Library", &library),
        ],
    );
    assert_eq!(
        result.module_order,
        [n("Library"), n("Left"), n("Right"), n("Main")]
    );
    assert_eq!(
        grind_patterns::read(result.checked.engine.environment()).unwrap(),
        [row(n("rule"), "trigger"), row(n("rule"), "other")]
    );
    assert!(grind_patterns::read(base.environment()).unwrap().is_empty());
}

#[test]
fn public_imports_project_grind_rows_while_legacy_imports_retain_private_targets() {
    let base = Engine::builder().build_empty();
    let library = "module\nprelude\npublic axiom A : Type\npublic axiom p : A -> Prop\npublic axiom trigger : A -> A\npublic theorem visible (x : A) (h : p x) : p x := h\nprivate theorem hidden (x : A) (h : p x) : p x := h\ngrind_pattern visible => trigger x\ngrind_pattern hidden => trigger x\n";
    let hidden = Name::num(n("_private.Library"), 0).append_core(&n("hidden"));
    for (main, private_visible) in [
        ("module\nprelude\npublic import Library", false),
        ("prelude\nimport Library", true),
    ] {
        let result = complete(&base, &[("Main", main), ("Library", library)]);
        let environment = result.checked.engine.environment();
        let mut expected = vec![row(n("visible"), "trigger")];
        if private_visible {
            expected.push(row(hidden.clone(), "trigger"));
        }
        assert_eq!(grind_patterns::read(environment).unwrap(), expected);
        assert_eq!(environment.contains(&hidden), private_visible);
        assert!(!environment.contains(&n("hidden")));
    }
}

#[test]
fn a_private_trigger_on_a_public_rule_refuses_the_module_atomically() {
    let base = Engine::builder().build_empty();
    let before = base.logical_root(&KVMap::new());
    let valid = "module\nprelude\npublic axiom A : Type\npublic axiom p : A -> Prop\npublic axiom trigger : A -> A\nprivate axiom hidden : A -> A\npublic theorem rule (x : A) (h : p x) : p x := h\ngrind_pattern rule => trigger x\n";
    let accepted = complete(&base, &[("Main", valid)]);
    assert_eq!(
        grind_patterns::read(accepted.checked.engine.environment()).unwrap(),
        [row(n("rule"), "trigger")]
    );
    let invalid = format!("{valid}grind_pattern rule => hidden x\n");
    let error = check(&base, &[("Main", &invalid)]).unwrap_err();
    match error {
        SourceModuleCheckError::Source { module, .. } => assert_eq!(module, n("Main")),
        SourceModuleCheckError::Extension {
            module, extension, ..
        } => {
            assert_eq!(module, n("Main"));
            assert_eq!(extension, grind_patterns::journal_name());
        }
        other => panic!("unexpected refusal: {other:?}"),
    }
    assert_eq!(base.logical_root(&KVMap::new()), before);
    assert!(base.environment().is_empty());
    assert!(grind_patterns::read(base.environment()).unwrap().is_empty());
}

#[test]
fn artifact_export_reimports_ordered_groups_without_mutating_the_source_base() {
    let base = Engine::builder().build_empty();
    let before = base.logical_root(&KVMap::new());
    let registered = format!(
        "{CORE}grind_pattern rule => trigger x\ngrind_pattern rule => other x\ngrind_pattern rule => trigger x\n"
    );
    let built = build(&base, &[("Main", &registered)]);
    assert_eq!(built.artifacts.len(), 1);
    let imported = import(&base, &built);
    let expected = [
        row(n("rule"), "trigger"),
        row(n("rule"), "other"),
        row(n("rule"), "trigger"),
    ];
    assert_eq!(
        grind_patterns::read(built.checked.checked.engine.environment()).unwrap(),
        expected
    );
    assert_eq!(
        grind_patterns::read(imported.engine.environment()).unwrap(),
        expected
    );
    assert_eq!(imported.modules[0].grind_entries, 3);
    assert_eq!(imported.modules[0].grind_patterns, 3);
    assert_eq!(imported.modules[0].deferred_grind, 0);
    assert_eq!(base.logical_root(&KVMap::new()), before);
    assert!(base.environment().is_empty());
}

#[test]
fn support_arguments_cannot_supply_the_only_coverage_for_a_theorem_parameter() {
    let base = Engine::builder().build_empty();
    let before = base.logical_root(&KVMap::new());
    for (label, declarations, pattern) in [
        (
            "a compound type argument",
            "prelude\naxiom A : Type\naxiom a : A\naxiom P : Prop\nnoncomputable def T (x : A) : Type := A\naxiom tag {X : Type} (v : X) : A\naxiom rule (x : A) : P\n",
            "@tag (T x) a",
        ),
        (
            "a compound instance argument",
            "prelude\naxiom A : Type\naxiom P : Prop\nclass C where\n  val : A\naxiom tag [C] : A\naxiom rule (x : A) : P\n",
            "@tag (C.mk x)",
        ),
    ] {
        let accepted = complete(&base, &[("Main", declarations)]);
        assert!(
            grind_patterns::read(accepted.checked.engine.environment())
                .unwrap()
                .is_empty(),
            "{label}"
        );
        let source = format!("{declarations}grind_pattern rule => {pattern}\n");
        let error = check(&base, &[("Main", &source)]).unwrap_err();
        assert!(
            matches!(&error, SourceModuleCheckError::Source { module, .. } if *module == n("Main")),
            "{label}: {error:?}"
        );
        assert!(
            format!("{error:?}").contains("support argument"),
            "{label}: {error:?}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before, "{label}");
        assert!(base.environment().is_empty());
        assert!(grind_patterns::read(base.environment()).unwrap().is_empty());
    }
}

#[test]
fn prelude_subtype_property_uses_its_checked_polymorphic_value_projection() {
    let base = Engine::builder().build_empty();
    let source = "prelude\nuniverse u\nstructure Subtype {α : Sort u} (p : α → Prop) where\n  val : α\n  property : p val\ngrind_pattern Subtype.property => self.val\n";
    let result = complete(&base, &[("Main", source)]);
    let environment = result.checked.engine.environment();
    let Some(fln_env::constants::ConstantInfo::Defn(property)) =
        environment.find(&n("Subtype.property"))
    else {
        panic!("Subtype.property must be an admitted proof projection");
    };
    let Some(fln_env::constants::ConstantInfo::Defn(value)) = environment.find(&n("Subtype.val"))
    else {
        panic!("Subtype.val must be an admitted data projection");
    };
    assert_eq!(property.safety, fln_env::constants::DefinitionSafety::Safe);
    assert_eq!(value.safety, fln_env::constants::DefinitionSafety::Safe);
    assert_eq!(property.base.level_params.len(), 1);
    assert_eq!(value.base.level_params, property.base.level_params);
    let levels = property
        .base
        .level_params
        .iter()
        .cloned()
        .map(fln_core::level::Level::param)
        .collect();
    let trigger = [2, 1, 0]
        .into_iter()
        .fold(Expr::const_(n("Subtype.val"), levels), |function, index| {
            Expr::app(function, Expr::bvar(index).unwrap())
        });
    assert_eq!(
        grind_patterns::read(environment).unwrap(),
        [GrindPattern {
            declaration: n("Subtype.property"),
            num_params: 3,
            data_params: 3,
            patterns: vec![trigger.clone()],
            captured: Some(CapturedPatterns {
                patterns: vec![trigger.clone()],
                symbols: vec![n("Subtype.val")],
            }),
        }]
    );
    // The registered proof is the structure's original second projection,
    // and its dependent result refers to the same first-projection trigger.
    let mut type_ = &property.base.type_;
    let mut body = &property.value;
    for _ in 0..3 {
        let fln::ExprNode::ForallE {
            body: next_type, ..
        } = type_.node()
        else {
            panic!("Subtype.property must retain its three-parameter telescope");
        };
        let fln::ExprNode::Lam {
            body: next_body, ..
        } = body.node()
        else {
            panic!("Subtype.property must retain its three-parameter proof");
        };
        type_ = next_type;
        body = next_body;
    }
    assert_eq!(*type_, Expr::app(Expr::bvar(1).unwrap(), trigger));
    assert_eq!(*body, Expr::proj(n("Subtype"), 1, Expr::bvar(0).unwrap()));
    assert!(base.environment().is_empty());
}

#[path = "source_grind_modules/artifacts.rs"]
mod artifacts;
