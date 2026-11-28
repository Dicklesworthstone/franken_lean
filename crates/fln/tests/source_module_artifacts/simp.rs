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

const PINNED_STACK: usize = 256 * 1024 * 1024;
const PINNED_BYTES: usize = 256 * 1024 * 1024;

struct PinnedSimpArtifact {
    name: Name,
    public: Vec<u8>,
    server: Option<Vec<u8>>,
    private: Option<Vec<u8>>,
}

struct PinnedSimpFixture {
    engine: Engine,
    artifacts: Vec<PinnedSimpArtifact>,
}

impl PinnedSimpFixture {
    fn inputs(&self) -> Vec<OleanModuleInput<'_>> {
        self.artifacts
            .iter()
            .map(|artifact| OleanModuleInput {
                name: &artifact.name,
                artifact: &artifact.public,
                server_artifact: artifact.server.as_deref(),
                private_artifact: artifact.private.as_deref(),
            })
            .collect()
    }

    fn import(&self, built: &SourceModuleBuild) -> SourceOleanImport {
        let mut inputs = self.inputs();
        inputs.extend(built.artifacts.iter().map(|artifact| {
            OleanModuleInput {
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
            }
        }));
        // Re-admit the actual dependency closure and our physical delta into
        // an empty engine. No source-session snapshot authorizes this import.
        Engine::builder()
            .build_empty()
            .import_olean_modules_for_source(
                &inputs,
                &[name("Main")],
                &KVMap::new(),
                SourceOleanImportLimits::new(OleanCheckLimits::new(
                    PINNED_BYTES,
                    Budget::for_stack_bytes(PINNED_STACK),
                )),
            )
            .unwrap()
            .into_complete()
            .unwrap()
    }
}

fn with_pinned_simp(run: impl FnOnce(&PinnedSimpFixture) + Send + 'static) {
    use std::collections::{BTreeMap, BTreeSet};
    use std::sync::{Mutex, OnceLock};

    static FIXTURE: OnceLock<Option<PinnedSimpFixture>> = OnceLock::new();
    static SERIAL: Mutex<()> = Mutex::new(());
    std::thread::Builder::new()
        .stack_size(PINNED_STACK)
        .spawn(move || {
            let _serial = SERIAL
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let fixture = FIXTURE.get_or_init(|| {
                let compiler = aliases::pinned_lean()?;
                let library = compiler
                    .parent()
                    .unwrap()
                    .parent()
                    .unwrap()
                    .join("lib/lean");
                let root = name("Init.SimpLemmas");
                let mut pending = vec![(root.clone(), false)];
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
                    assert!(
                        seen.len() <= 512,
                        "bounded actual simp-helper import closure"
                    );
                    let path = library
                        .join(module.to_display_string().replace('.', "/"))
                        .with_extension("olean");
                    let optional = |path| match std::fs::read(path) {
                        Ok(bytes) => Some(bytes),
                        Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
                        Err(error) => panic!("reading a pinned companion: {error}"),
                    };
                    let public = std::fs::read(&path).unwrap();
                    let dependencies = fln::olean_module_imports(
                        &public,
                        fln::OleanDecodeLimits::new(PINNED_BYTES),
                    )
                    .unwrap();
                    artifacts.insert(
                        module.clone(),
                        PinnedSimpArtifact {
                            name: module.clone(),
                            public,
                            server: optional(path.with_extension("olean.server")),
                            private: optional(path.with_extension("olean.private")),
                        },
                    );
                    pending.push((module, true));
                    pending.extend(dependencies.into_iter().rev().map(|module| (module, false)));
                }
                let mut fixture = PinnedSimpFixture {
                    engine: Engine::builder().build_empty(),
                    artifacts: ordered
                        .into_iter()
                        .map(|module| artifacts.remove(&module).unwrap())
                        .collect(),
                };
                fixture.engine = fixture
                    .engine
                    .import_olean_modules_for_source(
                        &fixture.inputs(),
                        &[root],
                        &KVMap::new(),
                        SourceOleanImportLimits::new(OleanCheckLimits::new(
                            PINNED_BYTES,
                            Budget::for_stack_bytes(PINNED_STACK),
                        )),
                    )
                    .unwrap()
                    .into_complete()
                    .unwrap()
                    .engine;
                // These are the pin's checked declarations, not fixture axioms
                // with trusted helper names and arbitrary statements.
                for helper in [
                    "eq_true",
                    "eq_false",
                    "Bool.of_not_eq_true",
                    "Bool.of_not_eq_false",
                ] {
                    assert!(
                        matches!(
                            fixture.engine.environment().find(&name(helper)),
                            Some(fln::ConstantInfo::Thm(_))
                        ),
                        "actual checked helper {helper}"
                    );
                }
                Some(fixture)
            });
            if let Some(fixture) = fixture {
                run(fixture);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

/// Keep the small native fixtures, but give the Reference consumer its genuine
/// tactic/notation import. Importing Init beside their synthetic root Eq would
/// collide; rebuild the same user declarations on checked Init instead. The
/// simp journal must be identical, and Lean still sees only native artifacts.
fn reference_simp_artifacts(
    native: &SourceModuleBuild,
    files: &[(&str, &str)],
    probes: &[(&str, bool)],
) {
    let expected: Vec<_> = native
        .artifacts
        .iter()
        .map(|artifact| (artifact.name.clone(), metadata(&artifact.bytes).simps))
        .collect();
    let files: Vec<_> = files
        .iter()
        .map(|(module, source)| {
            let source = if let Some(rest) = source
                .strip_prefix("prelude\n")
                .and_then(|source| source.strip_prefix(EQUALITY))
            {
                format!("prelude\nimport Init.SimpLemmas\n{rest}")
            } else {
                (*source).to_owned()
            };
            ((*module).to_owned(), source)
        })
        .collect();
    assert!(
        files
            .iter()
            .any(|(_, source)| source.contains("import Init.SimpLemmas"))
    );
    let probes: Vec<_> = probes
        .iter()
        .map(|(source, accepted)| ((*source).to_owned(), *accepted))
        .collect();
    with_pinned_simp(move |fixture| {
        let files: Vec<_> = files
            .iter()
            .map(|(module, source)| (module.as_str(), source.as_str()))
            .collect();
        let built = build(&fixture.engine, &files, OleanWriteBudget::default())
            .unwrap()
            .into_complete()
            .unwrap();
        let actual: Vec<_> = built
            .artifacts
            .iter()
            .map(|artifact| (artifact.name.clone(), metadata(&artifact.bytes).simps))
            .collect();
        assert_eq!(
            actual, expected,
            "the genuine Init import cannot change the tested simp entries"
        );
        for (source, accepted) in probes {
            aliases::reference_import(&built, &source, accepted);
        }
    });
}

const PREPROCESSED: &str = r#"prelude
import Init.SimpLemmas
namespace SimpExport
def positive : Prop := True
def negative : Prop := False
def differentLeft : Prop := False
def differentRight : Prop := True
def falseNe : Bool := Bool.false
def trueNe : Bool := Bool.true
def falseNot : Bool := Bool.false
def trueNot : Bool := Bool.true
def iffLeft : Prop := True
def iffRight : Prop := True
theorem positiveRule : positive := True.intro
theorem negativeRule : Not negative := fun h => h
theorem differentRule : Ne differentLeft differentRight := false_ne_true
theorem falseNeRule : Ne falseNe Bool.true := fun h => Bool.noConfusion h
theorem trueNeRule : Ne trueNe Bool.false := fun h => Bool.noConfusion h
theorem falseNotRule : Not (Eq falseNot Bool.true) := fun h => Bool.noConfusion h
theorem trueNotRule : Not (Eq trueNot Bool.false) := fun h => Bool.noConfusion h
theorem iffRule : Iff iffLeft iffRight := Iff.intro (fun h => h) (fun h => h)
attribute [irreducible] positive negative differentLeft differentRight falseNe trueNe falseNot trueNot iffLeft iffRight
attribute [simp 1100] positiveRule negativeRule differentRule falseNeRule trueNeRule falseNotRule trueNotRule iffRule
def first.{u} {A : Sort u} (_x : A) : Prop := True
def second.{u} {A : Sort u} (_x _y : A) : Prop := True
def echo.{u} {A : Sort u} (x : A) : A := x
theorem grouped.{u} {A : Sort u} (x : A) :
    And (first x) (And (Eq (echo x) x) (forall y : A, second x y)) :=
  And.intro True.intro (And.intro rfl (fun _y => True.intro))
attribute [irreducible] first second
attribute [simp 900] grouped
attribute [irreducible] echo
attribute [-simp] grouped
attribute [simp 1200] grouped
def repeated.{u} {A : Sort u} (_x : A) : Prop := True
theorem duplicate.{u} {A : Sort u} (x : A) : And (repeated x) (repeated x) :=
  And.intro True.intro True.intro
attribute [irreducible] repeated
attribute [simp 1150] duplicate
def collision._simp_1 : Nat := Nat.succ Nat.zero
def collisionProp : Prop := True
theorem collision : collisionProp := True.intro
attribute [irreducible] collisionProp
attribute [simp 1175] collision
end SimpExport
"#;

const PREPROCESSED_CONSUMER: &str = r#"theorem consumerPositive : SimpExport.positive := by simp
theorem consumerNegative : Not SimpExport.negative := by simp
theorem consumerDifferent : Not (Eq SimpExport.differentLeft SimpExport.differentRight) := by simp
theorem consumerFalseNe : Eq SimpExport.falseNe Bool.false := by simp
theorem consumerTrueNe : Eq SimpExport.trueNe Bool.true := by simp
theorem consumerFalseNot : Eq SimpExport.falseNot Bool.false := by simp
theorem consumerTrueNot : Eq SimpExport.trueNot Bool.true := by simp
theorem consumerIff : Iff SimpExport.iffLeft SimpExport.iffRight := by simp
theorem consumerFirst.{u} {A : Sort u} (x : A) : SimpExport.first x := by simp
theorem consumerSecond.{u} {A : Sort u} (x y : A) : SimpExport.second x y := by simp
theorem consumerEcho.{u} {A : Sort u} (x : A) : Eq (SimpExport.echo x) x := by simp
theorem consumerDuplicate.{u} {A : Sort u} (x : A) : SimpExport.repeated x := by simp
theorem consumerCollision : SimpExport.collisionProp := by simp
theorem helperPositive : Eq SimpExport.positive True := SimpExport.positiveRule._simp_1
theorem helperNegative : Eq SimpExport.negative False := SimpExport.negativeRule._simp_1
theorem helperDifferent : Eq (Eq SimpExport.differentLeft SimpExport.differentRight) False := SimpExport.differentRule._simp_1
theorem helperFirst.{u} {A : Sort u} (x : A) : Eq (SimpExport.first x) True := SimpExport.grouped._simp_1 x
theorem helperEcho.{u} {A : Sort u} (x : A) : Eq (SimpExport.echo x) x := SimpExport.grouped._simp_2 x
theorem helperSecond.{u} {A : Sort u} (x y : A) : Eq (SimpExport.second x y) True := SimpExport.grouped._simp_3 x y
theorem occupiedNameUnchanged : Eq SimpExport.collision._simp_1 (Nat.succ Nat.zero) := rfl
"#;

#[test]
fn forward_propositions_and_conjunctions_survive_native_artifacts_and_the_pin() {
    with_pinned_simp(|fixture| {
        let before = fixture.engine.logical_root(&KVMap::new());
        let built = build(
            &fixture.engine,
            &[("Main", PREPROCESSED)],
            OleanWriteBudget::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
        assert_eq!(
            built.artifacts.len(),
            1,
            "the native output is a module delta"
        );
        let rows = metadata(&built.artifacts[0].bytes).simps;
        let leaf = |head: &str, arity: usize| {
            std::iter::once(DiscrTreeKey::Const(name(head), arity as u32))
                .chain(std::iter::repeat_n(DiscrTreeKey::Star, arity))
                .collect::<Vec<_>>()
        };
        let mut expected = vec![
            ("positiveRule", 1, 1100, leaf("SimpExport.positive", 0)),
            ("negativeRule", 1, 1100, leaf("SimpExport.negative", 0)),
            (
                "differentRule",
                1,
                1100,
                vec![
                    DiscrTreeKey::Const(name("Eq"), 3),
                    DiscrTreeKey::Other,
                    DiscrTreeKey::Const(name("SimpExport.differentLeft"), 0),
                    DiscrTreeKey::Const(name("SimpExport.differentRight"), 0),
                ],
            ),
            ("falseNeRule", 1, 1100, leaf("SimpExport.falseNe", 0)),
            ("trueNeRule", 1, 1100, leaf("SimpExport.trueNe", 0)),
            ("falseNotRule", 1, 1100, leaf("SimpExport.falseNot", 0)),
            ("trueNotRule", 1, 1100, leaf("SimpExport.trueNot", 0)),
            ("iffRule", 1, 1100, leaf("SimpExport.iffLeft", 0)),
        ];
        for priority in [900, 1200] {
            expected.extend([
                ("grouped", 1, priority, leaf("SimpExport.first", 2)),
                ("grouped", 2, priority, leaf("SimpExport.echo", 2)),
                ("grouped", 3, priority, leaf("SimpExport.second", 3)),
            ]);
        }
        expected.extend([
            ("duplicate", 1, 1150, leaf("SimpExport.repeated", 2)),
            ("duplicate", 1, 1150, leaf("SimpExport.repeated", 2)),
            ("collision", 2, 1175, leaf("SimpExport.collisionProp", 0)),
        ]);
        assert_eq!(rows.len(), expected.len());
        for (row, (origin, suffix, priority, keys)) in rows.iter().zip(&expected) {
            assert_eq!(row.scope, None);
            let SimpKind::Theorem(theorem) = &row.kind else {
                panic!("proposition preprocessing must emit a checked theorem: {row:?}")
            };
            let origin = name(&format!("SimpExport.{origin}"));
            let proof = Name::str(origin.clone(), format!("_simp_{suffix}"));
            assert_eq!(theorem.origin, origin);
            assert_eq!(theorem.proof, fln::Expr::const_(proof.clone(), vec![]));
            assert!(theorem.level_params.is_empty());
            assert_eq!(theorem.priority, *priority);
            assert_eq!(&theorem.keys, keys);
            assert!(theorem.post);
            assert!(!theorem.origin_reverse);
            assert!(!theorem.permutation);
            // The actual pin leaves these proofs untagged, including the
            // equality projected from grouped: its type alone is not rfl.
            assert!(!theorem.reflexive);
            assert!(!theorem.backward_reflexive);
            let Some(fln::ConstantInfo::Thm(checked)) =
                built.checked.checked.engine.environment().find(&proof)
            else {
                panic!("every selected helper is an admitted theorem: {proof:?}")
            };
            assert_eq!(checked.all, [proof]);
            for expression in [&checked.base.type_, &checked.value] {
                assert!(!expression.has_fvar());
                assert!(!expression.has_expr_mvar());
                assert!(!expression.has_level_mvar());
                assert!(!expression.has_loose_bvars());
            }
            assert_eq!(
                checked.base.level_params,
                if matches!(
                    origin.to_display_string().as_str(),
                    "SimpExport.grouped" | "SimpExport.duplicate"
                ) {
                    vec![name("u")]
                } else {
                    vec![]
                },
            );
        }
        for absent in [
            "SimpExport.grouped._simp_4",
            "SimpExport.duplicate._simp_2",
            "SimpExport.collision._simp_3",
        ] {
            assert!(
                !built
                    .checked
                    .checked
                    .engine
                    .environment()
                    .contains(&name(absent))
            );
        }
        let physical = fixture.import(&built);
        let report = physical
            .modules
            .iter()
            .find(|module| module.module == name("Main"))
            .unwrap();
        assert_eq!(report.simps, expected.len());
        assert_eq!(report.activated_simps, expected.len());
        assert_eq!(report.deferred_simps, 0);
        let active = simp::read(physical.engine.environment()).unwrap();
        let group: Vec<_> = active
            .iter()
            .filter(|row| row.declaration == name("SimpExport.grouped"))
            .collect();
        assert_eq!(group.len(), 3);
        assert!(group.iter().all(|row| row.priority == 1200));
        assert_eq!(
            active
                .iter()
                .filter(|row| row.declaration == name("SimpExport.duplicate"))
                .count(),
            1
        );

        let source = format!("prelude\nimport Main\n{PREPROCESSED_CONSUMER}");
        let consumer = name("Consumer");
        physical
            .engine
            .check_source_modules(
                &[SourceModuleInput {
                    name: &consumer,
                    source: source.as_bytes(),
                }],
                &consumer,
                &KVMap::new(),
                limits(),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        aliases::reference_import(&built, &source, true);

        for goal in [
            "theorem absentFirst.{u} {A : Sort u} (x : A) : SimpExport.first x := by simp",
            "theorem absentEcho.{u} {A : Sort u} (x : A) : Eq (SimpExport.echo x) x := by simp",
            "theorem absentSecond.{u} {A : Sort u} (x y : A) : SimpExport.second x y := by simp",
        ] {
            let erased = format!("attribute [-simp] SimpExport.grouped\n{goal}");
            refused(&physical.engine, &erased);
            aliases::reference_import(&built, &format!("prelude\nimport Main\n{erased}"), false);
        }
        let false_goal = "theorem rejectedFalse : SimpExport.negative := by simp";
        refused(&physical.engine, false_goal);
        aliases::reference_import(
            &built,
            &format!("prelude\nimport Main\n{false_goal}"),
            false,
        );
        assert_eq!(fixture.engine.logical_root(&KVMap::new()), before);
    });
}

#[test]
fn proposition_preprocessing_never_exports_false_or_unsafe_proofs() {
    with_pinned_simp(|fixture| {
        let before = fixture.engine.logical_root(&KVMap::new());
        for invalid in [
            "@[simp] theorem falseProposition : False := True.intro",
            "unsafe def unsafeProposition : True := True.intro\nattribute [simp] unsafeProposition",
            "@[simp] theorem falseConjunction : And True False := And.intro True.intro True.intro",
        ] {
            let source = format!("prelude\nimport Init.SimpLemmas\n{invalid}");
            let error = build(
                &fixture.engine,
                &[("Main", &source)],
                OleanWriteBudget::default(),
            )
            .expect_err("a false or unsafe source proof must not produce an artifact");
            assert!(
                !matches!(
                    error.disposition().0,
                    "resource" | "inconclusive" | "internal-fault"
                ),
                "{error:?}"
            );
            assert_eq!(fixture.engine.logical_root(&KVMap::new()), before);
        }
    });
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
fn ordinary_simp_definitions_without_equality_keep_an_explicit_export_refusal() {
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
fn ordinary_definition_equations_and_backward_tags_survive_physical_import() {
    let source = format!(
        "prelude\n{EQUALITY}\
         @[simp 1400] def wrap.{{u}} {{A : Sort u}} (x : A) : A := x\n\
         attribute [irreducible] wrap"
    );
    let built = compiled(&[("Main", &source)]);
    assert!(
        built
            .checked
            .checked
            .engine
            .environment()
            .contains(&name("wrap.eq_1"))
    );
    let physical = metadata(&built.artifacts[0].bytes);
    assert_eq!(physical.simps.len(), 3);
    let SimpKind::Theorem(theorem) = &physical.simps[0].kind else {
        panic!("the equation proof must precede its group and unfolding entry")
    };
    assert_eq!(theorem.origin, name("wrap.eq_1"));
    assert_eq!(theorem.priority, 1400);
    assert!(!theorem.reflexive);
    assert!(theorem.backward_reflexive);
    assert_eq!(
        physical.simps[1].kind,
        SimpKind::UnfoldTheorems {
            declaration: name("wrap"),
            theorems: vec![name("wrap.eq_1")],
        }
    );
    assert_eq!(physical.simps[2].kind, SimpKind::Unfold(name("wrap")));
    assert!(!physical.defeq.contains(&name("wrap.eq_1")));
    assert!(physical.backward_defeq.contains(&name("wrap.eq_1")));

    let receipt = imported(&built);
    assert_eq!(receipt.modules[0].activated_simps, 3);
    assert!(
        !simp::defeq::read(receipt.engine.environment(), || Ok(()))
            .unwrap()
            .contains(&name("wrap.eq_1"))
    );
    assert!(
        simp::defeq::read_backward(receipt.engine.environment(), || Ok(()))
            .unwrap()
            .contains(&name("wrap.eq_1"))
    );
    accepted(
        &receipt.engine,
        "theorem use.{u} {A : Sort u} (x : A) : wrap (wrap x) = x := by simp",
    );
    accepted(
        &receipt.engine,
        "theorem useEquation.{u} {A : Sort u} (x : A) : wrap x = x := wrap.eq_1 x",
    );
    accepted(
        &receipt.engine,
        "attribute [-simp] wrap.eq_1\ntheorem unfoldingRemains.{u} {A : Sort u} (x : A) : wrap x = x := by simp",
    );
    refused(
        &receipt.engine,
        "attribute [-simp] wrap\ntheorem erased.{u} {A : Sort u} (x : A) : wrap x = x := by simp",
    );
    refused(
        &receipt.engine,
        "theorem falseGoal.{u} {A : Sort u} (x y : A) : wrap x = y := by simp",
    );
}

#[test]
fn dependent_universes_and_let_bodies_produce_importable_checked_equations() {
    let source = format!(
        "prelude\n{EQUALITY}\
         @[simp] def dependent.{{u,v}} {{A : Sort u}} (B : A -> Sort v) (x : A) (y : B x) : B x := y\n\
         @[simp] def letWrap.{{u}} {{A : Sort u}} (x : A) : A := let y := x; y\n\
         attribute [irreducible] dependent letWrap"
    );
    let built = compiled(&[("Main", &source)]);
    let receipt = imported(&built);
    accepted(
        &receipt.engine,
        "theorem dependentProof.{u,v} {A : Sort u} (B : A -> Sort v) (x : A) (y : B x) : dependent B x y = y := dependent.eq_1 B x y\n\
         theorem letProof.{u} {A : Sort u} (x : A) : letWrap x = x := letWrap.eq_1 x\n\
         theorem simplify.{u,v} {A : Sort u} (B : A -> Sort v) (x : A) (y : B x) : letWrap (dependent B x y) = y := by simp",
    );
    refused(
        &receipt.engine,
        "theorem falseDependent.{u,v} {A : Sort u} (B : A -> Sort v) (x : A) (y z : B x) : dependent B x y = z := by simp",
    );
}

#[test]
fn class_projections_unfold_without_equations_but_ordinary_wrappers_generate_them() {
    let source = format!(
        "prelude\n{EQUALITY}\
         class Cell (A : Type) where\n  value : A\n\
         attribute [simp] Cell.value\n\
         @[simp] def getCell {{A : Type}} (h : Cell A) : A := @Cell.value A h"
    );
    let built = compiled(&[("Main", &source)]);
    let env = built.checked.checked.engine.environment();
    assert!(!env.contains(&name("Cell.value.eq_1")));
    assert!(env.contains(&name("getCell.eq_1")));
    let rows = metadata(&built.artifacts[0].bytes).simps;
    assert_eq!(rows.len(), 4);
    assert_eq!(rows[0].kind, SimpKind::Unfold(name("Cell.value")));
    let receipt = imported(&built);
    accepted(
        &receipt.engine,
        "theorem projection (A : Type) (x : A) : @Cell.value A (Cell.mk x) = x := by simp\n\
         theorem wrapper {A : Type} (h : Cell A) : getCell h = @Cell.value A h := getCell.eq_1 h",
    );
}

#[test]
fn lazy_equation_requests_and_simp_attributes_share_one_checked_realization() {
    for first in ["wrap.eq_1 x", "by rw [wrap]"] {
        let source = format!(
            "prelude\n{EQUALITY}\
             def wrap.{{u}} {{A : Sort u}} (x : A) : A := x\n\
             theorem first.{{u}} {{A : Sort u}} (x : A) : wrap x = x := {first}\n\
             attribute [simp 1300] wrap\n\
             attribute [irreducible] wrap\n\
             theorem second.{{u}} {{A : Sort u}} (x : A) : wrap (wrap x) = x := by simp"
        );
        let built = compiled(&[("Main", &source)]);
        let physical = metadata(&built.artifacts[0].bytes);
        assert_eq!(physical.simps.len(), 3, "{first}");
        let SimpKind::Theorem(theorem) = &physical.simps[0].kind else {
            panic!("the lazy generated proof remains the selected equation")
        };
        assert_eq!(theorem.origin, name("wrap.eq_1"));
        assert_eq!(theorem.priority, 1300);
        assert!(!theorem.reflexive);
        assert!(theorem.backward_reflexive);
        let receipt = imported(&built);
        accepted(
            &receipt.engine,
            "theorem downstream.{u} {A : Sort u} (x : A) : wrap (wrap x) = x := by simp",
        );
    }
}

#[test]
fn private_equation_requests_preserve_public_simp_artifacts() {
    for first in ["wrap.eq_1 x", "by rw [wrap]"] {
        let source = format!(
            "module\nprelude\n\
             public inductive Eq.{{u}} {{A : Sort u}} : A -> A -> Prop where | refl (a : A) : Eq a a\n\
             @[expose] public def wrap.{{u}} {{A : Sort u}} (x : A) : A := x\n\
             theorem first.{{u}} {{A : Sort u}} (x : A) : wrap x = x := {first}\n\
             public section\nattribute [simp 1300] wrap\n\
             attribute [irreducible] wrap"
        );
        let built = compiled(&[("Main", &source)]);
        assert!(built.artifacts[0].companions.is_some());
        let artifact = &built.artifacts[0];
        let parts = artifact.companions.as_ref().unwrap();
        let public = fln_olean::region::OleanView::parse(&artifact.bytes).unwrap();
        let private = fln_olean::region::OleanView::parse_with_dependencies(
            &parts.private,
            &[&artifact.bytes, &parts.server],
        )
        .unwrap();
        let declarations = fln_olean::decl::decode_chain_constants_with_origin(
            &public,
            &private,
            fln::OleanWalkBudget::default(),
        )
        .unwrap();
        assert!(declarations.private_only().next().is_some());
        let physical = metadata(&built.artifacts[0].bytes);
        assert_eq!(physical.simps.len(), 3, "{first}");
        let SimpKind::Theorem(theorem) = &physical.simps[0].kind else {
            panic!("the public equation retains its theorem registration")
        };
        assert_eq!(theorem.origin, name("wrap.eq_1"));
        assert_eq!(theorem.priority, 1300);
        let receipt = imported(&built);
        let private_use = "theorem leaked.{u} {A : Sort u} (x : A) : wrap x = x := first x";
        assert!(
            receipt
                .engine
                .check_source_files(&[private_use.as_bytes()], &KVMap::new(), limits().source,)
                .is_err()
        );
        assert!(!receipt.engine.environment().contains(&name("first")));
        assert!(receipt.engine.environment().contains(&name("wrap.eq_1")));
        accepted(
            &receipt.engine,
            "theorem downstream.{u} {A : Sort u} (x : A) : wrap (wrap x) = x := by simp",
        );
        // This API emits source data, not the IR required by the pin's normal
        // import path. Read the real regions through its data reader instead.
        aliases::reference_import_stdout(
            &built,
            r#"import Lean
open Lean
#eval do
  let parts ← readModuleDataParts #["Main.olean", "Main.olean.server", "Main.olean.private"]
  let some (exported, _) := parts[0]? | throw (IO.userError "missing exported region")
  let some (complete, _) := parts[2]? | throw (IO.userError "missing private region")
  IO.println s!"{parts.size}/{exported.isModule}/{exported.constNames.contains `wrap.eq_1}/{decide (complete.constNames.size > exported.constNames.size)}"
"#,
            true,
            Some("3/true/true/true\n"),
        );
        let exact_budget = OleanWriteBudget {
            max_bytes: artifact.report.file_bytes
                + parts.server_report.file_bytes
                + parts.private_report.file_bytes,
            max_objects: artifact.report.runtime_objects
                + parts.server_report.runtime_objects
                + parts.private_report.runtime_objects,
        };
        let initial = Engine::builder().build_empty();
        for budget in [
            OleanWriteBudget {
                max_bytes: exact_budget.max_bytes - 1,
                ..exact_budget
            },
            OleanWriteBudget {
                max_objects: exact_budget.max_objects - 1,
                ..exact_budget
            },
        ] {
            assert!(matches!(
                build(&initial, &[("Main", &source)], budget),
                Err(SourceModuleBuildError::Encode {
                    error: fln::OleanWriteError::Budget { .. },
                    ..
                })
            ));
        }
        let exact = build(&initial, &[("Main", &source)], exact_budget)
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(exact.artifacts[0].bytes, artifact.bytes);
        let exact_parts = exact.artifacts[0].companions.as_ref().unwrap();
        assert_eq!(exact_parts.server, parts.server);
        assert_eq!(exact_parts.private, parts.private);
    }
}

#[test]
fn module_families_keep_import_visibility_and_share_the_closure_writer_budget() {
    let files = [
        (
            "Main",
            "module\nprelude\npublic import Lib\nimport Secret\n@[expose] public def chosen : Token := value\n",
        ),
        (
            "Lib",
            "module\nprelude\npublic inductive Token where | mk\n@[expose] public def value : Token := Token.mk\n",
        ),
        (
            "Secret",
            "module\nprelude\npublic inductive Hidden where | mk\n",
        ),
    ];
    let initial = Engine::builder().build_empty();
    let built = build(&initial, &files, OleanWriteBudget::default())
        .unwrap()
        .into_complete()
        .unwrap();
    let main = built
        .artifacts
        .iter()
        .find(|a| a.name == name("Main"))
        .unwrap();
    let module = fln_olean::region::OleanView::parse(&main.bytes)
        .unwrap()
        .module_data(fln::OleanWalkBudget::default())
        .unwrap();
    assert!(module.is_module);
    assert_eq!(
        module
            .imports
            .iter()
            .map(|i| (i.module.clone(), i.is_exported))
            .collect::<Vec<_>>(),
        [(name("Lib"), true), (name("Secret"), false)]
    );
    let receipt = imported(&built);
    accepted(&receipt.engine, "def selected : Token := chosen");
    let mut exact_budget = OleanWriteBudget {
        max_bytes: 0,
        max_objects: 0,
    };
    for artifact in &built.artifacts {
        let parts = artifact.companions.as_ref().unwrap();
        for report in [artifact.report, parts.server_report, parts.private_report] {
            exact_budget.max_bytes += report.file_bytes;
            exact_budget.max_objects += report.runtime_objects;
        }
    }
    for budget in [
        OleanWriteBudget {
            max_bytes: exact_budget.max_bytes - 1,
            ..exact_budget
        },
        OleanWriteBudget {
            max_objects: exact_budget.max_objects - 1,
            ..exact_budget
        },
    ] {
        let error = build(&initial, &files, budget).unwrap_err();
        assert_eq!(error.disposition(), ("resource", false, 3));
        assert!(initial.environment().is_empty());
    }
    let retry = build(&initial, &files, exact_budget)
        .unwrap()
        .into_complete()
        .unwrap();
    for (actual, expected) in retry.artifacts.iter().zip(&built.artifacts) {
        assert_eq!(actual.bytes, expected.bytes);
        let actual = actual.companions.as_ref().unwrap();
        let expected = expected.companions.as_ref().unwrap();
        assert_eq!(actual.server, expected.server);
        assert_eq!(actual.private, expected.private);
    }
}

#[test]
fn repeated_definition_attributes_reuse_one_checked_equation_with_each_priority() {
    let source = format!(
        "prelude\n{EQUALITY}\
         @[simp 1200] def wrap.{{u}} {{A : Sort u}} (x : A) : A := x\n\
         attribute [simp 1500] wrap\n\
         attribute [irreducible] wrap"
    );
    let built = compiled(&[("Main", &source)]);
    let physical = metadata(&built.artifacts[0].bytes);
    assert_eq!(physical.simps.len(), 6);
    let priorities: Vec<_> = physical
        .simps
        .iter()
        .filter_map(|row| match &row.kind {
            SimpKind::Theorem(theorem) => Some(theorem.priority),
            _ => None,
        })
        .collect();
    assert_eq!(priorities, [1200, 1500]);
    assert_eq!(
        physical
            .backward_defeq
            .iter()
            .filter(|tag| **tag == name("wrap.eq_1"))
            .count(),
        1
    );
    let receipt = imported(&built);
    let selected = simp::read(receipt.engine.environment()).unwrap();
    let equation = selected
        .iter()
        .find(|rule| rule.declaration == name("wrap.eq_1"))
        .expect("the final equation registration remains selected");
    assert_eq!(equation.priority, 1500);
    accepted(
        &receipt.engine,
        "theorem use.{u} {A : Sort u} (x : A) : wrap (wrap x) = x := by simp",
    );
}

#[test]
fn checked_equations_replay_across_fresh_module_sessions() {
    use fln::source_check::modules::persisted::{
        PersistedModules, SourceModuleKey, SourceModuleStore,
    };
    use fln::source_check::modules::reuse::CheckerIdentity;
    use std::cell::RefCell;
    use std::collections::BTreeMap;

    #[derive(Default)]
    struct Records(RefCell<BTreeMap<SourceModuleKey, Vec<u8>>>);
    impl SourceModuleStore for Records {
        fn load(&self, key: SourceModuleKey) -> Result<Option<Vec<u8>>, String> {
            Ok(self.0.borrow().get(&key).cloned())
        }
        fn save(&self, key: SourceModuleKey, bytes: &[u8]) -> Result<(), String> {
            self.0.borrow_mut().insert(key, bytes.to_vec());
            Ok(())
        }
    }

    let base = format!(
        "prelude\n{EQUALITY}\
         def wrap.{{u}} {{A : Sort u}} (x : A) : A := x\n\
         attribute [simp] wrap\n\
         attribute [irreducible] wrap"
    );
    let files = [
        ("Base", base.as_str()),
        ("Left", "prelude\nimport Base"),
        ("Right", "prelude\nimport Base"),
        (
            "Main",
            "prelude\nimport Left\nimport Right\ntheorem use.{u} {A : Sort u} (x : A) : wrap (wrap x) = x := by simp",
        ),
    ];
    let names: Vec<_> = files.iter().map(|(module, _)| name(module)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    let records = Records::default();
    let compile = || {
        let mut session = SourceModuleSession::new(
            Engine::builder().build_empty(),
            KVMap::new(),
            limits(),
            SourceModuleCacheLimits::default(),
        );
        session
            .compile_with_records(
                &inputs,
                &name("Main"),
                OleanWriteBudget::default(),
                Some(PersistedModules {
                    checker: CheckerIdentity::of_executable(b"checked-simp-equation-replay"),
                    store: &records,
                }),
                None,
            )
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let cold = compile();
    let warm = compile();
    assert_eq!((cold.elaborated_modules, cold.persisted_modules), (4, 0));
    assert_eq!((warm.elaborated_modules, warm.persisted_modules), (0, 4));
    assert_eq!(warm.checked.checked.theorems, cold.checked.checked.theorems);
    assert_eq!(
        warm.checked.checked.result_logical_root,
        cold.checked.checked.result_logical_root
    );
    for (cold, warm) in cold.artifacts.iter().zip(&warm.artifacts) {
        assert_eq!(warm.name, cold.name);
        assert_eq!(warm.bytes, cold.bytes);
        let rows = metadata(&warm.bytes);
        assert_eq!(
            rows.simps.len(),
            if warm.name == name("Base") { 3 } else { 0 }
        );
    }
    let receipt = imported(&warm);
    accepted(
        &receipt.engine,
        "theorem useAgain.{u} {A : Sort u} (x : A) : wrap (wrap x) = x := by simp",
    );
}

#[test]
fn nondefault_equation_policy_cannot_disappear_from_an_artifact() {
    let initial = Engine::builder().build_empty();
    let module = name("Main");
    let files = [SourceModuleInput {
        name: &module,
        source: b"prelude\ndef plain.{u} {A : Sort u} (x : A) : A := x",
    }];
    for (option, value) in [
        ("backward.eqns.nonrecursive", false),
        ("backward.eqns.deepRecursiveSplit", false),
        ("backward.defeqAttrib.useBackward", true),
    ] {
        let mut options = KVMap::new();
        options.insert(name(option), fln::DataValue::OfBool(value));
        let error = initial
            .compile_source_modules(
                &files,
                &module,
                &options,
                limits(),
                OleanWriteBudget::default(),
            )
            .expect_err("the pinned persistent equation options must not be omitted");
        assert!(
            matches!(error,
            SourceModuleBuildError::Check(SourceModuleCheckError::Extension { extension, .. })
                if extension == simp::equations::journal_name()),
            "{option}"
        );
        assert!(initial.environment().is_empty());
    }
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
fn simp_erasures_remain_local_while_owned_and_imported_additions_persist() {
    let initial = Engine::builder().build_empty();
    let root = initial.logical_root(&KVMap::new());
    let probe = "theorem use.{u} {A : Sort u} (x : A) : wrap (wrap x) = x := by simp";
    let false_goal = "theorem wrong.{u} {A : Sort u} (x y : A) : wrap x = y := by simp";
    for (declaration, origin, expected_rows) in [
        (
            "@[simp] def wrap.{u} {A : Sort u} (x : A) : A := x",
            "wrap",
            3,
        ),
        (
            "def wrap.{u} {A : Sort u} (x : A) : A := x\n\
             @[simp 900] theorem unwrap.{u} {A : Sort u} (x : A) : wrap x = x := by rfl",
            "unwrap",
            1,
        ),
    ] {
        let library = format!("prelude\n{EQUALITY}{declaration}\nattribute [irreducible] wrap");
        let erased = format!("{library}\nattribute [-simp] {origin}");
        let owned = compiled(&[("Main", &erased)]);
        assert!(
            simp::read(owned.checked.checked.engine.environment())
                .unwrap()
                .is_empty()
        );
        refused(&owned.checked.checked.engine, probe);
        assert_eq!(
            metadata(&owned.artifacts[0].bytes).simps.len(),
            expected_rows
        );
        let physical = imported(&owned);
        accepted(&physical.engine, probe);
        refused(&physical.engine, false_goal);
        reference_simp_artifacts(
            &owned,
            &[("Main", &erased)],
            &[
                (&format!("prelude\nimport Main\n{probe}"), true),
                (
                    &format!("prelude\nimport Main\nattribute [-simp] {origin}\n{probe}"),
                    false,
                ),
            ],
        );

        // An adapter containing only an erasure exports no simp operations.
        // Its consumer still receives the provider's original registration.
        let adapter = format!("prelude\nimport Base\nattribute [-simp] {origin}");
        let consumer = format!(
            "prelude\nimport Adapter\n{}",
            probe.replace("theorem use.", "theorem fromImport.")
        );
        let graph = compiled(&[
            ("Main", &consumer),
            ("Adapter", &adapter),
            ("Base", &library),
        ]);
        assert_eq!(graph.artifacts[1].report.constants, 0);
        assert!(metadata(&graph.artifacts[1].bytes).simps.is_empty());
        let physical = imported(&graph);
        for engine in [&graph.checked.checked.engine, &physical.engine] {
            accepted(engine, probe);
            refused(engine, false_goal);
        }
        reference_simp_artifacts(
            &graph,
            &[
                ("Main", &consumer),
                ("Adapter", &adapter),
                ("Base", &library),
            ],
            &[(&format!("prelude\nimport Main\n{probe}"), true)],
        );

        let invalid = format!("{erased}\n{probe}");
        assert!(matches!(
            build(&initial, &[("Main", &invalid)], OleanWriteBudget::default()),
            Err(SourceModuleBuildError::Check(
                SourceModuleCheckError::Source { .. }
            ))
        ));
        assert_eq!(initial.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn erasing_and_readding_simp_preserves_original_tie_slots_and_new_priorities() {
    let declarations = format!(
        "prelude\n{EQUALITY}\
         def choose.{{u}} {{A : Sort u}} (x : A) : A := x\n\
         def first.{{u}} {{A : Sort u}} (x : A) : A := x\n\
         def second.{{u}} {{A : Sort u}} (x : A) : A := x\n\
         @[simp 900] theorem pickFirst.{{u}} {{A : Sort u}} (x : A) : choose x = first x := by rfl\n\
         @[simp 900] theorem pickSecond.{{u}} {{A : Sort u}} (x : A) : choose x = second x := by rfl\n\
         attribute [irreducible] choose first second\n\
         attribute [-simp] pickFirst"
    );
    for (priority, selected, rejected) in [
        (900, "first", "second"),
        (1200, "first", "second"),
        (700, "second", "first"),
    ] {
        let source = format!("{declarations}\nattribute [simp {priority}] pickFirst");
        let built = compiled(&[("Main", &source)]);
        let rows = metadata(&built.artifacts[0].bytes).simps;
        assert_eq!(
            rows.len(),
            3,
            "erasure must not replace the chronological additions"
        );
        let priorities: Vec<_> = rows
            .iter()
            .map(|row| match &row.kind {
                SimpKind::Theorem(theorem) => theorem.priority,
                other => panic!("unexpected simp row: {other:?}"),
            })
            .collect();
        assert_eq!(priorities, [900, 900, priority]);
        let proof = |target| {
            format!(
                "theorem chosen.{{u}} {{A : Sort u}} (x : A) (P : A -> Prop) (h : P ({target} x)) : P (choose x) := by simpa using h"
            )
        };
        let good = proof(selected);
        let bad = proof(rejected);
        let physical = imported(&built);
        for engine in [&built.checked.checked.engine, &physical.engine] {
            accepted(engine, &good);
            refused(engine, &bad);
        }
        reference_simp_artifacts(
            &built,
            &[("Main", &source)],
            &[
                (&format!("prelude\nimport Main\n{good}"), true),
                (&format!("prelude\nimport Main\n{bad}"), false),
            ],
        );
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

#[test]
fn method_specs_simp_attribute_validates_targets_without_entering_default_simp() {
    let initial = Engine::builder().build_empty();
    let built = compiled(&[(
        "Main",
        "module\nprelude\npublic section\n\
         inductive N : Type where | z : N | s : N -> N\n\
         inductive Same {α : Type} (a : α) : α -> Prop where | refl : Same a a\n\
         def idN (n : N) : N := n\n\
         @[method_specs_simp] theorem idN_eq (n : N) : Same (idN n) n := Same.refl\n\
         @[method_specs_simp ← low + 1] theorem idN_eq_rev (n : N) : Same n (idN n) := Same.refl\n\
         @[local method_specs_simp ↓] theorem idN_eq_pre (n : N) : Same (idN n) n := Same.refl\n",
    )]);
    assert!(
        built
            .checked
            .checked
            .engine
            .environment()
            .contains(&name("idN_eq"))
    );
    let active = simp::read(built.checked.checked.engine.environment()).unwrap();
    assert!(
        active.is_empty(),
        "method_specs_simp must stay out of the default simp set: {active:?}"
    );
    for bad in [
        "prelude\n@[method_specs_simp] inductive Bad where | a\n",
        "prelude\n@[method_specs_simp] structure Bad where\n  x : Prop\n",
        "prelude\ninductive N where | z\n@[method_specs_simp] opaque badOpaque (n : N) : N := n\n",
    ] {
        let err = build(&initial, &[("Main", bad)], OleanWriteBudget::default()).unwrap_err();
        assert_eq!(err.disposition().2, 1, "must refuse invalid target: {bad}");
    }
    assert!(initial.environment().is_empty());
}
