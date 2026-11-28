//! The real Prelude parser-description family must fit the normal source
//! auxiliary budget without weakening constructor equality or resource stops.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, OleanCheckLimits, OleanModuleInput,
    SourceCheckLimits,
};
use fln_elab::inductive::auxiliaries::{AuxiliaryError, no_confusion_declarations};
use fln_elab::records::RecordBudget;
use fln_env::constants::{ConstantInfo, ConstructorVal};
use std::sync::OnceLock;

const STACK: usize = 128 * 1024 * 1024;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))
}

fn on_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("both checking seats complete")
    .engine
}

fn parser_descr_source() -> &'static str {
    let prelude = include_str!("../../../vendor/lean4-src/src/Init/Prelude.lean");
    let start = prelude
        .find("inductive ParserDescr where")
        .expect("pinned Prelude declares ParserDescr");
    let declaration = &prelude[start..];
    let end = declaration
        .find("\ninstance : Inhabited ParserDescr")
        .expect("the next declaration delimits the unchanged ParserDescr source");
    &declaration[..end]
}

fn parser_descr() -> Engine {
    static PARSER_DESCR: OnceLock<Engine> = OnceLock::new();
    PARSER_DESCR
        .get_or_init(|| {
            // Reuse the checked Prelude import used by the generated-eliminator
            // integration tests. The small source seed deliberately omits
            // Eq.ndrec and the ctorElim prerequisites for the pin's linear
            // noConfusion construction; it is not a Prelude replacement.
            let module = name("Init.Prelude");
            let inputs = [OleanModuleInput {
                name: &module,
                artifact: include_bytes!(
                    "../../fln-conformance/fixtures/tag_attributes/prelude.olean"
                ),
                server_artifact: Some(include_bytes!(
                    "../../fln-conformance/fixtures/tag_attributes/prelude.olean.server"
                )),
                private_artifact: Some(include_bytes!(
                    "../../fln-conformance/fixtures/tag_attributes/prelude.olean.private"
                )),
            }];
            let base = Engine::builder()
                .build_empty()
                .import_olean_modules_for_source(
                    &inputs,
                    std::slice::from_ref(&module),
                    &KVMap::new(),
                    SourceOleanImportLimits::new(OleanCheckLimits::new(16 << 20, limits().kernel)),
                )
                .unwrap()
                .into_complete()
                .unwrap()
                .engine;
            for dependency in ["Eq.ndrec", "HEq.refl", "PULift", "dite", "Nat.decEq"] {
                assert!(base.environment().contains(&name(dependency)));
            }
            let before = base.logical_root(&KVMap::new());
            let result = checked(
                &base,
                &format!(
                    "namespace DefaultBudgetProbe\nopen Lean\n{}\nend DefaultBudgetProbe\n",
                    parser_descr_source()
                ),
            );
            assert_eq!(base.logical_root(&KVMap::new()), before);
            assert!(
                !base
                    .environment()
                    .contains(&name("DefaultBudgetProbe.ParserDescr"))
            );
            result
        })
        .clone()
}

#[test]
fn the_real_parser_description_family_fits_the_default_auxiliary_budget() {
    on_stack(|| {
        let engine = parser_descr();
        let env = engine.environment();
        let Some(ConstantInfo::Induct(family)) = env.find(&name("DefaultBudgetProbe.ParserDescr"))
        else {
            panic!("the actual Prelude family must be admitted");
        };
        assert_eq!(family.ctors.len(), 13);
        assert!(family.is_rec);
        let constructors: Vec<ConstructorVal> = family
            .ctors
            .iter()
            .enumerate()
            .map(|(index, constructor)| {
                let Some(ConstantInfo::Ctor(info)) = env.find(constructor) else {
                    panic!("missing source constructor {constructor:?}");
                };
                assert_eq!(info.cidx as usize, index);
                assert_eq!(info.induct, family.base.name);
                info.clone()
            })
            .collect();
        assert_eq!(
            constructors.iter().map(|ctor| ctor.num_fields).sum::<u32>(),
            33
        );
        assert!(matches!(
            env.find(&name("DefaultBudgetProbe.ParserDescr.rec")),
            Some(ConstantInfo::Rec(_))
        ));
        for suffix in [
            "recOn",
            "casesOn",
            "ctorElim",
            "noConfusionType",
            "noConfusion",
        ] {
            assert!(
                matches!(
                    env.find(&name(&format!("DefaultBudgetProbe.ParserDescr.{suffix}"))),
                    Some(ConstantInfo::Defn(_))
                ),
                "default source admission must include {suffix}"
            );
        }
    });
}

#[test]
fn large_family_no_confusion_preserves_injectivity_and_discrimination() {
    on_stack(|| {
        let base = parser_descr();
        let result = checked(
            &base,
            r#"
namespace DefaultBudgetProbe
theorem symbol_injective (left right : String)
    (h : ParserDescr.symbol left = ParserDescr.symbol right) : left = right :=
  ParserDescr.noConfusion h (fun equality => equality)

theorem sepBy_flag_injective (p q psep qsep : ParserDescr) (left right : String)
    (a b : Bool)
    (h : ParserDescr.sepBy p left psep a = ParserDescr.sepBy q right qsep b) : a = b :=
  ParserDescr.noConfusion h (fun hp hs hpsep flagEquality => flagEquality)

theorem separated_parsers_are_disjoint (P : Prop) (p psep : ParserDescr) (separator : String)
    (flag : Bool)
    (h : ParserDescr.sepBy p separator psep flag = ParserDescr.sepBy1 p separator psep flag) : P :=
  ParserDescr.noConfusion h
end DefaultBudgetProbe
"#,
        );
        for theorem in [
            "DefaultBudgetProbe.symbol_injective",
            "DefaultBudgetProbe.sepBy_flag_injective",
            "DefaultBudgetProbe.separated_parsers_are_disjoint",
        ] {
            assert!(matches!(
                result.environment().find(&name(theorem)),
                Some(ConstantInfo::Thm(_))
            ));
        }

        let before = base.logical_root(&KVMap::new());
        for invalid in [
            r#"namespace DefaultBudgetProbe
theorem bad (P : Prop) (text : String) : P :=
  ParserDescr.noConfusion (Eq.refl (ParserDescr.symbol text))
end DefaultBudgetProbe"#,
            r#"namespace DefaultBudgetProbe
theorem bad (p q psep qsep : ParserDescr) (left right : String) (a b : Bool)
    (h : ParserDescr.sepBy p left psep a = ParserDescr.sepBy q right qsep b) : a = b :=
  ParserDescr.noConfusion h (fun hp hs hpsep flagEquality => hp)
end DefaultBudgetProbe"#,
        ] {
            assert!(
                base.check_source_files(
                    &[invalid.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits()),
                )
                .is_err(),
                "{invalid}"
            );
            assert_eq!(base.logical_root(&KVMap::new()), before);
            assert!(!base.environment().contains(&name("DefaultBudgetProbe.bad")));
        }
    });
}

#[test]
fn a_smaller_binder_budget_still_refuses_the_same_real_family() {
    on_stack(|| {
        let engine = parser_descr();
        let before = engine.logical_root(&KVMap::new());
        let env = engine.environment();
        let Some(ConstantInfo::Induct(family)) = env.find(&name("DefaultBudgetProbe.ParserDescr"))
        else {
            panic!("missing source family");
        };
        let constructors: Vec<ConstructorVal> = family
            .ctors
            .iter()
            .map(|constructor| match env.find(constructor) {
                Some(ConstantInfo::Ctor(info)) => info.clone(),
                _ => panic!("missing constructor {constructor:?}"),
            })
            .collect();
        let Some(ConstantInfo::Defn(cases_on)) =
            env.find(&name("DefaultBudgetProbe.ParserDescr.casesOn"))
        else {
            panic!("missing casesOn");
        };
        let smaller = RecordBudget {
            max_binders: 200,
            ..RecordBudget::default()
        };
        assert_eq!(
            no_confusion_declarations(family, &constructors, cases_on, false, smaller, |name| {
                env.find(name)
            }),
            Err(AuxiliaryError::ResourceLimit)
        );
        assert_eq!(engine.logical_root(&KVMap::new()), before);

        // Exhaustion cannot contaminate a later attempt. Independent retained-pin
        // definition parity is covered by derived_no_confusion; this check binds
        // the direct default-budget path to the declarations actually admitted
        // through the complete source command above.
        let generated = no_confusion_declarations(
            family,
            &constructors,
            cases_on,
            false,
            RecordBudget::default(),
            |name| env.find(name),
        )
        .expect("the normal budget still succeeds after the bounded refusal")
        .expect("ParserDescr has noConfusion");
        assert!(!generated.is_enum_construction);
        for definition in [generated.no_confusion_type, generated.no_confusion] {
            assert_eq!(
                env.find(&definition.base.name),
                Some(&ConstantInfo::Defn(definition.clone()))
            );
        }
        assert_eq!(engine.logical_root(&KVMap::new()), before);
    });
}
