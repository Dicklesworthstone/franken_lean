//! Lifted local partial SCCs keep their complete checked implementation private
//! while publishing only the source owner's public interface and codegen state.
#![forbid(unsafe_code)]

use fln::source_check::modules::{
    SourceModuleCheck, SourceModuleCheckError, SourceModuleCheckLimits,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, Environment, KVMap, Name,
    Outcome, SourceCheckLimits, SourceModuleInput,
};
use fln_env::constants::{ConstantInfo, DefinitionSafety};

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn private_name(module: &str, text: &str) -> Name {
    Name::num(name(&format!("_private.{module}")), 0).append_core(&name(text))
}

fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 << 20),
    )))
}

fn seed() -> Engine {
    Engine::with_source_seed(limits().source.admission)
        .unwrap()
        .into_complete()
        .unwrap()
}

fn on_stack(body: impl FnOnce() + Send) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(16 << 20)
            .spawn_scoped(scope, body)
            .unwrap()
            .join()
            .unwrap();
    });
}

fn check(
    base: &Engine,
    files: &[(&str, &str)],
) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
    let names: Vec<_> = files.iter().map(|(module, _)| name(module)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    base.check_source_modules(&inputs, &names[0], &KVMap::new(), limits())
}

fn complete(base: &Engine, files: &[(&str, &str)]) -> SourceModuleCheck {
    check(base, files)
        .unwrap_or_else(|error| panic!("{files:?}\n{error:?}"))
        .into_complete()
        .unwrap()
}

fn execute(engine: &Engine, source: &str, expected: &[&str]) {
    let before = engine.logical_root(&KVMap::new());
    let result = engine
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().source.admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let values: Vec<_> = result
        .executions
        .iter()
        .map(|execution| {
            let fln::VmExit::Returned(returned) = &execution.exit else {
                panic!("unexpected partial-loop exit: {:?}", execution.exit);
            };
            fln::nat_decimal(&returned.value).unwrap()
        })
        .collect();
    assert_eq!(values, expected);
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

fn linked_group(environment: &Environment, logical: &[Name]) {
    let logical = logical.to_vec();
    let executable: Vec<_> = logical
        .iter()
        .map(|value| Name::str(value.clone(), "_unsafe_rec"))
        .collect();
    for (name, companion) in logical.iter().zip(&executable) {
        let Some(ConstantInfo::Opaque(owner)) = environment.find(name) else {
            panic!("missing checked logical interface {name:?}");
        };
        assert!(!owner.is_unsafe);
        assert_eq!(owner.all, logical);
        let Some(ConstantInfo::Defn(body)) = environment.find(companion) else {
            panic!("missing checked partial implementation {companion:?}");
        };
        assert_eq!(body.safety, DefinitionSafety::Partial);
        assert_eq!(body.all, executable);
        assert_eq!(body.base.type_, owner.base.type_);
        assert_eq!(body.base.level_params, owner.base.level_params);
    }
}

const API: &str = r#"module
prelude
def hidden : Nat := 7
public partial def climb (n : Nat) : Nat :=
  if n == 0 then hidden else
    let rec loop (i : Nat) : Nat :=
      if i == n then i + climb (n - 1) else loop (i + 1)
    loop 0
public partial def index (n : Nat) : Nat :=
  let rec loop (i : Nat) : Nat :=
    if i == n then hidden + i else loop (i + 1)
  loop 0
"#;

#[test]
fn captured_local_sccs_execute_without_publishing_their_private_helpers() {
    on_stack(|| {
        let base = seed();
        let before = base.logical_root(&KVMap::new());
        let checked = complete(&base, &[("Api", API)]);
        let imported = complete(
            &base,
            &[
                (
                    "Main",
                    "module\nprelude\npublic import Api\npublic def call (n : Nat) : Nat := climb n\n",
                ),
                ("Api", API),
            ],
        );
        let private = checked.checked.engine.environment();
        let public = imported.checked.engine.environment();
        linked_group(private, &[private_name("Api", "climb.loop"), name("climb")]);
        linked_group(private, &[private_name("Api", "index.loop")]);
        assert!(!private.contains(&name("climb.loop")));
        assert!(!private.contains(&name("index.loop")));
        assert!(
            matches!(private.find(&name("index")), Some(ConstantInfo::Defn(value))
            if value.safety == DefinitionSafety::Safe)
        );
        assert!(!private.contains(&name("index._unsafe_rec")));
        for owner in ["climb", "index"] {
            let Some(ConstantInfo::Axiom(header)) = public.find(&name(owner)) else {
                panic!("public owner must have only its checked signature");
            };
            assert!(!header.is_unsafe);
            assert_eq!(
                &header.base,
                private.find(&name(owner)).unwrap().constant_val()
            );
        }
        let hidden = private_name("Api", "hidden");
        assert!(private.contains(&hidden));
        for private_name in [
            private_name("Api", "climb.loop"),
            private_name("Api", "climb.loop._unsafe_rec"),
            name("climb._unsafe_rec"),
            private_name("Api", "index.loop"),
            private_name("Api", "index.loop._unsafe_rec"),
            hidden,
        ] {
            assert!(!public.contains(&private_name), "leaked {private_name:?}");
        }
        execute(
            &checked.checked.engine,
            "#eval climb 4\n#eval index 4\n",
            &["17", "11"],
        );
        execute(&imported.checked.engine, "#eval call 4\n", &["17"]);
        for forbidden in [
            "public def leak : Nat := hidden",
            "public def leak : Nat := climb.loop 4 0",
            "public def leak : Nat := index.loop 4 0",
            "public theorem leak : climb 0 = 7 := by rfl",
        ] {
            let main = format!("module\nprelude\npublic import Api\n{forbidden}\n");
            assert!(check(&base, &[("Main", &main), ("Api", API)]).is_err());
        }
        assert_eq!(base.logical_root(&KVMap::new()), before);
    });
}

#[test]
fn helper_codegen_failures_mark_safe_owners_once_and_keep_opaque_witnesses_unmarked() {
    on_stack(|| {
        let base = seed();
        let dependency = base
            .check_source_files(
                &[b"noncomputable def hidden : Nat := 7\n"],
                &KVMap::new(),
                SourceCheckLimits::new(limits().source.admission),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
        let syntax = fln_parse::parse_definition(
            b"partial def index (n : Nat) : Nat :=\n  let rec loop (i : Nat) : Nat :=\n    if i == n then hidden + i else loop (i + 1)\n  loop 0\n",
        )
        .unwrap();
        let candidate = fln_elab::source::partial::elaborate(
            syntax.syntax(),
            dependency.environment(),
            limits().source.admission.kernel,
            &fln_elab::source::scope::SourceScope {
                noncomputable_section: true,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(candidate.owner_name(), Some(&name("index")));
        assert!(
            candidate
                .noncomputable()
                .contains(&name("index.loop._unsafe_rec"))
        );
        assert!(!candidate.noncomputable().contains(&name("index")));
        let admitted = dependency
            .admit_declarations(
                candidate.declarations(),
                &KVMap::new(),
                limits().source.admission,
            )
            .unwrap()
            .into_complete()
            .unwrap();
        let propagated = candidate
            .record_codegen(admitted.engine.environment())
            .unwrap();
        assert!(
            fln_elab::noncomputable::read(&propagated)
                .unwrap()
                .contains(&name("index"))
        );
        let api = API.replace(
            "def hidden : Nat := 7",
            "noncomputable def hidden : Nat := 7\nnoncomputable section",
        ) + "end\n";
        let local = complete(&base, &[("Api", &api)]);
        let private = local.checked.engine.environment();
        let tags = fln_elab::noncomputable::read(private).unwrap();
        for marked in [
            name("index"),
            private_name("Api", "index.loop._unsafe_rec"),
            name("climb._unsafe_rec"),
            private_name("Api", "climb.loop._unsafe_rec"),
        ] {
            assert!(
                tags.contains(&marked),
                "missing codegen failure for {marked:?}"
            );
        }
        for logical in [
            private_name("Api", "index.loop"),
            name("climb"),
            private_name("Api", "climb.loop"),
        ] {
            assert!(
                !tags.contains(&logical),
                "tagged logical witness {logical:?}"
            );
        }
        let imported = complete(
            &base,
            &[
                ("Main", "module\nprelude\npublic import Api\n"),
                ("Api", &api),
            ],
        );
        let public = imported.checked.engine.environment();
        let public_tags = fln_elab::noncomputable::read(public).unwrap();
        assert!(public_tags.contains(&name("index")));
        assert!(!public_tags.contains(&name("climb")));
        for value in ["index 4", "climb 4"] {
            let source = format!("#eval {value}");
            let error = local
                .checked
                .engine
                .execute_source_definitions(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    EngineExecutionLimits::new(limits().source.admission.kernel),
                )
                .expect_err(
                    "failed local compilation cannot become executable through its public owner",
                );
            assert!(
                format!("{error:?}")
                    .to_ascii_lowercase()
                    .contains("noncomputable"),
                "{error:?}"
            );
        }
        let tags = fln_elab::noncomputable::read(imported.checked.engine.environment()).unwrap();
        assert!(tags.contains(&name("index")));
        assert!(!tags.contains(&private_name("Api", "index.loop._unsafe_rec")));
        for value in ["index 4", "climb 4"] {
            let source =
                format!("module\nprelude\npublic import Api\npublic def leak : Nat := {value}\n");
            assert!(check(&base, &[("Main", &source), ("Api", &api)]).is_err());
        }
    });
}

#[test]
fn invalid_local_partial_batches_publish_neither_helpers_nor_owner() {
    on_stack(|| {
        let base = seed();
        let before = base.logical_root(&KVMap::new());
        for source in [
            "public partial def bad (n : Nat) : Nat :=\n  let rec loop (i : Nat) : Nat := if i == n then true else loop (i + 1)\n  loop 0\n",
            "public partial def bad (n : Nat) : Nat :=\n  let rec loop (i : Nat) : False := loop (i + 1)\n  False.elim (loop n)\n",
            "def bad.loop (n : Nat) : Nat := n\npublic partial def bad (n : Nat) : Nat :=\n  let rec loop (i : Nat) : Nat := if i == n then i else loop (i + 1)\n  loop 0\n",
        ] {
            let source = format!("module\nprelude\n{source}");
            assert!(
                check(&base, &[("Api", &source)]).is_err(),
                "accepted {source}"
            );
            assert_eq!(base.logical_root(&KVMap::new()), before);
            for failed in ["bad", "bad.loop", "bad._unsafe_rec", "bad.loop._unsafe_rec"] {
                assert!(!base.environment().contains(&name(failed)));
                assert!(!base.environment().contains(&private_name("Api", failed)));
            }
        }
        let retry = complete(&base, &[("Api", API)]);
        execute(&retry.checked.engine, "#eval climb 4\n", &["17"]);
        assert_eq!(base.logical_root(&KVMap::new()), before);
    });
}
