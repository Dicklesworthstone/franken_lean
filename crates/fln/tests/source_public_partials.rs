//! Public partial definitions keep the checked logical signature separate from
//! their private, atomically admitted executable companion.
#![forbid(unsafe_code)]

use fln::source_check::modules::{
    SourceModuleCheck, SourceModuleCheckError, SourceModuleCheckLimits,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, Outcome,
    SourceCheckLimits, SourceModuleInput,
};
use fln_env::constants::{ConstantInfo, DefinitionSafety};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 * 1024 * 1024),
    )))
}

fn seed() -> Engine {
    Engine::with_source_seed(limits().source.admission)
        .unwrap()
        .into_complete()
        .unwrap()
}

fn check(
    base: &Engine,
    files: &[(&str, &str)],
) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
    let names: Vec<_> = files.iter().map(|(name, _)| n(name)).collect();
    let modules: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    base.check_source_modules(&modules, &names[0], &KVMap::new(), limits())
}

fn complete(base: &Engine, files: &[(&str, &str)]) -> SourceModuleCheck {
    check(base, files)
        .unwrap_or_else(|error| panic!("{files:?}\n{error:?}"))
        .into_complete()
        .unwrap()
}

const API: &str = r#"module
prelude
def hidden : Nat := 7
public partial def count (n : Nat) : Nat :=
  if n == 0 then hidden else count (n - 1)
public partial def noRec (n : Nat) : Nat := hidden + n
"#;

#[test]
fn public_partial_bodies_use_private_values_and_export_only_checked_headers() {
    let base = seed();
    let before = base.environment().clone();
    let local = complete(&base, &[("Api", API)]);
    let private = local.checked.engine.environment();
    let hidden = Name::str(Name::num(n("_private.Api"), 0), "hidden");
    assert!(private.contains(&hidden));
    let Some(ConstantInfo::Opaque(logical)) = private.find(&n("count")) else {
        panic!("partial owner must retain its checked opaque declaration")
    };
    assert!(!logical.is_unsafe);
    assert!(matches!(
        private.find(&n("count._unsafe_rec")),
        Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Partial
    ));
    assert!(matches!(
        private.find(&n("noRec")),
        Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Safe
    ));
    assert!(!private.contains(&n("noRec._unsafe_rec")));
    let execution = local
        .checked
        .engine
        .execute_source_definitions(
            &[b"#eval count 4\n#eval noRec 1"],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().source.admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let values: Vec<_> = execution
        .executions
        .iter()
        .map(|execution| {
            let fln::VmExit::Returned(value) = &execution.exit else {
                panic!("expected a computed result: {execution:?}")
            };
            fln_vm::interpreter::nat_decimal(&value.value).unwrap()
        })
        .collect();
    assert_eq!(values, ["7", "8"]);

    let imported = complete(
        &base,
        &[
            (
                "Main",
                "module\nprelude\npublic import Api\npublic def call (n : Nat) : Nat := count n\n",
            ),
            ("Api", API),
        ],
    );
    let public = imported.checked.engine.environment();
    let Some(ConstantInfo::Axiom(header)) = public.find(&n("count")) else {
        panic!("an importing module must receive only the safe logical header")
    };
    assert!(!header.is_unsafe);
    assert_eq!(header.base, logical.base);
    assert!(matches!(
        public.find(&n("noRec")),
        Some(ConstantInfo::Axiom(_))
    ));
    assert!(!public.contains(&n("count._unsafe_rec")));
    assert!(!public.contains(&hidden));
    for source in [
        "public def leak : Nat := hidden",
        "public def leak : Nat := count._unsafe_rec 0",
        "public theorem leak : count 0 = 7 := by rfl",
    ] {
        let main = format!("module\nprelude\npublic import Api\n{source}\n");
        assert!(check(&base, &[("Main", &main), ("Api", API)]).is_err());
    }
    assert_eq!(base.environment(), &before);
}

#[test]
fn public_partial_headers_cannot_capture_private_types() {
    let base = seed();
    let before = base.environment().clone();
    let private = r#"module
prelude
inductive Hidden where | token
instance : Inhabited Hidden where default := Hidden.token
partial def keep (n : Nat) := if n == 0 then Hidden.token else keep (n - 1)
"#;
    complete(&base, &[("Api", private)]);
    for declaration in [
        "public partial def keep (n : Hidden) : Hidden := keep n",
        "public partial def keep (n : Nat) := if n == 0 then Hidden.token else keep (n - 1)",
    ] {
        let source = format!(
            "module\nprelude\ninductive Hidden where | token\n\
             instance : Inhabited Hidden where default := Hidden.token\n{declaration}\n"
        );
        assert!(check(&base, &[("Api", &source)]).is_err(), "{source}");
    }
    assert_eq!(base.environment(), &before);
}

#[test]
fn public_partial_codegen_tags_keep_owner_and_companion_semantics() {
    let base = seed();
    let api = r#"module
prelude
noncomputable def hidden : Nat := 41
noncomputable section
public partial def unavailable : Nat := hidden
public partial def recursive (n : Nat) : Nat :=
  if n == 0 then hidden else recursive (n - 1)
end
"#;
    let local = complete(&base, &[("Api", api)]);
    let tags = fln_elab::noncomputable::read(local.checked.engine.environment()).unwrap();
    assert!(tags.contains(&n("unavailable")));
    assert!(tags.contains(&n("recursive._unsafe_rec")));
    assert!(!tags.contains(&n("recursive")));

    let imported = complete(
        &base,
        &[
            ("Main", "module\nprelude\npublic import Api\n"),
            ("Api", api),
        ],
    );
    let tags = fln_elab::noncomputable::read(imported.checked.engine.environment()).unwrap();
    assert!(tags.contains(&n("unavailable")));
    assert!(!tags.contains(&n("recursive")));
    assert!(!tags.contains(&n("recursive._unsafe_rec")));
    for value in ["unavailable", "recursive 0"] {
        let main =
            format!("module\nprelude\npublic import Api\npublic def leak : Nat := {value}\n");
        assert!(check(&base, &[("Main", &main), ("Api", api)]).is_err());
    }
}

#[test]
fn invalid_public_partial_batches_publish_neither_half() {
    let base = seed();
    let before = base.environment().clone();
    for body in [
        "public partial def bad (n : Nat) : Nat := if n == 0 then true else bad (n - 1)",
        "public partial def bad (n : Nat) : False := bad n",
        "public def bad._unsafe_rec (n : Nat) : Nat := n\npublic partial def bad (n : Nat) : Nat := bad n",
        "@[simp] public partial def bad (n : Nat) : Nat := bad n",
    ] {
        let source = format!("module\nprelude\n{body}\n");
        assert!(check(&base, &[("Api", &source)]).is_err(), "{source}");
        assert_eq!(base.environment(), &before);
    }
    complete(&base, &[("Api", API)]);
}
