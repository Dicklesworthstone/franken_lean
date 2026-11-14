//! Command quotations preserve definition-site globals, local telescopes and fresh names.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};

fn check(source: &str) -> Result<(Engine, usize), String> {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission),
        )
        .map_err(|error| format!("{error:?}"))
        .map(|result| {
            let checked = result.into_complete().unwrap();
            (checked.engine, checked.theorems)
        })
}

#[test]
fn generated_declaration_binders_shadow_globals_in_the_result_and_body() {
    let source = r#"
def x : Nat := 99
def α : Type := Nat
macro "named_id " n:ident : command => `(def $n:ident (x : Nat) : Nat := x)
macro "named_poly " n:ident : command => `(def $n:ident (α : Type) (x : α) : α := x)
named_id generated
named_poly poly
theorem kept : generated 5 = 5 := rfl
theorem dependent : poly Bool true = true := rfl
"#;
    assert_eq!(check(source).unwrap().1, 2);
    assert!(check(&source.replace("generated 5 = 5", "generated 5 = 99")).is_err());
}

#[test]
fn literal_declaration_names_are_fresh_in_the_invocation_namespace() {
    let source = r#"
namespace DefinitionSite
def hidden : Nat := 99
macro "make_hidden" : command => `(def hidden : Nat := 7)
end DefinitionSite
namespace Caller
make_hidden
make_hidden
end Caller
theorem unchanged : DefinitionSite.hidden = 99 := rfl
"#;
    let (engine, theorems) = check(source).unwrap();
    assert_eq!(theorems, 1);
    let generated: Vec<_> = engine
        .environment()
        .constants()
        .map(|(name, _)| name)
        .filter(|name| {
            name.has_macro_scopes()
                && name.erase_macro_scopes() == Name::from_components(["Caller", "hidden"])
        })
        .collect();
    assert_eq!(generated.len(), 2, "{generated:?}");
    assert_ne!(generated[0], generated[1]);
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let resumed = engine
        .check_source_files(
            &[br#"
namespace DefinitionSite
macro "make_hidden" : command => `(def hidden : Nat := 7)
end DefinitionSite
namespace Caller
make_hidden
end Caller
"#],
            &KVMap::new(),
            SourceCheckLimits::new(admission),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        resumed
            .engine
            .environment()
            .constants()
            .filter(|(name, _)| {
                name.has_macro_scopes()
                    && name.erase_macro_scopes() == Name::from_components(["Caller", "hidden"])
            })
            .count(),
        3
    );
}

#[test]
fn generated_self_references_cannot_resolve_to_an_existing_global() {
    for declaration in [
        "def shadow : Nat := 99\nmacro \"bad_self\" : command => `(def shadow : Nat := shadow)\nbad_self\n",
        "theorem shadow : True := True.intro\nmacro \"bad_self\" : command => `(theorem shadow : True := shadow)\nbad_self\n",
    ] {
        assert!(check(declaration).is_err(), "{declaration}");
    }
}

#[test]
fn imported_command_templates_keep_globals_and_replay_in_new_namespaces() {
    use fln::SourceModuleInput;
    use fln::source_check::modules::SourceModuleCheckLimits;

    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let limits = SourceCheckLimits::new(admission);
    let engine = Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let library = Name::from_components(["CommandLibrary"]);
    let main = Name::from_components(["CommandConsumer"]);
    let built = engine
        .check_source_modules(
            &[
                SourceModuleInput {
                    name: &library,
                    source: br#"
namespace Producer
def amount : Nat := 8
macro "make_imported " n:ident : command => `(def $n:ident : Nat := amount)
end Producer
"#,
                },
                SourceModuleInput {
                    name: &main,
                    source: br#"
import CommandLibrary
namespace Consumer
def amount : Nat := 99
make_imported generated
theorem original : generated = 8 := rfl
end Consumer
"#,
                },
            ],
            &main,
            &KVMap::new(),
            SourceModuleCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let resumed = built.checked.engine;
    let root = resumed.logical_root(&KVMap::new());
    let source = br#"
namespace Replay
def amount : Nat := 100
make_imported another
theorem originalAgain : another = 8 := rfl
end Replay
"#;
    let checked = resumed
        .check_source_files(&[source], &KVMap::new(), limits)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(checked.theorems, 1);
    assert!(
        resumed
            .check_source_files(
                &[b"make_imported wrong\ntheorem wrongProof : wrong = 99 := rfl\n"],
                &KVMap::new(),
                limits,
            )
            .is_err()
    );
    assert_eq!(resumed.logical_root(&KVMap::new()), root);
}
