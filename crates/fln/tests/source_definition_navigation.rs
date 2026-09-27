//! Real source-to-elaborator-to-origin joins, not a text-matching navigation mock.
#![forbid(unsafe_code)]
use fln::source_check::inspect::{DefinitionLookupLimits, SourceDefinition};
use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheckError, SourceModuleCheckLimits, SourceModuleSession,
};
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits, SourceModuleInput};

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn session() -> SourceModuleSession {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let base = Engine::with_source_seed(admission).unwrap().into_complete().unwrap();
    SourceModuleSession::new(
        base, KVMap::new(), SourceModuleCheckLimits::new(SourceCheckLimits::new(admission)),
        SourceModuleCacheLimits::default(),
    )
}
fn lookup(source: &str, at: usize) -> Option<SourceDefinition> {
    let main = name("Main");
    session().definition(&[SourceModuleInput { name: &main, source: source.as_bytes() }], &main, at)
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete().unwrap()
}

#[test]
fn same_module_reference_returns_the_explicit_definition_identifier() {
    let source = "def value : Nat := 7\ndef pending : Nat := value";
    let found = lookup(source, source.rfind("value").unwrap()).unwrap();
    assert_eq!(found.name, name("value"));
    assert_eq!(found.module, name("Main"));
    assert_eq!(found.range, 4..9);
    assert_eq!(&source[found.range], "value");
}

#[test]
fn current_namespace_beats_a_same_spelled_opened_declaration() {
    let source = "namespace A\ndef value : Nat := 1\nend A\nnamespace B\ndef value : Nat := 2\nopen A\ndef pending : Nat := value";
    let found = lookup(source, source.rfind("value").unwrap()).unwrap();
    assert_eq!(found.name, name("B.value"));
    let start = source.find("def value : Nat := 2").unwrap() + 4;
    assert_eq!(found.range, start..start + 5);
}

#[test]
fn root_qualification_is_structural_not_a_display_string_guess() {
    let source = "def value : Nat := 1\nnamespace A\ndef value : Nat := 2\ndef pending : Nat := _root_.value";
    let found = lookup(source, source.rfind("_root_.value").unwrap()).unwrap();
    assert_eq!(found.name, name("value"));
    assert_eq!(found.range, 4..9);
}

#[test]
fn local_shadowing_never_navigates_to_an_unrelated_global() {
    let source = "def value : Nat := 1\ndef pending (value : Nat) : Nat := value";
    assert!(lookup(source, source.rfind("value").unwrap()).is_none());
}

#[test]
fn seed_constant_without_a_source_origin_has_no_invented_location() {
    let source = "def pending : Nat := Nat.succ 1";
    assert!(lookup(source, source.find("Nat.succ").unwrap()).is_none());
}

#[test]
fn escaped_dots_remain_one_identifier_component() {
    let source = "def «a.b» : Nat := 1\ndef pending : Nat := «a.b»";
    let found = lookup(source, source.rfind("«a.b»").unwrap()).unwrap();
    assert_eq!(found.name, Name::from_components(["a.b"]));
    assert_eq!(&source[found.range], "«a.b»");
}

#[test]
fn declaration_locations_use_original_crlf_and_non_bmp_source_bytes() {
    let source = "-- 😀\r\nnamespace A\r\ndef value : Nat := 1\r\ndef pending : Nat := value";
    let found = lookup(source, source.rfind("value").unwrap()).unwrap();
    let at = source.find("def value").unwrap() + 4;
    assert_eq!(found.name, name("A.value"));
    assert_eq!(found.range, at..at + 5);
    assert_eq!(&source[found.range], "value");
}

#[test]
fn checked_imports_map_resolved_names_to_the_owning_module() {
    let main = name("Main");
    let lib = name("Lib");
    let source = "import Lib\nopen Library\ndef pending : Nat := value";
    let library = "namespace Library\ndef value : Nat := 3\nend Library";
    let found = session().definition(&[
        SourceModuleInput { name: &main, source: source.as_bytes() },
        SourceModuleInput { name: &lib, source: library.as_bytes() },
    ], &main, source.rfind("value").unwrap()).unwrap().into_complete().unwrap().unwrap();
    assert_eq!(found.name, name("Library.value"));
    assert_eq!(found.module, lib);
    assert_eq!(&library[found.range], "value");
}

#[test]
fn imported_source_edits_relocate_origins_without_stale_cache_hits() {
    let main = name("Main");
    let lib = name("Lib");
    let source = "import Lib\ndef pending : Nat := value";
    let mut checker = session();
    for library in ["def value : Nat := 1", "-- 😀\r\n\r\ndef value : Nat := 2"] {
        let found = checker.definition(&[
            SourceModuleInput { name: &main, source: source.as_bytes() },
            SourceModuleInput { name: &lib, source: library.as_bytes() },
        ], &main, source.rfind("value").unwrap()).unwrap().into_complete().unwrap().unwrap();
        assert_eq!(found.module, lib);
        assert_eq!(found.range.start, library.find("def value").unwrap() + 4);
        assert_eq!(&library[found.range], "value");
    }
    assert!(checker.definition(&[
        SourceModuleInput { name: &main, source: source.as_bytes() },
        SourceModuleInput { name: &lib, source: b"def removed : Nat := 2" },
    ], &main, source.rfind("value").unwrap()).is_err());
}

#[test]
fn an_invalid_prefix_is_not_navigation_authority() {
    let main = name("Main");
    let source = "theorem bad : False := by exact True.intro\ndef value : Nat := 1\ndef pending : Nat := value";
    assert!(session().definition(&[SourceModuleInput { name: &main, source: source.as_bytes() }],
        &main, source.rfind("value").unwrap()).is_err());
}

#[test]
fn declaration_body_is_not_unfolded_to_a_different_navigation_target() {
    let source = "def original : Nat := 1\ndef alias : Nat := original\ndef pending : Nat := alias";
    let found = lookup(source, source.rfind("alias").unwrap()).unwrap();
    assert_eq!(found.name, name("alias"));
    assert_eq!(found.range.start, source.find("def alias").unwrap() + 4);
}

#[test]
fn lookup_limits_and_invalid_positions_refuse_instead_of_returning_partial_locations() {
    let main = name("Main");
    let source = "-- 😀\ndef value : Nat := 1\ndef pending : Nat := value";
    let inputs = [SourceModuleInput { name: &main, source: source.as_bytes() }];
    let at = source.rfind("value").unwrap();
    for limits in [
        DefinitionLookupLimits { max_source_bytes: 1, ..DefinitionLookupLimits::default() },
        DefinitionLookupLimits { max_modules: 0, ..DefinitionLookupLimits::default() },
        DefinitionLookupLimits { max_commands: 0, ..DefinitionLookupLimits::default() },
        DefinitionLookupLimits { max_head_steps: 0, ..DefinitionLookupLimits::default() },
    ] {
        assert!(matches!(session().definition_with_limits(&inputs, &main, at, limits),
            Err(SourceModuleCheckError::Limit { .. })));
    }
    assert!(session().definition(&inputs, &main, source.len() + 1).is_err());
    assert!(session().definition(&inputs, &main, source.find('😀').unwrap() + 1).is_err());
}
