//! Real source-to-elaborator-to-origin joins, not a text-matching navigation mock.
#![forbid(unsafe_code)]
use fln::source_check::inspect::{DefinitionLookupLimits, DocumentSymbolLimits, SourceDefinition};
use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheckError, SourceModuleCheckLimits, SourceModuleSession,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits, SourceModuleInput,
};

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn session() -> SourceModuleSession {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let base = Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    SourceModuleSession::new(
        base,
        KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(admission)),
        SourceModuleCacheLimits::default(),
    )
}
fn lookup(source: &str, at: usize) -> Option<SourceDefinition> {
    let main = name("Main");
    session()
        .definition(
            &[SourceModuleInput {
                name: &main,
                source: source.as_bytes(),
            }],
            &main,
            at,
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
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
    let found = session()
        .definition(
            &[
                SourceModuleInput {
                    name: &main,
                    source: source.as_bytes(),
                },
                SourceModuleInput {
                    name: &lib,
                    source: library.as_bytes(),
                },
            ],
            &main,
            source.rfind("value").unwrap(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .unwrap();
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
        let found = checker
            .definition(
                &[
                    SourceModuleInput {
                        name: &main,
                        source: source.as_bytes(),
                    },
                    SourceModuleInput {
                        name: &lib,
                        source: library.as_bytes(),
                    },
                ],
                &main,
                source.rfind("value").unwrap(),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .unwrap();
        assert_eq!(found.module, lib);
        assert_eq!(found.range.start, library.find("def value").unwrap() + 4);
        assert_eq!(&library[found.range], "value");
    }
    assert!(
        checker
            .definition(
                &[
                    SourceModuleInput {
                        name: &main,
                        source: source.as_bytes()
                    },
                    SourceModuleInput {
                        name: &lib,
                        source: b"def removed : Nat := 2"
                    },
                ],
                &main,
                source.rfind("value").unwrap()
            )
            .is_err()
    );
}

#[test]
fn an_invalid_prefix_is_not_navigation_authority() {
    let main = name("Main");
    let source = "theorem bad : False := by exact True.intro\ndef value : Nat := 1\ndef pending : Nat := value";
    assert!(
        session()
            .definition(
                &[SourceModuleInput {
                    name: &main,
                    source: source.as_bytes()
                }],
                &main,
                source.rfind("value").unwrap()
            )
            .is_err()
    );
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
    let inputs = [SourceModuleInput {
        name: &main,
        source: source.as_bytes(),
    }];
    let at = source.rfind("value").unwrap();
    for limits in [
        DefinitionLookupLimits {
            max_source_bytes: 1,
            ..DefinitionLookupLimits::default()
        },
        DefinitionLookupLimits {
            max_modules: 0,
            ..DefinitionLookupLimits::default()
        },
        DefinitionLookupLimits {
            max_commands: 0,
            ..DefinitionLookupLimits::default()
        },
        DefinitionLookupLimits {
            max_head_steps: 0,
            ..DefinitionLookupLimits::default()
        },
    ] {
        assert!(matches!(
            session().definition_with_limits(&inputs, &main, at, limits),
            Err(SourceModuleCheckError::Limit { .. })
        ));
    }
    assert!(
        session()
            .definition(&inputs, &main, source.len() + 1)
            .is_err()
    );
    assert!(
        session()
            .definition(&inputs, &main, source.find('😀').unwrap() + 1)
            .is_err()
    );
}

#[test]
fn document_outline_uses_checked_qualified_names_and_original_declaration_ranges() {
    let main = name("Main");
    let source = "-- 😀\r\nnamespace Outer\r\nnamespace Inner\r\ndef value : Nat := 7\r\ntheorem identity (P : Prop) (h : P) : P := h\r\nend Inner\r\nprivate def hidden : Nat := 8\r\nend Outer\r\ndef «a.b» : Nat := 1\r\n";
    let symbols = session()
        .document_symbols(
            &[SourceModuleInput {
                name: &main,
                source: source.as_bytes(),
            }],
            &main,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        symbols
            .iter()
            .map(|symbol| symbol.name.clone())
            .collect::<Vec<_>>(),
        [
            name("Outer.Inner.value"),
            name("Outer.Inner.identity"),
            name("Outer.hidden"),
            Name::from_components(["a.b"]),
        ]
    );
    for (symbol, spelling) in symbols.iter().zip(["value", "identity", "hidden", "«a.b»"]) {
        assert_eq!(&source[symbol.selection_range.clone()], spelling);
        assert!(symbol.range.start <= symbol.selection_range.start);
        assert!(symbol.selection_range.end <= symbol.range.end);
        assert!(!source[symbol.range.clone()].ends_with('\r'));
    }
    assert_eq!(&source[symbols[0].range.clone()], "def value : Nat := 7");
}

#[test]
fn document_outline_excludes_imports_locals_and_anonymous_declarations() {
    let main = name("Main");
    let lib = name("Lib");
    let source = "import Lib\ndef localValue (parameter : Nat) : Nat := parameter\nexample : Nat := localValue 4\n";
    let symbols = session()
        .document_symbols(
            &[
                SourceModuleInput {
                    name: &main,
                    source: source.as_bytes(),
                },
                SourceModuleInput {
                    name: &lib,
                    source: b"def imported : Nat := 1",
                },
            ],
            &main,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(symbols.len(), 1);
    assert_eq!(symbols[0].name, name("localValue"));
    assert_eq!(&source[symbols[0].selection_range.clone()], "localValue");
}

#[test]
fn document_outline_rechecks_replacements_and_never_returns_old_success_on_failure() {
    let main = name("Main");
    let mut checker = session();
    for (source, expected) in [
        ("def first : Nat := 1", "first"),
        ("-- relocated\ndef second : Nat := 2", "second"),
    ] {
        let symbols = checker
            .document_symbols(
                &[SourceModuleInput {
                    name: &main,
                    source: source.as_bytes(),
                }],
                &main,
            )
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(symbols.len(), 1);
        assert_eq!(symbols[0].name, name(expected));
        assert_eq!(&source[symbols[0].selection_range.clone()], expected);
    }
    assert!(
        checker
            .document_symbols(
                &[SourceModuleInput {
                    name: &main,
                    source: b"theorem invalid : False := by exact True.intro",
                }],
                &main
            )
            .is_err()
    );
    let empty = checker
        .document_symbols(
            &[SourceModuleInput {
                name: &main,
                source: b"-- an empty source outline",
            }],
            &main,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(empty.is_empty());
}

#[test]
fn document_outline_has_independent_source_command_and_traversal_bounds() {
    let main = name("Main");
    let inputs = [SourceModuleInput {
        name: &main,
        source: b"def value : Nat := 1",
    }];
    for limits in [
        DocumentSymbolLimits {
            max_modules: 0,
            ..DocumentSymbolLimits::default()
        },
        DocumentSymbolLimits {
            max_source_bytes: 1,
            ..DocumentSymbolLimits::default()
        },
        DocumentSymbolLimits {
            max_commands: 0,
            ..DocumentSymbolLimits::default()
        },
        DocumentSymbolLimits {
            max_syntax_nodes: 0,
            ..DocumentSymbolLimits::default()
        },
    ] {
        assert!(matches!(
            session().document_symbols_with_limits(&inputs, &main, limits),
            Err(SourceModuleCheckError::Limit { .. })
        ));
    }
}

#[test]
fn document_outline_bounds_replay_work_inside_temporary_scopes() {
    let main = name("Main");
    let inputs = [SourceModuleInput {
        name: &main,
        source: b"open Nat in def value : Nat := 1",
    }];
    assert!(matches!(
        session().document_symbols_with_limits(
            &inputs,
            &main,
            DocumentSymbolLimits {
                max_commands: 1,
                ..DocumentSymbolLimits::default()
            }
        ),
        Err(SourceModuleCheckError::Limit {
            resource: "document symbol commands",
            limit: 1
        })
    ));
    let symbols = session()
        .document_symbols_with_limits(
            &inputs,
            &main,
            DocumentSymbolLimits {
                max_commands: 2,
                ..DocumentSymbolLimits::default()
            },
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(symbols.len(), 1);
    assert_eq!(symbols[0].name, name("value"));
}

#[test]
fn document_outline_preserves_each_mutual_member_and_data_declaration_header() {
    let main = name("Main");
    let source = "namespace N\r\nmutual\r\n  def first : Nat := 1\r\n  def second : Nat := 2\r\nend\r\ninductive Choice where\r\n  | left\r\n  | right\r\nstructure Box where\r\n  value : Nat\r\naxiom Witness : Prop\r\nend N\r\n";
    let symbols = session()
        .document_symbols(
            &[SourceModuleInput {
                name: &main,
                source: source.as_bytes(),
            }],
            &main,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        symbols
            .iter()
            .map(|symbol| symbol.name.clone())
            .collect::<Vec<_>>(),
        [
            name("N.first"),
            name("N.second"),
            name("N.Choice"),
            name("N.Box"),
            name("N.Witness"),
        ]
    );
    for (symbol, spelling) in symbols
        .iter()
        .zip(["first", "second", "Choice", "Box", "Witness"])
    {
        assert_eq!(&source[symbol.selection_range.clone()], spelling);
    }
    assert_eq!(&source[symbols[0].range.clone()], "def first : Nat := 1");
    assert_eq!(&source[symbols[1].range.clone()], "def second : Nat := 2");
}

#[test]
fn document_outline_replays_imported_syntax_and_file_local_notation() {
    let main = name("Main");
    let lib = name("Lib");
    let source = r#"import Lib
section
local notation "⟪" x "⟫" => Nat.add x x
theorem local_works : ⟪(2 : Nat)⟫ = 4 := rfl
end
theorem imported_works : select! (Nat.add 5 6) = (5 : Nat) := rfl
"#;
    let library = r#"syntax "select! " term:max : term
macro_rules | `(select! (Nat.add $x $y)) => `($x)
"#;
    let symbols = session()
        .document_symbols(
            &[
                SourceModuleInput {
                    name: &main,
                    source: source.as_bytes(),
                },
                SourceModuleInput {
                    name: &lib,
                    source: library.as_bytes(),
                },
            ],
            &main,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        symbols
            .iter()
            .map(|symbol| symbol.name.clone())
            .collect::<Vec<_>>(),
        [name("local_works"), name("imported_works")]
    );
    for (symbol, spelling) in symbols.iter().zip(["local_works", "imported_works"]) {
        assert_eq!(&source[symbol.selection_range.clone()], spelling);
    }
}

#[test]
fn document_outline_restores_local_grammar_between_declarations() {
    let main = name("Main");
    let source = r#"syntax "localValue! " num : term
macro_rules | `(localValue! $n:num) => `($n)
section Outer
local macro_rules | `(localValue! 0) => `((10 : Nat))
theorem outer_before : localValue! 0 = (10 : Nat) := rfl
section Inner
local macro_rules | `(localValue! 0) => `((20 : Nat))
theorem inner : localValue! 0 = (20 : Nat) := rfl
end Inner
theorem outer_after : localValue! 0 = (10 : Nat) := rfl
end Outer
theorem outside : localValue! 0 = (0 : Nat) := rfl
"#;
    let symbols = session()
        .document_symbols(
            &[SourceModuleInput {
                name: &main,
                source: source.as_bytes(),
            }],
            &main,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        symbols
            .iter()
            .map(|symbol| symbol.name.clone())
            .collect::<Vec<_>>(),
        [
            name("outer_before"),
            name("inner"),
            name("outer_after"),
            name("outside")
        ]
    );
}
