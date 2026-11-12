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
fn navigation_covers_axioms_data_headers_constructors_fields_and_named_instances() {
    for (source, reference, target, spelling) in [
        (
            "axiom witness : Nat\ndef pending : Nat := witness",
            "witness",
            "witness",
            "witness",
        ),
        (
            "opaque hidden : Nat := 7\ndef pending : Nat := hidden",
            "hidden",
            "hidden",
            "hidden",
        ),
        (
            "inductive Choice where\n| left\n| right\ndef pending : Type := Choice",
            "Choice",
            "Choice",
            "Choice",
        ),
        (
            "inductive Choice where\n| left\n| right\ndef pending : Choice := Choice.right",
            "Choice.right",
            "Choice.right",
            "right",
        ),
        (
            "structure Box where\n  value : Nat\ndef pending : Type := Box",
            "Box",
            "Box",
            "Box",
        ),
        (
            "structure Box where\n  value : Nat\ndef pending (box : Box) : Nat := Box.value box",
            "Box.value",
            "Box.value",
            "value",
        ),
        (
            "structure Box where\n  value : Nat\ndef pending (box : Box) : Nat := box.value",
            "box.value",
            "Box.value",
            "value",
        ),
        (
            "class Reader where\n  read : Nat\ndef pending : Type := Reader",
            "Reader",
            "Reader",
            "Reader",
        ),
        (
            "class Reader where\n  read : Nat\ndef pending (reader : Reader) : Nat := @Reader.read reader",
            "Reader.read",
            "Reader.read",
            "read",
        ),
        (
            "class Reader where\n  read : Nat\ninstance configured : Reader := ⟨7⟩\ndef pending : Reader := configured",
            "configured",
            "configured",
            "configured",
        ),
    ] {
        let found = lookup(source, source.rfind(reference).unwrap())
            .unwrap_or_else(|| panic!("missing origin for {target}: {source}"));
        assert_eq!(found.name, name(target), "{source}");
        assert_eq!(&source[found.range], spelling, "{source}");
    }
}

#[test]
fn navigation_keeps_private_identity_and_mutual_member_origins() {
    let private = Name::num(name("_private.Main"), 0);
    for (source, reference, target) in [
        (
            "private def hidden : Nat := 1\ndef pending : Nat := hidden",
            "hidden",
            private.append_core(&name("hidden")),
        ),
        (
            "module\nprelude\nnamespace N\ninductive Choice where\n| left\ndef pending : Choice := Choice.left",
            "Choice.left",
            private.append_core(&name("N.Choice.left")),
        ),
        (
            "namespace N\nmutual\n  def first : Nat := 1\n  def second : Nat := 2\nend\ndef pending : Nat := second",
            "second",
            name("N.second"),
        ),
    ] {
        let found = lookup(source, source.rfind(reference).unwrap()).unwrap();
        assert_eq!(found.name, target);
        assert_eq!(&source[found.range], reference.rsplit('.').next().unwrap());
    }
}

#[test]
fn navigation_replays_local_grammar_before_locating_a_checked_declaration() {
    let source = r#"syntax "fixed!" : term
macro_rules | `(fixed!) => `((7 : Nat))
section
local notation "twice!" x => Nat.add x x
def value : Nat := twice! fixed!
end
def pending : Nat := value
"#;
    let found = lookup(source, source.rfind("value").unwrap()).unwrap();
    assert_eq!(found.name, name("value"));
    assert_eq!(found.range.start, source.find("def value").unwrap() + 4);
}

#[test]
fn imported_constructor_origins_keep_escaped_components_and_original_bytes() {
    let main = name("Main");
    let lib = name("Lib");
    let library = "-- 😀\r\nnamespace N\r\ninductive Choice where\r\n  | «a.b»\r\nend N\r\n";
    let source = "import Lib\ndef pending : N.Choice := N.Choice.«a.b»";
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
            source.rfind("N.Choice.«a.b»").unwrap(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .unwrap();
    assert_eq!(found.name, Name::from_components(["N", "Choice", "a.b"]));
    assert_eq!(found.module, lib);
    assert_eq!(&library[found.range], "«a.b»");
}

#[test]
fn imported_origins_replay_their_own_transitive_grammar_without_sibling_modules() {
    let main = name("Main");
    let lib = name("Lib");
    let grammar = name("Grammar");
    let sibling = name("Sibling");
    let source = "import Lib\nimport Sibling\ndef pending : Nat := value";
    let library = "import Grammar\ndef value : Nat := select! (Nat.add 1 2)";
    let grammar_source = r#"syntax "select! " term:max : term
macro_rules | `(select! (Nat.add $x $y)) => `($x)
"#;
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
                SourceModuleInput {
                    name: &grammar,
                    source: grammar_source.as_bytes(),
                },
                SourceModuleInput {
                    name: &sibling,
                    source: b"def unrelated : Nat := 0",
                },
            ],
            &main,
            source.rfind("value").unwrap(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .unwrap();
    assert_eq!(found.name, name("value"));
    assert_eq!(found.module, lib);
    assert_eq!(&library[found.range], "value");
}

#[test]
fn generated_constructor_and_shadowed_field_do_not_invent_origins() {
    let generated = "structure Box where\n  value : Nat\ndef pending : Box := Box.mk 7";
    assert!(lookup(generated, generated.rfind("Box.mk").unwrap()).is_none());
    let shadowed = "structure Box where\n  value : Nat\ndef pending (value : Nat) : Nat := value";
    assert!(lookup(shadowed, shadowed.rfind("value").unwrap()).is_none());
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
fn navigation_bounds_the_whole_checked_closure_after_finding_a_target() {
    let main = name("Main");
    let lib = name("Lib");
    let source = "import Lib\ndef other : Nat := 2\ndef pending : Nat := value";
    let inputs = [
        SourceModuleInput {
            name: &main,
            source: source.as_bytes(),
        },
        SourceModuleInput {
            name: &lib,
            source: b"def value : Nat := 1",
        },
    ];
    assert!(matches!(
        session().definition_with_limits(
            &inputs,
            &main,
            source.rfind("value").unwrap(),
            DefinitionLookupLimits {
                max_commands: 1,
                ..DefinitionLookupLimits::default()
            },
        ),
        Err(SourceModuleCheckError::Limit {
            resource: "definition commands",
            limit: 1,
        })
    ));
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
            name("N.Choice.left"),
            name("N.Choice.right"),
            name("N.Box"),
            name("N.Box.value"),
            name("N.Witness"),
        ]
    );
    for (symbol, spelling) in symbols.iter().zip([
        "first", "second", "Choice", "left", "right", "Box", "value", "Witness",
    ]) {
        assert_eq!(&source[symbol.selection_range.clone()], spelling);
    }
    assert_eq!(&source[symbols[0].range.clone()], "def first : Nat := 1");
    assert_eq!(&source[symbols[1].range.clone()], "def second : Nat := 2");
}

#[test]
fn document_outline_lists_grouped_and_class_fields_without_inherited_helpers() {
    let main = name("Main");
    let source = "-- 😀\r\nnamespace N\r\nstructure Base where\r\n  value : Nat\r\nstructure Pair extends Base where\r\n  (left right : Nat)\r\n  value := 1\r\nclass Reader where\r\n  read : Nat\r\nend N\r\n";
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
            name("N.Base"),
            name("N.Base.value"),
            name("N.Pair"),
            name("N.Pair.left"),
            name("N.Pair.right"),
            name("N.Reader"),
            name("N.Reader.read"),
        ]
    );
    for (symbol, spelling) in symbols
        .iter()
        .zip(["Base", "value", "Pair", "left", "right", "Reader", "read"])
    {
        assert_eq!(&source[symbol.selection_range.clone()], spelling);
        assert!(symbol.range.start <= symbol.selection_range.start);
        assert!(symbol.selection_range.end <= symbol.range.end);
        assert!(!source[symbol.range.clone()].ends_with('\r'));
    }
    assert_eq!(&source[symbols[3].range.clone()], "(left right : Nat)");
    assert_eq!(symbols[3].range, symbols[4].range);
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
