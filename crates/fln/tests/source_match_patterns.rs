//! `[match_pattern]` is an executable pattern elaboration rule, not a no-op
//! attribute. Positive controls and refusals are checked at the pinned Lean
//! source semantics; every accepted native definition passes both checkers.
#![forbid(unsafe_code)]
use fln::source_check::modules::SourceModuleCheckLimits;
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, OleanCheckLimits, OleanModuleInput,
    OleanWriteBudget, SourceCheckError, SourceCheckLimits, SourceModuleInput,
};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn base() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn check(source: &str) {
    base()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
}

fn reject(source: &str) -> SourceCheckError {
    let engine = base();
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let error = engine
        .check_source_files(
            &[source.as_bytes()],
            &options,
            SourceCheckLimits::new(limits()),
        )
        .unwrap_err();
    assert!(
        !format!("{error:?}").contains("Frontend(Parse("),
        "{source}\n{error:?}"
    );
    assert_eq!(before, engine.logical_root(&options));
    error
}

#[test]
fn inline_and_standalone_tags_select_real_constructors() {
    check(
        "inductive Color where | red | blue\n\
        @[match_pattern] abbrev scarlet : Color := Color.red\n\
        def azure : Color := Color.blue\n\
        attribute [match_pattern] azure\n\
        attribute [match_pattern] azure\n\
        def classify (c : Color) : Nat := match c with | scarlet => 7 | azure => 9\n\
        theorem red_case : classify Color.red = 7 := by rfl\n\
        theorem blue_case : classify Color.blue = 9 := by rfl",
    );
}

#[test]
fn generic_aliases_preserve_nested_constructor_fields() {
    check(
        "@[match_pattern] def wrapped {α : Type} (x : α) : Option α := Option.some x\n\
        def take (v : Option (Option Nat)) : Nat := match v with\n\
        | wrapped (wrapped x) => x\n\
        | wrapped Option.none => 5\n\
        | Option.none => 9\n\
        theorem nested : take (Option.some (Option.some 7)) = 7 := by rfl\n\
        theorem inner : take (Option.some Option.none) = 5 := by rfl\n\
        theorem outer : take Option.none = 9 := by rfl",
    );
}

#[test]
fn the_pins_documented_string_alias_has_real_literal_semantics() {
    // String decisions require the actual admitted comparison/Decidable
    // definitions; the small source seed deliberately does not invent them.
    let source = "prelude\nimport Init.Prelude\n\
        @[match_pattern] def yellowString : String := \"yellow\"\n\
        def isYellow (color : String) : Bool := match color with | yellowString => true | _ => false\n\
        theorem hit : isYellow \"yellow\" = true := by rfl\n\
        theorem miss : isYellow \"blue\" = false := by rfl";
    const STACK: usize = 128 * 1024 * 1024;
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let prelude = Name::from_components(["Init", "Prelude"]);
            let imported = Engine::builder()
                .build_empty()
                .import_olean_modules_for_source(
                    &[OleanModuleInput {
                        name: &prelude,
                        artifact: include_bytes!(
                            "../../fln-conformance/fixtures/tag_attributes/prelude.olean"
                        ),
                        server_artifact: Some(include_bytes!(
                            "../../fln-conformance/fixtures/tag_attributes/prelude.olean.server"
                        )),
                        private_artifact: Some(include_bytes!(
                            "../../fln-conformance/fixtures/tag_attributes/prelude.olean.private"
                        )),
                    }],
                    std::slice::from_ref(&prelude),
                    &KVMap::new(),
                    SourceOleanImportLimits::new(OleanCheckLimits::new(
                        16 << 20,
                        Budget::for_stack_bytes(STACK),
                    )),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            let name = Name::from_components(["Main"]);
            imported
                .check_source_modules(
                    &[SourceModuleInput {
                        name: &name,
                        source: source.as_bytes(),
                    }],
                    &name,
                    &KVMap::new(),
                    SourceModuleCheckLimits::new(SourceCheckLimits::new(
                        EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)),
                    )),
                    None,
                )
                .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
                .into_complete()
                .unwrap();
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn namespace_aliases_and_named_arguments_keep_telescope_order() {
    check(
        "namespace PatternNames\n\
        inductive Pair where | mk (left right : Nat)\n\
        @[match_pattern] def swapped (left right : Nat) : Pair := Pair.mk right left\n\
        end PatternNames\n\
        open PatternNames\n\
        def first (p : Pair) : Nat := match p with | swapped (right := y) x => x\n\
        theorem reordered : first (Pair.mk 2 7) = 7 := by rfl\n\
        def ignoreRight (p : Pair) : Nat := match p with | swapped x .. => x\n\
        theorem ellipsis : ignoreRight (Pair.mk 2 7) = 7 := by rfl",
    );
}

#[test]
fn supplied_implicit_arguments_are_terms_not_pattern_bindings() {
    check(
        "@[match_pattern] def wrapped {α : Type} (x : α) : Option α := Option.some x\n\
        def take (v : Option Nat) : Nat := match v with | @wrapped Nat x => x | Option.none => 0\n\
        def takeNamed (v : Option Nat) : Nat := match v with | wrapped (α := Nat) x => x | Option.none => 0\n\
        theorem explicit_type : take (Option.some 7) = 7 := by rfl\n\
        theorem named_type : takeNamed (Option.some 8) = 8 := by rfl",
    );
    reject(
        "@[match_pattern] def wrapped {α : Type} (x : α) : Option α := Option.some x\n\
        def bad (v : Option Nat) : Nat := match v with | wrapped (α := A) x => x | Option.none => 0",
    );
    reject(
        "@[match_pattern] def wrapped {α : Type} (x : α) : Option α := Option.some x\n\
        def bad (v : Option Nat) : Nat := match v with | @wrapped Bool x => 1 | Option.none => 0",
    );
}

#[test]
fn ordinary_helpers_unfold_but_irreducible_pattern_heads_do_not() {
    check(
        "def helper (n : Nat) : Nat := Nat.succ n\n\
        @[match_pattern] def successor (n : Nat) : Nat := helper n\n\
        def previous (n : Nat) : Nat := match n with | successor p => p | 0 => 9\n\
        theorem stepped : previous 7 = 6 := by rfl\n\
        theorem zero : previous 0 = 9 := by rfl",
    );
    let error = reject(
        "@[irreducible] def hidden (n : Nat) : Nat := Nat.succ n\n\
        @[match_pattern] def successor (n : Nat) : Nat := hidden n\n\
        def bad (n : Nat) : Nat := match n with | successor p => p | _ => 0",
    );
    assert!(
        format!("{error:?}").contains("UnsupportedDefinitionPattern"),
        "{error:?}"
    );
    let error = reject(
        "@[irreducible, match_pattern] def successor (n : Nat) : Nat := Nat.succ n\n\
        def bad (n : Nat) : Nat := match n with | successor p => p | _ => 0",
    );
    assert!(
        format!("{error:?}").contains("UnsupportedDefinitionPattern"),
        "{error:?}"
    );
}

#[test]
fn reducible_nat_add_shape_drives_a_recursion_from_a_literal_argument() {
    check(
        "@[match_pattern] def addPattern (n k : Nat) : Nat := Nat.add n k\n\
        def previous (n : Nat) : Nat := match n with | addPattern p 1 => p | 0 => 9\n\
        theorem stepped : previous 8 = 7 := by rfl\n\
        theorem zero : previous 0 = 9 := by rfl",
    );
}

#[test]
fn prelude_reflexivity_aliases_infer_inaccessible_constructor_indices() {
    check(
        "namespace PreludePatterns\n\
        @[match_pattern] def rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a\n\
        end PreludePatterns\n\
        def equalityCase {α : Sort u} {a b : α} (h : Eq a b) : Nat :=\n\
          match h with | PreludePatterns.rfl => 7\n\
        theorem reflexivity : equalityCase (Eq.refl 3) = 7 := by rfl",
    );
    check(
        "namespace PreludePatterns\n\
        @[match_pattern] protected def HEq.rfl {α : Sort u} {a : α} : HEq a a := HEq.refl a\n\
        end PreludePatterns\n\
        def equalityCase {α : Sort u} {a : α} (h : HEq a a) : Nat :=\n\
          match h with | PreludePatterns.HEq.rfl => 7\n\
        theorem reflexivity : equalityCase (HEq.refl 3) = 7 := by rfl",
    );
}

#[test]
fn actual_prelude_unit_alias_elaborates_from_checked_empty_source() {
    let prelude = include_str!("../../../vendor/lean4-src/src/Init/Prelude.lean");
    let alias = "@[match_pattern] abbrev Unit.unit : Unit := PUnit.unit";
    let end = prelude.find(alias).expect("the pinned Prelude Unit alias") + alias.len();
    // Preserve the real bootstrap options, definitions, visibility, and source
    // order leading to this alias, rather than recreating its dependencies.
    let source = format!(
        "{}\ndef keep (x : Unit) : Unit := match x with | Unit.unit => Unit.unit\n",
        &prelude[..end]
    );
    let name = Name::from_components(["Init", "Prelude"]);
    Engine::builder()
        .build_empty()
        .compile_source_modules(
            &[SourceModuleInput {
                name: &name,
                source: source.as_bytes(),
            }],
            &name,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
            OleanWriteBudget::default(),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
}

#[test]
fn target_validation_arity_and_nonlinear_bindings_are_not_erased() {
    for source in [
        "attribute [match_pattern] Nat.add",
        "@[match_pattern] axiom alias : Nat",
        "@[match_pattern] opaque alias : Nat := 0",
        "@[match_pattern] theorem alias : 0 = 0 := rfl",
        "inductive Color where | red\nattribute [match_pattern] Color.red",
        "def plain (n : Nat) : Nat := Nat.succ n\ndef bad (n : Nat) : Nat := match n with | plain x => x | _ => 0",
        "@[match_pattern] def next (n : Nat) : Nat := Nat.succ n\ndef bad (n : Nat) : Nat := match n with | next => 0 | _ => 1",
        "@[match_pattern] def next (n : Nat) : Nat := Nat.succ n\ndef bad (n : Nat) : Nat := match n with | next (unknown := x) => 0 | _ => 1",
        "@[match_pattern] def ignored (n : Nat) : Nat := 0\ndef bad (n : Nat) : Nat := match n with | ignored x => 1 | _ => 2",
        "inductive Pair where | mk (left right : Nat)\n@[match_pattern] def duplicate (n : Nat) : Pair := Pair.mk n n\ndef bad (p : Pair) : Nat := match p with | duplicate x => x | _ => 0",
    ] {
        reject(source);
    }
}

#[test]
fn dependent_alias_patterns_keep_the_original_type_obligation() {
    reject(
        "inductive Vec (α : Type) : Nat -> Type where\n\
        | nil : Vec α 0\n\
        | cons (n : Nat) (head : α) (tail : Vec α n) : Vec α (Nat.succ n)\n\
        @[match_pattern] def node (n : Nat) (head : Nat) (tail : Vec Nat n) : Vec Nat (Nat.succ n) := Vec.cons n head tail\n\
        def bad (v : Vec Nat 2) : Nat := match v with | node k x _ => x",
    );
}

#[test]
fn original_alias_universes_are_checked_before_erasing_the_head() {
    check(
        "@[match_pattern] def propUnit (x : PUnit.{0}) : PUnit.{0} := x\n\
        def same (p : PUnit.{0}) : Nat := match p with | propUnit PUnit.unit => 0",
    );
    reject(
        "@[match_pattern] def propUnit (x : PUnit.{0}) : PUnit.{0} := x\n\
        def bad (p : PUnit.{1}) : Nat := match p with | propUnit PUnit.unit => 0",
    );
}

#[test]
fn repeated_holes_and_supplied_index_relationships_are_not_forgotten() {
    let repeated = reject(
        "inductive Pair where | mk (left right : Nat)\n\
        @[match_pattern] def duplicate (n : Nat) : Pair := Pair.mk n n\n\
        def bad (p : Pair) : Nat := match p with | duplicate _ => 1 | _ => 2",
    );
    assert!(
        format!("{repeated:?}").contains("UnsupportedDefinitionPattern"),
        "{repeated:?}"
    );
    let relation = reject(
        "inductive IndexedNat : Nat -> Type where | mk (n : Nat) : IndexedNat n\n\
        @[match_pattern] def packed {n : Nat} : IndexedNat n := IndexedNat.mk n\n\
        def bad (n m : Nat) (h : IndexedNat m) : Nat := match n, h with\n\
          | x, packed (n := x) => 1\n\
          | _, _ => 2",
    );
    assert!(
        format!("{relation:?}").contains("UnsupportedDefinitionPattern"),
        "{relation:?}"
    );
    check(
        "inductive IndexedNat : Nat -> Type where | mk (n : Nat) : IndexedNat n\n\
        @[match_pattern] def packed {n : Nat} : IndexedNat n := IndexedNat.mk n\n\
        def fixed (h : IndexedNat 3) : Nat := match h with | packed (n := 3) => 7\n\
        theorem fixed_case : fixed (IndexedNat.mk 3) = 7 := by rfl",
    );
}

#[test]
fn unsafe_literal_aliases_cannot_be_laundered_by_normalization() {
    // The pin accepts an unsafe head that disappears during normalization.
    // The native slice reports this as unsupported, not a reference rejection.
    check("@[match_pattern] unsafe def unsafeZero : Nat := 0");
    let error = reject(
        "@[match_pattern] unsafe def unsafeZero : Nat := 0\n\
        def bad (n : Nat) : Nat := match n with | unsafeZero => 1 | _ => 2",
    );
    assert!(
        format!("{error:?}").contains("UnsupportedDefinitionPattern"),
        "{error:?}"
    );
}

#[test]
fn module_visibility_is_checked_before_registering_a_public_pattern() {
    for source in [
        "module\nprelude\npublic inductive Color where | red\n@[match_pattern] public def alias : Color := Color.red",
        "module\nprelude\npublic inductive Color where | red\npublic def alias : Color := Color.red\nattribute [match_pattern] alias",
    ] {
        let name = Name::from_components(["Main"]);
        let error = Engine::builder()
            .build_empty()
            .compile_source_modules(
                &[SourceModuleInput {
                    name: &name,
                    source: source.as_bytes(),
                }],
                &name,
                &KVMap::new(),
                SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
                OleanWriteBudget::default(),
            )
            .unwrap_err();
        assert!(format!("{error:?}").contains("match_pattern"), "{error:?}");
    }
}
