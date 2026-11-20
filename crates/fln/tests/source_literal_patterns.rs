//! Literal decisions preserve ordered rows and kernel typing obligations.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(source: &str) {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
}
fn reject(source: &str) {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let result = engine.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    assert!(
        result.is_err(),
        "invalid literal pattern accepted: {source}"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}
#[test]
fn natural_equations_have_exact_ordered_matches_and_a_real_fallback() {
    check(
        "def digit : Nat -> Nat | 0 => 7 | 1 => 9 | n => n + 10\n\
        theorem zero : digit 0 = 7 := by rfl\n\
        theorem one : digit 1 = 9 := by rfl\n\
        theorem other : digit 12 = 22 := by rfl",
    );
}
#[test]
fn arbitrary_precision_literals_are_not_unary_patterns() {
    check(
        "def large : Nat -> Nat | 340282366920938463463374607431768211456 => 17 | _ => 19\n\
        theorem yes : large 340282366920938463463374607431768211456 = 17 := by rfl\n\
        theorem no : large 340282366920938463463374607431768211457 = 19 := by rfl",
    );
}
#[test]
fn different_literal_spellings_are_compared_by_value() {
    check("def value : Nat -> Nat | 0x10 => 7 | _ => 9\n theorem same : value 16 = 7 := by rfl");
    for duplicate in ["0x10", "0b10000", "0o20", "1_6"] {
        reject(&format!(
            "def duplicate : Nat -> Nat | 16 => 1 | {duplicate} => 2 | _ => 3"
        ));
    }
}
#[test]
fn string_patterns_do_not_invent_an_unchecked_comparison_rule() {
    for source in [
        r#"def code : String -> Nat | "a\nb" => 7 | _ => 9"#,
        r##"def code : String -> Nat | r#"🦀"# => 9 | _ => 11"##,
    ] {
        reject(source);
    }
}
#[test]
fn mixed_literal_columns_retain_first_row_priority_and_bindings() {
    check(
        "def code : Nat -> Bool -> Nat | 1, true => 7 | _, true => 9 | 1, false => 11 | n, false => n\n\
        theorem first : code 1 true = 7 := by rfl\n\
        theorem second : code 3 true = 9 := by rfl\n\
        theorem third : code 1 false = 11 := by rfl\n\
        theorem last : code 12 false = 12 := by rfl",
    );
}
#[test]
fn literals_inside_constructor_payloads_use_the_same_matrix() {
    check(
        "inductive Maybe (A : Type) where | none | some (value : A)\n\
        def code : Maybe Nat -> Nat | .none => 0 | .some 7 => 1 | .some x => x\n\
        theorem selected : code (Maybe.some 7) = 1 := by rfl\n\
        theorem fallback : code (Maybe.some 9) = 9 := by rfl",
    );
}
#[test]
fn literal_and_constructor_overlap_preserves_order_without_large_expansion() {
    check(
        "def code : Nat -> Nat | 0 => 7 | .succ 340282366920938463463374607431768211456 => 9 | .succ k => k\n\
        theorem zero : code 0 = 7 := by rfl\n\
        theorem huge : code 340282366920938463463374607431768211457 = 9 := by rfl\n\
        theorem other : code 20 = 19 := by rfl",
    );
}
#[test]
fn literal_zero_keeps_the_structural_predecessor_available_for_recursion() {
    check(
        "def copy : Nat -> Nat | 0 => 0 | .succ k => Nat.succ (copy k)\n\
        theorem computed : copy 7 = 7 := by rfl\n\
        def withFlag : Bool -> Nat -> Nat | _, 0 => 0 | b, .succ k => Nat.succ (withFlag b k)\n\
        theorem later : withFlag false 4 = 4 := by rfl",
    );
}
#[test]
fn literal_pattern_functions_are_checked_higher_order_arguments() {
    check(
        "def apply (f : Nat -> Nat) (n : Nat) : Nat := f n\n\
        theorem used : apply (fun | 7 => 11 | _ => 13) 7 = 11 := by rfl",
    );
}
#[test]
fn finite_literal_rows_do_not_prove_coverage_even_for_a_closed_input() {
    for source in [
        "def bad : Nat := match 0 with | 0 => 7",
        "def bad : String -> Nat | \"a\" => 0 | \"b\" => 1",
    ] {
        reject(source);
    }
}
#[test]
fn wrong_literal_domains_and_foreign_constructor_patterns_are_not_erased() {
    for source in [
        "def bad : Bool -> Nat | 0 => 1 | _ => 2",
        "def bad : Nat -> Nat | \"a\" => 1 | _ => 2",
        "def bad : Nat -> Nat | 0 => 1 | \"a\" => 2 | _ => 3",
        "inductive Other where | zero | succ (n : Nat)\ndef bad : Other -> Nat | 0 => 1 | Other.succ k => k",
    ] {
        reject(source);
    }
}
#[test]
fn unused_discriminants_annotations_and_shadowed_intrinsic_names_stay_checked() {
    reject("def bad : Nat := match (1 : String) with | 0 => 0 | _ => 1");
    reject("def bad : Nat -> Nat | 0 => 7 | _ => let invalid := (1 : String); 9");
    reject("def bad : Nat -> Nat | _ => 7 | 0 => (1 : String)");
    check(
        "def good (beq : Nat) : Nat := match 7 with | 7 => beq | _ => 0\n theorem same : good 9 = 9 := by rfl",
    );
}
#[test]
fn boolean_comparisons_do_not_fabricate_dependent_equalities() {
    reject("theorem bad (n : Nat) : n = 0 := match n with | 0 => rfl | _ => rfl");
    check("def retain (n : Nat) (h : n = n) : n = n := match n with | 0 => h | _ => h");
}
#[test]
fn recursive_calls_hidden_in_literal_alternatives_remain_termination_obligations() {
    reject("def bad : Nat -> Nat | 0 => 0 | n => bad n");
    reject("def bad : Nat -> Nat | 0 => let unused := bad 0; 0 | .succ k => bad k");
}

#[test]
fn indexed_empty_matching_searches_only_bounded_selected_evidence() {
    check(
        "inductive Step : Nat -> Prop where | next (n : Nat) (h : Step n) : Step (Nat.succ n)\n\
         theorem emptyStep (h : Step 3) : False := nomatch h",
    );
    let prefix = "inductive Loop : Nat -> Prop where | next (n : Nat) (h : Loop n) : Loop n\n";
    check(prefix);
    for source in [
        "theorem noUnboundedSearch (h : Loop 0) : False := nomatch h",
        "def noAmbientProof (ambient : False) (n : Nat) : Nat := nomatch n",
    ] {
        reject(&format!("{prefix}{source}"));
    }
}

#[test]
fn same_named_finite_types_do_not_erase_data_or_unrelated_proofs() {
    for (field_type, field_value) in [("Bool", "true"), ("True", "True.intro")] {
        let prefix = format!(
            "inductive Fin (n : Nat) where | mk (value : Nat) (extra : {field_type})\n\
             instance : OfNat (Fin 3) 0 where ofNat := Fin.mk 0 {field_value}\n"
        );
        check(&prefix);
        let source =
            format!("{prefix}def code (x : Fin 3) : Nat := match x with | 0 => 1 | _ => 2");
        let engine = engine();
        let root = engine.logical_root(&KVMap::new());
        let error = engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect_err("a same-named constructor is not the canonical Fin model");
        assert_eq!(
            error.disposition(),
            ("capability", false, 5),
            "{source}\n{error:?}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn finite_literals_use_the_actual_imported_bounds_and_instances() {
    use fln::source_check::modules::imported::SourceOleanImportLimits;
    use fln::{Name, OleanCheckLimits, OleanDecodeLimits, OleanModuleInput, olean_module_imports};
    use std::collections::BTreeSet;
    use std::path::PathBuf;

    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|path| path.join("Init/Data/Fin/Basic.olean").is_file());
    let Some(library) = library else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "FLN_REQUIRE_REFERENCE is set but the pinned Fin library is absent"
        );
        eprintln!("SKIP: Fin literals require the pinned Reference library");
        return;
    };
    const STACK: usize = 256 * 1024 * 1024;
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let root = Name::from_components(["Init", "Data", "Fin", "Basic"]);
            let mut pending = vec![root.clone()];
            let mut seen = BTreeSet::new();
            let mut names = Vec::new();
            let mut parts = Vec::new();
            while let Some(module) = pending.pop() {
                if !seen.insert(module.clone()) {
                    continue;
                }
                let path = module
                    .to_display_string()
                    .split('.')
                    .fold(library.clone(), |path, part| path.join(part))
                    .with_extension("olean");
                let exported = std::fs::read(&path).unwrap();
                pending.extend(
                    olean_module_imports(&exported, OleanDecodeLimits::new(exported.len()))
                        .unwrap(),
                );
                parts.push([
                    exported,
                    std::fs::read(path.with_extension("olean.server")).unwrap(),
                    std::fs::read(path.with_extension("olean.private")).unwrap(),
                ]);
                names.push(module);
            }
            let inputs: Vec<_> = names
                .iter()
                .zip(&parts)
                .map(|(name, [exported, server, private])| OleanModuleInput {
                    name,
                    artifact: exported,
                    server_artifact: Some(server),
                    private_artifact: Some(private),
                })
                .collect();
            let budget = Budget::for_stack_bytes(STACK);
            let engine = Engine::builder()
                .build_empty()
                .import_olean_modules_for_source(
                    &inputs,
                    &[root],
                    &KVMap::new(),
                    SourceOleanImportLimits::new(OleanCheckLimits::new(STACK, budget)),
                )
                .unwrap()
                .into_complete()
                .unwrap()
                .engine;
            let options = KVMap::new();
            let initial_root = engine.logical_root(&options);
            let check = |source: &str| {
                let result = engine.check_source_files(
                    &[source.as_bytes()],
                    &options,
                    SourceCheckLimits::new(EngineAdmissionLimits::new(budget)),
                );
                assert_eq!(engine.logical_root(&options), initial_root, "{source}");
                result
            };
            for source in [
                // `boo` is the literal Fin match in the pin's matchSparse2.lean.
                "def boo (x : Fin 3) : Nat := match x with | 0 => 1 | 1 => 2 | 2 => 4\n\
                 theorem zero : boo 0 = 1 := by rfl\n\
                 theorem one : boo 1 = 2 := by rfl\n\
                 theorem two : boo 2 = 4 := by rfl",
                "def wrap : Fin 3 -> Nat | 3 => 1 | 4 => 2 | 5 => 4\n\
                 theorem zero : wrap 0 = 1 := by rfl\n\
                 theorem one : wrap 1 = 2 := by rfl\n\
                 theorem two : wrap 2 = 4 := by rfl",
                "def singleton (x : Fin 1) : Nat := match x with | 0 => 9\n\
                 theorem value : _root_.singleton 0 = 9 := by rfl",
                "def sparse (x : Fin 5) : Nat := match x with | 4 => 11 | _ => 13\n\
                 theorem selected : sparse 4 = 11 := by rfl\n\
                 theorem fallback : sparse 0 = 13 := by rfl",
                "def large (x : Fin 3) : Nat := match x with\n\
                 | 0 => 1 | 340282366920938463463374607431768211456 => 2 | 2 => 4\n\
                 theorem value : large 1 = 2 := by rfl",
                "def combine (x : Fin 2) (b : Bool) : Nat := match x, b with\n\
                 | 0, false => 11 | 0, true => 12 | 1, false => 21 | 1, true => 22\n\
                 theorem first : combine 0 true = 12 := by rfl\n\
                 theorem last : combine 1 false = 21 := by rfl",
                "abbrev Three := Fin 3\n\
                 def alias (x : Three) : Nat := match x with | 0 => 1 | 1 => 2 | 2 => 4\n\
                 theorem value : alias 2 = 4 := by rfl",
            ] {
                check(source)
                    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
                    .into_complete()
                    .unwrap_or_else(|outcome| panic!("{source}\n{outcome:?}"));
            }
            // Reuse the same admitted Fin environment through the normal
            // compiler, bytecode codec, and VM. Bounds are proof-only fields;
            // the generated impossible branch must also survive erasure.
            let runtime_source = b"def compiledFin (x : Fin 3) : Nat := match x with | 0 => 1 | 1 => 2 | 2 => 4\n\
                #eval compiledFin 0\n#eval compiledFin 1\n#eval compiledFin 2\n#eval compiledFin 3";
            let executed = engine
                .execute_source_commands_with_checks(
                    runtime_source,
                    &options,
                    fln::EngineExecutionLimits::new(budget),
                )
                .unwrap_or_else(|error| panic!("finite matching runtime: {error:?}"))
                .into_complete()
                .unwrap_or_else(|outcome| panic!("finite matching runtime: {outcome:?}"));
            let actual: Vec<_> = executed
                .batch
                .source_evaluation_indices
                .iter()
                .map(|&index| {
                    let fln::VmExit::Returned(value) = &executed.batch.executions[index].exit else {
                        panic!("finite matching evaluation must return")
                    };
                    fln_vm::interpreter::nat_decimal(&value.value).expect("Nat result")
                })
                .collect();
            assert_eq!(actual, ["1", "2", "4", "1"]);
            assert_eq!(engine.logical_root(&options), initial_root);

            for source in [
                "def missing (x : Fin 3) : Nat := match x with | 0 => 1 | 1 => 2",
                "def missing (h : False) (x : Fin 3) : Nat := match x with | 0 => 1 | 1 => 2",
                "def duplicate (x : Fin 3) : Nat := match x with | 0 => 1 | 3 => 2 | 1 => 3 | 2 => 4",
                "def missing (x : Fin 2) (b : Bool) : Nat := match x, b with\n\
                 | 0, false => 11 | 0, true => 12 | 1, false => 21",
                "def emptyLiteral (x : Fin 0) : Nat := match x with | 0 => 1",
                "def hugeBound (x : Fin 340282366920938463463374607431768211456) : Nat := match x with | 0 => 1",
            ] {
                assert!(check(source).is_err(), "invalid finite coverage accepted: {source}");
            }
            // These are capability stops, never decided rejections of the
            // source. A changed dictionary requires the pin's original RHS
            // typing witness even though its value patterns are canonicalized.
            for source in [
                "local instance changedZero : OfNat (Fin 3) 0 where ofNat := ⟨1, by decide⟩\n\
                 def changed (x : Fin 3) : Nat := match x with | 0 => 10 | 1 => 20 | 2 => 30",
                "def symbolic (n : Nat) [NeZero n] (x : Fin n) : Nat := match x with | 0 => 1 | _ => 2",
            ] {
                let error = check(source).expect_err("unsupported Fin lowering must remain a nonanswer");
                assert_eq!(error.disposition(), ("capability", false, 5), "{source}\n{error:?}");
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
