//! Default source candidates fill unknown inputs after ordinary synthesis and
//! retain the pin's independent priority, chronology and visibility semantics.
#![forbid(unsafe_code)]

use fln::source_check::modules::SourceModuleCheckLimits;
use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name,
    SourceCheckLimits, SourceModuleInput,
};
use fln_elab::instances::{InstanceRegistry, InstanceRegistryError, defaults};

fn n(name: &str) -> Name {
    Name::from_components(name.split('.'))
}

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
        .engine
}

fn owned_defaults(before: &Engine, after: &Engine) -> Vec<defaults::DefaultInstance> {
    let prior = defaults::read(before.environment()).unwrap();
    let rows = defaults::read(after.environment()).unwrap();
    let mut inherited = Vec::new();
    let mut owned = Vec::new();
    for mut row in rows {
        if row.candidate.order < prior.len() {
            inherited.push(row);
        } else {
            // Test chronology within this source suffix while retaining and
            // checking every pre-existing seed row verbatim.
            row.candidate.order -= prior.len();
            owned.push(row);
        }
    }
    assert_eq!(inherited, prior, "source defaults changed inherited rows");
    owned
}

const PROVIDER: &str = "class Provider (A : Type) where
  value : A
def supplied {A : Type} [Provider A] : A := Provider.value";

fn evaluated(base: &Engine, source: &str, expected: &str) {
    let result = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(result) = &result.executions.last().unwrap().exit else {
        panic!("source default application did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some(expected)
    );
}

#[test]
fn inline_and_standalone_defaults_resume_real_unknown_callable_applications() {
    for registration in [
        "@[default_instance] def callable : Provider ((n : Nat) -> Nat) := { value := fun n => n + 22 }",
        "def callable : Provider ((n : Nat) -> Nat) := { value := fun n => n + 22 }\nattribute [default_instance] callable",
    ] {
        // An attribute introduced inside the execution batch must reach
        // admission before the later unknown application is elaborated.
        let provider = checked(&engine(), PROVIDER);
        evaluated(
            &provider,
            &format!(
                "{registration}\ndef batchAnswer : Nat := let f : _ := supplied; f (n := 20)\n#eval batchAnswer"
            ),
            "42",
        );
        let base = checked(&engine(), &format!("{PROVIDER}\n{registration}"));
        assert!(
            InstanceRegistry::read(base.environment())
                .unwrap()
                .candidates(&n("Provider"))
                .is_empty()
        );
        assert_eq!(owned_defaults(&provider, &base)[0].candidate.priority, 1000);
        assert_eq!(
            fln_elab::reducibility::known_status(base.environment(), &n("callable")),
            Ok(None)
        );
        for call in ["f 20", "f (n := 20)"] {
            let source = format!("def answer : Nat := let f : _ := supplied; {call}");
            checked(
                &base,
                &format!("{source}\ntheorem computes : answer = 42 := by rfl"),
            );
            evaluated(&base, &format!("{source}\n#eval answer"), "42");
        }
    }

    // The single-declaration API must publish the same admitted metadata as
    // the source command driver, with the receipt naming its actual successor.
    let base = checked(&engine(), PROVIDER);
    let root = base.logical_root(&KVMap::new());
    let admitted = base
        .admit_source_declaration(
            b"@[default_instance 1700] def direct : Provider Nat := { value := 42 }",
            &KVMap::new(),
            limits().admission,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(admitted.base_logical_root, root);
    assert_eq!(
        admitted.result_logical_root,
        admitted.engine.logical_root(&KVMap::new())
    );
    let rows = owned_defaults(&base, &admitted.engine);
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].candidate.declaration, n("direct"));
    assert_eq!(rows[0].candidate.priority, 1700);
    checked(
        &admitted.engine,
        "def fromDirect := let value : _ := supplied; value\ntheorem directValue : fromDirect = 42 := by rfl",
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&n("direct")));

    let opaque = checked(
        &base,
        "@[default_instance] opaque opaqueCandidate : Provider Nat := { value := 42 }\ndef fromOpaque := let value : _ := supplied; value",
    );
    let Some(ConstantInfo::Opaque(candidate)) = opaque.environment().find(&n("opaqueCandidate"))
    else {
        panic!("a safe opaque default must keep its admitted declaration kind");
    };
    assert!(!candidate.is_unsafe);
    let rows = owned_defaults(&base, &opaque);
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].candidate.declaration, n("opaqueCandidate"));
    assert_eq!(
        opaque
            .environment()
            .find(&n("fromOpaque"))
            .unwrap()
            .constant_val()
            .type_,
        fln::Expr::const_(n("Nat"), vec![])
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

#[test]
fn repeated_priorities_are_cumulative_and_equal_priority_uses_newest_registration() {
    let seed = engine();
    let base = checked(
        &seed,
        &format!(
            "{PROVIDER}\ndef first : Provider Nat := {{ value := 7 }}\ndef second : Provider Nat := {{ value := 9 }}\nattribute [default_instance 2000] first\nattribute [default_instance 1000] second\nattribute [default_instance 100] first"
        ),
    );
    checked(
        &base,
        "def chosen := let value : _ := supplied; value\ntheorem oldPrioritySurvives : chosen = 7 := by rfl",
    );
    let rows = owned_defaults(&seed, &base);
    assert_eq!(
        rows.iter()
            .map(|row| (
                row.candidate.declaration.clone(),
                row.candidate.priority,
                row.candidate.order
            ))
            .collect::<Vec<_>>(),
        [
            (n("first"), 2000, 0),
            (n("second"), 1000, 1),
            (n("first"), 100, 2)
        ]
    );
    let recent = checked(
        &base,
        "attribute [default_instance 2000] second\ndef chosen := let value : _ := supplied; value\ntheorem newestWins : chosen = 9 := by rfl",
    );
    let rows = owned_defaults(&seed, &recent);
    assert_eq!(rows.len(), 4);
    assert_eq!(rows[0].candidate.declaration, n("second"));
    assert_eq!(rows[0].candidate.order, 3);
    assert_eq!(rows[1].candidate.declaration, n("first"));
    assert_eq!(rows[1].candidate.order, 0);
    assert_eq!(owned_defaults(&seed, &base).len(), 3);
}

#[test]
fn ordinary_search_precedes_defaults_and_anonymous_instance_attributes_keep_admitted_names() {
    let seed = engine();
    let ordinary = checked(
        &seed,
        &format!(
            "{PROVIDER}\ninstance (priority := 1) normal : Provider Nat := {{ value := 7 }}\n@[default_instance 4000] def fallback : Provider Nat := {{ value := 9 }}\ndef knownInput : Nat := supplied\ntheorem ordinaryWins : knownInput = 7 := by rfl"
        ),
    );
    let registry = InstanceRegistry::read(ordinary.environment()).unwrap();
    let [normal] = registry.candidates(&n("Provider")) else {
        panic!("a default attribute must leave the ordinary registry unchanged");
    };
    assert_eq!(normal.declaration, n("normal"));
    assert_eq!(normal.priority, 1);
    assert_eq!(
        fln_elab::reducibility::known_status(ordinary.environment(), &n("fallback")),
        Ok(None)
    );

    let anonymous = checked(
        &seed,
        &format!(
            "{PROVIDER}\nnamespace Auto\n@[default_instance 1700] instance : Provider Nat := {{ value := 42 }}\nend Auto\ndef inferred := let value : _ := supplied; value\ntheorem anonymousValue : inferred = 42 := by rfl"
        ),
    );
    let defaults = owned_defaults(&seed, &anonymous);
    let [candidate] = defaults.as_slice() else {
        panic!("an anonymous instance must publish one default row");
    };
    let registry = InstanceRegistry::read(anonymous.environment()).unwrap();
    let [normal] = registry.candidates(&n("Provider")) else {
        panic!("the same admitted anonymous instance must remain ordinary");
    };
    assert_eq!(candidate.candidate.declaration, normal.declaration);
    assert_eq!(candidate.candidate.declaration.parent(), n("Auto"));
    assert_eq!(candidate.candidate.priority, 1700);
    assert_eq!(normal.priority, 1000);
    assert!(anonymous.environment().contains(&normal.declaration));
    assert_eq!(
        fln_elab::reducibility::known_status(anonymous.environment(), &normal.declaration),
        Ok(Some(
            fln_elab::reducibility::Reducibility::ImplicitReducible
        ))
    );
}

#[test]
fn global_defaults_resolve_exact_names_and_survive_sections_and_files() {
    let base = checked(&engine(), PROVIDER);
    let first = "namespace A
def «dictionary.part» : Provider Nat := { value := 7 }
end A
namespace dictionary
def part : Provider Nat := { value := 9 }
end dictionary
open A
section
attribute [default_instance (high)] «dictionary.part»
end";
    let second = "def selected := let value : _ := supplied; value
theorem afterSection : selected = 7 := by rfl
attribute [default_instance (low)] dictionary.part
def selectedAgain := let value : _ := supplied; value
theorem afterFile : selectedAgain = 7 := by rfl";
    let checked = base
        .check_source_files(
            &[first.as_bytes(), second.as_bytes()],
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(checked.files, 2);
    assert_eq!(checked.theorems, 2);
    let rows = owned_defaults(&base, &checked.engine);
    assert_eq!(rows.len(), 2);
    assert_eq!(
        rows[0].candidate.declaration,
        Name::from_components(["A", "dictionary.part"])
    );
    assert_eq!(rows[1].candidate.declaration, n("dictionary.part"));
    assert_eq!(rows[0].candidate.priority, 10000);
    assert_eq!(rows[1].candidate.priority, 100);
    assert!(
        defaults::read(base.environment())
            .unwrap()
            .iter()
            .all(|row| row.class != n("Provider"))
    );
}

#[test]
fn malformed_attributes_and_late_invalid_candidates_publish_no_successor() {
    let base = checked(
        &engine(),
        &format!(
            "{PROVIDER}\ndef candidate : Provider Nat := {{ value := 7 }}\ndef plain : Nat := 0"
        ),
    );
    let root = base.logical_root(&KVMap::new());
    for source in [
        "attribute [default_instance] candidate missing",
        "attribute [default_instance] candidate plain",
        "attribute [local default_instance] candidate",
        "attribute [scoped default_instance] candidate",
        "attribute [-default_instance] candidate",
        "attribute [default_instance high + 1] candidate",
        "attribute [default_instance 4294967296] candidate",
        "@[default_instance] def rejected : Nat := 0",
        "@[default_instance] def rejected : Provider Nat := 0",
        "@[default_instance] example : Nat := 0",
        "@[default_instance] structure rejected where\n  value : Nat",
        "@[default_instance] class rejected where\n  value : Nat",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(
            defaults::read(base.environment())
                .unwrap()
                .iter()
                .all(|row| row.class != n("Provider"))
        );
        assert!(!base.environment().contains(&n("rejected")));
    }
    assert!(
        base.admit_source_declaration(
            b"@[default_instance] def rejected : Nat := 0",
            &KVMap::new(),
            limits().admission,
        )
        .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&n("rejected")));
    checked(
        &base,
        "attribute [default_instance] candidate\ndef recovered := let value : _ := supplied; value\ntheorem recovery : recovered = 7 := by rfl",
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

#[test]
fn default_registration_and_suffix_export_are_bounded_without_changing_the_base() {
    let base = checked(
        &engine(),
        &format!("{PROVIDER}\ndef candidate : Provider Nat := {{ value := 7 }}"),
    );
    let root = base.logical_root(&KVMap::new());
    let source = format!("attribute [default_instance] {}", "candidate ".repeat(4097));
    let error = base
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_err();
    assert_eq!(error.disposition(), ("resource", false, 3));
    let first = defaults::register(base.environment(), &n("candidate"), 1000).unwrap();
    let second = defaults::register(&first, &n("candidate"), 10).unwrap();
    assert_eq!(
        defaults::registrations(&first, &second, 0),
        Err(InstanceRegistryError::Limit)
    );
    let rows = defaults::registrations(&first, &second, usize::MAX).unwrap();
    assert_eq!(rows.entries.len(), 1);
    assert_eq!(rows.entries[0].candidate.priority, 10);
    assert!(rows.work > 0 && rows.bytes_examined > 0);
    assert_eq!(
        defaults::registrations(&first, &second, rows.work).unwrap(),
        rows
    );
    assert_eq!(
        defaults::registrations(&first, &second, rows.work - 1),
        Err(InstanceRegistryError::Limit)
    );
    assert_eq!(
        defaults::registrations(&second, &second, 0).unwrap().work,
        0
    );
    assert!(defaults::registrations(&second, &first, usize::MAX).is_err());
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

fn modules(base: &Engine, files: &[(&str, &str)]) -> Result<Engine, String> {
    let names: Vec<_> = files.iter().map(|(name, _)| n(name)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    base.check_source_modules(
        &inputs,
        &n("Main"),
        &KVMap::new(),
        SourceModuleCheckLimits::new(limits()),
    )
    .map_err(|error| format!("{error:?}"))?
    .into_complete()
    .map(|checked| checked.checked.engine)
    .map_err(|error| format!("{error:?}"))
}

#[test]
fn private_defaults_stay_private_and_public_headers_use_only_public_candidates() {
    let base = checked(&engine(), PROVIDER);
    let private = "module\nprelude
        @[default_instance] def hidden : Provider Nat := { value := 42 }
        def selected := let value : _ := supplied; value
        theorem localValue : selected = 42 := by rfl";
    let result = modules(&base, &[("Main", private)]).unwrap();
    assert_eq!(owned_defaults(&base, &result).len(), 1);
    let hidden = Name::num(n("_private.Main"), 0).append_core(&n("hidden"));
    assert_eq!(
        owned_defaults(&base, &result)[0].candidate.declaration,
        hidden
    );
    assert!(
        modules(
            &base,
            &[(
                "Main",
                &format!(
                    "{private}\n@[expose] public def leak := let value : _ := supplied; value"
                )
            )]
        )
        .is_err()
    );
    let imported = modules(
        &base,
        &[("Library", private), ("Main", "prelude\nimport Library")],
    )
    .unwrap();
    assert!(owned_defaults(&base, &imported).is_empty());
    assert!(!imported.environment().contains(&n("hidden")));
    assert!(
        !imported
            .environment()
            .contains(&Name::num(n("_private.Library"), 0).append_core(&n("hidden")))
    );
    assert!(
        modules(
            &base,
            &[
                ("Library", private),
                (
                    "Main",
                    "prelude\nimport Library\ndef leak := let value : _ := supplied; value"
                )
            ]
        )
        .is_err()
    );

    let both = "module\nprelude
@[default_instance 1000, expose] public def visible : Provider Nat := { value := 7 }
@[default_instance 2000] def hidden : Provider Nat := { value := 42 }
def localSelection := let value : _ := supplied; value
theorem localValue : localSelection = 42 := by rfl
@[expose] public def publicSelection := let value : _ := supplied; value
public theorem publicValue : publicSelection = 7 := by rfl";
    modules(&base, &[("Main", both)]).unwrap();
    let imported = modules(
        &base,
        &[
            ("Library", both),
            (
                "Main",
                "prelude\nimport Library\ndef imported := let value : _ := supplied; value\ntheorem importedValue : imported = 7 := by rfl",
            ),
        ],
    )
    .unwrap();
    let rows = owned_defaults(&base, &imported);
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].candidate.declaration, n("visible"));
}

#[test]
fn global_attributes_export_visible_candidates_even_from_private_sections() {
    let base = checked(&engine(), PROVIDER);
    let library = "module\nprelude
        @[expose] public def visible : Provider Nat := { value := 7 }
        def hidden : Provider Nat := { value := 9 }
        section
        attribute [default_instance 700] visible
        attribute [default_instance 900] hidden
        attribute [default_instance 700] visible
        end
        def localSelection := let value : _ := supplied; value
        theorem localValue : localSelection = 9 := by rfl";
    let local = modules(&base, &[("Main", library)]).unwrap();
    let local_rows = owned_defaults(&base, &local);
    assert_eq!(local_rows.len(), 3);
    assert_eq!(local_rows[0].candidate.priority, 900);
    assert_eq!(local_rows[1].candidate.order, 2);
    assert_eq!(local_rows[2].candidate.order, 0);
    let imported = modules(
        &base,
        &[
            ("Library", library),
            (
                "Main",
                "prelude\nimport Library\ndef imported := let value : _ := supplied; value\ntheorem importedValue : imported = 7 := by rfl",
            ),
        ],
    )
    .unwrap();
    let rows = owned_defaults(&base, &imported);
    assert_eq!(rows.len(), 2);
    assert!(
        rows.iter()
            .all(|row| row.candidate.declaration == n("visible") && row.candidate.priority == 700)
    );
    assert_eq!(rows[0].candidate.order, 1);
    assert_eq!(rows[1].candidate.order, 0);
}

#[test]
fn safe_public_proof_interfaces_and_repeated_inline_attributes_remain_defaults() {
    let base = checked(
        &engine(),
        "class Marker (A : Type) : Prop where\n  proof : True\ndef typeFromProof {A : Type} [Marker A] : Type := A",
    );
    let library = "module\nprelude
        @[default_instance 10] public axiom axiomCandidate : Marker (Nat -> Nat)
        private theorem hiddenProof : True := True.intro
        @[default_instance 2000, default_instance 1000] public theorem proofCandidate : Marker Nat := Marker.mk hiddenProof
        def selected := let value : _ := typeFromProof; value
        theorem isNat : selected = Nat := by rfl";
    assert!(
        modules(
            &base,
            &[(
                "Main",
                "module\nprelude\ndef Hidden : Type := Nat\n@[default_instance] public axiom badSignature : Marker Hidden"
            )]
        )
        .is_err(),
        "a public axiom must not gain a signature mentioning a private type"
    );
    let scoped = "module\nprelude
def Hidden : Type 1 := Type
section
variable (secret : Hidden)
@[default_instance] public axiom badSection : Marker secret
end";
    let private_scoped = scoped.replace("public axiom", "axiom");
    modules(&base, &[("Main", &private_scoped)]).unwrap();
    assert!(
        modules(&base, &[("Main", scoped)]).is_err(),
        "a public axiom must not capture a section variable of a private type"
    );
    let local = modules(&base, &[("Main", library)]).unwrap();
    assert!(matches!(
        local.environment().find(&n("proofCandidate")),
        Some(ConstantInfo::Thm(_))
    ));
    let result = modules(
        &base,
        &[
            ("Library", library),
            (
                "Main",
                "prelude\nimport Library\ndef another := let value : _ := typeFromProof; value\ntheorem isNatAgain : another = Nat := by rfl",
            ),
        ],
    )
    .unwrap();
    for candidate in ["axiomCandidate", "proofCandidate"] {
        let Some(ConstantInfo::Axiom(interface)) = result.environment().find(&n(candidate)) else {
            panic!("a safe public proof interface must retain its admitted kind");
        };
        assert!(!interface.is_unsafe);
    }
    let rows = owned_defaults(&base, &result);
    assert_eq!(
        rows.iter()
            .map(|row| (row.candidate.declaration.clone(), row.candidate.priority))
            .collect::<Vec<_>>(),
        [
            (n("proofCandidate"), 2000),
            (n("proofCandidate"), 1000),
            (n("axiomCandidate"), 10)
        ]
    );
    assert!(
        InstanceRegistry::read(result.environment())
            .unwrap()
            .candidates(&n("Marker"))
            .is_empty()
    );
    assert!(
        !result
            .environment()
            .contains(&Name::num(n("_private.Library"), 0).append_core(&n("hiddenProof")))
    );
}
