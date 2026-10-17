//! Lexical noncomputable sections keep checking, computation and publication distinct.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
    VmExit,
};
use std::collections::BTreeSet;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20))
}
fn seed() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn n(name: &str) -> Name {
    Name::from_components(name.split('.'))
}
fn tags(engine: &Engine) -> BTreeSet<Name> {
    fln_elab::noncomputable::read(engine.environment()).unwrap()
}
fn check(engine: &Engine, source: &str) -> Engine {
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("both checkers complete")
        .engine
}
const TYPE: &str = "inductive T where | a | b (x : T)\n";
const COUNT: &str = "T.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 1) t";
fn source(body: &str) -> String {
    format!("{TYPE}{body}").replace("COUNT", COUNT)
}

#[test]
fn sections_suppress_declaration_codegen_only_after_the_body_checks() {
    let engine = check(
        &seed(),
        include_str!("../../fln-parse/tests/fixtures/noncomputable_section_recursors.lean"),
    );
    assert_eq!(tags(&engine), BTreeSet::from([n("count")]));
    assert!(engine.environment().contains(&n("computed")));
}

#[test]
fn nested_sections_and_namespaces_restore_the_enclosing_compilation_policy() {
    let engine = check(
        &seed(),
        &source(
            "namespace N\nnoncomputable section A.B\ndef first (t : T) : Nat := COUNT\nend B\nsection\ndef second (t : T) : Nat := COUNT\nend\nend A\nend N\n",
        ),
    );
    assert_eq!(tags(&engine), BTreeSet::from([n("N.first"), n("N.second")]));
    let root = engine.logical_root(&KVMap::new());
    let bad = "def outside (t : T) : Nat := COUNT\n".replace("COUNT", COUNT);
    assert!(
        engine
            .check_source_files(
                &[bad.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err()
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn successful_definitions_in_a_noncomputable_section_remain_executable() {
    let run = seed().execute_source_commands_with_checks(
        b"noncomputable section\ndef answer : Nat := 7\ndef addOne (x : Nat) : Nat := x + 1\ntheorem correct : answer = 7 := by rfl\n#eval addOne answer\nend\n#eval answer\n",
        &KVMap::new(), EngineExecutionLimits::new(limits().kernel),
    ).unwrap().into_complete().unwrap();
    assert!(tags(&run.batch.engine).is_empty());
    let values: Vec<_> = run
        .batch
        .executions
        .iter()
        .map(|execution| {
            let VmExit::Returned(result) = &execution.exit else {
                panic!("returned Nat")
            };
            fln_vm::interpreter::nat_decimal(&result.value).unwrap()
        })
        .collect();
    assert_eq!(values, ["8", "7"]);
}

#[test]
fn evaluation_is_not_suppressed_by_a_noncomputable_section() {
    let base = check(&seed(), TYPE);
    for source in [
        "noncomputable section\n#eval T.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 1) T.a\nend\n".to_owned(),
        "noncomputable section\ndef count (t : T) : Nat := COUNT\n#eval count T.a\nend\n".replace("COUNT", COUNT),
    ] {
        assert!(base.execute_source_commands_with_checks(
            source.as_bytes(), &KVMap::new(), EngineExecutionLimits::new(limits().kernel),
        ).is_err(), "accepted {source}");
    }
}

#[test]
fn wrong_terms_and_failed_suffixes_publish_neither_declarations_nor_tags() {
    let base = seed();
    let root = base.logical_root(&KVMap::new());
    for body in [
        "noncomputable section\ndef invalid : Nat := true\nend\n",
        "noncomputable section\ndef count (t : T) : Nat := COUNT\ntheorem invalid : False := by exact True.intro\nend\n",
    ] {
        assert!(
            base.check_source_files(
                &[source(body).as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err()
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(tags(&base).is_empty());
    }
    check(
        &base,
        &source("noncomputable section\ndef count (t : T) : Nat := COUNT\nend\n"),
    );
}

#[test]
fn section_inference_tags_actual_named_and_anonymous_instance_and_opaque_declarations() {
    let engine = check(
        &seed(),
        &source(
            "class Marker where\n  value : Nat\nnamespace N\nnoncomputable section\ninstance named : Marker := Marker.mk (T.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 1) T.a)\nlocal instance : Marker := Marker.mk (T.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 1) T.a)\nopaque secret (t : T) : Nat := COUNT\nend\nend N\n",
        ),
    );
    let tags = tags(&engine);
    assert_eq!(tags.len(), 3);
    assert!(tags.contains(&n("N.named")));
    assert!(tags.contains(&n("N.secret")));
    for name in tags {
        assert!(engine.environment().contains(&name));
    }
}

#[test]
fn erasure_still_prevents_false_noncomputable_tags_inside_sections() {
    let engine = check(
        &seed(),
        &source(
            "def sink (_ : True) : Nat := 7\nnoncomputable section\ndef keep (t : T) : Nat := sink ((fun (_ : Nat) => True.intro) (COUNT))\nend\n",
        ),
    );
    assert!(tags(&engine).is_empty());
}

#[test]
fn section_policy_does_not_escape_a_source_file_or_leave_an_incomplete_batch() {
    let base = check(&seed(), TYPE);
    let root = base.logical_root(&KVMap::new());
    let first = "noncomputable section\ndef first (t : T) : Nat := COUNT\n".replace("COUNT", COUNT);
    let second = "def second (t : T) : Nat := COUNT\n".replace("COUNT", COUNT);
    assert!(
        base.check_source_files(
            &[first.as_bytes(), second.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(tags(&base).is_empty());
    let next = base
        .check_source_files(
            &[first.as_bytes(), b"def plain : Nat := 7\n"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    assert_eq!(tags(&next), BTreeSet::from([n("first")]));
}

#[test]
fn public_sections_export_actual_noncomputable_tags_but_not_the_lexical_policy() {
    use fln::source_check::modules::SourceModuleCheckLimits;
    let library = source(
        "module\nprelude\n@[expose] public noncomputable section\ninductive U where | a | b (x : U)\ndef count (t : U) : Nat := U.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 1) t\ndef plain : Nat := 7\nend\n",
    );
    // TYPE is deliberately not prepended here: a module's header must be first.
    let library = library.strip_prefix(TYPE).unwrap();
    let main = "prelude\nimport Library\ntheorem computed : count (U.b U.a) = 1 := by rfl\n";
    let lib_name = n("Library");
    let main_name = n("Main");
    let inputs = [
        fln::SourceModuleInput {
            name: &lib_name,
            source: library.as_bytes(),
        },
        fln::SourceModuleInput {
            name: &main_name,
            source: main.as_bytes(),
        },
    ];
    let next = seed()
        .check_source_modules(
            &inputs,
            &main_name,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .checked
        .engine;
    assert_eq!(tags(&next), BTreeSet::from([n("count")]));
    let run = next
        .execute_source_commands_with_checks(
            b"#eval plain\n",
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(run.batch.executions.len(), 1);
    let invalid =
        "def outside (t : U) : Nat := U.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 1) t\n";
    assert!(
        next.check_source_files(
            &[invalid.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err()
    );
}
