//! Registered simp rules use immutable source snapshots and both checking engines.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};
use fln_elab::source::scope::simp;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, sources: &[&str]) -> fln::SourceFileCheck {
    base.check_source_files(
        &sources.iter().map(|s| s.as_bytes()).collect::<Vec<_>>(),
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|e| panic!("{sources:?}\n{e:?}"))
    .into_complete()
    .unwrap()
}
fn refused(base: &Engine, source: &str) {
    let root = base.logical_root(&KVMap::new());
    let result = base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    assert!(!matches!(result, Ok(Outcome::Complete(_))), "{source}");
    assert_eq!(base.logical_root(&KVMap::new()), root);
}
const WRAP: &str = "def wrap.{u} {A : Sort u} (x : A) : A := x\n\
    theorem unwrap.{u} {A : Sort u} (x : A) : wrap x = x := by rfl\n";

#[test]
fn inline_simp_attributes_are_registered_only_after_checked_admission() {
    let base = engine();
    let result = checked(
        &base,
        &["def wrap.{u} {A : Sort u} (x : A) : A := x\n\
         @[simp 800] theorem unwrap.{u} {A : Sort u} (x : A) : wrap x = x := by rfl\n\
         theorem nested (n : Nat) : wrap (wrap n) = n := by simp\n\
         theorem typeValue (A : Type) : wrap A = A := by simp"],
    );
    assert_eq!(result.commands, 4);
    assert_eq!(result.theorems, 3);
    let rules = simp::read(result.engine.environment()).unwrap();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].declaration, Name::from_components(["unwrap"]));
    assert_eq!(rules[0].priority, 800);
    assert!(!rules[0].reverse);
    assert!(simp::read(base.environment()).unwrap().is_empty());
    let defined = checked(&base, &["def wrap (n : Nat) : Nat := n"]).engine;
    for bad in [
        "@[simp] theorem circular (n : Nat) : wrap n = n := by simp",
        "@[simp] theorem bad : (0 : Nat) = 1 := by rfl",
        "@[simp] theorem unsupported (p : Prop) (h : p) : p := by exact h",
        "@[simp ←] def backwards (n : Nat) := n",
    ] {
        refused(&defined, bad);
    }
    assert!(simp::read(defined.environment()).unwrap().is_empty());
}

#[test]
fn inline_attributes_bind_qualified_names_and_survive_command_and_file_scopes() {
    let base = engine();
    let result = checked(
        &base,
        &[
            "namespace N\n@[simp] def wrap.{u} {A : Sort u} (x : A) : A := x\n\
         @[simp ← 900] theorem «re.verse».{u} {A : Sort u} (x : A) : x = wrap x := by rfl\nend N",
            "open N\ntheorem use (n : Nat) : wrap (wrap n) = n := by simp\n\
         attribute [-simp] wrap «re.verse»",
        ],
    );
    assert_eq!(result.theorems, 2);
    assert!(simp::read(result.engine.environment()).unwrap().is_empty());
    assert!(
        result
            .engine
            .environment()
            .contains(&Name::from_components(["N", "re.verse"]))
    );
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["N", "wrap"]))
    );
}

#[test]
fn single_declaration_admission_publishes_the_simp_extension_and_logical_root() {
    let base = engine();
    let admitted = base
        .admit_source_declaration(
            b"@[simp] def wrapped (n : Nat) := n",
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(admitted.base_logical_root, base.logical_root(&KVMap::new()));
    assert_eq!(
        admitted.result_logical_root,
        admitted.engine.logical_root(&KVMap::new())
    );
    assert_ne!(admitted.base_logical_root, admitted.result_logical_root);
    assert_eq!(simp::read(admitted.engine.environment()).unwrap().len(), 1);
    checked(
        &admitted.engine,
        &["theorem use (n : Nat) : wrapped (wrapped n) = n := by simp"],
    );
    refused(
        &base,
        "@[simp] def early (n : Nat) := n\n@[unknown] def later := 0",
    );
    let absolute = base
        .admit_source_declaration(
            b"@[simp] def _root_.absolute (n : Nat) := n",
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        simp::read(absolute.engine.environment()).unwrap()[0].declaration,
        Name::from_components(["absolute"]),
    );
    checked(
        &absolute.engine,
        &["theorem use (n : Nat) : absolute n = n := by simp"],
    );
    checked(
        &base,
        &[
            "namespace N\n@[simp] def _root_.absolute (n : Nat) := n\nend N\ntheorem use (n : Nat) : absolute n = n := by simp",
        ],
    );
}

#[test]
fn executable_definition_door_cannot_silently_drop_inline_metadata() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let result = base.execute_source_definition(
        b"@[simp] def wrapped : Nat := 7",
        &KVMap::new(),
        fln::EngineExecutionLimits::new(limits().kernel),
    );
    assert!(result.is_err());
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(simp::read(base.environment()).unwrap().is_empty());
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["wrapped"]))
    );
}

#[test]
fn registered_polymorphic_lemmas_simplify_without_an_explicit_rule_list() {
    let base = checked(&engine(), &[WRAP]).engine;
    refused(&base, "theorem missing (n : Nat) : wrap n = n := by simp");
    let result = checked(
        &base,
        &["attribute [simp] unwrap\n\
        theorem nested (n : Nat) : wrap (wrap n) = n := by simp\n\
        theorem generic {A : Type} (x : A) : wrap (wrap x) = x := by simp []\n\
        theorem higher (A : Type) : wrap A = A := by simp"],
    );
    assert_eq!(result.commands, 4);
    assert_eq!(result.theorems, 3);
    assert!(simp::read(base.environment()).unwrap().is_empty());
    assert_eq!(simp::read(result.engine.environment()).unwrap().len(), 1);
}

#[test]
fn only_excludes_defaults_and_erasure_is_snapshot_local() {
    let base = checked(&engine(), &[WRAP, "attribute [simp] unwrap"]).engine;
    refused(
        &base,
        "theorem missing (n : Nat) : wrap n = n := by simp only []",
    );
    let erased = checked(&base, &["attribute [-simp] unwrap"]).engine;
    refused(&erased, "theorem missing (n : Nat) : wrap n = n := by simp");
    checked(
        &base,
        &["theorem retained (n : Nat) : wrap n = n := by simp"],
    );
    checked(
        &erased,
        &["theorem explicit (n : Nat) : wrap n = n := by simp only [unwrap]"],
    );
    assert_ne!(
        base.logical_root(&KVMap::new()),
        erased.logical_root(&KVMap::new())
    );
    assert_eq!(simp::read(base.environment()).unwrap().len(), 1);
    assert!(simp::read(erased.environment()).unwrap().is_empty());
}

#[test]
fn exact_registered_names_cannot_be_captured_by_locals_or_namespaces() {
    let source = "namespace Lib\n\
        def wrap {A : Type} (x : A) : A := x\n\
        theorem unwrap {A : Type} (x : A) : wrap x = x := by rfl\n\
        attribute [simp] unwrap\nend Lib\n\
        namespace Client\n\
        theorem t (unwrap : Nat) (x : Nat) : Lib.wrap x = x := by simp\n\
        theorem qualified (Lib.unwrap : Nat) (x : Nat) : Lib.wrap x = x := by simp\n\
        end Client";
    checked(&engine(), &[source]);
    let base = checked(
        &engine(),
        &["def wrap (n : Nat) : Nat := n\nattribute [simp] wrap"],
    )
    .engine;
    checked(
        &base,
        &["theorem t (n : Nat) : wrap n = n := by let wrap : Nat := 0; simp"],
    );
}

#[test]
fn registered_rules_transport_hypotheses_and_combine_with_selected_proofs() {
    let base = checked(&engine(), &[WRAP, "attribute [simp] unwrap"]).engine;
    checked(
        &base,
        &[
            "theorem transport (P : Nat -> Prop) (x : Nat) (h : P (wrap x)) : P x := by simp at h; exact h\n\
        theorem selected (f : Nat -> Nat) (n : Nat) (h : f n = n) : wrap (f n) = n := by simp [h]",
        ],
    );
    let conditional = "theorem contract (f : Nat -> Nat) (x : Nat) (h : f x = x) : f (f x) = f x := by simp only [h]\n\
        attribute [simp] contract\n\
        theorem t (f : Nat -> Nat) (x : Nat) (h : f x = x) : f (f x) = x := by simp [h]";
    checked(&engine(), &[conditional]);
    refused(
        &base,
        "theorem fake (P : Nat -> Prop) (x : Nat) : P (wrap x) := by simp",
    );
}

#[test]
fn reverse_registration_and_priorities_are_retained_deterministically() {
    let base = checked(
        &engine(),
        &[
            WRAP,
            "theorem backwards {A : Type} (x : A) : x = wrap x := by rfl\n\
         attribute [simp <- 900] backwards\nattribute [simp 100] unwrap",
        ],
    );
    let rows = simp::read(base.engine.environment()).unwrap();
    assert_eq!(
        rows.iter()
            .map(|r| (r.priority, r.reverse))
            .collect::<Vec<_>>(),
        [(900, true), (100, false)]
    );
    checked(
        &base.engine,
        &["theorem t (n : Nat) : wrap (wrap n) = n := by simp"],
    );
    let newer = checked(&base.engine, &["attribute [simp 900] unwrap"]);
    let rows = simp::read(newer.engine.environment()).unwrap();
    assert_eq!(rows[0].declaration, Name::from_components(["unwrap"]));
    let again = checked(&newer.engine, &["attribute [simp 900] unwrap"]);
    assert_eq!(newer.result_logical_root, again.result_logical_root);
}

#[test]
fn multi_name_registration_and_later_files_are_failure_atomic() {
    let base = checked(&engine(), &[WRAP]).engine;
    for source in [
        "attribute [simp] unwrap missing",
        "attribute [simp <-] wrap",
        "attribute [other] unwrap",
    ] {
        refused(&base, source);
        assert!(simp::read(base.environment()).unwrap().is_empty());
    }
    let root = base.logical_root(&KVMap::new());
    let result = base.check_source_files(
        &[
            b"attribute [simp] unwrap",
            b"theorem fake : 1 = 2 := by simp",
        ],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    assert!(!matches!(result, Ok(Outcome::Complete(_))));
    assert_eq!(base.logical_root(&KVMap::new()), root);
    checked(
        &base,
        &[
            "attribute [simp] unwrap",
            "theorem recovered (n : Nat) : wrap n = n := by simp",
        ],
    );
}

#[test]
fn open_namespace_resolution_and_escaped_names_preserve_identity() {
    checked(
        &engine(),
        &["namespace A\ndef «wrap.x» (n : Nat) : Nat := n\n\
        theorem «unwrap.x» (n : Nat) : «wrap.x» n = n := by rfl\nend A\n\
        open A\nattribute [simp] «unwrap.x»\n\
        theorem t (n : Nat) : A.«wrap.x» n = n := by simp"],
    );
    refused(
        &engine(),
        "namespace A\ndef x := 1\nend A\nnamespace B\ndef x := 2\nend B\nopen A B\nattribute [simp] x",
    );
}

#[test]
fn malformed_default_registry_never_becomes_success_or_a_tactic_fallback() {
    use fln_env::extensions::{
        CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
    };
    let base = engine();
    let name = Name::from_components(["FrankenLean", "sourceSimp", "v1"]);
    let env = base
        .environment()
        .register_extension(ExtensionDescriptor {
            name: name.clone(),
            merge: MergeSemantics::AppendOrdered,
            checkpoint: CheckpointSemantics::FullJournal,
            provenance: PayloadProvenance::Understood,
        })
        .unwrap()
        .push_extension_entry(&name, b"invalid versioned journal".to_vec())
        .unwrap();
    let damaged = Engine::from_environment(env);
    for proof in ["simp", "simp []", "first | simp | rfl", "try simp; rfl"] {
        let source = format!("theorem bad (n : Nat) : n = n := by {proof}");
        let error = damaged
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .unwrap_err();
        assert!(
            format!("{error:?}").contains("SimpSet(Malformed)"),
            "{error:?}"
        );
        assert_eq!(error.disposition(), ("internal-fault", false, 4));
    }
    checked(
        &damaged,
        &["theorem isolated (n : Nat) : n = n := by simp only []"],
    );
    assert!(simp::read(base.environment()).unwrap().is_empty());
}

#[test]
fn default_conditional_rules_do_not_invent_their_premises() {
    let base = checked(&engine(), &[WRAP,
        "theorem guarded (x : Nat) (h : x = 0) : wrap x = 0 := by simp only [wrap, h]\nattribute [simp] guarded",
    ]).engine;
    checked(
        &base,
        &["theorem t (x : Nat) (h : x = 0) : wrap x = 0 := by simp [h]"],
    );
    refused(&base, "theorem bad (x : Nat) : wrap x = 0 := by simp");
    refused(
        &base,
        "theorem bad (x : Nat) (h : x = 0) : wrap x = 0 := by simp",
    );
}

#[test]
fn registry_resource_stops_are_nonanswers_not_successful_fallbacks() {
    use fln_env::extensions::{
        CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
    };
    let base = engine();
    let name = Name::from_components(["FrankenLean", "sourceSimp", "v1"]);
    let env = base
        .environment()
        .register_extension(ExtensionDescriptor {
            name: name.clone(),
            merge: MergeSemantics::AppendOrdered,
            checkpoint: CheckpointSemantics::FullJournal,
            provenance: PayloadProvenance::Understood,
        })
        .unwrap()
        .push_extension_entry(&name, vec![0; 16385])
        .unwrap();
    let exhausted = Engine::from_environment(env);
    let source = "theorem bad (n : Nat) : n = n := by first | simp | rfl";
    let error = exhausted
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_err();
    assert_eq!(error.disposition(), ("resource", false, 3));
    checked(
        &exhausted,
        &["theorem explicit (n : Nat) : n = n := by simp only []"],
    );
}
