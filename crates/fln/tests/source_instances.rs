//! Source -> native instance search -> both ordinary checking engines.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};
use fln_core::expr::{Expr, ExprNode};
use fln_env::constants::ConstantInfo;

fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
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
fn checked(base: &Engine, text: &str) -> Engine {
    base.check_source_files(&[text.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{text}\n{error:?}"))
        .into_complete()
        .unwrap()
        .engine
}
fn has_constant(expr: &Expr, name: &Name) -> bool {
    let mut pending = vec![expr];
    while let Some(term) = pending.pop() {
        match term.node() {
            ExprNode::Const { name: n, .. } if n == name => return true,
            ExprNode::App { f, a } => {
                pending.push(a);
                pending.push(f);
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                pending.push(body);
                pending.push(binder_type);
            }
            _ => {}
        }
    }
    false
}
#[test]
fn scalar_default_instances_are_real_checked_values() {
    checked(
        &engine(),
        r#"theorem natDefault : default = 0 := by rfl
theorem stringDefault : default = "" := by rfl
theorem boolDefault : default = false := by rfl"#,
    );
}
#[test]
fn source_instance_binders_feed_calls_after_explicit_argument_inference() {
    checked(
        &engine(),
        "def choose {A : Type} [i : Inhabited A] (x : A) : A := default\ndef nested {A : Type} [Inhabited A] (x : A) : A := choose x",
    );
}
#[test]
fn newest_local_instance_wins_without_using_the_global_default() {
    let result = checked(
        &engine(),
        "def pick [first : Inhabited Nat] [second : Inhabited Nat] : Nat := default",
    );
    let Some(ConstantInfo::Defn(def)) = result.environment().find(&n("pick")) else {
        panic!("definition");
    };
    let mut value = &def.value;
    for _ in 0..2 {
        let ExprNode::Lam { body, .. } = value.node() else {
            panic!("lambda")
        };
        value = body;
    }
    let ExprNode::App { a, .. } = value.node() else {
        panic!("instance application")
    };
    assert!(matches!(a.node(), ExprNode::BVar { idx: 0 }));
    assert!(!has_constant(&def.value, &n("instInhabitedNat")));
}
#[test]
fn ordinary_class_parameters_are_local_instances() {
    let base = checked(
        &engine(),
        "def dictionary (i : Inhabited Nat) : Inhabited Nat := inferInstance\ntheorem selected (i : Inhabited Nat) : dictionary i = i := by rfl",
    );
    let before = base.logical_root(&KVMap::new());
    for source in [
        "theorem wrong (i : Inhabited Nat) : default = 0 := by rfl",
        "theorem wrong [i : Inhabited Nat] : default = 0 := by rfl",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(before, base.logical_root(&KVMap::new()));
    }
    checked(&base, "theorem recovery : default = 0 := by rfl");
}

#[test]
fn class_valued_lets_follow_local_instance_recency() {
    checked(
        &engine(),
        "def chosen : Nat := let d := Inhabited.mk 9; default\ntheorem result : chosen = 9 := by rfl\ndef newest (i : Inhabited Nat) : Nat := let d := Inhabited.mk 7; default\ntheorem recent (i : Inhabited Nat) : newest i = 7 := by rfl",
    );
}

#[test]
fn ordinary_functions_and_opaque_type_aliases_are_not_local_instances() {
    checked(
        &engine(),
        "def functionDictionary (f : Nat -> Inhabited Nat) : Inhabited Nat := inferInstance\ntheorem functionIgnored (f : Nat -> Inhabited Nat) : functionDictionary f = instInhabitedNat := by rfl\ndef Alias : Type := Inhabited Nat\ndef aliasDictionary (i : Alias) : Inhabited Nat := inferInstance\ntheorem aliasIgnored (i : Alias) : aliasDictionary i = instInhabitedNat := by rfl\ndef localAlias : Nat := let A : Type := Inhabited Nat; let i : A := Inhabited.mk 9; default\ntheorem localAliasIgnored : localAlias = 0 := by rfl",
    );
}

#[test]
fn instance_binders_and_targets_require_a_reducible_class_head() {
    let base = checked(&engine(), "def Alias : Type := Inhabited Nat");
    let before = base.logical_root(&KVMap::new());
    for source in [
        "def bad [i : Alias] : Nat := 0",
        "def bad : Alias := inferInstance",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(before, base.logical_root(&KVMap::new()));
    }
    checked(&base, "def recovery : Inhabited Nat := inferInstance");
}
#[test]
fn nonclasses_and_missing_instances_are_visible_refusals() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    for text in [
        "def bad [i : Nat] : Nat := i",
        "def missing (A : Type) : A := default",
        "def bad [i : Inhabited Nat -> Inhabited Nat] : Nat := 0",
    ] {
        assert!(
            base.check_source_files(&[text.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{text}"
        );
        assert_eq!(before, base.logical_root(&KVMap::new()));
    }
}
#[test]
fn registered_globals_are_priority_ordered_and_snapshot_local() {
    let base = checked(
        &engine(),
        "def seven : Inhabited Nat := Inhabited.mk 7\ndef nine : Inhabited Nat := Inhabited.mk 9",
    );
    let first =
        fln_elab::instances::register_instance(base.environment(), &n("seven"), 2000).unwrap();
    let second = fln_elab::instances::register_instance(&first, &n("nine"), 3000).unwrap();
    checked(
        &Engine::from_environment(first),
        "theorem picked : default = 7 := by rfl",
    );
    checked(
        &Engine::from_environment(second),
        "theorem picked : default = 9 := by rfl",
    );
    checked(&base, "theorem original : default = 0 := by rfl");
}
#[test]
fn failed_recursive_candidate_tries_the_next_global_without_state_leaks() {
    let base = checked(
        &engine(),
        "def recursive {A : Type} [i : Inhabited A] : Inhabited A := i",
    );
    let env =
        fln_elab::instances::register_instance(base.environment(), &n("recursive"), 2000).unwrap();
    checked(
        &Engine::from_environment(env),
        "theorem fallback : default = 0 := by rfl",
    );
}

#[test]
fn generic_type_constructor_instances_check_the_whole_noninjective_candidate() {
    let base = checked(
        &engine(),
        "class Choice (A B : Type) where\n  value : Nat\ndef Erase (_ : Type) : Type := Nat\ninstance (priority := 2000) nonlinear {m : Type -> Type} {A : Type} : Choice (m A) (m A) := { value := 9 }",
    );
    let before = base.logical_root(&KVMap::new());
    // First-order approximation can choose m := Erase and A := Nat, but its
    // second result argument must still match at instance transparency. Erase
    // is not an injective type constructor, nor a reducible instance alias.
    assert!(
        base.check_source_files(
            &[b"def refused : Choice (Erase Nat) (Erase Bool) := inferInstance".as_slice()],
            &KVMap::new(),
            limits(),
        )
        .is_err()
    );
    assert_eq!(before, base.logical_root(&KVMap::new()));
    checked(
        &base,
        "def agreed : Choice (Erase Nat) (Erase Nat) := inferInstance\ntheorem selected : agreed.value = 9 := by rfl",
    );
    let fallback = checked(
        &base,
        "instance (priority := 1000) fallback : Choice (Erase Nat) (Erase Bool) := { value := 7 }",
    );
    checked(
        &fallback,
        "def recovered : Choice (Erase Nat) (Erase Bool) := inferInstance\ntheorem fallbackSelected : recovered.value = 7 := by rfl",
    );
    assert_eq!(before, base.logical_root(&KVMap::new()));
}
#[test]
fn recursive_instance_dependencies_are_synthesized() {
    let base = checked(
        &engine(),
        "def functionDefault {A : Type} [Inhabited A] : Inhabited (Nat -> A) := Inhabited.mk (fun x => default)",
    );
    let env =
        fln_elab::instances::register_instance(base.environment(), &n("functionDefault"), 2000)
            .unwrap();
    checked(
        &Engine::from_environment(env),
        "def use : Nat -> Nat := default\ntheorem actual : use 123 = 0 := by rfl",
    );
}
#[test]
fn class_metadata_participates_in_logical_roots() {
    let base = checked(&engine(), "def seven : Inhabited Nat := Inhabited.mk 7");
    let env =
        fln_elab::instances::register_instance(base.environment(), &n("seven"), 2000).unwrap();
    assert_ne!(
        base.logical_root(&KVMap::new()),
        env.logical_root(&KVMap::new())
    );
    assert!(fln_elab::instances::register_instance(&env, &n("seven"), 3000).is_err());
}
#[test]
fn instance_binder_syntax_preserves_original_source_bytes() {
    for source in [
        "def f {A : Type} [i : Inhabited A] (x : A) : A := default",
        "def f [Inhabited Nat] : Nat := default",
    ] {
        let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
    }
}
#[test]
fn instance_source_does_not_turn_kernel_exhaustion_into_rejection() {
    let base = engine();
    let mut low = limits();
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    for source in [
        "def f : Nat := default",
        "def f : Nat -> Inhabited Nat := inferInstance",
    ] {
        let result = base.check_source_files(&[source.as_bytes()], &KVMap::new(), low);
        assert!(
            matches!(result, Ok(Outcome::Inconclusive(_)))
                || result
                    .as_ref()
                    .is_err_and(|error| error.disposition().2 == 3)
        );
    }
    checked(
        &base,
        "def recovery : Nat -> Inhabited Nat := inferInstance",
    );
}

#[test]
fn source_instance_registration_is_visible_to_later_commands_and_files() {
    let base = engine();
    let result = base
        .check_source_files(
            &[
                b"instance seven : Inhabited Nat := Inhabited.mk 7",
                b"theorem observed : default = 7 := by rfl",
            ],
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.commands, 2);
    assert_ne!(result.base_logical_root, result.result_logical_root);
    let rows = fln_elab::instances::InstanceRegistry::read(result.engine.environment()).unwrap();
    assert_eq!(rows.candidates(&n("Inhabited"))[0].declaration, n("seven"));
    checked(&base, "theorem unchanged : default = 0 := by rfl");
}

#[test]
fn source_instance_priority_and_equal_priority_recency_choose_the_dictionary() {
    checked(
        &engine(),
        "instance (priority := 2000) seven : Inhabited Nat := Inhabited.mk 7\ninstance (priority := 1001) nine : Inhabited Nat := Inhabited.mk 9\ntheorem higher : default = 7 := by rfl\ninstance (priority := 2000) newest : Inhabited Nat := Inhabited.mk 11\ntheorem recent : default = 11 := by rfl",
    );
}

#[test]
fn recursive_source_instance_declarations_drive_real_computation() {
    checked(
        &engine(),
        "instance functionDefault {A : Type} [Inhabited A] : Inhabited (Nat -> A) := Inhabited.mk (fun x => default)\ndef f : Nat -> Nat -> Nat := default\ntheorem result : f 1 2 = 0 := by rfl",
    );
}

#[test]
fn source_instances_are_not_registered_on_kernel_rejection_or_late_failure() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    for source in [
        "instance invalid : Inhabited Nat := 1",
        "instance bad : Nat := 1",
        "instance seven : Inhabited Nat := Inhabited.mk 7\ntheorem false : default = 0 := by rfl",
        "instance seven : Inhabited Nat := Inhabited.mk 7\ninstance seven : Inhabited Nat := Inhabited.mk 8",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(before, base.logical_root(&KVMap::new()));
    }
}

#[test]
fn named_instance_syntax_is_canonical_and_lossless_and_bounded() {
    for source in [
        "instance x : Inhabited Nat := Inhabited.mk 1",
        "instance (priority := 7) x [Inhabited Nat] : Inhabited Nat := Inhabited.mk default",
    ] {
        let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
        assert!(
            fln_elab::source::instance_registration(parsed.syntax())
                .unwrap()
                .is_some()
        );
        assert!(fln_parse::parse_nat_definition(source.as_bytes()).is_err());
        let command = fln_parse::parse_source_command(source.as_bytes()).unwrap();
        assert_eq!(command.kind(), fln_parse::SourceCommandKind::Definition);
        assert_eq!(command.syntax(), parsed.syntax());
        assert!(command.query_term_normalized().is_none());
    }
    // An anonymous instance is named by the pin's generator (`mkInstanceName`).
    assert!(matches!(
        engine().check_source_files(
            &[b"instance : Inhabited Nat := Inhabited.mk 1".as_slice()],
            &KVMap::new(),
            limits()
        ),
        Ok(fln::Outcome::Complete(_))
    ));
    for source in [
        "instance (priority := -1) x : Inhabited Nat := Inhabited.mk 1",
        "instance (priority := 4294967296) x : Inhabited Nat := Inhabited.mk 1",
    ] {
        assert!(
            engine()
                .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err()
        );
    }
}

#[test]
fn explicit_instance_admission_binds_the_registered_successor_root() {
    let base = engine();
    let options = KVMap::new();
    let result = base
        .admit_source_declaration(
            b"instance high : Inhabited Nat := Inhabited.mk 13",
            &options,
            limits().admission,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.base_logical_root, base.logical_root(&options));
    assert_eq!(
        result.result_logical_root,
        result.engine.logical_root(&options)
    );
    checked(&result.engine, "theorem seen : default = 13 := by rfl");
}

#[test]
fn infer_instance_is_an_ordinary_checked_identity_term() {
    checked(
        &engine(),
        "def dictionary : Inhabited Nat := inferInstance\ntheorem same : dictionary = instInhabitedNat := by rfl\ndef fromProof : Inhabited Nat := by exact inferInstance\ntheorem sameProof : fromProof = dictionary := by rfl",
    );
}

#[test]
fn infer_instance_prefers_the_current_local_dictionary() {
    checked(
        &engine(),
        "def dictionary [i : Inhabited Nat] : Inhabited Nat := inferInstance\ntheorem same [i : Inhabited Nat] : dictionary = i := by rfl",
    );
}

#[test]
fn function_instance_targets_preserve_ambient_dictionary_selection() {
    checked(
        &engine(),
        "def constant : Nat -> Inhabited Nat := inferInstance\n\
         theorem constant_ok : constant 3 = instInhabitedNat := by rfl\n\
         def ignored : Inhabited Nat -> Inhabited Nat -> Inhabited Nat := inferInstance\n\
         theorem ignored_ok (a b : Inhabited Nat) : ignored a b = instInhabitedNat := by rfl\n\
         def ambient (i : Inhabited Nat) : Inhabited Nat -> Inhabited Nat := inferInstance\n\
         theorem ambient_ok (i j : Inhabited Nat) : ambient i j = i := by rfl",
    );
}

#[test]
fn function_instance_targets_use_source_defined_classes_and_recursive_fallback() {
    checked(
        &engine(),
        "class Choice (A : Type) where\n  value : A\n\
         instance natChoice : Choice Nat := Choice.mk 11\n\
         instance recursive {A : Type} [i : Choice A] : Choice A := i\n\
         def dictionary : Nat -> Nat -> Choice Nat := inferInstance\n\
         theorem dictionary_ok : dictionary 4 5 = natChoice := by rfl",
    );
}

#[test]
fn failed_function_instance_targets_publish_nothing_and_recover() {
    let base = checked(
        &engine(),
        "class Choice (A : Type) where\n  value : A\n\
         instance natChoice : Choice Nat := Choice.mk 11\n\
         instance recursive {A : Type} [i : Choice A] : Choice A := i",
    );
    let before = base.logical_root(&KVMap::new());
    for source in [
        "def missing : Nat -> Choice Bool := inferInstance",
        "def nonclass : Nat -> Nat := inferInstance",
        "def wrong : Choice Nat -> Choice Nat := inferInstance\n\
         theorem leaked (i : Choice Nat) : wrong i = i := by rfl",
    ] {
        let error = base
            .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
            .unwrap_err();
        assert_eq!(error.disposition().2, 1, "{source}: {error}");
        assert_eq!(before, base.logical_root(&KVMap::new()));
    }
    checked(
        &base,
        "def recovery : Nat -> Choice Nat := inferInstance\n\
         theorem recovery_ok : recovery 3 = natChoice := by rfl",
    );
}

#[test]
fn apply_synthesizes_instance_parameters_without_exposing_them_as_proof_goals() {
    let e = checked(
        &engine(),
        "theorem keep {A : Type} [Inhabited A] (x : A) : x = x := by rfl\ntheorem use (x : Nat) : x = x := by apply keep",
    );
    let ConstantInfo::Thm(theorem) = e.environment().find(&n("use")).unwrap() else {
        panic!("theorem")
    };
    assert!(has_constant(&theorem.value, &n("keep")));
    assert!(has_constant(&theorem.value, &n("instInhabitedNat")));
}

#[test]
fn apply_keeps_introduced_instance_scopes_inside_the_final_lambda() {
    checked(
        &engine(),
        "def choose {A : Type} [Inhabited A] (x : A) : A := default\ndef use (A : Type) [i : Inhabited A] : A -> A := by intro x; apply choose; exact x",
    );
}

#[test]
fn rewriting_and_simp_synthesize_lemma_instances_without_implicit_hypothesis_search() {
    let e = checked(
        &engine(),
        "theorem keep {A : Type} [Inhabited A] (f : A -> A) (x : A) (h : f x = x) : f x = x := by exact h",
    );
    checked(
        &e,
        "theorem rewriteUse (f : Nat -> Nat) (x : Nat) (h : f x = x) : f x = x := by rw [keep f]; exact h\ntheorem simpUse (f : Nat -> Nat) (x : Nat) (h : f x = x) : f (f x) = x := by simp only [keep f, h]",
    );
    let before = e.environment().logical_root(&KVMap::new());
    assert!(e.check_source_files(&[b"theorem mustNotUseHidden (f : Nat -> Nat) (x : Nat) (h : f x = x) : f x = x := by simp only [keep f]"], &KVMap::new(), limits()).is_err());
    assert_eq!(e.environment().logical_root(&KVMap::new()), before);
}

#[test]
fn instance_dependent_tactics_refuse_missing_dictionaries_without_publishing() {
    let e = checked(
        &engine(),
        "theorem keep {A : Type} [Inhabited A] (x : A) : x = x := by rfl",
    );
    let before = e.environment().logical_root(&KVMap::new());
    for source in [
        "def missing (A : Type) : Inhabited A := inferInstance",
        "theorem missing (A : Type) (x : A) : x = x := by apply keep",
    ] {
        assert!(
            e.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err()
        );
        assert_eq!(e.environment().logical_root(&KVMap::new()), before);
    }
}

#[test]
fn rewriting_synthesizes_known_dictionary_arguments_before_matching() {
    let base = checked(
        &engine(),
        "def consume (i : Inhabited Nat) : Nat := 0\ntheorem rule (P : Prop) [i : Inhabited Nat] (hp : P) : consume i = 0 := by rfl",
    );
    for script in ["rw [rule P]; exact hp", "simp only [rule P, hp]"] {
        let source = format!(
            "theorem use (P : Prop) (hp : P) : consume instInhabitedNat = 0 := by {script}"
        );
        let result = checked(&base, &source);
        let ConstantInfo::Thm(theorem) = result.environment().find(&n("use")).unwrap() else {
            panic!("theorem")
        };
        assert!(has_constant(&theorem.value, &n("rule")));
        assert!(has_constant(&theorem.value, &n("instInhabitedNat")));
    }
}

#[test]
fn fully_applied_dictionary_rules_keep_their_original_arguments() {
    let base = checked(
        &engine(),
        "def consume (i : Inhabited Nat) : Nat := 0\ntheorem rule (P : Prop) [i : Inhabited Nat] (hp : P) : consume i = 0 := by rfl",
    );
    for script in ["rw [rule P hp]", "simp only [rule P hp]"] {
        let source = format!(
            "theorem use (P : Prop) (hp : P) : consume instInhabitedNat = 0 := by {script}"
        );
        let result = checked(&base, &source);
        let ConstantInfo::Thm(theorem) = result.environment().find(&n("use")).unwrap() else {
            panic!("theorem")
        };
        assert!(has_constant(&theorem.value, &n("rule")));
        assert!(has_constant(&theorem.value, &n("instInhabitedNat")));
    }
}

#[test]
fn dictionary_rewriting_uses_local_precedence_without_guessing_from_occurrences() {
    let base = checked(
        &engine(),
        "theorem rule (P : Prop) (f : Inhabited Nat -> Nat) [i : Inhabited Nat] (h : f i = 0) (hp : P) : f i = 0 := by exact h",
    );
    for binder in ["(i : Inhabited Nat)", "[i : Inhabited Nat]"] {
        let source = format!(
            "theorem use (P : Prop) (f : Inhabited Nat -> Nat) {binder} (h : f i = 0) (hp : P) : f i = 0 := by rw [rule P f]; exact h; exact hp"
        );
        let result = checked(&base, &source);
        let ConstantInfo::Thm(theorem) = result.environment().find(&n("use")).unwrap() else {
            panic!("theorem")
        };
        assert!(has_constant(&theorem.value, &n("rule")));
        assert!(!has_constant(&theorem.value, &n("instInhabitedNat")));
    }
    checked(
        &base,
        "theorem use (P : Prop) (f : Inhabited Nat -> Nat) (h : f instInhabitedNat = 0) (hp : P) : f instInhabitedNat = 0 := by rw [rule P f]; exact h; exact hp",
    );
    let before = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(
            &[b"theorem wrong (P : Prop) (f : Inhabited Nat -> Nat) [i : Inhabited Nat] (h : f i = 0) (hp : P) : f instInhabitedNat = 0 := by rw [rule P f]; exact h; exact hp"],
            &KVMap::new(),
            limits(),
        )
        .is_err()
    );
    assert_eq!(before, base.logical_root(&KVMap::new()));
}

/// Anonymous instances get the pin's generated names (`mkInstanceName`,
/// `Lean/Elab/DeclNameGen.lean`): type heads in order, `Of…` for each binder the type
/// does not mention, the current namespace's constants omitted, and `_1`, … while a name
/// is taken. Every name below is the one the pinned Reference generates for this source;
/// a wrong one is an unknown identifier in the `example` that uses it.
#[test]
fn anonymous_instances_receive_the_pins_generated_names() {
    let source = "class Shape (α : Type) where
  area : α → Nat
structure Sq where
  s : Nat
instance : Shape Sq := ⟨fun q => q.s⟩
instance : Shape (List Sq) := ⟨fun _ => 0⟩
instance : Inhabited Sq := ⟨⟨1⟩⟩
instance : Inhabited Sq := ⟨⟨2⟩⟩
class Foo (α : Type) (n : Nat) where
  x : Nat
instance {α : Type} [Inhabited α] : Foo (List α) 3 := ⟨1⟩
instance (n : Nat) : Foo Sq n := ⟨n⟩
namespace Sq
instance : Shape (Option Sq) := ⟨fun _ => 0⟩
end Sq
example : Shape Sq := instShapeSq
example : Shape (List Sq) := instShapeListSq
example : Inhabited Sq := instInhabitedSq_1
example : Foo (List Nat) 3 := instFooListOfNatNatOfInhabited
example : Foo Sq 4 := instFooSq 4
example : Shape (Option Sq) := Sq.instShapeOption
";
    let result = engine().check_source_files(&[source.as_bytes()], &KVMap::new(), limits());
    assert!(
        matches!(result, Ok(fln::Outcome::Complete(_))),
        "{result:?}"
    );
}

/// The pin's tests/elab/509.lean, with its notation expanded. Matching
/// foo.has_note2 requires solving the candidate's function-valued dictionary
/// before a stuck parent-class projection can reduce.
const INHERITED_FUNCTION_INSTANCES: &str = r#"
class has_note (M : Type) where
  note : M
class has_note2 (M : Type) extends has_note M
variable {ι : Type} (β : ι → Type)
structure foo [∀ i, has_note (β i)] : Type where
  to_fun : ∀ i, β i
instance foo.has_note [∀ i, has_note (β i)] : has_note (foo (fun i => β i)) where
  note := { to_fun := fun _ => has_note.note }
instance foo.has_note2 [∀ i, has_note2 (β i)] : has_note2 (foo (fun i => β i)) where
  note := has_note.note
variable (α : Type) (M : Type)
structure bar [has_note M] where
  to_fun : α → M
instance bar.has_note [has_note M] : has_note (bar α M) where
  note := { to_fun := fun _ => has_note.note }
instance bar.has_note2 [has_note2 M] : has_note2 (bar α M) where
  note := has_note.note
"#;

#[test]
fn higher_order_instance_projection_constraints_synthesize_the_candidate_dictionary() {
    let base = checked(&engine(), INHERITED_FUNCTION_INSTANCES);
    // The explicit candidate already works. The search must find that same
    // checked dictionary instead of abandoning its unresolved projection.
    let base = checked(
        &base,
        r#"def explicit {ι : Type} (β : ι → Type) (M : Type) [has_note2 M] :
  has_note2 (foo (fun (i : ι) => bar (β i) M)) := foo.has_note2 _"#,
    );
    let result = checked(
        &base,
        r#"def inferred {ι : Type} (β : ι → Type) (M : Type) [has_note2 M] :
  has_note2 (foo (fun (i : ι) => bar (β i) M)) := inferInstance
theorem same {ι : Type} (β : ι → Type) (M : Type) [has_note2 M] :
  inferred β M = explicit β M := by rfl"#,
    );
    let Some(ConstantInfo::Defn(definition)) = result.environment().find(&n("inferred")) else {
        panic!("instance synthesis must publish the checked definition");
    };
    assert!(has_constant(&definition.value, &n("foo.has_note2")));
    assert!(has_constant(&definition.value, &n("bar.has_note2")));
}

#[test]
fn higher_order_instance_projection_failures_preserve_the_environment_and_recover() {
    let base = checked(&engine(), INHERITED_FUNCTION_INSTANCES);
    let before = base.logical_root(&KVMap::new());
    // A parent dictionary cannot supply the stronger child class. A solved
    // candidate from an earlier command must not escape a later refusal.
    let source = r#"def provisional {ι : Type} (β : ι → Type) (M : Type) [has_note2 M] :
  has_note2 (foo (fun (i : ι) => bar (β i) M)) := inferInstance
def rejected {ι : Type} (β : ι → Type) (M : Type) [has_note M] :
  has_note2 (foo (fun (i : ι) => bar (β i) M)) := inferInstance"#;
    let error = base
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .expect_err("a missing child instance must remain a real synthesis failure");
    assert_eq!(error.disposition(), ("elaboration", false, 1));
    assert!(
        matches!(error, fln::SourceCheckError::Command { command: 1, .. }),
        "the valid earlier command must complete before the missing-instance refusal: {error:?}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
    assert!(!base.environment().contains(&n("provisional")));
    assert!(!base.environment().contains(&n("rejected")));
    checked(
        &base,
        r#"def recovered {ι : Type} (β : ι → Type) (M : Type) [has_note2 M] :
  has_note2 (foo (fun (i : ι) => bar (β i) M)) := inferInstance"#,
    );
}
