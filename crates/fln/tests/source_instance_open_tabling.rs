//! Inferred instance outputs must stay inferable and backtrackable across table hits.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn seed() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("source checking failed: {error:?}\n{source}"))
        .into_complete()
        .unwrap()
        .engine
}

#[test]
fn repeated_inferred_outputs_share_the_first_complete_answer() {
    let mut source = String::from(
        "class Out0 (A : outParam Type) where\n  value : A\ninstance out0 : Out0 Nat := Out0.mk 7\n",
    );
    for depth in 1..=12 {
        let previous = depth - 1;
        source.push_str(&format!(
            "class Out{depth} (A : outParam Type) where\n  value : A\ninstance out{depth} {{A B : Type}} [first : Out{previous} A] [second : Out{previous} B] : Out{depth} Nat := Out{depth}.mk 7\n"
        ));
    }
    let base = checked(&seed(), &source);
    checked(
        &base,
        "def result : Out12 Nat := inferInstance\ntheorem correct : result.value = 7 := by rfl",
    );
}

const CHOICES: &str = r#"class Pick (A : outParam Type) where
  value : A
  stamp : Nat
instance (priority := 500) natural : Pick Nat := Pick.mk 8 1
instance (priority := 2000) boolean : Pick Bool := Pick.mk true 2
class Need (A : Type) where
  finish : A -> Nat
instance needNat : Need Nat := Need.mk (fun x => x + 1)
class Root where
  value : Nat
  stamp : Nat
"#;

#[test]
fn a_cached_output_choice_can_resume_when_a_later_prerequisite_fails() {
    let base = checked(&seed(), CHOICES);
    checked(
        &base,
        r#"instance root {A B : Type} [warm : Pick A] [pick : Pick B] [need : Need B] : Root := Root.mk (need.finish pick.value) warm.stamp
def result : Root := inferInstance
theorem resumed : result.value = 9 := by rfl
theorem firstUnchanged : result.stamp = 2 := by rfl"#,
    );
}

#[test]
fn replay_resumes_nested_choices_not_just_the_next_top_level_candidate() {
    let base = checked(&seed(), CHOICES);
    checked(
        &base,
        r#"class Mid (A : outParam Type) where
  value : A
  stamp : Nat
instance middle {A : Type} [pick : Pick A] : Mid A := Mid.mk pick.value pick.stamp
instance root {A B : Type} [warm : Mid A] [pick : Mid B] [need : Need B] : Root := Root.mk (need.finish pick.value) warm.stamp
def result : Root := inferInstance
theorem resumed : result.value = 9 := by rfl
theorem firstUnchanged : result.stamp = 2 := by rfl"#,
    );
}

#[test]
fn an_open_answer_cannot_override_a_known_output_or_poison_a_later_search() {
    let base = checked(&seed(), CHOICES);
    let base = checked(
        &base,
        r#"instance fallback : Root := Root.mk 7 7
instance incompatible {A : Type} [warm : Pick A] [wrong : Pick Nat] : Root := Root.mk 99 warm.stamp"#,
    );
    checked(
        &base,
        "def result : Root := inferInstance\ntheorem fallbackSelected : result.value = 7 := by rfl",
    );
    let before = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(
            &[b"def wrong : Pick Nat := inferInstance"],
            &KVMap::new(),
            limits()
        )
        .is_err()
    );
    assert_eq!(before, base.logical_root(&KVMap::new()));
    checked(
        &base,
        "instance (priority := 3000) added : Pick Nat := Pick.mk 4 3\ndef result : Pick Nat := inferInstance\ntheorem recovered : result.value = 4 := by rfl",
    );
}

#[test]
fn repeated_impossible_output_queries_reach_the_valid_fallback() {
    let mut source = String::from("class Dead0 (A : outParam Type) where\n  value : A\n");
    for depth in 1..=12 {
        let previous = depth - 1;
        source.push_str(&format!(
            "class Dead{depth} (A : outParam Type) where\n  value : A\ninstance left{depth} {{A : Type}} [d : Dead{previous} A] : Dead{depth} Nat := Dead{depth}.mk 0\ninstance right{depth} {{A : Type}} [d : Dead{previous} A] : Dead{depth} Nat := Dead{depth}.mk 0\n"
        ));
    }
    source.push_str("class Root where\n  value : Nat\ninstance fallback : Root := Root.mk 7\ninstance failing {A : Type} [d : Dead12 A] : Root := Root.mk 99\n");
    let base = checked(&seed(), &source);
    checked(
        &base,
        "def result : Root := inferInstance\ntheorem fallbackWorks : result.value = 7 := by rfl",
    );
    let before = base.logical_root(&KVMap::new());
    let error = base
        .check_source_files(
            &[b"def missing : Dead12 Nat := inferInstance"],
            &KVMap::new(),
            limits(),
        )
        .unwrap_err();
    assert_eq!(error.disposition(), ("elaboration", false, 1));
    assert_eq!(before, base.logical_root(&KVMap::new()));
    checked(
        &base,
        "instance supplied : Dead0 Nat := Dead0.mk 1\ndef result : Root := inferInstance\ntheorem noStaleFailure : result.value = 99 := by rfl",
    );
}

#[test]
fn repeated_semi_output_queries_share_answers_without_erasing_known_filters() {
    let mut source = String::from(
        "class Semi0 (A : semiOutParam Type) where\n  value : A\ninstance semi0 : Semi0 Nat := Semi0.mk 7\n",
    );
    for depth in 1..=12 {
        let previous = depth - 1;
        source.push_str(&format!(
            "class Semi{depth} (A : semiOutParam Type) where\n  value : A\ninstance semi{depth} {{A B : Type}} [first : Semi{previous} A] [second : Semi{previous} B] : Semi{depth} Nat := Semi{depth}.mk 7\n"
        ));
    }
    let base = checked(&seed(), &source);
    checked(
        &base,
        "def result : Semi12 Nat := inferInstance\ntheorem correct : result.value = 7 := by rfl",
    );
    let base = checked(&seed(), &CHOICES.replace("outParam", "semiOutParam"));
    checked(
        &base,
        "instance root {A : Type} [warm : Pick A] [filtered : Pick Nat] : Root := Root.mk filtered.value warm.stamp\ndef result : Root := inferInstance\ntheorem filtered : result.value = 8 := by rfl\ntheorem firstPriority : result.stamp = 2 := by rfl",
    );
}

#[test]
fn recursive_semi_output_variants_do_not_evade_cycle_detection() {
    checked(
        &seed(),
        r#"class Semi (A : semiOutParam Type) where
  value : A
instance (priority := 500) base : Semi Nat := Semi.mk 7
instance (priority := 2000) loop {A : Type} [d : Semi A] : Semi Nat := Semi.mk 9
class Root where
  value : Nat
instance root {A : Type} [s : Semi A] : Root := Root.mk 1
def result : Root := inferInstance
theorem completed : result.value = 1 := by rfl"#,
    );
}

#[test]
fn semi_output_cycle_keys_preserve_repeated_unknowns() {
    checked(
        &seed(),
        r#"class Duo (A : semiOutParam Type) (B : semiOutParam Type) where
  value : Nat
instance (priority := 500) unequal : Duo Nat Bool := Duo.mk 3
instance (priority := 2000) bridge {A B : Type} [d : Duo A B] : Duo Nat Nat := Duo.mk 7
class Root where
  value : Nat
instance root {A : Type} [d : Duo A A] : Root := Root.mk d.value
def result : Root := inferInstance
theorem preserved : result.value = 7 := by rfl"#,
    );
}

#[test]
fn resumed_semi_output_answers_do_not_replace_the_first_priority_answer() {
    let base = checked(&seed(), &CHOICES.replace("outParam", "semiOutParam"));
    checked(
        &base,
        r#"instance root {A B C : Type} [warm : Pick A] [pick : Pick B] [need : Need B] [again : Pick C] : Root := Root.mk (need.finish pick.value) again.stamp
def result : Root := inferInstance
theorem resumed : result.value = 9 := by rfl
theorem firstStillFirst : result.stamp = 2 := by rfl"#,
    );
}
