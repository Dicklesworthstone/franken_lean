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
