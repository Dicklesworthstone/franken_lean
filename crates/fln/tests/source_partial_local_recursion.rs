//! Partial local closures keep checked logical interfaces, complete executable
//! groups, and their actual lexical captures. Oracle shapes were checked against
//! Lean 8c9756b28d64dab099da31a4c09229a9e6a2ef35.
#![forbid(unsafe_code)]

use fln::{
    BinderInfo, Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, ExprNode, KVMap,
    Name, Outcome, SourceCheckLimits, VmExit,
};
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use std::sync::OnceLock;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn seed() -> Engine {
    static SEED: OnceLock<Engine> = OnceLock::new();
    SEED.get_or_init(|| {
        Engine::with_source_seed(limits())
            .unwrap()
            .into_complete()
            .unwrap()
    })
    .clone()
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("both checkers completed")
    .engine
}

fn values(base: &Engine, source: &str) -> Vec<String> {
    let batch = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("native execution completed");
    batch
        .source_evaluation_indices
        .iter()
        .map(|&index| {
            let VmExit::Returned(value) = &batch.executions[index].exit else {
                panic!("expected a returned Nat: {:?}", batch.executions[index]);
            };
            fln_vm::interpreter::nat_decimal(&value.value).expect("Nat result")
        })
        .collect()
}

fn binders(engine: &Engine, declaration: &str) -> Vec<(String, BinderInfo)> {
    let info = engine.environment().find(&name(declaration)).unwrap();
    let mut type_ = &info.constant_val().type_;
    let mut result = Vec::new();
    while let ExprNode::ForallE {
        binder_name,
        binder_info,
        body,
        ..
    } = type_.node()
    {
        result.push((binder_name.to_display_string(), *binder_info));
        type_ = body;
    }
    result
}

fn explicit_binders(engine: &Engine, declaration: &str, expected: &[&str]) {
    let expected: Vec<_> = expected
        .iter()
        .map(|text| ((*text).to_owned(), BinderInfo::Default))
        .collect();
    assert_eq!(binders(engine, declaration), expected, "{declaration}");
}

fn partial_group(engine: &Engine, members: &[&str]) {
    let expected: Vec<_> = members.iter().map(|text| name(text)).collect();
    let mut ordering = None;
    for member in &expected {
        let Some(ConstantInfo::Opaque(logical)) = engine.environment().find(member) else {
            panic!("expected a checked opaque interface: {member:?}");
        };
        assert!(!logical.is_unsafe);
        assert_eq!(logical.all.len(), expected.len());
        assert!(expected.iter().all(|peer| logical.all.contains(peer)));
        if let Some(ordering) = &ordering {
            assert_eq!(&logical.all, ordering);
        } else {
            ordering = Some(logical.all.clone());
        }
        let Some(ConstantInfo::Defn(executable)) = engine
            .environment()
            .find(&Name::str(member.clone(), "_unsafe_rec"))
        else {
            panic!("missing executable companion: {member:?}");
        };
        assert_eq!(executable.safety, DefinitionSafety::Partial);
        assert_eq!(executable.base.type_, logical.base.type_);
        assert_eq!(executable.base.level_params, logical.base.level_params);
        assert_eq!(
            executable.all,
            logical
                .all
                .iter()
                .map(|peer| Name::str(peer.clone(), "_unsafe_rec"))
                .collect::<Vec<_>>()
        );
    }
}

fn ordinary_owner(engine: &Engine, owner: &str) {
    assert!(matches!(
        engine.environment().find(&name(owner)),
        Some(ConstantInfo::Defn(definition)) if definition.safety == DefinitionSafety::Safe
    ));
    assert!(
        !engine
            .environment()
            .contains(&Name::str(name(owner), "_unsafe_rec"))
    );
}

fn refuses(base: &Engine, source: &str) {
    let before = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .is_err(),
        "accepted {source}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
}

const CYCLE: &str = r#"
partial def cycle (limit offset n : Nat) : Nat :=
  if n == 0 then offset
  else
    let rec loop (i : Nat) : Nat :=
      if i == limit then cycle limit offset (n - 1) else loop (i + 1)
    loop 0
"#;

const LOCAL: &str = r#"
partial def localOnly (target offset : Nat) : Nat :=
  let rec loop (i : Nat) : Nat :=
    if i == target then offset else loop (i + 1)
  loop 0
"#;

const LEXICAL: &str = r#"
partial def lexical (input : Nat) : Nat :=
  let target := input + 2
  let answer := target + 3
  let rec loop (i : Nat) : Nat :=
    if i == target then answer else loop (i + 1)
  loop 0
"#;

#[test]
fn owner_and_nested_helper_cycles_have_complete_checked_groups() {
    let base = checked(&seed(), CYCLE);
    partial_group(&base, &["cycle", "cycle.loop"]);
    explicit_binders(&base, "cycle", &["limit", "offset", "n"]);
    explicit_binders(&base, "cycle.loop", &["limit", "offset", "n", "i"]);
    assert_eq!(values(&base, "#eval cycle 3 42 2"), ["42"]);

    let nested = checked(
        &base,
        r#"
partial def nested (target offset : Nat) : Nat :=
  let rec middle (j : Nat) : Nat :=
    let rec inner (i : Nat) : Nat :=
      if i == target then if j == 0 then offset else middle (j - 1)
      else inner (i + 1)
    inner 0
  middle 2
"#,
    );
    ordinary_owner(&nested, "nested");
    partial_group(&nested, &["nested.middle", "nested.middle.inner"]);
    explicit_binders(&nested, "nested.middle", &["target", "offset", "j"]);
    explicit_binders(
        &nested,
        "nested.middle.inner",
        &["target", "offset", "j", "i"],
    );
    assert_eq!(values(&nested, "#eval nested 3 42"), ["42"]);
}

#[test]
fn helper_only_recursion_captures_actual_values_and_can_escape() {
    let base = checked(&checked(&seed(), LOCAL), LEXICAL);
    ordinary_owner(&base, "localOnly");
    ordinary_owner(&base, "lexical");
    partial_group(&base, &["localOnly.loop"]);
    partial_group(&base, &["lexical.loop"]);
    explicit_binders(&base, "localOnly.loop", &["target", "offset", "i"]);
    // Neither `input` nor the definitions of these already evaluated locals
    // belong to the helper's argument list.
    explicit_binders(&base, "lexical.loop", &["target", "answer", "i"]);
    assert_eq!(
        values(&base, "#eval localOnly 3 42\n#eval lexical 37"),
        ["42", "42"]
    );

    let base = checked(
        &base,
        r#"
partial def factory (target offset : Nat) : Nat → Nat :=
  let rec loop (i : Nat) : Nat :=
    if i == target then offset else loop (i + 1)
  loop
partial def localAnswer : Nat :=
  let rec loop (i : Nat) : Nat :=
    if i == 3 then 42 else loop (i + 1)
  loop 0
partial def unusedOwner : Nat :=
  let rec unused (i : Nat) : Nat := unusedOwner
  42
"#,
    );
    ordinary_owner(&base, "factory");
    partial_group(&base, &["factory.loop"]);
    ordinary_owner(&base, "localAnswer");
    partial_group(&base, &["localAnswer.loop"]);
    explicit_binders(&base, "localAnswer.loop", &["i"]);
    // The unused declaration is still checked, but its reference to the owner
    // cannot manufacture an owner-to-helper edge or a false recursive cycle.
    ordinary_owner(&base, "unusedOwner");
    ordinary_owner(&base, "unusedOwner.unused");
    explicit_binders(&base, "unusedOwner.unused", &["i"]);
    let Some(ConstantInfo::Defn(factory)) = base.environment().find(&name("factory")) else {
        panic!("factory must remain a safe function producer");
    };
    let mut body = &factory.value;
    let mut stages = 0;
    while let ExprNode::Lam { body: next, .. } = body.node() {
        stages += 1;
        body = next;
    }
    assert_eq!(
        stages, 2,
        "returning a closure must not eta-expand its owner"
    );
    assert_eq!(
        values(
            &base,
            "#eval localAnswer\n#eval unusedOwner\n#eval let first := factory 3 41; let second := factory 3 7; first 0 + second 0"
        ),
        ["42", "42", "48"]
    );
}

#[test]
fn dependent_instances_heap_values_and_callbacks_survive_recursive_captures() {
    let base = checked(
        &seed(),
        r#"
universe u
partial def dependent {A : Type u} [inst : Inhabited A] (target : Nat) : A :=
  let rec loop (i : Nat) : A :=
    if i == target then default else loop (i + 1)
  loop 0
partial def captured (message : String) (step : Nat → Nat) (target : Nat) : Nat :=
  let rec loop (i : Nat) : Nat :=
    if i == target then step (String.length message) else loop (i + 1)
  loop 0
partial def textLoop (message : String) (target : Nat) : String :=
  let rec loop (i : Nat) : String :=
    if i == target then message ++ "!" else loop (i + 1)
  loop 0
"#,
    );
    partial_group(&base, &["dependent.loop"]);
    assert_eq!(
        binders(&base, "dependent.loop"),
        [
            ("A".to_owned(), BinderInfo::Implicit),
            ("inst".to_owned(), BinderInfo::InstImplicit),
            ("target".to_owned(), BinderInfo::Default),
            ("i".to_owned(), BinderInfo::Default),
        ]
    );
    explicit_binders(&base, "captured.loop", &["message", "step", "target", "i"]);
    explicit_binders(&base, "textLoop.loop", &["message", "target", "i"]);
    assert_eq!(
        values(
            &base,
            r#"
#eval @dependent Nat ⟨43⟩ 3
#eval captured ("abc" ++ "def") (fun n => n + 36) 5
#eval captured "x" (fun n => n + 5) 2
#eval String.length (textLoop ("abc" ++ "def") 4)
"#
        ),
        ["43", "42", "6", "7"]
    );
}

#[test]
fn partial_helpers_do_not_authorize_proofs_unsafe_links_or_total_recursion() {
    let base = checked(&checked(&seed(), CYCLE), LOCAL);
    for source in [
        "theorem falseComputation : localOnly.loop 3 42 3 = 42 := by rfl",
        "def unsafeLeak : Nat := localOnly.loop._unsafe_rec 3 42 0",
        "def ordinary (n : Nat) : Nat := let rec loop (i : Nat) : Nat := if i == n then 7 else loop (i + 1); loop 0",
        "partial def falseHelper (n : Nat) : Nat := let rec impossible (i : Nat) : False := impossible (i + 1); n",
        "partial def typeCycle (n : Nat) : Nat := let rec loop (i : Nat) : typeCycle n = 0 := loop (i + 1); n",
        "partial def inBody (n : Nat) : Nat := let rec loop (i : Nat) : Nat := if i == n then 7 else loop (i + 1); have h : loop n = 7 := by rfl; n",
        "partial def badBody (n : Nat) : Nat := let rec loop (i : Nat) : Nat := true; n",
    ] {
        refuses(&base, source);
    }
    assert_eq!(values(&base, "#eval cycle 3 42 2"), ["42"]);
}

#[test]
fn closure_names_are_deterministic_and_collisions_roll_back_every_candidate() {
    let base = seed();
    let before = base.logical_root(&KVMap::new());
    let first = checked(&base, LEXICAL);
    let second = checked(&base, LEXICAL);
    assert_eq!(
        first.logical_root(&KVMap::new()),
        second.logical_root(&KVMap::new())
    );
    for declaration in ["lexical", "lexical.loop", "lexical.loop._unsafe_rec"] {
        assert_eq!(
            first.environment().find(&name(declaration)),
            second.environment().find(&name(declaration))
        );
    }
    assert_eq!(base.logical_root(&KVMap::new()), before);
    for collision in ["lexical.loop", "lexical.loop._unsafe_rec"] {
        let occupied = checked(&base, &format!("def {collision} (n : Nat) : Nat := n"));
        refuses(&occupied, LEXICAL);
        assert!(!occupied.environment().contains(&name("lexical")));
        assert_eq!(values(&occupied, &format!("#eval {collision} 42")), ["42"]);
    }
    assert_eq!(values(&first, "#eval lexical 37"), ["42"]);
}

#[test]
fn nonterminating_local_helpers_exhaust_the_vm_without_running_inhabitants() {
    let base = checked(
        &checked(&seed(), LOCAL),
        "partial def spin (start : Nat) : Nat := let rec loop (i : Nat) : Nat := loop (i + 1); loop start",
    );
    ordinary_owner(&base, "spin");
    partial_group(&base, &["spin.loop"]);
    let before = base.logical_root(&KVMap::new());
    let mut execution = EngineExecutionLimits::new(limits().kernel);
    execution.vm.max_steps = 1000;
    assert!(matches!(
        base.execute_source_definitions(&[b"#eval spin 0"], &KVMap::new(), execution)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&KVMap::new()), before);
    assert_eq!(
        values(&base, "#eval localOnly 3 42\n#eval localOnly 2 7"),
        ["42", "7"]
    );
}

#[test]
fn unused_helpers_share_owner_universes_before_component_partitioning() {
    let base = checked(
        &seed(),
        r#"
universe u
partial def keepUniverse (A : Type u) (x : A) : A :=
  let rec echo (i : Nat) : Nat := i
  let rec loop (i : Nat) : Nat := loop (i + 1)
  x
def inheritedLoop : Nat -> Nat := keepUniverse.loop.{0}
"#,
    );
    ordinary_owner(&base, "keepUniverse");
    ordinary_owner(&base, "keepUniverse.echo");
    partial_group(&base, &["keepUniverse.loop"]);
    for declaration in [
        "keepUniverse",
        "keepUniverse.echo",
        "keepUniverse.loop",
        "keepUniverse.loop._unsafe_rec",
    ] {
        assert_eq!(
            base.environment()
                .find(&name(declaration))
                .unwrap()
                .constant_val()
                .level_params,
            [name("u")],
            "{declaration}"
        );
    }
    assert_eq!(
        values(
            &base,
            "#eval keepUniverse.{0} Nat 37\n#eval keepUniverse.echo.{0} 19"
        ),
        ["37", "19"]
    );
}

#[test]
fn owner_retains_ordered_universes_used_only_by_an_unused_helper() {
    let base = checked(
        &seed(),
        r#"
partial def unusedUniverse.{v, u} (n : Nat) : Nat :=
  let rec loop (A : Type u) (B : Type v) (x : A) (y : B) (i : Nat) : A :=
    loop A B x y (i + 1)
  n
def explicitHelper (A B : Type) (x : A) (y : B) : Nat -> A :=
  unusedUniverse.loop.{0, 0} A B x y
"#,
    );
    ordinary_owner(&base, "unusedUniverse");
    partial_group(&base, &["unusedUniverse.loop"]);
    for declaration in [
        "unusedUniverse",
        "unusedUniverse.loop",
        "unusedUniverse.loop._unsafe_rec",
    ] {
        assert_eq!(
            base.environment()
                .find(&name(declaration))
                .unwrap()
                .constant_val()
                .level_params,
            [name("v"), name("u")],
            "{declaration}"
        );
    }
    assert_eq!(values(&base, "#eval unusedUniverse.{0, 0} 23"), ["23"]);
}
