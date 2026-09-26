//! Generated algebraic families use the ordinary two-checker admission path.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome};
use fln_core::expr::{BinderInfo, Expr, FVarId};
use fln_core::level::Level;
use fln_elab::inductive::{ConstructorSpec, InductiveError, InductiveSpec, inductive_declaration};
use fln_elab::lctx::LocalDecl;
use fln_elab::records::RecordBudget;
use fln_kernel::Declaration;

fn name(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn constant(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn field(s: &str, type_: Expr) -> LocalDecl {
    LocalDecl {
        id: FVarId(name(s)),
        user_name: name(s),
        type_,
        value: None,
        binder_info: BinderInfo::Default,
        index: 0,
    }
}
fn spec(s: &str, constructors: Vec<ConstructorSpec>) -> InductiveSpec {
    InductiveSpec {
        name: name(s),
        parameters: vec![],
        indices: vec![],
        level_params: vec![],
        constructors,
        result_level: Level::one(),
    }
}
fn ctor(s: &str, fields: Vec<LocalDecl>) -> ConstructorSpec {
    ConstructorSpec {
        name: name(s),
        fields,
        result_indices: vec![],
    }
}
fn admit(spec: &InductiveSpec) -> Engine {
    let declaration = inductive_declaration(spec, RecordBudget::default()).unwrap();
    let result = engine().admit_declarations(&[declaration], &KVMap::new(), limits());
    result.unwrap().into_complete().unwrap().engine
}
fn proof(engine: &Engine, text: &str) {
    let result = engine.admit_source_declaration(text.as_bytes(), &KVMap::new(), limits());
    assert!(
        matches!(result, Ok(Outcome::Complete(_))),
        "{text}: {result:?}"
    );
}

#[test]
fn arbitrary_constructor_counts_and_dependent_fields_are_dually_checked() {
    let type_field = field("A", Expr::sort(Level::one()));
    let value = field("value", Expr::fvar(type_field.id.clone()));
    let mut data = spec(
        "Payload",
        vec![
            ctor("empty", vec![]),
            ctor("number", vec![field("n", constant("Nat"))]),
            ctor("package", vec![type_field, value]),
        ],
    );
    data.result_level = Level::one().succ().unwrap();
    let e = admit(&data);
    proof(
        &e,
        "theorem number_ok : Payload.number 7 = Payload.number 7 := by rfl",
    );
    proof(
        &e,
        "theorem package_ok : Payload.package Nat 9 = Payload.package Nat 9 := by rfl",
    );
}

#[test]
fn parametric_sums_infer_constructor_parameters() {
    let a = field("A", Expr::sort(Level::one()));
    let b = field("B", Expr::sort(Level::one()));
    let mut data = spec(
        "Either",
        vec![
            ctor("left", vec![field("x", Expr::fvar(a.id.clone()))]),
            ctor("right", vec![field("y", Expr::fvar(b.id.clone()))]),
        ],
    );
    data.parameters = vec![a, b];
    let e = admit(&data);
    proof(&e, "def leftValue : Either Nat Bool := Either.left 9");
    proof(&e, "def rightValue : Either Nat Bool := Either.right true");
}

#[test]
fn direct_recursive_families_have_real_induction_hypotheses() {
    let data = spec(
        "Unary",
        vec![
            ctor("zero", vec![]),
            ctor("succ", vec![field("previous", constant("Unary"))]),
        ],
    );
    let e = admit(&data);
    proof(
        &e,
        "theorem constructor_ok : Unary.succ Unary.zero = Unary.succ Unary.zero := by rfl",
    );
    let info = e.environment().find(&name("Unary.rec")).unwrap();
    let fln_env::constants::ConstantInfo::Rec(rec) = info else {
        panic!("recursor metadata");
    };
    assert_eq!(rec.rules.len(), 2);
    assert_eq!(rec.rules[1].nfields, 1);
}

#[test]
fn forged_recursive_rules_cannot_publish() {
    let data = spec(
        "Unary",
        vec![
            ctor("zero", vec![]),
            ctor("succ", vec![field("previous", constant("Unary"))]),
        ],
    );
    let Declaration::Inductive(mut block) =
        inductive_declaration(&data, RecordBudget::default()).unwrap()
    else {
        panic!("inductive");
    };
    block.recursors[0].rules[1].rhs = Expr::sort(Level::zero());
    let e = engine();
    let before = e.logical_root(&KVMap::new());
    assert!(!matches!(
        e.admit_declarations(&[Declaration::Inductive(block)], &KVMap::new(), limits()),
        Ok(Outcome::Complete(_))
    ));
    assert_eq!(e.logical_root(&KVMap::new()), before);
}

#[test]
fn invalid_constructor_telescope_and_budget_refusals_are_explicit() {
    let negative = Expr::forall_e(
        name("x"),
        constant("Bad"),
        constant("Nat"),
        BinderInfo::Default,
    );
    assert!(
        inductive_declaration(
            &spec("Bad", vec![ctor("mk", vec![field("f", negative)])]),
            RecordBudget::default()
        )
        .is_err()
    );
    assert_eq!(
        inductive_declaration(
            &spec("Bad", vec![ctor("same", vec![]), ctor("same", vec![])]),
            RecordBudget::default()
        ),
        Err(InductiveError::DuplicateConstructor)
    );
    assert_eq!(
        inductive_declaration(
            &spec("Bad", vec![ctor("one", vec![])]),
            RecordBudget {
                max_binders: 0,
                max_nodes: 0
            }
        ),
        Err(InductiveError::ResourceLimit)
    );
    let foreign = field("x", Expr::fvar(FVarId(name("absent"))));
    assert!(
        inductive_declaration(
            &spec("Bad", vec![ctor("mk", vec![foreign])]),
            RecordBudget::default()
        )
        .is_err()
    );
}

/// The payload's type is A -> B, hence its universe is imax u v. Do not
/// pre-normalize that type or replace the field with a synthetic sort witness:
/// the council must independently infer the actual function-field universe.
fn function_box(result_level: Level) -> InductiveSpec {
    let a = field("A", Expr::sort(Level::param(name("u"))));
    let b = field("B", Expr::sort(Level::param(name("v"))));
    let function = Expr::forall_e(
        name("x"),
        Expr::fvar(a.id.clone()),
        Expr::fvar(b.id.clone()),
        BinderInfo::Default,
    );
    let mut data = spec("FunctionBox", vec![ctor("mk", vec![field("f", function)])]);
    data.level_params = vec![name("u"), name("v")];
    data.parameters = vec![a, b];
    data.result_level = result_level;
    data
}

#[test]
fn correlated_function_universes_reach_both_checkers_and_source_reduction() {
    let u = Level::param(name("u"));
    let v = Level::param(name("v"));
    let correlated = Level::imax(u.clone(), v.clone()).unwrap();
    let e = admit(&function_box(
        Level::max(correlated.clone(), Level::one()).unwrap(),
    ));
    assert!(e.environment().find(&name("FunctionBox.mk")).is_some());
    let info = e.environment().find(&name("FunctionBox.rec")).unwrap();
    let fln_env::constants::ConstantInfo::Rec(rec) = info else {
        panic!("independently admitted recursor metadata");
    };
    assert_eq!(rec.rules.len(), 1);
    assert_eq!(rec.rules[0].nfields, 1);
    proof(
        &e,
        "def boxedIdentity : FunctionBox Nat Nat := @FunctionBox.mk Nat Nat (fun x => x)",
    );
    proof(
        &e,
        "theorem read_box : @FunctionBox.rec Nat Nat (fun _ => Nat) (fun f => f 7) (@FunctionBox.mk Nat Nat (fun x => x)) = 7 := by rfl",
    );
    // Both bounds are at least `imax u v` for every `u` and `v`, but the pin's
    // KR-604 check is its syntactic `is_geq`, which proves neither: the pinned
    // kernel's `addDeclCore` refuses both with "universe level of
    // type_of(arg #3) of 'FunctionBox.mk' is too big". K1 answers as the pin
    // does, so the council must refuse them too.
    for bound in [
        correlated.succ().unwrap(),
        Level::imax(u.succ().unwrap(), v).unwrap().succ().unwrap(),
    ] {
        let declaration =
            inductive_declaration(&function_box(bound), RecordBudget::default()).unwrap();
        let refused = engine().admit_declarations(&[declaration], &KVMap::new(), limits());
        assert!(
            !matches!(refused, Ok(Outcome::Complete(_))),
            "a bound the pin refuses was admitted: {refused:?}"
        );
    }
}

#[test]
fn correlated_function_universes_keep_the_zero_codomain_case() {
    let correlated = Level::imax(Level::param(name("u")), Level::param(name("v"))).unwrap();
    let e = admit(&function_box(Level::max(correlated, Level::one()).unwrap()));
    // True : Sort 0, so Nat -> True is a proof even though Nat : Sort 1.
    // The surrounding FunctionBox remains data and may eliminate into Nat.
    proof(
        &e,
        "theorem read_proof_box : @FunctionBox.rec Nat True (fun _ => Nat) (fun _ => 7) (@FunctionBox.mk Nat True (fun _ => True.intro)) = 7 := by rfl",
    );
}

#[test]
fn oversized_function_universes_cannot_publish_and_valid_retry_is_deterministic() {
    let e = engine();
    let before = e.logical_root(&KVMap::new());
    // For u = v = 2 the function field lives in Sort 2, not Sort 1.
    // Generation is not authority; the complete proposed block must be refused.
    let oversized =
        inductive_declaration(&function_box(Level::one()), RecordBudget::default()).unwrap();
    let refused = e.admit_declarations(&[oversized], &KVMap::new(), limits());
    assert!(
        !matches!(refused, Ok(Outcome::Complete(_))),
        "oversized polymorphic payload was admitted: {refused:?}"
    );
    assert_eq!(e.logical_root(&KVMap::new()), before);
    for member in ["FunctionBox", "FunctionBox.mk", "FunctionBox.rec"] {
        assert!(e.environment().find(&name(member)).is_none());
    }

    let correlated = Level::imax(Level::param(name("u")), Level::param(name("v"))).unwrap();
    let valid = function_box(Level::max(correlated, Level::one()).unwrap());
    let declaration = inductive_declaration(&valid, RecordBudget::default()).unwrap();
    let retried = e
        .admit_declarations(&[declaration], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let fresh = admit(&valid);
    assert_eq!(
        retried.logical_root(&KVMap::new()),
        fresh.logical_root(&KVMap::new())
    );
    assert_eq!(e.logical_root(&KVMap::new()), before);
}
