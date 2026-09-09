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
        level_params: vec![],
        constructors,
        result_level: Level::one(),
    }
}
fn ctor(s: &str, fields: Vec<LocalDecl>) -> ConstructorSpec {
    ConstructorSpec {
        name: name(s),
        fields,
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
