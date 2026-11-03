//! Real admitted datatype candidates and constructed expression inputs. These
//! test the native data boundary; they are not Reference expansion parity cells.
use super::*;
use crate::{Budget, Engine, EngineAdmissionLimits, KVMap};
use fln_core::expr::{BinderInfo, FVarId, NatLit};
use fln_elab::inductive::{ConstructorSpec, InductiveSpec, inductive_declaration};
use fln_elab::lctx::LocalDecl;
use fln_elab::records::RecordBudget;
use fln_env::constants::{ConstantVal, DefinitionVal, OpaqueVal, ReducibilityHints};
use fln_kernel::Declaration;
use fln_olean::source_extensions::parsers::PARSER_DESCR_CONSTRUCTOR_FIELDS;
use std::sync::OnceLock;

fn c(symbol: &str) -> Expr {
    Expr::const_(name(symbol), vec![])
}

fn app(symbol: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(c(symbol), Expr::app)
}

fn number(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}

fn text(value: &str) -> Expr {
    Expr::lit(Literal::Str(value.into()))
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn definition(symbol: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name(symbol),
            level_params: vec![],
            type_,
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name(symbol)],
    })
}

fn datatype(symbol: &str, constructors: ConstructorFields) -> Declaration {
    inductive_declaration(
        &InductiveSpec {
            name: name(symbol),
            level_params: vec![],
            parameters: vec![],
            indices: vec![],
            constructors: constructors
                .iter()
                .map(|(constructor, fields)| ConstructorSpec {
                    name: Name::from_components([constructor.rsplit('.').next().unwrap()]),
                    fields: fields
                        .iter()
                        .enumerate()
                        .map(|(index, type_)| {
                            let field = format!("field{index}");
                            LocalDecl {
                                id: FVarId(Name::str(name(constructor), &field)),
                                user_name: name(&field),
                                type_: c(type_),
                                value: None,
                                binder_info: BinderInfo::Default,
                                index,
                            }
                        })
                        .collect(),
                    result_indices: vec![],
                })
                .collect(),
            result_level: Level::one(),
        },
        RecordBudget::default(),
    )
    .unwrap()
}

/// Shared by the public artifact/macro integration fixture. Flatten each real
/// block into its type, constructor and recursor rows before artifact emission;
/// ordinary artifact admission independently checks those rows again.
pub(crate) fn fixture_declarations() -> Vec<Declaration> {
    let alias =
        |source: &str, target: &str| definition(source, Expr::sort(Level::one()), c(target));
    vec![
        datatype("Lean.Name", PARSER_NAME_CONSTRUCTOR_FIELDS),
        alias(PARSER_TYPE_ALIASES[0].0, PARSER_TYPE_ALIASES[0].1),
        datatype("Lean.ParserDescr", PARSER_DESCR_CONSTRUCTOR_FIELDS),
        alias(PARSER_TYPE_ALIASES[1].0, PARSER_TYPE_ALIASES[1].1),
    ]
}

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn admit(engine: &Engine, declarations: &[Declaration]) -> Engine {
    engine
        .admit_declarations(declarations, &KVMap::new(), admission())
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

fn scalar_base() -> &'static Engine {
    static BASE: OnceLock<Engine> = OnceLock::new();
    BASE.get_or_init(|| {
        admit(
            &Engine::builder().build_empty(),
            &[
                fln_elab::seed::nat_inductive_seed_declaration(),
                fln_elab::seed::string_seed_declaration(),
                fln_elab::seed::bool_seed_declaration(),
            ],
        )
    })
}

fn base() -> &'static Engine {
    static BASE: OnceLock<Engine> = OnceLock::new();
    BASE.get_or_init(|| {
        let mut declarations = fixture_declarations();
        declarations.extend(
            fln_elab::instances::numeric::declarations()
                .unwrap()
                .declarations
                .into_iter()
                .take(3),
        );
        admit(scalar_base(), &declarations)
    })
}

fn allowed(engine: &Engine) -> BTreeSet<Name> {
    engine
        .environment()
        .constants()
        .map(|(name, _)| name.clone())
        .collect()
}

fn limits() -> DataLimits {
    DataLimits {
        max_steps: 100_000,
        max_depth: 128,
        max_bytes: 16_384,
    }
}

fn string_function(symbol: &str, arity: u32, reversed: bool) -> Declaration {
    let mut value = c("Lean.Name.anonymous");
    for index in 0..arity {
        let variable = if reversed { index } else { arity - 1 - index };
        value = app("Lean.Name.str", [value, b(variable)]);
    }
    let mut type_ = c("Lean.Name");
    for index in (0..arity).rev() {
        let binder = name(&format!("part{index}"));
        type_ = Expr::forall_e(binder.clone(), c("String"), type_, BinderInfo::Default);
        value = Expr::lam(binder, c("String"), value, BinderInfo::Default);
    }
    definition(symbol, type_, value)
}

#[test]
fn actual_mkstr_bodies_preserve_argument_order_and_closed_lexical_scopes() {
    let declarations: Vec<_> = (1..=8)
        .map(|arity| string_function(&format!("Lean.Name.mkStr{arity}"), arity, false))
        .collect();
    let engine = admit(base(), &declarations);
    let permitted = allowed(&engine);
    let mut reader = Reader::new(engine.environment(), &permitted, limits());
    for arity in 1..=8 {
        let pieces: Vec<_> = (0..arity).map(|index| format!("part{index}")).collect();
        let expression = app(
            &format!("Lean.Name.mkStr{arity}"),
            pieces.iter().map(|piece| text(piece)),
        );
        assert_eq!(
            reader.name(Value::closed(expression)).unwrap(),
            Name::from_components(pieces.iter().map(String::as_str))
        );
    }
    let expression = Expr::let_e(
        name("outer"),
        c("String"),
        text("left"),
        Expr::app(
            Expr::lam(
                name("inner"),
                c("String"),
                app("Lean.Name.mkStr2", [b(1), b(0)]),
                BinderInfo::Default,
            ),
            text("right"),
        ),
        false,
    );
    assert_eq!(
        reader.name(Value::closed(expression)).unwrap(),
        name("left.right")
    );
    assert!(reader.used().contains(&name("Lean.Name.mkStr8")));
    assert!(reader.used().contains(&name("Lean.Name.str")));
}

#[test]
fn same_named_helpers_use_their_actual_body_and_do_not_select_intrinsics() {
    let mut zero = number(0);
    let mut type_ = c("Nat");
    for binder in ["right", "left"] {
        zero = Expr::lam(name(binder), c("Nat"), zero, BinderInfo::Default);
        type_ = Expr::forall_e(name(binder), c("Nat"), type_, BinderInfo::Default);
    }
    let engine = admit(
        base(),
        &[
            string_function("Lean.Name.mkStr2", 2, true),
            definition("Nat.add", type_, zero),
        ],
    );
    let permitted = allowed(&engine);
    let mut reader = Reader::new(engine.environment(), &permitted, limits());
    assert_eq!(
        reader
            .name(Value::closed(app(
                "Lean.Name.mkStr2",
                [text("a"), text("b")]
            )))
            .unwrap(),
        name("b.a")
    );
    assert_eq!(
        reader
            .nat_u32(Value::closed(app("Nat.add", [number(4), number(5)])))
            .unwrap(),
        0
    );
}

fn of_nat(number_: u64, dictionary: Expr) -> Expr {
    [c("Nat"), number(number_), dictionary].into_iter().fold(
        Expr::const_(name("OfNat.ofNat"), vec![Level::zero()]),
        Expr::app,
    )
}

#[test]
fn ofnat_reduces_the_actual_polymorphic_projection_and_dictionary_field() {
    let engine = base();
    let permitted = allowed(engine);
    let mut reader = Reader::new(engine.environment(), &permitted, limits());
    let canonical = of_nat(37, app("instOfNatNat", [number(37)]));
    assert_eq!(reader.nat_u32(Value::closed(canonical)).unwrap(), 37);
    let unusual = [c("Nat"), number(7), number(9)].into_iter().fold(
        Expr::const_(name("OfNat.mk"), vec![Level::zero()]),
        Expr::app,
    );
    assert_eq!(
        reader.nat_u32(Value::closed(of_nat(7, unusual))).unwrap(),
        9
    );
    for required in ["OfNat.ofNat", "OfNat", "OfNat.mk", "instOfNatNat"] {
        assert!(reader.used().contains(&name(required)), "{required}");
    }
}

#[test]
fn opaque_values_and_recursor_code_are_not_executable_data() {
    let symbol = name("SecretName");
    let engine = admit(
        base(),
        &[Declaration::Opaque(OpaqueVal {
            base: ConstantVal {
                name: symbol.clone(),
                level_params: vec![],
                type_: c("Lean.Name"),
            },
            value: c("Lean.Name.anonymous"),
            is_unsafe: false,
            all: vec![symbol],
        })],
    );
    let permitted = allowed(&engine);
    let mut reader = Reader::new(engine.environment(), &permitted, limits());
    assert!(matches!(
        reader.name(Value::closed(c("SecretName"))),
        Err(DataError::Unsupported(_))
    ));
    let recursor = Expr::const_(name("Nat.rec"), vec![Level::zero()]);
    assert!(matches!(
        reader.nat_u32(Value::closed(recursor)),
        Err(DataError::Unsupported(_))
    ));
}

#[test]
fn full_datatype_contract_rejects_a_same_named_changed_unused_constructor() {
    const CHANGED: ConstructorFields = &[
        ("Lean.Name.anonymous", &[]),
        ("Lean.Name.str", &["Lean.Name", "Nat"]),
        ("Lean.Name.num", &["Lean.Name", "Nat"]),
    ];
    let engine = admit(scalar_base(), &[datatype("Lean.Name", CHANGED)]);
    let permitted = allowed(&engine);
    let mut reader = Reader::new(engine.environment(), &permitted, limits());
    assert!(matches!(
        reader.name(Value::closed(c("Lean.Name.anonymous"))),
        Err(DataError::Unsupported(
            "parser-description constructor field type"
        ))
    ));
}

#[test]
fn constructor_aliases_follow_checked_bodies_and_reject_changed_pin_targets() {
    let engine = base();
    let permitted = allowed(engine);
    let mut reader = Reader::new(engine.environment(), &permitted, limits());
    reader
        .validate_family(&name("Lean.ParserDescr"), PARSER_DESCR_CONSTRUCTOR_FIELDS)
        .unwrap();
    assert!(reader.used().contains(&name("Lean.SyntaxNodeKind")));
    let altered = admit(
        scalar_base(),
        &[
            datatype("Lean.Name", PARSER_NAME_CONSTRUCTOR_FIELDS),
            definition("Lean.SyntaxNodeKind", Expr::sort(Level::one()), c("String")),
            datatype("Lean.ParserDescr", PARSER_DESCR_CONSTRUCTOR_FIELDS),
        ],
    );
    let permitted = allowed(&altered);
    let mut reader = Reader::new(altered.environment(), &permitted, limits());
    assert_eq!(
        reader.validate_family(&name("Lean.ParserDescr"), PARSER_DESCR_CONSTRUCTOR_FIELDS),
        Err(DataError::Unsupported(
            "parser-description data type alias interface"
        ))
    );
}

#[test]
fn ownership_includes_helpers_and_the_complete_constructor_interface() {
    let engine = admit(base(), &[string_function("Lean.Name.mkStr1", 1, false)]);
    let mut permitted = allowed(&engine);
    permitted.remove(&name("Lean.Name.mkStr1"));
    let mut reader = Reader::new(engine.environment(), &permitted, limits());
    assert!(
        matches!(reader.name(Value::closed(app("Lean.Name.mkStr1", [text("a")]))),
        Err(DataError::NotPermitted(symbol)) if symbol == name("Lean.Name.mkStr1"))
    );
    let mut permitted = allowed(&engine);
    permitted.remove(&name("Lean.Name.num"));
    let mut reader = Reader::new(engine.environment(), &permitted, limits());
    assert!(
        matches!(reader.name(Value::closed(c("Lean.Name.anonymous"))),
        Err(DataError::NotPermitted(symbol)) if symbol == name("Lean.Name.num"))
    );
}

#[test]
fn scalar_constructors_and_numeric_name_components_preserve_their_values() {
    let engine = base();
    let permitted = allowed(engine);
    let mut reader = Reader::new(engine.environment(), &permitted, limits());
    assert!(!reader.boolean(Value::closed(c("Bool.false"))).unwrap());
    assert!(reader.boolean(Value::closed(c("Bool.true"))).unwrap());
    let numeral = app("Nat.succ", [app("Nat.succ", [c("Nat.zero")])]);
    assert_eq!(reader.nat_u32(Value::closed(numeral)).unwrap(), 2);
    let symbol = app(
        "Lean.Name.num",
        [
            app("Lean.Name.str", [c("Lean.Name.anonymous"), text("x.y")]),
            number(42),
        ],
    );
    assert_eq!(
        reader.name(Value::closed(symbol)).unwrap(),
        Name::num(Name::str(Name::anonymous(), "x.y"), 42)
    );
    assert!(matches!(
        reader.nat_u32(Value::closed(number(u64::from(u32::MAX) + 1))),
        Err(DataError::Resource(_))
    ));
    let wide = Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![0, 1])));
    assert!(matches!(
        reader.name(Value::closed(app(
            "Lean.Name.num",
            [c("Lean.Name.anonymous"), wide],
        ))),
        Err(DataError::Resource(_))
    ));
    assert!(matches!(
        reader.nat_u32(Value::closed(app("Nat.succ", [number(u64::MAX)]))),
        Err(DataError::Resource(_))
    ));
}

#[test]
fn projection_requires_the_actual_saturated_record_constructor() {
    let engine = base();
    let permitted = allowed(engine);
    let mut reader = Reader::new(engine.environment(), &permitted, limits());
    for receiver in [
        c("Bool.true"),
        Expr::const_(name("OfNat.mk"), vec![Level::zero()]),
    ] {
        assert!(matches!(
            reader.nat_u32(Value::closed(Expr::proj(name("OfNat"), 0, receiver))),
            Err(DataError::Unsupported(_))
        ));
    }
    let dictionary = [c("Nat"), number(7), number(9)].into_iter().fold(
        Expr::const_(name("OfNat.mk"), vec![Level::zero()]),
        Expr::app,
    );
    assert!(matches!(
        reader.nat_u32(Value::closed(Expr::proj(name("OfNat"), 1, dictionary))),
        Err(DataError::Unsupported(_))
    ));
}

#[test]
fn budgets_accumulate_across_values_and_never_expand_deep_substitutions() {
    let engine = base();
    let permitted = allowed(engine);
    let mut limited = limits();
    limited.max_bytes = 2;
    let mut reader = Reader::new(engine.environment(), &permitted, limited);
    assert_eq!(reader.string(Value::closed(text("ab"))).unwrap(), "ab");
    assert_eq!(reader.remaining_limits().max_bytes, 0);
    assert_eq!(
        reader.string(Value::closed(text("c"))),
        Err(DataError::Resource("parser-description data bytes"))
    );
    let mut exhausted = Reader::new(
        engine.environment(),
        &permitted,
        DataLimits {
            max_steps: 0,
            ..limits()
        },
    );
    assert_eq!(
        exhausted.string(Value::closed(text(""))),
        Err(DataError::Resource("parser-description data steps"))
    );
    let mut expression = text("value");
    for _ in 0..1_000 {
        expression = Expr::let_e(name("unused"), c("Nat"), number(0), expression, true);
    }
    let mut reader = Reader::new(
        engine.environment(),
        &permitted,
        DataLimits {
            max_depth: 8,
            ..limits()
        },
    );
    assert!(matches!(
        reader.string(Value::closed(expression)),
        Err(DataError::Resource(_))
    ));
    let remaining = reader.remaining_limits();
    assert!(remaining.max_steps < limits().max_steps);
    let mut next_module = Reader::new(engine.environment(), &permitted, remaining);
    assert_eq!(next_module.string(Value::closed(text("ok"))).unwrap(), "ok");
    let _bindings = next_module.into_used();
}

#[test]
fn deep_lexical_scopes_are_released_on_a_small_host_stack() {
    let engine = base().clone();
    let permitted = allowed(&engine);
    let mut expression = text("kept");
    for _ in 0..4_096 {
        expression = Expr::let_e(name("unused"), c("Nat"), number(0), expression, true);
    }
    let result = std::thread::Builder::new()
        .name("parser-data-closure-cleanup".into())
        .stack_size(128 * 1024)
        .spawn(move || {
            let mut reader = Reader::new(
                engine.environment(),
                &permitted,
                DataLimits {
                    max_depth: 16_384,
                    ..limits()
                },
            );
            reader.string(Value::closed(expression))
        })
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(result.unwrap(), "kept");
}
