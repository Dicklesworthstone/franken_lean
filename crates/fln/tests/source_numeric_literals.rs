//! Numeric syntax goes through admitted dictionaries and the ordinary council.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};
use fln_core::expr::{Expr, ExprNode, Literal, NatLit};
use fln_env::constants::ConstantInfo;
use fln_syntax::source::SourceInfo;
use fln_syntax::tree::Syntax;

fn base() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
    .unwrap()
    .into_complete()
    .unwrap()
}

fn checked(base: &Engine, source: &str) -> fln::SourceFileCheck {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
            2 * 1024 * 1024,
        ))),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .unwrap()
}

fn value(engine: &Engine, name: &str) -> Expr {
    let Some(ConstantInfo::Defn(info)) = engine.environment().find(&Name::from_components([name]))
    else {
        panic!("expected an admitted source definition: {name}");
    };
    info.value.clone()
}

fn application(mut term: Expr) -> (Expr, Vec<Expr>) {
    let mut arguments = Vec::new();
    loop {
        match term.node() {
            ExprNode::App { f, a } => {
                arguments.push(a.clone());
                term = f.clone();
            }
            ExprNode::MData { expr, .. } => term = expr.clone(),
            _ => break,
        }
    }
    arguments.reverse();
    (term, arguments)
}

fn constant(term: &Expr, name: &str) {
    assert!(
        matches!(term.node(), ExprNode::Const { name: actual, .. }
        if actual == &Name::from_components(name.split('.'))),
        "expected {name}, got {term:?}"
    );
}

fn raw_nat(term: &Expr, expected: u64) {
    assert!(
        matches!(term.node(), ExprNode::Lit { literal: Literal::Nat(value) }
        if value == &NatLit::from_u64(expected)),
        "expected raw {expected}, got {term:?}"
    );
}

fn ascribed_value(term: &Expr, carrier: &str) -> Expr {
    let ExprNode::LetE {
        type_, value, body, ..
    } = term.node()
    else {
        panic!("expected the retained type ascription, got {term:?}");
    };
    constant(type_, carrier);
    assert_eq!(body, &Expr::bvar(0).unwrap());
    value.clone()
}

fn generated_numeral(source: &str, spelling: &str) -> Syntax {
    fn replace(syntax: &mut Syntax, spelling: &str) -> usize {
        let Syntax::Node { kind, args, .. } = syntax else {
            return 0;
        };
        if kind == &Name::from_components(["num"]) {
            *syntax = Syntax::node(
                Name::from_components(["num"]),
                vec![Syntax::atom(SourceInfo::None, spelling)],
            );
            1
        } else {
            args.iter_mut().map(|arg| replace(arg, spelling)).sum()
        }
    }
    let mut syntax = fln_parse::parse_definition(source.as_bytes())
        .unwrap()
        .syntax()
        .clone();
    assert_eq!(replace(&mut syntax, spelling), 1);
    syntax
}

#[test]
fn generated_numerals_keep_their_value_and_ordinary_dictionary_admission() {
    let base = base();
    let options = KVMap::new();
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    for (spelling, expected) in [
        ("0x", NatLit::from_u64(0)),
        ("0b__", NatLit::from_u64(0)),
        ("0o_", NatLit::from_u64(0)),
        ("1_", NatLit::from_u64(1)),
        ("0x_f_", NatLit::from_u64(15)),
        ("0b1_01_", NatLit::from_u64(5)),
        ("00_1", NatLit::from_u64(1)),
        (
            "0x1_0000_0000_0000_0000_",
            NatLit::from_limbs_le(vec![0, 1]),
        ),
        ("18446744073709551617_", NatLit::from_limbs_le(vec![1, 1])),
    ] {
        for (carrier, raw) in [("Nat", false), ("Float", false), ("Nat", true)] {
            let prefix = if raw { "nat_lit " } else { "" };
            let syntax =
                generated_numeral(&format!("def generated : {carrier} := {prefix}7"), spelling);
            let declaration = fln_elab::elaborate_definition_in_with_budget(
                &syntax,
                base.environment(),
                limits.kernel,
            )
            .unwrap_or_else(|error| panic!("{carrier}, raw={raw}, {spelling}: {error:?}"));
            let admitted = base
                .admit_declaration(declaration, &options, limits)
                .unwrap()
                .into_complete()
                .expect("generated numeric syntax must pass both admission seats");
            let value = value(&admitted.engine, "generated");
            let expected = Expr::lit(Literal::Nat(expected.clone()));
            if raw {
                assert_eq!(value, expected);
            } else {
                let (head, args) = application(value);
                constant(&head, "OfNat.ofNat");
                assert_eq!(args.len(), 3);
                constant(&args[0], carrier);
                assert_eq!(args[1], expected);
                let (dictionary, arguments) = application(args[2].clone());
                constant(&dictionary, &format!("instOfNat{carrier}"));
                assert_eq!(arguments, [expected]);
            }
        }
    }
}

#[test]
fn generated_numerals_refuse_invalid_atoms_in_ordinary_and_raw_contexts() {
    let base = base();
    for spelling in [
        "", "_1", "0_", "0_1", "0__1", "0b2", "0o8", "0xg", "-1", "٠1",
    ] {
        for source in [
            "def generated : Nat := 7",
            "def generated : Nat := nat_lit 7",
        ] {
            let result = fln_elab::elaborate_definition_in_with_budget(
                &generated_numeral(source, spelling),
                base.environment(),
                Budget::for_stack_bytes(2 * 1024 * 1024),
            );
            assert!(
                matches!(
                    result,
                    Err(fln_elab::NatDefinitionElabError::InvalidNaturalLiteral)
                ),
                "{source}, {spelling:?}: {result:?}"
            );
        }
    }
}

#[test]
fn source_numerals_preserve_the_pins_prefix_boundary_and_strict_lexing() {
    let base = base();
    checked(
        &base,
        "def ordinary : Nat := 00_1\ndef repeated : Nat := 1__2\ndef raw : Nat := nat_lit 00_1\n\
         theorem ordinary_ok : ordinary = 1 := rfl\n\
         theorem repeated_ok : repeated = 12 := rfl\n\
         theorem raw_ok : raw = 1 := rfl",
    );
    let options = KVMap::new();
    let before = base.logical_root(&options);
    for source in [
        "def bad : Nat := 0_1",
        "def bad : Nat := 0__1",
        "def bad : Nat := nat_lit 0_1",
        "def bad (n : Nat) : Nat := match n with | 0_1 => 7 | _ => 11",
    ] {
        assert!(fln_parse::parse_definition(source.as_bytes()).is_ok());
        let error = base
            .check_source_files(
                &[source.as_bytes()],
                &options,
                SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
                    2 * 1024 * 1024,
                ))),
            )
            .unwrap_err();
        assert!(
            matches!(
                &error,
                fln::SourceCheckError::Command { error, .. }
                    if matches!(
                        error.as_ref(),
                        fln::EngineExecutionError::Frontend(
                            fln::NatDefinitionFrontendError::Elaborate(
                                fln_elab::NatDefinitionElabError::InvalidNaturalLiteral
                            )
                        )
                    )
            ),
            "{source}: {error:?}"
        );
        // Malformed literal data uses the existing input-error taxonomy,
        // distinct from the inference-failure elaboration branch.
        assert_eq!(error.disposition(), ("input", false, 1));
        assert_eq!(base.logical_root(&options), before);
    }
    // Only generated Syntax bypasses lexing. These spellings remain invalid
    // as source tokens even though the public numeric decoder can read them.
    for spelling in ["0x", "0b", "0o", "1_", "0x1_"] {
        assert!(
            fln_parse::parse_definition(format!("def bad : Nat := {spelling}").as_bytes()).is_err(),
            "{spelling}"
        );
    }
}

#[test]
fn scientific_literals_retain_the_pins_class_application_and_raw_components() {
    let checked = checked(
        &base(),
        "def wide : Float := 1.25\ndef narrow : Float32 := 1.25e+2\ndef inferred := 1.5",
    );
    for (name, carrier, mantissa, sign, exponent) in [
        ("wide", "Float", 125, "Bool.true", 2),
        ("narrow", "Float32", 125, "Bool.false", 0),
        ("inferred", "Float", 15, "Bool.true", 1),
    ] {
        let (head, args) = application(value(&checked.engine, name));
        constant(&head, "OfScientific.ofScientific");
        assert_eq!(args.len(), 5);
        constant(&args[0], carrier);
        constant(&args[1], &format!("instOfScientific{carrier}"));
        raw_nat(&args[2], mantissa);
        constant(&args[3], sign);
        raw_nat(&args[4], exponent);
    }
}

#[test]
fn ordinary_numerals_keep_ofnat_instead_of_becoming_float_bit_literals() {
    let checked = checked(
        &base(),
        "def natural := 7\ndef wide : Float := 7\ndef narrow : Float32 := 7\ndef addition (x : Float) : Float := x + 2.25\ndef negative : Float32 := -1.5\ndef explicit : Float := OfNat.ofNat (α := Float) 3",
    );
    for (name, carrier, dictionary) in [
        ("natural", "Nat", "instOfNatNat"),
        ("wide", "Float", "instOfNatFloat"),
        ("narrow", "Float32", "instOfNatFloat32"),
    ] {
        let (head, args) = application(value(&checked.engine, name));
        constant(&head, "OfNat.ofNat");
        assert_eq!(args.len(), 3);
        constant(&args[0], carrier);
        raw_nat(&args[1], 7);
        let (instance, parameters) = application(args[2].clone());
        constant(&instance, dictionary);
        assert_eq!(parameters.len(), 1);
        raw_nat(&parameters[0], 7);
    }
    let addition = value(&checked.engine, "addition");
    let ExprNode::Lam { body, .. } = addition.node() else {
        panic!("source function retains its binder");
    };
    constant(&application(body.clone()).0, "HAdd.hAdd");
    constant(
        &application(value(&checked.engine, "negative")).0,
        "Neg.neg",
    );
    let (head, args) = application(value(&checked.engine, "explicit"));
    constant(&head, "OfNat.ofNat");
    constant(&args[0], "Float");
    let (index, _) = application(args[1].clone());
    constant(&index, "OfNat.ofNat");
}

#[test]
fn field_notation_defaults_numeric_receiver_types_before_method_lookup() {
    let checked = checked(
        &base(),
        "theorem natural : (2).succ = 3 := by rfl\ndef decimal := (1.5).abs\ndef small := (1.5 : Float32).abs",
    );
    constant(
        &application(value(&checked.engine, "decimal")).0,
        "Float.abs",
    );
    constant(
        &application(value(&checked.engine, "small")).0,
        "Float32.abs",
    );
}

#[test]
fn expected_precision_reaches_nested_operations_and_function_arguments() {
    let checked = checked(
        &base(),
        concat!(
            "def choose (flag : Bool) (x y : Float32) : Float32 := if flag then x else y\n",
            "def selected := choose true (1.5 + 2.25) (9.0 / 2.0)\n",
            "def infinite := Float32.isInf (1.0 / 0.0)\n",
            "def nested : Float32 := -(1.5 + 2 * (4.0 - 0.5))\n",
            "def mixed (x : Float32) := (1.0 + 2.0) * x\n",
        ),
    );
    for name in ["selected", "nested"] {
        let Some(ConstantInfo::Defn(info)) = checked
            .engine
            .environment()
            .find(&Name::from_components([name]))
        else {
            panic!("expected admitted definition {name}");
        };
        constant(&info.base.type_, "Float32");
    }
}

#[test]
fn numeric_aliases_preserve_explicit_types_and_matching_custom_instances() {
    let checked = checked(
        &base(),
        concat!(
            "def NumericAlias (A : Type) : Type := A\n",
            "def fromExplicit : NumericAlias Nat := (7 : Nat)\n",
            "def scientificExplicit : NumericAlias Float := (1.25 : Float)\n",
            "instance customLiteral : OfNat (NumericAlias Nat) 7 := { ofNat := (8 : Nat) }\n",
            "def fromCustom : NumericAlias Nat := 7\n",
            "theorem explicit_ok : fromExplicit = (7 : Nat) := by rfl\n",
            "theorem custom_ok : fromCustom = (8 : Nat) := by rfl\n",
        ),
    );
    let (explicit_head, explicit_args) = application(ascribed_value(
        &value(&checked.engine, "fromExplicit"),
        "Nat",
    ));
    constant(&explicit_head, "OfNat.ofNat");
    assert_eq!(explicit_args.len(), 3);
    constant(&explicit_args[0], "Nat");
    raw_nat(&explicit_args[1], 7);
    constant(&application(explicit_args[2].clone()).0, "instOfNatNat");
    let (scientific_head, scientific_args) = application(ascribed_value(
        &value(&checked.engine, "scientificExplicit"),
        "Float",
    ));
    constant(&scientific_head, "OfScientific.ofScientific");
    assert_eq!(scientific_args.len(), 5);
    constant(&scientific_args[0], "Float");
    constant(&scientific_args[1], "instOfScientificFloat");
    raw_nat(&scientific_args[2], 125);
    constant(&scientific_args[3], "Bool.true");
    raw_nat(&scientific_args[4], 2);
    let (_, custom_args) = application(value(&checked.engine, "fromCustom"));
    constant(&custom_args[2], "customLiteral");
}

#[test]
fn user_scientific_instances_and_expected_types_control_literal_meaning() {
    checked(
        &base(),
        concat!(
            "structure DecimalParts where\n  mantissa : Nat\n  negativeExponent : Bool\n  exponent : Nat\n",
            "instance decimalScientific : OfScientific DecimalParts := { ofScientific := fun m s e => { mantissa := m, negativeExponent := s, exponent := e } }\n",
            "def parts : DecimalParts := 1.25e-2\n",
            "theorem mantissa_ok : parts.mantissa = 125 := by rfl\n",
            "theorem exponent_ok : parts.exponent = 4 := by rfl\n",
            "theorem sign_ok : parts.negativeExponent = true := by rfl\n",
        ),
    );
}

#[test]
fn heterogeneous_user_operations_keep_their_input_and_output_types() {
    let checked = checked(
        &base(),
        concat!(
            "instance natBoolAdd : HAdd Nat Bool Nat := { hAdd := fun n flag => if flag then n else 0 }\n",
            "instance natNatToBool : HAdd Nat Nat Bool := { hAdd := fun x y => Nat.beq x y }\n",
            "def selected : Nat := (7 : Nat) + true\n",
            "def compared : Bool := (3 : Nat) + (3 : Nat)\n",
            "theorem selected_ok : selected = 7 := by rfl\n",
            "theorem compared_ok : compared = true := by rfl\n",
        ),
    );
    for (name, left, right, output, instance) in [
        ("selected", "Nat", "Bool", "Nat", "natBoolAdd"),
        ("compared", "Nat", "Nat", "Bool", "natNatToBool"),
    ] {
        let (head, args) = application(value(&checked.engine, name));
        constant(&head, "HAdd.hAdd");
        assert_eq!(args.len(), 6);
        for (argument, expected) in args.iter().zip([left, right, output, instance]) {
            constant(argument, expected);
        }
    }
}

#[test]
fn unsupported_numeric_types_and_mixed_widths_cannot_publish() {
    let base = base();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : Nat := 1.5",
        "def bad : String := 1.5",
        "def bad (A : Type) : A := 1.5",
        "def bad : Float := (1.5 : Float32)",
        "def bad := (1.5 : Float) + (2.5 : Float32)",
        "def bad : False := 0",
    ] {
        let result = base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
                2 * 1024 * 1024,
            ))),
        );
        assert!(!matches!(result, Ok(Outcome::Complete(_))), "{source}");
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}
