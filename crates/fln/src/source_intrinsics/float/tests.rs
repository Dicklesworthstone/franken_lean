//! Actual pinned data exercises the compiler bridge, not module admission.
//!
//! The fixture keeps decoded declarations and their native/source metadata.
//! Every new source definition and changed model below still passes both
//! ordinary declaration checkers. The Reference supplies no execution fallback.
use super::*;
use fln_elab::externs::{self, ExternEntry};
use fln_elab::instances::imported;
use fln_olean::source_extensions as metadata;
use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::sync::OnceLock;

const STACK: usize = 128 * 1024 * 1024;
const BYTES: usize = 256 * 1024 * 1024;
const MODULES: [&str; 11] = [
    "Init/Prelude",
    "Init/Data/Cast",
    "Init/Core",
    "Init/Data/Int/Basic",
    "Init/Data/Nat/Bitwise/Basic",
    "Init/Data/UInt/BasicAux",
    "Init/Data/String/Bootstrap",
    "Init/Data/Float",
    "Init/Data/Float32",
    "Init/Data/Nat/Log2",
    "Init/Data/OfScientific",
];

struct Fixture {
    environment: Environment,
    externs: BTreeMap<Name, Vec<ExternEntry>>,
}

fn inventory() -> BTreeMap<Name, &'static str> {
    let mut rows = BTreeMap::new();
    for line in DEPENDENCIES.lines() {
        let (encoded, digest) = line.split_once('\t').unwrap();
        let name = dependency_name(encoded, &mut 0, IngressLimits::default()).unwrap();
        assert!(
            rows.insert(name, digest).is_none(),
            "duplicate Float model row"
        );
    }
    assert!(!rows.is_empty());
    rows
}

fn model_roots() -> Vec<Name> {
    let mut roots = Vec::new();
    for float in ["Float", "Float32"] {
        for operation in FLOAT_OPERATIONS
            .iter()
            .copied()
            .chain(["ofScientific", "ofNat"])
        {
            roots.push(name(&format!("{float}.{operation}")));
        }
    }
    for word in ["UInt32", "UInt64"] {
        for operation in ["ofNat", "toNat", "toFloat", "toFloat32"] {
            roots.push(name(&format!("{word}.{operation}")));
        }
    }
    roots.extend(
        [
            "Nat.toFloat",
            "Nat.toFloat32",
            "Float.toFloat32",
            "Float32.toFloat",
            "Bool.rec",
            "True.rec",
            "PUnit.rec",
            "PProd.rec",
            "OfNat.rec",
        ]
        .into_iter()
        .map(name),
    );
    roots
}

fn dependencies(
    constants: &BTreeMap<Name, ConstantInfo>,
    roots: impl IntoIterator<Item = Name>,
) -> BTreeSet<Name> {
    let mut pending: Vec<_> = roots.into_iter().collect();
    let mut result = BTreeSet::new();
    while let Some(label) = pending.pop() {
        if !result.insert(label.clone()) {
            continue;
        }
        let info = constants.get(&label).unwrap_or_else(|| {
            panic!(
                "actual Float dependency {} is missing",
                label.to_display_string()
            )
        });
        let mut expressions = vec![&info.constant_val().type_];
        match info {
            ConstantInfo::Defn(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Opaque(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Thm(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Induct(value) => {
                pending.extend(value.ctors.iter().cloned());
                pending.extend(value.all.iter().cloned());
                for label in &value.all {
                    let recursor = Name::str(label.clone(), "rec");
                    if constants.contains_key(&recursor) {
                        pending.push(recursor);
                    }
                }
            }
            ConstantInfo::Ctor(value) => pending.push(value.induct.clone()),
            ConstantInfo::Rec(value) => {
                pending.extend(value.all.iter().cloned());
                for rule in &value.rules {
                    pending.push(rule.ctor.clone());
                    expressions.push(&rule.rhs);
                }
            }
            _ => {}
        }
        while let Some(expr) = expressions.pop() {
            match expr.node() {
                ExprNode::Const { name, .. } => pending.push(name.clone()),
                ExprNode::App { f, a } => expressions.extend([f, a]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => expressions.extend([binder_type, body]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => expressions.extend([type_, value, body]),
                ExprNode::Proj {
                    struct_name, expr, ..
                } => {
                    pending.push(struct_name.clone());
                    expressions.push(expr);
                }
                ExprNode::MData { expr, .. } => expressions.push(expr),
                _ => {}
            }
        }
    }
    result
}

fn instance_key(key: metadata::InstanceKey) -> fln_elab::instances::discr_tree::Key {
    use fln_elab::instances::discr_tree::Key;
    match key {
        metadata::InstanceKey::Star => Key::Star,
        metadata::InstanceKey::Other => Key::Other,
        metadata::InstanceKey::Lit(literal) => Key::Lit(literal),
        metadata::InstanceKey::FVar(name, arity) => Key::FVar(fln_core::expr::FVarId(name), arity),
        metadata::InstanceKey::Const(name, arity) => Key::Const(name, arity),
        metadata::InstanceKey::Arrow => Key::Arrow,
        metadata::InstanceKey::Proj(name, field, arity) => Key::Proj(name, field, arity),
    }
}

fn fixture() -> Option<&'static Fixture> {
    static FIXTURE: OnceLock<Option<Fixture>> = OnceLock::new();
    FIXTURE
        .get_or_init(|| {
            let library = std::env::var_os("FLN_REFERENCE_LIB")
                .map(PathBuf::from)
                .or_else(|| {
                    std::env::var_os("HOME").map(|home| {
                        PathBuf::from(home)
                            .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
                    })
                })
                .filter(|library| library.is_dir());
            let Some(library) = library else {
                assert!(
                    std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                    "the actual pinned Reference library is required"
                );
                eprintln!("SKIP: pinned Reference lib/lean absent");
                return None;
            };
            let mut constants = BTreeMap::new();
            let mut extern_rows = BTreeMap::new();
            let mut implementation_rows = BTreeMap::new();
            let mut classes = Vec::new();
            let mut instances = Vec::new();
            let mut defaults = Vec::new();
            for module in MODULES {
                let path = library.join(module).with_extension("olean");
                let parts = [
                    std::fs::read(&path).unwrap(),
                    std::fs::read(path.with_extension("olean.server")).unwrap(),
                    std::fs::read(path.with_extension("olean.private")).unwrap(),
                ];
                let decoded = decode_olean_module_artifacts(
                    &parts[0],
                    &parts[1],
                    &parts[2],
                    OleanDecodeLimits::new(BYTES),
                )
                .unwrap();
                let view = if decoded.module.is_module {
                    fln_olean::region::OleanView::parse_with_dependencies(
                        &parts[2],
                        &[parts[0].as_slice(), parts[1].as_slice()],
                    )
                } else {
                    fln_olean::region::OleanView::parse(&parts[0])
                }
                .unwrap();
                let blocks = view
                    .extension_payloads(OleanWalkBudget::default(), BYTES)
                    .unwrap();
                let extensions =
                    metadata::decode(&blocks, metadata::DecodeLimits::default()).unwrap();
                classes.extend(extensions.classes);
                instances.extend(extensions.instances);
                defaults.extend(extensions.defaults);
                for row in extensions.implemented_by {
                    implementation_rows.insert(row.declaration, row.implementation);
                }
                for row in extensions.externs {
                    let entries: Vec<_> = row
                        .entries
                        .into_iter()
                        .map(|entry| match entry {
                            metadata::ExternEntry::Adhoc { backend } => {
                                ExternEntry::Adhoc { backend }
                            }
                            metadata::ExternEntry::Inline { backend, pattern } => {
                                ExternEntry::Inline { backend, pattern }
                            }
                            metadata::ExternEntry::Standard { backend, symbol } => {
                                ExternEntry::Standard { backend, symbol }
                            }
                            metadata::ExternEntry::Opaque => ExternEntry::Opaque,
                        })
                        .collect();
                    if let Some(previous) = extern_rows.insert(row.declaration, entries.clone()) {
                        assert_eq!(previous, entries);
                    }
                }
                for info in decoded.constants {
                    constants.entry(info.name().clone()).or_insert(info);
                }
            }
            // Source notation needs the real dictionaries as well as the primitive
            // model. These extra declarations supply no native authority.
            let mut roots: Vec<_> = inventory().into_keys().collect();
            for label in [
                "instOfNatNat",
                "instHAdd",
                "instHSub",
                "instHMul",
                "instHDiv",
            ] {
                roots.push(name(label));
            }
            for width in ["Float", "Float32"] {
                for class in [
                    "OfNat",
                    "OfScientific",
                    "Add",
                    "Sub",
                    "Mul",
                    "Div",
                    "Neg",
                    "BEq",
                ] {
                    roots.push(name(&format!("inst{class}{width}")));
                }
            }
            // Retain the actual executable companions too: their selected
            // externs must keep precedence before Float's private adaptation.
            roots.extend(
                ["Nat.shiftLeft._unsafe_rec", "Nat.shiftRight._unsafe_rec"]
                    .into_iter()
                    .map(name),
            );
            let needed = dependencies(&constants, roots);
            let mut environment = Environment::new();
            for (label, info) in constants {
                if needed.contains(&label) {
                    environment = environment.add_decl(info).unwrap();
                }
            }
            let mut actual_externs = BTreeMap::new();
            for (label, entries) in extern_rows {
                if environment.contains(&label) {
                    environment = externs::register(&environment, &label, entries.clone()).unwrap();
                    actual_externs.insert(label, entries);
                }
            }
            for (label, target) in implementation_rows {
                if environment.contains(&label) {
                    environment =
                        fln_elab::implemented_by::register(&environment, &label, &target).unwrap();
                }
            }
            let mut activation = imported::ImportActivation::new(environment);
            for row in classes {
                if needed.contains(&row.name) {
                    activation = activation
                        .register_class(
                            &row.name,
                            &imported::ClassParameters {
                                out_params: row.out_params,
                                out_level_params: row.out_level_params,
                            },
                        )
                        .unwrap();
                }
            }
            for row in instances {
                if needed.contains(&row.declaration) {
                    activation = activation
                        .register_instance(
                            &row.declaration,
                            &imported::InstanceParameters {
                                priority: row.priority,
                                synth_order: row.synth_order,
                                scope: row.scope,
                                keys: row.keys.into_iter().map(instance_key).collect(),
                            },
                        )
                        .unwrap();
                }
            }
            for row in defaults {
                if needed.contains(&row.class) && needed.contains(&row.declaration) {
                    activation = activation
                        .register_default(&row.declaration, row.priority)
                        .unwrap();
                }
            }
            Some(Fixture {
                environment: activation.finish().unwrap(),
                externs: actual_externs,
            })
        })
        .as_ref()
}

fn with_fixture(test: impl FnOnce(&Fixture) + Send + 'static) {
    std::thread::Builder::new()
        .name("fln-imported-floats".to_owned())
        .stack_size(STACK)
        .spawn(move || {
            if let Some(fixture) = fixture() {
                test(fixture);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

fn model(environment: &Environment) -> Result<bool, IngressError> {
    matches(
        environment,
        &mut None,
        &mut None,
        &mut 0,
        IngressLimits::default(),
    )
}

#[derive(Debug)]
enum Expected {
    Float(f64),
    Float32(f32),
    Nat(&'static str),
    Bool(bool),
    String(&'static str),
}

fn assert_value(type_: &Expr, exit: &VmExit, expected: &Expected) {
    match expected {
        Expected::Float(value) => assert_eq!(
            closed_float_value(type_, exit).unwrap(),
            Some(ClosedFloatValue::Float(value.to_bits()))
        ),
        Expected::Float32(value) => assert_eq!(
            closed_float_value(type_, exit).unwrap(),
            Some(ClosedFloatValue::Float32(value.to_bits()))
        ),
        Expected::Nat(value) => {
            let VmExit::Returned(returned) = exit else {
                panic!("expected Nat {value}, got {exit:?}");
            };
            assert_eq!(
                fln_vm::interpreter::nat_decimal(&returned.value).as_deref(),
                Some(*value)
            );
        }
        Expected::Bool(value) => assert_eq!(
            closed_vm_value(exit).unwrap(),
            Some(ClosedVmValue::Scalar(usize::from(*value)))
        ),
        Expected::String(value) => assert_eq!(
            closed_vm_value(exit).unwrap(),
            Some(ClosedVmValue::String((*value).to_owned()))
        ),
    }
}

fn execute_and_replay(engine: &Engine, source: &str, expected: &[Expected]) {
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let completed = engine
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &options,
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .unwrap_or_else(|error| panic!("checked imported Float source {source}: {error:?}"))
        .into_complete()
        .unwrap();
    let indices = &completed.batch.source_evaluation_indices;
    assert_eq!(indices.len(), expected.len());
    for (&index, expected) in indices.iter().zip(expected) {
        let execution = &completed.batch.executions[index];
        // #eval's auxiliary is unsafe at the pin (BuiltinEvalCommand.lean:92).
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::UnsafeQuarantine
        );
        assert_value(&execution.runtime_type, &execution.exit, expected);
        let replay = execute_flbc_artifact(
            &execution.flbc_artifact,
            &options,
            FlbcExecutionLimits::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
        assert_value(&execution.runtime_type, &replay, expected);
    }
    assert_eq!(engine.logical_root(&options), before);
}

#[test]
fn actual_scientific_literals_and_float_methods_execute_and_replay() {
    with_fixture(|fixture| {
        let constants = fixture
            .environment
            .constants()
            .map(|(label, info)| (label.clone(), info.clone()))
            .collect();
        assert_eq!(
            dependencies(&constants, model_roots()),
            inventory().into_keys().collect()
        );
        for (label, digest) in inventory() {
            assert_eq!(
                fixture.environment.entry(&label).unwrap().digest().to_hex(),
                digest,
                "{}",
                label.to_display_string()
            );
        }
        assert!(model(&fixture.environment).unwrap());
        execute_and_replay(
            &Engine::from_environment(fixture.environment.clone()),
            r#"
def importedAffine (x slope : Float) : Float := x * slope + 0.5
def importedShift (delta : Float32) : Float32 → Float32 := fun x => x + delta
#eval importedAffine 2.5 4.0
#eval (1.25e2 : Float32)
#eval importedShift 0.25 1.5
#eval Float.sqrt 2.25
#eval Float32.toFloat (Float.toFloat32 1.5)
#eval Float.beq 1.25 1.25
#eval Float.toString 2.1
#eval (let plus := Float.add 0.5; plus 1.25)
"#,
            &[
                Expected::Float(10.5),
                Expected::Float32(125.0),
                Expected::Float32(1.75),
                Expected::Float(1.5),
                Expected::Float(1.5),
                Expected::Bool(true),
                Expected::String("2.100000"),
                Expected::Float(1.75),
            ],
        );
    });
}

#[test]
fn actual_float_bit_helpers_preserve_native_precedence_over_recursive_companions() {
    with_fixture(|fixture| {
        for label in ["Nat.shiftLeft", "Nat.shiftRight"] {
            assert!(
                matches!(
                    fixture.environment.find(&Name::str(name(label), "_unsafe_rec")),
                    Some(ConstantInfo::Defn(value))
                        if value.safety == fln_env::constants::DefinitionSafety::Partial
                ),
                "{label}"
            );
        }
        execute_and_replay(
            &Engine::from_environment(fixture.environment.clone()),
            r#"
def shiftedLeft (n e : Nat) : Nat := Nat.shiftLeft n e
def shiftedRight (n e : Nat) : Nat := Nat.shiftRight n e
def useShift (f : Nat → Nat → Nat) (n e : Nat) : Nat := f n e
def useLog (f : Nat → Nat) (n : Nat) : Nat := f n
#eval shiftedLeft 1 130
#eval shiftedRight 1361129467683753853853498429727072845824 129
#eval useShift Nat.shiftLeft 7 65
#eval useShift Nat.shiftRight 258254417031933722624 64
#eval useLog Nat.log2 1361129467683753853853498429727072845824
"#,
            &[
                Expected::Nat("1361129467683753853853498429727072845824"),
                Expected::Nat("2"),
                Expected::Nat("258254417031933722624"),
                Expected::Nat("14"),
                Expected::Nat("130"),
            ],
        );
    });
}

#[test]
fn actual_float_scaling_accepts_dynamic_logical_ints_and_higher_order_calls() {
    with_fixture(|fixture| {
        execute_and_replay(
            &Engine::from_environment(fixture.environment.clone()),
            r#"
def scale64 (x : Float) (e : Int) : Float := Float.scaleB x e
def scale32 (x : Float32) (e : Int) : Float32 := Float32.scaleB x e
def delayedScale (x : Float) : Int → Float := Float.scaleB x
def useScale (f : Float → Int → Float) (x : Float) (e : Int) : Float := f x e
structure ExponentBox where
  exponent : Int
def boxedScale (b : ExponentBox) (x : Float) : Float := scale64 x b.exponent
#eval scale64 1.5 (Int.ofNat 3)
#eval scale32 1.5 (Int.negSucc 0)
#eval delayedScale 1.5 (Int.ofNat 2)
#eval useScale Float.scaleB 1.5 (Int.negSucc 1)
#eval boxedScale (ExponentBox.mk (Int.negSucc 2)) 8.0
#eval scale64 (Float.ofBits (UInt64.ofNat 4607182418800017409)) (Int.negSucc 1074)
#eval scale32 (Float32.ofBits (UInt32.ofNat 1065353217)) (Int.negSucc 149)
#eval scale64 (Float.ofBits (UInt64.ofNat 1)) (Int.ofNat 1074)
#eval scale32 (Float32.ofBits (UInt32.ofNat 1)) (Int.ofNat 149)
#eval scale64 (-0.0) (Int.negSucc 2147483647)
#eval scale64 (-0.0) (Int.negSucc 2147483648)
#eval scale32 (-0.0) (Int.ofNat 2147483648)
#eval scale64 (-1.0) (Int.ofNat 2147483648)
"#,
            &[
                Expected::Float(12.0),
                Expected::Float32(0.75),
                Expected::Float(6.0),
                Expected::Float(0.375),
                Expected::Float(1.0),
                Expected::Float(f64::from_bits(1)),
                Expected::Float32(f32::from_bits(1)),
                Expected::Float(1.0),
                Expected::Float32(1.0),
                Expected::Float(-0.0),
                Expected::Float(0.0),
                Expected::Float32(0.0),
                Expected::Float(f64::NEG_INFINITY),
            ],
        );
    });
}

#[test]
fn original_float_examples_execute_and_replay_over_the_actual_pin_model() {
    with_fixture(|fixture| {
        let engine = Engine::from_environment(fixture.environment.clone());
        execute_and_replay(
            &engine,
            include_str!("../../../../../examples/native_floats.lean"),
            &[
                Expected::Float(10.5),
                Expected::Float32(3.75),
                Expected::Float(6.0),
                Expected::Float32(-1.25),
            ],
        );
        execute_and_replay(
            &engine,
            include_str!("../../../../../examples/native_float_runtime.lean"),
            &[
                Expected::Float(10.5),
                Expected::Float32(125.0),
                Expected::String("2.100000"),
                Expected::Nat("9223372036854775808"),
            ],
        );
    });
}

#[test]
fn actual_float_words_keep_logical_layout_and_higher_order_calls() {
    with_fixture(|fixture| {
        execute_and_replay(
            &Engine::from_environment(fixture.environment.clone()),
            r#"
def applyFloatBits (f : Float → UInt64) (x : Float) : Nat := UInt64.toNat (f x)
#eval UInt64.toNat (Float.toBits (-0.0 : Float))
#eval UInt32.toNat (Float32.toBits (-0.0 : Float32))
#eval Float.ofBits (UInt64.ofNat 4607182418800017408)
#eval Float32.ofBits (UInt32.ofNat 1065353216)
#eval applyFloatBits Float.toBits 1.0
#eval (let convert := Float.ofBits; convert (Float.toBits 1.5))
#eval (let project := UInt64.toNat; project (Float.toUInt64 42.75))
#eval (let convert := UInt64.toFloat; convert (UInt64.ofNat 42))
#eval UInt32.toNat (UInt32.ofNat 4294967301)
#eval UInt64.toNat (UInt64.ofNat 18446744073709551621)
"#,
            &[
                Expected::Nat("9223372036854775808"),
                Expected::Nat("2147483648"),
                Expected::Float(1.0),
                Expected::Float32(1.0),
                Expected::Nat("4607182418800017408"),
                Expected::Float(1.5),
                Expected::Nat("42"),
                Expected::Float(42.0),
                Expected::Nat("5"),
                Expected::Nat("5"),
            ],
        );
    });
}

fn rebuild(fixture: &Fixture, missing: Option<&Name>, omit_extern: Option<&Name>) -> Environment {
    let mut environment = Environment::new();
    for (label, _) in fixture.environment.constants() {
        if missing != Some(label) {
            environment = environment
                .with_entry(fixture.environment.entry(label).unwrap())
                .unwrap();
        }
    }
    for (label, entries) in &fixture.externs {
        if missing != Some(label) && omit_extern != Some(label) {
            environment = externs::register(&environment, label, entries.clone()).unwrap();
        }
    }
    environment
}

#[test]
fn actual_float_model_refuses_missing_dependencies_foreign_externs_and_exhaustion() {
    with_fixture(|fixture| {
        for label in [
            "Float.ofBits",
            "Float32.ofBits",
            "Float.scaleB",
            "Float32.scaleB",
            "UInt32.ofNat",
            "UInt64.toNat",
            "Int.ofNat",
            "Int.negSucc",
            "Nat.log2",
            "Nat.shiftLeft",
            "Nat.shiftRight",
        ] {
            let missing = rebuild(fixture, None, Some(&name(label)));
            assert!(
                matches!(model(&missing), Err(IngressError::UnsupportedNode { .. })),
                "{label}"
            );
        }
        for label in [
            "Float.ofScientific",
            "Float32.ofScientific",
            "Float.mk",
            "UInt64.ofBitVec",
            "Fin.mk",
            "Int.rec",
        ] {
            assert!(fixture.environment.contains(&name(label)), "{label}");
            assert!(
                !matches!(model(&rebuild(fixture, Some(&name(label)), None)), Ok(true)),
                "{label}"
            );
        }
        for label in [
            "Float.add",
            "Float32.ofBits",
            "Float.scaleB",
            "Float32.scaleB",
            "UInt64.toNat",
            "Int.ofNat",
            "Int.negSucc",
            "Nat.log2",
            "Nat.shiftLeft",
            "Nat.shiftRight",
        ] {
            let changed = externs::register(
                &fixture.environment,
                &name(label),
                vec![ExternEntry::Standard {
                    backend: name("all"),
                    symbol: "counterfeit_float_abi".to_owned(),
                }],
            )
            .unwrap();
            assert!(
                matches!(model(&changed), Err(IngressError::UnsupportedNode { .. })),
                "{label}"
            );
        }
        let mut measured = 0;
        assert!(
            matches(
                &fixture.environment,
                &mut None,
                &mut None,
                &mut measured,
                IngressLimits::default()
            )
            .unwrap()
        );
        assert!(measured > inventory().len());
        let exhausted = matches(
            &fixture.environment,
            &mut None,
            &mut None,
            &mut 0,
            IngressLimits {
                max_nodes: measured - 1,
                ..IngressLimits::default()
            },
        )
        .unwrap_err();
        assert!(exhausted.is_resource_exhaustion());
        assert!(model(&fixture.environment).unwrap());
    });
}

fn lambda_body(type_: &Expr, result: Expr) -> Expr {
    let mut domains = Vec::new();
    let mut current = type_;
    loop {
        match current.node() {
            ExprNode::MData { expr, .. } => current = expr,
            ExprNode::ForallE {
                binder_name,
                binder_type,
                binder_info,
                body,
            } => {
                domains.push((binder_name.clone(), binder_type.clone(), *binder_info));
                current = body;
            }
            _ => break,
        }
    }
    domains
        .into_iter()
        .rev()
        .fold(result, |body, (name, type_, info)| {
            Expr::lam(name, type_, body, info)
        })
}

#[test]
fn well_typed_changed_float_bodies_and_executable_replacements_are_not_the_pin() {
    with_fixture(|fixture| {
        let target = name("Float.add");
        let Some(ConstantInfo::Opaque(original)) = fixture.environment.find(&target) else {
            panic!("actual Float.add opaque");
        };
        let mut changed = original.clone();
        changed.value = lambda_body(&original.base.type_, Expr::bvar(1).unwrap());
        let admitted = Engine::from_environment(rebuild(fixture, Some(&target), None))
            .admit_declaration(
                Declaration::Opaque(changed),
                &KVMap::new(),
                EngineAdmissionLimits::for_stack_bytes(STACK),
            )
            .expect("the changed Float body is ordinarily checked at its real type")
            .into_complete()
            .unwrap();
        assert_eq!(
            admitted.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        let changed = externs::register(
            admitted.engine.environment(),
            &target,
            fixture.externs[&target].clone(),
        )
        .unwrap();
        assert!(matches!(
            model(&changed),
            Err(IngressError::UnsupportedNode { .. })
        ));

        let scientific = name("Float.ofScientific");
        let Some(ConstantInfo::Opaque(original_scientific)) = fixture.environment.find(&scientific)
        else {
            panic!("actual scientific opaque body");
        };
        let mut changed_scientific = original_scientific.clone();
        let zero = Expr::app(
            Expr::const_(name("Float.ofBits"), Vec::new()),
            Expr::app(
                Expr::const_(name("UInt64.ofNat"), Vec::new()),
                Expr::lit(fln_core::expr::Literal::Nat(
                    fln_core::expr::NatLit::from_u64(0),
                )),
            ),
        );
        changed_scientific.value = lambda_body(&original_scientific.base.type_, zero);
        let admitted_scientific =
            Engine::from_environment(rebuild(fixture, Some(&scientific), None))
                .admit_declaration(
                    Declaration::Opaque(changed_scientific),
                    &KVMap::new(),
                    EngineAdmissionLimits::for_stack_bytes(STACK),
                )
                .expect("a different scientific algorithm remains ordinarily well typed")
                .into_complete()
                .unwrap();
        assert_eq!(
            admitted_scientific.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        assert!(matches!(
            model(admitted_scientific.engine.environment()),
            Err(IngressError::UnsupportedNode { .. })
        ));

        let alternate = name("alternateFloatAdd");
        let mut base = original.base.clone();
        base.name = alternate.clone();
        let definition = fln_env::constants::DefinitionVal {
            base,
            value: lambda_body(&original.base.type_, Expr::bvar(1).unwrap()),
            hints: fln_env::constants::ReducibilityHints::Regular(0),
            safety: fln_env::constants::DefinitionSafety::Safe,
            all: vec![alternate.clone()],
        };
        let admitted = Engine::from_environment(fixture.environment.clone())
            .admit_declaration(
                Declaration::Defn(definition),
                &KVMap::new(),
                EngineAdmissionLimits::for_stack_bytes(STACK),
            )
            .expect("replacement Float body is ordinarily checked")
            .into_complete()
            .unwrap();
        assert_eq!(
            admitted.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        let replaced =
            fln_elab::implemented_by::register(admitted.engine.environment(), &target, &alternate)
                .unwrap();
        assert!(matches!(
            model(&replaced),
            Err(IngressError::UnsupportedNode { .. })
        ));
        assert!(model(&fixture.environment).unwrap());
    });
}
