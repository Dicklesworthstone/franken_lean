//! Explicit structure constructors through source elaboration, both checkers,
//! record notation, compiled execution and physical module import.
//! The pin's `Structure.expandCtor` appends the authored suffix unchanged; its
//! kernel uses that whole suffix for the recursor's minor binder.
#![forbid(unsafe_code)]

use fln::source_check::modules::SourceModuleCheckLimits;
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name,
    OleanCheckLimits, OleanModuleInput, OleanWriteBudget, SourceCheckLimits, SourceModuleInput,
    VmExit,
};
use fln_core::expr::ExprNode;
use fln_syntax::tree::Syntax;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn name(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn check(base: &Engine, source: &str) -> fln::SourceFileCheck {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("the full declaration batch passes both checkers")
}

#[test]
fn prelude_constructor_forms_bootstrap_without_seed_declarations() {
    let base = Engine::builder().build_empty();
    let root = base.logical_root(&KVMap::new());
    // These are the constructor forms of the actual Prelude structures. No
    // imported or seeded Prod, And, or PLift can conceal a source refusal. The
    // pin's compiler marker types use ordinary axioms here, accepted by both
    // source doors; unsafe axiom syntax is an independent bootstrap frontier.
    let checked = check(
        &base,
        r#"
universe u v
axiom lcErased : Type
axiom lcAny : Type
axiom lcVoid : Type
structure Prod (A : Type u) (B : Type v) where
  /-- The explicit product constructor. -/
  mk ::
  fst : A
  snd : B
attribute [unbox] Prod
@[pp_using_anonymous_constructor] structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
@[unbox] structure PLift (A : Sort u) : Type u where
  up ::
  down : A
def swap {A : Type u} {B : Type v} (p : Prod A B) : Prod B A :=
  Prod.mk p.snd p.fst
theorem leftProof {a b : Prop} (ha : a) (hb : b) : a :=
  (And.intro ha hb).left
def raised {A : Sort u} (a : A) : PLift A := PLift.up a
"#,
    );
    let env = checked.engine.environment();
    assert_eq!(
        fln_elab::unbox::read(env).unwrap(),
        std::collections::BTreeSet::from([name("Prod"), name("PLift")])
    );
    assert!(
        fln_elab::delaborator_tags::DelaboratorTags::read(env)
            .unwrap()
            .anonymous_constructor(&name("And"))
    );
    for (record, ctor) in [("Prod", "mk"), ("And", "intro"), ("PLift", "up")] {
        let Some(ConstantInfo::Induct(family)) = env.find(&name(record)) else {
            panic!("missing source record {record}");
        };
        let constructor = name(&format!("{record}.{ctor}"));
        assert_eq!(family.ctors.as_slice(), std::slice::from_ref(&constructor));
        assert!(matches!(
            env.find(&constructor),
            Some(ConstantInfo::Ctor(_))
        ));
        assert!(env.contains(&Name::str(constructor, "_flat_ctor")));
        if ctor != "mk" {
            assert!(!env.contains(&name(&format!("{record}.mk"))));
        }
    }
    assert!(base.environment().is_empty());
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

#[test]
fn anonymous_constructor_tags_control_actual_printing_without_inventing_structures() {
    let base = engine();
    let untagged = check(
        &base,
        "structure Pair where\n  x : Nat\n  y : Nat\ndef pair : Pair := Pair.mk 1 2",
    );
    let Some(ConstantInfo::Defn(pair)) = untagged.engine.environment().find(&name("pair")) else {
        panic!("missing checked pair");
    };
    assert_eq!(
        fln::pretty::Printer::new(untagged.engine.environment())
            .expr(&pair.value, 0)
            .unwrap(),
        "{ x := 1, y := 2 }"
    );
    let checked = check(
        &base,
        r#"
structure Pair where
  x : Nat
  y : Nat
attribute [pp_using_anonymous_constructor] Pair Pair
@[pp_using_anonymous_constructor] structure Nested where
  pair : Pair
  last : Nat
@[pp_using_anonymous_constructor] structure EmptyRecord where
@[pp_using_anonymous_constructor] inductive Atom where | mk
@[pp_using_anonymous_constructor] inductive Phantom (A : Type) where | mk
@[pp_using_anonymous_constructor] inductive Recursive where | stop | next (tail : Recursive)
structure CtorOnly where
  value : Nat
attribute [pp_using_anonymous_constructor] CtorOnly.mk
@[pp_using_anonymous_constructor] def identity (n : Nat) : Nat := n
@[pp_using_anonymous_constructor] axiom arbitrary : Type
attribute [pp_using_anonymous_constructor] identity
def pair : Pair := Pair.mk 1 2
def nested : Nested := Nested.mk (Pair.mk 1 2) 3
def empty : EmptyRecord := EmptyRecord.mk
def atom : Atom := Atom.mk
def phantom : Phantom Nat := Phantom.mk
def ctorOnly : CtorOnly := CtorOnly.mk 4
"#,
    );
    let env = checked.engine.environment();
    let tags = fln_elab::delaborator_tags::DelaboratorTags::read(env).unwrap();
    for tagged in [
        "Pair",
        "Nested",
        "EmptyRecord",
        "Atom",
        "Phantom",
        "Recursive",
        "CtorOnly.mk",
        "identity",
        "arbitrary",
    ] {
        assert!(tags.anonymous_constructor(&name(tagged)), "{tagged}");
    }
    assert!(!tags.anonymous_constructor(&name("CtorOnly")));
    let mut printer = fln::pretty::Printer::new(env);
    for (declaration, expected) in [
        ("pair", "⟨1, 2⟩"),
        ("nested", "⟨⟨1, 2⟩, 3⟩"),
        ("empty", "⟨⟩"),
        ("atom", "Atom.mk"),
        ("ctorOnly", "{ value := 4 }"),
    ] {
        let Some(ConstantInfo::Defn(value)) = env.find(&name(declaration)) else {
            panic!("missing checked value {declaration}");
        };
        assert_eq!(
            printer.expr(&value.value, 0).unwrap(),
            expected,
            "{declaration}"
        );
    }
    let Some(ConstantInfo::Defn(phantom)) = env.find(&name("phantom")) else {
        panic!("missing parameterized nullary inductive value");
    };
    let printed = printer.expr(&phantom.value, 0).unwrap();
    assert!(
        printed.contains("Phantom.mk") && !printed.contains('⟨'),
        "{printed}"
    );
}

#[test]
fn anonymous_constructor_tags_preserve_definition_compiler_checks() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for attribute in ["", "@[pp_using_anonymous_constructor] "] {
        let source = format!(
            "noncomputable def unavailable : Nat := 3\n{attribute}def use : Nat := unavailable"
        );
        let error = base
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .unwrap_err();
        assert!(
            format!("{error:?}").contains("NoncomputableDependency"),
            "{error:?}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}

const COMPUTING: &str = r#"
namespace Named
structure Pair (A : Type) where
  /-- Make the two fields. -/
  build ::
  left : A
  right : A
attribute [unbox] Pair Pair
def direct : Pair Nat := Pair.build 7 9
def anonymous : Pair Nat := ⟨7, 9⟩
def literal : Pair Nat := { left := 7, right := 9 }
theorem direct_ok : Eq direct.left 7 := rfl
theorem anonymous_ok : Eq anonymous.right 9 := rfl
theorem literal_ok : Eq literal.left 7 := rfl
def sum (p : Pair Nat) : Nat :=
  match p with
  | Pair.build x y => Nat.add x y
theorem sum_ok : Eq (sum direct) 16 := rfl
theorem recursor_ok :
    Eq (Pair.rec (motive := fun _ => Nat) (fun x _ => x) anonymous) 7 := rfl
@[unbox] structure Bits where
  ofFin ::
  toFin : Nat
def bitValue : Bits := Bits.ofFin 11
theorem bits_ok : Eq bitValue.toFin 11 := rfl
end Named
"#;

#[test]
fn named_constructors_compute_through_patterns_projections_and_the_vm() {
    let base = engine();
    let checked = check(&base, COMPUTING);
    assert_eq!(checked.theorems, 6);
    let env = checked.engine.environment();
    assert!(env.contains(&name("Named.Pair.build._flat_ctor")));
    assert!(!env.contains(&name("Named.Pair.mk")));
    assert!(!env.contains(&name("Named.Bits.mk")));
    assert_eq!(
        fln_elab::unbox::read(env).unwrap(),
        std::collections::BTreeSet::from([name("Named.Pair"), name("Named.Bits")])
    );
    let result = base
        .execute_source_commands_with_checks(
            format!("{COMPUTING}\n#eval Named.sum Named.literal\n").as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let execution = result.batch.executions.last().unwrap();
    let VmExit::Returned(returned) = &execution.exit else {
        panic!("the named constructor program must return");
    };
    assert_eq!(fln::nat_decimal(&returned.value).as_deref(), Some("16"));
    let replay =
        fln::execute_flbc_artifact(&execution.flbc_artifact, &KVMap::new(), Default::default())
            .unwrap()
            .into_complete()
            .unwrap();
    let VmExit::Returned(returned) = replay else {
        panic!("the serialized program must return");
    };
    assert_eq!(fln::nat_decimal(&returned.value).as_deref(), Some("16"));
}

#[test]
fn named_parents_defaults_dependent_fields_and_classes_use_their_real_constructors() {
    let checked = check(
        &engine(),
        r#"
structure Parent where
  pack ::
  x : Nat := 7
structure Child extends Parent where
  assemble ::
  y : Nat := x
def child : Child := {}
def overridden : Child := { x := 12 }
def updated := { child with y := 4 }
theorem child_x : Eq child.x 7 := rfl
theorem child_y : Eq child.y 7 := rfl
theorem override_y : Eq overridden.y 12 := rfl
theorem update_x : Eq updated.x 7 := rfl
theorem update_y : Eq updated.y 4 := rfl
structure Overriding extends Parent where
  replace ::
  x := 10
  y : Nat := x
def altered : Overriding := {}
theorem altered_x : Eq altered.x 10 := rfl
theorem altered_y : Eq altered.y 10 := rfl
structure Package where
  ofValue ::
  carrier : Type := Nat
  value : carrier
  copy : carrier := value
def package : Package := { value := 9 }
theorem package_ok : Eq package.copy (9 : Nat) := rfl
class Token (A : Type) where
  create ::
  token : A
instance : Token Nat := Token.create 8
theorem chosen : Eq (Token.token (A := Nat)) 8 := rfl
structure Conj (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
theorem conjunction (a b : Prop) (ha : a) (hb : b) : a :=
  (Conj.intro ha hb).left
"#,
    );
    // Prop projections are also checked theorems. Assert the actual authored
    // obligations and generated projections rather than an incidental count.
    for theorem in [
        "child_x",
        "child_y",
        "override_y",
        "update_x",
        "update_y",
        "altered_x",
        "altered_y",
        "package_ok",
        "chosen",
        "conjunction",
        "Conj.left",
        "Conj.right",
    ] {
        assert!(
            matches!(
                checked.engine.environment().find(&name(theorem)),
                Some(ConstantInfo::Thm(_))
            ),
            "missing checked theorem {theorem}"
        );
    }
    for ctor in [
        "Parent.pack",
        "Child.assemble",
        "Package.ofValue",
        "Token.create",
    ] {
        assert!(checked.engine.environment().contains(&name(ctor)));
        assert!(
            checked
                .engine
                .environment()
                .contains(&name(&format!("{ctor}._flat_ctor")))
        );
    }
}

#[test]
fn qualified_constructor_suffixes_and_the_mk_field_keep_the_pins_names() {
    let checked = check(
        &engine(),
        r#"
namespace N
structure Named (A : Type) where
  inner.make ::
  value : A
structure Rooted where
  _root_.build ::
  value : Nat
structure HasMk where
  pack ::
  mk : Nat
def named : Named Nat := Named.inner.make 5
def rooted : Rooted := Rooted._root_.build 6
theorem named_ok : Eq named.value 5 := rfl
theorem rooted_ok : Eq rooted.value 6 := rfl
theorem mk_field : Eq (HasMk.pack 7).mk 7 := rfl
end N
"#,
    );
    let env = checked.engine.environment();
    for (record, suffix) in [("N.Named", "inner.make"), ("N.Rooted", "_root_.build")] {
        let Some(ConstantInfo::Rec(rec)) = env.find(&name(&format!("{record}.rec"))) else {
            panic!("missing generated recursor");
        };
        let mut type_ = &rec.base.type_;
        for _ in 0..rec.num_params + rec.num_motives {
            let ExprNode::ForallE { body, .. } = type_.node() else {
                panic!("missing recursor parameter");
            };
            type_ = body;
        }
        let ExprNode::ForallE { binder_name, .. } = type_.node() else {
            panic!("missing constructor minor");
        };
        assert_eq!(binder_name, &name(suffix));
        assert_eq!(rec.rules[0].ctor, name(&format!("{record}.{suffix}")));
        assert!(env.contains(&name(&format!("{record}.{suffix}._flat_ctor"))));
    }
    assert!(!env.contains(&name("build")));
    assert!(matches!(
        env.find(&name("N.HasMk.mk")),
        Some(ConstantInfo::Defn(_))
    ));
}

#[test]
fn generated_constructor_names_preserve_hygienic_record_prefixes() {
    let module = name("Quotation");
    let scoped_name = fln_syntax::hygiene::add_macro_scope(&module, &name("Scoped"), 17).unwrap();
    let user_record = fln_syntax::hygiene::add_macro_scope(&module, &name("N.Scoped"), 17).unwrap();
    for private in [false, true] {
        for (header, suffix) in [("", "mk"), ("  inner.build ::\n", "inner.build")] {
            let source = format!("structure Scoped (A : Type) where\n{header}  value : A\n");
            let mut syntax = fln_parse::parse_definition(source.as_bytes())
                .unwrap()
                .syntax()
                .clone();
            let Syntax::Node {
                args: declaration, ..
            } = &mut syntax
            else {
                panic!("declaration syntax");
            };
            let Syntax::Node {
                args: structure, ..
            } = &mut declaration[1]
            else {
                panic!("structure syntax");
            };
            let Syntax::Node {
                args: identifier, ..
            } = &mut structure[1]
            else {
                panic!("declaration identifier syntax");
            };
            let Syntax::Ident { val, .. } = &mut identifier[0] else {
                panic!("authored structure name");
            };
            *val = scoped_name.clone();
            let scope = fln_elab::source::scope::SourceScope {
                namespace: name("N"),
                private_module: private.then(|| name("Main")),
                ..Default::default()
            };
            let base = Engine::builder().build_empty();
            let record = fln_elab::source::scope::elaborate_record(
                &syntax,
                base.environment(),
                limits().kernel,
                fln_elab::records::RecordBudget::default(),
                &scope,
            )
            .unwrap();
            let actual = if private {
                Name::num(name("_private.Main"), 0).append_core(&user_record)
            } else {
                user_record.clone()
            };
            assert_eq!(record.name, actual);
            let constructor = actual.append_core(&name(suffix));
            assert_eq!(
                record.flat_constructor,
                Name::str(constructor.clone(), "_flat_ctor")
            );
            let checked = base
                .admit_declarations(&record.declarations, &KVMap::new(), limits())
                .unwrap()
                .into_complete()
                .expect("hygienic names preserve ordinary dual-checker admission");
            assert!(matches!(
                checked.engine.environment().find(&constructor),
                Some(ConstantInfo::Ctor(_))
            ));
        }
    }
}

#[test]
fn invalid_constructor_names_and_uses_do_not_publish_partial_records() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "structure FieldCollision where\n  build ::\n  build : Nat\n",
        "structure RecCollision where\n  rec ::\n  value : Nat\n",
        "def Taken.make : Nat := 0\nstructure Taken where\n  make ::\n  value : Nat\n",
        "def Future.fn : Nat := 0\nstructure Future where\n  fn.eq_1 ::\n  value : Nat\n",
        "structure Wrong where\n  build ::\n  value : Nat\ndef wrong : Wrong := Wrong.build true\n",
        "structure NoMk where\n  build ::\n  value : Nat\ndef missing : NoMk := NoMk.mk 0\n",
        "structure Claim where\n  build ::\n  value : Nat\ntheorem wrong : Eq (Claim.build 3).value 4 := rfl\n",
    ] {
        let error = base
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect_err(source);
        assert_ne!(error.disposition().0, "capability", "{source}\n{error:?}");
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&name("Taken.make")));
        assert!(!base.environment().contains(&name("Wrong")));
        assert!(!base.environment().contains(&name("NoMk")));
    }
}

#[test]
fn private_constructor_visibility_is_supported_without_accepting_parameter_overrides() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let module = name("Main");
    let source = "prelude\nstructure Hidden where\n  private create ::\n  value : Nat\n\
        def selected : Hidden := Hidden.create 17\n\
        theorem selectedValue : Eq selected.value 17 := rfl\n";
    let checked = base
        .check_source_modules(
            &[SourceModuleInput {
                name: &module,
                source: source.as_bytes(),
            }],
            &module,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let private_constructor =
        Name::num(name("_private.Main"), 0).append_core(&name("Hidden.create"));
    assert!(matches!(
        checked
            .checked
            .engine
            .environment()
            .find(&private_constructor),
        Some(ConstantInfo::Ctor(_))
    ));
    assert!(
        !checked
            .checked
            .engine
            .environment()
            .contains(&name("Hidden.create"))
    );
    // Changing constructor parameter binder styles is a distinct unsupported
    // feature; implementing visibility must not silently discard the override.
    let unsupported = "structure Override (A : Type) where\n  create {A} ::\n  value : A\n";
    assert!(
        base.check_source_files(
            &[unsupported.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .is_err()
    );
    assert!(!base.environment().contains(&name("Hidden")));
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

#[test]
fn constructor_visibility_and_name_checks_distinguish_authored_private_from_module_defaults() {
    let base = Engine::builder().build_empty();
    let root = base.logical_root(&KVMap::new());
    let module = name("Main");
    let compiler_markers = "axiom lcErased : Type\naxiom lcAny : Type\naxiom lcVoid : Type\n";
    for (source, capability) in [
        (
            format!(
                "prelude\n{compiler_markers}private def Shadow.build : Type := Prop\nstructure Shadow where\n  build ::\n  value : Type\n"
            ),
            false,
        ),
        (
            format!(
                "prelude\n{compiler_markers}private structure Twice where\n  private build ::\n  value : Type\n"
            ),
            false,
        ),
        (
            format!(
                "prelude\n{compiler_markers}private structure TwiceProtected where\n  protected build ::\n  value : Type\n"
            ),
            false,
        ),
    ] {
        let error = base
            .check_source_modules(
                &[SourceModuleInput {
                    name: &module,
                    source: source.as_bytes(),
                }],
                &module,
                &KVMap::new(),
                SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
            )
            .expect_err(&source);
        assert_eq!(
            error.disposition().0 == "capability",
            capability,
            "{source}\n{error:?}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(base.environment().is_empty());
    }
    // Pin-verified (`Lean/Elab/Structure.lean:262`): module-default privacy is not authored
    // `private`, so `protected create ::` is accepted on `structure Hidden` inside a module.
    let module_protected = format!(
        "module\nprelude\npublic section\n{compiler_markers}end\nstructure Hidden where\n  protected create ::\n  value : Type\n"
    );
    let checked = base
        .check_source_modules(
            &[SourceModuleInput {
                name: &module,
                source: module_protected.as_bytes(),
            }],
            &module,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .unwrap_or_else(|error| panic!("{module_protected}\n{error:?}"))
        .into_complete()
        .expect("complete module check");
    let protected =
        fln_elab::protected_names::ProtectedNames::read(checked.checked.engine.environment())
            .unwrap();
    let ctor_name = Name::str(
        Name::str(
            Name::num(Name::from_components(["_private", "Main"]), 0),
            "Hidden",
        ),
        "create",
    );
    assert!(
        protected.contains(&ctor_name),
        "module-default structure protected constructor must be recorded in ProtectedNames"
    );
    let module_private = module_protected.replace("protected create", "private create");
    let private = base
        .check_source_modules(
            &[SourceModuleInput {
                name: &module,
                source: module_private.as_bytes(),
            }],
            &module,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(matches!(
        private.checked.engine.environment().find(&ctor_name),
        Some(ConstantInfo::Ctor(_))
    ));
    assert!(
        !private
            .checked
            .engine
            .environment()
            .contains(&name("Hidden.create"))
    );
}

#[test]
fn named_record_interfaces_survive_compiled_module_boundaries() {
    let base = Engine::builder().build_empty();
    let library = name("Library");
    let main = name("Main");
    let library_source = b"prelude\n\
        axiom lcErased : Type\naxiom lcAny : Type\naxiom lcVoid : Type\n\
        inductive Token where | left | right\n\
        structure Parent where\n  create ::\n  value : Token\n\
        structure Child extends Parent where\n  pack ::\n  extra : Token\n\
        private structure Secret where\n  assemble ::\n  value : Token\n\
        def privateValue : Token := (Secret.assemble Token.left).value\n";
    let main_source = b"prelude\nimport Library\n\
        def original : Child := { value := Token.left, extra := Token.right }\n\
        def copied : Child := { original with value := Token.right }\n";
    let built = base
        .compile_source_modules(
            &[
                SourceModuleInput {
                    name: &library,
                    source: library_source,
                },
                SourceModuleInput {
                    name: &main,
                    source: main_source,
                },
            ],
            &main,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
            OleanWriteBudget::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let inputs: Vec<_> = built
        .artifacts
        .iter()
        .map(|artifact| OleanModuleInput {
            name: &artifact.name,
            artifact: &artifact.bytes,
            server_artifact: artifact
                .companions
                .as_ref()
                .map(|parts| parts.server.as_slice()),
            private_artifact: artifact
                .companions
                .as_ref()
                .map(|parts| parts.private.as_slice()),
        })
        .collect();
    let loaded = base
        .import_olean_modules_for_source(
            &inputs,
            std::slice::from_ref(&main),
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(16 * 1024 * 1024, limits().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    for env in [
        built.checked.checked.engine.environment(),
        loaded.engine.environment(),
    ] {
        assert!(env.contains(&name("Parent.create")));
        assert!(env.contains(&name("Child.pack._flat_ctor")));
        assert!(!env.contains(&name("Parent.mk")));
        assert!(!env.contains(&name("Child.mk")));
    }
    check(
        &loaded.engine,
        "def restored : Child := { value := Token.left, extra := Token.right }\n\
         theorem selected (P : Token -> Prop) (h : P Token.right) : P copied.value := h\n\
         theorem fresh (P : Token -> Prop) (h : P Token.left) : P restored.value := h\n",
    );
    assert!(base.environment().is_empty());
}
