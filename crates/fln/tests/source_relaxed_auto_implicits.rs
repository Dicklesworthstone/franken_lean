//! The pin's relaxed auto-implicit policy applies to inferred term indices as
//! well as carriers. All inferred binders still enter ordinary checked headers.
#![forbid(unsafe_code)]

use fln::source_check::modules::SourceModuleCheckLimits;
use fln::{
    BinderInfo, Budget, ConstantInfo, Engine, EngineAdmissionLimits, Expr, ExprNode, KVMap, Name,
    SourceCheckLimits, SourceModuleInput,
};
use std::path::PathBuf;
use std::process::Command;

// This retains the declaration and anonymous-instance shape of Prelude's
// TSyntax, with a small source-built syntax type and Nat syntax kinds.
const INDEXED_INSTANCE: &str = r#"namespace RelaxedHeader
inductive Syntax where
  | missing
  | atom (kind : Nat)
def SyntaxNodeKinds := List Nat
structure TSyntax (ks : SyntaxNodeKinds) where
  raw : Syntax
instance : Inhabited Syntax where
  default := Syntax.missing
instance : Inhabited (TSyntax ks) where
  default := ⟨default⟩
def emptySyntax : TSyntax (List.nil : SyntaxNodeKinds) := default
theorem default_raw : emptySyntax.raw = Syntax.missing := rfl
def recoverKinds (_value : TSyntax syntaxKinds) : SyntaxNodeKinds := syntaxKinds
theorem recovered_kinds : recoverKinds emptySyntax = (List.nil : SyntaxNodeKinds) := rfl
end RelaxedHeader
"#;

const TYPE_HEADERS: &str = r#"def keepCarrier (value : inferredCarrier) : inferredCarrier := value
def Applied (family : Type → Type) : Type := family Nat
def keepFamily (value : Applied inferredFamily) : Applied inferredFamily := value
def InstalledCarrier : Type := Nat
def useInstalled (value : InstalledCarrier) : InstalledCarrier := value
theorem carrier_result : keepCarrier (7 : Nat) = 7 := rfl
theorem family_result : @keepFamily (fun _ : Type => Nat) (9 : Nat) = (9 : Nat) := rfl
theorem installed_result (value : InstalledCarrier) : useInstalled value = value := rfl
"#;

const SCOPED_OPTIONS: &str = r#"set_option relaxedAutoImplicit false in
def strictSuffix (value : α₁') : α₁' := value
section
set_option relaxedAutoImplicit false
set_option relaxedAutoImplicit true in
def explicitlyRelaxed (value : longCarrier) : longCarrier := value
end
def defaultRestored (value : anotherCarrier) : anotherCarrier := value
set_option autoImplicit false in
def explicitlyBound (carrier : Type) (value : carrier) : carrier := value
theorem strict_works : strictSuffix (5 : Nat) = 5 := rfl
theorem restored_works : defaultRestored (7 : Nat) = 7 := rfl
"#;

const UNIVERSE_HEADERS: &str = r#"def relaxedUniverse (A : Sort wideUniverse) (value : A) : A := value
set_option relaxedAutoImplicit false in
def strictUniverse (A : Sort u₁') (value : A) : A := value
set_option autoImplicit false in
def anonymousUniverse (A : Sort _) (value : A) : A := value
universe DeclaredLevel
set_option autoImplicit false in
def explicitUniverse (A : Sort DeclaredLevel) (value : A) : A := value
set_option relaxedAutoImplicit false in
def explicitStrictUniverse (A : Sort DeclaredLevel) (value : A) : A := value
"#;

// In a prelude-free environment these names are unknown, so the pin treats
// them as implicit parameters. They are never guessed to be Init constants.
// Noncomputable declarations need no compiler marker constants from Prelude.
const EMPTY_PRELUDE: &str = "prelude\nnoncomputable def keepUnit (value : Unit) : Unit := value\nnoncomputable def keepIO (value : IO) : IO := value\n";

const REFUSED: &[&str] = &[
    "set_option autoImplicit false in\ndef disabled (value : longCarrier) : longCarrier := value\n",
    "set_option relaxedAutoImplicit false in\ndef strict (value : longCarrier) : longCarrier := value\n",
    "def selfName (value : selfName) : Nat := 0\n",
    "def qualified (value : MissingNamespace.Carrier) : Nat := 0\n",
    "def rooted (value : _root_.missingCarrier) : Nat := 0\n",
    "def bodyOnly : Nat := missingBodyValue\n",
    "def cannotGuessFamily (value : unavailableFamily Nat) : unavailableFamily Nat := value\n",
    "def later (carrier : Type) (value : carrier) (proof : value = laterValue) : Nat := 0\n",
    "structure Indexed (index : Nat) where\n  value : Nat\ndef wrongResult (_value : Indexed indexValue) : Bool := indexValue\n",
    "structure Indexed (index : Nat) where\n  value : Nat\nset_option relaxedAutoImplicit false in\ninstance : Inhabited (Indexed indexValue) where\n  default := ⟨0⟩\n",
    "structure Indexed (index : Nat) where\n  value : Nat\nset_option autoImplicit false in\ninstance : Inhabited (Indexed k) where\n  default := ⟨0⟩\n",
    "set_option relaxedAutoImplicit false\nset_option relaxedAutoImplicit true in\ndef temporarilyAllowed (value : longCarrier) : longCarrier := value\ndef stillStrict (value : secondCarrier) : secondCarrier := value\n",
    "macro \"unknownHeader\" : term => `(macroOnlyCarrier)\ndef hygienic (value : unknownHeader) : Nat := 0\n",
    "set_option autoImplicit false in\ndef noUniverse (A : Sort u) (value : A) : A := value\n",
    "set_option relaxedAutoImplicit false in\ndef longUniverse (A : Sort wideUniverse) (value : A) : A := value\n",
    "set_option relaxedAutoImplicit false in\ndef upperUniverse (A : Sort U) (value : A) : A := value\n",
    "set_option relaxedAutoImplicit false in\ndef greekUniverse (A : Sort α) (value : A) : A := value\n",
];

fn name(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20))
}

fn on_stack(body: impl FnOnce() + Send) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(16 << 20)
            .spawn_scoped(scope, body)
            .unwrap()
            .join()
            .unwrap();
    });
}

fn seed() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .unwrap()
    .engine
}

fn first_binder(engine: &Engine, declaration: &str) -> (Name, BinderInfo, Expr) {
    let constant = engine
        .environment()
        .find(&name(declaration))
        .unwrap_or_else(|| panic!("missing {declaration}"));
    let ExprNode::ForallE {
        binder_name,
        binder_type,
        binder_info,
        ..
    } = constant.constant_val().type_.node()
    else {
        panic!("{declaration} has no parameter")
    };
    (binder_name.clone(), *binder_info, binder_type.clone())
}

#[test]
fn anonymous_instances_infer_multi_letter_term_indices_before_their_bodies() {
    on_stack(|| {
        let base = seed();
        let checked = checked(&base, INDEXED_INSTANCE);
        let instance = "RelaxedHeader.instInhabitedTSyntax";
        let (binder, style, type_) = first_binder(&checked, instance);
        assert_eq!(binder, name("ks"));
        assert_eq!(style, BinderInfo::Implicit);
        assert_eq!(
            type_,
            Expr::const_(name("RelaxedHeader.SyntaxNodeKinds"), vec![])
        );
        assert!(matches!(
            checked.environment().find(&name(instance)),
            Some(ConstantInfo::Defn(_))
        ));
        assert!(!checked.environment().is_assumed(&name(instance)));
        assert!(matches!(
            checked
                .environment()
                .find(&name("RelaxedHeader.default_raw")),
            Some(ConstantInfo::Thm(_))
        ));
        assert_eq!(
            first_binder(&checked, "RelaxedHeader.recoverKinds").0,
            name("syntaxKinds")
        );
        assert!(!base.environment().contains(&name(instance)));
    });
}

#[test]
fn relaxed_headers_infer_types_and_type_families_without_shadowing_known_globals() {
    on_stack(|| {
        let checked = checked(&seed(), TYPE_HEADERS);
        let (carrier, style, type_) = first_binder(&checked, "keepCarrier");
        assert_eq!(carrier, name("inferredCarrier"));
        assert_eq!(style, BinderInfo::Implicit);
        assert!(matches!(type_.node(), ExprNode::Sort { .. }));
        let (family, style, type_) = first_binder(&checked, "keepFamily");
        assert_eq!(family, name("inferredFamily"));
        assert_eq!(style, BinderInfo::Implicit);
        assert!(matches!(type_.node(), ExprNode::ForallE { .. }));
        let (value, style, type_) = first_binder(&checked, "useInstalled");
        assert_eq!(value, name("value"));
        assert_eq!(style, BinderInfo::Default);
        assert_eq!(type_, Expr::const_(name("InstalledCarrier"), vec![]));
    });
}

#[test]
fn strict_and_relaxed_options_are_scoped_and_explicit_parameters_still_work() {
    on_stack(|| {
        let checked = checked(&seed(), SCOPED_OPTIONS);
        for (declaration, binder) in [
            ("strictSuffix", "α₁'"),
            ("explicitlyRelaxed", "longCarrier"),
            ("defaultRestored", "anotherCarrier"),
        ] {
            let (actual, style, _) = first_binder(&checked, declaration);
            assert_eq!(actual, name(binder));
            assert_eq!(style, BinderInfo::Implicit);
        }
        assert_eq!(
            first_binder(&checked, "explicitlyBound").1,
            BinderInfo::Default
        );
    });
}

#[test]
fn universe_names_obey_both_options_while_explicit_names_and_holes_remain_valid() {
    on_stack(|| {
        let checked = checked(&seed(), UNIVERSE_HEADERS);
        for (declaration, parameter) in [
            ("relaxedUniverse", "wideUniverse"),
            ("strictUniverse", "u₁'"),
            ("explicitUniverse", "DeclaredLevel"),
            ("explicitStrictUniverse", "DeclaredLevel"),
        ] {
            let constant = checked.environment().find(&name(declaration)).unwrap();
            assert_eq!(constant.constant_val().level_params, [name(parameter)]);
            assert_eq!(first_binder(&checked, declaration).1, BinderInfo::Default);
        }
        let constant = checked
            .environment()
            .find(&name("anonymousUniverse"))
            .unwrap();
        assert_eq!(constant.constant_val().level_params.len(), 1);
        assert!(!constant.constant_val().type_.has_level_mvar());
    });
}

#[test]
fn empty_world_headers_use_the_same_relaxed_policy_without_assumed_init_names() {
    on_stack(|| {
        let initial = Engine::builder().build_empty();
        let module = name("EmptyAutoImplicit");
        let checked = initial
            .check_source_modules(
                &[SourceModuleInput {
                    name: &module,
                    source: EMPTY_PRELUDE.as_bytes(),
                }],
                &module,
                &KVMap::new(),
                SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        assert!(initial.environment().is_empty());
        for (declaration, binder) in [("keepUnit", "Unit"), ("keepIO", "IO")] {
            let (actual, style, type_) = first_binder(&checked.checked.engine, declaration);
            assert_eq!(actual, name(binder));
            assert_eq!(style, BinderInfo::Implicit);
            assert!(matches!(type_.node(), ExprNode::Sort { .. }));
            assert!(!checked.checked.engine.environment().contains(&name(binder)));
        }
    });
}

#[test]
fn unknown_bodies_qualified_names_hygiene_and_invalid_headers_remain_refused() {
    on_stack(|| {
        let base = seed();
        let root = base.logical_root(&KVMap::new());
        for source in REFUSED {
            assert!(
                base.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits()),
                )
                .is_err(),
                "accepted {source}"
            );
            assert_eq!(base.logical_root(&KVMap::new()), root);
        }
    });
}

#[test]
fn exact_pin_agrees_on_relaxed_header_option_and_unknown_name_cases() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let library = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(library.parent()?.parent()?.join("bin/lean"))
        })
        .filter(|path| path.is_file());
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference is required"
        );
        eprintln!("SKIP: relaxed auto-implicit differential requires the pinned Reference");
        return;
    };
    let identity = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(identity.status.success());
    assert_eq!(
        String::from_utf8(identity.stdout).unwrap().trim(),
        fln::OLEAN_PIN_COMMIT
    );
    let root = std::env::temp_dir().join(format!(
        "fln-relaxed-auto-implicits-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&root).unwrap();
    let accepted = [
        INDEXED_INSTANCE,
        TYPE_HEADERS,
        SCOPED_OPTIONS,
        UNIVERSE_HEADERS,
        EMPTY_PRELUDE,
    ];
    for (index, (source, accepted)) in accepted
        .into_iter()
        .map(|source| (source, true))
        .chain(REFUSED.iter().map(|source| (*source, false)))
        .enumerate()
    {
        let file = root.join(format!("case-{index}.lean"));
        std::fs::write(&file, source).unwrap();
        let output = Command::new(&reference)
            .current_dir(&root)
            .env_remove("LEAN_PATH")
            .env_remove("LEAN_SYSROOT")
            .arg("-j1")
            .arg(&file)
            .output()
            .unwrap();
        assert_eq!(output.status.success(), accepted, "{source}\n{output:?}");
    }
}
