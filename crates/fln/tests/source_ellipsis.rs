//! Application ellipsis is checked against the locked compiler and actual Prelude.
#![forbid(unsafe_code)]
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, OleanCheckLimits, OleanModuleInput,
    Outcome, SourceCheckLimits,
};
use fln_core::expr::Expr;
use fln_env::constants::ConstantInfo;
use std::{
    path::{Path, PathBuf},
    process::Command,
    sync::{
        OnceLock,
        atomic::{AtomicUsize, Ordering},
    },
};

const STACK: usize = 128 * 1024 * 1024;
fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)))
}
fn with_fixture(test: impl FnOnce(&Engine, &Path) + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            static FIXTURE: OnceLock<Option<(Engine, PathBuf)>> = OnceLock::new();
            let fixture = FIXTURE.get_or_init(|| {
                let row = include_str!("../../../SUITE.lock")
                    .lines()
                    .find(|line| line.starts_with("reference leanprover/lean4 "))
                    .unwrap();
                let field = |key: &str| {
                    row.split_whitespace()
                        .find_map(|word| word.strip_prefix(key))
                        .unwrap()
                };
                let library = std::env::var_os("FLN_REFERENCE_LIB")
                    .map(PathBuf::from)
                    .or_else(|| {
                        std::env::var_os("HOME").map(|home| {
                            PathBuf::from(home)
                                .join(".elan/toolchains")
                                .join(format!("leanprover--lean4---{}", field("tag=")))
                                .join("lib/lean")
                        })
                    })
                    .filter(|path| path.join("Init/Prelude.olean").is_file());
                let Some(library) = library else {
                    assert!(
                        std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                        "locked Reference required"
                    );
                    eprintln!("SKIP: locked Reference library absent");
                    return None;
                };
                let compiler = library.parent().unwrap().parent().unwrap().join("bin/lean");
                let version = Command::new(&compiler).arg("--version").output().unwrap();
                let text = String::from_utf8(version.stdout).unwrap();
                assert!(
                    version.status.success()
                        && text.contains(field("tag=").trim_start_matches('v'))
                        && text.contains(field("commit=")),
                    "{text}"
                );
                let path = library.join("Init/Prelude.olean");
                let parts = [
                    std::fs::read(&path).unwrap(),
                    std::fs::read(path.with_extension("olean.server")).unwrap(),
                    std::fs::read(path.with_extension("olean.private")).unwrap(),
                ];
                let module = Name::from_components(["Init", "Prelude"]);
                let engine = Engine::builder()
                    .build_empty()
                    .import_olean_modules_for_source(
                        &[OleanModuleInput {
                            name: &module,
                            artifact: &parts[0],
                            server_artifact: Some(&parts[1]),
                            private_artifact: Some(&parts[2]),
                        }],
                        std::slice::from_ref(&module),
                        &KVMap::new(),
                        SourceOleanImportLimits::new(OleanCheckLimits::new(
                            STACK,
                            limits().admission.kernel,
                        )),
                    )
                    .unwrap()
                    .into_complete()
                    .unwrap()
                    .engine;
                Some((engine, compiler))
            });
            if let Some((engine, compiler)) = fixture {
                test(engine, compiler);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
fn oracle(compiler: &Path, source: &str, accepted: bool) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let root = std::env::temp_dir().join(format!("fln-ellipsis-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let path = root.join(format!("{}.lean", NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::write(&path, format!("prelude\nimport Init.Prelude\n{source}")).unwrap();
    let result = Command::new(compiler).arg(path).output().unwrap();
    assert_eq!(
        result.status.success(),
        accepted,
        "{source}\n{}{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
}
fn check(engine: &Engine, compiler: &Path, source: &str) -> Engine {
    oracle(compiler, source, true);
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let result = engine
        .check_source_files(&[source.as_bytes()], &options, limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("source and both admission seats complete")
        .engine;
    assert_eq!(engine.logical_root(&options), root);
    result
}
fn definition(engine: &Engine, name: &str) -> (Expr, Expr) {
    let Some(ConstantInfo::Defn(value)) = engine
        .environment()
        .find(&Name::from_components(name.split('.')))
    else {
        panic!("missing definition {name}");
    };
    (value.base.type_.clone(), value.value.clone())
}
fn same(engine: &Engine, left: &str, right: &str) {
    assert_eq!(
        definition(engine, left),
        definition(engine, right),
        "{left} / {right}"
    );
}

#[test]
fn expected_results_infer_all_explicit_arguments_without_eta_expansion() {
    with_fixture(|base, compiler| {
        let engine = check(
            base,
            compiler,
            r#"
def inferred (n : Nat) : Eq n n := Eq.refl ..
def explicit (n : Nat) : Eq n n := @Eq.refl ..
def spelled (n : Nat) : Eq n n := @Eq.refl Nat n
inductive Triple : Nat -> Nat -> Nat -> Type where
  | mk (a b c : Nat) : Triple a b c
def all : Triple 1 2 3 := Triple.mk ..
def prefixed : Triple 1 2 3 := Triple.mk 1 ..
def named : Triple 1 2 3 := Triple.mk (b := 2) ..
def complete : Triple 1 2 3 := Triple.mk 1 2 3
"#,
        );
        same(&engine, "inferred", "spelled");
        same(&engine, "explicit", "spelled");
        for name in ["all", "prefixed", "named"] {
            same(&engine, name, "complete");
        }
    });
}

#[test]
fn defaults_are_instantiated_after_inferred_arguments_and_explicit_calls_opt_out() {
    with_fixture(|base, compiler| {
        let engine = check(
            base,
            compiler,
            r#"
def chosen (n : Nat := 42) : Nat := n
def implicitDefault : Nat := chosen ..
def explicitDefault : Nat := @chosen 42
def dependent (n : Nat) (m : Nat := n) : Eq n n := Eq.refl n
def inferredDefault (n : Nat) : Eq n n := dependent ..
def spelledDefault (n : Nat) : Eq n n := @dependent n n
def overridden (n : Nat) : Eq n n := dependent (m := 7) ..
def spelledOverride (n : Nat) : Eq n n := @dependent n 7
"#,
        );
        same(&engine, "implicitDefault", "explicitDefault");
        same(&engine, "inferredDefault", "spelledDefault");
        same(&engine, "overridden", "spelledOverride");
    });
}

#[test]
fn local_and_field_applications_keep_supplied_arguments_and_captured_locals() {
    with_fixture(|base, compiler| {
        let engine = check(
            base,
            compiler,
            r#"
def call (f : (n : Nat) -> Eq n n) (x : Nat) : Eq x x := f ..
def callSpelled (f : (n : Nat) -> Eq n n) (x : Nat) : Eq x x := f x
def Nat.atValue (value index : Nat) : Eq index index := Eq.refl index
def fromField (value index : Nat) : Eq index index := value.atValue ..
def fieldSpelled (value index : Nat) : Eq index index := Nat.atValue value index
def witness (A : Type) (f : A -> A) (n : Nat) : Eq n n := Eq.refl n
def higher (n : Nat) : Eq n n := witness Nat (fun x => x) ..
def higherSpelled (n : Nat) : Eq n n := witness Nat (fun x => x) n
"#,
        );
        same(&engine, "call", "callSpelled");
        same(&engine, "fromField", "fieldSpelled");
        same(&engine, "higher", "higherSpelled");
    });
}

#[test]
fn strict_implicit_boundaries_and_explicit_instantiation_follow_the_pin() {
    with_fixture(|base, compiler| {
        let engine = check(
            base,
            compiler,
            r#"
theorem close {A : Type} ⦃x : A⦄ : Eq x x := Eq.refl x
def explicitStrict (n : Nat) : Eq n n := @close ..
def spelledStrict (n : Nat) : Eq n n := @close Nat n
def chosenStrict (n : Nat) : Eq n n := close (x := n) ..
def selected {A : Type} [Inhabited A] : A := default
def ordinary : Nat := selected ..
def spelled : Nat := selected (A := Nat)
def zero : Nat := 0
def noArguments : Nat := zero ..
def noArgumentsSpelled : Nat := zero
"#,
        );
        same(&engine, "explicitStrict", "spelledStrict");
        same(&engine, "chosenStrict", "spelledStrict");
        same(&engine, "ordinary", "spelled");
        same(&engine, "noArguments", "noArgumentsSpelled");
    });
}

#[test]
fn unresolved_ordinary_and_proof_arguments_do_not_gain_search_or_default_authority() {
    with_fixture(|base, compiler| {
        for source in [
            "def bad (a b : Nat) (h : Eq a b) : Eq b a := Eq.symm ..",
            "def choose (n : Nat := 42) : Nat := n\ndef bad : Nat := @choose ..",
            "def selected {A : Type} [Inhabited A] : A := default\ndef bad : Nat := @selected ..",
            "theorem close {A : Type} ⦃x : A⦄ : Eq x x := Eq.refl x\ndef bad : Eq (3 : Nat) 3 := close ..",
            "def pick (x y : Nat) : Nat := x\ndef bad : Nat -> Nat := pick ..",
            "theorem bad : Eq (0 : Nat) 1 := Eq.refl ..",
            "def bad : Eq (3 : Nat) 3 := Eq.refl \"wrong\" ..",
        ] {
            oracle(compiler, source, false);
            let options = KVMap::new();
            let root = base.logical_root(&options);
            let result = base.check_source_files(&[source.as_bytes()], &options, limits());
            assert!(
                result.is_err(),
                "expected semantic refusal, not resource exhaustion: {source}\n{result:?}"
            );
            assert_eq!(base.logical_root(&options), root);
            assert!(!base.environment().contains(&Name::from_components(["bad"])));
        }
        let source = "def repaired (n : Nat) : Eq n n := Eq.refl ..";
        let one = check(base, compiler, source);
        let two = check(base, compiler, source);
        assert_eq!(
            one.logical_root(&KVMap::new()),
            two.logical_root(&KVMap::new())
        );
    });
}

#[test]
fn stopped_admission_and_failed_proofs_publish_no_prefix_and_retry_deterministically() {
    with_fixture(|base, compiler| {
        let source = "theorem value (n : Nat) : Eq n n := Eq.refl ..";
        oracle(compiler, source, true);
        let options = KVMap::new();
        let root = base.logical_root(&options);
        let mut low = limits();
        low.admission.kernel.steps = 1;
        assert!(matches!(
            base.check_source_files(&[source.as_bytes()], &options, low),
            Ok(Outcome::Inconclusive(_))
        ));
        assert_eq!(base.logical_root(&options), root);
        let first = check(base, compiler, source);
        let second = check(base, compiler, source);
        assert_eq!(first.logical_root(&options), second.logical_root(&options));
        let invalid = format!("{source}\ntheorem impossible : Eq (0 : Nat) 1 := Eq.refl ..");
        oracle(compiler, &invalid, false);
        let error = base
            .check_source_files(&[invalid.as_bytes()], &options, limits())
            .unwrap_err();
        assert_ne!(error.disposition().0, "resource", "{error:?}");
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["value"]))
        );
        assert_eq!(base.logical_root(&options), root);
    });
}
