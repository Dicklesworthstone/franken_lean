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
fn record_patterns_select_actual_structure_fields_in_written_order() {
    with_fixture(|base, compiler| {
        check(
            base,
            compiler,
            r#"
structure Pair where
  left : Nat
  right : Nat
def direct : Pair -> Nat | { left := x, right := y } => x
def reordered : Pair -> Nat | { right := y, left := x } => y
def takeRight : Pair -> Nat | { right := y, .. } => y
def annotated : Pair -> Nat | { right := y, .. : Pair } => y
def whole : Pair -> Pair | all@{ left := x, .. } => all
def explicitMatch (p : Pair) : Nat := match p with | { left := x, right := y } => x
def abbreviated : Pair -> Nat | { left, right } => right
theorem direct_eq : Eq (direct { left := 4, right := 9 }) 4 := Eq.refl 4
theorem reordered_eq : Eq (reordered { left := 4, right := 9 }) 9 := Eq.refl 9
theorem partial_eq : Eq (takeRight { left := 4, right := 9 }) 9 := Eq.refl 9
theorem explicit_eq : Eq (explicitMatch { left := 4, right := 9 }) 4 := Eq.refl 4
theorem abbreviated_eq : Eq (abbreviated { left := 4, right := 9 }) 9 := Eq.refl 9
"#,
        );
    });
}

#[test]
fn record_patterns_cover_inherited_nested_and_repeated_field_paths() {
    with_fixture(|base, compiler| {
        check(
            base,
            compiler,
            r#"
structure Base where
  left : Nat
structure Child extends Base where
  right : Nat
structure Nested where
  child : Child
  flag : Bool
def inherited : Child -> Nat | { left := x, right := y } => x
def parent : Child -> Nat | { toBase := { left := x }, right := y } => y
def nested : Nested -> Nat | { child := { right := y, .. }, flag := _ } => y
def dotted : Nested -> Nat | { child.left := x, child.right := y, flag := _ } => x
def alternatives : Nested -> Nat
  | { child.left := x, flag := true, .. } => x
  | { child := { right := y, .. }, flag := false } => y
theorem inherited_eq : Eq (inherited { left := 4, right := 9 }) 4 := Eq.refl 4
theorem parent_eq : Eq (parent { left := 4, right := 9 }) 9 := Eq.refl 9
theorem nested_eq : Eq (nested { child := { left := 4, right := 9 }, flag := true }) 9 := Eq.refl 9
theorem dotted_eq : Eq (dotted { child := { left := 4, right := 9 }, flag := true }) 4 := Eq.refl 4
theorem true_eq : Eq (alternatives { child := { left := 4, right := 9 }, flag := true }) 4 := Eq.refl 4
theorem false_eq : Eq (alternatives { child := { left := 4, right := 9 }, flag := false }) 9 := Eq.refl 9
"#,
        );
    });
}

#[test]
fn dependent_record_patterns_keep_implicit_fields_and_scope_checks() {
    with_fixture(|base, compiler| {
        check(
            base,
            compiler,
            r#"
structure Pack : Type 1 where
  A : Type
  value : A
def rebuild : Pack -> Pack | { A := A, value := x } => { A := A, value := x }
abbrev PackAlias := Pack
def aliasRebuild : PackAlias -> Pack | { A := A, value := x } => { A := A, value := x }
structure ImplicitPack : Type 1 where
  {A : Type}
  value : A
def implicitRebuild : ImplicitPack -> ImplicitPack | { A := A, value := x } => @ImplicitPack.mk A x
def inferred : ImplicitPack -> ImplicitPack | { value := x, .. } => { value := x }
def implicitConstruct : ImplicitPack := ImplicitPack.mk 4
structure InstancePack where
  [inst : Inhabited Nat]
  value : Nat
def instanceRebuild : InstancePack -> InstancePack | { inst := h, value := x } => @InstancePack.mk h x
def instanceIgnored : InstancePack -> Nat | { value := x, .. } => x
def instanceConstruct [h : Inhabited Nat] : InstancePack := InstancePack.mk 4
structure Box (A : Type) where
  value : A
def annotatedColumn : (A : Type) -> Box A -> A
  | A, { value := x : Box A } => x
"#,
        );
    });
}

#[test]
fn record_pattern_branches_execute_on_the_native_vm_like_the_pin() {
    with_fixture(|_, compiler| {
        let library = compiler
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("lib/lean");
        let root_module = Name::from_components(["Init", "Data", "Repr"]);
        let mut pending = vec![root_module.clone()];
        let mut artifacts = std::collections::BTreeMap::new();
        while let Some(module) = pending.pop() {
            if artifacts.contains_key(&module) {
                continue;
            }
            assert!(artifacts.len() < 256, "bounded actual Repr import closure");
            let path = library
                .join(module.to_display_string().replace('.', "/"))
                .with_extension("olean");
            let parts = [
                std::fs::read(&path).unwrap(),
                std::fs::read(path.with_extension("olean.server")).unwrap(),
                std::fs::read(path.with_extension("olean.private")).unwrap(),
            ];
            pending.extend(
                fln::olean_module_imports(&parts[0], fln::OleanDecodeLimits::new(STACK)).unwrap(),
            );
            artifacts.insert(module, parts);
        }
        let inputs: Vec<_> = artifacts
            .iter()
            .map(|(module, parts)| OleanModuleInput {
                name: module,
                artifact: &parts[0],
                server_artifact: Some(&parts[1]),
                private_artifact: Some(&parts[2]),
            })
            .collect();
        let mut admission =
            SourceOleanImportLimits::new(OleanCheckLimits::new(STACK, limits().admission.kernel));
        admission.jobs.threads = std::num::NonZeroUsize::new(1).unwrap();
        admission.jobs.worker_stack_bytes = STACK;
        admission.read_jobs = admission.jobs;
        let base = Engine::builder()
            .build_empty()
            .import_olean_modules_for_source(&inputs, &[root_module], &KVMap::new(), admission)
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
        let source = r#"
structure Base where
  left : Nat
structure Child extends Base where
  right : Nat
structure Nested where
  child : Child
  flag : Bool
def first : Child -> Nat | { left := x, .. } => x
def second : Child -> Nat | { right := y, .. } => y
def total : Child -> Nat | { right := y, left := x } => Nat.add x y
def whole : Child -> Child | all@{ left := _, .. } => all
def nested : Nested -> Nat | { child := { right := y, .. }, flag := _ } => y
def alternatives : Nested -> Nat
  | { child.left := x, flag := true, .. } => x
  | { child := { right := y, .. }, flag := false } => y
def dotted : Nested -> Nat | { child.left := x, child.right := y, flag := _ } => Nat.add x y
#eval first { left := 4, right := 9 }
#eval second { left := 4, right := 9 }
#eval total { left := 4, right := 9 }
#eval (whole { left := 4, right := 9 }).left
#eval nested { child := { left := 4, right := 9 }, flag := true }
#eval alternatives { child := { left := 4, right := 9 }, flag := true }
#eval alternatives { child := { left := 4, right := 9 }, flag := false }
#eval dotted { child := { left := 4, right := 9 }, flag := true }
"#;
        let path = std::env::temp_dir().join(format!(
            "fln-record-pattern-runtime-{}.lean",
            std::process::id()
        ));
        std::fs::write(&path, format!("prelude\nimport Init.Data.Repr\n{source}")).unwrap();
        let pinned = Command::new(compiler).arg(path).output().unwrap();
        assert!(pinned.status.success(), "{pinned:?}");
        assert_eq!(
            String::from_utf8(pinned.stdout).unwrap(),
            "4\n9\n13\n4\n9\n4\n9\n13\n"
        );
        assert!(pinned.stderr.is_empty());
        let options = KVMap::new();
        let root = base.logical_root(&options);
        let result = base
            .execute_source_commands_with_checks(
                source.as_bytes(),
                &options,
                fln::EngineExecutionLimits::new(limits().admission.kernel),
            )
            .unwrap()
            .into_complete()
            .expect("record patterns compile and execute natively");
        let values: Vec<_> = result
            .batch
            .source_evaluation_indices
            .iter()
            .map(|index| {
                fln::closed_vm_value(&result.batch.executions[*index].exit)
                    .unwrap()
                    .unwrap()
            })
            .collect();
        let expected = [4, 9, 13, 4, 9, 4, 9, 13].map(fln::ClosedVmValue::Scalar);
        assert_eq!(values, expected);
        assert_eq!(base.logical_root(&options), root);
    });
}

#[test]
fn invalid_record_patterns_are_semantic_refusals_and_publish_no_declarations() {
    with_fixture(|base, compiler| {
        for source in [
            "structure R where\n a : Nat\n b : Nat\ndef bad : R -> Nat | { a := x } => x",
            "structure R where\n a : Nat\n b : Nat := 8\ndef bad : R -> Nat | { a := x } => x",
            "structure R where\n a : Nat\ndef bad : R -> Nat | { nope := x, .. } => x",
            "structure R where\n a : Nat\ndef bad : R -> Nat | { a := x, a := y } => x",
            "structure R where\n a : Nat\n b : Nat\ndef bad : R -> Nat | { a := x, b := x } => x",
            "inductive R where\n | mk (a : Nat)\ndef bad : R -> Nat | { a := x } => x",
            "structure R where\n {a : Nat}\n b : Nat\ndef bad : R -> Nat | { b := x } => x",
            "structure R where\n [h : Inhabited Nat]\n b : Nat\ndef bad : R -> Nat | { b := x } => x",
            "structure R where\n a : Nat\nstructure S where\n a : Nat\ndef bad : R -> Nat | { a := x : S } => x",
            "structure Base where\n a : Nat\nstructure R extends Base where\n b : Nat\ndef bad : R -> Nat | { toBase := p, a := x, b := y } => x",
            "structure Base where\n a : Nat\n b : Nat\nstructure R where\n inner : Base\ndef bad : R -> Nat | { inner.a := x } => x",
            "structure Pack : Type 1 where\n A : Type\n value : A\ndef bad : Pack -> Pack | { value := x, A := A } => { A := A, value := x }",
            "structure Pack : Type 1 where\n A : Type\n value : A\nabbrev Alias := Pack\ndef bad : Alias -> Pack | { value := x, A := A } => { A := A, value := x }",
            "structure Pack : Type 1 where\n A : Type\n value : A\ndef Alias := Pack\ndef bad : Alias -> Pack | { value := x, A := A } => { A := A, value := x }",
        ] {
            oracle(compiler, source, false);
            let options = KVMap::new();
            let root = base.logical_root(&options);
            let error = base
                .check_source_files(&[source.as_bytes()], &options, limits())
                .unwrap_err();
            assert_eq!(error.disposition().2, 1, "{source}\n{error:?}");
            assert_eq!(
                error.disposition().0,
                "elaboration",
                "semantic refusal required: {source}\n{error:?}"
            );
            assert_eq!(base.logical_root(&options), root);
        }
    });
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

#[test]
fn named_constructor_patterns_select_fields_in_telescope_order() {
    with_fixture(|base, compiler| {
        check(
            base,
            compiler,
            r#"
inductive T where
  | mk (a : Nat) (b : Bool) (c : Nat)
def chosen : T -> Nat
  | T.mk (b := true) (a := x) _ => x
  | _ => 0
def last (t : T) : Nat := match t with | .mk (c := z) .. => z
def mixed : T -> Nat
  | .mk (b := true) (a := x) _ => x
  | .mk x false z => Nat.add x z
def reordered : T -> Nat
  | .mk (c := z) x (b := false) => Nat.add z x
  | .mk (a := x) (c := _) (b := true) => x
theorem chosenTrue : Eq (chosen (.mk 4 true 9)) 4 := rfl
theorem chosenFalse : Eq (chosen (.mk 4 false 9)) 0 := rfl
theorem lastValue : Eq (last (.mk 4 true 9)) 9 := rfl
theorem mixedTrue : Eq (mixed (.mk 4 true 9)) 4 := rfl
theorem mixedFalse : Eq (mixed (.mk 4 false 9)) 13 := rfl
theorem reorderedTrue : Eq (reordered (.mk 4 true 9)) 4 := rfl
theorem reorderedFalse : Eq (reordered (.mk 4 false 9)) 13 := rfl
"#,
        );
    });
}

#[test]
fn named_constructor_patterns_bind_implicit_and_nested_fields() {
    with_fixture(|base, compiler| {
        check(
            base,
            compiler,
            r#"
inductive Box where
  | mk {n : Nat} (value : Nat) : Box
def unbox : Box -> Nat | .mk (n := n) v => Nat.add n v
inductive Pack : Type 1 where
  | mk {A : Type} (value : A) : Pack
def typeOf : Pack -> Type | .mk (value := _) (A := A) => A
def repack : Pack -> Pack | .mk (A := A) (value := x) => @Pack.mk A x
def repackAbsolute : Pack -> Pack | Pack.mk (value := x) (A := A) => @Pack.mk A x
def Ignore (A : Type) : Type := Nat
inductive ErasedPack : Type 1 where
  | mk {A : Type} (value : Ignore A) : ErasedPack
def erasedValue : ErasedPack -> Nat | .mk (value := x) (A := A) => x
inductive Inner where
  | mk (left right : Nat)
inductive Outer where
  | mk (flag : Bool) (inside : Inner)
def nested : Outer -> Nat
  | .mk (inside := .mk (right := y) (left := x)) (flag := true) => Nat.add x y
  | _ => 0
def alias : Outer -> Nat
  | whole@(.mk (inside := inner@(.mk (right := y) ..)) ..) => y
def mixedNested : Outer -> Nat
  | .mk (inside := .mk (left := 0) (right := y)) (flag := _) => y
  | .mk _ (.mk x _) => x
theorem implicitValue : Eq (unbox (.mk (n := 4) 9)) 13 := rfl
theorem implicitType : Eq (typeOf (.mk (A := Nat) 7)) Nat := rfl
theorem dependentField : Eq (repack (.mk (A := Nat) 7)) (.mk (A := Nat) 7) := rfl
theorem absoluteOrder : Eq (repackAbsolute (.mk (A := Nat) 7)) (.mk (A := Nat) 7) := rfl
theorem erasedDependency : Eq (erasedValue (.mk (A := Nat) (7 : Nat))) 7 := rfl
theorem nestedValue : Eq (nested (.mk true (.mk 4 9))) 13 := rfl
theorem nestedFallback : Eq (nested (.mk false (.mk 4 9))) 0 := rfl
theorem aliasValue : Eq (alias (.mk false (.mk 4 9))) 9 := rfl
theorem mixedNestedZero : Eq (mixedNested (.mk false (.mk 0 9))) 9 := rfl
theorem mixedNestedSucc : Eq (mixedNested (.mk true (.mk 4 9))) 4 := rfl
"#,
        );
    });
}

#[test]
fn named_constructor_patterns_preserve_dependent_wildcard_refinement() {
    with_fixture(|base, compiler| {
        check(
            base,
            compiler,
            r#"
inductive V : Nat -> Type where
  | mk (n : Nat) (value : Nat) : V (Nat.succ n)
def readValue (v : V 2) : Nat := match v with | .mk (value := x) (n := _) => x
def equations : V 2 -> Nat | .mk (value := x) (n := _) => x
theorem getValue : Eq (readValue (.mk 1 8)) 8 := rfl
theorem equationValue : Eq (equations (.mk 1 8)) 8 := rfl
"#,
        );
    });
}

#[test]
fn named_constructor_pattern_errors_are_typed_and_publish_nothing() {
    with_fixture(|base, compiler| {
        let prefix = "inductive T where\n  | mk (a : Nat) (b : Bool) (c : Nat)\n";
        let options = KVMap::new();
        let root = base.logical_root(&options);
        for (body, expected) in [
            (
                "def bad : T -> Nat | .mk (missing := x) .. => 0",
                "InvalidNamedArgument",
            ),
            (
                "def bad : T -> Nat | .mk (a := x) (a := y) .. => x",
                "DuplicateNamedArgument",
            ),
            ("def bad : T -> Nat | .mk (a := x) => x", "WrongArity"),
            (
                "def bad : T -> Nat | .mk (a := x) y z extra => x",
                "WrongArity",
            ),
            (
                "def bad : T -> Nat | .mk (a := x) (c := x) .. => x",
                "DuplicateVariable",
            ),
            (
                "def bad : T -> Nat | .mk (a := true) .. => 0",
                "TypeMismatch",
            ),
            (
                "def bad : T -> Nat | .mk (b := true) (a := x) _ => x | .mk x false z => Nat.add x z | .mk _ (b := true) _ => unknownBody",
                "UnreachableRow",
            ),
        ] {
            let source = format!("{prefix}{body}\n");
            oracle(compiler, &source, false);
            let error = base
                .check_source_files(&[source.as_bytes()], &options, limits())
                .unwrap_err();
            assert!(
                format!("{error:?}").contains(expected),
                "{source}\n{error:?}"
            );
            assert_eq!(base.logical_root(&options), root);
            assert!(!base.environment().contains(&Name::from_components(["T"])));
        }
        let source = "inductive V : Nat -> Type where\n  | mk (n : Nat) (value : Nat) : V (Nat.succ n)\ndef bad (v : V 2) : Nat := match v with | .mk (value := x) (n := n) => x\n";
        oracle(compiler, source, false);
        let error = base
            .check_source_files(&[source.as_bytes()], &options, limits())
            .unwrap_err();
        assert!(format!("{error:?}").contains("TypeMismatch"), "{error:?}");
        assert_eq!(base.logical_root(&options), root);
        for family in [
            "def Family (A : Type) : Type := A",
            "opaque Family (A : Type) : Type := A",
        ] {
            let source = format!(
                "{family}\ninductive FamilyPack : Type 1 where\n  | mk (A : Type) (value : Family A) : FamilyPack\ndef bad : FamilyPack -> FamilyPack | .mk (value := x) (A := A) => FamilyPack.mk A x\n"
            );
            oracle(compiler, &source, false);
            let error = base
                .check_source_files(&[source.as_bytes()], &options, limits())
                .unwrap_err();
            assert!(
                format!("{error:?}").contains("TypeMismatch"),
                "{source}\n{error:?}"
            );
            assert_eq!(base.logical_root(&options), root);
        }
        for source in [
            "inductive FamilyPack : Type 1 where\n  | mk (F : Nat -> Type) (value : F 0) : FamilyPack\ndef bad : FamilyPack -> FamilyPack | .mk (value := x) (F := F) => FamilyPack.mk F x\n",
            "inductive PredicatePack where\n  | mk (P : Nat -> Prop) (value : P 0) : PredicatePack\ndef bad : PredicatePack -> PredicatePack | .mk (value := x) (P := P) => PredicatePack.mk P x\n",
            "opaque ProofFamily (h : (n : Nat) -> Eq n n) : Type := Nat\ninductive ProofPack where\n  | mk (h : (n : Nat) -> Eq n n) (value : ProofFamily h) : ProofPack\ndef bad : ProofPack -> ProofPack | .mk (value := x) (h := h) => ProofPack.mk h x\n",
        ] {
            oracle(compiler, source, false);
            let error = base
                .check_source_files(&[source.as_bytes()], &options, limits())
                .unwrap_err();
            assert!(
                format!("{error:?}").contains("TypeMismatch"),
                "{source}\n{error:?}"
            );
            assert_eq!(base.logical_root(&options), root);
        }
        // The relative head's variables are collected in written named-argument order,
        // unlike an absolute head. `x`'s type cannot refer to the later variable `A`.
        let source = "inductive Pack : Type 1 where\n  | mk {A : Type} (value : A) : Pack\ndef bad : Pack -> Pack | .mk (value := x) (A := A) => @Pack.mk A x\n";
        oracle(compiler, source, false);
        let error = base
            .check_source_files(&[source.as_bytes()], &options, limits())
            .unwrap_err();
        assert!(format!("{error:?}").contains("TypeMismatch"), "{error:?}");
        assert_eq!(base.logical_root(&options), root);
    });
}
