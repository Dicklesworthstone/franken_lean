//! Constructor fields whose types carry the pin's type-annotation gadgets: `optParam`
//! defaults (`(m : Nat := 3)`), a written `autoParam`, `outParam` and `semiOutParam`, also on
//! parameters, indices, recursive-field arguments and under later dependent fields (bead
//! `fln-optparam-constructor-field-recursor-1b0b`). The family and constructor types keep the
//! annotations; the pin's kernel opens every recursor local through `mk_local_decl`, which
//! drops them (`consume_type_annotations`, vendored `src/kernel/inductive.cpp:178-185`), so
//! `T.rec`'s minor premise reads `(n m : Nat)` where `T.a` reads `(m : optParam Nat 3)`.
//!
//! The fixture is compiled by the pinned `lean -o` over the real `Init.Core` closure, that
//! artifact is rechecked here through both admission seats, and every listed declaration this
//! engine elaborates from the same source must equal the pin's, constant for constant: the
//! families, constructors, recursors and their rules, `casesOn`, `recOn`, `below` and `brecOn`.
//! The program's `match`, `cases` and `induction` uses must be accepted on both sides.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::{SourceOleanImport, SourceOleanImportLimits};
use fln::{
    Budget, Engine, EngineAdmissionLimits, Environment, KVMap, Name, OleanCheckLimits,
    OleanDecodeLimits, OleanModuleInput, Outcome, SourceCheckLimits,
};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;

const STACK: usize = 256 * 1024 * 1024;
const BYTES: usize = 256 * 1024 * 1024;
const HEADER: &str = "prelude\nimport Init.Core\n";

/// Accepted by the pinned `lean` v4.32.0 with `HEADER` (2026-10-23, exit 0, no messages).
///
/// Families omit their result sort where the pin infers it (`fln-inductive-inferred-sort-normalization-f178`).
/// `V` is only accepted, not compared: under `n : optParam Nat 2`, `n + 1` is stored here as
/// `@HAdd.hAdd (optParam Nat 2) Nat Nat …` where the pin's `HAdd` output is `optParam Nat 2`, as
/// it is for an `axiom` with the same binders; `D` is the same family without the operator.
const FIXTURE: &str = "inductive T where
  | a (n : Nat) (m : Nat := 3)
example : T.a 1 = T.a 1 3 := rfl
def T.sum : T → Nat
  | .a n m => n + m
example : T.sum (T.a 1) = 4 := rfl
theorem T.sum_cases (t : T) : t.sum = t.sum := by
  cases t with
  | a n m => rfl
theorem T.sum_induction (t : T) : t.sum = t.sum := by
  induction t with
  | a n m => rfl
inductive V where
  | c (n : Nat := 2) (f : Fin (n + 1)) (m : Nat := n)
def V.get : V → Nat
  | .c n _ m => n + m
inductive D where
  | c (n : Nat := 2) (f : Fin (Nat.succ n)) (m : Nat := n)
def D.get : D → Nat
  | .c n _ m => n + m
structure S where
  x : Nat := 3
  y : Nat
example : ({ y := 1 } : S).x = 3 := rfl
inductive I : Nat → Type where
  | mk (n : Nat) (k : Nat := 5) : I n
def I.second : I n → Nat
  | .mk _ k => k
example : (I.mk 2 : I 2).second = 5 := rfl
inductive R where
  | leaf
  | node (l : R) (k : Nat := 0)
def R.size : R → Nat
  | .leaf => 0
  | .node l k => l.size + k + 1
example : (R.node .leaf).size = 1 := rfl
theorem R.size_induction (r : R) : r.size = r.size := by
  induction r with
  | leaf => rfl
  | node l k ih => rfl
mutual
inductive A where
  | base (n : Nat := 1)
  | step (b : B) (k : Nat := 2)
inductive B where
  | wrap (a : A) (j : Nat := 3)
end
inductive N where
  | mk (xs : List N) (k : Nat := 1)
inductive F where
  | leaf
  | node (f : (x : Nat := 3) → F)
inductive P (n : Nat := 3) where
  | mk : P n
inductive O where
  | mk (α : outParam Type) (x : semiOutParam Nat)
inductive Q where
  | mk (m : optParam (optParam Nat 3) 4)
inductive J : (n : Nat := 3) → Type where
  | mk : J 0
def tac : Lean.Syntax := Lean.Syntax.missing
inductive W where
  | mk (n : Nat) (h : autoParam (n = n) tac)
";

/// Every declaration compared with the pin's, one family per row: its own constants, its
/// recursors and the auxiliaries both sides generate from them.
const COMPARED: &[&str] = &[
    "T T.a T.rec T.casesOn T.recOn",
    "D D.c D.rec D.casesOn D.recOn",
    "S S.mk S.rec S.casesOn S.recOn",
    "I I.mk I.rec I.casesOn I.recOn",
    "R R.leaf R.node R.rec R.casesOn R.recOn R.below R.brecOn",
    "A A.base A.step A.rec A.casesOn A.recOn",
    "B B.wrap B.rec B.casesOn B.recOn",
    "N N.mk N.rec N.rec_1 N.casesOn N.recOn",
    "F F.leaf F.node F.rec F.casesOn F.recOn F.below F.brecOn",
    "P P.mk P.rec P.casesOn P.recOn",
    "O O.mk O.rec O.casesOn O.recOn",
    "Q Q.mk Q.rec Q.casesOn Q.recOn",
    "J J.mk J.rec J.casesOn J.recOn",
    "W W.mk W.rec W.casesOn W.recOn",
];

/// Tactics remain quoted until a constructor application supplies its actual
/// fields. These are accepted by the pin even when the generic default is not
/// provable (Deferred), or requires a caller local (Contextual and Later).
const TACTIC_DEFAULT: &str = r#"
inductive U where
  | b (n : Nat) (h : n > 0 := by decide)
def U.value : U → Nat
  | .b n _ => n
theorem positive_default : (U.b 1).value = 1 := rfl
inductive Grouped where
  | mk (left right : Nat := by exact 7)
def Grouped.sum : Grouped → Nat
  | .mk left right => Nat.add left right
def rawConstructor : Nat → Nat → Grouped := @Grouped.mk
theorem grouped_default : Grouped.mk = @Grouped.mk 7 7 := rfl
theorem grouped_override : Grouped.mk (right := 2) = @Grouped.mk 7 2 := rfl
inductive Deferred where
  | mk (n : Nat) (h : n = 0 := by rfl)
def zero : Deferred := Deferred.mk 0
theorem explicit_override (h : 1 = 0) : Deferred.mk 1 h = @Deferred.mk 1 h := rfl
inductive Contextual where
  | mk (n : Nat := by assumption)
theorem caller_context (wanted : Nat) : Contextual.mk = @Contextual.mk wanted := rfl
inductive Later where
  | mk {α : Type} (value : α := by assumption) (witness : α)
theorem later_argument (wanted : Nat) :
    Later.mk (witness := Nat.zero) = @Later.mk Nat wanted Nat.zero := rfl
mutual
  inductive SharedA where
    | leaf (n : Nat := by exact 5)
    | step (b : SharedB)
  inductive SharedB where
    | wrap (a : SharedA) (n : Nat := by exact 7)
end
theorem mutual_default : SharedB.wrap SharedA.leaf = @SharedB.wrap (@SharedA.leaf 5) 7 := rfl
set_option Elab.async false in
inductive Sync where
  | mk (left right : Nat := by exact 7)
inductive Parameter (n : Nat := by exact 3) where
  | mk
"#;

const TACTIC_COMPARED: &[&str] = &[
    "U U.b U.rec U.casesOn U.recOn",
    "Grouped Grouped.mk Grouped.rec Grouped.casesOn Grouped.recOn",
    "Deferred Deferred.mk Deferred.rec Deferred.casesOn Deferred.recOn",
    "Contextual Contextual.mk Contextual.rec Contextual.casesOn Contextual.recOn",
    "Later Later.mk Later.rec Later.casesOn Later.recOn",
    "SharedA SharedA.leaf SharedA.step SharedA.rec SharedA.casesOn SharedA.recOn",
    "SharedB SharedB.wrap SharedB.rec SharedB.casesOn SharedB.recOn",
    "Sync Sync.mk Sync.rec Sync.casesOn Sync.recOn",
    "Parameter Parameter.mk Parameter.rec Parameter.casesOn Parameter.recOn",
];

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn reference() -> Option<(PathBuf, PathBuf)> {
    let row = include_str!("../../../SUITE.lock")
        .lines()
        .find(|line| line.starts_with("reference leanprover/lean4 "))
        .expect("Reference row in SUITE.lock");
    let field = |key: &str| {
        row.split_whitespace()
            .find_map(|word| word.strip_prefix(key))
            .expect("SUITE.lock Reference field")
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
        .filter(|path| path.join("Init/Core.olean").is_file());
    let Some(library) = library else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference library is required"
        );
        eprintln!("SKIP: pinned Reference library absent");
        return None;
    };
    let compiler = library.parent()?.parent()?.join("bin/lean");
    let githash = Command::new(&compiler).arg("--githash").output().unwrap();
    assert!(githash.status.success());
    assert_eq!(
        String::from_utf8_lossy(&githash.stdout).trim(),
        field("commit="),
        "the pinned compiler"
    );
    Some((compiler, library))
}

fn workspace() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-inductive-optional-fields-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The pinned `lean` on `HEADER` + `body` as module `module`, writing its `.olean` when
/// `olean` is set. Returns whether it was accepted, and its output.
fn pinned(
    compiler: &Path,
    library: &Path,
    root: &Path,
    module: &str,
    body: &str,
    olean: bool,
) -> (bool, String) {
    let source = format!("{module}.lean");
    std::fs::write(root.join(&source), format!("{HEADER}{body}")).unwrap();
    let mut command = Command::new(compiler);
    command.current_dir(root).env("LEAN_PATH", library);
    if olean {
        command.args(["-o", &format!("{module}.olean")]);
    }
    let output = command.arg(&source).output().unwrap();
    (
        output.status.success(),
        format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ),
    )
}

/// Import `root` and its whole closure, from `fixture` or the pinned library, through both
/// admission seats into an empty environment.
fn import(root: &Name, fixture: &Path, library: &Path) -> Engine {
    import_receipt(root, fixture, library).engine
}

fn import_receipt(root: &Name, fixture: &Path, library: &Path) -> SourceOleanImport {
    let mut pending = vec![(root.clone(), false)];
    let mut seen = BTreeSet::new();
    let mut ordered = Vec::new();
    let mut artifacts = BTreeMap::new();
    while let Some((module, finished)) = pending.pop() {
        if finished {
            ordered.push(module);
            continue;
        }
        if !seen.insert(module.clone()) {
            continue;
        }
        assert!(seen.len() <= 64, "bounded actual Init.Core closure");
        let relative = module.to_display_string().replace('.', "/");
        let path = [fixture, library]
            .into_iter()
            .map(|base| base.join(&relative).with_extension("olean"))
            .find(|path| path.is_file())
            .unwrap_or_else(|| panic!("missing module {relative}"));
        let optional = |path: PathBuf| match std::fs::read(path) {
            Ok(bytes) => Some(bytes),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => panic!("reading an artifact companion: {error}"),
        };
        let public = std::fs::read(&path).unwrap();
        let imports = fln::olean_module_imports(&public, OleanDecodeLimits::new(BYTES)).unwrap();
        artifacts.insert(
            module.clone(),
            (
                public,
                optional(path.with_extension("olean.server")),
                optional(path.with_extension("olean.private")),
            ),
        );
        pending.push((module, true));
        pending.extend(imports.into_iter().rev().map(|name| (name, false)));
    }
    let inputs: Vec<_> = ordered
        .iter()
        .map(|module| {
            let (public, server, private) = &artifacts[module];
            OleanModuleInput {
                name: module,
                artifact: public,
                server_artifact: server.as_deref(),
                private_artifact: private.as_deref(),
            }
        })
        .collect();
    Engine::from_environment(Environment::new())
        .import_olean_modules_for_source(
            &inputs,
            std::slice::from_ref(root),
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                BYTES,
                Budget::for_stack_bytes(STACK),
            )),
        )
        .unwrap_or_else(|error| panic!("importing {}: {error:?}", root.to_display_string()))
        .into_complete()
        .expect("actual import completes")
}

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)))
}

#[test]
fn annotated_constructor_fields_produce_the_pins_recursors() {
    let Some((compiler, library)) = reference() else {
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let root = workspace();
            let (accepted, output) =
                pinned(&compiler, &library, &root, "OptionalFields", FIXTURE, true);
            assert!(accepted && output.is_empty(), "the pin: {output}");
            let (accepted, output) = pinned(
                &compiler,
                &library,
                &root,
                "TacticDefault",
                TACTIC_DEFAULT,
                true,
            );
            assert!(accepted, "the pin rejects the tactic default: {output}");

            eprintln!("checking actual Init.Core and the modern constructor-default consumer");
            let receipt = import_receipt(&name("Init.Core"), &root, &library);
            let base = &receipt.engine;
            let options = KVMap::new();
            let producer = name("PublicConstructorDefaults");
            let consumer = name("ConstructorConsumer");
            let imported = receipt.check_source_modules(&[
                fln::SourceModuleInput { name: &producer, source: b"module\nprelude\npublic import Init.Core\npublic inductive PublicAuto where | mk (n : Nat := by exact 7)\n" },
                fln::SourceModuleInput { name: &consumer, source: b"module\nprelude\npublic import PublicConstructorDefaults\npublic theorem imported_default : PublicAuto.mk = @PublicAuto.mk 7 := rfl\n" },
            ], &consumer, &options,
                fln::source_check::modules::SourceModuleCheckLimits::new(limits()), None)
                .unwrap().into_complete().unwrap();
            let imported = &imported.checked.engine;
            assert!(matches!(imported.environment().find(&name("PublicAuto._auto_1")),
                Some(fln::ConstantInfo::Defn(_))));
            assert!(imported.environment().contains(&name("imported_default")));

            // The pin's artifact, rechecked here: its recursors are what this kernel regenerates.
            eprintln!("checking the pin's optional-field artifact through both admission seats");
            let theirs = import(&name("OptionalFields"), &root, &library);
            let ours = match base.check_source_files(&[FIXTURE.as_bytes()], &options, limits()) {
                Ok(Outcome::Complete(checked)) => checked.engine,
                Ok(_) => panic!("a nonanswer is not a verdict"),
                Err(error) => panic!("the fixture is refused: {error:?}"),
            };
            let mut differing = Vec::new();
            let mut first = None;
            for constant in COMPARED.iter().flat_map(|row| row.split_whitespace()) {
                let key = name(constant);
                match (
                    theirs.environment().find(&key),
                    ours.environment().find(&key),
                ) {
                    (Some(pinned), Some(native)) if pinned == native => {}
                    (Some(pinned), Some(native)) => {
                        differing.push(constant);
                        first.get_or_insert_with(|| format!("{native:?}\n  the pin's: {pinned:?}"));
                    }
                    (pinned, native) => {
                        differing.push(constant);
                        first.get_or_insert_with(|| {
                            format!(
                                "present at the pin: {}, here: {}",
                                pinned.is_some(),
                                native.is_some()
                            )
                        });
                    }
                }
            }
            assert!(
                differing.is_empty(),
                "differ from the pin's: {differing:?}\nfirst: {}",
                first.unwrap_or_default()
            );

            eprintln!("elaborating constructor tactic defaults and comparing the pin's artifact");
            let tactics = base
                .check_source_files(&[TACTIC_DEFAULT.as_bytes()], &options, limits())
                .expect("constructor tactic defaults elaborate")
                .into_complete()
                .expect("constructor default admission completes")
                .engine;
            let pinned_tactics = import(&name("TacticDefault"), &root, &library);
            for label in TACTIC_COMPARED.iter().flat_map(|row| row.split_whitespace()) {
                let key = name(label);
                assert_eq!(
                    tactics.environment().find(&key),
                    pinned_tactics.environment().find(&key),
                    "constructor or recursor differs from the pin: {label}"
                );
                assert!(tactics.environment().contains(&key), "missing {label}");
            }
            for label in [
                "U._auto_1",
                "Grouped._auto_1", "Grouped._auto_3",
                "Deferred._auto_1", "Contextual._auto_1", "Later._auto_1",
                "SharedA._auto_1", "SharedA._auto_3",
                "Sync._auto_1", "Sync._auto_2", "Parameter._auto_1",
            ] {
                let Some(fln::ConstantInfo::Defn(quote)) = tactics.environment().find(&name(label)) else {
                    panic!("missing checked quotation {label}");
                };
                assert_eq!(quote.safety, fln::DefinitionSafety::Safe);
                assert_eq!(quote.base.type_, fln::Expr::const_(name("Lean.Syntax"), Vec::new()));
                assert!(quote.base.level_params.is_empty());
                assert!(!quote.value.has_fvar() && !quote.value.has_loose_bvars());
            }
            let logical_root = tactics.logical_root(&options);
            for (module, source, absent) in [
                ("FalseDefault", "def badDefault : Deferred := Deferred.mk 1\n", "badDefault"),
                ("MalformedOwner", "inductive Broken where | mk (n : Nat := by exact 7) (bad : 0)\n", "Broken"),
            ] {
                let (accepted, output) = pinned(&compiler, &library, &root, module,
                    &format!("{TACTIC_DEFAULT}\n{source}"), false);
                assert!(!accepted, "the pin accepted {module}: {output}");
                let refused = tactics.check_source_files(&[source.as_bytes()], &options, limits())
                    .expect_err("an invalid selected default or owner must be refused");
                assert_eq!(refused.disposition().0, "elaboration", "{refused:?}");
                if module == "FalseDefault" {
                    let fln::SourceCheckError::Command { error, .. } = &refused else {
                        panic!("expected a failed constructor-default proof: {refused:?}");
                    };
                    let fln::EngineExecutionError::Frontend(
                        fln::NatDefinitionFrontendError::Elaborate(
                            fln_elab::NatDefinitionElabError::Inference(
                                fln_elab::source::SourceInferenceError::ConversionRefused(verdict),
                            ),
                        ),
                    ) = error.as_ref() else {
                        panic!("expected failed reflexivity, got {refused:?}");
                    };
                    assert!(matches!(verdict.as_ref(), fln_kernel::verdict::Verdict::Rejected {
                        class: fln::RejectClass::NotDefEq, ..
                    }), "{refused:?}");
                }
                assert!(!tactics.environment().contains(&name(absent)));
                assert!(!tactics.environment().contains(&name("Broken._auto_1")));
                assert_eq!(tactics.logical_root(&options), logical_root);
            }
            eprintln!("executing constructor defaults");
            let executed = tactics.execute_source_commands_with_checks(
                b"#eval U.value (U.b 1)\n#eval Grouped.sum Grouped.mk\n",
                &options, fln::EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
            ).unwrap().into_complete().unwrap();
            let values: Vec<_> = executed.batch.executions.iter().map(|execution| {
                let fln::VmExit::Returned(value) = &execution.exit else {
                    panic!("constructor default must execute: {:?}", execution.exit);
                };
                fln::nat_decimal(&value.value).expect("natural constructor payload")
            }).collect();
            assert_eq!(values, ["1", "14"]);

        })
        .unwrap()
        .join()
        .unwrap();
}
