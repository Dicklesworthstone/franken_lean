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

use fln::source_check::modules::imported::SourceOleanImportLimits;
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
/// Two divergences of their own, not about annotations on recursors, keep some of it out of
/// the comparison. Every family states its sort: an inferred one is stored here as the
/// unnormalized `max (max 1 1) 1` where the pin stores `Type`. And `V` is only accepted, not
/// compared: under `n : optParam Nat 2`, `n + 1` is stored here as `@HAdd.hAdd (optParam Nat 2)
/// Nat Nat …` where the pin's `HAdd` output is `optParam Nat 2`, as it is for an `axiom` with
/// the same binders; `D` is the same family without the operator.
const FIXTURE: &str = "inductive T : Type where
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
inductive V : Type where
  | c (n : Nat := 2) (f : Fin (n + 1)) (m : Nat := n)
def V.get : V → Nat
  | .c n _ m => n + m
inductive D : Type where
  | c (n : Nat := 2) (f : Fin (Nat.succ n)) (m : Nat := n)
def D.get : D → Nat
  | .c n _ m => n + m
structure S : Type where
  x : Nat := 3
  y : Nat
example : ({ y := 1 } : S).x = 3 := rfl
inductive I : Nat → Type where
  | mk (n : Nat) (k : Nat := 5) : I n
def I.second : I n → Nat
  | .mk _ k => k
example : (I.mk 2 : I 2).second = 5 := rfl
inductive R : Type where
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
inductive A : Type where
  | base (n : Nat := 1)
  | step (b : B) (k : Nat := 2)
inductive B : Type where
  | wrap (a : A) (j : Nat := 3)
end
inductive N : Type where
  | mk (xs : List N) (k : Nat := 1)
inductive F : Type where
  | leaf
  | node (f : (x : Nat := 3) → F)
inductive P (n : Nat := 3) : Type where
  | mk : P n
inductive O : Type 1 where
  | mk (α : outParam Type) (x : semiOutParam Nat)
inductive Q : Type where
  | mk (m : optParam (optParam Nat 3) 4)
inductive J : (n : Nat := 3) → Type where
  | mk : J 0
def tac : Lean.Syntax := Lean.Syntax.missing
inductive W : Type where
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

/// A tactic default (`binderTactic`) needs the pin's quoted `Lean.Syntax` declaration
/// (`U._auto_1`), which this engine does not build: a typed refusal of the unsupported
/// syntax, never a kernel verdict. The pin accepts it (2026-10-23, exit 0).
const TACTIC_DEFAULT: &str = "inductive U where\n  | b (n : Nat) (h : n > 0 := by decide)\n";

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
        .engine
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
                false,
            );
            assert!(accepted, "the pin rejects the tactic default: {output}");

            // The pin's artifact, rechecked here: its recursors are what this kernel regenerates.
            let theirs = import(&name("OptionalFields"), &root, &library);
            let base = import(&name("Init.Core"), &root, &library);
            let options = KVMap::new();
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

            let refused = base
                .check_source_files(&[TACTIC_DEFAULT.as_bytes()], &options, limits())
                .expect_err("a tactic default is refused here");
            assert_eq!(refused.disposition().0, "input", "{refused:?}");
            assert!(
                format!("{refused:?}").contains("absent binder default"),
                "not the typed refusal: {refused:?}"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
