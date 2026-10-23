//! The pin's two reducibility warnings, through the drop-in `lean` over `prelude` with
//! `Init.Core`: `warn.classDefReducibility` on a class-typed `def` left without
//! `@[reducible]`, `@[implicit_reducible]` or `@[irreducible]` (vendored
//! `src/Lean/Elab/MutualDef.lean:1246-1256`), and `addInstance`'s on an `instance` attribute
//! added to a definition that is neither `@[reducible]` nor `@[implicit_reducible]`
//! (`src/Lean/Meta/Instances.lean:281-289`). Each program runs through the pinned `lean`
//! v4.32.0 in the same test and must print exactly what the pin prints.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Core\n";

/// Which definitions warn: a plain class-typed `def` (also under binders, behind a function
/// arrow, through an `abbrev` and as `DecidablePred`), while the reducibility attributes,
/// `abbrev`, `instance`, `theorem`, `example`, a type behind a `def`, and the `Decidable`,
/// `DecidableEq` and `Setoid` heads do not. The warning sits at the declaration's first token,
/// a `mutual` block's keyword, before the unused-variables linter and the `sorry` warning.
const DEFINITIONS: &str = "def plain : Inhabited Nat := ⟨1⟩
@[reducible] def red : Inhabited Nat := ⟨1⟩
@[implicit_reducible] def impl : Inhabited Nat := ⟨1⟩
@[irreducible] def irr : Inhabited Nat := ⟨1⟩
abbrev ab : Inhabited Nat := ⟨1⟩
instance inst : Inhabited Nat := ⟨1⟩
def dec (p : Prop) [h : Decidable p] : Decidable p := h
def deq : DecidableEq Nat := inferInstance
def sto (s : Setoid Nat) : Setoid Nat := s
theorem thm : Nonempty Nat := ⟨1⟩
example : Inhabited Nat := ⟨1⟩
/-- A documented definition. -/
def documented : Inhabited Nat := ⟨1⟩
def binders (α : Type) (a : α) : Inhabited α := ⟨a⟩
def arrow : Inhabited Nat → Inhabited Nat := fun x => x
abbrev MyInhabited := Inhabited Nat
def viaAbbrev : MyInhabited := ⟨1⟩
def MyClass := Inhabited Nat
def viaDef : MyClass := ⟨1⟩
def pred : DecidablePred (fun n : Nat => n = 0) := fun _ => inferInstance
def unused (x : Nat) : Inhabited Nat := ⟨1⟩
def withSorry : Inhabited Nat := sorry
mutual
def m1 : Inhabited Nat := ⟨1⟩
def m2 : Inhabited Nat := ⟨2⟩
end
namespace N
def inner : Inhabited Nat := ⟨1⟩
end N
";

/// `attribute [instance]` on an unmarked definition warns at the attribute's `instance`
/// keyword, each time and for each name; an `@[irreducible]` definition is still unmarked, while
/// a `@[reducible]` one, an imported instance and a theorem are not warned about. A proposition
/// `def` is a definition. Local and scoped attributes warn as global ones do.
const ATTRIBUTES: &str = "def unm : Inhabited Nat := ⟨2⟩
attribute [instance] unm
attribute [instance 30] unm
def a1 : Inhabited Nat := ⟨1⟩
def a2 : Inhabited Nat := ⟨2⟩
attribute [instance] a1 a2
def ir : Inhabited Nat := ⟨1⟩
attribute [irreducible] ir
attribute [instance] ir
def rd : Inhabited Nat := ⟨1⟩
attribute [reducible] rd
attribute [instance] rd
attribute [instance] instInhabitedNat
class P : Prop where
  h : True
theorem pthm : P := ⟨trivial⟩
attribute [instance] pthm
def pdef : P := ⟨trivial⟩
attribute [instance] pdef
section
def loc : Inhabited Nat := ⟨1⟩
attribute [local instance] loc
end
namespace Q
def sc : Inhabited Nat := ⟨1⟩
attribute [scoped instance] sc
end Q
";

/// A declaration's own attributes apply in order, before the class-typed `def` check: an
/// `instance` before `reducible` finds the definition unmarked, one after does not, and an
/// `abbrev`'s own `reducible` comes after its list. Both precede the `sorry` warning.
const INLINE: &str = "@[instance] def i1 : Inhabited Nat := ⟨3⟩
@[instance 100] def i2 : Inhabited Nat := ⟨3⟩
@[reducible, instance] def i3 : Inhabited Nat := ⟨1⟩
@[instance, reducible] def i4 : Inhabited Nat := ⟨1⟩
@[instance] abbrev i5 : Inhabited Nat := ⟨1⟩
@[instance] def i6 : Inhabited Nat := sorry
";

/// `set_option warn.classDefReducibility false` silences the definition's warning, for one
/// command with `in`, and never the instance attribute's.
const SWITCHED_OFF: &str = "set_option warn.classDefReducibility false in
def once : Inhabited Nat := ⟨1⟩
def after : Inhabited Nat := ⟨1⟩
set_option warn.classDefReducibility false
def off : Inhabited Nat := ⟨1⟩
attribute [instance] off
";

const PROGRAMS: &[(&str, &str, usize, usize)] = &[
    ("definitions", DEFINITIONS, 11, 0),
    ("attributes", ATTRIBUTES, 8, 8),
    ("inline", INLINE, 3, 5),
    ("switched_off", SWITCHED_OFF, 1, 1),
];

fn pinned_toolchain() -> Option<PathBuf> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                    .join("lib/lean")
            })
        })
        .filter(|lib| lib.join("Init/Core.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference library is required"
    );
    if lib.is_none() {
        eprintln!("SKIP: pinned Reference lib/lean absent");
    }
    lib
}

fn workspace() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-class-def-reducibility-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The stdout of this crate's `lean` and of the pinned `lean` on `HEADER` + `program`.
fn outputs(lib: &Path, root: &Path, name: &str, program: &str) -> (String, String) {
    let entry = format!("{name}.lean");
    std::fs::write(root.join(&entry), format!("{HEADER}{program}")).unwrap();
    let run = |binary: &Path| {
        let output = Command::new(binary)
            .arg(&entry)
            .current_dir(root)
            .env("LEAN_PATH", lib)
            .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
            .output()
            .expect("run lean");
        assert_eq!(
            output.status.code(),
            Some(0),
            "{name}: {}\n{}",
            binary.display(),
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).expect("UTF-8 output")
    };
    let pinned = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .expect("the pinned toolchain's lean");
    (run(Path::new(env!("CARGO_BIN_EXE_lean"))), run(&pinned))
}

#[test]
fn reducibility_warnings_match_the_pin() {
    let Some(lib) = pinned_toolchain() else {
        return;
    };
    let root = workspace();
    for &(name, program, definitions, instances) in PROGRAMS {
        let (ours, pinned) = outputs(&lib, &root, name, program);
        assert_eq!(ours, pinned, "{name}: {program}");
        // The programs must actually exercise both warnings.
        assert_eq!(
            ours.matches("of class type must be marked with").count(),
            definitions,
            "{name}: {ours}"
        );
        assert_eq!(
            ours.matches("warning: instance `").count(),
            instances,
            "{name}: {ours}"
        );
    }
}
