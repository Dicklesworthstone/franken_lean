//! The applicative notations through the installed drop-in `lean`, over `prelude` with
//! `Init.Data.Option.Basic`: the pin's `macro_rules` (`Init/Notation.lean:430-440`) make `x <*> y`
//! `Seq.seq x fun _ : Unit => y`, and `x <* y` and `x *> y` `SeqLeft.seqLeft` and
//! `SeqRight.seqRight` alike, elaborated as ordinary applications. The macro's names are its
//! own: a local named `SeqRight` or `Unit` does not capture them. Not a pattern. `x <|> y` and
//! `x >> y` use `binop_lazy%` with `HOrElse.hOrElse` and `HAndThen.hAndThen`, respectively;
//! their right operands are `Unit` closures. Init.Control.Basic's plain mixfix operators use
//! ordinary applications of the declarations to which their notations resolve.
//!
//! The original applicative cases were run through pinned `lean` v4.32.0 with the same header
//! (2026-10-30). All cases consult the pin when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Data.Option.Basic\n";

/// Programs the pin accepts, printing nothing.
const ACCEPTED: &[&str] = &[
    "def m : EStateM Nat Unit Nat := pure 1 *> pure 2\n\
     example : m.run () = EStateM.Result.ok 2 () := rfl\n",
    "def k : EStateM Nat Unit Nat := pure 1 <* pure 2\n\
     example : k.run () = EStateM.Result.ok 1 () := rfl\n",
    "def ap (g : Option (Nat → Nat)) (x : Option Nat) : Option Nat := g <*> x\n",
    "example : (some 1 *> some 2 : Option Nat) = some 2 := rfl\n",
    "example : (some 1 <* some 2 : Option Nat) = some 1 := rfl\n",
    "example : ((none : Option Nat) *> some 2) = none := rfl\n",
    "example : (some Nat.succ <*> some 1 : Option Nat) = some 2 := rfl\n",
    "example : (some 1 *> some 2 <* some 3 : Option Nat) = some 2 := rfl\n",
    "example : (Nat.add <$> some 1 <*> some 2) = some 3 := rfl\n",
    "def t (SeqRight : Nat) : Option Nat := some 1 *> some SeqRight\n",
    "def u (Unit : Nat) : Option Nat := some Unit <* some 2\n",
    "example : ((none : Option Nat) <|> some 2) = some 2 := rfl\n",
    "example : (some 1 <|> some 2) = some 1 := rfl\n",
    "example : (none <|> none <|> some 3 : Option Nat) = some 3 := rfl\n",
    "example : (some 1 *> none <|> some 3 : Option Nat) = some 3 := rfl\n",
    "def first (x y : Option Nat) : Option Nat := x <|> y\n",
];

/// Programs the pin rejects: wrong values; right operands of the wrong type; a left operand whose
/// type nothing fixes; and the notation as a pattern.
const REFUSED: &[&str] = &[
    "example : (some 1 *> some 2 : Option Nat) = some 1 := rfl\n",
    "def bad : Option Nat := some 1 *> 2\n",
    "example : (none *> some 2 : Option Nat) = none := rfl\n",
    "def p (x : Option Nat) : Nat := match x with\n  | a *> b => 0\n  | _ => 1\n",
    "example : (some 1 <|> some 2) = some 2 := rfl\n",
    "def bad' : Option Nat := some 1 <|> 2\n",
];

fn pinned_lib() -> Option<PathBuf> {
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
        "fln-sequence-notation-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The pinned `lean`'s exit code and stdout on `entry`, when the binary is present.
fn pinned(lib: &Path, entry: &Path) -> Option<(i32, String)> {
    let lean = lib.parent()?.parent()?.join("bin/lean");
    if !lean.is_file() {
        return None;
    }
    let output = Command::new(lean)
        .arg(entry)
        .env("LEAN_PATH", lib)
        .output()
        .expect("run the pinned lean");
    Some((
        output.status.code().expect("normal pinned exit"),
        String::from_utf8(output.stdout).unwrap(),
    ))
}

/// The installed `lean` on `entry`: its exit code, stdout and stderr.
fn ours(lib: &Path, root: &Path, entry: &Path) -> (i32, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run lean");
    (
        output.status.code().expect("normal exit"),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

#[test]
fn applicative_notations_are_the_pins_applications() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    for (index, program) in ACCEPTED.iter().enumerate() {
        let entry = root.join(format!("Accepted{index}.lean"));
        std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
        if let Some((code, stdout)) = pinned(&lib, &entry) {
            assert_eq!((code, stdout.as_str()), (0, ""), "the pin moved: {program}");
        }
        let (code, stdout, stderr) = ours(&lib, &root, &entry);
        assert_eq!((code, stdout.as_str()), (0, ""), "{program}: {stderr}");
    }
    for (index, program) in REFUSED.iter().enumerate() {
        let entry = root.join(format!("Refused{index}.lean"));
        std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
        if let Some((code, _)) = pinned(&lib, &entry) {
            assert_eq!(code, 1, "the pin rejects {program}");
        }
        let (code, stdout, stderr) = ours(&lib, &root, &entry);
        assert_ne!(code, 0, "{program}: {stdout}");
        assert!(stderr.contains("refused"), "{program}: {stderr}");
    }
}

#[test]
fn init_control_operators_elaborate_with_the_pins_argument_order_and_hygiene() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let accepted = [
        "example : (some 2 <&> Nat.succ) = some 3 := rfl\n",
        "def mapShadow (Functor : Nat) : Option Nat := some Functor <&> Nat.succ\n\
         example : mapShadow 2 = some 3 := rfl\n",
        "example : ((none : Option Nat) <&> Nat.succ) = none := rfl\n",
        "example : (some false <||> some true : Option Bool) = some true := rfl\n",
        "example : (some true <||> none : Option Bool) = some true := rfl\n",
        "example : (some false <&&> none : Option Bool) = some false := rfl\n",
        "example : (some true <&&> some false : Option Bool) = some false := rfl\n",
        "example : (some true <||> some false <&&> some false : Option Bool) = some true := rfl\n",
        "def up (n : Nat) : Option Nat := some (n + 1)\n\
         def twice (n : Nat) : Option Nat := some (n * 2)\n\
         example : (up >=> twice) 3 = some 8 := rfl\n\
         example : (up <=< twice) 3 = some 7 := rfl\n\
         example : (up =<< some 3) = some 4 := rfl\n\
         example : (up =<< up =<< some 3) = some 5 := rfl\n\
         example : (up >=> twice >=> up) 3 = some 9 := rfl\n",
        "def bindShadow (Bind : Nat) : Option Nat := (fun n : Nat => some (Nat.succ n)) =<< some Bind\n\
         example : bindShadow 3 = some 4 := rfl\n",
        "def both : True ⊕' Nat := PSum.inl True.intro\n",
        "def three : True ⊕' False ⊕' Nat := PSum.inr (PSum.inr 3)\n",
        "def sumShadow (PSum : Nat) : True ⊕' Nat := _root_.PSum.inr PSum\n",
        "instance : HasSubset Nat where Subset a b := a ≤ b\n\
         instance : HasSSubset Nat where SSubset a b := a < b\n\
         example (a b : Nat) : (a ⊇ b) = (b ≤ a) := rfl\n\
         example (a b : Nat) : (a ⊃ b) = (b < a) := rfl\n",
        "instance : HAndThen Bool Nat Nat where\n\
           hAndThen b next := if b then next () else 7\n\
         example : ((true : Bool) >> (12 : Nat)) = 12 := rfl\n\
         example : ((false : Bool) >> (12 : Nat)) = 7 := rfl\n\
         def lazyShadow (HAndThen Unit : Nat) : Nat := (true : Bool) >> (HAndThen + Unit)\n\
         example : lazyShadow 4 2 = 6 := rfl\n",
    ];
    for (index, program) in accepted.iter().enumerate() {
        let entry = root.join(format!("ControlAccepted{index}.lean"));
        std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
        if let Some((code, stdout)) = pinned(&lib, &entry) {
            assert_eq!((code, stdout.as_str()), (0, ""), "the pin moved: {program}");
        }
        let (code, stdout, stderr) = ours(&lib, &root, &entry);
        assert_eq!((code, stdout.as_str()), (0, ""), "{program}: {stderr}");
    }
    for (index, program) in [
        "example : (some 2 <&> Nat.succ) = some 2 := rfl\n",
        "example : (some true <||> some false : Option Bool) = some false := rfl\n",
        "example : (some false <&&> some true : Option Bool) = some true := rfl\n",
        "def bad : Option Nat := Nat.succ =<< some 3\n",
        "def bad (a b c : Nat) := a ⊇ b ⊇ c\n",
        "def bad : Nat := (true : Bool) >> (3 : Nat)\n",
    ]
    .iter()
    .enumerate()
    {
        let entry = root.join(format!("ControlRefused{index}.lean"));
        std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
        if let Some((code, _)) = pinned(&lib, &entry) {
            assert_eq!(code, 1, "the pin rejects {program}");
        }
        let (code, stdout, stderr) = ours(&lib, &root, &entry);
        assert_ne!(code, 0, "{program}: {stdout}");
        assert!(stderr.contains("refused"), "{program}: {stderr}");
    }
}
