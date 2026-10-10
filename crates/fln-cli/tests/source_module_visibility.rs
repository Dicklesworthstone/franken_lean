//! Installed source doors preserve private implementations and exposed module APIs.
#![forbid(unsafe_code)]

use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);
struct Project(PathBuf);
impl Project {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-module-visibility-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn write(&self, path: &str, source: &str) {
        std::fs::write(self.0.join(path), source).unwrap();
    }
    fn fln(&self, command: &str) -> Output {
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args([command, "--json", "Main.lean"])
            .current_dir(&self.0)
            .env("LEAN_PATH", &self.0)
            .output()
            .unwrap()
    }
    fn complete(&self, command: &str) -> String {
        let output = self.fln(command);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stderr.is_empty());
        let result = String::from_utf8(output.stdout).unwrap();
        assert!(result.contains("\"outcome\":\"complete\""), "{result}");
        result
    }
    fn refused(&self, command: &str) -> String {
        let output = self.fln(command);
        assert!(!output.status.success());
        assert!(
            output.stdout.is_empty(),
            "failed module exposed partial output"
        );
        String::from_utf8(output.stderr).unwrap()
    }
    fn lean(&self) -> Output {
        Command::new(env!("CARGO_BIN_EXE_lean"))
            .arg("Main.lean")
            .current_dir(&self.0)
            .env("LEAN_PATH", &self.0)
            .output()
            .unwrap()
    }
    fn lean_complete(&self) -> String {
        let output = self.lean();
        assert!(
            output.status.success(),
            "stdout={}\nstderr={}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stderr.is_empty());
        String::from_utf8(output.stdout).unwrap()
    }
}
impl Drop for Project {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

const ID: &str = "def identity.{u} {A : Sort u} (x : A) : A := x";
const PRIVATE_ID: &str = "module\nprelude\ndef identity.{u} {A : Sort u} (x : A) : A := x\ndef again.{u} {A : Sort u} (x : A) : A := identity x";

#[test]
fn installed_check_run_and_lean_accept_private_module_commands() {
    let p = Project::new();
    p.write("Main.lean", PRIVATE_ID);
    p.complete("check-source");
    p.complete("run");
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg("Main.lean")
        .current_dir(&p.0)
        .env("LEAN_PATH", &p.0)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
    p.write("Main.lean", &format!("{PRIVATE_ID}\n#check identity"));
    assert!(p.complete("run").contains("\"checks\":1"));
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg("Main.lean")
        .current_dir(&p.0)
        .env("LEAN_PATH", &p.0)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"identity.{u} {A : Sort u} (x : A) : A\n");
    assert!(output.stderr.is_empty());
    // A module-system prelude receives no synthetic Nat declarations.
    p.write("Main.lean", "module\nprelude\ndef seedLeak : Nat := 0");
    p.refused("check-source");
    p.refused("run");
    p.write("Main.lean", PRIVATE_ID);
    p.complete("check-source");
}

#[test]
fn installed_imports_keep_private_siblings_and_transitive_imports_hidden() {
    let p = Project::new();
    p.write("A.lean", PRIVATE_ID);
    p.write("B.lean", PRIVATE_ID);
    p.write("Main.lean", "prelude\nimport A\nimport B");
    assert!(p.complete("check-source").contains("\"files\":3"));
    p.complete("run");
    p.write(
        "Main.lean",
        "prelude\nimport A\ndef stolen.{u} {A : Sort u} (x : A) : A := identity x",
    );
    p.refused("check-source");
    p.refused("run");
    p.write("A.lean", ID);
    p.write(
        "B.lean",
        "module\nprelude\nimport A\ndef localUse.{u} {A : Sort u} (x : A) : A := identity x",
    );
    p.write(
        "Main.lean",
        "prelude\nimport B\ndef use.{u} {A : Sort u} (x : A) : A := identity x",
    );
    p.refused("check-source");
    p.refused("run");
    p.write(
        "Main.lean",
        "prelude\nimport B\nimport A\ndef use.{u} {A : Sort u} (x : A) : A := identity x",
    );
    p.complete("check-source");
    p.complete("run");
}

#[test]
fn installed_module_uses_actual_init_and_prelude_suppresses_it() {
    let p = Project::new();
    p.write("Init.lean", &format!("prelude\n{ID}"));
    p.write(
        "Main.lean",
        "module\ndef use.{u} {A : Sort u} (x : A) : A := identity x",
    );
    assert!(p.complete("check-source").contains("\"files\":2"));
    p.complete("run");
    p.write(
        "Main.lean",
        "module\nprelude\ndef use.{u} {A : Sort u} (x : A) : A := identity x",
    );
    p.refused("check-source");
    p.refused("run");
}

#[test]
fn installed_public_imports_reexport_the_selected_api_without_private_names() {
    let p = Project::new();
    p.write("Api.lean", &format!("prelude\n{ID}"));
    p.write(
        "Secret.lean",
        "prelude\ndef hidden.{u} {A : Sort u} (x : A) : A := x",
    );
    p.write(
        "Wrapper.lean",
        "module\nprelude\nimport Secret\npublic import Api\ndef localUse.{u} {A : Sort u} (x : A) : A := hidden (identity x)",
    );
    p.write("Facade.lean", "module\nprelude\npublic import Wrapper");
    p.write(
        "Main.lean",
        "prelude\nimport Facade\ndef use.{u} {A : Sort u} (x : A) : A := identity x",
    );
    assert!(p.complete("check-source").contains("\"files\":5"));
    p.complete("run");
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg("Main.lean")
        .current_dir(&p.0)
        .env("LEAN_PATH", &p.0)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
    for declaration in ["hidden", "localUse"] {
        p.write(
            "Main.lean",
            &format!("prelude\nimport Facade\ndef stolen.{{u}} {{A : Sort u}} (x : A) : A := {declaration} x"),
        );
        p.refused("check-source");
        p.refused("run");
    }
}

#[test]
fn installed_public_data_and_exposed_definitions_preserve_reduction_and_section_defaults() {
    let p = Project::new();
    p.write(
        "Api.lean",
        "module\nprelude\nnamespace API\n@[expose] public section Exported\ninductive Token where\n | left\n | right\nstructure Box where\n value : Token\nprivate def hidden (x : Token) : Token := x\ndef boxed : Box := { value := Token.left }\ndef unwrap (b : Box) : Token := b.value\ndef flip (x : Token) : Token := match x with\n | Token.left => Token.right\n | Token.right => Token.left\nend Exported\ndef after (x : Token) : Token := x\nend API",
    );
    // These dependent signatures require the imported exposed bodies,
    // constructors, recursor, and record projection to reduce correctly.
    let consumer = "prelude\nimport Api\ndef verifies (P : API.Token -> Prop) (h : P API.Token.left) : P (API.unwrap API.boxed) := h\ndef checksMatch (P : API.Token -> Prop) (h : P API.Token.left) : P (API.flip (API.Box.mk API.Token.right).value) := h";
    p.write("Main.lean", consumer);
    assert!(p.complete("check-source").contains("\"files\":2"));
    p.complete("run");
    assert!(p.lean_complete().is_empty());
    p.write("Main.lean", &format!("{consumer}\n#check API.unwrap"));
    assert!(p.complete("run").contains("\"checks\":1"));
    let displayed = p.lean_complete();
    assert!(displayed.contains("API.unwrap"), "{displayed}");
    assert!(displayed.contains("API.Box"), "{displayed}");
    assert!(displayed.contains("API.Token"), "{displayed}");
    assert!(!displayed.contains("_private"), "{displayed}");
    for hidden in ["hidden", "after"] {
        p.write(
            "Main.lean",
            &format!("{consumer}\ndef stolen (x : API.Token) : API.Token := API.{hidden} x"),
        );
        p.refused("check-source");
        p.refused("run");
        assert!(!p.lean().status.success());
    }
}

#[test]
fn installed_public_signatures_and_exposed_bodies_cannot_use_private_dependencies() {
    let p = Project::new();
    p.write("Main.lean", "prelude\nimport Api");
    p.write("Secret.lean", &format!("prelude\n{ID}"));
    for invalid in [
        "module\nprelude\ninductive Secret where | mk\n@[expose] public def reveal (x : Secret) : Secret := x",
        "module\nprelude\ndef hidden.{u} {A : Sort u} (x : A) : A := x\n@[expose] public def reveal.{u} {A : Sort u} (x : A) : A := hidden x",
        "module\nprelude\nimport Secret\n@[expose] public def reveal.{u} {A : Sort u} (x : A) : A := identity x",
        "module\nprelude\n@[expose] public def wrong (A B : Type) (x : A) : B := x",
    ] {
        p.write("Api.lean", invalid);
        p.refused("check-source");
        p.refused("run");
        let refused = p.lean();
        assert!(!refused.status.success(), "{invalid}");
    }
    // The same private implementation is still available to private commands.
    p.write(
        "Api.lean",
        "module\nprelude\nimport Secret\nprivate def localUse.{u} {A : Sort u} (x : A) : A := identity x\n@[expose] public def reveal.{u} {A : Sort u} (x : A) : A := x",
    );
    p.write(
        "Main.lean",
        "prelude\nimport Api\ndef use.{u} {A : Sort u} (x : A) : A := reveal x",
    );
    p.complete("check-source");
    p.complete("run");
    assert!(p.lean_complete().is_empty());
}

#[test]
fn installed_public_deriving_exports_the_checked_dictionary_and_its_helper() {
    let p = Project::new();
    p.write(
        "Core.lean",
        "prelude\nuniverse u\nclass Inhabited (A : Sort u) where\n default : A",
    );
    p.write(
        "Api.lean",
        "module\nprelude\npublic import Core\npublic inductive Token where\n | left\n | right\n deriving Inhabited",
    );
    p.write(
        "Main.lean",
        "prelude\nimport Api\ndef chosen : Token := Inhabited.default\ndef verifies (P : Token -> Prop) (h : P Token.left) : P chosen := h",
    );
    p.complete("check-source");
    p.complete("run");
    assert!(p.lean_complete().is_empty());
}

const SCOPED_BASE: &str = "prelude\ninductive Token where\n | first\n | second\n | third\nclass Pick where\n value : Token\ndef pickInstance [i : Pick] : Pick := i\ninstance fallback : Pick := Pick.mk Token.first\nnamespace Chosen\ndef dictionary : Pick := Pick.mk Token.second\nattribute [scoped instance] dictionary\nnamespace Nested\ndef dictionary : Pick := Pick.mk Token.third\nattribute [scoped instance] dictionary\nend Chosen.Nested";
const SCOPED_HIDDEN: &str = "prelude\nimport Base\nclass Hidden where\n value : Token\ninstance hidden : Hidden := Hidden.mk Token.third\ninstance hiddenPick : Pick := Pick.mk Token.third";

#[test]
fn installed_module_scopes_keep_separate_instance_journals_and_restore_dotted_frames() {
    let p = Project::new();
    p.write("Base.lean", SCOPED_BASE);
    p.write("Hidden.lean", SCOPED_HIDDEN);
    p.write(
        "Library.lean",
        "module\nprelude\npublic import Base\nimport Hidden\nnamespace Chosen.Nested\n@[expose] public def nested : Pick := pickInstance\nprivate def localNested : Pick := pickInstance\nprivate def checkNested (P : Token -> Prop) (h : P Token.third) : P localNested.value := h\nend Nested\n@[expose] public def parent : Pick := pickInstance\nprivate def localParent : Pick := pickInstance\nprivate def checkParent (P : Token -> Prop) (h : P Token.second) : P localParent.value := h\nend Chosen\n@[expose] public def outside : Pick := pickInstance\nprivate def localOutside : Pick := pickInstance\nprivate def checkOutside (P : Token -> Prop) (h : P Token.third) : P localOutside.value := h\nopen scoped Chosen in @[expose] public def temporary : Pick := pickInstance\n@[expose] public def afterTemporary : Pick := pickInstance\n@[expose] public section\nopen Chosen in def publicTemporary : Pick := pickInstance\nprivate def stillPrivate : Pick := pickInstance\nprivate def checkStillPrivate (P : Token -> Prop) (h : P Token.third) : P stillPrivate.value := h\nend",
    );
    p.write(
        "Main.lean",
        "prelude\nimport Library\ndef checkNested (P : Token -> Prop) (h : P Token.third) : P Chosen.Nested.nested.value := h\ndef checkParent (P : Token -> Prop) (h : P Token.second) : P Chosen.parent.value := h\ndef checkOutside (P : Token -> Prop) (h : P Token.first) : P outside.value := h\ndef checkTemporary (P : Token -> Prop) (h : P Token.second) : P temporary.value := h\ndef checkAfterTemporary (P : Token -> Prop) (h : P Token.first) : P afterTemporary.value := h\ndef checkPublicTemporary (P : Token -> Prop) (h : P Token.second) : P publicTemporary.value := h",
    );
    p.complete("check-source");
    p.complete("run");
    assert!(p.lean_complete().is_empty());
}

#[test]
fn installed_public_scoped_instances_keep_activation_before_later_global_registrations() {
    let p = Project::new();
    p.write("Base.lean", SCOPED_BASE);
    p.write("Hidden.lean", SCOPED_HIDDEN);
    p.write(
        "Library.lean",
        "module\nprelude\npublic import Base\nimport Hidden\nsection\nopen scoped Chosen\n@[expose] public def before : Pick := pickInstance\nprivate def privateLater : Pick := Pick.mk Token.third\nattribute [instance] privateLater\n@[expose] public def afterPrivate : Pick := pickInstance\nprivate def selectedPrivate : Pick := pickInstance\nprivate def checkPrivate (P : Token -> Prop) (h : P Token.third) : P selectedPrivate.value := h\n@[expose] public section\ndef publicLater : Pick := Pick.mk Token.first\nattribute [instance] publicLater\ndef afterGlobal : Pick := pickInstance\nprivate def privateAfterGlobal : Pick := pickInstance\nprivate def checkPrivateAfter (P : Token -> Prop) (h : P Token.first) : P privateAfterGlobal.value := h\nend\nend\nopen scoped Chosen in @[expose] public def reopened : Pick := pickInstance\n@[expose] public def afterReopened : Pick := pickInstance\nnamespace Fresh\n@[expose] public section\ndef newDictionary : Pick := Pick.mk Token.second\nattribute [scoped instance] newDictionary\ndef afterRegistration : Pick := pickInstance\nprivate def localChoice : Pick := pickInstance\nprivate def checkLocal (P : Token -> Prop) (h : P Token.second) : P localChoice.value := h\nend\nend Fresh",
    );
    p.write(
        "Main.lean",
        "prelude\nimport Library\ndef checkBefore (P : Token -> Prop) (h : P Token.second) : P before.value := h\ndef checkAfterPrivate (P : Token -> Prop) (h : P Token.second) : P afterPrivate.value := h\ndef checkGlobal (P : Token -> Prop) (h : P Token.first) : P afterGlobal.value := h\ndef checkReopened (P : Token -> Prop) (h : P Token.second) : P reopened.value := h\ndef checkAfterReopened (P : Token -> Prop) (h : P Token.first) : P afterReopened.value := h\ndef checkFresh (P : Token -> Prop) (h : P Token.second) : P Fresh.afterRegistration.value := h",
    );
    p.complete("check-source");
    p.complete("run");
    assert!(p.lean_complete().is_empty());
}

#[test]
fn unsupported_visibility_refuses_before_missing_import_io() {
    let p = Project::new();
    for clause in [
        "meta import Missing",
        "public meta import Missing",
        "import all Missing",
    ] {
        p.write(
            "Main.lean",
            &format!("\u{feff}module\r\nprelude\r\n{clause}"),
        );
        for command in ["check-source", "run"] {
            let error = p.refused(command);
            let field = if command == "check-source" {
                "outcome"
            } else {
                "class"
            };
            assert!(
                error.contains(&format!("\"{field}\":\"capability\"")),
                "{error}"
            );
            assert!(error.contains("\"authority\":false"), "{error}");
            assert!(error.contains("not implemented"), "{error}");
        }
    }
    for modifier in ["public", "meta", "expose"] {
        p.write("Main.lean", &format!("module\nprelude\n{modifier} {ID}"));
        p.refused("check-source");
        p.refused("run");
    }
    p.write("Main.lean", PRIVATE_ID);
    p.complete("check-source");
}
