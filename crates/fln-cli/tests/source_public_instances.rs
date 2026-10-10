//! Installed module doors export authored data instances and execute their
//! checked dictionary bodies. No reference runtime or synthetic Init is used.
#![forbid(unsafe_code)]

use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Project(PathBuf);
impl Project {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-public-instances-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn write(&self, name: &str, source: &str) {
        std::fs::write(self.0.join(name), source).unwrap();
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
        let text = String::from_utf8(output.stdout).unwrap();
        assert!(text.contains("\"outcome\":\"complete\""), "{text}");
        text
    }

    fn refused(&self, command: &str) -> String {
        let output = self.fln(command);
        assert!(
            !output.status.success(),
            "unexpected success: {}",
            String::from_utf8_lossy(&output.stdout)
        );
        assert!(
            output.stdout.is_empty(),
            "failed module published partial output"
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
            "{}",
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

const BASE: &str = "prelude\ninductive Token where\n| left\n| right\nclass Pick (A : Type) where\n  value : A\nstructure Box (A : Type) where\n  value : A\ndef chosen {A : Type} [p : Pick A] : A := p.value";

#[test]
fn installed_doors_accept_named_and_anonymous_public_instances() {
    let p = Project::new();
    p.write("Base.lean", BASE);
    p.write(
        "Api.lean",
        "module\nprelude\npublic import Base\npublic instance named : Pick Token := Pick.mk Token.left\npublic instance {A : Type} [p : Pick A] : Pick (Box A) := Pick.mk (Box.mk p.value)",
    );
    p.write("Facade.lean", "module\nprelude\npublic import Api");
    p.write(
        "Main.lean",
        "prelude\nimport Facade\ndef boxed : Box Token := chosen\ndef correct (P : Token -> Prop) (h : P Token.left) : P boxed.value := h",
    );
    p.complete("check-source");
    p.complete("run");
    assert!(p.lean_complete().is_empty());
}

#[test]
fn installed_runtime_evaluates_the_exposed_instance_body() {
    let p = Project::new();
    p.write(
        "Base.lean",
        "prelude\ninductive Bool where\n| false\n| true\nclass Pick where\n  value : Bool",
    );
    p.write(
        "Api.lean",
        "module\nprelude\npublic import Base\npublic instance selected : Pick := Pick.mk Bool.true",
    );
    p.write("Main.lean", "prelude\nimport Api\n#eval Pick.value");
    let result = p.complete("run");
    assert!(
        result.contains("\"kind\":\"bool\",\"value\":true"),
        "{result}"
    );
    // Native run projects the checked Bool directly. The compatibility door
    // must still refuse instance-directed printing without a real Init/Repr.
    let lean = p.lean();
    assert!(!lean.status.success());
    assert!(lean.stdout.is_empty());
    assert!(String::from_utf8_lossy(&lean.stderr).contains("do not reach `Init`"));
}

#[test]
fn installed_public_section_instances_keep_private_overrides_local() {
    let p = Project::new();
    p.write("Base.lean", BASE);
    p.write(
        "Api.lean",
        "module\nprelude\npublic import Base\npublic section\ninstance selected : Pick Token := Pick.mk Token.left\nprivate instance (priority := 2000) hidden : Pick Token := Pick.mk Token.right\nend\ninstance (priority := 3000) afterSection : Pick Token := Pick.mk Token.right\ndef localChoice : Token := chosen\ndef localCorrect (P : Token -> Prop) (h : P Token.right) : P localChoice := h",
    );
    let consumer = "prelude\nimport Api\ndef observed : Token := chosen\ndef correct (P : Token -> Prop) (h : P Token.left) : P observed := h";
    p.write("Main.lean", consumer);
    p.complete("check-source");
    p.complete("run");
    assert!(p.lean_complete().is_empty());
    p.write(
        "Main.lean",
        "prelude\nimport Api\ndef observed : Token := chosen\ndef wrong (P : Token -> Prop) (h : P Token.right) : P observed := h",
    );
    p.refused("check-source");
    p.refused("run");
    assert!(!p.lean().status.success());
    p.write("Main.lean", consumer);
    p.complete("check-source");
}

#[test]
fn installed_public_instances_refuse_hidden_dependencies_and_recover() {
    let p = Project::new();
    p.write("Base.lean", BASE);
    p.write(
        "Secret.lean",
        "prelude\nimport Base\ndef hidden : Token := Token.right\ninstance hiddenDictionary : Pick Token := Pick.mk Token.right",
    );
    p.write("Main.lean", "prelude\nimport Api");
    for declaration in [
        "public instance leaked : Pick Token := Pick.mk hidden",
        "public instance leaked : Pick (Box Token) := Pick.mk (Box.mk chosen)",
        "@[no_expose] public instance leaked : Pick Token := Pick.mk Token.left",
        "public instance leaked : Pick Token := Token.left",
    ] {
        p.write(
            "Api.lean",
            &format!("module\nprelude\npublic import Base\nimport Secret\n{declaration}"),
        );
        p.refused("check-source");
        p.refused("run");
        let lean = p.lean();
        assert!(!lean.status.success(), "{declaration}");
        assert!(lean.stdout.is_empty());
    }
    p.write(
        "Api.lean",
        "module\nprelude\npublic import Base\nimport Secret\n@[expose] public instance selected : Pick Token := Pick.mk Token.left",
    );
    p.write(
        "Main.lean",
        "prelude\nimport Api\ndef observed : Token := chosen\ndef correct (P : Token -> Prop) (h : P Token.left) : P observed := h",
    );
    p.complete("check-source");
    p.complete("run");
    assert!(p.lean_complete().is_empty());
}
