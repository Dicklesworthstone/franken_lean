//! Source display hides only the current module's internal private prefix.
#![forbid(unsafe_code)]

use fln::source_check::modules::SourceModuleCheckLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, Expr, KVMap, Level, Name, SourceCheckLimits,
    SourceModuleInput,
};
use fln_elab::source::scope::SourceScope;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn private(declaration: &str) -> Name {
    Name::num(n("_private.Main"), 0).append_core(&n(declaration))
}

#[test]
fn private_signatures_applications_and_fields_use_source_names_without_changing_lookup() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let initial = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let module = n("Main");
    let source = "module\nprelude\nnamespace Local\ndef identity.{u} {A : Sort u} (x : A) : A := x\ndef «odd-name».{u} {A : Sort u} (x : A) : A := identity x\nstructure Box where\n value : Nat\ndef box : Box := { value := 9 }\nend Local";
    let result = initial
        .check_source_modules(
            &[SourceModuleInput {
                name: &module,
                source: source.as_bytes(),
            }],
            &module,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let environment = result.checked.engine.environment();
    let mut printer = fln::pretty::Printer::in_scope(environment, &result.checked.scope);
    let identity = private("Local.identity");
    let type_ = &environment.find(&identity).unwrap().constant_val().type_;
    assert_eq!(
        printer.signature(&identity, type_).unwrap(),
        "Local.identity.{u} {A : Sort u} (x : A) : A",
    );
    assert_eq!(printer.constant(&identity), "@Local.identity");
    let escaped = private("Local.odd-name");
    let escaped_type = &environment.find(&escaped).unwrap().constant_val().type_;
    assert_eq!(
        printer.signature(&escaped, escaped_type).unwrap(),
        "Local.«odd-name».{u} {A : Sort u} (x : A) : A",
    );
    assert_eq!(printer.constant(&escaped), "@Local.«odd-name»");
    let application = Expr::app(
        Expr::app(
            Expr::const_(identity.clone(), vec![Level::one()]),
            Expr::const_(private("Local.Box"), vec![]),
        ),
        Expr::const_(private("Local.box"), vec![]),
    );
    assert_eq!(
        printer.expr(&application, 0).unwrap(),
        "Local.identity Local.box"
    );
    let field = Expr::app(
        Expr::const_(private("Local.Box.value"), vec![]),
        Expr::const_(private("Local.box"), vec![]),
    );
    assert_eq!(printer.expr(&field, 0).unwrap(), "Local.box.value");
    assert_eq!(printer.constant(&n("Nat")), "Nat");

    // A scope from another source file cannot turn this module's private
    // declaration into a local alias; the default core printer is unchanged.
    let other = SourceScope {
        private_module: Some(n("Other")),
        ..Default::default()
    };
    let raw = format!("@{}", identity.to_display_string());
    assert_eq!(
        fln::pretty::Printer::new(environment).constant(&identity),
        raw
    );
    assert_eq!(
        fln::pretty::Printer::in_scope(environment, &other).constant(&identity),
        raw
    );
}
