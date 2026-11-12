//! Primary artifacts may retain unsafe bodies whose checked helpers are private.
//! Real three-part codec inputs exercise admission and the source projection.
use super::*;
use crate::source_check::modules::imported::{
    SourceOleanImport, SourceOleanImportError, SourceOleanImportLimits,
};
use fln_core::expr::{Expr, Literal, NatLit};
use fln_core::level::Level;
use fln_env::constants::{ConstantVal, DefinitionVal, ReducibilityHints};
use fln_olean::format;
use fln_olean::write::{ModuleWriteInput, OleanWriteHeader, WriteBudget, encode_module};

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn private(label: &str) -> Name {
    Name::str(Name::num(name("_private.Implementations"), 0), label)
}

fn natural(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}

fn constant(name: Name) -> Expr {
    Expr::const_(name, Vec::new())
}

fn definition(name: Name, type_: Expr, value: Expr, safety: DefinitionSafety) -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: name.clone(),
            level_params: Vec::new(),
            type_,
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety,
        all: vec![name],
    })
}

fn owner(safety: DefinitionSafety) -> ConstantInfo {
    definition(
        name("implementation"),
        constant(name("Nat")),
        constant(private("helper")),
        safety,
    )
}

fn helper() -> ConstantInfo {
    definition(
        private("helper"),
        constant(name("Nat")),
        natural(7),
        DefinitionSafety::Safe,
    )
}

fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 << 20),
    )))
}

fn receipt(
    exported: &[ConstantInfo],
    complete: &[ConstantInfo],
) -> Result<Outcome<SourceOleanImport>, SourceOleanImportError> {
    let parts: Vec<_> = [exported, exported, complete]
        .into_iter()
        .enumerate()
        .map(|(index, constants)| {
            encode_module(
                ModuleWriteInput {
                    is_module: true,
                    imports: &[],
                    constants,
                    extra_const_names: &[],
                },
                OleanWriteHeader {
                    version: format::OLEAN_ACCEPTED_VERSIONS[0],
                    flags: 1,
                    lean_version: format::PIN_TAG.strip_prefix('v').unwrap(),
                    githash: format::PIN_COMMIT,
                    base_addr: (1_u64 << 40) + ((index as u64) << 30),
                },
                WriteBudget::default(),
            )
            .unwrap()
            .bytes
        })
        .collect();
    let module = name("Implementations");
    Engine::with_source_seed(limits().source.admission)
        .unwrap()
        .into_complete()
        .unwrap()
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
                8 << 20,
                limits().source.admission.kernel,
            )),
        )
}

fn project(
    receipt: &SourceOleanImport,
) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
    let main = name("Main");
    receipt.check_source_modules(
        &[SourceModuleInput {
            name: &main,
            source:
                b"module\nprelude\npublic import Implementations\npublic def answer : Nat := 42\n",
        }],
        &main,
        &KVMap::new(),
        limits(),
        None,
    )
}

fn missing(error: SourceModuleCheckError, declaration: &Name, missing: &Name) {
    let SourceModuleCheckError::ImportDeclarations { module, error } = error else {
        panic!("expected exported dependency refusal: {error:?}")
    };
    assert_eq!(module, name("Implementations"));
    assert!(
        matches!(error.as_ref(), OleanCheckError::MissingConstants { declaration: actual, names }
            if actual == declaration && names == std::slice::from_ref(missing)),
        "{error:?}"
    );
}

#[test]
fn exported_unsafe_bodies_reuse_complete_admission_without_exposing_private_helpers() {
    let exported = owner(DefinitionSafety::Unsafe);
    let receipt = receipt(
        std::slice::from_ref(&exported),
        &[helper(), exported.clone()],
    )
    .unwrap()
    .into_complete()
    .unwrap();
    let root = receipt.engine.logical_root(&KVMap::new());
    assert!(receipt.engine.environment().contains(&private("helper")));
    let checked = project(&receipt).unwrap().into_complete().unwrap();
    let environment = checked.checked.engine.environment();
    assert_eq!(environment.find(exported.name()), Some(&exported));
    assert!(!environment.contains(&private("helper")));
    assert!(environment.contains(&name("answer")));
    assert_eq!(receipt.engine.logical_root(&KVMap::new()), root);

    // The primary file remains incomplete on its own. The fix requires the
    // private receipt; it does not relax the ordinary declaration planner.
    let primary = receipt.contexts.modules[&name("Implementations")]
        .public
        .as_ref()
        .unwrap()
        .decoded
        .as_ref()
        .clone();
    assert!(matches!(
        receipt.contexts.origin.check_decoded_olean(
            primary,
            &KVMap::new(),
            OleanCheckLimits::new(8 << 20, limits().source.admission.kernel),
        ),
        Err(OleanCheckError::MissingConstants { declaration, names })
            if declaration == name("implementation") && names == [private("helper")]
    ));
}

#[test]
fn public_implementation_projection_still_checks_the_primary_independent_reading() {
    let exported = owner(DefinitionSafety::Unsafe);
    let mut receipt = receipt(
        std::slice::from_ref(&exported),
        &[helper(), exported.clone()],
    )
    .unwrap()
    .into_complete()
    .unwrap();
    let public = receipt
        .contexts
        .modules
        .get_mut(&name("Implementations"))
        .unwrap()
        .public
        .as_mut()
        .unwrap();
    Arc::make_mut(&mut public.decoded).independent = crate::IndependentReading::Read(Vec::new());
    let error = project(&receipt).unwrap_err();
    assert!(
        matches!(&error, SourceModuleCheckError::ImportDeclarations { error, .. }
            if matches!(error.as_ref(), OleanCheckError::IndependentReadingDiffers { name: actual, .. }
                if actual == &name("implementation"))),
        "{error:?}"
    );
}

#[test]
fn public_implementation_types_and_safe_bodies_still_require_public_dependencies() {
    let safe = owner(DefinitionSafety::Safe);
    let checked = receipt(std::slice::from_ref(&safe), &[helper(), safe.clone()])
        .unwrap()
        .into_complete()
        .unwrap();
    missing(
        project(&checked).unwrap_err(),
        &name("implementation"),
        &private("helper"),
    );

    let carrier = definition(
        private("Carrier"),
        Expr::sort(Level::succ(Level::zero()).unwrap()),
        constant(name("Nat")),
        DefinitionSafety::Safe,
    );
    let mut unsafe_owner = owner(DefinitionSafety::Unsafe);
    let ConstantInfo::Defn(value) = &mut unsafe_owner else {
        unreachable!()
    };
    value.base.type_ = constant(private("Carrier"));
    let checked = receipt(
        std::slice::from_ref(&unsafe_owner),
        &[helper(), carrier, unsafe_owner.clone()],
    )
    .unwrap()
    .into_complete()
    .unwrap();
    missing(
        project(&checked).unwrap_err(),
        &name("implementation"),
        &private("Carrier"),
    );
}

#[test]
fn missing_or_changed_private_implementations_never_create_a_public_receipt() {
    let exported = owner(DefinitionSafety::Unsafe);
    let missing = receipt(
        std::slice::from_ref(&exported),
        std::slice::from_ref(&exported),
    )
    .unwrap_err();
    assert!(
        missing
            .to_string()
            .contains(&private("helper").to_display_string()),
        "{missing:?}"
    );
    let mut corrupt = exported.clone();
    let ConstantInfo::Defn(value) = &mut corrupt else {
        unreachable!()
    };
    value.value = natural(9);
    assert!(receipt(&[exported], &[helper(), corrupt]).is_err());

    let exported = owner(DefinitionSafety::Unsafe);
    let mut ill_typed = helper();
    let ConstantInfo::Defn(value) = &mut ill_typed else {
        unreachable!()
    };
    value.value = constant(name("Bool.true"));
    assert!(
        receipt(
            std::slice::from_ref(&exported),
            &[ill_typed, exported.clone()]
        )
        .is_err()
    );
}
