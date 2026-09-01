//! Real-artifact regression for the first recursive `Init.Prelude` family.
//!
//! `fln-checker/tests/init_nat.rs` proves the generic direct-recursion machinery
//! against an independently constructed Nat-shaped fixture. That is necessary
//! but not sufficient: a fixture can accidentally preserve the same mistaken
//! binder style, recursor metadata, or de Bruijn convention as the code it is
//! testing. This test moves exactly one variable. It decodes the pinned
//! Reference's own `Nat`, `Nat.zero`, `Nat.succ`, and `Nat.rec` rows and sends
//! those exact values through the product facade's ordinary K1 + independent
//! checker council.
//!
//! The Reference remains an oracle/fixture source only. No upstream
//! implementation code executes as a FrankenLean component.

#![forbid(unsafe_code)]

use std::path::PathBuf;

use fln::{
    Budget, Declaration, Engine, EngineAdmissionLimits, Environment, KVMap, Outcome,
};
use fln_env::constants::ConstantInfo;
use fln_olean::decl::DeclDecoder;
use fln_olean::region::{OleanView, WalkBudget};

fn reference_lib() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("FLN_REFERENCE_LIB") {
        let path = PathBuf::from(path);
        return path.is_dir().then_some(path);
    }
    let home = std::env::var("HOME").ok()?;
    let path = PathBuf::from(home)
        .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean");
    path.is_dir().then_some(path)
}

fn pinned_nat_block() -> Option<fln_kernel::InductiveBlock> {
    let lib = reference_lib()?;
    let base = lib.join("Init/Prelude.olean");
    let exported = std::fs::read(&base).ok()?;
    let server = std::fs::read(base.with_extension("olean.server")).ok()?;
    let private = std::fs::read(base.with_extension("olean.private")).ok()?;
    let view = OleanView::parse_with_dependencies(&private, &[&exported, &server]).ok()?;
    let infos = DeclDecoder::new(&view, WalkBudget::default())
        .decode_module_constants()
        .ok()?;

    let mut nat = None;
    let mut zero = None;
    let mut succ = None;
    let mut rec = None;
    for info in infos {
        let name = info.name().to_display_string();
        match (name.as_str(), info) {
            ("Nat", ConstantInfo::Induct(value)) => nat = Some(value),
            ("Nat.zero", ConstantInfo::Ctor(value)) => zero = Some(value),
            ("Nat.succ", ConstantInfo::Ctor(value)) => succ = Some(value),
            ("Nat.rec", ConstantInfo::Rec(value)) => rec = Some(value),
            _ => {}
        }
    }

    let nat = nat?;
    let zero = zero?;
    let succ = succ?;
    let rec = rec?;
    Some(fln_kernel::InductiveBlock {
        types: vec![nat],
        ctors: vec![zero, succ],
        recursors: vec![rec],
    })
}

#[test]
fn pinned_init_nat_completes_the_two_checker_council() {
    let Some(block) = pinned_nat_block() else {
        eprintln!(
            "SKIP: pinned Reference Init.Prelude companion chain is unavailable; \
             this test has no synthetic substitute"
        );
        return;
    };

    assert_eq!(block.types.len(), 1, "Nat is one inductive type");
    assert!(block.types[0].is_rec, "the pin marks Nat recursive");
    assert_eq!(
        block.types[0]
            .ctors
            .iter()
            .map(|name| name.to_display_string())
            .collect::<Vec<_>>(),
        ["Nat.zero", "Nat.succ"],
        "constructor order is index-visible and must come from the pin"
    );
    assert_eq!(block.recursors.len(), 1, "Nat has one primary recursor row");
    assert_eq!(
        block.recursors[0].base.name.to_display_string(),
        "Nat.rec",
        "the block must carry the pin's actual Nat.rec"
    );

    let engine = Engine::from_environment(Environment::new());
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let outcome = engine
        .admit_declaration(Declaration::Inductive(block), &KVMap::new(), limits)
        .expect("the pinned Nat block must reach the two-checker council without rejection");

    match outcome {
        Outcome::Complete(_) => {}
        Outcome::Inconclusive(reason) => {
            panic!("pinned Nat council was inconclusive: {reason:?}")
        }
        Outcome::InternalFault(fault) => {
            panic!("pinned Nat council faulted: {fault:?}")
        }
    }
}
