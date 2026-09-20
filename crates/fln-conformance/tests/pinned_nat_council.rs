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

use std::path::{Path, PathBuf};

use fln::{
    Budget, Declaration, Engine, EngineAdmissionLimits, Environment, KVMap, OleanCheckLimits,
    Outcome,
};
use fln_env::constants::ConstantInfo;
use fln_olean::decl::DeclDecoder;
use fln_olean::region::{OleanView, WalkBudget};

fn reference_lib() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("FLN_REFERENCE_LIB") {
        let path = PathBuf::from(path);
        if path.is_dir() {
            return Some(path);
        }
    }
    for candidate in [
        std::env::var("HOME").ok().map(PathBuf::from),
        Some(PathBuf::from("/home/ubuntu")),
        Some(PathBuf::from("/root")),
    ]
    .into_iter()
    .flatten()
    {
        let path = candidate.join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean");
        if path.is_dir() {
            return Some(path);
        }
    }
    None
}

fn pinned_nat_block(lib: &Path) -> fln_kernel::InductiveBlock {
    let base = lib.join("Init/Prelude.olean");
    let exported = std::fs::read(&base)
        .unwrap_or_else(|error| panic!("read pinned exported Prelude {base:?}: {error}"));
    let server_path = base.with_extension("olean.server");
    let server = std::fs::read(&server_path)
        .unwrap_or_else(|error| panic!("read pinned Prelude server part {server_path:?}: {error}"));
    let private_path = base.with_extension("olean.private");
    let private = std::fs::read(&private_path).unwrap_or_else(|error| {
        panic!("read pinned Prelude private part {private_path:?}: {error}")
    });
    let view = OleanView::parse_with_dependencies(&private, &[&exported, &server])
        .expect("parse pinned Prelude private part against exported + server dependencies");
    let infos = DeclDecoder::new(&view, WalkBudget::default())
        .decode_module_constants()
        .expect("decode pinned Prelude private constant array");

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
            ("Nat" | "Nat.zero" | "Nat.succ" | "Nat.rec", other) => {
                panic!("{name} decoded with unexpected ConstantInfo kind: {other:?}")
            }
            _ => {}
        }
    }

    fln_kernel::InductiveBlock {
        types: vec![nat.expect("pinned Prelude contains Nat inductive row")],
        ctors: vec![
            zero.expect("pinned Prelude contains Nat.zero constructor row"),
            succ.expect("pinned Prelude contains Nat.succ constructor row"),
        ],
        recursors: vec![rec.expect("pinned Prelude contains Nat.rec recursor row")],
    }
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init.Prelude companion chain"]
fn pinned_init_nat_completes_the_two_checker_council() {
    let lib = reference_lib().expect(
        "pinned Reference library is unavailable; install Lean v4.32.0 or set FLN_REFERENCE_LIB before invoking this ignored real-artifact test",
    );
    let block = pinned_nat_block(&lib);

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

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init.Prelude companion chain"]
fn pinned_init_prelude_reaches_two_checker_council_frontier() {
    let lib = reference_lib().expect(
        "pinned Reference library is unavailable; install Lean v4.32.0 or set FLN_REFERENCE_LIB before invoking this ignored real-artifact test",
    );
    let base = lib.join("Init/Prelude.olean");
    let exported = std::fs::read(&base).expect("read exported Prelude");
    let server_path = base.with_extension("olean.server");
    let server = std::fs::read(&server_path).expect("read Prelude server companion");
    let private_path = base.with_extension("olean.private");
    let private = std::fs::read(&private_path).expect("read Prelude private companion");

    let engine = Engine::from_environment(Environment::new());
    let limits = OleanCheckLimits::new(64 * 1024 * 1024, Budget::for_stack_bytes(2 * 1024 * 1024));
    let result = engine.check_olean_artifact_parts(
        &exported,
        Some(&server),
        Some(&private),
        &KVMap::new(),
        limits,
    );
    match result {
        Ok(Outcome::Complete(checked)) => {
            eprintln!(
                "COMPLETE: checked {} declarations!",
                checked.declarations.len()
            );
            assert_eq!(checked.declarations.len(), 2314);
        }
        Ok(Outcome::Inconclusive(reason)) => {
            panic!("INCONCLUSIVE: {reason:?}");
        }
        Ok(Outcome::InternalFault(fault)) => {
            panic!("INTERNAL_FAULT: {fault:?}");
        }
        Err(error) => {
            panic!("FRONTIER: {error}");
        }
    }
}

fn check_decl_closure(target: &[&str]) -> Outcome<fln::CheckedOlean> {
    let lib = reference_lib().expect(
        "pinned Reference library is unavailable; install Lean v4.32.0 or set FLN_REFERENCE_LIB before invoking this ignored real-artifact test",
    );
    let base = lib.join("Init/Prelude.olean");
    let exported = std::fs::read(&base).expect("read exported Prelude");
    let server_path = base.with_extension("olean.server");
    let server = std::fs::read(&server_path).expect("read Prelude server companion");
    let private_path = base.with_extension("olean.private");
    let private = std::fs::read(&private_path).expect("read Prelude private companion");
    let view = OleanView::parse_with_dependencies(&private, &[&exported, &server]).expect("parse");
    let infos = DeclDecoder::new(&view, WalkBudget::default())
        .decode_module_constants()
        .expect("decode");
    let owners: std::collections::BTreeMap<_, _> = infos
        .iter()
        .enumerate()
        .map(|(i, c)| (c.name().clone(), i))
        .collect();
    let mut needed = std::collections::BTreeSet::new();
    let mut queue = vec![fln_core::name::Name::from_components(
        target.iter().copied(),
    )];
    loop {
        let mut added = false;
        while let Some(name) = queue.pop() {
            if !needed.insert(name.clone()) {
                continue;
            }
            added = true;
            if let Some(&idx) = owners.get(&name) {
                let info = &infos[idx];
                let mut exprs = vec![info.constant_val().type_.clone()];
                match info {
                    ConstantInfo::Thm(t) => exprs.push(t.value.clone()),
                    ConstantInfo::Defn(d) => exprs.push(d.value.clone()),
                    ConstantInfo::Ctor(c) => exprs.push(c.base.type_.clone()),
                    _ => {}
                }
                for e in exprs {
                    let mut stack = vec![e];
                    while let Some(cur) = stack.pop() {
                        match cur.node() {
                            fln_core::expr::ExprNode::Const { name, .. } => {
                                if !needed.contains(name) {
                                    queue.push(name.clone());
                                }
                            }
                            fln_core::expr::ExprNode::App { f, a } => {
                                stack.push(f.clone());
                                stack.push(a.clone());
                            }
                            fln_core::expr::ExprNode::Lam {
                                binder_type, body, ..
                            }
                            | fln_core::expr::ExprNode::ForallE {
                                binder_type, body, ..
                            } => {
                                stack.push(binder_type.clone());
                                stack.push(body.clone());
                            }
                            fln_core::expr::ExprNode::LetE {
                                type_, value, body, ..
                            } => {
                                stack.push(type_.clone());
                                stack.push(value.clone());
                                stack.push(body.clone());
                            }
                            fln_core::expr::ExprNode::Proj { expr, .. } => {
                                stack.push(expr.clone());
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        for info in &infos {
            match info {
                ConstantInfo::Induct(ind) => {
                    if needed.contains(&ind.base.name) || ind.all.iter().any(|m| needed.contains(m))
                    {
                        for m in &ind.all {
                            if !needed.contains(m) {
                                queue.push(m.clone());
                            }
                        }
                        for c in &ind.ctors {
                            if !needed.contains(c) {
                                queue.push(c.clone());
                            }
                        }
                    }
                }
                ConstantInfo::Ctor(ctor) => {
                    if needed.contains(&ctor.induct) || needed.contains(&ctor.base.name) {
                        if !needed.contains(&ctor.induct) {
                            queue.push(ctor.induct.clone());
                        }
                        if !needed.contains(&ctor.base.name) {
                            queue.push(ctor.base.name.clone());
                        }
                    }
                }
                ConstantInfo::Rec(rec) => {
                    if rec.all.iter().any(|m| needed.contains(m)) || needed.contains(&rec.base.name)
                    {
                        if !needed.contains(&rec.base.name) {
                            queue.push(rec.base.name.clone());
                        }
                        for m in &rec.all {
                            if !needed.contains(m) {
                                queue.push(m.clone());
                            }
                        }
                    }
                }
                ConstantInfo::Defn(defn) => {
                    if defn.all.iter().any(|m| needed.contains(m)) {
                        for m in &defn.all {
                            if !needed.contains(m) {
                                queue.push(m.clone());
                            }
                        }
                    }
                }
                ConstantInfo::Quot(_) => {
                    if needed.contains(info.name()) {
                        for q in [
                            fln_core::name::Name::from_components(["Quot"]),
                            fln_core::name::Name::from_components(["Quot", "mk"]),
                            fln_core::name::Name::from_components(["Quot", "lift"]),
                            fln_core::name::Name::from_components(["Quot", "ind"]),
                        ] {
                            if !needed.contains(&q) {
                                queue.push(q);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        if queue.is_empty() && !added {
            break;
        }
    }
    let subset: Vec<ConstantInfo> = infos
        .into_iter()
        .filter(|c| needed.contains(c.name()))
        .collect();

    let engine = Engine::from_environment(Environment::new());
    let limits = OleanCheckLimits::new(64 * 1024 * 1024, Budget::for_stack_bytes(2 * 1024 * 1024));
    let mut decoded =
        fln::decode_olean_module_artifacts(&exported, &server, &private, limits.decode)
            .expect("decode");
    decoded.constants = subset;
    engine
        .check_decoded_olean(decoded, &KVMap::new(), limits)
        .expect("check_decoded_olean failed")
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init.Prelude companion chain"]
fn inspect_char_of_nat_proof_2() {
    let outcome = check_decl_closure(&["Char", "ofNat", "_proof_2"]);
    let Outcome::Complete(checked) = outcome else {
        panic!("Char.ofNat._proof_2 dependency closure must pass council, got: {outcome:?}");
    };
    assert!(!checked.declarations.is_empty());
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init.Prelude companion chain"]
fn inspect_nat_mod_core_lt() {
    let outcome = check_decl_closure(&["Nat", "modCore_lt"]);
    let Outcome::Complete(checked) = outcome else {
        panic!("Nat.modCore_lt dependency closure must pass council, got: {outcome:?}");
    };
    assert!(!checked.declarations.is_empty());
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init.Prelude companion chain"]
fn inspect_lean_parser_descr() {
    let outcome = check_decl_closure(&["Lean", "ParserDescr"]);
    let Outcome::Complete(checked) = outcome else {
        panic!("Lean.ParserDescr dependency closure must pass council, got: {outcome:?}");
    };
    assert!(!checked.declarations.is_empty());
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init.Prelude companion chain"]
fn inspect_lean_syntax() {
    let outcome = check_decl_closure(&["Lean", "Syntax"]);
    let Outcome::Complete(checked) = outcome else {
        panic!("Lean.Syntax dependency closure must pass council, got: {outcome:?}");
    };
    assert!(!checked.declarations.is_empty());
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init.Prelude companion chain"]
fn inspect_lean_parser_descr_no_confusion() {
    let outcome = check_decl_closure(&["Lean", "ParserDescr", "noConfusion"]);
    let Outcome::Complete(checked) = outcome else {
        panic!(
            "Lean.ParserDescr.noConfusion dependency closure must pass council, got: {outcome:?}"
        );
    };
    assert!(!checked.declarations.is_empty());
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init.Prelude and Init.Coe companion chains"]
fn pinned_init_coe_council_run() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");
    let prelude_base = lib.join("Init/Prelude.olean");
    let prelude_exported = std::fs::read(&prelude_base).expect("read exported Prelude");
    let prelude_server =
        std::fs::read(prelude_base.with_extension("olean.server")).expect("read Prelude server");
    let prelude_private =
        std::fs::read(prelude_base.with_extension("olean.private")).expect("read Prelude private");

    let coe_base = lib.join("Init/Coe.olean");
    let coe_exported = std::fs::read(&coe_base).expect("read exported Coe");
    let coe_server =
        std::fs::read(coe_base.with_extension("olean.server")).expect("read Coe server");
    let coe_private =
        std::fs::read(coe_base.with_extension("olean.private")).expect("read Coe private");

    let prelude_name = fln_core::name::Name::from_components(["Init", "Prelude"]);
    let coe_name = fln_core::name::Name::from_components(["Init", "Coe"]);

    let modules = [
        fln::OleanModuleInput {
            name: &prelude_name,
            artifact: &prelude_exported,
            server_artifact: Some(&prelude_server),
            private_artifact: Some(&prelude_private),
        },
        fln::OleanModuleInput {
            name: &coe_name,
            artifact: &coe_exported,
            server_artifact: Some(&coe_server),
            private_artifact: Some(&coe_private),
        },
    ];

    let engine = Engine::from_environment(Environment::new());
    let limits = OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
    let result = engine.check_olean_modules(&modules, &KVMap::new(), limits);
    match result {
        Ok(Outcome::Complete(checked)) => {
            eprintln!("COMPLETE: checked {} modules!", checked.modules.len());
            for m in &checked.modules {
                eprintln!(
                    "  module {}: {} declarations",
                    m.name.to_display_string(),
                    m.declarations.len()
                );
            }
            assert_eq!(checked.modules.len(), 2);
            assert_eq!(checked.modules[0].declarations.len(), 2314);
            assert_eq!(checked.modules[1].declarations.len(), 158);
        }
        Ok(Outcome::Inconclusive(reason)) => {
            panic!("INCONCLUSIVE: {reason:?}");
        }
        Ok(Outcome::InternalFault(fault)) => {
            panic!("INTERNAL_FAULT: {fault:?}");
        }
        Err(error) => {
            panic!("FRONTIER: {error}");
        }
    }
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init.Notation companion chain"]
fn inspect_init_notation_module() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");
    let notation_base = lib.join("Init/Notation.olean");
    let exported = std::fs::read(&notation_base).expect("read exported Notation");
    let server =
        std::fs::read(notation_base.with_extension("olean.server")).expect("read Notation server");
    let private = std::fs::read(notation_base.with_extension("olean.private"))
        .expect("read Notation private");

    let limits = OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
    let decoded = fln::decode_olean_module_artifacts(&exported, &server, &private, limits.decode)
        .expect("decode Notation");

    eprintln!("Init.Notation module imports:");
    for import in &decoded.module.imports {
        eprintln!("  import: {}", import.module.to_display_string());
    }
    eprintln!("Init.Notation constant count: {}", decoded.constants.len());
    let mut inducts = Vec::new();
    let mut ctors = Vec::new();
    let mut recs = Vec::new();
    let mut defs = Vec::new();
    let mut thms = Vec::new();
    let mut axioms = Vec::new();
    let mut opaques = Vec::new();
    let mut quots = Vec::new();
    for c in &decoded.constants {
        match c {
            ConstantInfo::Induct(i) => inducts.push(i.base.name.to_display_string()),
            ConstantInfo::Ctor(ctor) => ctors.push(ctor.base.name.to_display_string()),
            ConstantInfo::Rec(r) => recs.push(r.base.name.to_display_string()),
            ConstantInfo::Defn(d) => defs.push(d.base.name.to_display_string()),
            ConstantInfo::Thm(t) => thms.push(t.base.name.to_display_string()),
            ConstantInfo::Axiom(a) => axioms.push(a.base.name.to_display_string()),
            ConstantInfo::Opaque(o) => opaques.push(o.base.name.to_display_string()),
            ConstantInfo::Quot(q) => quots.push(q.base.name.to_display_string()),
        }
    }
    eprintln!("Inductives ({}): {:?}", inducts.len(), inducts);
    eprintln!("Ctors ({}): {:?}", ctors.len(), ctors);
    eprintln!("Recs ({}): {:?}", recs.len(), recs);
    eprintln!("Axioms ({}): {:?}", axioms.len(), axioms);
    eprintln!("Opaques ({}): {:?}", opaques.len(), opaques);
    eprintln!("Quots ({}): {:?}", quots.len(), quots);
    eprintln!("Defs count: {}", defs.len());
    eprintln!("Thms count: {}", thms.len());
    for c in &decoded.constants {
        if c.name()
            .to_display_string()
            .starts_with("Lean.Parser.Category")
        {
            eprintln!("  {:?}: {:?}", c.name().to_display_string(), c);
        }
    }
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init.Prelude, Init.Coe, and Init.Notation companion chains"]
fn preflight_init_notation_dependencies() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let load = |name: &str| {
        let base = lib.join(format!("{name}.olean"));
        let exported = std::fs::read(&base).expect("read exported");
        let server = std::fs::read(base.with_extension("olean.server")).expect("read server");
        let private = std::fs::read(base.with_extension("olean.private")).expect("read private");
        let limits =
            OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
        fln::decode_olean_module_artifacts(&exported, &server, &private, limits.decode)
            .expect("decode")
    };

    let prelude = load("Init/Prelude");
    let coe = load("Init/Coe");
    let notation = load("Init/Notation");

    let mut available = std::collections::BTreeSet::new();
    for c in &prelude.constants {
        available.insert(c.name().clone());
    }
    for c in &coe.constants {
        available.insert(c.name().clone());
    }
    for c in &notation.constants {
        available.insert(c.name().clone());
    }

    eprintln!(
        "Total available constants: Prelude={}, Coe={}, Notation={}",
        prelude.constants.len(),
        coe.constants.len(),
        notation.constants.len()
    );

    let mut missing = std::collections::BTreeSet::new();
    for c in &notation.constants {
        let mut exprs = vec![c.constant_val().type_.clone()];
        match c {
            ConstantInfo::Thm(t) => exprs.push(t.value.clone()),
            ConstantInfo::Defn(d) => exprs.push(d.value.clone()),
            ConstantInfo::Ctor(ctor) => exprs.push(ctor.base.type_.clone()),
            _ => {}
        }
        for e in exprs {
            let mut stack = vec![e];
            while let Some(cur) = stack.pop() {
                match cur.node() {
                    fln_core::expr::ExprNode::Const { name, .. } => {
                        if !available.contains(name) {
                            missing.insert((c.name().clone(), name.clone()));
                        }
                    }
                    fln_core::expr::ExprNode::App { f, a } => {
                        stack.push(f.clone());
                        stack.push(a.clone());
                    }
                    fln_core::expr::ExprNode::Lam {
                        binder_type, body, ..
                    }
                    | fln_core::expr::ExprNode::ForallE {
                        binder_type, body, ..
                    } => {
                        stack.push(binder_type.clone());
                        stack.push(body.clone());
                    }
                    fln_core::expr::ExprNode::LetE {
                        type_, value, body, ..
                    } => {
                        stack.push(type_.clone());
                        stack.push(value.clone());
                        stack.push(body.clone());
                    }
                    fln_core::expr::ExprNode::Proj { expr, .. } => {
                        stack.push(expr.clone());
                    }
                    _ => {}
                }
            }
        }
    }

    eprintln!("Missing constants count: {}", missing.len());
    for (caller, dep) in &missing {
        eprintln!(
            "  caller {} needs missing: {}",
            caller.to_display_string(),
            dep.to_display_string()
        );
    }
    assert!(
        missing.is_empty(),
        "all dependencies of Init.Notation must be available"
    );
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init.Prelude, Init.Coe, and Init.Notation companion chains"]
fn pinned_init_prelude_coe_notation_council_run() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let prelude_base = lib.join("Init/Prelude.olean");
    let prelude_exported = std::fs::read(&prelude_base).expect("read exported Prelude");
    let prelude_server =
        std::fs::read(prelude_base.with_extension("olean.server")).expect("read Prelude server");
    let prelude_private =
        std::fs::read(prelude_base.with_extension("olean.private")).expect("read Prelude private");

    let coe_base = lib.join("Init/Coe.olean");
    let coe_exported = std::fs::read(&coe_base).expect("read exported Coe");
    let coe_server =
        std::fs::read(coe_base.with_extension("olean.server")).expect("read Coe server");
    let coe_private =
        std::fs::read(coe_base.with_extension("olean.private")).expect("read Coe private");

    let notation_base = lib.join("Init/Notation.olean");
    let notation_exported = std::fs::read(&notation_base).expect("read exported Notation");
    let notation_server =
        std::fs::read(notation_base.with_extension("olean.server")).expect("read Notation server");
    let notation_private = std::fs::read(notation_base.with_extension("olean.private"))
        .expect("read Notation private");

    let prelude_name = fln_core::name::Name::from_components(["Init", "Prelude"]);
    let coe_name = fln_core::name::Name::from_components(["Init", "Coe"]);
    let notation_name = fln_core::name::Name::from_components(["Init", "Notation"]);

    let modules = [
        fln::OleanModuleInput {
            name: &prelude_name,
            artifact: &prelude_exported,
            server_artifact: Some(&prelude_server),
            private_artifact: Some(&prelude_private),
        },
        fln::OleanModuleInput {
            name: &coe_name,
            artifact: &coe_exported,
            server_artifact: Some(&coe_server),
            private_artifact: Some(&coe_private),
        },
        fln::OleanModuleInput {
            name: &notation_name,
            artifact: &notation_exported,
            server_artifact: Some(&notation_server),
            private_artifact: Some(&notation_private),
        },
    ];

    let engine = Engine::from_environment(Environment::new());
    let limits = OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
    let result = engine.check_olean_modules(&modules, &KVMap::new(), limits);
    match result {
        Ok(Outcome::Complete(checked)) => {
            eprintln!("COMPLETE: checked {} modules!", checked.modules.len());
            for m in &checked.modules {
                eprintln!(
                    "  module {}: {} declarations",
                    m.name.to_display_string(),
                    m.declarations.len()
                );
            }
            assert_eq!(checked.modules.len(), 3);
            assert_eq!(checked.modules[0].declarations.len(), 2314);
            assert_eq!(checked.modules[1].declarations.len(), 158);
            assert_eq!(checked.modules[2].declarations.len(), 284);
        }
        Ok(Outcome::Inconclusive(reason)) => {
            panic!("INCONCLUSIVE: {reason:?}");
        }
        Ok(Outcome::InternalFault(fault)) => {
            panic!("INTERNAL_FAULT: {fault:?}");
        }
        Err(error) => {
            panic!("FRONTIER: {error}");
        }
    }
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init.Tactics companion chain"]
fn inspect_init_tactics_module() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");
    let tactics_base = lib.join("Init/Tactics.olean");
    let exported = std::fs::read(&tactics_base).expect("read exported Tactics");
    let server =
        std::fs::read(tactics_base.with_extension("olean.server")).expect("read Tactics server");
    let private =
        std::fs::read(tactics_base.with_extension("olean.private")).expect("read Tactics private");

    let limits = OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
    let decoded = fln::decode_olean_module_artifacts(&exported, &server, &private, limits.decode)
        .expect("decode Tactics");

    eprintln!("Init.Tactics module imports:");
    for import in &decoded.module.imports {
        eprintln!("  import: {}", import.module.to_display_string());
    }
    eprintln!("Init.Tactics constant count: {}", decoded.constants.len());
    let mut inducts = Vec::new();
    let mut ctors = Vec::new();
    let mut recs = Vec::new();
    let mut defs = Vec::new();
    let mut thms = Vec::new();
    let mut axioms = Vec::new();
    let mut opaques = Vec::new();
    let mut quots = Vec::new();
    for c in &decoded.constants {
        match c {
            ConstantInfo::Induct(i) => inducts.push(i.base.name.to_display_string()),
            ConstantInfo::Ctor(ctor) => ctors.push(ctor.base.name.to_display_string()),
            ConstantInfo::Rec(r) => recs.push(r.base.name.to_display_string()),
            ConstantInfo::Defn(d) => defs.push(d.base.name.to_display_string()),
            ConstantInfo::Thm(t) => thms.push(t.base.name.to_display_string()),
            ConstantInfo::Axiom(a) => axioms.push(a.base.name.to_display_string()),
            ConstantInfo::Opaque(o) => opaques.push(o.base.name.to_display_string()),
            ConstantInfo::Quot(q) => quots.push(q.base.name.to_display_string()),
        }
    }
    eprintln!("Inductives ({}): {:?}", inducts.len(), inducts);
    eprintln!("Ctors ({}): {:?}", ctors.len(), ctors);
    eprintln!("Recs ({}): {:?}", recs.len(), recs);
    eprintln!("Axioms ({}): {:?}", axioms.len(), axioms);
    eprintln!("Opaques ({}): {:?}", opaques.len(), opaques);
    eprintln!("Quots ({}): {:?}", quots.len(), quots);
    eprintln!("Defs count: {}", defs.len());
    eprintln!("Thms count: {}", thms.len());
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init companion chains"]
fn preflight_init_tactics_dependencies() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let load = |name: &str| {
        let base = lib.join(format!("{name}.olean"));
        let exported = std::fs::read(&base).expect("read exported");
        let server = std::fs::read(base.with_extension("olean.server")).expect("read server");
        let private = std::fs::read(base.with_extension("olean.private")).expect("read private");
        let limits =
            OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
        fln::decode_olean_module_artifacts(&exported, &server, &private, limits.decode)
            .expect("decode")
    };

    let prelude = load("Init/Prelude");
    let coe = load("Init/Coe");
    let notation = load("Init/Notation");
    let tactics = load("Init/Tactics");

    let mut available = std::collections::BTreeSet::new();
    for c in &prelude.constants {
        available.insert(c.name().clone());
    }
    for c in &coe.constants {
        available.insert(c.name().clone());
    }
    for c in &notation.constants {
        available.insert(c.name().clone());
    }
    for c in &tactics.constants {
        available.insert(c.name().clone());
    }

    eprintln!(
        "Total available constants: Prelude={}, Coe={}, Notation={}, Tactics={}",
        prelude.constants.len(),
        coe.constants.len(),
        notation.constants.len(),
        tactics.constants.len()
    );

    let mut missing = std::collections::BTreeSet::new();
    for c in &tactics.constants {
        let mut exprs = vec![c.constant_val().type_.clone()];
        match c {
            ConstantInfo::Thm(t) => exprs.push(t.value.clone()),
            ConstantInfo::Defn(d) => exprs.push(d.value.clone()),
            ConstantInfo::Ctor(ctor) => exprs.push(ctor.base.type_.clone()),
            _ => {}
        }
        for e in exprs {
            let mut stack = vec![e];
            while let Some(cur) = stack.pop() {
                match cur.node() {
                    fln_core::expr::ExprNode::Const { name, .. } => {
                        if !available.contains(name) {
                            missing.insert((c.name().clone(), name.clone()));
                        }
                    }
                    fln_core::expr::ExprNode::App { f, a } => {
                        stack.push(f.clone());
                        stack.push(a.clone());
                    }
                    fln_core::expr::ExprNode::Lam {
                        binder_type, body, ..
                    }
                    | fln_core::expr::ExprNode::ForallE {
                        binder_type, body, ..
                    } => {
                        stack.push(binder_type.clone());
                        stack.push(body.clone());
                    }
                    fln_core::expr::ExprNode::LetE {
                        type_, value, body, ..
                    } => {
                        stack.push(type_.clone());
                        stack.push(value.clone());
                        stack.push(body.clone());
                    }
                    fln_core::expr::ExprNode::Proj { expr, .. } => {
                        stack.push(expr.clone());
                    }
                    _ => {}
                }
            }
        }
    }

    eprintln!("Missing constants count: {}", missing.len());
    for (caller, dep) in &missing {
        eprintln!(
            "  caller {} needs missing: {}",
            caller.to_display_string(),
            dep.to_display_string()
        );
    }
    assert!(
        missing.is_empty(),
        "all dependencies of Init.Tactics must be available"
    );
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init 4-module companion chain"]
fn pinned_init_prelude_coe_notation_tactics_council_run() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let prelude_base = lib.join("Init/Prelude.olean");
    let prelude_exported = std::fs::read(&prelude_base).expect("read exported Prelude");
    let prelude_server =
        std::fs::read(prelude_base.with_extension("olean.server")).expect("read Prelude server");
    let prelude_private =
        std::fs::read(prelude_base.with_extension("olean.private")).expect("read Prelude private");

    let coe_base = lib.join("Init/Coe.olean");
    let coe_exported = std::fs::read(&coe_base).expect("read exported Coe");
    let coe_server =
        std::fs::read(coe_base.with_extension("olean.server")).expect("read Coe server");
    let coe_private =
        std::fs::read(coe_base.with_extension("olean.private")).expect("read Coe private");

    let notation_base = lib.join("Init/Notation.olean");
    let notation_exported = std::fs::read(&notation_base).expect("read exported Notation");
    let notation_server =
        std::fs::read(notation_base.with_extension("olean.server")).expect("read Notation server");
    let notation_private = std::fs::read(notation_base.with_extension("olean.private"))
        .expect("read Notation private");

    let tactics_base = lib.join("Init/Tactics.olean");
    let tactics_exported = std::fs::read(&tactics_base).expect("read exported Tactics");
    let tactics_server =
        std::fs::read(tactics_base.with_extension("olean.server")).expect("read Tactics server");
    let tactics_private =
        std::fs::read(tactics_base.with_extension("olean.private")).expect("read Tactics private");

    let prelude_name = fln_core::name::Name::from_components(["Init", "Prelude"]);
    let coe_name = fln_core::name::Name::from_components(["Init", "Coe"]);
    let notation_name = fln_core::name::Name::from_components(["Init", "Notation"]);
    let tactics_name = fln_core::name::Name::from_components(["Init", "Tactics"]);

    let modules = [
        fln::OleanModuleInput {
            name: &prelude_name,
            artifact: &prelude_exported,
            server_artifact: Some(&prelude_server),
            private_artifact: Some(&prelude_private),
        },
        fln::OleanModuleInput {
            name: &coe_name,
            artifact: &coe_exported,
            server_artifact: Some(&coe_server),
            private_artifact: Some(&coe_private),
        },
        fln::OleanModuleInput {
            name: &notation_name,
            artifact: &notation_exported,
            server_artifact: Some(&notation_server),
            private_artifact: Some(&notation_private),
        },
        fln::OleanModuleInput {
            name: &tactics_name,
            artifact: &tactics_exported,
            server_artifact: Some(&tactics_server),
            private_artifact: Some(&tactics_private),
        },
    ];

    let engine = Engine::from_environment(Environment::new());
    let limits = OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
    let result = engine.check_olean_modules(&modules, &KVMap::new(), limits);
    match result {
        Ok(Outcome::Complete(checked)) => {
            eprintln!("COMPLETE: checked {} modules!", checked.modules.len());
            for m in &checked.modules {
                eprintln!(
                    "  module {}: {} declarations",
                    m.name.to_display_string(),
                    m.declarations.len()
                );
            }
            assert_eq!(checked.modules.len(), 4);
            assert_eq!(checked.modules[0].declarations.len(), 2314);
            assert_eq!(checked.modules[1].declarations.len(), 158);
            assert_eq!(checked.modules[2].declarations.len(), 284);
            assert_eq!(checked.modules[3].declarations.len(), 360);
        }
        Ok(Outcome::Inconclusive(reason)) => {
            panic!("INCONCLUSIVE: {reason:?}");
        }
        Ok(Outcome::InternalFault(fault)) => {
            panic!("INTERNAL_FAULT: {fault:?}");
        }
        Err(error) => {
            panic!("FRONTIER: {error}");
        }
    }
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init companion chains"]
fn inspect_init_sizeof_module() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");
    let sizeof_base = lib.join("Init/SizeOf.olean");
    let exported = std::fs::read(&sizeof_base).expect("read exported SizeOf");
    let server =
        std::fs::read(sizeof_base.with_extension("olean.server")).expect("read SizeOf server");
    let private =
        std::fs::read(sizeof_base.with_extension("olean.private")).expect("read SizeOf private");

    let limits = OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
    let decoded = fln::decode_olean_module_artifacts(&exported, &server, &private, limits.decode)
        .expect("decode SizeOf");

    eprintln!("Init.SizeOf module imports:");
    for import in &decoded.module.imports {
        eprintln!("  import: {}", import.module.to_display_string());
    }
    eprintln!("Init.SizeOf constant count: {}", decoded.constants.len());
    let mut inducts = Vec::new();
    let mut ctors = Vec::new();
    let mut recs = Vec::new();
    let mut defs = Vec::new();
    let mut thms = Vec::new();
    let mut axioms = Vec::new();
    let mut opaques = Vec::new();
    let mut quots = Vec::new();
    for c in &decoded.constants {
        match c {
            ConstantInfo::Induct(i) => inducts.push(i.base.name.to_display_string()),
            ConstantInfo::Ctor(ctor) => ctors.push(ctor.base.name.to_display_string()),
            ConstantInfo::Rec(r) => recs.push(r.base.name.to_display_string()),
            ConstantInfo::Defn(d) => defs.push(d.base.name.to_display_string()),
            ConstantInfo::Thm(t) => thms.push(t.base.name.to_display_string()),
            ConstantInfo::Axiom(a) => axioms.push(a.base.name.to_display_string()),
            ConstantInfo::Opaque(o) => opaques.push(o.base.name.to_display_string()),
            ConstantInfo::Quot(q) => quots.push(q.base.name.to_display_string()),
        }
    }
    eprintln!("Inductives ({}): {:?}", inducts.len(), inducts);
    eprintln!("Ctors ({}): {:?}", ctors.len(), ctors);
    eprintln!("Recs ({}): {:?}", recs.len(), recs);
    eprintln!("Axioms ({}): {:?}", axioms.len(), axioms);
    eprintln!("Opaques ({}): {:?}", opaques.len(), opaques);
    eprintln!("Quots ({}): {:?}", quots.len(), quots);
    eprintln!("Defs count: {}", defs.len());
    eprintln!("Thms count: {}", thms.len());
    for c in &decoded.constants {
        if c.name().to_display_string() == "Unit.sizeOf" {
            eprintln!("Found Unit.sizeOf:");
            eprintln!("  kind: {:?}", match c { ConstantInfo::Thm(_) => "Thm", ConstantInfo::Defn(_) => "Defn", _ => "Other" });
            eprintln!("  type: {:?}", c.constant_val().type_);
            if let ConstantInfo::Thm(t) = c {
                eprintln!("  thm value: {:?}", t.value);
            } else if let ConstantInfo::Defn(d) = c {
                eprintln!("  defn value: {:?}", d.value);
            }
        }
    }
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init companion chains"]
fn preflight_init_sizeof_dependencies() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let load = |name: &str| {
        let base = lib.join(format!("{name}.olean"));
        let exported = std::fs::read(&base).expect("read exported");
        let server = std::fs::read(base.with_extension("olean.server")).expect("read server");
        let private = std::fs::read(base.with_extension("olean.private")).expect("read private");
        let limits =
            OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
        fln::decode_olean_module_artifacts(&exported, &server, &private, limits.decode)
            .expect("decode")
    };

    let prelude = load("Init/Prelude");
    let coe = load("Init/Coe");
    let notation = load("Init/Notation");
    let tactics = load("Init/Tactics");
    let sizeof = load("Init/SizeOf");

    let mut available = std::collections::BTreeSet::new();
    for c in &prelude.constants {
        available.insert(c.name().clone());
    }
    for c in &coe.constants {
        available.insert(c.name().clone());
    }
    for c in &notation.constants {
        available.insert(c.name().clone());
    }
    for c in &tactics.constants {
        available.insert(c.name().clone());
    }
    for c in &sizeof.constants {
        available.insert(c.name().clone());
    }

    eprintln!(
        "Total available constants before SizeOf: Prelude={}, Coe={}, Notation={}, Tactics={}",
        prelude.constants.len(),
        coe.constants.len(),
        notation.constants.len(),
        tactics.constants.len()
    );
    eprintln!("Init.SizeOf has {} constants", sizeof.constants.len());

    let mut missing = std::collections::BTreeSet::new();
    for c in &sizeof.constants {
        let mut exprs = vec![c.constant_val().type_.clone()];
        match c {
            ConstantInfo::Thm(t) => exprs.push(t.value.clone()),
            ConstantInfo::Defn(d) => exprs.push(d.value.clone()),
            ConstantInfo::Ctor(ctor) => exprs.push(ctor.base.type_.clone()),
            _ => {}
        }
        for e in exprs {
            let mut stack = vec![e];
            while let Some(cur) = stack.pop() {
                match cur.node() {
                    fln_core::expr::ExprNode::Const { name, .. } => {
                        if !available.contains(name) {
                            missing.insert((c.name().clone(), name.clone()));
                        }
                    }
                    fln_core::expr::ExprNode::App { f, a } => {
                        stack.push(f.clone());
                        stack.push(a.clone());
                    }
                    fln_core::expr::ExprNode::Lam {
                        binder_type, body, ..
                    }
                    | fln_core::expr::ExprNode::ForallE {
                        binder_type, body, ..
                    } => {
                        stack.push(binder_type.clone());
                        stack.push(body.clone());
                    }
                    fln_core::expr::ExprNode::LetE {
                        type_, value, body, ..
                    } => {
                        stack.push(type_.clone());
                        stack.push(value.clone());
                        stack.push(body.clone());
                    }
                    fln_core::expr::ExprNode::Proj { expr, .. } => {
                        stack.push(expr.clone());
                    }
                    _ => {}
                }
            }
        }
    }

    eprintln!("Missing constants count: {}", missing.len());
    for (caller, dep) in &missing {
        eprintln!(
            "  caller {} needs missing: {}",
            caller.to_display_string(),
            dep.to_display_string()
        );
    }
    assert!(
        missing.is_empty(),
        "all dependencies of Init.SizeOf must be available"
    );
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init companion chains"]
fn inspect_init_core_module() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");
    let core_base = lib.join("Init/Core.olean");
    let exported = std::fs::read(&core_base).expect("read exported Core");
    let server =
        std::fs::read(core_base.with_extension("olean.server")).expect("read Core server");
    let private =
        std::fs::read(core_base.with_extension("olean.private")).expect("read Core private");

    let limits = OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
    let decoded = fln::decode_olean_module_artifacts(&exported, &server, &private, limits.decode)
        .expect("decode Core");

    eprintln!("Init.Core module imports:");
    for import in &decoded.module.imports {
        eprintln!("  import: {}", import.module.to_display_string());
    }
    eprintln!("Init.Core constant count: {}", decoded.constants.len());
    let mut inducts = Vec::new();
    let mut ctors = Vec::new();
    let mut recs = Vec::new();
    let mut defs = Vec::new();
    let mut thms = Vec::new();
    let mut axioms = Vec::new();
    let mut opaques = Vec::new();
    let mut quots = Vec::new();
    for c in &decoded.constants {
        match c {
            ConstantInfo::Induct(i) => inducts.push(i.base.name.to_display_string()),
            ConstantInfo::Ctor(ctor) => ctors.push(ctor.base.name.to_display_string()),
            ConstantInfo::Rec(r) => recs.push(r.base.name.to_display_string()),
            ConstantInfo::Defn(d) => defs.push(d.base.name.to_display_string()),
            ConstantInfo::Thm(t) => thms.push(t.base.name.to_display_string()),
            ConstantInfo::Axiom(a) => axioms.push(a.base.name.to_display_string()),
            ConstantInfo::Opaque(o) => opaques.push(o.base.name.to_display_string()),
            ConstantInfo::Quot(q) => quots.push(q.base.name.to_display_string()),
        }
    }
    eprintln!("Inductives ({}): {:?}", inducts.len(), inducts);
    eprintln!("Ctors ({}): {:?}", ctors.len(), ctors);
    eprintln!("Recs ({}): {:?}", recs.len(), recs);
    eprintln!("Axioms ({}): {:?}", axioms.len(), axioms);
    eprintln!("Opaques ({}): {:?}", opaques.len(), opaques);
    eprintln!("Quots ({}): {:?}", quots.len(), quots);
    eprintln!("Defs count: {}", defs.len());
    eprintln!("Thms count: {}", thms.len());
    for c in &decoded.constants {
        if c.name().to_display_string() == "Function.id_comp" {
            eprintln!("FOUND Function.id_comp: {:?}", c);
        }
    }
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init companion chains"]
fn inspect_init_control_modules() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let inspect = |rel_path: &str| {
        let base = lib.join(format!("{rel_path}.olean"));
        let exported = std::fs::read(&base).expect("read exported");
        let server = std::fs::read(base.with_extension("olean.server")).expect("read server");
        let private = std::fs::read(base.with_extension("olean.private")).expect("read private");
        let limits =
            OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
        let decoded =
            fln::decode_olean_module_artifacts(&exported, &server, &private, limits.decode)
                .expect("decode");
        eprintln!("=== Module {rel_path} ===");
        eprintln!("  imports: {:?}", decoded.module.imports.iter().map(|i| i.module.to_display_string()).collect::<Vec<_>>());
        eprintln!("  total declarations: {}", decoded.constants.len());
        let mut inducts = Vec::new();
        let mut ctors = Vec::new();
        let mut recs = Vec::new();
        let mut defs = Vec::new();
        let mut thms = Vec::new();
        let mut axioms = Vec::new();
        let mut opaques = Vec::new();
        let mut quots = Vec::new();
        for c in &decoded.constants {
            match c {
                ConstantInfo::Induct(i) => inducts.push(i.base.name.to_display_string()),
                ConstantInfo::Ctor(ctor) => ctors.push(ctor.base.name.to_display_string()),
                ConstantInfo::Rec(r) => recs.push(r.base.name.to_display_string()),
                ConstantInfo::Defn(d) => defs.push(d.base.name.to_display_string()),
                ConstantInfo::Thm(t) => thms.push(t.base.name.to_display_string()),
                ConstantInfo::Axiom(a) => axioms.push(a.base.name.to_display_string()),
                ConstantInfo::Opaque(o) => opaques.push(o.base.name.to_display_string()),
                ConstantInfo::Quot(q) => quots.push(q.base.name.to_display_string()),
            }
        }
        eprintln!("  Inducts ({}): {:?}", inducts.len(), inducts);
        eprintln!("  Ctors ({}): {:?}", ctors.len(), ctors);
        eprintln!("  Recs ({}): {:?}", recs.len(), recs);
        eprintln!("  Defs count: {}", defs.len());
        eprintln!("  Thms count: {}", thms.len());
        eprintln!("  Axioms ({}): {:?}", axioms.len(), axioms);
        eprintln!("  Opaques ({}): {:?}", opaques.len(), opaques);
        eprintln!("  Quots ({}): {:?}", quots.len(), quots);
        for d in defs.iter().take(10) {
            eprintln!("    def sample: {d}");
        }
        for t in thms.iter().take(10) {
            eprintln!("    thm sample: {t}");
        }
    };

    inspect("Init/Control/MonadAttach");
    inspect("Init/Control/Basic");
    inspect("Init/Control/Id");
    inspect("Init/Control/Except");
    inspect("Init/Control/Reader");
    inspect("Init/Control/State");
    inspect("Init/Control/StateCps");
    inspect("Init/Control/ExceptCps");
    inspect("Init/Control/EState");
    inspect("Init/Control/Option");
    inspect("Init/Control/Lawful/MonadLift/Basic");
    inspect("Init/Control/Lawful/MonadLift/Instances");
    inspect("Init/Control/Lawful/MonadLift/Lemmas");
    inspect("Init/Control/Lawful/MonadLift");
    inspect("Init/Control/Lawful/MonadAttach/Instances");
    inspect("Init/Control/Lawful/MonadAttach/Lemmas");
    inspect("Init/Control/Lawful/MonadAttach");
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init companion chains"]
fn preflight_init_control_council_fast_admission() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let load = |name: &str| {
        let base = lib.join(format!("{name}.olean"));
        let exported = std::fs::read(&base).expect("read exported");
        let server = std::fs::read(base.with_extension("olean.server")).expect("read server");
        let private = std::fs::read(base.with_extension("olean.private")).expect("read private");
        let limits =
            OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
        fln::decode_olean_module_artifacts(&exported, &server, &private, limits.decode)
            .expect("decode")
    };

    let base_modules = [
        "Init/Prelude",
        "Init/Coe",
        "Init/Notation",
        "Init/Tactics",
        "Init/SizeOf",
        "Init/Core",
        "Init/BinderNameHint",
    ];

    let mut env = Environment::new();
    for name in &base_modules {
        let m = load(name);
        for c in m.constants {
            env = env.add_decl(c).expect("add decl to env");
        }
    }
    eprintln!("Preloaded base environment has {} constants", env.len());

    let engine = Engine::from_environment(env);
    let limits = OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));

    let monad_attach = load("Init/Control/MonadAttach");
    eprintln!(
        "Checking Init/Control/MonadAttach ({} constants)...",
        monad_attach.constants.len()
    );
    let outcome = engine
        .check_decoded_olean(monad_attach, &KVMap::new(), limits)
        .expect("check MonadAttach");
    let monad_attach_engine = match outcome {
        Outcome::Complete(checked) => {
            eprintln!(
                "SUCCESS! Checked MonadAttach with {} declarations!",
                checked.declarations.len()
            );
            assert_eq!(checked.declarations.len(), 30);
            checked.engine
        }
        Outcome::Inconclusive(reason) => panic!("INCONCLUSIVE: {reason:?}"),
        Outcome::InternalFault(fault) => panic!("FAULT: {fault:?}"),
    };

    let basic = load("Init/Control/Basic");
    eprintln!(
        "Checking Init/Control/Basic ({} constants)...",
        basic.constants.len()
    );
    let outcome = monad_attach_engine
        .check_decoded_olean(basic, &KVMap::new(), limits)
        .expect("check Basic");
    let basic_engine = match outcome {
        Outcome::Complete(checked) => {
            eprintln!(
                "SUCCESS! Checked Basic with {} declarations!",
                checked.declarations.len()
            );
            assert_eq!(checked.declarations.len(), 108);
            checked.engine
        }
        Outcome::Inconclusive(reason) => panic!("INCONCLUSIVE: {reason:?}"),
        Outcome::InternalFault(fault) => panic!("FAULT: {fault:?}"),
    };

    let id = load("Init/Control/Id");
    eprintln!(
        "Checking Init/Control/Id ({} constants)...",
        id.constants.len()
    );
    let outcome = basic_engine
        .check_decoded_olean(id, &KVMap::new(), limits)
        .expect("check Id");
    let id_engine = match outcome {
        Outcome::Complete(checked) => {
            eprintln!(
                "SUCCESS! Checked Id with {} declarations!",
                checked.declarations.len()
            );
            assert_eq!(checked.declarations.len(), 12);
            checked.engine
        }
        Outcome::Inconclusive(reason) => panic!("INCONCLUSIVE: {reason:?}"),
        Outcome::InternalFault(fault) => panic!("FAULT: {fault:?}"),
    };

    let except = load("Init/Control/Except");
    eprintln!(
        "Checking Init/Control/Except ({} constants)...",
        except.constants.len()
    );
    let outcome = id_engine
        .check_decoded_olean(except, &KVMap::new(), limits)
        .expect("check Except");
    let except_engine = match outcome {
        Outcome::Complete(checked) => {
            eprintln!(
                "SUCCESS! Checked Except with {} declarations!",
                checked.declarations.len()
            );
            assert_eq!(checked.declarations.len(), 62);
            checked.engine
        }
        Outcome::Inconclusive(reason) => panic!("INCONCLUSIVE: {reason:?}"),
        Outcome::InternalFault(fault) => panic!("FAULT: {fault:?}"),
    };

    let reader = load("Init/Control/Reader");
    eprintln!(
        "Checking Init/Control/Reader ({} constants)...",
        reader.constants.len()
    );
    let outcome = except_engine
        .check_decoded_olean(reader, &KVMap::new(), limits)
        .expect("check Reader");
    let reader_engine = match outcome {
        Outcome::Complete(checked) => {
            eprintln!(
                "SUCCESS! Checked Reader with {} declarations!",
                checked.declarations.len()
            );
            assert_eq!(checked.declarations.len(), 9);
            checked.engine
        }
        Outcome::Inconclusive(reason) => panic!("INCONCLUSIVE: {reason:?}"),
        Outcome::InternalFault(fault) => panic!("FAULT: {fault:?}"),
    };

    let state = load("Init/Control/State");
    eprintln!(
        "Checking Init/Control/State ({} constants)...",
        state.constants.len()
    );
    let outcome = reader_engine
        .check_decoded_olean(state, &KVMap::new(), limits)
        .expect("check State");
    match outcome {
        Outcome::Complete(checked) => {
            eprintln!(
                "SUCCESS! Checked State with {} declarations!",
                checked.declarations.len()
            );
            assert_eq!(checked.declarations.len(), 33);
        }
        Outcome::Inconclusive(reason) => panic!("INCONCLUSIVE: {reason:?}"),
        Outcome::InternalFault(fault) => panic!("FAULT: {fault:?}"),
    }

    eprintln!("ALL 6 CONTROL MODULES (254 DECLARATIONS) VERIFIED THROUGH TWO-CHECKER COUNCIL!");
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init companion chains"]
fn preflight_extended_12_modules_council_fast_admission() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let load = |name: &str| {
        let base = lib.join(format!("{name}.olean"));
        let exported = std::fs::read(&base).expect("read exported");
        let server = std::fs::read(base.with_extension("olean.server")).expect("read server");
        let private = std::fs::read(base.with_extension("olean.private")).expect("read private");
        let limits =
            OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
        fln::decode_olean_module_artifacts(&exported, &server, &private, limits.decode)
            .expect("decode")
    };

    let base_modules = [
        "Init/Prelude",
        "Init/Coe",
        "Init/Notation",
        "Init/Tactics",
        "Init/SizeOf",
        "Init/Core",
        "Init/BinderNameHint",
        "Init/Control/MonadAttach",
        "Init/Control/Basic",
        "Init/Control/Id",
        "Init/Control/Except",
        "Init/Control/Reader",
        "Init/Control/State",
    ];

    let mut env = Environment::new();
    for name in &base_modules {
        let m = load(name);
        for c in m.constants {
            env = env.add_decl(c).expect("add decl to env");
        }
    }
    eprintln!("Preloaded 13-module base environment has {} constants", env.len());

    let mut engine = Engine::from_environment(env);
    let limits = OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));

    let candidates = [
        ("Init/Control/Lawful/MonadLift/Basic", 16),
        ("Init/Data/PLift", 7),
        ("Init/Data/ULift", 7),
        ("Init/Data/Zero", 13),
        ("Init/Data/Cast", 15),
        ("Init/Data/Option/Coe", 1),
        ("Init/Data/LawfulHashable", 9),
        ("Init/Data/Array/Set", 4),
        ("Init/Data/Slice/Basic", 24),
        ("Init/Data/Order/Classes", 109),
        ("Init/Dynamic", 28),
        ("Init/Try", 43),
    ];

    let mut total_new_decls = 0;
    for (name, expected_count) in candidates {
        let start = std::time::Instant::now();
        let m = load(name);
        eprintln!("Checking candidate {name} ({} declarations)...", m.constants.len());
        let outcome = engine
            .check_decoded_olean(m, &KVMap::new(), limits)
            .unwrap_or_else(|err| panic!("check failed for {name}: {err}"));
        match outcome {
            Outcome::Complete(checked) => {
                let elapsed = start.elapsed();
                eprintln!(
                    "SUCCESS! Checked {name} with {} declarations in {:.2?}!",
                    checked.declarations.len(),
                    elapsed
                );
                assert_eq!(checked.declarations.len(), expected_count);
                total_new_decls += checked.declarations.len();
                engine = checked.engine;
            }
            Outcome::Inconclusive(reason) => panic!("INCONCLUSIVE for {name}: {reason:?}"),
            Outcome::InternalFault(fault) => panic!("FAULT for {name}: {fault:?}"),
        }
    }

    assert_eq!(total_new_decls, 276);
    eprintln!(
        "ALL 12 EXTENDED MODULES ({total_new_decls} DECLARATIONS) VERIFIED THROUGH TWO-CHECKER COUNCIL!"
    );
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init companion chains"]
fn preflight_candidate_next_batch_council_admission() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let load = |name: &str| {
        let base = lib.join(format!("{name}.olean"));
        let exported = std::fs::read(&base).expect("read exported");
        let server = std::fs::read(base.with_extension("olean.server")).expect("read server");
        let private = std::fs::read(base.with_extension("olean.private")).expect("read private");
        let limits =
            OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
        fln::decode_olean_module_artifacts(&exported, &server, &private, limits.decode)
            .expect("decode")
    };

    let base_modules = [
        "Init/Prelude",
        "Init/Coe",
        "Init/Notation",
        "Init/Tactics",
        "Init/SizeOf",
        "Init/Core",
        "Init/BinderNameHint",
        "Init/Control/MonadAttach",
        "Init/Control/Basic",
        "Init/Control/Id",
        "Init/Control/Except",
        "Init/Control/Reader",
        "Init/Control/State",
        "Init/Control/Lawful/MonadLift/Basic",
        "Init/Data/PLift",
        "Init/Data/ULift",
        "Init/Data/Zero",
        "Init/Data/Cast",
        "Init/Data/Option/Coe",
        "Init/Data/LawfulHashable",
        "Init/Data/Array/Set",
        "Init/Data/Slice/Basic",
        "Init/Data/Order/Classes",
        "Init/Dynamic",
        "Init/Try",
    ];

    let mut env = Environment::new();
    let mut set_of_all: std::collections::BTreeSet<fln_core::name::Name> = std::collections::BTreeSet::new();
    let mut available_consts: std::collections::BTreeSet<fln_core::name::Name> = std::collections::BTreeSet::new();
    for name in &base_modules {
        set_of_all.insert(fln_core::name::Name::from_components(name.split('/')));
        let m = load(name);
        for c in m.constants {
            available_consts.insert(c.name().clone());
            env = env.add_decl(c).expect("add decl to env");
        }
    }
    eprintln!("Preloaded 25-module base environment has {} constants", env.len());

    let mut engine = Engine::from_environment(env);
    let limits = OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));

    let candidates = [
        "Init/Data/NeZero",
        "Init/Syntax",
        "Init/Grind/Annotated",
        "Init/Grind/Attr",
        "Init/Grind/Lint",
        "Init/Internal/Order/Tactic",
        "Init/Sym/DSimp/DSimprocDSL",
        "Init/Sym/Simp/SimprocDSL",
        "Init/SimpLemmas",
        "Init/Grind/Interactive",
        "Init/Grind/Tactics",
        "Init/Data/Option/Basic",
        "Init/Data/Nat/Basic",
    ];

    for name in candidates {
        let start = std::time::Instant::now();
        let m = load(name);
        let num_decls = m.constants.len();
        eprintln!("\n=== CANDIDATE {name} ({num_decls} declarations) ===");

        let mut missing_imports = Vec::new();
        for imp in &m.module.imports {
            if !set_of_all.contains(&imp.module) {
                missing_imports.push(imp.module.to_display_string());
            }
        }
        if !missing_imports.is_empty() {
            eprintln!("SKIPPING {name}: missing imports {missing_imports:?}");
            continue;
        }

        let mut check_consts = available_consts.clone();
        for c in &m.constants {
            check_consts.insert(c.name().clone());
        }

        let mut missing_consts = std::collections::BTreeSet::new();
        for c in &m.constants {
            let mut exprs = vec![c.constant_val().type_.clone()];
            match c {
                ConstantInfo::Thm(t) => exprs.push(t.value.clone()),
                ConstantInfo::Defn(d) => exprs.push(d.value.clone()),
                ConstantInfo::Ctor(ctor) => exprs.push(ctor.base.type_.clone()),
                _ => {}
            }
            for e in exprs {
                let mut stack = vec![e];
                while let Some(cur) = stack.pop() {
                    match cur.node() {
                        fln_core::expr::ExprNode::Const { name: cname, .. } => {
                            if !check_consts.contains(cname) {
                                missing_consts.insert(cname.clone());
                            }
                        }
                        fln_core::expr::ExprNode::App { f, a } => {
                            stack.push(f.clone());
                            stack.push(a.clone());
                        }
                        fln_core::expr::ExprNode::Lam {
                            binder_type, body, ..
                        }
                        | fln_core::expr::ExprNode::ForallE {
                            binder_type, body, ..
                        } => {
                            stack.push(binder_type.clone());
                            stack.push(body.clone());
                        }
                        fln_core::expr::ExprNode::LetE {
                            type_, value, body, ..
                        } => {
                            stack.push(type_.clone());
                            stack.push(value.clone());
                            stack.push(body.clone());
                        }
                        fln_core::expr::ExprNode::Proj { expr, .. } => {
                            stack.push(expr.clone());
                        }
                        _ => {}
                    }
                }
            }
        }

        if !missing_consts.is_empty() {
            eprintln!(
                "SKIPPING {name}: {} missing constant references (sample: {:?})",
                missing_consts.len(),
                missing_consts.iter().take(5).map(|n| n.to_display_string()).collect::<Vec<_>>()
            );
            continue;
        }

        eprintln!("All imports and constants closed! Running council check...");
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            engine.clone().check_decoded_olean(m, &KVMap::new(), limits)
        }));
        match result {
            Ok(Ok(Outcome::Complete(checked))) => {
                let elapsed = start.elapsed();
                eprintln!(
                    "PASS: Checked {name} with {} declarations in {:.2?}!",
                    checked.declarations.len(),
                    elapsed
                );
                set_of_all.insert(fln_core::name::Name::from_components(name.split('/')));
                for c in &checked.declarations {
                    available_consts.insert(c.name.clone());
                }
                engine = checked.engine;
            }
            Ok(Ok(Outcome::Inconclusive(reason))) => {
                eprintln!("INCONCLUSIVE for {name}: {reason:?}");
            }
            Ok(Ok(Outcome::InternalFault(fault))) => {
                eprintln!("FAULT for {name}: {fault:?}");
            }
            Ok(Err(err)) => {
                eprintln!("ERR for {name}: {err}");
            }
            Err(_) => {
                eprintln!("PANIC for {name}");
            }
        }
    }
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init companion chains"]
fn preflight_init_core_dependencies() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let load = |name: &str| {
        let base = lib.join(format!("{name}.olean"));
        let exported = std::fs::read(&base).expect("read exported");
        let server = std::fs::read(base.with_extension("olean.server")).expect("read server");
        let private = std::fs::read(base.with_extension("olean.private")).expect("read private");
        let limits =
            OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
        fln::decode_olean_module_artifacts(&exported, &server, &private, limits.decode)
            .expect("decode")
    };

    let prelude = load("Init/Prelude");
    let coe = load("Init/Coe");
    let notation = load("Init/Notation");
    let tactics = load("Init/Tactics");
    let sizeof = load("Init/SizeOf");
    let core = load("Init/Core");

    let mut available = std::collections::BTreeSet::new();
    for c in &prelude.constants {
        available.insert(c.name().clone());
    }
    for c in &coe.constants {
        available.insert(c.name().clone());
    }
    for c in &notation.constants {
        available.insert(c.name().clone());
    }
    for c in &tactics.constants {
        available.insert(c.name().clone());
    }
    for c in &sizeof.constants {
        available.insert(c.name().clone());
    }
    for c in &core.constants {
        available.insert(c.name().clone());
    }

    eprintln!(
        "Total available constants: Prelude={}, Coe={}, Notation={}, Tactics={}, SizeOf={}, Core={}",
        prelude.constants.len(),
        coe.constants.len(),
        notation.constants.len(),
        tactics.constants.len(),
        sizeof.constants.len(),
        core.constants.len()
    );

    let mut missing = std::collections::BTreeSet::new();
    for c in &core.constants {
        let mut exprs = vec![c.constant_val().type_.clone()];
        match c {
            ConstantInfo::Thm(t) => exprs.push(t.value.clone()),
            ConstantInfo::Defn(d) => exprs.push(d.value.clone()),
            ConstantInfo::Ctor(ctor) => exprs.push(ctor.base.type_.clone()),
            _ => {}
        }
        for e in exprs {
            let mut stack = vec![e];
            while let Some(cur) = stack.pop() {
                match cur.node() {
                    fln_core::expr::ExprNode::Const { name, .. } => {
                        if !available.contains(name) {
                            missing.insert((c.name().clone(), name.clone()));
                        }
                    }
                    fln_core::expr::ExprNode::App { f, a } => {
                        stack.push(f.clone());
                        stack.push(a.clone());
                    }
                    fln_core::expr::ExprNode::Lam {
                        binder_type, body, ..
                    }
                    | fln_core::expr::ExprNode::ForallE {
                        binder_type, body, ..
                    } => {
                        stack.push(binder_type.clone());
                        stack.push(body.clone());
                    }
                    fln_core::expr::ExprNode::LetE {
                        type_, value, body, ..
                    } => {
                        stack.push(type_.clone());
                        stack.push(value.clone());
                        stack.push(body.clone());
                    }
                    fln_core::expr::ExprNode::Proj { expr, .. } => {
                        stack.push(expr.clone());
                    }
                    _ => {}
                }
            }
        }
    }

    eprintln!("Missing constants count: {}", missing.len());
    for (caller, dep) in &missing {
        eprintln!(
            "  caller {} needs missing: {}",
            caller.to_display_string(),
            dep.to_display_string()
        );
    }
    assert!(
        missing.is_empty(),
        "all dependencies of Init.Core must be available"
    );
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init companion chains"]
fn preflight_init_bindernamehint_dependencies() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let load = |name: &str| {
        let base = lib.join(format!("{name}.olean"));
        let exported = std::fs::read(&base).expect("read exported");
        let server = std::fs::read(base.with_extension("olean.server")).expect("read server");
        let private = std::fs::read(base.with_extension("olean.private")).expect("read private");
        let limits =
            OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
        fln::decode_olean_module_artifacts(&exported, &server, &private, limits.decode)
            .expect("decode")
    };

    let prelude = load("Init/Prelude");
    let coe = load("Init/Coe");
    let notation = load("Init/Notation");
    let tactics = load("Init/Tactics");
    let sizeof = load("Init/SizeOf");
    let core = load("Init/Core");
    let bnh = load("Init/BinderNameHint");

    let mut available = std::collections::BTreeSet::new();
    for c in &prelude.constants {
        available.insert(c.name().clone());
    }
    for c in &coe.constants {
        available.insert(c.name().clone());
    }
    for c in &notation.constants {
        available.insert(c.name().clone());
    }
    for c in &tactics.constants {
        available.insert(c.name().clone());
    }
    for c in &sizeof.constants {
        available.insert(c.name().clone());
    }
    for c in &core.constants {
        available.insert(c.name().clone());
    }
    for c in &bnh.constants {
        available.insert(c.name().clone());
    }

    assert_eq!(bnh.constants.len(), 2, "Init.BinderNameHint has 2 declarations");

    let mut missing = std::collections::BTreeSet::new();
    for c in &bnh.constants {
        let mut exprs = vec![c.constant_val().type_.clone()];
        match c {
            ConstantInfo::Thm(t) => exprs.push(t.value.clone()),
            ConstantInfo::Defn(d) => exprs.push(d.value.clone()),
            ConstantInfo::Ctor(ctor) => exprs.push(ctor.base.type_.clone()),
            _ => {}
        }
        for e in exprs {
            let mut stack = vec![e];
            while let Some(cur) = stack.pop() {
                match cur.node() {
                    fln_core::expr::ExprNode::Const { name, .. } => {
                        if !available.contains(name) {
                            missing.insert((c.name().clone(), name.clone()));
                        }
                    }
                    fln_core::expr::ExprNode::App { f, a } => {
                        stack.push(f.clone());
                        stack.push(a.clone());
                    }
                    fln_core::expr::ExprNode::Lam {
                        binder_type, body, ..
                    }
                    | fln_core::expr::ExprNode::ForallE {
                        binder_type, body, ..
                    } => {
                        stack.push(binder_type.clone());
                        stack.push(body.clone());
                    }
                    fln_core::expr::ExprNode::LetE {
                        type_, value, body, ..
                    } => {
                        stack.push(type_.clone());
                        stack.push(value.clone());
                        stack.push(body.clone());
                    }
                    fln_core::expr::ExprNode::Proj { expr, .. } => {
                        stack.push(expr.clone());
                    }
                    _ => {}
                }
            }
        }
    }

    assert!(
        missing.is_empty(),
        "all dependencies of Init.BinderNameHint must be available: {missing:?}"
    );
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init companion chains"]
fn preflight_candidate_modules() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let load = |name: &str| {
        let base = lib.join(format!("{name}.olean"));
        let exported = std::fs::read(&base).expect("read exported");
        let server = std::fs::read(base.with_extension("olean.server")).expect("read server");
        let private = std::fs::read(base.with_extension("olean.private")).expect("read private");
        let limits =
            OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
        fln::decode_olean_module_artifacts(&exported, &server, &private, limits.decode)
            .expect("decode")
    };

    let module_names = [
        "Init/Prelude",
        "Init/Coe",
        "Init/Notation",
        "Init/Tactics",
        "Init/SizeOf",
        "Init/Core",
        "Init/BinderNameHint",
        "Init/Control/MonadAttach",
        "Init/Control/Basic",
        "Init/Control/Id",
        "Init/Control/Except",
        "Init/Control/Reader",
        "Init/Control/State",
    ];

    let mut set_of_names = std::collections::BTreeSet::new();
    for name in &module_names {
        let fln_name = fln_core::name::Name::from_components(name.split('/'));
        set_of_names.insert(fln_name);
    }

    let mut total_consts = 0;
    for name in &module_names {
        let m = load(name);
        total_consts += m.constants.len();
        eprintln!("  module {}: {} declarations", name, m.constants.len());
        for imp in &m.module.imports {
            eprintln!("    imports: {}", imp.module.to_display_string());
            assert!(
                set_of_names.contains(&imp.module),
                "Module {} imports {} which is NOT in the set!",
                name,
                imp.module.to_display_string()
            );
        }
    }
    let mut available_consts = std::collections::BTreeSet::new();
    let mut missing_by_module: std::collections::BTreeMap<&str, std::collections::BTreeSet<(fln_core::name::Name, fln_core::name::Name)>> =
        std::collections::BTreeMap::new();
    for name in &module_names {
        let m = load(name);
        for c in &m.constants {
            available_consts.insert(c.name().clone());
        }
        for c in &m.constants {
            let mut exprs = vec![c.constant_val().type_.clone()];
            match c {
                ConstantInfo::Thm(t) => exprs.push(t.value.clone()),
                ConstantInfo::Defn(d) => exprs.push(d.value.clone()),
                ConstantInfo::Ctor(ctor) => exprs.push(ctor.base.type_.clone()),
                _ => {}
            }
            for e in exprs {
                let mut stack = vec![e];
                while let Some(cur) = stack.pop() {
                    match cur.node() {
                        fln_core::expr::ExprNode::Const { name: cname, .. } => {
                            if !available_consts.contains(cname) {
                                missing_by_module
                                    .entry(*name)
                                    .or_default()
                                    .insert((c.name().clone(), cname.clone()));
                            }
                        }
                        fln_core::expr::ExprNode::App { f, a } => {
                            stack.push(f.clone());
                            stack.push(a.clone());
                        }
                        fln_core::expr::ExprNode::Lam {
                            binder_type, body, ..
                        }
                        | fln_core::expr::ExprNode::ForallE {
                            binder_type, body, ..
                        } => {
                            stack.push(binder_type.clone());
                            stack.push(body.clone());
                        }
                        fln_core::expr::ExprNode::LetE {
                            type_, value, body, ..
                        } => {
                            stack.push(type_.clone());
                            stack.push(value.clone());
                            stack.push(body.clone());
                        }
                        fln_core::expr::ExprNode::Proj { expr, .. } => {
                            stack.push(expr.clone());
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    for (mod_name, missing) in &missing_by_module {
        eprintln!(
            "MODULE {} HAS {} MISSING CONSTANT REFS:",
            mod_name,
            missing.len()
        );
        for (decl, needed) in missing.iter().take(10) {
            eprintln!(
                "  decl {} needs {}",
                decl.to_display_string(),
                needed.to_display_string()
            );
        }
    }
    assert!(
        missing_by_module.is_empty(),
        "No modules in the candidate set should have missing constant references!"
    );

    eprintln!(
        "ALL 13 MODULES HAVE CLOSED IMPORTS AND ZERO MISSING CONSTANTS! Total declarations: {}",
        total_consts
    );
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init companion chains"]
fn scan_downstream_candidates() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let base_modules = [
        "Init.Prelude",
        "Init.Coe",
        "Init.Notation",
        "Init.Tactics",
        "Init.SizeOf",
        "Init.Core",
        "Init.BinderNameHint",
        "Init.Control.MonadAttach",
        "Init.Control.Basic",
        "Init.Control.Id",
        "Init.Control.Except",
        "Init.Control.Reader",
        "Init.Control.State",
        "Init.Control.Lawful.MonadLift.Basic",
        "Init.Data.PLift",
        "Init.Data.ULift",
        "Init.Data.Zero",
        "Init.Data.Cast",
        "Init.Data.Option.Coe",
        "Init.Data.LawfulHashable",
        "Init.Data.Array.Set",
        "Init.Data.Slice.Basic",
        "Init.Data.Order.Classes",
        "Init.Dynamic",
        "Init.Try",
    ];
    let mut known: std::collections::BTreeSet<fln_core::name::Name> = std::collections::BTreeSet::new();
    for name in &base_modules {
        known.insert(fln_core::name::Name::from_components(name.split('.')));
    }

    let init_dir = lib.join("Init");
    let mut olean_files = Vec::new();
    fn visit_dir(dir: &Path, files: &mut Vec<PathBuf>) {
        if let Ok(entries) = std::fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    visit_dir(&path, files);
                } else if path.extension().and_then(|s| s.to_str()) == Some("olean") {
                    files.push(path);
                }
            }
        }
    }
    visit_dir(&init_dir, &mut olean_files);
    olean_files.sort();

    let limits = OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));

    let mut immediate_candidates = Vec::new();
    for path in &olean_files {
        let rel = path.strip_prefix(&lib).unwrap().with_extension("");
        let components: Vec<&str> = rel.iter().map(|s| s.to_str().unwrap()).collect();
        let fln_name = fln_core::name::Name::from_components(components);
        if known.contains(&fln_name) {
            continue;
        }

        let exported = match std::fs::read(path) {
            Ok(bytes) => bytes,
            Err(_) => continue,
        };
        let server = std::fs::read(path.with_extension("olean.server")).unwrap_or_default();
        let private = std::fs::read(path.with_extension("olean.private")).unwrap_or_default();
        if let Ok(decoded) = fln::decode_olean_module_artifacts(&exported, &server, &private, limits.decode) {
            let mut all_imports_satisfied = true;
            let mut missing_imports = Vec::new();
            for imp in &decoded.module.imports {
                if !known.contains(&imp.module) {
                    all_imports_satisfied = false;
                    missing_imports.push(imp.module.to_display_string());
                }
            }
            if all_imports_satisfied {
                immediate_candidates.push((fln_name.to_display_string(), decoded.constants.len()));
            } else {
                eprintln!(
                    "Unsatisfied: {} (needs: {:?})",
                    fln_name.to_display_string(),
                    missing_imports
                );
            }
        }
    }

    eprintln!("\n=== IMMEDIATE CANDIDATE MODULES (ALL IMPORTS SATISFIED BY CURRENT 25) ===");
    for (cand, count) in &immediate_candidates {
        eprintln!("  Candidate: {} ({} declarations)", cand, count);
    }
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init companion chains"]
fn preflight_candidate_25_modules() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let load = |name: &str| {
        let base = lib.join(format!("{name}.olean"));
        let exported = std::fs::read(&base).expect("read exported");
        let server = std::fs::read(base.with_extension("olean.server")).expect("read server");
        let private = std::fs::read(base.with_extension("olean.private")).expect("read private");
        let limits =
            OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
        fln::decode_olean_module_artifacts(&exported, &server, &private, limits.decode)
            .expect("decode")
    };

    let base_modules = [
        "Init/Prelude",
        "Init/Coe",
        "Init/Notation",
        "Init/Tactics",
        "Init/SizeOf",
        "Init/Core",
        "Init/BinderNameHint",
        "Init/Control/MonadAttach",
        "Init/Control/Basic",
        "Init/Control/Id",
        "Init/Control/Except",
        "Init/Control/Reader",
        "Init/Control/State",
    ];

    let candidate_modules = [
        "Init/Control/Lawful/MonadLift/Basic",
        "Init/Data/PLift",
        "Init/Data/ULift",
        "Init/Data/Zero",
        "Init/Data/Cast",
        "Init/Data/Option/Coe",
        "Init/Data/LawfulHashable",
        "Init/Data/Array/Set",
        "Init/Data/Slice/Basic",
        "Init/Data/Order/Classes",
        "Init/Dynamic",
        "Init/Try",
    ];

    let mut set_of_all = std::collections::BTreeSet::new();
    for name in base_modules.iter().chain(candidate_modules.iter()) {
        let fln_name = fln_core::name::Name::from_components(name.split('/'));
        set_of_all.insert(fln_name);
    }

    let mut available_consts = std::collections::BTreeSet::new();
    let mut total_decls = 0;
    for name in &base_modules {
        let m = load(name);
        total_decls += m.constants.len();
        for c in &m.constants {
            available_consts.insert(c.name().clone());
        }
    }

    for name in &candidate_modules {
        let m = load(name);
        total_decls += m.constants.len();
        eprintln!("Checking candidate {}: {} declarations", name, m.constants.len());
        for imp in &m.module.imports {
            eprintln!("  imports: {}", imp.module.to_display_string());
            assert!(
                set_of_all.contains(&imp.module),
                "Candidate {} imports {} which is not available!",
                name,
                imp.module.to_display_string()
            );
        }
        for c in &m.constants {
            available_consts.insert(c.name().clone());
        }
    }

    let mut missing_by_module: std::collections::BTreeMap<&str, std::collections::BTreeSet<(fln_core::name::Name, fln_core::name::Name)>> =
        std::collections::BTreeMap::new();
    for name in &candidate_modules {
        let m = load(name);
        for c in &m.constants {
            let mut exprs = vec![c.constant_val().type_.clone()];
            match c {
                ConstantInfo::Thm(t) => exprs.push(t.value.clone()),
                ConstantInfo::Defn(d) => exprs.push(d.value.clone()),
                ConstantInfo::Ctor(ctor) => exprs.push(ctor.base.type_.clone()),
                _ => {}
            }
            for e in exprs {
                let mut stack = vec![e];
                while let Some(cur) = stack.pop() {
                    match cur.node() {
                        fln_core::expr::ExprNode::Const { name: cname, .. } => {
                            if !available_consts.contains(cname) {
                                missing_by_module
                                    .entry(*name)
                                    .or_default()
                                    .insert((c.name().clone(), cname.clone()));
                            }
                        }
                        fln_core::expr::ExprNode::App { f, a } => {
                            stack.push(f.clone());
                            stack.push(a.clone());
                        }
                        fln_core::expr::ExprNode::Lam {
                            binder_type, body, ..
                        }
                        | fln_core::expr::ExprNode::ForallE {
                            binder_type, body, ..
                        } => {
                            stack.push(binder_type.clone());
                            stack.push(body.clone());
                        }
                        fln_core::expr::ExprNode::LetE {
                            type_, value, body, ..
                        } => {
                            stack.push(type_.clone());
                            stack.push(value.clone());
                            stack.push(body.clone());
                        }
                        fln_core::expr::ExprNode::Proj { expr, .. } => {
                            stack.push(expr.clone());
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    for (mod_name, missing) in &missing_by_module {
        eprintln!(
            "MODULE {} HAS {} MISSING CONSTANT REFS:",
            mod_name,
            missing.len()
        );
        for (decl, needed) in missing.iter().take(10) {
            eprintln!(
                "  decl {} needs {}",
                decl.to_display_string(),
                needed.to_display_string()
            );
        }
    }
    assert!(
        missing_by_module.is_empty(),
        "No candidates should have missing constant references!"
    );

    assert_eq!(total_decls, 4974);
    eprintln!(
        "ALL 25 MODULES ({total_decls} TOTAL DECLARATIONS) HAVE STRICTLY SATISFIED IMPORTS AND ZERO MISSING CONSTANTS!"
    );
}




#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init 5-module companion chain"]
fn pinned_init_prelude_coe_notation_tactics_sizeof_council_run() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let prelude_base = lib.join("Init/Prelude.olean");
    let prelude_exported = std::fs::read(&prelude_base).expect("read exported Prelude");
    let prelude_server =
        std::fs::read(prelude_base.with_extension("olean.server")).expect("read Prelude server");
    let prelude_private =
        std::fs::read(prelude_base.with_extension("olean.private")).expect("read Prelude private");

    let coe_base = lib.join("Init/Coe.olean");
    let coe_exported = std::fs::read(&coe_base).expect("read exported Coe");
    let coe_server =
        std::fs::read(coe_base.with_extension("olean.server")).expect("read Coe server");
    let coe_private =
        std::fs::read(coe_base.with_extension("olean.private")).expect("read Coe private");

    let notation_base = lib.join("Init/Notation.olean");
    let notation_exported = std::fs::read(&notation_base).expect("read exported Notation");
    let notation_server =
        std::fs::read(notation_base.with_extension("olean.server")).expect("read Notation server");
    let notation_private = std::fs::read(notation_base.with_extension("olean.private"))
        .expect("read Notation private");

    let tactics_base = lib.join("Init/Tactics.olean");
    let tactics_exported = std::fs::read(&tactics_base).expect("read exported Tactics");
    let tactics_server =
        std::fs::read(tactics_base.with_extension("olean.server")).expect("read Tactics server");
    let tactics_private =
        std::fs::read(tactics_base.with_extension("olean.private")).expect("read Tactics private");

    let sizeof_base = lib.join("Init/SizeOf.olean");
    let sizeof_exported = std::fs::read(&sizeof_base).expect("read exported SizeOf");
    let sizeof_server =
        std::fs::read(sizeof_base.with_extension("olean.server")).expect("read SizeOf server");
    let sizeof_private =
        std::fs::read(sizeof_base.with_extension("olean.private")).expect("read SizeOf private");

    let prelude_name = fln_core::name::Name::from_components(["Init", "Prelude"]);
    let coe_name = fln_core::name::Name::from_components(["Init", "Coe"]);
    let notation_name = fln_core::name::Name::from_components(["Init", "Notation"]);
    let tactics_name = fln_core::name::Name::from_components(["Init", "Tactics"]);
    let sizeof_name = fln_core::name::Name::from_components(["Init", "SizeOf"]);

    let modules = [
        fln::OleanModuleInput {
            name: &prelude_name,
            artifact: &prelude_exported,
            server_artifact: Some(&prelude_server),
            private_artifact: Some(&prelude_private),
        },
        fln::OleanModuleInput {
            name: &coe_name,
            artifact: &coe_exported,
            server_artifact: Some(&coe_server),
            private_artifact: Some(&coe_private),
        },
        fln::OleanModuleInput {
            name: &notation_name,
            artifact: &notation_exported,
            server_artifact: Some(&notation_server),
            private_artifact: Some(&notation_private),
        },
        fln::OleanModuleInput {
            name: &tactics_name,
            artifact: &tactics_exported,
            server_artifact: Some(&tactics_server),
            private_artifact: Some(&tactics_private),
        },
        fln::OleanModuleInput {
            name: &sizeof_name,
            artifact: &sizeof_exported,
            server_artifact: Some(&sizeof_server),
            private_artifact: Some(&sizeof_private),
        },
    ];

    let engine = Engine::from_environment(Environment::new());
    let limits = OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
    let result = engine.check_olean_modules(&modules, &KVMap::new(), limits);
    match result {
        Ok(Outcome::Complete(checked)) => {
            eprintln!("COMPLETE: checked {} modules!", checked.modules.len());
            for m in &checked.modules {
                eprintln!(
                    "  module {}: {} declarations",
                    m.name.to_display_string(),
                    m.declarations.len()
                );
            }
            assert_eq!(checked.modules.len(), 5);
            assert_eq!(checked.modules[0].declarations.len(), 2314);
            assert_eq!(checked.modules[1].declarations.len(), 158);
            assert_eq!(checked.modules[2].declarations.len(), 284);
            assert_eq!(checked.modules[3].declarations.len(), 360);
            assert_eq!(checked.modules[4].declarations.len(), 174);
        }
        Ok(Outcome::Inconclusive(reason)) => {
            panic!("INCONCLUSIVE: {reason:?}");
        }
        Ok(Outcome::InternalFault(fault)) => {
            panic!("INTERNAL_FAULT: {fault:?}");
        }
        Err(error) => {
            panic!("FRONTIER: {error}");
        }
    }
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init 6-module companion chain"]
fn pinned_init_prelude_coe_notation_tactics_sizeof_core_council_run() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let prelude_base = lib.join("Init/Prelude.olean");
    let prelude_exported = std::fs::read(&prelude_base).expect("read exported Prelude");
    let prelude_server =
        std::fs::read(prelude_base.with_extension("olean.server")).expect("read Prelude server");
    let prelude_private =
        std::fs::read(prelude_base.with_extension("olean.private")).expect("read Prelude private");

    let coe_base = lib.join("Init/Coe.olean");
    let coe_exported = std::fs::read(&coe_base).expect("read exported Coe");
    let coe_server =
        std::fs::read(coe_base.with_extension("olean.server")).expect("read Coe server");
    let coe_private =
        std::fs::read(coe_base.with_extension("olean.private")).expect("read Coe private");

    let notation_base = lib.join("Init/Notation.olean");
    let notation_exported = std::fs::read(&notation_base).expect("read exported Notation");
    let notation_server =
        std::fs::read(notation_base.with_extension("olean.server")).expect("read Notation server");
    let notation_private = std::fs::read(notation_base.with_extension("olean.private"))
        .expect("read Notation private");

    let tactics_base = lib.join("Init/Tactics.olean");
    let tactics_exported = std::fs::read(&tactics_base).expect("read exported Tactics");
    let tactics_server =
        std::fs::read(tactics_base.with_extension("olean.server")).expect("read Tactics server");
    let tactics_private =
        std::fs::read(tactics_base.with_extension("olean.private")).expect("read Tactics private");

    let sizeof_base = lib.join("Init/SizeOf.olean");
    let sizeof_exported = std::fs::read(&sizeof_base).expect("read exported SizeOf");
    let sizeof_server =
        std::fs::read(sizeof_base.with_extension("olean.server")).expect("read SizeOf server");
    let sizeof_private =
        std::fs::read(sizeof_base.with_extension("olean.private")).expect("read SizeOf private");

    let core_base = lib.join("Init/Core.olean");
    let core_exported = std::fs::read(&core_base).expect("read exported Core");
    let core_server =
        std::fs::read(core_base.with_extension("olean.server")).expect("read Core server");
    let core_private =
        std::fs::read(core_base.with_extension("olean.private")).expect("read Core private");

    let prelude_name = fln_core::name::Name::from_components(["Init", "Prelude"]);
    let coe_name = fln_core::name::Name::from_components(["Init", "Coe"]);
    let notation_name = fln_core::name::Name::from_components(["Init", "Notation"]);
    let tactics_name = fln_core::name::Name::from_components(["Init", "Tactics"]);
    let sizeof_name = fln_core::name::Name::from_components(["Init", "SizeOf"]);
    let core_name = fln_core::name::Name::from_components(["Init", "Core"]);

    let modules = [
        fln::OleanModuleInput {
            name: &prelude_name,
            artifact: &prelude_exported,
            server_artifact: Some(&prelude_server),
            private_artifact: Some(&prelude_private),
        },
        fln::OleanModuleInput {
            name: &coe_name,
            artifact: &coe_exported,
            server_artifact: Some(&coe_server),
            private_artifact: Some(&coe_private),
        },
        fln::OleanModuleInput {
            name: &notation_name,
            artifact: &notation_exported,
            server_artifact: Some(&notation_server),
            private_artifact: Some(&notation_private),
        },
        fln::OleanModuleInput {
            name: &tactics_name,
            artifact: &tactics_exported,
            server_artifact: Some(&tactics_server),
            private_artifact: Some(&tactics_private),
        },
        fln::OleanModuleInput {
            name: &sizeof_name,
            artifact: &sizeof_exported,
            server_artifact: Some(&sizeof_server),
            private_artifact: Some(&sizeof_private),
        },
        fln::OleanModuleInput {
            name: &core_name,
            artifact: &core_exported,
            server_artifact: Some(&core_server),
            private_artifact: Some(&core_private),
        },
    ];

    let engine = Engine::from_environment(Environment::new());
    let limits = OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
    let result = engine.check_olean_modules(&modules, &KVMap::new(), limits);
    match result {
        Ok(Outcome::Complete(checked)) => {
            eprintln!("COMPLETE: checked {} modules!", checked.modules.len());
            for m in &checked.modules {
                eprintln!(
                    "  module {}: {} declarations",
                    m.name.to_display_string(),
                    m.declarations.len()
                );
            }
            assert_eq!(checked.modules.len(), 6);
            assert_eq!(checked.modules[0].declarations.len(), 2314);
            assert_eq!(checked.modules[1].declarations.len(), 158);
            assert_eq!(checked.modules[2].declarations.len(), 284);
            assert_eq!(checked.modules[3].declarations.len(), 360);
            assert_eq!(checked.modules[4].declarations.len(), 174);
            assert_eq!(checked.modules[5].declarations.len(), 1152);
        }
        Ok(Outcome::Inconclusive(reason)) => {
            panic!("INCONCLUSIVE: {reason:?}");
        }
        Ok(Outcome::InternalFault(fault)) => {
            panic!("INTERNAL_FAULT: {fault:?}");
        }
        Err(error) => {
            panic!("FRONTIER: {error}");
        }
    }
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init 5-module subchain"]
fn pinned_init_prelude_coe_notation_tactics_bindernamehint_council_run() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let prelude_base = lib.join("Init/Prelude.olean");
    let prelude_exported = std::fs::read(&prelude_base).expect("read exported Prelude");
    let prelude_server =
        std::fs::read(prelude_base.with_extension("olean.server")).expect("read Prelude server");
    let prelude_private =
        std::fs::read(prelude_base.with_extension("olean.private")).expect("read Prelude private");

    let coe_base = lib.join("Init/Coe.olean");
    let coe_exported = std::fs::read(&coe_base).expect("read exported Coe");
    let coe_server =
        std::fs::read(coe_base.with_extension("olean.server")).expect("read Coe server");
    let coe_private =
        std::fs::read(coe_base.with_extension("olean.private")).expect("read Coe private");

    let notation_base = lib.join("Init/Notation.olean");
    let notation_exported = std::fs::read(&notation_base).expect("read exported Notation");
    let notation_server =
        std::fs::read(notation_base.with_extension("olean.server")).expect("read Notation server");
    let notation_private = std::fs::read(notation_base.with_extension("olean.private"))
        .expect("read Notation private");

    let tactics_base = lib.join("Init/Tactics.olean");
    let tactics_exported = std::fs::read(&tactics_base).expect("read exported Tactics");
    let tactics_server =
        std::fs::read(tactics_base.with_extension("olean.server")).expect("read Tactics server");
    let tactics_private =
        std::fs::read(tactics_base.with_extension("olean.private")).expect("read Tactics private");

    let bnh_base = lib.join("Init/BinderNameHint.olean");
    let bnh_exported = std::fs::read(&bnh_base).expect("read exported BinderNameHint");
    let bnh_server =
        std::fs::read(bnh_base.with_extension("olean.server")).expect("read BinderNameHint server");
    let bnh_private =
        std::fs::read(bnh_base.with_extension("olean.private")).expect("read BinderNameHint private");

    let prelude_name = fln_core::name::Name::from_components(["Init", "Prelude"]);
    let coe_name = fln_core::name::Name::from_components(["Init", "Coe"]);
    let notation_name = fln_core::name::Name::from_components(["Init", "Notation"]);
    let tactics_name = fln_core::name::Name::from_components(["Init", "Tactics"]);
    let bnh_name = fln_core::name::Name::from_components(["Init", "BinderNameHint"]);

    let modules = [
        fln::OleanModuleInput {
            name: &prelude_name,
            artifact: &prelude_exported,
            server_artifact: Some(&prelude_server),
            private_artifact: Some(&prelude_private),
        },
        fln::OleanModuleInput {
            name: &coe_name,
            artifact: &coe_exported,
            server_artifact: Some(&coe_server),
            private_artifact: Some(&coe_private),
        },
        fln::OleanModuleInput {
            name: &notation_name,
            artifact: &notation_exported,
            server_artifact: Some(&notation_server),
            private_artifact: Some(&notation_private),
        },
        fln::OleanModuleInput {
            name: &tactics_name,
            artifact: &tactics_exported,
            server_artifact: Some(&tactics_server),
            private_artifact: Some(&tactics_private),
        },
        fln::OleanModuleInput {
            name: &bnh_name,
            artifact: &bnh_exported,
            server_artifact: Some(&bnh_server),
            private_artifact: Some(&bnh_private),
        },
    ];

    let engine = Engine::from_environment(Environment::new());
    let limits = OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
    let result = engine.check_olean_modules(&modules, &KVMap::new(), limits);
    match result {
        Ok(Outcome::Complete(checked)) => {
            eprintln!("COMPLETE: checked {} modules!", checked.modules.len());
            for m in &checked.modules {
                eprintln!(
                    "  module {}: {} declarations",
                    m.name.to_display_string(),
                    m.declarations.len()
                );
            }
            assert_eq!(checked.modules.len(), 5);
            assert_eq!(checked.modules[0].declarations.len(), 2314);
            assert_eq!(checked.modules[1].declarations.len(), 158);
            assert_eq!(checked.modules[2].declarations.len(), 284);
            assert_eq!(checked.modules[3].declarations.len(), 360);
            assert_eq!(checked.modules[4].declarations.len(), 2);
        }
        Ok(Outcome::Inconclusive(reason)) => {
            panic!("INCONCLUSIVE: {reason:?}");
        }
        Ok(Outcome::InternalFault(fault)) => {
            panic!("INTERNAL_FAULT: {fault:?}");
        }
        Err(error) => {
            panic!("FRONTIER: {error}");
        }
    }
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init 7-module companion chain"]
fn pinned_init_prelude_coe_notation_tactics_sizeof_core_bindernamehint_council_run() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let prelude_base = lib.join("Init/Prelude.olean");
    let prelude_exported = std::fs::read(&prelude_base).expect("read exported Prelude");
    let prelude_server =
        std::fs::read(prelude_base.with_extension("olean.server")).expect("read Prelude server");
    let prelude_private =
        std::fs::read(prelude_base.with_extension("olean.private")).expect("read Prelude private");

    let coe_base = lib.join("Init/Coe.olean");
    let coe_exported = std::fs::read(&coe_base).expect("read exported Coe");
    let coe_server =
        std::fs::read(coe_base.with_extension("olean.server")).expect("read Coe server");
    let coe_private =
        std::fs::read(coe_base.with_extension("olean.private")).expect("read Coe private");

    let notation_base = lib.join("Init/Notation.olean");
    let notation_exported = std::fs::read(&notation_base).expect("read exported Notation");
    let notation_server =
        std::fs::read(notation_base.with_extension("olean.server")).expect("read Notation server");
    let notation_private = std::fs::read(notation_base.with_extension("olean.private"))
        .expect("read Notation private");

    let tactics_base = lib.join("Init/Tactics.olean");
    let tactics_exported = std::fs::read(&tactics_base).expect("read exported Tactics");
    let tactics_server =
        std::fs::read(tactics_base.with_extension("olean.server")).expect("read Tactics server");
    let tactics_private =
        std::fs::read(tactics_base.with_extension("olean.private")).expect("read Tactics private");

    let sizeof_base = lib.join("Init/SizeOf.olean");
    let sizeof_exported = std::fs::read(&sizeof_base).expect("read exported SizeOf");
    let sizeof_server =
        std::fs::read(sizeof_base.with_extension("olean.server")).expect("read SizeOf server");
    let sizeof_private =
        std::fs::read(sizeof_base.with_extension("olean.private")).expect("read SizeOf private");

    let core_base = lib.join("Init/Core.olean");
    let core_exported = std::fs::read(&core_base).expect("read exported Core");
    let core_server =
        std::fs::read(core_base.with_extension("olean.server")).expect("read Core server");
    let core_private =
        std::fs::read(core_base.with_extension("olean.private")).expect("read Core private");

    let bnh_base = lib.join("Init/BinderNameHint.olean");
    let bnh_exported = std::fs::read(&bnh_base).expect("read exported BinderNameHint");
    let bnh_server =
        std::fs::read(bnh_base.with_extension("olean.server")).expect("read BinderNameHint server");
    let bnh_private =
        std::fs::read(bnh_base.with_extension("olean.private")).expect("read BinderNameHint private");

    let prelude_name = fln_core::name::Name::from_components(["Init", "Prelude"]);
    let coe_name = fln_core::name::Name::from_components(["Init", "Coe"]);
    let notation_name = fln_core::name::Name::from_components(["Init", "Notation"]);
    let tactics_name = fln_core::name::Name::from_components(["Init", "Tactics"]);
    let sizeof_name = fln_core::name::Name::from_components(["Init", "SizeOf"]);
    let core_name = fln_core::name::Name::from_components(["Init", "Core"]);
    let bnh_name = fln_core::name::Name::from_components(["Init", "BinderNameHint"]);

    let modules = [
        fln::OleanModuleInput {
            name: &prelude_name,
            artifact: &prelude_exported,
            server_artifact: Some(&prelude_server),
            private_artifact: Some(&prelude_private),
        },
        fln::OleanModuleInput {
            name: &coe_name,
            artifact: &coe_exported,
            server_artifact: Some(&coe_server),
            private_artifact: Some(&coe_private),
        },
        fln::OleanModuleInput {
            name: &notation_name,
            artifact: &notation_exported,
            server_artifact: Some(&notation_server),
            private_artifact: Some(&notation_private),
        },
        fln::OleanModuleInput {
            name: &tactics_name,
            artifact: &tactics_exported,
            server_artifact: Some(&tactics_server),
            private_artifact: Some(&tactics_private),
        },
        fln::OleanModuleInput {
            name: &sizeof_name,
            artifact: &sizeof_exported,
            server_artifact: Some(&sizeof_server),
            private_artifact: Some(&sizeof_private),
        },
        fln::OleanModuleInput {
            name: &core_name,
            artifact: &core_exported,
            server_artifact: Some(&core_server),
            private_artifact: Some(&core_private),
        },
        fln::OleanModuleInput {
            name: &bnh_name,
            artifact: &bnh_exported,
            server_artifact: Some(&bnh_server),
            private_artifact: Some(&bnh_private),
        },
    ];

    let engine = Engine::from_environment(Environment::new());
    let limits = OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
    let result = engine.check_olean_modules(&modules, &KVMap::new(), limits);
    match result {
        Ok(Outcome::Complete(checked)) => {
            eprintln!("COMPLETE: checked {} modules!", checked.modules.len());
            for m in &checked.modules {
                eprintln!(
                    "  module {}: {} declarations",
                    m.name.to_display_string(),
                    m.declarations.len()
                );
            }
            assert_eq!(checked.modules.len(), 7);
            assert_eq!(checked.modules[0].declarations.len(), 2314);
            assert_eq!(checked.modules[1].declarations.len(), 158);
            assert_eq!(checked.modules[2].declarations.len(), 284);
            assert_eq!(checked.modules[3].declarations.len(), 360);
            assert_eq!(checked.modules[4].declarations.len(), 174);
            assert_eq!(checked.modules[5].declarations.len(), 1152);
            assert_eq!(checked.modules[6].declarations.len(), 2);
        }
        Ok(Outcome::Inconclusive(reason)) => {
            panic!("INCONCLUSIVE: {reason:?}");
        }
        Ok(Outcome::InternalFault(fault)) => {
            panic!("INTERNAL_FAULT: {fault:?}");
        }
        Err(error) => {
            panic!("FRONTIER: {error}");
        }
    }
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init 13-module companion chain"]
fn pinned_init_control_companion_chain_council_run() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let load_module = |rel_path: &str| {
        let base = lib.join(format!("{rel_path}.olean"));
        let exported = std::fs::read(&base).expect("read exported");
        let server = std::fs::read(base.with_extension("olean.server")).expect("read server");
        let private = std::fs::read(base.with_extension("olean.private")).expect("read private");
        (exported, server, private)
    };

    let (prelude_exp, prelude_srv, prelude_prv) = load_module("Init/Prelude");
    let (coe_exp, coe_srv, coe_prv) = load_module("Init/Coe");
    let (not_exp, not_srv, not_prv) = load_module("Init/Notation");
    let (tac_exp, tac_srv, tac_prv) = load_module("Init/Tactics");
    let (sz_exp, sz_srv, sz_prv) = load_module("Init/SizeOf");
    let (core_exp, core_srv, core_prv) = load_module("Init/Core");
    let (bnh_exp, bnh_srv, bnh_prv) = load_module("Init/BinderNameHint");
    let (ma_exp, ma_srv, ma_prv) = load_module("Init/Control/MonadAttach");
    let (bas_exp, bas_srv, bas_prv) = load_module("Init/Control/Basic");
    let (id_exp, id_srv, id_prv) = load_module("Init/Control/Id");
    let (exc_exp, exc_srv, exc_prv) = load_module("Init/Control/Except");
    let (rdr_exp, rdr_srv, rdr_prv) = load_module("Init/Control/Reader");
    let (st_exp, st_srv, st_prv) = load_module("Init/Control/State");

    let prelude_name = fln_core::name::Name::from_components(["Init", "Prelude"]);
    let coe_name = fln_core::name::Name::from_components(["Init", "Coe"]);
    let not_name = fln_core::name::Name::from_components(["Init", "Notation"]);
    let tac_name = fln_core::name::Name::from_components(["Init", "Tactics"]);
    let sz_name = fln_core::name::Name::from_components(["Init", "SizeOf"]);
    let core_name = fln_core::name::Name::from_components(["Init", "Core"]);
    let bnh_name = fln_core::name::Name::from_components(["Init", "BinderNameHint"]);
    let ma_name = fln_core::name::Name::from_components(["Init", "Control", "MonadAttach"]);
    let bas_name = fln_core::name::Name::from_components(["Init", "Control", "Basic"]);
    let id_name = fln_core::name::Name::from_components(["Init", "Control", "Id"]);
    let exc_name = fln_core::name::Name::from_components(["Init", "Control", "Except"]);
    let rdr_name = fln_core::name::Name::from_components(["Init", "Control", "Reader"]);
    let st_name = fln_core::name::Name::from_components(["Init", "Control", "State"]);

    let modules = [
        fln::OleanModuleInput {
            name: &prelude_name,
            artifact: &prelude_exp,
            server_artifact: Some(&prelude_srv),
            private_artifact: Some(&prelude_prv),
        },
        fln::OleanModuleInput {
            name: &coe_name,
            artifact: &coe_exp,
            server_artifact: Some(&coe_srv),
            private_artifact: Some(&coe_prv),
        },
        fln::OleanModuleInput {
            name: &not_name,
            artifact: &not_exp,
            server_artifact: Some(&not_srv),
            private_artifact: Some(&not_prv),
        },
        fln::OleanModuleInput {
            name: &tac_name,
            artifact: &tac_exp,
            server_artifact: Some(&tac_srv),
            private_artifact: Some(&tac_prv),
        },
        fln::OleanModuleInput {
            name: &sz_name,
            artifact: &sz_exp,
            server_artifact: Some(&sz_srv),
            private_artifact: Some(&sz_prv),
        },
        fln::OleanModuleInput {
            name: &core_name,
            artifact: &core_exp,
            server_artifact: Some(&core_srv),
            private_artifact: Some(&core_prv),
        },
        fln::OleanModuleInput {
            name: &bnh_name,
            artifact: &bnh_exp,
            server_artifact: Some(&bnh_srv),
            private_artifact: Some(&bnh_prv),
        },
        fln::OleanModuleInput {
            name: &ma_name,
            artifact: &ma_exp,
            server_artifact: Some(&ma_srv),
            private_artifact: Some(&ma_prv),
        },
        fln::OleanModuleInput {
            name: &bas_name,
            artifact: &bas_exp,
            server_artifact: Some(&bas_srv),
            private_artifact: Some(&bas_prv),
        },
        fln::OleanModuleInput {
            name: &id_name,
            artifact: &id_exp,
            server_artifact: Some(&id_srv),
            private_artifact: Some(&id_prv),
        },
        fln::OleanModuleInput {
            name: &exc_name,
            artifact: &exc_exp,
            server_artifact: Some(&exc_srv),
            private_artifact: Some(&exc_prv),
        },
        fln::OleanModuleInput {
            name: &rdr_name,
            artifact: &rdr_exp,
            server_artifact: Some(&rdr_srv),
            private_artifact: Some(&rdr_prv),
        },
        fln::OleanModuleInput {
            name: &st_name,
            artifact: &st_exp,
            server_artifact: Some(&st_srv),
            private_artifact: Some(&st_prv),
        },
    ];

    let engine = Engine::from_environment(Environment::new());
    let limits = OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
    let result = engine.check_olean_modules(&modules, &KVMap::new(), limits);
    match result {
        Ok(Outcome::Complete(checked)) => {
            eprintln!("COMPLETE: checked {} modules!", checked.modules.len());
            for m in &checked.modules {
                eprintln!(
                    "  module {}: {} declarations",
                    m.name.to_display_string(),
                    m.declarations.len()
                );
            }
            assert_eq!(checked.modules.len(), 13);
            assert_eq!(checked.modules[0].declarations.len(), 2314);
            assert_eq!(checked.modules[1].declarations.len(), 158);
            assert_eq!(checked.modules[2].declarations.len(), 284);
            assert_eq!(checked.modules[3].declarations.len(), 360);
            assert_eq!(checked.modules[4].declarations.len(), 174);
            assert_eq!(checked.modules[5].declarations.len(), 1152);
            assert_eq!(checked.modules[6].declarations.len(), 2);
            assert_eq!(checked.modules[7].declarations.len(), 30);
            assert_eq!(checked.modules[8].declarations.len(), 108);
            assert_eq!(checked.modules[9].declarations.len(), 12);
            assert_eq!(checked.modules[10].declarations.len(), 62);
            assert_eq!(checked.modules[11].declarations.len(), 9);
            assert_eq!(checked.modules[12].declarations.len(), 33);
        }
        Ok(Outcome::Inconclusive(reason)) => {
            panic!("INCONCLUSIVE: {reason:?}");
        }
        Ok(Outcome::InternalFault(fault)) => {
            panic!("INTERNAL_FAULT: {fault:?}");
        }
        Err(error) => {
            panic!("FRONTIER: {error}");
        }
    }
}

#[test]
#[ignore = "requires the pinned Lean v4.32.0 Init 25-module companion chain"]
fn pinned_extended_25_module_companion_chain_council_run() {
    let lib = reference_lib().expect("pinned Reference library is unavailable");

    let load_module = |rel_path: &str| {
        let base = lib.join(format!("{rel_path}.olean"));
        let exported = std::fs::read(&base).expect("read exported");
        let server = std::fs::read(base.with_extension("olean.server")).expect("read server");
        let private = std::fs::read(base.with_extension("olean.private")).expect("read private");
        (exported, server, private)
    };

    let (prelude_exp, prelude_srv, prelude_prv) = load_module("Init/Prelude");
    let (coe_exp, coe_srv, coe_prv) = load_module("Init/Coe");
    let (not_exp, not_srv, not_prv) = load_module("Init/Notation");
    let (tac_exp, tac_srv, tac_prv) = load_module("Init/Tactics");
    let (sz_exp, sz_srv, sz_prv) = load_module("Init/SizeOf");
    let (core_exp, core_srv, core_prv) = load_module("Init/Core");
    let (bnh_exp, bnh_srv, bnh_prv) = load_module("Init/BinderNameHint");
    let (ma_exp, ma_srv, ma_prv) = load_module("Init/Control/MonadAttach");
    let (bas_exp, bas_srv, bas_prv) = load_module("Init/Control/Basic");
    let (id_exp, id_srv, id_prv) = load_module("Init/Control/Id");
    let (exc_exp, exc_srv, exc_prv) = load_module("Init/Control/Except");
    let (rdr_exp, rdr_srv, rdr_prv) = load_module("Init/Control/Reader");
    let (st_exp, st_srv, st_prv) = load_module("Init/Control/State");
    let (mlb_exp, mlb_srv, mlb_prv) = load_module("Init/Control/Lawful/MonadLift/Basic");
    let (plift_exp, plift_srv, plift_prv) = load_module("Init/Data/PLift");
    let (ulift_exp, ulift_srv, ulift_prv) = load_module("Init/Data/ULift");
    let (zero_exp, zero_srv, zero_prv) = load_module("Init/Data/Zero");
    let (cast_exp, cast_srv, cast_prv) = load_module("Init/Data/Cast");
    let (optcoe_exp, optcoe_srv, optcoe_prv) = load_module("Init/Data/Option/Coe");
    let (lh_exp, lh_srv, lh_prv) = load_module("Init/Data/LawfulHashable");
    let (arrset_exp, arrset_srv, arrset_prv) = load_module("Init/Data/Array/Set");
    let (slice_exp, slice_srv, slice_prv) = load_module("Init/Data/Slice/Basic");
    let (ord_exp, ord_srv, ord_prv) = load_module("Init/Data/Order/Classes");
    let (dyn_exp, dyn_srv, dyn_prv) = load_module("Init/Dynamic");
    let (try_exp, try_srv, try_prv) = load_module("Init/Try");

    let prelude_name = fln_core::name::Name::from_components(["Init", "Prelude"]);
    let coe_name = fln_core::name::Name::from_components(["Init", "Coe"]);
    let not_name = fln_core::name::Name::from_components(["Init", "Notation"]);
    let tac_name = fln_core::name::Name::from_components(["Init", "Tactics"]);
    let sz_name = fln_core::name::Name::from_components(["Init", "SizeOf"]);
    let core_name = fln_core::name::Name::from_components(["Init", "Core"]);
    let bnh_name = fln_core::name::Name::from_components(["Init", "BinderNameHint"]);
    let ma_name = fln_core::name::Name::from_components(["Init", "Control", "MonadAttach"]);
    let bas_name = fln_core::name::Name::from_components(["Init", "Control", "Basic"]);
    let id_name = fln_core::name::Name::from_components(["Init", "Control", "Id"]);
    let exc_name = fln_core::name::Name::from_components(["Init", "Control", "Except"]);
    let rdr_name = fln_core::name::Name::from_components(["Init", "Control", "Reader"]);
    let st_name = fln_core::name::Name::from_components(["Init", "Control", "State"]);
    let mlb_name = fln_core::name::Name::from_components(["Init", "Control", "Lawful", "MonadLift", "Basic"]);
    let plift_name = fln_core::name::Name::from_components(["Init", "Data", "PLift"]);
    let ulift_name = fln_core::name::Name::from_components(["Init", "Data", "ULift"]);
    let zero_name = fln_core::name::Name::from_components(["Init", "Data", "Zero"]);
    let cast_name = fln_core::name::Name::from_components(["Init", "Data", "Cast"]);
    let optcoe_name = fln_core::name::Name::from_components(["Init", "Data", "Option", "Coe"]);
    let lh_name = fln_core::name::Name::from_components(["Init", "Data", "LawfulHashable"]);
    let arrset_name = fln_core::name::Name::from_components(["Init", "Data", "Array", "Set"]);
    let slice_name = fln_core::name::Name::from_components(["Init", "Data", "Slice", "Basic"]);
    let ord_name = fln_core::name::Name::from_components(["Init", "Data", "Order", "Classes"]);
    let dyn_name = fln_core::name::Name::from_components(["Init", "Dynamic"]);
    let try_name = fln_core::name::Name::from_components(["Init", "Try"]);

    let modules = [
        fln::OleanModuleInput {
            name: &prelude_name,
            artifact: &prelude_exp,
            server_artifact: Some(&prelude_srv),
            private_artifact: Some(&prelude_prv),
        },
        fln::OleanModuleInput {
            name: &coe_name,
            artifact: &coe_exp,
            server_artifact: Some(&coe_srv),
            private_artifact: Some(&coe_prv),
        },
        fln::OleanModuleInput {
            name: &not_name,
            artifact: &not_exp,
            server_artifact: Some(&not_srv),
            private_artifact: Some(&not_prv),
        },
        fln::OleanModuleInput {
            name: &tac_name,
            artifact: &tac_exp,
            server_artifact: Some(&tac_srv),
            private_artifact: Some(&tac_prv),
        },
        fln::OleanModuleInput {
            name: &sz_name,
            artifact: &sz_exp,
            server_artifact: Some(&sz_srv),
            private_artifact: Some(&sz_prv),
        },
        fln::OleanModuleInput {
            name: &core_name,
            artifact: &core_exp,
            server_artifact: Some(&core_srv),
            private_artifact: Some(&core_prv),
        },
        fln::OleanModuleInput {
            name: &bnh_name,
            artifact: &bnh_exp,
            server_artifact: Some(&bnh_srv),
            private_artifact: Some(&bnh_prv),
        },
        fln::OleanModuleInput {
            name: &ma_name,
            artifact: &ma_exp,
            server_artifact: Some(&ma_srv),
            private_artifact: Some(&ma_prv),
        },
        fln::OleanModuleInput {
            name: &bas_name,
            artifact: &bas_exp,
            server_artifact: Some(&bas_srv),
            private_artifact: Some(&bas_prv),
        },
        fln::OleanModuleInput {
            name: &id_name,
            artifact: &id_exp,
            server_artifact: Some(&id_srv),
            private_artifact: Some(&id_prv),
        },
        fln::OleanModuleInput {
            name: &exc_name,
            artifact: &exc_exp,
            server_artifact: Some(&exc_srv),
            private_artifact: Some(&exc_prv),
        },
        fln::OleanModuleInput {
            name: &rdr_name,
            artifact: &rdr_exp,
            server_artifact: Some(&rdr_srv),
            private_artifact: Some(&rdr_prv),
        },
        fln::OleanModuleInput {
            name: &st_name,
            artifact: &st_exp,
            server_artifact: Some(&st_srv),
            private_artifact: Some(&st_prv),
        },
        fln::OleanModuleInput {
            name: &mlb_name,
            artifact: &mlb_exp,
            server_artifact: Some(&mlb_srv),
            private_artifact: Some(&mlb_prv),
        },
        fln::OleanModuleInput {
            name: &plift_name,
            artifact: &plift_exp,
            server_artifact: Some(&plift_srv),
            private_artifact: Some(&plift_prv),
        },
        fln::OleanModuleInput {
            name: &ulift_name,
            artifact: &ulift_exp,
            server_artifact: Some(&ulift_srv),
            private_artifact: Some(&ulift_prv),
        },
        fln::OleanModuleInput {
            name: &zero_name,
            artifact: &zero_exp,
            server_artifact: Some(&zero_srv),
            private_artifact: Some(&zero_prv),
        },
        fln::OleanModuleInput {
            name: &cast_name,
            artifact: &cast_exp,
            server_artifact: Some(&cast_srv),
            private_artifact: Some(&cast_prv),
        },
        fln::OleanModuleInput {
            name: &optcoe_name,
            artifact: &optcoe_exp,
            server_artifact: Some(&optcoe_srv),
            private_artifact: Some(&optcoe_prv),
        },
        fln::OleanModuleInput {
            name: &lh_name,
            artifact: &lh_exp,
            server_artifact: Some(&lh_srv),
            private_artifact: Some(&lh_prv),
        },
        fln::OleanModuleInput {
            name: &arrset_name,
            artifact: &arrset_exp,
            server_artifact: Some(&arrset_srv),
            private_artifact: Some(&arrset_prv),
        },
        fln::OleanModuleInput {
            name: &slice_name,
            artifact: &slice_exp,
            server_artifact: Some(&slice_srv),
            private_artifact: Some(&slice_prv),
        },
        fln::OleanModuleInput {
            name: &ord_name,
            artifact: &ord_exp,
            server_artifact: Some(&ord_srv),
            private_artifact: Some(&ord_prv),
        },
        fln::OleanModuleInput {
            name: &dyn_name,
            artifact: &dyn_exp,
            server_artifact: Some(&dyn_srv),
            private_artifact: Some(&dyn_prv),
        },
        fln::OleanModuleInput {
            name: &try_name,
            artifact: &try_exp,
            server_artifact: Some(&try_srv),
            private_artifact: Some(&try_prv),
        },
    ];

    let engine = Engine::from_environment(Environment::new());
    let limits = OleanCheckLimits::new(128 * 1024 * 1024, Budget::for_stack_bytes(4 * 1024 * 1024));
    let result = engine.check_olean_modules(&modules, &KVMap::new(), limits);
    match result {
        Ok(Outcome::Complete(checked)) => {
            eprintln!("COMPLETE: checked {} modules!", checked.modules.len());
            for m in &checked.modules {
                eprintln!(
                    "  module {}: {} declarations",
                    m.name.to_display_string(),
                    m.declarations.len()
                );
            }
            assert_eq!(checked.modules.len(), 25);
            assert_eq!(checked.modules[0].declarations.len(), 2314);
            assert_eq!(checked.modules[1].declarations.len(), 158);
            assert_eq!(checked.modules[2].declarations.len(), 284);
            assert_eq!(checked.modules[3].declarations.len(), 360);
            assert_eq!(checked.modules[4].declarations.len(), 174);
            assert_eq!(checked.modules[5].declarations.len(), 1152);
            assert_eq!(checked.modules[6].declarations.len(), 2);
            assert_eq!(checked.modules[7].declarations.len(), 30);
            assert_eq!(checked.modules[8].declarations.len(), 108);
            assert_eq!(checked.modules[9].declarations.len(), 12);
            assert_eq!(checked.modules[10].declarations.len(), 62);
            assert_eq!(checked.modules[11].declarations.len(), 9);
            assert_eq!(checked.modules[12].declarations.len(), 33);
            assert_eq!(checked.modules[13].declarations.len(), 16);
            assert_eq!(checked.modules[14].declarations.len(), 7);
            assert_eq!(checked.modules[15].declarations.len(), 7);
            assert_eq!(checked.modules[16].declarations.len(), 13);
            assert_eq!(checked.modules[17].declarations.len(), 15);
            assert_eq!(checked.modules[18].declarations.len(), 1);
            assert_eq!(checked.modules[19].declarations.len(), 9);
            assert_eq!(checked.modules[20].declarations.len(), 4);
            assert_eq!(checked.modules[21].declarations.len(), 24);
            assert_eq!(checked.modules[22].declarations.len(), 109);
            assert_eq!(checked.modules[23].declarations.len(), 28);
            assert_eq!(checked.modules[24].declarations.len(), 43);
        }
        Ok(Outcome::Inconclusive(reason)) => {
            panic!("INCONCLUSIVE: {reason:?}");
        }
        Ok(Outcome::InternalFault(fault)) => {
            panic!("INTERNAL_FAULT: {fault:?}");
        }
        Err(error) => {
            panic!("FRONTIER: {error}");
        }
    }
}






