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



