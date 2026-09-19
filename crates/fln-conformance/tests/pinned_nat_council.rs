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
    let infos = DeclDecoder::new(&view, WalkBudget::default()).decode_module_constants().expect("decode");
    let owners: std::collections::BTreeMap<_, _> = infos
        .iter()
        .enumerate()
        .map(|(i, c)| (c.name().clone(), i))
        .collect();
    let mut needed = std::collections::BTreeSet::new();
    let mut queue = vec![fln_core::name::Name::from_components(target.iter().copied())];
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
                            fln_core::expr::ExprNode::Lam { binder_type, body, .. }
                            | fln_core::expr::ExprNode::ForallE { binder_type, body, .. } => {
                                stack.push(binder_type.clone());
                                stack.push(body.clone());
                            }
                            fln_core::expr::ExprNode::LetE { type_, value, body, .. } => {
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
                    if needed.contains(&ind.base.name) || ind.all.iter().any(|m| needed.contains(m)) {
                        for m in &ind.all {
                            if !needed.contains(m) { queue.push(m.clone()); }
                        }
                        for c in &ind.ctors {
                            if !needed.contains(c) { queue.push(c.clone()); }
                        }
                    }
                }
                ConstantInfo::Ctor(ctor) => {
                    if needed.contains(&ctor.induct) || needed.contains(&ctor.base.name) {
                        if !needed.contains(&ctor.induct) { queue.push(ctor.induct.clone()); }
                        if !needed.contains(&ctor.base.name) { queue.push(ctor.base.name.clone()); }
                    }
                }
                ConstantInfo::Rec(rec) => {
                    if rec.all.iter().any(|m| needed.contains(m)) || needed.contains(&rec.base.name) {
                        if !needed.contains(&rec.base.name) { queue.push(rec.base.name.clone()); }
                        for m in &rec.all {
                            if !needed.contains(m) { queue.push(m.clone()); }
                        }
                    }
                }
                ConstantInfo::Defn(defn) => {
                    if defn.all.iter().any(|m| needed.contains(m)) {
                        for m in &defn.all {
                            if !needed.contains(m) { queue.push(m.clone()); }
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
                            if !needed.contains(&q) { queue.push(q); }
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
    for c in &infos {
        if let ConstantInfo::Induct(ind) = c {
            if ind.num_nested != 0 {
                println!("NESTED INDUCTIVE: {:?}, num_nested={}", ind.base.name, ind.num_nested);
            }
        }
    }
    println!("Closed dependencies count for {target:?}: {}", needed.len());
    let subset: Vec<ConstantInfo> = infos
        .into_iter()
        .filter(|c| needed.contains(c.name()))
        .collect();

    let target_name = fln_core::name::Name::from_components(target.iter().copied());
    for c in &subset {
        let s = c.name().to_display_string();
        if s.starts_with("Lean.Syntax") {
            println!("DECL: {s} ({:?})", std::mem::discriminant(c));
            if let ConstantInfo::Induct(ind) = c {
                println!("  ctors: {:?}", ind.ctors);
                println!("  all: {:?}", ind.all);
                println!("  num_nested: {}", ind.num_nested);
            } else if let ConstantInfo::Rec(rec) = c {
                println!("  all: {:?}", rec.all);
                println!("  num_motives: {}, num_minors: {}", rec.num_motives, rec.num_minors);
                println!("  rules: {}", rec.rules.len());
                for (idx, r) in rec.rules.iter().enumerate() {
                    println!("    rule {idx}: ctor={:?}, nfields={}, rhs={:?}", r.ctor, r.nfields, r.rhs);
                }
            }
        }
    }

    let engine = Engine::from_environment(Environment::new());
    let limits = OleanCheckLimits::new(64 * 1024 * 1024, Budget::for_stack_bytes(2 * 1024 * 1024));
    let mut decoded = fln::decode_olean_module_artifacts(&exported, &server, &private, limits.decode)
        .expect("decode");
    decoded.constants = subset;
    engine.check_decoded_olean(decoded, &KVMap::new(), limits).expect("check_decoded_olean failed")
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

