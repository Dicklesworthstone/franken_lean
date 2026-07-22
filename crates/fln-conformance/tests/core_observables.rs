//! The C0 core-observable fixture diff harness (bead franken_lean-p8a): every record
//! in `fixtures/core_observables.txt` — generated from the PINNED Reference binary by
//! `scripts/extract/gen_core_fixtures.sh` — is rebuilt natively with fln-core and every
//! observable is diffed. The corpus is closed on both ends: a fixture label this
//! harness cannot rebuild fails, and a case listed here that the fixture lacks fails.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;

use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::lean_hash::string_hash;
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::KVMap;

fn n(s: &str) -> Name {
    Name::str(Name::anonymous(), s)
}

fn string_case(label: &str) -> Option<String> {
    Some(match label {
        "empty" => String::new(),
        "a" => "a".into(),
        "ab" => "ab".into(),
        "abc" => "abc".into(),
        "abcd" => "abcd".into(),
        "abcde" => "abcde".into(),
        "abcdef" => "abcdef".into(),
        "abcdefg" => "abcdefg".into(),
        "abcdefgh" => "abcdefgh".into(),
        "abcdefghi" => "abcdefghi".into(),
        "unicode" => "héllo€ world".into(),
        "long" => "abcd".repeat(25),
        _ => return None,
    })
}

fn name_case(label: &str) -> Option<Name> {
    Some(match label {
        "anonymous" => Name::anonymous(),
        "Lean" => n("Lean"),
        "Lean.Meta" => Name::from_components(["Lean", "Meta"]),
        "Lean.Meta.run" => Name::from_components(["Lean", "Meta", "run"]),
        "uniq231" => Name::num(n("_uniq"), 231),
        "num0" => Name::num(Name::anonymous(), 0),
        "numMax" => Name::num(Name::anonymous(), u64::MAX),
        // 2^64 exceeds UInt64.size: the overflow constant 17 hashes it.
        "numOverflow" => Name::num_overflowing(Name::anonymous(), u64::MAX),
        "mixed" => Name::num(Name::str(Name::num(Name::anonymous(), 7), "x"), 9),
        _ => return None,
    })
}

fn u() -> Level {
    Level::param(n("u"))
}

fn v() -> Level {
    Level::param(n("v"))
}

fn lm() -> Level {
    Level::mvar(LMVarId(Name::num(n("_lmvar"), 1)))
}

fn nat_level(k: u32) -> Level {
    Level::zero().add_offset(k).expect("small")
}

fn level_case(label: &str) -> Option<Level> {
    let l = |r: Result<Level, _>| r.expect("fixture levels pack");
    Some(match label {
        "zero" => Level::zero(),
        "one" => Level::one(),
        "five" => nat_level(5),
        "u" => u(),
        "v" => v(),
        "mvar" => lm(),
        "succ_u" => l(u().succ()),
        "max_u_v" => l(Level::max(u(), v())),
        "max_v_u" => l(Level::max(v(), u())),
        "imax_u_v" => l(Level::imax(u(), v())),
        "imax_u_zero" => l(Level::imax(u(), Level::zero())),
        "imax_zero_u" => l(Level::imax(Level::zero(), u())),
        "imax_one_u" => l(Level::imax(Level::one(), u())),
        "imax_u_u" => l(Level::imax(u(), u())),
        "imax_u_succ_v" => l(Level::imax(u(), l(v().succ()))),
        "nested_max" => l(Level::max(l(Level::max(u(), v())), v())),
        "succ_max" => l(Level::max(u(), v())).succ().expect("packs"),
        "max_one_succ_u" => l(Level::max(Level::one(), l(u().succ()))),
        "max_three_u" => l(Level::max(nat_level(3), u())),
        "max_u_mvar" => l(Level::max(u(), lm())),
        _ => return None,
    })
}

fn expr_case(label: &str) -> Option<Expr> {
    let x = || Expr::fvar(FVarId(n("x")));
    let em = || Expr::mvar(MVarId(n("m")));
    let nat_c = || Expr::const_(n("Nat"), Vec::new());
    Some(match label {
        "bvar0" => Expr::bvar(0).expect("packs"),
        "bvar5" => Expr::bvar(5).expect("packs"),
        "fvar_x" => x(),
        "mvar_m" => em(),
        "sort_zero" => Expr::sort(Level::zero()),
        "sort_u" => Expr::sort(u()),
        "sort_mvar" => Expr::sort(lm()),
        "const_Nat" => nat_c(),
        "const_Foo" => Expr::const_(n("Foo"), vec![Level::zero(), u()]),
        "app" => Expr::app(nat_c(), x()),
        "app_chain" => Expr::app(Expr::app(nat_c(), x()), em()),
        "app_bvar" => Expr::app(nat_c(), Expr::bvar(9).expect("packs")),
        "lam_id" => Expr::lam(
            n("y"),
            nat_c(),
            Expr::bvar(0).expect("packs"),
            BinderInfo::Default,
        ),
        "lam_loose" => Expr::lam(
            n("y"),
            nat_c(),
            Expr::bvar(1).expect("packs"),
            BinderInfo::Implicit,
        ),
        "forall_dom_loose" => Expr::forall_e(
            n("y"),
            Expr::bvar(0).expect("packs"),
            nat_c(),
            BinderInfo::InstImplicit,
        ),
        "letE" => Expr::let_e(
            n("z"),
            nat_c(),
            Expr::bvar(2).expect("packs"),
            Expr::bvar(0).expect("packs"),
            false,
        ),
        "lit_nat" => Expr::lit(Literal::Nat(NatLit::from_u64(42))),
        "lit_nat_zero" => Expr::lit(Literal::Nat(NatLit::from_u64(0))),
        // 2^80 + 5 = limbs [5, 2^16] little-endian.
        "lit_nat_big" => Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![5, 1 << 16]))),
        "lit_str" => Expr::lit(Literal::Str("hi".into())),
        "mdata" => Expr::mdata(KVMap::default(), x()),
        "proj" => Expr::proj(n("Prod"), 1, x()),
        "proj_deep" => Expr::proj(
            n("Prod"),
            0,
            Expr::app(nat_c(), Expr::bvar(3).expect("packs")),
        ),
        "mdata_deep300" => {
            let mut e = x();
            for _ in 0..300 {
                e = Expr::mdata(KVMap::default(), e);
            }
            e
        }
        "mdata_deep301" => {
            let mut e = x();
            for _ in 0..301 {
                e = Expr::mdata(KVMap::default(), e);
            }
            e
        }
        _ => return None,
    })
}

/// Render a native boolean in the fixture's own encoding. Comparing in fixture space
/// means a malformed field is reported as an ordinary mismatch, never a panic.
fn bool_str(v: bool) -> &'static str {
    if v { "1" } else { "0" }
}

#[test]
fn core_observables_match_the_reference_fixture() {
    let text = include_str!("../fixtures/core_observables.txt");
    let mut mismatches: Vec<String> = Vec::new();
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut records = 0usize;

    let mut schema_ok = false;
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line == "schema fln-core-observables/1" {
            schema_ok = true;
            continue;
        }
        let fields: Vec<&str> = line.split('|').collect();
        records += 1;
        match fields.as_slice() {
            ["string", label, hash] => {
                seen.insert(format!("string/{label}"));
                let Some(s) = string_case(label) else {
                    mismatches.push(format!("unknown string case `{label}`"));
                    continue;
                };
                let ours = string_hash(&s);
                if ours.to_string() != *hash {
                    mismatches.push(format!("string/{label}: ours {ours}, oracle {hash}"));
                }
            }
            ["name", label, hash] => {
                seen.insert(format!("name/{label}"));
                let Some(name) = name_case(label) else {
                    mismatches.push(format!("unknown name case `{label}`"));
                    continue;
                };
                if name.hash().to_string() != *hash {
                    mismatches.push(format!("name/{label}: ours {}, oracle {hash}", name.hash()));
                }
            }
            ["level", label, hash, depth, has_mvar, has_param, norm_hash] => {
                seen.insert(format!("level/{label}"));
                let Some(level) = level_case(label) else {
                    mismatches.push(format!("unknown level case `{label}`"));
                    continue;
                };
                let checks = [
                    ("hash", level.hash().to_string(), hash.to_string()),
                    ("depth", level.depth().to_string(), depth.to_string()),
                    (
                        "hasMVar",
                        bool_str(level.has_mvar()).to_string(),
                        has_mvar.to_string(),
                    ),
                    (
                        "hasParam",
                        bool_str(level.has_param()).to_string(),
                        has_param.to_string(),
                    ),
                    (
                        "normHash",
                        level.normalize().hash().to_string(),
                        norm_hash.to_string(),
                    ),
                ];
                for (what, ours, oracle) in checks {
                    if ours != oracle {
                        mismatches.push(format!(
                            "level/{label}.{what}: ours {ours}, oracle {oracle}"
                        ));
                    }
                }
            }
            ["equiv", label_a, label_b, expected] => {
                seen.insert(format!("equiv/{label_a}/{label_b}"));
                // Equiv pairs may reference levels outside the labeled corpus; build
                // both sides here by pair identity.
                let pair = match (*label_a, *label_b) {
                    ("max_u_v", "max_v_u") => Some((
                        Level::max(u(), v()).expect("packs"),
                        Level::max(v(), u()).expect("packs"),
                    )),
                    ("imax_u_zero", "zero") => Some((
                        Level::imax(u(), Level::zero()).expect("packs"),
                        Level::zero(),
                    )),
                    ("succ_max", "max_succ") => Some((
                        Level::max(u(), v()).expect("packs").succ().expect("packs"),
                        Level::max(u().succ().expect("packs"), v().succ().expect("packs"))
                            .expect("packs"),
                    )),
                    ("u", "v") => Some((u(), v())),
                    _ => None,
                };
                let Some((a, b)) = pair else {
                    mismatches.push(format!("unknown equiv pair `{label_a}`/`{label_b}`"));
                    continue;
                };
                let ours = a.is_equiv(&b);
                if bool_str(ours) != *expected {
                    mismatches.push(format!(
                        "equiv/{label_a}/{label_b}: ours {ours}, oracle {expected}"
                    ));
                }
            }
            ["expr", label, hash, range, depth, fv, emv, lmv, lp] => {
                seen.insert(format!("expr/{label}"));
                let Some(expr) = expr_case(label) else {
                    mismatches.push(format!("unknown expr case `{label}`"));
                    continue;
                };
                let checks = [
                    ("hash", expr.hash().to_string(), hash.to_string()),
                    (
                        "looseBVarRange",
                        expr.loose_bvar_range().to_string(),
                        range.to_string(),
                    ),
                    (
                        "approxDepth",
                        expr.approx_depth().to_string(),
                        depth.to_string(),
                    ),
                    (
                        "hasFVar",
                        bool_str(expr.has_fvar()).to_string(),
                        fv.to_string(),
                    ),
                    (
                        "hasExprMVar",
                        bool_str(expr.has_expr_mvar()).to_string(),
                        emv.to_string(),
                    ),
                    (
                        "hasLevelMVar",
                        bool_str(expr.has_level_mvar()).to_string(),
                        lmv.to_string(),
                    ),
                    (
                        "hasLevelParam",
                        bool_str(expr.has_level_param()).to_string(),
                        lp.to_string(),
                    ),
                ];
                for (what, ours, oracle) in checks {
                    if ours != oracle {
                        mismatches
                            .push(format!("expr/{label}.{what}: ours {ours}, oracle {oracle}"));
                    }
                }
            }
            other => mismatches.push(format!("malformed fixture record: {other:?}")),
        }
    }

    assert!(schema_ok, "fixture is missing its schema line");
    assert!(records >= 60, "fixture corpus shrank: {records} records");
    assert!(
        mismatches.is_empty(),
        "{} observable mismatch(es) against the pinned Reference:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}
