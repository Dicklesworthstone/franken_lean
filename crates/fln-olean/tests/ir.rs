//! The pin's `.ir` files decoded into typed IR declarations (bead
//! `fln-ir-decoder-call-graph-sjzl`).
//!
//! The evidence here is a differential, not a self-check. The stock pinned
//! `lean` reads an `.ir` file with its own `readModuleData`, reads each entry as
//! its own `Lean.IR.Decl`, and prints one canonical line per declaration
//! (`scripts/tribunal/ir_dump.lean`). This suite renders the same spelling from
//! FrankenLean's reading of the same bytes and requires the two to be equal,
//! character for character: every name, type, flag, size and literal.
//!
//! * Per commit, on two real `.ir` files committed beside the pin's printout
//!   of them (`fixtures/ir/`).
//! * Where the pin is installed, the committed files are shown to be the pin's
//!   own and the printouts are regenerated and compared.
//! * On demand (`--ignored`), every `.ir` file of the toolchain.
//!
//! None of this shows that a declaration can be executed.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use fln_core::name::{LeafView, Name};
use fln_olean::ir::{
    IrAlt, IrArg, IrBody, IrCtorInfo, IrDecl, IrDecodeError, IrDecodeLimits, IrExpr, IrExternEntry,
    IrLit, IrModule, IrNat, IrParam, IrStmt, IrTerminal, IrType, decode_ir,
};
use fln_olean::region::{OleanView, OpaqueExtensionBlock, WalkBudget};
use fln_rt::convert::inject_name;
use fln_rt::obj::Obj;
use fln_rt::region::compact;

/// Cumulative allowance for the captured entries of one file. An entry is
/// captured as a standalone region, so a graph shared between declarations is
/// counted once per declaration.
const PAYLOAD_CAP: usize = 1 << 30;

/// `Init/Data/Nat/Basic.ir` and `Lean/Util/Profile.ir` of the pinned toolchain,
/// byte for byte, each beside the pin's printout of it. Between them they hold
/// 25 of the 28 forms the toolchain's IR uses; `uproj`, `uset` and `del` occur
/// only in the on-demand sweep.
const FIXTURES: [(&str, &[u8], &str); 2] = [
    (
        "Init/Data/Nat/Basic.ir",
        include_bytes!("../fixtures/ir/Init.Data.Nat.Basic.ir"),
        include_str!("../fixtures/ir/Init.Data.Nat.Basic.irdump"),
    ),
    (
        "Lean/Util/Profile.ir",
        include_bytes!("../fixtures/ir/Lean.Util.Profile.ir"),
        include_str!("../fixtures/ir/Lean.Util.Profile.irdump"),
    ),
];

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

/// The extension blocks of one `.ir` file and the name list the pin stored in
/// the same file's `extraConstNames`.
fn open(bytes: &[u8]) -> Result<(Vec<OpaqueExtensionBlock>, Vec<Name>), String> {
    let view = OleanView::parse(bytes).map_err(|error| format!("parse: {error}"))?;
    let blocks = view
        .extension_payloads(WalkBudget::default(), PAYLOAD_CAP)
        .map_err(|error| format!("extension payloads: {error}"))?;
    let names = view
        .extra_const_names(WalkBudget::default())
        .map_err(|error| format!("extraConstNames: {error}"))?;
    Ok((blocks, names))
}

fn fixture(index: usize) -> (Vec<OpaqueExtensionBlock>, IrModule) {
    let (blocks, _) = open(FIXTURES[index].1).expect("committed fixture opens");
    let module = decode_ir(&blocks, IrDecodeLimits::default()).expect("committed fixture decodes");
    (blocks, module)
}

// ---- the canonical spelling: a mirror of scripts/tribunal/ir_dump.lean ----

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn spell_name(name: &Name) -> String {
    let mut parts = Vec::new();
    let mut cursor = name.clone();
    loop {
        match cursor.leaf_view() {
            LeafView::Anonymous => break,
            LeafView::Num(value) => parts.push(format!("#{value}")),
            LeafView::Str(text) => {
                let plain = !text.is_empty()
                    && text
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '\'' | '!' | '?'));
                parts.push(if plain {
                    text.to_owned()
                } else {
                    format!("%{}", hex(text.as_bytes()))
                });
            }
        }
        let parent = cursor.parent();
        cursor = parent;
    }
    if parts.is_empty() {
        return "[anonymous]".to_owned();
    }
    parts.reverse();
    parts.join(".")
}

fn spell_type(ty: &IrType) -> String {
    let members = |types: &[IrType]| -> String {
        types
            .iter()
            .map(|t| format!(" {}", spell_type(t)))
            .collect()
    };
    match ty {
        IrType::Float => "float".into(),
        IrType::UInt8 => "u8".into(),
        IrType::UInt16 => "u16".into(),
        IrType::UInt32 => "u32".into(),
        IrType::UInt64 => "u64".into(),
        IrType::USize => "usize".into(),
        IrType::Erased => "erased".into(),
        IrType::Object => "obj".into(),
        IrType::TObject => "tobj".into(),
        IrType::Float32 => "float32".into(),
        IrType::Struct { lean_type, types } => {
            let owner = match lean_type {
                None => "none".to_owned(),
                Some(name) => format!("(some {})", spell_name(name)),
            };
            format!("(struct {owner}{})", members(types))
        }
        IrType::Union { lean_type, types } => {
            format!("(union {}{})", spell_name(lean_type), members(types))
        }
        IrType::Tagged => "tagged".into(),
        IrType::Void => "void".into(),
    }
}

fn spell_arg(arg: &IrArg) -> String {
    match arg {
        IrArg::Var(x) => format!("x{x}"),
        IrArg::Erased => "erased".into(),
    }
}

fn spell_args(args: &[IrArg]) -> String {
    args.iter()
        .map(|arg| format!(" {}", spell_arg(arg)))
        .collect()
}

fn spell_ctor_info(info: &IrCtorInfo) -> String {
    format!(
        "(ci {} {} {} {} {})",
        spell_name(&info.name),
        info.cidx,
        info.size,
        info.usize,
        info.ssize
    )
}

fn spell_nat(value: &IrNat) -> String {
    match value {
        IrNat::Small(value) => format!("{value:x}"),
        IrNat::Big(limbs) => {
            let mut out = String::new();
            for limb in limbs.iter().rev() {
                if out.is_empty() {
                    if *limb != 0 {
                        out = format!("{limb:x}");
                    }
                } else {
                    out.push_str(&format!("{limb:016x}"));
                }
            }
            if out.is_empty() { "0".into() } else { out }
        }
    }
}

fn spell_expr(expr: &IrExpr) -> String {
    match expr {
        IrExpr::Ctor { info, args } => {
            format!("(ctor {}{})", spell_ctor_info(info), spell_args(args))
        }
        IrExpr::Reset { n, x } => format!("(reset {n} x{x})"),
        IrExpr::Reuse {
            x,
            info,
            update_header,
            args,
        } => format!(
            "(reuse x{x} {} {}{})",
            spell_ctor_info(info),
            u8::from(*update_header),
            spell_args(args)
        ),
        IrExpr::Proj { i, x } => format!("(proj {i} x{x})"),
        IrExpr::UProj { i, x } => format!("(uproj {i} x{x})"),
        IrExpr::SProj { n, offset, x } => format!("(sproj {n} {offset} x{x})"),
        IrExpr::Fap { function, args } => {
            format!("(fap {}{})", spell_name(function), spell_args(args))
        }
        IrExpr::Pap { function, args } => {
            format!("(pap {}{})", spell_name(function), spell_args(args))
        }
        IrExpr::Ap { x, args } => format!("(ap x{x}{})", spell_args(args)),
        IrExpr::Box { ty, x } => format!("(box {} x{x})", spell_type(ty)),
        IrExpr::Unbox { x } => format!("(unbox x{x})"),
        IrExpr::Lit(IrLit::Num(value)) => format!("(num {})", spell_nat(value)),
        IrExpr::Lit(IrLit::Str(text)) => format!("(str \"{}\")", hex(text.as_bytes())),
        IrExpr::IsShared { x } => format!("(isShared x{x})"),
    }
}

fn spell_params(params: &[IrParam]) -> String {
    let each: Vec<String> = params
        .iter()
        .map(|p| {
            format!(
                "(p x{} {} {})",
                p.x,
                if p.borrow { "b" } else { "o" },
                spell_type(&p.ty)
            )
        })
        .collect();
    format!("({})", each.join(" "))
}

fn spell_body(body: &IrBody) -> String {
    let mut out = String::from("(body");
    for stmt in &body.stmts {
        out.push(' ');
        out.push_str(&match stmt {
            IrStmt::VDecl { x, ty, expr } => {
                format!("(vdecl x{x} {} {})", spell_type(ty), spell_expr(expr))
            }
            IrStmt::JDecl { j, params, value } => {
                format!(
                    "(jdecl j{j} {} {})",
                    spell_params(params),
                    spell_body(value)
                )
            }
            IrStmt::Set { x, i, y } => format!("(set x{x} {i} {})", spell_arg(y)),
            IrStmt::SetTag { x, cidx } => format!("(setTag x{x} {cidx})"),
            IrStmt::USet { x, i, y } => format!("(uset x{x} {i} x{y})"),
            IrStmt::SSet {
                x,
                i,
                offset,
                y,
                ty,
            } => format!("(sset x{x} {i} {offset} x{y} {})", spell_type(ty)),
            IrStmt::Inc {
                x,
                n,
                checked,
                persistent,
            } => format!(
                "(inc x{x} {n} {} {})",
                u8::from(*checked),
                u8::from(*persistent)
            ),
            IrStmt::Dec {
                x,
                n,
                checked,
                persistent,
            } => format!(
                "(dec x{x} {n} {} {})",
                u8::from(*checked),
                u8::from(*persistent)
            ),
            IrStmt::Del { x } => format!("(del x{x})"),
        });
    }
    out.push(' ');
    out.push_str(&match body.terminal.as_ref() {
        IrTerminal::Case {
            type_name,
            x,
            x_type,
            alts,
        } => {
            let alts: String = alts
                .iter()
                .map(|alt| match alt {
                    IrAlt::Ctor { info, body } => {
                        format!(" (alt {} {})", spell_ctor_info(info), spell_body(body))
                    }
                    IrAlt::Default { body } => format!(" (default {})", spell_body(body)),
                })
                .collect();
            format!(
                "(case {} x{x} {}{alts})",
                spell_name(type_name),
                spell_type(x_type)
            )
        }
        IrTerminal::Ret(arg) => format!("(ret {})", spell_arg(arg)),
        IrTerminal::Jmp { j, args } => format!("(jmp j{j}{})", spell_args(args)),
        IrTerminal::Unreachable => "(unreachable)".into(),
    });
    out.push(')');
    out
}

fn spell_decl(decl: &IrDecl) -> String {
    match decl {
        IrDecl::Function {
            name,
            params,
            result,
            body,
            sorry_dep,
        } => format!(
            "(fdecl {} {} {} {} {})",
            spell_name(name),
            spell_params(params),
            spell_type(result),
            spell_body(body),
            match sorry_dep {
                None => "none".to_owned(),
                Some(name) => format!("(some {})", spell_name(name)),
            }
        ),
        IrDecl::Extern {
            name,
            params,
            result,
            entries,
        } => {
            let entries: Vec<String> = entries
                .iter()
                .map(|entry| match entry {
                    IrExternEntry::Adhoc { backend } => format!("(adhoc {})", spell_name(backend)),
                    IrExternEntry::Inline { backend, pattern } => format!(
                        "(inline {} \"{}\")",
                        spell_name(backend),
                        hex(pattern.as_bytes())
                    ),
                    IrExternEntry::Standard { backend, function } => format!(
                        "(standard {} \"{}\")",
                        spell_name(backend),
                        hex(function.as_bytes())
                    ),
                    IrExternEntry::Opaque => "(opaque)".into(),
                })
                .collect();
            format!(
                "(extern {} {} {} ({}))",
                spell_name(name),
                spell_params(params),
                spell_type(result),
                entries.join(" ")
            )
        }
    }
}

/// Where two spellings first differ, with a little context from each.
fn first_difference(ours: &str, theirs: &str) -> String {
    let at = ours
        .bytes()
        .zip(theirs.bytes())
        .position(|(a, b)| a != b)
        .unwrap_or(ours.len().min(theirs.len()));
    let window = |text: &str| -> String {
        let from = at.saturating_sub(60);
        text.get(from..(at + 60).min(text.len()))
            .unwrap_or("<not on a character boundary>")
            .to_owned()
    };
    format!(
        "byte {at}: ours `{}` pin `{}`",
        window(ours),
        window(theirs)
    )
}

// ---- per commit: the committed files ----

#[test]
fn the_generated_layout_is_what_the_vendored_declarations_render_to() {
    let root = fln_core::checked_workspace_root!();
    let output = Command::new("python3")
        .args(["-I", "-S", "scripts/extract/gen_ir_contract.py", "--check"])
        .current_dir(&root)
        .output()
        .expect("python3 runs the extraction script");
    assert!(
        output.status.success(),
        "crates/fln-olean/src/ir_format.rs is not what the vendored IR declarations render to: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn two_real_ir_files_decode_to_exactly_what_the_pin_prints() {
    for (module_path, bytes, pin_printout) in FIXTURES {
        let (blocks, listed) = open(bytes).expect("committed fixture opens");
        let module =
            decode_ir(&blocks, IrDecodeLimits::default()).expect("committed fixture decodes");
        let pin_lines: Vec<&str> = pin_printout.lines().collect();
        assert_eq!(
            module.decls.len(),
            pin_lines.len(),
            "{module_path}: declaration count"
        );
        for (index, (decl, pin_line)) in module.decls.iter().zip(&pin_lines).enumerate() {
            let ours = spell_decl(decl);
            assert!(
                ours == *pin_line,
                "{module_path} declaration {index}: {}",
                first_difference(&ours, pin_line)
            );
        }
        // The pin writes the same names a second time with different code
        // (`getIRExtraConstNames`); a decoder that drops or invents one fails.
        let decoded: BTreeSet<&Name> = module.decls.iter().map(IrDecl::name).collect();
        assert_eq!(
            decoded.len(),
            module.decls.len(),
            "{module_path}: a name repeats"
        );
        assert_eq!(decoded, listed.iter().collect(), "{module_path}: name list");
        // `sortDecls` orders them by `Name.quickLt`.
        assert!(
            module
                .decls
                .windows(2)
                .all(|pair| pair[0].name().quick_lt(pair[1].name())),
            "{module_path}: stored order is not the pin's sort"
        );
    }
}

#[test]
fn the_fixtures_exercise_the_forms_the_differential_claims() {
    let mut forms = BTreeMap::new();
    for index in 0..FIXTURES.len() {
        for (form, count) in census(&fixture(index).1) {
            *forms.entry(form).or_insert(0u64) += count;
        }
    }
    let seen: Vec<&str> = forms.keys().copied().collect();
    assert_eq!(
        seen,
        [
            "Alt.ctor",
            "Alt.default",
            "Decl.extern",
            "Decl.fdecl",
            "Expr.ap",
            "Expr.box",
            "Expr.ctor",
            "Expr.fap",
            "Expr.isShared",
            "Expr.lit",
            "Expr.pap",
            "Expr.proj",
            "Expr.sproj",
            "Expr.unbox",
            "FnBody.case",
            "FnBody.dec",
            "FnBody.inc",
            "FnBody.jdecl",
            "FnBody.jmp",
            "FnBody.ret",
            "FnBody.set",
            "FnBody.setTag",
            "FnBody.sset",
            "FnBody.unreachable",
            "FnBody.vdecl",
        ],
        "the per-commit differential covers exactly these forms"
    );
    assert_eq!(forms["Decl.fdecl"], 85);
    assert_eq!(forms["Decl.extern"], 2);
    // The last block of an `.ir` file is the package table; it is named, not read.
    let (_, module) = fixture(0);
    assert_eq!(
        module
            .uninterpreted
            .iter()
            .map(spell_name)
            .collect::<Vec<_>>(),
        ["_private.Lean.Compiler.ModPkgExt.#0.Lean.modPkgExt"]
    );
}

#[test]
fn callees_are_the_full_and_partial_application_targets() {
    let (_, nat) = fixture(0);
    let callees = |module: &IrModule, name: &str| -> Vec<String> {
        let decl = module
            .decls
            .iter()
            .find(|decl| decl.name() == &n(name))
            .unwrap_or_else(|| panic!("{name} is in the fixture"));
        decl.callees().into_iter().map(spell_name).collect()
    };
    assert_eq!(callees(&nat, "Nat.blt"), ["Nat.add", "Nat.ble"]);
    // Its only edge is a partial application: `let x_1 : obj := pap Nat.instMax._lam_0._boxed`.
    assert_eq!(
        callees(&nat, "Nat.instMax._closed_0"),
        ["Nat.instMax._lam_0._boxed"]
    );
    assert!(callees(&nat, "Nat.instTransLt").is_empty());
    let (_, profile) = fixture(1);
    assert!(
        callees(&profile, "Lean.profileit").is_empty(),
        "an extern has no body"
    );
}

#[test]
fn every_limit_is_a_resource_stop() {
    let (blocks, _) = fixture(0);
    let stopped = |limits: IrDecodeLimits, resource: &str| match decode_ir(&blocks, limits) {
        Err(error @ IrDecodeError::Limit { .. }) => {
            assert!(error.is_resource());
            assert!(
                matches!(error, IrDecodeError::Limit { resource: named } if named == resource),
                "expected the {resource} limit, got {error}"
            );
        }
        other => panic!("expected the {resource} limit, got {other:?}"),
    };
    let base = IrDecodeLimits::default();
    stopped(
        IrDecodeLimits {
            max_decls: 41,
            ..base
        },
        "IR declarations",
    );
    stopped(
        IrDecodeLimits {
            max_bytes: 64,
            ..base
        },
        "payload bytes",
    );
    stopped(
        IrDecodeLimits {
            max_objects: 3,
            ..base
        },
        "objects",
    );
    stopped(
        IrDecodeLimits {
            max_nodes: 40,
            ..base
        },
        "IR nodes",
    );
    // `Nat.max` ends in a `case`, whose arms are one level down.
    stopped(
        IrDecodeLimits {
            max_depth: 1,
            ..base
        },
        "IR nesting depth",
    );
    // One declaration fewer than the file holds is refused; exactly as many is not.
    assert!(
        decode_ir(
            &blocks,
            IrDecodeLimits {
                max_decls: 42,
                ..base
            }
        )
        .is_ok()
    );
}

#[test]
fn a_changed_byte_is_a_typed_answer_and_never_a_panic() {
    let (blocks, original) = fixture(0);
    let declarations = blocks
        .iter()
        .position(|block| block.name == n("Lean.IR.declMapExt"))
        .expect("the fixture has a declaration block");
    let (mut refused, mut decoded, mut changed) = (0u64, 0u64, 0u64);
    // Each declaration is its own captured region, so it is mutated and decoded
    // alone: one flipped bit, one flipped sign bit, one inverted byte, at every
    // offset of every declaration.
    for (entry, original) in blocks[declarations].entries.iter().zip(&original.decls) {
        for offset in 0..entry.len() {
            for mask in [0x01u8, 0x80, 0xff] {
                let mut mutated = entry.clone();
                mutated[offset] ^= mask;
                let alone = [OpaqueExtensionBlock {
                    name: n("Lean.IR.declMapExt"),
                    entries: vec![mutated],
                }];
                match decode_ir(&alone, IrDecodeLimits::default()) {
                    Err(_) => refused += 1,
                    Ok(module) => {
                        decoded += 1;
                        changed += u64::from(module.decls.first() != Some(original));
                    }
                }
            }
        }
    }
    // Both outcomes must occur, or the loop proved nothing: a flipped tag is
    // refused, a flipped variable index is a different, well-formed declaration.
    assert!(refused > 1_000, "only {refused} mutations were refused");
    assert!(
        changed > 1_000,
        "only {changed} mutations decoded to something else"
    );
    assert!(decoded >= changed);

    // The container reader in front of it: every truncation is an answer too.
    let bytes = FIXTURES[0].1;
    for len in (0..bytes.len()).step_by(97) {
        let _ =
            open(&bytes[..len]).map(|(blocks, _)| decode_ir(&blocks, IrDecodeLimits::default()));
    }
}

/// An `.olean` written outside the module system carries its own compiled
/// declarations in the same entries. This one holds what the two `.ir` files do
/// not: a literal past one machine word, a persistent `inc`, and a string
/// outside ASCII.
#[test]
fn an_olean_that_carries_its_own_ir_decodes_to_what_the_pin_prints() {
    let bytes: &[u8] = include_bytes!("../fixtures/g05_pilot.olean");
    let pin = include_str!("../fixtures/ir/g05_pilot.olean.irdump");
    let (blocks, _) = open(bytes).expect("the fixture opens");
    let module = decode_ir(&blocks, IrDecodeLimits::default()).expect("the fixture decodes");
    let ours: Vec<String> = module.decls.iter().map(spell_decl).collect();
    let theirs: Vec<&str> = pin.lines().collect();
    assert_eq!(ours.len(), theirs.len(), "declaration count");
    for (index, (ours, theirs)) in ours.iter().zip(&theirs).enumerate() {
        assert!(
            ours == theirs,
            "declaration {index}: {}",
            first_difference(ours, theirs)
        );
    }
    let text = ours.join("\n");
    assert!(text.contains("(num 5ce0e9a56015fec5aadfa328ae398115)"));
    assert!(text.contains("(inc x1 1 1 1)"));
    assert!(
        module
            .decls
            .iter()
            .any(|decl| format!("{decl:?}").contains("héllo"))
    );
}

// ---- hand-built objects: shapes no real file contains ----

fn block_of(decl: &Obj) -> Vec<OpaqueExtensionBlock> {
    vec![OpaqueExtensionBlock {
        name: n("Lean.IR.declMapExt"),
        entries: vec![compact(decl, 0).expect("hand-built declaration compacts")],
    }]
}

/// `def f : obj := <body>` with no parameters and no `sorry` dependency.
fn function(body: Obj) -> Obj {
    Obj::mk_ctor(
        0,
        vec![
            inject_name(&n("f")),
            Obj::mk_array(vec![]),
            Obj::mk_nat(7), // IRType.object
            body,
            Obj::mk_nat(0), // DeclInfo is its one field: Option.none
        ],
        &[],
    )
}

fn ret_erased() -> Obj {
    // FnBody.ret (Arg.erased)
    Obj::mk_ctor(10, vec![Obj::mk_nat(1)], &[])
}

fn ctor_info() -> Obj {
    Obj::mk_ctor(
        0,
        vec![
            inject_name(&n("Prod.mk")),
            Obj::mk_nat(0),
            Obj::mk_nat(2),
            Obj::mk_nat(0),
            Obj::mk_nat(0),
        ],
        &[],
    )
}

fn shape_of(decl: &Obj) -> &'static str {
    match decode_ir(&block_of(decl), IrDecodeLimits::default()) {
        Err(IrDecodeError::Shape { detail }) => detail,
        other => panic!("expected a shape refusal, got {other:?}"),
    }
}

#[test]
fn reset_and_reuse_decode_though_no_toolchain_file_contains_them() {
    // The pin expands both away before it saves IR: neither occurs in any of
    // its 2,431 files. Their layout is therefore held only by the extraction
    // rule the other forms confirm, and by this object.
    let reuse = |update_header: u8| {
        Obj::mk_ctor(
            2,
            vec![
                Obj::mk_nat(4),
                ctor_info(),
                Obj::mk_array(vec![
                    Obj::mk_ctor(0, vec![Obj::mk_nat(9)], &[]),
                    Obj::mk_nat(1),
                ]),
            ],
            &[update_header],
        )
    };
    let reset = Obj::mk_ctor(1, vec![Obj::mk_nat(2), Obj::mk_nat(3)], &[]);
    let body = Obj::mk_ctor(
        0,
        vec![
            Obj::mk_nat(5),
            Obj::mk_nat(7),
            reset,
            Obj::mk_ctor(
                0,
                vec![Obj::mk_nat(6), Obj::mk_nat(7), reuse(1), ret_erased()],
                &[],
            ),
        ],
        &[],
    );
    let module = decode_ir(&block_of(&function(body)), IrDecodeLimits::default()).unwrap();
    assert_eq!(
        spell_decl(&module.decls[0]),
        "(fdecl f () obj (body (vdecl x5 obj (reset 2 x3)) \
         (vdecl x6 obj (reuse x4 (ci Prod.mk 0 2 0 0) 1 x9 erased)) (ret erased)) none)"
    );
    // The flag is a `Bool`: any byte but 0 or 1 is not one.
    let bad = Obj::mk_ctor(
        0,
        vec![Obj::mk_nat(6), Obj::mk_nat(7), reuse(2), ret_erased()],
        &[],
    );
    assert_eq!(shape_of(&function(bad)), "Bool scalar is neither 0 nor 1");
}

#[test]
fn struct_and_union_types_decode_though_no_file_contains_them() {
    // Zero occurrences in 712,497 declarations of the toolchain and Mathlib:
    // like `reset` and `reuse`, these are held by the extraction rule and by
    // this object, not by real data.
    let members = || Obj::mk_array(vec![Obj::mk_nat(1), Obj::mk_nat(7)]);
    let anonymous_struct = Obj::mk_ctor(10, vec![Obj::mk_nat(0), members()], &[]);
    let named_struct = Obj::mk_ctor(
        10,
        vec![
            Obj::mk_ctor(1, vec![inject_name(&n("Prod"))], &[]),
            Obj::mk_array(vec![anonymous_struct]),
        ],
        &[],
    );
    let union = Obj::mk_ctor(
        11,
        vec![inject_name(&n("Sum")), Obj::mk_array(vec![named_struct])],
        &[],
    );
    let decl = Obj::mk_ctor(
        0,
        vec![
            inject_name(&n("f")),
            Obj::mk_array(vec![]),
            union,
            ret_erased(),
            Obj::mk_nat(0),
        ],
        &[],
    );
    let module = decode_ir(&block_of(&decl), IrDecodeLimits::default()).unwrap();
    assert_eq!(
        spell_decl(&module.decls[0]),
        "(fdecl f () (union Sum (struct (some Prod) (struct none u8 obj))) (body (ret erased)) none)"
    );
    // Types nest, so they are under the depth limit like bodies are.
    assert!(matches!(
        decode_ir(
            &block_of(&decl),
            IrDecodeLimits {
                max_depth: 2,
                ..IrDecodeLimits::default()
            }
        ),
        Err(IrDecodeError::Limit {
            resource: "IR nesting depth"
        })
    ));
}

#[test]
fn an_unknown_or_misshapen_constructor_is_refused_not_skipped() {
    // A `Decl` constructor the pin does not have.
    let unknown_decl = Obj::mk_ctor(2, vec![inject_name(&n("f"))], &[]);
    assert_eq!(shape_of(&unknown_decl), "unknown Decl constructor");
    // `fdecl` with a field missing.
    let short = Obj::mk_ctor(
        0,
        vec![
            inject_name(&n("f")),
            Obj::mk_array(vec![]),
            Obj::mk_nat(7),
            ret_erased(),
        ],
        &[],
    );
    assert_eq!(shape_of(&short), "unexpected object-field count");
    // An instruction tag past `unreachable`, as an object and as a boxed tag.
    assert_eq!(
        shape_of(&function(Obj::mk_ctor(13, vec![Obj::mk_nat(0)], &[]))),
        "unknown FnBody constructor"
    );
    assert_eq!(
        shape_of(&function(Obj::mk_nat(11))),
        "unknown field-less FnBody"
    );
    // A result type past `void`.
    let bad_type = Obj::mk_ctor(
        0,
        vec![
            inject_name(&n("f")),
            Obj::mk_array(vec![]),
            Obj::mk_nat(14),
            ret_erased(),
            Obj::mk_nat(0),
        ],
        &[],
    );
    assert_eq!(shape_of(&bad_type), "unknown field-less IRType");
    // A parameter whose borrow flag is not a `Bool`.
    let parameter = Obj::mk_ctor(0, vec![Obj::mk_nat(1), Obj::mk_nat(7)], &[2]);
    let bad_param = Obj::mk_ctor(
        0,
        vec![
            inject_name(&n("f")),
            Obj::mk_array(vec![parameter]),
            Obj::mk_nat(7),
            ret_erased(),
            Obj::mk_nat(0),
        ],
        &[],
    );
    assert_eq!(shape_of(&bad_param), "Bool scalar is neither 0 nor 1");
    // Two declaration blocks in one file.
    let mut twice = block_of(&function(ret_erased()));
    twice.extend(block_of(&function(ret_erased())));
    assert!(matches!(
        decode_ir(&twice, IrDecodeLimits::default()),
        Err(IrDecodeError::Shape {
            detail: "duplicate IR declaration block"
        })
    ));
    // And the well-formed control, so the refusals above are not a decoder
    // that refuses everything.
    let module = decode_ir(
        &block_of(&function(ret_erased())),
        IrDecodeLimits::default(),
    )
    .unwrap();
    assert_eq!(
        spell_decl(&module.decls[0]),
        "(fdecl f () obj (body (ret erased)) none)"
    );
}

// ---- where the pin is installed ----

/// How many times each IR form occurs in a module, by the pin's own name for it.
fn census(module: &IrModule) -> BTreeMap<&'static str, u64> {
    let mut out = BTreeMap::new();
    let mut count = |form: &'static str| *out.entry(form).or_insert(0u64) += 1;
    for decl in &module.decls {
        let body = match decl {
            IrDecl::Extern { .. } => {
                count("Decl.extern");
                continue;
            }
            IrDecl::Function { body, .. } => {
                count("Decl.fdecl");
                body
            }
        };
        for nested in body.bodies() {
            for stmt in &nested.stmts {
                let form = match stmt {
                    IrStmt::VDecl { expr, .. } => {
                        count(match expr {
                            IrExpr::Ctor { .. } => "Expr.ctor",
                            IrExpr::Reset { .. } => "Expr.reset",
                            IrExpr::Reuse { .. } => "Expr.reuse",
                            IrExpr::Proj { .. } => "Expr.proj",
                            IrExpr::UProj { .. } => "Expr.uproj",
                            IrExpr::SProj { .. } => "Expr.sproj",
                            IrExpr::Fap { .. } => "Expr.fap",
                            IrExpr::Pap { .. } => "Expr.pap",
                            IrExpr::Ap { .. } => "Expr.ap",
                            IrExpr::Box { .. } => "Expr.box",
                            IrExpr::Unbox { .. } => "Expr.unbox",
                            IrExpr::Lit(_) => "Expr.lit",
                            IrExpr::IsShared { .. } => "Expr.isShared",
                        });
                        "FnBody.vdecl"
                    }
                    IrStmt::JDecl { .. } => "FnBody.jdecl",
                    IrStmt::Set { .. } => "FnBody.set",
                    IrStmt::SetTag { .. } => "FnBody.setTag",
                    IrStmt::USet { .. } => "FnBody.uset",
                    IrStmt::SSet { .. } => "FnBody.sset",
                    IrStmt::Inc { .. } => "FnBody.inc",
                    IrStmt::Dec { .. } => "FnBody.dec",
                    IrStmt::Del { .. } => "FnBody.del",
                };
                count(form);
            }
            let form = match nested.terminal.as_ref() {
                IrTerminal::Case { alts, .. } => {
                    for alt in alts {
                        count(match alt {
                            IrAlt::Ctor { .. } => "Alt.ctor",
                            IrAlt::Default { .. } => "Alt.default",
                        });
                    }
                    "FnBody.case"
                }
                IrTerminal::Ret(_) => "FnBody.ret",
                IrTerminal::Jmp { .. } => "FnBody.jmp",
                IrTerminal::Unreachable => "FnBody.unreachable",
            };
            count(form);
        }
    }
    out
}

fn reference_lib() -> Option<PathBuf> {
    if let Ok(dir) = std::env::var("FLN_REFERENCE_LIB") {
        let path = PathBuf::from(dir);
        return path.is_dir().then_some(path);
    }
    let home = std::env::var("HOME").ok()?;
    let path = PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean");
    path.is_dir().then_some(path)
}

/// The pinned `lean` beside a library directory, when both are there.
/// `FLN_REFERENCE_LEAN` names it for a library that is not a toolchain's own,
/// such as a built corpus (`FLN_REFERENCE_LIB=…/.lake/build/lib/lean`).
fn reference_lean(lib: &Path) -> Option<PathBuf> {
    if let Ok(lean) = std::env::var("FLN_REFERENCE_LEAN") {
        let lean = PathBuf::from(lean);
        return lean.is_file().then_some(lean);
    }
    let lean = lib.parent()?.parent()?.join("bin/lean");
    lean.is_file().then_some(lean)
}

fn ir_files(root: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(dir) = pending.pop() {
        let entries = std::fs::read_dir(&dir)
            .unwrap_or_else(|error| panic!("list {}: {error}", dir.display()));
        for entry in entries {
            let path = entry.expect("directory entry").path();
            if path.is_dir() {
                pending.push(path);
            } else if path.extension().is_some_and(|ext| ext == "ir") {
                out.push(path);
            }
        }
    }
    out.sort();
    out
}

#[derive(Default)]
struct Sweep {
    files: usize,
    declarations: u64,
    compared: u64,
    /// `struct` and `union` IR types among the compared declarations.
    aggregate_types: u64,
    edges: u64,
    forms: BTreeMap<&'static str, u64>,
    /// One row per file that did not open, decode, agree with its own name
    /// list, or agree with the pin's printout.
    rows: Vec<String>,
}

/// Decode every file, then have the pin print the same files and compare each
/// declaration's spelling. `lean` is `None` only where the pin's binary is not
/// beside its library; the decode half still runs.
fn sweep(root: &Path, lean: Option<&Path>) -> Sweep {
    let script = fln_core::checked_workspace_root!().join("scripts/tribunal/ir_dump.lean");
    let mut out = Sweep::default();
    let files = ir_files(root);
    out.files = files.len();
    for batch in files.chunks(64) {
        let mut child = lean.map(|lean| {
            Command::new(lean)
                .arg("--run")
                .arg(&script)
                .args(batch)
                .stdout(Stdio::piped())
                .stderr(Stdio::inherit())
                .spawn()
                .expect("the pinned lean starts")
        });
        let mut pin = child
            .as_mut()
            .map(|child| BufReader::new(child.stdout.take().expect("piped stdout")).lines());
        let mut pin_line = |shown: &str| -> Option<String> {
            let line = pin.as_mut()?.next();
            Some(
                line.unwrap_or_else(|| panic!("{shown}: the pin's printout ended early"))
                    .expect("the pin prints UTF-8"),
            )
        };
        for path in batch {
            let shown = path
                .strip_prefix(root)
                .unwrap_or(path)
                .display()
                .to_string();
            let header = pin_line(&shown);
            if let Some(header) = &header {
                assert_eq!(
                    header,
                    &format!("#file {}", path.display()),
                    "{shown}: out of step"
                );
            }
            // The pin's lines for this file, read whether or not ours decode, so
            // one bad file cannot put every later file out of step.
            let mut theirs = Vec::new();
            if header.is_some() {
                loop {
                    let line = pin_line(&shown).expect("a pin is present");
                    if let Some(count) = line.strip_prefix("#end ") {
                        assert_eq!(
                            count,
                            theirs.len().to_string(),
                            "{shown}: the pin's own count"
                        );
                        break;
                    }
                    theirs.push(line);
                }
            }
            let bytes = std::fs::read(path).unwrap_or_else(|error| panic!("read {shown}: {error}"));
            let (blocks, listed) = match open(&bytes) {
                Ok(opened) => opened,
                Err(error) => {
                    out.rows.push(format!("{shown}\tcontainer\t{error}"));
                    continue;
                }
            };
            let module = match decode_ir(&blocks, IrDecodeLimits::default()) {
                Ok(module) => module,
                Err(error) => {
                    out.rows.push(format!("{shown}\tdecode\t{error}"));
                    continue;
                }
            };
            out.declarations += module.decls.len() as u64;
            let decoded: BTreeSet<&Name> = module.decls.iter().map(IrDecl::name).collect();
            if decoded.len() != module.decls.len() || decoded != listed.iter().collect() {
                out.rows.push(format!(
                    "{shown}\tnames\tdecoded {} distinct of {}, the file lists {}",
                    decoded.len(),
                    module.decls.len(),
                    listed.len()
                ));
            }
            if !module
                .decls
                .windows(2)
                .all(|pair| pair[0].name().quick_lt(pair[1].name()))
            {
                out.rows
                    .push(format!("{shown}\torder\tnot sorted by Name.quickLt"));
            }
            if header.is_some() {
                if theirs.len() != module.decls.len() {
                    out.rows.push(format!(
                        "{shown}\tpin\twe decode {} declarations, the pin prints {}",
                        module.decls.len(),
                        theirs.len()
                    ));
                }
                for (index, (decl, pin_line)) in module.decls.iter().zip(&theirs).enumerate() {
                    let ours = spell_decl(decl);
                    out.compared += 1;
                    out.aggregate_types +=
                        (ours.matches("(struct ").count() + ours.matches("(union ").count()) as u64;
                    if &ours != pin_line {
                        out.rows.push(format!(
                            "{shown}\tpin\tdeclaration {index}: {}",
                            first_difference(&ours, pin_line)
                        ));
                        break;
                    }
                }
            }
            for decl in &module.decls {
                out.edges += decl.callees().len() as u64;
            }
            for (form, count) in census(&module) {
                *out.forms.entry(form).or_insert(0) += count;
            }
        }
        if let Some(mut child) = child {
            let status = child.wait().expect("the pinned lean exits");
            assert!(
                status.success(),
                "the pinned lean failed on a batch: {status}"
            );
        }
    }
    out
}

#[test]
fn the_committed_files_and_printouts_are_the_pins_own() {
    let Some(lib) = reference_lib() else {
        println!(
            "SKIP: no pinned toolchain (set FLN_REFERENCE_LIB); the committed printouts were not re-derived"
        );
        return;
    };
    let Some(lean) = reference_lean(&lib) else {
        println!(
            "SKIP: no `lean` beside {}; the committed printouts were not re-derived",
            lib.display()
        );
        return;
    };
    let script = fln_core::checked_workspace_root!().join("scripts/tribunal/ir_dump.lean");
    for (module_path, bytes, committed) in FIXTURES {
        let path = lib.join(module_path);
        let installed = std::fs::read(&path).expect("the pin has this module");
        assert!(
            installed == bytes,
            "{module_path}: the committed file is not the pin's"
        );
        let output = Command::new(&lean)
            .arg("--run")
            .arg(&script)
            .arg(&path)
            .output()
            .expect("the pinned lean starts");
        assert!(
            output.status.success(),
            "{module_path}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let printed = String::from_utf8(output.stdout).expect("the pin prints UTF-8");
        let declarations: Vec<&str> = printed
            .lines()
            .filter(|line| !line.starts_with('#'))
            .collect();
        let committed: Vec<&str> = committed.lines().collect();
        assert!(
            declarations == committed,
            "{module_path}: the committed printout is stale"
        );
    }
    // The `.olean` fixture is this repository's own file, so only its printout is re-derived.
    let olean =
        fln_core::checked_workspace_root!().join("crates/fln-olean/fixtures/g05_pilot.olean");
    let output = Command::new(&lean)
        .arg("--run")
        .arg(&script)
        .arg(&olean)
        .output()
        .expect("the pinned lean starts");
    assert!(
        output.status.success(),
        "g05_pilot.olean: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let printed = String::from_utf8(output.stdout).expect("the pin prints UTF-8");
    let declarations: Vec<&str> = printed
        .lines()
        .filter(|line| !line.starts_with('#'))
        .collect();
    let committed: Vec<&str> = include_str!("../fixtures/ir/g05_pilot.olean.irdump")
        .lines()
        .collect();
    assert!(
        declarations == committed,
        "g05_pilot.olean: the committed printout is stale"
    );
}

#[test]
#[ignore = "reads every .ir file of the pinned toolchain and has the pin print each; run with --ignored where the pin is installed"]
fn every_ir_file_of_the_pinned_toolchain_decodes_to_what_the_pin_prints() {
    let Some(root) = reference_lib() else {
        println!("SKIP: no pinned toolchain (set FLN_REFERENCE_LIB)");
        return;
    };
    let lean = reference_lean(&root);
    let started = std::time::Instant::now();
    let result = sweep(&root, lean.as_deref());
    for (form, count) in &result.forms {
        println!("FORM\t{form}\t{count}");
    }
    for row in result.rows.iter().take(40) {
        println!("ROW\t{row}");
    }
    println!(
        "SUMMARY\tfiles={}\tdeclarations={}\tcompared_with_pin={}\taggregate_types={}\tfailed_rows={}\tdirect_call_edges={}\tseconds={}",
        result.files,
        result.declarations,
        result.compared,
        result.aggregate_types,
        result.rows.len(),
        result.edges,
        started.elapsed().as_secs()
    );
    assert!(
        result.files > 2_000,
        "found only {} .ir files",
        result.files
    );
    assert!(
        result.rows.is_empty(),
        "{} row(s) disagree",
        result.rows.len()
    );
    // A sweep that compared nothing is the decode half only, and says so.
    assert!(
        lean.is_none() || result.compared == result.declarations,
        "compared {} of {} declarations with the pin",
        result.compared,
        result.declarations
    );
    if lean.is_none() {
        println!("PARTIAL: no `lean` beside the library; nothing was compared with the pin");
    }
}
