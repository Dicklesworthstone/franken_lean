//! What a corpus's compiled code demands of the toolchain, read off the pin's
//! `.ir` files (beads `fln-ir-decoder-call-graph-sjzl` item 5 and
//! `fln-mirror-price-cszo`).
//!
//! The call graph is product code (`fln_olean::ir::graph`) and is tested here on
//! hand-built modules. The pricing is a measurement: it joins that graph to the
//! census partition (`contracts/builtin_partition.tsv`, which says for every
//! constant of the pinned environment whether it is toolchain API, library code
//! or data) and asks what the corpus's own declarations reach, under the two
//! readings of where native code has to begin.
//!
//! * **Reading 1, today's partition.** Stop at the first toolchain-API symbol.
//!   What is reached there is the set of rows a native implementation owes.
//! * **Reading 2, a narrow core.** Look through every declaration that has an
//!   IR body and stop only where there is none: `extern` declarations and
//!   names no module declares. Whether the bodies looked through may run is a
//!   decision this does not take; it prices it.
//!
//! Both are static. A call through a closure value names no target, so each
//! demand set is exact for direct calls and silent about indirect ones.
//!
//! And both count calls only. Compiled code reads a structure's field with
//! `proj` and takes a value apart with `case`; neither names a function, so a
//! projection or a matcher the source mentions is no row here. What those fix
//! is an object layout, which the corpus run reports separately as the
//! constructors the corpus's own code builds and matches on by name.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use fln_core::name::{LeafView, Name};
use fln_olean::ir::graph::{IrCallGraph, IrNodeKind, NodeId};
use fln_olean::ir::{
    IrAlt, IrArg, IrBody, IrDecl, IrDecodeLimits, IrExpr, IrModule, IrStmt, IrTerminal, IrType,
    decode_ir,
};
use fln_olean::region::{OleanView, WalkBudget};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

// ---- hand-built modules ----

/// A function that fully applies `calls` and partially applies `captures`.
fn function(name: &str, calls: &[&str], captures: &[&str]) -> IrDecl {
    let mut stmts = Vec::new();
    for (x, callee) in calls.iter().enumerate() {
        stmts.push(IrStmt::VDecl {
            x: x as u64,
            ty: IrType::Object,
            expr: IrExpr::Fap {
                function: n(callee),
                args: Vec::new(),
            },
        });
    }
    for (x, callee) in captures.iter().enumerate() {
        stmts.push(IrStmt::VDecl {
            x: 1_000 + x as u64,
            ty: IrType::Object,
            expr: IrExpr::Pap {
                function: n(callee),
                args: Vec::new(),
            },
        });
    }
    IrDecl::Function {
        name: n(name),
        params: Vec::new(),
        result: IrType::Object,
        body: IrBody {
            stmts,
            terminal: Box::new(IrTerminal::Ret(IrArg::Erased)),
        },
        sorry_dep: None,
    }
}

fn external(name: &str) -> IrDecl {
    IrDecl::Extern {
        name: n(name),
        params: Vec::new(),
        result: IrType::Object,
        entries: Vec::new(),
    }
}

fn module(decls: Vec<IrDecl>) -> IrModule {
    IrModule {
        decls,
        uninterpreted: Vec::new(),
    }
}

fn names_of(graph: &IrCallGraph, reached: &[bool]) -> Vec<String> {
    let mut out: Vec<String> = (0..graph.len() as NodeId)
        .filter(|id| reached[*id as usize])
        .map(|id| graph.name(id).to_display_string())
        .collect();
    out.sort();
    out
}

#[test]
fn the_graph_keeps_the_first_declaration_and_names_what_nothing_declares() {
    let mut graph = IrCallGraph::new();
    graph
        .add_module(
            "one",
            &module(vec![
                function("a", &["b", "missing"], &["c"]),
                external("c"),
            ]),
        )
        .unwrap();
    graph
        .add_module(
            "two",
            &module(vec![
                function("b", &["a"], &[]),
                function("a", &["zzz"], &[]),
            ]),
        )
        .unwrap();
    let id = |name: &str| graph.node(&n(name)).unwrap();
    assert_eq!(graph.kind(id("a")), IrNodeKind::Function);
    assert_eq!(graph.kind(id("c")), IrNodeKind::Extern);
    assert_eq!(graph.kind(id("missing")), IrNodeKind::Undeclared);
    assert_eq!(graph.module(id("a")), Some("one"));
    assert_eq!(graph.module(id("b")), Some("two"));
    assert_eq!(graph.module(id("missing")), None);
    // Full and partial applications are both edges, in the order the names were first met
    // (a declaration's targets are met in name order).
    let callees: Vec<String> = graph
        .callees(id("a"))
        .iter()
        .map(|callee| graph.name(*callee).to_display_string())
        .collect();
    assert_eq!(callees, ["b", "c", "missing"]);
    // The second `a` is recorded and contributes nothing: `zzz` was never met.
    let repeats: Vec<(String, &str)> = graph
        .duplicates()
        .map(|(id, label)| (graph.name(id).to_display_string(), label))
        .collect();
    assert_eq!(repeats, [("a".to_owned(), "two")]);
    assert!(graph.node(&n("zzz")).is_none());
    assert_eq!(graph.len(), 4);
    assert_eq!(graph.edge_count(), 4);
}

#[test]
fn reach_looks_through_exactly_what_descend_accepts() {
    let mut graph = IrCallGraph::new();
    graph
        .add_module(
            "m",
            &module(vec![
                function("root", &["mid"], &[]),
                function("mid", &["wall", "root"], &[]),
                function("wall", &["behind"], &[]),
                function("behind", &[], &[]),
                function("island", &["behind"], &[]),
            ]),
        )
        .unwrap();
    let id = |name: &str| graph.node(&n(name)).unwrap();
    // Everything accepted: the cycle root -> mid -> root ends, the island stays out.
    let all = graph.reach([id("root")], |_| true);
    assert_eq!(names_of(&graph, &all), ["behind", "mid", "root", "wall"]);
    // A refused node is reached and not looked through.
    let wall = id("wall");
    let stopped = graph.reach([id("root")], |node| node != wall);
    assert_eq!(names_of(&graph, &stopped), ["mid", "root", "wall"]);
    // A refused root is still reached; nothing behind it is.
    let refused_root = graph.reach([id("root")], |_| false);
    assert_eq!(names_of(&graph, &refused_root), ["root"]);
    assert!(graph.reach([], |_| true).iter().all(|reached| !reached));
}

// ---- the census partition ----

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Class {
    /// Declared by a corpus module and not derived from a census constant.
    User,
    Library,
    Data,
    Toolchain,
    /// In no census row and declared by no corpus module.
    Unclassified,
}

struct Partition {
    rows: BTreeMap<Name, (Class, String)>,
}

/// Decode one JSON string literal starting at `text[0] == '"'`; returns the
/// string and the number of bytes consumed.
fn json_string(text: &str) -> Result<(String, usize), String> {
    let mut chars = text.char_indices();
    if chars.next().map(|(_, c)| c) != Some('"') {
        return Err("expected a string literal".into());
    }
    let mut out = String::new();
    while let Some((at, c)) = chars.next() {
        match c {
            '"' => return Ok((out, at + 1)),
            '\\' => match chars.next().map(|(_, c)| c) {
                Some('"') => out.push('"'),
                Some('\\') => out.push('\\'),
                Some('/') => out.push('/'),
                Some('n') => out.push('\n'),
                Some('t') => out.push('\t'),
                Some('r') => out.push('\r'),
                Some('b') => out.push('\u{8}'),
                Some('f') => out.push('\u{c}'),
                Some('u') => {
                    let unit = |chars: &mut std::str::CharIndices<'_>| -> Result<u32, String> {
                        let mut value = 0u32;
                        for _ in 0..4 {
                            let digit = chars
                                .next()
                                .and_then(|(_, c)| c.to_digit(16))
                                .ok_or("bad \\u escape")?;
                            value = value * 16 + digit;
                        }
                        Ok(value)
                    };
                    let high = unit(&mut chars)?;
                    let scalar = if (0xD800..0xDC00).contains(&high) {
                        if chars.next().map(|(_, c)| c) != Some('\\')
                            || chars.next().map(|(_, c)| c) != Some('u')
                        {
                            return Err("lone high surrogate".into());
                        }
                        let low = unit(&mut chars)?;
                        if !(0xDC00..0xE000).contains(&low) {
                            return Err("bad low surrogate".into());
                        }
                        0x10000 + ((high - 0xD800) << 10) + (low - 0xDC00)
                    } else {
                        high
                    };
                    out.push(char::from_u32(scalar).ok_or("escape is not a scalar value")?);
                }
                _ => return Err("unknown escape".into()),
            },
            other => out.push(other),
        }
    }
    Err("unterminated string literal".into())
}

/// A census key: `a`, then `/s"…"` for a string component or `/nN` for a number.
fn census_name(key: &str) -> Result<Name, String> {
    let mut rest = key
        .strip_prefix('a')
        .ok_or("key does not start at anonymous")?;
    let mut name = Name::anonymous();
    while !rest.is_empty() {
        if let Some(text) = rest.strip_prefix("/s") {
            let (component, used) = json_string(text)?;
            name = Name::str(name, component);
            rest = &text[used..];
        } else if let Some(text) = rest.strip_prefix("/n") {
            let digits = text.bytes().take_while(u8::is_ascii_digit).count();
            let value = text[..digits]
                .parse::<u64>()
                .map_err(|_| "numeric component out of range")?;
            name = Name::num(name, value);
            rest = &text[digits..];
        } else {
            return Err("unknown component kind".into());
        }
    }
    Ok(name)
}

fn parse_partition(text: &str) -> Result<Partition, String> {
    let mut rows = BTreeMap::new();
    let mut declared = None;
    for (index, line) in text.lines().enumerate() {
        let fail = |why: &str| format!("partition line {}: {why}", index + 1);
        if let Some(count) = line.strip_prefix("constant_count\t") {
            declared = Some(
                count
                    .parse::<usize>()
                    .map_err(|_| fail("bad constant_count"))?,
            );
        }
        let Some(row) = line.strip_prefix("partition\t") else {
            continue;
        };
        let (key, used) = json_string(row).map_err(|why| fail(&why))?;
        let mut fields = row[used..].split('\t');
        if fields.next() != Some("") {
            return Err(fail("no tab after the key"));
        }
        let class = match fields.next() {
            Some("toolchain-api") => Class::Toolchain,
            Some("library-code") => Class::Library,
            Some("user-facing-data") => Class::Data,
            _ => return Err(fail("unknown partition class")),
        };
        let reason = fields.next().ok_or_else(|| fail("no reason"))?.to_owned();
        let name = census_name(&key).map_err(|why| fail(&why))?;
        if rows.insert(name, (class, reason)).is_some() {
            return Err(fail("a constant is partitioned twice"));
        }
    }
    // A file that lost rows is a different census, not a smaller demand.
    if declared != Some(rows.len()) {
        return Err(format!(
            "partition declares {declared:?} constants and holds {}",
            rows.len()
        ));
    }
    Ok(Partition { rows })
}

/// The constant a compiler-generated name was made from: a specialization
/// `f._at_.site.spec_N` is `f`, and the trailing `_redArg`, `_boxed`, `_lam_N`,
/// `_closed_N` of an auxiliary declaration are dropped.
fn base_constant(name: &Name) -> Name {
    let mut parts = Vec::new();
    let mut cursor = name.clone();
    while !cursor.is_anonymous() {
        parts.push(cursor.clone());
        let parent = cursor.parent();
        cursor = parent;
    }
    parts.reverse();
    let mut base = name.clone();
    for prefix in &parts {
        if matches!(prefix.leaf_view(), LeafView::Str("_at_")) {
            base = prefix.parent();
            break;
        }
    }
    while matches!(base.leaf_view(), LeafView::Str(leaf) if leaf.starts_with('_'))
        && !base.parent().is_anonymous()
    {
        base = base.parent();
    }
    base
}

/// The class of every node, and the census constant each stands for.
fn classify(
    graph: &IrCallGraph,
    partition: &Partition,
    is_corpus: &dyn Fn(&str) -> bool,
) -> (Vec<Class>, Vec<Name>) {
    let mut classes = Vec::with_capacity(graph.len());
    let mut rows = Vec::with_capacity(graph.len());
    for id in 0..graph.len() as NodeId {
        let name = graph.name(id);
        let base = base_constant(name);
        let (class, row) = if let Some((class, _)) = partition.rows.get(name) {
            (*class, name.clone())
        } else if let Some((class, _)) = partition.rows.get(&base) {
            (*class, base)
        } else if graph.module(id).is_some_and(is_corpus) {
            (Class::User, name.clone())
        } else {
            (Class::Unclassified, name.clone())
        };
        classes.push(class);
        rows.push(row);
    }
    (classes, rows)
}

#[derive(Debug, Default, PartialEq, Eq)]
struct Price {
    roots: usize,
    /// Reading 1: toolchain-API constants reached without passing through one.
    native_rows: BTreeSet<Name>,
    /// Reading 1: library constants whose bodies were looked through.
    library_through: BTreeSet<Name>,
    /// Reading 1: names in no census row and no corpus module, reached.
    unclassified: BTreeSet<Name>,
    /// Reading 2: `extern` declarations reached.
    externs: BTreeSet<Name>,
    /// Reading 2: names no module declares, reached.
    undeclared: BTreeSet<Name>,
    /// Reading 2: toolchain-API constants whose IR bodies were looked through.
    toolchain_through: BTreeSet<Name>,
}

fn price(graph: &IrCallGraph, classes: &[Class], rows: &[Name], roots: &[NodeId]) -> Price {
    let mut out = Price {
        roots: roots.len(),
        ..Price::default()
    };
    let through = |id: NodeId| {
        matches!(
            classes[id as usize],
            Class::User | Class::Library | Class::Data
        )
    };
    let first = graph.reach(roots.iter().copied(), through);
    for id in 0..graph.len() as NodeId {
        if !first[id as usize] {
            continue;
        }
        let row = rows[id as usize].clone();
        match classes[id as usize] {
            Class::Toolchain => {
                out.native_rows.insert(row);
            }
            Class::Library if graph.kind(id) == IrNodeKind::Function => {
                {
                    out.library_through.insert(row);
                };
            }
            Class::Unclassified => {
                out.unclassified.insert(row);
            }
            Class::User | Class::Library | Class::Data => {}
        }
    }
    let second = graph.reach(roots.iter().copied(), |id| {
        graph.kind(id) == IrNodeKind::Function
    });
    for id in 0..graph.len() as NodeId {
        if !second[id as usize] {
            continue;
        }
        match graph.kind(id) {
            IrNodeKind::Extern => {
                out.externs.insert(graph.name(id).clone());
            }
            IrNodeKind::Undeclared => {
                out.undeclared.insert(graph.name(id).clone());
            }
            IrNodeKind::Function if classes[id as usize] == Class::Toolchain => {
                {
                    out.toolchain_through.insert(rows[id as usize].clone());
                };
            }
            IrNodeKind::Function => {}
        }
    }
    out
}

fn set(names: &[&str]) -> BTreeSet<Name> {
    names.iter().map(|name| n(name)).collect()
}

/// A small world: user code calls a library function and a specialized copy of
/// a toolchain function that the compiler placed in the user's own module.
fn small_world() -> (IrCallGraph, Partition) {
    let mut graph = IrCallGraph::new();
    graph
        .add_module(
            "toolchain/Lean",
            &module(vec![
                function("Lean.Meta.whnf", &["Lean.Meta.core", "List.map"], &[]),
                function("Lean.Meta.core", &["Lean.prim", "lean_builtin"], &[]),
                external("Lean.prim"),
                function("List.map", &["List.map"], &[]),
                function("Lean.Internal.aux", &[], &[]),
            ]),
        )
        .unwrap();
    graph
        .add_module(
            "corpus/Mathlib",
            &module(vec![
                function(
                    "Mathlib.tac",
                    &["List.map", "Lean.Meta.whnf._at_.Mathlib.tac.spec_0"],
                    &["Mathlib.tac._lam_0"],
                ),
                function("Mathlib.tac._lam_0", &["Lean.Expr.helper"], &[]),
                // Declared by the corpus in the toolchain's namespace: still user code.
                function("Lean.Expr.helper", &["Lean.Internal.aux"], &[]),
                function(
                    "Lean.Meta.whnf._at_.Mathlib.tac.spec_0",
                    &["Lean.Meta.core"],
                    &[],
                ),
                function("Mathlib.unused", &[], &[]),
            ]),
        )
        .unwrap();
    let partition = parse_partition(concat!(
        "constant_count\t5\n",
        "partition\t\"a/s\\\"Lean\\\"/s\\\"Meta\\\"/s\\\"whnf\\\"\"\ttoolchain-api\tlean-toolchain-namespace\n",
        "partition\t\"a/s\\\"Lean\\\"/s\\\"Meta\\\"/s\\\"core\\\"\"\ttoolchain-api\tlean-toolchain-namespace\n",
        "partition\t\"a/s\\\"Lean\\\"/s\\\"prim\\\"\"\ttoolchain-api\textern-intrinsic\n",
        "partition\t\"a/s\\\"List\\\"/s\\\"map\\\"\"\tlibrary-code\tpure-library-source\n",
        "partition\t\"a/s\\\"Lean\\\"/s\\\"Expr\\\"\"\tuser-facing-data\tkernel-generated-data-surface\n",
    ))
    .unwrap();
    (graph, partition)
}

fn corpus(label: &str) -> bool {
    label.starts_with("corpus/")
}

fn user_roots(graph: &IrCallGraph, classes: &[Class]) -> Vec<NodeId> {
    (0..graph.len() as NodeId)
        .filter(|id| classes[*id as usize] == Class::User && graph.module(*id).is_some_and(corpus))
        .collect()
}

#[test]
fn a_census_key_is_read_component_by_component() {
    assert_eq!(census_name("a").unwrap(), Name::anonymous());
    assert_eq!(census_name("a/s\"Nat\"/s\"add\"").unwrap(), n("Nat.add"));
    assert_eq!(
        census_name("a/s\"_private\"/n0/s\"x\\\"y\"").unwrap(),
        Name::str(Name::num(n("_private"), 0), "x\"y")
    );
    assert_eq!(
        census_name("a/s\"\\u00e9\\ud83d\\ude00\"").unwrap(),
        Name::str(Name::anonymous(), "é😀")
    );
    for bad in [
        "",
        "s\"x\"",
        "a/x",
        "a/s\"open",
        "a/n",
        "a/s\"\\q\"",
        "a/s\"\\ud83d\"",
    ] {
        assert!(census_name(bad).is_err(), "{bad:?} must be refused");
    }
    // A partition that lost a row is refused by its own declared count.
    assert!(
        parse_partition("constant_count\t2\npartition\t\"a/s\\\"x\\\"\"\tlibrary-code\tr\n")
            .is_err()
    );
    assert!(
        parse_partition("constant_count\t1\npartition\t\"a/s\\\"x\\\"\"\tnative\tr\n").is_err()
    );
    assert!(
        parse_partition(concat!(
            "constant_count\t2\n",
            "partition\t\"a/s\\\"x\\\"\"\tlibrary-code\tr\n",
            "partition\t\"a/s\\\"x\\\"\"\tlibrary-code\tr\n"
        ))
        .is_err()
    );
}

#[test]
fn a_compiler_generated_name_stands_for_the_constant_it_was_made_from() {
    let base = |text: &str| base_constant(&n(text)).to_display_string();
    assert_eq!(base("Nat.add"), "Nat.add");
    assert_eq!(base("Nat.recAux._redArg._boxed"), "Nat.recAux");
    assert_eq!(base("Nat.instMax._lam_0"), "Nat.instMax");
    assert_eq!(base("Nat.instMax._closed_3"), "Nat.instMax");
    assert_eq!(
        base(
            "Lean.PersistentHashMap.insert._at_.Lean.MVarId.assign._at_.Mathlib.T.f.spec_1.spec_1._boxed"
        ),
        "Lean.PersistentHashMap.insert"
    );
    // A private name keeps its `_private` head: only trailing components go.
    assert_eq!(base("_private.M.foo._redArg"), "_private.M.foo");
    assert_eq!(base("_private"), "_private");
}

#[test]
fn the_two_readings_stop_at_different_walls() {
    let (graph, partition) = small_world();
    let (classes, rows) = classify(&graph, &partition, &corpus);
    let class = |name: &str| classes[graph.node(&n(name)).unwrap() as usize];
    assert_eq!(class("Mathlib.tac"), Class::User);
    assert_eq!(class("Lean.Expr.helper"), Class::User);
    assert_eq!(
        class("Lean.Meta.whnf._at_.Mathlib.tac.spec_0"),
        Class::Toolchain
    );
    assert_eq!(class("List.map"), Class::Library);
    assert_eq!(class("Lean.Internal.aux"), Class::Unclassified);
    assert_eq!(class("lean_builtin"), Class::Unclassified);

    let roots = user_roots(&graph, &classes);
    let found = price(&graph, &classes, &rows, &roots);
    // Roots are the corpus's own declarations; the specialized toolchain copy is not one.
    assert_eq!(found.roots, 4);
    // Reading 1 stops at the specialized copy and charges the constant it was
    // made from; `Lean.Meta.core` and `Lean.prim` lie behind it and are not charged.
    assert_eq!(found.native_rows, set(&["Lean.Meta.whnf"]));
    assert_eq!(found.library_through, set(&["List.map"]));
    assert_eq!(found.unclassified, set(&["Lean.Internal.aux"]));
    // Reading 2 looks through every body and stops where there is none.
    assert_eq!(found.externs, set(&["Lean.prim"]));
    assert_eq!(found.undeclared, set(&["lean_builtin"]));
    assert_eq!(
        found.toolchain_through,
        set(&["Lean.Meta.whnf", "Lean.Meta.core"])
    );

    // Fewer roots, smaller demand: an unused declaration demands nothing.
    let unused = [graph.node(&n("Mathlib.unused")).unwrap()];
    assert_eq!(
        price(&graph, &classes, &rows, &unused),
        Price {
            roots: 1,
            ..Price::default()
        }
    );
}

// ---- the corpus ----

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

/// The data a declaration's own body builds or takes apart by name: the
/// constructors it allocates and the inductive types it matches on. Neither is
/// a call, so neither is an edge; both bake a type's layout into the code.
#[derive(Default)]
struct Shapes {
    declaration: Name,
    constructs: BTreeSet<Name>,
    matches_on: BTreeSet<Name>,
}

fn shapes_of(decl: &IrDecl) -> Option<Shapes> {
    let IrDecl::Function { name, body, .. } = decl else {
        return None;
    };
    let mut out = Shapes {
        declaration: name.clone(),
        ..Shapes::default()
    };
    for nested in body.bodies() {
        for stmt in &nested.stmts {
            if let IrStmt::VDecl {
                expr: IrExpr::Ctor { info, .. },
                ..
            } = stmt
                && !info.name.is_anonymous()
            {
                out.constructs.insert(info.name.clone());
            }
        }
        // The pin rarely fills a `case`'s type name; its arms name their constructors.
        if let IrTerminal::Case { alts, .. } = nested.terminal.as_ref() {
            for alt in alts {
                if let IrAlt::Ctor { info, .. } = alt
                    && !info.name.is_anonymous()
                {
                    out.matches_on.insert(info.name.clone());
                }
            }
        }
    }
    (!out.constructs.is_empty() || !out.matches_on.is_empty()).then_some(out)
}

/// Add every `.ir` file under `root` to the graph, labelled `prefix/relative`.
/// With `shapes`, also record what each declaration builds and matches on.
fn add_tree(
    graph: &mut IrCallGraph,
    prefix: &str,
    root: &Path,
    mut shapes: Option<&mut Vec<Shapes>>,
) -> (usize, u64) {
    let files = ir_files(root);
    let mut declarations = 0u64;
    for path in &files {
        let shown = path
            .strip_prefix(root)
            .unwrap_or(path)
            .display()
            .to_string();
        let bytes = std::fs::read(path).unwrap_or_else(|error| panic!("read {shown}: {error}"));
        let view = OleanView::parse(&bytes).unwrap_or_else(|error| panic!("{shown}: {error}"));
        let blocks = view
            .extension_payloads(WalkBudget::default(), 1 << 30)
            .unwrap_or_else(|error| panic!("{shown}: {error}"));
        let module = decode_ir(&blocks, IrDecodeLimits::default())
            .unwrap_or_else(|error| panic!("{shown}: {error}"));
        declarations += module.decls.len() as u64;
        if let Some(shapes) = shapes.as_deref_mut() {
            shapes.extend(module.decls.iter().filter_map(shapes_of));
        }
        graph
            .add_module(&format!("{prefix}/{shown}"), &module)
            .expect("the corpus fits a node id");
    }
    (files.len(), declarations)
}

fn head(name: &Name, components: usize) -> String {
    let mut parts = Vec::new();
    let mut cursor = name.clone();
    while !cursor.is_anonymous() {
        parts.push(match cursor.leaf_view() {
            LeafView::Str(text) => text.to_owned(),
            LeafView::Num(value) => value.to_string(),
            LeafView::Anonymous => String::new(),
        });
        let parent = cursor.parent();
        cursor = parent;
    }
    parts.reverse();
    // A private name is `_private.<module…>.0.<name…>`: report the name's own head.
    if parts.first().is_some_and(|first| first == "_private")
        && let Some(zero) = parts.iter().position(|part| part == "0")
    {
        parts.drain(..=zero);
    }
    parts.truncate(components);
    parts.join(".")
}

fn histogram<'a>(
    names: impl Iterator<Item = &'a Name>,
    key: impl Fn(&Name) -> String,
) -> Vec<(u64, String)> {
    let mut counts: BTreeMap<String, u64> = BTreeMap::new();
    for name in names {
        *counts.entry(key(name)).or_insert(0) += 1;
    }
    let mut out: Vec<(u64, String)> = counts
        .into_iter()
        .map(|(key, count)| (count, key))
        .collect();
    out.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(&b.1)));
    out
}

fn report(title: &str, found: &Price, partition: &Partition) {
    println!(
        "PRICE\t{title}\troots={}\treading1_native_rows={}\treading1_library_bodies={}\treading1_unclassified={}\treading2_externs={}\treading2_undeclared={}\treading2_toolchain_bodies={}",
        found.roots,
        found.native_rows.len(),
        found.library_through.len(),
        found.unclassified.len(),
        found.externs.len(),
        found.undeclared.len(),
        found.toolchain_through.len(),
    );
    for (count, reason) in histogram(found.native_rows.iter(), |name| {
        partition
            .rows
            .get(name)
            .map_or("?".to_owned(), |(_, reason)| reason.clone())
    }) {
        println!("REASON\t{title}\t{count}\t{reason}");
    }
    for (count, prefix) in histogram(found.native_rows.iter(), |name| head(name, 2))
        .into_iter()
        .take(25)
    {
        println!("PREFIX\t{title}\t{count}\t{prefix}");
    }
}

#[test]
#[ignore = "decodes every .ir file of the pinned toolchain and a built Mathlib corpus and needs the untracked census partition; run with --ignored where all three exist"]
fn the_corpus_demand_on_the_toolchain_under_both_readings() {
    let toolchain = std::env::var("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .ok()
        .or_else(|| {
            let home = std::env::var("HOME").ok()?;
            Some(PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean"))
        });
    let Some(toolchain) = toolchain.filter(|path| path.is_dir()) else {
        println!("SKIP: no pinned toolchain (set FLN_REFERENCE_LIB)");
        return;
    };
    let Some(mathlib) = std::env::var("FLN_MATHLIB_CORPUS")
        .map(PathBuf::from)
        .ok()
        .filter(|path| path.is_dir())
    else {
        println!("SKIP: no corpus (set FLN_MATHLIB_CORPUS to a built Mathlib checkout)");
        return;
    };
    let partition_path = std::env::var("FLN_BUILTIN_PARTITION")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            fln_core::checked_workspace_root!().join("contracts/builtin_partition.tsv")
        });
    let Ok(partition_text) = std::fs::read_to_string(&partition_path) else {
        println!(
            "SKIP: no census partition at {} (set FLN_BUILTIN_PARTITION)",
            partition_path.display()
        );
        return;
    };
    let partition = parse_partition(&partition_text).expect("the census partition parses");
    let started = std::time::Instant::now();

    let mut graph = IrCallGraph::new();
    let (files, declarations) = add_tree(&mut graph, "toolchain", &toolchain, None);
    println!("TREE\ttoolchain\tfiles={files}\tdeclarations={declarations}");
    let mut shapes = Vec::new();
    let mut trees = vec![(
        "corpus/Mathlib".to_owned(),
        mathlib.join(".lake/build/lib/lean"),
    )];
    let packages = mathlib.join(".lake/packages");
    let mut package_dirs: Vec<PathBuf> = std::fs::read_dir(&packages)
        .map(|entries| {
            entries
                .filter_map(|entry| Some(entry.ok()?.path()))
                .collect()
        })
        .unwrap_or_default();
    package_dirs.sort();
    for package in package_dirs {
        let lib = package.join(".lake/build/lib/lean");
        if lib.is_dir() {
            let name = package
                .file_name()
                .expect("package directory name")
                .to_string_lossy()
                .into_owned();
            trees.push((format!("corpus/{name}"), lib));
        }
    }
    for (label, root) in &trees {
        let (files, declarations) = add_tree(&mut graph, label, root, Some(&mut shapes));
        println!("TREE\t{label}\tfiles={files}\tdeclarations={declarations}");
    }
    let duplicates = graph.duplicates().count();
    println!(
        "GRAPH\tnodes={}\tedges={}\trepeated_declarations={duplicates}",
        graph.len(),
        graph.edge_count()
    );
    for (id, label) in graph.duplicates().take(5) {
        println!(
            "REPEAT\t{}\t{label}\tfirst={:?}",
            graph.name(id).to_display_string(),
            graph.module(id)
        );
    }

    let (classes, rows) = classify(&graph, &partition, &corpus);
    let mut by_class: BTreeMap<(Class, IrNodeKind, bool), u64> = BTreeMap::new();
    for id in 0..graph.len() as NodeId {
        let in_corpus = graph.module(id).is_some_and(corpus);
        *by_class
            .entry((classes[id as usize], graph.kind(id), in_corpus))
            .or_insert(0) += 1;
    }
    for ((class, kind, in_corpus), count) in &by_class {
        println!("NODES\t{class:?}\t{kind:?}\tdeclared_in_corpus={in_corpus}\t{count}");
    }

    let all = user_roots(&graph, &classes);
    let everything = price(&graph, &classes, &rows, &all);
    report("all corpus declarations", &everything, &partition);
    let tactic: Vec<NodeId> = all
        .iter()
        .copied()
        .filter(|id| {
            graph
                .module(*id)
                .is_some_and(|label| label.starts_with("corpus/Mathlib/Mathlib/Tactic/"))
        })
        .collect();
    let tactics = price(&graph, &classes, &rows, &tactic);
    report("Mathlib/Tactic modules", &tactics, &partition);

    // How much of the census's toolchain-API class is demanded at all.
    let toolchain_total = partition
        .rows
        .values()
        .filter(|(class, _)| *class == Class::Toolchain)
        .count();
    println!(
        "SHARE\ttoolchain_api_constants={toolchain_total}\tdemanded_reading1={}\tper_mille={}",
        everything.native_rows.len(),
        everything.native_rows.len() * 1000 / toolchain_total.max(1)
    );
    // Toolchain code the pin compiled into the corpus's own modules: specialized copies.
    let mut copies = 0u64;
    let mut copied: BTreeSet<&Name> = BTreeSet::new();
    for id in 0..graph.len() as NodeId {
        if classes[id as usize] == Class::Toolchain && graph.module(id).is_some_and(corpus) {
            copies += 1;
            copied.insert(&rows[id as usize]);
        }
    }
    println!(
        "COPIES\ttoolchain_functions_compiled_into_corpus_modules={copies}\tdistinct_constants={}",
        copied.len()
    );

    // What the corpus's own code builds and takes apart by name. A constructor
    // allocation and a `case` are not calls: they fix an object layout instead.
    // The census files a constructor under data whatever its namespace, so the
    // toolchain's are told apart by the census knowing them and by their head.
    let mut built: BTreeSet<&Name> = BTreeSet::new();
    let mut matched: BTreeSet<&Name> = BTreeSet::new();
    for shape in &shapes {
        let user = graph
            .node(&shape.declaration)
            .is_some_and(|id| classes[id as usize] == Class::User);
        if user {
            built.extend(&shape.constructs);
            matched.extend(&shape.matches_on);
        }
    }
    let touched: BTreeSet<&Name> = built.union(&matched).copied().collect();
    let census_known: Vec<&Name> = touched
        .iter()
        .copied()
        .filter(|name| partition.rows.contains_key(*name))
        .collect();
    let lean: Vec<&Name> = census_known
        .iter()
        .copied()
        .filter(|name| head(name, 1) == "Lean")
        .collect();
    let lean_types: BTreeSet<Name> = lean.iter().map(|name| name.parent()).collect();
    println!(
        "LAYOUT\tconstructors_built={}\tconstructors_matched_on={}\teither={}\tin_the_census={}\tunder_Lean={}\tdistinct_Lean_types={}",
        built.len(),
        matched.len(),
        touched.len(),
        census_known.len(),
        lean.len(),
        lean_types.len()
    );
    for (count, class) in histogram(census_known.iter().copied(), |name| {
        format!("{:?}", partition.rows[name].0)
    }) {
        println!("LAYOUT-CLASS\t{count}\t{class}");
    }
    for (count, prefix) in histogram(lean_types.iter(), |name| head(name, 2))
        .into_iter()
        .take(15)
    {
        println!("LAYOUT-TYPES\t{count}\t{prefix}");
    }

    // Control against an independent derivation: G0-8 listed the toolchain API
    // nine Mathlib modules demand, by having the pin type-check stubs. The
    // whole corpus's reading-1 demand should contain what IR can see of it.
    let control = fln_core::checked_workspace_root!().join("contracts/facade_llevels.ndjson");
    let control = std::fs::read_to_string(&control).expect("the tracked G0-8 demand list");
    let (mut listed, mut demanded, mut behind_a_wall, mut not_toolchain, mut absent) =
        (0u64, 0u64, 0u64, 0u64, 0u64);
    let mut missing = Vec::new();
    for line in control
        .lines()
        .filter(|line| line.contains("\"kind\": \"row\""))
    {
        let at = line.find("\"name\": ").expect("a row has a name") + "\"name\": ".len();
        let (display, _) = json_string(&line[at..]).expect("a row's name is a string");
        let name = Name::from_components(display.split('.'));
        listed += 1;
        if everything.native_rows.contains(&name) {
            demanded += 1;
        } else if everything.toolchain_through.contains(&name) || everything.externs.contains(&name)
        {
            behind_a_wall += 1;
        } else {
            match partition.rows.get(&name) {
                Some((Class::Toolchain, reason)) => {
                    absent += 1;
                    missing.push(format!("{display} ({reason})"));
                }
                Some(_) => not_toolchain += 1,
                None => {
                    absent += 1;
                    missing.push(format!(
                        "{display} (not a census constant under this spelling)"
                    ));
                }
            }
        }
    }
    println!(
        "CONTROL\tg0_8_rows={listed}\tin_reading1_demand={demanded}\treached_only_behind_a_toolchain_symbol={behind_a_wall}\tnot_toolchain_api_in_the_census={not_toolchain}\tnot_reached_at_all={absent}"
    );
    for row in missing.iter().take(20) {
        println!("CONTROL-MISSING\t{row}");
    }

    for name in everything.unclassified.iter().take(12) {
        println!("UNCLASSIFIED\t{}", name.to_display_string());
    }
    for name in everything.undeclared.iter().take(12) {
        println!("UNDECLARED\t{}", name.to_display_string());
    }
    println!("SECONDS\t{}", started.elapsed().as_secs());

    // A broken scan is not a small demand.
    assert!(graph.len() > 500_000, "only {} nodes", graph.len());
    assert!(all.len() > 50_000, "only {} corpus roots", all.len());
    assert!(!everything.native_rows.is_empty() && !everything.externs.is_empty());
    assert!(tactics.native_rows.is_subset(&everything.native_rows));
    assert!(tactics.externs.is_subset(&everything.externs));
}
