//! Extract equality-decision comparison data from the retained pinned Prelude.
//! Run with `cargo run -p fln --example extract_text_equality -- String` (or Char/Nat).
//! Nat emits separate sections for its native equality and ordering decisions.
//! `StringBootstrap` reads `FLN_REFERENCE_LIB` and emits the complete native
//! String adapter inventory, including the per-operation membership mask.
//! Writes only the requested inventory to stdout; never changes a logical declaration.
#![forbid(unsafe_code)]
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, Engine, Environment, ExprNode, KVMap, Name, OleanCheckLimits, OleanDecodeLimits,
    OleanModuleInput,
};
use fln_core::name::LeafView;
use fln_env::constants::ConstantInfo;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::path::PathBuf;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn dependencies(environment: &Environment, root: &str) -> Result<BTreeSet<Name>, String> {
    dependency_closure(
        environment,
        vec![n("Decidable.decide"), n(root), n("Bool"), n("Nat.beq")],
    )
}

fn dependency_closure(
    environment: &Environment,
    mut pending: Vec<Name>,
) -> Result<BTreeSet<Name>, String> {
    let mut found = BTreeSet::new();
    while let Some(label) = pending.pop() {
        if !found.insert(label.clone()) {
            continue;
        }
        let info = environment
            .find(&label)
            .ok_or_else(|| format!("missing {}", label.to_display_string()))?;
        let mut expressions = vec![&info.constant_val().type_];
        match info {
            ConstantInfo::Defn(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Opaque(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Thm(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Induct(value) => {
                pending.extend(value.all.iter().cloned());
                pending.extend(value.ctors.iter().cloned());
            }
            ConstantInfo::Ctor(value) => pending.push(value.induct.clone()),
            ConstantInfo::Rec(value) => {
                pending.extend(value.all.iter().cloned());
                pending.extend(value.rules.iter().map(|rule| rule.ctor.clone()));
                expressions.extend(value.rules.iter().map(|rule| &rule.rhs));
            }
            ConstantInfo::Axiom(_) | ConstantInfo::Quot(_) => {}
        }
        let mut visited = HashSet::new();
        while let Some(expression) = expressions.pop() {
            if !visited.insert(expression.allocation_identity()) {
                continue;
            }
            match expression.node() {
                ExprNode::Const { name, .. } => pending.push(name.clone()),
                ExprNode::App { f, a } => expressions.extend([f, a]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => expressions.extend([binder_type, body]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => expressions.extend([type_, value, body]),
                ExprNode::Proj {
                    struct_name, expr, ..
                } => {
                    pending.push(struct_name.clone());
                    expressions.push(expr);
                }
                ExprNode::MData { expr, .. } => expressions.push(expr),
                _ => {}
            }
        }
    }
    Ok(found)
}

fn encoded(label: &Name) -> String {
    let mut name = label.clone();
    let mut parts = Vec::new();
    while !name.is_anonymous() {
        assert!(!name.component_overflowed(), "overflowed name component");
        parts.push(match name.leaf_view() {
            LeafView::Str(part) => {
                assert!(!part.contains(['/', '\t', '\n']));
                format!("s:{part}")
            }
            LeafView::Num(part) => format!("n:{part}"),
            LeafView::Anonymous => unreachable!(),
        });
        name = name.parent();
    }
    parts.reverse();
    parts.join("/")
}

/// Membership order is checked against Operation::ALL by the independent
/// closure walk in source_intrinsics::string_bootstrap::tests.
const STRING_BOOTSTRAP: [&str; 38] = [
    "String.utf8ByteSize",
    "String.Internal.posOf",
    "String.Internal.offsetOfPos",
    "String.Internal.extract",
    "String.Internal.next",
    "String.Internal.pushn",
    "String.Internal.foldl",
    "String.Internal.isEmpty",
    "String.Internal.get",
    "String.Pos.Raw.get",
    "String.Pos.Raw.set",
    "String.decodeChar",
    "String.getUTF8Byte",
    "String.Pos.Raw.next'",
    "String.Pos.Raw.extract",
    "String.Pos.set",
    "String.extract",
    "String.toList",
    "String.get",
    "String.get'",
    "String.Pos.Raw.get'",
    "String.next'",
    "String.Pos.next",
    "String.set",
    "String.getUtf8Byte",
    "String.Internal.getUTF8Byte",
    "String.data",
    "String.Internal.front",
    "String.Pos.Raw.Internal.min",
    "String.Pos.Raw.Internal.sub",
    "Substring.Raw.Internal.toString",
    "Substring.Raw.Internal.drop",
    "Substring.Raw.Internal.front",
    "Substring.Raw.Internal.extract",
    "Substring.Raw.Internal.beq",
    "Substring.Raw.Internal.isEmpty",
    "Substring.Raw.Internal.get",
    "Substring.Raw.Internal.prev",
];

/// The same defining-module snapshots as the pinned comparison fixture.
/// Duplicate declarations must agree, and every root's complete
/// type/body/structural graph must close within this input set.
const STRING_BOOTSTRAP_MODULES: [&str; 81] = [
    "Init/ByCases",
    "Init/Classical",
    "Init/Control/Id",
    "Init/Control/Lawful/Basic",
    "Init/Core",
    "Init/Data/Array/Basic",
    "Init/Data/Array/Bootstrap",
    "Init/Data/Array/Extract",
    "Init/Data/Array/Lemmas",
    "Init/Data/Array/Set",
    "Init/Data/BEq",
    "Init/Data/BitVec/Basic",
    "Init/Data/BitVec/BasicAux",
    "Init/Data/BitVec/Bootstrap",
    "Init/Data/BitVec/Lemmas",
    "Init/Data/Bool",
    "Init/Data/ByteArray/Basic",
    "Init/Data/ByteArray/Bootstrap",
    "Init/Data/ByteArray/Lemmas",
    "Init/Data/Cast",
    "Init/Data/Char/Basic",
    "Init/Data/Int/Basic",
    "Init/Data/Int/DivMod/Basic",
    "Init/Data/Int/DivMod/Bootstrap",
    "Init/Data/Int/Lemmas",
    "Init/Data/Int/Order",
    "Init/Data/Int/Pow",
    "Init/Data/List/Basic",
    "Init/Data/List/BasicAux",
    "Init/Data/List/Control",
    "Init/Data/List/Lemmas",
    "Init/Data/List/Nat/TakeDrop",
    "Init/Data/List/Sublist",
    "Init/Data/List/TakeDrop",
    "Init/Data/List/ToArray",
    "Init/Data/Nat/Basic",
    "Init/Data/Nat/Bitwise/Basic",
    "Init/Data/Nat/Bitwise/Lemmas",
    "Init/Data/Nat/Div/Basic",
    "Init/Data/Nat/Div/Lemmas",
    "Init/Data/Nat/Dvd",
    "Init/Data/Nat/Gcd",
    "Init/Data/Nat/Lemmas",
    "Init/Data/Nat/Linear",
    "Init/Data/Nat/MinMax",
    "Init/Data/Nat/Order",
    "Init/Data/NeZero",
    "Init/Data/Option/Basic",
    "Init/Data/Option/Instances",
    "Init/Data/Option/Lemmas",
    "Init/Data/Order/Classes",
    "Init/Data/Order/Factories",
    "Init/Data/Order/Lemmas",
    "Init/Data/RArray",
    "Init/Data/Repr",
    "Init/Data/String/Basic",
    "Init/Data/String/Bootstrap",
    "Init/Data/String/Decode",
    "Init/Data/String/Defs",
    "Init/Data/String/Modify",
    "Init/Data/String/PosRaw",
    "Init/Data/ToString/Basic",
    "Init/Data/UInt/Basic",
    "Init/Data/UInt/BasicAux",
    "Init/Data/UInt/Bitwise",
    "Init/Data/UInt/Lemmas",
    "Init/Ext",
    "Init/GetElem",
    "Init/Omega/Coeffs",
    "Init/Omega/Constraint",
    "Init/Omega/Int",
    "Init/Omega/IntList",
    "Init/Omega/LinearCombo",
    "Init/Omega/Logic",
    "Init/Prelude",
    "Init/PropLemmas",
    "Init/SimpLemmas",
    "Init/SizeOf",
    "Init/Tactics",
    "Init/Util",
    "Init/WF",
];

fn string_bootstrap_inventory() -> Result<(), String> {
    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .ok_or_else(|| {
            "StringBootstrap requires FLN_REFERENCE_LIB at the pinned lib/lean".to_owned()
        })?;
    let limits = OleanDecodeLimits::new(256 << 20);
    let mut constants = BTreeMap::new();
    let mut owners: BTreeMap<Name, BTreeSet<Name>> = BTreeMap::new();
    for module in STRING_BOOTSTRAP_MODULES {
        let path = library.join(module).with_extension("olean");
        let module = n(&module.replace('/', "."));
        let read = |path: &std::path::Path| {
            std::fs::read(path).map_err(|error| format!("{}: {error}", path.display()))
        };
        let public = read(&path)?;
        let server = read(&path.with_extension("olean.server"))?;
        let private = read(&path.with_extension("olean.private"))?;
        let decoded = fln::decode_olean_module_artifacts(&public, &server, &private, limits)
            .map_err(|error| format!("{} declarations: {error:?}", path.display()))?;
        for info in decoded.constants {
            owners
                .entry(info.name().clone())
                .or_default()
                .insert(module.clone());
            if let Some(previous) = constants.insert(info.name().clone(), info.clone())
                && previous != info
            {
                return Err(format!(
                    "inconsistent declaration {} in {:?}",
                    info.name().to_display_string(),
                    owners[info.name()]
                ));
            }
        }
    }
    // Extraction compares data. It neither admits a module nor installs any
    // native binding; production still checks every digest and exact extern.
    let mut environment = Environment::new();
    for info in constants.into_values() {
        environment = environment
            .add_decl(info)
            .map_err(|error| format!("assemble comparison environment: {error:?}"))?;
    }
    let mut rows: BTreeMap<Name, u64> = BTreeMap::new();
    let mut counts = Vec::new();
    for (index, root) in STRING_BOOTSTRAP.into_iter().enumerate() {
        let mut roots = vec![n(root)];
        // Char/UInt8/proof adapters reconstruct checked Bool proof slots.
        // This is the same explicit seed used by the existing inventory.
        if index >= 8 || matches!(index, 1 | 5 | 6) {
            roots.push(n("Bool"));
        }
        let found = dependency_closure(&environment, roots)?;
        counts.push((root, found.len()));
        for label in found {
            *rows.entry(label).or_default() |= 1u64 << index;
        }
    }
    // Resolve the entire graph before emitting any records: failed extraction
    // must not leave a partial inventory that could be mistaken for complete.
    let mut defining = BTreeSet::new();
    let mut output = Vec::new();
    for (label, membership) in rows {
        defining.extend(owners[&label].iter().cloned());
        output.push(format!(
            "{membership:07x}\t{}\t{}",
            encoded(&label),
            environment.entry(&label).unwrap().digest().to_hex()
        ));
    }
    for (root, count) in counts {
        eprintln!("{root}: {count} complete type/body/structural dependencies");
    }
    eprintln!(
        "{} inventory declarations in {} defining modules",
        output.len(),
        defining.len()
    );
    for module in defining {
        eprintln!("module: {}", module.to_display_string());
    }
    for row in output {
        println!("{row}");
    }
    Ok(())
}

fn main() -> Result<(), String> {
    let carrier = std::env::args()
        .nth(1)
        .ok_or_else(|| "expected String, Char, Nat or StringBootstrap".to_owned())?;
    if !matches!(
        carrier.as_str(),
        "String" | "Char" | "Nat" | "StringBootstrap"
    ) {
        return Err("expected String, Char, Nat or StringBootstrap".to_owned());
    }
    std::thread::Builder::new()
        .stack_size(128 << 20)
        .spawn(move || {
            if carrier == "StringBootstrap" {
                return string_bootstrap_inventory();
            }
            let module = n("Init.Prelude");
            let imported = Engine::builder()
                .build_empty()
                .import_olean_modules_for_source(
                    &[OleanModuleInput {
                        name: &module,
                        artifact: include_bytes!(
                            "../../fln-conformance/fixtures/tag_attributes/prelude.olean"
                        ),
                        server_artifact: Some(include_bytes!(
                            "../../fln-conformance/fixtures/tag_attributes/prelude.olean.server"
                        )),
                        private_artifact: Some(include_bytes!(
                            "../../fln-conformance/fixtures/tag_attributes/prelude.olean.private"
                        )),
                    }],
                    std::slice::from_ref(&module),
                    &KVMap::new(),
                    SourceOleanImportLimits::new(OleanCheckLimits::new(
                        16 << 20,
                        Budget::for_stack_bytes(128 << 20),
                    )),
                )
                .unwrap()
                .into_complete()
                .expect("the actual Prelude must be council-admitted");
            let environment = imported.engine.environment();
            let roots = if carrier == "Nat" {
                vec![
                    "Nat.decEq".to_owned(),
                    "Nat.decLe".to_owned(),
                    "Nat.decLt".to_owned(),
                ]
            } else {
                vec![format!("instDecidableEq{carrier}")]
            };
            // Find every closure before emitting any records. A missing input
            // must not leave a partial inventory that looks complete.
            let groups = roots
                .into_iter()
                .map(|root| dependencies(environment, &root).map(|found| (root, found)))
                .collect::<Result<Vec<_>, _>>()?;
            for (root, found) in groups {
                eprintln!(
                    "{root}: {} complete type/body/structural dependencies",
                    found.len()
                );
                if carrier == "Nat" {
                    println!("@{root}");
                }
                for label in found {
                    println!(
                        "{}\t{}",
                        encoded(&label),
                        environment.entry(&label).unwrap().digest().to_hex()
                    );
                }
                if carrier == "Nat" {
                    println!();
                }
            }
            Ok(())
        })
        .map_err(|error| format!("could not spawn equality extractor: {error}"))?
        .join()
        .map_err(|_| "equality extraction worker panicked".to_owned())?
}
