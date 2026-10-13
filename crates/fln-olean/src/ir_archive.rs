//! Persist the existing validated IR graph and join it to a census partition.
//!
//! Classification is annotation, never execution authority. Only exact census
//! keys are automatically classified: an unknown name (including a compiler
//! specialization) stays unclassified, NOT user/library code by namespace or
//! suffix guessing. Explicit user names must not override a census row.

use crate::ir::graph::IrNodeKind;
use crate::ir_validate::ValidatedIrCallGraph;
use fln_core::name::Name;
use fln_hash::domain::{Digest, Domain, hash};
use fln_hash::ir_graph::{GraphArchiveError, GraphArchiveLimits, GraphClass, GraphKind, GraphNode, GraphSnapshot};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone)]
pub struct CensusPartition {
    rows: BTreeMap<Name, GraphClass>,
    digest: Digest,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrArchiveError {
    Graph(GraphArchiveError),
    Partition { line: usize, detail: &'static str },
    NameKey(&'static str),
    UserOverridesCensus(Name),
    UnknownUser(Name),
}

impl IrArchiveError {
    pub fn is_resource(&self) -> bool {
        matches!(self, Self::Graph(error) if error.is_resource())
    }
}

impl std::fmt::Display for IrArchiveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "IR graph classification: {self:?}")
    }
}

impl std::error::Error for IrArchiveError {}
impl From<GraphArchiveError> for IrArchiveError {
    fn from(value: GraphArchiveError) -> Self { Self::Graph(value) }
}

fn json_string(text: &str) -> Result<(String, usize), &'static str> {
    let mut chars = text.char_indices();
    if chars.next().map(|(_, c)| c) != Some('"') { return Err("expected JSON string"); }
    let mut out = String::new();
    while let Some((at, c)) = chars.next() {
        match c {
            '"' => return Ok((out, at + 1)),
            '\\' => match chars.next().map(|(_, c)| c) {
                Some('"') => out.push('"'), Some('\\') => out.push('\\'), Some('/') => out.push('/'),
                Some('n') => out.push('\n'), Some('t') => out.push('\t'), Some('r') => out.push('\r'),
                Some('b') => out.push('\u{8}'), Some('f') => out.push('\u{c}'),
                Some('u') => {
                    let unit = |chars: &mut std::str::CharIndices<'_>| -> Result<u32, &'static str> {
                        let mut value = 0;
                        for _ in 0..4 {
                            let digit = chars.next().and_then(|(_, c)| c.to_digit(16)).ok_or("bad Unicode escape")?;
                            value = value * 16 + digit;
                        }
                        Ok(value)
                    };
                    let high = unit(&mut chars)?;
                    let scalar = if (0xD800..0xDC00).contains(&high) {
                        if chars.next().map(|(_, c)| c) != Some('\\') || chars.next().map(|(_, c)| c) != Some('u') {
                            return Err("lone high surrogate");
                        }
                        let low = unit(&mut chars)?;
                        if !(0xDC00..0xE000).contains(&low) { return Err("invalid low surrogate"); }
                        0x10000 + ((high - 0xD800) << 10) + low - 0xDC00
                    } else { high };
                    out.push(char::from_u32(scalar).ok_or("invalid Unicode scalar")?);
                }
                _ => return Err("unknown JSON escape"),
            },
            c if c < '\u{20}' => return Err("raw control character in JSON string"),
            c => out.push(c),
        }
    }
    Err("unterminated JSON string")
}

fn parse_key(key: &str, components_left: &mut u64) -> Result<Name, IrArchiveError> {
    let mut rest = key.strip_prefix('a').ok_or(IrArchiveError::NameKey("expected anonymous key root"))?;
    let mut name = Name::anonymous();
    while !rest.is_empty() {
        *components_left = components_left.checked_sub(1)
            .ok_or(GraphArchiveError::Limit("partition name components"))?;
        if let Some(text) = rest.strip_prefix("/s") {
            let (component, used) = json_string(text).map_err(IrArchiveError::NameKey)?;
            name = Name::str(name, component);
            rest = &text[used..];
        } else if let Some(text) = rest.strip_prefix("/n") {
            let digits = text.bytes().take_while(u8::is_ascii_digit).count();
            let value = text[..digits].parse::<u64>()
                .map_err(|_| IrArchiveError::NameKey("invalid or out-of-range numeric component"))?;
            name = Name::num(name, value);
            rest = &text[digits..];
        } else { return Err(IrArchiveError::NameKey("unknown name component")); }
    }
    Ok(name)
}

/// Exact census-key syntax: `a/s"Lean"/s"Meta"/n0`. Unlike splitting on dots,
/// this distinguishes string/numeric components and dots inside a component.
pub fn parse_name_key(key: &str, max_bytes: usize, max_components: u64) -> Result<Name, IrArchiveError> {
    if key.len() > max_bytes { return Err(GraphArchiveError::Limit("name-key bytes").into()); }
    parse_key(key, &mut max_components.clone())
}

impl CensusPartition {
    /// Parse the generated partition TSV consumed by the repository's IR demand
    /// measurement. Metadata rows are not interpreted; partition keys, classes,
    /// nonempty reasons, duplicate keys, and exactly one matching constant_count
    /// are checked. The complete input bytes are fingerprinted, including metadata.
    pub fn parse(text: &str, limits: GraphArchiveLimits) -> Result<Self, IrArchiveError> {
        if text.len() > limits.max_bytes { return Err(GraphArchiveError::Limit("partition bytes").into()); }
        let mut rows = BTreeMap::new();
        let mut declared = None;
        let mut components = limits.max_name_components;
        for (index, line) in text.lines().enumerate() {
            let fail = |detail| IrArchiveError::Partition { line: index + 1, detail };
            if let Some(value) = line.strip_prefix("constant_count\t") {
                if declared.is_some() { return Err(fail("duplicate constant_count")); }
                let value = value.parse::<usize>().map_err(|_| fail("invalid constant_count"))?;
                if value > limits.max_nodes { return Err(GraphArchiveError::Limit("partition rows").into()); }
                declared = Some(value);
                continue;
            }
            let Some(row) = line.strip_prefix("partition\t") else { continue; };
            if rows.len() >= limits.max_nodes { return Err(GraphArchiveError::Limit("partition rows").into()); }
            let (key, used) = json_string(row).map_err(fail)?;
            let tail = row[used..].strip_prefix('\t').ok_or_else(|| fail("missing tab after key"))?;
            let mut fields = tail.split('\t');
            let class = match fields.next() {
                Some("toolchain-api") => GraphClass::ToolchainApi,
                Some("library-code") => GraphClass::LibraryCode,
                Some("user-facing-data") => GraphClass::Data,
                _ => return Err(fail("unknown census class")),
            };
            if fields.next().is_none_or(str::is_empty) { return Err(fail("missing classification reason")); }
            // Other generated columns are metadata; no column can override class.
            let name = parse_key(&key, &mut components)?;
            if rows.insert(name, class).is_some() { return Err(fail("duplicate census key")); }
        }
        if declared != Some(rows.len()) {
            return Err(IrArchiveError::Partition { line: 0, detail: "constant_count does not match partition rows" });
        }
        Ok(Self { rows, digest: hash(Domain::IrPartition, text.as_bytes()) })
    }

    pub fn digest(&self) -> Digest { self.digest }
    pub fn len(&self) -> usize { self.rows.len() }
    pub fn is_empty(&self) -> bool { self.rows.is_empty() }
    pub fn get(&self, name: &Name) -> Option<GraphClass> { self.rows.get(name).copied() }
}

/// Canonicalize the EXISTING validated graph into data-only snapshot rows.
/// Module labels and original node numbering deliberately do not enter the
/// identity. All named edges, including partial applications, are retained.
/// There is no conversion back from archive data to a validation/admission token.
pub fn snapshot_graph(
    checked: &ValidatedIrCallGraph,
    partition: Option<&CensusPartition>,
    explicit_users: &BTreeSet<Name>,
    limits: GraphArchiveLimits,
) -> Result<GraphSnapshot, IrArchiveError> {
    let graph = checked.graph();
    if graph.len() > limits.max_nodes || u32::try_from(graph.len()).is_err() {
        return Err(GraphArchiveError::Limit("nodes").into());
    }
    if graph.edge_count() > limits.max_edges { return Err(GraphArchiveError::Limit("edges").into()); }
    if explicit_users.len() > limits.max_nodes { return Err(GraphArchiveError::Limit("user names").into()); }
    for name in explicit_users {
        if partition.is_some_and(|p| p.get(name).is_some()) { return Err(IrArchiveError::UserOverridesCensus(name.clone())); }
        if graph.node(name).is_none() { return Err(IrArchiveError::UnknownUser(name.clone())); }
    }
    let mut ids = Vec::new();
    ids.try_reserve_exact(graph.len()).map_err(|_| GraphArchiveError::Limit("snapshot allocation"))?;
    ids.extend(0..graph.len() as u32);
    ids.sort_unstable_by(|a,b| graph.name(*a).cmp(graph.name(*b)));
    let mut remap = Vec::new();
    remap.try_reserve_exact(graph.len()).map_err(|_| GraphArchiveError::Limit("snapshot allocation"))?;
    remap.resize(graph.len(),0u32);
    for (rank, id) in ids.iter().enumerate() { remap[*id as usize] = rank as u32; }
    let mut nodes = Vec::new();
    nodes.try_reserve_exact(graph.len()).map_err(|_| GraphArchiveError::Limit("snapshot allocation"))?;
    for id in ids {
        let name = graph.name(id).clone();
        let (class, census_name) = if let Some(class) = partition.and_then(|p| p.get(&name)) {
            (class,Some(name.clone()))
        } else if explicit_users.contains(&name) {
            (GraphClass::User,None)
        } else { (GraphClass::Unclassified,None) };
        let kind = match graph.kind(id) {
            IrNodeKind::Function => GraphKind::Function,
            IrNodeKind::Extern => GraphKind::Extern,
            IrNodeKind::Undeclared => GraphKind::SignatureOnly,
        };
        let mut callees = Vec::new();
        callees.try_reserve_exact(graph.callees(id).len()).map_err(|_| GraphArchiveError::Limit("snapshot allocation"))?;
        callees.extend(graph.callees(id).iter().map(|id| remap[*id as usize]));
        callees.sort_unstable();
        nodes.push(GraphNode { name,kind,class,census_name,callees });
    }
    GraphSnapshot::new(nodes, checked.summary().dynamic_calls, partition.map(CensusPartition::digest), limits)
        .map_err(IrArchiveError::Graph)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{IrArg,IrBody,IrDecl,IrExpr,IrModule,IrParam,IrStmt,IrTerminal,IrType};
    use crate::ir_validate::{IrValidationLimits,build_validated_ir_call_graph};

    const PARTITION: &str = concat!(
        "constant_count\t2\n",
        "partition\t\"a/s\\\"Native\\\"\"\ttoolchain-api\textern-intrinsic\n",
        "partition\t\"a/s\\\"Library\\\"\"\tlibrary-code\tpure-library-source\n",
    );
    fn n(text: &str) -> Name { Name::from_components(text.split('.')) }
    fn function(name: &str, calls: &[&str]) -> IrDecl {
        IrDecl::Function {
            name:n(name),params:vec![],result:IrType::Erased,sorry_dep:None,
            body:IrBody {
                stmts:calls.iter().enumerate().map(|(x,name)| IrStmt::VDecl {
                    x:x as u64,ty:IrType::Erased,expr:IrExpr::Fap { function:n(name),args:vec![] },
                }).collect(), terminal:Box::new(IrTerminal::Ret(IrArg::Erased)),
            },
        }
    }
    fn module(decls: Vec<IrDecl>) -> IrModule { IrModule { decls,uninterpreted:vec![] } }
    fn partition() -> CensusPartition { CensusPartition::parse(PARTITION,GraphArchiveLimits::default()).unwrap() }

    #[test]
    fn census_keys_preserve_component_types_unicode_and_escaping() {
        let key = "a/s\"a.b\"/n42/s\"\\uD83D\\uDE00\\n\"";
        let actual = parse_name_key(key,1024,3).unwrap();
        let expected = Name::str(Name::num(Name::str(Name::anonymous(),"a.b"),42),"😀\n");
        assert_eq!(actual,expected);
        assert_ne!(parse_name_key("a/s\"42\"",1024,1).unwrap(),parse_name_key("a/n42",1024,1).unwrap());
        for key in ["", "b", "a/n", "a/n18446744073709551616", "a/x1", "a/s\"raw\n\"", "a/s\"\\uD800\"", "a/s\"\\uDC00\"", "a/s\"x\"junk"] {
            assert!(parse_name_key(key,1024,10).is_err(),"accepted {key:?}");
        }
    }
    #[test]
    fn name_key_resource_limits_are_explicit() {
        assert!(parse_name_key("a/s\"a\"",1,1).unwrap_err().is_resource());
        assert!(parse_name_key("a/s\"a\"/s\"b\"",1024,1).unwrap_err().is_resource());
        assert!(parse_name_key("a",1,0).unwrap().is_anonymous());
    }
    #[test]
    fn partition_counts_duplicates_and_classes_are_checked() {
        assert_eq!(partition().len(),2);
        assert_eq!(partition().get(&n("Native")),Some(GraphClass::ToolchainApi));
        for text in [PARTITION.replace("constant_count\t2","constant_count\t3"),
            PARTITION.replace("toolchain-api","unknown"),
            format!("{PARTITION}constant_count\t2\n"),
            format!("{}{}",PARTITION,PARTITION.lines().nth(1).unwrap()),
            PARTITION.lines().skip(1).collect::<Vec<_>>().join("\n")] {
            assert!(CensusPartition::parse(&text,GraphArchiveLimits::default()).is_err());
        }
    }
    #[test]
    fn partition_limits_do_not_become_malformedness_verdicts() {
        let exact = GraphArchiveLimits {max_bytes:PARTITION.len(),max_nodes:2,max_name_components:2,..GraphArchiveLimits::default()};
        CensusPartition::parse(PARTITION,exact).unwrap();
        for limits in [GraphArchiveLimits {max_bytes:exact.max_bytes-1,..exact},
            GraphArchiveLimits {max_nodes:1,..exact},GraphArchiveLimits {max_name_components:1,..exact}] {
            assert!(CensusPartition::parse(PARTITION,limits).unwrap_err().is_resource());
        }
    }
    #[test]
    fn snapshot_is_independent_of_module_labels_and_enumeration() {
        let a = module(vec![function("User", &["Library"])]);
        let b = module(vec![function("Library", &["Native"]),function("Native", &[])]);
        let first = build_validated_ir_call_graph(&[("/host/one",&a),("/host/two",&b)],&BTreeMap::new(),IrValidationLimits::default()).unwrap();
        let second = build_validated_ir_call_graph(&[("different",&b),("also-different",&a)],&BTreeMap::new(),IrValidationLimits::default()).unwrap();
        let p = partition(); let users = BTreeSet::from([n("User")]); let limits = GraphArchiveLimits::default();
        let first = snapshot_graph(&first,Some(&p),&users,limits).unwrap();
        let second = snapshot_graph(&second,Some(&p),&users,limits).unwrap();
        assert_eq!(first.encode(limits).unwrap(),second.encode(limits).unwrap());
        assert_eq!(first.unclassified_count(),0);
        let bytes = first.encode(limits).unwrap();
        let loaded = GraphSnapshot::decode(&bytes.bytes,limits).unwrap();
        assert_eq!(loaded.reach(&[n("User")], |row|row.class != GraphClass::ToolchainApi,100).unwrap().len(),3);
    }
    #[test]
    fn unknown_specializations_are_not_guessed_to_be_user_code() {
        let module = module(vec![function("Native._at_.User.spec_0", &[])]);
        let checked = build_validated_ir_call_graph(&[("corpus/User",&module)],&BTreeMap::new(),IrValidationLimits::default()).unwrap();
        let snapshot = snapshot_graph(&checked,Some(&partition()),&BTreeSet::new(),GraphArchiveLimits::default()).unwrap();
        assert_eq!(snapshot.nodes()[0].class,GraphClass::Unclassified);
        assert_eq!(snapshot.nodes()[0].census_name,None);
    }
    #[test]
    fn explicit_user_annotations_cannot_override_census_or_invent_nodes() {
        let module = module(vec![function("Native", &[])]);
        let checked = build_validated_ir_call_graph(&[("m",&module)],&BTreeMap::new(),IrValidationLimits::default()).unwrap();
        assert!(matches!(snapshot_graph(&checked,Some(&partition()),&BTreeSet::from([n("Native")]),GraphArchiveLimits::default()),Err(IrArchiveError::UserOverridesCensus(_))));
        assert!(matches!(snapshot_graph(&checked,None,&BTreeSet::from([n("missing")]),GraphArchiveLimits::default()),Err(IrArchiveError::UnknownUser(_))));
    }
    #[test]
    fn partial_and_dynamic_calls_survive_snapshot_conversion() {
        let mut entry = function("Entry", &[]);
        if let IrDecl::Function {body,..} = &mut entry {
            body.stmts = vec![
                IrStmt::VDecl {x:0,ty:IrType::Object,expr:IrExpr::Pap {function:n("Native"),args:vec![]}},
                IrStmt::VDecl {x:1,ty:IrType::Object,expr:IrExpr::Ap {x:0,args:vec![]}},
            ];
        }
        let external = IrDecl::Extern {name:n("Native"),params:vec![IrParam {x:0,borrow:false,ty:IrType::Object}],result:IrType::Object,entries:vec![]};
        let module = module(vec![entry,external]);
        let checked = build_validated_ir_call_graph(&[("m",&module)],&BTreeMap::new(),IrValidationLimits::default()).unwrap();
        let graph = snapshot_graph(&checked,Some(&partition()),&BTreeSet::new(),GraphArchiveLimits::default()).unwrap();
        assert_eq!(graph.edge_count(),1); assert_eq!(graph.dynamic_calls(),1);
        let root = graph.find(&n("Entry")).unwrap(); let native = graph.find(&n("Native")).unwrap();
        assert_eq!(graph.nodes()[root as usize].callees,vec![native]);
        assert_eq!(graph.nodes()[native as usize].kind,GraphKind::Extern);
    }
    #[test]
    fn partition_fingerprint_covers_metadata_as_well_as_classification() {
        assert_ne!(partition().digest(),CensusPartition::parse(&format!("epoch\tother\n{PARTITION}"),GraphArchiveLimits::default()).unwrap().digest());
    }
}
