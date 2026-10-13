//! Canonical, integrity-checked storage of a static IR call graph.
//!
//! A snapshot is DATA, not a checked declaration, execution permit, complete
//! runtime call graph, or authenticated census. Its digest detects byte changes;
//! authenticity requires a separately trusted expected digest. Names use the
//! shared canonical Name codec, never their potentially ambiguous display text.
//! Host paths, allocation IDs, traversal order and timings are not serialized.

use crate::canon::{
    CanonError, CanonReader, CanonWriter, Canonical, DecodeBudget, SCHEMA_IR_CALL_GRAPH,
};
use crate::domain::{Digest, Domain, hash};
use fln_core::name::Name;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GraphClass {
    ToolchainApi,
    LibraryCode,
    Data,
    User,
    /// Absence of a census match is NOT evidence that a symbol is user code.
    Unclassified,
}

impl GraphClass {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ToolchainApi => "toolchain-api",
            Self::LibraryCode => "library-code",
            Self::Data => "data",
            Self::User => "user",
            Self::Unclassified => "unclassified",
        }
    }

    const fn tag(self) -> u8 {
        match self {
            Self::ToolchainApi => 0,
            Self::LibraryCode => 1,
            Self::Data => 2,
            Self::User => 3,
            Self::Unclassified => 4,
        }
    }

    fn from_tag(tag: u8) -> Result<Self, GraphArchiveError> {
        match tag {
            0 => Ok(Self::ToolchainApi),
            1 => Ok(Self::LibraryCode),
            2 => Ok(Self::Data),
            3 => Ok(Self::User),
            4 => Ok(Self::Unclassified),
            _ => Err(GraphArchiveError::Shape("unknown symbol class")),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GraphKind {
    Function,
    Extern,
    SignatureOnly,
}

impl GraphKind {
    const fn tag(self) -> u8 {
        match self {
            Self::Function => 0,
            Self::Extern => 1,
            Self::SignatureOnly => 2,
        }
    }

    fn from_tag(tag: u8) -> Result<Self, GraphArchiveError> {
        match tag {
            0 => Ok(Self::Function),
            1 => Ok(Self::Extern),
            2 => Ok(Self::SignatureOnly),
            _ => Err(GraphArchiveError::Shape("unknown node kind")),
        }
    }
}

/// Node IDs are positions in the strictly Name-ordered node table. Each target
/// appears once, ascending. `census_name` records the exact row used to classify
/// a symbol; it may differ for a compiler auxiliary. This annotation is not an
/// authorization to execute either symbol.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GraphNode {
    pub name: Name,
    pub kind: GraphKind,
    pub class: GraphClass,
    pub census_name: Option<Name>,
    pub callees: Vec<u32>,
}

#[derive(Debug, Clone, Copy)]
pub struct GraphArchiveLimits {
    /// Complete encoded bytes, including the 32-byte digest trailer.
    pub max_bytes: usize,
    pub max_nodes: usize,
    pub max_edges: usize,
    /// Cumulative components in node names AND census-row names.
    pub max_name_components: u64,
}

impl Default for GraphArchiveLimits {
    fn default() -> Self {
        Self {
            max_bytes: 512 * 1024 * 1024,
            max_nodes: 1 << 20,
            max_edges: 16_000_000,
            max_name_components: 32_000_000,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GraphArchiveError {
    Limit(&'static str),
    Shape(&'static str),
    Canonical(CanonError),
    DigestMismatch,
    UnknownRoot(Name),
}

impl GraphArchiveError {
    pub fn is_resource(&self) -> bool {
        matches!(self, Self::Limit(_))
    }
}

impl std::fmt::Display for GraphArchiveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "IR graph archive: {self:?}")
    }
}

impl std::error::Error for GraphArchiveError {}

/// Immutable, structurally consistent analysis data. Decoding this type does
/// not revalidate the source IR or verify the census against the Reference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GraphSnapshot {
    nodes: Vec<GraphNode>,
    dynamic_calls: u64,
    /// Exact-byte identity of the classification input, under IrPartition.
    partition_digest: Option<Digest>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EncodedGraph {
    pub bytes: Vec<u8>,
    /// Hash of the schema-headed payload, not of the digest trailer itself.
    pub digest: Digest,
}

fn charge_name(name: &Name, left: &mut u64) -> Result<(), GraphArchiveError> {
    let mut cursor = name.clone();
    while !cursor.is_anonymous() {
        *left = left
            .checked_sub(1)
            .ok_or(GraphArchiveError::Limit("name components"))?;
        cursor = cursor.parent();
    }
    Ok(())
}

impl GraphSnapshot {
    /// Inputs must already have canonical node/edge ordering. Refusing rather
    /// than sorting here prevents a reader from normalizing a forged encoding.
    pub fn new(
        nodes: Vec<GraphNode>,
        dynamic_calls: u64,
        partition_digest: Option<Digest>,
        limits: GraphArchiveLimits,
    ) -> Result<Self, GraphArchiveError> {
        let result = Self { nodes, dynamic_calls, partition_digest };
        result.validate(limits)?;
        Ok(result)
    }

    pub fn nodes(&self) -> &[GraphNode] { &self.nodes }
    pub fn dynamic_calls(&self) -> u64 { self.dynamic_calls }
    pub fn partition_digest(&self) -> Option<Digest> { self.partition_digest }
    pub fn edge_count(&self) -> usize { self.nodes.iter().map(|node| node.callees.len()).sum() }
    pub fn unclassified_count(&self) -> usize {
        self.nodes.iter().filter(|node| node.class == GraphClass::Unclassified).count()
    }

    pub fn find(&self, name: &Name) -> Option<u32> {
        self.nodes.binary_search_by(|node| node.name.cmp(name)).ok()
            .and_then(|index| u32::try_from(index).ok())
    }

    fn validate(&self, limits: GraphArchiveLimits) -> Result<(), GraphArchiveError> {
        if self.nodes.len() > limits.max_nodes || u32::try_from(self.nodes.len()).is_err() {
            return Err(GraphArchiveError::Limit("nodes"));
        }
        let mut edges = 0usize;
        let mut components = limits.max_name_components;
        let mut previous = None;
        for node in &self.nodes {
            charge_name(&node.name, &mut components)?;
            if previous.is_some_and(|name: &Name| name >= &node.name) {
                return Err(GraphArchiveError::Shape("node names are not strictly ordered"));
            }
            previous = Some(&node.name);
            if let Some(origin) = &node.census_name {
                charge_name(origin, &mut components)?;
            }
            match node.class {
                GraphClass::ToolchainApi | GraphClass::LibraryCode | GraphClass::Data => {
                    if node.census_name.is_none() || self.partition_digest.is_none() {
                        return Err(GraphArchiveError::Shape("census class lacks its source identity"));
                    }
                }
                GraphClass::User | GraphClass::Unclassified if node.census_name.is_some() => {
                    return Err(GraphArchiveError::Shape("non-census class claims a census row"));
                }
                GraphClass::User | GraphClass::Unclassified => {}
            }
            if node.kind != GraphKind::Function && !node.callees.is_empty() {
                return Err(GraphArchiveError::Shape("a body-less node has outgoing calls"));
            }
            edges = edges.checked_add(node.callees.len())
                .filter(|count| *count <= limits.max_edges)
                .ok_or(GraphArchiveError::Limit("edges"))?;
            let mut last = None;
            for &target in &node.callees {
                if target as usize >= self.nodes.len() {
                    return Err(GraphArchiveError::Shape("call target is outside the node table"));
                }
                if last.is_some_and(|last| last >= target) {
                    return Err(GraphArchiveError::Shape("call targets are not strictly ordered"));
                }
                last = Some(target);
            }
        }
        Ok(())
    }

    pub fn encode(&self, limits: GraphArchiveLimits) -> Result<EncodedGraph, GraphArchiveError> {
        self.validate(limits)?;
        let payload_cap = limits.max_bytes.checked_sub(32)
            .ok_or(GraphArchiveError::Limit("archive bytes"))?;
        let mut writer = CanonWriter::with_limit(payload_cap);
        writer.schema(SCHEMA_IR_CALL_GRAPH);
        writer.u64(self.dynamic_calls);
        writer.bool(self.partition_digest.is_some());
        if let Some(digest) = self.partition_digest { writer.digest(&digest); }
        writer.u64(self.nodes.len() as u64);
        for node in &self.nodes {
            node.name.write_body(&mut writer);
            writer.u8(node.kind.tag());
            writer.u8(node.class.tag());
            writer.bool(node.census_name.is_some());
            if let Some(origin) = &node.census_name { origin.write_body(&mut writer); }
            writer.u64(node.callees.len() as u64);
            for &target in &node.callees { writer.u32(target); }
            if writer.overflowed() { return Err(GraphArchiveError::Limit("archive bytes")); }
        }
        if writer.overflowed() { return Err(GraphArchiveError::Limit("archive bytes")); }
        let mut bytes = writer.into_bytes();
        let digest = hash(Domain::IrCallGraph, &bytes);
        bytes.try_reserve(32).map_err(|_| GraphArchiveError::Limit("archive allocation"))?;
        bytes.extend_from_slice(&digest.0);
        Ok(EncodedGraph { bytes, digest })
    }

    /// Verify the digest, schema, canonical ordering, all lengths/indices and
    /// annotation invariants before returning any data. No trailing bytes,
    /// unknown tags, dropped duplicate rows or silently normalized edges.
    pub fn decode(bytes: &[u8], limits: GraphArchiveLimits) -> Result<Self, GraphArchiveError> {
        if bytes.len() > limits.max_bytes { return Err(GraphArchiveError::Limit("archive bytes")); }
        let split = bytes.len().checked_sub(32)
            .ok_or(GraphArchiveError::Shape("missing digest trailer"))?;
        let (payload, trailer) = bytes.split_at(split);
        if hash(Domain::IrCallGraph, payload).0.as_slice() != trailer {
            return Err(GraphArchiveError::DigestMismatch);
        }
        let mut reader = CanonReader::with_budget(
            payload, DecodeBudget::new(payload.len() as u64, limits.max_name_components),
        );
        macro_rules! read {
            ($expression:expr) => {
                match $expression {
                    Ok(value) => value,
                    Err(error) => return Err(if reader.exhausted().is_some() {
                        GraphArchiveError::Limit("name components")
                    } else {
                        GraphArchiveError::Canonical(error)
                    }),
                }
            };
        }
        read!(reader.expect_schema(SCHEMA_IR_CALL_GRAPH));
        let dynamic_calls = read!(reader.u64());
        let partition_digest = if read!(reader.bool()) {
            let mut digest = [0; 32];
            for byte in &mut digest { *byte = read!(reader.u8()); }
            Some(Digest(digest))
        } else { None };
        let count = usize::try_from(read!(reader.u64()))
            .map_err(|_| GraphArchiveError::Limit("nodes"))?;
        if count > limits.max_nodes || u32::try_from(count).is_err() {
            return Err(GraphArchiveError::Limit("nodes"));
        }
        // Every row requires more than one byte; check before sizing a Vec.
        if count > payload.len() - reader.offset() {
            return Err(GraphArchiveError::Shape("node count exceeds the remaining input"));
        }
        let mut nodes = Vec::new();
        nodes.try_reserve_exact(count).map_err(|_| GraphArchiveError::Limit("node allocation"))?;
        let mut total_edges = 0usize;
        for _ in 0..count {
            let name = read!(Name::read_body(&mut reader));
            let kind = GraphKind::from_tag(read!(reader.u8()))?;
            let class = GraphClass::from_tag(read!(reader.u8()))?;
            let census_name = if read!(reader.bool()) { Some(read!(Name::read_body(&mut reader))) } else { None };
            let edge_count = usize::try_from(read!(reader.u64()))
                .map_err(|_| GraphArchiveError::Limit("edges"))?;
            total_edges = total_edges.checked_add(edge_count)
                .filter(|n| *n <= limits.max_edges)
                .ok_or(GraphArchiveError::Limit("edges"))?;
            if edge_count > (payload.len() - reader.offset()) / 4 {
                return Err(GraphArchiveError::Shape("edge count exceeds the remaining input"));
            }
            let mut callees = Vec::new();
            callees.try_reserve_exact(edge_count).map_err(|_| GraphArchiveError::Limit("edge allocation"))?;
            for _ in 0..edge_count { callees.push(read!(reader.u32())); }
            nodes.push(GraphNode { name, kind, class, census_name, callees });
        }
        reader.finish().map_err(GraphArchiveError::Canonical)?;
        Self::new(nodes, dynamic_calls, partition_digest, limits)
    }

    /// Query the stored static graph without any IR files. `descend` is asked
    /// once per reached node; a refused root/node is reached, not traversed.
    /// Unknown roots and work exhaustion return no partial reachability result.
    pub fn reach(
        &self,
        roots: &[Name],
        mut descend: impl FnMut(&GraphNode) -> bool,
        max_work: u64,
    ) -> Result<Vec<u32>, GraphArchiveError> {
        let mut left = max_work;
        let charge = |left: &mut u64| -> Result<(), GraphArchiveError> {
            *left = left.checked_sub(1).ok_or(GraphArchiveError::Limit("query work"))?;
            Ok(())
        };
        let mut reached = Vec::new();
        reached.try_reserve_exact(self.nodes.len()).map_err(|_| GraphArchiveError::Limit("query allocation"))?;
        reached.resize(self.nodes.len(), false);
        let mut pending = Vec::new();
        pending.try_reserve_exact(self.nodes.len()).map_err(|_| GraphArchiveError::Limit("query allocation"))?;
        for name in roots {
            charge(&mut left)?;
            let id = self.find(name).ok_or_else(|| GraphArchiveError::UnknownRoot(name.clone()))?;
            if !std::mem::replace(&mut reached[id as usize], true) { pending.push(id); }
        }
        while let Some(id) = pending.pop() {
            charge(&mut left)?;
            let node = &self.nodes[id as usize];
            if !descend(node) { continue; }
            for &target in &node.callees {
                charge(&mut left)?;
                if !std::mem::replace(&mut reached[target as usize], true) { pending.push(target); }
            }
        }
        // Charge materialization too: querying an empty root set is not a way
        // to force an unaccounted traversal of a million-node table.
        let mut result = Vec::new();
        for (id, yes) in reached.into_iter().enumerate() {
            charge(&mut left)?;
            if yes {
                result.try_reserve(1).map_err(|_| GraphArchiveError::Limit("query allocation"))?;
                result.push(id as u32);
            }
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(text: &str) -> Name { Name::from_components(text.split('.')) }
    fn node(text: &str) -> GraphNode {
        GraphNode { name: n(text), kind: GraphKind::Function, class: GraphClass::Unclassified,
            census_name: None, callees: Vec::new() }
    }
    fn limits() -> GraphArchiveLimits { GraphArchiveLimits::default() }
    fn small() -> GraphSnapshot {
        let mut nodes = vec![node("entry"), node("middle"), node("native"), node("behind"), node("island")];
        nodes.sort_by(|a,b| a.name.cmp(&b.name));
        let id = |text: &str| nodes.iter().position(|row| row.name == n(text)).unwrap() as u32;
        let (entry, middle, native, behind) = (id("entry"), id("middle"), id("native"), id("behind"));
        nodes[entry as usize].callees = vec![middle];
        nodes[middle as usize].callees = vec![entry, native];
        nodes[middle as usize].callees.sort_unstable();
        nodes[native as usize].callees = vec![behind];
        nodes[native as usize].class = GraphClass::ToolchainApi;
        nodes[native as usize].census_name = Some(n("native"));
        GraphSnapshot::new(nodes, 3, Some(Digest([9;32])), limits()).unwrap()
    }
    fn raw(nodes: &[GraphNode], kind: Option<u8>, class: Option<u8>, extra: &[u8]) -> Vec<u8> {
        let mut w = CanonWriter::new();
        w.schema(SCHEMA_IR_CALL_GRAPH);
        w.u64(0); w.bool(false); w.u64(nodes.len() as u64);
        for row in nodes {
            row.name.write_body(&mut w);
            w.u8(kind.unwrap_or(row.kind.tag()));
            w.u8(class.unwrap_or(row.class.tag()));
            w.bool(row.census_name.is_some());
            if let Some(origin) = &row.census_name { origin.write_body(&mut w); }
            w.u64(row.callees.len() as u64);
            for id in &row.callees { w.u32(*id); }
        }
        let mut bytes = w.into_bytes();
        bytes.extend_from_slice(extra);
        let digest = hash(Domain::IrCallGraph, &bytes);
        bytes.extend_from_slice(&digest.0);
        bytes
    }
    #[test]
    fn roundtrip_preserves_every_field_and_the_payload_identity() {
        let graph = small();
        let encoded = graph.encode(limits()).unwrap();
        let decoded = GraphSnapshot::decode(&encoded.bytes, limits()).unwrap();
        assert_eq!(decoded, graph);
        assert_eq!(decoded.encode(limits()).unwrap(), encoded);
        assert_eq!(encoded.digest, hash(Domain::IrCallGraph, &encoded.bytes[..encoded.bytes.len()-32]));
        assert_ne!(encoded.digest, hash(Domain::Fixture, &encoded.bytes[..encoded.bytes.len()-32]));
        assert_eq!(decoded.dynamic_calls(), 3);
    }
    #[test]
    fn each_changed_byte_is_refused_without_an_updated_digest() {
        let original = small().encode(limits()).unwrap().bytes;
        for index in 0..original.len() {
            let mut changed = original.clone(); changed[index] ^= 0x40;
            assert_eq!(GraphSnapshot::decode(&changed, limits()), Err(GraphArchiveError::DigestMismatch));
        }
    }
    #[test]
    fn every_truncation_is_a_typed_refusal() {
        let bytes = small().encode(limits()).unwrap().bytes;
        for end in 0..bytes.len() { assert!(GraphSnapshot::decode(&bytes[..end], limits()).is_err()); }
    }
    #[test]
    fn a_resealed_unknown_kind_or_class_is_not_silently_skipped() {
        assert!(matches!(GraphSnapshot::decode(&raw(&[node("a")], Some(255), None, &[]), limits()), Err(GraphArchiveError::Shape(_))));
        assert!(matches!(GraphSnapshot::decode(&raw(&[node("a")], None, Some(255), &[]), limits()), Err(GraphArchiveError::Shape(_))));
    }
    #[test]
    fn resealed_duplicate_and_out_of_order_names_are_refused() {
        let a = node("a"); let b = node("b");
        assert!(GraphSnapshot::decode(&raw(&[a.clone(), a.clone()], None, None, &[]), limits()).is_err());
        let mut nodes = vec![a,b]; nodes.sort_by(|a,b| b.name.cmp(&a.name));
        assert!(GraphSnapshot::decode(&raw(&nodes, None, None, &[]), limits()).is_err());
    }
    #[test]
    fn resealed_out_of_range_and_duplicate_edges_are_refused() {
        for targets in [vec![1], vec![u32::MAX], vec![0,0]] {
            let mut row = node("a"); row.callees = targets;
            assert!(GraphSnapshot::decode(&raw(&[row], None, None, &[]), limits()).is_err());
        }
    }
    #[test]
    fn outgoing_edges_require_a_function_body() {
        for kind in [GraphKind::Extern,GraphKind::SignatureOnly] {
            let mut row = node("a"); row.kind = kind; row.callees = vec![0];
            assert!(GraphSnapshot::new(vec![row.clone()],0,None,limits()).is_err());
            assert!(GraphSnapshot::decode(&raw(&[row],None,None,&[]),limits()).is_err());
        }
    }
    #[test]
    fn a_census_annotation_needs_both_its_row_and_partition_identity() {
        let mut row = node("a"); row.class = GraphClass::LibraryCode;
        assert!(GraphSnapshot::new(vec![row.clone()],0,Some(Digest([1;32])),limits()).is_err());
        row.census_name = Some(n("base"));
        assert!(GraphSnapshot::new(vec![row.clone()],0,None,limits()).is_err());
        assert!(GraphSnapshot::new(vec![row.clone()],0,Some(Digest([1;32])),limits()).is_ok());
        for class in [GraphClass::User,GraphClass::Unclassified] {
            row.class = class;
            assert!(GraphSnapshot::new(vec![row.clone()],0,Some(Digest([1;32])),limits()).is_err());
        }
    }
    #[test]
    fn trailing_payload_bytes_are_refused_even_when_resealed() {
        assert!(GraphSnapshot::decode(&raw(&[node("a")],None,None,b"garbage"),limits()).is_err());
    }
    #[test]
    fn unknown_schema_and_version_are_refused_even_when_resealed() {
        for schema in [crate::canon::SchemaId { name: "wrong",version:1 },
            crate::canon::SchemaId { name: SCHEMA_IR_CALL_GRAPH.name,version:2 }] {
            let mut w = CanonWriter::new(); w.schema(schema); w.u64(0); w.bool(false); w.u64(0);
            let mut bytes = w.into_bytes(); let digest = hash(Domain::IrCallGraph,&bytes); bytes.extend_from_slice(&digest.0);
            assert!(matches!(GraphSnapshot::decode(&bytes,limits()),Err(GraphArchiveError::Canonical(_))));
        }
    }
    #[test]
    fn lengths_are_checked_before_allocation() {
        let mut w = CanonWriter::new(); w.schema(SCHEMA_IR_CALL_GRAPH); w.u64(0); w.bool(false); w.u64(u64::MAX);
        let mut bytes = w.into_bytes(); let digest = hash(Domain::IrCallGraph,&bytes); bytes.extend_from_slice(&digest.0);
        assert!(GraphSnapshot::decode(&bytes,limits()).unwrap_err().is_resource());
    }
    #[test]
    fn exact_byte_node_edge_and_component_limits_are_enforced() {
        let graph = small(); let encoded = graph.encode(limits()).unwrap();
        let exact = GraphArchiveLimits { max_bytes: encoded.bytes.len(), max_nodes:5,max_edges:4,max_name_components:6 };
        graph.encode(exact).unwrap(); GraphSnapshot::decode(&encoded.bytes,exact).unwrap();
        for below in [GraphArchiveLimits {max_bytes:exact.max_bytes-1,..exact},
            GraphArchiveLimits {max_nodes:4,..exact}, GraphArchiveLimits {max_edges:3,..exact},
            GraphArchiveLimits {max_name_components:5,..exact}] {
            assert!(graph.encode(below).unwrap_err().is_resource());
            assert!(GraphSnapshot::decode(&encoded.bytes,below).unwrap_err().is_resource());
        }
    }
    #[test]
    fn numeric_and_string_components_and_overflow_flags_do_not_collapse() {
        let names = [Name::str(Name::anonymous(),"A.B"),n("A.B"),
            Name::num(n("A"),7),Name::str(n("A"),"7"),Name::num_overflowing(n("A"),7)];
        let mut rows: Vec<_> = names.iter().map(|name| GraphNode { name:name.clone(),..node("unused") }).collect();
        rows.sort_by(|a,b| a.name.cmp(&b.name));
        let graph = GraphSnapshot::new(rows,0,None,limits()).unwrap();
        assert_eq!(GraphSnapshot::decode(&graph.encode(limits()).unwrap().bytes,limits()).unwrap(),graph);
        for name in names { assert!(graph.find(&name).is_some()); }
    }
    #[test]
    fn reach_handles_cycles_and_stops_at_the_native_boundary() {
        let graph = small();
        let all = graph.reach(&[n("entry")], |_| true, 100).unwrap();
        assert_eq!(all.len(),4);
        let front = graph.reach(&[n("entry")], |row| row.class != GraphClass::ToolchainApi,100).unwrap();
        assert_eq!(front.len(),3);
        assert!(front.contains(&graph.find(&n("native")).unwrap()));
        assert!(!front.contains(&graph.find(&n("behind")).unwrap()));
        assert_eq!(graph.reach(&[n("native")], |_|false,100).unwrap(),vec![graph.find(&n("native")).unwrap()]);
    }
    #[test]
    fn unknown_roots_and_query_exhaustion_return_no_partial_result() {
        let graph = small();
        assert!(matches!(graph.reach(&[n("absent")], |_|true,100),Err(GraphArchiveError::UnknownRoot(_))));
        assert!(graph.reach(&[n("entry")], |_|true,0).unwrap_err().is_resource());
        assert!(graph.reach(&[], |_|true,4).unwrap_err().is_resource());
        assert!(graph.reach(&[], |_|true,5).unwrap().is_empty());
        assert_eq!(graph.reach(&[n("entry"),n("entry")], |_|true,100).unwrap(),graph.reach(&[n("entry")], |_|true,100).unwrap());
    }
    #[test]
    fn different_dynamic_counts_classifications_and_origins_change_identity() {
        let graph = small(); let original = graph.encode(limits()).unwrap().digest;
        let mut changed = graph.clone(); changed.dynamic_calls += 1;
        assert_ne!(changed.encode(limits()).unwrap().digest,original);
        let id = graph.find(&n("native")).unwrap() as usize;
        changed = graph.clone(); changed.nodes[id].class = GraphClass::Data;
        assert_ne!(changed.encode(limits()).unwrap().digest,original);
        changed = graph.clone(); changed.nodes[id].census_name = Some(n("other"));
        assert_ne!(changed.encode(limits()).unwrap().digest,original);
        changed = graph.clone(); changed.partition_digest = Some(Digest([8;32]));
        assert_ne!(changed.encode(limits()).unwrap().digest,original);
    }
}
