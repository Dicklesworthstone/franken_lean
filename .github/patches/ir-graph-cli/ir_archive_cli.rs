//! Real executable coverage of reusable graph export and file-only queries.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_hash::domain::Digest;
use fln_hash::ir_graph::{GraphArchiveLimits, GraphClass, GraphKind, GraphNode, GraphSnapshot};
use fln_olean::ir::{IrDecodeLimits, decode_ir};
use fln_olean::region::{OleanView, WalkBudget};
use fln_olean::write::{ModuleWriteInput, OleanWriteHeader, WriteBudget};
use fln_olean::{ModuleExtensionInput, encode_module_with_extensions};
use fln_rt::region::materialize;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        loop {
            let path = std::env::temp_dir().join(format!("fln-ir-archive-{}-{}", std::process::id(), NEXT.fetch_add(1,Ordering::Relaxed)));
            match std::fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!(/* ubs:ignore -- test diagnostic. */ "scratch creation: {error}"),
            }
        }
    }
    fn write(&self, filename: &str, bytes: &[u8]) -> PathBuf {
        let path = self.0.join(filename); std::fs::write(&path,bytes).unwrap(); path
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        // Exclusively created by this test; never a caller-supplied directory.
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
fn n(text: &str) -> Name { Name::from_components(text.split('.')) }
fn limits() -> GraphArchiveLimits { GraphArchiveLimits::default() }

/// Unchanged declaration payload from the committed pin fixture in a synthetic
/// wrapper. No Reference process or implementation code is executed.
fn isolated(wanted: &str) -> Vec<u8> {
    let bytes = include_bytes!("../fixtures/ir/Init.Data.Nat.Basic.ir");
    let view = OleanView::parse(bytes).unwrap();
    let blocks = view.extension_payloads(WalkBudget::default(),1<<30).unwrap();
    let decoded = decode_ir(&blocks,IrDecodeLimits::default()).unwrap();
    let extension = n("Lean.IR.declMapExt");
    let block = blocks.iter().find(|block|block.name == extension).unwrap();
    let index = decoded.decls.iter().position(|decl|decl.name() == &n(wanted)).unwrap();
    let entries = vec![materialize(&block.entries[index],0).unwrap()];
    encode_module_with_extensions(
        ModuleWriteInput {is_module:false,imports:&[],constants:&[],extra_const_names:&[]},
        &[ModuleExtensionInput {name:&extension,entries:&entries}],
        OleanWriteHeader {version:2,flags:1,lean_version:"4.32.0",githash:"0123456789abcdef0123456789abcdef01234567",base_addr:0x20_000},
        WriteBudget::default(),
    ).unwrap().bytes
}
fn export(args: &[&str], files: &[PathBuf]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fln-ir-check")).args(args).args(files).output().unwrap()
}
fn query(args: &[&str], file: &PathBuf) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fln-ir-graph")).args(args).arg(file).output().unwrap()
}
fn archive(dir: &Scratch) -> (PathBuf, Vec<u8>) {
    let ir = dir.write("closed.ir",&isolated("Nat.instTransLe"));
    let output = export(&["--archive"],std::slice::from_ref(&ir));
    assert!(output.status.success(),"{:?}",output);
    let file = dir.write("graph.flig",&output.stdout);
    // The query must work without the input's original path being present.
    std::fs::rename(ir,dir.0.join("source-not-at-original-path")).unwrap();
    (file,output.stdout)
}

#[test]
fn export_to_file_and_query_without_the_original_ir() {
    let dir = Scratch::new(); let (path,bytes) = archive(&dir);
    let graph = GraphSnapshot::decode(&bytes,limits()).unwrap();
    assert_eq!(graph.nodes().len(),1); assert_eq!(graph.unclassified_count(),1);
    let digest = graph.encode(limits()).unwrap().digest.to_hex();
    let output = query(&["--root","Nat.instTransLe","--expect-digest",&digest],&path);
    assert!(output.status.success(),"{:?}",output);
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("nodes\t1\n")); assert!(text.contains("reached\t1\n"));
    assert!(text.contains("Nat.instTransLe")); assert!(text.contains("indirect_calls_whole_archive\t0"));
}

#[test]
fn file_order_and_locations_do_not_change_archive_bytes() {
    let first = Scratch::new(); let second = Scratch::new();
    let a = isolated("Nat.instTransLe"); let b = isolated("Nat.instTransLt");
    let paths = [first.write("a.ir",&a),first.write("b.ir",&b)];
    let relocated = [second.write("renamed-b.ir",&b),second.write("renamed-a.ir",&a)];
    let left = export(&["--archive"],&paths); let right = export(&["--archive"],&relocated);
    assert!(left.status.success(),"{:?}",left); assert!(right.status.success(),"{:?}",right);
    assert_eq!(left.stdout,right.stdout);
}

#[test]
fn census_classification_and_strict_unclassified_refusal_reach_the_binary() {
    let dir = Scratch::new(); let ir = dir.write("a.ir",&isolated("Nat.instTransLe"));
    let census = dir.write("partition.tsv",concat!(
        "constant_count\t1\n",
        "partition\t\"a/s\\\"Nat\\\"/s\\\"instTransLe\\\"\"\tuser-facing-data\tkernel-generated-data-surface\n",
    ).as_bytes());
    let unknown = export(&["--archive","--strict-classes"],std::slice::from_ref(&ir));
    assert_eq!(unknown.status.code(),Some(1)); assert!(unknown.stdout.is_empty());
    let known = export(&["--archive","--strict-classes","--partition",census.to_str().unwrap()],std::slice::from_ref(&ir));
    assert!(known.status.success(),"{:?}",known);
    let graph = GraphSnapshot::decode(&known.stdout,limits()).unwrap();
    assert_eq!(graph.nodes()[0].class,GraphClass::Data);
    assert_eq!(graph.nodes()[0].census_name,Some(n("Nat.instTransLe")));
    assert!(graph.partition_digest().is_some());
    let overridden = export(&["--archive","--partition",census.to_str().unwrap(),"--user-key","a/s\"Nat\"/s\"instTransLe\""],&[ir]);
    assert_eq!(overridden.status.code(),Some(1)); assert!(overridden.stdout.is_empty());
}

#[test]
fn explicit_user_keys_do_not_require_a_fabricated_census() {
    let dir = Scratch::new(); let ir = dir.write("a.ir",&isolated("Nat.instTransLe"));
    let output = export(&["--archive","--strict-classes","--user-key","a/s\"Nat\"/s\"instTransLe\""],&[ir]);
    assert!(output.status.success(),"{:?}",output);
    let graph = GraphSnapshot::decode(&output.stdout,limits()).unwrap();
    assert_eq!(graph.nodes()[0].class,GraphClass::User);
    assert_eq!(graph.nodes()[0].census_name,None); assert_eq!(graph.partition_digest(),None);
}

#[test]
fn unclosed_ir_bad_partition_and_output_exhaustion_emit_no_archive() {
    let dir = Scratch::new(); let bad = dir.write("unclosed.ir",&isolated("Nat.blt"));
    let missing = export(&["--archive"],&[bad]);
    assert_eq!(missing.status.code(),Some(1)); assert!(missing.stdout.is_empty());
    let good = dir.write("closed.ir",&isolated("Nat.instTransLe"));
    let bad_census = dir.write("bad.tsv",b"constant_count\t1\n");
    let output = export(&["--archive","--partition",bad_census.to_str().unwrap()],std::slice::from_ref(&good));
    assert_eq!(output.status.code(),Some(1)); assert!(output.stdout.is_empty());
    let output = export(&["--archive","--max-output-bytes","0"],&[good]);
    assert_eq!(output.status.code(),Some(5)); assert!(output.stdout.is_empty());
}

#[test]
fn digest_mismatch_and_corruption_cannot_publish_a_query_result() {
    let dir = Scratch::new(); let (path,bytes) = archive(&dir);
    let wrong = "0".repeat(64);
    let output = query(&["--list","--expect-digest",&wrong],&path);
    assert_eq!(output.status.code(),Some(1)); assert!(output.stdout.is_empty());
    let mut changed = bytes.clone(); changed[0] ^= 1;
    let broken = dir.write("broken.flig",&changed);
    let output = query(&["--list"],&broken);
    assert_eq!(output.status.code(),Some(1)); assert!(output.stdout.is_empty());
    let mut trailing = bytes; trailing.push(0);
    let extra = dir.write("trailing.flig",&trailing);
    assert_eq!(query(&[],&extra).status.code(),Some(1));
}

#[test]
fn query_and_read_budgets_have_exact_boundaries_and_no_partial_stdout() {
    let dir = Scratch::new(); let (path,bytes) = archive(&dir);
    let output = query(&["--root","Nat.instTransLe","--max-work","2"],&path);
    assert_eq!(output.status.code(),Some(5)); assert!(output.stdout.is_empty());
    assert!(query(&["--root","Nat.instTransLe","--max-work","3"],&path).status.success());
    let normal = query(&[],&path); assert!(normal.status.success());
    let exact = normal.stdout.len().to_string(); let below = (normal.stdout.len()-1).to_string();
    assert!(query(&["--max-output-bytes",&exact],&path).status.success());
    let output = query(&["--max-output-bytes",&below],&path);
    assert_eq!(output.status.code(),Some(5)); assert!(output.stdout.is_empty());
    assert!(query(&["--max-input-bytes",&bytes.len().to_string()],&path).status.success());
    assert_eq!(query(&["--max-input-bytes",&(bytes.len()-1).to_string()],&path).status.code(),Some(5));
}

#[test]
fn missing_roots_and_invalid_flag_combinations_are_typed_errors() {
    let dir = Scratch::new(); let (path,_) = archive(&dir);
    let absent = query(&["--root","not.in.graph"],&path);
    assert_eq!(absent.status.code(),Some(1)); assert!(absent.stdout.is_empty());
    for args in [vec!["--native-boundary"],vec!["--expect-digest","bad"],vec!["--max-work","-1"],vec!["--root-key","bad"]] {
        assert_eq!(query(&args,&path).status.code(),Some(2));
    }
    for args in [vec!["--archive","--dot"],vec!["--strict-classes"],vec!["--user-key","a/s\"X\""],vec!["--partition","x.tsv"]] {
        let output = export(&args,&[]);
        assert_eq!(output.status.code(),Some(2)); assert!(output.stdout.is_empty());
    }
}

#[test]
fn native_boundary_queries_stop_at_toolchain_and_unclassified_nodes() {
    let dir = Scratch::new();
    let mut nodes: Vec<_> = ["User","Native","Unknown","Behind"].into_iter().map(|name| GraphNode {
        name:n(name),kind:GraphKind::Function,class:GraphClass::User,census_name:None,callees:vec![],
    }).collect();
    nodes.sort_by(|a,b|a.name.cmp(&b.name));
    let id = |name: &str| nodes.iter().position(|node|node.name == n(name)).unwrap() as u32;
    let (user,native,unknown,behind) = (id("User"),id("Native"),id("Unknown"),id("Behind"));
    nodes[user as usize].callees = vec![native,unknown]; nodes[user as usize].callees.sort_unstable();
    nodes[native as usize].class = GraphClass::ToolchainApi; nodes[native as usize].census_name = Some(n("Native"));
    nodes[native as usize].callees = vec![behind];
    nodes[unknown as usize].class = GraphClass::Unclassified; nodes[unknown as usize].callees = vec![behind];
    let graph = GraphSnapshot::new(nodes,7,Some(Digest([3;32])),limits()).unwrap();
    let path = dir.write("demand.flig",&graph.encode(limits()).unwrap().bytes);
    let output = query(&["--root","User","--native-boundary"],&path);
    assert!(output.status.success(),"{:?}",output);
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("reached\t3\n")); assert!(!text.contains("\"Behind\""));
    assert!(text.contains("indirect_calls_whole_archive\t7\n"));
    let all = query(&["--root","User"],&path);
    assert!(all.status.success()); assert!(String::from_utf8(all.stdout).unwrap().contains("\"Behind\""));
}

#[test]
fn exact_root_keys_distinguish_numeric_and_dot_containing_components() {
    let dir = Scratch::new(); let name = Name::num(Name::str(Name::anonymous(),"literal.dot"),3);
    let graph = GraphSnapshot::new(vec![GraphNode {name,kind:GraphKind::Function,class:GraphClass::User,census_name:None,callees:vec![]}],0,None,limits()).unwrap();
    let path = dir.write("names.flig",&graph.encode(limits()).unwrap().bytes);
    assert!(query(&["--root-key","a/s\"literal.dot\"/n3"],&path).status.success());
    assert_eq!(query(&["--root","literal.dot.3"],&path).status.code(),Some(1));
}
