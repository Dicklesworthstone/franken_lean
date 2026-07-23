//! Real-path region loader (bead fln-wgp e2e driver): mmap a real `.olean`,
//! relocate its compacted region to the live mapping address, materialize
//! the module graph as live CompatHeap objects, and emit NDJSON facts
//! (schema `fln-region-load/1`). Optionally re-compact the graph with the
//! native writer and atomically publish it (`--rebuild-out`), with a
//! deliberate crash window for the staging drill (`--crash-after-temp`).
//!
//! Faults are TYPED: a malformed input exits 3 with a `fault` fact — never a
//! panic (FL-INV-07; the e2e negative lane asserts no `panicked` on stderr).

#![forbid(unsafe_code)]

use fln_rt::region::{
    canonical_digest, compact, materialize, parse_olean_envelope, relocate, staging_tmp_path,
    write_region_file,
};
use fln_unsafe_region::mapping::RegionMapping;

fn fact(kind: &str, body: &str) {
    println!("{{\"schema\":\"fln-region-load/1\",\"{kind}\":{body}}}");
}

fn fail(stage: &str, err: impl std::fmt::Display) -> ! {
    fact(
        "fault",
        &format!("{{\"stage\":\"{stage}\",\"detail\":\"{err}\"}}"),
    );
    std::process::exit(3)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut olean: Option<String> = None;
    let mut rebuild_out: Option<String> = None;
    let mut crash_after_temp = false;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--rebuild-out" => {
                i += 1;
                rebuild_out = args.get(i).cloned();
            }
            "--crash-after-temp" => crash_after_temp = true,
            other => olean = Some(other.to_string()),
        }
        i += 1;
    }
    let Some(olean) = olean else {
        eprintln!("usage: region_load <file.olean> [--rebuild-out <path> [--crash-after-temp]]");
        std::process::exit(2);
    };
    let path = std::path::Path::new(&olean);

    let mut mapping = match RegionMapping::map_file_private(path) {
        Ok(m) => m,
        Err(e) => fail("map", e),
    };
    let env = match parse_olean_envelope(mapping.as_slice()) {
        Ok(e) => e,
        Err(e) => fail("envelope", e),
    };
    fact(
        "envelope",
        &format!(
            "{{\"version\":{},\"base_addr\":{},\"payload_len\":{}}}",
            env.version, env.base_addr, env.payload_len
        ),
    );
    let target = (mapping.addr() + env.payload_offset) as u64;
    let payload_offset = env.payload_offset;
    let buf = match mapping.as_mut_slice() {
        Ok(b) => &mut b[payload_offset..],
        Err(e) => fail("borrow", e),
    };
    let report = match relocate(buf, env.payload_base(), target) {
        Ok(r) => r,
        Err(e) => fail("relocate", e),
    };
    let digest = match canonical_digest(buf, target) {
        Ok(d) => d,
        Err(e) => fail("digest", e),
    };
    let graph = match materialize(buf, target) {
        Ok(g) => g,
        Err(e) => fail("materialize", e),
    };
    if let Err(e) = mapping.seal() {
        fail("seal", e);
    }
    fact(
        "loaded",
        &format!(
            "{{\"objects\":{},\"pointers_fixed\":{},\"digest\":{},\"root_is_scalar\":{}}}",
            report.objects,
            report.pointers_fixed,
            digest,
            graph.is_scalar()
        ),
    );

    if let Some(out) = rebuild_out {
        let out = std::path::Path::new(&out);
        let payload = match compact(&graph, env.payload_base()) {
            Ok(p) => p,
            Err(e) => fail("recompact", e),
        };
        let mut file_bytes = mapping.as_slice()[..payload_offset].to_vec();
        file_bytes.extend_from_slice(&payload);
        if crash_after_temp {
            // The staging drill: die between temp write and rename.
            let tmp = staging_tmp_path(out);
            if let Err(e) = std::fs::write(&tmp, &file_bytes) {
                fail("stage-temp", e);
            }
            fact("crashing", &format!("{{\"tmp\":\"{}\"}}", tmp.display()));
            std::process::exit(9);
        }
        if let Err(e) = write_region_file(&file_bytes, out) {
            fail("publish", e);
        }
        fact(
            "rebuilt",
            &format!(
                "{{\"bytes\":{},\"out\":\"{}\"}}",
                file_bytes.len(),
                out.display()
            ),
        );
    }
}
