//! Page-sharing probe (bead fln-wgp — the PG-4/PG-6 mechanism, plan §6.4):
//! two private mappings of one region file share every untouched page
//! (`/proc/self/smaps` accounting), and a relocation walk on ONE mapping
//! dirties only ITS pages (CoW isolation), leaving the other consumer's
//! pages shared and clean. Emits NDJSON facts (schema `fln-region-share/1`)
//! and exits nonzero when the sharing law is violated.

#![forbid(unsafe_code)]

use fln_rt::region::{parse_olean_envelope, relocate};
use fln_unsafe_region::mapping::RegionMapping;

fn fact(kind: &str, body: &str) {
    println!("{{\"schema\":\"fln-region-share/1\",\"{kind}\":{body}}}");
}

/// (shared_clean_kb, private_clean_kb, private_dirty_kb, rss_kb) for the
/// mapping that starts at `addr`, parsed from /proc/self/smaps.
fn smaps_facts(addr: usize) -> (u64, u64, u64, u64) {
    let smaps = std::fs::read_to_string("/proc/self/smaps").expect("smaps readable");
    let start_tag = format!("{addr:x}-");
    let mut in_entry = false;
    let (mut shared, mut clean, mut dirty, mut rss) = (0u64, 0u64, 0u64, 0u64);
    for line in smaps.lines() {
        // A range header looks like `55d4aa-55d4ab r--p 00000000 103:07 ...`:
        // its first token is `<hexstart>-<hexend>`.
        let first = line.split_whitespace().next().unwrap_or("");
        if first.contains('-') && first.chars().all(|c| c.is_ascii_hexdigit() || c == '-') {
            in_entry = line.starts_with(&start_tag);
            continue;
        }
        if !in_entry {
            continue;
        }
        let grab = |prefix: &str| -> Option<u64> {
            line.strip_prefix(prefix)?
                .trim()
                .strip_suffix("kB")?
                .trim()
                .parse()
                .ok()
        };
        if let Some(v) = grab("Shared_Clean:") {
            shared = v;
        } else if let Some(v) = grab("Private_Clean:") {
            clean = v;
        } else if let Some(v) = grab("Private_Dirty:") {
            dirty = v;
        } else if let Some(v) = grab("Rss:") {
            rss = v;
        }
    }
    (shared, clean, dirty, rss)
}

fn main() {
    let Some(olean) = std::env::args().nth(1) else {
        eprintln!("usage: region_share_probe <file.olean>");
        std::process::exit(2);
    };
    let path = std::path::Path::new(&olean);

    let mut a = RegionMapping::map_file_private(path).expect("map a");
    let b = RegionMapping::map_file_private(path).expect("map b");

    // Touch every page READ-ONLY in both mappings so they are resident, then
    // measure: resident pages of both must be shared (page-cache backed),
    // with zero private-dirty.
    let checksum: u64 = a
        .as_slice()
        .iter()
        .chain(b.as_slice().iter())
        .map(|b| u64::from(*b))
        .sum();
    let (shared_a0, _clean_a0, dirty_a0, rss_a0) = smaps_facts(a.addr());
    let (shared_b0, _clean_b0, dirty_b0, rss_b0) = smaps_facts(b.addr());
    fact(
        "before",
        &format!(
            "{{\"checksum\":{checksum},\"a\":{{\"shared_kb\":{shared_a0},\"dirty_kb\":{dirty_a0},\"rss_kb\":{rss_a0}}},\"b\":{{\"shared_kb\":{shared_b0},\"dirty_kb\":{dirty_b0},\"rss_kb\":{rss_b0}}}}}"
        ),
    );
    if dirty_a0 != 0 || dirty_b0 != 0 || shared_a0 == 0 || shared_b0 == 0 {
        fact(
            "verdict",
            "{\"ok\":false,\"law\":\"untouched pages must be shared and clean\"}",
        );
        std::process::exit(4);
    }

    // Relocate mapping A in place: its touched pages must go private-dirty;
    // mapping B must stay entirely shared-clean (CoW isolation).
    let env = parse_olean_envelope(a.as_slice()).expect("envelope");
    let target = (a.addr() + env.payload_offset) as u64;
    let payload_offset = env.payload_offset;
    let buf = &mut a.as_mut_slice().expect("mut a")[payload_offset..];
    let report = relocate(buf, env.payload_base(), target).expect("relocate a");
    let (shared_a1, _clean_a1, dirty_a1, _) = smaps_facts(a.addr());
    let (shared_b1, clean_b1, dirty_b1, _) = smaps_facts(b.addr());
    // B's bytes must be untouched by A's relocation (CoW isolation).
    let checksum_b: u64 = b.as_slice().iter().map(|x| u64::from(*x)).sum();
    fact(
        "after_relocate_a",
        &format!(
            "{{\"pointers_fixed\":{},\"a\":{{\"shared_kb\":{shared_a1},\"dirty_kb\":{dirty_a1}}},\"b\":{{\"shared_kb\":{shared_b1},\"clean_kb\":{clean_b1},\"dirty_kb\":{dirty_b1},\"checksum\":{checksum_b}}}}}",
            report.pointers_fixed
        ),
    );
    // The isolation law: A's relocation dirtied A's pages only. B stays
    // entirely CLEAN (its resident pages are Shared_Clean while multiple
    // consumers map them, Private_Clean once it is the sole mapper — both
    // are page-cache-backed, unduplicated memory) and byte-identical.
    let expected_b: u64 = checksum / 2;
    let ok =
        dirty_a1 > 0 && dirty_b1 == 0 && (shared_b1 + clean_b1) > 0 && checksum_b == expected_b;
    fact(
        "verdict",
        &format!("{{\"ok\":{ok},\"law\":\"relocation dirties only its own consumer's pages\"}}"),
    );
    std::process::exit(if ok { 0 } else { 4 });
}
