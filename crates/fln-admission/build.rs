//! The admission authority's identity (bead `fln-import-reuse-composes-4ngt`).
//!
//! An import-reuse record says a council admitted a closure once. The identity it is keyed by
//! must change whenever anything that can change an admission verdict changes, and for nothing
//! else. That is this crate plus the dependency closure it compiles against, and the toolchain
//! that compiles them. The closure is read from the `Cargo.toml` files rather than listed, so
//! a new dependency joins the digest without anyone remembering to add it. A manifest shape
//! this reader does not understand fails the build, rather than leaving a dependency out.
//!
//! Every file of each closure crate's directory is digested, except `tests/`, `benches/`,
//! `examples/` and `target/`, which never link into a library. `include_*!` sites in the
//! digested code are confined to their crate's own directory, which a test in this crate
//! checks.
#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

const EXCLUDED_DIRECTORIES: [&str; 4] = ["tests", "benches", "examples", "target"];

fn main() {
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let crates_root = manifest
        .parent()
        .expect("crate directory has a parent")
        .to_path_buf();
    let workspace = crates_root
        .parent()
        .expect("crates/ has a parent")
        .to_path_buf();
    let closure = closure(&manifest);
    let mut digest = Sha256::new();
    digest.update(b"fln.admission-authority/1\0");
    for directory in &closure {
        let name = directory
            .file_name()
            .and_then(|name| name.to_str())
            .expect("crate directory name");
        field(&mut digest, b"crate", name.as_bytes());
        let mut files = Vec::new();
        collect(directory, directory, &mut files);
        files.sort();
        for relative in files {
            let path = directory.join(&relative);
            let bytes =
                std::fs::read(&path).unwrap_or_else(|error| panic!("{}: {error}", path.display()));
            field(
                &mut digest,
                b"path",
                relative.to_str().expect("utf-8 path").as_bytes(),
            );
            field(&mut digest, b"bytes", &bytes);
            println!("cargo:rerun-if-changed={}", path.display());
        }
        // A deleted or added file changes the set; watch the directories too.
        println!("cargo:rerun-if-changed={}", directory.display());
    }
    for shared in ["Cargo.toml", "Cargo.lock", "rust-toolchain.toml"] {
        let path = workspace.join(shared);
        let bytes =
            std::fs::read(&path).unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        field(&mut digest, b"workspace", shared.as_bytes());
        field(&mut digest, b"bytes", &bytes);
        println!("cargo:rerun-if-changed={}", path.display());
    }
    let rustc = std::env::var("RUSTC").expect("RUSTC");
    let version = std::process::Command::new(&rustc)
        .arg("-vV")
        .output()
        .expect("run rustc -vV");
    assert!(version.status.success(), "rustc -vV failed");
    field(&mut digest, b"rustc", &version.stdout);
    for variable in [
        "TARGET",
        "PROFILE",
        "OPT_LEVEL",
        "DEBUG",
        "CARGO_ENCODED_RUSTFLAGS",
    ] {
        let value = std::env::var(variable).unwrap_or_default();
        field(&mut digest, variable.as_bytes(), value.as_bytes());
        println!("cargo:rerun-if-env-changed={variable}");
    }
    let names: Vec<String> = closure
        .iter()
        .map(|directory| {
            directory
                .file_name()
                .unwrap()
                .to_string_lossy()
                .into_owned()
        })
        .collect();
    println!(
        "cargo:rustc-env=FLN_ADMISSION_AUTHORITY={}",
        hex(&digest.finalize())
    );
    println!("cargo:rustc-env=FLN_ADMISSION_CLOSURE={}", names.join(","));
}

fn field(digest: &mut Sha256, label: &[u8], value: &[u8]) {
    digest.update(&(label.len() as u64).to_le_bytes());
    digest.update(label);
    digest.update(&(value.len() as u64).to_le_bytes());
    digest.update(value);
}

/// This crate and every crate its `[dependencies]` reach, by path, sorted by directory name.
fn closure(start: &Path) -> Vec<PathBuf> {
    let mut seen = BTreeSet::new();
    let mut pending = vec![start.to_path_buf()];
    while let Some(directory) = pending.pop() {
        let directory = directory.canonicalize().expect("crate directory");
        if !seen.insert(directory.clone()) {
            continue;
        }
        let manifest = directory.join("Cargo.toml");
        let text = std::fs::read_to_string(&manifest)
            .unwrap_or_else(|error| panic!("{}: {error}", manifest.display()));
        println!("cargo:rerun-if-changed={}", manifest.display());
        for dependency in normal_dependencies(&manifest, &text) {
            pending.push(directory.join(dependency));
        }
    }
    seen.into_iter().collect()
}

/// The `path` of every entry in the `[dependencies]` table. Only `name = { path = "…" }` is
/// understood; anything else that could add a normal dependency fails the build.
fn normal_dependencies(manifest: &Path, text: &str) -> Vec<String> {
    let mut paths = Vec::new();
    let mut section = String::new();
    for raw in text.lines() {
        let line = raw.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        if line.starts_with('[') {
            section = line.to_owned();
            let refused = section.starts_with("[target")
                || (section.starts_with("[dependencies.") && section != "[dependencies]")
                || section == "[workspace.dependencies]";
            assert!(
                !refused,
                "{}: unsupported dependency table {section}",
                manifest.display()
            );
            continue;
        }
        if section != "[dependencies]" {
            continue;
        }
        let (_, value) = line
            .split_once('=')
            .unwrap_or_else(|| panic!("{}: unreadable dependency `{line}`", manifest.display()));
        let value = value.trim();
        let path = value
            .strip_prefix('{')
            .and_then(|inner| inner.strip_suffix('}'))
            .and_then(|inner| {
                let mut fields = inner.split(',').map(str::trim).filter(|f| !f.is_empty());
                let only = fields.next()?;
                fields.next().is_none().then_some(only)
            })
            .and_then(|field| field.strip_prefix("path"))
            .map(str::trim_start)
            .and_then(|rest| rest.strip_prefix('='))
            .map(str::trim)
            .and_then(|quoted| quoted.strip_prefix('"'))
            .and_then(|rest| rest.strip_suffix('"'))
            .unwrap_or_else(|| {
                panic!(
                    "{}: dependency `{line}` is not `name = {{ path = \"…\" }}`",
                    manifest.display()
                )
            });
        paths.push(path.to_owned());
    }
    paths
}

fn collect(root: &Path, directory: &Path, files: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("{}: {error}", directory.display()))
        .map(|entry| entry.expect("directory entry").path())
        .collect();
    entries.sort();
    for path in entries {
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("");
        let file_type = std::fs::symlink_metadata(&path)
            .expect("metadata")
            .file_type();
        assert!(
            !file_type.is_symlink(),
            "{}: symlinks are not digested",
            path.display()
        );
        if file_type.is_dir() {
            if directory == root && EXCLUDED_DIRECTORIES.contains(&name) {
                continue;
            }
            collect(root, &path, files);
        } else {
            files.push(path.strip_prefix(root).expect("under root").to_path_buf());
        }
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// FIPS 180-4 SHA-256, so the build script needs no dependency.
struct Sha256 {
    state: [u32; 8],
    buffer: Vec<u8>,
    length: u64,
}

const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

impl Sha256 {
    fn new() -> Self {
        Self {
            state: [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
                0x5be0cd19,
            ],
            buffer: Vec::with_capacity(64),
            length: 0,
        }
    }

    fn update(&mut self, mut bytes: &[u8]) {
        self.length = self.length.wrapping_add(bytes.len() as u64);
        while !bytes.is_empty() {
            let take = (64 - self.buffer.len()).min(bytes.len());
            self.buffer.extend_from_slice(&bytes[..take]);
            bytes = &bytes[take..];
            if self.buffer.len() == 64 {
                let block: [u8; 64] = self.buffer[..].try_into().expect("64 bytes");
                self.compress(&block);
                self.buffer.clear();
            }
        }
    }

    fn finalize(mut self) -> [u8; 32] {
        let bits = self.length.wrapping_mul(8);
        let mut tail = vec![0x80u8];
        while (self.buffer.len() + tail.len()) % 64 != 56 {
            tail.push(0);
        }
        tail.extend_from_slice(&bits.to_be_bytes());
        let length = self.length;
        self.update(&tail);
        self.length = length;
        let mut out = [0u8; 32];
        for (chunk, word) in out.chunks_mut(4).zip(self.state) {
            chunk.copy_from_slice(&word.to_be_bytes());
        }
        out
    }

    fn compress(&mut self, block: &[u8; 64]) {
        let mut w = [0u32; 64];
        for (index, chunk) in block.chunks(4).enumerate() {
            w[index] = u32::from_be_bytes(chunk.try_into().expect("4 bytes"));
        }
        for index in 16..64 {
            let s0 = w[index - 15].rotate_right(7)
                ^ w[index - 15].rotate_right(18)
                ^ (w[index - 15] >> 3);
            let s1 = w[index - 2].rotate_right(17)
                ^ w[index - 2].rotate_right(19)
                ^ (w[index - 2] >> 10);
            w[index] = w[index - 16]
                .wrapping_add(s0)
                .wrapping_add(w[index - 7])
                .wrapping_add(s1);
        }
        let mut v = self.state;
        for index in 0..64 {
            let s1 = v[4].rotate_right(6) ^ v[4].rotate_right(11) ^ v[4].rotate_right(25);
            let choose = (v[4] & v[5]) ^ (!v[4] & v[6]);
            let t1 = v[7]
                .wrapping_add(s1)
                .wrapping_add(choose)
                .wrapping_add(K[index])
                .wrapping_add(w[index]);
            let s0 = v[0].rotate_right(2) ^ v[0].rotate_right(13) ^ v[0].rotate_right(22);
            let majority = (v[0] & v[1]) ^ (v[0] & v[2]) ^ (v[1] & v[2]);
            let t2 = s0.wrapping_add(majority);
            v = [
                t1.wrapping_add(t2),
                v[0],
                v[1],
                v[2],
                v[3].wrapping_add(t1),
                v[4],
                v[5],
                v[6],
            ];
        }
        for (state, value) in self.state.iter_mut().zip(v) {
            *state = state.wrapping_add(value);
        }
    }
}
