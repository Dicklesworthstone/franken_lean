#![forbid(unsafe_code)]
//! Build-time baking of `fln identity` facts (bead-referenced in USAGE):
//! every reported pin is *derived* from `SUITE.lock` and this crate's own
//! `Cargo.toml` provenance comments at compile time, never hand-copied (plan
//! D5 extraction discipline). A fact whose source cannot be read bakes as
//! `"unavailable"` rather than a plausible-looking guess.
//!
//! Determinism: identical `SUITE.lock` + `Cargo.toml` yield byte-identical
//! binaries on the pinned toolchain; no clock, path, or host value enters any
//! baked variable.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

/// Emit one compile-time environment variable, always present.
fn bake(name: &str, value: String) {
    println!("cargo:rustc-env={name}={value}");
}

/// First value of `key=` inside a space-separated keyword row.
fn keyword<'a>(row: &'a str, key: &str) -> Option<&'a str> {
    row.split_ascii_whitespace()
        .find_map(|word| word.strip_prefix(key)?.strip_prefix('='))
}

/// The `<org/repo> tag=<tag> commit=<hash>` rows (`reference` / `corpus`).
fn pinned_row(lock: &str, leading: &str) -> Option<(String, String)> {
    let row = lock
        .lines()
        .find(|line| line.starts_with(leading) && !line.trim_start().starts_with('#'))?;
    Some((
        keyword(row, "tag")?.to_owned(),
        keyword(row, "commit")?.to_owned(),
    ))
}

/// This crate's declared product root, from its own `# fln-product-root:`
/// provenance comment — derived, not transcribed.
fn product_root(manifest_dir: &Path) -> Option<String> {
    let manifest = fs::read_to_string(manifest_dir.join("Cargo.toml")).ok()?;
    manifest.lines().find_map(|line| {
        let value = line.trim().strip_prefix("# fln-product-root:")?;
        Some(value.trim().to_owned())
    })
}

fn main() {
    println!("cargo:rerun-if-changed=../../SUITE.lock");
    println!("cargo:rerun-if-changed=Cargo.toml");
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap_or_default());
    let unavailable = "unavailable".to_owned();

    let lock = fs::read_to_string(manifest_dir.join("../../SUITE.lock")).unwrap_or_default();
    let channel = lock
        .lines()
        .find_map(|line| line.strip_prefix("rust-nightly "))
        .map(str::trim)
        .map(str::to_owned);
    bake(
        "FLN_IDENTITY_RUST_CHANNEL",
        channel.unwrap_or_else(|| unavailable.clone()),
    );

    let reference = pinned_row(&lock, "reference ");
    bake(
        "FLN_IDENTITY_REFERENCE_TAG",
        reference
            .as_ref()
            .map(|(tag, _)| tag.clone())
            .unwrap_or_else(|| unavailable.clone()),
    );
    bake(
        "FLN_IDENTITY_REFERENCE_COMMIT",
        reference
            .map(|(_, commit)| commit)
            .unwrap_or_else(|| unavailable.clone()),
    );

    let corpus = pinned_row(&lock, "corpus ");
    bake(
        "FLN_IDENTITY_CORPUS_TAG",
        corpus
            .as_ref()
            .map(|(tag, _)| tag.clone())
            .unwrap_or_else(|| unavailable.clone()),
    );
    bake(
        "FLN_IDENTITY_CORPUS_COMMIT",
        corpus
            .map(|(_, commit)| commit)
            .unwrap_or_else(|| unavailable.clone()),
    );

    bake(
        "FLN_IDENTITY_PRODUCT_ROOT",
        product_root(&manifest_dir).unwrap_or_else(|| unavailable.clone()),
    );
}
