#![forbid(unsafe_code)]

pub use fln_server::json_string;
pub const LSP_POSITION_ENCODING: &str = fln_server::LSP_POSITION_ENCODING;

#[allow(dead_code)]
#[path = "../src/json.rs"]
mod json;
#[allow(dead_code)]
#[path = "../src/state.rs"]
mod state;
#[allow(dead_code)]
#[path = "../src/wire.rs"]
mod wire;

#[test]
fn modular_foundations_share_the_published_position_contract() {
    assert_eq!(LSP_POSITION_ENCODING, "utf-16");
    assert!(json_string("FrankenLean").starts_with('"'));
}
