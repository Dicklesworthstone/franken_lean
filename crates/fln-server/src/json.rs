//! Binary-facing façade for Lantern's strict JSON-RPC parser.
//!
//! Transcript tools are separate binary crates, so they cannot name the private
//! `dispatch::json` module through the library API. They include this façade as
//! their local `json` module; the implementation itself remains single-source at
//! `dispatch/json.rs`.

#![allow(dead_code)]

include!("dispatch/json.rs");
