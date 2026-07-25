//! Scaffolding for instrumenting incremental-lexing divergences (bead franken_lean-81oq).
//!
//! **This file runs nothing.** It is kept, deliberately silent, because it is the harness that
//! found the five defects `incremental_lex_property` now guards against, and reconstructing it
//! took longer than writing it. Every real assertion lives in that suite; this is a place to
//! stand up a single edit and print what the two lexing paths did, when the property's
//! first-divergence report is not enough on its own.
//!
//! It is scaffolding rather than a test on purpose: there is no `#[test]`, so it compiles with
//! the crate and never appears in a run or prints to anyone's stderr. To use it, call
//! [`explain_one_edit`] from a temporary `#[test]` and read the returned report.

#![forbid(unsafe_code)]
#![allow(dead_code)] // scaffolding: reached only from a temporary test

mod common;

use common::table;
use fln_syntax::rope::Rope;
use fln_syntax::run::{lex_run, relex_incremental};
use fln_syntax::source::{BytePos, ByteSpan};

/// Apply one edit to `base` and describe what the incremental and full re-lexes each produced.
///
/// Returns the report rather than printing it, so a caller decides whether it is worth showing.
/// Total: a malformed request comes back as a described refusal, because scaffolding that
/// panics while explaining a failure is worse than no scaffolding.
pub fn explain_one_edit(base: &str, at: usize, insert: &str) -> String {
    let table = table();
    let Ok(mut rope) = Rope::from_utf8(base.as_bytes()) else {
        return format!("base is not valid UTF-8: {base:?}");
    };
    let before = rope.source_text().clone();
    let old = lex_run(&before, &table);

    let Some(span) = ByteSpan::new(BytePos(at), BytePos(at)) else {
        return format!("cannot build a span at {at}");
    };
    if let Err(error) = rope.replace(span, insert) {
        return format!("edit at {at} was refused: {error:?}");
    }
    let after = rope.source_text().clone();

    let (incremental, damage) = relex_incremental(&old, span, insert.len(), &after, &table);
    let full = lex_run(&after, &table);

    let mut report = format!(
        "edit at {at} inserting {insert:?}\n  damage={damage:?}\n  old={} incremental={} \
         full={}\n  agree={}\n",
        old.events.len(),
        incremental.events.len(),
        full.events.len(),
        incremental == full
    );
    let from = damage.reused_prefix.saturating_sub(2);
    let to = (damage.reused_prefix + damage.relexed + 3).min(incremental.events.len());
    for index in from..to {
        report.push_str(&format!(
            "  [{index}] incr={:?}\n",
            incremental.events[index]
        ));
        if let Some(event) = full.events.get(index) {
            report.push_str(&format!("        full={event:?}\n"));
        }
    }
    report
}
