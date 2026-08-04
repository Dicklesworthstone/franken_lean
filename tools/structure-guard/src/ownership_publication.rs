//! Structural refusal for interrupted kernel-ownership publication (bead `fln-3oj6`).
//!
//! The publisher's candidate is also its crash witness. Its presence means there is no
//! single clean terminal publication state, regardless of whether the candidate happens
//! to parse, so the gate reports typed inconclusive and never silently adopts it.

use std::fs;
use std::path::Path;

use crate::KERNEL_OWNERSHIP_CANDIDATE_FILE;
use crate::checks::Finding;

pub fn audit(root: &Path) -> Vec<Finding> {
    match fs::symlink_metadata(root.join(KERNEL_OWNERSHIP_CANDIDATE_FILE)) {
        Err(error) if matches!(error.kind(), std::io::ErrorKind::NotFound) => Vec::new(),
        Ok(_) => vec![Finding {
            code: "FLN-STRUCT-034",
            path: KERNEL_OWNERSHIP_CANDIDATE_FILE.to_string(),
            detail: "kernel-contract-ownership inconclusive reason=stale_candidate: interrupted or competing regeneration candidate exists; refuse the ownership publication until explicit resolution".to_string(),
        }],
        Err(error) => vec![Finding {
            code: "FLN-STRUCT-034",
            path: KERNEL_OWNERSHIP_CANDIDATE_FILE.to_string(),
            detail: format!(
                "kernel-contract-ownership inconclusive reason=candidate_state_unavailable: cannot establish candidate absence: {error}"
            ),
        }],
    }
}
