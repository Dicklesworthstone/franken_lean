//! The cell-F discriminator: an OPEN descriptor is not a HELD lock.
//!
//! Bead `franken_lean-gate-lock-producer-optional-o2vz`. `scripts/lib/gate_lock.sh` exists so that
//! "the lane ran" entails "the gate was held" — before it, the gate lockfile was named in zero
//! executable surfaces, so a FREE probe was uninformative (an unwrapped lane takes no lock) and a
//! HELD probe equally so (anything at all may take the path).
//!
//! **The defect this file guards is one layer inside that repair.** `fln_gate_inherited` scans
//! `/proc/self/fd` for the lockfile path and concludes an ancestor holds the gate. That premise is
//! false for a descriptor opened and never locked, and the two are indistinguishable by any path
//! scan — so a lane would run believing it held the freeze while nothing did, and then *journal*
//! that claim, making it durable rather than merely believed. The repair is
//! `fln_gate_confirm_inherited`: flock(2) locks belong to the open file description, so a SECOND
//! descriptor conflicts with a genuine ancestor lock and does not with a merely-open one.
//!
//! **Why this file exists rather than a recorded measurement.** The discriminator was measured in
//! both directions when it landed, on one host at one commit. Nothing held it afterwards. A repair
//! whose control is a paragraph is the shape this repository files beads about, so the control is
//! here and runs under plain `cargo test`.
//!
//! **The third cell is the one that matters.** Cells 1 and 2 pass just as happily against a library
//! whose discriminator has been gutted *if* the assertion is written loosely, so cell 3 plants
//! exactly that mutant and requires it to produce the WRONG answer. Without it, cell 1 would be a
//! test that cannot fail for the reason it names — and a green would mean nothing. A mutant that
//! fails to apply is scored VOID, never "0 killed".
//!
//! Everything here runs against a lockfile under the process's own temp directory. The real gate at
//! `/data/tmp/fln-gate.lockfile` is never opened, and `FLN_GATE_LOCKFILE` is set on every
//! invocation so the library's default can never be reached.
//!
//! Class `bounded_model`: this is process behaviour on one host. What it earns per commit is that
//! the discriminator still discriminates — not that the gate protects any lane.

use std::path::PathBuf;
use std::process::Command;

/// The library under test, resolved through the k60n tree check so a binary baked in one
/// checkout cannot answer for another.
fn library() -> PathBuf {
    let lib = fln_conformance::checked_workspace_root!().join("scripts/lib/gate_lock.sh");
    assert!(
        lib.is_file(),
        "scripts/lib/gate_lock.sh must exist; without it every cell below is vacuous rather \
         than passing (bead franken_lean-gate-lock-producer-optional-o2vz)"
    );
    lib
}

/// A per-process scratch lockfile. Deterministic per cell so repeated runs overwrite rather than
/// accumulate, and process-scoped so two panes running `cargo test` at once cannot collide.
fn scratch(cell: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("fln-gate-discriminator-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch directory is creatable");
    let path = dir.join(format!("{cell}.lockfile"));
    assert!(
        !path.starts_with("/data/tmp/fln-gate.lockfile"),
        "refusing to run against the real build gate"
    );
    path
}

/// Run a bash fragment with the gate library sourced and the scratch lockfile bound, and return
/// the reported `FLN_GATE_STATE`.
fn gate_state(lib: &PathBuf, lockfile: &PathBuf, wrapper: Wrapper, fragment: &str) -> String {
    let journal = lockfile.with_extension("journal");
    let script = format!(
        r#"set -u
             . "$GATE_LIB"
             {fragment}
             fln_gate_acquire discriminator_probe
             printf 'STATE=%s\n' "$FLN_GATE_STATE""#
    );
    let mut cmd = match wrapper {
        Wrapper::None => {
            let mut c = Command::new("bash");
            c.arg("-c").arg(&script);
            c
        }
        // The legacy shape: a caller that wraps the lane in `flock <lockfile> …`, handing us an
        // open AND LOCKED descriptor. This is the case that must still report `inherited`.
        Wrapper::GenuineAncestorLock => {
            let mut c = Command::new("flock");
            c.arg(lockfile).arg("bash").arg("-c").arg(&script);
            c
        }
    };
    let out = cmd
        .env("GATE_LIB", lib)
        .env("FLN_GATE_LOCKFILE", lockfile)
        .env("FLN_GATE_JOURNAL", &journal)
        // Bounded: a cell that reaches the acquire path must never inherit the shipped 2400s.
        .env("FLN_GATE_WAIT_S", "2")
        .output()
        .expect("bash/flock are available; their absence is an environment fault, not a finding");
    let stdout = String::from_utf8_lossy(&out.stdout);
    stdout
        .lines()
        .find_map(|l| l.strip_prefix("STATE="))
        .unwrap_or_else(|| {
            panic!(
                "the probe reported no FLN_GATE_STATE at all, so nothing was measured.\n\
                 stdout: {stdout}\nstderr: {}",
                String::from_utf8_lossy(&out.stderr)
            )
        })
        .trim()
        .to_string()
}

enum Wrapper {
    None,
    GenuineAncestorLock,
}

/// Opens a descriptor on the lockfile and never flocks it — cell F's decoy.
const OPEN_BUT_UNLOCKED_FD: &str = r#"exec 7>>"$FLN_GATE_LOCKFILE""#;

/// CELL 1 — the property. A descriptor that is merely open must not be read as a held gate.
///
/// This is the assertion that fails if the discriminator is ever removed, which is what makes it
/// the negative control for the repair rather than a restatement of it.
#[test]
fn an_open_but_unlocked_descriptor_is_not_mistaken_for_a_held_gate() {
    let lib = library();
    let lock = scratch("cell1");
    let state = gate_state(&lib, &lock, Wrapper::None, OPEN_BUT_UNLOCKED_FD);
    assert_eq!(
        state, "acquired",
        "a descriptor opened on the lockfile and NEVER flocked was reported as `{state}`. \
         Only `acquired` is correct: nothing held the gate, so the library must take it rather \
         than believe an ancestor already had it. Reporting `inherited` here is cell F — the lane \
         runs believing it holds a freeze that nothing holds, and journals that claim. The repair \
         is fln_gate_confirm_inherited's second-descriptor probe in scripts/lib/gate_lock.sh."
    );
}

/// CELL 2 — the opposite direction. A genuine ancestor lock must still be detected, or the
/// library re-acquires against its own launcher and stalls for FLN_GATE_WAIT_S (40 minutes at the
/// shipped default). Cell 1 alone would be satisfied by a discriminator that never reports
/// `inherited` at all; this is what forbids that degenerate repair.
#[test]
fn a_genuine_ancestor_lock_is_still_detected_as_inherited() {
    let lib = library();
    let lock = scratch("cell2");
    let state = gate_state(&lib, &lock, Wrapper::GenuineAncestorLock, "");
    assert_eq!(
        state, "inherited",
        "a lane wrapped in `flock <lockfile> …` reported `{state}`. It must report `inherited`: \
         the ancestor genuinely holds the gate, and re-acquiring blocks against our own launcher \
         for the full FLN_GATE_WAIT_S."
    );
}

/// CELL 3 — the anti-vacuity control, and the reason cells 1 and 2 are worth their slot.
///
/// Plants the pre-repair detector (the second-descriptor probe forced to report a conflict) and
/// requires it to give the WRONG answer on cell 1's input. If this mutant were to pass, cell 1
/// would be green for a library with no discriminator at all — a test that cannot fail for the
/// reason it names.
#[test]
fn the_pre_repair_detector_is_measurably_wrong_so_cell_one_is_not_vacuous() {
    let lib = library();
    let source = std::fs::read_to_string(&lib).expect("the library is readable");
    let mutant_body = source.replace("  if flock -n 9; then", "  if false; then");
    assert_ne!(
        mutant_body, source,
        "the mutant did not apply — `fln_gate_confirm_inherited`'s probe has been reworded, so \
         this cell measured NOTHING. Scored VOID, never as a surviving-mutant pass. Re-derive the \
         needle from the current library before trusting cell 1."
    );

    let lock = scratch("cell3");
    let mutant = lock.with_extension("mutant.sh");
    std::fs::write(&mutant, &mutant_body).expect("the mutant library is writable");

    let state = gate_state(&mutant, &lock, Wrapper::None, OPEN_BUT_UNLOCKED_FD);
    assert_eq!(
        state, "inherited",
        "the pre-repair detector reported `{state}` on a merely-open descriptor. It is supposed \
         to be WRONG here — that wrongness is precisely what cell 1 exists to catch. If the \
         mutant now agrees with the repaired library, the two are no longer distinguished by \
         this input and cell 1 has stopped testing the discriminator."
    );
}
