//! The fuel-parity prototype: the pin's counting law as a checked model, replayed
//! against the measured corpus thresholds (bead `franken_lean-7zr`, G0-6; plan
//! §4.2/§6.3/§8.5; feeds BN-08 and OQ-2).
//!
//! # The law, extracted from the pin and not from docs
//!
//! One heartbeat tick is ONE SMALL-OBJECT ALLOCATION in the owned allocator
//! (`runtime/alloc.cpp:391`, the `:127` comment stating it plainly), plus explicit
//! `lean_inc_heartbeat` bumps. The user-facing budget is in THOUSANDS of ticks
//! (`Lean/CoreM.lean:176`), the counter is a per-command DELTA (`:441` replaces
//! `initHeartbeats` at command start; the doc line at `:438` says the incoming value
//! is ignored), and the check is **strict** — `:490` fires on `delta > max`, so a
//! command consuming exactly its budget passes. Zero disables the limit entirely.
//! `maxRecDepth` (`Lean/Util/RecDepth.lean:15`, default 512 via
//! `Init/Prelude.lean:4804`) has its own enter/leave model and is never inferred
//! from allocation counts.
//!
//! # What the model can and cannot claim
//!
//! The measured thresholds (receipt `evidence/g06_fuel_parity/thresholds_v4.32.0.jsonl`,
//! bisected at the pin, every edge re-verified against the real binary by
//! `scripts/tribunal/g06_fuel_probe.sh`) bound each file's true consumption to a
//! 1000-tick interval `((C-1)·1000, C·1000]`. The replay therefore proves verdict
//! parity by **interval endpoints**: a verdict uniform across both endpoints is
//! uniform across the interval, because the law is monotone in consumption. That is
//! the declaration-granular form G0-9's amendment ratified; per-charge-site
//! checkpoints reactivate only on a demonstrated need no consumer has shown.
//!
//! Exhaustion of the model's own counter is a typed sticky state that refuses
//! verdicts — FL-INV-07 one layer down: an overflowed meter must never turn
//! exhaustion into acceptance *or* rejection.

/// Versioned schema for the fuel model and its replay artifacts.
pub const FUEL_SCHEMA: &str = "fln-g06-fuel-model/1";

/// Ticks per user-facing `maxHeartbeats` unit (`CoreM.lean:176`).
pub const TICKS_PER_UNIT: u64 = 1000;

/// The default `maxHeartbeats` option value at the pin (`CoreM.lean:31`).
pub const DEFAULT_MAX_HEARTBEATS: u64 = 200_000;

/// The default `maxRecDepth` at the pin (`Init/Prelude.lean:4804`).
pub const DEFAULT_MAX_REC_DEPTH: usize = 512;

/// A fuel verdict. `Inconclusive` is the meter's own exhaustion and is neither
/// acceptance nor rejection (FL-INV-07).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum FuelVerdict {
    Completed,
    TimedOut,
    Inconclusive,
}

/// The heartbeat meter: the pin's counting seam as a checked model.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FuelMeter {
    consumed_ticks: u64,
    overflowed: bool,
}

impl FuelMeter {
    /// A fresh per-command meter — the `initHeartbeats` reset (`CoreM.lean:441`).
    pub fn new() -> Self {
        Self::default()
    }

    /// One small allocation, one tick (`alloc.cpp:391`).
    pub fn charge_small_alloc(&mut self) {
        self.charge(1);
    }

    /// An explicit multi-tick charge (`lean_inc_heartbeat` and batching sites).
    /// Overflow is sticky and poisons every later verdict rather than wrapping.
    pub fn charge(&mut self, ticks: u64) {
        match self.consumed_ticks.checked_add(ticks) {
            Some(total) => self.consumed_ticks = total,
            None => self.overflowed = true,
        }
    }

    pub fn consumed_ticks(&self) -> u64 {
        self.consumed_ticks
    }

    /// The verdict at a user budget (thousands of ticks). Zero disables the
    /// limit; the comparison is STRICT (`CoreM.lean:490`): exactly-at-budget
    /// completes. An overflowed meter refuses to answer.
    pub fn verdict(&self, max_heartbeats: u64) -> FuelVerdict {
        if self.overflowed {
            return FuelVerdict::Inconclusive;
        }
        if max_heartbeats == 0 {
            return FuelVerdict::Completed;
        }
        match max_heartbeats.checked_mul(TICKS_PER_UNIT) {
            Some(budget_ticks) if self.consumed_ticks > budget_ticks => FuelVerdict::TimedOut,
            Some(_) => FuelVerdict::Completed,
            // A budget so large its tick form overflows u64 cannot be exceeded
            // by a non-overflowed counter.
            None => FuelVerdict::Completed,
        }
    }
}

/// A recursion-depth refusal, carrying the depth that was needed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DepthExceeded {
    pub needed: usize,
    pub max: usize,
}

/// The recursion-depth meter: enter/leave/unwind, never inferred from ticks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecDepthMeter {
    depth: usize,
    max: usize,
}

impl RecDepthMeter {
    /// Zero means no limit, as the pin's option states.
    pub fn new(max: usize) -> Self {
        Self { depth: 0, max }
    }

    /// Enter one frame; refuses when the NEEDED depth exceeds the limit. The
    /// measured semantics: a shape needing 806 frames fails at `maxRecDepth=805`
    /// and succeeds at 806, so the check is `needed > max`.
    pub fn enter(&mut self) -> Result<(), DepthExceeded> {
        let needed = self.depth + 1;
        if self.max != 0 && needed > self.max {
            return Err(DepthExceeded {
                needed,
                max: self.max,
            });
        }
        self.depth = needed;
        Ok(())
    }

    pub fn leave(&mut self) {
        self.depth = self.depth.saturating_sub(1);
    }

    /// Unwind to a checkpoint (error-recovery paths restore depth wholesale).
    pub fn unwind_to(&mut self, depth: usize) {
        self.depth = depth;
    }

    pub fn depth(&self) -> usize {
        self.depth
    }
}

/// One measured corpus row: a file whose true consumption is bounded to the
/// interval `((threshold-1)·1000, threshold·1000]` by bisection at the pin.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MeasuredRow {
    pub file: String,
    pub family: String,
    /// `None` = unbracketed (cheap accept, or a reject that fires before the
    /// counter can trip — measured budget-independent on the pilot slice).
    pub threshold: Option<u64>,
}

/// Parse the committed thresholds receipt. Total: refuses malformed rows.
pub fn parse_receipt(text: &str) -> Result<Vec<MeasuredRow>, String> {
    let mut rows = Vec::new();
    for (i, line) in text.lines().enumerate() {
        if !line.contains("\"schema\":\"fln-g06-fuel-thresholds/1\"") {
            return Err(format!("receipt line {}: wrong or missing schema", i + 1));
        }
        if line.contains("\"step\":") {
            continue; // negative_control / summary rows
        }
        let field = |key: &str| -> Option<&str> {
            let tag = format!("\"{key}\":");
            let start = line.find(&tag)? + tag.len();
            let rest = line[start..].trim_start_matches('"');
            rest.split(['"', ',', '}']).next()
        };
        let (Some(file), Some(family), Some(threshold)) =
            (field("file"), field("family"), field("threshold"))
        else {
            return Err(format!("receipt line {}: missing fields", i + 1));
        };
        let threshold = if threshold == "null" {
            None
        } else {
            Some(
                threshold
                    .parse::<u64>()
                    .map_err(|e| format!("receipt line {}: bad threshold: {e}", i + 1))?,
            )
        };
        rows.push(MeasuredRow {
            file: file.to_string(),
            family: family.to_string(),
            threshold,
        });
    }
    Ok(rows)
}

/// Replay one measured row's verdict across a budget through the model, by
/// interval endpoints. Returns `None` when the two endpoints disagree — which
/// the monotone law makes impossible unless the budget cuts the interval, i.e.
/// exactly the 1000-tick resolution boundary the granularity states.
pub fn replay_verdict(threshold: u64, budget: u64) -> Option<FuelVerdict> {
    let mut low = FuelMeter::new();
    low.charge((threshold - 1) * TICKS_PER_UNIT + 1);
    let mut high = FuelMeter::new();
    high.charge(threshold * TICKS_PER_UNIT);
    let (a, b) = (low.verdict(budget), high.verdict(budget));
    if a == b { Some(a) } else { None }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The committed receipt, held to the real binary by
    /// `scripts/tribunal/g06_fuel_probe.sh`.
    const RECEIPT: &str = include_str!("../evidence/g06_fuel_parity/thresholds_v4.32.0.jsonl");

    #[test]
    fn the_model_reproduces_every_measured_verdict_on_the_pilot_slice() {
        let rows = parse_receipt(RECEIPT).expect("the committed receipt parses");
        let bracketed: Vec<&MeasuredRow> = rows.iter().filter(|r| r.threshold.is_some()).collect();
        // Anti-vacuity floors: the slice has 16 rows, 9 bracketed (WindowsNewlines
        // and every d1 reject are unbracketed — sub-1k or budget-independent).
        assert_eq!(rows.len(), 16, "row census");
        assert_eq!(bracketed.len(), 9, "bracketed census");
        for row in &bracketed {
            let c = row.threshold.unwrap();
            // The measured facts: C-1 times out, C completes — and the model
            // must answer uniformly across the whole measured interval.
            assert_eq!(
                replay_verdict(c, c - 1),
                Some(FuelVerdict::TimedOut),
                "{}: one-under must time out",
                row.file
            );
            assert_eq!(
                replay_verdict(c, c),
                Some(FuelVerdict::Completed),
                "{}: exactly-at must complete (STRICT >)",
                row.file
            );
            // Distant budgets, the corpus table's own grid.
            assert_eq!(
                replay_verdict(c, 2 * c),
                Some(FuelVerdict::Completed),
                "{}",
                row.file
            );
            if c / 2 >= 1 && c / 2 < c - 1 {
                assert_eq!(
                    replay_verdict(c, c / 2),
                    Some(FuelVerdict::TimedOut),
                    "{}: half budget must time out",
                    row.file
                );
            }
            // Budget zero disables the limit at ANY consumption.
            assert_eq!(
                replay_verdict(c, 0),
                Some(FuelVerdict::Completed),
                "{}",
                row.file
            );
        }
    }

    #[test]
    fn the_strict_boundary_is_load_bearing_a_ge_law_diverges_at_exactly_at_budget() {
        // The mutant this kills is the one-tick-off law: a prototype checking
        // `>=` instead of `>` flips exactly-at-budget from Completed to
        // TimedOut. CoreM.lean:490 is strict, and this cell is why the model
        // must be too.
        let mut meter = FuelMeter::new();
        meter.charge(21 * TICKS_PER_UNIT);
        assert_eq!(
            meter.verdict(21),
            FuelVerdict::Completed,
            "exactly-at passes"
        );
        meter.charge(1);
        assert_eq!(
            meter.verdict(21),
            FuelVerdict::TimedOut,
            "one tick over fails"
        );
    }

    #[test]
    fn dropped_and_doubled_charges_are_visible_at_the_measured_edges() {
        // A charge law that drops or doubles ticks moves the verdict at the
        // interval edges the bisection pinned — the compensating-error shapes
        // the design clause names cannot cancel at BOTH edges of a 1000-tick
        // interval bounded by real measurements.
        let c = 21u64;
        let mut dropped = FuelMeter::new();
        dropped.charge(c * TICKS_PER_UNIT - TICKS_PER_UNIT); // one unit short
        assert_eq!(
            dropped.verdict(c - 1),
            FuelVerdict::Completed,
            "a dropped-unit meter no longer times out at C-1 — detectable"
        );
        let mut doubled = FuelMeter::new();
        doubled.charge(2 * c * TICKS_PER_UNIT);
        assert_eq!(
            doubled.verdict(c),
            FuelVerdict::TimedOut,
            "a doubled meter times out at C where the Reference completes — detectable"
        );
    }

    #[test]
    fn overflow_is_sticky_inconclusive_never_a_verdict() {
        let mut meter = FuelMeter::new();
        meter.charge(u64::MAX - 5);
        meter.charge(100); // overflows
        assert_eq!(
            meter.verdict(0),
            FuelVerdict::Inconclusive,
            "even unlimited refuses"
        );
        assert_eq!(meter.verdict(u64::MAX), FuelVerdict::Inconclusive);
        assert_eq!(meter.verdict(1), FuelVerdict::Inconclusive);
        // And it stays poisoned: further charges do not un-overflow it.
        meter.charge(1);
        assert_eq!(meter.verdict(1), FuelVerdict::Inconclusive);
    }

    #[test]
    fn the_depth_meter_reproduces_the_measured_flip_and_unwind_restores() {
        // The measured cell: a shape needing 806 frames fails at maxRecDepth=805
        // and succeeds at 806, byte-identical edges (bead comment 1664).
        let needed = 806usize;
        let run = |max: usize| -> Result<(), DepthExceeded> {
            let mut meter = RecDepthMeter::new(max);
            for _ in 0..needed {
                meter.enter()?;
            }
            for _ in 0..needed {
                meter.leave();
            }
            Ok(())
        };
        assert_eq!(
            run(805),
            Err(DepthExceeded {
                needed: 806,
                max: 805
            }),
            "805 must refuse at the 806th frame"
        );
        assert_eq!(run(806), Ok(()), "806 must complete");
        assert_eq!(run(0), Ok(()), "zero is no limit");
        // Unwind: an error path restoring to a checkpoint really restores.
        let mut meter = RecDepthMeter::new(10);
        for _ in 0..9 {
            meter.enter().expect("under limit");
        }
        let checkpoint = 3;
        meter.unwind_to(checkpoint);
        assert_eq!(meter.depth(), checkpoint);
        for _ in 0..7 {
            meter.enter().expect("post-unwind headroom is real");
        }
        assert!(
            meter.enter().is_err(),
            "and the limit still holds after unwind"
        );
    }

    #[test]
    fn the_replay_is_schedule_independent_at_1_8_and_32_workers() {
        // The bead's thread clause at prototype scale: verdict replay of the
        // measured rows partitioned across real threads, canonical reduction
        // (a sorted verdict table — parallel work, set-reduced), identical at
        // every width and equal to the serial computation.
        let rows = parse_receipt(RECEIPT).expect("parses");
        let work: Vec<(String, u64)> = rows
            .iter()
            .filter_map(|r| r.threshold.map(|c| (r.file.clone(), c)))
            .collect();
        let grid = |c: u64| [c - 1, c, 2 * c, (c / 2).max(1)];
        let score = |part: &[(String, u64)]| -> Vec<(String, u64, Vec<Option<FuelVerdict>>)> {
            part.iter()
                .map(|(f, c)| {
                    (
                        f.clone(),
                        *c,
                        grid(*c).iter().map(|b| replay_verdict(*c, *b)).collect(),
                    )
                })
                .collect()
        };
        let serial = {
            let mut v = score(&work);
            v.sort();
            v
        };
        for workers in [1usize, 8, 32] {
            let workers = workers.min(work.len());
            let chunk = work.len().div_ceil(workers);
            let mut merged: Vec<_> = std::thread::scope(|scope| {
                let handles: Vec<_> = work
                    .chunks(chunk)
                    .map(|part| scope.spawn(move || score(part)))
                    .collect();
                handles
                    .into_iter()
                    .flat_map(|h| h.join().expect("worker"))
                    .collect()
            });
            merged.sort();
            assert_eq!(merged, serial, "verdict table at {workers} workers");
        }
    }

    #[test]
    fn hostile_receipt_bytes_refuse_typed_never_panic() {
        for junk in [
            "not json at all",
            "{\"schema\":\"fln-g06-fuel-thresholds/1\",\"file\":\"x\"}",
            "{\"schema\":\"wrong/9\",\"file\":\"x\",\"family\":\"c1\",\"threshold\":3}",
            "{\"schema\":\"fln-g06-fuel-thresholds/1\",\"file\":\"x\",\"family\":\"c1\",\"threshold\":\"banana\"}",
        ] {
            assert!(parse_receipt(junk).is_err(), "must refuse: {junk}");
        }
        assert_eq!(parse_receipt("").expect("empty is zero rows").len(), 0);
    }
}
