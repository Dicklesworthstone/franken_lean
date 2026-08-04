//! `closure_binding_population` — the guard for the closure-binding exempt/bound/complete
//! disclosure in AGENTS.md (bead `franken_lean-closure-binding-exempt-rows-uninspected-3s8w`).
//!
//! # What this exists for
//!
//! The closure-binding law (bead `fln-judgement-row-not-bound-to-its-closure-iumd`) binds a
//! `complete` coverage row to the closure it judges, but only for beads closed at or after
//! `CLOSURE_BINDING_EFFECTIVE_FROM`. Everything closed before that instant is **exempt by
//! date, never by inspection**, and AGENTS.md discloses the size of that exempt population in
//! prose. That number is the whole subject of `3s8w`: it does not shrink through use, it can
//! grow silently (42 pre-boundary closed beads carry no coverage row at all, and a row added
//! for any of them is exempt *by construction*), and until this file existed nothing rechecked
//! it. AGENTS.md said so itself: "the 105 is a number in a row that nothing rechecks."
//!
//! # The predicate is BORROWED, not re-implemented
//!
//! `scripts/evidence.py validate-verification-manifest` already emits all three figures --
//! `closure_exempt_rows`, `closure_bound_rows`, and `derived_state_counts.complete`. This guard
//! **runs the validator and reads its output**. It contains no second copy of the exemption
//! predicate, because a Rust re-implementation would be a second definition free to drift from
//! the one the manifest is actually judged by -- which is the defect family this bead sits in
//! (AGENTS.md item 7). AGENTS.md prescribed the guard live "in `scripts/evidence.py` beside
//! where `closure_exempt_rows` is produced" for exactly that reason; consuming the producer's
//! own output satisfies the reason without needing to live in the producer.
//!
//! # Why the three figures are bound DIFFERENTLY, which is this guard's whole design
//!
//! AGENTS.md prescribes "equality in both directions, plus the conservation identity
//! `exempt + bound == complete` as the anti-vacuity guard". Applied to all three that is
//! **wrong in one direction and useless in the other**, and both halves were measured before
//! this file was written:
//!
//! * `exempt` is bound by **equality**, both directions. It is the population the bead is
//!   about. It does not fall when someone repairs a row (repairing an exempt row does not move
//!   its bead's `closed_at`), and it rises only when a row is added for a pre-boundary closed
//!   bead. Silent growth there is precisely the defect, so growth must be deliberate: the
//!   author raises the disclosed number and says why.
//!
//! * `bound` and `complete` are bound by a **floor** — they may rise freely and may not fall.
//!   Equality is a wall here: both move on *every close by any pane*, so an equality gate would
//!   redden on exactly the commits that record good work. That is the cry-wolf failure AGENTS.md
//!   already measured once, when an enforcement census drifted 26 -> 27 -> 28 while the live
//!   population never moved. A floor still catches the direction that matters — a close silently
//!   disappearing, or the classifier losing rows.
//!
//! * The conservation identity is kept and is **deliberately labelled weak**. Every `complete`
//!   row is exactly one of exempt or bound, so `exempt + bound == complete` is true by
//!   construction of the classifier: it can only fail if the classifier itself breaks, never
//!   when the populations move. It is a check on the producer's internal consistency, not on
//!   whether the disclosure still describes the tree, and AGENTS.md's passage used one for the
//!   other.
//!
//! The measurement behind that design, taken for this bead on 2026-07-27 and re-taken on
//! 2026-08-04: `exempt` was 105 at every sampling, unmoved across eight days, while `bound`
//! and `complete` each grew by about a hundred rows. **A guard binding only `exempt`, as
//! prescribed, would have been green through the whole of that drift.**
//!
//! The current figures are deliberately NOT repeated here. They live in exactly one place --
//! AGENTS.md's `closure-binding population disclosed by 3s8w:` line, which this guard reads --
//! because `bound` and `complete` move on every close, and a second copy of a moving number
//! in a file nobody re-reads is the drift this bead is about, one floor down.
//!
//! # Anti-vacuity
//!
//! A guard that reads nothing and compares nothing is green. So: the validator must actually
//! run and report `valid`; all three figures must parse out of its JSON; all three must parse
//! out of AGENTS.md's sentence; and a zero from either side is refused as a broken scan rather
//! than reported as agreement. Every one of those refusals is reachable from a test, by
//! injecting the inputs rather than waiting for the day the scan breaks.
//!
//! # What this does not earn
//!
//! It establishes that the disclosed numbers still describe the tree, never that any exempt row
//! is *correct*. The 105 rows remain exempt by date and uninspected; whether a given one was
//! authored for the closure it is filed under is a semantic question no count can answer, and
//! `3s8w` says so. Nothing here reads a row's prose.

#![forbid(unsafe_code)]

use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

fn root() -> PathBuf {
    fln_conformance::checked_workspace_root!()
}

/// The three figures, from whichever side produced them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Population {
    exempt: usize,
    bound: usize,
    complete: usize,
}

/// Materialise a path as HEAD holds it. See [`measure`] for why the committed blob and not
/// the working copy.
fn committed_blob(root: &Path, path: &str, into: &Path) -> Result<PathBuf, String> {
    let output = Command::new("git")
        .args(["show", &format!("HEAD:{path}")])
        .current_dir(root)
        .output()
        .map_err(|error| format!("git could not be launched to read HEAD:{path}: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "HEAD:{path} could not be read ({}), so this guard has no committed state to \
             judge and refuses rather than falling back to the working copy, which in this \
             shared checkout carries other panes' in-flight writes",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let target = into.join(path.rsplit('/').next().unwrap_or(path));
    fs::write(&target, &output.stdout)
        .map_err(|error| format!("the committed blob for {path} could not be staged: {error}"))?;
    Ok(target)
}

/// Run the validator and read its own numbers back. The predicate lives there, not here.
///
/// **It judges HEAD, not the working copy, and that is deliberate.** Six panes share this
/// checkout, and every pane's ordinary `br` command auto-flushes the whole tracker into the
/// shared `.beads/issues.jsonl`. So the working copy routinely holds another pane's half-done
/// close, or a bead at a status the validator's vocabulary does not carry — measured on
/// 2026-08-04, when a peer's `blocked` status made the validator refuse outright while HEAD
/// validated clean. A guard reading the working copy would therefore be a function of other
/// panes' uncommitted work: red for a cause its own author cannot fix, which is the
/// wrong-tree class of defect this repository already pays for elsewhere. The disclosure in
/// AGENTS.md is a claim about the committed repository, so the committed repository is what
/// it is held against.
fn measure(root: &Path) -> Result<(Population, bool), String> {
    let scratch = std::env::var("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| root.join("target"))
        .join(format!("fln-closure-binding-{}", std::process::id()));
    fs::create_dir_all(&scratch)
        .map_err(|error| format!("the scratch directory could not be created: {error}"))?;
    let manifest = committed_blob(root, "ci/VERIFICATION_MANIFEST.jsonl", &scratch)?;
    let beads = committed_blob(root, ".beads/issues.jsonl", &scratch)?;
    let output = Command::new("python3")
        .args([
            "-I",
            "-S",
            "scripts/evidence.py",
            "validate-verification-manifest",
        ])
        .arg("--manifest")
        .arg(&manifest)
        .arg("--beads")
        .arg(&beads)
        .current_dir(root)
        .output()
        .map_err(|error| format!("the manifest validator could not be launched: {error}"))?;
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    if !output.status.success() {
        return Err(format!(
            "the manifest validator refused the COMMITTED manifest and tracker, so this guard \
             has no measurement to compare against and refuses rather than passing vacuously. \
             Note what this is not: the working copy is not consulted, so a peer's in-flight \
             bead cannot cause this. A refusal here means a landed commit carries a manifest \
             the validator rejects.\n\nstdout: {stdout}\nstderr: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    parse_validator(&stdout)
}

/// Pull the three figures out of the validator's report without a JSON dependency: the
/// closed dependency universe (D1) has no serde, so this reads the flat fields it needs and
/// **refuses** anything it cannot find rather than defaulting to zero.
fn parse_validator(stdout: &str) -> Result<(Population, bool), String> {
    fn number(text: &str, key: &str) -> Result<usize, String> {
        let needle = format!("\"{key}\":");
        let start = text
            .find(&needle)
            .ok_or_else(|| format!("the validator report carries no {key:?} field"))?
            + needle.len();
        let rest = text[start..].trim_start();
        let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
        if digits.is_empty() {
            return Err(format!("the validator's {key:?} field is not a number"));
        }
        digits
            .parse()
            .map_err(|_| format!("the validator's {key:?} field does not parse"))
    }
    // `complete` lives inside derived_state_counts, so scope the search to that object rather
    // than to the whole report: a bare "complete" search would also match any other object
    // that grows one.
    let counts_start = stdout
        .find("\"derived_state_counts\":")
        .ok_or_else(|| "the validator report carries no derived_state_counts".to_owned())?;
    let counts_end = stdout[counts_start..]
        .find('}')
        .ok_or_else(|| "derived_state_counts is not a closed object".to_owned())?
        + counts_start;
    let complete = number(&stdout[counts_start..=counts_end], "complete")?;
    let valid = stdout.contains("\"valid\":true");
    Ok((
        Population {
            exempt: number(stdout, "closure_exempt_rows")?,
            bound: number(stdout, "closure_bound_rows")?,
            complete,
        },
        valid,
    ))
}

/// The sentence in AGENTS.md that this guard holds to the tree. Written as one line so a
/// hard wrap cannot separate a number from the word that types it.
const DISCLOSURE_NEEDLE: &str = "closure-binding population disclosed by 3s8w:";

/// Read the disclosed figures out of AGENTS.md. Refuses a missing or unparsable disclosure --
/// a guard that silently finds nothing to compare is the vacuity this file exists to avoid.
fn disclosed(agents: &str) -> Result<Population, String> {
    let line = agents
        .lines()
        .find(|line| line.contains(DISCLOSURE_NEEDLE))
        .ok_or_else(|| {
            format!(
                "AGENTS.md no longer carries the closure-binding disclosure line \
                 ({DISCLOSURE_NEEDLE:?}). The number this guard exists to hold has been \
                 deleted or reworded, which is exactly the silent movement it watches for, so \
                 it refuses rather than passing with nothing to compare."
            )
        })?;
    fn field(line: &str, key: &str) -> Result<usize, String> {
        let start = line
            .find(&format!("{key}="))
            .ok_or_else(|| format!("the disclosure line carries no {key}="))?
            + key.len()
            + 1;
        let digits: String = line[start..]
            .chars()
            .take_while(char::is_ascii_digit)
            .collect();
        if digits.is_empty() {
            return Err(format!("the disclosure's {key}= is not a number"));
        }
        digits
            .parse()
            .map_err(|_| format!("the disclosure's {key}= does not parse"))
    }
    Ok(Population {
        exempt: field(line, "exempt")?,
        bound: field(line, "bound-floor")?,
        complete: field(line, "complete-floor")?,
    })
}

/// The judgement, in one place so every cell below exercises the same rules.
fn judge(disclosed: Population, measured: Population, valid: bool) -> Vec<String> {
    let mut faults = Vec::new();

    if !valid {
        faults.push(
            "the validator did not report valid=true, so its population figures describe a \
             manifest it has already rejected and this guard will not compare against them"
                .to_owned(),
        );
    }

    // Anti-vacuity, both sides. A zero here is a broken scan, not a clean tree: there is no
    // state of this repository in which zero rows are complete.
    if measured.complete == 0 || measured.exempt == 0 {
        faults.push(format!(
            "the validator reported exempt={} complete={}; a zero on either is a broken \
             measurement rather than a population, and comparing against it would make every \
             disclosure agree vacuously",
            measured.exempt, measured.complete
        ));
    }
    if disclosed.complete == 0 || disclosed.exempt == 0 {
        faults.push(format!(
            "AGENTS.md discloses exempt={} complete-floor={}; a zeroed disclosure agrees with \
             anything and is refused",
            disclosed.exempt, disclosed.complete
        ));
    }

    // exempt: EQUALITY, both directions. This is the population 3s8w is about.
    if disclosed.exempt != measured.exempt {
        faults.push(format!(
            "the disclosed closure-binding-exempt population no longer describes this tree: \
             AGENTS.md says exempt={}, the validator measures {} ({:+}).\n\nEquality is \
             required in BOTH directions and that is deliberate. The exempt set does not shrink \
             when a row is repaired -- repairing it does not move its bead's closed_at -- and it \
             grows whenever a coverage row is added for a bead that closed before \
             CLOSURE_BINDING_EFFECTIVE_FROM, which is exempt by construction and needs no one's \
             permission. Growth is the defect this number exists to make visible, so raise it \
             deliberately and say why. Do NOT move CLOSURE_BINDING_EFFECTIVE_FROM to make this \
             agree: that reddens the workspace over history nobody can repair.",
            disclosed.exempt,
            measured.exempt,
            measured.exempt as isize - disclosed.exempt as isize
        ));
    }

    // bound and complete: FLOORS. They rise on every close; equality would be a wall.
    for (label, floor, now) in [
        ("bound-floor", disclosed.bound, measured.bound),
        ("complete-floor", disclosed.complete, measured.complete),
    ] {
        if now < floor {
            faults.push(format!(
                "{label} fell: AGENTS.md discloses {floor}, the validator measures {now} \
                 ({:+}). These two are floors rather than equalities because both rise on \
                 every close by any pane, so an equality gate would redden on exactly the \
                 commits that record good work. A FALL is different: it means a close \
                 disappeared from the tracker, a coverage row was removed, or the classifier \
                 stopped counting rows it used to count.",
                now as isize - floor as isize
            ));
        }
    }

    // The partition. Labelled weak in the module header and checked anyway, because the one
    // thing it does catch -- the classifier itself breaking -- is the thing that would make
    // every other comparison here meaningless.
    if measured.exempt + measured.bound != measured.complete {
        faults.push(format!(
            "the producer's own partition broke: exempt {} + bound {} != complete {}. Every \
             complete row is exactly one of exempt or bound, so this cannot fail when the \
             populations merely move -- it fails when the classifier does, which invalidates \
             the other comparisons in this guard rather than merely disagreeing with them",
            measured.exempt, measured.bound, measured.complete
        ));
    }

    faults
}

#[test]
fn the_closure_binding_disclosure_still_describes_this_tree() {
    let root = root();
    let agents = fs::read_to_string(root.join("AGENTS.md")).expect("AGENTS.md must be readable");
    let disclosed = disclosed(&agents).expect("AGENTS.md must carry a parsable disclosure");
    let (measured, valid) = match measure(&root) {
        Ok(pair) => pair,
        Err(reason) => panic!("{reason}"),
    };
    let faults = judge(disclosed, measured, valid);
    assert!(
        faults.is_empty(),
        "the closure-binding population disclosure and the tree disagree:\n\n{}",
        faults.join("\n\n")
    );
}

#[test]
fn the_disclosure_is_parsed_rather_than_assumed() {
    // The positive control for the reader: without it, a disclosure guard that could never
    // parse anything would still pass every negative cell below.
    let line = "closure-binding population disclosed by 3s8w: exempt=105 (equality, both \
                directions) bound-floor=107 complete-floor=212";
    let parsed = disclosed(line).expect("the canonical disclosure line must parse");
    assert_eq!(
        parsed,
        Population {
            exempt: 105,
            bound: 107,
            complete: 212
        }
    );
}

#[test]
fn a_missing_disclosure_refuses_rather_than_passing() {
    let error = disclosed("AGENTS.md with the sentence deleted\n").expect_err(
        "a deleted disclosure must refuse: silently finding nothing to compare is the \
         vacuity this guard exists to avoid",
    );
    assert!(error.contains("no longer carries"), "{error}");
}

#[test]
fn a_disclosure_missing_one_field_refuses_rather_than_defaulting() {
    let line = "closure-binding population disclosed by 3s8w: exempt=105 complete-floor=212";
    let error = disclosed(line).expect_err("a disclosure missing bound-floor must refuse");
    assert!(error.contains("bound-floor"), "{error}");
}

#[test]
fn exempt_growth_is_refused_in_the_direction_that_hides_it() {
    // The defect 3s8w is named for: a coverage row added for a pre-boundary closed bead joins
    // the exempt set by construction, and nobody had to agree to it.
    let disclosed = Population {
        exempt: 105,
        bound: 107,
        complete: 212,
    };
    let measured = Population {
        exempt: 106,
        bound: 107,
        complete: 213,
    };
    let faults = judge(disclosed, measured, true);
    assert!(
        faults.iter().any(|fault| fault.contains("exempt=105")
            && fault.contains("measures 106")
            && fault.contains("BOTH directions")),
        "{faults:?}"
    );
}

#[test]
fn exempt_shrinkage_is_refused_too_because_the_set_does_not_shrink_on_repair() {
    let disclosed = Population {
        exempt: 105,
        bound: 107,
        complete: 212,
    };
    let measured = Population {
        exempt: 104,
        bound: 107,
        complete: 211,
    };
    let faults = judge(disclosed, measured, true);
    assert!(
        faults.iter().any(|fault| fault.contains("measures 104")),
        "a one-way allowance would let the exempt population fall unremarked, and repairing \
         an exempt row does not move its bead's closed_at, so a fall is not a repair: {faults:?}"
    );
}

#[test]
fn an_ordinary_close_does_not_redden_the_bound_and_complete_floors() {
    // The wall this design exists to avoid. Every pane's close raises both figures; under an
    // equality gate this cell would be a failure, and the guard would be reverted within a day.
    let disclosed = Population {
        exempt: 105,
        bound: 107,
        complete: 212,
    };
    let measured = Population {
        exempt: 105,
        bound: 108,
        complete: 213,
    };
    assert!(
        judge(disclosed, measured, true).is_empty(),
        "a close raised bound and complete by one each, which is the normal event this guard \
         must not fire on"
    );
}

#[test]
fn a_fallen_bound_floor_is_refused() {
    let disclosed = Population {
        exempt: 105,
        bound: 107,
        complete: 212,
    };
    let measured = Population {
        exempt: 105,
        bound: 106,
        complete: 211,
    };
    let faults = judge(disclosed, measured, true);
    assert!(
        faults
            .iter()
            .any(|fault| fault.starts_with("bound-floor fell")),
        "{faults:?}"
    );
}

#[test]
fn a_broken_partition_is_refused_even_when_every_figure_matches_its_disclosure() {
    // exempt equals its disclosure and both floors hold, so every other rule here is satisfied.
    // Only the partition catches it, which is the one thing that check is for.
    let disclosed = Population {
        exempt: 105,
        bound: 107,
        complete: 212,
    };
    let measured = Population {
        exempt: 105,
        bound: 107,
        complete: 213,
    };
    let faults = judge(disclosed, measured, true);
    assert!(
        faults
            .iter()
            .any(|fault| fault.contains("the producer's own partition broke")),
        "{faults:?}"
    );
}

#[test]
fn a_zeroed_measurement_is_refused_as_a_broken_scan() {
    let disclosed = Population {
        exempt: 0,
        bound: 0,
        complete: 0,
    };
    let measured = Population {
        exempt: 0,
        bound: 0,
        complete: 0,
    };
    // Every equality and every floor is satisfied by zeros, and the partition holds: 0 + 0 == 0.
    // Without the anti-vacuity rule this is a passing guard that measured nothing.
    let faults = judge(disclosed, measured, true);
    assert!(
        faults
            .iter()
            .any(|fault| fault.contains("broken measurement")),
        "{faults:?}"
    );
    assert!(
        faults
            .iter()
            .any(|fault| fault.contains("zeroed disclosure")),
        "{faults:?}"
    );
}

#[test]
fn a_validator_that_did_not_report_valid_is_not_compared_against() {
    let population = Population {
        exempt: 105,
        bound: 107,
        complete: 212,
    };
    let faults = judge(population, population, false);
    assert!(
        faults
            .iter()
            .any(|fault| fault.contains("did not report valid=true")),
        "{faults:?}"
    );
}

#[test]
fn the_validator_report_parser_refuses_a_report_it_cannot_read() {
    assert!(parse_validator("{}").is_err());
    assert!(parse_validator("{\"closure_exempt_rows\":105}").is_err());
    // Present but not a number: the field exists, so a `find`-only check would accept it.
    assert!(
        parse_validator(
            "{\"closure_exempt_rows\":null,\"closure_bound_rows\":1,\
             \"derived_state_counts\":{\"complete\":1}}"
        )
        .is_err()
    );
    // The positive control: a well-formed report parses, so the refusals above are about the
    // input rather than a parser that can never succeed.
    let (population, valid) = parse_validator(
        "{\"closure_bound_rows\":107,\"closure_exempt_rows\":105,\
         \"derived_state_counts\":{\"active\":25,\"complete\":212},\"valid\":true}",
    )
    .expect("a well-formed validator report must parse");
    assert_eq!(
        population,
        Population {
            exempt: 105,
            bound: 107,
            complete: 212
        }
    );
    assert!(valid);
}

#[test]
fn complete_is_read_from_the_state_counts_rather_than_from_anywhere_it_appears() {
    // `complete` is a common word in this report's neighbourhood. Scoping the search to
    // derived_state_counts is load-bearing: a bare search would bind the guard to whichever
    // object grew a `complete` field first, and nothing would say so.
    let (population, _) = parse_validator(
        "{\"bundle\":{\"complete\":9999},\"closure_bound_rows\":107,\
         \"closure_exempt_rows\":105,\"derived_state_counts\":{\"complete\":212},\
         \"valid\":true}",
    )
    .expect("the report must parse");
    assert_eq!(
        population.complete, 212,
        "complete was read from the wrong object"
    );
}
