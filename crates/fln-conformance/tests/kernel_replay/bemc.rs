//! Judge each transported mutation twice, against immutable imports only.
//! No acceptance, rejection, or missing answer can change the next trial.
use super::*;
use fln_checker::admit::{Verdict as CheckerVerdict, admit};
use fln_checker::environment::{ConstantEnvironment, EnvironmentOutcome};
use fln_checker::wire::{NamePart, WireName};

fn core_name(name: &WireName) -> Name {
    name.parts()
        .iter()
        .fold(Name::anonymous(), |prefix, part| match part {
            NamePart::Text(s) => Name::str(prefix, s.as_str()),
            NamePart::Numeric {
                value,
                overflowed: false,
            } => Name::num(prefix, *value),
            NamePart::Numeric {
                value,
                overflowed: true,
            } => Name::num_overflowing(prefix, *value),
        })
}

pub(super) fn judge(
    inventory: &CorpusInventory,
    chosen: &str,
    pin: &HashMap<String, (String, String)>,
) {
    let require_complete = match std::env::var("FLN_BEMC_REQUIRE_COMPLETE_CHECKER").as_deref() {
        Err(std::env::VarError::NotPresent) | Ok("0") => false,
        Ok("1") => true,
        _ => panic!("FLN_BEMC_REQUIRE_COMPLETE_CHECKER must be 0 or 1"),
    };
    let min_checker_rejects = std::env::var_os("FLN_BEMC_MIN_CHECKER_REJECTS").map(|value| {
        value
            .to_str()
            .and_then(|s| s.parse::<std::num::NonZeroU64>().ok())
            .expect("FLN_BEMC_MIN_CHECKER_REJECTS must be a positive integer")
            .get()
    });
    let limits = fln::CheckerExecutionLimits::default();
    let mut context = ReferenceFixtureContext::new();
    let mut checker = ConstantEnvironment::empty();
    let mut k1_rows = Vec::new();
    let mut checker_rows = Vec::new();

    for module in corpus_module_order(inventory).expect("order mutation batch imports") {
        let source = &inventory.modules[&module];
        let (decoded, reading) = decode_corpus_module_with(&source.path, &module, |parts| {
            fln_checker::olean::read_constants(parts, WalkBudget::default().max_objects)
                .map_err(|err| format!("checker reading of {module}: {err}"))
        })
        .unwrap_or_else(|err| panic!("{module}: {err}"));
        assert_eq!(
            decoded.olean_hash, source.olean_hash,
            "{module}: bytes changed since inventory"
        );
        let checker_imports: BTreeSet<_> = reading
            .imports
            .iter()
            .map(|import| core_name(&import.module).to_display_string())
            .collect();
        assert_eq!(
            checker_imports, source.imports,
            "{module}: decoder import sets differ"
        );
        // The pin takes a module's last serialized row for a repeated name.
        let (active, _, _) = reference_active_rows(&decoded.infos);
        let mut independent: BTreeMap<_, _> = reading
            .constants
            .into_iter()
            .map(|entry| (core_name(entry.name()), entry))
            .collect();
        assert_eq!(
            active.len(),
            independent.len(),
            "{module}: decoder name inventories differ"
        );
        for info in &active {
            let entry = independent
                .remove(info.name())
                .expect("both decoders must read this name");
            if module != chosen {
                // Match the first representative in the replay environment;
                // extend_reference_fixture_environment verifies every collision.
                if context.environment.contains(info.name()) {
                    continue;
                }
                checker = match checker.extend(entry, limits.environment) {
                    EnvironmentOutcome::Complete { environment, .. } => environment,
                    outcome => panic!(
                        "{module}: checker import {}: {outcome:?}",
                        info.name().to_display_string()
                    ),
                };
                continue;
            }
            let lead = info.name().to_display_string();
            let decl = match info {
                ConstantInfo::Thm(value) => Declaration::Thm(value.clone()),
                ConstantInfo::Defn(value) => Declaration::Defn(value.clone()),
                _ => panic!("{module}: unexpected transported declaration {lead}"),
            };
            let (outcome, class, message, _, _) = verdict_facts(&fln_kernel::check(
                &context.environment,
                &decl,
                Budget::DEFAULT,
            ));
            k1_rows.push(BemcJudgedRow {
                lead: lead.clone(),
                outcome: class
                    .map_or_else(|| outcome.clone(), |class| format!("{outcome}:{class}")),
                message,
            });
            let verdict = admit(&checker, &entry, limits.admission);
            let outcome = match &verdict {
                CheckerVerdict::Admitted(_) => "accepted",
                CheckerVerdict::Rejected(_) => "rejected",
                CheckerVerdict::Deferred(_) => "deferred",
                CheckerVerdict::Inconclusive(_) => "inconclusive",
                CheckerVerdict::InternalFault(_) => "internal-fault",
            };
            checker_rows.push(BemcJudgedRow {
                lead,
                outcome: outcome.into(),
                message: format!("{verdict:?}"),
            });
        }
        if module == chosen {
            break;
        }
        let (next, merge) = extend_reference_fixture_environment(context, &active, &module)
            .expect("prepare original Reference fixture imports");
        assert!(
            merge.collisions.is_empty(),
            "{module}: incompatible imports: {:?}",
            merge.collisions
        );
        context = next;
    }

    let mut clean = true;
    for (engine, rows) in [("K1", k1_rows), ("fln-checker", checker_rows)] {
        let cells = join_bemc_rows(&rows, pin).expect("one seat verdict per pin name");
        eprintln!(
            "bemc-join module={chosen} engine={engine} joined={} agree_reject={} agree_accept={} deferred_on_pin_reject={} other={} inconclusive={} fatal={}",
            cells.joined,
            cells.agree_reject,
            cells.agree_accept,
            cells.deferred_rejects.len(),
            cells.other.len(),
            cells.inconclusive.len(),
            cells.fatal.len()
        );
        // The scheduled lane requires an actual rejection when there are
        // negative controls. A checker that defers every one cannot pass.
        if !cells.deferred_rejects.is_empty() && (require_complete || cells.agree_reject == 0) {
            clean = false;
        }
        if engine == "fln-checker"
            && let Some(minimum) = min_checker_rejects
            && cells.agree_reject < minimum
        {
            eprintln!(
                "bemc-coverage module={chosen} engine={engine} observed_rejects={} required_rejects={minimum}",
                cells.agree_reject
            );
            clean = false;
        }
        for row in cells.deferred_rejects {
            eprintln!("bemc-row engine={engine} uncovered {row}");
        }
        for (kind, findings) in [
            ("FATAL", cells.fatal),
            ("inconclusive", cells.inconclusive),
            ("divergence", cells.other),
        ] {
            for row in findings {
                eprintln!("bemc-row engine={engine} {kind} {row}");
                clean = false;
            }
        }
    }
    assert!(
        clean,
        "{chosen}: divergent judgments or required coverage missing"
    );
}
