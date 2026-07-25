//! CLI for the structural gate. See `lib.rs` for what is enforced.
//!
//! Usage: `structure-guard [--root <path>] [--robot]
//!        structure-guard --publish-contract-inventory [--root <path>] [--robot]
//!        structure-guard --recover-contract-inventory [--root <path>] [--robot]
//!        structure-guard --publish-contract-handoff [--root <path>] [--robot]
//!        structure-guard --recover-contract-handoff [--root <path>] [--robot]`
//! Exit codes: 0 = clean, 1 = findings, 2 = setup/parse failure at the root.

#![forbid(unsafe_code)]

use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Instant;

use structure_guard::contract_handoff;
use structure_guard::contract_inventory::{
    self, ABI_EXTRACTOR_ID, ABI_EXTRACTOR_VERSION, DEFINITION_SCHEMA, EXTRACTOR_ID,
    EXTRACTOR_VERSION, FORMAT_EXTRACTOR_ID, FORMAT_EXTRACTOR_VERSION, INVENTORY_SCHEMA,
    InventoryError, MAX_LINE_BYTES, MAX_ROWS, MAX_SOURCE_BYTES, POLICY_SCHEMA, PublicationReceipt,
};
use structure_guard::{checks, report};

const PUBLICATION_SCENARIO_ID: &str = "fln-k5rr.contract-inventory-atomic-publication";
const HANDOFF_SCENARIO_ID: &str = "franken_lean-w75y.contract-handoff-atomic-publication";

const USAGE: &str = "usage: structure-guard [--root <path>] [--robot]\n\
       structure-guard --publish-contract-inventory [--root <path>] [--robot]\n\
       structure-guard --recover-contract-inventory [--root <path>] [--robot]\n\
       structure-guard --publish-contract-handoff [--root <path>] [--robot]\n\
       structure-guard --recover-contract-handoff [--root <path>] [--robot]\n\
  --root <path>  workspace root to check (default: current directory)\n\
  --robot        NDJSON output (schema structure-guard/3) on stdout\n\
  --publish-contract-inventory  validate, sync, and atomically publish a candidate\n\
  --recover-contract-inventory  validate and atomically promote a leftover candidate\n\
  --publish-contract-handoff  validate every rendered contract output and atomically publish their join\n\
  --recover-contract-handoff  validate and atomically promote a leftover handoff candidate\n\
exit codes: 0 clean, 1 findings, 2 setup failure, 3 inconclusive authority";

#[derive(Debug, Eq, PartialEq)]
enum CliAction {
    Run { root: PathBuf, robot: bool },
    PublishInventory { root: PathBuf, robot: bool },
    RecoverInventory { root: PathBuf, robot: bool },
    PublishHandoff { root: PathBuf, robot: bool },
    RecoverHandoff { root: PathBuf, robot: bool },
    Help { robot: bool },
}

#[derive(Debug, Eq, PartialEq)]
struct CliError {
    root: PathBuf,
    robot: bool,
    detail: String,
}

fn is_option(value: &OsStr) -> bool {
    value.to_string_lossy().starts_with('-')
}

/// Parse only after pre-scanning for `--robot`. Robot mode is a property of the
/// complete request, not of how far parsing progressed, so even an earlier malformed
/// argument must produce the versioned machine contract rather than human stderr.
fn parse_cli(args: &[OsString]) -> Result<CliAction, CliError> {
    let robot = args.iter().any(|arg| arg == "--robot");
    let mut root = PathBuf::from(".");
    let mut root_seen = false;
    let mut help = false;
    let mut publication_action: Option<&'static str> = None;
    let mut index = 0;

    while index < args.len() {
        let arg = &args[index];
        if arg == "--root" {
            index += 1;
            let Some(value) = args.get(index) else {
                return Err(CliError {
                    root,
                    robot,
                    detail: "--root requires a path".to_string(),
                });
            };
            if is_option(value) {
                return Err(CliError {
                    root,
                    robot,
                    detail: "--root requires a path".to_string(),
                });
            }
            // A trusted gate must never accept an ambiguous target. Silently taking the
            // last `--root` would let an injected argument redirect validation away from
            // the workspace the caller believes is being checked, so a repeated flag is
            // a setup failure whether or not the two paths agree.
            if root_seen {
                return Err(CliError {
                    root,
                    robot,
                    detail: "--root given more than once; the workspace root under check must be unambiguous".to_string(),
                });
            }
            root_seen = true;
            root = PathBuf::from(value);
        } else if arg == "--robot" {
            // Already captured by the whole-request pre-scan.
        } else if arg == "--publish-contract-inventory" {
            if publication_action.replace("publish").is_some() {
                return Err(CliError {
                    root,
                    robot,
                    detail:
                        "contract inventory publication action given more than once or conflicts with recovery"
                            .to_string(),
                });
            }
        } else if arg == "--recover-contract-inventory" {
            if publication_action.replace("recover-inventory").is_some() {
                return Err(CliError {
                    root,
                    robot,
                    detail:
                        "contract inventory recovery action given more than once or conflicts with publication"
                            .to_string(),
                });
            }
        } else if arg == "--publish-contract-handoff" {
            if publication_action.replace("publish-handoff").is_some() {
                return Err(CliError {
                    root,
                    robot,
                    detail:
                        "contract publication action given more than once or conflicts with another publication action"
                            .to_string(),
                });
            }
        } else if arg == "--recover-contract-handoff" {
            if publication_action.replace("recover-handoff").is_some() {
                return Err(CliError {
                    root,
                    robot,
                    detail:
                        "contract publication action given more than once or conflicts with another publication action"
                            .to_string(),
                });
            }
        } else if arg == "--help" || arg == "-h" {
            help = true;
        } else {
            return Err(CliError {
                root,
                robot,
                detail: format!("unknown argument `{}`", arg.to_string_lossy()),
            });
        }
        index += 1;
    }

    if help {
        Ok(CliAction::Help { robot })
    } else {
        match publication_action {
            Some("publish") => Ok(CliAction::PublishInventory { root, robot }),
            Some("recover-inventory") => Ok(CliAction::RecoverInventory { root, robot }),
            Some("publish-handoff") => Ok(CliAction::PublishHandoff { root, robot }),
            Some("recover-handoff") => Ok(CliAction::RecoverHandoff { root, robot }),
            None => Ok(CliAction::Run { root, robot }),
            Some(_) => unreachable!("closed publication action parser"),
        }
    }
}

fn success_step_id(action: &str) -> &'static str {
    match action {
        "published" => "publish.atomic-commit",
        "recovered" => "recover.atomic-commit",
        _ => "unknown.atomic-commit",
    }
}

fn success_stage(action: &str) -> &'static str {
    match action {
        "published" => "candidate-validated-renamed-and-directory-synced",
        "recovered" => "candidate-revalidated-renamed-and-directory-synced",
        _ => "unknown-commit-stage",
    }
}

fn requested_step_id(action: &str) -> &'static str {
    match action {
        "publish" => "publish.refused",
        "recover" => "recover.refused",
        _ => "unknown.refused",
    }
}

fn render_publication_success(receipt: &PublicationReceipt, duration_ms: u128) -> String {
    let snapshot = &receipt.snapshot;
    let action = receipt.action.as_str();
    let run_id = format!(
        "{PUBLICATION_SCENARIO_ID}:{action}:{}",
        snapshot.inventory_root
    );
    format!(
        "{{\"schema\":\"structure-guard/3\",\"event\":\"contract_inventory_publication\",\"run_id\":\"{}\",\"scenario_id\":\"{PUBLICATION_SCENARIO_ID}\",\"step_id\":\"{}\",\"action\":\"{action}\",\"verdict\":\"pass\",\"exit_code\":0,\"inventory_schema\":\"{INVENTORY_SCHEMA}\",\"definition_schema\":\"{DEFINITION_SCHEMA}\",\"policy_schema\":\"{POLICY_SCHEMA}\",\"extractor_id\":\"{EXTRACTOR_ID}\",\"extractor_version\":\"{EXTRACTOR_VERSION}\",\"abi_extractor_id\":\"{ABI_EXTRACTOR_ID}\",\"abi_extractor_version\":\"{ABI_EXTRACTOR_VERSION}\",\"format_extractor_id\":\"{FORMAT_EXTRACTOR_ID}\",\"format_extractor_version\":\"{FORMAT_EXTRACTOR_VERSION}\",\"reference_root\":\"{}\",\"suite_lock_root\":\"{}\",\"abi_target_layout_root\":\"{}\",\"olean_ilean_format_root\":\"{}\",\"schema_root\":\"{}\",\"target_facts\":{{\"rows\":{},\"certified_rows\":{},\"abi_rows\":{},\"format_rows\":{}}},\"raw_root\":\"{}\",\"canonical_root\":\"{}\",\"policy_root\":\"{}\",\"rows_total\":{},\"unresolved_rows\":{},\"resource_facts\":{{\"source_bytes\":{},\"canonical_bytes\":{},\"max_source_bytes\":{MAX_SOURCE_BYTES},\"max_rows\":{MAX_ROWS},\"max_line_bytes\":{MAX_LINE_BYTES}}},\"publication_stage\":\"{}\",\"authority\":\"complete\",\"cleanup\":\"candidate_absent\",\"final_published_root\":\"{}\",\"duration_ms\":{duration_ms}}}\n",
        report::json_escape(&run_id),
        success_step_id(action),
        report::json_escape(&snapshot.reference_root),
        report::json_escape(&snapshot.suite_lock_root),
        report::json_escape(&snapshot.abi_target_layout_root),
        report::json_escape(&snapshot.olean_ilean_format_root),
        report::json_escape(&snapshot.schema_root),
        snapshot.target_row_count,
        snapshot.target_row_count,
        snapshot.abi_row_count,
        snapshot.format_row_count,
        report::json_escape(&snapshot.raw_root),
        report::json_escape(&snapshot.inventory_root),
        report::json_escape(&snapshot.policy_root),
        snapshot.row_count,
        snapshot.unresolved_row_count,
        snapshot.source_bytes,
        snapshot.canonical_bytes,
        success_stage(action),
        report::json_escape(&snapshot.inventory_root),
    )
}

fn render_publication_failure(
    requested_action: &str,
    error: &InventoryError,
    duration_ms: u128,
) -> String {
    let run_id = format!(
        "{PUBLICATION_SCENARIO_ID}:{requested_action}:{}",
        error.reason
    );
    format!(
        "{{\"schema\":\"structure-guard/3\",\"event\":\"contract_inventory_publication\",\"run_id\":\"{}\",\"scenario_id\":\"{PUBLICATION_SCENARIO_ID}\",\"step_id\":\"{}\",\"action\":\"{}\",\"verdict\":\"{}\",\"exit_code\":{},\"inventory_schema\":\"{INVENTORY_SCHEMA}\",\"definition_schema\":\"{DEFINITION_SCHEMA}\",\"policy_schema\":\"{POLICY_SCHEMA}\",\"extractor_id\":\"{EXTRACTOR_ID}\",\"extractor_version\":\"{EXTRACTOR_VERSION}\",\"abi_extractor_id\":\"{ABI_EXTRACTOR_ID}\",\"abi_extractor_version\":\"{ABI_EXTRACTOR_VERSION}\",\"format_extractor_id\":\"{FORMAT_EXTRACTOR_ID}\",\"format_extractor_version\":\"{FORMAT_EXTRACTOR_VERSION}\",\"reference_root\":null,\"suite_lock_root\":null,\"abi_target_layout_root\":null,\"olean_ilean_format_root\":null,\"schema_root\":null,\"target_facts\":null,\"raw_root\":null,\"canonical_root\":null,\"policy_root\":null,\"rows_total\":null,\"unresolved_rows\":null,\"resource_facts\":{{\"source_bytes\":null,\"canonical_bytes\":null,\"max_source_bytes\":{MAX_SOURCE_BYTES},\"max_rows\":{MAX_ROWS},\"max_line_bytes\":{MAX_LINE_BYTES}}},\"publication_stage\":\"refused-or-failed-before-clean-terminal-receipt\",\"authority\":\"{}\",\"cleanup\":\"not_established\",\"final_published_root\":null,\"reason\":\"{}\",\"path\":\"{}\",\"detail\":\"{}\",\"duration_ms\":{duration_ms}}}\n",
        report::json_escape(&run_id),
        requested_step_id(requested_action),
        requested_action,
        error.class.as_str(),
        error.class.exit_code(),
        error.class.as_str(),
        report::json_escape(error.reason),
        report::json_escape(&error.path),
        report::json_escape(&error.detail),
    )
}

fn render_publication_success_human(receipt: &PublicationReceipt, duration_ms: u128) -> String {
    let snapshot = &receipt.snapshot;
    let action = receipt.action.as_str();
    let run_id = format!(
        "{PUBLICATION_SCENARIO_ID}:{action}:{}",
        snapshot.inventory_root
    );
    format!(
        "structure-guard: contract_inventory_publication run_id={run_id} scenario_id={PUBLICATION_SCENARIO_ID} step_id={} action={action} verdict=pass exit_code=0 inventory_schema={INVENTORY_SCHEMA} definition_schema={DEFINITION_SCHEMA} policy_schema={POLICY_SCHEMA} extractor_id={EXTRACTOR_ID} extractor_version={EXTRACTOR_VERSION} abi_extractor_id={ABI_EXTRACTOR_ID} abi_extractor_version={ABI_EXTRACTOR_VERSION} format_extractor_id={FORMAT_EXTRACTOR_ID} format_extractor_version={FORMAT_EXTRACTOR_VERSION} reference_root={} suite_lock_root={} abi_target_layout_root={} olean_ilean_format_root={} schema_root={} target_rows={} target_certified_rows={} abi_rows={} format_rows={} raw_root={} canonical_root={} policy_root={} rows_total={} unresolved_rows={} source_bytes={} canonical_bytes={} max_source_bytes={MAX_SOURCE_BYTES} max_rows={MAX_ROWS} max_line_bytes={MAX_LINE_BYTES} publication_stage={} authority=complete cleanup=candidate_absent final_published_root={} duration_ms={duration_ms}\n",
        success_step_id(action),
        snapshot.reference_root,
        snapshot.suite_lock_root,
        snapshot.abi_target_layout_root,
        snapshot.olean_ilean_format_root,
        snapshot.schema_root,
        snapshot.target_row_count,
        snapshot.target_row_count,
        snapshot.abi_row_count,
        snapshot.format_row_count,
        snapshot.raw_root,
        snapshot.inventory_root,
        snapshot.policy_root,
        snapshot.row_count,
        snapshot.unresolved_row_count,
        snapshot.source_bytes,
        snapshot.canonical_bytes,
        success_stage(action),
        snapshot.inventory_root,
    )
}

fn render_publication_failure_human(
    requested_action: &str,
    error: &InventoryError,
    duration_ms: u128,
) -> String {
    let run_id = format!(
        "{PUBLICATION_SCENARIO_ID}:{requested_action}:{}",
        error.reason
    );
    format!(
        "structure-guard: contract_inventory_publication run_id={run_id} scenario_id={PUBLICATION_SCENARIO_ID} step_id={} action={requested_action} verdict={} exit_code={} inventory_schema={INVENTORY_SCHEMA} definition_schema={DEFINITION_SCHEMA} policy_schema={POLICY_SCHEMA} extractor_id={EXTRACTOR_ID} extractor_version={EXTRACTOR_VERSION} abi_extractor_id={ABI_EXTRACTOR_ID} abi_extractor_version={ABI_EXTRACTOR_VERSION} format_extractor_id={FORMAT_EXTRACTOR_ID} format_extractor_version={FORMAT_EXTRACTOR_VERSION} reference_root=unavailable suite_lock_root=unavailable abi_target_layout_root=unavailable olean_ilean_format_root=unavailable schema_root=unavailable target_facts=unavailable raw_root=unavailable canonical_root=unavailable policy_root=unavailable rows_total=unavailable unresolved_rows=unavailable source_bytes=unavailable canonical_bytes=unavailable max_source_bytes={MAX_SOURCE_BYTES} max_rows={MAX_ROWS} max_line_bytes={MAX_LINE_BYTES} publication_stage=refused-or-failed-before-clean-terminal-receipt authority={} cleanup=not_established final_published_root=unavailable reason={} path={} detail={} duration_ms={duration_ms}\n",
        requested_step_id(requested_action),
        error.class.as_str(),
        error.class.exit_code(),
        error.class.as_str(),
        error.reason,
        error.path,
        error.detail.replace('\n', "\\n"),
    )
}

fn execute_publication(
    root: &Path,
    robot: bool,
    requested_action: &'static str,
    started: Instant,
) -> ExitCode {
    let result = match requested_action {
        "publish" => contract_inventory::publish(root),
        "recover" => contract_inventory::recover(root),
        _ => unreachable!("closed publication action"),
    };
    match result {
        Ok(receipt) => {
            if robot {
                print!(
                    "{}",
                    render_publication_success(&receipt, started.elapsed().as_millis())
                );
            } else {
                print!(
                    "{}",
                    render_publication_success_human(&receipt, started.elapsed().as_millis())
                );
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            if robot {
                print!(
                    "{}",
                    render_publication_failure(
                        requested_action,
                        &error,
                        started.elapsed().as_millis()
                    )
                );
            } else {
                eprint!(
                    "{}",
                    render_publication_failure_human(
                        requested_action,
                        &error,
                        started.elapsed().as_millis()
                    )
                );
            }
            ExitCode::from(error.class.exit_code())
        }
    }
}

fn execute_handoff_publication(
    root: &Path,
    robot: bool,
    requested_action: &'static str,
    started: Instant,
) -> ExitCode {
    let result = match requested_action {
        "publish" => contract_handoff::publish(root),
        "recover" => contract_handoff::recover(root),
        _ => unreachable!("closed handoff publication action"),
    };
    match result {
        Ok(receipt) => {
            let snapshot = &receipt.snapshot;
            let action = receipt.action.as_str();
            let duration_ms = started.elapsed().as_millis();
            if robot {
                println!(
                    "{{\"schema\":\"structure-guard/3\",\"event\":\"contract_handoff_publication\",\"scenario_id\":\"{HANDOFF_SCENARIO_ID}\",\"step_id\":\"{action}.atomic-commit\",\"action\":\"{action}\",\"verdict\":\"pass\",\"exit_code\":0,\"handoff_schema\":\"{}\",\"definition_schema\":\"{}\",\"policy_schema\":\"{}\",\"canonical_root\":\"{}\",\"inventory_root\":\"{}\",\"suite_lock_root\":\"{}\",\"definition_root\":\"{}\",\"policy_root\":\"{}\",\"output_root\":\"{}\",\"rows_total\":{},\"domains_total\":{},\"resource_facts\":{{\"output_bytes\":{},\"canonical_bytes\":{},\"max_output_bytes\":{}}},\"publication_stage\":\"candidate-validated-renamed-and-directory-synced\",\"authority\":\"complete\",\"cleanup\":\"candidate_absent\",\"final_published_root\":\"{}\",\"duration_ms\":{duration_ms}}}",
                    contract_handoff::HANDOFF_SCHEMA,
                    contract_handoff::DEFINITION_SCHEMA,
                    contract_handoff::POLICY_SCHEMA,
                    report::json_escape(&snapshot.handoff_root),
                    report::json_escape(&snapshot.inventory_root),
                    report::json_escape(&snapshot.suite_lock_root),
                    report::json_escape(&snapshot.definition_root),
                    report::json_escape(&snapshot.policy_root),
                    report::json_escape(&snapshot.output_root),
                    snapshot.row_count,
                    snapshot.domain_count,
                    snapshot.output_bytes,
                    snapshot.canonical_bytes,
                    contract_handoff::MAX_OUTPUT_BYTES,
                    report::json_escape(&snapshot.handoff_root),
                );
            } else {
                println!(
                    "structure-guard: contract_handoff_publication scenario_id={HANDOFF_SCENARIO_ID} step_id={action}.atomic-commit action={action} verdict=pass exit_code=0 handoff_schema={} definition_schema={} policy_schema={} canonical_root={} inventory_root={} suite_lock_root={} definition_root={} policy_root={} output_root={} rows_total={} domains_total={} output_bytes={} canonical_bytes={} max_output_bytes={} publication_stage=candidate-validated-renamed-and-directory-synced authority=complete cleanup=candidate_absent final_published_root={} duration_ms={duration_ms}",
                    contract_handoff::HANDOFF_SCHEMA,
                    contract_handoff::DEFINITION_SCHEMA,
                    contract_handoff::POLICY_SCHEMA,
                    snapshot.handoff_root,
                    snapshot.inventory_root,
                    snapshot.suite_lock_root,
                    snapshot.definition_root,
                    snapshot.policy_root,
                    snapshot.output_root,
                    snapshot.row_count,
                    snapshot.domain_count,
                    snapshot.output_bytes,
                    snapshot.canonical_bytes,
                    contract_handoff::MAX_OUTPUT_BYTES,
                    snapshot.handoff_root,
                );
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            let duration_ms = started.elapsed().as_millis();
            if robot {
                println!(
                    "{{\"schema\":\"structure-guard/3\",\"event\":\"contract_handoff_publication\",\"scenario_id\":\"{HANDOFF_SCENARIO_ID}\",\"step_id\":\"{requested_action}.refused\",\"action\":\"{requested_action}\",\"verdict\":\"{}\",\"exit_code\":{},\"handoff_schema\":\"{}\",\"definition_schema\":\"{}\",\"policy_schema\":\"{}\",\"canonical_root\":null,\"inventory_root\":null,\"suite_lock_root\":null,\"definition_root\":null,\"policy_root\":null,\"output_root\":null,\"rows_total\":null,\"domains_total\":null,\"resource_facts\":{{\"output_bytes\":null,\"canonical_bytes\":null,\"max_output_bytes\":{}}},\"publication_stage\":\"refused-or-failed-before-clean-terminal-receipt\",\"authority\":\"{}\",\"cleanup\":\"not_established\",\"final_published_root\":null,\"reason\":\"{}\",\"path\":\"{}\",\"detail\":\"{}\",\"duration_ms\":{duration_ms}}}",
                    error.class.as_str(),
                    error.class.exit_code(),
                    contract_handoff::HANDOFF_SCHEMA,
                    contract_handoff::DEFINITION_SCHEMA,
                    contract_handoff::POLICY_SCHEMA,
                    contract_handoff::MAX_OUTPUT_BYTES,
                    error.class.as_str(),
                    report::json_escape(error.reason),
                    report::json_escape(&error.path),
                    report::json_escape(&error.detail),
                );
            } else {
                eprintln!(
                    "structure-guard: contract_handoff_publication scenario_id={HANDOFF_SCENARIO_ID} step_id={requested_action}.refused action={requested_action} verdict={} exit_code={} authority={} cleanup=not_established reason={} path={} detail={} duration_ms={duration_ms}",
                    error.class.as_str(),
                    error.class.exit_code(),
                    error.class.as_str(),
                    error.reason,
                    error.path,
                    error.detail.replace('\n', "\\n"),
                );
            }
            ExitCode::from(error.class.exit_code())
        }
    }
}

fn main() -> ExitCode {
    let started = Instant::now();
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    let action = match parse_cli(&args) {
        Ok(action) => action,
        Err(error) => {
            if error.robot {
                print!(
                    "{}",
                    report::render_cli_failure_ndjson(
                        &error.root.display().to_string(),
                        &error.detail,
                        started.elapsed().as_millis()
                    )
                );
            } else {
                eprintln!("{}\n{USAGE}", error.detail);
            }
            return ExitCode::from(2);
        }
    };
    let (root, robot) = match action {
        CliAction::Run { root, robot } => (root, robot),
        CliAction::PublishInventory { root, robot } => {
            return execute_publication(&root, robot, "publish", started);
        }
        CliAction::RecoverInventory { root, robot } => {
            return execute_publication(&root, robot, "recover", started);
        }
        CliAction::PublishHandoff { root, robot } => {
            return execute_handoff_publication(&root, robot, "publish", started);
        }
        CliAction::RecoverHandoff { root, robot } => {
            return execute_handoff_publication(&root, robot, "recover", started);
        }
        CliAction::Help { robot } => {
            if robot {
                print!(
                    "{}",
                    report::render_help_ndjson(USAGE, started.elapsed().as_millis())
                );
            } else {
                println!("{USAGE}");
            }
            return ExitCode::SUCCESS;
        }
    };

    let root_display = root.display().to_string();
    match checks::run(&root) {
        Ok(outcome) => {
            let exit_code = outcome.exit_code();
            if robot {
                print!(
                    "{}",
                    report::render_ndjson(&root_display, &outcome, started.elapsed().as_millis())
                );
            } else {
                print!("{}", report::render_human(&root_display, &outcome));
            }
            ExitCode::from(exit_code)
        }
        Err(e) => {
            if robot {
                print!(
                    "{}",
                    report::render_setup_failure_ndjson(
                        &root_display,
                        &e,
                        started.elapsed().as_millis()
                    )
                );
            } else {
                eprintln!("structure-guard: setup failure: {e}");
            }
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn arguments(values: &[&str]) -> Vec<OsString> {
        values.iter().map(OsString::from).collect()
    }

    #[test]
    fn robot_request_is_detected_after_an_unknown_argument() {
        let error = parse_cli(&arguments(&["--not-a-flag", "--robot"]))
            .expect_err("unknown argument must fail");
        assert!(error.robot);
        assert_eq!(error.detail, "unknown argument `--not-a-flag`");
    }

    #[test]
    fn robot_is_not_consumed_as_a_missing_root_value() {
        let error =
            parse_cli(&arguments(&["--root", "--robot"])).expect_err("root value is missing");
        assert!(error.robot);
        assert_eq!(error.detail, "--root requires a path");
    }

    /// Both the identical and the conflicting duplicate must fail: the defect is the
    /// ambiguity itself, not the disagreement.
    #[test]
    fn duplicate_root_arguments_fail_closed_in_both_modes() {
        for request in [
            vec!["--root", "/a", "--root", "/a"],
            vec!["--root", "/a", "--root", "/b"],
        ] {
            let error = parse_cli(&arguments(&request)).expect_err("duplicate --root must fail");
            assert!(!error.robot);
            assert!(
                error.detail.contains("--root given more than once"),
                "unexpected detail: {}",
                error.detail
            );

            let mut robot_request = request.clone();
            robot_request.push("--robot");
            let error =
                parse_cli(&arguments(&robot_request)).expect_err("duplicate --root must fail");
            assert!(error.robot, "robot mode is a property of the whole request");
        }

        // A repeated `--robot` is idempotent and stays legal; only the target root is
        // ambiguous when repeated.
        assert_eq!(
            parse_cli(&arguments(&["--robot", "--root", "/a", "--robot"])),
            Ok(CliAction::Run {
                root: PathBuf::from("/a"),
                robot: true
            })
        );
    }

    #[test]
    fn help_preserves_whole_request_robot_mode() {
        assert_eq!(
            parse_cli(&arguments(&["--help", "--robot"])),
            Ok(CliAction::Help { robot: true })
        );
    }

    #[test]
    fn publication_actions_are_explicit_and_mutually_exclusive() {
        assert_eq!(
            parse_cli(&arguments(&[
                "--publish-contract-inventory",
                "--root",
                "/a",
                "--robot",
            ])),
            Ok(CliAction::PublishInventory {
                root: PathBuf::from("/a"),
                robot: true,
            })
        );
        assert_eq!(
            parse_cli(&arguments(&["--recover-contract-inventory"])),
            Ok(CliAction::RecoverInventory {
                root: PathBuf::from("."),
                robot: false,
            })
        );
        assert_eq!(
            parse_cli(&arguments(&[
                "--publish-contract-handoff",
                "--root",
                "/a",
                "--robot",
            ])),
            Ok(CliAction::PublishHandoff {
                root: PathBuf::from("/a"),
                robot: true,
            })
        );
        assert_eq!(
            parse_cli(&arguments(&["--recover-contract-handoff"])),
            Ok(CliAction::RecoverHandoff {
                root: PathBuf::from("."),
                robot: false,
            })
        );
        let error = parse_cli(&arguments(&[
            "--publish-contract-inventory",
            "--recover-contract-inventory",
        ]))
        .expect_err("publication and recovery cannot share one request");
        assert!(error.detail.contains("conflicts"));
        let error = parse_cli(&arguments(&[
            "--publish-contract-inventory",
            "--publish-contract-handoff",
        ]))
        .expect_err("inventory and handoff publication cannot share one request");
        assert!(error.detail.contains("conflicts"));
    }

    #[test]
    fn publication_robot_records_are_single_line_terminal_and_escaped() {
        use structure_guard::contract_inventory::{
            ErrorClass, InventorySnapshot, PublicationAction,
        };

        let receipt = PublicationReceipt {
            action: PublicationAction::Published,
            snapshot: InventorySnapshot {
                inventory_root: "fnv1a64:0000000000000001".to_string(),
                schema_root: "fnv1a64:0000000000000002".to_string(),
                suite_lock_root: "fnv1a64:0000000000000003".to_string(),
                abi_target_layout_root: "fnv1a64:0000000000000007".to_string(),
                olean_ilean_format_root: "fnv1a64:0000000000000008".to_string(),
                raw_root: "fnv1a64:0000000000000004".to_string(),
                policy_root: "fnv1a64:0000000000000005".to_string(),
                reference_root: "fnv1a64:0000000000000006".to_string(),
                row_count: 8,
                target_row_count: 1,
                abi_row_count: 1,
                format_row_count: 2,
                unresolved_row_count: 0,
                source_bytes: 300,
                canonical_bytes: 700,
            },
        };
        let success = render_publication_success(&receipt, 7);
        assert_eq!(success.lines().count(), 1);
        assert!(success.contains("\"verdict\":\"pass\""));
        assert!(success.contains("\"exit_code\":0"));
        for field in [
            "\"run_id\":",
            "\"scenario_id\":",
            "\"step_id\":",
            "\"inventory_schema\":",
            "\"definition_schema\":",
            "\"extractor_version\":",
            "\"abi_extractor_version\":",
            "\"reference_root\":",
            "\"suite_lock_root\":",
            "\"abi_target_layout_root\":",
            "\"target_facts\":",
            "\"raw_root\":",
            "\"canonical_root\":",
            "\"policy_root\":",
            "\"rows_total\":",
            "\"unresolved_rows\":",
            "\"resource_facts\":",
            "\"publication_stage\":",
            "\"authority\":\"complete\"",
            "\"cleanup\":\"candidate_absent\"",
            "\"final_published_root\":",
        ] {
            assert!(success.contains(field), "success record lost {field}");
        }
        let human = render_publication_success_human(&receipt, 8);
        assert_eq!(human.lines().count(), 1);
        assert!(human.contains("cleanup=candidate_absent"));
        assert!(human.contains("final_published_root=fnv1a64:0000000000000001"));

        let failure = render_publication_failure(
            "recover",
            &InventoryError {
                class: ErrorClass::Inconclusive,
                reason: "stale_candidate",
                path: "contracts/a\"b".to_string(),
                detail: "first\nsecond".to_string(),
            },
            9,
        );
        assert_eq!(failure.lines().count(), 1);
        assert!(failure.contains("\"verdict\":\"inconclusive\""));
        assert!(failure.contains("\"exit_code\":3"));
        assert!(failure.contains("a\\\"b"));
        assert!(failure.contains("first\\nsecond"));
        assert!(failure.contains("\"reference_root\":null"));
        assert!(failure.contains("\"abi_target_layout_root\":null"));
        assert!(failure.contains("\"cleanup\":\"not_established\""));
        assert!(failure.contains("\"final_published_root\":null"));

        let human_failure = render_publication_failure_human(
            "recover",
            &InventoryError {
                class: ErrorClass::Inconclusive,
                reason: "stale_candidate",
                path: "contracts/a".to_string(),
                detail: "first\nsecond".to_string(),
            },
            10,
        );
        assert_eq!(human_failure.lines().count(), 1);
        assert!(human_failure.contains("authority=inconclusive"));
        assert!(human_failure.contains("cleanup=not_established"));
    }
}
