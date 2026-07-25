//! CLI for the structural gate. See `lib.rs` for what is enforced.
//!
//! Usage: `structure-guard [--root <path>] [--robot]
//!        structure-guard --publish-contract-inventory [--root <path>] [--robot]
//!        structure-guard --recover-contract-inventory [--root <path>] [--robot]`
//! Exit codes: 0 = clean, 1 = findings, 2 = setup/parse failure at the root.

#![forbid(unsafe_code)]

use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Instant;

use structure_guard::contract_inventory::{self, InventoryError, PublicationReceipt};
use structure_guard::{checks, report};

const USAGE: &str = "usage: structure-guard [--root <path>] [--robot]\n\
       structure-guard --publish-contract-inventory [--root <path>] [--robot]\n\
       structure-guard --recover-contract-inventory [--root <path>] [--robot]\n\
  --root <path>  workspace root to check (default: current directory)\n\
  --robot        NDJSON output (schema structure-guard/3) on stdout\n\
  --publish-contract-inventory  validate, sync, and atomically publish a candidate\n\
  --recover-contract-inventory  validate and atomically promote a leftover candidate\n\
exit codes: 0 clean, 1 findings, 2 setup failure, 3 inconclusive authority";

#[derive(Debug, Eq, PartialEq)]
enum CliAction {
    Run { root: PathBuf, robot: bool },
    PublishInventory { root: PathBuf, robot: bool },
    RecoverInventory { root: PathBuf, robot: bool },
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
            if publication_action.replace("recover").is_some() {
                return Err(CliError {
                    root,
                    robot,
                    detail:
                        "contract inventory recovery action given more than once or conflicts with publication"
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
            Some("recover") => Ok(CliAction::RecoverInventory { root, robot }),
            None => Ok(CliAction::Run { root, robot }),
            Some(_) => unreachable!("closed publication action parser"),
        }
    }
}

fn render_publication_success(receipt: &PublicationReceipt, duration_ms: u128) -> String {
    let snapshot = &receipt.snapshot;
    format!(
        "{{\"schema\":\"structure-guard/3\",\"event\":\"contract_inventory_publication\",\"action\":\"{}\",\"verdict\":\"pass\",\"exit_code\":0,\"inventory_root\":\"{}\",\"schema_root\":\"{}\",\"suite_lock_root\":\"{}\",\"policy_root\":\"{}\",\"rows\":{},\"duration_ms\":{duration_ms}}}\n",
        receipt.action.as_str(),
        report::json_escape(&snapshot.inventory_root),
        report::json_escape(&snapshot.schema_root),
        report::json_escape(&snapshot.suite_lock_root),
        report::json_escape(&snapshot.policy_root),
        snapshot.row_count,
    )
}

fn render_publication_failure(
    requested_action: &str,
    error: &InventoryError,
    duration_ms: u128,
) -> String {
    format!(
        "{{\"schema\":\"structure-guard/3\",\"event\":\"contract_inventory_publication\",\"action\":\"{}\",\"verdict\":\"{}\",\"exit_code\":{},\"reason\":\"{}\",\"path\":\"{}\",\"detail\":\"{}\",\"duration_ms\":{duration_ms}}}\n",
        requested_action,
        error.class.as_str(),
        error.class.exit_code(),
        report::json_escape(error.reason),
        report::json_escape(&error.path),
        report::json_escape(&error.detail),
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
                println!(
                    "structure-guard: contract inventory {} root={} rows={}",
                    receipt.action.as_str(),
                    receipt.snapshot.inventory_root,
                    receipt.snapshot.row_count
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
                eprintln!("structure-guard: contract inventory {error}");
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
        let error = parse_cli(&arguments(&[
            "--publish-contract-inventory",
            "--recover-contract-inventory",
        ]))
        .expect_err("publication and recovery cannot share one request");
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
                policy_root: "fnv1a64:0000000000000004".to_string(),
                row_count: 5,
            },
        };
        let success = render_publication_success(&receipt, 7);
        assert_eq!(success.lines().count(), 1);
        assert!(success.contains("\"verdict\":\"pass\""));
        assert!(success.contains("\"exit_code\":0"));

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
    }
}
