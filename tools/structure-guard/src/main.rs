//! CLI for the structural gate. See `lib.rs` for what is enforced.
//!
//! Usage: `structure-guard [--root <path>] [--robot]`
//! Exit codes: 0 = clean, 1 = findings, 2 = setup/parse failure at the root.

#![forbid(unsafe_code)]

use std::ffi::{OsStr, OsString};
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use structure_guard::{checks, report};

const USAGE: &str = "usage: structure-guard [--root <path>] [--robot]\n\
  --root <path>  workspace root to check (default: current directory)\n\
  --robot        NDJSON output (schema structure-guard/2) on stdout\n\
exit codes: 0 clean, 1 findings, 2 setup failure";

#[derive(Debug, Eq, PartialEq)]
enum CliAction {
    Run { root: PathBuf, robot: bool },
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
    let mut help = false;
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
            root = PathBuf::from(value);
        } else if arg == "--robot" {
            // Already captured by the whole-request pre-scan.
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
        Ok(CliAction::Run { root, robot })
    }
}

fn main() -> ExitCode {
    let started = Instant::now();
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    let (root, robot) = match parse_cli(&args) {
        Ok(CliAction::Run { root, robot }) => (root, robot),
        Ok(CliAction::Help { robot }) => {
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

    let root_display = root.display().to_string();
    match checks::run(&root) {
        Ok(outcome) => {
            let clean = outcome.findings.is_empty();
            if robot {
                print!(
                    "{}",
                    report::render_ndjson(&root_display, &outcome, started.elapsed().as_millis())
                );
            } else {
                print!("{}", report::render_human(&root_display, &outcome));
            }
            if clean {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(1)
            }
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

    #[test]
    fn help_preserves_whole_request_robot_mode() {
        assert_eq!(
            parse_cli(&arguments(&["--help", "--robot"])),
            Ok(CliAction::Help { robot: true })
        );
    }
}
