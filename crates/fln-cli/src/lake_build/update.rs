//! Local manifest resolution with checked native Lean configuration evaluation.
//! The resolver captures and rechecks every configuration before publication;
//! this adapter evaluates only the exact bytes supplied by that resolver.

use super::*;

enum UpdateFailure {
    Resolution(fln_lake::LakeUpdateError),
    Configuration(Failure),
}

impl From<fln_lake::LakeUpdateError> for UpdateFailure {
    fn from(error: fln_lake::LakeUpdateError) -> Self {
        Self::Resolution(error)
    }
}

pub(crate) fn run(
    directory: PathBuf,
    json: bool,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
    command: &str,
) -> MultiplexerOutput {
    let worker = std::thread::Builder::new()
        .name("fln-lake-update".to_owned())
        .stack_size(OLEAN_CHECK_KERNEL_STACK_BYTES)
        .spawn(move || {
            let mut imports = Vec::new();
            let manifest = fln_lake::update_manifest_with_lean(&directory, |root, bytes| {
                let loaded = lean_config::load_source(root, bytes, jobs, posture)
                    .map_err(UpdateFailure::Configuration)?;
                imports.push(loaded.imports);
                Ok::<_, UpdateFailure>(loaded.config)
            })?;
            Ok::<_, UpdateFailure>((manifest, imports))
        });
    let result = match worker {
        Ok(worker) => worker.join().unwrap_or_else(|_| {
            Err(UpdateFailure::Configuration(Failure::new(
                "internal-fault",
                "manifest update worker panicked",
            )))
        }),
        Err(error) => Err(UpdateFailure::Configuration(Failure::new(
            "resource",
            format!("could not start manifest update worker: {error}"),
        ))),
    };
    match result {
        Ok((manifest, imports)) => {
            if json {
                let imports = if imports.is_empty() {
                    String::new()
                } else {
                    format!(
                        ",\"configuration_imports\":[{}]",
                        imports
                            .iter()
                            .map(|report| format!("{{{}}}", source_check::posture_json(report)))
                            .collect::<Vec<_>>()
                            .join(","),
                    )
                };
                MultiplexerOutput::success(format!(
                    "{{\"schema\":\"fln.lake-update/1\",\"status\":\"success\",\"package\":{},\"packages_count\":{}{imports}}}\n",
                    json_string(&manifest.name),
                    manifest.packages.len(),
                ))
            } else {
                MultiplexerOutput::success(String::new())
            }
        }
        Err(UpdateFailure::Configuration(error)) => {
            error.render_as(json, "fln.lake-update/1", &format!("lake {command}"))
        }
        Err(UpdateFailure::Resolution(error)) => match error {
            error @ (fln_lake::LakeUpdateError::DependencyResolutionUnavailable { .. }
            | fln_lake::LakeUpdateError::Unsupported(_)) => {
                lake_not_implemented(command, &error.to_string(), json)
            }
            error @ fln_lake::LakeUpdateError::Resource(_) => {
                let detail = if json {
                    format!(
                        "{{\"schema\":\"fln.lake-update/1\",\"status\":\"inconclusive\",\"class\":\"resource\",\"authority\":false,\"error\":{}}}\n",
                        json_string(&error.to_string()),
                    )
                } else {
                    format!("{error}\n")
                };
                MultiplexerOutput::failure(detail, 3)
            }
            error => {
                let detail = if json {
                    format!(
                        "{{\"schema\":\"fln.lake-update/1\",\"status\":\"error\",\"error\":{}}}\n",
                        json_string(&error.to_string()),
                    )
                } else {
                    format!("{error}\n")
                };
                MultiplexerOutput::failure(detail, 1)
            }
        },
    }
}
