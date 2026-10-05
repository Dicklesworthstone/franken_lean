//! The on-disk record store and checker identity behind the `reuse-verified` import
//! posture (bead `fln-uyuz`). The key, the record and the re-proof live in
//! `fln::source_check::modules::reuse`; this file only decides where records are
//! kept and who is checking, so moving the store elsewhere changes no trust semantics.
use super::*;
use fln::source_check::modules::persisted::{PersistedModules, SourceModuleKey, SourceModuleStore};
use fln::source_check::modules::reuse::{
    CheckerIdentity, ImportClosureKey, ImportPosture, ImportPostureReport, ImportPostureRequest,
    ImportReuseStore, RecordLookup, RecordWrite, ReuseVerified,
};
use std::sync::OnceLock;

/// The largest record read back. `Init`'s is well under a megabyte.
const MAX_RECORD_BYTES: usize = 64 * 1024 * 1024;
/// The largest executable hashed for the checker identity.
const MAX_EXECUTABLE_BYTES: usize = 1 << 30;

/// Records as files named by their key, in one directory: `FLN_IMPORT_REUSE_DIR`,
/// else `$XDG_CACHE_HOME/fln/import-reuse`, else `$HOME/.cache/fln/import-reuse`.
pub(in crate::source_check) struct RecordDirectory(PathBuf);

impl RecordDirectory {
    pub(in crate::source_check) fn from_environment() -> Result<Self, String> {
        let directory = std::env::var_os("FLN_IMPORT_REUSE_DIR")
            .filter(|value| !value.is_empty())
            .map(PathBuf::from)
            .or_else(|| {
                std::env::var_os("XDG_CACHE_HOME")
                    .filter(|value| !value.is_empty())
                    .map(|cache| PathBuf::from(cache).join("fln/import-reuse"))
            })
            .or_else(|| {
                std::env::var_os("HOME")
                    .filter(|value| !value.is_empty())
                    .map(|home| PathBuf::from(home).join(".cache/fln/import-reuse"))
            })
            .ok_or("no FLN_IMPORT_REUSE_DIR, XDG_CACHE_HOME or HOME names a record directory")?;
        if !directory.is_absolute() {
            return Err(format!(
                "the record directory {} is not absolute",
                directory.display()
            ));
        }
        Ok(Self(directory))
    }

    fn path(&self, key: ImportClosureKey) -> PathBuf {
        self.0.join(format!("{}.record", key.to_hex()))
    }
}

impl ImportReuseStore for RecordDirectory {
    fn load(&self, key: ImportClosureKey) -> Result<Option<Vec<u8>>, String> {
        let path = self.path(key);
        match std::fs::symlink_metadata(&path) {
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(format!("{}: {error}", path.display())),
            Ok(_) => {}
        }
        read_bounded(&path, MAX_RECORD_BYTES, "import reuse record")
            .map(Some)
            .map_err(|error| error.to_string())
    }

    fn save(&self, key: ImportClosureKey, bytes: &[u8]) -> Result<(), String> {
        std::fs::create_dir_all(&self.0)
            .map_err(|error| format!("{}: {error}", self.0.display()))?;
        let path = self.path(key);
        fln::publish_file_atomic(bytes, &path)
            .map_err(|error| format!("{}: {error}", path.display()))
    }
}

/// Source module records (bead `franken_lean-z8j.1.1`) sit beside the import records,
/// one directory down, under the same trust boundary and checker identity.
impl SourceModuleStore for RecordDirectory {
    fn load(&self, key: SourceModuleKey) -> Result<Option<Vec<u8>>, String> {
        let path = self.module_path(key);
        match std::fs::symlink_metadata(&path) {
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(format!("{}: {error}", path.display())),
            Ok(_) => {}
        }
        read_bounded(&path, MAX_RECORD_BYTES, "source module record")
            .map(Some)
            .map_err(|error| error.to_string())
    }

    fn save(&self, key: SourceModuleKey, bytes: &[u8]) -> Result<(), String> {
        let directory = self.0.join("source-modules");
        std::fs::create_dir_all(&directory)
            .map_err(|error| format!("{}: {error}", directory.display()))?;
        let path = self.module_path(key);
        fln::publish_file_atomic(bytes, &path)
            .map_err(|error| format!("{}: {error}", path.display()))
    }
}

impl RecordDirectory {
    fn module_path(&self, key: SourceModuleKey) -> PathBuf {
        self.0
            .join("source-modules")
            .join(format!("{}.record", key.to_hex()))
    }
}

/// Where a build's source module records come from, resolved against this host:
/// nowhere under `recheck`, the import record directory's `source-modules/` under
/// `reuse-verified`, or nowhere with a reason when that cannot be established.
pub(crate) struct ModuleRecords(Resolved);

impl ModuleRecords {
    pub(in crate::source_check) fn new(posture: ImportPosture) -> Self {
        ModuleRecords(Resolved::new(posture))
    }

    pub(crate) fn persisted(&self) -> Option<PersistedModules<'_>> {
        match &self.0 {
            Resolved::Reuse(checker, directory) => Some(PersistedModules {
                checker: *checker,
                store: directory,
            }),
            Resolved::Recheck | Resolved::Unavailable(_) => None,
        }
    }

    /// The report's `"module_records"` value.
    pub(crate) fn state(&self) -> &'static str {
        match &self.0 {
            Resolved::Recheck => "off",
            Resolved::Reuse(..) => "on",
            Resolved::Unavailable(_) => "unavailable",
        }
    }

    /// Why records are unavailable, when they are.
    pub(crate) fn unavailable(&self) -> Option<&str> {
        match &self.0 {
            Resolved::Unavailable(reason) => Some(reason),
            Resolved::Recheck | Resolved::Reuse(..) => None,
        }
    }
}

/// The digest of this process's own executable bytes, read once. `/proc/self/exe`
/// names the running image even if its path was replaced since it started.
fn checker_identity() -> Result<CheckerIdentity, String> {
    static IDENTITY: OnceLock<Result<CheckerIdentity, String>> = OnceLock::new();
    IDENTITY
        .get_or_init(|| {
            let running = PathBuf::from("/proc/self/exe");
            let path = if running.exists() {
                running
            } else {
                std::env::current_exe().map_err(|error| format!("current executable: {error}"))?
            };
            let bytes =
                std::fs::read(&path).map_err(|error| format!("{}: {error}", path.display()))?;
            if bytes.len() > MAX_EXECUTABLE_BYTES {
                return Err("the executable is too large to identify".to_owned());
            }
            Ok(CheckerIdentity::of_executable(&bytes))
        })
        .clone()
}

/// What a front door was asked for, resolved against this host.
pub(in crate::source_check) enum Resolved {
    Recheck,
    Reuse(CheckerIdentity, RecordDirectory),
    Unavailable(String),
}

impl Resolved {
    pub(in crate::source_check) fn new(posture: ImportPosture) -> Self {
        match posture {
            ImportPosture::Recheck => Resolved::Recheck,
            ImportPosture::ReuseVerified => {
                match (checker_identity(), RecordDirectory::from_environment()) {
                    (Ok(identity), Ok(directory)) => Resolved::Reuse(identity, directory),
                    (Err(reason), _) | (_, Err(reason)) => Resolved::Unavailable(reason),
                }
            }
        }
    }

    pub(in crate::source_check) fn request(&self) -> ImportPostureRequest<'_> {
        match self {
            Resolved::Recheck => ImportPostureRequest::Recheck,
            Resolved::Reuse(checker, store) => ImportPostureRequest::ReuseVerified(ReuseVerified {
                checker: *checker,
                store,
            }),
            Resolved::Unavailable(reason) => ImportPostureRequest::ReuseUnavailable(reason.clone()),
        }
    }
}

/// The posture fields every import-bearing output carries, as JSON members after an
/// opening brace: `"trust"` (the posture), `"admission"` (whether the council ran in
/// this run), and under `reuse-verified` the closure key and the record's fate.
pub(in crate::source_check) fn json_fields(report: &ImportPostureReport) -> String {
    let mut fields = format!(
        "\"trust\":{},\"admission\":{}",
        json_string(report.posture.as_str()),
        json_string(report.admission.as_str())
    );
    if let Some(key) = report.key {
        fields.push_str(&format!(",\"closureKey\":{}", json_string(&key.to_hex())));
    }
    if let Some(record) = report.record.code() {
        fields.push_str(&format!(",\"record\":{}", json_string(&record)));
    }
    if let Some(write) = report.record_write.code() {
        fields.push_str(&format!(",\"recordWrite\":{}", json_string(write)));
    }
    fields
}

/// One human sentence naming the posture and what it did.
pub(in crate::source_check) fn sentence(report: &ImportPostureReport) -> String {
    let key = report.key.map_or(String::new(), |key| {
        format!("; closure key {}", key.to_hex())
    });
    let record = match &report.record {
        RecordLookup::NotConsulted => String::new(),
        RecordLookup::Unavailable(reason) => format!("; no record store ({reason})"),
        RecordLookup::Absent => "; no record yet".to_owned(),
        RecordLookup::Unreadable(reason) => format!("; record unreadable ({reason})"),
        RecordLookup::Refused(refusal) => format!("; record refused ({refusal})"),
        RecordLookup::Hit => String::new(),
    };
    let write = match &report.record_write {
        RecordWrite::NotAttempted => String::new(),
        RecordWrite::Stored => "; admission recorded".to_owned(),
        RecordWrite::Failed(reason) => format!("; admission not recorded ({reason})"),
        RecordWrite::Unrecordable(refusal) => format!("; admission not recordable ({refusal})"),
    };
    let how = match report.admission {
        fln::source_check::modules::reuse::ImportAdmission::Council => {
            "each admitted by K1 and the independent checker in this run"
        }
        fln::source_check::modules::reuse::ImportAdmission::Reused => {
            "reused from this binary's earlier K1 and independent-checker admission of the identical bytes, re-proved by logical root"
        }
    };
    format!(
        "{how}; trust: {}{key}{record}{write}",
        report.posture.as_str()
    )
}
