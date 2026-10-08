//! The `reuse-verified` import posture: D6's single named exception (bead `fln-uyuz`).
//!
//! # What D6 says, and what this file does instead
//!
//! D6: nothing but the kernel may admit a constant. The `recheck` posture honours that
//! literally: every declaration of an imported `.olean` closure passes K1 and the
//! independent checker on every run. For the pinned `Init` closure that is 65,404
//! declarations, about 84 CPU-minutes per invocation, so an interactive door with an
//! implicit `import Init` gives no verdict at all.
//!
//! `reuse-verified` is a cache over PRIOR council admissions of identical inputs:
//!
//! * **Keyed** by [`ImportClosureKey`], one `Domain::CacheKey` digest over every byte of
//!   every imported part (exported, server and private), the ordered import roots, the
//!   options, and the [`CheckerIdentity`] of the binary whose council admitted it.
//! * **Re-proved on every use.** The closure is decoded from the very bytes the key
//!   hashed and its declarations are placed into an empty environment by
//!   `Engine::rebuild_reused_olean_set` — the one place outside `fln-kernel` that calls
//!   `Environment::plan_add_decl` — and the result must reach exactly the logical roots
//!   the council's admission reached: the base root, every module's base and result root,
//!   the declaration root, and, after the shared metadata activation, the result root.
//!   A logical root covers declarations, extension deltas and options (plan §7.1), so a
//!   rebuilt environment that differs from the admitted one in any constant refuses the
//!   record, and the caller re-admits through the council.
//! * **Composable.** On an exact-closure miss, module records bind each artifact's
//!   complete bytes and ordered dependency keys. Their councils ran against only the
//!   module's declared import closure. Every use re-proves that context's base and
//!   result roots, all decoded declaration content (including subsuming repeats), and
//!   complete checker-row coverage. Reused and newly checked modules are assembled in
//!   the original deterministic order before the shared metadata activation runs once.
//!   Legacy whole-closure records never manufacture these narrower-context records.
//! * **Reported.** [`ImportPostureReport`] names the posture, whether the council ran,
//!   the key, and what happened to the record; every front door prints it.
//!
//! # Where it may be used, and where it may not
//!
//! The interactive doors (`fln check-source`, `lake build`) default to it. `recheck`
//! stays the only posture of `fln check-olean`, its frontier, its receipts and anything
//! G1 evidence is drawn from: those doors call [`Engine::check_olean_modules`] and its
//! siblings, which never consult a record. A record is evidence that a council ran once;
//! it is never evidence for G1.
//!
//! # What a record is trusted for
//!
//! The root comparison proves the rebuilt environment is the one the record describes.
//! It cannot prove the record describes a council admission: whoever can write the record
//! store can write a record. The store is a per-user cache with the same standing as the
//! user's own `.olean` files, which the Reference trusts outright, so this posture is
//! still strictly stronger than the Reference's own. Kernel receipts (plan B3, bead
//! route 2) are the hardening that removes that trust; they must keep this key and these
//! report fields. `trust-producer` is not implemented.
//!
//! # The record does not depend on its storage
//!
//! [`ImportReuseStore`] is a byte store keyed by [`ImportClosureKey`]. The key, the
//! record bytes and the re-proof are defined here and nowhere else, so moving the store
//! to frankensqlite changes neither the trust semantics nor any key.
use super::imported::{SourceOleanImport, SourceOleanImportError, SourceOleanImportLimits};
use crate::*;
use fln_env::environment::{DeclarationCommitted, DeclarationPlan, MeasuredDeclaration};
use fln_hash::domain::{Digest, Domain, DomainHasher};
use std::collections::{BTreeMap, BTreeSet};

/// How a front door obtains the environment of its imported `.olean` closure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImportPosture {
    /// Every declaration passes K1 and the independent checker in this run.
    Recheck,
    /// A council admission recorded earlier by this binary for these exact bytes is
    /// rebuilt and re-proved by logical root; otherwise the council runs and is recorded.
    ReuseVerified,
}

impl ImportPosture {
    /// The stable spelling every output uses.
    pub const fn as_str(self) -> &'static str {
        match self {
            ImportPosture::Recheck => "recheck",
            ImportPosture::ReuseVerified => "reuse-verified",
        }
    }

    /// The command-line spelling, or why it is refused. `trust-producer` is a
    /// named posture of plan §7.2 that D6 does not permit here.
    pub fn parse(text: &str) -> std::result::Result<Self, String> {
        match text {
            "recheck" => Ok(ImportPosture::Recheck),
            "reuse-verified" => Ok(ImportPosture::ReuseVerified),
            "trust-producer" => Err(
                "import posture `trust-producer` is not implemented: D6 permits `recheck` and the `reuse-verified` carve-out only"
                    .to_owned(),
            ),
            other => Err(format!(
                "unknown import posture `{other}` (expected `recheck` or `reuse-verified`)"
            )),
        }
    }
}

/// The identity of the checking binary: a digest of its exact executable bytes.
///
/// A record names the identity whose council admitted the closure, and a binary with
/// any other identity refuses it, so a changed kernel, checker or decoder never inherits
/// an earlier binary's verdicts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CheckerIdentity(Digest);

impl CheckerIdentity {
    /// The identity of a binary whose executable bytes are `executable`.
    pub fn of_executable(executable: &[u8]) -> Self {
        let mut hasher = DomainHasher::new(Domain::CacheKey);
        hasher.update(b"fln.checker-identity/1\0");
        hasher.update(
            &u64::try_from(executable.len())
                .unwrap_or(u64::MAX)
                .to_le_bytes(),
        );
        hasher.update(executable);
        CheckerIdentity(hasher.finalize())
    }

    pub fn digest(self) -> Digest {
        self.0
    }
}

/// The `Domain::CacheKey` digest a record is stored and found under.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ImportClosureKey(Digest);

impl ImportClosureKey {
    /// Over every byte of every part of every module (sorted by module name, so the
    /// discovery order of the caller's loader does not matter), the ordered roots
    /// (metadata replay order depends on them), the options, and the checker identity.
    /// Every field is length-prefixed, so no two distinct inputs share an encoding.
    pub fn compute(
        modules: &[OleanModuleInput<'_>],
        roots: &[Name],
        options: &KVMap,
        checker: CheckerIdentity,
    ) -> Self {
        fn field(hasher: &mut DomainHasher, bytes: &[u8]) {
            hasher.update(&u64::try_from(bytes.len()).unwrap_or(u64::MAX).to_le_bytes());
            hasher.update(bytes);
        }
        let mut hasher = DomainHasher::new(Domain::CacheKey);
        hasher.update(b"fln.import-closure-key/1\0");
        hasher.update(&checker.0.0);
        field(&mut hasher, &options.to_canonical_bytes());
        hasher.update(&u64::try_from(roots.len()).unwrap_or(u64::MAX).to_le_bytes());
        for root in roots {
            field(&mut hasher, &root.to_canonical_bytes());
        }
        let mut sorted: Vec<(Vec<u8>, &OleanModuleInput<'_>)> = modules
            .iter()
            .map(|module| (module.name.to_canonical_bytes(), module))
            .collect();
        sorted.sort_by(|left, right| left.0.cmp(&right.0));
        hasher.update(
            &u64::try_from(sorted.len())
                .unwrap_or(u64::MAX)
                .to_le_bytes(),
        );
        for (name, module) in sorted {
            field(&mut hasher, &name);
            field(&mut hasher, module.artifact);
            for part in [module.server_artifact, module.private_artifact] {
                match part {
                    Some(bytes) => {
                        hasher.update(&[1]);
                        field(&mut hasher, bytes);
                    }
                    None => {
                        hasher.update(&[0]);
                    }
                }
            }
        }
        ImportClosureKey(hasher.finalize())
    }

    pub fn digest(self) -> Digest {
        self.0
    }

    pub fn to_hex(self) -> String {
        self.0.to_hex()
    }
}

/// Bytes keyed by [`ImportClosureKey`]. The store holds no trust of its own: whatever it
/// returns is parsed strictly, bound to the key and checker identity, and re-proved.
pub trait ImportReuseStore {
    /// The bytes stored under `key`, `Ok(None)` when there are none.
    fn load(&self, key: ImportClosureKey) -> std::result::Result<Option<Vec<u8>>, String>;
    /// Store `bytes` under `key`, replacing what was there.
    fn save(&self, key: ImportClosureKey, bytes: &[u8]) -> std::result::Result<(), String>;
}

/// Why a record was not used. Each refusal leaves the caller to re-admit through the
/// council; none is a verdict about the imported declarations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportReuseRefusal {
    /// The bytes are not a well-formed record of this schema.
    Malformed(&'static str),
    /// The record's seal does not match its body: truncated or corrupted.
    Seal,
    /// The record was found under a key it does not carry.
    Key,
    /// The record was made by a binary with another checker identity.
    CheckerIdentity,
    /// The base engine is not empty; records describe admission into an empty base.
    NonEmptyBase,
    /// The closure no longer decodes under this run's limits.
    Decode(Box<OleanCheckError>),
    /// The record's modules are not this closure's modules in its checking order.
    ModuleInventory,
    /// The record's checker rows do not cover each module's declarations exactly once.
    Rows,
    /// A rebuilt logical root differs from the admitted one.
    Root {
        at: &'static str,
        module: Option<Name>,
    },
    /// A council admission that cannot be written as a record.
    Unrecordable(&'static str),
}

impl ImportReuseRefusal {
    /// A short stable code for reports.
    pub fn code(&self) -> String {
        match self {
            ImportReuseRefusal::Malformed(_) => "malformed".to_owned(),
            ImportReuseRefusal::Seal => "seal".to_owned(),
            ImportReuseRefusal::Key => "key".to_owned(),
            ImportReuseRefusal::CheckerIdentity => "checker-identity".to_owned(),
            ImportReuseRefusal::NonEmptyBase => "non-empty-base".to_owned(),
            ImportReuseRefusal::Decode(_) => "decode".to_owned(),
            ImportReuseRefusal::ModuleInventory => "module-inventory".to_owned(),
            ImportReuseRefusal::Rows => "rows".to_owned(),
            ImportReuseRefusal::Root { at, .. } => format!("root-{at}"),
            ImportReuseRefusal::Unrecordable(_) => "unrecordable".to_owned(),
        }
    }
}

impl std::fmt::Display for ImportReuseRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ImportReuseRefusal::Malformed(reason) => write!(f, "malformed record: {reason}"),
            ImportReuseRefusal::Seal => f.write_str("record seal does not match its body"),
            ImportReuseRefusal::Key => f.write_str("record carries another closure key"),
            ImportReuseRefusal::CheckerIdentity => {
                f.write_str("record was made by another checker identity")
            }
            ImportReuseRefusal::NonEmptyBase => {
                f.write_str("records describe admission into an empty base")
            }
            ImportReuseRefusal::Decode(error) => write!(f, "closure does not decode: {error}"),
            ImportReuseRefusal::ModuleInventory => {
                f.write_str("record modules differ from the closure's checking order")
            }
            ImportReuseRefusal::Rows => {
                f.write_str("record checker rows do not cover the declarations exactly once")
            }
            ImportReuseRefusal::Root { at, module } => match module {
                Some(module) => write!(
                    f,
                    "rebuilt {at} logical root of {} differs from the admitted one",
                    module.to_display_string()
                ),
                None => write!(f, "rebuilt {at} logical root differs from the admitted one"),
            },
            ImportReuseRefusal::Unrecordable(reason) => {
                write!(f, "admission cannot be recorded: {reason}")
            }
        }
    }
}

/// Version 2: the recorded roots are over Merkle `DeclContent` digests
/// ("decl-content-dag/1", bead fln-merkle-decl-digest-80ni). A version-1 record's roots
/// are over the retired tree digests, so it is refused by its schema line rather than
/// left to fail on a root comparison.
const RECORD_SCHEMA: &str = "fln.import-reuse-record/2";
const RECORD_SEAL_PREFIX: &[u8] = b"fln.import-reuse-record-seal/1\0";
/// The checker-row schemas a record can carry, one letter each: the `.olean` council's
/// own and the independent checker's admission observation. An admission with a row of
/// any other schema is not recordable, so a new schema is never stored as an old one.
const CHECKER_ROW_SCHEMAS: [(char, &str); 2] = [
    ('v', "fln-checker/v1"),
    ('k', fln_checker::admit::ADMISSION_SCHEMA),
];

fn schema_code(schema: &str) -> Option<char> {
    CHECKER_ROW_SCHEMAS
        .iter()
        .find(|(_, known)| *known == schema)
        .map(|(code, _)| *code)
}

fn schema_of(code: char) -> Option<&'static str> {
    CHECKER_ROW_SCHEMAS
        .iter()
        .find(|(known, _)| *known == code)
        .map(|(_, schema)| *schema)
}

/// What the council's admission of one closure reached, as the re-proof needs it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportReuseRecord {
    key: Digest,
    checker: Digest,
    base_root: Digest,
    declaration_root: Digest,
    result_root: Digest,
    modules: Vec<RecordedModule>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RecordedModule {
    /// Canonical bytes of the module name.
    name: Vec<u8>,
    base_root: Digest,
    result_root: Digest,
    /// The council's checker rows in its order: an index into the module's decoded
    /// declaration table, and the agreement (schema and admission ground) it reported.
    rows: Vec<(usize, CheckerAgreement)>,
}

/// One letter per admission ground. Exhaustive in both directions, so a new ground
/// fails to compile here rather than being recorded as an old one.
fn ground_code(ground: CheckerAdmissionGround) -> char {
    match ground {
        CheckerAdmissionGround::AxiomPreamble => 'a',
        CheckerAdmissionGround::BodyCheckedAgainstDeclaredType => 'b',
        CheckerAdmissionGround::QuotientPrimitiveChecked => 'q',
        CheckerAdmissionGround::InductiveNonrecursiveChecked => 'i',
        CheckerAdmissionGround::UnsafeQuarantine => 'u',
        CheckerAdmissionGround::PartialQuarantine => 'p',
    }
}

fn ground_of(code: char) -> Option<CheckerAdmissionGround> {
    Some(match code {
        'a' => CheckerAdmissionGround::AxiomPreamble,
        'b' => CheckerAdmissionGround::BodyCheckedAgainstDeclaredType,
        'q' => CheckerAdmissionGround::QuotientPrimitiveChecked,
        'i' => CheckerAdmissionGround::InductiveNonrecursiveChecked,
        'u' => CheckerAdmissionGround::UnsafeQuarantine,
        'p' => CheckerAdmissionGround::PartialQuarantine,
        _ => return None,
    })
}

fn hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(char::from_digit(u32::from(byte >> 4), 16).unwrap_or('0'));
        out.push(char::from_digit(u32::from(byte & 0xf), 16).unwrap_or('0'));
    }
    out
}

fn unhex(text: &str) -> Option<Vec<u8>> {
    let digit = |c: u8| match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        _ => None,
    };
    let (pairs, odd) = text.as_bytes().as_chunks::<2>();
    if !odd.is_empty() {
        return None;
    }
    pairs
        .iter()
        .map(|&[high, low]| Some((digit(high)? << 4) | digit(low)?))
        .collect()
}

fn digest_of(text: &str) -> Option<Digest> {
    let bytes = unhex(text)?;
    Some(Digest(bytes.try_into().ok()?))
}

fn seal(body: &[u8]) -> Digest {
    let mut hasher = DomainHasher::new(Domain::CacheKey);
    hasher.update(RECORD_SEAL_PREFIX);
    hasher.update(body);
    hasher.finalize()
}

/// A separate key space for one module and its declared import closure. Dependency
/// keys are in the artifact's import order and already bind their own dependencies,
/// so each raw artifact is hashed once rather than once per importing module.
fn module_reuse_key(
    module: &OleanModuleInput<'_>,
    dependencies: &[ImportClosureKey],
    options: &KVMap,
    checker: CheckerIdentity,
) -> ImportClosureKey {
    let mut hasher = DomainHasher::new(Domain::CacheKey);
    hasher.update(b"fln.import-module-reuse-key/1\0");
    hasher.update(&checker.0.0);
    let mut field = |bytes: &[u8]| {
        hasher.update(&u64::try_from(bytes.len()).unwrap_or(u64::MAX).to_le_bytes());
        hasher.update(bytes);
    };
    field(&options.to_canonical_bytes());
    field(&module.name.to_canonical_bytes());
    field(module.artifact);
    for part in [module.server_artifact, module.private_artifact] {
        match part {
            Some(bytes) => {
                field(&[1]);
                field(bytes);
            }
            None => field(&[0]),
        }
    }
    field(
        &u64::try_from(dependencies.len())
            .unwrap_or(u64::MAX)
            .to_le_bytes(),
    );
    for dependency in dependencies {
        field(&dependency.0.0);
    }
    ImportClosureKey(hasher.finalize())
}

/// Module records deliberately cannot be parsed as whole-closure records. Their
/// base/result roots describe the module's OWN import closure, not its position in
/// a larger request. The inner declaration root covers every decoded constant,
/// including a subsuming repeat whose body is not retained in the environment.
const MODULE_RECORD_PREFIX: &[u8] = b"fln.import-module-reuse-record/1\n";

#[derive(Debug, Clone, PartialEq, Eq)]
struct ModuleReuseRecord(ImportReuseRecord);

impl ModuleReuseRecord {
    fn from_checked(
        name: &Name,
        checked: &CheckedOlean,
        key: ImportClosureKey,
        checker: CheckerIdentity,
        content_root: LogicalRoot,
    ) -> std::result::Result<Self, ImportReuseRefusal> {
        let module = RecordedModule::from_checked(
            name,
            &checked.decoded,
            &checked.declarations,
            checked.base_logical_root,
            checked.result_logical_root,
        )?;
        Ok(Self(ImportReuseRecord {
            key: key.0,
            checker: checker.0,
            base_root: checked.base_logical_root.0,
            declaration_root: content_root.0,
            result_root: checked.result_logical_root.0,
            modules: vec![module],
        }))
    }

    fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = MODULE_RECORD_PREFIX.to_vec();
        bytes.extend(self.0.to_bytes());
        bytes
    }

    fn parse(bytes: &[u8]) -> std::result::Result<Self, ImportReuseRefusal> {
        let body = bytes
            .strip_prefix(MODULE_RECORD_PREFIX)
            .ok_or(ImportReuseRefusal::Malformed("module record schema"))?;
        let record = ImportReuseRecord::parse(body)?;
        let [module] = record.modules.as_slice() else {
            return Err(ImportReuseRefusal::ModuleInventory);
        };
        if module.base_root != record.base_root || module.result_root != record.result_root {
            return Err(ImportReuseRefusal::Malformed("module context roots"));
        }
        Ok(Self(record))
    }
}

impl RecordedModule {
    fn from_checked(
        name: &Name,
        decoded: &DecodedOlean,
        declarations: &[OleanCheckedDeclaration],
        base: LogicalRoot,
        result: LogicalRoot,
    ) -> std::result::Result<Self, ImportReuseRefusal> {
        let mut index = BTreeMap::new();
        for (at, constant) in decoded.constants.iter().enumerate() {
            if index.insert(constant.name(), at).is_some() {
                return Err(ImportReuseRefusal::Unrecordable(
                    "a module declares one name twice",
                ));
            }
        }
        let mut rows = Vec::with_capacity(declarations.len());
        let mut seen = BTreeSet::new();
        for row in declarations {
            if schema_code(row.checker.schema).is_none() {
                return Err(ImportReuseRefusal::Unrecordable(
                    "a checker row carries an unknown schema",
                ));
            }
            let Some(&at) = index.get(&row.name) else {
                return Err(ImportReuseRefusal::Unrecordable(
                    "a checker row names no declaration of its module",
                ));
            };
            if !seen.insert(at) {
                return Err(ImportReuseRefusal::Unrecordable(
                    "two checker rows name one declaration",
                ));
            }
            rows.push((at, row.checker));
        }
        if rows.len() != decoded.constants.len() {
            return Err(ImportReuseRefusal::Unrecordable(
                "checker rows do not cover every declaration",
            ));
        }
        Ok(Self {
            name: name.to_canonical_bytes(),
            base_root: base.0,
            result_root: result.0,
            rows,
        })
    }
}

fn module_content_root(
    decoded: &DecodedOlean,
    options: &KVMap,
    cancellation: Option<&dyn CancellationProbe>,
) -> Outcome<LogicalRoot> {
    let mut pairs = Vec::with_capacity(decoded.constants.len());
    for info in &decoded.constants {
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Outcome::Inconclusive(Inconclusive::cancelled("import-reuse/module-content"));
        }
        pairs.push((
            info.name().to_canonical_bytes(),
            Environment::decl_content_digest(info),
        ));
    }
    pairs.sort_unstable_by(|left, right| left.0.cmp(&right.0));
    Outcome::Complete(fln_hash::root::declaration_root(
        pairs.len(),
        pairs.iter().map(|(name, digest)| (name.as_slice(), digest)),
        Some(options),
    ))
}

impl ImportReuseRecord {
    /// The record of a council admission that has just completed under `key`.
    ///
    /// Refused when the admission is not over an empty base, or when a checker row
    /// cannot be bound to exactly one declaration of its module.
    pub fn from_admission(
        key: ImportClosureKey,
        checker: CheckerIdentity,
        options: &KVMap,
        import: &SourceOleanImport,
    ) -> std::result::Result<Self, ImportReuseRefusal> {
        let checked = &import.checked;
        if checked.base_logical_root != Environment::new().logical_root(options) {
            return Err(ImportReuseRefusal::Unrecordable(
                "the admission was not over an empty base",
            ));
        }
        let mut modules = Vec::with_capacity(checked.modules.len());
        for module in &checked.modules {
            modules.push(RecordedModule::from_checked(
                &module.name,
                &module.decoded,
                &module.declarations,
                module.base_logical_root,
                module.result_logical_root,
            )?);
        }
        Ok(ImportReuseRecord {
            key: key.0,
            checker: checker.0,
            base_root: checked.base_logical_root.0,
            declaration_root: checked.result_logical_root.0,
            result_root: import.result_logical_root.0,
            modules,
        })
    }

    pub fn key(&self) -> ImportClosureKey {
        ImportClosureKey(self.key)
    }

    /// Line-oriented ASCII, sealed by a digest over everything before the seal line.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut body = String::new();
        let mut line = |text: String| {
            body.push_str(&text);
            body.push('\n');
        };
        line(RECORD_SCHEMA.to_owned());
        line(format!("key {}", self.key.to_hex()));
        line(format!("checker {}", self.checker.to_hex()));
        line(format!("base-root {}", self.base_root.to_hex()));
        line(format!(
            "declaration-root {}",
            self.declaration_root.to_hex()
        ));
        line(format!("result-root {}", self.result_root.to_hex()));
        line(format!("modules {}", self.modules.len()));
        for module in &self.modules {
            // Rows were admitted to a record only with a known schema, so the
            // placeholder never appears in a record `from_admission` made.
            let rows = if module.rows.is_empty() {
                "-".to_owned()
            } else {
                module
                    .rows
                    .iter()
                    .map(|(at, agreement)| {
                        format!(
                            "{at}{}{}",
                            schema_code(agreement.schema).unwrap_or('?'),
                            ground_code(agreement.ground)
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(",")
            };
            line(format!(
                "module {} {} {} {} {rows}",
                hex(&module.name),
                module.base_root.to_hex(),
                module.result_root.to_hex(),
                module.rows.len(),
            ));
        }
        let sealed = seal(body.as_bytes());
        body.push_str(&format!("seal {}\n", sealed.to_hex()));
        body.into_bytes()
    }

    /// Strict inverse of [`Self::to_bytes`]: every line, count, digest and row is
    /// checked, and the seal must match the body. Never panics on any input.
    pub fn parse(bytes: &[u8]) -> std::result::Result<Self, ImportReuseRefusal> {
        let malformed = ImportReuseRefusal::Malformed;
        let text = std::str::from_utf8(bytes).map_err(|_| malformed("not UTF-8"))?;
        let body_end = text
            .strip_suffix('\n')
            .and_then(|without| without.rfind('\n'))
            .map(|at| at + 1)
            .ok_or(malformed("no seal line"))?;
        let (body, seal_line) = text.split_at(body_end);
        let sealed = seal_line
            .strip_prefix("seal ")
            .and_then(|rest| rest.strip_suffix('\n'))
            .and_then(digest_of)
            .ok_or(malformed("bad seal line"))?;
        if seal(body.as_bytes()) != sealed {
            return Err(ImportReuseRefusal::Seal);
        }
        let mut lines = body.lines();
        let mut next = |what: &'static str| lines.next().ok_or(malformed(what));
        if next("schema")? != RECORD_SCHEMA {
            return Err(malformed("unknown schema"));
        }
        let digest_line = |line: &str, name: &'static str| {
            line.strip_prefix(name)
                .and_then(|rest| rest.strip_prefix(' '))
                .and_then(digest_of)
                .ok_or(malformed(name))
        };
        let key = digest_line(next("key")?, "key")?;
        let checker = digest_line(next("checker")?, "checker")?;
        let base_root = digest_line(next("base-root")?, "base-root")?;
        let declaration_root = digest_line(next("declaration-root")?, "declaration-root")?;
        let result_root = digest_line(next("result-root")?, "result-root")?;
        let count: usize = next("modules")?
            .strip_prefix("modules ")
            .and_then(|count| count.parse().ok())
            .ok_or(malformed("modules"))?;
        if count > bytes.len() {
            return Err(malformed("module count exceeds the record"));
        }
        let mut modules = Vec::with_capacity(count);
        for _ in 0..count {
            let line = next("module")?;
            let fields: Vec<&str> = line.split(' ').collect();
            let [tag, name, base, result, rows_count, rows] = fields.as_slice() else {
                return Err(malformed("module line"));
            };
            if *tag != "module" {
                return Err(malformed("module line"));
            }
            let name = unhex(name).ok_or(malformed("module name"))?;
            let base_root = digest_of(base).ok_or(malformed("module base root"))?;
            let result_root = digest_of(result).ok_or(malformed("module result root"))?;
            let rows_count: usize = rows_count.parse().map_err(|_| malformed("row count"))?;
            let rows: Vec<(usize, CheckerAgreement)> = if *rows == "-" {
                Vec::new()
            } else {
                rows.split(',')
                    .map(|row| {
                        let ground = row.chars().last()?;
                        let row = row.strip_suffix(ground)?;
                        let schema = row.chars().last()?;
                        let at = row.strip_suffix(schema)?;
                        if at.is_empty() || !at.bytes().all(|b| b.is_ascii_digit()) {
                            return None;
                        }
                        Some((
                            at.parse().ok()?,
                            CheckerAgreement {
                                schema: schema_of(schema)?,
                                ground: ground_of(ground)?,
                            },
                        ))
                    })
                    .collect::<Option<_>>()
                    .ok_or(malformed("checker row"))?
            };
            if rows.len() != rows_count {
                return Err(malformed("row count"));
            }
            modules.push(RecordedModule {
                name,
                base_root,
                result_root,
                rows,
            });
        }
        if next("end").is_ok() {
            return Err(malformed("trailing lines"));
        }
        Ok(ImportReuseRecord {
            key,
            checker,
            base_root,
            declaration_root,
            result_root,
            modules,
        })
    }

    /// Plant a different value in one root, for the negative tests of the re-proof.
    #[cfg(test)]
    fn with_declaration_root(mut self, root: Digest) -> Self {
        self.declaration_root = root;
        self
    }

    #[cfg(test)]
    fn with_key(mut self, key: ImportClosureKey) -> Self {
        self.key = key.0;
        self
    }
}

/// How the closure's environment was obtained.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImportAdmission {
    /// K1 and the independent checker admitted every declaration in this run.
    Council,
    /// A record of an earlier council admission was rebuilt and re-proved.
    Reused,
    /// Some modules were re-proved from records and the council checked the rest.
    Composed,
}

impl ImportAdmission {
    pub const fn as_str(self) -> &'static str {
        match self {
            ImportAdmission::Council => "council",
            ImportAdmission::Reused => "reused",
            ImportAdmission::Composed => "composed",
        }
    }
}

/// What the store had for the key.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordLookup {
    /// `recheck`: the store is never consulted.
    NotConsulted,
    /// `reuse-verified` was asked for, but no checker identity or store exists.
    Unavailable(String),
    /// Nothing is stored under the key.
    Absent,
    /// The store could not be read.
    Unreadable(String),
    /// A record was found and refused; the council ran instead.
    Refused(ImportReuseRefusal),
    /// A record was found, rebuilt and re-proved.
    Hit,
}

impl RecordLookup {
    /// `None` when the store was not consulted.
    pub fn code(&self) -> Option<String> {
        match self {
            RecordLookup::NotConsulted => None,
            RecordLookup::Unavailable(_) => Some("unavailable".to_owned()),
            RecordLookup::Absent => Some("absent".to_owned()),
            RecordLookup::Unreadable(_) => Some("unreadable".to_owned()),
            RecordLookup::Refused(refusal) => Some(format!("refused:{}", refusal.code())),
            RecordLookup::Hit => Some("hit".to_owned()),
        }
    }
}

/// What happened to the record of a council admission made under `reuse-verified`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordWrite {
    /// Nothing to write: `recheck`, or the record was reused.
    NotAttempted,
    Stored,
    Failed(String),
    Unrecordable(ImportReuseRefusal),
}

impl RecordWrite {
    pub fn code(&self) -> Option<&'static str> {
        match self {
            RecordWrite::NotAttempted => None,
            RecordWrite::Stored => Some("stored"),
            RecordWrite::Failed(_) => Some("failed"),
            RecordWrite::Unrecordable(_) => Some("unrecordable"),
        }
    }
}

/// Every output of a front door that imports `.olean` modules carries this.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportPostureReport {
    pub posture: ImportPosture,
    pub admission: ImportAdmission,
    /// Present whenever `reuse-verified` was established.
    pub key: Option<ImportClosureKey>,
    pub record: RecordLookup,
    pub record_write: RecordWrite,
    /// Modules whose earlier council admission was re-proved in this run.
    pub reused_modules: usize,
    /// Modules handed to K1 and the independent checker in this run.
    pub council_modules: usize,
}

/// What `reuse-verified` needs: who is checking, and where records live.
pub struct ReuseVerified<'a> {
    pub checker: CheckerIdentity,
    pub store: &'a dyn ImportReuseStore,
}

/// The posture a front door asks for.
pub enum ImportPostureRequest<'a> {
    Recheck,
    ReuseVerified(ReuseVerified<'a>),
    /// `reuse-verified` was asked for, but no checker identity or store could be
    /// established. The council runs, and the report says why.
    ReuseUnavailable(String),
}

/// A reused closure, or why its record was refused.
#[derive(Debug)]
pub enum ImportReuse {
    Reused(Box<SourceOleanImport>),
    Refused(ImportReuseRefusal),
}

type ImportResult<T> = std::result::Result<T, SourceOleanImportError>;

struct ComposedModules {
    checked: CheckedOleanSet,
    records: Vec<(ImportClosureKey, ModuleReuseRecord)>,
    unrecordable: Option<ImportReuseRefusal>,
    reused: usize,
}

impl Engine {
    /// [`Engine::import_olean_modules_for_source_with_cancel`] under an explicit posture.
    ///
    /// `Recheck` is exactly the council import and never touches a store.
    /// `ReuseVerified` looks the closure up by [`ImportClosureKey`]; a found record is
    /// re-proved (rebuilt by the D6 carve-out in this module) and used only if every
    /// root matches; anything else runs the council and records its admission.
    pub fn import_olean_modules_with_posture(
        &self,
        modules: &[OleanModuleInput<'_>],
        roots: &[Name],
        options: &KVMap,
        limits: SourceOleanImportLimits,
        posture: ImportPostureRequest<'_>,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> ImportResult<Outcome<(SourceOleanImport, ImportPostureReport)>> {
        let council = |report: ImportPostureReport| -> ImportResult<
            Outcome<(SourceOleanImport, ImportPostureReport)>,
        > {
            Ok(self
                .import_olean_modules_for_source_with_cancel(
                    modules,
                    roots,
                    options,
                    limits,
                    cancellation,
                )?
                .map_complete(|import| (import, report)))
        };
        let reuse = match posture {
            ImportPostureRequest::Recheck => {
                return council(ImportPostureReport {
                    posture: ImportPosture::Recheck,
                    admission: ImportAdmission::Council,
                    key: None,
                    record: RecordLookup::NotConsulted,
                    record_write: RecordWrite::NotAttempted,
                    reused_modules: 0,
                    council_modules: modules.len(),
                });
            }
            ImportPostureRequest::ReuseUnavailable(reason) => {
                return council(ImportPostureReport {
                    posture: ImportPosture::ReuseVerified,
                    admission: ImportAdmission::Council,
                    key: None,
                    record: RecordLookup::Unavailable(reason),
                    record_write: RecordWrite::NotAttempted,
                    reused_modules: 0,
                    council_modules: modules.len(),
                });
            }
            ImportPostureRequest::ReuseVerified(reuse) => reuse,
        };
        if roots.is_empty() {
            return Err(SourceOleanImportError::EmptyRoots);
        }
        if roots.len() > limits.max_roots {
            return Err(SourceOleanImportError::Limit("import roots"));
        }
        let key = ImportClosureKey::compute(modules, roots, options, reuse.checker);
        let record = match reuse.store.load(key) {
            Ok(None) => RecordLookup::Absent,
            Err(error) => RecordLookup::Unreadable(error),
            Ok(Some(bytes)) => match ImportReuseRecord::parse(&bytes) {
                Err(refusal) => RecordLookup::Refused(refusal),
                Ok(record) => match self.reuse_recorded_closure(
                    modules,
                    roots,
                    options,
                    limits,
                    key,
                    reuse.checker,
                    &record,
                    cancellation,
                )? {
                    Outcome::Complete(ImportReuse::Reused(import)) => {
                        return Ok(Outcome::Complete((
                            *import,
                            ImportPostureReport {
                                posture: ImportPosture::ReuseVerified,
                                admission: ImportAdmission::Reused,
                                key: Some(key),
                                record: RecordLookup::Hit,
                                record_write: RecordWrite::NotAttempted,
                                reused_modules: modules.len(),
                                council_modules: 0,
                            },
                        )));
                    }
                    Outcome::Complete(ImportReuse::Refused(refusal)) => {
                        RecordLookup::Refused(refusal)
                    }
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                },
            },
        };
        let composed = match self
            .compose_recorded_modules(modules, options, limits, &reuse, cancellation)
            .map_err(|error| SourceOleanImportError::Check(Box::new(error)))?
        {
            Outcome::Complete(composed) => composed,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let (admitted, module_records, unrecordable, reused_modules) = match composed {
            Some(composed) => (
                self.activate_source_metadata(
                    composed.checked,
                    modules,
                    roots,
                    options,
                    limits,
                    cancellation,
                )?,
                composed.records,
                composed.unrecordable,
                composed.reused,
            ),
            None => (
                self.import_olean_modules_for_source_with_cancel(
                    modules,
                    roots,
                    options,
                    limits,
                    cancellation,
                )?,
                Vec::new(),
                None,
                0,
            ),
        };
        let import = match admitted {
            Outcome::Complete(import) => import,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "import-reuse/record",
            )));
        }
        // No module memo escapes an unsuccessful import or incomplete metadata
        // activation. Storage is optional; failures do not change its logical result.
        let mut record_write =
            match ImportReuseRecord::from_admission(key, reuse.checker, options, &import) {
                Err(refusal) => RecordWrite::Unrecordable(refusal),
                Ok(made) => match reuse.store.save(key, &made.to_bytes()) {
                    Ok(()) => RecordWrite::Stored,
                    Err(error) => RecordWrite::Failed(error),
                },
            };
        for (module_key, made) in module_records {
            if let Err(error) = reuse.store.save(module_key, &made.to_bytes()) {
                record_write = RecordWrite::Failed(error);
            }
        }
        if let Some(refusal) = unrecordable
            && !matches!(record_write, RecordWrite::Failed(_))
        {
            record_write = RecordWrite::Unrecordable(refusal);
        }
        let council_modules = modules.len().saturating_sub(reused_modules);
        let admission = match (reused_modules, council_modules) {
            (0, _) => ImportAdmission::Council,
            (_, 0) => ImportAdmission::Reused,
            _ => ImportAdmission::Composed,
        };
        Ok(Outcome::Complete((
            import,
            ImportPostureReport {
                posture: ImportPosture::ReuseVerified,
                admission,
                key: Some(key),
                record,
                record_write,
                reused_modules,
                council_modules,
            },
        )))
    }

    /// Populate/reuse module records only from checks against the declared import
    /// closure. A legacy whole-closure record cannot supply that authority: its
    /// council may have seen unrelated earlier modules in the request.
    fn compose_recorded_modules(
        &self,
        modules: &[OleanModuleInput<'_>],
        options: &KVMap,
        limits: SourceOleanImportLimits,
        reuse: &ReuseVerified<'_>,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<Option<ComposedModules>>, OleanCheckError> {
        if self.environment != Environment::new() || !self.imported_modules.is_empty() {
            return Ok(Outcome::Complete(None));
        }
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "import-reuse/modules",
            )));
        }
        let ordered =
            self.decode_olean_module_set(modules, limits.check, CheckerReading::Skip, limits.jobs)?;
        let count = ordered.len();
        let inputs: BTreeMap<_, _> = modules.iter().map(|module| (module.name, module)).collect();
        let positions: BTreeMap<_, _> = ordered
            .iter()
            .enumerate()
            .map(|(index, (name, _))| (name.clone(), index))
            .collect();
        let mut dependencies = Vec::with_capacity(count);
        let mut closures: Vec<std::sync::Arc<BTreeSet<usize>>> = Vec::with_capacity(count);
        let mut keys = Vec::with_capacity(count);
        for (index, (name, decoded)) in ordered.iter().enumerate() {
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                    "import-reuse/module-key",
                )));
            }
            let mut imports = BTreeSet::new();
            let mut closure = BTreeSet::new();
            let mut dependency_keys = Vec::new();
            for import in &decoded.module.imports {
                let Some(&dependency) = positions.get(&import.module).filter(|i| **i < index)
                else {
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "a module reuse dependency is not before its importer",
                    });
                };
                imports.insert(dependency);
                closure.extend(closures[dependency].iter().copied());
                dependency_keys.push(keys[dependency]);
            }
            closure.insert(index);
            let Some(input) = inputs.get(name) else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "a decoded reuse module has no artifact input",
                });
            };
            keys.push(module_reuse_key(
                input,
                &dependency_keys,
                options,
                reuse.checker,
            ));
            dependencies.push(imports);
            closures.push(std::sync::Arc::new(closure));
        }
        let mut engines = FrontierEngines::new(
            (0..count)
                .map(|index| frontier_base_of(&dependencies, &closures, |i| i, index))
                .collect(),
        );
        let mut accepted: Vec<Option<std::sync::Arc<FrontierAccepted>>> = vec![None; count];
        let mut scheduled = Vec::with_capacity(count);
        let mut records = Vec::new();
        let mut unrecordable = None;
        let mut reused = 0;
        let mut ambient = self.environment.clone();
        let names: Vec<Name> = ordered.iter().map(|(name, _)| name.clone()).collect();
        for (index, (name, artifact)) in ordered.into_iter().enumerate() {
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                    "import-reuse/module",
                )));
            }
            let base = engines.release(index, &closures, true)?;
            let closure = closures[index]
                .iter()
                .filter(|member| **member != index)
                .filter_map(|member| accepted[*member].clone())
                .collect();
            let job = FrontierJob {
                index,
                position: index,
                name: name.clone(),
                artifact,
                base,
                closure,
                retain: true,
            };
            let context = self.frontier_closure_engine(&job)?;
            let mut decoded = job.artifact;
            let content_root = match module_content_root(&decoded, options, cancellation) {
                Outcome::Complete(root) => root,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            let key = keys[index];
            let record = reuse
                .store
                .load(key)
                .ok()
                .flatten()
                .and_then(|bytes| ModuleReuseRecord::parse(&bytes).ok());
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                    "import-reuse/module-lookup",
                )));
            }
            let hit = match record {
                Some(record) => match context.rebuild_recorded_module(
                    &name,
                    &decoded,
                    key,
                    reuse.checker,
                    &record,
                    content_root,
                    options,
                    cancellation,
                ) {
                    Outcome::Complete(Ok(checked)) => Some(checked),
                    Outcome::Complete(Err(_)) => None,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                },
                None => None,
            };
            let from_record = hit.is_some();
            let checked = match hit {
                Some(checked) => {
                    reused += 1;
                    checked
                }
                None => {
                    // The independent seat reads the original bytes itself only for
                    // misses. A primary decode is never passed off as its reading.
                    let input = inputs[&name];
                    let mut parts = vec![input.artifact];
                    parts.extend(input.server_artifact);
                    parts.extend(input.private_artifact);
                    decoded.independent = independent_reading(&parts, limits.check.decode);
                    match context.check_composed_module(decoded, options, limits) {
                        Ok(Outcome::Complete(checked)) => checked,
                        Ok(Outcome::Inconclusive(reason)) => {
                            return Ok(Outcome::Inconclusive(reason));
                        }
                        Ok(Outcome::InternalFault(fault)) => {
                            return Ok(Outcome::InternalFault(fault));
                        }
                        Err(OleanCheckError::MissingConstants { names, .. })
                            if !names.is_empty()
                                && names.iter().all(|name| {
                                    ambient.contains(name) && !context.environment.contains(name)
                                }) =>
                        {
                            // Preserve the serial door's established behavior for a
                            // declaration relying on an undeclared sibling module.
                            // None of this abandoned attempt's records is published.
                            return Ok(Outcome::Complete(None));
                        }
                        Err(error) => return Err(error),
                    }
                }
            };
            if !from_record {
                match ModuleReuseRecord::from_checked(
                    &name,
                    &checked,
                    key,
                    reuse.checker,
                    content_root,
                ) {
                    Ok(record) => records.push((key, record)),
                    Err(refusal) => unrecordable = Some(refusal),
                }
            }
            let mut admitted = Vec::new();
            let mut closure_digests = Vec::with_capacity(checked.decoded.constants.len());
            for info in &checked.decoded.constants {
                let Some(entry) = checked.engine.environment.entry(info.name()) else {
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "a checked module reuse constant has no environment entry",
                    });
                };
                closure_digests.push(Some(entry.digest()));
                if !context.environment.contains(info.name()) {
                    ambient = merge_frontier_entry(ambient, &entry)?;
                    admitted.push(entry);
                }
            }
            let checker_entries = if from_record {
                BTreeMap::new()
            } else {
                frontier_checker_entries(&checked.engine, &admitted, limits.check)
            };
            let mut engine = checked.engine;
            let mut imported = (*engine.imported_modules).clone();
            imported.insert(name.clone());
            engine.imported_modules = std::sync::Arc::new(imported);
            let module = std::sync::Arc::new(FrontierAccepted {
                index,
                position: index,
                name,
                admitted,
            });
            accepted[index] = Some(std::sync::Arc::clone(&module));
            engines.keep(index, Some(engine));
            scheduled.push(ScheduledOleanModule {
                module,
                decoded: checked.decoded,
                declarations: checked.declarations,
                closure_digests,
                checker_entries,
            });
        }
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "import-reuse/assemble",
            )));
        }
        let checked = if reused == 0 {
            self.reassemble_olean_module_set(names, scheduled, true, options, limits.check)?
        } else {
            match self.reassemble_reused_modules(scheduled, options, limits, cancellation)? {
                Outcome::Complete(checked) => checked,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            }
        };
        Ok(Outcome::Complete(Some(ComposedModules {
            checked,
            records,
            unrecordable,
            reused,
        })))
    }

    /// A cold module uses the same configured worker stack as the scheduled council
    /// door. The caller's admission budget was calibrated for that stack; silently
    /// running it on the calling thread would change its resource contract.
    fn check_composed_module(
        &self,
        decoded: DecodedOlean,
        options: &KVMap,
        limits: SourceOleanImportLimits,
    ) -> Result<Outcome<CheckedOlean>, OleanCheckError> {
        let check = || self.check_decoded_olean(decoded, options, limits.check);
        if limits.jobs.threads.get() == 1 {
            return check();
        }
        std::thread::scope(|scope| {
            let worker = std::thread::Builder::new()
                .name("fln-import-reuse-council".to_owned())
                .stack_size(limits.jobs.worker_stack_bytes)
                .spawn_scoped(scope, check)
                .map_err(|_| OleanCheckError::InternalInvariant {
                    detail: "could not start a module reuse council worker",
                })?;
            worker.join().map_err(frontier_unwound)?
        })
    }

    /// The module form of the D6 carve-out, confined to this same file. It starts
    /// from a re-proved import context and requires both that context's root and
    /// the complete decoded content before publishing any declaration.
    #[allow(clippy::too_many_arguments)]
    fn rebuild_recorded_module(
        &self,
        name: &Name,
        decoded: &DecodedOlean,
        key: ImportClosureKey,
        checker: CheckerIdentity,
        record: &ModuleReuseRecord,
        content_root: LogicalRoot,
        options: &KVMap,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Outcome<std::result::Result<CheckedOlean, ImportReuseRefusal>> {
        let refuse = |reason| Outcome::Complete(Err(reason));
        let record = &record.0;
        if record.checker != checker.0 {
            return refuse(ImportReuseRefusal::CheckerIdentity);
        }
        if record.key != key.0 {
            return refuse(ImportReuseRefusal::Key);
        }
        let [module] = record.modules.as_slice() else {
            return refuse(ImportReuseRefusal::ModuleInventory);
        };
        if module.name != name.to_canonical_bytes() {
            return refuse(ImportReuseRefusal::ModuleInventory);
        }
        let base = self.logical_root(options);
        if base.0 != record.base_root || module.base_root != record.base_root {
            return refuse(ImportReuseRefusal::Root {
                at: "module-base",
                module: Some(name.clone()),
            });
        }
        if content_root.0 != record.declaration_root {
            return refuse(ImportReuseRefusal::Root {
                at: "module-content",
                module: Some(name.clone()),
            });
        }
        let mut covered = vec![false; decoded.constants.len()];
        let mut declarations = Vec::with_capacity(module.rows.len());
        for &(at, checker) in &module.rows {
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Outcome::Inconclusive(Inconclusive::cancelled("import-reuse/module-rows"));
            }
            match covered.get_mut(at) {
                Some(slot) if !*slot => *slot = true,
                _ => return refuse(ImportReuseRefusal::Rows),
            }
            declarations.push(OleanCheckedDeclaration {
                name: decoded.constants[at].name().clone(),
                checker,
            });
        }
        if covered.iter().any(|covered| !covered) {
            return refuse(ImportReuseRefusal::Rows);
        }
        let mut environment = self.environment.clone();
        let mut admitted_any = false;
        for info in &decoded.constants {
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Outcome::Inconclusive(Inconclusive::cancelled(
                    "import-reuse/module-declaration",
                ));
            }
            if environment.contains(info.name()) {
                // Both the effective context root and this copy's complete content
                // are bound above. The council keeps the already-present copy.
                continue;
            }
            let measured = match Environment::measure_declaration(
                info.clone(),
                DeclarationBudget::UNBOUNDED,
                cancellation,
            ) {
                Outcome::Complete(measured) => measured,
                Outcome::Inconclusive(reason) => return Outcome::Inconclusive(reason),
                Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
            };
            let plan = match environment.plan_measured_decl(measured, CollisionBudget::UNBOUNDED) {
                Outcome::Complete(DeclarationPlan::Prepared(plan)) => plan,
                Outcome::Complete(DeclarationPlan::DuplicateName { .. }) => {
                    return Outcome::InternalFault(InternalFault::new(
                        "import reuse",
                        "an absent module constant was planned as a duplicate",
                    ));
                }
                Outcome::Inconclusive(reason) => return Outcome::Inconclusive(reason),
                Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
            };
            environment = match plan.commit(&environment, cancellation) {
                Outcome::Complete(DeclarationCommitted::Published(published)) => {
                    published.environment
                }
                Outcome::Complete(DeclarationCommitted::DuplicateName { .. }) => {
                    return Outcome::InternalFault(InternalFault::new(
                        "import reuse",
                        "an absent module constant was published as a duplicate",
                    ));
                }
                Outcome::Inconclusive(reason) => return Outcome::Inconclusive(reason),
                Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
            };
            admitted_any = true;
        }
        let root = environment.logical_root(options);
        if root.0 != record.result_root || module.result_root != record.result_root {
            return refuse(ImportReuseRefusal::Root {
                at: "module-result",
                module: Some(name.clone()),
            });
        }
        let mut engine = self.clone();
        engine.environment = environment;
        engine.checker_environment = None;
        if admitted_any {
            engine.options = options.clone();
        }
        Outcome::Complete(Ok(CheckedOlean {
            engine,
            decoded: decoded.clone(),
            base_logical_root: base,
            result_logical_root: root,
            declarations,
        }))
    }

    /// Reassemble own-context admissions in the requested set's canonical order.
    /// As on an exact record hit, the independent projection is absent; a later
    /// council projects the dependencies it actually reaches. Metadata is activated
    /// only by the caller, after the complete declaration world has been assembled.
    fn reassemble_reused_modules(
        &self,
        scheduled: Vec<ScheduledOleanModule>,
        options: &KVMap,
        limits: SourceOleanImportLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<CheckedOleanSet>, OleanCheckError> {
        let base = self.logical_root(options);
        let mut environment = self.environment.clone();
        let mut deltas = Vec::with_capacity(scheduled.len());
        let mut pending = Vec::with_capacity(scheduled.len());
        for scheduled in scheduled {
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                    "import-reuse/assemble-module",
                )));
            }
            let ScheduledOleanModule {
                module,
                decoded,
                declarations,
                closure_digests,
                ..
            } = scheduled;
            if closure_digests.len() != decoded.constants.len() {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "a reused module's context digests do not cover its declarations",
                });
            }
            let own: BTreeSet<&Name> = module
                .admitted
                .iter()
                .map(|entry| entry.declaration().name())
                .collect();
            let repeats = decoded
                .constants
                .iter()
                .zip(&closure_digests)
                .any(|(info, copy)| {
                    environment.entry(info.name()).is_some_and(|present| {
                        own.contains(info.name())
                            || copy.is_none_or(|copy| copy != present.digest())
                    })
                });
            let declarations = if repeats {
                serial_olean_rows(&environment, &decoded, declarations, limits.check)?
            } else {
                declarations
            };
            let mut delta = Vec::new();
            for entry in &module.admitted {
                if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                    return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                        "import-reuse/assemble-declaration",
                    )));
                }
                if !environment.contains(entry.declaration().name()) {
                    delta.push((
                        entry.declaration().name().to_canonical_bytes(),
                        entry.digest(),
                    ));
                }
                environment = merge_frontier_entry(environment, entry)?;
            }
            deltas.push(delta);
            pending.push((module.name.clone(), decoded, declarations));
        }
        let roots = module_roots(base, &deltas, options, limits.jobs);
        let mut previous = base;
        let mut checked_modules = Vec::with_capacity(pending.len());
        for ((name, decoded, declarations), root) in pending.into_iter().zip(roots) {
            checked_modules.push(CheckedOleanModule {
                name,
                decoded,
                declarations,
                base_logical_root: previous,
                result_logical_root: root,
            });
            previous = root;
        }
        if environment.logical_root(options) != previous {
            return Ok(Outcome::InternalFault(InternalFault::new(
                "import reuse",
                "composed module roots differ from the assembled environment",
            )));
        }
        let imported = checked_modules
            .iter()
            .map(|module| module.name.clone())
            .collect();
        let dependencies = checked_modules
            .iter()
            .map(|module| {
                (
                    module.name.clone(),
                    module
                        .decoded
                        .module
                        .imports
                        .iter()
                        .map(|import| import.module.clone())
                        .collect(),
                )
            })
            .collect();
        let admitted_any = deltas.iter().any(|delta| !delta.is_empty());
        let engine = Engine {
            environment: environment.clone(),
            checker_environment: None,
            imported_modules: std::sync::Arc::new(imported),
            imported_environment: Some(environment),
            imported_module_dependencies: std::sync::Arc::new(dependencies),
            epoch: self.epoch.clone(),
            mode: self.mode,
            reproducibility: self.reproducibility,
            options: if admitted_any {
                options.clone()
            } else {
                self.options.clone()
            },
        };
        Ok(Outcome::Complete(CheckedOleanSet {
            engine,
            base_logical_root: base,
            result_logical_root: previous,
            modules: checked_modules,
        }))
    }

    /// Rebuild the closure `record` describes and keep it only if it re-proves.
    ///
    /// The record must carry `key` (the caller computed it from these very `modules`)
    /// and `checker`; the rebuild must reach every root the record names; and after the
    /// shared metadata activation the result root must match too. Any failure is a
    /// [`ImportReuse::Refused`], never an error about the closure: the council decides
    /// that. Metadata errors are returned as the council path would return them.
    #[allow(clippy::too_many_arguments)]
    fn reuse_recorded_closure(
        &self,
        modules: &[OleanModuleInput<'_>],
        roots: &[Name],
        options: &KVMap,
        limits: SourceOleanImportLimits,
        key: ImportClosureKey,
        checker: CheckerIdentity,
        record: &ImportReuseRecord,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> ImportResult<Outcome<ImportReuse>> {
        // Identity before key: a record planted under this key by another binary is
        // named as what it is.
        if record.checker != checker.0 {
            return Ok(Outcome::Complete(ImportReuse::Refused(
                ImportReuseRefusal::CheckerIdentity,
            )));
        }
        if record.key != key.0 {
            return Ok(Outcome::Complete(ImportReuse::Refused(
                ImportReuseRefusal::Key,
            )));
        }
        let checked = match self.rebuild_reused_olean_set(
            modules,
            options,
            limits.check,
            limits.jobs,
            record,
            cancellation,
        ) {
            Outcome::Complete(Ok(checked)) => checked,
            Outcome::Complete(Err(refusal)) => {
                return Ok(Outcome::Complete(ImportReuse::Refused(refusal)));
            }
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let import = match self.activate_source_metadata(
            checked,
            modules,
            roots,
            options,
            limits,
            cancellation,
        )? {
            Outcome::Complete(import) => import,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        if import.result_logical_root.0 != record.result_root {
            return Ok(Outcome::Complete(ImportReuse::Refused(
                ImportReuseRefusal::Root {
                    at: "result",
                    module: None,
                },
            )));
        }
        Ok(Outcome::Complete(ImportReuse::Reused(Box::new(import))))
    }

    /// **THE D6 CARVE-OUT.** The only production code outside `fln-kernel` that places a
    /// constant into an environment without the kernel checking it in this run
    /// (structure-guard FLN-STRUCT-039 names this file, and only this file, beside the
    /// two kernel call sites).
    ///
    /// It decodes the closure exactly as the council's serial door does
    /// ([`Engine::decode_olean_module_set`], the same planner and order), inserts each
    /// module's declarations under the council's rule for a repeated name (the copy
    /// already present is kept), and refuses unless it reaches the record's base root,
    /// every module's base and result root, and the declaration root. The checker rows
    /// are the record's, bound to declaration-table indices and required to cover each
    /// module exactly once. The independent checker's retained projection is left empty:
    /// a later admission projects what it reaches, as it does for any projected import
    /// world ([`super::contexts`]).
    fn rebuild_reused_olean_set(
        &self,
        modules: &[OleanModuleInput<'_>],
        options: &KVMap,
        limits: OleanCheckLimits,
        jobs: OleanFrontierJobs,
        record: &ImportReuseRecord,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Outcome<std::result::Result<CheckedOleanSet, ImportReuseRefusal>> {
        let refuse = |refusal| Outcome::Complete(Err(refusal));
        if !self.environment.is_empty() || !self.imported_modules.is_empty() {
            return refuse(ImportReuseRefusal::NonEmptyBase);
        }
        let ordered = match self.decode_olean_module_set(
            modules,
            limits,
            crate::CheckerReading::Skip,
            jobs,
        ) {
            Ok(ordered) => ordered,
            Err(error) => return refuse(ImportReuseRefusal::Decode(Box::new(error))),
        };
        if ordered.len() != record.modules.len()
            || ordered
                .iter()
                .zip(&record.modules)
                .any(|((name, _), recorded)| name.to_canonical_bytes() != recorded.name)
        {
            return refuse(ImportReuseRefusal::ModuleInventory);
        }
        let base_logical_root = self.logical_root(options);
        if base_logical_root.0 != record.base_root {
            return refuse(ImportReuseRefusal::Root {
                at: "base",
                module: None,
            });
        }
        let mut environment = self.environment.clone();
        // Every module's root is the root of the environment after it. The base is
        // empty and the olean path adds no extension state, so a module's root is
        // the root over the (name, digest) pairs published by it and every module
        // before it. Each module's pairs are kept here and the roots are computed
        // once the closure is in place ([`module_roots`]): finalizing a cumulative
        // builder per module re-encoded every earlier name for every one of the
        // closure's modules (601 for `Init`), a sixth of a warm import. The final
        // root is checked against `Environment::logical_root` below.
        let mut deltas: Vec<Vec<(Vec<u8>, Digest)>> = Vec::with_capacity(ordered.len());
        let mut admitted_any = false;
        let mut pending = Vec::with_capacity(ordered.len());
        // Each declaration's digest and preflight read only the declaration, so they
        // are measured for the whole closure at once; publication stays in order.
        let mut measured = measure_closure(&ordered, jobs).into_iter();
        for (name, decoded) in ordered {
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Outcome::Inconclusive(Inconclusive::cancelled("import-reuse/module"));
            }
            let Some(mut module_measured) = measured.next().map(Vec::into_iter) else {
                return Outcome::InternalFault(InternalFault::new(
                    "import reuse",
                    "a decoded module has no measurements",
                ));
            };
            let mut delta = Vec::new();
            for info in &decoded.constants {
                let Some(measurement) = module_measured.next() else {
                    return Outcome::InternalFault(InternalFault::new(
                        "import reuse",
                        "a decoded declaration has no measurement",
                    ));
                };
                if environment.contains(info.name()) {
                    // An identical or subsuming repeat: the council keeps the copy
                    // already present. A difference here is caught by the roots.
                    continue;
                }
                let content = match measurement {
                    Outcome::Complete(content) => content,
                    Outcome::Inconclusive(reason) => return Outcome::Inconclusive(reason),
                    Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
                };
                let plan = match environment.plan_measured_decl(content, CollisionBudget::UNBOUNDED)
                {
                    Outcome::Complete(DeclarationPlan::Prepared(plan)) => plan,
                    Outcome::Complete(DeclarationPlan::DuplicateName { .. }) => {
                        return Outcome::InternalFault(InternalFault::new(
                            "import reuse",
                            "an absent name was planned as a duplicate",
                        ));
                    }
                    Outcome::Inconclusive(reason) => return Outcome::Inconclusive(reason),
                    Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
                };
                environment = match plan.commit(&environment, cancellation) {
                    Outcome::Complete(DeclarationCommitted::Published(published)) => {
                        delta.push((info.name().to_canonical_bytes(), published.digest));
                        published.environment
                    }
                    Outcome::Complete(DeclarationCommitted::DuplicateName { .. }) => {
                        return Outcome::InternalFault(InternalFault::new(
                            "import reuse",
                            "an absent name was published as a duplicate",
                        ));
                    }
                    Outcome::Inconclusive(reason) => return Outcome::Inconclusive(reason),
                    Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
                };
            }
            admitted_any |= !delta.is_empty();
            deltas.push(delta);
            pending.push((name, decoded));
        }
        let roots = module_roots(base_logical_root, &deltas, options, jobs);
        let mut checked_modules = Vec::with_capacity(pending.len());
        let mut module_base_root = base_logical_root;
        for (((name, decoded), recorded), root) in
            pending.into_iter().zip(&record.modules).zip(roots)
        {
            if module_base_root.0 != recorded.base_root {
                return refuse(ImportReuseRefusal::Root {
                    at: "module-base",
                    module: Some(name),
                });
            }
            if root.0 != recorded.result_root {
                return refuse(ImportReuseRefusal::Root {
                    at: "module-result",
                    module: Some(name),
                });
            }
            let mut covered = vec![false; decoded.constants.len()];
            let mut declarations = Vec::with_capacity(recorded.rows.len());
            for &(at, checker) in &recorded.rows {
                match covered.get_mut(at) {
                    Some(slot) if !*slot => *slot = true,
                    _ => return refuse(ImportReuseRefusal::Rows),
                }
                declarations.push(OleanCheckedDeclaration {
                    name: decoded.constants[at].name().clone(),
                    checker,
                });
            }
            if covered.iter().any(|covered| !covered) {
                return refuse(ImportReuseRefusal::Rows);
            }
            checked_modules.push(CheckedOleanModule {
                name,
                decoded,
                base_logical_root: module_base_root,
                result_logical_root: root,
                declarations,
            });
            module_base_root = root;
        }
        let root = module_base_root;
        if root.0 != record.declaration_root {
            return refuse(ImportReuseRefusal::Root {
                at: "declarations",
                module: None,
            });
        }
        // The accumulated roots stand in for `Environment::logical_root`; if they
        // ever disagree that is a defect here, never a property of the record.
        if environment.logical_root(options) != root {
            return Outcome::InternalFault(InternalFault::new(
                "import reuse",
                "the accumulated logical root differs from the environment's",
            ));
        }
        let mut imported = (*self.imported_modules).clone();
        imported.extend(checked_modules.iter().map(|module| module.name.clone()));
        let mut dependencies = (*self.imported_module_dependencies).clone();
        for module in &checked_modules {
            dependencies.insert(
                module.name.clone(),
                module
                    .decoded
                    .module
                    .imports
                    .iter()
                    .map(|import| import.module.clone())
                    .collect(),
            );
        }
        let engine = Engine {
            environment: environment.clone(),
            checker_environment: None,
            imported_modules: std::sync::Arc::new(imported),
            // The base is empty, so the imports alone produced this environment.
            imported_environment: Some(environment),
            imported_module_dependencies: std::sync::Arc::new(dependencies),
            epoch: self.epoch.clone(),
            mode: self.mode,
            reproducibility: self.reproducibility,
            options: if admitted_any {
                options.clone()
            } else {
                self.options.clone()
            },
        };
        Outcome::Complete(Ok(CheckedOleanSet {
            engine,
            base_logical_root,
            result_logical_root: root,
            modules: checked_modules,
        }))
    }
}

/// [`Environment::measure_declaration`] for every declaration of every module, in
/// module and table order, `jobs.threads` modules at once. A measurement reads only
/// its declaration, so the result does not depend on `jobs`.
fn measure_closure(
    ordered: &[(Name, DecodedOlean)],
    jobs: OleanFrontierJobs,
) -> Vec<Vec<Outcome<MeasuredDeclaration>>> {
    let measure_module = |decoded: &DecodedOlean| {
        decoded
            .constants
            .iter()
            .map(|info| {
                Environment::measure_declaration(info.clone(), DeclarationBudget::UNBOUNDED, None)
            })
            .collect::<Vec<_>>()
    };
    let threads = jobs.threads.get().min(ordered.len());
    if threads <= 1 {
        return ordered
            .iter()
            .map(|(_, decoded)| measure_module(decoded))
            .collect();
    }
    let next = std::sync::atomic::AtomicUsize::new(0);
    let slots: Vec<std::sync::OnceLock<Vec<Outcome<MeasuredDeclaration>>>> =
        ordered.iter().map(|_| std::sync::OnceLock::new()).collect();
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                loop {
                    let module = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    let (Some(slot), Some((_, decoded))) = (slots.get(module), ordered.get(module))
                    else {
                        return;
                    };
                    let _ = slot.set(measure_module(decoded));
                }
            });
        }
    });
    slots
        .into_iter()
        .zip(ordered)
        .map(|(slot, (_, decoded))| slot.into_inner().unwrap_or_else(|| measure_module(decoded)))
        .collect()
}

/// The logical root after each module of a rebuilt closure: module `k`'s root is the
/// root over every pair published by modules `0..=k`, and `base` while none has
/// published anything. This is exactly the root a builder accumulating those pairs
/// would finalize to after module `k` ([`fln_hash::root::declaration_root`] is that
/// encoding), so the result does not depend on `jobs`; only the wall time does.
fn module_roots(
    base: LogicalRoot,
    deltas: &[Vec<(Vec<u8>, Digest)>],
    options: &KVMap,
    jobs: OleanFrontierJobs,
) -> Vec<LogicalRoot> {
    // Every published pair once, in canonical name order, tagged by its module.
    let mut sorted: Vec<(&[u8], &Digest, usize)> = deltas
        .iter()
        .enumerate()
        .flat_map(|(module, delta)| {
            delta
                .iter()
                .map(move |(name, digest)| (name.as_slice(), digest, module))
        })
        .collect();
    sorted.sort_unstable_by(|left, right| left.0.cmp(right.0));
    let mut published = 0_usize;
    let counts: Vec<usize> = deltas
        .iter()
        .map(|delta| {
            published += delta.len();
            published
        })
        .collect();
    let root_of = |module: usize| {
        if counts[module] == 0 {
            return base;
        }
        fln_hash::root::declaration_root(
            counts[module],
            sorted
                .iter()
                .filter(|(_, _, owner)| *owner <= module)
                .map(|(name, digest, _)| (*name, *digest)),
            Some(options),
        )
    };
    let threads = jobs.threads.get().min(deltas.len());
    if threads <= 1 {
        return (0..deltas.len()).map(root_of).collect();
    }
    let next = std::sync::atomic::AtomicUsize::new(0);
    let slots: Vec<std::sync::OnceLock<LogicalRoot>> =
        deltas.iter().map(|_| std::sync::OnceLock::new()).collect();
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                loop {
                    let module = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    let Some(slot) = slots.get(module) else {
                        return;
                    };
                    let _ = slot.set(root_of(module));
                }
            });
        }
    });
    slots
        .into_iter()
        .enumerate()
        .map(|(module, slot)| slot.into_inner().unwrap_or_else(|| root_of(module)))
        .collect()
}

/// The checked set `record` re-proves for `modules`, for tests elsewhere in the crate
/// that need a second copy of a council-admitted closure without a second council.
#[cfg(test)]
impl Engine {
    pub(super) fn rebuild_for_test(
        &self,
        modules: &[OleanModuleInput<'_>],
        record: &ImportReuseRecord,
    ) -> Option<CheckedOleanSet> {
        match self.rebuild_reused_olean_set(
            modules,
            &KVMap::new(),
            super::imported::tests::limits(1).check,
            OleanFrontierJobs::SERIAL,
            record,
            None,
        ) {
            Outcome::Complete(Ok(checked)) => Some(checked),
            _ => None,
        }
    }
}

#[cfg(test)]
mod composed_tests;

#[cfg(test)]
mod tests {
    use super::super::imported::tests::{closure, inputs, limits, n, on_import_stack, pinned_lib};
    use super::*;
    use std::sync::Mutex;

    /// Records held in memory under the same byte contract as any other store.
    #[derive(Default)]
    pub(super) struct Memory(pub(super) Mutex<BTreeMap<ImportClosureKey, Vec<u8>>>);
    impl ImportReuseStore for Memory {
        fn load(&self, key: ImportClosureKey) -> std::result::Result<Option<Vec<u8>>, String> {
            Ok(self.0.lock().expect("store lock").get(&key).cloned())
        }
        fn save(&self, key: ImportClosureKey, bytes: &[u8]) -> std::result::Result<(), String> {
            self.0
                .lock()
                .expect("store lock")
                .insert(key, bytes.to_vec());
            Ok(())
        }
    }

    pub(super) fn identity(name: &str) -> CheckerIdentity {
        CheckerIdentity::of_executable(name.as_bytes())
    }

    pub(super) fn import_with(
        modules: &[OleanModuleInput<'_>],
        roots: &[Name],
        posture: ImportPostureRequest<'_>,
    ) -> (SourceOleanImport, ImportPostureReport) {
        Engine::from_environment(Environment::new())
            .import_olean_modules_with_posture(
                modules,
                roots,
                &KVMap::new(),
                limits(1),
                posture,
                None,
            )
            .expect("the pinned closure imports")
            .into_complete()
            .expect("the pinned closure imports completely")
    }

    pub(super) fn reuse<'a>(
        checker: CheckerIdentity,
        store: &'a dyn ImportReuseStore,
    ) -> ImportPostureRequest<'a> {
        ImportPostureRequest::ReuseVerified(ReuseVerified { checker, store })
    }

    /// The decoded declarations of one module's parts.
    fn declarations(
        name: &Name,
        parts: &[Vec<u8>; 3],
    ) -> std::result::Result<Vec<ConstantInfo>, OleanCheckError> {
        let [exported, server, private] = parts;
        crate::decode_olean_module_input(
            &OleanModuleInput {
                name,
                artifact: exported,
                server_artifact: (!server.is_empty()).then_some(server.as_slice()),
                private_artifact: (!private.is_empty()).then_some(private.as_slice()),
            },
            limits(1).check,
        )
        .map(|decoded| decoded.constants)
    }

    /// Change the last byte of the only occurrence of `word` in part `part`.
    fn flip(parts: &mut [Vec<u8>; 3], part: usize, word: &[u8]) {
        let bytes = &mut parts[part];
        let hits: Vec<usize> = bytes
            .windows(word.len())
            .enumerate()
            .filter(|(_, window)| *window == word)
            .map(|(at, _)| at)
            .collect();
        assert_eq!(hits.len(), 1, "{word:?} must occur once in part {part}");
        let last = hits[0] + word.len() - 1;
        bytes[last] = if bytes[last] == b'z' { b'y' } else { b'z' };
    }

    /// Everything the council's checked set and the reused one must share. The fields
    /// that differ are stated, not skipped: the council retains its independent-checker
    /// projection of every admitted declaration, the rebuild retains none; and the
    /// council's decode carries the checker's own reading of each artifact, which the
    /// rebuild never consults and so never makes.
    fn assert_same_closure(council: &SourceOleanImport, reused: &SourceOleanImport) {
        let (left, right) = (&council.checked, &reused.checked);
        assert!(
            left.engine.environment == right.engine.environment,
            "environments"
        );
        assert_eq!(left.engine.imported_modules, right.engine.imported_modules);
        assert!(left.engine.imported_environment == right.engine.imported_environment);
        assert_eq!(
            left.engine.imported_module_dependencies,
            right.engine.imported_module_dependencies
        );
        assert_eq!(left.engine.options, right.engine.options);
        assert_eq!(left.engine.epoch, right.engine.epoch);
        assert_eq!(left.base_logical_root, right.base_logical_root);
        assert_eq!(left.result_logical_root, right.result_logical_root);
        assert_eq!(left.modules.len(), right.modules.len());
        for (left, right) in left.modules.iter().zip(&right.modules) {
            assert_eq!(left.name, right.name);
            assert!(
                matches!(left.decoded.independent, crate::IndependentReading::Read(_)),
                "the council read every artifact itself"
            );
            assert!(
                matches!(
                    right.decoded.independent,
                    crate::IndependentReading::Unread(_)
                ),
                "the rebuild makes no checker reading"
            );
            let mut council_decode = left.decoded.clone();
            council_decode.independent = right.decoded.independent.clone();
            assert!(council_decode == right.decoded, "decoded artifacts");
            assert_eq!(left.base_logical_root, right.base_logical_root);
            assert_eq!(left.result_logical_root, right.result_logical_root);
            assert_eq!(left.declarations, right.declarations, "checker rows");
        }
        assert!(left.engine.checker_environment.is_some());
        assert!(right.engine.checker_environment.is_none());
        assert!(
            council.engine.environment == reused.engine.environment,
            "metadata engines"
        );
        assert_eq!(council.result_logical_root, reused.result_logical_root);
        assert_eq!(council.modules, reused.modules, "metadata reports");
    }

    /// The positive half: a multi-module closure admitted once is rebuilt from its
    /// record into the same closure, says so, and checks source to the same roots.
    #[test]
    fn a_recorded_closure_is_rebuilt_into_the_council_closure_and_says_so() {
        let Some(lib) = pinned_lib() else {
            eprintln!("SKIP: pinned Reference lib/lean absent");
            return;
        };
        let roots = ["Init.Data.Cast", "Init.Data.Option.Coe", "Init.Data.Zero"];
        let closure = closure(&lib, &roots);
        let modules = inputs(&closure);
        let roots: Vec<Name> = roots.iter().map(|root| n(root)).collect();
        on_import_stack(|| {
            let store = Memory::default();
            let checker = identity("checker A");
            let (council, first) = import_with(&modules, &roots, reuse(checker, &store));
            assert_eq!(first.posture, ImportPosture::ReuseVerified);
            assert_eq!(first.admission, ImportAdmission::Council);
            assert_eq!(first.record, RecordLookup::Absent);
            assert_eq!(first.record_write, RecordWrite::Stored);
            let (reused, second) = import_with(&modules, &roots, reuse(checker, &store));
            assert_eq!(second.admission, ImportAdmission::Reused);
            assert_eq!(second.record, RecordLookup::Hit);
            assert_eq!(second.record_write, RecordWrite::NotAttempted);
            assert_eq!(first.key, second.key);
            assert_same_closure(&council, &reused);

            let main = n("Main");
            let source =
                b"prelude\nimport Init.Data.Cast\ntheorem keep (P : Prop) (h : P) : P := h\n";
            let check = |receipt: &SourceOleanImport| {
                receipt
                    .check_source_modules(
                        &[SourceModuleInput {
                            name: &main,
                            source,
                        }],
                        &main,
                        &KVMap::new(),
                        super::super::SourceModuleCheckLimits::new(SourceCheckLimits::new(
                            EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
                        )),
                        None,
                    )
                    .expect("source checks against the receipt")
                    .into_complete()
                    .expect("source checks completely")
            };
            let (council, reused) = (check(&council), check(&reused));
            assert_eq!(council.checked.theorems, 1);
            assert_eq!(council.checked.theorems, reused.checked.theorems);
            assert_eq!(
                council.checked.base_logical_root,
                reused.checked.base_logical_root
            );
            assert_eq!(
                council.checked.result_logical_root,
                reused.checked.result_logical_root
            );
            assert!(council.checked.engine.environment == reused.checked.engine.environment);
        });
    }

    /// `recheck` is the council import and says so. A `Recheck` request carries no
    /// store, so there is nothing it could consult; the report must not claim one.
    #[test]
    fn recheck_is_the_council_import_and_reports_no_record() {
        let Some(lib) = pinned_lib() else {
            eprintln!("SKIP: pinned Reference lib/lean absent");
            return;
        };
        let closure = closure(&lib, &["Init.Prelude"]);
        let modules = inputs(&closure);
        let roots = [n("Init.Prelude")];
        on_import_stack(|| {
            let (_, report) = import_with(&modules, &roots, ImportPostureRequest::Recheck);
            assert_eq!(report.posture, ImportPosture::Recheck);
            assert_eq!(report.admission, ImportAdmission::Council);
            assert_eq!(report.record, RecordLookup::NotConsulted);
            assert_eq!(report.record_write, RecordWrite::NotAttempted);
            assert_eq!(report.key, None);
        });
    }

    /// The planted negatives, on the real Prelude.
    ///
    /// 1. One changed byte in a docstring (the `.server` part): the declarations are
    ///    unchanged, so only the KEY can catch it, and it does: the record is not found
    ///    and the council admits again.
    /// 2. A record of another checker identity, planted under this identity's key, is
    ///    refused as such and the council admits again.
    /// 3. A record with one wrong root is refused at that root, while the genuine record
    ///    over the same bytes still re-proves.
    #[test]
    fn changed_bytes_other_checkers_and_forged_records_are_refused() {
        let Some(lib) = pinned_lib() else {
            eprintln!("SKIP: pinned Reference lib/lean absent");
            return;
        };
        let prelude = n("Init.Prelude");
        let roots = [prelude.clone()];
        let original = closure(&lib, &["Init.Prelude"]);
        assert_eq!(original.len(), 1);
        let unchanged = declarations(&prelude, &original[0].1).expect("Prelude decodes");

        let mut docstring = original.clone();
        flip(&mut docstring[0].1, 1, b"The identity function");
        assert!(
            declarations(&prelude, &docstring[0].1).expect("still decodes") == unchanged,
            "the docstring flip must leave every declaration as it was"
        );

        on_import_stack(|| {
            let store = Memory::default();
            let checker = identity("checker A");
            let modules = inputs(&original);
            let (_, stored) = import_with(&modules, &roots, reuse(checker, &store));
            assert_eq!(stored.record_write, RecordWrite::Stored);
            let key = stored.key.expect("reuse-verified computes a key");
            let record_bytes = store.load(key).unwrap().expect("the record was stored");
            let record = ImportReuseRecord::parse(&record_bytes).expect("the record parses");

            // 1. A docstring byte: another key, so the council admits again.
            let (_, changed) = import_with(&inputs(&docstring), &roots, reuse(checker, &store));
            assert_ne!(changed.key, Some(key));
            assert_eq!(changed.record, RecordLookup::Absent);
            assert_eq!(changed.admission, ImportAdmission::Council);

            // 2. Another checker identity's record under this identity's key.
            let other = identity("checker B");
            let other_key = ImportClosureKey::compute(&modules, &roots, &KVMap::new(), other);
            assert_ne!(other_key, key, "the identity is part of the key");
            store.save(other_key, &record_bytes).unwrap();
            let (_, refused) = import_with(&modules, &roots, reuse(other, &store));
            assert_eq!(
                refused.record,
                RecordLookup::Refused(ImportReuseRefusal::CheckerIdentity)
            );
            assert_eq!(refused.admission, ImportAdmission::Council);
            assert_eq!(refused.record_write, RecordWrite::Stored);

            let base = Engine::from_environment(Environment::new());
            // 3. The genuine bytes with one wrong root: refused at that root.
            let wrong = record
                .clone()
                .with_declaration_root(fln_hash::domain::hash(Domain::CacheKey, b"planted"));
            let verdict = base
                .reuse_recorded_closure(
                    &modules,
                    &roots,
                    &KVMap::new(),
                    limits(1),
                    key,
                    checker,
                    &wrong,
                    None,
                )
                .expect("a refusal is not an import error")
                .into_complete()
                .expect("the re-proof answers");
            assert!(
                matches!(
                    verdict,
                    ImportReuse::Refused(ImportReuseRefusal::Root {
                        at: "declarations",
                        module: None
                    })
                ),
                "{verdict:?}"
            );
            // The genuine record still re-proves: the refusals above are about the
            // planted differences, not about a rebuild that never succeeds.
            assert!(matches!(
                base.reuse_recorded_closure(
                    &modules,
                    &roots,
                    &KVMap::new(),
                    limits(1),
                    key,
                    checker,
                    &record,
                    None,
                )
                .expect("the genuine record re-proves")
                .into_complete()
                .expect("the re-proof answers"),
                ImportReuse::Reused(_)
            ));
        });
    }

    /// One `.olean` for module `Lib`, written by this toolchain from `source`.
    fn built_lib(source: &str) -> Vec<u8> {
        let lib = n("Lib");
        let built = Engine::builder()
            .build_empty()
            .compile_source_modules(
                &[SourceModuleInput {
                    name: &lib,
                    source: source.as_bytes(),
                }],
                &lib,
                &KVMap::new(),
                super::super::SourceModuleCheckLimits::new(SourceCheckLimits::new(
                    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
                )),
                OleanWriteBudget::default(),
            )
            .expect("Lib builds")
            .into_complete()
            .expect("Lib builds completely");
        assert_eq!(built.artifacts.len(), 1);
        built.artifacts[0].bytes.clone()
    }

    /// The key is not the only guard. A record whose key is forged onto another closure
    /// (here: the same module name, a different declaration, both genuine artifacts that
    /// decode) is refused by the ROOTS at that module, through the store and the posture
    /// door, and the council admits the real closure instead.
    #[test]
    fn a_record_forged_onto_other_declarations_is_refused_by_the_roots() {
        let lib = n("Lib");
        let roots = [lib.clone()];
        let first = built_lib("prelude\ndef Lib.v.{u} {A : Sort u} (x : A) : A := x\n");
        let other = built_lib("prelude\ndef Lib.w.{u} {A : Sort u} (x : A) : A := x\n");
        assert_ne!(first, other);
        let input = |artifact: &'static [u8]| -> Vec<OleanModuleInput<'static>> {
            let name: &'static Name = Box::leak(Box::new(n("Lib")));
            vec![OleanModuleInput {
                name,
                artifact,
                server_artifact: None,
                private_artifact: None,
            }]
        };
        let first: &'static [u8] = Box::leak(first.into_boxed_slice());
        let other: &'static [u8] = Box::leak(other.into_boxed_slice());
        on_import_stack(|| {
            let store = Memory::default();
            let checker = identity("checker A");
            let (_, stored) = import_with(&input(first), &roots, reuse(checker, &store));
            assert_eq!(stored.record_write, RecordWrite::Stored);
            let record = ImportReuseRecord::parse(
                &store
                    .load(stored.key.expect("a key"))
                    .unwrap()
                    .expect("the record was stored"),
            )
            .expect("the record parses");

            let other_key =
                ImportClosureKey::compute(&input(other), &roots, &KVMap::new(), checker);
            store
                .save(other_key, &record.clone().with_key(other_key).to_bytes())
                .unwrap();
            let (admitted, refused) = import_with(&input(other), &roots, reuse(checker, &store));
            assert_eq!(
                refused.record,
                RecordLookup::Refused(ImportReuseRefusal::Root {
                    at: "module-result",
                    module: Some(lib.clone()),
                })
            );
            assert_eq!(refused.admission, ImportAdmission::Council);
            assert!(admitted.engine.environment.contains(&n("Lib.w")));
            assert!(!admitted.engine.environment.contains(&n("Lib.v")));
        });
    }

    /// The record format is strict and never panics: a round trip is exact, and every
    /// truncation and every single-byte change of a real record is refused.
    #[test]
    fn records_round_trip_and_every_damaged_record_is_refused() {
        let record = ImportReuseRecord {
            key: fln_hash::domain::hash(Domain::CacheKey, b"key"),
            checker: fln_hash::domain::hash(Domain::CacheKey, b"checker"),
            base_root: fln_hash::domain::hash(Domain::CacheKey, b"base"),
            declaration_root: fln_hash::domain::hash(Domain::CacheKey, b"declarations"),
            result_root: fln_hash::domain::hash(Domain::CacheKey, b"result"),
            modules: vec![
                RecordedModule {
                    name: n("A.B").to_canonical_bytes(),
                    base_root: fln_hash::domain::hash(Domain::CacheKey, b"a0"),
                    result_root: fln_hash::domain::hash(Domain::CacheKey, b"a1"),
                    rows: vec![
                        (
                            1,
                            CheckerAgreement {
                                schema: "fln-checker/v1",
                                ground: CheckerAdmissionGround::BodyCheckedAgainstDeclaredType,
                            },
                        ),
                        (
                            0,
                            CheckerAgreement {
                                schema: fln_checker::admit::ADMISSION_SCHEMA,
                                ground: CheckerAdmissionGround::AxiomPreamble,
                            },
                        ),
                        (
                            12,
                            CheckerAgreement {
                                schema: "fln-checker/v1",
                                ground: CheckerAdmissionGround::PartialQuarantine,
                            },
                        ),
                    ],
                },
                RecordedModule {
                    name: n("C").to_canonical_bytes(),
                    base_root: fln_hash::domain::hash(Domain::CacheKey, b"a1"),
                    result_root: fln_hash::domain::hash(Domain::CacheKey, b"a1"),
                    rows: Vec::new(),
                },
            ],
        };
        let bytes = record.to_bytes();
        assert_eq!(ImportReuseRecord::parse(&bytes), Ok(record));
        for end in 0..bytes.len() {
            assert!(
                ImportReuseRecord::parse(&bytes[..end]).is_err(),
                "prefix {end}"
            );
        }
        for at in 0..bytes.len() {
            let mut damaged = bytes.clone();
            damaged[at] ^= 0x01;
            assert!(ImportReuseRecord::parse(&damaged).is_err(), "byte {at}");
        }
        assert!(ImportReuseRecord::parse(b"").is_err());
        assert!(ImportReuseRecord::parse(&[0xff; 64]).is_err());

        // A pre-Merkle record differs only in its schema line and is correctly sealed,
        // so it is refused for its format, not for damage.
        let text = String::from_utf8(bytes).expect("records are UTF-8");
        let body_end = text
            .trim_end_matches('\n')
            .rfind('\n')
            .expect("a seal line")
            + 1;
        let old_body = text[..body_end].replacen(RECORD_SCHEMA, "fln.import-reuse-record/1", 1);
        assert_ne!(old_body, text[..body_end]);
        let old = format!("{old_body}seal {}\n", seal(old_body.as_bytes()).to_hex());
        assert_eq!(
            ImportReuseRecord::parse(old.as_bytes()),
            Err(ImportReuseRefusal::Malformed("unknown schema"))
        );
    }
}
