//! The census-derived W5 extern row schema (`ExternRowContractV1`, bead
//! `franken_lean-pw6t`): one canonical row per `@[extern]` declaration at the pin,
//! joining the extern census, the builtin environment/partition shards, and the
//! ABI ownership contract, with stable ids and typed refusals everywhere.
//!
//! # What this module is, and what it deliberately is not
//!
//! This is the **schema and table authority** for the intrinsic families (W5 beads
//! `52h0`, `65t5`, `m7vm`, `zm78`): the row type, the closed field vocabularies,
//! the canonical wire codec, and the content-addressed hash framing. It owns no
//! execution semantics — values, budgets, and the FL-INV-07 outcome algebra arrive
//! with the families, which is why this crate is std-only and adds no dependency
//! edges (the design record lives in the bead).
//!
//! # The wire format
//!
//! Rows in `contracts/EXTERN_ROW_CONTRACT.txt` follow the contract idiom landed by
//! `franken_lean-53v`: space-separated `key=value` fields, values percent-encoded
//! with the fixed safe set `-._~/:$` plus ASCII alphanumerics, every field
//! round-trip checked at parse so a non-canonical spelling is a refusal rather
//! than a silent normalization. The final line of the contract is its own
//! `contract-root`, recomputed at load; a row that does not recompute is drift,
//! never a pass.

use std::collections::BTreeMap;
use std::fmt;

/// Schema of the canonical contract artifact.
pub const CONTRACT_SCHEMA: &str = "fln-extern-row-contract/1";
/// The contract's declared type name.
pub const CONTRACT_NAME: &str = "ExternRowContractV1";
/// Schema of the semantic NDJSON evidence stream for this contract's suites.
pub const SEMANTIC_SCHEMA: &str = "fln.extern-rows.semantic/1";
/// Schema of the telemetry NDJSON evidence stream for this contract's suites.
pub const TELEMETRY_SCHEMA: &str = "fln.extern-rows.telemetry/1";
/// Hash domain for a single extern row's `row-root`.
pub const ROW_ROOT_DOMAIN: &str = "fln.extern-row/1";
/// Hash domain for the whole contract's terminal `contract-root`.
pub const CONTRACT_ROOT_DOMAIN: &str = "fln.extern-row-contract/1";
/// The declared anti-vacuity population: the pin's extern census, and nothing else.
/// Moving it is a schema revision, not an edit.
pub const DECLARED_ROW_COUNT: usize = 954;

/// A load or validation failure. Every failure path is a typed `Result`; nothing
/// in this module panics on malformed input (FL-INV-07 posture: malformed
/// artifacts are values, not invariant violations).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContractError(String);

impl ContractError {
    pub fn new(message: impl Into<String>) -> Self {
        ContractError(message.into())
    }

    pub fn message(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for ContractError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for ContractError {}

/// The declaration kind of an extern row, from the census.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ExternKind {
    Defn,
    Opaque,
    Ctor,
    Axiom,
}

impl ExternKind {
    pub fn as_str(self) -> &'static str {
        match self {
            ExternKind::Defn => "defn",
            ExternKind::Opaque => "opaque",
            ExternKind::Ctor => "ctor",
            ExternKind::Axiom => "axiom",
        }
    }

    pub fn parse(text: &str) -> Result<Self, ContractError> {
        match text {
            "defn" => Ok(ExternKind::Defn),
            "opaque" => Ok(ExternKind::Opaque),
            "ctor" => Ok(ExternKind::Ctor),
            "axiom" => Ok(ExternKind::Axiom),
            other => Err(ContractError::new(format!("unknown extern kind {other:?}"))),
        }
    }
}

/// The effect family of an extern row, from the builtin environment shard.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum EffectClass {
    Pure,
    ToolchainMonad,
    Io,
    MonadTransformer,
    Task,
    State,
    Effect,
}

impl EffectClass {
    pub fn as_str(self) -> &'static str {
        match self {
            EffectClass::Pure => "pure",
            EffectClass::ToolchainMonad => "toolchain-monad",
            EffectClass::Io => "io",
            EffectClass::MonadTransformer => "monad-transformer",
            EffectClass::Task => "task",
            EffectClass::State => "state",
            EffectClass::Effect => "effect",
        }
    }

    pub fn parse(text: &str) -> Result<Self, ContractError> {
        match text {
            "pure" => Ok(EffectClass::Pure),
            "toolchain-monad" => Ok(EffectClass::ToolchainMonad),
            "io" => Ok(EffectClass::Io),
            "monad-transformer" => Ok(EffectClass::MonadTransformer),
            "task" => Ok(EffectClass::Task),
            "state" => Ok(EffectClass::State),
            "effect" => Ok(EffectClass::Effect),
            other => Err(ContractError::new(format!(
                "unknown effect class {other:?}"
            ))),
        }
    }
}

/// The Lean-side safety annotation of an extern row.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SafetyClass {
    Safe,
    Partial,
    Unsafe,
}

impl SafetyClass {
    pub fn as_str(self) -> &'static str {
        match self {
            SafetyClass::Safe => "safe",
            SafetyClass::Partial => "partial",
            SafetyClass::Unsafe => "unsafe",
        }
    }

    pub fn parse(text: &str) -> Result<Self, ContractError> {
        match text {
            "safe" => Ok(SafetyClass::Safe),
            "partial" => Ok(SafetyClass::Partial),
            "unsafe" => Ok(SafetyClass::Unsafe),
            other => Err(ContractError::new(format!(
                "unknown safety class {other:?}"
            ))),
        }
    }
}

/// The Native Mirror partition of an extern row (plan §4.3). Extern rows are
/// expected to be `ToolchainApi` (native implementation required); the census
/// join records the measured partition and the generator refuses anything else,
/// so an unexpected class can never ride the table silently.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PartitionClass {
    ToolchainApi,
    LibraryCode,
    UserFacingData,
}

impl PartitionClass {
    pub fn as_str(self) -> &'static str {
        match self {
            PartitionClass::ToolchainApi => "toolchain-api",
            PartitionClass::LibraryCode => "library-code",
            PartitionClass::UserFacingData => "user-facing-data",
        }
    }

    pub fn parse(text: &str) -> Result<Self, ContractError> {
        match text {
            "toolchain-api" => Ok(PartitionClass::ToolchainApi),
            "library-code" => Ok(PartitionClass::LibraryCode),
            "user-facing-data" => Ok(PartitionClass::UserFacingData),
            other => Err(ContractError::new(format!(
                "unknown partition class {other:?}"
            ))),
        }
    }
}

/// The mode axis (plan §4): which build modes may serve this row natively. The
/// `LLVM.*` upstream-backend family is the one declared exception (`Frontier`
/// with the reason carried in the contract header): FrankenLean has no LLVM on
/// the sovereign path, so those rows are never `all`.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ModeSupport {
    All,
    Frontier,
}

impl ModeSupport {
    pub fn as_str(self) -> &'static str {
        match self {
            ModeSupport::All => "all",
            ModeSupport::Frontier => "frontier",
        }
    }

    pub fn parse(text: &str) -> Result<Self, ContractError> {
        match text {
            "all" => Ok(ModeSupport::All),
            "frontier" => Ok(ModeSupport::Frontier),
            other => Err(ContractError::new(format!(
                "unknown mode support {other:?}"
            ))),
        }
    }
}

/// One binder of the Lean-side telescope, canonically: quoted name, binder-info
/// class, and the mix256 type hash from the environment shard.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Binder {
    pub name: String,
    pub info: String,
    pub type_hash: String,
}

/// The ownership convention of the C symbol, canonically and never guessed:
/// either the ABI contract's per-parameter signature, or a declared rule class.
/// A contradiction between the rule and the ABI contract fails generation; an
/// unclassifiable row fails generation. The rule classes: the FFI default
/// (args borrowed; result owned — `borrowed-result` for the `*_borrowed`
/// family), `scalar-args,scalar-result` for libm-class bare symbols (no heap
/// objects cross the call), and `llvm-c-api` for the upstream-backend family.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Ownership {
    AbiSignature(String),
    DefaultRuleOwnedResult,
    DefaultRuleBorrowedResult,
    ScalarRule,
    LlvmCApi,
}

/// Executable disposition of one generated extern argument.
///
/// Raw pointers and result-only ownership classes are deliberately absent:
/// they do not establish a safe FLBC register transfer.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ArgumentOwnership {
    Borrowed,
    Owned,
    Unique,
    Scalar,
}

impl ArgumentOwnership {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Borrowed => "borrowed",
            Self::Owned => "owned",
            Self::Unique => "unique",
            Self::Scalar => "scalar",
        }
    }
}

/// Executable ownership class of one generated extern result.
///
/// `RawObject` is intentionally explicit: it records that the C signature does
/// not itself prove ownership. Golem may execute such a row only through a
/// reviewed row-specific implementation that returns an internally owned
/// object; this type never converts a raw pointer.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ResultOwnership {
    Owned,
    Borrowed,
    Scalar,
    RawObject,
}

impl ResultOwnership {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Owned => "owned",
            Self::Borrowed => "borrowed",
            Self::Scalar => "scalar",
            Self::RawObject => "raw-object",
        }
    }
}

impl Ownership {
    pub fn as_str(&self) -> String {
        match self {
            Ownership::AbiSignature(signature) => format!("abi({signature})"),
            Ownership::DefaultRuleOwnedResult => "rule(borrowed-args,owned-result)".to_string(),
            Ownership::DefaultRuleBorrowedResult => {
                "rule(borrowed-args,borrowed-result)".to_string()
            }
            Ownership::ScalarRule => "rule(scalar-args,scalar-result)".to_string(),
            Ownership::LlvmCApi => "rule(llvm-c-api)".to_string(),
        }
    }

    pub fn parse(text: &str) -> Result<Self, ContractError> {
        if let Some(signature) = text.strip_prefix("abi(").and_then(|t| t.strip_suffix(')')) {
            if signature.is_empty() {
                return Err(ContractError::new("empty abi() ownership signature"));
            }
            return Ok(Ownership::AbiSignature(signature.to_string()));
        }
        match text {
            "rule(borrowed-args,owned-result)" => Ok(Ownership::DefaultRuleOwnedResult),
            "rule(borrowed-args,borrowed-result)" => Ok(Ownership::DefaultRuleBorrowedResult),
            "rule(scalar-args,scalar-result)" => Ok(Ownership::ScalarRule),
            "rule(llvm-c-api)" => Ok(Ownership::LlvmCApi),
            other => Err(ContractError::new(format!(
                "unknown ownership form {other:?}"
            ))),
        }
    }

    /// Parse the argument half of this generated ownership contract.
    ///
    /// The caller supplies the executable FLBC arity rather than the Lean
    /// telescope arity: erased type parameters do not cross the runtime ABI.
    pub fn argument_ownership(
        &self,
        argument_count: usize,
    ) -> Result<Vec<ArgumentOwnership>, ContractError> {
        let ownership = match self {
            Self::AbiSignature(signature) => parse_abi_argument_ownership(signature)?,
            Self::DefaultRuleOwnedResult | Self::DefaultRuleBorrowedResult => {
                repeated_argument_ownership(ArgumentOwnership::Borrowed, argument_count)?
            }
            Self::ScalarRule => {
                repeated_argument_ownership(ArgumentOwnership::Scalar, argument_count)?
            }
            Self::LlvmCApi => {
                return Err(ContractError::new(
                    "llvm-c-api ownership does not establish executable FLBC argument transfer",
                ));
            }
        };
        if ownership.len() != argument_count {
            return Err(ContractError::new(format!(
                "ownership signature carries {} executable arguments, FLBC carries {argument_count}",
                ownership.len()
            )));
        }
        Ok(ownership)
    }

    /// Parse the result half of this generated ownership contract.
    pub fn result_ownership(&self) -> Result<ResultOwnership, ContractError> {
        match self {
            Self::AbiSignature(signature) => parse_abi_result_ownership(signature),
            Self::DefaultRuleOwnedResult => Ok(ResultOwnership::Owned),
            Self::DefaultRuleBorrowedResult => Ok(ResultOwnership::Borrowed),
            Self::ScalarRule => Ok(ResultOwnership::Scalar),
            Self::LlvmCApi => Err(ContractError::new(
                "llvm-c-api ownership does not establish executable FLBC result transfer",
            )),
        }
    }
}

fn repeated_argument_ownership(
    disposition: ArgumentOwnership,
    count: usize,
) -> Result<Vec<ArgumentOwnership>, ContractError> {
    let mut ownership = Vec::new();
    ownership.try_reserve_exact(count).map_err(|_| {
        ContractError::new(format!(
            "could not reserve {count} generated argument ownership dispositions"
        ))
    })?;
    ownership.resize(count, disposition);
    Ok(ownership)
}

fn parse_abi_argument_ownership(signature: &str) -> Result<Vec<ArgumentOwnership>, ContractError> {
    let (parameters, result) = signature.split_once(" -> ").ok_or_else(|| {
        ContractError::new(format!(
            "ABI ownership signature lacks canonical result separator: {signature:?}"
        ))
    })?;
    if result.is_empty() {
        return Err(ContractError::new(
            "ABI ownership signature has an empty result class",
        ));
    }
    let parameters = parameters
        .strip_prefix('(')
        .and_then(|text| text.strip_suffix(')'))
        .ok_or_else(|| {
            ContractError::new(format!(
                "ABI ownership parameter list is not parenthesized: {parameters:?}"
            ))
        })?;
    if parameters.is_empty() || parameters == "()" {
        return Ok(Vec::new());
    }

    let count = parameters.split(", ").count();
    let mut ownership = Vec::new();
    ownership.try_reserve_exact(count).map_err(|_| {
        ContractError::new(format!(
            "could not reserve {count} ABI argument ownership dispositions"
        ))
    })?;
    for parameter in parameters.split(", ") {
        if parameter.is_empty() {
            return Err(ContractError::new(
                "ABI ownership signature carries an empty parameter",
            ));
        }
        let class = parameter
            .rsplit_once(": ")
            .map_or(parameter, |(_, class)| class);
        let disposition = match class {
            "borrowed_arg" => ArgumentOwnership::Borrowed,
            "owned_arg" => ArgumentOwnership::Owned,
            "unique_arg" => ArgumentOwnership::Unique,
            "value" => ArgumentOwnership::Scalar,
            "raw_object" => {
                return Err(ContractError::new(format!(
                    "raw_object argument {parameter:?} has no safe FLBC ownership disposition"
                )));
            }
            other => {
                return Err(ContractError::new(format!(
                    "unknown ABI argument ownership class {other:?}"
                )));
            }
        };
        ownership.push(disposition);
    }
    Ok(ownership)
}

fn parse_abi_result_ownership(signature: &str) -> Result<ResultOwnership, ContractError> {
    let (_, result) = signature.split_once(" -> ").ok_or_else(|| {
        ContractError::new(format!(
            "ABI ownership signature lacks canonical result separator: {signature:?}"
        ))
    })?;
    if result.is_empty() {
        return Err(ContractError::new(
            "ABI ownership signature has an empty result class",
        ));
    }
    let class = result.rsplit_once(": ").map_or(result, |(_, class)| class);
    match class {
        "owned_res" => Ok(ResultOwnership::Owned),
        "borrowed_res" => Ok(ResultOwnership::Borrowed),
        "value" => Ok(ResultOwnership::Scalar),
        "raw_object" => Ok(ResultOwnership::RawObject),
        other => Err(ContractError::new(format!(
            "unknown ABI result ownership class {other:?}"
        ))),
    }
}

/// One canonical extern row (parsed form; the generated table's `&'static` twin
/// lives in `extern_table_generated.rs` and is zipped against this field-by-field
/// at load).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExternRow {
    /// Stable row id: `extern:<display-name>`. Names are unique in the census;
    /// the id is content, never a position.
    pub id: String,
    /// Display Lean name, e.g. `Nat.add`.
    pub name: String,
    /// Census declaration kind.
    pub kind: ExternKind,
    /// Display module, e.g. `Init.Prelude`.
    pub module: String,
    /// Universe parameter count.
    pub levels: u32,
    /// Lean arity.
    pub arity: u32,
    /// Canonical telescope (binders in order).
    pub telescope: Vec<Binder>,
    /// mix256 type hash from the environment shard.
    pub type_hash: String,
    /// mix256 value hash, or `-` where the kind carries no value body.
    pub value_hash: String,
    /// Lean-side safety annotation.
    pub safety: SafetyClass,
    /// Canonical attribute string (e.g. `extern;reducibility=...`).
    pub attributes: String,
    /// Extern entry class (`standard` at the pin).
    pub entry_class: String,
    /// Extern entry scope (`all` at the pin).
    pub entry_scope: String,
    /// The C symbol, e.g. `lean_add`.
    pub symbol: String,
    /// Effect family from the environment shard.
    pub effect: EffectClass,
    /// Native Mirror partition from the partition shard.
    pub partition: PartitionClass,
    /// Ownership convention (never guessed).
    pub ownership: Ownership,
    /// Mode support.
    pub mode: ModeSupport,
    /// Profile support (`faithful,sound` — intrinsics preserve semantics).
    pub profile: String,
    /// The row's content address over every preceding field.
    pub row_root: String,
}

impl ExternRow {
    /// The fields that content-address this row, in canonical order. The wire
    /// order, the hash order, and the generated-table order are one order, so no
    /// projection can disagree about what the bytes mean.
    pub fn root_fields(&self) -> Vec<String> {
        vec![
            self.id.clone(),
            self.name.clone(),
            self.kind.as_str().to_string(),
            self.module.clone(),
            self.levels.to_string(),
            self.arity.to_string(),
            canonical_telescope(&self.telescope),
            self.type_hash.clone(),
            self.value_hash.clone(),
            self.safety.as_str().to_string(),
            self.attributes.clone(),
            self.entry_class.clone(),
            self.entry_scope.clone(),
            self.symbol.clone(),
            self.effect.as_str().to_string(),
            self.partition.as_str().to_string(),
            self.ownership.as_str(),
            self.mode.as_str().to_string(),
            self.profile.clone(),
        ]
    }

    pub fn compute_row_root(&self) -> String {
        framed_hash(
            ROW_ROOT_DOMAIN,
            self.root_fields().iter().map(String::as_str),
        )
    }
}

/// The canonical telescope encoding: `name:info:hash;...` with each component
/// percent-encoded, and `-` for an empty telescope — the same spelling the
/// generator emits, so wire, hash, and table agree.
pub fn canonical_telescope(binders: &[Binder]) -> String {
    if binders.is_empty() {
        return "-".to_string();
    }
    binders
        .iter()
        .map(|binder| format!("{}:{}:{}", binder.name, binder.info, binder.type_hash))
        .collect::<Vec<_>>()
        .join(";")
}

/// Parse the canonical telescope, refusing malformed and truncated forms.
pub fn parse_telescope(text: &str) -> Result<Vec<Binder>, ContractError> {
    if text == "-" {
        return Ok(Vec::new());
    }
    let mut binders = Vec::new();
    for cell in text.split(';') {
        let mut parts = cell.splitn(3, ':');
        let name = parts.next().unwrap_or_default();
        let info = parts.next().unwrap_or_default();
        let hash = parts.next().unwrap_or_default();
        if name.is_empty() || info.is_empty() || hash.is_empty() {
            return Err(ContractError::new(format!(
                "malformed telescope cell {cell:?}"
            )));
        }
        binders.push(Binder {
            name: name.to_string(),
            info: info.to_string(),
            type_hash: hash.to_string(),
        });
    }
    Ok(binders)
}

/// The FNV-1a-64 digest, framed exactly as the 53v contract family frames it:
/// `fnv1a64:` plus sixteen lowercase hex digits.
pub fn fnv(bytes: &[u8]) -> String {
    let mut value = 0xcbf29ce484222325_u64;
    for byte in bytes {
        value ^= u64::from(*byte);
        value = value.wrapping_mul(0x100000001b3);
    }
    format!("fnv1a64:{value:016x}")
}

/// Content-address a field list under a domain tag: each field u64le-length-
/// prefixed, the domain first. Mirror of the 53v framing; the generator and the
/// tests re-implement it independently so a one-sided drift has nowhere to hide.
pub fn framed_hash<'a>(domain: &'a str, fields: impl IntoIterator<Item = &'a str>) -> String {
    let mut payload = Vec::new();
    for field in std::iter::once(domain).chain(fields) {
        payload.extend_from_slice(&(field.len() as u64).to_le_bytes());
        payload.extend_from_slice(field.as_bytes());
    }
    fnv(&payload)
}

/// Percent-encode with the fixed safe set (ASCII alphanumerics plus `-._~/:$`).
pub fn percent_encode(value: &str) -> String {
    let mut encoded = String::new();
    for byte in value.bytes() {
        if byte.is_ascii_alphanumeric()
            || matches!(byte, b'-' | b'.' | b'_' | b'~' | b'/' | b':' | b'$')
        {
            encoded.push(char::from(byte));
        } else {
            use std::fmt::Write as _;
            let _ = write!(encoded, "%{byte:02X}");
        }
    }
    encoded
}

fn hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

/// Percent-decode, refusing truncated and invalid escapes and non-UTF-8 results.
pub fn percent_decode(value: &str) -> Result<String, ContractError> {
    let bytes = value.as_bytes();
    let mut decoded = Vec::with_capacity(bytes.len());
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] != b'%' {
            decoded.push(bytes[index]);
            index += 1;
            continue;
        }
        if index + 2 >= bytes.len() {
            return Err(ContractError::new(format!(
                "truncated percent escape in {value:?}"
            )));
        }
        let high = hex_nibble(bytes[index + 1])
            .ok_or_else(|| ContractError::new(format!("invalid escape in {value:?}")))?;
        let low = hex_nibble(bytes[index + 2])
            .ok_or_else(|| ContractError::new(format!("invalid escape in {value:?}")))?;
        decoded.push((high << 4) | low);
        index += 3;
    }
    String::from_utf8(decoded)
        .map_err(|_| ContractError::new(format!("percent-decoded value is not UTF-8: {value:?}")))
}

/// Parse a line of `key=value` tokens into a field map, refusing duplicates,
/// empty keys/values, and non-canonical percent spellings.
pub fn parse_fields(text: &str) -> Result<BTreeMap<String, String>, ContractError> {
    let mut values = BTreeMap::new();
    for token in text.split_ascii_whitespace() {
        let (key, value) = token
            .split_once('=')
            .ok_or_else(|| ContractError::new(format!("field {token:?} is not key=value")))?;
        if key.is_empty() || value.is_empty() {
            return Err(ContractError::new(format!(
                "field {token:?} has an empty key or value"
            )));
        }
        let decoded = percent_decode(value)?;
        if percent_encode(&decoded) != value {
            return Err(ContractError::new(format!(
                "field {key:?} is not canonically percent-encoded"
            )));
        }
        if values.insert(key.to_string(), decoded).is_some() {
            return Err(ContractError::new(format!("duplicate field {key:?}")));
        }
    }
    Ok(values)
}

/// Serialize fields in canonical order with canonical percent-encoding.
pub fn render_fields(fields: &[(&str, &str)]) -> String {
    fields
        .iter()
        .map(|(key, value)| format!("{key}={}", percent_encode(value)))
        .collect::<Vec<_>>()
        .join(" ")
}

fn take(fields: &BTreeMap<String, String>, key: &str) -> Result<String, ContractError> {
    fields
        .get(key)
        .cloned()
        .ok_or_else(|| ContractError::new(format!("extern row is missing field {key:?}")))
}

fn take_u32(fields: &BTreeMap<String, String>, key: &str) -> Result<u32, ContractError> {
    let text = take(fields, key)?;
    let value = text
        .parse::<u32>()
        .map_err(|_| ContractError::new(format!("field {key:?} is not a u32: {text:?}")))?;
    if value.to_string() != text {
        return Err(ContractError::new(format!(
            "field {key:?} is not canonical decimal: {text:?}"
        )));
    }
    Ok(value)
}

/// The exact field set of a row line, in canonical order. The parser requires
/// exactly these, no more and no less, so an unknown field is as much drift as a
/// missing one.
pub const ROW_FIELD_ORDER: &[&str] = &[
    "id",
    "name",
    "kind",
    "module",
    "levels",
    "arity",
    "telescope",
    "type-hash",
    "value-hash",
    "safety",
    "attributes",
    "entry-class",
    "entry-scope",
    "symbol",
    "effect",
    "partition",
    "ownership",
    "mode",
    "profile",
    "row-root",
];

/// Parse one `row` line into an [`ExternRow`], refusing unknown or missing
/// fields and any field whose value fails its closed vocabulary — then recompute
/// the row root, so a structurally valid line with a moved byte is still drift.
pub fn parse_row(text: &str) -> Result<ExternRow, ContractError> {
    let fields = parse_fields(text)?;
    let mut present: Vec<&str> = fields.keys().map(String::as_str).collect();
    present.sort_unstable();
    let mut expected = ROW_FIELD_ORDER.to_vec();
    expected.sort_unstable();
    if present != expected {
        return Err(ContractError::new(format!(
            "extern row fields differ from the schema: present {present:?}, expected {expected:?}"
        )));
    }

    let id = take(&fields, "id")?;
    if !id.starts_with("extern:") {
        return Err(ContractError::new(format!(
            "row id {id:?} does not carry the extern: namespace"
        )));
    }
    let name = take(&fields, "name")?;
    if id != format!("extern:{name}") {
        return Err(ContractError::new(format!(
            "row id {id:?} does not match its name {name:?}"
        )));
    }
    let kind = ExternKind::parse(&take(&fields, "kind")?)?;
    let module = take(&fields, "module")?;
    let levels = take_u32(&fields, "levels")?;
    let arity = take_u32(&fields, "arity")?;
    let telescope = parse_telescope(&take(&fields, "telescope")?)?;
    let type_hash = take(&fields, "type-hash")?;
    if !type_hash.starts_with("mix256:") {
        return Err(ContractError::new(format!(
            "type-hash {type_hash:?} is not mix256-framed"
        )));
    }
    let value_hash = take(&fields, "value-hash")?;
    if value_hash != "-" && !value_hash.starts_with("mix256:") {
        return Err(ContractError::new(format!(
            "value-hash {value_hash:?} is neither '-' nor mix256-framed"
        )));
    }
    let safety = SafetyClass::parse(&take(&fields, "safety")?)?;
    let attributes = take(&fields, "attributes")?;
    if !attributes.split(';').any(|attr| attr == "extern") {
        return Err(ContractError::new(format!(
            "attributes {attributes:?} do not carry the extern marker"
        )));
    }
    let entry_class = take(&fields, "entry-class")?;
    if entry_class != "standard" {
        return Err(ContractError::new(format!(
            "entry-class {entry_class:?} is not the pinned 'standard'"
        )));
    }
    let entry_scope = take(&fields, "entry-scope")?;
    if entry_scope != "all" {
        return Err(ContractError::new(format!(
            "entry-scope {entry_scope:?} is not the pinned 'all'"
        )));
    }
    let symbol = take(&fields, "symbol")?;
    if !(symbol.starts_with("lean_")
        || symbol.starts_with("llvm_")
        || symbol
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_'))
    {
        return Err(ContractError::new(format!(
            "symbol {symbol:?} is not a C identifier in a reviewed namespace"
        )));
    }
    let effect = EffectClass::parse(&take(&fields, "effect")?)?;
    let partition = PartitionClass::parse(&take(&fields, "partition")?)?;
    let ownership = Ownership::parse(&take(&fields, "ownership")?)?;
    let mode = ModeSupport::parse(&take(&fields, "mode")?)?;
    let profile = take(&fields, "profile")?;
    if profile != "faithful,sound" {
        return Err(ContractError::new(format!(
            "profile {profile:?} is not the pinned 'faithful,sound'"
        )));
    }
    let row_root = take(&fields, "row-root")?;

    let row = ExternRow {
        id,
        name,
        kind,
        module,
        levels,
        arity,
        telescope,
        type_hash,
        value_hash,
        safety,
        attributes,
        entry_class,
        entry_scope,
        symbol,
        effect,
        partition,
        ownership,
        mode,
        profile,
        row_root,
    };
    let recomputed = row.compute_row_root();
    if row.row_root != recomputed {
        return Err(ContractError::new(format!(
            "row {} carries root {} but recomputes to {recomputed}",
            row.id, row.row_root
        )));
    }
    Ok(row)
}

/// Render a row back to its canonical line (body, without the leading `row `).
pub fn render_row(row: &ExternRow) -> String {
    let levels = row.levels.to_string();
    let arity = row.arity.to_string();
    let telescope = canonical_telescope(&row.telescope);
    let ownership = row.ownership.as_str();
    let fields = vec![
        ("id", row.id.as_str()),
        ("name", row.name.as_str()),
        ("kind", row.kind.as_str()),
        ("module", row.module.as_str()),
        ("levels", levels.as_str()),
        ("arity", arity.as_str()),
        ("telescope", telescope.as_str()),
        ("type-hash", row.type_hash.as_str()),
        ("value-hash", row.value_hash.as_str()),
        ("safety", row.safety.as_str()),
        ("attributes", row.attributes.as_str()),
        ("entry-class", row.entry_class.as_str()),
        ("entry-scope", row.entry_scope.as_str()),
        ("symbol", row.symbol.as_str()),
        ("effect", row.effect.as_str()),
        ("partition", row.partition.as_str()),
        ("ownership", ownership.as_str()),
        ("mode", row.mode.as_str()),
        ("profile", row.profile.as_str()),
        ("row-root", row.row_root.as_str()),
    ];
    render_fields(&fields)
}

/// Require a strictly ascending, duplicate-free sequence.
pub fn require_sorted_unique<'a>(
    values: impl IntoIterator<Item = &'a str>,
    context: &str,
) -> Result<(), ContractError> {
    let values = values.into_iter().collect::<Vec<_>>();
    if values.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(ContractError::new(format!(
            "{context} are not strictly sorted and unique"
        )));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{ArgumentOwnership, Ownership, ResultOwnership};

    #[test]
    fn executable_argument_ownership_parses_named_and_bare_abi_classes() {
        let named = Ownership::parse(
            "abi((a: owned_arg, i: borrowed_arg, u: unique_arg, n: value) -> raw_object)",
        )
        .expect("named ABI ownership signature");
        assert_eq!(
            named
                .argument_ownership(4)
                .expect("all safe executable ownership classes"),
            vec![
                ArgumentOwnership::Owned,
                ArgumentOwnership::Borrowed,
                ArgumentOwnership::Unique,
                ArgumentOwnership::Scalar,
            ]
        );

        let bare =
            Ownership::parse("abi((borrowed_arg, owned_arg, unique_arg, value) -> owned_res)")
                .expect("bare ABI ownership signature");
        assert_eq!(
            bare.argument_ownership(4)
                .expect("bare classes are executable"),
            vec![
                ArgumentOwnership::Borrowed,
                ArgumentOwnership::Owned,
                ArgumentOwnership::Unique,
                ArgumentOwnership::Scalar,
            ]
        );
        assert_eq!(
            Ownership::parse("abi(() -> owned_res)")
                .expect("zero-argument ABI signature")
                .argument_ownership(0)
                .expect("zero arguments"),
            Vec::new()
        );
    }

    #[test]
    fn executable_argument_ownership_expands_rules_and_refuses_unsafe_or_drifting_shapes() {
        assert_eq!(
            Ownership::DefaultRuleOwnedResult
                .argument_ownership(3)
                .expect("the default rule borrows every executable argument"),
            vec![ArgumentOwnership::Borrowed; 3]
        );
        assert_eq!(
            Ownership::ScalarRule
                .argument_ownership(2)
                .expect("the scalar rule classifies every executable argument"),
            vec![ArgumentOwnership::Scalar; 2]
        );

        let arity = Ownership::parse("abi((a: owned_arg) -> raw_object)")
            .expect("well-formed ABI ownership")
            .argument_ownership(2)
            .expect_err("FLBC arity drift is not guessed");
        assert_eq!(
            arity.message(),
            "ownership signature carries 1 executable arguments, FLBC carries 2"
        );

        let raw = Ownership::parse("abi((a: raw_object) -> raw_object)")
            .expect("well-formed but non-executable ABI ownership")
            .argument_ownership(1)
            .expect_err("raw pointers have no safe FLBC transfer");
        assert_eq!(
            raw.message(),
            "raw_object argument \"a: raw_object\" has no safe FLBC ownership disposition"
        );

        let llvm = Ownership::LlvmCApi
            .argument_ownership(1)
            .expect_err("the optional LLVM surface never establishes FLBC transfer");
        assert_eq!(
            llvm.message(),
            "llvm-c-api ownership does not establish executable FLBC argument transfer"
        );
    }

    #[test]
    fn executable_result_ownership_parses_abi_classes_and_rules() {
        for (signature, expected) in [
            (
                "abi((a: borrowed_arg) -> owned_res)",
                ResultOwnership::Owned,
            ),
            (
                "abi((a: borrowed_arg) -> borrowed_res)",
                ResultOwnership::Borrowed,
            ),
            ("abi((a: value) -> value)", ResultOwnership::Scalar),
            (
                "abi((a: owned_arg) -> raw_object)",
                ResultOwnership::RawObject,
            ),
            (
                "abi((a: borrowed_arg) -> result: owned_res)",
                ResultOwnership::Owned,
            ),
        ] {
            assert_eq!(
                Ownership::parse(signature)
                    .expect("ownership signature")
                    .result_ownership()
                    .expect("executable result"),
                expected
            );
        }
        assert_eq!(
            Ownership::DefaultRuleOwnedResult
                .result_ownership()
                .expect("owned rule"),
            ResultOwnership::Owned
        );
        assert_eq!(
            Ownership::DefaultRuleBorrowedResult
                .result_ownership()
                .expect("borrowed rule"),
            ResultOwnership::Borrowed
        );
        assert_eq!(
            Ownership::ScalarRule
                .result_ownership()
                .expect("scalar rule"),
            ResultOwnership::Scalar
        );
    }

    #[test]
    fn executable_result_ownership_refuses_unknown_empty_and_llvm_classes() {
        let unknown = Ownership::parse("abi((a: borrowed_arg) -> mystery)")
            .expect("well-formed ownership")
            .result_ownership()
            .expect_err("unknown result class");
        assert_eq!(
            unknown.message(),
            "unknown ABI result ownership class \"mystery\""
        );

        let empty = Ownership::parse("abi((a: borrowed_arg) -> )")
            .expect("well-formed ownership")
            .result_ownership()
            .expect_err("empty result class");
        assert_eq!(
            empty.message(),
            "ABI ownership signature has an empty result class"
        );

        let llvm = Ownership::LlvmCApi
            .result_ownership()
            .expect_err("LLVM result ownership is not executable");
        assert_eq!(
            llvm.message(),
            "llvm-c-api ownership does not establish executable FLBC result transfer"
        );
    }
}
