//! File-scale T2/T3 declaration-identity comparator (bead `fln-file-scale-t2-differential-5f1b`,
//! plan §18.2).
//!
//! Compares the checked declarations and attributes introduced by a Lean source file in
//! FrankenLean's exact production `lean` front-door environment against the pinned Reference's
//! `.olean` emission (`lean -o <file>.olean`, decoded via `fln-olean`), in the same invocation.
//!
//! Design laws:
//! * **Exact front-door environment, never stdout parsing** — native snapshots come directly
//!   from `fln_cli::capture_lean_source`, which shares `lean`'s exact pipeline line-for-line.
//! * **Declared, versioned normalizer (`T2NormalizerId::V1`)** — strips ONLY alpha binder names
//!   (`ForallE`/`Lam`/`LetE`), canonical positional universe parameter names + algebraic `Level`
//!   normalization, and `ExprNode::MData` wrappers. `BinderInfo`, types, universe levels,
//!   constant kinds, arities, flags, safety, reducibility hint classes, attributes, and
//!   auxiliary declaration name sets are NEVER stripped.
//! * **Strict T2 vs T3 separation** — proof bodies and definition values (`T3`) are compared
//!   independently of interface/statement identity (`T2`).
//! * **Inconclusive is never rejection (FL-INV-07)** — timeouts, resource stops, and
//!   missing/corrupted artifacts remain typed non-answers.
//! * **No-false-accept and ratchet discipline** — a Reference-rejected file accepted natively
//!   always fails; per-family nonzero floors cannot shrink; T2-identical files cannot regress;
//!   every residual difference must name an owner or reviewed Behavior Note.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};

use fln::OleanDecodeLimits;
use fln_cli::CapturedLeanModule;
use fln_core::expr::{BinderInfo, Expr, ExprNode};
use fln_core::level::{Level, LevelView};
use fln_core::name::{LeafView, Name};
use fln_core::scratch::{ScratchRoot, T2_DIFFERENTIAL_PREFIX};
use fln_env::constants::{ConstantInfo, DefinitionSafety, ReducibilityHints};
use fln_hash::domain::{Domain, hash as domain_hash};
use fln_olean::region::OleanView;
use fln_olean::source_extensions::{
    CoeFnKind, DecodeLimits as ExtensionDecodeLimits, InlineKind, ReducibilityStatus, SimpKind,
    SourceExtensions, decode as decode_source_extensions,
};
use fln_server::json_string;

pub mod runner;

/// Versioned identifier of the T2/T3 declaration normalizer (plan §18.2).
pub const T2_NORMALIZER_V1_ID: &str = "fln.t2-decl-normalizer/1";
/// On-disk JSONL checkpoint schema for crash/resume differential runs.
pub const CHECKPOINT_SCHEMA: &str = "fln.t2-differential-checkpoint/1";
/// Checked-in TSV ratchet ledger schema identifier.
pub const LEDGER_SCHEMA: &str = "fln.t2-differential-ledger/1";

const DEFAULT_NORMALIZE_BUDGET: usize = 2_000_000;
const DEFAULT_DIFF_BUDGET: usize = 200_000;

/// Create a fenced, self-reclaiming scratch workspace for T2 differential runs.
pub fn scratch_root(tag: &str) -> std::io::Result<ScratchRoot> {
    ScratchRoot::create(T2_DIFFERENTIAL_PREFIX, "t2-differential", tag)
}

/// Deterministic domain-separated digest of fixture/source/binary bytes.
pub fn fixture_digest_hex(bytes: &[u8]) -> String {
    domain_hash(Domain::Fixture, bytes).to_hex()
}

/// Frozen normalizer version selector. Changing normalization semantics requires
/// minting a new variant and identifier, never mutating an existing one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum T2NormalizerId {
    /// v1 (`fln.t2-decl-normalizer/1`):
    /// * strips `ForallE`/`Lam`/`LetE` binder *names* only (`BinderInfo` and `non_dep` preserved);
    /// * renumbers `ConstantVal.level_params` positionally (`#u0`, `#u1`, ...) and normalizes
    ///   `Level` algebraically via `Level::normalize()`;
    /// * strips `ExprNode::MData` wrappers only (inner expression preserved verbatim).
    V1,
}

impl T2NormalizerId {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::V1 => T2_NORMALIZER_V1_ID,
        }
    }
}

/// Typed refusal when normalization hits its structural work or depth ceiling.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NormalizeError {
    BudgetExhausted { limit: usize },
    LevelTooDeep { depth: u32 },
    TooManyBoundVars { range: u32 },
}

impl fmt::Display for NormalizeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BudgetExhausted { limit } => {
                write!(f, "T2 normalizer exceeded work budget ({limit} nodes)")
            }
            Self::LevelTooDeep { depth } => {
                write!(f, "T2 normalizer encountered level depth {depth} > limit")
            }
            Self::TooManyBoundVars { range } => {
                write!(
                    f,
                    "T2 normalizer encountered loose bvar range {range} > limit"
                )
            }
        }
    }
}

impl std::error::Error for NormalizeError {}

/// Coarse auxiliary-declaration classification for reporting missing/extra side names.
/// Both primary and auxiliary declarations remain part of strict `full_t2_identical`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AuxClass {
    Equation,
    Matcher,
    Sunfold,
    BreconFunctional,
    UnsafeRec,
    Mutual,
    ProofAux,
    InductiveConstruction,
    SizeOf,
    FlatCtor,
    Private,
}

impl AuxClass {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Equation => "equation",
            Self::Matcher => "matcher",
            Self::Sunfold => "sunfold",
            Self::BreconFunctional => "brecon_functional",
            Self::UnsafeRec => "unsafe_rec",
            Self::Mutual => "mutual",
            Self::ProofAux => "proof_aux",
            Self::InductiveConstruction => "inductive_construction",
            Self::SizeOf => "sizeof",
            Self::FlatCtor => "flat_ctor",
            Self::Private => "private",
        }
    }
}

/// Whether a declaration is a user/primary constant or a compiler/elaborator auxiliary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclarationRole {
    Primary,
    Auxiliary(AuxClass),
}

/// Classify a declaration name as primary vs auxiliary for structured reporting.
/// Note: auxiliary declarations are still strictly compared for `full_t2_identical`.
pub fn classify_declaration_name(name: &Name) -> DeclarationRole {
    let display = name.to_display_string();
    if display.starts_with("_private.") {
        return DeclarationRole::Auxiliary(AuxClass::Private);
    }
    let LeafView::Str(leaf) = name.leaf_view() else {
        return DeclarationRole::Primary;
    };
    if leaf == "_sunfold" {
        return DeclarationRole::Auxiliary(AuxClass::Sunfold);
    }
    if leaf == "_f" {
        return DeclarationRole::Auxiliary(AuxClass::BreconFunctional);
    }
    if leaf == "_unsafe_rec" {
        return DeclarationRole::Auxiliary(AuxClass::UnsafeRec);
    }
    if leaf == "_mutual" {
        return DeclarationRole::Auxiliary(AuxClass::Mutual);
    }
    if leaf == "_flat_ctor" {
        return DeclarationRole::Auxiliary(AuxClass::FlatCtor);
    }
    if leaf == "eq_def"
        || leaf == "eq_unfold"
        || leaf.strip_prefix("eq_").is_some_and(|rest| {
            !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit() || b == b'_')
        })
    {
        return DeclarationRole::Auxiliary(AuxClass::Equation);
    }
    if leaf.strip_prefix("match_").is_some_and(|rest| {
        !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit() || b == b'_')
    }) || leaf.strip_prefix("_sparseCasesOn_").is_some_and(|rest| {
        !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit() || b == b'_')
    }) {
        return DeclarationRole::Auxiliary(AuxClass::Matcher);
    }
    if leaf.starts_with("_proof_")
        || leaf.starts_with("_simp_")
        || leaf.starts_with("_aux_")
        || leaf.starts_with("_eval")
    {
        return DeclarationRole::Auxiliary(AuxClass::ProofAux);
    }
    if leaf == "_sizeOf_inst" || leaf == "sizeOf_spec" || leaf.starts_with("_sizeOf_") {
        return DeclarationRole::Auxiliary(AuxClass::SizeOf);
    }
    if display.ends_with(".brecOn.eq")
        || display.ends_with(".below.rec")
        || display.ends_with(".below.fn")
        || leaf == "_autoParam"
    {
        return DeclarationRole::Auxiliary(AuxClass::InductiveConstruction);
    }
    if matches!(
        leaf,
        "casesOn"
            | "recOn"
            | "binductionOn"
            | "brecOn"
            | "below"
            | "ibelow"
            | "noConfusion"
            | "noConfusionType"
            | "ctorIdx"
            | "ctorElim"
            | "ctorElimType"
            | "inj"
            | "injEq"
            | "hinj"
            | "toCtorIdx"
            | "ofNat"
            | "elim"
    ) {
        return DeclarationRole::Auxiliary(AuxClass::InductiveConstruction);
    }
    DeclarationRole::Primary
}

/// Typed failure when reading or decoding a `.olean` artifact snapshot.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SnapshotError {
    MissingArtifact { path: PathBuf },
    Io { path: PathBuf, detail: String },
    Decode { detail: String },
    ExtensionDecode { detail: String },
}

impl fmt::Display for SnapshotError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingArtifact { path } => {
                write!(f, "missing .olean artifact at {}", path.display())
            }
            Self::Io { path, detail } => {
                write!(f, "reading {}: {detail}", path.display())
            }
            Self::Decode { detail } => write!(f, "decoding .olean constants: {detail}"),
            Self::ExtensionDecode { detail } => {
                write!(f, "decoding .olean extensions: {detail}")
            }
        }
    }
}

impl std::error::Error for SnapshotError {}

/// A module's checked declarations and normalized attribute tags.
#[derive(Debug, Clone)]
pub struct ModuleSnapshot {
    pub module: Name,
    pub constants: BTreeMap<Name, ConstantInfo>,
    pub attributes: BTreeMap<Name, BTreeSet<String>>,
}

impl ModuleSnapshot {
    /// Build a snapshot directly from FrankenLean's exact `lean` front-door capture.
    pub fn from_captured_module(captured: &CapturedLeanModule) -> Self {
        let mut constants = BTreeMap::new();
        for constant in &captured.constants {
            constants.insert(constant.name().clone(), constant.clone());
        }
        Self {
            module: captured.module.clone(),
            constants,
            attributes: captured.attributes.clone(),
        }
    }

    /// Build a snapshot by decoding pinned Reference `.olean` bytes (and optional
    /// `.olean.server` / `.olean.private` companions) via `fln-olean`.
    pub fn from_olean_bytes(
        module: Name,
        bytes: &[u8],
        server: Option<&[u8]>,
        private: Option<&[u8]>,
        limits: OleanDecodeLimits,
    ) -> Result<Self, SnapshotError> {
        let decoded =
            match (server, private) {
                (Some(s), Some(p)) => fln::decode_olean_module_artifacts(bytes, s, p, limits)
                    .map_err(|error| SnapshotError::Decode {
                        detail: error.to_string(),
                    })?,
                _ => fln::decode_olean_artifact(bytes, limits).map_err(|error| {
                    SnapshotError::Decode {
                        detail: error.to_string(),
                    }
                })?,
            };
        let mut constants = BTreeMap::new();
        for constant in decoded.constants {
            constants.insert(constant.name().clone(), constant);
        }

        let mut attributes = BTreeMap::new();
        let view = OleanView::parse(bytes).map_err(|error| SnapshotError::Decode {
            detail: error.to_string(),
        })?;
        let blocks = view
            .extension_payloads(limits.module, limits.max_bytes)
            .map_err(|error| SnapshotError::ExtensionDecode {
                detail: error.to_string(),
            })?;
        let extensions = decode_source_extensions(&blocks, ExtensionDecodeLimits::default())
            .map_err(|error| SnapshotError::ExtensionDecode {
                detail: error.to_string(),
            })?;
        merge_olean_attributes(&mut attributes, &extensions);

        if let Some(server_bytes) = server {
            let server_view =
                OleanView::parse_with_dependencies(server_bytes, &[bytes]).map_err(|error| {
                    SnapshotError::Decode {
                        detail: error.to_string(),
                    }
                })?;
            let server_blocks = server_view
                .extension_payloads(limits.module, limits.max_bytes)
                .map_err(|error| SnapshotError::ExtensionDecode {
                    detail: error.to_string(),
                })?;
            let server_ext =
                decode_source_extensions(&server_blocks, ExtensionDecodeLimits::default())
                    .map_err(|error| SnapshotError::ExtensionDecode {
                        detail: error.to_string(),
                    })?;
            merge_olean_attributes(&mut attributes, &server_ext);
        }

        Ok(Self {
            module,
            constants,
            attributes,
        })
    }

    /// Read a `.olean` file (plus `.olean.server` / `.olean.private` siblings if
    /// present) and decode into a [`ModuleSnapshot`].
    pub fn from_olean_file(
        module: Name,
        path: &Path,
        limits: OleanDecodeLimits,
    ) -> Result<Self, SnapshotError> {
        if !path.is_file() {
            return Err(SnapshotError::MissingArtifact {
                path: path.to_path_buf(),
            });
        }
        let bytes = fs::read(path).map_err(|error| SnapshotError::Io {
            path: path.to_path_buf(),
            detail: error.to_string(),
        })?;
        let sibling = |suffix: &str| {
            let mut os = path.as_os_str().to_os_string();
            os.push(suffix);
            PathBuf::from(os)
        };
        let server_path = sibling(".server");
        let private_path = sibling(".private");
        let server = if server_path.is_file() {
            Some(fs::read(&server_path).map_err(|error| SnapshotError::Io {
                path: server_path,
                detail: error.to_string(),
            })?)
        } else {
            None
        };
        let private = if private_path.is_file() {
            Some(fs::read(&private_path).map_err(|error| SnapshotError::Io {
                path: private_path,
                detail: error.to_string(),
            })?)
        } else {
            None
        };
        Self::from_olean_bytes(
            module,
            &bytes,
            server.as_deref(),
            private.as_deref(),
            limits,
        )
    }
}

/// Convert decoded pinned `.olean` `SourceExtensions` into the exact same canonical
/// per-declaration attribute tag vocabulary produced by
/// `fln::source_check::modules::artifacts::extract_native_module_attributes`.
pub fn extract_olean_attributes(ext: &SourceExtensions) -> BTreeMap<Name, BTreeSet<String>> {
    let mut attrs = BTreeMap::new();
    merge_olean_attributes(&mut attrs, ext);
    attrs
}

fn merge_olean_attributes(attrs: &mut BTreeMap<Name, BTreeSet<String>>, ext: &SourceExtensions) {
    let mut tag = |decl: Name, label: String| {
        attrs.entry(decl).or_default().insert(label);
    };

    for class in &ext.classes {
        tag(class.name.clone(), "class".to_owned());
        if !class.out_params.is_empty() {
            tag(
                class.name.clone(),
                format!("class:out_params={:?}", class.out_params),
            );
        }
        if !class.out_level_params.is_empty() {
            tag(
                class.name.clone(),
                format!("class:out_level_params={:?}", class.out_level_params),
            );
        }
    }
    for instance in &ext.instances {
        tag(
            instance.declaration.clone(),
            format!("instance:priority={}", instance.priority),
        );
        if let Some(scope) = &instance.scope {
            tag(
                instance.declaration.clone(),
                format!("instance:scope={}", scope.to_display_string()),
            );
        }
    }
    for row in &ext.defaults {
        tag(
            row.declaration.clone(),
            format!(
                "default_instance:class={},priority={}",
                row.class.to_display_string(),
                row.priority
            ),
        );
    }
    for row in &ext.simps {
        match &row.kind {
            SimpKind::Unfold(decl) => tag(decl.clone(), "simp:unfold".to_owned()),
            SimpKind::UnfoldTheorems { declaration, .. } => {
                tag(declaration.clone(), "simp:unfold_theorems".to_owned());
            }
            SimpKind::Theorem(theorem) => {
                tag(
                    theorem.origin.clone(),
                    format!("simp:theorem:priority={}", theorem.priority),
                );
            }
        }
    }
    let reducibility_label = |status: ReducibilityStatus| match status {
        ReducibilityStatus::Reducible => "reducibility:reducible",
        ReducibilityStatus::Semireducible => "reducibility:semireducible",
        ReducibilityStatus::Irreducible => "reducibility:irreducible",
        ReducibilityStatus::ImplicitReducible => "reducibility:implicit_reducible",
    };
    for row in &ext.reducibility {
        tag(
            row.declaration.clone(),
            reducibility_label(row.status).to_owned(),
        );
    }
    for row in &ext.reducibility_extra {
        tag(
            row.declaration.clone(),
            format!("extra:{}", reducibility_label(row.status)),
        );
    }
    for name in &ext.protected {
        tag(name.clone(), "protected".to_owned());
    }
    for row in &ext.deprecations {
        tag(row.declaration.clone(), "deprecated".to_owned());
    }
    for name in &ext.aux_recursors {
        tag(name.clone(), "aux_recursor".to_owned());
    }
    for name in &ext.noncomputable {
        tag(name.clone(), "noncomputable".to_owned());
    }
    for name in &ext.unbox {
        tag(name.clone(), "unbox".to_owned());
    }
    for name in &ext.match_patterns {
        tag(name.clone(), "match_pattern".to_owned());
    }
    for entry in &ext.symms {
        tag(entry.declaration.clone(), "symm".to_owned());
    }
    for entry in &ext.coercions {
        let kind = match entry.kind {
            CoeFnKind::Coe => "coe",
            CoeFnKind::CoeFun => "coe_fun",
            CoeFnKind::CoeSort => "coe_sort",
        };
        tag(
            entry.declaration.clone(),
            format!("coe:{kind}:{}:{}", entry.num_args, entry.coercee),
        );
    }
    for row in &ext.inline {
        let kind = match row.kind {
            InlineKind::Inline => "inline",
            InlineKind::NoInline => "no_inline",
            InlineKind::MacroInline => "macro_inline",
            InlineKind::InlineIfReduce => "inline_if_reduce",
            InlineKind::AlwaysInline => "always_inline",
        };
        tag(row.declaration.clone(), format!("inline:{kind}"));
    }
    for row in &ext.structures {
        tag(row.name.clone(), "structure".to_owned());
    }
}

fn canonical_param_map(level_params: &[Name]) -> BTreeMap<Name, Name> {
    level_params
        .iter()
        .enumerate()
        .map(|(index, param)| {
            (
                param.clone(),
                Name::from_components([format!("#u{index}").as_str()]),
            )
        })
        .collect()
}

fn normalize_level(
    level: &Level,
    param_map: &BTreeMap<Name, Name>,
    budget: &mut usize,
) -> Result<Level, NormalizeError> {
    let mapped = subst_level_params(level, param_map, budget)?;
    Ok(mapped.normalize())
}

fn subst_level_params(
    level: &Level,
    param_map: &BTreeMap<Name, Name>,
    budget: &mut usize,
) -> Result<Level, NormalizeError> {
    if *budget == 0 {
        return Err(NormalizeError::BudgetExhausted {
            limit: DEFAULT_NORMALIZE_BUDGET,
        });
    }
    *budget -= 1;
    match level.view() {
        LevelView::Zero => Ok(Level::zero()),
        LevelView::Param(name) => {
            let renamed = param_map.get(name).cloned().unwrap_or_else(|| name.clone());
            Ok(Level::param(renamed))
        }
        LevelView::MVar(id) => Ok(Level::mvar(id.clone())),
        LevelView::Succ(inner) => {
            let inner = subst_level_params(inner, param_map, budget)?;
            inner
                .succ()
                .map_err(|error| NormalizeError::LevelTooDeep { depth: error.depth })
        }
        LevelView::Max(left, right) => {
            let left = subst_level_params(left, param_map, budget)?;
            let right = subst_level_params(right, param_map, budget)?;
            Level::max(left, right)
                .map_err(|error| NormalizeError::LevelTooDeep { depth: error.depth })
        }
        LevelView::IMax(left, right) => {
            let left = subst_level_params(left, param_map, budget)?;
            let right = subst_level_params(right, param_map, budget)?;
            Level::imax(left, right)
                .map_err(|error| NormalizeError::LevelTooDeep { depth: error.depth })
        }
    }
}

/// Normalize an expression under `normalizer`:
/// * strips ONLY `ExprNode::MData` wrappers and bound-variable binder *names*;
/// * canonically renames `level_params` and normalizes `Level` algebraically;
/// * strictly preserves `BinderInfo`, `non_dep`, `BVar` indices, constants,
///   literals, projections, and application structure.
pub fn normalize_expr(
    expr: &Expr,
    level_params: &[Name],
    normalizer: T2NormalizerId,
) -> Result<Expr, NormalizeError> {
    let T2NormalizerId::V1 = normalizer;
    let param_map = canonical_param_map(level_params);
    let mut budget = DEFAULT_NORMALIZE_BUDGET;
    normalize_expr_inner(expr, &param_map, &mut budget)
}

fn normalize_expr_inner(
    expr: &Expr,
    param_map: &BTreeMap<Name, Name>,
    budget: &mut usize,
) -> Result<Expr, NormalizeError> {
    if *budget == 0 {
        return Err(NormalizeError::BudgetExhausted {
            limit: DEFAULT_NORMALIZE_BUDGET,
        });
    }
    *budget -= 1;
    match expr.node() {
        ExprNode::MData { expr: inner, .. } => normalize_expr_inner(inner, param_map, budget),
        ExprNode::BVar { idx } => Expr::bvar(*idx)
            .map_err(|error| NormalizeError::TooManyBoundVars { range: error.range }),
        ExprNode::FVar { id } => Ok(Expr::fvar(id.clone())),
        ExprNode::MVar { id } => Ok(Expr::mvar(id.clone())),
        ExprNode::Sort { level } => Ok(Expr::sort(normalize_level(level, param_map, budget)?)),
        ExprNode::Const { name, levels } => {
            let mut normalized_levels = Vec::with_capacity(levels.len());
            for level in levels {
                normalized_levels.push(normalize_level(level, param_map, budget)?);
            }
            Ok(Expr::const_(name.clone(), normalized_levels))
        }
        ExprNode::App { f, a } => {
            let f = normalize_expr_inner(f, param_map, budget)?;
            let a = normalize_expr_inner(a, param_map, budget)?;
            Ok(Expr::app(f, a))
        }
        ExprNode::Lam {
            binder_type,
            body,
            binder_info,
            ..
        } => {
            let binder_type = normalize_expr_inner(binder_type, param_map, budget)?;
            let body = normalize_expr_inner(body, param_map, budget)?;
            Ok(Expr::lam(
                Name::anonymous(),
                binder_type,
                body,
                *binder_info,
            ))
        }
        ExprNode::ForallE {
            binder_type,
            body,
            binder_info,
            ..
        } => {
            let binder_type = normalize_expr_inner(binder_type, param_map, budget)?;
            let body = normalize_expr_inner(body, param_map, budget)?;
            Ok(Expr::forall_e(
                Name::anonymous(),
                binder_type,
                body,
                *binder_info,
            ))
        }
        ExprNode::LetE {
            type_,
            value,
            body,
            non_dep,
            ..
        } => {
            let type_ = normalize_expr_inner(type_, param_map, budget)?;
            let value = normalize_expr_inner(value, param_map, budget)?;
            let body = normalize_expr_inner(body, param_map, budget)?;
            Ok(Expr::let_e(Name::anonymous(), type_, value, body, *non_dep))
        }
        ExprNode::Lit { literal } => Ok(Expr::lit(literal.clone())),
        ExprNode::Proj {
            struct_name,
            idx,
            expr: inner,
        } => {
            let inner = normalize_expr_inner(inner, param_map, budget)?;
            Ok(Expr::proj(struct_name.clone(), *idx, inner))
        }
    }
}

fn binder_info_str(info: BinderInfo) -> &'static str {
    match info {
        BinderInfo::Default => "Default",
        BinderInfo::Implicit => "Implicit",
        BinderInfo::StrictImplicit => "StrictImplicit",
        BinderInfo::InstImplicit => "InstImplicit",
    }
}

fn level_sketch(level: &Level) -> String {
    match level.view() {
        LevelView::Zero => "0".to_owned(),
        LevelView::Param(name) => name.to_display_string(),
        LevelView::MVar(id) => format!("?{}", id.0.to_display_string()),
        LevelView::Succ(inner) => format!("succ({})", level_sketch(inner)),
        LevelView::Max(a, b) => format!("max({},{})", level_sketch(a), level_sketch(b)),
        LevelView::IMax(a, b) => format!("imax({},{})", level_sketch(a), level_sketch(b)),
    }
}

fn expr_head_sketch(expr: &Expr) -> String {
    match expr.node() {
        ExprNode::BVar { idx } => format!("#{idx}"),
        ExprNode::FVar { id } => format!("fvar({})", id.0.to_display_string()),
        ExprNode::MVar { id } => format!("?{}", id.0.to_display_string()),
        ExprNode::Sort { level } => format!("Sort({})", level_sketch(level)),
        ExprNode::Const { name, levels } => {
            if levels.is_empty() {
                format!("Const({})", name.to_display_string())
            } else {
                let lvls: Vec<String> = levels.iter().map(level_sketch).collect();
                format!("Const({}@{{{}}})", name.to_display_string(), lvls.join(","))
            }
        }
        ExprNode::App { .. } => "App".to_owned(),
        ExprNode::Lam { binder_info, .. } => format!("Lam({})", binder_info_str(*binder_info)),
        ExprNode::ForallE { binder_info, .. } => {
            format!("ForallE({})", binder_info_str(*binder_info))
        }
        ExprNode::LetE { non_dep, .. } => format!("LetE(non_dep={non_dep})"),
        ExprNode::Lit { literal } => format!("Lit({literal:?})"),
        ExprNode::MData { .. } => "MData".to_owned(),
        ExprNode::Proj {
            struct_name, idx, ..
        } => format!("Proj({}.{idx})", struct_name.to_display_string()),
    }
}

/// Locate the first structural difference between two already-normalized expressions.
pub fn first_expr_diff(native: &Expr, pin: &Expr) -> Option<String> {
    let mut budget = DEFAULT_DIFF_BUDGET;
    first_expr_diff_inner(native, pin, "root", &mut budget)
}

fn first_expr_diff_inner(
    native: &Expr,
    pin: &Expr,
    path: &str,
    budget: &mut usize,
) -> Option<String> {
    if native == pin {
        return None;
    }
    if *budget == 0 {
        return Some(format!("{path}: diff budget exhausted"));
    }
    *budget -= 1;
    match (native.node(), pin.node()) {
        (ExprNode::BVar { idx: a }, ExprNode::BVar { idx: b }) if a != b => {
            Some(format!("{path}: bvar #{a} vs #{b}"))
        }
        (ExprNode::Sort { level: a }, ExprNode::Sort { level: b }) if a != b => Some(format!(
            "{path}: sort level {} vs {}",
            level_sketch(a),
            level_sketch(b)
        )),
        (
            ExprNode::Const {
                name: a_name,
                levels: a_lvls,
            },
            ExprNode::Const {
                name: b_name,
                levels: b_lvls,
            },
        ) => {
            if a_name != b_name {
                return Some(format!(
                    "{path}: const {} vs {}",
                    a_name.to_display_string(),
                    b_name.to_display_string()
                ));
            }
            if a_lvls.len() != b_lvls.len() {
                return Some(format!(
                    "{path}: const {} level count {} vs {}",
                    a_name.to_display_string(),
                    a_lvls.len(),
                    b_lvls.len()
                ));
            }
            for (idx, (al, bl)) in a_lvls.iter().zip(b_lvls).enumerate() {
                if al != bl {
                    return Some(format!(
                        "{path}.levels[{idx}]: {} vs {}",
                        level_sketch(al),
                        level_sketch(bl)
                    ));
                }
            }
            None
        }
        (ExprNode::App { f: af, a: aa }, ExprNode::App { f: bf, a: ba }) => {
            first_expr_diff_inner(af, bf, &format!("{path}.fn"), budget)
                .or_else(|| first_expr_diff_inner(aa, ba, &format!("{path}.arg"), budget))
        }
        (
            ExprNode::ForallE {
                binder_type: at,
                body: ab,
                binder_info: ai,
                ..
            },
            ExprNode::ForallE {
                binder_type: bt,
                body: bb,
                binder_info: bi,
                ..
            },
        ) => {
            if ai != bi {
                return Some(format!(
                    "{path}.binder_info: {} vs {}",
                    binder_info_str(*ai),
                    binder_info_str(*bi)
                ));
            }
            first_expr_diff_inner(at, bt, &format!("{path}.domain"), budget)
                .or_else(|| first_expr_diff_inner(ab, bb, &format!("{path}.body"), budget))
        }
        (
            ExprNode::Lam {
                binder_type: at,
                body: ab,
                binder_info: ai,
                ..
            },
            ExprNode::Lam {
                binder_type: bt,
                body: bb,
                binder_info: bi,
                ..
            },
        ) => {
            if ai != bi {
                return Some(format!(
                    "{path}.binder_info: {} vs {}",
                    binder_info_str(*ai),
                    binder_info_str(*bi)
                ));
            }
            first_expr_diff_inner(at, bt, &format!("{path}.domain"), budget)
                .or_else(|| first_expr_diff_inner(ab, bb, &format!("{path}.body"), budget))
        }
        (
            ExprNode::LetE {
                type_: at,
                value: av,
                body: ab,
                non_dep: an,
                ..
            },
            ExprNode::LetE {
                type_: bt,
                value: bv,
                body: bb,
                non_dep: bn,
                ..
            },
        ) => {
            if an != bn {
                return Some(format!("{path}.non_dep: {an} vs {bn}"));
            }
            first_expr_diff_inner(at, bt, &format!("{path}.type"), budget)
                .or_else(|| first_expr_diff_inner(av, bv, &format!("{path}.value"), budget))
                .or_else(|| first_expr_diff_inner(ab, bb, &format!("{path}.body"), budget))
        }
        (
            ExprNode::Proj {
                struct_name: a_s,
                idx: a_i,
                expr: a_e,
            },
            ExprNode::Proj {
                struct_name: b_s,
                idx: b_i,
                expr: b_e,
            },
        ) => {
            if a_s != b_s {
                return Some(format!(
                    "{path}.proj_struct: {} vs {}",
                    a_s.to_display_string(),
                    b_s.to_display_string()
                ));
            }
            if a_i != b_i {
                return Some(format!("{path}.proj_idx: {a_i} vs {b_i}"));
            }
            first_expr_diff_inner(a_e, b_e, &format!("{path}.proj_expr"), budget)
        }
        _ => Some(format!(
            "{path}: {} vs {}",
            expr_head_sketch(native),
            expr_head_sketch(pin)
        )),
    }
}

fn reducibility_hint_class(hints: ReducibilityHints) -> &'static str {
    match hints {
        ReducibilityHints::Opaque => "opaque",
        ReducibilityHints::Abbrev => "abbrev",
        ReducibilityHints::Regular(_) => "regular",
    }
}

fn safety_str(safety: DefinitionSafety) -> &'static str {
    match safety {
        DefinitionSafety::Unsafe => "unsafe",
        DefinitionSafety::Safe => "safe",
        DefinitionSafety::Partial => "partial",
    }
}

/// One T2 interface difference on a declaration present in both environments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclarationT2Diff {
    pub name: Name,
    pub role: DeclarationRole,
    pub reasons: Vec<String>,
}

/// One T3 implementation/proof-body difference on a declaration present in both environments.
/// Explicitly separated from T2 interface identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclarationT3Diff {
    pub name: Name,
    pub role: DeclarationRole,
    pub detail: String,
}

/// Complete declaration-level T2 and T3 comparison of one module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleComparison {
    pub module: Name,
    pub normalizer: T2NormalizerId,
    pub native_declaration_count: usize,
    pub pin_declaration_count: usize,
    pub shared_count: usize,
    pub pin_only_primary: Vec<Name>,
    pub pin_only_auxiliary: Vec<(Name, AuxClass)>,
    pub native_only_primary: Vec<Name>,
    pub native_only_auxiliary: Vec<(Name, AuxClass)>,
    pub t2_diffs: Vec<DeclarationT2Diff>,
    pub t3_diffs: Vec<DeclarationT3Diff>,
    pub primary_t2_identical: bool,
    pub full_t2_identical: bool,
    pub t3_identical: bool,
    pub first_difference: Option<String>,
}

impl ModuleComparison {
    /// Coarse machine-readable divergence class for ledger tracking.
    pub fn diff_class(&self) -> &'static str {
        if self.full_t2_identical {
            return "identical";
        }
        if !self.pin_only_primary.is_empty() || !self.native_only_primary.is_empty() {
            return "primary_name_set";
        }
        if self
            .t2_diffs
            .iter()
            .any(|diff| matches!(diff.role, DeclarationRole::Primary))
        {
            return "primary_t2_interface";
        }
        if !self.pin_only_auxiliary.is_empty() || !self.native_only_auxiliary.is_empty() {
            return "auxiliary_name_set";
        }
        "auxiliary_t2_interface"
    }
}

/// Compare FrankenLean's checked module snapshot against the pinned Reference's
/// `.olean` snapshot at both T2 (interface/names/attributes) and T3 (values/proofs).
pub fn compare_modules(
    native: &ModuleSnapshot,
    pin: &ModuleSnapshot,
    normalizer: T2NormalizerId,
) -> Result<ModuleComparison, NormalizeError> {
    let mut pin_only_primary = Vec::new();
    let mut pin_only_auxiliary = Vec::new();
    let mut native_only_primary = Vec::new();
    let mut native_only_auxiliary = Vec::new();
    let mut shared_names = Vec::new();

    for name in pin.constants.keys() {
        if native.constants.contains_key(name) {
            shared_names.push(name.clone());
        } else {
            match classify_declaration_name(name) {
                DeclarationRole::Primary => pin_only_primary.push(name.clone()),
                DeclarationRole::Auxiliary(class) => pin_only_auxiliary.push((name.clone(), class)),
            }
        }
    }
    for name in native.constants.keys() {
        if !pin.constants.contains_key(name) {
            match classify_declaration_name(name) {
                DeclarationRole::Primary => native_only_primary.push(name.clone()),
                DeclarationRole::Auxiliary(class) => {
                    native_only_auxiliary.push((name.clone(), class));
                }
            }
        }
    }

    let mut t2_diffs = Vec::new();
    let mut t3_diffs = Vec::new();

    for name in &shared_names {
        let native_info = &native.constants[name];
        let pin_info = &pin.constants[name];
        let role = classify_declaration_name(name);
        let mut reasons = Vec::new();

        if native_info.kind_name() != pin_info.kind_name() {
            reasons.push(format!(
                "kind: {} vs {}",
                native_info.kind_name(),
                pin_info.kind_name()
            ));
        }

        let native_base = native_info.constant_val();
        let pin_base = pin_info.constant_val();
        if native_base.level_params.len() != pin_base.level_params.len() {
            reasons.push(format!(
                "level_param_count: {} vs {}",
                native_base.level_params.len(),
                pin_base.level_params.len()
            ));
        }

        let native_type =
            normalize_expr(&native_base.type_, &native_base.level_params, normalizer)?;
        let pin_type = normalize_expr(&pin_base.type_, &pin_base.level_params, normalizer)?;
        if let Some(diff) = first_expr_diff(&native_type, &pin_type) {
            reasons.push(format!("type: {diff}"));
        }

        compare_kind_metadata(native_info, pin_info, &mut reasons);

        let empty_attrs = BTreeSet::new();
        let native_attrs = native.attributes.get(name).unwrap_or(&empty_attrs);
        let pin_attrs = pin.attributes.get(name).unwrap_or(&empty_attrs);
        if native_attrs != pin_attrs {
            let missing: Vec<&str> = pin_attrs
                .difference(native_attrs)
                .map(String::as_str)
                .collect();
            let extra: Vec<&str> = native_attrs
                .difference(pin_attrs)
                .map(String::as_str)
                .collect();
            reasons.push(format!(
                "attributes: missing_in_native={missing:?}, extra_in_native={extra:?}"
            ));
        }

        if !reasons.is_empty() {
            t2_diffs.push(DeclarationT2Diff {
                name: name.clone(),
                role,
                reasons,
            });
        }

        // T3 value/body comparison is strictly separated from T2 interface identity.
        if let Some(detail) = compare_t3_body(native_info, pin_info, normalizer)? {
            t3_diffs.push(DeclarationT3Diff {
                name: name.clone(),
                role,
                detail,
            });
        }
    }

    let primary_t2_diffs = t2_diffs
        .iter()
        .any(|diff| matches!(diff.role, DeclarationRole::Primary));
    let primary_t2_identical =
        pin_only_primary.is_empty() && native_only_primary.is_empty() && !primary_t2_diffs;
    let full_t2_identical = primary_t2_identical
        && pin_only_auxiliary.is_empty()
        && native_only_auxiliary.is_empty()
        && t2_diffs.is_empty();
    let t3_identical = full_t2_identical && t3_diffs.is_empty();

    let first_difference = if let Some(name) = pin_only_primary.first() {
        Some(format!("pin_only_primary: {}", name.to_display_string()))
    } else if let Some(name) = native_only_primary.first() {
        Some(format!("native_only_primary: {}", name.to_display_string()))
    } else if let Some(diff) = t2_diffs
        .iter()
        .find(|d| matches!(d.role, DeclarationRole::Primary))
    {
        Some(format!(
            "primary_t2_diff {}: {}",
            diff.name.to_display_string(),
            diff.reasons.join("; ")
        ))
    } else if let Some((name, class)) = pin_only_auxiliary.first() {
        Some(format!(
            "pin_only_aux({}): {}",
            class.as_str(),
            name.to_display_string()
        ))
    } else if let Some((name, class)) = native_only_auxiliary.first() {
        Some(format!(
            "native_only_aux({}): {}",
            class.as_str(),
            name.to_display_string()
        ))
    } else {
        t2_diffs.first().map(|diff| {
            format!(
                "aux_t2_diff {}: {}",
                diff.name.to_display_string(),
                diff.reasons.join("; ")
            )
        })
    };

    Ok(ModuleComparison {
        module: native.module.clone(),
        normalizer,
        native_declaration_count: native.constants.len(),
        pin_declaration_count: pin.constants.len(),
        shared_count: shared_names.len(),
        pin_only_primary,
        pin_only_auxiliary,
        native_only_primary,
        native_only_auxiliary,
        t2_diffs,
        t3_diffs,
        primary_t2_identical,
        full_t2_identical,
        t3_identical,
        first_difference,
    })
}

fn compare_kind_metadata(native: &ConstantInfo, pin: &ConstantInfo, reasons: &mut Vec<String>) {
    match (native, pin) {
        (ConstantInfo::Axiom(a), ConstantInfo::Axiom(b)) => {
            if a.is_unsafe != b.is_unsafe {
                reasons.push(format!(
                    "axiom.is_unsafe: {} vs {}",
                    a.is_unsafe, b.is_unsafe
                ));
            }
        }
        (ConstantInfo::Defn(a), ConstantInfo::Defn(b)) => {
            if a.safety != b.safety {
                reasons.push(format!(
                    "defn.safety: {} vs {}",
                    safety_str(a.safety),
                    safety_str(b.safety)
                ));
            }
            if reducibility_hint_class(a.hints) != reducibility_hint_class(b.hints) {
                reasons.push(format!(
                    "defn.hints: {} vs {}",
                    reducibility_hint_class(a.hints),
                    reducibility_hint_class(b.hints)
                ));
            }
        }
        (ConstantInfo::Opaque(a), ConstantInfo::Opaque(b)) => {
            if a.is_unsafe != b.is_unsafe {
                reasons.push(format!(
                    "opaque.is_unsafe: {} vs {}",
                    a.is_unsafe, b.is_unsafe
                ));
            }
        }
        (ConstantInfo::Induct(a), ConstantInfo::Induct(b)) => {
            if a.num_params != b.num_params {
                reasons.push(format!(
                    "induct.num_params: {} vs {}",
                    a.num_params, b.num_params
                ));
            }
            if a.num_indices != b.num_indices {
                reasons.push(format!(
                    "induct.num_indices: {} vs {}",
                    a.num_indices, b.num_indices
                ));
            }
            if a.ctors != b.ctors {
                reasons.push(format!(
                    "induct.ctors: {} vs {}",
                    a.ctors.len(),
                    b.ctors.len()
                ));
            }
            if a.is_rec != b.is_rec {
                reasons.push(format!("induct.is_rec: {} vs {}", a.is_rec, b.is_rec));
            }
            if a.is_unsafe != b.is_unsafe {
                reasons.push(format!(
                    "induct.is_unsafe: {} vs {}",
                    a.is_unsafe, b.is_unsafe
                ));
            }
            if a.is_reflexive != b.is_reflexive {
                reasons.push(format!(
                    "induct.is_reflexive: {} vs {}",
                    a.is_reflexive, b.is_reflexive
                ));
            }
        }
        (ConstantInfo::Ctor(a), ConstantInfo::Ctor(b)) => {
            if a.induct != b.induct {
                reasons.push(format!(
                    "ctor.induct: {} vs {}",
                    a.induct.to_display_string(),
                    b.induct.to_display_string()
                ));
            }
            if a.cidx != b.cidx {
                reasons.push(format!("ctor.cidx: {} vs {}", a.cidx, b.cidx));
            }
            if a.num_params != b.num_params {
                reasons.push(format!(
                    "ctor.num_params: {} vs {}",
                    a.num_params, b.num_params
                ));
            }
            if a.num_fields != b.num_fields {
                reasons.push(format!(
                    "ctor.num_fields: {} vs {}",
                    a.num_fields, b.num_fields
                ));
            }
            if a.is_unsafe != b.is_unsafe {
                reasons.push(format!(
                    "ctor.is_unsafe: {} vs {}",
                    a.is_unsafe, b.is_unsafe
                ));
            }
        }
        (ConstantInfo::Rec(a), ConstantInfo::Rec(b)) => {
            if a.num_params != b.num_params {
                reasons.push(format!(
                    "rec.num_params: {} vs {}",
                    a.num_params, b.num_params
                ));
            }
            if a.num_indices != b.num_indices {
                reasons.push(format!(
                    "rec.num_indices: {} vs {}",
                    a.num_indices, b.num_indices
                ));
            }
            if a.num_motives != b.num_motives {
                reasons.push(format!(
                    "rec.num_motives: {} vs {}",
                    a.num_motives, b.num_motives
                ));
            }
            if a.num_minors != b.num_minors {
                reasons.push(format!(
                    "rec.num_minors: {} vs {}",
                    a.num_minors, b.num_minors
                ));
            }
            if a.k != b.k {
                reasons.push(format!("rec.k: {} vs {}", a.k, b.k));
            }
            if a.is_unsafe != b.is_unsafe {
                reasons.push(format!("rec.is_unsafe: {} vs {}", a.is_unsafe, b.is_unsafe));
            }
        }
        (ConstantInfo::Quot(a), ConstantInfo::Quot(b)) if a.kind != b.kind => {
            reasons.push(format!("quot.kind: {:?} vs {:?}", a.kind, b.kind));
        }
        _ => {}
    }
}

fn compare_t3_body(
    native: &ConstantInfo,
    pin: &ConstantInfo,
    normalizer: T2NormalizerId,
) -> Result<Option<String>, NormalizeError> {
    match (native, pin) {
        (ConstantInfo::Defn(a), ConstantInfo::Defn(b)) => {
            let av = normalize_expr(&a.value, &a.base.level_params, normalizer)?;
            let bv = normalize_expr(&b.value, &b.base.level_params, normalizer)?;
            Ok(first_expr_diff(&av, &bv).map(|diff| format!("defn.value: {diff}")))
        }
        (ConstantInfo::Thm(a), ConstantInfo::Thm(b)) => {
            let av = normalize_expr(&a.value, &a.base.level_params, normalizer)?;
            let bv = normalize_expr(&b.value, &b.base.level_params, normalizer)?;
            Ok(first_expr_diff(&av, &bv).map(|diff| format!("thm.proof: {diff}")))
        }
        (ConstantInfo::Opaque(a), ConstantInfo::Opaque(b)) => {
            let av = normalize_expr(&a.value, &a.base.level_params, normalizer)?;
            let bv = normalize_expr(&b.value, &b.base.level_params, normalizer)?;
            Ok(first_expr_diff(&av, &bv).map(|diff| format!("opaque.value: {diff}")))
        }
        (ConstantInfo::Rec(a), ConstantInfo::Rec(b)) => {
            if a.rules.len() != b.rules.len() {
                return Ok(Some(format!(
                    "rec.rules count: {} vs {}",
                    a.rules.len(),
                    b.rules.len()
                )));
            }
            for (idx, (ar, br)) in a.rules.iter().zip(&b.rules).enumerate() {
                if ar.ctor != br.ctor || ar.nfields != br.nfields {
                    return Ok(Some(format!(
                        "rec.rules[{idx}]: ({}, {}) vs ({}, {})",
                        ar.ctor.to_display_string(),
                        ar.nfields,
                        br.ctor.to_display_string(),
                        br.nfields
                    )));
                }
                let av = normalize_expr(&ar.rhs, &a.base.level_params, normalizer)?;
                let bv = normalize_expr(&br.rhs, &b.base.level_params, normalizer)?;
                if let Some(diff) = first_expr_diff(&av, &bv) {
                    return Ok(Some(format!("rec.rules[{idx}].rhs: {diff}")));
                }
            }
            Ok(None)
        }
        _ => Ok(None),
    }
}

/// Verdict classification for one side (FL-INV-07: inconclusive is distinct from reject).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SideVerdict {
    Accept,
    Reject,
    Inconclusive,
}

impl SideVerdict {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accept => "accept",
            Self::Reject => "reject",
            Self::Inconclusive => "inconclusive",
        }
    }

    pub fn parse(text: &str) -> Option<Self> {
        match text {
            "accept" => Some(Self::Accept),
            "reject" => Some(Self::Reject),
            "inconclusive" => Some(Self::Inconclusive),
            _ => None,
        }
    }
}

/// T2/T3 status cell for a single file row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TierStatus {
    Identical,
    Diff,
    NotApplicable,
}

impl TierStatus {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Identical => "identical",
            Self::Diff => "diff",
            Self::NotApplicable => "n/a",
        }
    }

    pub fn parse(text: &str) -> Option<Self> {
        match text {
            "identical" => Some(Self::Identical),
            "diff" => Some(Self::Diff),
            "n/a" => Some(Self::NotApplicable),
            _ => None,
        }
    }
}

/// Observed T2/T3 differential row for one source file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObservedFileRow {
    pub family: String,
    pub file: String,
    pub source_digest: String,
    pub pin_tag: String,
    pub pin_commit: String,
    pub binary_digest: String,
    pub normalizer: String,
    pub pin_verdict: SideVerdict,
    pub native_verdict: SideVerdict,
    pub primary_t2: TierStatus,
    pub full_t2: TierStatus,
    pub t3: TierStatus,
    pub diff_class: String,
    pub first_difference: String,
    pub native_decls: usize,
    pub pin_decls: usize,
}

impl ObservedFileRow {
    /// Render as one canonical JSONL line for crash/resume checkpoints and structured logs.
    pub fn to_jsonl_line(&self) -> String {
        format!(
            "{{\"schema\":{},\"family\":{},\"file\":{},\"source_digest\":{},\"pin_tag\":{},\"pin_commit\":{},\"binary_digest\":{},\"normalizer\":{},\"pin_verdict\":{},\"native_verdict\":{},\"primary_t2\":{},\"full_t2\":{},\"t3\":{},\"diff_class\":{},\"first_difference\":{},\"native_decls\":{},\"pin_decls\":{}}}",
            json_string(CHECKPOINT_SCHEMA),
            json_string(&self.family),
            json_string(&self.file),
            json_string(&self.source_digest),
            json_string(&self.pin_tag),
            json_string(&self.pin_commit),
            json_string(&self.binary_digest),
            json_string(&self.normalizer),
            json_string(self.pin_verdict.as_str()),
            json_string(self.native_verdict.as_str()),
            json_string(self.primary_t2.as_str()),
            json_string(self.full_t2.as_str()),
            json_string(self.t3.as_str()),
            json_string(&self.diff_class),
            json_string(&self.first_difference),
            self.native_decls,
            self.pin_decls,
        )
    }

    /// Parse one canonical JSONL line back; returns `None` on truncation or corruption.
    pub fn from_jsonl_line(line: &str) -> Option<Self> {
        let trimmed = line.trim();
        if !trimmed.starts_with('{') || !trimmed.ends_with('}') {
            return None;
        }
        if json_string_field(trimmed, "schema").as_deref() != Some(CHECKPOINT_SCHEMA) {
            return None;
        }
        Some(Self {
            family: json_string_field(trimmed, "family")?,
            file: json_string_field(trimmed, "file")?,
            source_digest: json_string_field(trimmed, "source_digest")?,
            pin_tag: json_string_field(trimmed, "pin_tag")?,
            pin_commit: json_string_field(trimmed, "pin_commit")?,
            binary_digest: json_string_field(trimmed, "binary_digest")?,
            normalizer: json_string_field(trimmed, "normalizer")?,
            pin_verdict: SideVerdict::parse(&json_string_field(trimmed, "pin_verdict")?)?,
            native_verdict: SideVerdict::parse(&json_string_field(trimmed, "native_verdict")?)?,
            primary_t2: TierStatus::parse(&json_string_field(trimmed, "primary_t2")?)?,
            full_t2: TierStatus::parse(&json_string_field(trimmed, "full_t2")?)?,
            t3: TierStatus::parse(&json_string_field(trimmed, "t3")?)?,
            diff_class: json_string_field(trimmed, "diff_class")?,
            first_difference: json_string_field(trimmed, "first_difference")?,
            native_decls: json_usize_field(trimmed, "native_decls")?,
            pin_decls: json_usize_field(trimmed, "pin_decls")?,
        })
    }

    /// Whether this checkpoint entry is still valid for the exact current inputs.
    pub fn matches_identity(
        &self,
        source_digest: &str,
        pin_tag: &str,
        pin_commit: &str,
        binary_digest: &str,
        normalizer: &str,
    ) -> bool {
        self.source_digest == source_digest
            && self.pin_tag == pin_tag
            && self.pin_commit == pin_commit
            && self.binary_digest == binary_digest
            && self.normalizer == normalizer
    }
}

fn json_string_field(line: &str, key: &str) -> Option<String> {
    let needle = format!("\"{key}\":\"");
    let start = line.find(&needle)? + needle.len();
    let mut out = String::new();
    let mut chars = line[start..].chars();
    while let Some(ch) = chars.next() {
        match ch {
            '"' => return Some(out),
            '\\' => match chars.next()? {
                '"' => out.push('"'),
                '\\' => out.push('\\'),
                '/' => out.push('/'),
                'n' => out.push('\n'),
                't' => out.push('\t'),
                'r' => out.push('\r'),
                'b' => out.push('\u{8}'),
                'f' => out.push('\u{c}'),
                'u' => {
                    let code: String = chars.by_ref().take(4).collect();
                    let val = u32::from_str_radix(&code, 16).ok()?;
                    out.push(char::from_u32(val)?);
                }
                other => out.push(other),
            },
            other => out.push(other),
        }
    }
    None
}

fn json_usize_field(line: &str, key: &str) -> Option<usize> {
    let needle = format!("\"{key}\":");
    let start = line.find(&needle)? + needle.len();
    let digits: String = line[start..]
        .chars()
        .take_while(char::is_ascii_digit)
        .collect();
    if digits.is_empty() {
        return None;
    }
    digits.parse().ok()
}

/// Crash/resume JSONL checkpoint journal for file-scale T2 differential runs.
#[derive(Debug, Clone)]
pub struct CheckpointJournal {
    path: PathBuf,
    entries: BTreeMap<String, ObservedFileRow>,
    corrupted_lines: usize,
}

impl CheckpointJournal {
    /// Load an existing JSONL checkpoint if present; truncated or malformed lines
    /// are counted and ignored so interrupted runs resume cleanly.
    pub fn load(path: impl Into<PathBuf>) -> Result<Self, String> {
        let path = path.into();
        let mut entries = BTreeMap::new();
        let mut corrupted_lines = 0usize;
        if path.is_file() {
            let text = fs::read_to_string(&path)
                .map_err(|error| format!("cannot read checkpoint {}: {error}", path.display()))?;
            for line in text.lines() {
                if line.trim().is_empty() {
                    continue;
                }
                match ObservedFileRow::from_jsonl_line(line) {
                    Some(row) => {
                        entries.insert(row.file.clone(), row);
                    }
                    None => {
                        corrupted_lines += 1;
                    }
                }
            }
        }
        Ok(Self {
            path,
            entries,
            corrupted_lines,
        })
    }

    pub fn corrupted_lines(&self) -> usize {
        self.corrupted_lines
    }

    /// Look up a previously completed entry matching the exact current identity.
    pub fn reusable(
        &self,
        file: &str,
        source_digest: &str,
        pin_tag: &str,
        pin_commit: &str,
        binary_digest: &str,
        normalizer: &str,
    ) -> Option<&ObservedFileRow> {
        self.entries.get(file).filter(|row| {
            row.matches_identity(
                source_digest,
                pin_tag,
                pin_commit,
                binary_digest,
                normalizer,
            )
        })
    }

    /// Append one completed observation durably to the JSONL checkpoint.
    pub fn record(&mut self, row: ObservedFileRow) -> Result<(), String> {
        if let Some(parent) = self.path.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| format!("create checkpoint dir {}: {error}", parent.display()))?;
        }
        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.path)
            .map_err(|error| format!("open checkpoint {}: {error}", self.path.display()))?;
        writeln!(file, "{}", row.to_jsonl_line())
            .map_err(|error| format!("write checkpoint {}: {error}", self.path.display()))?;
        file.flush()
            .map_err(|error| format!("flush checkpoint {}: {error}", self.path.display()))?;
        self.entries.insert(row.file.clone(), row);
        Ok(())
    }
}

/// One row of the checked-in T2 ratchet ledger.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct T2LedgerRow {
    pub family: String,
    pub file: String,
    pub pin_verdict: SideVerdict,
    pub native_verdict: SideVerdict,
    pub primary_t2: TierStatus,
    pub full_t2: TierStatus,
    pub t3: TierStatus,
    pub diff_class: String,
    pub owner_or_note: String,
}

/// Checked-in T2 ratchet ledger with per-family nonzero floors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct T2RatchetLedger {
    pub pin_tag: String,
    pub normalizer_id: String,
    pub family_floors: BTreeMap<String, usize>,
    pub rows: BTreeMap<String, T2LedgerRow>,
}

/// Result of verifying live observations against a [`T2RatchetLedger`].
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct RatchetVerdict {
    pub problems: Vec<String>,
    pub improvements: Vec<String>,
}

impl RatchetVerdict {
    pub fn is_clean(&self) -> bool {
        self.problems.is_empty()
    }
}

impl T2RatchetLedger {
    pub fn parse(text: &str) -> Result<Self, String> {
        let mut pin_tag = String::new();
        let mut normalizer_id = String::new();
        let mut family_floors = BTreeMap::new();
        let mut rows = BTreeMap::new();

        for (index, line) in text.lines().enumerate() {
            let line_no = index + 1;
            let trimmed = line.trim();
            if trimmed.is_empty() {
                continue;
            }
            if let Some(rest) = trimmed.strip_prefix('#') {
                let rest = rest.trim();
                if let Some(val) = rest.strip_prefix("pin_tag=") {
                    pin_tag = val.trim().to_owned();
                } else if let Some(val) = rest.strip_prefix("normalizer=") {
                    normalizer_id = val.trim().to_owned();
                } else if let Some(val) = rest.strip_prefix("floor ") {
                    let parts: Vec<&str> = val.split_whitespace().collect();
                    if parts.len() != 2 {
                        return Err(format!("ledger:{line_no}: malformed floor directive"));
                    }
                    let floor = parts[1]
                        .parse::<usize>()
                        .map_err(|_| format!("ledger:{line_no}: invalid floor count"))?;
                    if floor == 0 {
                        return Err(format!(
                            "ledger:{line_no}: family floor for {} must be nonzero",
                            parts[0]
                        ));
                    }
                    family_floors.insert(parts[0].to_owned(), floor);
                }
                continue;
            }
            let fields: Vec<&str> = line.split('\t').collect();
            if fields.len() != 9 {
                return Err(format!(
                    "ledger:{line_no}: expected 9 tab-separated fields, found {}",
                    fields.len()
                ));
            }
            let pin_verdict = SideVerdict::parse(fields[2])
                .ok_or_else(|| format!("ledger:{line_no}: invalid pin_verdict {:?}", fields[2]))?;
            let native_verdict = SideVerdict::parse(fields[3]).ok_or_else(|| {
                format!("ledger:{line_no}: invalid native_verdict {:?}", fields[3])
            })?;
            let primary_t2 = TierStatus::parse(fields[4])
                .ok_or_else(|| format!("ledger:{line_no}: invalid primary_t2 {:?}", fields[4]))?;
            let full_t2 = TierStatus::parse(fields[5])
                .ok_or_else(|| format!("ledger:{line_no}: invalid full_t2 {:?}", fields[5]))?;
            let t3 = TierStatus::parse(fields[6])
                .ok_or_else(|| format!("ledger:{line_no}: invalid t3 {:?}", fields[6]))?;
            let row = T2LedgerRow {
                family: fields[0].to_owned(),
                file: fields[1].to_owned(),
                pin_verdict,
                native_verdict,
                primary_t2,
                full_t2,
                t3,
                diff_class: fields[7].to_owned(),
                owner_or_note: fields[8].to_owned(),
            };
            if rows.insert(row.file.clone(), row).is_some() {
                return Err(format!("ledger:{line_no}: duplicate row for {}", fields[1]));
            }
        }
        if pin_tag.is_empty() || normalizer_id.is_empty() {
            return Err("ledger missing required pin_tag or normalizer header".to_owned());
        }
        if family_floors.is_empty() {
            return Err("ledger must declare nonzero family floors".to_owned());
        }
        Ok(Self {
            pin_tag,
            normalizer_id,
            family_floors,
            rows,
        })
    }

    pub fn render(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("# schema={LEDGER_SCHEMA}\n"));
        out.push_str(&format!("# pin_tag={}\n", self.pin_tag));
        out.push_str(&format!("# normalizer={}\n", self.normalizer_id));
        for (family, floor) in &self.family_floors {
            out.push_str(&format!("# floor {family} {floor}\n"));
        }
        out.push_str("# family\tfile\tpin_verdict\tnative_verdict\tprimary_t2\tfull_t2\tt3\tdiff_class\towner_or_note\n");
        for row in self.rows.values() {
            out.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                row.family,
                row.file,
                row.pin_verdict.as_str(),
                row.native_verdict.as_str(),
                row.primary_t2.as_str(),
                row.full_t2.as_str(),
                row.t3.as_str(),
                row.diff_class,
                row.owner_or_note,
            ));
        }
        out
    }

    /// Enforce all T2 ratchet laws against live observed rows:
    /// 1. Every declared family meets its nonzero floor.
    /// 2. Zero false accepts (`pin=reject, native=accept`).
    /// 3. Zero T2 regressions (once `full_t2=identical` or `primary_t2=identical`,
    ///    regressing fails; losing acceptance fails).
    /// 4. Every residual non-identical row has a non-empty `diff_class` and `owner_or_note`.
    /// 5. Exact population bijection between observed files and ledger rows.
    pub fn verify(&self, observed: &[ObservedFileRow]) -> RatchetVerdict {
        let mut verdict = RatchetVerdict::default();
        let mut counts_by_family: BTreeMap<&str, usize> = BTreeMap::new();
        let mut seen = BTreeSet::new();

        for row in observed {
            if !seen.insert(row.file.as_str()) {
                verdict
                    .problems
                    .push(format!("duplicate observed file {}", row.file));
                continue;
            }
            *counts_by_family.entry(row.family.as_str()).or_default() += 1;

            // Constitutional compatibility law: never falsely accept what the Reference rejects.
            if row.pin_verdict == SideVerdict::Reject && row.native_verdict == SideVerdict::Accept {
                verdict.problems.push(format!(
                    "FALSE ACCEPT: {} rejected by pinned Reference but accepted by FrankenLean",
                    row.file
                ));
            }
            if row.pin_verdict == SideVerdict::Inconclusive
                || row.native_verdict == SideVerdict::Inconclusive
            {
                verdict.problems.push(format!(
                    "INCONCLUSIVE: {} pin={} native={} ({})",
                    row.file,
                    row.pin_verdict.as_str(),
                    row.native_verdict.as_str(),
                    row.first_difference
                ));
                continue;
            }

            let Some(expected) = self.rows.get(&row.file) else {
                verdict.problems.push(format!(
                    "unrecorded file {} (family {}); update ledger deliberately",
                    row.file, row.family
                ));
                continue;
            };
            if expected.family != row.family {
                verdict.problems.push(format!(
                    "{}: family drifted {} -> {}",
                    row.file, expected.family, row.family
                ));
            }
            if expected.pin_verdict != row.pin_verdict {
                verdict.problems.push(format!(
                    "{}: pinned Reference verdict drifted {} -> {}",
                    row.file,
                    expected.pin_verdict.as_str(),
                    row.pin_verdict.as_str()
                ));
            }
            if expected.native_verdict == SideVerdict::Accept
                && row.native_verdict != SideVerdict::Accept
            {
                verdict.problems.push(format!(
                    "REGRESSION (acceptance): {} was accept, now {}",
                    row.file,
                    row.native_verdict.as_str()
                ));
            }
            if expected.primary_t2 == TierStatus::Identical
                && row.primary_t2 != TierStatus::Identical
            {
                verdict.problems.push(format!(
                    "REGRESSION (primary T2): {} was identical, now {} ({})",
                    row.file,
                    row.primary_t2.as_str(),
                    row.first_difference
                ));
            }
            if expected.full_t2 == TierStatus::Identical && row.full_t2 != TierStatus::Identical {
                verdict.problems.push(format!(
                    "REGRESSION (full T2): {} was identical, now {} ({})",
                    row.file,
                    row.full_t2.as_str(),
                    row.first_difference
                ));
            }

            if row.full_t2 != TierStatus::Identical
                && row.pin_verdict == SideVerdict::Accept
                && (expected.diff_class.trim().is_empty()
                    || expected.owner_or_note.trim().is_empty())
            {
                verdict.problems.push(format!(
                    "UNOWNED RESIDUAL: {} has non-identical status without diff_class and owner_or_note",
                    row.file
                ));
            }

            if expected.full_t2 != TierStatus::Identical && row.full_t2 == TierStatus::Identical {
                verdict
                    .improvements
                    .push(format!("IMPROVED (full T2): {}", row.file));
            } else if expected.primary_t2 != TierStatus::Identical
                && row.primary_t2 == TierStatus::Identical
            {
                verdict
                    .improvements
                    .push(format!("IMPROVED (primary T2): {}", row.file));
            } else if expected.native_verdict != SideVerdict::Accept
                && row.native_verdict == SideVerdict::Accept
                && row.pin_verdict == SideVerdict::Accept
            {
                verdict
                    .improvements
                    .push(format!("IMPROVED (accepted): {}", row.file));
            }
        }

        for file in self.rows.keys() {
            if !seen.contains(file.as_str()) {
                verdict.problems.push(format!(
                    "missing observed file for ledger row {file} (population cannot shrink silently)"
                ));
            }
        }

        for (family, floor) in &self.family_floors {
            let count = counts_by_family.get(family.as_str()).copied().unwrap_or(0);
            if count < *floor {
                verdict.problems.push(format!(
                    "family {family} observed {count} files, below declared nonzero floor {floor}"
                ));
            }
        }

        verdict
    }
}
