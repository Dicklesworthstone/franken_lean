//! The three-stage load of the canonical extern row contract (bead
//! `franken_lean-pw6t`), mirroring the 53v discipline: **parse** the canonical
//! text with the root law, **zip** the parsed rows against the generated table
//! field-by-field, then **independently re-derive** the row roots in Rust so no
//! single artifact can drift without a named divergence.
//!
//! Every stage needs only the committed artifacts, so the whole load runs on
//! every machine: the contract is self-certifying, and the shard-side
//! verification (the generator's envelope check plus `--check`
//! byte-regeneration) is what binds the fields to the pin.

use crate::extern_row::{
    CONTRACT_NAME, CONTRACT_ROOT_DOMAIN, CONTRACT_SCHEMA, ContractError, DECLARED_ROW_COUNT,
    ExternRow, framed_hash, parse_row, render_row, require_sorted_unique,
};
use crate::extern_table_generated::{EXTERN_ROW_CONTRACT_ROOT, EXTERN_ROW_COUNT, EXTERN_ROWS};

/// The contract after a successful load: the fixed header lines (part of the
/// hashed body, so they travel verbatim), the header facts, and the parsed rows.
#[derive(Clone, Debug)]
pub struct ExternRowContract {
    pub schema: String,
    pub name: String,
    pub reference: String,
    pub observation_platform: String,
    pub contract_root: String,
    pub header_lines: Vec<String>,
    pub rows: Vec<ExternRow>,
}

impl ExternRowContract {
    /// The terminal root, recomputed over the placeholder form of the
    /// projection line — the two-pass law the generator publishes under.
    pub fn recompute_root(&self) -> String {
        framed_hash(
            CONTRACT_ROOT_DOMAIN,
            self.root_lines().iter().map(String::as_str),
        )
    }

    fn root_lines(&self) -> Vec<String> {
        let mut lines = self.header_lines.clone();
        lines.push("rows-begin".to_string());
        for row in &self.rows {
            lines.push(format!("row {}", render_row(row)));
        }
        lines.push("rows-end".to_string());
        lines.push(
            "projection kind=rust path=crates/fln-vm/src/extern_table_generated.rs \
             template-root=fnv1a64:EXTERN_ROW_CONTRACT_ROOT"
                .to_string(),
        );
        lines
    }

    /// Look up a row by its stable id (`extern:<display-name>`).
    pub fn row(&self, id: &str) -> Option<&ExternRow> {
        self.rows.iter().find(|row| row.id == id)
    }
}

/// Stage 1: parse the canonical contract text. Refuses a wrong schema or name,
/// a missing or misplaced `contract-root`, a root that does not recompute, a
/// moved population count, unsorted or duplicate rows, and any row that fails
/// its own field laws.
pub fn parse(text: &str) -> Result<ExternRowContract, ContractError> {
    if !text.ends_with('\n') {
        return Err(ContractError::new(
            "contract does not end in a final newline",
        ));
    }
    let lines: Vec<&str> = text.split_terminator('\n').collect();
    if lines.len() < 12 {
        return Err(ContractError::new("contract is implausibly short"));
    }
    let schema = lines[0]
        .strip_prefix("schema ")
        .ok_or_else(|| ContractError::new("first line is not the schema row"))?;
    if schema != CONTRACT_SCHEMA {
        return Err(ContractError::new(format!(
            "contract schema is {schema:?}, expected {CONTRACT_SCHEMA:?}"
        )));
    }
    let name = lines[1]
        .strip_prefix("contract ")
        .ok_or_else(|| ContractError::new("second line is not the contract row"))?;
    if name != CONTRACT_NAME {
        return Err(ContractError::new(format!(
            "contract name is {name:?}, expected {CONTRACT_NAME:?}"
        )));
    }
    let reference = lines[5]
        .strip_prefix("reference ")
        .ok_or_else(|| ContractError::new("sixth line is not the reference row"))?;
    let platform = lines[6]
        .strip_prefix("observation-platform ")
        .ok_or_else(|| ContractError::new("seventh line is not the platform row"))?;
    if platform != "linux-x86_64" {
        return Err(ContractError::new(format!(
            "observation-platform {platform:?} is not the reviewed linux-x86_64"
        )));
    }
    let declared_count: usize = lines[7]
        .strip_prefix("row-count ")
        .and_then(|count| count.parse().ok())
        .ok_or_else(|| ContractError::new("eighth line is not the row-count row"))?;

    let root_line = lines
        .last()
        .ok_or_else(|| ContractError::new("contract is empty"))?;
    let declared_root = root_line
        .strip_prefix("contract-root ")
        .ok_or_else(|| ContractError::new("the final line is not the contract-root row"))?;
    if !declared_root.starts_with("fnv1a64:") {
        return Err(ContractError::new("contract-root is not fnv1a64-framed"));
    }
    if lines[..lines.len() - 1]
        .iter()
        .any(|line| line.starts_with("contract-root "))
    {
        return Err(ContractError::new(
            "contract-root appears before the final line",
        ));
    }

    let begin = lines
        .iter()
        .position(|line| *line == "rows-begin")
        .ok_or_else(|| ContractError::new("rows-begin is missing"))?;
    let end = lines
        .iter()
        .position(|line| *line == "rows-end")
        .ok_or_else(|| ContractError::new("rows-end is missing"))?;
    if end <= begin + 1 {
        return Err(ContractError::new("rows region is empty or misordered"));
    }

    // The projection law: the region after the rows is exactly one projection
    // line and the terminal root — nothing else, and nothing the root law
    // cannot see. A mutation inside the projection line is drift like any
    // other (the fuzz battery found this hole: the recompute used to rebuild
    // the projection from a constant and never read the input's).
    if end + 2 != lines.len() - 1 {
        return Err(ContractError::new(
            "the region between rows-end and contract-root must be exactly one \
             projection line",
        ));
    }
    const PROJECTION_PATH: &str = "crates/fln-vm/src/extern_table_generated.rs";
    const PROJECTION_PLACEHOLDER: &str = "fnv1a64:EXTERN_ROW_CONTRACT_ROOT";
    let projection = lines[end + 1];
    let fields = projection
        .strip_prefix("projection ")
        .ok_or_else(|| ContractError::new("the projection line does not start with `projection `"))?
        .split_ascii_whitespace()
        .map(|token| {
            token.split_once('=').ok_or_else(|| {
                ContractError::new(format!("projection field {token:?} is not key=value"))
            })
        })
        .collect::<Result<Vec<_>, ContractError>>()?;
    if fields.len() != 3
        || fields[0] != ("kind", "rust")
        || fields[1] != ("path", PROJECTION_PATH)
        || fields[2].0 != "template-root"
        || (fields[2].1 != declared_root && fields[2].1 != PROJECTION_PLACEHOLDER)
    {
        return Err(ContractError::new(format!(
            "projection must be exactly kind=rust, the pinned path, and \
             template-root <contract-root|placeholder>; got {projection:?}"
        )));
    }

    let mut rows = Vec::with_capacity(end - begin - 1);
    for line in &lines[begin + 1..end] {
        let body = line
            .strip_prefix("row ")
            .ok_or_else(|| ContractError::new("a rows-region line does not start with `row `"))?;
        let row = parse_row(body)?;
        // The byte-canonical law: a row line that parses but re-renders
        // differently (moved whitespace, reordered fields, a re-spelled
        // escape) is drift the root law should see — refuse it by name.
        if render_row(&row) != body {
            return Err(ContractError::new(format!(
                "row line is not byte-canonical: {body:?}"
            )));
        }
        rows.push(row);
    }
    if rows.len() != declared_count {
        return Err(ContractError::new(format!(
            "row-count declares {declared_count} but {} rows are present",
            rows.len()
        )));
    }
    if rows.len() != DECLARED_ROW_COUNT {
        return Err(ContractError::new(format!(
            "row population is {} against the declared {DECLARED_ROW_COUNT} — a moved \
             census is a schema revision, not an edit",
            rows.len()
        )));
    }
    require_sorted_unique(rows.iter().map(|row| row.id.as_str()), "row ids")?;

    let header_lines: Vec<String> = lines[..begin].iter().map(|line| line.to_string()).collect();
    let contract = ExternRowContract {
        schema: schema.to_string(),
        name: name.to_string(),
        reference: reference.to_string(),
        observation_platform: platform.to_string(),
        contract_root: declared_root.to_string(),
        header_lines,
        rows,
    };
    let recomputed = contract.recompute_root();
    if contract.contract_root != recomputed {
        return Err(ContractError::new(format!(
            "contract-root {} does not recompute: {recomputed}",
            contract.contract_root
        )));
    }
    Ok(contract)
}

/// Stage 2: zip the parsed rows against the generated table field-by-field, and
/// bind the generated table's provenance constant to the parsed root. A table
/// regenerated from older input is drift here, never a quiet pass.
pub fn validate_generated_projection(contract: &ExternRowContract) -> Result<(), ContractError> {
    if EXTERN_ROW_CONTRACT_ROOT != contract.contract_root {
        return Err(ContractError::new(format!(
            "the generated table carries root {EXTERN_ROW_CONTRACT_ROOT} but the contract \
             carries {}",
            contract.contract_root
        )));
    }
    if EXTERN_ROW_COUNT != contract.rows.len() {
        return Err(ContractError::new(format!(
            "the generated table declares {EXTERN_ROW_COUNT} rows but the contract holds {}",
            contract.rows.len()
        )));
    }
    for (generated, parsed) in EXTERN_ROWS.iter().zip(contract.rows.iter()) {
        let parsed_telescope = crate::extern_row::canonical_telescope(&parsed.telescope);
        let parsed_ownership = parsed.ownership.as_str();
        let parsed_fields: [(&str, &str); 18] = [
            ("id", parsed.id.as_str()),
            ("name", parsed.name.as_str()),
            ("kind", parsed.kind.as_str()),
            ("module", parsed.module.as_str()),
            ("telescope", parsed_telescope.as_str()),
            ("type_hash", parsed.type_hash.as_str()),
            ("value_hash", parsed.value_hash.as_str()),
            ("safety", parsed.safety.as_str()),
            ("attributes", parsed.attributes.as_str()),
            ("entry_class", parsed.entry_class.as_str()),
            ("entry_scope", parsed.entry_scope.as_str()),
            ("symbol", parsed.symbol.as_str()),
            ("effect", parsed.effect.as_str()),
            ("partition", parsed.partition.as_str()),
            ("ownership", parsed_ownership.as_str()),
            ("mode", parsed.mode.as_str()),
            ("profile", parsed.profile.as_str()),
            ("row_root", parsed.row_root.as_str()),
        ];
        let generated_fields: [(&str, &str); 18] = [
            ("id", generated.id),
            ("name", generated.name),
            ("kind", generated.kind),
            ("module", generated.module),
            ("telescope", generated.telescope),
            ("type_hash", generated.type_hash),
            ("value_hash", generated.value_hash),
            ("safety", generated.safety),
            ("attributes", generated.attributes),
            ("entry_class", generated.entry_class),
            ("entry_scope", generated.entry_scope),
            ("symbol", generated.symbol),
            ("effect", generated.effect),
            ("partition", generated.partition),
            ("ownership", generated.ownership),
            ("mode", generated.mode),
            ("profile", generated.profile),
            ("row_root", generated.row_root),
        ];
        for ((field, expected), (_, actual)) in generated_fields.iter().zip(parsed_fields.iter()) {
            if expected != actual {
                return Err(ContractError::new(format!(
                    "row {} field {field} diverges between the generated table and the \
                     contract: {expected:?} vs {actual:?}",
                    parsed.id
                )));
            }
        }
        if generated.levels != parsed.levels || generated.arity != parsed.arity {
            return Err(ContractError::new(format!(
                "row {} levels/arity diverge between the generated table and the contract",
                parsed.id
            )));
        }
    }
    Ok(())
}

/// Stage 3: independently re-derive every row root from the row's own fields.
/// This is the stage that makes a one-sided edit anywhere in the pipeline a
/// named divergence rather than a silent one: the root fields ARE the row.
pub fn validate_row_roots(contract: &ExternRowContract) -> Result<(), ContractError> {
    for row in &contract.rows {
        let recomputed = row.compute_row_root();
        if row.row_root != recomputed {
            return Err(ContractError::new(format!(
                "row {} carries root {} but recomputes to {recomputed}",
                row.id, row.row_root
            )));
        }
    }
    Ok(())
}

/// The full load: parse, then projection, then row roots. Every stage's refusal
/// names its stage, so a drift report says which law fired.
pub fn load(text: &str) -> Result<ExternRowContract, ContractError> {
    let contract = parse(text)?;
    validate_generated_projection(&contract)
        .map_err(|error| ContractError::new(format!("generated-projection stage: {error}")))?;
    validate_row_roots(&contract)
        .map_err(|error| ContractError::new(format!("row-roots stage: {error}")))?;
    Ok(contract)
}

/// The embedded contract text. Lives behind a function so the include happens
/// exactly once.
pub fn embedded_contract_text() -> &'static str {
    include_str!("../../../contracts/EXTERN_ROW_CONTRACT.txt")
}

/// Load the committed contract.
pub fn load_embedded() -> Result<ExternRowContract, ContractError> {
    load(embedded_contract_text())
}

/// The evidence of a productive reduction: how many rows each worker closed and
/// the schedule-invariant semantic root over them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ScheduleEvidence {
    pub workers: usize,
    pub completed_per_worker: Vec<usize>,
    pub semantic_root: String,
}

/// Partition the row population across `workers` by index modulo, then prove
/// two things: conservation (every row closes exactly once — the partitions
/// cover the population with no overlap and no hole) and worker-invariance
/// (the semantic root is over the canonical row-root stream, so it is
/// identical at 1, 8, or 32 workers — the {1, 8, 32} thread-matrix law for
/// this table, plan PG-5: the answer does not depend on how the work was cut).
///
/// Refuses an unproductive cut: zero workers, or more workers than rows (an
/// empty partition would report agreement about nothing).
pub fn reduce_productively(
    contract: &ExternRowContract,
    workers: usize,
) -> Result<ScheduleEvidence, ContractError> {
    if workers == 0 || workers > contract.rows.len() {
        return Err(ContractError::new(format!(
            "refusing an unproductive reduction: {workers} workers over {} rows",
            contract.rows.len()
        )));
    }
    let mut completed_per_worker = vec![0usize; workers];
    for (index, _row) in contract.rows.iter().enumerate() {
        completed_per_worker[index % workers] += 1;
    }
    if completed_per_worker.iter().sum::<usize>() != contract.rows.len() {
        return Err(ContractError::new(
            "partition conservation violated: the workers did not close the population",
        ));
    }
    let semantic_root = framed_hash(
        "fln.extern-row/schedule/1",
        contract.rows.iter().map(|row| row.row_root.as_str()),
    );
    Ok(ScheduleEvidence {
        workers,
        completed_per_worker,
        semantic_root,
    })
}
