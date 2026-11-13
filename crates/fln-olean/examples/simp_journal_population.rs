//! Measure the pin's persisted default-simp population through native readers.
//!
//! cargo run -p fln-olean --example simp_journal_population -- LIB/lean Init Std Lean
//!
//! stdout is a deterministic census, emitted only after every requested import
//! closure succeeds. No Reference code executes. Each module and closure row
//! reports:
//! - `events`: raw persisted `simp` extension entries in the `.olean` journal;
//! - `retained`: global entries that emit a native `FrankenLean.sourceSimp.v1`
//!   row (`scope == None`; dormant `scoped` entries emit 0 native rows);
//! - `max_payload_bytes`: exact worst-case native journal payload bytes across
//!   retained entries (`max(activated_payload, erase_payload)` in `fln-elab`'s
//!   wire format), before adding `retained * size_of::<ExtensionEntry>()`.
//!
//! Module-system companions are cumulative, so only the final private part counts.
#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use fln_core::expr::ExprNode;
use fln_core::name::{LeafView, Name};
use fln_olean::format::{PIN_COMMIT, PIN_TAG};
use fln_olean::pin::check_pinned_header;
use fln_olean::region::{ExtensionBlock, OleanView, OpaqueExtensionBlock, WalkBudget};
use fln_olean::source_extensions::{DecodeLimits, SIMP_EXTENSION, SimpEntry, SimpKind, decode};

const MAX_COMPONENTS: usize = 256;
const MAX_ROW_BYTES: usize = 16_384;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PopulationMetrics {
    events: u64,
    retained: u64,
    max_payload_bytes: u128,
}

struct Population {
    imports: Vec<Name>,
    metrics: PopulationMetrics,
}

fn structural_name_bytes(name: &Name) -> Result<usize, String> {
    let mut parts = Vec::new();
    let mut cursor = name.clone();
    while !cursor.is_anonymous() {
        if parts.len() >= MAX_COMPONENTS {
            return Err(format!(
                "simp name {} exceeds {MAX_COMPONENTS} components",
                name.to_display_string()
            ));
        }
        parts.push(cursor.clone());
        cursor = cursor.parent();
    }
    if parts.is_empty() {
        return Err("anonymous simp name".to_owned());
    }
    let mut bytes = 2usize;
    for part in parts.into_iter().rev() {
        match part.leaf_view() {
            LeafView::Str(s) => {
                if s.len() > MAX_ROW_BYTES {
                    return Err(format!("simp name component exceeds {MAX_ROW_BYTES} bytes"));
                }
                bytes = bytes
                    .checked_add(5)
                    .and_then(|n| n.checked_add(s.len()))
                    .ok_or("simp name byte overflow")?;
            }
            LeafView::Num(_) => {
                bytes = bytes.checked_add(9).ok_or("simp name byte overflow")?;
            }
            LeafView::Anonymous => return Err("anonymous simp name component".to_owned()),
        }
        if bytes > MAX_ROW_BYTES {
            return Err(format!(
                "simp structural name exceeds {MAX_ROW_BYTES} bytes"
            ));
        }
    }
    Ok(bytes)
}

fn source_payload_bytes(declaration: &Name) -> Result<usize, String> {
    let mut cursor = declaration.clone();
    let mut string_lengths = Vec::new();
    let mut all_nonempty_strings = true;
    while !cursor.is_anonymous() {
        if string_lengths.len() >= MAX_COMPONENTS {
            all_nonempty_strings = false;
            break;
        }
        match cursor.leaf_view() {
            LeafView::Str(part) if !part.is_empty() => string_lengths.push(part.len()),
            _ => {
                all_nonempty_strings = false;
                break;
            }
        }
        cursor = cursor.parent();
    }
    let bytes = if all_nonempty_strings {
        if string_lengths.is_empty() {
            return Err("anonymous simp source declaration".to_owned());
        }
        string_lengths
            .into_iter()
            .try_fold(18usize, |acc, len| acc.checked_add(4 + len))
            .ok_or("simp source payload overflow")?
    } else {
        14usize
            .checked_add(structural_name_bytes(declaration)?)
            .ok_or("simp structural source payload overflow")?
    };
    if bytes > MAX_ROW_BYTES {
        return Err(format!("simp source payload exceeds {MAX_ROW_BYTES} bytes"));
    }
    Ok(bytes)
}

fn entry_native_metrics(entry: &SimpEntry) -> Result<(u64, u128), String> {
    if entry.scope.is_some() {
        return Ok((0, 0));
    }
    let max_bytes = match &entry.kind {
        SimpKind::Theorem(theorem) => {
            let erase_bytes = source_payload_bytes(&theorem.origin)?;
            if theorem.post
                && !theorem.origin_reverse
                && !theorem.permutation
                && let ExprNode::Const { name, .. } = theorem.proof.node()
            {
                let origin_bytes = structural_name_bytes(&theorem.origin)?;
                let proof_name_bytes = structural_name_bytes(name)?;
                let proof_bytes = 14usize
                    .checked_add(origin_bytes)
                    .and_then(|n| n.checked_add(proof_name_bytes))
                    .ok_or("simp proof payload overflow")?;
                if proof_bytes > MAX_ROW_BYTES {
                    return Err(format!("simp proof payload exceeds {MAX_ROW_BYTES} bytes"));
                }
                erase_bytes.max(proof_bytes)
            } else {
                erase_bytes
            }
        }
        SimpKind::Unfold(declaration) => source_payload_bytes(declaration)?,
        SimpKind::UnfoldTheorems {
            declaration,
            theorems,
        } => {
            if theorems.len() > MAX_ROW_BYTES / 5 {
                return Err("simp unfold-theorems count exceeds row bound".to_owned());
            }
            let erase_bytes = source_payload_bytes(declaration)?;
            let mut unfold_bytes = 13usize
                .checked_add(structural_name_bytes(declaration)?)
                .ok_or("simp unfold-theorems payload overflow")?;
            for theorem in theorems {
                unfold_bytes = unfold_bytes
                    .checked_add(structural_name_bytes(theorem)?)
                    .ok_or("simp unfold-theorems payload overflow")?;
            }
            if unfold_bytes > MAX_ROW_BYTES {
                return Err(format!(
                    "simp unfold-theorems payload exceeds {MAX_ROW_BYTES} bytes"
                ));
            }
            erase_bytes.max(unfold_bytes)
        }
    };
    Ok((1, max_bytes as u128))
}

fn event_count(blocks: &[ExtensionBlock]) -> Result<u64, String> {
    let mut seen = BTreeSet::new();
    let mut count = 0;
    for block in blocks {
        if !seen.insert(&block.name) {
            return Err(format!("duplicate extension block {}", block.name));
        }
        if block.name == SIMP_EXTENSION {
            count = block.entries;
        }
    }
    Ok(count)
}

fn decode_metrics(
    view: &OleanView,
    budget: WalkBudget,
    events: u64,
) -> Result<PopulationMetrics, String> {
    if events == 0 {
        return Ok(PopulationMetrics {
            events: 0,
            retained: 0,
            max_payload_bytes: 0,
        });
    }
    let simp_name = Name::from_components(SIMP_EXTENSION.split('.'));
    let selected = view
        .selected_extension_payloads(budget, 64 << 20, |name| *name == simp_name)
        .map_err(|error| error.to_string())?;
    let mut blocks = Vec::new();
    for block in selected {
        if let Some(entries) = block.entries {
            blocks.push(OpaqueExtensionBlock {
                name: block.name,
                entries,
            });
        }
    }
    let decoded = decode(&blocks, DecodeLimits::default()).map_err(|error| error.to_string())?;
    if decoded.simps.len() as u64 != events {
        return Err(format!(
            "decoded simp count {} disagrees with block header {events}",
            decoded.simps.len()
        ));
    }
    let mut retained = 0u64;
    let mut max_payload_bytes = 0u128;
    for entry in &decoded.simps {
        let (entry_retained, entry_bytes) = entry_native_metrics(entry)?;
        retained = retained
            .checked_add(entry_retained)
            .ok_or("retained simp event overflow")?;
        max_payload_bytes = max_payload_bytes
            .checked_add(entry_bytes)
            .ok_or("simp payload byte overflow")?;
    }
    Ok(PopulationMetrics {
        events,
        retained,
        max_payload_bytes,
    })
}

fn inspect(public: &[u8], companions: Option<(&[u8], &[u8])>) -> Result<Population, String> {
    let budget = WalkBudget::default();
    check_pinned_header(public).map_err(|error| error.to_string())?;
    let view = OleanView::parse(public).map_err(|error| error.to_string())?;
    view.walk(budget).map_err(|error| error.to_string())?;
    let module = view
        .module_data(budget)
        .map_err(|error| error.to_string())?;
    let metrics = if module.is_module {
        let (server, private) =
            companions.ok_or("module-system artifact requires server and private companions")?;
        for part in [server, private] {
            check_pinned_header(part).map_err(|error| error.to_string())?;
        }
        let private_view = OleanView::parse_with_dependencies(private, &[public, server])
            .map_err(|error| error.to_string())?;
        private_view
            .walk(budget)
            .map_err(|error| error.to_string())?;
        let final_module = private_view
            .module_data(budget)
            .map_err(|error| error.to_string())?;
        let events = event_count(&final_module.extensions)?;
        decode_metrics(&private_view, budget, events)?
    } else {
        let events = event_count(&module.extensions)?;
        decode_metrics(&view, budget, events)?
    };
    Ok(Population {
        imports: module
            .imports
            .into_iter()
            .map(|import| import.module)
            .collect(),
        metrics,
    })
}

fn module_path(lib: &Path, module: &Name) -> Result<PathBuf, String> {
    let display = module.to_display_string();
    if Name::from_components(display.split('.')) != *module {
        return Err(format!("unsupported structural module name {display}"));
    }
    let mut path = lib.to_path_buf();
    for component in display.split('.') {
        // Refuse an unrepresentable module path instead of interpreting source
        // quoting, numeric Name components, or paths outside the supplied library.
        if component.is_empty()
            || !component
                .chars()
                .all(|c| c.is_alphanumeric() || matches!(c, '_' | '\''))
        {
            return Err(format!("unsupported module path {display}"));
        }
        path.push(component);
    }
    Ok(path)
}

fn read_module(lib: &Path, name: &Name) -> Result<Population, String> {
    let base = module_path(lib, name)?;
    let read = |extension: &str| {
        let path = base.with_extension(extension);
        std::fs::read(&path).map_err(|error| format!("{}: {error}", path.display()))
    };
    let public = read("olean")?;
    check_pinned_header(&public).map_err(|error| error.to_string())?;
    let is_module = OleanView::parse(&public)
        .map_err(|error| error.to_string())?
        .module_data(WalkBudget::default())
        .map_err(|error| error.to_string())?
        .is_module;
    if is_module {
        let server = read("olean.server")?;
        let private = read("olean.private")?;
        inspect(&public, Some((&server, &private)))
    } else {
        inspect(&public, None)
    }
}

fn run(args: &[String]) -> Result<String, String> {
    let [lib, roots @ ..] = args else {
        return Err("usage: simp_journal_population LIB/lean Init [Std] [Lean]".to_owned());
    };
    if roots.is_empty()
        || roots
            .iter()
            .any(|root| !matches!(root.as_str(), "Init" | "Std" | "Lean"))
    {
        return Err("request at least one of the pinned roots Init, Std, or Lean".to_owned());
    }
    let roots: BTreeSet<Name> = roots
        .iter()
        .map(|root| Name::from_components([root.as_str()]))
        .collect();
    let mut modules = BTreeMap::<Name, Population>::new();
    let mut closures = Vec::new();
    for root in roots {
        let mut pending = vec![root.clone()];
        let mut seen = BTreeSet::new();
        let mut totals = PopulationMetrics {
            events: 0,
            retained: 0,
            max_payload_bytes: 0,
        };
        while let Some(name) = pending.pop() {
            if !seen.insert(name.clone()) {
                continue;
            }
            let population = match modules.entry(name.clone()) {
                std::collections::btree_map::Entry::Occupied(entry) => entry.into_mut(),
                std::collections::btree_map::Entry::Vacant(entry) => entry
                    .insert(read_module(Path::new(lib), &name).map_err(|error| {
                        format!("module {}: {error}", name.to_display_string())
                    })?),
            };
            totals.events = totals
                .events
                .checked_add(population.metrics.events)
                .ok_or("simp population count overflow")?;
            totals.retained = totals
                .retained
                .checked_add(population.metrics.retained)
                .ok_or("simp retained count overflow")?;
            totals.max_payload_bytes = totals
                .max_payload_bytes
                .checked_add(population.metrics.max_payload_bytes)
                .ok_or("simp payload byte count overflow")?;
            pending.extend(population.imports.iter().cloned());
        }
        if totals.events == 0 {
            return Err(format!(
                "root {} has no simp entries",
                root.to_display_string()
            ));
        }
        closures.push((root, seen.len(), totals));
    }
    let mut output = format!("schema fln-simp-journal-population/2\npin {PIN_TAG} {PIN_COMMIT}\n");
    for (name, population) in &modules {
        output.push_str(&format!(
            "module\t{}\t{}\t{}\t{}\n",
            name.to_display_string(),
            population.metrics.events,
            population.metrics.retained,
            population.metrics.max_payload_bytes
        ));
    }
    for (root, modules, totals) in closures {
        output.push_str(&format!(
            "closure\t{}\t{modules}\t{}\t{}\t{}\n",
            root.to_display_string(),
            totals.events,
            totals.retained,
            totals.max_payload_bytes
        ));
    }
    Ok(output)
}

fn main() -> ExitCode {
    match run(&std::env::args().skip(1).collect::<Vec<_>>()) {
        Ok(output) => {
            print!("{output}");
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("simp_journal_population: {error}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn real_pinned_prelude_counts_only_the_complete_companion() {
        let public = include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean");
        let server =
            include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean.server");
        let private =
            include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean.private");
        let population = inspect(public, Some((server, private))).unwrap();
        assert_eq!(population.metrics.events, 3);
        assert_eq!(population.metrics.retained, 3);
        assert!(population.metrics.max_payload_bytes > 0);
        assert!(population.imports.is_empty());
        assert!(inspect(public, None).is_err());
    }

    #[test]
    fn duplicate_blocks_and_unknown_requested_roots_refuse() {
        let block = ExtensionBlock {
            name: SIMP_EXTENSION.to_owned(),
            entries: 7,
        };
        assert_eq!(event_count(std::slice::from_ref(&block)).unwrap(), 7);
        assert!(event_count(&[block.clone(), block]).is_err());
        assert!(run(&["unused".to_owned(), "Missing".to_owned()]).is_err());
        assert!(run(&["unused".to_owned()]).is_err());
    }
}
