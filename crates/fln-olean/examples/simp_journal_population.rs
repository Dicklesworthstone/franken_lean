//! Measure the pin's persisted default-simp population through native readers.
//!
//! cargo run -p fln-olean --example simp_journal_population -- LIB/lean Init Std Lean
//!
//! stdout is a deterministic census, emitted only after every requested import
//! closure succeeds. No Reference code executes. These are raw persisted events,
//! not active rules or a claim that any theorem has passed kernel admission.
//! The source importer currently emits at most one native event per such entry.
//! Module-system companions are cumulative, so only the final private part counts.
#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use fln_core::name::Name;
use fln_olean::format::{PIN_COMMIT, PIN_TAG};
use fln_olean::pin::check_pinned_header;
use fln_olean::region::{ExtensionBlock, OleanView, WalkBudget};
use fln_olean::source_extensions::SIMP_EXTENSION;

struct Population {
    imports: Vec<Name>,
    events: u64,
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

fn inspect(
    public: &[u8],
    companions: Option<(&[u8], &[u8])>,
) -> Result<Population, String> {
    let budget = WalkBudget::default();
    check_pinned_header(public).map_err(|error| error.to_string())?;
    let view = OleanView::parse(public).map_err(|error| error.to_string())?;
    view.walk(budget).map_err(|error| error.to_string())?;
    let module = view.module_data(budget).map_err(|error| error.to_string())?;
    let events = if module.is_module {
        let (server, private) =
            companions.ok_or("module-system artifact requires server and private companions")?;
        for part in [server, private] {
            check_pinned_header(part).map_err(|error| error.to_string())?;
        }
        let private_view = OleanView::parse_with_dependencies(private, &[public, server])
            .map_err(|error| error.to_string())?;
        private_view.walk(budget).map_err(|error| error.to_string())?;
        let final_module = private_view
            .module_data(budget)
            .map_err(|error| error.to_string())?;
        event_count(&final_module.extensions)?
    } else {
        event_count(&module.extensions)?
    };
    Ok(Population {
        imports: module.imports.into_iter().map(|import| import.module).collect(),
        events,
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
        || roots.iter().any(|root| !matches!(root.as_str(), "Init" | "Std" | "Lean"))
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
        let mut events = 0u64;
        while let Some(name) = pending.pop() {
            if !seen.insert(name.clone()) {
                continue;
            }
            let population = match modules.entry(name.clone()) {
                std::collections::btree_map::Entry::Occupied(entry) => entry.into_mut(),
                std::collections::btree_map::Entry::Vacant(entry) => entry.insert(
                    read_module(Path::new(lib), &name)
                        .map_err(|error| format!("module {}: {error}", name.to_display_string()))?,
                ),
            };
            events = events
                .checked_add(population.events)
                .ok_or("simp population count overflow")?;
            pending.extend(population.imports.iter().cloned());
        }
        if events == 0 {
            return Err(format!("root {} has no simp entries", root.to_display_string()));
        }
        closures.push((root, seen.len(), events));
    }
    let mut output = format!(
        "schema fln-simp-journal-population/1\npin {PIN_TAG} {PIN_COMMIT}\n"
    );
    for (name, population) in &modules {
        output.push_str(&format!(
            "module\t{}\t{}\n",
            name.to_display_string(),
            population.events
        ));
    }
    for (root, modules, events) in closures {
        output.push_str(&format!(
            "closure\t{}\t{modules}\t{events}\n",
            root.to_display_string()
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
        assert_eq!(population.events, 3);
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
