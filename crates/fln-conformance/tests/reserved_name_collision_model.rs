//! Suite `reserved_name_collision_model` (bead fln-7gr6): the collision validator
//! as an order-independent model. Case variants, alias collisions, crate
//! double-claims, and a new conflicting registry entry must each fail for the
//! intended, typed reason with canonically ordered witnesses; row permutations can
//! never change a verdict.

#![forbid(unsafe_code)]

use fln_conformance::naming::{self, REGISTRY_PATH, Registry, RegistryError, Status, SubsystemRow};

fn row(name: &str, owner: &str, crates: &[&str], aliases: &[&str], status: Status) -> SubsystemRow {
    SubsystemRow {
        name: name.to_string(),
        owner: owner.to_string(),
        scope: format!("{name} scope"),
        crates: crates.iter().map(|krate| krate.to_string()).collect(),
        aliases: aliases.iter().map(|alias| alias.to_string()).collect(),
        status,
        reason: format!("{name} reason"),
        line: 0,
    }
}

#[test]
fn distinct_rows_validate() {
    let registry = Registry {
        rows: vec![
            row(
                "Vellum",
                "franken_lean",
                &["fln-parse"],
                &[],
                Status::Active,
            ),
            row("Quill", "frankensearch", &[], &[], Status::Reserved),
        ],
    };
    naming::validate_collisions(&registry).expect("distinct names are fine");
}

#[test]
fn mutant_case_variant_duplicate_is_killed() {
    // A lowercase variant is the SAME name: case-insensitivity is the law.
    let registry = Registry {
        rows: vec![
            row("Quill", "frankensearch", &[], &[], Status::Reserved),
            row("quill", "franken_lean", &[], &[], Status::Active),
        ],
    };
    match naming::validate_collisions(&registry) {
        Err(RegistryError::NameCollision { witnesses }) => {
            assert_eq!(witnesses.len(), 1);
            assert!(
                witnesses[0].starts_with("`quill` claimed by"),
                "witness names the case-folded key: {}",
                witnesses[0]
            );
        }
        other => panic!("MUTANT-SURVIVED case_variant: {other:?}"),
    }
}

#[test]
fn mutant_alias_colliding_with_name_is_killed() {
    let registry = Registry {
        rows: vec![
            row("Vellum", "franken_lean", &[], &[], Status::Active),
            row(
                "Parchment",
                "franken_lean",
                &[],
                &["vellum"],
                Status::Active,
            ),
        ],
    };
    match naming::validate_collisions(&registry) {
        Err(RegistryError::NameCollision { witnesses }) => {
            assert!(witnesses[0].contains("alias of Parchment"), "{witnesses:?}");
        }
        other => panic!("MUTANT-SURVIVED alias_vs_name: {other:?}"),
    }
}

#[test]
fn mutant_alias_colliding_with_alias_is_killed() {
    let registry = Registry {
        rows: vec![
            row("Alpha", "franken_lean", &[], &["Shared"], Status::Active),
            row("Beta", "franken_lean", &[], &["shared"], Status::Active),
        ],
    };
    match naming::validate_collisions(&registry) {
        Err(RegistryError::NameCollision { witnesses }) => {
            assert!(witnesses[0].starts_with("`shared`"), "{witnesses:?}");
        }
        other => panic!("MUTANT-SURVIVED alias_vs_alias: {other:?}"),
    }
}

#[test]
fn mutant_crate_claimed_twice_is_killed() {
    let registry = Registry {
        rows: vec![
            row(
                "Vellum",
                "franken_lean",
                &["fln-parse"],
                &[],
                Status::Active,
            ),
            row(
                "Grimoire",
                "franken_lean",
                &["fln-parse"],
                &[],
                Status::Active,
            ),
        ],
    };
    match naming::validate_collisions(&registry) {
        Err(RegistryError::CrateCollision { witnesses }) => {
            assert!(
                witnesses[0].contains("crate `fln-parse` claimed by [Grimoire, Vellum]"),
                "witness is canonical: {witnesses:?}"
            );
        }
        other => panic!("MUTANT-SURVIVED crate_double_claim: {other:?}"),
    }
}

#[test]
fn mutant_new_conflicting_registry_entry_is_killed() {
    // The bead's headline mutant: someone re-registers Quill for FrankenLean.
    let real =
        std::fs::read_to_string(naming::scan_root().join(REGISTRY_PATH)).expect("registry exists");
    let mutated = format!(
        "{real}row Quill | franken_lean | parser engine | - | - | active | conflicting re-registration\n"
    );
    let parsed = naming::parse_registry(&mutated).expect("row itself is well-formed");
    match naming::validate_collisions(&parsed) {
        Err(RegistryError::NameCollision { witnesses }) => {
            assert!(
                witnesses
                    .iter()
                    .any(|witness| witness.starts_with("`quill`")),
                "the collision names the reserved key: {witnesses:?}"
            );
        }
        other => panic!("MUTANT-SURVIVED conflicting_registry_entry: {other:?}"),
    }
}

#[test]
fn verdicts_are_independent_of_row_order() {
    let base = [
        row(
            "Vellum",
            "franken_lean",
            &["fln-parse"],
            &[],
            Status::Active,
        ),
        row("Quill", "frankensearch", &[], &[], Status::Reserved),
        row("quill", "franken_lean", &[], &[], Status::Active),
        row(
            "Grimoire",
            "franken_lean",
            &["fln-parse"],
            &[],
            Status::Active,
        ),
    ];
    let mut verdicts = Vec::new();
    let permutations: [[usize; 4]; 4] = [[0, 1, 2, 3], [3, 2, 1, 0], [2, 0, 3, 1], [1, 3, 0, 2]];
    for order in permutations {
        let registry = Registry {
            rows: order.iter().map(|&index| base[index].clone()).collect(),
        };
        verdicts.push(naming::validate_collisions(&registry));
    }
    for verdict in &verdicts[1..] {
        assert_eq!(
            verdict, &verdicts[0],
            "a row permutation changed the verdict or its witnesses"
        );
    }
    assert!(
        matches!(verdicts[0], Err(RegistryError::NameCollision { .. })),
        "the seeded collision is detected in every order"
    );
}

#[test]
fn witnesses_are_canonically_ordered() {
    let registry = Registry {
        rows: vec![
            row("Zeta", "franken_lean", &[], &[], Status::Active),
            row("zeta", "franken_lean", &[], &[], Status::Active),
            row("Alpha", "franken_lean", &[], &[], Status::Active),
            row("alpha", "franken_lean", &[], &[], Status::Active),
        ],
    };
    match naming::validate_collisions(&registry) {
        Err(RegistryError::NameCollision { witnesses }) => {
            assert_eq!(witnesses.len(), 2);
            let mut sorted = witnesses.clone();
            sorted.sort();
            assert_eq!(
                witnesses, sorted,
                "witnesses are emitted in canonical order"
            );
            assert!(witnesses[0].starts_with("`alpha`"));
            assert!(witnesses[1].starts_with("`zeta`"));
        }
        other => panic!("expected a name collision, got {other:?}"),
    }
}

#[test]
fn the_real_registry_survives_the_model() {
    let registry = naming::load_registry(&naming::scan_root()).unwrap_or_else(|error| {
        panic!("registry gate failed: {error}");
    });
    naming::validate_collisions(&registry).expect("the shipped registry is collision-free");
}
