//! PG-1 phase-profiling harness (bead `fln-kfdr`).
//!
//! Measures per-phase wall time (primary `.olean` decode, independent checker
//! `.olean` decode, declaration planning, K1 kernel checking, independent checker
//! + projection + publication) and prints the slowest individual declarations
//! for `Init.Prelude` and any target stdlib module with its transitive closure.
//!
//! All tests are `#[ignore]` so plain `cargo test` stays fast and offline.
#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fs;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::{Duration, Instant};

use fln_admission::{
    Admitted, ArtifactReadings, CheckerReading, OleanCheckLimits, OleanFrontierJobs,
    OleanModuleInput, ReadingCheck, decode_olean_module_input_with, plan_olean_declarations,
};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_env::environment::Environment;
use fln_kernel::verdict::{Budget, Verdict};

const STACK_BYTES: usize = 64 * 1024 * 1024;
const MAX_BYTES: usize = 2 * 1024 * 1024 * 1024;

fn lib_lean_root() -> Option<PathBuf> {
    let sysroot = std::env::var("LEAN_SYSROOT")
        .unwrap_or_else(|_| "/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.32.0".to_owned());
    let path = PathBuf::from(sysroot).join("lib/lean");
    path.is_dir().then_some(path)
}

struct LoadedModule {
    name: Name,
    main: Vec<u8>,
    server: Option<Vec<u8>>,
    private: Option<Vec<u8>>,
}

fn load_module_parts(root: &Path, mod_name: &str) -> LoadedModule {
    let rel = mod_name.replace('.', "/");
    let main_path = root.join(format!("{rel}.olean"));
    let server_path = root.join(format!("{rel}.olean.server"));
    let private_path = root.join(format!("{rel}.olean.private"));
    let main = fs::read(&main_path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", main_path.display()));
    let server = server_path
        .is_file()
        .then(|| fs::read(&server_path).expect("read server part"));
    let private = private_path
        .is_file()
        .then(|| fs::read(&private_path).expect("read private part"));
    LoadedModule {
        name: Name::from_components(mod_name.split('.')),
        main,
        server,
        private,
    }
}

fn empty_admitted() -> Admitted {
    Admitted {
        environment: Environment::new(),
        checker_environment: None,
        imported_modules: Arc::new(BTreeSet::new()),
        imported_environment: None,
        imported_module_dependencies: Arc::new(BTreeMap::new()),
        executable_opaques: Arc::new(BTreeSet::new()),
        runtime_initializers: Arc::new(BTreeSet::new()),
        options: KVMap::new(),
    }
}

fn collect_transitive_imports(
    root: &Path,
    target_mod: &str,
    limits: OleanCheckLimits,
) -> Vec<LoadedModule> {
    let mut loaded: BTreeMap<String, LoadedModule> = BTreeMap::new();
    let mut queue = VecDeque::new();
    queue.push_back(target_mod.to_owned());
    while let Some(name) = queue.pop_front() {
        if loaded.contains_key(&name) {
            continue;
        }
        let m = load_module_parts(root, &name);
        let input = OleanModuleInput {
            name: &m.name,
            artifact: &m.main,
            server_artifact: m.server.as_deref(),
            private_artifact: m.private.as_deref(),
        };
        let decoded = decode_olean_module_input_with(&input, limits, CheckerReading::Skip)
            .unwrap_or_else(|e| panic!("decode header for {name}: {e}"));
        for imp in &decoded.module.imports {
            let imp_name = imp.module.to_display_string();
            if !loaded.contains_key(&imp_name) {
                queue.push_back(imp_name);
            }
        }
        loaded.insert(name, m);
    }
    loaded.into_values().collect()
}

fn profile_module_against_base(
    label: &str,
    base: Admitted,
    target: &LoadedModule,
    limits: OleanCheckLimits,
) {
    let input = OleanModuleInput {
        name: &target.name,
        artifact: &target.main,
        server_artifact: target.server.as_deref(),
        private_artifact: target.private.as_deref(),
    };

    let t0 = Instant::now();
    let decoded_primary_only = decode_olean_module_input_with(&input, limits, CheckerReading::Skip)
        .expect("decode primary");
    let decode_primary = t0.elapsed();

    let t1 = Instant::now();
    let decoded_full =
        decode_olean_module_input_with(&input, limits, CheckerReading::Read).expect("decode full");
    let decode_both = t1.elapsed();
    let decode_checker_est = decode_both.saturating_sub(decode_primary);
    drop(decoded_primary_only);

    let t2 = Instant::now();
    let plan = plan_olean_declarations(&base.environment, &decoded_full.constants, limits)
        .expect("plan declarations");
    let plan_dur = t2.elapsed();

    let readings = ArtifactReadings::new(&decoded_full.independent).expect("readings");
    let reading = ReadingCheck::Artifact(&readings);
    let options = KVMap::new();

    let mut engine = base;
    let mut k1_total = Duration::ZERO;
    let mut council_total = Duration::ZERO;
    let mut k1_steps_total: u64 = 0;

    #[derive(Clone)]
    struct UnitProfile {
        name: String,
        k1_ms: f64,
        checker_est_ms: f64,
        council_ms: f64,
        k1_steps: u64,
    }
    let mut profiles: Vec<UnitProfile> = Vec::with_capacity(plan.order.len());

    for &unit_idx in &plan.order {
        let unit = &plan.units[unit_idx];
        let unit_name = unit
            .names
            .first()
            .map(Name::to_display_string)
            .unwrap_or_else(|| "<unnamed>".to_owned());

        let tk = Instant::now();
        let k1_outcome = fln_kernel::check(
            &engine.environment,
            &unit.declaration,
            limits.admission.kernel,
        );
        let k1_dur = tk.elapsed();
        let k1_steps = match k1_outcome {
            Outcome::Complete(Verdict::Accepted { consumption }) => consumption.steps,
            other => panic!("K1 did not accept {unit_name}: {other:?}"),
        };

        let tc = Instant::now();
        let admitted = match engine
            .admit_declaration_unrooted(
                unit.declaration.clone(),
                &options,
                limits.admission,
                reading,
            )
            .unwrap_or_else(|e| panic!("council error on {unit_name}: {e}"))
        {
            Outcome::Complete(admitted) => admitted,
            Outcome::Inconclusive(r) => panic!("council inconclusive on {unit_name}: {r:?}"),
            Outcome::InternalFault(f) => panic!("council fault on {unit_name}: {f:?}"),
        };
        let council_dur = tc.elapsed();
        // `admit_declaration_unrooted` runs BOTH K1 and independent checker + projection + publish.
        let checker_est = council_dur.saturating_sub(k1_dur);

        k1_total += k1_dur;
        council_total += council_dur;
        k1_steps_total = k1_steps_total.saturating_add(k1_steps);
        profiles.push(UnitProfile {
            name: unit_name,
            k1_ms: k1_dur.as_secs_f64() * 1000.0,
            checker_est_ms: checker_est.as_secs_f64() * 1000.0,
            council_ms: council_dur.as_secs_f64() * 1000.0,
            k1_steps,
        });
        engine = admitted.engine;
    }

    let checker_plus_publish = council_total.saturating_sub(k1_total);
    let total_est = decode_both + plan_dur + council_total;
    println!("\n=== PG-1 PHASE PROFILE: {label} ===");
    println!(
        "constants={} units={} total_est_ms={:.1}",
        decoded_full.constants.len(),
        plan.order.len(),
        total_est.as_secs_f64() * 1000.0
    );
    println!(
        "  decode_primary_ms = {:8.1} ({:5.1}%)",
        decode_primary.as_secs_f64() * 1000.0,
        100.0 * decode_primary.as_secs_f64() / total_est.as_secs_f64().max(1e-9)
    );
    println!(
        "  decode_checker_ms = {:8.1} ({:5.1}%)",
        decode_checker_est.as_secs_f64() * 1000.0,
        100.0 * decode_checker_est.as_secs_f64() / total_est.as_secs_f64().max(1e-9)
    );
    println!(
        "  plan_ms           = {:8.1} ({:5.1}%)",
        plan_dur.as_secs_f64() * 1000.0,
        100.0 * plan_dur.as_secs_f64() / total_est.as_secs_f64().max(1e-9)
    );
    println!(
        "  k1_kernel_ms      = {:8.1} ({:5.1}%)  [k1_steps={k1_steps_total}]",
        k1_total.as_secs_f64() * 1000.0,
        100.0 * k1_total.as_secs_f64() / total_est.as_secs_f64().max(1e-9)
    );
    println!(
        "  checker+proj+pub  = {:8.1} ({:5.1}%)",
        checker_plus_publish.as_secs_f64() * 1000.0,
        100.0 * checker_plus_publish.as_secs_f64() / total_est.as_secs_f64().max(1e-9)
    );

    profiles.sort_by(|a, b| b.council_ms.total_cmp(&a.council_ms));
    println!("  Top 15 slowest declaration units:");
    for (i, p) in profiles.iter().take(15).enumerate() {
        println!(
            "   {:2}. {:58} council={:8.1}ms  k1={:7.1}ms  chk+pub={:8.1}ms  steps={}",
            i + 1,
            p.name,
            p.council_ms,
            p.k1_ms,
            p.checker_est_ms,
            p.k1_steps
        );
    }
}

#[test]
#[ignore = "PG-1 phase profiler against pinned v4.32.0 stdlib .olean files"]
fn pg1_profile_prelude_and_target_modules() {
    let Some(root) = lib_lean_root() else {
        eprintln!("SKIP: LEAN_SYSROOT lib/lean directory not present on this host");
        return;
    };
    let handle = std::thread::Builder::new()
        .name("pg1-profile".to_owned())
        .stack_size(STACK_BYTES)
        .spawn(move || {
            let limits = OleanCheckLimits::new(MAX_BYTES, Budget::for_stack_bytes(STACK_BYTES));
            let targets_env = std::env::var("FLN_PG1_PROFILE_MODULES").unwrap_or_else(|_| {
                "Init.Prelude,Init.Data.Array.Extract,Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas".to_owned()
            });
            for mod_name in targets_env.split(',').map(str::trim).filter(|s| !s.is_empty()) {
                if mod_name == "Init.Prelude" {
                    let prelude = load_module_parts(&root, "Init.Prelude");
                    profile_module_against_base("Init.Prelude", empty_admitted(), &prelude, limits);
                } else {
                    let t_imp = Instant::now();
                    let all = collect_transitive_imports(&root, mod_name, limits);
                    let target_name = Name::from_components(mod_name.split('.'));
                    let (targets, deps): (Vec<_>, Vec<_>) =
                        all.into_iter().partition(|m| m.name == target_name);
                    let target = targets.into_iter().next().expect("target present");
                    let dep_inputs: Vec<OleanModuleInput<'_>> = deps
                        .iter()
                        .map(|m| OleanModuleInput {
                            name: &m.name,
                            artifact: &m.main,
                            server_artifact: m.server.as_deref(),
                            private_artifact: m.private.as_deref(),
                        })
                        .collect();
                    let jobs = OleanFrontierJobs {
                        threads: NonZeroUsize::new(16).expect("non-zero"),
                        worker_stack_bytes: STACK_BYTES,
                    };
                    let checked = match empty_admitted()
                        .check_olean_modules_scheduled(
                            &dep_inputs,
                            &KVMap::new(),
                            limits,
                            jobs,
                            None,
                        )
                        .expect("check import closure")
                    {
                        Outcome::Complete(c) => c,
                        Outcome::Inconclusive(r) => {
                            panic!("import closure inconclusive for {mod_name}: {r:?}")
                        }
                        Outcome::InternalFault(f) => {
                            panic!("import closure fault for {mod_name}: {f:?}")
                        }
                    };
                    println!(
                        "\n[closure for {mod_name}: {} dep modules loaded in {:.1}s]",
                        dep_inputs.len(),
                        t_imp.elapsed().as_secs_f64()
                    );
                    profile_module_against_base(mod_name, checked.engine, &target, limits);
                }
            }
        })
        .expect("spawn profiler thread");
    handle.join().expect("profiler thread succeeded");
}
