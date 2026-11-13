//! Property, oracle-differential, unknown-reader conservatism, and planted
//! read-omission mutant tests for metavariable wakeup completeness
//! (bead `franken_lean-zis`, plan §10.1, FL-INV-01).

#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, FVarId, MVarId};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_elab::constraint::{Constraint, ConstraintId, ConstraintKind, ConstraintQueue};
use fln_elab::lctx::LocalContext;
use fln_elab::mvar::{AssignmentJustification, MetavarKind, MetavarStore};
use std::collections::{BTreeSet, HashSet};

fn name1(s: impl AsRef<str>) -> Name {
    Name::from_components([s.as_ref()])
}

fn mvar_id(idx: usize) -> MVarId {
    MVarId(name1(format!("m{idx}")))
}

#[derive(Clone, Copy)]
struct SplitMix64(u64);

impl SplitMix64 {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn pick(&mut self, upper: usize) -> usize {
        (self.next_u64() as usize) % upper
    }
}

/// Independent full-scan oracle: inspects every remaining constraint before and
/// after an assignment and reports every constraint whose live dependency set
/// changed (or which carries an opaque `reads_unknown` marker).
fn full_scan_oracle_affected(
    before_rows: &[Constraint],
    before_store: &MetavarStore,
    after_store: &MetavarStore,
) -> BTreeSet<ConstraintId> {
    let mut must_wake = BTreeSet::new();
    for row in before_rows {
        if row.reads_unknown {
            must_wake.insert(row.id);
            continue;
        }
        let deps_before = row.dependencies(before_store);
        let deps_after = row.dependencies(after_store);
        if deps_before != deps_after {
            must_wake.insert(row.id);
        }
    }
    must_wake
}

#[test]
fn wakeup_matches_full_scan_oracle_across_generated_graphs_with_zero_missed_wakeups() {
    let prop_const = Expr::const_(Name::from_components(["P"]), Vec::new());

    for seed in 0..64u64 {
        let mut rng = SplitMix64(0x7150_0000_0000_0000 ^ seed);
        let mut store = MetavarStore::new();
        let mut queue = ConstraintQueue::new();
        let n = 8usize;
        let ids: Vec<MVarId> = (0..n).map(mvar_id).collect();

        // Declare m0..m3 with ground types, and m4..m7 whose types/contexts depend on earlier mvars!
        for i in 0..n {
            let mut lctx = LocalContext::new();
            let ty = if i < 4 {
                Expr::sort(Level::one())
            } else {
                let dep_ty = &ids[rng.pick(i)];
                let dep_let = &ids[rng.pick(i)];
                lctx.add_let(
                    FVarId(name1(format!("let_{i}"))),
                    name1(format!("let_{i}")),
                    Expr::sort(Level::one()),
                    Expr::mvar(dep_let.clone()),
                );
                Expr::app(prop_const.clone(), Expr::mvar(dep_ty.clone()))
            };
            store.declare(
                ids[i].clone(),
                ids[i].0.clone(),
                ty,
                lctx,
                MetavarKind::Natural,
                0,
                None,
            );
        }

        // Pre-wire one alias edge `m0 := ?m1` on odd seeds to exercise pre-existing chains.
        let start_idx = if seed % 2 == 1 {
            store
                .assign(
                    ids[0].clone(),
                    Expr::mvar(ids[1].clone()),
                    AssignmentJustification::DirectDefEq,
                )
                .expect("alias m0 := ?m1");
            assert_eq!(store.assignment_revision(), 1);
            1
        } else {
            0
        };

        // Enqueue 10 obligations mixing DefEq, HasType, SynthInstance, DelayedAssign, and conservative unknown readers.
        for c_idx in 0..10usize {
            let a = &ids[rng.pick(n)];
            let b = &ids[rng.pick(n)];
            let mut lctx = LocalContext::new();
            if c_idx % 3 == 0 {
                let ctx_dep = &ids[rng.pick(n)];
                lctx.add_param(
                    FVarId(name1(format!("p_{c_idx}"))),
                    name1(format!("p_{c_idx}")),
                    Expr::app(prop_const.clone(), Expr::mvar(ctx_dep.clone())),
                    BinderInfo::Default,
                );
            }
            let kind = match c_idx % 4 {
                0 => ConstraintKind::DefEq {
                    lhs: Expr::mvar(a.clone()),
                    rhs: Expr::mvar(b.clone()),
                },
                1 => ConstraintKind::HasType {
                    expr: Expr::mvar(a.clone()),
                    expected_type: Expr::app(prop_const.clone(), Expr::mvar(b.clone())),
                },
                2 => ConstraintKind::SynthInstance {
                    class: Expr::app(prop_const.clone(), Expr::mvar(a.clone())),
                    mvar: b.clone(),
                },
                _ => ConstraintKind::DelayedAssign {
                    mvar: b.clone(),
                    fvars: Vec::new(),
                    val: Expr::mvar(a.clone()),
                },
            };
            if c_idx == 9 {
                queue.enqueue_conservative_scoped(kind, &store, &lctx, 0);
            } else {
                queue.enqueue_scoped(kind, &store, &lctx, 0);
            }
        }

        // Assign each remaining mvar either to an unassigned higher mvar (forming chains) or to Sort(0).
        for step in start_idx..n {
            let before_store = store.clone();
            let mut before_rows: Vec<Constraint> = queue.constraints().values().cloned().collect();
            before_rows.sort_by_key(|row| row.id);
            let rev_before = store.assignment_revision();

            let rhs = if step + 1 < n && rng.pick(3) == 0 {
                Expr::mvar(ids[step + 1].clone())
            } else {
                Expr::sort(Level::zero())
            };

            let awakened = queue
                .assign_mvar(
                    &mut store,
                    ids[step].clone(),
                    rhs,
                    AssignmentJustification::DirectDefEq,
                )
                .expect("acyclic assignment succeeds");
            assert_eq!(store.assignment_revision(), rev_before + 1);

            let awakened_ids: BTreeSet<ConstraintId> = awakened.iter().map(|c| c.id).collect();
            // Strictly monotonic ConstraintId order on every returned batch (FL-INV-01).
            let raw_order: Vec<ConstraintId> = awakened.iter().map(|c| c.id).collect();
            let sorted_order: Vec<ConstraintId> = awakened_ids.iter().copied().collect();
            assert_eq!(
                raw_order, sorted_order,
                "wake batch must be in canonical ID order"
            );

            let oracle_must_wake = full_scan_oracle_affected(&before_rows, &before_store, &store);
            for required in &oracle_must_wake {
                assert!(
                    awakened_ids.contains(required),
                    "seed={seed} step={step}: missed wakeup for {required:?}! awakened={awakened_ids:?}, required={oracle_must_wake:?}"
                );
            }

            // Re-enqueue any awakened obligation that still has unresolved dependencies (simulating partial progress).
            for row in awakened {
                let remaining = row.dependencies(&store);
                if !remaining.is_empty() {
                    if row.reads_unknown {
                        queue.enqueue_conservative(row.kind, remaining, row.depth);
                    } else if let Some(locals) = row.local_context.as_deref() {
                        queue.enqueue_scoped(row.kind, &store, locals, row.depth);
                    } else {
                        queue.enqueue(row.kind, remaining, row.depth);
                    }
                }
            }
        }
    }
}

#[test]
fn unknown_reader_conservatism_wakes_on_any_assignment_blocks_take_ready_and_narrows_cleanly() {
    let mut store = MetavarStore::new();
    let m_hidden = mvar_id(1);
    let m_other = mvar_id(2);
    for id in [&m_hidden, &m_other] {
        store.declare(
            id.clone(),
            id.0.clone(),
            Expr::sort(Level::one()),
            LocalContext::new(),
            MetavarKind::Natural,
            0,
            None,
        );
    }

    let mut queue = ConstraintQueue::new();
    let ground_kind = ConstraintKind::DefEq {
        lhs: Expr::sort(Level::zero()),
        rhs: Expr::sort(Level::zero()),
    };

    // An obligation with unknown dynamic reads (empty syntactic set, `reads_unknown = true`)
    // must NOT be prematurely drained by `take_ready` while its reads are unknown.
    let conservative_id = queue.enqueue_conservative(ground_kind.clone(), HashSet::new(), 0);
    let ready_known_id = queue.enqueue(ground_kind.clone(), HashSet::new(), 0);
    let sleeping_known_id = queue.enqueue(ground_kind.clone(), HashSet::from([m_other.clone()]), 0);
    assert_eq!(queue.unknown_reader_count(), 1);

    let ready = queue.take_ready();
    assert_eq!(
        ready.iter().map(|r| r.id).collect::<Vec<_>>(),
        vec![ready_known_id],
        "take_ready must extract known-ready obligations and hold unknown-reader obligations"
    );
    assert_eq!(queue.unknown_reader_count(), 1);

    // Empty mvar wake call wakes nothing.
    assert!(
        queue
            .wake_up_for_mvars(std::iter::empty::<&MVarId>())
            .is_empty()
    );

    // Assigning `m_hidden` conservatively wakes `conservative_id` while keeping `sleeping_known_id` asleep!
    let woke = queue
        .assign_mvar(
            &mut store,
            m_hidden,
            Expr::sort(Level::zero()),
            AssignmentJustification::DirectDefEq,
        )
        .expect("assign m_hidden");
    assert_eq!(woke.len(), 1);
    assert_eq!(woke[0].id, conservative_id);
    assert!(woke[0].reads_unknown);
    assert_eq!(queue.unknown_reader_count(), 0);
    assert!(queue.constraints().contains_key(&sleeping_known_id));

    // Re-enqueuing conservatively and then narrowing via `update_reads` clears `reads_unknown`.
    let narrowed_id = queue.enqueue_conservative(ground_kind, HashSet::new(), 0);
    assert_eq!(queue.unknown_reader_count(), 1);
    assert!(queue.update_reads(narrowed_id, HashSet::new()));
    assert_eq!(queue.unknown_reader_count(), 0);
    let ready_after_narrow = queue.take_ready();
    assert_eq!(
        ready_after_narrow.iter().map(|r| r.id).collect::<Vec<_>>(),
        vec![narrowed_id]
    );
}

#[test]
fn planted_read_omission_mutants_are_caught_by_completeness_oracle() {
    let prop_const = Expr::const_(Name::from_components(["P"]), Vec::new());
    let m_type_dep = mvar_id(10);
    let m_term = mvar_id(11);

    // Mutant 1: omitting transitive metavariable-type dependency (`?m_term : P ?m_type_dep`)
    // by passing syntactic-only `{m_term}` instead of `enqueue_scoped`.
    let mut store_mutant = MetavarStore::new();
    store_mutant.declare(
        m_type_dep.clone(),
        m_type_dep.0.clone(),
        Expr::sort(Level::one()),
        LocalContext::new(),
        MetavarKind::Natural,
        0,
        None,
    );
    store_mutant.declare(
        m_term.clone(),
        m_term.0.clone(),
        Expr::app(prop_const, Expr::mvar(m_type_dep.clone())),
        LocalContext::new(),
        MetavarKind::Natural,
        0,
        None,
    );
    let mut store_prod = store_mutant.clone();

    let kind = ConstraintKind::HasType {
        expr: Expr::mvar(m_term.clone()),
        expected_type: Expr::sort(Level::zero()),
    };
    let mut mutant_queue = ConstraintQueue::new();
    // Planted read-omission mutant: syntactic-only `{m_term}`, omitting `m_type_dep`!
    let mutant_cid = mutant_queue.enqueue(kind.clone(), HashSet::from([m_term]), 0);

    let mut prod_queue = ConstraintQueue::new();
    let prod_cid = prod_queue.enqueue_scoped(kind, &store_prod, &LocalContext::new(), 0);

    let before_rows: Vec<Constraint> = mutant_queue.constraints().values().cloned().collect();
    let before_store = store_mutant.clone();
    let mutant_woke = mutant_queue
        .assign_mvar(
            &mut store_mutant,
            m_type_dep.clone(),
            Expr::sort(Level::zero()),
            AssignmentJustification::DirectDefEq,
        )
        .unwrap();
    let oracle_required = full_scan_oracle_affected(&before_rows, &before_store, &store_mutant);
    assert!(
        oracle_required.contains(&mutant_cid) && mutant_woke.is_empty(),
        "planted syntactic-only read-omission mutant must miss the oracle-required wakeup"
    );

    let prod_woke = prod_queue
        .assign_mvar(
            &mut store_prod,
            m_type_dep,
            Expr::sort(Level::zero()),
            AssignmentJustification::DirectDefEq,
        )
        .unwrap();
    assert_eq!(
        prod_woke.iter().map(|c| c.id).collect::<Vec<_>>(),
        vec![prod_cid],
        "production `enqueue_scoped` wakes on transitive metavariable-type dependency"
    );
}
