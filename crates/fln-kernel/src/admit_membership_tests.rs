#[cfg(test)]
mod tests {
//! Regression coverage for the inductive-block constructor inventory.
//!
//! These tests exercise the real admission engine, not a model of its filter.
//! Public-admission fixtures establish acceptance before mutation.

use super::*;
use crate::verdict::Verdict;
use fln_env::constants::ConstantVal;

fn name(s: &str) -> Name {
    Name::str(Name::anonymous(), s)
}

fn empty_block(names: &[&str], level: Level) -> InductiveBlock {
    let all: Vec<Name> = names.iter().map(|s| name(s)).collect();
    InductiveBlock {
        types: all
            .iter()
            .map(|n| InductiveVal {
                base: ConstantVal {
                    name: n.clone(),
                    level_params: Vec::new(),
                    type_: Expr::sort(level.clone()),
                },
                num_params: 0,
                num_indices: 0,
                all: all.clone(),
                ctors: Vec::new(),
                num_nested: 0,
                is_rec: false,
                is_unsafe: false,
                is_reflexive: false,
            })
            .collect(),
        ctors: Vec::new(),
        recursors: Vec::new(),
    }
}

fn constructor(n: Name, parent: Name, result: Name, cidx: u32) -> ConstructorVal {
    ConstructorVal {
        base: ConstantVal {
            name: n,
            level_params: Vec::new(),
            type_: Expr::const_(result, Vec::new()),
        },
        induct: parent,
        cidx,
        num_params: 0,
        num_fields: 0,
        is_unsafe: false,
    }
}

fn finish_block(env: &Environment, mut block: InductiveBlock) -> InductiveBlock {
    let (recursors, is_rec, is_reflexive) = {
        let mut engine = Engine::new(env, &block, Budget::DEFAULT)
            .expect("the baseline inventory must be valid");
        engine
            .run_synthesized()
            .expect("the baseline declaration must synthesize")
    };
    block.recursors = recursors;
    for ind in &mut block.types {
        ind.is_rec = is_rec;
        ind.is_reflexive = is_reflexive;
    }
    let outcome = crate::check(
        env,
        &crate::Declaration::Inductive(block.clone()),
        Budget::DEFAULT,
    );
    assert!(
        matches!(outcome, Outcome::Complete(Verdict::Accepted { .. })),
        "the unmodified baseline must be accepted: {outcome:?}"
    );
    block
}

fn assert_membership_rejection(env: &Environment, block: InductiveBlock) {
    let outcome = crate::check(env, &crate::Declaration::Inductive(block), Budget::DEFAULT);
    match outcome {
        Outcome::Complete(Verdict::Rejected {
            class: RejectClass::BlockMismatch,
            message,
            ..
        }) => {
            assert!(message.contains("Forged"), "{message}");
            assert!(message.contains("Foreign"), "{message}");
            assert!(message.contains("outside the inductive block"), "{message}");
        }
        other => panic!("an orphan constructor must be rejected: {other:?}"),
    }
}

#[test]
fn orphan_constructor_cannot_inhabit_an_empty_proposition() {
    let env = Environment::new();
    let mut block = finish_block(&env, empty_block(&["Empty"], Level::zero()));
    // The forged type is well-formed, but it would inhabit an empty Prop.
    // The old per-parent filter never visits this row; the generated Empty
    // recursor still matches, leaving the poisoned row unchecked.
    block.ctors.push(constructor(
        name("Forged"),
        name("Foreign"),
        name("Empty"),
        0,
    ));
    assert_membership_rejection(&env, block);
    assert!(!env.contains(&name("Empty")));
    assert!(!env.contains(&name("Forged")));
}

#[test]
fn an_existing_parent_is_not_a_member_of_the_current_block() {
    let base = Environment::new();
    let foreign = finish_block(&base, empty_block(&["Foreign"], Level::zero()));
    let foreign_type = foreign.types[0].clone();
    let env = scratch_admit(
        &base,
        ConstantInfo::Induct(foreign_type.clone()),
        &foreign_type.base.name,
    )
    .expect("publish the already-checked foreign type for this fixture");
    let mut block = finish_block(&env, empty_block(&["Empty"], Level::zero()));
    block.ctors.push(constructor(
        name("Forged"),
        name("Foreign"),
        name("Empty"),
        0,
    ));
    assert_membership_rejection(&env, block);
    assert!(env.contains(&name("Foreign")));
    assert!(!env.contains(&name("Empty")));
    assert!(!env.contains(&name("Forged")));
}

#[test]
fn orphan_inventory_is_rejected_before_its_untrusted_type_is_traversed() {
    let env = Environment::new();
    let mut block = finish_block(&env, empty_block(&["Empty"], Level::zero()));
    let mut forged = constructor(name("Forged"), name("Foreign"), name("Empty"), 0);
    forged.base.type_ = Expr::bvar(0).expect("packs");
    block.ctors.push(forged);
    assert_membership_rejection(&env, block);
}

#[test]
fn synthesized_admission_cannot_bypass_constructor_membership() {
    let env = Environment::new();
    let mut block = empty_block(&["Empty"], Level::zero());
    Engine::new(&env, &block, Budget::DEFAULT)
        .expect("valid baseline")
        .run_synthesized()
        .expect("the synthesis baseline must succeed");
    block.ctors.push(constructor(
        name("Forged"),
        name("Foreign"),
        name("Empty"),
        0,
    ));
    match Engine::new(&env, &block, Budget::DEFAULT) {
        Err(Stop::Reject(RejectClass::BlockMismatch, message)) => {
            assert!(message.contains("outside the inductive block"), "{message}");
        }
        Err(other) => panic!("expected a typed membership rejection: {other:?}"),
        Ok(_) => panic!("the synthesized path admitted an orphan inventory"),
    }
}

#[test]
fn valid_mutual_constructors_may_be_interleaved_in_module_order() {
    let env = Environment::new();
    let mut block = empty_block(&["Left", "Right"], Level::one());
    for ind in &mut block.types {
        ind.ctors = vec![
            Name::str(ind.base.name.clone(), "first"),
            Name::str(ind.base.name.clone(), "second"),
        ];
    }
    for cidx in 0..2 {
        for ind in &block.types {
            block.ctors.push(constructor(
                ind.ctors[cidx as usize].clone(),
                ind.base.name.clone(),
                ind.base.name.clone(),
                cidx,
            ));
        }
    }
    let accepted = finish_block(&env, block);
    assert_eq!(accepted.ctors.len(), 4);
    assert_eq!(accepted.recursors.len(), 2);
}

#[test]
fn valid_single_constructor_still_admits() {
    let env = Environment::new();
    let mut block = empty_block(&["UnitLike"], Level::one());
    let parent = block.types[0].base.name.clone();
    let ctor_name = Name::str(parent.clone(), "mk");
    block.types[0].ctors.push(ctor_name.clone());
    block
        .ctors
        .push(constructor(ctor_name, parent.clone(), parent, 0));
    let accepted = finish_block(&env, block);
    assert_eq!(accepted.ctors.len(), 1);
}

#[test]
fn orphan_constructor_cannot_acquire_a_checked_declaration_capability() {
    use crate::capability::admit;
    use crate::council::{Council, CouncilOutcome, convene};

    let env = Environment::new();
    let mut block = finish_block(&env, empty_block(&["Empty"], Level::zero()));
    let baseline = admit(
        &env,
        crate::Declaration::Inductive(block.clone()),
        Budget::DEFAULT,
    );
    let Outcome::Complete(baseline) = baseline else {
        panic!("the valid block must complete capability admission");
    };
    assert!(matches!(
        convene(&Council::nobody_was_asked(), baseline),
        CouncilOutcome::Agreed(_)
    ));
    block.ctors.push(constructor(
        name("Forged"),
        name("Foreign"),
        name("Empty"),
        0,
    ));
    let poisoned = admit(&env, crate::Declaration::Inductive(block), Budget::DEFAULT);
    let Outcome::Complete(poisoned) = poisoned else {
        panic!("an orphan inventory must be a rejection, not a non-answer");
    };
    assert!(matches!(
        convene(&Council::nobody_was_asked(), poisoned),
        CouncilOutcome::KernelRejected {
            class: RejectClass::BlockMismatch,
            ..
        }
    ));
    assert!(!env.contains(&name("Forged")));
}

#[test]
fn nested_metadata_does_not_skip_constructor_membership() {
    let env = Environment::new();
    let mut block = finish_block(&env, empty_block(&["Empty"], Level::zero()));
    block.types[0].num_nested = 1;
    block.ctors.push(constructor(
        name("Forged"),
        name("Foreign"),
        name("Empty"),
        0,
    ));
    assert_membership_rejection(&env, block);
}

#[test]
fn unsafe_blocks_still_require_every_constructor_to_have_a_block_parent() {
    let env = Environment::new();
    let mut baseline = empty_block(&["Empty"], Level::zero());
    baseline.types[0].is_unsafe = true;
    let mut block = finish_block(&env, baseline);
    let mut forged = constructor(name("Forged"), name("Foreign"), name("Empty"), 0);
    forged.is_unsafe = true;
    block.ctors.push(forged);
    assert_membership_rejection(&env, block);
}
}
