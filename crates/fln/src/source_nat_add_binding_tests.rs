//! The arithmetic intrinsic must agree with the admitted helper closure.
//! These environments cross both admission engines; the changed functional
//! is a valid definition, not unchecked replacement of a published constant.

use super::{Engine, EngineAdmissionLimits, source_intrinsic_binding};
use fln_core::expr::{Expr, ExprNode, Literal, NatLit};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_env::constants::ConstantInfo;
use fln_env::environment::Environment;
use fln_kernel::Declaration;
use fln_kernel::verdict::Budget;

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn returning_zero(value: &Expr) -> Expr {
    let mut binders = Vec::new();
    let mut current = value;
    while let ExprNode::Lam {
        binder_name,
        binder_type,
        binder_info,
        body,
    } = current.node()
    {
        binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
        current = body;
    }
    assert_eq!(binders.len(), 3, "the actual functional has three inputs");
    let mut result = Expr::lit(Literal::Nat(NatLit::from_u64(0)));
    for (name, type_, info) in binders.into_iter().rev() {
        result = Expr::lam(name, type_, result, info);
    }
    result
}

fn admitted_addition(change_functional: bool) -> Engine {
    let mut engine = Engine::from_environment(Environment::new());
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let options = KVMap::new();
    let mut changed = false;
    for mut declaration in fln_elab::seed::source_seed_declarations() {
        if let Declaration::Defn(definition) = &mut declaration
            && definition.base.name == name("Nat.add._f")
            && change_functional
        {
            definition.value = returning_zero(&definition.value);
            changed = true;
        }
        let is_add = matches!(&declaration, Declaration::Defn(definition)
            if definition.base.name == name("Nat.add"));
        engine = engine
            .admit_declaration(declaration, &options, limits)
            .expect("each candidate is valid under both admission engines")
            .into_complete()
            .expect("both admission engines must complete")
            .engine;
        if is_add {
            assert_eq!(changed, change_functional);
            return engine;
        }
    }
    panic!("the source seed must contain the logical Nat.add definition");
}

#[test]
fn a_changed_admitted_addition_functional_cannot_receive_the_arithmetic_intrinsic() {
    let canonical = admitted_addition(false);
    let changed = admitted_addition(true);
    let add = name("Nat.add");
    let functional = name("Nat.add._f");
    assert!(matches!(
        canonical.environment().find(&add),
        Some(ConstantInfo::Defn(_))
    ));
    assert_eq!(
        canonical.environment().find(&add),
        changed.environment().find(&add),
        "the actual Nat.add body and telescope are identical"
    );
    assert_ne!(
        canonical.environment().find(&functional),
        changed.environment().find(&functional),
        "only the dependency's admitted behavior changed"
    );
    assert!(source_intrinsic_binding(canonical.environment(), &add).is_some());
    assert!(
        source_intrinsic_binding(changed.environment(), &add).is_none(),
        "a byte-identical Nat.add body must not hide a different admitted helper"
    );
}
