//! Reproduce raw native-update contract rows from the independent pin fixture.
//! No expected digest participates in choosing or traversing a declaration.
use super::*;
use fln_core::name::LeafView;
use fln_elab::externs::ExternTable;
use fln_elab::implemented_by::ImplementedByTable;

fn encoded(label: &Name) -> String {
    let mut components = Vec::new();
    let mut label = label.clone();
    loop {
        match label.leaf_view() {
            LeafView::Anonymous => break,
            LeafView::Str(text) => components.push(format!("s:{text}")),
            LeafView::Num(number) => components.push(format!("n:{number}")),
        }
        label = label.parent();
    }
    components.reverse();
    components.join("/")
}

pub(super) fn rows(environment: &Environment) -> Vec<String> {
    let implementations = ImplementedByTable::read(environment).expect("actual pin selections");
    let externs = ExternTable::read(environment).expect("actual pin externs");
    let mut pending = vec![
        name("Array.push"),
        name("Array.set"),
        name("Array.pop"),
        name("Array.modifyM"),
    ];
    let mut seen = BTreeSet::new();
    let mut seen_expressions = HashSet::new();
    let mut rows = BTreeMap::new();
    while let Some(label) = pending.pop() {
        if !seen.insert(label.clone()) {
            continue;
        }
        let info = environment
            .find(&label)
            .expect("actual closure declaration");
        let entry = environment.entry(&label).expect("actual closure entry");
        let implementation = implementations.get(&label).cloned();
        let has_body = matches!(info, ConstantInfo::Defn(value) if value.safety == DefinitionSafety::Safe)
            || matches!(info, ConstantInfo::Opaque(value) if !value.is_unsafe);
        let companion = Name::str(label.clone(), "_unsafe_rec");
        let companion = (has_body && environment.contains(&companion)).then_some(companion);
        let key = encoded(&label);
        rows.insert(
            key.clone(),
            format!(
                "{key}\t{}\t{}\t{}\t{}",
                entry.digest().to_hex(),
                implementation
                    .as_ref()
                    .map(encoded)
                    .unwrap_or_else(|| "-".to_owned()),
                if externs.get(&label).is_some() {
                    "extern"
                } else {
                    "-"
                },
                companion
                    .as_ref()
                    .map(encoded)
                    .unwrap_or_else(|| "-".to_owned()),
            ),
        );
        pending.extend(implementation);
        pending.extend(companion);
        let mut expressions = vec![&info.constant_val().type_];
        match info {
            ConstantInfo::Defn(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Opaque(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Thm(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Induct(value) => {
                pending.extend(value.all.iter().cloned());
                pending.extend(value.ctors.iter().cloned());
            }
            ConstantInfo::Ctor(value) => pending.push(value.induct.clone()),
            ConstantInfo::Rec(value) => {
                pending.extend(value.all.iter().cloned());
                pending.extend(value.rules.iter().map(|rule| rule.ctor.clone()));
                expressions.extend(value.rules.iter().map(|rule| &rule.rhs));
            }
            ConstantInfo::Axiom(_) | ConstantInfo::Quot(_) => {}
        }
        while let Some(expression) = expressions.pop() {
            if !seen_expressions.insert(expression.allocation_identity()) {
                continue;
            }
            match expression.node() {
                ExprNode::Const { name, .. } => pending.push(name.clone()),
                ExprNode::App { f, a } => expressions.extend([f, a]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => expressions.extend([binder_type, body]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => expressions.extend([type_, value, body]),
                ExprNode::Proj {
                    struct_name, expr, ..
                } => {
                    pending.push(struct_name.clone());
                    expressions.push(expr);
                }
                ExprNode::MData { expr, .. } => expressions.push(expr),
                _ => {}
            }
        }
    }
    rows.into_values().collect()
}
