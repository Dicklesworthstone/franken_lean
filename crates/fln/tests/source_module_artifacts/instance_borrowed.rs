//! Borrowed parameter metadata survives declarations without changing instance keys.
#![forbid(unsafe_code)]
use super::*;
use fln::{Expr, ExprNode};
use source_extensions::DiscrTreeKey as Key;

fn assert_borrowed_count(type_: &Expr) {
    let ExprNode::MData { data, expr } = type_.node() else {
        panic!("the source borrowing annotation must remain on the declared type")
    };
    assert_eq!(data.len(), 1);
    assert!(data.get_bool(&name("borrowed"), false));
    assert_eq!(*expr, Expr::const_(name("Count"), vec![]));
}

fn assert_declared_annotations(engine: &Engine) {
    let declaration = engine.environment().find(&name("borrowed")).unwrap();
    let mut type_ = &declaration.constant_val().type_;
    for _ in 0..2 {
        let ExprNode::ForallE {
            binder_type, body, ..
        } = type_.node()
        else {
            panic!("the instance must retain its two ordinary parameters")
        };
        assert_borrowed_count(binder_type);
        type_ = body;
    }
    let ExprNode::App { a: relation, .. } = type_.node() else {
        panic!("the result must remain an application of Choice")
    };
    let mut head = relation;
    let mut arguments = Vec::new();
    while let ExprNode::App { f, a } = head.node() {
        arguments.push(a);
        head = f;
    }
    assert!(matches!(head.node(), ExprNode::Const { name: relation, .. }
        if *relation == name("Rel.rel")));
    assert_eq!(arguments.len(), 4);
    // As in the unchanged Prelude Nat.decLe/decLt declarations, inference
    // propagates the borrowed domain to the relation's explicit type argument.
    assert_borrowed_count(arguments[3]);
}

#[test]
fn borrowed_instance_parameters_preserve_exact_keys_and_physical_dictionary_selection() {
    let source = r#"prelude
inductive Token where
  | left
  | right
inductive Count where
  | zero
  | succ (n : Count)
inductive Below (n m : Count) : Prop where
  | intro
class Rel (A : Type) where
  rel : A -> A -> Prop
instance countRel : Rel Count := Rel.mk Below
class Choice (p : Prop) where
  value : Token
instance (priority := 500) fallback (n m : Count) : Choice (Rel.rel n m) := Choice.mk Token.left
instance (priority := 2000) borrowed (n m : @& Count) : Choice (Rel.rel n m) := Choice.mk Token.right
"#;
    let built = compiled(&[("Main", source)]);
    let rows = metadata(&built.artifacts[0].bytes).instances;
    assert_eq!(rows.len(), 3);
    let expected_keys = [
        Key::Const(name("Choice"), 1),
        Key::Const(name("Rel.rel"), 4),
        Key::Const(name("Count"), 0),
        Key::Star,
        Key::Star,
        Key::Star,
    ];
    for (declaration, priority) in [("fallback", 500), ("borrowed", 2000)] {
        let row = rows
            .iter()
            .find(|row| row.declaration == name(declaration))
            .unwrap();
        assert_eq!(row.keys, expected_keys);
        assert!(row.synth_order.is_empty());
        assert_eq!(row.priority, priority);
        assert!(row.scope.is_none());
    }
    let receipt = imported(&built);
    assert_eq!(receipt.modules[0].instances, 3);
    let consumer = "def chosen : Token := Choice.value (p := Rel.rel Count.zero (Count.succ Count.zero))\ntheorem correct (P : Token -> Prop) (h : P Token.right) : P chosen := h";
    let refused = "def chosen : Token := Choice.value (p := Rel.rel Count.zero (Count.succ Count.zero))\ntheorem wrong (P : Token -> Prop) (h : P Token.left) : P chosen := h";
    for engine in [&built.checked.checked.engine, &receipt.engine] {
        assert_declared_annotations(engine);
        let root = engine.logical_root(&KVMap::new());
        engine
            .check_source_files(&[consumer.as_bytes()], &KVMap::new(), limits().source)
            .unwrap()
            .into_complete()
            .unwrap();
        assert!(
            engine
                .check_source_files(&[refused.as_bytes()], &KVMap::new(), limits().source)
                .is_err()
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
        assert!(!engine.environment().contains(&name("chosen")));
    }
    for (probe, accepted) in [(consumer, true), (refused, false)] {
        aliases::reference_import(
            &built,
            &format!("prelude\nimport Main\nnoncomputable section\n{probe}"),
            accepted,
        );
    }
}
