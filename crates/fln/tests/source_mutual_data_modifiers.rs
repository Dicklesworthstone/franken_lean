//! Documented and private mutually inductive families use atomic native admission.
#![forbid(unsafe_code)]

use fln::source_check::modules::SourceModuleCheckLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
    SourceModuleInput,
};
use fln_env::constants::ConstantInfo;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
        .engine
}
const FAMILIES: &str = r#"mutual
  /-- The tree may refer forward to its forest. -/
  inductive Tree (A : Type) where
    | leaf (value : A)
    | node (children : Forest A)
  /-- The forest refers back to the tree; `end` here is doc text. -/
  inductive Forest (A : Type) where
    | nil
    | cons (head : Tree A) (tail : Forest A)
end
"#;

#[test]
fn documented_families_generate_reusable_constructors_and_both_recursors() {
    let base = checked(&engine(), FAMILIES);
    for text in ["Tree", "Forest"] {
        assert!(matches!(base.environment().find(&n(text)),
            Some(ConstantInfo::Induct(info)) if info.all.len() == 2 && info.num_params == 1));
        assert!(
            matches!(base.environment().find(&n(&format!("{text}.rec"))),
            Some(ConstantInfo::Rec(info)) if info.num_motives == 2)
        );
    }
    let source = "def tree : Tree Nat := Tree.node (Forest.cons (Tree.leaf 7) Forest.nil)\ndef unpack (tree : Tree Nat) : Nat := match tree with | Tree.leaf n => n | Tree.node _ => 19\n#eval unpack tree";
    let executed = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(result) = &executed.executions.last().unwrap().exit else {
        panic!("VM result");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some("19")
    );
}

#[test]
fn explicit_private_families_keep_generated_names_inside_the_module() {
    let base = engine();
    let name = n("Main");
    let source = format!(
        "module\nprelude\nnamespace Local\n{}\ndef localTree : Tree Nat := Tree.node Forest.nil\nend Local",
        FAMILIES.replace("  inductive", "  private inductive")
    );
    let checked = base
        .check_source_modules(
            &[SourceModuleInput {
                name: &name,
                source: source.as_bytes(),
            }],
            &name,
            &KVMap::new(),
            SourceModuleCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{error:?}"))
        .into_complete()
        .unwrap();
    for text in [
        "Local.Tree",
        "Local.Forest",
        "Local.Tree.rec",
        "Local.Forest.rec",
        "Local.Tree.leaf",
        "Local.localTree",
    ] {
        let private = Name::num(n("_private.Main"), 0).append_core(&n(text));
        assert!(
            checked.checked.engine.environment().contains(&private),
            "{text}"
        );
        assert!(
            !checked.checked.engine.environment().contains(&n(text)),
            "{text}"
        );
        assert!(!base.environment().contains(&private));
    }
}

#[test]
fn documented_indexed_families_still_prove_through_the_ordinary_checkers() {
    let source = r#"mutual
  /-- Zero is even; successors refer to the opposite predicate. -/
  inductive Even : Nat -> Prop where
    | zero : Even 0
    | succ (n : Nat) : Odd n -> Even (n + 1)
  /-- This is not a constructor comment or a separate command. -/
  inductive Odd : Nat -> Prop where
    | succ (n : Nat) : Even n -> Odd (n + 1)
end
theorem two : Even 2 := Even.succ 1 (Odd.succ 0 Even.zero)
"#;
    let compiled = checked(&engine(), source);
    assert!(compiled.environment().contains(&n("two")));
    assert!(
        compiled
            .check_source_files(
                &[b"theorem false_even : Even 1 := Even.zero"],
                &KVMap::new(),
                limits()
            )
            .is_err()
    );
}

#[test]
fn documented_negative_and_mixed_groups_do_not_publish_any_member() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "mutual\n/-- a -/\ninductive Tree where | bad (f : Forest -> Nat)\n/-- b -/\ninductive Forest where | nil | back (t : Tree)\nend",
        "mutual\n/-- a -/\ninductive Tree where | leaf\n/-- b -/\npartial def Forest : Nat := 7\nend",
        "mutual\n/-- a -/\npartial def Tree : Nat := 7\n/-- b -/\ninductive Forest where | leaf\nend",
        "mutual\n/-- a -/\ninductive Tree where | leaf\nnamespace Hidden\nend\nend",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert!(!base.environment().contains(&n("Tree")));
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    checked(&base, FAMILIES);
}

#[test]
fn private_mutual_families_and_partial_consumers_execute_in_the_module_world() {
    use fln::source_check::modules::{execution::SourceProgramLimits, imported::SourceOleanImport};
    let options = KVMap::new();
    let imported = SourceOleanImport::empty(&options);
    let name = n("Main");
    let support = n("Support");
    // Supply real, checked support declarations instead of exporting an ambient seed.
    let support_source = b"prelude\nuniverse u\nclass Inhabited (A : Sort u) where\n default : A\ndef default {A : Sort u} [inst : Inhabited A] : A := Inhabited.default\n";
    let source = r#"module
prelude
import Support
mutual
  /-- Trees and forests are private recursive library data. -/
  private inductive Tree where | leaf | node (xs : Forest)
  /-- The backwards family edge is checked in the same group. -/
  private inductive Forest where | nil | cons (head : Tree) (tail : Forest)
end
mutual
  /-- The parameter provides a logical inhabitant, not the runtime result. -/
  private partial def first (fallback : Tree) (xs : Forest) : Tree := match xs with
    | Forest.nil => fallback
    | Forest.cons head tail => second head tail
  private partial def second (fallback : Tree) (xs : Forest) : Tree := match xs with
    | Forest.nil => fallback
    | Forest.cons head tail => first head tail
end
#eval first Tree.leaf (Forest.cons (Tree.node Forest.nil) Forest.nil)
"#;
    let execute = |source: &str| {
        imported.execute_source_modules(
            &[
                SourceModuleInput {
                    name: &name,
                    source: source.as_bytes(),
                },
                SourceModuleInput {
                    name: &support,
                    source: support_source,
                },
            ],
            &name,
            &options,
            SourceProgramLimits::new(EngineExecutionLimits::new(limits().admission.kernel)),
            None,
        )
    };
    let program = execute(source)
        .unwrap_or_else(|error| panic!("{error:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(program.modules.len(), 2);
    assert_eq!(program.modules[1].module, name);
    let batch = &program.modules[1].commands.batch;
    let result = &batch.executions.last().unwrap().exit;
    let fln::VmExit::Returned(result) = result else {
        panic!("expected completed private execution")
    };
    assert_eq!(
        fln::vm_value_kind(&result.value),
        fln_vm::interpreter::ValueKind::Ctor(1)
    );
    // Even this true runtime equality is not definitional equality through a partial interface.
    let bad = format!(
        "{source}\ntheorem invalid : first Tree.leaf (Forest.cons (Tree.node Forest.nil) Forest.nil) = Tree.node Forest.nil := by rfl\n"
    );
    assert!(execute(&bad).is_err());
    execute(source).unwrap().into_complete().unwrap();
}
