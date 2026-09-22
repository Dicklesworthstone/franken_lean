//! Section data declarations remain ordinary candidates for both checking engines.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_core::expr::{BinderInfo, ExprNode};
use fln_env::constants::ConstantInfo;

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
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap()
        .engine
}
fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn params(e: &Engine, name: &str) -> Vec<(Name, BinderInfo)> {
    let ConstantInfo::Induct(family) = e.environment().find(&n(name)).unwrap() else {
        panic!("not inductive")
    };
    let mut ty = family.base.type_.clone();
    let mut out = Vec::new();
    for _ in 0..family.num_params {
        let ExprNode::ForallE {
            binder_name,
            binder_info,
            body,
            ..
        } = ty.node()
        else {
            panic!("missing parameter")
        };
        out.push((binder_name.clone(), *binder_info));
        ty = body.clone();
    }
    out
}

#[test]
fn field_only_parameters_close_recursive_references_and_support_recursion() {
    let e = checked(
        &engine(),
        r#"section
variable (A : Type u) (unused : Nat)
inductive Chain where
  | nil
  | cons (head : A) (tail : Chain)
end
def sum (xs : Chain Nat) : Nat := match xs with
  | .nil => 0
  | .cons n tail => n + sum tail
theorem computes : sum (Chain.cons 20 (Chain.cons 22 Chain.nil)) = 42 := by rfl"#,
    );
    assert_eq!(params(&e, "Chain"), vec![(n("A"), BinderInfo::Default)]);
    assert!(!e.environment().contains(&n("A")));
    assert!(!e.environment().contains(&n("unused")));
}

#[test]
fn constructor_types_select_transitive_term_and_universe_dependencies() {
    let e = checked(
        &engine(),
        r#"section
variable {A : Type u} (unused : Nat) (family : A -> Type v) (x : A)
inductive Choice where
  | mk (value : family x)
inductive Independent where | unit
end
def value : Choice (fun n : Nat => Nat) 7 := Choice.mk 42
theorem works : value = Choice.mk 42 := by rfl"#,
    );
    assert_eq!(
        params(&e, "Choice"),
        vec![
            (n("A"), BinderInfo::Implicit),
            (n("family"), BinderInfo::Default),
            (n("x"), BinderInfo::Default),
        ]
    );
    assert!(params(&e, "Independent").is_empty());
    assert_eq!(
        e.environment()
            .find(&n("Choice"))
            .unwrap()
            .constant_val()
            .level_params
            .as_slice(),
        &[n("u"), n("v")]
    );
}

#[test]
fn indexed_recursive_families_retain_section_parameters_and_exact_results() {
    let e = checked(
        &engine(),
        r#"section
variable (A : Type)
inductive Vec : Nat -> Type where
  | nil : Vec 0
  | cons (n : Nat) (head : A) (tail : Vec n) : Vec (Nat.succ n)
end
def two : Vec Nat 2 := Vec.cons 1 20 (Vec.cons 0 22 Vec.nil)
theorem same : two = Vec.cons 1 20 (Vec.cons 0 22 Vec.nil) := by rfl"#,
    );
    assert_eq!(params(&e, "Vec"), vec![(n("A"), BinderInfo::Default)]);
    for bad in [
        "def bad : Vec Nat 1 := Vec.nil",
        "def bad : Vec Nat 1 := Vec.cons 0 true Vec.nil",
    ] {
        assert!(
            e.check_source_files(&[bad.as_bytes()], &KVMap::new(), limits())
                .is_err()
        );
    }
}

#[test]
fn constructor_index_inference_captures_only_the_required_local_dictionary() {
    let e = checked(
        &engine(),
        r#"section
variable {A : Type} [inh : Inhabited A] (unused : Nat)
inductive AtDefault : A -> Type where
  | mk : AtDefault default
end
def atZero : AtDefault (A := Nat) 0 := AtDefault.mk (A := Nat)
theorem same : atZero = AtDefault.mk (A := Nat) := by rfl"#,
    );
    assert_eq!(
        params(&e, "AtDefault"),
        vec![
            (n("A"), BinderInfo::Implicit),
            (n("inh"), BinderInfo::InstImplicit),
        ]
    );
}

#[test]
fn proposition_families_and_shadowed_written_parameters_do_not_gain_assumptions() {
    let e = checked(
        &engine(),
        r#"section
variable (p : Prop) (unused : False) (A : Type)
include unused
inductive Wrap : Prop where | intro (h : p)
inductive Shadow (A : Type) where | mk (value : A)
end
theorem unwrap (p : Prop) (w : Wrap p) : p := by
  cases w with
  | intro h => exact h
def value : Shadow Nat := Shadow.mk 42"#,
    );
    assert_eq!(params(&e, "Wrap"), vec![(n("p"), BinderInfo::Default)]);
    assert_eq!(params(&e, "Shadow"), vec![(n("A"), BinderInfo::Default)]);
}

#[test]
fn mutually_recursive_families_share_sibling_only_section_dependencies() {
    let e = checked(
        &engine(),
        r#"section
variable (A : Type u) (unused : Nat)
mutual
  inductive Tree where | node (children : Forest)
  inductive Forest where | nil | leaf (value : A) | cons (head : Tree) (tail : Forest)
end
end
def tree : Tree Nat := Tree.node (Forest.leaf 42)
def inspect (t : Tree Nat) : Nat := match t with
  | .node children => match children with
    | .nil => 0
    | .leaf n => n
    | .cons head tail => 1
theorem computes : inspect tree = 42 := by rfl"#,
    );
    for name in ["Tree", "Forest"] {
        assert_eq!(params(&e, name), vec![(n("A"), BinderInfo::Default)]);
    }
}

#[test]
fn mutual_written_parameters_keep_section_dependencies_while_rebinding_names() {
    let e = checked(
        &engine(),
        r#"namespace Nested
section
variable (A : Type u) (P : A -> Type v) (unused : Nat)
mutual
  inductive Tree (x : A) where
    | leaf (value : P x)
    | node (children : Forest x)
  inductive Forest (y : A) where
    | nil
    | cons (head : Tree y) (tail : Forest y)
end
end
end Nested
def tree : Nested.Tree Nat (fun n => Bool) 7 := Nested.Tree.leaf true
def forest : Nested.Forest Nat (fun n => Bool) 7 := Nested.Forest.cons tree Nested.Forest.nil
theorem same : forest = Nested.Forest.cons tree Nested.Forest.nil := by rfl"#,
    );
    // The mutual generator uses the first member's shared parameter names.
    for name in ["Nested.Tree", "Nested.Forest"] {
        assert_eq!(
            params(&e, name),
            vec![
                (n("A"), BinderInfo::Default),
                (n("P"), BinderInfo::Default),
                (n("x"), BinderInfo::Default),
            ]
        );
    }
}

#[test]
fn mutual_index_telescopes_can_read_the_captured_section_context() {
    let e = checked(
        &engine(),
        r#"section
variable (A : Type)
mutual
  inductive Tree : A -> Type where
    | node (x : A) (children : Forest x) : Tree x
  inductive Forest : A -> Type where
    | nil (x : A) : Forest x
    | cons (x : A) (head : Tree x) (tail : Forest x) : Forest x
end
end
def forest : Forest Nat 7 := Forest.cons 7 (Tree.node 7 (Forest.nil 7)) (Forest.nil 7)"#,
    );
    for name in ["Tree", "Forest"] {
        assert_eq!(params(&e, name), vec![(n("A"), BinderInfo::Default)]);
    }
}

#[test]
fn invalid_inductive_groups_preserve_the_original_environment_and_can_retry() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "variable (A : Type)\ninductive Bad where | bad (f : Bad -> A)",
        "variable (A : Type)\ninductive Bad : A -> Type where | bad : Bad true",
        "variable (A : Type)\ninductive Bad where | bad : (Bad : Prop)",
        "section\nvariable (A : Type)\nend\ninductive Bad where | bad (x : A)",
        "variable (A : Type)\nmutual\ninductive T where | node (f : F -> A)\ninductive F where | nil\nend",
        "variable (A : Type)\nmutual\ninductive T (x : A) where | node (f : F A)\ninductive F (B : Type) where | nil\nend",
        "variable (A : Type)\nmutual\ninductive T where | node (f : F)\ninductive F where | nil : (F : Prop)\nend",
        "variable (A : Type)\nmutual\ninductive T where | node (f : F)\ninductive F where | leaf (x : A)\nend\ntheorem wrong : 0 = 1 := by rfl",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        for name in ["A", "Bad", "Bad.rec", "T", "F", "T.node", "F.rec"] {
            assert!(!base.environment().contains(&n(name)));
        }
    }
    checked(
        &base,
        "variable (A : Type)\ninductive Good where | mk (x : A)",
    );
}

#[test]
fn captured_parameters_count_in_single_and_mutual_generator_limits() {
    use fln_elab::{
        NatDefinitionElabError,
        records::RecordBudget,
        source::{
            SourceInferenceError,
            scope::{self, SourceScope},
        },
    };
    use fln_parse::command_scope::ScopeCommand;
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let Some(ScopeCommand::Variable(syntax)) =
        fln_parse::command_scope::parse(b"variable (A : Type)").unwrap()
    else {
        panic!("variable syntax")
    };
    let mut scope = SourceScope::default();
    scope.variables = scope::variables::declare(
        &syntax,
        base.environment(),
        limits().admission.kernel,
        &scope,
    )
    .unwrap();
    let source = fln_parse::parse_definition(b"inductive T where | mk (x : A)").unwrap();
    let small = RecordBudget {
        max_binders: 2,
        ..RecordBudget::default()
    };
    let error = scope::elaborate_inductive(
        source.syntax(),
        base.environment(),
        limits().admission.kernel,
        small,
        &scope,
    )
    .unwrap_err();
    assert!(
        matches!(
            error,
            NatDefinitionElabError::Inference(SourceInferenceError::Inductive(
                fln_elab::inductive::InductiveError::ResourceLimit
            ))
        ),
        "{error:?}"
    );
    let exact = RecordBudget {
        max_binders: 3,
        ..small
    };
    let candidate = scope::elaborate_inductive(
        source.syntax(),
        base.environment(),
        limits().admission.kernel,
        exact,
        &scope,
    )
    .unwrap();
    base.admit_declaration(candidate, &KVMap::new(), limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let sources = [
        "inductive T where | mk (x : A)",
        "inductive F where | mk (t : T)",
    ];
    let syntax = sources
        .iter()
        .map(|s| {
            fln_parse::parse_definition(s.as_bytes())
                .unwrap()
                .syntax()
                .clone()
        })
        .collect::<Vec<_>>();
    let small = RecordBudget {
        max_binders: 5,
        ..small
    };
    let error = scope::elaborate_mutual_inductives(
        &syntax,
        base.environment(),
        limits().admission.kernel,
        small,
        &scope,
    )
    .unwrap_err();
    assert!(
        matches!(
            error,
            NatDefinitionElabError::Inference(SourceInferenceError::Inductive(
                fln_elab::inductive::InductiveError::ResourceLimit
            ))
        ),
        "{error:?}"
    );
    let exact = RecordBudget {
        max_binders: 6,
        ..small
    };
    let candidate = scope::elaborate_mutual_inductives(
        &syntax,
        base.environment(),
        limits().admission.kernel,
        exact,
        &scope,
    )
    .unwrap();
    base.admit_declaration(candidate, &KVMap::new(), limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(base.logical_root(&KVMap::new()), root);
}
