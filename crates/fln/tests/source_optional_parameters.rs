//! The pin expands value defaults to `optParam` and fills omitted arguments
//! through its ordinary application elaborator (Lean/Elab/Binders.lean and
//! Lean/Elab/App.lean). No declaration is added to the source seed here.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, Environment, KVMap, Name, OleanCheckLimits,
    OleanModuleInput, Outcome, SourceCheckLimits,
};
use fln_core::expr::{Expr, ExprNode};
use fln_env::constants::ConstantInfo;
use std::path::PathBuf;

const STACK: usize = 256 * 1024 * 1024;
const OPTIONAL: &str = "universe u\n\
    abbrev optParam (α : Sort u) (default : α) : Sort u := α\n";

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)))
}

fn base() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}

fn check(engine: &Engine, source: &str) -> Engine {
    engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("complete source admission")
        .engine
}

fn checked(source: &str) -> Engine {
    check(&base(), &format!("{OPTIONAL}{source}"))
}

fn definition(engine: &Engine, name: &str) -> (Expr, Expr) {
    let Some(ConstantInfo::Defn(info)) = engine
        .environment()
        .find(&Name::from_components(name.split('.')))
    else {
        panic!("missing definition {name}");
    };
    (info.base.type_.clone(), info.value.clone())
}

fn same(engine: &Engine, left: &str, right: &str) {
    assert_eq!(
        definition(engine, left),
        definition(engine, right),
        "{left} / {right}"
    );
}

#[test]
fn declaration_defaults_preserve_checked_terms_and_dependent_values() {
    let engine = checked(
        "def addDefault (n : Nat) (step : Nat := 1) : Nat := n + step\n\
         def implicitDefault (n : Nat) : Nat := addDefault n\n\
         def explicitDefault (n : Nat) : Nat := @addDefault n 1\n\
         def overrideDefault (n : Nat) : Nat := addDefault n (step := 2)\n\
         def explicitOverride (n : Nat) : Nat := @addDefault n 2\n\
         def chain (a : Nat := 3) (b : Nat := a + 1) (c : Nat := b + 2) : Nat := a + b + c\n\
         def proofDefault (n : Nat) (h : n = n := (by rfl)) : Nat := n\n\
         def inferredDefault (n := 42) : Nat := n\n\
         def groupedDefault (x : Nat) (x y : Nat := x) : Nat := y\n\
         def polymorphicDefault (A : Type) (x : A) (y : A := x) : A := y\n\
         theorem ordinary_value : addDefault 41 = 42 := rfl\n\
         theorem override_value : addDefault 40 (step := 2) = 42 := rfl\n\
         theorem chain_value : chain = 13 := rfl\n\
         theorem proof_value : proofDefault 42 = 42 := rfl\n\
         theorem inferred_value : inferredDefault = 42 := rfl\n\
         theorem grouped_value : groupedDefault 40 42 = 42 := rfl\n\
         theorem polymorphic_value (A : Type) (x : A) : polymorphicDefault A x = x := rfl\n",
    );
    same(&engine, "implicitDefault", "explicitDefault");
    same(&engine, "overrideDefault", "explicitOverride");
    let (type_, _) = definition(&engine, "addDefault");
    let ExprNode::ForallE { body, .. } = type_.node() else {
        panic!("required first parameter");
    };
    let ExprNode::ForallE { binder_type, .. } = body.node() else {
        panic!("optional second parameter");
    };
    let ExprNode::App { f, .. } = binder_type.node() else {
        panic!("default annotation retained");
    };
    let ExprNode::App { f, .. } = f.node() else {
        panic!("optParam has its type and value");
    };
    assert!(matches!(f.node(), ExprNode::Const { name, .. }
        if name == &Name::from_components(["optParam"])));
}

#[test]
fn eta_expansion_named_arguments_and_explicit_opt_out_have_distinct_results() {
    let engine = checked(
        "def tailDefault (x : Nat) (y : Nat := 2) : Nat := x + y\n\
         def lifted : Nat → Nat := tailDefault\n\
         def explicitLifted : Nat → Nat := fun x => @tailDefault x 2\n\
         def raw : Nat → Nat → Nat := @tailDefault\n\
         def defaultBeforeRequired (x : Nat := 40) (y : Nat) : Nat := x + y\n\
         def trailing : Nat → Nat := defaultBeforeRequired\n\
         def dependentNamed (x : Nat) (y : Nat := x) : Nat := x + y\n\
         def named : Nat → Nat := dependentNamed (y := 2)\n\
         def explicitNamed : Nat → Nat := fun x => @dependentNamed x 2\n\
         def strictBoundary (x : Nat) ⦃y : Nat⦄ (z : Nat := x) : Nat := x + z\n\
         def implicitStrict := strictBoundary\n\
         def explicitStrict := fun (x : Nat) => strictBoundary x\n\
         theorem eta_value : lifted 40 = 42 := rfl\n\
         theorem explicit_value : raw 40 2 = 42 := rfl\n\
         theorem trailing_value : trailing 2 = 42 := rfl\n\
         theorem named_value : named 40 = 42 := rfl\n\
         theorem strict_value : implicitStrict 21 (y := 0) = 42 := rfl\n",
    );
    same(&engine, "lifted", "explicitLifted");
    same(&engine, "named", "explicitNamed");
    same(&engine, "implicitStrict", "explicitStrict");
    assert!(
        matches!(definition(&engine, "raw").1.node(), ExprNode::Const { name, .. }
        if name == &Name::from_components(["tailDefault"]))
    );
}

#[test]
fn pi_lambda_local_defaults_and_hygiene_share_the_same_annotation() {
    let engine = checked(
        "def arrow : (i : Nat) → (j : Nat := 3) → Nat := fun i j => i + j\n\
         def explicitArrow : (i : Nat) → (j : optParam Nat 3) → Nat := fun i j => i + j\n\
         def keepLambda : (n : optParam Nat 42) → Nat := fun n => n\n\
         def explicitLambda : (n : optParam Nat 42) → Nat := fun (n : optParam Nat 42) => n\n\
         theorem universal : ∀ (i : Nat) (j : Nat := 3), j = j := fun _ _ => rfl\n\
         def localDefault : Nat := let f (n : Nat := 42) : Nat := n; f\n\
         def localGrouped (x : Nat) : Nat := let f (x y : Nat := x) : Nat := y; f 42\n\
         namespace Shadow\n\
         def optParam : Nat := 99\n\
         def fromNamespace (n : Nat := 42) : Nat := n\n\
         end Shadow\n\
         def fromLocal (optParam : Nat) (n : Nat := optParam) : Nat := n\n\
         theorem arrow_value : arrow 39 = 42 := rfl\n\
         theorem lambda_value : keepLambda = 42 := rfl\n\
         theorem local_value : localDefault = 42 := rfl\n\
         theorem local_grouped : localGrouped 40 = 42 := rfl\n\
         theorem namespace_value : Shadow.fromNamespace = 42 := rfl\n\
         theorem local_hygiene : fromLocal 42 = 42 := rfl\n",
    );
    same(&engine, "arrow", "explicitArrow");
    same(&engine, "keepLambda", "explicitLambda");
    assert!(matches!(
        definition(&engine, "keepLambda").1.node(),
        ExprNode::Lam { .. }
    ));
}

#[test]
fn field_receivers_consume_defaults_before_resolving_methods_or_projections() {
    let engine = checked(
        "def chosen (n : Nat := 41) : Nat := n\n\
         def next : Nat := chosen.succ\n\
         def explicitNext : Nat := Nat.succ (@chosen 41)\n\
         def explicitReceiver : Nat := (@chosen).succ\n\
         def added : Nat := chosen.add 1\n\
         def explicitAdded : Nat := Nat.add (@chosen 41) 1\n\
         def localReceiver (f : (n : Nat := 41) → Nat) : Nat := f.succ\n\
         def explicitLocalReceiver (f : (n : Nat := 41) → Nat) : Nat := Nat.succ (@f 41)\n\
         structure OptionalBox where\n  value : Nat\n\
         def box (n : Nat := 42) : OptionalBox := { value := n }\n\
         def boxField : Nat := box.value\n\
         def explicitBoxField : Nat := OptionalBox.value (@box 42)\n\
         def indexedBoxField : Nat := (@box).1\n\
         theorem method_value : next = 42 := rfl\n\
         theorem applied_method_value : added = 42 := rfl\n\
         theorem indexed_value : indexedBoxField = 42 := rfl\n",
    );
    same(&engine, "next", "explicitNext");
    same(&engine, "explicitReceiver", "explicitNext");
    same(&engine, "added", "explicitAdded");
    same(&engine, "localReceiver", "explicitLocalReceiver");
    same(&engine, "boxField", "explicitBoxField");
    same(&engine, "indexedBoxField", "explicitBoxField");
}

#[test]
fn defaults_are_checked_and_failures_leave_the_predecessor_usable() {
    let engine = checked("def chosen (n : Nat := 42) : Nat := n\n");
    let root = engine.logical_root(&KVMap::new());
    for source in [
        "def wrongType (n : Nat := true) : Nat := n\n",
        "def unknownDefault (n : Nat := noSuchValue) : Nat := n\n",
        "def falseDefault (h : 0 = 1 := (by rfl)) : Nat := 0\n",
        "def unfinishedDefault (n : Nat := _) : Nat := n\n",
        "def automaticTactic (h : 0 = 0 := by rfl) : Nat := 0\n",
        "def invalidLambda : Nat → Nat := fun (n : Nat := 42) => n\n",
        "def explicitMissing : Nat := @chosen\n",
        "def wrongExpected : Nat → Nat := chosen\n",
        "def validPrefix : Nat := chosen\ntheorem falseSuffix : chosen = 43 := rfl\n",
    ] {
        let result = engine.check_source_files(&[source.as_bytes()], &KVMap::new(), limits());
        assert!(!matches!(result, Ok(Outcome::Complete(_))), "{source}");
        assert_eq!(engine.logical_root(&KVMap::new()), root);
        assert!(
            engine
                .environment()
                .find(&Name::from_components(["validPrefix"]))
                .is_none()
        );
    }
    let recovered = check(&engine, "theorem recovery : chosen = 42 := rfl\n");
    assert!(
        recovered
            .environment()
            .find(&Name::from_components(["recovery"]))
            .is_some()
    );
    let missing = base().check_source_files(
        &[b"def noOptParam (n : Nat := 42) : Nat := n\n"],
        &KVMap::new(),
        limits(),
    );
    assert!(!matches!(missing, Ok(Outcome::Complete(_))));
}

// These declarations and computation theorems were accepted by the pinned
// Lean 4.32.0. Its pp.all recursor types strip only the opened local's head:
// the recursive function field keeps its annotated domain, while its IH does not.
const INDUCTIVE_DEFAULTS: &str = r#"
inductive WithDefault where
  | mk (n : Nat) (m : Nat := 3)
def implicitCtor : WithDefault := WithDefault.mk 1
def explicitCtor : WithDefault := @WithDefault.mk 1 3
theorem rec_default : WithDefault.rec (fun _ m => m) (WithDefault.mk 1) = 3 := rfl
inductive DepDefault where
  | leaf
  | node (n : Nat := 3) (f : (m : Nat := n) → DepDefault)
theorem recursive_default : DepDefault.rec 7 (fun n _ ih => ih n) (DepDefault.node (f := fun _ => DepDefault.leaf)) = 7 := rfl
mutual
  inductive OptionalTree where
    | leaf (n : Nat := 3)
    | node (children : (n : Nat := 4) → OptionalForest)
  inductive OptionalForest where
    | nil
    | cons (head : OptionalTree) (tail : OptionalForest)
end
inductive ParameterDefault (n : Nat := 3) where
  | mk
namespace Foreign
abbrev optParam (α : Sort u) (value : α) : Sort u := α
end Foreign
inductive ForeignAnnotated where
  | mk (n : Foreign.optParam Nat 3)
"#;

fn constant_type<'a>(engine: &'a Engine, name: &str) -> &'a Expr {
    let info = engine
        .environment()
        .find(&Name::from_components(name.split('.')))
        .unwrap_or_else(|| panic!("missing {name}"));
    match info {
        ConstantInfo::Ctor(info) => &info.base.type_,
        ConstantInfo::Rec(info) => &info.base.type_,
        ConstantInfo::Induct(info) => &info.base.type_,
        _ => panic!("expected an inductive-family declaration: {name}"),
    }
}

fn domains(mut type_: &Expr) -> Vec<&Expr> {
    let mut result = Vec::new();
    while let ExprNode::ForallE {
        binder_type, body, ..
    } = type_.node()
    {
        result.push(binder_type);
        type_ = body;
    }
    result
}

fn assert_nat(type_: &Expr) {
    assert!(
        matches!(type_.node(), ExprNode::Const { name, levels }
        if name == &Name::from_components(["Nat"]) && levels.is_empty()),
        "{type_:?}"
    );
}

fn assert_annotation(type_: &Expr, annotation: &str) {
    let ExprNode::App { f, .. } = type_.node() else {
        panic!("expected {annotation} annotation: {type_:?}");
    };
    let ExprNode::App { f, a } = f.node() else {
        panic!("expected two {annotation} arguments: {type_:?}");
    };
    assert_nat(a);
    assert!(
        matches!(f.node(), ExprNode::Const { name, .. }
        if name == &Name::from_components(annotation.split('.'))),
        "{type_:?}"
    );
}

fn check_inductive_defaults(base: &Engine) {
    let engine = check(base, INDUCTIVE_DEFAULTS);
    same(&engine, "implicitCtor", "explicitCtor");
    assert_annotation(
        domains(constant_type(&engine, "WithDefault.mk"))[1],
        "optParam",
    );
    let recursor = domains(constant_type(&engine, "WithDefault.rec"));
    let minor = domains(recursor[1]);
    assert_eq!(minor.len(), 2);
    for field in minor {
        assert_nat(field);
    }
    let recursor = domains(constant_type(&engine, "DepDefault.rec"));
    let minor = domains(recursor[2]);
    assert_eq!(minor.len(), 3);
    assert_nat(minor[0]);
    assert_annotation(domains(minor[1])[0], "optParam");
    assert_nat(domains(minor[2])[0]);
    for recursor in ["OptionalTree.rec", "OptionalForest.rec"] {
        let telescope = domains(constant_type(&engine, recursor));
        assert_nat(domains(telescope[2])[0]);
        let node = domains(telescope[3]);
        assert_eq!(node.len(), 2);
        assert_annotation(domains(node[0])[0], "optParam");
        assert_nat(domains(node[1])[0]);
    }
    assert_annotation(
        domains(constant_type(&engine, "ParameterDefault"))[0],
        "optParam",
    );
    assert_nat(domains(constant_type(&engine, "ParameterDefault.rec"))[0]);
    let recursor = domains(constant_type(&engine, "ForeignAnnotated.rec"));
    assert_annotation(domains(recursor[1])[0], "Foreign.optParam");
}

#[test]
fn inductive_and_mutual_defaults_preserve_constructor_domains_and_clean_recursor_locals() {
    check_inductive_defaults(&checked(""));
}

/// The real pinned Prelude defines `Array.extract` with defaults `0` and
/// `as.size`. Its actual exported/private artifacts pass both admission seats
/// before these source declarations are elaborated; no seed enters this test.
#[test]
fn actual_imported_array_extract_defaults_match_explicit_checked_applications() {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|path| path.is_dir());
    let Some(lib) = lib else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned v4.32.0 artifacts are required"
        );
        eprintln!("SKIP: pinned v4.32.0 lib/lean is unavailable");
        return;
    };
    std::thread::Builder::new().stack_size(STACK).spawn(move || {
        let path = lib.join("Init/Prelude.olean");
        let exported = std::fs::read(&path).unwrap();
        let server = std::fs::read(path.with_extension("olean.server")).unwrap();
        let private = std::fs::read(path.with_extension("olean.private")).unwrap();
        let name = Name::from_components(["Init", "Prelude"]);
        let imported = Engine::from_environment(Environment::new())
            .import_olean_modules_for_source(
                &[OleanModuleInput {
                    name: &name,
                    artifact: &exported,
                    server_artifact: Some(&server),
                    private_artifact: Some(&private),
                }],
                std::slice::from_ref(&name),
                &KVMap::new(),
                SourceOleanImportLimits::new(OleanCheckLimits::new(
                    STACK, Budget::for_stack_bytes(STACK))),
            ).unwrap().into_complete().expect("actual Prelude admission").engine;
        let checked = check(&imported,
            "def crop (as : Array Nat) : Array Nat := as.extract\n\
             def explicitCrop (as : Array Nat) : Array Nat := @Array.extract Nat as 0 as.size\n\
             def namedCrop (as : Array Nat) (stop : Nat) : Array Nat := as.extract (stop := stop)\n\
             def explicitNamedCrop (as : Array Nat) (stop : Nat) : Array Nat := @Array.extract Nat as 0 stop\n\
             def sourceDefault (as : Array Nat) (stop : Nat := as.size) : Nat := stop\n\
             def useSourceDefault (as : Array Nat) : Nat := sourceDefault as\n\
             def explicitSourceDefault (as : Array Nat) : Nat := as.size\n");
        same(&checked, "crop", "explicitCrop");
        same(&checked, "namedCrop", "explicitNamedCrop");
        let (_, applied) = definition(&checked, "useSourceDefault");
        let (_, explicit) = definition(&checked, "explicitSourceDefault");
        assert_ne!(applied, explicit, "the named source definition remains in the term");
        let recovered = check(&checked,
            "theorem importedDefault (as : Array Nat) : useSourceDefault as = as.size := rfl\n");
        assert!(recovered.environment().find(&Name::from_components(["importedDefault"])).is_some());
        check_inductive_defaults(&imported);
        // Init.Tactics defines precisely this abbrev over the Prelude's actual
        // Lean.Syntax. This checks autoParam recursor generation, separately
        // from the still unsupported quoted tactic-default binder syntax.
        let automatic = check(&imported,
            "abbrev autoParam.{u} (α : Sort u) (tactic : Lean.Syntax) : Sort u := α\n\
             inductive Automatic where | mk (n : autoParam Nat Lean.Syntax.missing)\n\
             def automaticValue : Automatic := Automatic.mk 3\n");
        assert_annotation(domains(constant_type(&automatic, "Automatic.mk"))[0], "autoParam");
        let recursor = domains(constant_type(&automatic, "Automatic.rec"));
        assert_nat(domains(recursor[1])[0]);
    }).unwrap().join().unwrap();
}
