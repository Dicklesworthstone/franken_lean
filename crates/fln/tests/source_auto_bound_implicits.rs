//! Auto-bound implicits in a definition header, as the pin binds them (`withAutoBoundImplicit`,
//! Lean/Elab/Term/TermElabM.lean:1932-1955; `checkValidAutoBoundImplicitName`,
//! Lean/Elab/AutoBound.lean:31-63). Every program here was run through the pinned `lean`
//! v4.32.0 first (2026-10-11), and each signature is its `#check @f`.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_core::expr::{BinderInfo, Expr, ExprNode};
use fln_env::constants::ConstantInfo;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(source: &str) -> Engine {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
        .engine
}
fn refused(source: &str) -> String {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let Err(error) = base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    ) else {
        panic!("accepted: {source}");
    };
    assert_eq!(base.logical_root(&KVMap::new()), root);
    format!("{error:?} {error}")
}
/// The leading binders of a declaration's type: name, style and domain.
fn binders(engine: &Engine, name: &str, count: usize) -> Vec<(String, BinderInfo, Expr)> {
    let info = engine
        .environment()
        .find(&Name::from_components(name.split('.')))
        .unwrap_or_else(|| panic!("{name} not declared"));
    let ConstantInfo::Defn(definition) = info else {
        panic!("{name} is not a definition");
    };
    let mut type_ = &definition.base.type_;
    let mut found = Vec::new();
    for _ in 0..count {
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = type_.node()
        else {
            panic!("{name}: fewer than {count} binders");
        };
        found.push((
            binder_name.to_display_string(),
            *binder_info,
            binder_type.clone(),
        ));
        type_ = body;
    }
    found
}
fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_components([name]), vec![])
}

/// `@idα : {α : Sort u_1} → α → α`, `@vlen : {α : Type} → {n : Nat} → Vec α n → Nat`: each
/// unknown header name becomes a leading implicit binder, in order of appearance, typed by its use.
#[test]
fn unknown_header_names_become_leading_implicit_binders() {
    let engine = checked(
        "inductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A 0\n  | cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (n + 1)\n\
         def idα (x : α) : α := x\n\
         theorem idα_ok : idα (3 : Nat) = 3 := rfl\n\
         def vlen (v : Vec α n) : Nat := n\n\
         theorem vlen_ok : vlen (Vec.cons 0 true Vec.nil) = 1 := rfl\n",
    );
    let id = binders(&engine, "idα", 2);
    assert_eq!(id[0].0, "α");
    assert_eq!(id[0].1, BinderInfo::Implicit);
    assert!(
        matches!(id[0].2.node(), ExprNode::Sort { .. }),
        "{:?}",
        id[0].2
    );
    assert_eq!(id[1].1, BinderInfo::Default);
    let vlen = binders(&engine, "vlen", 3);
    assert_eq!(
        vlen.iter()
            .map(|(name, style, _)| (name.as_str(), *style))
            .collect::<Vec<_>>(),
        [
            ("α", BinderInfo::Implicit),
            ("n", BinderInfo::Implicit),
            ("v", BinderInfo::Default)
        ]
    );
    assert_eq!(vlen[1].2, constant("Nat"));
}

/// Strict names with a suffix of digits, subscripts, `_` or `'`, and a theorem's header.
#[test]
fn strict_names_with_suffixes_and_theorem_headers_are_bound() {
    checked("def k (x : α₁) (y : β') : α₁ := x\ntheorem refl_any (x : α) : x = x := rfl\n");
}

/// `set_option autoImplicit false` restores the unknown identifier (the pin: "Unknown identifier
/// `β`", 2:11), the definition's own name is never bound (1:11), and an auto whose type would be
/// a later binder is refused (the pin: "Type mismatch", 1:36).
#[test]
fn the_option_the_own_name_and_later_binders_refuse_as_at_the_pin() {
    let off = refused("set_option autoImplicit false in\ndef g (x : β) : β := x\n");
    assert!(off.contains("Unknown identifier `β`"), "{off}");
    let own = refused("def α (x : α) : Nat := 0\n");
    assert!(own.contains("Unknown identifier `α`"), "{own}");
    refused("def bad (A : Type) (x : A) (h : x = y) : Nat := 0\n");
}
