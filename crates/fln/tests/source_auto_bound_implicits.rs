//! Auto-bound implicits in a definition header, as the pin binds them (`withAutoBoundImplicit`,
//! Lean/Elab/Term/TermElabM.lean:1932-1955; `checkValidAutoBoundImplicitName`,
//! Lean/Elab/AutoBound.lean:31-63). Every program here was run through the pinned `lean`
//! v4.32.0 first (2026-10-11), and each signature is its `#check @f`.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_core::expr::{BinderInfo, Expr, ExprNode};

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
    let mut type_ = &info.constant_val().type_;
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

/// Inductive, constructor and structure/class headers bind as the pin's `#check` shows:
/// `@G : {n : Nat} → F n → Type`, `@V.cons : {α : Type} → {n : Nat} → α → V α n → V α (n + 1)`,
/// `@Box : {α : Sort u_1} → α → Type`, `@OpAssoc : {α : Sort u_1} → (α → α → α) → Prop`.
#[test]
fn inductive_constructor_and_structure_headers_bind_leading_implicits() {
    let engine = checked(
        "inductive F : Nat → Type where\n  | mk (n : Nat) : F n\n\
         inductive G : F n → Type where\n  | mk : G (F.mk n)\n\
         inductive V (α : Type) : Nat → Type where\n  | nil : V α 0\n  | cons (x : α) (xs : V α n) : V α (n + 1)\n\
         structure Box (x : α) where\n  val : Nat\n\
         class OpAssoc (op : α → α → α) : Prop where\n  assoc : ∀ a b c, op (op a b) c = op a (op b c)\n",
    );
    let styles = |name: &str, count: usize| {
        binders(&engine, name, count)
            .into_iter()
            .map(|(name, style, _)| (name, style))
            .collect::<Vec<_>>()
    };
    let implicit = |name: &str| (name.to_owned(), BinderInfo::Implicit);
    assert_eq!(styles("G", 1), [implicit("n")]);
    assert_eq!(binders(&engine, "G", 1)[0].2, constant("Nat"));
    assert_eq!(styles("V.cons", 2), [implicit("α"), implicit("n")]);
    assert_eq!(binders(&engine, "V.cons", 2)[1].2, constant("Nat"));
    assert_eq!(styles("Box", 1), [implicit("α")]);
    assert_eq!(styles("OpAssoc", 1), [implicit("α")]);
}

/// A universe hole in an inductive family's telescope, from `Type _`, `Sort _` or an auto-bound
/// implicit, becomes a level parameter once the constructors are elaborated, as the pin's
/// `levelMVarToParamAtInductives` makes it. Each expectation is the pinned v4.32.0's
/// `#check @c` under `pp.universes`.
#[test]
fn inductive_universe_holes_become_level_parameters() {
    let engine = checked(
        "inductive T (α : Type _) where\n  | mk : α → T α\n\
         inductive Mem (a : α) : α → Prop where\n  | refl : Mem a a\n\
         inductive Opt (α : Sort _) where\n  | none\n  | some (x : α)\n\
         inductive Two (α : Type _) (β : Sort _) where\n  | mk (x : α) (y : β)\n\
         inductive L (α : Type u) where\n  | nil\n  | cons (a : α) (t : L α)\n\
         inductive V (α : Sort _) where\n  | mk (xs : L α) : V α\n\
         mutual\ninductive Ev (α : Type _) where\n  | nil : Ev α\n  | cons : α → Od α → Ev α\n\
         inductive Od (α : Type _) where\n  | cons : α → Ev α → Od α\nend\n",
    );
    let environment = engine.environment();
    let mut printer = fln::pretty::Printer::new(environment);
    for (name, levels, type_) in [
        ("T", "u_1", "Type u_1 → Type u_1"),
        ("T.mk", "u_1", "{α : Type u_1} → α → T α"),
        ("Mem", "u_1", "{α : Sort u_1} → α → α → Prop"),
        ("Mem.refl", "u_1", "∀ {α : Sort u_1} {a : α}, Mem a a"),
        ("Opt", "u_1", "Sort u_1 → Sort (max 1 u_1)"),
        ("Opt.some", "u_1", "{α : Sort u_1} → α → Opt α"),
        (
            "Two",
            "u_1 u_2",
            "Type u_1 → Sort u_2 → Sort (max (u_1 + 1) u_2)",
        ),
        (
            "Two.mk",
            "u_1 u_2",
            "{α : Type u_1} → {β : Sort u_2} → α → β → Two α β",
        ),
        // A constructor may constrain the hole first: `L α` makes `α : Sort ?u` a `Type`.
        ("V", "u_1", "Type u_1 → Type u_1"),
        ("V.mk", "u_1", "{α : Type u_1} → L α → V α"),
        // Members of a mutual block generalize their equal headers to the same parameter.
        ("Ev", "u_1", "Type u_1 → Type u_1"),
        ("Ev.cons", "u_1", "{α : Type u_1} → α → Od α → Ev α"),
        ("Od.cons", "u_1", "{α : Type u_1} → α → Ev α → Od α"),
    ] {
        let info = environment
            .find(&Name::from_components(name.split('.')))
            .unwrap_or_else(|| panic!("{name} not declared"));
        let declared: Vec<_> = info
            .constant_val()
            .level_params
            .iter()
            .map(Name::to_display_string)
            .collect();
        assert_eq!(declared.join(" "), levels, "{name}");
        assert_eq!(
            printer.expr(&info.constant_val().type_, 0).unwrap(),
            type_,
            "{name}"
        );
    }
}

/// A universe hole only a constructor or a field mentions is not a parameter at the pin: it is
/// fitted to the family's universe or defaulted (`inductive T | mk (β : Type _)` is `T : Type 1`,
/// and `structure S where β : Type _` rejects `⟨Type⟩`). Generalizing it would accept that
/// program, so it stays refused.
#[test]
fn a_universe_hole_no_header_mentions_is_refused() {
    for source in [
        "inductive T where\n  | mk (β : Type _) : T\n",
        "inductive U (α : Type _) where\n  | mk (β : Sort _) (x : α) : U α\n",
        "mutual\ninductive A where\n  | mk (β : Type _) : A\ninductive B where\n  | mk : A → B\nend\n",
        "structure S where\n  β : Type _\n",
        "structure S where\n  β : Type _\nexample : S := ⟨Type⟩\n",
    ] {
        let error = refused(source);
        assert!(error.contains("UnresolvedUniverses"), "{source}\n{error}");
    }
}

/// A structure or class parent keeps its parameters' universe holes until the record
/// generalizes its whole telescope, as for its own fields. Expectations are the pinned
/// v4.32.0's `#check @c` under `pp.universes`.
#[test]
fn structure_parents_keep_universe_holes_for_the_record_to_generalize() {
    let engine = checked(
        "class Pointed (α : Sort u) where\n  point : α\n\
         class Foo (α : Type _) extends Pointed α\n\
         structure S (α : Type _) extends Pointed α where\n  y : α\n\
         class F (α : Sort _) extends Pointed α\n",
    );
    let environment = engine.environment();
    let mut printer = fln::pretty::Printer::new(environment);
    for (name, levels, type_) in [
        ("Foo", "u_1", "Type u_1 → Type u_1"),
        (
            "Foo.toPointed",
            "u_1",
            "{α : Type u_1} → [self : Foo α] → Pointed α",
        ),
        ("S", "u_1", "Type u_1 → Type u_1"),
        ("S.mk", "u_1", "{α : Type u_1} → Pointed α → α → S α"),
        ("F", "u_1", "Sort u_1 → Sort (max 1 u_1)"),
        (
            "F.toPointed",
            "u_1",
            "{α : Sort u_1} → [self : F α] → Pointed α",
        ),
    ] {
        let info = environment
            .find(&Name::from_components(name.split('.')))
            .unwrap_or_else(|| panic!("{name} not declared"));
        let declared: Vec<_> = info
            .constant_val()
            .level_params
            .iter()
            .map(Name::to_display_string)
            .collect();
        assert_eq!(declared.join(" "), levels, "{name}");
        assert_eq!(
            printer.expr(&info.constant_val().type_, 0).unwrap(),
            type_,
            "{name}"
        );
    }
}

/// A header's binder group gives each name its own copy of the type, as the pin's `toBinderViews`
/// does: two universe holes for `(A B : Type _)`, two type holes for `{α β}`. One shared hole
/// refused `pair Nat (Type)`, which the pinned v4.32.0 accepts. Each expectation is its `#check @c`
/// under `pp.universes`.
#[test]
fn a_header_binder_group_elaborates_its_type_for_each_name() {
    let engine = checked(
        "def pair (A B : Type _) (a : A) (b : B) : A := a\n\
         example : Nat := pair Nat (Type) 1 Nat\n\
         class Funny (F : Type _) (A B : outParam (Type _)) where\n  toFun : F → A → B\n\
         def keep {α β} (a : α) (b : β) : α := a\n",
    );
    let environment = engine.environment();
    let mut printer = fln::pretty::Printer::new(environment);
    for (name, levels, type_) in [
        (
            "pair",
            "u_1 u_2",
            "(A : Type u_1) → (B : Type u_2) → A → B → A",
        ),
        (
            "Funny.toFun",
            "u_1 u_2 u_3",
            "{F : Type u_1} → {A : outParam (Type u_2)} → {B : outParam (Type u_3)} → [self : Funny F A B] → F → A → B",
        ),
        (
            "keep",
            "u_1 u_2",
            "{α : Sort u_1} → {β : Sort u_2} → α → β → α",
        ),
    ] {
        let info = environment
            .find(&Name::from_components(name.split('.')))
            .unwrap_or_else(|| panic!("{name} not declared"));
        let declared: Vec<_> = info
            .constant_val()
            .level_params
            .iter()
            .map(Name::to_display_string)
            .collect();
        assert_eq!(declared.join(" "), levels, "{name}");
        assert_eq!(
            printer.expr(&info.constant_val().type_, 0).unwrap(),
            type_,
            "{name}"
        );
    }
}

/// `Type` takes a level only at leading precedence, as the pin's `checkPrec leadPrec` in
/// `Lean.Parser.Term.type`: `pair Nat Type 1 Nat` passes `Type` and `1` as two arguments, while
/// `Type 1` heading a term, after `:=`, before `→` or in parentheses takes it. The pinned v4.32.0
/// accepts all of this program.
#[test]
fn a_sort_takes_its_level_only_in_leading_position() {
    checked(
        "def pair (A B : Type _) (a : A) (b : B) : A := a\n\
         example : Nat := pair Nat Type 1 Nat\n\
         example : Type 2 := Type 1\n\
         example : Type 1 → Type 1 := fun x => x\n\
         def wrap (A : Type 2) := A\n\
         example : Type 2 := wrap (Type 1)\n",
    );
}

/// `variable (R : α → α → Prop)` makes `α` an implicit variable, included where `R` is:
/// `@r : ∀ {α : Sort u_1} (R : α → α → Prop) (x : α), R x x → R x x`; an unused section leaves
/// `s : Nat → Nat` alone. A field never auto-binds: the pin refuses `structure P where x : α`.
#[test]
fn variables_bind_and_fields_do_not() {
    let engine = checked(
        "section\nvariable (R : α → α → Prop)\ndef r (x : α) (h : R x x) : R x x := h\ndef s (n : Nat) : Nat := n\nend\n",
    );
    let r = binders(&engine, "r", 3);
    assert_eq!(
        r.iter()
            .map(|(name, style, _)| (name.as_str(), *style))
            .collect::<Vec<_>>(),
        [
            ("α", BinderInfo::Implicit),
            ("R", BinderInfo::Default),
            ("x", BinderInfo::Default)
        ]
    );
    assert_eq!(binders(&engine, "s", 1)[0].2, constant("Nat"));
    refused("structure P where\n  x : α\n");
}
