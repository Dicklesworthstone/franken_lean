//! Code generator hints, which change neither a verdict nor a value: `inline`, `noinline`,
//! `always_inline` and `inline_if_reduce` (the pin's `inlineAttrs`, Lean/Compiler/InlineAttrs.lean)
//! on a definition or an opaque constant, and `specialize` without arguments
//! (Lean/Compiler/Specialize.lean) on any declaration. Every program here was run through the pinned
//! `lean` v4.32.0 first (2026-10-11); a refusal quotes the pin's message.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(source: &str) -> Result<(), String> {
    match engine().check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    ) {
        Ok(outcome) => {
            outcome.into_complete().unwrap();
            Ok(())
        }
        Err(error) => Err(error.to_string()),
    }
}

const INLINING: [&str; 4] = ["inline", "noinline", "always_inline", "inline_if_reduce"];

#[test]
fn compiler_hints_leave_definitions_unchanged() {
    for hint in INLINING.into_iter().chain(["specialize"]) {
        for declaration in [
            "@[HINT] def d (n : Nat) : Nat := n + 1\ntheorem t : d 1 = 2 := rfl\n",
            "@[HINT] abbrev d (n : Nat) : Nat := n + 1\ntheorem t : d 1 = 2 := rfl\n",
            "class K where\n  k : Nat\n@[HINT] instance d : K := ⟨3⟩\ntheorem t : K.k = 3 := rfl\n",
            "class K where\n  k : Nat\n@[HINT] instance : K := ⟨3⟩\n",
            "@[HINT] opaque d : Nat\n",
            "@[HINT] def d : Nat → Nat\n  | 0 => 0\n  | n + 1 => d n\n",
        ] {
            let source = declaration.replace("HINT", hint);
            check(&source).unwrap_or_else(|error| panic!("{source}: {error}"));
        }
    }
    for source in [
        // `specialize` without arguments takes any declaration.
        "@[specialize] theorem d : 1 = 1 := rfl\n",
        "@[specialize] axiom d : Nat\n",
        // Several hints, and a hint beside `simp` or an exposure attribute.
        "@[inline, noinline, specialize] def d (n : Nat) : Nat := n\n",
        "@[inline, simp] def d (n : Nat) : Nat := n\ntheorem t (n : Nat) : d n = n := by simp\n",
        "@[expose, noinline] def d (n : Nat) : Nat := n\n",
    ] {
        check(source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
}

#[test]
fn compiler_hint_refusals_match_the_pin() {
    for hint in INLINING {
        for (declaration, pin) in [
            (
                "@[HINT] theorem d : 1 = 1 := rfl\n",
                "Cannot add attribute `[HINT]`: Declaration `d` is not a definition",
            ),
            (
                "@[HINT] axiom d : Nat\n",
                "Cannot add attribute `[HINT]`: Declaration `d` is not a definition",
            ),
            (
                "@[HINT] structure d where\n  x : Nat\n",
                "Cannot add attribute `[HINT]`: Declaration `d` is not a definition",
            ),
            (
                "@[HINT] inductive d where\n  | a\n",
                "Cannot add attribute `[HINT]`: Declaration `d` is not a definition",
            ),
            (
                "@[local HINT] def d (n : Nat) : Nat := n\n",
                "Invalid attribute scope: Attribute `[HINT]` must be global, not `local`",
            ),
            (
                "@[scoped HINT] def d (n : Nat) : Nat := n\n",
                "Scoped attributes must be used inside namespaces",
            ),
            (
                "@[HINT 1] def d (n : Nat) : Nat := n\n",
                "Unexpected attribute argument: This attribute takes no arguments",
            ),
            (
                "@[HINT, simp] theorem d : 1 = 1 := rfl\n",
                "Cannot add attribute `[HINT]`: Declaration `d` is not a definition",
            ),
        ] {
            let source = declaration.replace("HINT", hint);
            assert!(
                check(&source).is_err(),
                "accepted {source} (the pin: {pin})"
            );
        }
    }
    for (source, pin) in [
        (
            "@[specialize zz] def d (n : Nat) : Nat := n\n",
            "Invalid specialization argument name `zz`: `d` does not have an argument with this name",
        ),
        (
            "@[specialize 0] def d (n : Nat) : Nat := n\n",
            "Invalid specialization argument index `0`: Index must be greater than 0",
        ),
        (
            "@[specialize 9] def d (n : Nat) : Nat := n\n",
            "Invalid argument index `8`: `d` has only 1 arguments",
        ),
        (
            "@[macro_inline] opaque d : Nat\n",
            "Cannot add `[macro_inline]` attribute to `d`: This attribute does not support this kind of declaration",
        ),
        (
            "@[macro_inline] def d : Nat → Nat\n  | 0 => 0\n  | n + 1 => d n\n",
            "Cannot add `[macro_inline]` attribute to `d`: This attribute does not support this kind of declaration",
        ),
        // A hint does not excuse a body the pin refuses.
        ("@[inline] def d (n : Nat) : Nat := true\n", "Type mismatch"),
    ] {
        assert!(check(source).is_err(), "accepted {source} (the pin: {pin})");
    }
}

#[test]
fn prelude_compiler_and_metadata_tags_match_the_pin() {
    for source in [
        "class C where\n  x : Nat\nattribute [weak_specialize] C\n",
        "@[weak_specialize] def d (n : Nat) : Nat := n\n",
        "@[weak_specialize] theorem t : 1 = 1 := rfl\n",
        "@[never_extract] def d (n : Nat) : Nat := n\n",
        "@[noinline, never_extract] def d (n : Nat) : Nat := n\n",
        "@[never_extract] theorem t : 1 = 1 := rfl\n",
        "@[never_extract] structure S where\n  x : Nat\n",
        "def d : Nat := 0\nattribute [never_extract] d\n",
        "@[nospecialize] def d (n : Nat) : Nat := n\n",
        "@[nospecialize] theorem t : 1 = 1 := rfl\n",
        "@[nospecialize] structure S where\n  x : Nat\n",
        "@[export my_sym] def d (x : Nat) : Nat := x\n",
        "@[export foo.bar] def d (x : Nat) : Nat := x\n",
        "@[export my_thm] theorem t : 1 = 1 := rfl\n",
        "@[export my_s] structure S where\n  x : Nat\n",
        "@[suggest_for Foo, suggest_for Bar] inductive Baz | mk\n",
        "@[suggest_for Foo] def d : Nat := 0\n",
        "inductive Baz | mk\nattribute [suggest_for Foo] Baz\n",
        "def a : Nat := 0\n@[inherit_doc a] def b : Nat := 0\n",
        "def a : Nat := 0\n@[always_inline, inline, inherit_doc a] def b : Nat := a\n",
    ] {
        check(source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }

    for (source, pin) in [
        (
            "@[local weak_specialize] def d : Nat := 0\n",
            "Invalid attribute scope: Attribute `[weak_specialize]` must be global",
        ),
        (
            "@[weak_specialize 1] def d : Nat := 0\n",
            "Unexpected attribute argument: This attribute takes no arguments",
        ),
        (
            "@[local never_extract] def d : Nat := 0\n",
            "Invalid attribute scope: Attribute `[never_extract]` must be global",
        ),
        (
            "@[local nospecialize] def d : Nat := 0\n",
            "Invalid attribute scope: Attribute `[nospecialize]` must be global",
        ),
        (
            "@[export foo'] def d (x : Nat) : Nat := x\n",
            "Invalid `export` function name: `foo'` is not a valid C++ identifier",
        ),
        (
            "@[export α] def d (x : Nat) : Nat := x\n",
            "Invalid `export` function name: `α` is not a valid C++ identifier",
        ),
        (
            "@[local export my_sym] def d (x : Nat) : Nat := x\n",
            "Invalid attribute scope: Attribute `[export]` must be global",
        ),
        (
            "@[local suggest_for Foo] inductive Baz | mk\n",
            "Invalid attribute scope: Attribute `[suggest_for]` must be global",
        ),
        (
            "@[inherit_doc noSuchDecl999] def b : Nat := 0\n",
            "Unknown constant `noSuchDecl999`",
        ),
        (
            "def a : Nat := 0\n@[local inherit_doc a] def b : Nat := 0\n",
            "Invalid attribute scope: Attribute `[inherit_doc]` must be global",
        ),
    ] {
        assert!(check(source).is_err(), "accepted {source} (the pin: {pin})");
    }
}
