//! Visibility selection is separate from checking. These tests exercise the
//! parser/scope boundary and real untrusted candidates; engine tests own export
//! projection and dual-checker publication across source-module imports.
#![forbid(unsafe_code)]
use fln_core::expr::Expr;
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_elab::source::scope::{self, ScopeError, SourceScope};
use fln_elab::{NatDefinitionElabError, source::SourceInferenceError};
use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};
use fln_env::environment::Environment;
use fln_kernel::verdict::{Budget, Verdict};
use fln_kernel::{Declaration, check};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn module() -> SourceScope {
    SourceScope {
        namespace: n("API"),
        private_module: Some(n("Main")),
        ..SourceScope::default()
    }
}

fn private(name: &Name) -> Name {
    Name::num(n("_private.Main"), 0).append_core(name)
}

fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}

#[test]
fn visibility_overrides_preserve_module_identity_and_do_not_mutate_defaults() {
    let lexical = module();
    let public = lexical
        .for_command_source(b"@[expose] public def identity (a : Type) (x : a) : a := x")
        .unwrap();
    assert!(public.exports_declaration());
    assert_eq!(public.private_module, lexical.private_module);
    assert_eq!(
        public.declaration_name(&n("identity")).unwrap(),
        n("API.identity")
    );
    assert_eq!(
        lexical.declaration_name(&n("identity")).unwrap(),
        private(&n("API.identity"))
    );
    let explicit = public
        .for_command_source(b"private def identity (a : Type) (x : a) : a := x")
        .unwrap();
    assert!(!explicit.exports_declaration());
    assert_eq!(
        explicit.declaration_name(&n("_root_.identity")).unwrap(),
        private(&n("identity"))
    );
    assert!(public.exports_declaration());
    // Local private aliases remain available in the private world even after
    // selecting a public declaration's naming scope.
    let private_name = private(&n("API.helper"));
    assert_eq!(
        public
            .resolve(&n("helper"), |name| name == &private_name)
            .unwrap(),
        Some(private_name)
    );
}

#[test]
fn hidden_public_bodies_and_public_mutual_groups_remain_explicit_refusals() {
    let mut public = module();
    public.public_declarations = true;
    public.expose_definitions = true;
    for source in [
        "@[no_expose] def hidden (a : Type) (x : a) : a := x",
        "@[expose] public theorem proof (p : Prop) (h : p) : p := h",
        "@[no_expose] public theorem proof (p : Prop) (h : p) : p := h",
        "@[no_expose] public instance dictionary : Type := Type",
        "mutual inductive A where | mk inductive B where | mk end",
        "mutual inductive A where | mk public inductive B where | mk end",
    ] {
        assert!(
            public.for_command_source(source.as_bytes()).is_err(),
            "{source}"
        );
    }
    assert!(
        module()
            .for_command_source(b"public def hidden (a : Type) (x : a) : a := x")
            .is_err()
    );
    assert!(
        module()
            .for_command_source(b"mutual inductive A where | mk public inductive B where | mk end")
            .is_err()
    );
    assert!(
        !module()
            .for_command_source(b"mutual inductive A where | mk inductive B where | mk end")
            .unwrap()
            .exports_declaration()
    );
}

#[test]
fn public_instance_and_theorem_headers_select_the_exported_world() {
    for scope in [
        module(),
        SourceScope {
            public_declarations: true,
            expose_definitions: true,
            ..module()
        },
    ] {
        for source in [
            "public instance dictionary : Type := Type",
            "@[expose] public instance dictionary : Type := Type",
            "public theorem proof (p : Prop) (h : p) : p := h",
        ] {
            let effective = scope.for_command_source(source.as_bytes()).unwrap();
            assert!(effective.exports_declaration(), "{source}");
            assert_eq!(effective.private_module, scope.private_module);
        }
    }
    let public = SourceScope {
        public_declarations: true,
        ..module()
    };
    assert!(
        public
            .for_command_source(b"instance dictionary : Type := Type")
            .unwrap()
            .exports_declaration()
    );
    assert!(
        !public
            .for_command_source(b"private instance dictionary : Type := Type")
            .unwrap()
            .exports_declaration()
    );
    // Header selection grants no admission: the instance elaborator still
    // checks the class and result sort before accepting its body.
}

#[test]
fn queries_and_ordinary_examples_stay_private_inside_public_exposure_sections() {
    let mut public = module();
    public.public_declarations = true;
    public.expose_definitions = true;
    for source in [
        "#check Type",
        "#eval (fun (a : Type) (x : a) => x)",
        "example (p : Prop) (h : p) : p := h",
    ] {
        let effective = public.for_command_source(source.as_bytes()).unwrap();
        assert!(!effective.exports_declaration(), "{source}");
        assert_eq!(effective.private_module, public.private_module);
    }
    assert!(
        public
            .for_command_source(b"public example (p : Prop) (h : p) : p := h")
            .is_err()
    );
}

#[test]
fn exposed_and_private_definition_candidates_have_checked_structural_names() {
    let env = Environment::new();
    let lexical = module();
    for (source, expected) in [
        (
            "@[expose] public def identity (a : Type) (x : a) : a := x",
            n("API.identity"),
        ),
        (
            "private def identity (a : Type) (x : a) : a := x",
            private(&n("API.identity")),
        ),
        (
            "@[expose] private def identity (a : Type) (x : a) : a := x",
            private(&n("API.identity")),
        ),
    ] {
        let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
        let declaration = fln_elab::elaborate_definition_in_scope_with_budget(
            parsed.syntax(),
            &env,
            budget(),
            &lexical,
        )
        .unwrap();
        assert!(
            matches!(
                check(&env, &declaration, budget()),
                Outcome::Complete(Verdict::Accepted { .. })
            ),
            "{source}"
        );
        let Declaration::Defn(value) = declaration else {
            panic!("definition candidate")
        };
        assert_eq!(value.base.name, expected);
        assert_eq!(value.all, vec![expected]);
    }
    let source =
        fln_parse::parse_definition(b"public def identity (a : Type) (x : a) : a := x").unwrap();
    let legacy = fln_elab::elaborate_definition_in_scope_with_budget(
        source.syntax(),
        &env,
        budget(),
        &SourceScope::default(),
    )
    .unwrap();
    assert!(matches!(legacy, Declaration::Defn(value) if value.base.name == n("identity")));
}

#[test]
fn public_data_bundle_names_include_the_family_constructors_and_recursor() {
    let env = Environment::new();
    let parsed = fln_parse::parse_definition(b"public inductive Token where | one | two").unwrap();
    let declaration = scope::elaborate_inductive(
        parsed.syntax(),
        &env,
        budget(),
        fln_elab::records::RecordBudget::default(),
        &module(),
    )
    .unwrap();
    assert!(matches!(
        check(&env, &declaration, budget()),
        Outcome::Complete(Verdict::Accepted { .. })
    ));
    let Declaration::Inductive(block) = declaration else {
        panic!("inductive bundle")
    };
    assert_eq!(block.types[0].base.name, n("API.Token"));
    assert_eq!(
        block
            .ctors
            .iter()
            .map(|ctor| ctor.base.name.clone())
            .collect::<Vec<_>>(),
        vec![n("API.Token.one"), n("API.Token.two")]
    );
    assert_eq!(block.recursors[0].base.name, n("API.Token.rec"));
    let record =
        fln_parse::parse_definition(b"@[expose] public structure Box (a : Type) where\n value : a")
            .unwrap();
    let record = scope::elaborate_record(
        record.syntax(),
        &env,
        budget(),
        fln_elab::records::RecordBudget::default(),
        &module(),
    )
    .unwrap();
    assert_eq!(record.name, n("API.Box"));
    assert!(record.declarations.iter().any(|declaration| matches!(declaration, Declaration::Defn(value) if value.base.name == n("API.Box.value"))));
}

#[test]
fn exposure_tags_combine_with_simp_without_dropping_other_attribute_effects() {
    for source in [
        "@[expose, simp] public def identity (a : Type) (x : a) : a := x",
        "@[simp, expose] public def identity (a : Type) (x : a) : a := x",
    ] {
        let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
        assert!(
            module()
                .for_declaration(parsed.syntax())
                .unwrap()
                .exports_declaration()
        );
        assert_eq!(
            scope::simp::registration(parsed.syntax()).unwrap(),
            Some((n("identity"), 1000, false))
        );
    }
    for source in [
        "@[local expose] public def identity (a : Type) (x : a) : a := x",
        "@[expose 10] public def identity (a : Type) (x : a) : a := x",
        "@[expose, inline] public def identity (a : Type) (x : a) : a := x",
    ] {
        let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
        assert!(
            fln_elab::elaborate_definition_in_scope_with_budget(
                parsed.syntax(),
                &Environment::new(),
                budget(),
                &module()
            )
            .is_err(),
            "{source}"
        );
    }
}

#[test]
fn public_private_name_collisions_are_checked_against_the_full_environment() {
    let mut public = module();
    public.public_declarations = true;
    let env = Environment::new()
        .add_decl(ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: private(&n("API.identity")),
                level_params: Vec::new(),
                type_: Expr::sort(Level::one()),
            },
            is_unsafe: false,
        }))
        .unwrap();
    assert!(
        matches!(public.check_public_name(&n("API.identity"), &env), Err(NatDefinitionElabError::Inference(SourceInferenceError::NameScope(ScopeError::PublicShadowsPrivate(name)))) if name == n("API.identity"))
    );
    assert!(public.check_public_name(&n("API.different"), &env).is_ok());
    assert!(module().check_public_name(&n("API.identity"), &env).is_ok());
}
