use super::*;

fn c(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn app(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}

fn engine() -> Engine {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[br#"
def headKeep (A : Type) (value : A) : A := value
structure HeadBox (A : Type) where
  value : A
structure HeadPayload where
  flag : Bool
  value : if flag then Nat else String
inductive HeadBad where
  | mk (callback : Nat -> HeadBad) (payload : HeadPayload)
"#],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

fn projection(value: Expr) -> Expr {
    Expr::proj(name("HeadBox"), 0, app(c("HeadBox.mk"), [c("Nat"), value]))
}

#[test]
fn terminal_heads_retain_their_full_syntax_with_one_charged_visit() {
    let environment = Environment::new();
    let types = [
        Expr::sort(Level::one()),
        b(3),
        nat::literal(42),
        Expr::lam(name("kept"), c("Nat"), b(0), BinderInfo::InstImplicit),
        Expr::forall_e(name("kept"), c("Nat"), b(0), BinderInfo::Implicit),
    ];
    for source in types {
        let mut preparation = Preparation::new(
            &environment,
            IngressLimits {
                max_nodes: 1,
                max_context_depth: 0,
                max_application_args: 0,
                ..IngressLimits::default()
            },
        );
        assert_eq!(preparation.type_head(&source).unwrap(), source);
        assert_eq!(preparation.visited, 1);
        assert!(preparation.specializations.heads.entries.is_empty());
        assert_eq!(
            preparation.type_head(&source),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                limit: 1,
                observed: 2,
            })
        );
    }
}

#[test]
fn completed_heads_reuse_exact_open_and_closed_inputs_without_changing_source() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let identity = Expr::lam(name("identity"), c("Nat"), b(0), BinderInfo::Default);
    let open = |value| {
        Expr::let_e(
            name("open"),
            c("Nat"),
            value,
            Expr::app(identity.clone(), b(0)),
            false,
        )
    };
    let cases = [
        (
            app(c("headKeep"), [c("Nat"), nat::literal(42)]),
            nat::literal(42),
        ),
        (
            app(c("headKeep"), [c("Nat"), nat::literal(7)]),
            nat::literal(7),
        ),
        (projection(nat::literal(42)), nat::literal(42)),
        (projection(nat::literal(7)), nat::literal(7)),
        (open(b(1)), b(1)),
        (open(b(2)), b(2)),
        (Expr::mdata(KVMap::new(), open(b(1))), b(1)),
    ];
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    for (source, expected) in &cases {
        let original = source.clone();
        assert_eq!(preparation.type_head(source).unwrap(), *expected);
        assert_eq!(*source, original);
        assert!(
            preparation
                .specializations
                .heads
                .entries
                .contains_key(source)
        );
    }
    for (source, expected) in cases {
        let before = preparation.visited;
        assert_eq!(preparation.type_head(&source).unwrap(), expected);
        assert_eq!(preparation.visited, before + 1);
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn a_new_canonical_definition_invalidates_an_earlier_opaque_head() {
    let engine = engine();
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let future_name = Name::num(name("_fln_runtime_specialization"), 0);
    let future = Expr::const_(future_name.clone(), Vec::new());
    assert_eq!(preparation.type_head(&future).unwrap(), future);
    assert_eq!(
        preparation.specializations.heads.entries[&future].generation,
        0
    );

    let specialized = preparation
        .specialize_call(&c("headKeep"), &[c("Nat")])
        .unwrap()
        .unwrap();
    assert_eq!(specialized, future);
    let definition = preparation.specialized_definition(&future_name).unwrap();
    assert_eq!(preparation.specializations.definitions.len(), 1);
    let rows = preparation.specializations.heads.entries.len();
    assert_eq!(preparation.type_head(&future).unwrap(), definition.value);
    assert_eq!(preparation.specializations.heads.entries.len(), rows);
    assert_eq!(
        preparation.specializations.heads.entries[&future].generation,
        1
    );

    let before = preparation.visited;
    preparation.limits.max_nodes = before + 1;
    assert_eq!(preparation.type_head(&future).unwrap(), definition.value);
    assert_eq!(preparation.visited, before + 1);
    assert_eq!(
        preparation.specialized_definition(&future_name),
        Some(definition)
    );
}

#[test]
fn cached_heads_do_not_bypass_tighter_spine_or_projection_limits() {
    let environment = Environment::new();
    let source = app(c("opaque"), [nat::literal(1), nat::literal(2)]);
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    assert_eq!(preparation.type_head(&source).unwrap(), source);
    preparation.limits.max_application_args = 1;
    assert_eq!(
        preparation.type_head(&source),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ApplicationArguments,
            limit: 1,
            observed: 2,
        })
    );
    preparation.limits.max_application_args = 2;
    assert_eq!(preparation.type_head(&source).unwrap(), source);

    let source = Expr::proj(name("Outer"), 0, Expr::proj(name("Inner"), 0, c("opaque")));
    assert_eq!(preparation.type_head(&source).unwrap(), source);
    preparation.limits.max_context_depth = 1;
    assert_eq!(
        preparation.type_head(&source),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ProgramTables,
            limit: 1,
            observed: 2,
        })
    );
    preparation.limits.max_context_depth = 2;
    assert_eq!(preparation.type_head(&source).unwrap(), source);
}

#[test]
fn failed_reductions_and_failed_insertions_never_publish_a_head_result() {
    let environment = Environment::new();
    let source = Expr::let_e(name("value"), c("Nat"), nat::literal(42), b(0), false);
    let mut measured = Preparation::new(&environment, IngressLimits::default());
    assert_eq!(measured.type_head(&source).unwrap(), nat::literal(42));
    let complete = measured.visited;
    assert!(complete > 2);
    for allowed in [0, 1, complete - 1] {
        let mut preparation = Preparation::new(
            &environment,
            IngressLimits {
                max_nodes: allowed,
                ..IngressLimits::default()
            },
        );
        assert_eq!(
            preparation.type_head(&source),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                limit: allowed,
                observed: allowed + 1,
            })
        );
        assert!(preparation.specializations.heads.entries.is_empty());
        preparation.limits.max_nodes = IngressLimits::default().max_nodes;
        assert_eq!(preparation.type_head(&source).unwrap(), nat::literal(42));
        let before = preparation.visited;
        preparation.limits.max_nodes = before + 1;
        assert_eq!(preparation.type_head(&source).unwrap(), nat::literal(42));
        assert_eq!(preparation.visited, before + 1);
    }
}

#[test]
fn memo_capacity_failure_retains_completed_rows_and_stale_replacement_is_bounded() {
    let mut entries = HashMap::new();
    let entry = |generation, result| Entry {
        generation,
        limits: Limits::from(IngressLimits::default()),
        result,
    };
    remember(&mut entries, c("first"), entry(0, c("Nat")), 1).unwrap();
    assert_eq!(
        remember(&mut entries, c("second"), entry(0, c("Bool")), 1),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit: 1,
            observed: 2,
        })
    );
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[&c("first")].result, c("Nat"));
    remember(&mut entries, c("first"), entry(1, c("Bool")), 1).unwrap();
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[&c("first")].generation, 1);
    assert_eq!(entries[&c("first")].result, c("Bool"));
}

#[test]
fn successful_head_syntax_survives_unrelated_representation_rollback() {
    let engine = engine();
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let source = projection(nat::literal(42));
    let result = preparation.type_head(&source).unwrap();
    assert_eq!(result, nat::literal(42));
    let interfaces = preparation.interfaces.len();
    let constructors = preparation.constructors.len();
    assert!(preparation.value_type(&c("HeadBad")).unwrap().is_none());
    assert_eq!(preparation.interfaces.len(), interfaces);
    assert_eq!(preparation.constructors.len(), constructors);
    let before = preparation.visited;
    preparation.limits.max_nodes = before + 1;
    assert_eq!(preparation.type_head(&source).unwrap(), result);
    assert_eq!(preparation.visited, before + 1);
}
