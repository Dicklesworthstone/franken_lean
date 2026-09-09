//! Arbitrary record candidates go through the production K1/checker council.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome};
use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_elab::lctx::LocalContext;
use fln_elab::records::{RecordBudget, RecordError, RecordSpec, record_declarations};
use fln_kernel::Declaration;

fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn nat() -> Expr {
    Expr::const_(n("Nat"), vec![])
}
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn local(ctx: &mut LocalContext, name: &str, ty: Expr) -> Expr {
    let id = fln_core::expr::FVarId(n(name));
    ctx.add_param(id.clone(), n(name), ty, BinderInfo::Default);
    Expr::fvar(id)
}
fn record(name: &str, fields: LocalContext, level: Level) -> RecordSpec {
    RecordSpec {
        name: n(name),
        level_params: vec![],
        parameters: vec![],
        fields: fields.decls().to_vec(),
        result_level: level,
        is_class: false,
    }
}
fn admitted(engine: &Engine, spec: &RecordSpec) -> Engine {
    engine
        .admit_declarations(
            &record_declarations(spec, RecordBudget::default()).unwrap(),
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}
fn proof(engine: &Engine, text: &str) {
    engine
        .admit_source_declaration(text.as_bytes(), &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
}

#[test]
fn nondependent_record_computes_through_generated_projections_and_both_checkers() {
    let mut fields = LocalContext::new();
    local(&mut fields, "left", nat());
    local(&mut fields, "right", nat());
    let result = admitted(&engine(), &record("Pair", fields, Level::one()));
    proof(
        &result,
        "theorem left_ok : Pair.left (Pair.mk 7 9) = 7 := by rfl",
    );
    proof(
        &result,
        "theorem right_ok : Pair.right (Pair.mk 7 9) = 9 := by rfl",
    );
}

#[test]
fn dependent_record_projection_replaces_earlier_field_locals() {
    let mut fields = LocalContext::new();
    let ty = local(&mut fields, "carrier", Expr::sort(Level::one()));
    local(&mut fields, "value", ty);
    let result = admitted(
        &engine(),
        &record("Package", fields, Level::one().succ().unwrap()),
    );
    proof(
        &result,
        "theorem value_ok : Package.value (Package.mk Nat 13) = 13 := by rfl",
    );
}

#[test]
fn type_parameters_are_inferred_by_constructors_and_projections() {
    let mut params = LocalContext::new();
    let alpha = local(&mut params, "A", Expr::sort(Level::one()));
    let mut fields = LocalContext::new();
    local(&mut fields, "value", alpha);
    let mut spec = record("Box", fields, Level::one());
    spec.parameters = params.decls().to_vec();
    let result = admitted(&engine(), &spec);
    proof(
        &result,
        "theorem box_ok : Box.value (Box.mk 19) = 19 := by rfl",
    );
}

#[test]
fn polymorphic_record_uses_fresh_eliminator_universe() {
    let mut params = LocalContext::new();
    let u = Level::param(n("u"));
    let alpha = local(&mut params, "A", Expr::sort(u.clone()));
    let mut fields = LocalContext::new();
    local(&mut fields, "value", alpha);
    let mut spec = record("PolyBox", fields, Level::max(Level::one(), u).unwrap());
    spec.level_params = vec![n("u")];
    spec.parameters = params.decls().to_vec();
    let result = admitted(&engine(), &spec);
    proof(
        &result,
        "theorem box_ok : PolyBox.value (PolyBox.mk 23) = 23 := by rfl",
    );
}

#[test]
fn empty_record_has_a_checked_constructor_and_eliminator() {
    let spec = record("EmptyRecord", LocalContext::new(), Level::one());
    let result = admitted(&engine(), &spec);
    proof(
        &result,
        "theorem empty_ok : EmptyRecord.mk = EmptyRecord.mk := by rfl",
    );
}

#[test]
fn forged_record_eliminator_never_exposes_a_successor() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let mut fields = LocalContext::new();
    local(&mut fields, "value", nat());
    let mut declarations = record_declarations(
        &record("Forged", fields, Level::one()),
        RecordBudget::default(),
    )
    .unwrap();
    let Declaration::Inductive(block) = &mut declarations[0] else {
        panic!("block");
    };
    block.recursors[0].rules[0].rhs = Expr::sort(Level::zero());
    assert!(!matches!(
        base.admit_declarations(&declarations, &KVMap::new(), limits()),
        Ok(Outcome::Complete(_))
    ));
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&n("Forged")));
}

#[test]
fn forward_references_duplicate_names_and_unresolved_domains_are_refused() {
    let mut fields = LocalContext::new();
    local(
        &mut fields,
        "value",
        Expr::fvar(fln_core::expr::FVarId(n("missing"))),
    );
    assert_eq!(
        record_declarations(
            &record("Bad", fields, Level::one()),
            RecordBudget::default()
        ),
        Err(RecordError::InvalidTelescope)
    );
    let mut fields = LocalContext::new();
    local(&mut fields, "value", nat());
    let mut spec = record("Bad", fields, Level::one());
    let mut duplicate = spec.fields[0].clone();
    duplicate.id = fln_core::expr::FVarId(n("other"));
    spec.fields.push(duplicate);
    assert_eq!(
        record_declarations(&spec, RecordBudget::default()),
        Err(RecordError::DuplicateField)
    );
    assert_eq!(
        record_declarations(
            &spec,
            RecordBudget {
                max_binders: 0,
                max_nodes: 0
            }
        ),
        Err(RecordError::ResourceLimit)
    );
}

#[test]
fn late_projection_failure_does_not_publish_the_record_block() {
    let base = engine();
    let mut fields = LocalContext::new();
    local(&mut fields, "value", nat());
    let mut declarations = record_declarations(
        &record("LateFailure", fields, Level::one()),
        RecordBudget::default(),
    )
    .unwrap();
    let Declaration::Defn(projection) = &mut declarations[1] else {
        panic!("projection");
    };
    projection.value = Expr::sort(Level::zero());
    assert!(!matches!(
        base.admit_declarations(&declarations, &KVMap::new(), limits()),
        Ok(Outcome::Complete(_))
    ));
    assert!(!base.environment().contains(&n("LateFailure")));
}
