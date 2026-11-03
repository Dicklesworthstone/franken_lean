//! Expanded syntax follows the ordinary module public/private admission worlds.
use super::modules::{check, succeeded};
use super::*;
use crate::source_check::modules::SourceModuleCheckError;
use fln_olean::ir::IrAlt;

fn private(module: &str, declaration: &str) -> Name {
    Name::num(name(&format!("_private.{module}")), 0).append_core(&name(declaration))
}

#[test]
fn module_macro_visibility_follows_public_and_private_import_forwarding() {
    let (imported, code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    for (visibility, expected, main_scope) in [("import", 18, 17), ("public import", 11, 19)] {
        let library = format!(
            "module\nprelude\n{visibility} SourceLibrary\n\
             def localOnly : Nat := 7 + 11"
        );
        let main = format!(
            "prelude\nimport Lib\ndef observed : Nat := 7 + 11\n\
             theorem checked : observed = {expected} := by rfl"
        );
        let report = check(
            &imported,
            &code,
            &[("Main", &main), ("Lib", &library)],
            MacroTreeLimits::default(),
            None,
        );
        let checked = succeeded(&report);
        assert_declared_value(&checked.checked.engine, "observed", expected);
        assert!(
            !checked
                .checked
                .engine
                .environment()
                .contains(&name("localOnly"))
        );
        assert!(
            !checked
                .checked
                .engine
                .environment()
                .contains(&private("Lib", "localOnly"))
        );
        let states = report.states.as_ref().unwrap();
        assert_eq!(states[&name("Lib")].macro_scope, 19);
        assert_eq!(states[&name("Main")].macro_scope, main_scope);
    }
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

#[test]
fn public_macro_definitions_export_expanded_values_and_only_checked_hidden_signatures() {
    let (imported, code) = batches::artifact_import_fixture();
    let report = check(
        &imported,
        &code,
        &[
            (
                "Main",
                "prelude\nimport Api\n\
                 theorem exportedValue : exposed = 11 := by rfl\n\
                 noncomputable def usesSignature : Nat := hiddenBody",
            ),
            (
                "Api",
                "module\nprelude\npublic import SourceLibrary\n\
                 def secret : Nat := 23\n\
                 @[expose] public def exposed : Nat := 7 + 11\n\
                 public def hiddenBody : Nat := False + secret",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    let environment = checked.checked.engine.environment();
    assert_declared_value(&checked.checked.engine, "exposed", 11);
    assert!(matches!(environment.find(&name("hiddenBody")),
        Some(ConstantInfo::Axiom(interface))
            if !interface.is_unsafe && interface.base.type_ == Expr::const_(name("Nat"), vec![])));
    assert!(!environment.contains(&name("secret")));
    assert!(!environment.contains(&private("Api", "secret")));
    assert!(environment.contains(&name("exportedValue")));
    assert!(environment.contains(&name("usesSignature")));
    // Public and private checking consume the same expanded tree. They must
    // not execute a macro twice for one command with a hidden implementation.
    assert_eq!(report.attempts.len(), 4);
    assert_eq!(
        report.states.as_ref().unwrap()[&name("Api")].macro_scope,
        21
    );
}

#[test]
fn expanded_public_bodies_signatures_and_false_proofs_cannot_publish_private_state() {
    let (imported, code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    for command in [
        "@[expose] public def leaked : Nat := False + secret",
        "public def leaked : Nat + Secret := Secret.make",
        "public theorem wrong : (7 + 11) = 18 := by rfl",
    ] {
        let source = format!(
            "module\nprelude\npublic import SourceLibrary\n\
             def secret : Nat := 23\n\
             inductive Secret where\n  | make\n\
             @[expose] public def checkedPrefix : Nat := 7 + 11\n{command}"
        );
        let report = check(
            &imported,
            &code,
            &[("Main", "prelude\nimport Api"), ("Api", &source)],
            MacroTreeLimits::default(),
            None,
        );
        assert!(
            matches!(&report.outcome, Outcome::Complete(Err(SourceModuleCheckError::Source { module, .. })) if module == &name("Api")),
            "{command}: {report:?}"
        );
        assert!(report.attempts.len() >= 4, "{command}: expansion must run");
        assert!(report.states.is_none());
        assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
        assert!(
            !imported
                .engine
                .environment()
                .contains(&name("checkedPrefix"))
        );
    }
    let good = check(
        &imported,
        &code,
        &[
            (
                "Main",
                "prelude\nimport Api\ntheorem inherited : (11 : Nat) = 11 := by exact correct",
            ),
            (
                "Api",
                "module\nprelude\npublic import SourceLibrary\n\
                 public theorem correct : (7 + 11) = 11 := by rfl",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        succeeded(&good)
            .checked
            .engine
            .environment()
            .contains(&name("inherited"))
    );
}

#[test]
fn expanded_public_proof_instances_export_their_checked_interface_and_instance_journal() {
    let (imported, code) = batches::artifact_import_fixture();
    let report = check(
        &imported,
        &code,
        &[
            (
                "Main",
                "prelude\nimport Api\n\
                 theorem proof : True := @Law.proof True (inferInstance : Law True)",
            ),
            (
                "Api",
                "module\nprelude\npublic import SourceLibrary\n\
                 public class Law (P : Prop) : Prop where\n  proof : P\n\
                 private theorem hidden : True := True.intro\n\
                 public instance lawful : Law (False + True) := Law.mk hidden",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    let environment = checked.checked.engine.environment();
    assert!(
        matches!(environment.find(&name("lawful")), Some(ConstantInfo::Axiom(signature)) if !signature.is_unsafe)
    );
    assert!(matches!(
        environment.find(&name("proof")),
        Some(ConstantInfo::Thm(_))
    ));
    assert!(!environment.contains(&private("Api", "hidden")));
    let instances = fln_elab::instances::InstanceRegistry::read(environment).unwrap();
    let [instance] = instances.candidates(&name("Law")) else {
        panic!("exactly the checked public proof instance must be exported")
    };
    assert_eq!(instance.declaration, name("lawful"));
    assert_eq!(report.attempts.len(), 2);
}

fn equation_reference_function() -> IrDecl {
    let mut declaration = function("SourceLibrary.preresolved", Behavior::Identity);
    let IrDecl::Function { body, .. } = &mut declaration else {
        unreachable!()
    };
    body.stmts = vec![
        bind(3, IrExpr::Lit(IrLit::Num(IrNat::Small(0)))),
        bind(
            4,
            IrExpr::Fap {
                function: name("Lean.Syntax.getArg"),
                args: vec![IrArg::Var(0), IrArg::Var(3)],
            },
        ),
        bind(5, IrExpr::Proj { i: 0, x: 4 }),
        bind(6, IrExpr::Proj { i: 1, x: 4 }),
        bind(7, IrExpr::Lit(IrLit::Str("eq_1".into()))),
        bind(
            8,
            IrExpr::Fap {
                function: name("Lean.Name.mkStr1"),
                args: vec![IrArg::Var(7)],
            },
        ),
        bind(
            9,
            ctor(layout::SYNTAX_IDENT, "Lean.Syntax.ident", &[5, 6, 8, 3]),
        ),
        bind(10, ctor(layout::RESULT_OK, "EStateM.Result.ok", &[9, 2])),
    ];
    *body.terminal = IrTerminal::Ret(IrArg::Var(10));
    declaration
}

#[test]
fn public_equations_are_staged_from_expansion_even_without_an_equation_name_in_source() {
    let (imported, mut code) = batches::artifact_import_fixture();
    let declaration = code
        .iter_mut()
        .flat_map(|module| &mut module.decls)
        .find(|declaration| declaration.name() == &name("SourceLibrary.preresolved"))
        .unwrap();
    *declaration = equation_reference_function();
    // The macro constructs the bare equation name under the definition's
    // namespace. Original bytes contain neither that name nor its suffix.
    let source = "module\nprelude\npublic import SourceLibrary\n\
                  @[expose] public def exposed : Nat := 11\n\
                  namespace exposed\n\
                  public theorem witness : exposed = 11 := placeholder / 0\n\
                  end exposed";
    assert!(!source.contains("eq_"));
    let report = check(
        &imported,
        &code,
        &[
            (
                "Main",
                "prelude\nimport Api\ntheorem use : exposed = 11 := by exact exposed.witness",
            ),
            ("Api", source),
        ],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    assert!(matches!(
        checked
            .checked
            .engine
            .environment()
            .find(&name("exposed.eq_1")),
        Some(ConstantInfo::Thm(_))
    ));
    assert!(checked.checked.engine.environment().contains(&name("use")));
    assert_eq!(report.attempts.len(), 1);
}

#[test]
fn public_mutual_groups_use_expanded_constructor_types_and_keep_visibility_rules() {
    let (imported, code) = batches::artifact_import_fixture();
    let source = r"module
prelude
public import SourceLibrary
mutual
  public inductive MacroTree where
    | leaf (value : Bool + Nat)
    | node (children : MacroForest)
  public inductive MacroForest where
    | nil
    | cons (tag : Bool + Nat) (head : MacroTree) (tail : MacroForest)
end";
    let report = check(
        &imported,
        &code,
        &[
            (
                "Main",
                r"prelude
import Api
def unpack (tree : MacroTree) : Nat := match tree with
  | MacroTree.leaf n => n
  | MacroTree.node _ => 0
theorem value : unpack (MacroTree.leaf 11) = 11 := by rfl",
            ),
            ("Api", source),
        ],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    assert_declared_value(&checked.checked.engine, "unpack (MacroTree.leaf 11)", 11);
    for declaration in ["MacroTree", "MacroForest"] {
        assert!(
            matches!(checked.checked.engine.environment().find(&name(declaration)),
            Some(ConstantInfo::Induct(info)) if info.all.len() == 2)
        );
    }
    assert_eq!(report.attempts.len(), 4);
    for invalid in [
        "mutual\npublic inductive Exposed where\n  | make (n : Bool + Nat)\ninductive Hidden where\n  | make\nend",
        "mutual\npublic def first : Nat := 7 + 11\npublic def second : Nat := 13 + 17\nend",
    ] {
        let invalid = format!("module\nprelude\npublic import SourceLibrary\n{invalid}");
        let report = check(
            &imported,
            &code,
            &[("Main", "prelude\nimport Api"), ("Api", &invalid)],
            MacroTreeLimits::default(),
            None,
        );
        assert!(
            matches!(&report.outcome,
            Outcome::Complete(Err(SourceModuleCheckError::Source { module, .. })) if module == &name("Api")),
            "{report:?}"
        );
        assert!(report.states.is_none());
    }
}

/// Remove one explicit visibility override, leaving the existing inherited
/// section default in force. The second visit returns unsupported, so ordinary
/// recursive expansion terminates without discarding the declaration wrapper.
fn inherited_visibility_function() -> IrDecl {
    let mut declaration = function("SourceLibrary.attributeProbe", Behavior::Identity);
    let IrDecl::Function { body, .. } = &mut declaration else {
        unreachable!()
    };
    let call = |target: &str, args: &[u64]| IrExpr::Fap {
        function: name(target),
        args: args.iter().copied().map(IrArg::Var).collect(),
    };
    body.stmts = vec![
        bind(3, IrExpr::Lit(IrLit::Num(IrNat::Small(0)))),
        bind(4, IrExpr::Lit(IrLit::Num(IrNat::Small(2)))),
        bind(5, call("Lean.Syntax.getArg", &[0, 4])),
        bind(6, call("Lean.Syntax.getArg", &[5, 3])),
        IrStmt::VDecl {
            x: 7,
            ty: IrType::UInt8,
            expr: call("Lean.Syntax.isMissing", &[6]),
        },
    ];
    *body.terminal = IrTerminal::Case {
        type_name: name("Bool"),
        x: 7,
        x_type: IrType::UInt8,
        alts: vec![
            IrAlt::Ctor {
                info: IrCtorInfo {
                    name: name("Bool.true"),
                    cidx: 1,
                    size: 0,
                    usize: 0,
                    ssize: 0,
                },
                body: IrBody {
                    stmts: vec![
                        bind(
                            8,
                            IrExpr::Lit(IrLit::Num(IrNat::Small(
                                layout::EXCEPTION_UNSUPPORTED_TAG as u64,
                            ))),
                        ),
                        bind(
                            9,
                            ctor(layout::RESULT_ERROR, "EStateM.Result.error", &[8, 2]),
                        ),
                    ],
                    terminal: Box::new(IrTerminal::Ret(IrArg::Var(9))),
                },
            },
            IrAlt::Default {
                body: IrBody {
                    stmts: vec![
                        bind(10, call("Lean.Syntax.getArg", &[0, 3])),
                        bind(11, IrExpr::Proj { i: 0, x: 0 }),
                        bind(12, IrExpr::Proj { i: 1, x: 0 }),
                        bind(13, IrExpr::Proj { i: 2, x: 0 }),
                        bind(14, call("Array.set!", &[13, 4, 10])),
                        bind(
                            15,
                            ctor(layout::SYNTAX_NODE, "Lean.Syntax.node", &[11, 12, 14]),
                        ),
                        bind(16, ctor(layout::RESULT_OK, "EStateM.Result.ok", &[15, 2])),
                    ],
                    terminal: Box::new(IrTerminal::Ret(IrArg::Var(16))),
                },
            },
        ],
    };
    declaration
}

#[test]
fn module_public_routing_uses_the_final_macro_generated_visibility_modifiers() {
    let (imported, mut code) = batches::artifact_import_fixture_with_extra_rows(&[(
        "Lean.Parser.Command.declModifiers",
        "SourceLibrary.attributeProbe",
        Some("ModifierRewrite"),
    )]);
    let declaration = code
        .iter_mut()
        .flat_map(|module| &mut module.decls)
        .find(|declaration| declaration.name() == &name("SourceLibrary.attributeProbe"))
        .unwrap();
    *declaration = inherited_visibility_function();
    for (body, exported) in [
        (
            "open scoped ModifierRewrite\npublic def shifted : Nat := 7 + 11",
            false,
        ),
        (
            "public section\nopen scoped ModifierRewrite\nprivate def shifted : Nat := 7 + 11\nend",
            true,
        ),
    ] {
        let source = format!("module\nprelude\npublic import SourceLibrary\n{body}");
        let report = check(
            &imported,
            &code,
            &[("Main", "prelude\nimport Api"), ("Api", &source)],
            MacroTreeLimits::default(),
            None,
        );
        let checked = succeeded(&report);
        let declaration = checked.checked.engine.environment().find(&name("shifted"));
        if exported {
            assert!(
                matches!(declaration, Some(ConstantInfo::Axiom(signature)) if !signature.is_unsafe)
            );
        } else {
            assert!(declaration.is_none());
        }
        assert!(
            !checked
                .checked
                .engine
                .environment()
                .contains(&private("Api", "shifted"))
        );
        assert_eq!(report.attempts.len(), 4);
        assert_eq!(
            report.attempts[0].declaration,
            name("SourceLibrary.attributeProbe")
        );
    }
}

#[test]
fn rewritten_public_declarations_keep_the_public_instance_activation_timeline() {
    let (imported, mut code) = batches::artifact_import_fixture_with_extra_rows(&[(
        "Lean.Parser.Command.declModifiers",
        "SourceLibrary.attributeProbe",
        Some("ModifierRewrite"),
    )]);
    let declaration = code
        .iter_mut()
        .flat_map(|module| &mut module.decls)
        .find(|declaration| declaration.name() == &name("SourceLibrary.attributeProbe"))
        .unwrap();
    *declaration = inherited_visibility_function();
    let source = r#"module
prelude
public import SourceLibrary
public class Pick where
  value : Nat
instance privateRow : Pick := Pick.mk 99
namespace Regional
@[expose] public scoped instance regional : Pick := Pick.mk 7
end Regional
open scoped Regional
@[expose] public instance later : Pick := Pick.mk 13
open scoped Regional
@[expose] public section
open scoped ModifierRewrite
private def shifted : Nat := Pick.value
end
"#;
    // The private registration makes the two journals' activation anchors
    // different. In the public world, opening Regional precedes the equal-
    // priority global registration of later; reopening Regional is idempotent.
    // Removing `private` then selects that public world and its own anchors,
    // rather than transplanting the private journal's selection state.
    let report = check(
        &imported,
        &code,
        &[
            (
                "Main",
                "prelude\nimport Api\ntheorem publicWinner : shifted = 13 := by rfl",
            ),
            ("Api", source),
        ],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    let environment = checked.checked.engine.environment();
    assert_declared_value(&checked.checked.engine, "shifted", 13);
    assert!(matches!(
        environment.find(&name("shifted")),
        Some(ConstantInfo::Defn(_))
    ));
    assert!(environment.contains(&name("publicWinner")));
    assert!(!environment.contains(&private("Api", "privateRow")));
    assert!(!environment.contains(&private("Api", "shifted")));
    let instances = fln_elab::instances::InstanceRegistry::read(environment).unwrap();
    let [instance] = instances.candidates(&name("Pick")) else {
        panic!("only the checked public global instance is active in the consumer")
    };
    assert_eq!(instance.declaration, name("later"));
    assert_eq!(report.attempts.len(), 2);
    for attempt in &report.attempts {
        assert_eq!(attempt.declaration, name("SourceLibrary.attributeProbe"));
        assert!(attempt.vm_usage.is_some());
    }
    assert_eq!(
        report.states.as_ref().unwrap()[&name("Api")].expanded_macro_declarations,
        [name("SourceLibrary.attributeProbe")]
    );
}
