//! Native Nonempty deriving over a genuinely admitted selected Prelude slice.
//! The fixture retains the original choice axiom and ofNonempty definition;
//! runtime checks consume derived proofs only through ordinary proof erasure.
#![forbid(unsafe_code)]

use fln::source_check::modules::{SourceModuleCheck, SourceModuleCheckLimits};
use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, EngineExecutionLimits, Expr, ExprNode,
    KVMap, Name, SourceCheckLimits, VmExit,
};
use fln_elab::instances::InstanceRegistry;
use fln_elab::reducibility::{Reducibility, ReducibilityTable};
use std::path::PathBuf;
use std::sync::OnceLock;

#[path = "source_deriving_nonempty/fixture.rs"]
mod fixture;

const STACK: usize = 16 * 1024 * 1024;
const BYTES: usize = 128 * 1024 * 1024;

const BASIC: &str = r#"
inductive Flag where
  | first
  | second
deriving Nonempty
structure Point (A : Type) where
  x : A
  y : A
deriving Nonempty
structure TaskLike (A : Type) where
  get : A
deriving Inhabited, Nonempty
def pointWitness : Nonempty (Point Nat) := inferInstance
def taskWitness : Nonempty (TaskLike Nat) := inferInstance
def ignoreWitness {A : Sort u} [Nonempty A] (n : Nat) : Nat := n + 1
"#;

const HEADERS: &str = r#"
structure Pair (A : Type u) (B : Type v) where
  first : A
  second : B
deriving Nonempty
def expectedPair {A : Type u} [Nonempty A] {B : Type v} [Nonempty B] :
    Nonempty (Pair A B) := inferInstance
structure Phantom (A B : Type) where
  value : A
deriving Nonempty
def expectedPhantom {A : Type} [Nonempty A] {B : Type} :
    Nonempty (Phantom A B) := inferInstance
inductive Lst (A : Type) where
  | nil
  | cons (head : A) (tail : Lst A)
deriving Nonempty
def expectedList {A : Type} : Nonempty (Lst A) := inferInstance
structure Existing (A : Type) [Nonempty A] where
  value : A
deriving Nonempty
def expectedExisting {A : Type} [Nonempty A] {original : Nonempty A} :
    Nonempty (@Existing A original) := inferInstance
"#;

const FALLBACK: &str = r#"
inductive NoValues where
inductive Pick (A B : Type) where
  | impossible (f : Nat -> NoValues)
  | good (value : B)
deriving Nonempty
def expectedPick {A B : Type} [Nonempty B] : Nonempty (Pick A B) := inferInstance
structure FunctionCase (A B : Type) where
  run : A -> B
deriving Nonempty
def expectedFunction {A B : Type} [Nonempty B] : Nonempty (FunctionCase A B) := inferInstance
inductive Recursive where
  | step (previous : Recursive)
  | base
deriving Nonempty
def recursiveWitness : Nonempty Recursive := inferInstance
inductive DependentFallback where
  | hidden (A : Type) (value : A)
  | done
deriving Nonempty
def fallbackWitness : Nonempty DependentFallback := inferInstance
"#;

const INDEXED: &str = r#"
inductive Indexed : Nat -> Type where
  | zero : Indexed 0
  | any (n : Nat) : Indexed n
deriving Nonempty
def expectedIndexed {n : Nat} : Nonempty (Indexed n) := inferInstance
inductive Interleaved (A : Type) : Type -> Nat -> Type where
  | mk (B : Type) (n : Nat) (a : A) (b : B) : Interleaved A B n
deriving Nonempty
def expectedInterleaved {A : Type} [Nonempty A] {B : Type} [Nonempty B] {n : Nat} :
    Nonempty (Interleaved A B n) := inferInstance
"#;

const PUBLIC_MODULE: &str = r#"module
prelude
public structure TaskLike (A : Type) where
  get : A
  deriving Inhabited, Nonempty
"#;

const PRIVATE_PROOF_MODULE: &str = r#"module
prelude
public inductive Field where
  | mk (n : Nat)
private instance fieldWitness : Nonempty Field := Nonempty.intro (Field.mk 7)
public structure Wrapper where
  field : Field
deriving instance Nonempty for Wrapper
"#;

const MIXED_MODULE: &str = r#"module
prelude
public inductive Published where
  | value
inductive Hidden where
  | value
deriving instance Nonempty for Published, Hidden
def localWitness : Nonempty Published := inferInstance
"#;

const EXPOSED_MODULE: &str = r#"module
prelude
@[expose] public section
structure Visible (A : Type) where
  value : A
  deriving Nonempty
end
"#;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))
}

fn foundation() -> Option<&'static Engine> {
    static ENGINE: OnceLock<Option<Engine>> = OnceLock::new();
    ENGINE
        .get_or_init(|| {
            let library = std::env::var_os("FLN_REFERENCE_LIB")
                .map(PathBuf::from)
                .or_else(|| {
                    std::env::var_os("HOME").map(|home| {
                        PathBuf::from(home)
                            .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
                    })
                })
                .filter(|path| path.is_dir());
            let Some(library) = library else {
                assert!(
                    std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                    "the actual pinned Prelude artifacts are required"
                );
                eprintln!("SKIP: pinned Reference lib/lean unavailable");
                return None;
            };
            Some(fixture::admitted(&library))
        })
        .as_ref()
}

fn with_foundation(run: impl FnOnce(&Engine) + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            if let Some(engine) = foundation() {
                run(engine);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(admission()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("the generated proof and its consumers pass both checking engines")
    .engine
}

fn checked_modules(base: &Engine, files: &[(&str, &str)]) -> SourceModuleCheck {
    let names: Vec<_> = files.iter().map(|(label, _)| name(label)).collect();
    let modules: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| fln::SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    base.check_source_modules(
        &modules,
        &names[0],
        &KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())),
    )
    .unwrap_or_else(|error| panic!("{files:?}\n{error:?}"))
    .into_complete()
    .expect("the complete source module group passes both checkers")
}

fn private(module: &str, declaration: &str) -> Name {
    Name::num(name(&format!("_private.{module}")), 0).append_core(&name(declaration))
}

fn alpha_type(expr: &Expr) -> Expr {
    match expr.node() {
        ExprNode::Sort { level } => Expr::sort(level.normalize()),
        ExprNode::Const { name, levels } => Expr::const_(
            name.clone(),
            levels
                .iter()
                .map(fln_core::level::Level::normalize)
                .collect(),
        ),
        ExprNode::ForallE {
            binder_type,
            body,
            binder_info,
            ..
        } => Expr::forall_e(
            Name::anonymous(),
            alpha_type(binder_type),
            alpha_type(body),
            *binder_info,
        ),
        ExprNode::App { f, a } => Expr::app(alpha_type(f), alpha_type(a)),
        _ => expr.clone(),
    }
}

fn same_type(engine: &Engine, generated: &str, expected: &str) {
    let generated = engine
        .environment()
        .find(&name(generated))
        .unwrap()
        .constant_val();
    let expected = engine
        .environment()
        .find(&name(expected))
        .unwrap()
        .constant_val();
    assert_eq!(generated.level_params, expected.level_params);
    // Inference may retain max v u where the written header uses max u v.
    // Normalize only universe representation: every binder style, argument,
    // dictionary position and dependency still participates in exact equality.
    assert_eq!(alpha_type(&generated.type_), alpha_type(&expected.type_));
    let verdict = fln_kernel::check_def_eq(
        engine.environment(),
        &generated.level_params,
        &generated.type_,
        &expected.type_,
        admission().kernel,
    );
    assert!(
        matches!(
            &verdict,
            fln::Outcome::Complete(fln_kernel::verdict::Verdict::Accepted { .. })
        ),
        "the complete derived and expected headers must be kernel-convertible: {verdict:?}"
    );
}

fn references(expr: &Expr, expected: &Name) -> bool {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        match expr.node() {
            ExprNode::Const { name, .. } if name == expected => return true,
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    false
}

#[test]
fn real_nonempty_proofs_pass_both_checkers_and_erase_before_native_execution() {
    with_foundation(|base| {
        let before = base.logical_root(&KVMap::new());
        let engine = checked(base, BASIC);
        for label in [
            "instNonemptyFlag",
            "instNonemptyPoint",
            "instNonemptyTaskLike",
        ] {
            let Some(ConstantInfo::Thm(theorem)) = engine.environment().find(&name(label)) else {
                panic!("derived Nonempty must be a checked theorem: {label}");
            };
            assert!(!theorem.value.has_fvar());
            assert!(!theorem.value.has_loose_bvars());
            assert!(!theorem.value.has_expr_mvar());
            assert!(!theorem.value.has_level_mvar());
            if label != "instNonemptyFlag" {
                assert!(references(&theorem.value, &name("Classical.ofNonempty")));
            }
            assert!(!base.environment().contains(&name(label)));
        }
        let report = engine
            .execute_source_definitions(
                &[b"#eval ignoreWitness (A := Point Nat) 41\n#eval ignoreWitness (A := TaskLike Nat) 6"],
                &KVMap::new(),
                EngineExecutionLimits::new(admission().kernel),
            )
            .unwrap()
            .into_complete()
            .expect("derived evidence is erased, not executed as choice");
        assert_eq!(report.executions.len(), 2);
        for (execution, expected) in report.executions.iter().zip(["42", "7"]) {
            let VmExit::Returned(value) = &execution.exit else {
                panic!("proof consumer did not return normally");
            };
            assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some(expected));
            let replay = fln::execute_flbc_artifact(
                &execution.flbc_artifact,
                &KVMap::new(),
                Default::default(),
            )
            .unwrap()
            .into_complete()
            .expect("ordinary proof erasure survives FLBC replay");
            let VmExit::Returned(value) = replay else {
                panic!("proof consumer artifact did not return normally");
            };
            assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some(expected));
        }
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert_eq!(
            engine.logical_root(&KVMap::new()),
            checked(base, BASIC).logical_root(&KVMap::new())
        );
    });
}

#[test]
fn assumptions_are_interleaved_and_only_successful_constructor_requirements_survive() {
    with_foundation(|base| {
        let engine = checked(base, HEADERS);
        for (generated, expected) in [
            ("instNonemptyPair", "expectedPair"),
            ("instNonemptyPhantom", "expectedPhantom"),
            ("instNonemptyLst", "expectedList"),
            ("instNonemptyExisting", "expectedExisting"),
        ] {
            same_type(&engine, generated, expected);
        }
    });
}

#[test]
fn failed_constructors_backtrack_without_requiring_impossible_or_recursive_fields() {
    with_foundation(|base| {
        let engine = checked(base, FALLBACK);
        same_type(&engine, "instNonemptyPick", "expectedPick");
        same_type(&engine, "instNonemptyFunctionCase", "expectedFunction");
        for (instance, constructor, unused) in [
            ("instNonemptyPick", "Pick.good", "Pick.impossible"),
            ("instNonemptyRecursive", "Recursive.base", "Recursive.step"),
            (
                "instNonemptyDependentFallback",
                "DependentFallback.done",
                "DependentFallback.hidden",
            ),
        ] {
            let Some(ConstantInfo::Thm(theorem)) = engine.environment().find(&name(instance))
            else {
                panic!("missing derived proof {instance}");
            };
            assert!(references(&theorem.value, &name(constructor)));
            assert!(!references(&theorem.value, &name(unused)));
        }
    });
}

#[test]
fn indexed_constructor_results_determine_arguments_before_nonempty_search() {
    with_foundation(|base| {
        let engine = checked(base, INDEXED);
        same_type(&engine, "instNonemptyIndexed", "expectedIndexed");
        same_type(&engine, "instNonemptyInterleaved", "expectedInterleaved");
    });
}

#[test]
fn arbitrary_props_sorts_and_dependent_fields_refuse_without_new_axioms_or_publication() {
    with_foundation(|base| {
        let before = base.logical_root(&KVMap::new());
        for source in [
            "inductive EmptyCase where\nderiving Nonempty",
            "structure PropCase (P : Prop) where\n proof : P\nderiving Nonempty",
            "structure SortCase (A : Sort u) where\n value : A\nderiving Nonempty",
            "inductive Hidden where\n | mk (A : Type) (value : A)\nderiving Nonempty",
            "structure PropExisting (P : Prop) [Nonempty P] where\n proof : P\nderiving Nonempty",
            "structure Dependent (A : Type) (B : A -> Type) where\n a : A\n b : B a\nderiving Nonempty",
            "structure Incomplete where\n value : Nat\nderiving Nonempty, UnknownHandler",
        ] {
            assert!(
                base.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(admission()),
                )
                .is_err(),
                "the exact pin refuses this program: {source}"
            );
            assert_eq!(base.logical_root(&KVMap::new()), before);
        }
        // The eligibility restriction belongs to generated untyped variables,
        // not ordinary written class binders in another elaboration context.
        checked(
            base,
            r#"
def typedLocal {P : Prop} {h : Nonempty P} : Nonempty P := inferInstance
def typedInstance {P : Prop} [h : Nonempty P] : Nonempty P := inferInstance
inductive Recovery where
  | done
deriving Nonempty
def recovered : Nonempty Recovery := inferInstance
"#,
        );
    });
}

#[test]
fn public_nonempty_instances_keep_their_checked_proofs_private_and_replay_safe_interfaces() {
    with_foundation(|base| {
        let local = checked_modules(base, &[("Api", PUBLIC_MODULE)]);
        let local_environment = local.checked.engine.environment();
        let label = name("instNonemptyTaskLike");
        let Some(ConstantInfo::Thm(proof)) = local_environment.find(&label) else {
            panic!("the defining module must retain the checked derived theorem");
        };
        assert!(references(&proof.value, &name("Classical.ofNonempty")));
        assert_eq!(
            ReducibilityTable::effective(local_environment)
                .unwrap()
                .status(&label),
            Reducibility::Semireducible
        );
        let imported = checked_modules(
            base,
            &[
                (
                    "Main",
                    "module\nprelude\npublic import Api\npublic theorem client : Nonempty (TaskLike Nat) := inferInstance",
                ),
                ("Api", PUBLIC_MODULE),
            ],
        );
        let environment = imported.checked.engine.environment();
        let Some(ConstantInfo::Axiom(interface)) = environment.find(&label) else {
            panic!("the importing module sees only the checked proof interface");
        };
        assert_eq!(interface.base, proof.base);
        assert!(!interface.is_unsafe);
        assert!(matches!(
            environment.find(&name("client")),
            Some(ConstantInfo::Thm(_))
        ));
        assert!(matches!(
            environment.find(&name("instInhabitedTaskLike")),
            Some(ConstantInfo::Defn(_))
        ));
        assert!(
            InstanceRegistry::read(environment)
                .unwrap()
                .candidates(&name("Nonempty"))
                .iter()
                .any(|row| row.declaration == label)
        );
        assert_eq!(
            ReducibilityTable::effective(environment)
                .unwrap()
                .status(&label),
            Reducibility::Semireducible
        );
    });
}

#[test]
fn standalone_public_nonempty_proofs_can_use_private_instances_without_exporting_them() {
    with_foundation(|base| {
        let local = checked_modules(base, &[("Api", PRIVATE_PROOF_MODULE)]);
        let environment = local.checked.engine.environment();
        let secret = private("Api", "fieldWitness");
        let label = name("instNonemptyWrapper");
        let Some(ConstantInfo::Thm(proof)) = environment.find(&label) else {
            panic!("the actual private instance must be consumed by a checked theorem");
        };
        assert!(references(&proof.value, &secret));
        let imported = checked_modules(
            base,
            &[
                (
                    "Main",
                    "module\nprelude\npublic import Api\npublic theorem client : Nonempty Wrapper := inferInstance",
                ),
                ("Api", PRIVATE_PROOF_MODULE),
            ],
        );
        let environment = imported.checked.engine.environment();
        let Some(ConstantInfo::Axiom(interface)) = environment.find(&label) else {
            panic!("the public consumer must receive the checked proof interface");
        };
        assert_eq!(interface.base, proof.base);
        assert!(!environment.contains(&secret));
        assert!(
            InstanceRegistry::read(environment)
                .unwrap()
                .candidates(&name("Nonempty"))
                .iter()
                .all(|row| row.declaration != secret)
        );
        assert!(
            imported
                .checked
                .engine
                .check_source_files(
                    &[b"def unavailable : Nonempty Field := inferInstance"],
                    &KVMap::new(),
                    SourceCheckLimits::new(admission()),
                )
                .is_err(),
            "private field evidence must not become an imported instance"
        );
    });
}

#[test]
fn a_mixed_public_private_deriving_group_keeps_all_proof_instances_private() {
    with_foundation(|base| {
        let local = checked_modules(base, &[("Api", MIXED_MODULE)]);
        let local_environment = local.checked.engine.environment();
        for label in ["instNonemptyPublished", "instNonemptyHidden"] {
            assert!(matches!(
                local_environment.find(&private("Api", label)),
                Some(ConstantInfo::Thm(_))
            ));
            assert!(!local_environment.contains(&name(label)));
        }
        let imported = checked_modules(
            base,
            &[
                (
                    "Main",
                    "module\nprelude\npublic import Api\npublic def value : Published := Published.value",
                ),
                ("Api", MIXED_MODULE),
            ],
        );
        let environment = imported.checked.engine.environment();
        assert!(!environment.contains(&private("Api", "Hidden")));
        assert!(!environment.contains(&private("Api", "instNonemptyPublished")));
        assert!(
            imported
                .checked
                .engine
                .check_source_files(
                    &[b"def unavailable : Nonempty Published := inferInstance"],
                    &KVMap::new(),
                    SourceCheckLimits::new(admission()),
                )
                .is_err()
        );
    });
}

#[test]
fn an_exposed_section_does_not_expose_nonempty_proofs_or_private_constructors() {
    with_foundation(|base| {
        let local = checked_modules(base, &[("Api", EXPOSED_MODULE)]);
        assert!(matches!(
            local
                .checked
                .engine
                .environment()
                .find(&name("instNonemptyVisible")),
            Some(ConstantInfo::Thm(_))
        ));
        let imported = checked_modules(
            base,
            &[
                (
                    "Main",
                    "module\nprelude\npublic import Api\npublic theorem client : Nonempty (Visible Nat) := inferInstance",
                ),
                ("Api", EXPOSED_MODULE),
            ],
        );
        assert!(matches!(
            imported
                .checked
                .engine
                .environment()
                .find(&name("instNonemptyVisible")),
            Some(ConstantInfo::Axiom(_))
        ));
        // The pin permits a hidden derived proof to consume private evidence
        // even inside an exposed section, for both suffix and standalone forms.
        for declaration in [
            "@[expose] public section\nstructure Wrapper where\n field : Field\n deriving Nonempty\nend",
            "public structure Wrapper where\n field : Field\n@[expose] public section\nderiving instance Nonempty for Wrapper\nend",
        ] {
            let source = format!(
                "module\nprelude\npublic inductive Field where\n | mk (n : Nat)\nprivate instance fieldWitness : Nonempty Field := Nonempty.intro (Field.mk 7)\n{declaration}"
            );
            let local = checked_modules(base, &[("Api", &source)]);
            let Some(ConstantInfo::Thm(proof)) = local
                .checked
                .engine
                .environment()
                .find(&name("instNonemptyWrapper"))
            else {
                panic!("the exposed derived proof must still be checked privately");
            };
            assert!(references(&proof.value, &private("Api", "fieldWitness")));
            let imported = checked_modules(
                base,
                &[
                    (
                        "Main",
                        "module\nprelude\npublic import Api\npublic theorem client : Nonempty Wrapper := inferInstance",
                    ),
                    ("Api", &source),
                ],
            );
            let environment = imported.checked.engine.environment();
            assert!(matches!(
                environment.find(&name("instNonemptyWrapper")),
                Some(ConstantInfo::Axiom(_))
            ));
            assert!(!environment.contains(&private("Api", "fieldWitness")));
        }
        let module = name("PrivateCtor");
        assert!(
            base.check_source_modules(
                &[fln::SourceModuleInput {
                    name: &module,
                    source: b"module\nprelude\n@[expose] public section\nstructure PrivateFields where\n private value : Nat\n deriving Nonempty\nend",
                }],
                &module,
                &KVMap::new(),
                SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())),
            )
            .is_err(),
            "the pin refuses exposed deriving with private constructors"
        );
    });
}
