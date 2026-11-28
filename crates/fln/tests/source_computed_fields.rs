//! Computed fields retain checked logical equations and execute cached layouts.
//!
//! The exact SUITE.lock executable is an independent test oracle only. Native
//! source admission and bytecode execution never invoke it. Prelude import has
//! a separate large-stack budget; all new source runs use the ordinary 2 MiB
//! kernel budget.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::{SourceOleanImport, SourceOleanImportLimits};
use fln::source_check::modules::{
    SourceModuleArtifact, SourceModuleBuildError, SourceModuleCheckError, SourceModuleCheckLimits,
    SourceModuleIrError, SourceModuleIrLimits,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, Environment, KVMap, Name,
    OleanCheckLimits, OleanModuleInput, OleanWriteBudget, SourceCheckLimits, SourceModuleInput,
    VmExit,
};
use fln_comp::flbc::{
    CallableResultOwnership, Function, FunctionId, Instruction, Program, Register, ValidatedProgram,
};
use fln_core::expr::{BinderInfo, Expr, ExprNode};
use fln_elab::implemented_by::ImplementedByTable;
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{
    OnceLock,
    atomic::{AtomicUsize, Ordering},
};

const IMPORT_STACK: usize = 64 * 1024 * 1024;
const SOURCE_STACK: usize = 2 * 1024 * 1024;
const SINGLE: &str = r#"
inductive Cache where
  | empty
  | add (n : Nat) (tail : Cache)
with
  @[computed_field, inline] total : Cache → Nat
    | .empty => 0
    | .add n tail => Nat.add n tail.total
"#;
const CROSS: &str = r#"
inductive Cross where
  | empty
  | add (n : Nat) (tail : Cross)
with
  @[computed_field, inline] first : Cross → Nat
    | .empty => 0
    | .add n tail => Nat.add n tail.second
  @[computed_field] second : Cross → Nat
    | .empty => 0
    | .add n tail => Nat.add (Nat.add n tail.first) 10
"#;
const WORD: &str = r#"
inductive Digest where
  | empty
  | add (n : UInt64) (tail : Digest)
with
  @[computed_field, inline] hash : Digest → UInt64
    | .empty => UInt64.ofNatLT 1 (of_decide_eq_true rfl)
    | .add n tail => mixHash tail.hash n
"#;
const PACKED: &str = r#"
inductive PackedCache where
  | empty
  | mk (flag : Bool) (word : UInt64) (payload : Nat)
with
  @[computed_field, inline] wide : PackedCache → UInt64
    | .empty => UInt64.ofNatLT 1 (of_decide_eq_true rfl)
    | .mk _ n _ => n
  @[computed_field] flag : PackedCache → Bool
    | .empty => false
    | .mk f _ _ => match f with
      | false => true
      | true => false
"#;
const WIDTHS: &str = r#"
inductive Widths where
  | empty
  | pack (a : UInt8) (b : UInt16) (c : UInt32) (d : UInt64)
with
  @[computed_field] tally : Widths → Nat
    | .empty => 0
    | .pack _ _ _ _ => 42
"#;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(SOURCE_STACK))
}
fn check_limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel))
}

struct Fixture {
    imported: SourceOleanImport,
    compiler: PathBuf,
    library: PathBuf,
    prelude: [Vec<u8>; 3],
}

fn with_fixture(test: impl FnOnce(&Fixture) + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(IMPORT_STACK)
        .spawn(move || {
            static FIXTURE: OnceLock<Option<Fixture>> = OnceLock::new();
            let fixture = FIXTURE.get_or_init(|| {
                let library = std::env::var_os("FLN_REFERENCE_LIB")
                    .map(PathBuf::from)
                    .or_else(|| {
                        std::env::var_os("HOME").map(|home| {
                            PathBuf::from(home)
                                .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
                        })
                    })
                    .filter(|path| path.join("Init/Prelude.olean").is_file());
                let Some(library) = library else {
                    assert!(
                        std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                        "computed-field tests require the exact pinned Reference library"
                    );
                    eprintln!("SKIP: pinned Reference library absent");
                    return None;
                };
                let compiler = std::env::var_os("FLN_REFERENCE_LEAN")
                    .map(PathBuf::from)
                    .unwrap_or_else(|| {
                        library.parent().unwrap().parent().unwrap().join("bin/lean")
                    });
                let commit = Command::new(&compiler).arg("--githash").output().unwrap();
                assert!(commit.status.success());
                assert_eq!(
                    String::from_utf8(commit.stdout).unwrap().trim(),
                    fln::OLEAN_PIN_COMMIT,
                    "the test oracle must match SUITE.lock exactly"
                );
                let path = library.join("Init/Prelude.olean");
                let parts = [
                    std::fs::read(&path).unwrap(),
                    std::fs::read(path.with_extension("olean.server")).unwrap(),
                    std::fs::read(path.with_extension("olean.private")).unwrap(),
                ];
                let module = name("Init.Prelude");
                let inputs = [OleanModuleInput {
                    name: &module,
                    artifact: &parts[0],
                    server_artifact: Some(&parts[1]),
                    private_artifact: Some(&parts[2]),
                }];
                let imported = Engine::builder()
                    .build_empty()
                    .import_olean_modules_for_source(
                        &inputs,
                        std::slice::from_ref(&module),
                        &KVMap::new(),
                        SourceOleanImportLimits::new(OleanCheckLimits::new(
                            IMPORT_STACK,
                            Budget::for_stack_bytes(IMPORT_STACK),
                        )),
                    )
                    .expect("the original pinned Prelude passes checked import")
                    .into_complete()
                    .expect("checked Prelude import completes within its separate import budget");
                let native_families = fln_elab::computed_fields::families(
                    imported.engine.environment(),
                    Default::default(),
                )
                .expect("imported computed-field provenance has a valid journal");
                eprintln!("pinned Prelude recovered native computed families: {native_families:?}");
                Some(Fixture {
                    imported,
                    compiler,
                    library,
                    prelude: parts,
                })
            });
            if let Some(fixture) = fixture {
                test(fixture);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

fn reference(compiler: &Path, source: &str, expected: Option<&str>) -> String {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory =
        std::env::temp_dir().join(format!("fln-computed-fields-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let path = directory.join(format!("{}.lean", NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::write(&path, source).unwrap();
    let output = Command::new(compiler)
        .arg("-j1")
        .arg(&path)
        .output()
        .unwrap();
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    if let Some(expected) = expected {
        assert!(output.status.success(), "{source}\n{text}");
        assert_eq!(text.trim(), expected, "{source}");
    } else {
        assert!(
            !output.status.success(),
            "the pin unexpectedly accepted {source}\n{text}"
        );
    }
    text
}

fn checked(engine: &Engine, source: &str) -> Engine {
    engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), check_limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("computed-field source completes with the ordinary source budget")
        .engine
}

fn execute(engine: &Engine, source: &str, expected: &[&str]) -> Vec<Vec<u8>> {
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let report = engine
        .execute_source_definitions(&[source.as_bytes()], &options, limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("computed-field execution completes with ordinary source and VM budgets");
    assert_eq!(report.executions.len(), expected.len());
    let mut artifacts = Vec::new();
    for (execution, expected) in report.executions.iter().zip(expected) {
        let VmExit::Returned(returned) = &execution.exit else {
            panic!(
                "computed-field execution did not return: {:?}",
                execution.exit
            );
        };
        assert_eq!(
            fln::nat_decimal(&returned.value).as_deref(),
            Some(*expected)
        );
        let replay =
            fln::execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
                .expect("the native computed-field artifact validates")
                .into_complete()
                .expect("computed-field bytecode replays without a source environment");
        let VmExit::Returned(returned) = replay else {
            panic!("computed-field bytecode replay did not return");
        };
        assert_eq!(
            fln::nat_decimal(&returned.value).as_deref(),
            Some(*expected)
        );
        artifacts.push(execution.flbc_artifact.clone());
    }
    assert_eq!(engine.logical_root(&options), before);
    artifacts
}

fn mentions(expression: &Expr, requested: &Name) -> bool {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        match expression.node() {
            ExprNode::Const { name, .. } if name == requested => return true,
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

fn cache_read(instruction: &Instruction) -> bool {
    matches!(
        instruction,
        Instruction::CtorField {
            expected_tag: 1,
            expected_fields: 3,
            field: 0,
            ..
        }
    )
}

fn execute_stored_cache_control(bytecode: &ValidatedProgram) {
    let getter = bytecode
        .functions()
        .iter()
        .find(|function| {
            function.arity == 1
                && function.result_ownership == CallableResultOwnership::OwnedOrScalar
                && function.code.iter().any(cache_read)
        })
        .expect("generated Nat getter has an executable cached projection");
    let mut functions = bytecode.functions().to_vec();
    let entry = FunctionId::new(u32::try_from(functions.len()).unwrap());
    let r = Register::new;
    functions.push(Function {
        id: entry,
        arity: 0,
        parameter_ownership: Vec::new(),
        register_count: 5,
        result_ownership: CallableResultOwnership::OwnedOrScalar,
        code: vec![
            Instruction::Nat {
                dst: r(0),
                value: 99,
            },
            Instruction::Nat {
                dst: r(1),
                value: 2,
            },
            Instruction::Nat {
                dst: r(2),
                value: 0,
            },
            Instruction::Ctor {
                dst: r(3),
                tag: 1,
                fields: vec![r(0), r(1), r(2)],
                scalar_bytes: Vec::new(),
            },
            Instruction::Call {
                dst: r(4),
                function: getter.id,
                args: vec![r(3)],
                argument_ownership: getter.parameter_ownership.clone(),
                result_ownership: getter.result_ownership,
            },
            Instruction::Return { src: r(4) },
        ],
    });
    // This representation control stays below source elaboration and grants
    // no unsafeCast primitive or environment authority.
    let controlled = fln_comp::flbc::validate(Program::new(entry, functions)).unwrap();
    let bytes = fln_comp::flbc::encode_canonical(&controlled, Default::default()).unwrap();
    let result = fln::execute_flbc_artifact(&bytes, &KVMap::new(), Default::default())
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = result else {
        panic!("stored-cache control did not return");
    };
    assert_eq!(
        fln::nat_decimal(&value.value).as_deref(),
        Some("99"),
        "getter must return stored cache99, not recompute payload2"
    );
}

fn assert_generated(engine: &Engine, family: &str, constructor: &str, fields: &[&str], count: u32) {
    let logical = format!("{family}.{constructor}");
    let implementation = format!("{logical}._impl");
    let Some(ConstantInfo::Ctor(original)) = engine.environment().find(&name(&logical)) else {
        panic!("missing logical constructor {logical}");
    };
    let Some(ConstantInfo::Ctor(cached)) = engine.environment().find(&name(&implementation)) else {
        panic!("missing generated constructor {implementation}");
    };
    assert_eq!(cached.num_fields, original.num_fields + count);
    assert_eq!(cached.induct, name(&format!("{family}._impl")));
    let Some(ConstantInfo::Defn(constructor_override)) = engine
        .environment()
        .find(&name(&format!("{logical}._override")))
    else {
        panic!("missing cached constructor override");
    };
    for field in fields {
        assert!(
            mentions(
                &constructor_override.value,
                &name(&format!("{family}.{field}"))
            ),
            "constructor cache construction must read the child's {field} cache without unfolding its logical recursion"
        );
    }
    let replacements = ImplementedByTable::read(engine.environment()).unwrap();
    for operation in std::iter::once(logical)
        .chain(std::iter::once(format!("{family}.casesOn")))
        .chain(fields.iter().map(|field| format!("{family}.{field}")))
    {
        let target = format!("{operation}._override");
        assert_eq!(replacements.get(&name(&operation)), Some(&name(&target)));
        let Some(ConstantInfo::Defn(definition)) = engine.environment().find(&name(&target)) else {
            panic!("missing generated executable definition {target}");
        };
        assert_eq!(definition.safety, DefinitionSafety::Unsafe);
        assert!(!definition.value.has_fvar());
        assert!(!definition.value.has_expr_mvar());
        assert!(!definition.value.has_level_mvar());
        assert!(!definition.value.has_loose_bvars());
    }
    for field in fields {
        let getter = format!("{family}.{field}");
        let Some(ConstantInfo::Defn(definition)) = engine.environment().find(&name(&getter)) else {
            panic!("missing checked logical definition {getter}");
        };
        assert_eq!(definition.safety, DefinitionSafety::Safe);
        assert!(
            !engine
                .environment()
                .contains(&name(&format!("{getter}._unsafe_rec")))
        );
    }
}

#[test]
fn recursive_fields_preserve_logical_equations_aliases_and_cached_bytecode() {
    with_fixture(|fixture| {
        let source = format!(
            r#"{SINGLE}
def sample : Cache := .add 2 (.add 3 .empty)
theorem empty_equation : Eq Cache.empty.total 0 := rfl
theorem add_equation (n : Nat) (tail : Cache) :
    Eq (Cache.add n tail).total (Nat.add n tail.total) := rfl
theorem sample_equation : Eq sample.total 5 := rfl
abbrev CacheAlias := Cache
def retain (value : CacheAlias) : CacheAlias := value
def observe (value : CacheAlias) : Nat := match value with
  | .empty => 0
  | .add n tail => Nat.add n tail.total
"#
        );
        let evaluations = "#eval sample.total\n#eval (retain sample).total\n#eval observe (retain sample)\n#eval Cache.empty.total\n";
        reference(
            &fixture.compiler,
            &format!("{source}{evaluations}"),
            Some("5\n5\n5\n0"),
        );
        let engine = checked(&fixture.imported.engine, &source);
        assert_generated(&engine, "Cache", "add", &["total"], 1);
        let artifacts = execute(&engine, evaluations, &["5", "5", "5", "0"]);
        assert_eq!(
            artifacts,
            execute(&engine, evaluations, &["5", "5", "5", "0"])
        );
        let bytecode = fln_comp::flbc::decode_canonical(&artifacts[0], Default::default()).unwrap();
        execute_stored_cache_control(&bytecode);
        assert!(bytecode.functions().iter().flat_map(|function| &function.code).any(|instruction| {
            matches!(instruction, Instruction::Ctor { tag: 1, fields, .. } if fields.len() == 3)
                || matches!(instruction, Instruction::CtorPacked { tag: 1, fields, .. } if fields.len() == 3)
        }), "runtime constructors must carry the computed cache as their third object field");
        assert!(
            bytecode
                .functions()
                .iter()
                .flat_map(|function| &function.code)
                .any(|instruction| {
                    matches!(
                        instruction,
                        Instruction::CtorField {
                            expected_tag: 1,
                            expected_fields: 3,
                            field: 0,
                            ..
                        }
                    )
                }),
            "the generated getter must read the stored first field of the cached representation"
        );
        assert!(
            !fixture
                .imported
                .engine
                .environment()
                .contains(&name("Cache"))
        );
    });
}

#[test]
fn mutually_recursive_fields_and_word_caches_execute_and_replay() {
    with_fixture(|fixture| {
        let cross = format!(
            r#"{CROSS}
def sample : Cross := .add 2 (.add 3 (.add 4 .empty))
theorem first_equation : Eq sample.first 19 := rfl
theorem second_equation : Eq sample.second 29 := rfl
"#
        );
        let evaluations = "#eval sample.first\n#eval sample.second\n";
        reference(
            &fixture.compiler,
            &format!("{cross}{evaluations}"),
            Some("19\n29"),
        );
        let engine = checked(&fixture.imported.engine, &cross);
        assert_generated(&engine, "Cross", "add", &["first", "second"], 2);
        execute(&engine, evaluations, &["19", "29"]);

        let word = format!(
            r#"{WORD}
def sample : Digest := .add (UInt64.ofNatLT 2 (of_decide_eq_true rfl))
  (.add (UInt64.ofNatLT 3 (of_decide_eq_true rfl)) .empty)
"#
        );
        let evaluations = "#eval BitVec.toNat (UInt64.toBitVec sample.hash)\n#eval BitVec.toNat (UInt64.toBitVec Digest.empty.hash)\n";
        reference(
            &fixture.compiler,
            &format!("{word}{evaluations}"),
            Some("5467619628213459297\n1"),
        );
        let engine = checked(&fixture.imported.engine, &word);
        assert_generated(&engine, "Digest", "add", &["hash"], 1);
        // Native Golem keeps imported UInt64 as its checked record carrier;
        // only the hash primitive uses a scalar. The family still adds a real
        // cached field, independent of the future pinned module IR layout.
        let artifacts = execute(&engine, evaluations, &["5467619628213459297", "1"]);
        let bytecode = fln_comp::flbc::decode_canonical(&artifacts[0], Default::default()).unwrap();
        assert!(bytecode.functions().iter().flat_map(|function| &function.code).any(|instruction| {
            matches!(instruction, Instruction::Ctor { tag: 1, fields, .. } if fields.len() == 3)
        }), "cached UInt64 values must occupy the augmented native record representation");
    });
}

#[test]
fn invalid_fields_refuse_the_whole_family_without_publishing_a_partial_world() {
    with_fixture(|fixture| {
        let cases = [
            (
                "one constructor",
                "inductive Bad where | mk (n : Nat)\nwith\n  @[computed_field] total : Bad → Nat\n    | .mk n => n\n",
                "at least two constructors",
            ),
            (
                "missing attribute",
                "inductive Bad where | left | right\nwith\n  total : Bad → Nat\n    | .left => 0\n    | .right => 1\n",
                "must be tagged",
            ),
            (
                "outside attribute",
                "@[computed_field] def bad (n : Nat) : Nat := n\n",
                "computed_field",
            ),
            (
                "major dependence",
                "inductive Bad where | left | right\nwith\n  @[computed_field] same : (x : Bad) → Eq x x\n    | .left => rfl\n    | .right => rfl\n",
                "must not depend on value",
            ),
            (
                "index dependence",
                "inductive Bad : Bool → Type where\n  | left : Bad false\n  | right : Bad true\nwith\n  @[computed_field] same : (b : Bool) → Bad b → Eq b b\n    | _, .left => rfl\n    | _, .right => rfl\n",
                "must not depend on indices",
            ),
            (
                "irreducible constructor result",
                "opaque opaqueScore {A : Type} (_ : A) : Nat := 0\ninductive Bad where\n  | empty\n  | value (n : Nat)\nwith\n  @[computed_field] total : Bad → Nat\n    | .empty => opaqueScore Bad.empty\n    | .value n => opaqueScore (Bad.value n)\n",
                "does not reduce for constructor",
            ),
            (
                "invalid unused field",
                "inductive Bad where | empty | value (n : Nat)\nwith\n  @[computed_field] total : Bad → Nat\n    | .empty => 0\n    | .value n => n\n  @[computed_field] invalid : Bad → Bool\n    | .empty => Nat.zero\n    | .value _ => true\n",
                "Type mismatch",
            ),
            (
                "unknown attribute",
                "inductive Bad where | left | right\nwith\n  @[computed_field, no_such_computed_attribute] total : Bad → Nat\n    | .left => 0\n    | .right => 1\n",
                "Unknown attribute",
            ),
        ];
        let engine = &fixture.imported.engine;
        let options = KVMap::new();
        let before = engine.logical_root(&options);
        for (label, source, diagnostic) in cases {
            let output = reference(&fixture.compiler, source, None);
            assert!(
                output.contains(diagnostic),
                "wrong pin boundary for {label}: {output}"
            );
            let error = engine
                .check_source_files(&[source.as_bytes()], &options, check_limits())
                .expect_err(label);
            assert!(
                matches!(error.disposition(), ("elaboration" | "input", false, 1))
                    || (matches!(label, "one constructor" | "index dependence")
                        && error.disposition() == ("capability", false, 5)),
                "{label}: {error:?}"
            );
            assert_eq!(engine.logical_root(&options), before, "{label}");
            for unpublished in [
                "Bad",
                "Bad._impl",
                "Bad.total",
                "Bad.invalid",
                "Bad.total._override",
                "bad",
            ] {
                assert!(
                    !engine.environment().contains(&name(unpublished)),
                    "{label}: {unpublished}"
                );
            }
        }
        let retry = checked(engine, SINGLE);
        assert_generated(&retry, "Cache", "add", &["total"], 1);
        assert_eq!(engine.logical_root(&options), before);
    });
}

#[test]
fn generated_cache_provenance_does_not_authorize_user_written_unsafe_casts() {
    with_fixture(|fixture| {
        let source = format!(
            r#"{SINGLE}
unsafe def injected : Cache := unsafeCast (Cache.add._impl 99 2 Cache.empty)
#eval injected.total
"#
        );
        // The pin confirms that a getter reads the stored cache, even when an
        // explicitly unsafe client fabricates an inconsistent representation.
        reference(&fixture.compiler, &source, Some("99"));
        let before = fixture.imported.engine.logical_root(&KVMap::new());
        let error = fixture
            .imported
            .engine
            .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
            .expect_err("native cached-field provenance does not grant arbitrary cast authority");
        let diagnostic = format!("{error:?}");
        assert!(
            diagnostic.contains("unsafeCast")
                || diagnostic.to_ascii_lowercase().contains("unsupported"),
            "{diagnostic}"
        );
        assert_eq!(fixture.imported.engine.logical_root(&KVMap::new()), before);
    });
}

#[test]
fn generated_inventory_refuses_changed_override_and_constructor_layout() {
    with_fixture(|fixture| {
        let engine = checked(&fixture.imported.engine, SINGLE);
        let original = engine.environment();
        let Some(ConstantInfo::Defn(mut altered_body)) =
            original.find(&name("Cache.add._override")).cloned()
        else {
            panic!("generated constructor override");
        };
        // Even a type-correct identity wrapper changes the generated body and
        // must not inherit its authority merely by keeping the same name.
        altered_body.value = Expr::app(
            Expr::lam(
                Name::anonymous(),
                altered_body.base.type_.clone(),
                Expr::bvar(0).unwrap(),
                BinderInfo::Default,
            ),
            altered_body.value,
        );
        let Some(ConstantInfo::Ctor(mut altered_layout)) =
            original.find(&name("Cache.add._impl")).cloned()
        else {
            panic!("generated constructor layout");
        };
        altered_layout.num_fields -= 1;
        for replacement in [
            ConstantInfo::Defn(altered_body),
            ConstantInfo::Ctor(altered_layout),
        ] {
            let mut altered = Environment::new();
            for (label, _) in original.constants() {
                if label != replacement.name() {
                    altered = altered.with_entry(original.entry(label).unwrap()).unwrap();
                }
            }
            for (journal, state) in original.extensions() {
                altered = altered
                    .register_extension(state.descriptor.clone())
                    .unwrap();
                for entry in state.entries() {
                    altered = altered
                        .push_extension_entry(journal, entry.payload.clone())
                        .unwrap();
                }
            }
            altered = altered.add_decl(replacement).unwrap();
            let error = fln_elab::computed_fields::validated_family(
                &altered,
                &name("Cache"),
                limits().kernel,
                Default::default(),
            )
            .expect_err("a journal claim cannot authorize a changed generated implementation");
            assert!(
                !error.is_resource_limit(),
                "the complete mutated model must be rejected: {error:?}"
            );
            let mut inert = Environment::new();
            for (label, _) in altered.constants() {
                inert = inert.with_entry(altered.entry(label).unwrap()).unwrap();
            }
            for (journal, state) in altered.extensions() {
                if journal == &fln_elab::computed_fields::journal_name() {
                    continue;
                }
                inert = inert.register_extension(state.descriptor.clone()).unwrap();
                for entry in state.entries() {
                    inert = inert
                        .push_extension_entry(journal, entry.payload.clone())
                        .unwrap();
                }
            }
            assert!(
                fln_elab::computed_fields::tags::read_tags(&inert)
                    .unwrap()
                    .contains(&name("Cache.total"))
            );
            assert!(
                fln_elab::computed_fields::recover_imported(
                    &inert,
                    &name("Cache"),
                    &[name("Cache.total")],
                    &[name("Cache.total")],
                    limits().kernel,
                    Default::default(),
                )
                .expect("a changed generated model is an inert foreign candidate")
                .is_none()
            );
            assert!(
                inert
                    .extension(&fln_elab::computed_fields::journal_name())
                    .is_none()
            );
        }
        let error = fln_elab::computed_fields::recover_imported(
            original,
            &name("Cache"),
            &[name("Cache.total")],
            &[name("Cache.total")],
            limits().kernel,
            fln_elab::records::RecordBudget {
                max_nodes: 1,
                ..Default::default()
            },
        )
        .expect_err("recovery exhaustion must not be reported as an inert candidate");
        assert!(error.is_resource_limit());
    });
}

#[test]
fn pinned_name_import_keeps_a_consistent_native_representation() {
    with_fixture(|fixture| {
        let env = fixture.imported.engine.environment();
        let families = fln_elab::computed_fields::families(env, Default::default()).unwrap();
        let model = fln_elab::computed_fields::validated_family(
            env,
            &name("Lean.Name"),
            limits().kernel,
            Default::default(),
        )
        .expect("pin import either recovers an exact Name model or retains inert tags");
        assert_eq!(model.is_some(), families.contains(&name("Lean.Name")));
        let source = r#"
def inspectImportedName (value : Lean.Name) : Nat := match value with
  | .anonymous => 0
  | .num _ n => n
  | .str parent _ => match parent with
    | .anonymous => 1
    | .str _ _ => 2
    | .num _ n => n
"#;
        let evaluations = r#"#eval inspectImportedName (Lean.Name.str (Lean.Name.num Lean.Name.anonymous 7) "cache")
#eval inspectImportedName (Lean.Name.num (Lean.Name.str Lean.Name.anonymous "cache") 11)
#eval inspectImportedName Lean.Name.anonymous
"#;
        reference(
            &fixture.compiler,
            &format!("{source}{evaluations}"),
            Some("7\n11\n0"),
        );
        let engine = checked(&fixture.imported.engine, source);
        execute(&engine, evaluations, &["7", "11", "0"]);
        if model.is_some() {
            let hash = "#eval BitVec.toNat (UInt64.toBitVec Lean.Name.anonymous.hash)\n";
            reference(&fixture.compiler, hash, Some("1723"));
            execute(&engine, hash, &["1723"]);
        }
    });
}

#[test]
fn public_computed_family_admits_following_instances_without_duplicate_metadata() {
    with_fixture(|fixture| {
        let module = name("ComputedContinuation");
        let source = format!(
            "module\nprelude\npublic import Init.Prelude\npublic section\n{SINGLE}\ninstance : Inhabited Cache where\n  default := Cache.empty\n"
        );
        let files = [SourceModuleInput {
            name: &module,
            source: source.as_bytes(),
        }];
        let options = KVMap::new();
        let before = fixture.imported.engine.logical_root(&options);
        let checked = fixture
            .imported
            .check_source_modules(
                &files,
                &module,
                &options,
                SourceModuleCheckLimits::new(check_limits()),
                None,
            )
            .expect("an ordinary public instance must not re-register the hidden computed getter")
            .into_complete()
            .unwrap();
        assert!(
            checked
                .checked
                .engine
                .environment()
                .contains(&name("instInhabitedCache"))
        );
        assert!(matches!(
            checked
                .checked
                .engine
                .environment()
                .find(&name("Cache.total")),
            Some(ConstantInfo::Defn(_))
        ));
        assert_eq!(fixture.imported.engine.logical_root(&options), before);
    });
}

fn assert_computed_ir_boundary(artifact: &mut SourceModuleArtifact, family: &str) {
    let public = artifact.bytes.clone();
    let error = artifact
        .compile_ir(SourceModuleIrLimits::new(limits()))
        .expect_err("logical computed artifacts do not claim an implemented pinned IR ABI");
    assert!(
        matches!(&error, SourceModuleIrError::Unsupported {
        module, declaration, reason,
    } if module == &artifact.name
        && declaration == &name(family)
        && *reason == "computed-field source IR requires cached constructor and replacement ABI lowering"),
        "unexpected computed IR boundary: {error:?}"
    );
    assert_eq!(
        artifact.bytes, public,
        "a refused IR facet must preserve its logical artifact"
    );
}

#[test]
fn physical_module_roundtrip_recovers_cached_execution_and_scalar_field_order() {
    with_fixture(|fixture| {
        let module = name("ComputedRoundtrip");
        let source = format!(
            "module\nprelude\npublic import Init.Prelude\npublic section\n{SINGLE}{CROSS}{WORD}{PACKED}{WIDTHS}"
        );
        let options = KVMap::new();
        let before = fixture.imported.engine.logical_root(&options);
        // This fixture deliberately combines five families and all four word
        // widths. Reserve a finite aggregate allowance for six inventory phases
        // per family plus the scalar shape/bound checks; every declaration
        // keeps the ordinary kernel budget and production defaults are unchanged.
        let mut module_limits = SourceModuleCheckLimits::new(check_limits());
        module_limits.max_work = 5_000_000;
        let mut built = fixture
            .imported
            .compile_source_modules(
                &[SourceModuleInput {
                    name: &module,
                    source: source.as_bytes(),
                }],
                &module,
                &options,
                module_limits,
                OleanWriteBudget::default(),
            )
            .expect("all supported cached fields publish complete logical artifacts")
            .into_complete()
            .unwrap();
        assert_eq!(built.artifacts.len(), 1);
        assert_computed_ir_boundary(&mut built.artifacts[0], "Cache");

        let directory = std::env::temp_dir().join(format!(
            "fln-computed-roundtrip-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos(),
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let artifact = &built.artifacts[0];
        let companions = artifact
            .companions
            .as_ref()
            .expect("modern module companions");
        let paths = [
            "ComputedRoundtrip.olean",
            "ComputedRoundtrip.olean.server",
            "ComputedRoundtrip.olean.private",
        ];
        for (path, bytes) in paths.iter().zip([
            artifact.bytes.as_slice(),
            companions.server.as_slice(),
            companions.private.as_slice(),
        ]) {
            std::fs::write(directory.join(path), bytes).unwrap();
        }
        let parts = paths.map(|path| std::fs::read(directory.join(path)).unwrap());
        let prelude = name("Init.Prelude");
        let empty = Engine::builder().build_empty();
        let fresh = empty
            .import_olean_modules_for_source(
                &[
                    OleanModuleInput {
                        name: &prelude,
                        artifact: &fixture.prelude[0],
                        server_artifact: Some(&fixture.prelude[1]),
                        private_artifact: Some(&fixture.prelude[2]),
                    },
                    OleanModuleInput {
                        name: &module,
                        artifact: &parts[0],
                        server_artifact: Some(&parts[1]),
                        private_artifact: Some(&parts[2]),
                    },
                ],
                std::slice::from_ref(&module),
                &options,
                SourceOleanImportLimits::new(OleanCheckLimits::new(
                    IMPORT_STACK,
                    Budget::for_stack_bytes(IMPORT_STACK),
                )),
            )
            .expect("physical native companions pass independent checked import")
            .into_complete()
            .unwrap();
        assert!(empty.environment().is_empty());
        for (family, fields) in [
            ("Cache", vec!["total"]),
            ("Cross", vec!["first", "second"]),
            ("Digest", vec!["hash"]),
            // Tags are a name set. Cache order must come from the fully
            // regenerated representation, not this alphabetically sorted set.
            ("PackedCache", vec!["wide", "flag"]),
            ("Widths", vec!["tally"]),
        ] {
            let loaded = fln_elab::computed_fields::validated_family(
                fresh.engine.environment(),
                &name(family),
                limits().kernel,
                Default::default(),
            )
            .expect("recovered model can be validated with the ordinary source budget")
            .expect("a full native artifact recovers its generated representation");
            assert_eq!(
                loaded
                    .fields
                    .iter()
                    .map(|field| field.name.clone())
                    .collect::<Vec<_>>(),
                fields
                    .iter()
                    .map(|field| name(&format!("{family}.{field}")))
                    .collect::<Vec<_>>()
            );
            let original = fln_elab::computed_fields::validated_family(
                built.checked.checked.engine.environment(),
                &name(family),
                limits().kernel,
                Default::default(),
            )
            .unwrap()
            .unwrap();
            assert_eq!(
                loaded, original,
                "physical module recovery changed {family}"
            );
        }
        let samples = r#"
def importedCache : Cache := .add 2 (.add 3 .empty)
def importedCross : Cross := .add 2 (.add 3 (.add 4 .empty))
def importedDigest : Digest := .add (UInt64.ofNatLT 2 (of_decide_eq_true rfl))
  (.add (UInt64.ofNatLT 3 (of_decide_eq_true rfl)) .empty)
def importedPacked : PackedCache := .mk true (UInt64.ofNatLT 2 (of_decide_eq_true rfl)) 7
"#;
        let controls = r#"#eval importedCache.total
#eval importedCross.first
#eval importedCross.second
#eval BitVec.toNat (UInt64.toBitVec importedDigest.hash)
#eval BitVec.toNat (UInt64.toBitVec importedPacked.wide)
#eval match importedPacked.flag with | false => 11 | true => 13
#eval match importedPacked with | .empty => 0 | .mk _ _ payload => payload
"#;
        reference(
            &fixture.compiler,
            &format!("{SINGLE}{CROSS}{WORD}{PACKED}{WIDTHS}{samples}{controls}"),
            Some("5\n19\n29\n5467619628213459297\n2\n11\n7"),
        );
        let sample_engine = checked(&fresh.engine, samples);
        let bytecode = execute(
            &sample_engine,
            controls,
            &["5", "19", "29", "5467619628213459297", "2", "11", "7"],
        );
        execute_stored_cache_control(
            &fln_comp::flbc::decode_canonical(&bytecode[0], Default::default()).unwrap(),
        );

        // The Reference reads our actual emitted maps. UInt64 slots precede
        // Bool bytes in the scalar area, independently of declaration order.
        let inspector = r#"module
import Lean
import all Lean.Compiler.LCNF.ToImpureType
public import ComputedRoundtrip
open Lean Elab Command
run_cmd do
  for n in [`PackedCache.mk, `PackedCache.mk._impl] do
    let layout ← liftCoreM <| Compiler.LCNF.getCtorLayout n
    let fields := layout.fieldInfo.toList.map fun f => toString (Compiler.LCNF.CtorFieldInfo.format f)
    liftIO <| IO.println s!"LAYOUT {n} {reprStr layout.ctorInfo} {fields}"
"#;
        std::fs::write(directory.join("Inspect.lean"), inspector).unwrap();
        let pin = Command::new(&fixture.compiler)
            .current_dir(&directory)
            .env(
                "LEAN_PATH",
                std::env::join_paths([&directory, &fixture.library]).unwrap(),
            )
            .args(["-j1", "Inspect.lean"])
            .output()
            .unwrap();
        assert!(
            pin.status.success(),
            "the pin refused our mixed cache layouts: {pin:?}"
        );
        assert!(pin.stderr.is_empty(), "{pin:?}");
        assert_eq!(
            String::from_utf8(pin.stdout).unwrap().trim(),
            "LAYOUT PackedCache.mk { name := `PackedCache.mk, cidx := 1, size := 1, usize := 0, ssize := 9 } [scalar#1@8:UInt8, scalar#8@0:UInt64, obj@0:tobj]\nLAYOUT PackedCache.mk._impl { name := `PackedCache.mk._impl, cidx := 1, size := 1, usize := 0, ssize := 18 } [scalar#8@0:UInt64, scalar#1@16:UInt8, scalar#1@17:UInt8, scalar#8@8:UInt64, obj@0:tobj]"
        );
        assert!(!directory.join("ComputedRoundtrip.ir").exists());

        let consumer = name("ComputedConsumer");
        let consumer_source = "module\nprelude\npublic import ComputedRoundtrip\npublic def payload (value : Cache) : Nat := match value with\n  | .empty => 0\n  | .add n _ => n\n";
        let mut consumer_build = fresh
            .compile_source_modules(
                &[SourceModuleInput {
                    name: &consumer,
                    source: consumer_source.as_bytes(),
                }],
                &consumer,
                &options,
                SourceModuleCheckLimits::new(check_limits()),
                OleanWriteBudget::default(),
            )
            .expect("a downstream source module can use the fresh imported family")
            .into_complete()
            .unwrap();
        assert_eq!(consumer_build.artifacts.len(), 1);
        assert_computed_ir_boundary(&mut consumer_build.artifacts[0], "Cache");
        assert_eq!(fixture.imported.engine.logical_root(&options), before);
    });
}

#[test]
fn module_export_publishes_complete_supported_layouts_and_refuses_unsupported_payloads() {
    with_fixture(|fixture| {
        let module = name("Computed");
        let source =
            format!("module\nprelude\npublic import Init.Prelude\npublic section\n{SINGLE}");
        let files = [SourceModuleInput {
            name: &module,
            source: source.as_bytes(),
        }];
        let options = KVMap::new();
        let before = fixture.imported.engine.logical_root(&options);
        let built = fixture
            .imported
            .compile_source_modules(
                &files,
                &module,
                &options,
                SourceModuleCheckLimits::new(check_limits()),
                OleanWriteBudget::default(),
            )
            .expect("supported computed-field artifacts include their complete metadata")
            .into_complete()
            .unwrap();
        assert_eq!(built.artifacts.len(), 1);
        let blocks = fln_olean::region::OleanView::parse(&built.artifacts[0].bytes)
            .unwrap()
            .extension_payloads(fln::OleanWalkBudget::default(), IMPORT_STACK)
            .unwrap();
        let metadata = fln_olean::source_extensions::decode(&blocks, Default::default()).unwrap();
        assert_eq!(metadata.computed_fields, [name("Cache.total")]);
        assert!(metadata.noncomputable.contains(&name("Cache.total")));
        assert!(
            metadata
                .aux_recursors
                .contains(&name("Cache._impl.casesOn"))
        );
        for original in ["Cache.empty", "Cache.add", "Cache.casesOn", "Cache.total"] {
            assert!(metadata.implemented_by.iter().any(|edge| {
                edge.declaration == name(original)
                    && edge.implementation == name(&format!("{original}._override"))
            }));
        }
        let private_extension = |module: &str, leaf: &str| {
            ["Lean", "Compiler", "LCNF", leaf].into_iter().fold(
                Name::num(name(&format!("_private.Lean.Compiler.LCNF.{module}")), 0),
                Name::str,
            )
        };
        let families = [name("Cache"), name("Cache._impl")];
        let constructors = [
            name("Cache.empty"),
            name("Cache.add"),
            name("Cache.empty._impl"),
            name("Cache.add._impl"),
        ];
        for (extension, expected) in [
            (
                private_extension("MonoTypes", "trivialStructureInfoExt"),
                families.to_vec(),
            ),
            (
                private_extension("ToImpureType", "impureTrivialStructureInfoExt"),
                families.to_vec(),
            ),
            (
                name("Lean.Compiler.LCNF.monoTypeExt"),
                families.iter().chain(&constructors).cloned().collect(),
            ),
            (
                private_extension("ToImpureType", "impureTypeExt"),
                families.to_vec(),
            ),
            (
                private_extension("ToImpureType", "ctorLayoutExt"),
                constructors.to_vec(),
            ),
        ] {
            let block = blocks.iter().find(|block| block.name == extension).unwrap();
            let mut conversion = fln_rt::convert::Conversion::new();
            let actual = block
                .entries
                .iter()
                .map(|bytes| {
                    let entry = fln_rt::region::materialize(bytes, 0).unwrap();
                    conversion.project_name(&entry.ctor_child(0)).unwrap()
                })
                .collect::<std::collections::BTreeSet<_>>();
            assert_eq!(
                actual,
                expected.into_iter().collect(),
                "compiler cache {extension:?}"
            );
        }
        assert_eq!(fixture.imported.engine.logical_root(&options), before);

        // USize is valid in a logical constructor and the checked cache
        // generator, but its separate machine-word layout is not projected by
        // this artifact profile. Refuse the whole publication at that boundary.
        let unsupported = SINGLE
            .replace("Cache", "UnsupportedCache")
            .replace("(n : Nat)", "(n : USize)")
            .replace("Nat.add n tail.total", "Nat.add 1 tail.total")
            .replace("| .add n tail =>", "| .add _ tail =>");
        reference(&fixture.compiler, &unsupported, Some(""));
        let admitted = checked(&fixture.imported.engine, &unsupported);
        assert!(
            admitted
                .environment()
                .contains(&name("UnsupportedCache.add._impl"))
        );
        let source =
            format!("module\nprelude\npublic import Init.Prelude\npublic section\n{unsupported}");
        let error = fixture
            .imported
            .compile_source_modules(
                &[SourceModuleInput {
                    name: &module,
                    source: source.as_bytes(),
                }],
                &module,
                &options,
                SourceModuleCheckLimits::new(check_limits()),
                OleanWriteBudget::default(),
            )
            .expect_err("unsupported computed payloads cannot publish partial artifacts");
        assert!(
            matches!(error,
                SourceModuleBuildError::Check(SourceModuleCheckError::Extension { module: ref failed, ref extension, reason })
                    if failed == &module
                    && extension == &fln_elab::computed_fields::journal_name()
                    && reason == "computed-field artifacts require supported logical and implementation compiler layouts"
            ),
            "unexpected computed-field artifact refusal: {error:?}"
        );
        assert_eq!(fixture.imported.engine.logical_root(&options), before);
    });
}
