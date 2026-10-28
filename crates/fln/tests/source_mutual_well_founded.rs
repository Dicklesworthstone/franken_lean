//! Mutually recursive `def`s with `termination_by` measures, judged against the pin.
//!
//! The pin (`Lean/Elab/PreDefinition/WF/Main.lean`, `Mutual.lean`, `PackMutual.lean`)
//! packs a recursive group's varying arguments into a right-nested `PSum` of each
//! member's `PSigma` pack, in SCC order, defines `<first>._mutual` by one
//! `WellFounded.Nat.fix`, and makes each member an `@[irreducible]` wrapper
//! `fun xs => <first>._mutual fixed (PSum.inl ⟨xs⟩)` etc. Every program below is
//! first run through the pinned `lean`; its exit code is the verdict to match.
#![forbid(unsafe_code)]
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, ClosedVmValue, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name,
    OleanCheckLimits, OleanDecodeLimits, OleanModuleInput, SourceCheckLimits, olean_module_imports,
};
use fln_core::expr::{Expr, ExprNode};
use fln_elab::reducibility::{Reducibility, table};
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

const STACK: usize = 256 * 1024 * 1024;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))
}

fn pinned_lib() -> Option<PathBuf> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|lib| lib.is_dir());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "FLN_REQUIRE_REFERENCE is set but the pinned Reference lib/lean is absent"
    );
    lib
}

fn import_closure(lib: &Path, modules: &[&str]) -> Engine {
    let roots: Vec<_> = modules.iter().map(|module| n(module)).collect();
    let mut pending = roots.clone();
    let mut seen = BTreeSet::new();
    let mut names = Vec::new();
    let mut parts = Vec::new();
    while let Some(module) = pending.pop() {
        if !seen.insert(module.clone()) {
            continue;
        }
        let base = module
            .to_display_string()
            .split('.')
            .fold(lib.to_path_buf(), |path, part| path.join(part))
            .with_extension("olean");
        let exported = std::fs::read(&base).expect("pinned exported artifact");
        pending.extend(
            olean_module_imports(&exported, OleanDecodeLimits::new(exported.len()))
                .expect("pinned module imports"),
        );
        parts.push([
            exported,
            std::fs::read(base.with_extension("olean.server")).expect("pinned server artifact"),
            std::fs::read(base.with_extension("olean.private")).expect("pinned private artifact"),
        ]);
        names.push(module);
    }
    let inputs: Vec<_> = names
        .iter()
        .zip(&parts)
        .map(|(name, [exported, server, private])| OleanModuleInput {
            name,
            artifact: exported,
            server_artifact: Some(server),
            private_artifact: Some(private),
        })
        .collect();
    Engine::builder()
        .build_empty()
        .import_olean_modules_for_source(
            &inputs,
            &roots,
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(256 * 1024 * 1024, limits().kernel)),
        )
        .expect("the imported library passes both checkers")
        .into_complete()
        .expect("the import finishes")
        .engine
}

/// The pinned `lean` binary next to the pinned library, or None (a SKIP).
fn reference() -> Option<&'static Path> {
    static REFERENCE: OnceLock<Option<PathBuf>> = OnceLock::new();
    REFERENCE
        .get_or_init(|| {
            let executable = pinned_lib()?.parent()?.parent()?.join("bin/lean");
            executable.is_file().then_some(executable)
        })
        .as_deref()
}

/// Run the pinned `lean` on `source`; assert its exit code and return its output.
fn oracle(source: &str, accepted: bool) -> String {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let reference = reference().expect("callers check for the pin first");
    let dir = std::env::temp_dir().join(format!("fln-mutual-wf-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{}.lean", NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::write(&path, source).unwrap();
    let output = Command::new(reference).arg(&path).output().unwrap();
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        output.status.code(),
        Some(if accepted { 0 } else { 1 }),
        "Reference verdict differs from the expectation for:\n{source}\n{text}"
    );
    text
}

/// One shared import of the closure the single-function suite uses for omega and
/// the default decreasing tactic. Built on a large stack, then shared read-only.
fn base() -> Option<&'static Engine> {
    static BASE: OnceLock<Option<Engine>> = OnceLock::new();
    BASE.get_or_init(|| {
        let Some(lib) = pinned_lib() else {
            eprintln!(
                "SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)"
            );
            return None;
        };
        reference()?;
        let started = std::time::Instant::now();
        let engine = std::thread::Builder::new()
            .stack_size(STACK)
            .spawn(move || {
                import_closure(&lib, &["Init.WFTactics", "Init.Omega", "Init.WFComputable"])
            })
            .expect("spawn import thread")
            .join()
            .expect("the import closure loads");
        eprintln!("imported the closure in {:?}", started.elapsed());
        Some(engine)
    })
    .as_ref()
}

fn on_large_stack(test: impl FnOnce(&'static Engine) + Send + 'static) {
    let Some(base) = base() else {
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || test(base))
        .expect("spawn checking thread")
        .join()
        .expect("checks finish");
}

fn check(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("both checkers complete")
    .engine
}

/// A refusal is a semantic answer here, never a resource stop or a fault, and it
/// leaves the predecessor unchanged.
fn refuse(base: &Engine, source: &str) -> String {
    let root = base.logical_root(&KVMap::new());
    let error = base
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .err()
        .unwrap_or_else(|| panic!("the pin refuses this program, so must we:\n{source}"));
    assert!(
        !matches!(
            error.disposition().0,
            "resource" | "inconclusive" | "internal-fault"
        ),
        "a refusal, not a stop: {error:?}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    format!("{error:?}")
}

fn evaluate(engine: &Engine, query: &str) -> ClosedVmValue {
    let result = engine
        .execute_source_definitions(
            &[query.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{query}: {error:?}"))
        .into_complete()
        .expect("the evaluation finishes");
    let [execution] = result.executions.as_slice() else {
        panic!("one execution for {query}");
    };
    fln::closed_vm_value(&execution.exit)
        .expect("a normal VM exit")
        .expect("a closed value")
}

/// A compact, binder-name-free rendering: constants by name, every argument
/// (implicit ones included) in application order, bound variables by de Bruijn
/// index. Enough to compare a wrapper's packing with the pin's `#print`.
fn shape(expr: &Expr) -> String {
    match expr.node() {
        ExprNode::BVar { idx } => format!("#{idx}"),
        ExprNode::Const { name, .. } => name.to_display_string(),
        ExprNode::App { .. } => {
            let mut arguments = Vec::new();
            let mut head = expr;
            while let ExprNode::App { f, a } = head.node() {
                arguments.push(shape(a));
                head = f;
            }
            arguments.reverse();
            format!("({} {})", shape(head), arguments.join(" "))
        }
        ExprNode::Lam { body, .. } => format!("(fun {})", shape(body)),
        _ => "?".to_owned(),
    }
}

fn definition(engine: &Engine, name: &str) -> fln_env::constants::DefinitionVal {
    match engine.environment().find(&n(name)) {
        Some(ConstantInfo::Defn(definition)) => definition.clone(),
        other => panic!("{name} is a definition: {other:?}"),
    }
}

fn assert_member(engine: &Engine, name: &str, all: &[&str], wrapper: &str) {
    let member = definition(engine, name);
    assert_eq!(member.safety, DefinitionSafety::Safe);
    assert_eq!(
        member.all,
        all.iter().map(|name| n(name)).collect::<Vec<_>>()
    );
    assert_eq!(shape(&member.value), wrapper, "{name}'s wrapper");
    assert_eq!(
        table(engine.environment()).unwrap().status(&n(name)),
        Reducibility::Irreducible,
        "{name} is @[irreducible] at the pin"
    );
}

fn assert_auxiliary(engine: &Engine, name: &str) {
    let auxiliary = definition(engine, name);
    assert_eq!(auxiliary.safety, DefinitionSafety::Safe);
    assert_eq!(auxiliary.all, vec![n(name)]);
    assert_ne!(
        table(engine.environment()).unwrap().status(&n(name)),
        Reducibility::Irreducible,
        "{name} stays semireducible at the pin"
    );
    let mut body = &auxiliary.value;
    while let ExprNode::Lam { body: next, .. } = body.node() {
        body = next;
    }
    assert!(
        shape(body).starts_with("(WellFounded.Nat.fix "),
        "{name} is a Nat.fix: {}",
        shape(body)
    );
    // `fun x a => PSum.casesOn (motive := …) x alt₀ … a`, as the pin prints it.
    let ExprNode::App { a: functional, .. } = body.node() else {
        panic!("{name} applies the fixpoint to its functional");
    };
    let ExprNode::Lam {
        body: functional, ..
    } = functional.node()
    else {
        panic!("{name}'s functional binds the packed argument");
    };
    let ExprNode::Lam {
        body: functional, ..
    } = functional.node()
    else {
        panic!("{name}'s functional binds the continuation");
    };
    let rendered = shape(functional);
    assert!(
        rendered.starts_with("(PSum.casesOn ") && rendered.ends_with(" #0)"),
        "{name}'s functional cases on the packed argument and passes the continuation: {rendered}"
    );
}

/// `partial def <member>._unsafe_rec`, the pin's executable companions
/// (`addAndCompileUnsafe`), one Partial group naming each other.
fn assert_companions(engine: &Engine, members: &[&str]) {
    let group: Vec<_> = members
        .iter()
        .map(|member| n(&format!("{member}._unsafe_rec")))
        .collect();
    for (member, companion) in members.iter().zip(&group) {
        let executable = definition(engine, &companion.to_display_string());
        assert_eq!(executable.safety, DefinitionSafety::Partial);
        assert_eq!(executable.all, group);
        assert_eq!(executable.base.type_, definition(engine, member).base.type_);
    }
}

const EVEN_ODD: &str = "mutual
def ev (n : Nat) : Bool := if h : n = 0 then true else od (n - 1)
termination_by n
decreasing_by omega
def od (n : Nat) : Bool := if h : n = 0 then false else ev (n - 1)
termination_by n
decreasing_by omega
end
";

#[test]
fn decreasing_by_members_pack_into_one_nat_fix() {
    on_large_stack(|base| {
        let printed = oracle(
            &format!("{EVEN_ODD}#print ev\n#print od\n#eval ev 7\n#print ev._unsafe_rec\n"),
            true,
        );
        assert!(
            printed.contains("fun n => ev._mutual (PSum.inl n)"),
            "{printed}"
        );
        assert!(printed.contains("partial def ev._unsafe_rec"), "{printed}");
        assert!(
            printed.contains("fun n => ev._mutual (PSum.inr n)"),
            "{printed}"
        );
        assert!(
            printed.contains("\nfalse\n") || printed.starts_with("false\n"),
            "{printed}"
        );
        let engine = check(base, EVEN_ODD);
        assert_member(
            &engine,
            "ev",
            &["ev", "od"],
            "(fun (ev._mutual (PSum.inl Nat Nat #0)))",
        );
        assert_member(
            &engine,
            "od",
            &["ev", "od"],
            "(fun (ev._mutual (PSum.inr Nat Nat #0)))",
        );
        assert_auxiliary(&engine, "ev._mutual");
        assert_companions(&engine, &["ev", "od"]);
        // Bool.false is constructor 0.
        assert_eq!(evaluate(&engine, "#eval ev 7"), ClosedVmValue::Scalar(0));
        assert_eq!(evaluate(&engine, "#eval od 7"), ClosedVmValue::Scalar(1));
    });
}

#[test]
fn the_default_decreasing_tactic_proves_each_call() {
    let source = EVEN_ODD.replace("decreasing_by omega\n", "");
    on_large_stack(move |base| {
        oracle(&source, true);
        let engine = check(base, &source);
        assert_auxiliary(&engine, "ev._mutual");
        assert_eq!(evaluate(&engine, "#eval ev 10"), ClosedVmValue::Scalar(1));
    });
}

/// `vendor/lean4-src/tests/elab/mutwf2.lean`: equations and termination_by only.
const EX1: &str = "namespace Ex1
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  termination_by n => n
  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
  termination_by n => n
end
end Ex1
";

#[test]
fn upstream_mutwf2_equation_members() {
    on_large_stack(|base| {
        let printed = oracle(&format!("{EX1}#print Ex1.isEven\n#print Ex1.isOdd\n"), true);
        assert!(
            printed.contains("fun a => Ex1.isEven._mutual (PSum.inl a)"),
            "{printed}"
        );
        let engine = check(base, EX1);
        assert_member(
            &engine,
            "Ex1.isEven",
            &["Ex1.isEven", "Ex1.isOdd"],
            "(fun (Ex1.isEven._mutual (PSum.inl Nat Nat #0)))",
        );
        assert_member(
            &engine,
            "Ex1.isOdd",
            &["Ex1.isEven", "Ex1.isOdd"],
            "(fun (Ex1.isEven._mutual (PSum.inr Nat Nat #0)))",
        );
        assert_auxiliary(&engine, "Ex1.isEven._mutual");
        assert_eq!(
            evaluate(&engine, "#eval Ex1.isOdd 9"),
            ClosedVmValue::Scalar(1)
        );
    });
}

const ABC: &str = "mutual
def a (n : Nat) : Nat := if h : n = 0 then 0 else c (n - 1)
termination_by n
decreasing_by omega
def b (n : Nat) : Nat := if h : n = 0 then 1 else a (n - 1)
termination_by n
decreasing_by omega
def c (n : Nat) : Nat := if h : n = 0 then 2 else b (n - 1)
termination_by n
decreasing_by omega
end
";

/// The PSum positions follow the pin's Tarjan order over first-occurrence call
/// edges (a, c, b here), not the source order (a, b, c).
#[test]
fn members_are_packed_in_strongly_connected_component_order() {
    on_large_stack(|base| {
        let printed = oracle(&format!("{ABC}#print b\n#print c\n#eval a 5\n"), true);
        assert!(
            printed.contains("fun n => a._mutual (PSum.inr (PSum.inr n))"),
            "{printed}"
        );
        assert!(
            printed.contains("fun n => a._mutual (PSum.inr (PSum.inl n))"),
            "{printed}"
        );
        let engine = check(base, ABC);
        let order = ["a", "c", "b"];
        assert_member(
            &engine,
            "a",
            &order,
            "(fun (a._mutual (PSum.inl Nat (PSum Nat Nat) #0)))",
        );
        assert_member(
            &engine,
            "c",
            &order,
            "(fun (a._mutual (PSum.inr Nat (PSum Nat Nat) (PSum.inl Nat Nat #0))))",
        );
        assert_member(
            &engine,
            "b",
            &order,
            "(fun (a._mutual (PSum.inr Nat (PSum Nat Nat) (PSum.inr Nat Nat #0))))",
        );
        assert_auxiliary(&engine, "a._mutual");
        assert_companions(&engine, &["a", "c", "b"]);
        // a 5 = c 4 = b 3 = a 2 = c 1 = b 0 = 1, as the pin prints.
        assert!(printed.ends_with("1\n"), "{printed}");
        assert_eq!(evaluate(&engine, "#eval a 5"), ClosedVmValue::Scalar(1));
    });
}

#[test]
fn a_nonrecursive_member_is_published_after_its_recursive_component() {
    let source = format!(
        "{}def d (n : Nat) : Bool := ev n && od n\nend\n",
        EVEN_ODD.trim_end().trim_end_matches("end")
    );
    on_large_stack(move |base| {
        let printed = oracle(&format!("{source}#print d\n#eval d 4\n"), true);
        assert!(printed.contains("def d : Nat → Bool"), "{printed}");
        let engine = check(base, &source);
        let d = definition(&engine, "d");
        assert_eq!(d.all, vec![n("d")]);
        assert_ne!(
            table(engine.environment()).unwrap().status(&n("d")),
            Reducibility::Irreducible
        );
        assert_member(
            &engine,
            "ev",
            &["ev", "od"],
            "(fun (ev._mutual (PSum.inl Nat Nat #0)))",
        );
        // ev 4 && od 4 = true && false.
        assert_eq!(evaluate(&engine, "#eval d 4"), ClosedVmValue::Scalar(0));
    });
}

/// The pin only warns ("unused `termination_by`, function is not recursive")
/// for a hint on a member outside every recursive component.
#[test]
fn hints_on_nonrecursive_members_are_ignored() {
    let source = "mutual
def p (n : Nat) : Nat := q n
termination_by n
def q (n : Nat) : Nat := n
end
";
    on_large_stack(move |base| {
        let printed = oracle(source, true);
        assert!(printed.contains("unused `termination_by`"), "{printed}");
        let engine = check(base, source);
        assert_eq!(definition(&engine, "p").all, vec![n("p")]);
        assert_ne!(
            table(engine.environment()).unwrap().status(&n("p")),
            Reducibility::Irreducible
        );
        assert!(!engine.environment().contains(&n("p._mutual")));
    });
}

#[test]
fn a_call_that_does_not_decrease_is_refused() {
    let source = "mutual
def a (n : Nat) : Nat := if h : n = 0 then 0 else b (n + 2)
termination_by n
def b (n : Nat) : Nat := if h : n = 0 then 1 else a (n - 1)
termination_by n
end
";
    on_large_stack(move |base| {
        let printed = oracle(source, false);
        assert!(printed.contains("failed to prove termination"), "{printed}");
        assert!(printed.contains("⊢ n + 2 < n"), "{printed}");
        let refusal = refuse(base, source);
        eprintln!("non-decreasing call: {refusal}");
        assert!(!base.environment().contains(&n("a")));
        assert!(!base.environment().contains(&n("a._mutual")));
    });
}

/// `vendor/lean4-src/tests/elab_fail/mutwftypemismatch.lean`, both namespaces.
#[test]
fn measures_of_different_types_are_refused() {
    let first = "namespace Ex1
mutual
def foo : Nat → Nat
 | 0   => 1
 | n+1 => bar n
termination_by n => n

def bar : Nat → Nat
 | 0   => 1
 | n+1 => foo n
termination_by n => n > 2
end
end Ex1
";
    let second = "namespace Ex2
mutual
def foo (fixed : Nat) : Nat → Nat
 | 0   => 1
 | n+1 => bar fixed n
termination_by n => n

def bar (fixed : Nat) : Nat → Nat
 | 0   => 1
 | n+1 => foo fixed n
termination_by n => (⟨n, sorry⟩ : Fin fixed)
end
end Ex2
";
    on_large_stack(move |base| {
        for source in [first, second] {
            let printed = oracle(source, false);
            assert!(
                printed.contains(
                    "The termination measures of mutually recursive functions must have the same return type"
                ),
                "{printed}"
            );
            let refusal = refuse(base, source);
            eprintln!("measure type mismatch: {refusal}");
        }
    });
}

/// The pin reports "incomplete set of termination hints" (exit 1) and then still
/// defines the group by GuessLex. We refuse the whole group: the exit code agrees,
/// but GuessLex across a group is not implemented, so this is not parity.
#[test]
fn a_member_without_a_measure_is_refused() {
    let source = "mutual
def a (n : Nat) : Nat := if h : n = 0 then 0 else b (n - 1)
termination_by n
def b (n : Nat) : Nat := if h : n = 0 then 1 else a (n - 1)
end
";
    on_large_stack(move |base| {
        let printed = oracle(source, false);
        assert!(
            printed.contains("incomplete set of termination hints"),
            "{printed}"
        );
        let refusal = refuse(base, source);
        eprintln!("incomplete hints: {refusal}");
        assert!(!base.environment().contains(&n("a")));
    });
}

/// `vendor/lean4-src/tests/elab/955.lean`: measures that are themselves `match`es.
#[test]
fn upstream_955_match_measures() {
    let source = "namespace Ex2
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  termination_by n =>
    match n with
    | _ => n

  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
  termination_by n =>
    match n with
    | _ => n
end
end Ex2
";
    on_large_stack(move |base| {
        oracle(source, true);
        let engine = check(base, source);
        assert_member(
            &engine,
            "Ex2.isOdd",
            &["Ex2.isEven", "Ex2.isOdd"],
            "(fun (Ex2.isEven._mutual (PSum.inr Nat Nat #0)))",
        );
        assert_auxiliary(&engine, "Ex2.isEven._mutual");
        assert_eq!(
            evaluate(&engine, "#eval Ex2.isEven 6"),
            ClosedVmValue::Scalar(1)
        );
    });
}

/// `vendor/lean4-src/tests/elab/issue2925.lean`: member types that are
/// definitions unfolding to function types, and a member with two varying
/// arguments packed as a `PSigma`.
#[test]
fn upstream_issue2925_function_type_definitions() {
    let source = "def FunType := Nat → Nat
def Fun2Type := Nat → Nat → Nat

mutual
def foo : FunType
  | .zero => 0
  | .succ n => bar n
termination_by n => n
def bar : Nat → Nat
  | .zero => 0
  | .succ n => baz n 0
termination_by n => n
def baz : Fun2Type
  | .zero, m => 0
  | .succ n, m => foo n
termination_by n _ => n
end
";
    on_large_stack(move |base| {
        let printed = oracle(&format!("{source}#print baz\n"), true);
        assert!(
            printed.contains("fun a a_1 => foo._mutual (PSum.inr (PSum.inr ⟨a, a_1⟩))"),
            "{printed}"
        );
        let engine = check(base, source);
        let order = ["foo", "bar", "baz"];
        assert_member(
            &engine,
            "bar",
            &order,
            "(fun (foo._mutual (PSum.inr Nat (PSum Nat (PSigma Nat (fun Nat))) (PSum.inl Nat (PSigma Nat (fun Nat)) #0))))",
        );
        assert_member(
            &engine,
            "baz",
            &order,
            "(fun (fun (foo._mutual (PSum.inr Nat (PSum Nat (PSigma Nat (fun Nat))) (PSum.inr Nat (PSigma Nat (fun Nat)) (PSigma.mk Nat (fun Nat) #1 #0))))))",
        );
        assert_auxiliary(&engine, "foo._mutual");
        assert_companions(&engine, &order);
        assert_eq!(evaluate(&engine, "#eval foo 5"), ClosedVmValue::Scalar(0));
    });
}

#[test]
fn section_captures_flow_through_measures_and_acyclic_peers() {
    let source = "section\nvariable (unused : String) (offset : Nat)\nmutual\n\
        def wfCapturedLeft (n : Nat) : Nat := if h : n = 0 then wfCapturedHelper 0 else wfCapturedRight (n-1) + 1\n\
        termination_by n + offset\ndecreasing_by omega\n\
        def wfCapturedRight (n : Nat) : Nat := if h : n = 0 then wfCapturedHelper 1 else wfCapturedLeft (n-1) + 2\n\
        termination_by n + offset\ndecreasing_by omega\n\
        def wfCapturedHelper (n : Nat) : Nat := offset + n\nend\nend\n";
    on_large_stack(move |base| {
        let printed = oracle(
            &format!("{source}#eval wfCapturedLeft 7 2\n#eval wfCapturedRight 7 2\n"),
            true,
        );
        for expected in ["10", "11"] {
            assert!(printed.lines().any(|line| line == expected), "{printed}");
        }
        let engine = check(base, source);
        assert_member(
            &engine,
            "wfCapturedLeft",
            &["wfCapturedLeft", "wfCapturedRight"],
            "(fun (fun (wfCapturedLeft._mutual #1 (PSum.inl Nat Nat #0))))",
        );
        assert_auxiliary(&engine, "wfCapturedLeft._mutual");
        assert_companions(&engine, &["wfCapturedLeft", "wfCapturedRight"]);
        assert_eq!(
            evaluate(&engine, "#eval wfCapturedLeft 7 2"),
            ClosedVmValue::Scalar(10)
        );
        assert_eq!(
            evaluate(&engine, "#eval wfCapturedRight 7 2"),
            ClosedVmValue::Scalar(11)
        );
    });
}

#[test]
fn section_captures_preserve_polymorphic_values_and_instance_dictionaries() {
    let values = "universe u\nsection\nvariable (A : Type u) (left right : A)\nmutual\n\
        def wfPickLeft (n : Nat) : A := if h : n = 0 then left else wfPickRight (n-1)\n\
        termination_by n\ndecreasing_by omega\n\
        def wfPickRight (n : Nat) : A := if h : n = 0 then right else wfPickLeft (n-1)\n\
        termination_by n\ndecreasing_by omega\nend\nend\n";
    let instance = "universe u\nsection\nvariable {A : Type u} [Inhabited A]\nmutual\n\
        def wfDefaultLeft (n : Nat) : A := if h : n = 0 then default else wfDefaultRight (n-1)\n\
        termination_by n\ndecreasing_by omega\n\
        def wfDefaultRight (n : Nat) : A := if h : n = 0 then default else wfDefaultLeft (n-1)\n\
        termination_by n\ndecreasing_by omega\nend\nend\n";
    on_large_stack(move |base| {
        for (source, member, peer, query, expected) in [
            (
                values,
                "wfPickLeft",
                "wfPickRight",
                "#eval wfPickLeft Nat 7 13 3",
                13,
            ),
            (
                instance,
                "wfDefaultLeft",
                "wfDefaultRight",
                "#eval (wfDefaultRight 3 : Nat)",
                0,
            ),
        ] {
            oracle(&format!("{source}{query}\n"), true);
            let engine = check(base, source);
            let definition = definition(&engine, member);
            assert_eq!(definition.base.level_params, vec![n("u")]);
            assert!(!definition.base.type_.has_fvar());
            assert!(!definition.value.has_fvar());
            assert_eq!(
                table(engine.environment()).unwrap().status(&n(member)),
                Reducibility::Irreducible
            );
            assert_companions(&engine, &[member, peer]);
            assert_eq!(evaluate(&engine, query), ClosedVmValue::Scalar(expected));
        }
    });
}

#[test]
fn section_captures_preserve_shadowed_parameters_and_measure_aliases() {
    let source = "section\nvariable (value : Nat)\nmutual\n\
        def wfShadow (value : Nat) : Nat := match value with\n\
        | 0 => 0\n| n+1 => wfPeer n\ntermination_by value\n\
        def wfPeer : Nat -> Nat\n| 0 => value\n| n+1 => wfShadow n\n\
        termination_by n => n\nend\nend\n";
    on_large_stack(move |base| {
        oracle(
            &format!("{source}#eval wfShadow 7 3\n#eval wfPeer 7 3\n"),
            true,
        );
        let engine = check(base, source);
        assert_companions(&engine, &["wfShadow", "wfPeer"]);
        assert_eq!(
            evaluate(&engine, "#eval wfShadow 7 3"),
            ClosedVmValue::Scalar(7)
        );
        assert_eq!(
            evaluate(&engine, "#eval wfPeer 7 3"),
            ClosedVmValue::Scalar(0)
        );
    });
}

#[test]
fn section_captures_exclude_hint_only_variables_and_nondecreasing_calls() {
    let measure_only = "section\nvariable (offset : Nat)\nmutual\n\
        def measureLeft (n : Nat) : Nat := if h : n = 0 then 0 else measureRight (n-1) + 1\n\
        termination_by n + offset\ndecreasing_by omega\n\
        def measureRight (n : Nat) : Nat := if h : n = 0 then 1 else measureLeft (n-1) + 2\n\
        termination_by n + offset\ndecreasing_by omega\nend\nend\n";
    let unused_measure_value = "section\nvariable (offset : Nat)\nmutual\n\
        def measureLeft (n : Nat) : Nat := if h : n = 0 then 0 else measureRight (n-1) + 1\n\
        termination_by let unused := offset; n\ndecreasing_by omega\n\
        def measureRight (n : Nat) : Nat := if h : n = 0 then 1 else measureLeft (n-1) + 2\n\
        termination_by n\ndecreasing_by omega\nend\nend\n";
    let nondecreasing = "section\nvariable (offset : Nat)\nmutual\n\
        def wfBadLeft (n : Nat) : Nat := if h : n = 0 then offset else wfBadRight n\n\
        termination_by n\ndecreasing_by omega\n\
        def wfBadRight (n : Nat) : Nat := wfBadLeft n\n\
        termination_by n\ndecreasing_by omega\nend\nend\n";
    let proof_only = "section\nvariable (secret : Nat)\nmutual\n\
        def proofScopeLeft (n : Nat) : Nat := if h : n = 0 then 0 else proofScopeRight (n-1) + 1\n\
        termination_by n\ndecreasing_by\n  let unused := secret\n  omega\n\
        def proofScopeRight (n : Nat) : Nat := if h : n = 0 then 1 else proofScopeLeft (n-1) + 2\n\
        termination_by n\ndecreasing_by omega\nend\nend\n";
    on_large_stack(move |base| {
        for source in [
            measure_only,
            unused_measure_value,
            nondecreasing,
            proof_only,
        ] {
            oracle(source, false);
            refuse(base, source);
            assert!(!base.environment().contains(&n("measureLeft")));
            assert!(!base.environment().contains(&n("wfBadLeft")));
        }
        let recovery = proof_only.replace("  let unused := secret\n", "");
        let printed = oracle(&format!("{recovery}#eval proofScopeLeft 2\n"), true);
        assert!(printed.lines().any(|line| line == "3"), "{printed}");
        let engine = check(base, &recovery);
        assert_eq!(
            evaluate(&engine, "#eval proofScopeLeft 2"),
            ClosedVmValue::Scalar(3)
        );
    });
}

/// Outside the supported slice a group stays a typed refusal: never a resource
/// stop, a fault, or a partial publication. The pin's verdict is recorded for
/// each; where it accepts, this is a known gap, not parity.
#[test]
fn shapes_outside_the_slice_stay_typed_refusals() {
    // `vendor/lean4-src/tests/elab/psumAtWF.lean`: the members auto-bind a
    // universe (`α : Sort u_1`); the pin accepts.
    let universe = "mutual

def fn (f : α → α) (a : α) (n : Nat) : α :=
  match n with
  | 0 => a
  | n+1 => gn f (f (f a)) (f a) n
termination_by n

def gn (f : α → α) (a b : α) (n : Nat) : α :=
  match n with
  | 0 => b
  | n+1 => fn f (f b) n
termination_by n

end
";
    // A lexicographic measure; the pin accepts (`Prod.Lex`).
    let lexicographic = "mutual
def f (n : Nat) (b : Bool) : Nat := if b then f n false else if h : n = 0 then 0 else g (n - 1)
termination_by (n, if b then 1 else 0)
decreasing_by all_goals sorry
def g (n : Nat) : Nat := f n true
termination_by (n, 2)
decreasing_by all_goals sorry
end
";
    // `vendor/lean4-src/tests/elab_fail/mutwf1.lean`: the pin refuses both groups.
    let failing = "namespace Ex2
mutual
  def f : Nat → Bool → Nat
    | n, true  => 2 * f n false
    | 0, false => 1
    | n, false => n + g (n+1) -- Error
  termination_by n b => (n, if b then 2 else 1)

  def g (n : Nat) : Nat :=
    if h : n ≠ 0 then
      f (n-1) true
    else
      n
  termination_by (n, 0)
end
end Ex2
";
    on_large_stack(move |base| {
        for (source, accepted) in [(universe, true), (lexicographic, true), (failing, false)] {
            oracle(source, accepted);
            let root = base.logical_root(&KVMap::new());
            let error = base
                .check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits()),
                )
                .err()
                .unwrap_or_else(|| panic!("outside the supported slice:\n{source}"));
            assert!(
                !matches!(
                    error.disposition().0,
                    "resource" | "inconclusive" | "internal-fault"
                ),
                "a refusal, not a stop: {error:?}"
            );
            assert_eq!(base.logical_root(&KVMap::new()), root);
            eprintln!("outside the slice (pin accepts: {accepted}): {error:?}");
        }
    });
}
